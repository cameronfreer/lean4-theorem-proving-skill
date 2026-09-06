#!/usr/bin/env python3
"""Lean/Lake integration suite for the file-gate and /disprove certification
sequence documented in PR #195 (issue #166).

What this establishes, against a REAL pinned Lean toolchain and the REAL
transaction helper (``lib/scripts/disprove_artifact_txn.py``):

    The documented certification sequence checks the intended declaration
    against freshly built imports, reads that declaration's actual axiom
    dependencies, and removes temporary material without creating stale
    target artifacts.

Concretely (one test family per numbered group below):

1. ``lake env lean`` elaborates against BUILT imports (false pass AND false
   failure after an imported source changes, through a transitive import);
   ``lake lean`` rebuilds the imports first and follows current source.
2. An imported theorem whose TYPE is unchanged but whose proof switches to
   ``sorry`` / a custom axiom still elaborates (exit 0!) — only the same-run
   ``#print axioms`` output exposes it; the reverse transition clears it.
3. Namespace collision: with a clean imported ROOT decoy of the fixed artifact
   name and the artifact appended inside a namespace left open to EOF, the
   unqualified probe inspects the appended declaration; the root-qualified
   probe inspects the decoy (negative control). Witness shapes must audit the
   wrapper, not the witness.
4. Accepted target layouts: ordinary module, custom-``srcDir`` module, and a
   scratch file outside every ``lean_lib``, all via the source path.
5. Target-artifact isolation: ``lake lean`` neither creates nor overwrites the
   target's own ``.olean`` (imports may be rebuilt); a targeted ``lake build``
   does write it, which is the leak the sequence avoids.
6. Rejection (compile failure / forbidden axiom) → rollback leaves unrelated
   source intact, the target's pre-existing ``.olean`` byte-identical, and the
   temporary declaration invisible to a consumer.
7. Success (direct and witness shapes) → all gate blocks gone, artifact kept,
   the gate-free file re-elaborates, and (module variant) a consumer can use
   the artifact after an explicit module build.
8. Inconclusive evidence: missing / wrong-declaration / truncated / malformed
   (``[,]``, ``[]``, non-name entries) / conflicting ``#print axioms`` records
   are REJECTED by the certification helper, never read as an empty axiom
   set. Acceptance requires ONE CONSISTENT axiom set for the expected
   declaration (identical duplicate records are fine; a malformed record for
   it poisons the run even beside a clean one).

What this does NOT establish: that an agent follows the documentation
(Check 39 in tools/test_contracts.sh pins the prose), or the persistent-LSP
``lean_verify`` staleness itself (needs a version-pinned leanclient harness;
belongs upstream).

Requirements: ``lake``/``lean`` on PATH (elan resolves the fixture's
``lean-toolchain``), Python 3.11+ (the transaction helper's floor). A missing
toolchain is a hard FAILURE of this suite, never a skip — CI provisions it.

Run:  python3 plugins/lean4/tests/integration/test_lean_file_gate.py -v
"""

from __future__ import annotations

import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from dataclasses import dataclass, field

_HERE = os.path.dirname(os.path.abspath(__file__))
_PLUGIN = os.path.dirname(os.path.dirname(_HERE))  # plugins/lean4
FIXTURE = os.path.join(_PLUGIN, "tests", "fixtures", "lean_file_gate")
TXN = os.path.join(_PLUGIN, "lib", "scripts", "disprove_artifact_txn.py")

# The whitelist /disprove's Prime Directive allows (without the native_decide
# opt-in, which is out of scope here).
WHITELIST = frozenset({"propext", "Classical.choice", "Quot.sound"})

# Modern Lean 4 `#print axioms` output (the pinned toolchain's format).
_DEPENDS = re.compile(
    r"^'(?P<name>[^']+)' depends on axioms: \[(?P<axioms>[^\]]*)\]\s*$"
)
_NO_AXIOMS = re.compile(r"^'(?P<name>[^']+)' does not depend on any axioms\s*$")
# Anything that starts like a record but did not fully match one of the two
# well-formed shapes above is MALFORMED evidence for that declaration.
_RECORD_PREFIX = re.compile(r"^'(?P<name>[^']+)' (?:depends on axioms|does not depend)")
# A printed axiom entry: a (possibly dotted) Lean name, e.g. `Classical.choice`.
_LEAN_NAME = re.compile(r"^[A-Za-z_«][^\s,\[\]]*$")

TIMEOUT = 600  # seconds per lake invocation; generous for a cold toolchain


# ---------------------------------------------------------------------------
# Certification helper (test-support code; deliberately NOT a production module)
# ---------------------------------------------------------------------------


def parse_axiom_records(text: str) -> list[tuple[str, frozenset[str] | None]]:
    """Return every `#print axioms` record as (name, axiom set | None).

    An explicit "does not depend on any axioms" is an affirmative EMPTY set.
    A line that STARTS like a record for some declaration but is not a
    complete, well-formed one — truncated list, empty/blank entries such as
    ``[,]`` or ``[]``, an entry that is not a Lean name — is returned as
    ``(name, None)``: MALFORMED evidence for that declaration, never silently
    dropped. Lines that do not look like records at all are ignored.
    """
    records: list[tuple[str, frozenset[str] | None]] = []
    for raw in text.splitlines():
        line = raw.strip()
        m = _NO_AXIOMS.match(line)
        if m:
            records.append((m.group("name"), frozenset()))
            continue
        m = _DEPENDS.match(line)
        if m:
            entries = [a.strip() for a in m.group("axioms").split(",")]
            if entries and all(_LEAN_NAME.match(a) for a in entries):
                records.append((m.group("name"), frozenset(entries)))
            else:
                records.append((m.group("name"), None))
            continue
        m = _RECORD_PREFIX.match(line)
        if m:
            records.append((m.group("name"), None))
    return records


@dataclass(frozen=True)
class Verdict:
    """Outcome of one certification run.

    ``status`` is one of: certified, rejected-axioms, compile-failed,
    inconclusive. Only ``certified`` licenses REFUTED.
    """

    status: str
    reason: str
    axioms: frozenset[str] | None
    records: list[tuple[str, frozenset[str] | None]] = field(default_factory=list)


def decide(
    returncode: int,
    output: str,
    expected_decl: str,
    allowed: frozenset[str] = WHITELIST,
) -> Verdict:
    """The certification decision: a CONJUNCTION, never exit status alone.

    ``expected_decl`` is the fully qualified identity the fixture EXPECTS
    (e.g. ``ProbeNs.T_counterexample``). It is supplied by the test, never
    derived from whatever the probe printed — so a probe that inspects the
    wrong declaration cannot silently update its own expected answer.
    """
    records = parse_axiom_records(output)
    if returncode != 0:
        return Verdict("compile-failed", f"exit {returncode}", None, records)
    mine = [ax for name, ax in records if name == expected_decl]
    if not mine:
        seen = sorted({name for name, _ in records})
        return Verdict(
            "inconclusive",
            f"no #print axioms record for {expected_decl!r} (saw {seen})",
            None,
            records,
        )
    if any(ax is None for ax in mine):
        # Malformed evidence for the expected declaration poisons the run even
        # when a complete clean record is also present.
        return Verdict(
            "inconclusive",
            f"malformed #print axioms record for {expected_decl!r}",
            None,
            records,
        )
    sets = {ax for ax in mine if ax is not None}
    if len(sets) > 1:
        # Identical duplicates are one consistent axiom set; differing sets
        # for the same declaration are conflicting evidence.
        return Verdict(
            "inconclusive",
            f"conflicting axiom records for {expected_decl!r}: {[sorted(s) for s in sets]}",
            None,
            records,
        )
    axioms = next(iter(sets))
    forbidden = axioms - allowed
    if forbidden:
        return Verdict(
            "rejected-axioms", f"forbidden axioms {sorted(forbidden)}", axioms, records
        )
    return Verdict("certified", "ok", axioms, records)


# ---------------------------------------------------------------------------
# Fixture project driver
# ---------------------------------------------------------------------------


@dataclass
class Run:
    argv: list[str]
    returncode: int
    stdout: str
    stderr: str

    @property
    def output(self) -> str:
        return self.stdout + "\n" + self.stderr

    def describe(self) -> str:
        return (
            f"$ {' '.join(self.argv)}\n"
            f"exit={self.returncode}\n--- stdout ---\n{self.stdout}\n--- stderr ---\n{self.stderr}"
        )


class Project:
    """A private copy of the fixture project in a temporary directory."""

    def __init__(self, root: str) -> None:
        self.root = root
        self.log: list[Run] = []

    # -- filesystem --------------------------------------------------------
    def path(self, rel: str) -> str:
        return os.path.join(self.root, rel)

    def read(self, rel: str) -> str:
        with open(self.path(rel), encoding="utf-8") as f:
            return f.read()

    def write(self, rel: str, text: str) -> None:
        os.makedirs(os.path.dirname(self.path(rel)) or self.root, exist_ok=True)
        with open(self.path(rel), "w", encoding="utf-8") as f:
            f.write(text)

    def olean(self, module: str) -> str:
        """Path of a module's .olean under Lake's build dir (may not exist)."""
        return self.path(
            os.path.join(".lake", "build", "lib", "lean", *module.split(".")) + ".olean"
        )

    def sha(self, abs_path: str) -> str | None:
        if not os.path.exists(abs_path):
            return None
        with open(abs_path, "rb") as f:
            return hashlib.sha256(f.read()).hexdigest()

    # -- processes ---------------------------------------------------------
    def run(self, argv: list[str], *, stdin: str = "", timeout: float = TIMEOUT) -> Run:
        try:
            proc = subprocess.run(
                argv,
                cwd=self.root,
                input=stdin,
                capture_output=True,
                text=True,
                timeout=timeout,
                check=False,
            )
        except subprocess.TimeoutExpired as exc:
            # Record the attempt (with whatever partial output exists) BEFORE
            # propagating, so COMMANDS.log shows the command that hung.
            def _txt(b: object) -> str:
                return (
                    b.decode("utf-8", "replace")
                    if isinstance(b, bytes)
                    else str(b or "")
                )

            self.log.append(
                Run(
                    argv,
                    -1,
                    _txt(exc.stdout),
                    _txt(exc.stderr) + f"\n[TIMEOUT after {timeout}s]",
                )
            )
            raise
        r = Run(argv, proc.returncode, proc.stdout, proc.stderr)
        self.log.append(r)
        return r

    def lake_env_lean(self, rel: str) -> Run:
        return self.run(["lake", "env", "lean", rel])

    def lake_lean(self, rel: str) -> Run:
        return self.run(["lake", "lean", rel])

    def lake_build(self, target: str) -> Run:
        return self.run(["lake", "build", target])

    # -- the real transaction helper --------------------------------------
    def txn_begin(self) -> str:
        r = self.run([sys.executable, TXN, "begin"])
        assert r.returncode == 0, r.describe()
        return r.stdout.strip()

    def txn_append(self, rel: str, txn: str, role: str, decl: str, body: str) -> Run:
        return self.run(
            [
                sys.executable,
                TXN,
                "append",
                "--scope-file",
                rel,
                "--txn",
                txn,
                "--role",
                role,
                "--decl",
                decl,
            ],
            stdin=body,
        )

    def txn_drop_gate(self, rel: str, txn: str) -> Run:
        return self.run(
            [
                sys.executable,
                TXN,
                "drop-role",
                "--scope-file",
                rel,
                "--txn",
                txn,
                "--role",
                "gate",
            ]
        )

    def txn_rollback(self, rel: str, txn: str) -> Run:
        return self.run(
            [sys.executable, TXN, "rollback", "--scope-file", rel, "--txn", txn]
        )

    # -- the documented certification sequence -----------------------------
    def certify(self, rel: str, expected_decl: str) -> tuple[Run, Verdict]:
        """One fresh `lake lean` run on the resolved target file, and the
        verdict read from THAT run's output for the expected declaration."""
        r = self.lake_lean(rel)
        return r, decide(r.returncode, r.output, expected_decl)

    def context(self, *files: str) -> str:
        """Diagnostic dump for assertion messages: last runs + source state."""
        parts = [r.describe() for r in self.log[-3:]]
        for rel in files:
            try:
                parts.append(f"--- {rel} ---\n{self.read(rel)}")
            except OSError as exc:
                parts.append(f"--- {rel}: {exc}")
        return "\n\n".join(parts)


class LeanFileGateCase(unittest.TestCase):
    """Base: hard-fails without a toolchain; each test gets a fresh project."""

    toolchain_ok = False

    @classmethod
    def setUpClass(cls) -> None:
        if not os.path.isdir(FIXTURE):
            raise AssertionError(f"fixture missing: {FIXTURE}")
        if not os.path.isfile(TXN):
            raise AssertionError(f"transaction helper missing: {TXN}")
        if shutil.which("lake") is None or shutil.which("lean") is None:
            raise AssertionError(
                "lake/lean not on PATH — this suite requires the pinned Lean "
                "toolchain (see the fixture's lean-toolchain); it never skips"
            )
        if sys.version_info < (3, 11):
            raise AssertionError("Python 3.11+ required (transaction helper floor)")

    def _new_project(self) -> None:
        """Create the private fixture copy and register export-or-cleanup.

        Registered via addCleanup BEFORE the baseline build so it also runs
        when setUp itself fails (unittest skips tearDown in that case) — a
        failed baseline must still be exported for diagnosis.
        """
        self._tmp = tempfile.mkdtemp(prefix="lean_file_gate.")
        self.p = Project(os.path.join(self._tmp, "proj"))
        shutil.copytree(FIXTURE, self.p.root)
        self.addCleanup(self._export_or_cleanup)

    def setUp(self) -> None:
        self._new_project()
        # A successful BASELINE build first, so later negative controls are
        # attributable to the fixture change, not to a broken setup.
        r = self.p.lake_build("Gate.B")
        self.assertEqual(r.returncode, 0, "baseline build failed:\n" + r.describe())
        self.assertTrue(
            os.path.exists(self.p.olean("Gate.B")), "baseline produced no Gate.B .olean"
        )

    def _failed(self) -> bool:
        # Called from a cleanup. unittest runs each cleanup inside its own
        # testPartExecutor, which RESETS `_Outcome.success` to True for the
        # duration of the cleanup — so that flag is useless here. The result
        # lists are reliable: setUp / body / tearDown failures are recorded on
        # the result immediately (before cleanups run).
        outcome = getattr(self, "_outcome", None)
        result = getattr(outcome, "result", None)
        if result is None:
            return False
        recorded = list(getattr(result, "failures", [])) + list(
            getattr(result, "errors", [])
        )
        return any(t is self for t, _ in recorded)

    def _export_or_cleanup(self) -> None:
        """Export the project on failure (CI) or keep/delete it (local)."""
        failed = self._failed()
        keep_dir = os.environ.get("LEAN_FILE_GATE_KEEP_DIR")
        if failed and keep_dir:
            # CI: export the failing project (sources AND .lake artifacts —
            # the artifact state is part of the evidence) plus a transcript
            # of every command run (timed-out ones included), so the failure
            # survives the runner.
            dest = os.path.join(keep_dir, self.id().replace(".", "_"))
            shutil.copytree(self.p.root, dest, dirs_exist_ok=True)
            with open(os.path.join(dest, "COMMANDS.log"), "w", encoding="utf-8") as f:
                f.write("\n\n".join(r.describe() for r in self.p.log))
            sys.stderr.write(f"[lean_file_gate] exported failing project to {dest}\n")
            shutil.rmtree(self._tmp, ignore_errors=True)
        elif failed and os.environ.get("LEAN_FILE_GATE_KEEP", "1") == "1":
            sys.stderr.write(
                f"[lean_file_gate] kept failing project at {self.p.root}\n"
            )
        else:
            shutil.rmtree(self._tmp, ignore_errors=True)

    # helpers
    def assertExit(self, r: Run, code: int, why: str, *files: str) -> None:  # noqa: N802
        self.assertEqual(r.returncode, code, f"{why}\n{self.p.context(*files)}")

    def assertNotExit(self, r: Run, code: int, why: str, *files: str) -> None:  # noqa: N802
        self.assertNotEqual(r.returncode, code, f"{why}\n{self.p.context(*files)}")

    def assertRestored(self, actual: str, baseline: str) -> None:  # noqa: N802
        """Source after rollback == baseline, modulo the helper's separator.

        The transaction helper inserts one blank line before a block and
        excises only the marker-delimited block on rollback, so a rolled-back
        file may legitimately end with extra newlines. Nothing else may differ:
        the baseline must be an exact prefix and the remainder pure newlines.
        """
        self.assertTrue(
            actual.startswith(baseline),
            "rollback changed content before the appended blocks:\n" + self.p.context(),
        )
        tail = actual[len(baseline) :]
        self.assertEqual(
            tail.strip("\n"),
            "",
            f"rollback left non-separator material behind: {tail!r}\n{self.p.context()}",
        )


# ---------------------------------------------------------------------------
# 0. Toolchain identity
# ---------------------------------------------------------------------------


class T0Toolchain(LeanFileGateCase):
    def test_pinned_toolchain_is_the_one_running(self) -> None:
        want = self.p.read("lean-toolchain").strip()  # leanprover/lean4:v4.33.1
        version = want.rsplit(":v", 1)[-1]
        r = self.p.run(["lean", "--version"])
        self.assertExit(r, 0, "lean --version failed")
        self.assertIn(
            version,
            r.stdout,
            f"expected Lean {version} per lean-toolchain:\n{r.describe()}",
        )
        r = self.p.run(["lake", "--version"])
        self.assertExit(r, 0, "lake --version failed")
        self.assertIn(version, r.stdout, r.describe())


# ---------------------------------------------------------------------------
# 1. Stale-import checks (transitive: B → Middle → A)
# ---------------------------------------------------------------------------


class T1StaleImport(LeanFileGateCase):
    A = "Gate/A.lean"
    B = "Gate/B.lean"

    def _set_value(self, n: int) -> None:
        self.p.write(
            self.A,
            f"def Gate.value : Nat := {n}\n\ntheorem Gate.fact : (0 : Nat) ≠ 1 := by decide\n",
        )

    def test_false_pass_then_lake_lean_catches_it(self) -> None:
        self._set_value(2)  # A's source now contradicts B; A's .olean is stale
        r = self.p.lake_env_lean(self.B)
        self.assertExit(
            r,
            0,
            "EXPECTED NEGATIVE CONTROL: lake env lean should false-pass against the stale import",
            self.A,
            self.B,
        )
        r = self.p.lake_lean(self.B)
        self.assertNotExit(
            r, 0, "lake lean must rebuild A (transitively) and reject B", self.A, self.B
        )
        self.assertIn(
            "B.lean",
            r.output,
            "failure must be attributed to the fixture target:\n" + r.describe(),
        )

    def test_false_failure_then_lake_lean_accepts(self) -> None:
        self._set_value(2)
        self.assertExit(self.p.lake_build("Gate.A"), 0, "building the value=2 import")
        self._set_value(1)  # source back to truth; the built import still says 2
        r = self.p.lake_env_lean(self.B)
        self.assertNotExit(
            r,
            0,
            "EXPECTED NEGATIVE CONTROL: lake env lean should false-FAIL against the stale import",
            self.A,
            self.B,
        )
        r = self.p.lake_lean(self.B)
        self.assertExit(
            r, 0, "lake lean must rebuild A and accept B again", self.A, self.B
        )


# ---------------------------------------------------------------------------
# 2. Same-type axiom changes in an import
# ---------------------------------------------------------------------------


class T2SameTypeAxiomChange(LeanFileGateCase):
    A = "Gate/A.lean"
    T = "Target.lean"  # scratch target outside every lean_lib
    DECL = "T_counterexample"

    def setUp(self) -> None:
        super().setUp()
        self.p.write(
            self.T,
            "import Gate.A\n\ntheorem T_counterexample : (0 : Nat) ≠ 1 := Gate.fact\n#print axioms T_counterexample\n",
        )

    def _fact(self, proof: str, prelude: str = "") -> None:
        self.p.write(
            self.A,
            f"def Gate.value : Nat := 1\n{prelude}\ntheorem Gate.fact : (0 : Nat) ≠ 1 := {proof}\n",
        )

    def test_sorry_in_import_is_seen_by_same_run_probe_and_exit_is_zero(self) -> None:
        r, v = self.p.certify(self.T, self.DECL)
        self.assertEqual(v.status, "certified", f"clean baseline: {v}\n{r.describe()}")
        self._fact("by\n  sorry")
        r, v = self.p.certify(self.T, self.DECL)
        # The load-bearing assertion: exit status alone would LICENSE this.
        self.assertExit(
            r,
            0,
            "dirty import still elaborates (exit 0) — the probe, not the exit code, must decide",
            self.A,
            self.T,
        )
        self.assertEqual(v.status, "rejected-axioms", f"{v}\n{r.describe()}")
        assert v.axioms is not None
        self.assertIn("sorryAx", v.axioms)
        # Reverse transition: a fresh run drops the obsolete dependency.
        self._fact("by decide")
        r, v = self.p.certify(self.T, self.DECL)
        self.assertEqual(v.status, "certified", f"{v}\n{r.describe()}")
        self.assertEqual(v.axioms, frozenset())

    def test_custom_axiom_in_import_is_seen(self) -> None:
        self._fact("Gate.bad", prelude="axiom Gate.bad : (0 : Nat) ≠ 1\n")
        r, v = self.p.certify(self.T, self.DECL)
        self.assertExit(r, 0, "custom-axiom import still elaborates", self.A, self.T)
        self.assertEqual(v.status, "rejected-axioms", f"{v}\n{r.describe()}")
        assert v.axioms is not None
        self.assertIn("Gate.bad", v.axioms)
        self.assertNotIn("sorryAx", v.axioms, "must not be a sorryAx-only special case")


# ---------------------------------------------------------------------------
# 3. Namespace collision with an imported clean decoy
# ---------------------------------------------------------------------------


class T3NamespaceCollision(LeanFileGateCase):
    T = "Target.lean"
    HEADER = "import Gate.Decoys\n\naxiom regressionBad : False\n\nnamespace ProbeNs\n-- Deliberately no `end ProbeNs`.\n"

    def setUp(self) -> None:
        super().setUp()
        self.p.write(self.T, self.HEADER)
        self.txn = self.p.txn_begin()

    def test_unqualified_probe_inspects_appended_decl_root_probe_inspects_decoy(
        self,
    ) -> None:
        r = self.p.txn_append(
            self.T,
            self.txn,
            "artifact",
            "T_counterexample",
            "theorem T_counterexample : ¬ True :=\n  fun _ => regressionBad",
        )
        self.assertExit(r, 0, "append artifact", self.T)
        r = self.p.txn_append(
            self.T,
            self.txn,
            "gate",
            "T_counterexample_axioms",
            "#print axioms T_counterexample",
        )
        self.assertExit(r, 0, "append production probe", self.T)
        # Expected identity is DECLARED here, not read back from the probe.
        r, v = self.p.certify(self.T, "ProbeNs.T_counterexample")
        self.assertExit(r, 0, "target elaborates", self.T)
        self.assertEqual(v.status, "rejected-axioms", f"{v}\n{r.describe()}")
        assert v.axioms is not None
        self.assertIn("regressionBad", v.axioms)
        # Negative control: the root-qualified spelling inspects the DECOY and
        # reports it clean — exactly why production forbids `_root_.` here.
        r = self.p.txn_append(
            self.T,
            self.txn,
            "gate",
            "root_probe",
            "#print axioms _root_.T_counterexample",
        )
        self.assertExit(r, 0, "append root-qualified probe (control)", self.T)
        r = self.p.lake_lean(self.T)
        self.assertExit(r, 0, "control run", self.T)
        recs = dict(parse_axiom_records(r.output))
        self.assertEqual(
            recs.get("T_counterexample"),
            frozenset(),
            f"root probe must report the clean decoy:\n{r.describe()}",
        )
        self.assertIn(
            "regressionBad", recs.get("ProbeNs.T_counterexample", frozenset())
        )
        # Deciding for the appended decl still rejects; deciding for the decoy
        # name would "certify" — the identity must come from the fixture.
        self.assertEqual(
            decide(r.returncode, r.output, "ProbeNs.T_counterexample").status,
            "rejected-axioms",
        )
        self.assertEqual(
            decide(r.returncode, r.output, "T_counterexample").status, "certified"
        )

    def test_witness_shape_audits_the_wrapper_not_the_witness(self) -> None:
        witness = (
            "theorem T_counterexample : ∃ n : Nat, ¬ (n < 10) :=\n  ⟨10, by decide⟩"
        )
        wrapper = (
            "theorem T_counterexample_negates_target : ¬ (∀ n : Nat, n < 10) :=\n"
            "  fun _ => regressionBad"  # deliberately dirty wrapper, clean witness
        )
        self.assertExit(
            self.p.txn_append(
                self.T, self.txn, "artifact", "T_counterexample", witness
            ),
            0,
            "append witness",
            self.T,
        )
        self.assertExit(
            self.p.txn_append(
                self.T, self.txn, "gate", "T_counterexample_negates_target", wrapper
            ),
            0,
            "append wrapper",
            self.T,
        )
        self.assertExit(
            self.p.txn_append(
                self.T,
                self.txn,
                "gate",
                "T_counterexample_axioms",
                "#print axioms T_counterexample_negates_target",
            ),
            0,
            "append probe",
            self.T,
        )
        # Also probe the witness so both records are in one run.
        self.assertExit(
            self.p.txn_append(
                self.T,
                self.txn,
                "gate",
                "witness_probe",
                "#print axioms T_counterexample",
            ),
            0,
            "append witness probe",
            self.T,
        )
        r = self.p.lake_lean(self.T)
        self.assertExit(r, 0, "target elaborates", self.T)
        self.assertEqual(
            decide(
                r.returncode, r.output, "ProbeNs.T_counterexample_negates_target"
            ).status,
            "rejected-axioms",
            r.describe(),
        )
        self.assertEqual(
            decide(r.returncode, r.output, "ProbeNs.T_counterexample").status,
            "certified",
            "auditing the witness instead would mislead:\n" + r.describe(),
        )
        # Decoy control for the wrapper name as well.
        self.assertExit(
            self.p.txn_append(
                self.T,
                self.txn,
                "gate",
                "root_probe",
                "#print axioms _root_.T_counterexample_negates_target",
            ),
            0,
            "append root probe",
            self.T,
        )
        r = self.p.lake_lean(self.T)
        self.assertExit(r, 0, "control run", self.T)
        self.assertEqual(
            dict(parse_axiom_records(r.output)).get("T_counterexample_negates_target"),
            frozenset(),
            r.describe(),
        )


# ---------------------------------------------------------------------------
# 4. Accepted target layouts + 5. Target-artifact isolation
# ---------------------------------------------------------------------------


class T4Layouts(LeanFileGateCase):
    def _stale_a(self) -> None:
        self.p.write(
            "Gate/A.lean",
            "def Gate.value : Nat := 2\n\ntheorem Gate.fact : (0 : Nat) ≠ 1 := by decide\n",
        )

    def test_ordinary_module_by_source_path(self) -> None:
        self.assertExit(self.p.lake_lean("Gate/B.lean"), 0, "ordinary module")
        self._stale_a()
        self.assertNotExit(
            self.p.lake_lean("Gate/B.lean"),
            0,
            "stale import must be rebuilt and rejected",
        )

    def test_custom_srcdir_module_by_source_path(self) -> None:
        self.assertExit(
            self.p.lake_lean("src/Custom/Inner.lean"), 0, "custom srcDir module"
        )
        # Target-spelling control while the project is still VALID, so the
        # failure below is attributable to the target name, not to a false
        # theorem: the real module name builds, the hand-derived one does not.
        self.assertExit(self.p.lake_build("Custom.Inner"), 0, "real module name builds")
        r = self.p.lake_build("src.Custom.Inner")
        self.assertNotExit(r, 0, "naive / -> . derivation must fail")
        self.assertIn(
            "unknown",
            r.output.lower(),
            "failure must be an unresolved target, not a build error:\n" + r.describe(),
        )
        self._stale_a()
        self.assertNotExit(
            self.p.lake_lean("src/Custom/Inner.lean"),
            0,
            "stale import through custom srcDir",
        )

    def test_scratch_file_outside_every_lib(self) -> None:
        self.p.write(
            "Scratch.lean",
            "import Gate.A\n\ntheorem scratch_ok : Gate.value = 1 := rfl\n",
        )
        self.assertExit(
            self.p.lake_lean("Scratch.lean"), 0, "scratch file via lake lean"
        )
        self.assertNotExit(
            self.p.lake_build("Scratch.lean"),
            0,
            "a targeted lake build cannot address a non-module file",
        )
        self._stale_a()
        self.assertNotExit(
            self.p.lake_lean("Scratch.lean"), 0, "scratch file sees the rebuilt import"
        )


class T5ArtifactIsolation(LeanFileGateCase):
    def test_lake_lean_does_not_write_target_olean_but_may_rebuild_imports(
        self,
    ) -> None:
        b_olean = self.p.olean("Gate.B")
        a_olean = self.p.olean("Gate.A")
        b0, a0 = self.p.sha(b_olean), self.p.sha(a_olean)
        self.p.write(
            "Gate/B.lean",
            self.p.read("Gate/B.lean") + "\ntheorem extra : True := True.intro\n",
        )
        self.p.write(
            "Gate/A.lean",
            "def Gate.value : Nat := 1\n\ntheorem Gate.fact : (0 : Nat) ≠ 1 := by decide\n-- touched\n",
        )
        self.assertExit(self.p.lake_lean("Gate/B.lean"), 0, "lake lean")
        self.assertEqual(
            self.p.sha(b_olean), b0, "lake lean must not overwrite the TARGET's .olean"
        )
        self.assertNotEqual(
            self.p.sha(a_olean), a0, "imports MAY be rebuilt by lake lean"
        )
        # A targeted lake build DOES write the target's artifact (the leak).
        self.assertExit(self.p.lake_build("Gate/B.lean"), 0, "targeted build")
        self.assertNotEqual(
            self.p.sha(b_olean), b0, "targeted lake build rewrites the target .olean"
        )

    def test_unbuilt_target_stays_unbuilt(self) -> None:
        self.p.write(
            "Scratch.lean",
            "import Gate.A\n\ntheorem scratch_ok : Gate.value = 1 := rfl\n#print axioms scratch_ok\n",
        )
        r, v = self.p.certify("Scratch.lean", "scratch_ok")
        self.assertEqual(v.status, "certified", f"{v}\n{r.describe()}")
        self.assertIsNone(
            self.p.sha(self.p.olean("Scratch")),
            "lake lean created a target .olean for a scratch file",
        )
        self.assertFalse(
            any(
                n.endswith("Scratch.olean")
                for _, _, fs in os.walk(self.p.path(".lake"))
                for n in fs
            ),
            "no Scratch.olean anywhere under .lake",
        )


# ---------------------------------------------------------------------------
# 6. Rejection and rollback
# ---------------------------------------------------------------------------


class T6RejectionRollback(LeanFileGateCase):
    B = "Gate/B.lean"
    CONSUMER = "Consumer.lean"

    def setUp(self) -> None:
        super().setUp()
        # Put the forbidden axiom in the target itself so a candidate can use it.
        self.p.write(self.B, self.p.read(self.B) + "\naxiom regressionBad : False\n")
        self.assertExit(
            self.p.lake_build("Gate.B"), 0, "rebuild baseline with the axiom present"
        )
        self.baseline_src = self.p.read(self.B)
        self.baseline_olean = self.p.sha(self.p.olean("Gate.B"))
        self.p.write(self.CONSUMER, "import Gate.B\n#check T_counterexample\n")
        self.txn = self.p.txn_begin()

    def _consumer_sees_candidate(self) -> bool:
        # lake env lean on purpose: we are inspecting the ARTIFACT state.
        return self.p.lake_env_lean(self.CONSUMER).returncode == 0

    def test_forbidden_axiom_candidate_is_rolled_back_without_artifact_leak(
        self,
    ) -> None:
        self.assertFalse(
            self._consumer_sees_candidate(),
            "precondition: consumer must not see the candidate yet",
        )
        self.assertExit(
            self.p.txn_append(
                self.B,
                self.txn,
                "artifact",
                "T_counterexample",
                "theorem T_counterexample : ¬ True := fun _ => regressionBad",
            ),
            0,
            "append",
        )
        self.assertExit(
            self.p.txn_append(
                self.B,
                self.txn,
                "gate",
                "T_counterexample_axioms",
                "#print axioms T_counterexample",
            ),
            0,
            "append probe",
        )
        r, v = self.p.certify(self.B, "T_counterexample")
        self.assertEqual(v.status, "rejected-axioms", f"{v}\n{r.describe()}")
        self.assertExit(self.p.txn_rollback(self.B, self.txn), 0, "rollback", self.B)
        self.assertRestored(self.p.read(self.B), self.baseline_src)
        self.assertEqual(
            self.p.sha(self.p.olean("Gate.B")),
            self.baseline_olean,
            "target .olean must be byte-identical (lake lean wrote nothing)",
        )
        self.assertFalse(
            self._consumer_sees_candidate(),
            "temporary declaration leaked into the target artifact",
        )

    def test_targeted_build_control_does_leak(self) -> None:
        # Paired negative control: the sequence #195 REPLACED leaks the candidate.
        self.assertExit(
            self.p.txn_append(
                self.B,
                self.txn,
                "artifact",
                "T_counterexample",
                "theorem T_counterexample : ¬ True := fun _ => regressionBad",
            ),
            0,
            "append",
        )
        self.assertExit(
            self.p.lake_build("Gate/B.lean"),
            0,
            "targeted build with the candidate present",
        )
        self.assertExit(
            self.p.txn_rollback(self.B, self.txn), 0, "source-only rollback"
        )
        self.assertRestored(self.p.read(self.B), self.baseline_src)
        self.assertNotEqual(
            self.p.sha(self.p.olean("Gate.B")),
            self.baseline_olean,
            "control: the targeted build rewrote the artifact",
        )
        self.assertTrue(
            self._consumer_sees_candidate(),
            "control: consumer still sees the rolled-back candidate via the stale .olean",
        )

    def test_compile_failure_candidate_is_rolled_back(self) -> None:
        self.assertExit(
            self.p.txn_append(
                self.B,
                self.txn,
                "artifact",
                "T_counterexample",
                "theorem T_counterexample : ¬ True := fun h => h",
            ),
            0,
            "append",
        )
        self.assertExit(
            self.p.txn_append(
                self.B,
                self.txn,
                "gate",
                "T_counterexample_axioms",
                "#print axioms T_counterexample",
            ),
            0,
            "append probe",
        )
        r, v = self.p.certify(self.B, "T_counterexample")
        self.assertEqual(v.status, "compile-failed", f"{v}\n{r.describe()}")
        self.assertIn(
            "B.lean", r.output, "failure attributed to the target:\n" + r.describe()
        )
        self.assertExit(self.p.txn_rollback(self.B, self.txn), 0, "rollback", self.B)
        self.assertRestored(self.p.read(self.B), self.baseline_src)
        self.assertEqual(self.p.sha(self.p.olean("Gate.B")), self.baseline_olean)


# ---------------------------------------------------------------------------
# 7. Successful cleanup
# ---------------------------------------------------------------------------


class T7Success(LeanFileGateCase):
    B = "Gate/B.lean"

    def _finish(self, txn: str, artifact_body: str, expected_decl: str) -> None:
        self.assertExit(
            self.p.txn_drop_gate(self.B, txn), 0, "drop gate blocks", self.B
        )
        src = self.p.read(self.B)
        self.assertNotIn("#print axioms", src)
        self.assertNotIn("role=gate", src)
        self.assertIn(artifact_body, src)
        # Exact contribution: baseline + one artifact block, per the helper's
        # separator convention (blank line, begin marker, body, end marker).
        self.assertTrue(
            src.startswith(self.baseline), "baseline prefix must be untouched"
        )
        tail = src[len(self.baseline) :]
        self.assertEqual(tail.count("lean4:disprove-begin"), 1)
        self.assertEqual(tail.count("lean4:disprove-end"), 1)
        # Gate-free recheck (the documented second run).
        r, v = self.p.certify(self.B, expected_decl)
        self.assertEqual(
            v.status,
            "inconclusive",
            "no probe remains, so the recheck is compile-only: " + str(v),
        )
        self.assertExit(r, 0, "gate-free file must elaborate", self.B)
        # Module variant: an explicit build, then a consumer uses the artifact.
        self.assertExit(
            self.p.lake_build("Gate/B.lean"),
            0,
            "explicit module build after certification",
        )
        self.p.write("Consumer.lean", f"import Gate.B\n#check {expected_decl}\n")
        self.assertExit(
            self.p.lake_env_lean("Consumer.lean"),
            0,
            "consumer can use the surviving artifact",
            "Consumer.lean",
        )

    def setUp(self) -> None:
        super().setUp()
        self.baseline = self.p.read(self.B)

    def test_direct_shape(self) -> None:
        txn = self.p.txn_begin()
        body = "theorem T_counterexample : ¬ (∀ n : Nat, n < 10) :=\n  fun h => absurd (h 10) (by decide)"
        self.assertExit(
            self.p.txn_append(self.B, txn, "artifact", "T_counterexample", body),
            0,
            "append",
        )
        self.assertExit(
            self.p.txn_append(
                self.B,
                txn,
                "gate",
                "T_counterexample_axioms",
                "#print axioms T_counterexample",
            ),
            0,
            "append probe",
        )
        r, v = self.p.certify(self.B, "T_counterexample")
        self.assertEqual(v.status, "certified", f"{v}\n{r.describe()}")
        self._finish(txn, body, "T_counterexample")

    def test_witness_shape(self) -> None:
        txn = self.p.txn_begin()
        witness = (
            "theorem T_counterexample : ∃ n : Nat, ¬ (n < 10) :=\n  ⟨10, by decide⟩"
        )
        wrapper = (
            "theorem T_counterexample_negates_target :\n    ¬ (∀ n : Nat, n < 10) :=\n"
            "  fun h =>\n    Exists.elim T_counterexample (fun n hn => hn (h n))"
        )
        self.assertExit(
            self.p.txn_append(self.B, txn, "artifact", "T_counterexample", witness),
            0,
            "append witness",
        )
        self.assertExit(
            self.p.txn_append(
                self.B, txn, "gate", "T_counterexample_negates_target", wrapper
            ),
            0,
            "append wrapper",
        )
        self.assertExit(
            self.p.txn_append(
                self.B,
                txn,
                "gate",
                "T_counterexample_axioms",
                "#print axioms T_counterexample_negates_target",
            ),
            0,
            "append probe",
        )
        r, v = self.p.certify(self.B, "T_counterexample_negates_target")
        self.assertEqual(v.status, "certified", f"{v}\n{r.describe()}")
        self._finish(txn, witness, "T_counterexample")
        self.assertNotIn(
            "T_counterexample_negates_target",
            self.p.read(self.B),
            "wrapper must be gone",
        )


# ---------------------------------------------------------------------------
# 8. Inconclusive evidence (matcher cases; no Lean needed but same harness)
# ---------------------------------------------------------------------------


class T8Matcher(unittest.TestCase):
    OK = "'T_counterexample' does not depend on any axioms\n"
    BAD = "'T_counterexample' depends on axioms: [propext, regressionBad]\n"

    def test_empty_set_is_affirmative(self) -> None:
        self.assertEqual(decide(0, self.OK, "T_counterexample").status, "certified")

    def test_missing_record_is_inconclusive_not_clean(self) -> None:
        v = decide(0, "✔ [2/3] Built Gate.A\n", "T_counterexample")
        self.assertEqual(v.status, "inconclusive")
        self.assertIsNone(v.axioms)

    def test_wrong_declaration_is_inconclusive(self) -> None:
        v = decide(
            0,
            "'ProbeNs.T_counterexample' does not depend on any axioms\n",
            "T_counterexample",
        )
        self.assertEqual(v.status, "inconclusive")

    def test_truncated_record_alongside_a_clean_one_is_inconclusive(self) -> None:
        # A malformed record for the EXPECTED declaration poisons the run even
        # though a complete clean record is also present (review of #198).
        out = self.OK + "'T_counterexample' depends on axioms: [regressionBad,\n"
        v = decide(0, out, "T_counterexample")
        self.assertEqual(v.status, "inconclusive", v)
        self.assertIn("malformed", v.reason)

    def test_empty_or_blank_entries_are_malformed_not_empty_set(self) -> None:
        for bad in (
            "'T_counterexample' depends on axioms: [,]\n",
            "'T_counterexample' depends on axioms: []\n",
            "'T_counterexample' depends on axioms: [propext, ]\n",
            "'T_counterexample' depends on axioms: [propext, not a name]\n",
        ):
            with self.subTest(bad.strip()):
                v = decide(0, bad, "T_counterexample")
                self.assertEqual(v.status, "inconclusive", v)
                self.assertIsNone(v.axioms)

    def test_malformed_record_for_another_declaration_does_not_poison(self) -> None:
        out = self.OK + "'Other' depends on axioms: [regressionBad,\n"
        self.assertEqual(decide(0, out, "T_counterexample").status, "certified")

    def test_truncated_record_is_not_a_record(self) -> None:
        v = decide(
            0, "'T_counterexample' depends on axioms: [propext,\n", "T_counterexample"
        )
        self.assertEqual(v.status, "inconclusive")

    def test_conflicting_records_are_inconclusive(self) -> None:
        v = decide(0, self.OK + self.BAD, "T_counterexample")
        self.assertEqual(v.status, "inconclusive")

    def test_identical_duplicate_records_are_fine(self) -> None:
        self.assertEqual(
            decide(0, self.OK + self.OK, "T_counterexample").status, "certified"
        )

    def test_nonzero_exit_wins_over_a_clean_record(self) -> None:
        self.assertEqual(
            decide(1, self.OK, "T_counterexample").status, "compile-failed"
        )

    def test_forbidden_axiom_rejects_and_whitelist_passes(self) -> None:
        self.assertEqual(
            decide(0, self.BAD, "T_counterexample").status, "rejected-axioms"
        )
        ok = "'T_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        self.assertEqual(decide(0, ok, "T_counterexample").status, "certified")


# ---------------------------------------------------------------------------
# 9. Harness self-checks (no Lean needed): failure evidence must be retained
#    even when setUp fails, and timed-out commands must reach the transcript.
# ---------------------------------------------------------------------------


class T9Harness(unittest.TestCase):
    def test_timed_out_command_is_logged_before_raising(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            p = Project(d)
            with self.assertRaises(subprocess.TimeoutExpired):
                p.run([sys.executable, "-c", "import time; time.sleep(5)"], timeout=0.3)
            self.assertEqual(len(p.log), 1)
            self.assertEqual(p.log[-1].returncode, -1)
            self.assertIn("TIMEOUT after 0.3s", p.log[-1].stderr)
            self.assertIn("time.sleep(5)", p.log[-1].describe())

    def test_setup_failure_is_exported_to_keep_dir(self) -> None:
        # A failed BASELINE (setUp) must still export the project + transcript:
        # unittest does not run tearDown after a setUp failure, so the export
        # is registered with addCleanup inside _new_project().
        class _SetUpFails(LeanFileGateCase):
            @classmethod
            def setUpClass(cls) -> None:  # no toolchain needed for this check
                pass

            def setUp(self) -> None:
                self._new_project()
                self.p.log.append(Run(["lake", "build", "Gate.B"], 1, "", "simulated"))
                raise AssertionError("simulated baseline failure")

            def test_never_runs(self) -> None:
                raise AssertionError("body must not run after a failed setUp")

        with tempfile.TemporaryDirectory() as keep:
            old = os.environ.get("LEAN_FILE_GATE_KEEP_DIR")
            os.environ["LEAN_FILE_GATE_KEEP_DIR"] = keep
            try:
                result = unittest.TestResult()
                _SetUpFails("test_never_runs").run(result)
            finally:
                if old is None:
                    del os.environ["LEAN_FILE_GATE_KEEP_DIR"]
                else:
                    os.environ["LEAN_FILE_GATE_KEEP_DIR"] = old
            self.assertEqual(len(result.failures), 1, result.failures)
            self.assertIn("simulated baseline failure", result.failures[0][1])
            exported = os.listdir(keep)
            self.assertEqual(len(exported), 1, exported)
            dest = os.path.join(keep, exported[0])
            self.assertTrue(os.path.exists(os.path.join(dest, "lakefile.toml")))
            with open(os.path.join(dest, "COMMANDS.log"), encoding="utf-8") as f:
                self.assertIn("lake build Gate.B", f.read())


if __name__ == "__main__":
    unittest.main(verbosity=2)
