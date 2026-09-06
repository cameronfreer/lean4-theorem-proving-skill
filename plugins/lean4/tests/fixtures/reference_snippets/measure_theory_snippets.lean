-- Compile-check for the exact Lean snippets the references ship (#188 / #162
-- / the #200 reference audit). Requires a Mathlib project; run from one:
--
--   lake env lean /path/to/lean4-skills/plugins/lean4/tests/fixtures/reference_snippets/measure_theory_snippets.lean
--
-- Not wired into CI (CI has no Mathlib). Last checked: Mathlib at Lean
-- 4.34.0-rc1 (local checkout) — see the PR #200 body. If you change one of the
-- documented snippets, change it here too and re-run.
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

open MeasureTheory

-- measure-theory.md § condExpWith: optional σ-finiteness freeze via plain `have`
-- (plain `have` registers the instance; `haveI` would only inline).
example {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) : True := by
  have : SigmaFinite (μ.trim hm) := inferInstance
  trivial

-- measure-theory.md § Set-Integral Projection: the wrapper, with a NAMED ambient
-- space (never `‹_›`, which resolves to `m` itself), `MeasurableSet[m] s`, and the
-- finite-measure assumption that supplies `SigmaFinite (μ.trim hm)`.
lemma setIntegral_condExp_eq {Ω : Type*} [m₀ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {s : Set Ω} (hs : MeasurableSet[m] s) {g : Ω → ℝ} (hg : Integrable g μ) :
    ∫ x in s, (μ[g|m]) x ∂μ = ∫ x in s, g x ∂μ :=
  setIntegral_condExp hm hg hs

-- measure-theory.md § Manual instances: probability pushforward.
example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → β} (hf : AEMeasurable f μ) : True := by
  have : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf
  trivial

-- measure-theory.md lemma list: a.e.-strong measurability of the CE.
example {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}
    {m : MeasurableSpace Ω} {f : Ω → ℝ} : AEStronglyMeasurable[m] (μ[f | m]) μ :=
  stronglyMeasurable_condExp.aestronglyMeasurable

-- lean-phrasebook.md § Goal Manipulation.
example : True ∧ True := by
  constructor
  swap
  all_goals trivial

example : True ∧ True ∧ True := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left 1
  pick_goal 2
  all_goals trivial

-- compilation-errors.md: termination_by (Lean ≥ 4.6 syntax).
def my_rec : Nat → Nat
  | 0 => 0
  | n + 1 => my_rec n
termination_by n => n

-- compilation-errors.md / tactics-reference.md: infer_instance.
example : Nonempty Nat := by infer_instance
