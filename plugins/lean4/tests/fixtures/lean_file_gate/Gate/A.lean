-- The imported module the tests mutate. `Gate.value` changes truth (1 → 2);
-- `Gate.fact` keeps its TYPE while its proof changes (clean → sorry → axiom).
def Gate.value : Nat := 1

theorem Gate.fact : (0 : Nat) ≠ 1 := by decide
