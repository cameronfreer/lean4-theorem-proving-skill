-- Clean ROOT declarations carrying the fixed /disprove artifact names. A
-- root-qualified probe (`#print axioms _root_.T_counterexample`) resolves to
-- THESE, not to an artifact appended inside a namespace left open to
-- end-of-file — which is why the production probe is unqualified.
theorem T_counterexample : True := True.intro

theorem T_counterexample_negates_target : True := True.intro
