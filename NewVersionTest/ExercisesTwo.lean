import Mathlib
open Real

-- Leans writes an implication as → since it sees
-- a proof of P → Q as a function that sends a proof of P to a proof of Q
-- the lemma `sq_pos_of_pos` claims `0 < a → 0 < a^2`
-- so we apply the "function" `sq_pos_of_pos` to the assumption `ha`
theorem example_one_implication (a : ℝ) (ha : 0 < a) : 0 < a^2 := by
  exact sq_pos_of_pos ha  -- assumption is exactly what we need to prove

-- we can also apply backwards reasoning
theorem example_two_implication (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by
  apply sq_pos_of_pos
  apply sq_pos_of_pos
  exact ha  -- this is exactly our assumption ha
