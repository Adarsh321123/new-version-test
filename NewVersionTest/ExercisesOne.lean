import Mathlib
open Real

theorem example_three_rw (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  -- rw [h] -- rewriting to replace the assumption in the theorem, this changes the current goal
  -- rw [h']
  rw [h, h'] -- simpler
  ring

theorem example_five_rw (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  -- rw [exp_add (a + b) c]  -- exp_add lemma says exp (x + y) = exp x * exp y
  -- rw [exp_add a b]
  -- rw [exp_add, exp_add]  -- Lean rewrites the first matching expression, so we don't
  -- need to provide arguments
  sorry
