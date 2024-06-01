import Mathlib
open Nat (add_assoc add_comm)
open Real

theorem foo (a : Nat) : a + 1 = Nat.succ a := by
  sorry

theorem bar (a b : Nat) : a + b = b + a := by
  rw[add_comm]

theorem abs_val (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  sorry
