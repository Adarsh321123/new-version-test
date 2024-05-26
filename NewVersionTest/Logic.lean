import Mathlib
open Real
open Function

theorem example_one_conjunction (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  tauto

theorem example_seven_existential (a b c : ℤ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  exact h₁.trans h₂
