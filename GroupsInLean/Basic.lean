import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic
import Paperproof

variable (G : Type) [Group G]

/-- If the square of every element of a group `G` is the identity, then `G` is abelian. -/
lemma comm_of_exponent_two (h : ∀ x : G, x * x = 1) : ∀ x y : G, x * y = y * x := by
  intro x y
  rw [← mul_left_inj (x * y), h (x * y), mul_assoc, ← mul_assoc x x y, h x, one_mul, h y]
