import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic
import Paperproof

variable (G : Type) [Group G]

/-- If the square of every element of a group `G` is the identity, then `G` is abelian. -/
lemma comm_of_exponent_two (h : ∀ x : G, x * x = 1) : ∀ x y : G, x * y = y * x := by
  intro x y
  rw [← mul_left_inj (x * y), h (x * y), mul_assoc, ← mul_assoc x x y, h x, one_mul, h y]

/-- If a group `G` is finite and of order 4, then $G$ is abelian. -/
lemma comm_of_order_four [Fintype G] (h : Fintype.card G = 4) : ∀ x y : G, x * y = y * x := by
  by_cases h4 : ∃ x : G, orderOf x = 4
  · obtain ⟨x, hx⟩ := h4
    obtain : IsCyclic G := isCyclic_of_orderOf_eq_card x (h ▸ hx)
    obtain : CommGroup G := IsCyclic.commGroup (α := G)
    intro x y
    -- exact mul_comm x y
    sorry
  · push_neg at h4
    sorry
