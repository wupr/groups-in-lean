import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic
import Paperproof

variable {G : Type} [Group G]

/-- If the square of every element of a group `G` is the identity, then `G` is abelian. -/
lemma comm_of_self_mul_eq_one (h : ∀ x : G, x * x = 1) : ∀ x y : G, x * y = y * x := by
  intro x y
  rw [← mul_left_inj (x * y), h (x * y), mul_assoc, ← mul_assoc x x y, h x, one_mul, h y]

/-- If the order of an element `x` in a group divides 2,
    then `x` multiplied with itself is the identity. -/
lemma orderOf_dvd_two_iff_self_mul_eq_one (x : G) : orderOf x ∣ 2 ↔ x * x = 1 :=
  pow_two x ▸ orderOf_dvd_iff_pow_eq_one

/-- If a group `G` is finite and of order 4, then `G` is abelian. -/
lemma comm_of_order_four [Fintype G] (h : Fintype.card G = 4) : ∀ x y : G, x * y = y * x := by
  by_cases h4 : ∃ a : G, orderOf a = 4
  · obtain ⟨a, ha⟩ := h4
    have : IsCyclic G := isCyclic_of_orderOf_eq_card a (h ▸ ha)
    have : CommGroup G := IsCyclic.commGroup (α := G)
    intro x y
    -- exact mul_comm x y
    sorry
  · push_neg at h4
    apply comm_of_self_mul_eq_one
    intro x
    specialize h4 x
    suffices : orderOf x ∣ 2
    · rwa [← orderOf_dvd_two_iff_self_mul_eq_one]
    have : orderOf x ∣ 4 := h ▸ orderOf_dvd_card (x := x)
    rw [← pow_one 2, Nat.dvd_prime_pow Nat.prime_two]
    rw [show 4 = 2 ^ 2 by norm_num1, Nat.dvd_prime_pow Nat.prime_two] at this
    generalize orderOf x = n at *
    obtain ⟨k, hk, rfl⟩ := this
    use k
    revert k
    decide
