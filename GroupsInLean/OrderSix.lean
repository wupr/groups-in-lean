import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Dihedral

variable {G : Type*} [Group G] [Fintype G]

noncomputable example (h1 : Fintype.card G = 6) (h2 : ¬IsCyclic G) :
    G ≃* DihedralGroup 3 := by
  have : (∃ x : G, orderOf x = 3) ∧ (∃ y : G, orderOf y = 2)
  · apply And.intro
    all_goals {
      apply exists_prime_orderOf_dvd_card
      rw [h1]
      norm_num
    }
  choose x hx using this.left
  choose y hy using this.right
  let P := Subgroup.zpowers x
  have : Fintype.card P = 3 := hx ▸ Fintype.card_zpowers
  have : P.Normal := sorry
  -- have : Fintype.card P = 3 ^ (Nat.factorization (Fintype.card G)) 3
  -- · rw [this, h1]
  --   sorry
  -- let P := Sylow.ofCard (p := 3) P this
  have : (y * x * y⁻¹) ∈ P := this.conj_mem x (Subgroup.mem_zpowers x) y
  -- in general, discuss by the multiplicative order of k
  have hP (x' : G) : x' ∈ P → ∃ a < 3, x' = x ^ a
  · rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff]
    intro ⟨k, hk⟩
    rw [← hk]
    use k % 3, Nat.mod_lt k (show 0 < 3 by norm_num1)
    apply pow_eq_pow_mod
    exact hx ▸ pow_orderOf_eq_one x
  choose a ha using hP (y * x * y⁻¹) this
  match a with
  | 0 => {
    simp only [zero_lt_three, pow_zero, true_and] at ha
    rw [mul_inv_eq_one] at ha
    have := self_eq_mul_right.mp ha.symm
    have := orderOf_eq_one_iff.mpr this ▸ hx
    contradiction
  }
  | 1 => {
    absurd h2
    apply isCyclic_of_orderOf_eq_card (y * x)
    rw [h1]
    rw [pow_one] at ha
    have : Nat.Coprime (orderOf y) (orderOf x)
    · rw [hx, hy]
      norm_num1
    have := Commute.orderOf_mul_eq_mul_orderOf_of_coprime (eq_mul_of_mul_inv_eq ha.right) this
    rw [this, hy, hx]
  }
  | 2 => {
    have ha := eq_mul_of_mul_inv_eq ha.right
    sorry
  }
  | n + 3 => {
    have := ha.left
    contradiction
  }

-- #check Sylow.directProductOfNormal

-- tidy up Mathlib.Algebra.BigOperators.Basic
