-- import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Sylow

variable {G : Type*} [Group G] [Fintype G]

lemma Subgroup.normal_of_index_eq_two (H : Subgroup G) (h : H.index = 2) : H.Normal where
  conj_mem x hx y := by
    obtain ⟨z, hz⟩ := Subgroup.index_eq_two_iff.mp h
    obtain (hy | hy) := hz y⁻¹
    · obtain (hyxy | hyxy) := hz (y * x * y⁻¹)
      · rw [mul_assoc, mul_mem_cancel_right hy.left, mul_mem_cancel_right hx] at hyxy
        absurd hy.right
        exact inv_mem hyxy.left
      · exact hyxy.left
    · apply Subgroup.mul_mem H _ hy.left
      exact Subgroup.mul_mem H (inv_inv y ▸ Subgroup.inv_mem H hy.left) hx
    -- obtain ⟨z, hz⟩ := Nat.card_eq_two_iff' ((1 : G) : G ⧸ H) |>.mp h
    -- simp at hz

noncomputable example (h1 : Fintype.card G = 6) (h2 : ¬IsCyclic G) :
    DihedralGroup 3 ≃* G := by
  have : (∃ x : G, orderOf x = 3) ∧ (∃ y : G, orderOf y = 2)
  · apply And.intro
    all_goals {
      apply exists_prime_orderOf_dvd_card
      rw [h1]
      norm_num
    }
  choose x hx using this.left
  choose y hy using this.right
  have hx' (i j : ZMod 3) : x ^ ZMod.val i = x ^ ZMod.val j → i = j
  · intro h
    apply Fin.eq_of_val_eq
    rw [pow_eq_pow_iff_modEq, hx,
      show ZMod.val i = Fin.val i by rfl, show ZMod.val j = Fin.val j by rfl] at h
    change Fin.val i % 3 = Fin.val j % 3 at h
    rwa [Nat.mod_eq_of_lt (Fin.prop i), Nat.mod_eq_of_lt (Fin.prop j)] at h
  let P := Subgroup.zpowers x
  have hP_card : Nat.card P = 3 := Nat.card_eq_fintype_card (α := P) ▸ hx ▸ Fintype.card_zpowers
  have hy' (i j : ZMod 3) : y * x ^ (ZMod.val i) ≠ x ^ (ZMod.val j)
  · intro h
    generalize ZMod.val i = i at h ⊢
    generalize ZMod.val j = j at h ⊢
    have h1 : x ^ i ∈ P := Subgroup.npow_mem_zpowers x i
    have h2 : x ^ j ∈ P := Subgroup.npow_mem_zpowers x j
    rw [← h, Subgroup.mul_mem_cancel_right P h1] at h2
    have := hy ▸ hP_card ▸ (Subgroup.orderOf_dvd_natCard P h2)
    contradiction
  have : P.Normal := by
    refine Subgroup.normal_of_index_eq_two P ?_
    have := h1 ▸ Nat.card_eq_fintype_card (α := G) ▸ hP_card ▸ Subgroup.card_mul_index P
    linarith
  have : (y * x * y⁻¹) ∈ P := this.conj_mem x (Subgroup.mem_zpowers x) y
  have hP (x' : G) : x' ∈ P → ∃ a < 3, x' = x ^ a
  · rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff]
    intro ⟨k, hk⟩
    rw [← hk]
    use k % 3, Nat.mod_lt k (show 0 < 3 by norm_num1)
    apply pow_eq_pow_mod
    exact hx ▸ pow_orderOf_eq_one x
  choose a ha using hP (y * x * y⁻¹) this
  -- in general, discuss by the multiplicative order of a
  match a with
  | 0 =>
    simp only [zero_lt_three, pow_zero, true_and] at ha
    rw [mul_inv_eq_one] at ha
    have := self_eq_mul_right.mp ha.symm
    have := orderOf_eq_one_iff.mpr this ▸ hx
    contradiction
  | 1 =>
    absurd h2
    apply isCyclic_of_orderOf_eq_card (y * x)
    rw [h1]
    rw [pow_one] at ha
    have : Nat.Coprime (orderOf y) (orderOf x)
    · rw [hx, hy]
      norm_num1
    have := Commute.orderOf_mul_eq_mul_orderOf_of_coprime (eq_mul_of_mul_inv_eq ha.right) this
    rw [this, hy, hx]
  | 2 =>
    have hy2 : y⁻¹ = y
    · rw [← mul_left_inj y, ← pow_two, ← hy, pow_orderOf_eq_one y, mul_left_inv]
    have hxy (n : ℕ) : x ^ n * y = y * x ^ (2 * n)
    · induction n with
      | zero => simp
      | succ n h =>
        rw [pow_succ, mul_assoc, h, ← mul_assoc]
        rw [mul_assoc, eq_comm, ← inv_mul_eq_iff_eq_mul, hy2] at ha
        rw [← ha.right, mul_assoc, ← pow_add, show 2 + 2 * n = 2 * Nat.succ n by linarith]
    let f : DihedralGroup 3 → G
    | DihedralGroup.r i => x ^ i.val
    | DihedralGroup.sr i => y * x ^ i.val
    let F : DihedralGroup 3 →* G := {
      toFun := f
      map_one' := by
        change x ^ ZMod.val 0 = 1
        rw [ZMod.val_zero, pow_zero]
      map_mul' := by
        intro u v
        have hij3 : ∀ i j : ZMod 3, ZMod.val (j - i) % 3 = (2 * ZMod.val i + ZMod.val j) % 3
        · decide
        match u, v with
        | DihedralGroup.r i, DihedralGroup.r j => {
          simp [← pow_add, pow_inj_mod, hx, ZMod.val_add]
        }
        | DihedralGroup.sr i, DihedralGroup.r j => {
          simp [mul_assoc, mul_right_inj, ← pow_add, pow_inj_mod, hx, ZMod.val_add]
        }
        | DihedralGroup.r i, DihedralGroup.sr j => {
          simp only [DihedralGroup.r_mul_sr]
          rw [← mul_assoc, hxy, mul_assoc, mul_right_inj, ← pow_add, pow_inj_mod, hx]
          exact hij3 i j
        }
        | DihedralGroup.sr i, DihedralGroup.sr j => {
          simp only [DihedralGroup.sr_mul_sr]
          rw [mul_assoc, ← mul_assoc _ y, hxy, mul_assoc y, ← mul_assoc, ← pow_two,
            ← hy, pow_orderOf_eq_one y, one_mul, hy, ← pow_add, pow_inj_mod, hx]
          exact hij3 i j
        }
    }
    have : f.Injective
    · intro u v
      match u, v with
      | DihedralGroup.r i, DihedralGroup.r j =>
        rw [DihedralGroup.r.injEq]
        exact hx' i j
      | DihedralGroup.sr i, DihedralGroup.r j => intro h; exact hy' i j h |>.elim
      | DihedralGroup.r i, DihedralGroup.sr j => intro h; exact hy' j i h.symm |>.elim
      | DihedralGroup.sr i, DihedralGroup.sr j =>
        rw [mul_right_inj, DihedralGroup.sr.injEq]
        exact hx' i j
    apply MulEquiv.ofBijective F
    apply (Fintype.bijective_iff_injective_and_card f).mpr
    use this
    rw [h1]
    rfl
  | n + 3 =>
    have := ha.left
    contradiction

-- #check Sylow.directProductOfNormal

-- tidy up Mathlib.Algebra.BigOperators.Basic
