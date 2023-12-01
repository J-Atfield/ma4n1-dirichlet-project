import Mathlib.Tactic

namespace TPwLDirichlet

open ZMod
open Nat
open Polynomial

-- Creating a definition for infinitely many in lean
-- There are various ways to repsent this, therefore additional versions of this will be defined
def exists_infinitely_many_P : Prop := ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p ≥ n


-- [Someone write something for this]
lemma fundamental_lemma {f: Polynomial ℤ} (h : degree f > 0) : exists_infinitely_many_P ∧ (∃ x : ℤ, f.eval x ≡ 0 [ZMOD p]) := by
  sorry
  done


-- Any prime greater than 2 is odd
theorem prime_gt_two_is_odd {p : ℕ} (hp : Nat.Prime p) (hp2 : p > 2) : Odd p := by
  refine Prime.odd_of_ne_two hp ?h_two
  norm_num
  exact Nat.ne_of_gt hp2
  done


-- Proving equivalence of different odd definitions
lemma n_odd_if_Odd {n : ℕ} (h : Odd n) : n % 2 = 1 := by
  rcases h with ⟨k, hk⟩
  rw [hk]
  rw [add_mod_of_add_mod_lt]
  · simp only [mul_mod_right, one_mod, zero_add]
  · simp only [mul_mod_right, one_mod, zero_add, lt_succ_self]
  done

-- If p is odd, then it is congruent to 1 mod 4 or 3 mod 4
theorem p_odd_then_one_or_three_mod_four {p : ℕ} (hp : Odd p) : (p % 4 = 1) ∨ (p % 4 = 3) := by
  refine Nat.odd_mod_four_iff.mp ?h_two
  apply n_odd_if_Odd
  exact hp
  done

-- Proving that if p is odd and is not congruent to 3 mod 4, then it is congruent to 1 mod 4
theorem p_not_three_mod_four_implies_p_one_mod_four {p : ℕ} (hp : Odd p) : ¬(p % 4 = 3) -> (p % 4 = 1) := by
  have h_imp_equiv_or : (p % 4 = 1) ∨ (p % 4 = 3) := by
  {
    apply p_odd_then_one_or_three_mod_four
    exact hp
  }
  {
    cases h_imp_equiv_or with
    | inl hp2 => exact fun _ => hp2
    | inr hp3 => exact fun a => (a hp3).elim
  }
  done

-- Proving that if p is odd and congruent to 1 mod 4, then it is not congruent to 3 mod 4
theorem p_one_mod_four_implies_p_not_three_mod_four {p : ℕ} (hp : Odd p): (p % 4 = 1) -> ¬(p % 4 = 3) := by
  intro h1
  rw[h1]
  exact ne_of_beq_eq_false rfl
  done

-- Proving the if and only if version of the two above theorems, applying them both together
theorem p_one_mod_four_iff_p_not_three_mod_four {p : ℕ} (hp : Odd p) : (p % 4 = 1) ↔ ¬(p % 4 = 3) := by
  apply Iff.intro
  · apply p_one_mod_four_implies_p_not_three_mod_four
    exact hp
  · apply p_not_three_mod_four_implies_p_one_mod_four
    exact hp
  done

variable (p : ℕ) [Fact p.Prime]

-- Lemma 2.14
-- Proving the quadratic congruence x^2 + 1 ≡ 0 mod p where p is an odd prime has a solution if and only if p ≡ 1 mod 4
-- Showing the implication in the left direction (Is it Left or Right???)
theorem square_eq_neg_one_mod_p_imp_p_eq_one_mod_four (hp : p > 2) (hp2 : p.Prime): IsSquare (-1 : ZMod p) → p % 4 = 1 := by
  rw[ZMod.exists_sq_eq_neg_one_iff]
  simp only [ne_eq]
  apply p_not_three_mod_four_implies_p_one_mod_four
  apply prime_gt_two_is_odd
  case hp => apply hp2
  case hp2 => apply hp
  done

-- Showing the implication in the right direction (Is it Left or Right???)
theorem p_eq_one_mod_four_imp_square_eq_neg_one_mod_p (hp : p > 2) (hp2 : p.Prime) (hp3 : p % 4 = 1): IsSquare (-1 : ZMod p) := by
  have hp4 : ¬(p % 4 = 3) := by
  {
    apply p_one_mod_four_implies_p_not_three_mod_four
    case a => apply hp3
    apply prime_gt_two_is_odd
    case hp2 => apply hp
    case hp => apply hp2
    done
  }
  rw[ZMod.exists_sq_eq_neg_one_iff]
  simp only [ne_eq]
  exact hp4
  done

-- Combining the left and right implications to get an equality
theorem square_eq_neg_one_mod_p_iff_p_eq_one_mod_four (hp : p > 2) (hp2 : p.Prime): IsSquare (-1 : ZMod p) ↔ p % 4 = 1 := by
  apply Iff.intro
  case mp =>
    apply square_eq_neg_one_mod_p_imp_p_eq_one_mod_four
    case hp => apply hp
    case hp2 => apply hp2
    done
  case mpr =>
    apply p_eq_one_mod_four_imp_square_eq_neg_one_mod_p
    case hp => apply hp
    case hp2 => apply hp2
    done
  done



-- Have a theorem which allows you to split the fraction and
-- allow you to evaluate 1/2 to 0 with the integer division
theorem split_fraction {k : ℕ} : (2 * k + 1) / 2 = ((2 * k) / 2) + (1 / 2) := by
  refine Nat.add_div_of_dvd_right ?hca
  exact Nat.dvd_mul_right 2 k
  done


-- We have the congruence `legendreSym p a ≡ a ^ (p / 2) mod p`.
-- Proving that for odd or Prime (>2) p, p / 2 = (p - 1) / 2 for integer division
theorem odd_int_div {p : ℕ} (hp : Odd p) : (p / 2) = ((p - 1) / 2) := by
  rcases hp with ⟨k, hk⟩
  rw [hk, Nat.add_sub_cancel]
  rw [mul_comm, Nat.mul_div_cancel k]
  rw [mul_comm, split_fraction]
  rw [mul_comm, Nat.mul_div_cancel k]
  exact rfl
  · norm_num
  · norm_num
  done

-- Proving an alternate version of Eulers Criterion, to make it applicable to our application
theorem eulers_criterion' (a : ℤ) (hp : Nat.Prime p) (hp2 : p > 2) : (legendreSym p a : ZMod p) = (a : ZMod p) ^ ((p-1) / 2) := by
  rw[←odd_int_div]
  rw[legendreSym.eq_pow]
  apply prime_gt_two_is_odd
  apply hp
  apply hp2
  done

lemma rearrange {p k : ℕ} (h : Nat.Prime p) (hp : p % 4 = 1) : (p - 1) / 4 = k → p = 4*k + 1 := by
  intro h2
  have h3 : 4*((p-1) / 4) + 1 = p := by
  {
    rw [← hp]
    rw [← div_eq_sub_mod_div, add_comm]
    apply mod_add_div p 4
  }
  rw [← h3, ← h2]
  done

theorem p_mod_4_eq_one_iff_p_eq_4k_plus_1' {p : ℕ} (hp : p.Prime) : (p % 4 = 1) ↔ (∃ (k : ℕ), p = 4*k + 1) := by
  apply Iff.intro
  case mpr =>
    simp only [forall_exists_index]
    intro k h_4k_1
    rw [h_4k_1, add_mod, mul_mod_right, zero_add, mod_mod]
    exact rfl
  case mp =>
    intro hp_mod_4
    have h_mod_equiv : 1 ≡ p [MOD 4] := by
      rw [← hp_mod_4]
      exact mod_modEq p 4
    have h_four_div_p_minus_one : 4 ∣ (p - 1) := by
      rw [← modEq_iff_dvd']
      apply h_mod_equiv
      refine one_le_iff_ne_zero.mpr ?_
      exact Nat.Prime.ne_zero hp
    have h_exists_k_p1_eq_k4 : ∃ (k : ℕ), p-1=k*4 := by
      apply exists_eq_mul_left_of_dvd
      exact h_four_div_p_minus_one
    cases h_exists_k_p1_eq_k4 with
    | intro k h =>
      use k
      rw [mul_comm]
      have : 1 ≤ p := by
      {
        rw [@one_le_iff_ne_zero]
        exact Nat.Prime.ne_zero hp
      }
      exact Nat.eq_add_of_sub_eq this h
  done

theorem p_mod_n_eq_one_iff_p_eq_nk_plus_1' {p : ℕ} (hp : p.Prime) : (p % (n+2) = 1) ↔ (∃ (k : ℕ), p = (n+2)*k + 1) := by
  apply Iff.intro
  case mpr =>
    simp only [forall_exists_index]
    intro k h_nk_1
    rw [h_nk_1, add_mod, mul_mod_right, zero_add, mod_mod]
    apply one_mod
  case mp =>
    intro hp_mod_n_plus_2
    have h_mod_equiv : 1 ≡ p [MOD (n+2)] := by
      rw [← hp_mod_n_plus_2]
      exact mod_modEq p (n+2)
    have h_n_plus_2_div_p_minus_one : (n + 2) ∣ (p - 1) := by
      rw [← modEq_iff_dvd']
      apply h_mod_equiv
      refine one_le_iff_ne_zero.mpr ?_
      exact Nat.Prime.ne_zero hp
    have h_exists_k_p1_eq_kn : ∃ (k : ℕ), p-1=k*(n+2) := by
      apply exists_eq_mul_left_of_dvd
      exact h_n_plus_2_div_p_minus_one
    cases h_exists_k_p1_eq_kn with
    | intro k h =>
      use k
      rw [mul_comm]
      have : 1 ≤ p := by
      {
        rw [@one_le_iff_ne_zero]
        exact Nat.Prime.ne_zero hp
      }
      exact Nat.eq_add_of_sub_eq this h
  done

theorem inf_p_4k_plus_one (hp : p.Prime) (hp2 : p > 2) (hs : IsSquare (-1 : ZMod p)) : p = 4*k+1 ∧ exists_infinitely_many_P := by
  have hp_odd : Odd p := by
    {
      apply prime_gt_two_is_odd
      exact hp
      exact hp2
    }
  have h_cong_1 : p % 4 = 1 := by
    rw[← square_eq_neg_one_mod_p_iff_p_eq_one_mod_four]
    assumption
    assumption
    assumption
  have h_ex_k : (∃ (k : ℕ), p = 4*k + 1) := by
  {
    rw [← p_mod_4_eq_one_iff_p_eq_4k_plus_1']
    assumption
    assumption
  }
  apply And.intro
  case left =>
    sorry
  case right =>
    sorry
      -- apply Nat.exists_infinite_primes
  done

end TPwLDirichlet
