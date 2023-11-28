import Mathlib.Tactic

namespace TPwLDirichlet

open ZMod
open Nat
open Polynomial

def exists_infinitely_many_P : Prop := ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n

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


theorem p_not_three_mod_four_implies_p_one_mod_four {p : ℕ } (hp : Odd p) : ¬(p % 4 = 3) -> (p % 4 = 1) := by
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

theorem p_one_mod_four_implies_p_not_three_mod_four {p : ℕ} (hp : Odd p): (p % 4 = 1) -> ¬(p % 4 = 3) := by
  intro h1
  rw[h1]
  simp only
  done

variable (p : ℕ) [Fact p.Prime]
-- Lemma 2.14
-- Proving the quadratic congruence x2 + 1 ≡ 0 mod p where p is an odd prime has a solution if and only if p ≡ 1 mod 4
-- Showing the implication in the left direction (Is it Left or Right???)
theorem neg_1_square_mod_left_imp (hp : p > 2) (hp2 : p.Prime): IsSquare (-1 : ZMod p) → p % 4 = 1 := by
  rw[ZMod.exists_sq_eq_neg_one_iff]
  simp only [ne_eq]
  apply p_not_three_mod_four_implies_p_one_mod_four
  apply prime_gt_two_is_odd
  case hp => apply hp2
  case hp2 => apply hp
  done

-- Showing the implication in the right direction (Is it Left or Right???)
theorem neg_1_square_mod_right_imp (hp : p > 2) (hp2 : p.Prime) (hp3 : p % 4 = 1): IsSquare (-1 : ZMod p) := by
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
theorem neg_1_square_mod (hp : p > 2) (hp2 : p.Prime): IsSquare (-1 : ZMod p) ↔ p % 4 = 1 := by
  apply Iff.intro
  case mp =>
    apply neg_1_square_mod_left_imp
    case hp => apply hp
    case hp2 => apply hp2
    done
  case mpr =>
    apply neg_1_square_mod_right_imp
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

-- ZMod.euler_criterion_units
-- legendreSym.eq_pow
theorem eulers_criterion' (a : ℤ) (hp : Nat.Prime p) (hp2 : p > 2) : (legendreSym p a : ZMod p) = (a : ZMod p) ^ ((p-1) / 2) := by
  rw[←odd_int_div]

  rw[legendreSym.eq_pow]
  apply prime_gt_two_is_odd
  apply hp
  apply hp2

  done

-- Special Case p = 6k + 1
---------------------------------------------
variable (q : ℕ) [Fact q.Prime]

theorem neg_3_square_mod_6 (hp : p > 2) (hp2 : p.Prime): IsSquare (-3 : ZMod p) ↔ p % 6 = 1 := by
  sorry
  done

theorem legendre_neg_3_p_eq_legendre_p_3 : (legendreSym p (-3) : ZMod p) = legendreSym 3 p := by
  rw[<-neg_one_mul]
  rw[legendreSym.mul]
  rw[legendreSym.eq_pow]

  done

theorem applying_legendre_mul: (legendreSym p ((-1) * 3) : ZMod p) = (legendreSym p (-1) : ZMod p) * (legendreSym p 3 : ZMod p) := by
  rw[legendreSym.mul]
  simp only [Int.cast_mul]
  done


theorem three_div_two : q = 3 -> q / 2 = 1 := by
  intro hp
  rw [hp]
  simp only
  done

theorem testing (hp : q = 3) (hp2 : Odd p) (hp3 : p > 2): legendreSym p q = (-1)^((p-1)/2) * legendreSym q p := by
  rw[legendreSym.quadratic_reciprocity']
  rw [three_div_two, one_mul]
  rw [odd_int_div]
  apply hp2
  case a => exact hp
  case hp =>
    simp only [ne_eq]
    rw [hp]
    simp only
    done
  case hq =>
    simp only [ne_eq]
    apply Nat.ne_of_gt
    case h => exact hp3
    done
  done



theorem testing' : (legendreSym p (-3) : ZMod p) = 0 := by
  rw[legendreSym.eq_pow]

  done

theorem legendreAtNegOne : legendreSym p (-1) = 0 := by
  rw[legendreSym.at_neg_one]
  rw[ZMod.χ₄_eq_neg_one_pow]
  sorry
  done





end TPwLDirichlet
