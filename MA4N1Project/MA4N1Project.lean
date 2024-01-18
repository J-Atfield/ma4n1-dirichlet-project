import Mathlib.Tactic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Polynomial.Degree.Lemmas

namespace TPwLDirichlet

open ZMod
open Polynomial
open Nat

---------------------------------------------------------------------------------------------------
-- Introduction:  The following namespace aims to prove some special cases of dirilichts theorem.
-- These cases are: There exists infinitely many primes p of the form p = 4k + 1, p = 6k + 1 and
-- p = 8k + 1.
---------------------------------------------------------------------------------------------------

-- Creating a definition for infinitely many in lean
-- There are various ways to repsent this, therefore additional versions of this will be defined
def exists_infinitely_many_P : Prop := ∀ n : ℕ, ∃ p : ℕ, p ≥ n ∧ Nat.Prime p


-- [Someone write something for this]
lemma fundamental_lemma {f: Polynomial ℤ} (h : degree f > 0) : exists_infinitely_many_P ∧ (∃ x : ℤ, f.eval x ≡ 0 [ZMOD p]) := by
  sorry
  done


---------------------------------------------------------------------------------------------------
-- Section 1:  The lemma proved below is our fundamental lemma. This lemma is used in all three of
-- the cases which are proved in this namespace: 4k + 1, 6k + 1 and 8k + 1
---------------------------------------------------------------------------------------------------

open scoped Polynomial in
lemma two.one {f : ℤ[X]} (hf : f.natDegree ≠ 0) (M : ℤ) : ∃ p n, _root_.Prime p ∧ M ≤ p ∧ p ∣ f.eval n := by
  apply?
  done

---------------------------------------------------------------------------------------------------
-- Section 2: The following section contains some prelimnary theorems and lemmas which will be used
-- throughout the rest of the proofs.
---------------------------------------------------------------------------------------------------

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


---------------------------------------------------------------------------------------------------
-- Section 3: The following three theorems prove some equivalences between vaiour congruences which
-- are used to throughout later theorems
---------------------------------------------------------------------------------------------------

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

-- Establishes the equivalence between p % 4 = 1 and the existence of a natural number k such that p = 4*k + 1 for a prime number p
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

-- Shows that for a prime number p, p % (n+2) = 1 is equivalent to the existence of a natural number k such that p = (n+2)*k + 1
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


---------------------------------------------------------------------------------------------------
-- Section 4: The following theorem proves our first special case. That there exist infinitely many
-- primes p of the form 4k + 1.
---------------------------------------------------------------------------------------------------
theorem x_squared_degree_2 : natDegree (X ^ 2 + 1 : ℤ[X]) = 2 := by
  rw [natDegree_add_eq_left_of_natDegree_lt] <;>
  simp
  done

theorem testing (hp : (f : ℤ[X]) = X^2 + 1) : ∃ p n, _root_.Prime p ∧ M ≤ p ∧ p ∣ f.eval n := by
  apply two.one
  case hf =>
    rw [hp]
    rw [x_squared_degree_2]
    simp only
  done

theorem testing' : ∃ p n, _root_.Prime p ∧ M ≤ p ∧ p ∣ eval n (X^2 + 1 : ℤ[X]):= by
  apply testing
  case hp => simp only
  done

theorem inf_p_4k_plus_one (hp : p.Prime) (hp2 : p > 2) (hs : IsSquare (-1 : ZMod p)) : (∃ (k : ℕ), p = 4*k+1) ∧ ∃ p n, _root_.Prime p ∧ M ≤ p ∧ p ∣ eval n (X^2 + 1 : ℤ[X]) := by
  have h_cong_1 : p % 4 = 1 := by
    {
    rw[← square_eq_neg_one_mod_p_iff_p_eq_one_mod_four]
    assumption
    assumption
    assumption
    }
  rw [← p_mod_4_eq_one_iff_p_eq_4k_plus_1']
  apply And.intro
  case left =>
    apply h_cong_1
  case right =>
    apply testing'
  exact hp
  done

variable (q : ℕ) [Fact q.Prime]


---------------------------------------------------------------------------------------------------
-- Section 5: The theorems split_fration and odd_int_div allow us to adapt eulers criterion to be
-- applicable to our case. Most notably, odd_int_div states that for an odd number p, when divided
-- by 2 using integer division, p / 2 = (p - 1) / 2.
---------------------------------------------------------------------------------------------------


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

-- If a prime number p satisfies p % 4 = 1 then p = 4 * k + 1
lemma rearrange {p k : ℕ} (hp : p % 4 = 1) : (p - 1) / 4 = k → p = 4*k + 1 := by
  intro h2
  have h3 : 4*((p-1) / 4) + 1 = p := by
  {
    rw [← hp]
    rw [← div_eq_sub_mod_div, add_comm]
    apply mod_add_div p 4
  }
  rw [← h3, ← h2]
  done

---------------------------------------------------------------------------------------------------
-- Section 6: The following theorems establish the equality between various legendre symbols. These
-- are typically used in in the proof of the special case of 6k + 1, and allows us to use the throrems
-- in a form which applies correctly for our forms.
---------------------------------------------------------------------------------------------------

theorem eq_zero_iff_gcd_ne_one {a : ℤ} {p : ℕ} [pp : Fact p.Prime] :
    (a : ZMod p) = 0 ↔ a.gcd p ≠ 1 := by
  rw [Ne, Int.gcd_comm, Int.gcd_eq_one_iff_coprime,
    (Nat.prime_iff_prime_int.1 pp.1).coprime_iff_not_dvd, Classical.not_not,
    int_cast_zmod_eq_zero_iff_dvd]

theorem ne_eq_zero_iff_gcd_one {a : ℤ} {p : ℕ} [pp : Fact p.Prime] :
    (a : ZMod p) ≠ 0 ↔ a.gcd p = 1 := by
  refine not_iff_comm.mpr ?_
  exact Iff.symm eq_zero_iff_gcd_ne_one
  done

theorem three_mod_p_ne_eq_zero_iff_gcd_one : ((3 : ℤ) : ZMod p) ≠ 0 ↔ Int.gcd 3 p = 1 := by
  rw[ne_eq_zero_iff_gcd_one]
  done

theorem three_mod_p_ne_eq_zero_iff_gcd_one_without_cast : (3 : ZMod p) ≠ 0 ↔ Int.gcd 3 p = 1 := by
  rw [← three_mod_p_ne_eq_zero_iff_gcd_one]
  simp only [ne_eq, Int.int_cast_ofNat]
  done

lemma primes_coprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : Coprime p q := by
  exact (coprime_primes hp hq).mpr hpq
  done

theorem gcd_three_prime_not_three_is_one (hp : p.Prime) (hp2 : p ≠ 3) : Int.gcd 3 p = 1 := by
  have h_3_prime : Nat.Prime 3 := by
    exact prime_three
  have hp2' : 3 ≠ p := by
    exact fun a => hp2 (Eq.symm a)
  have h_3_p_coprime : Coprime 3 p := by
    exact primes_coprime h_3_prime hp hp2'
  rename_i _ _
  simp_all only [ne_eq]
  exact h_3_p_coprime
  done

theorem x_squared_plus_three_degree_2 : natDegree (X ^ 2 + 3 : ℤ[X]) = 2 := by
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow 2
  have h : natDegree (3 : ℤ[X]) = 0 := by
    exact natDegree_C 3
  · rw [h]
    rename_i _ _
    simp_all only [natDegree_pow, natDegree_X, mul_one, zero_lt_two]
  done

theorem exists_prime_div_of_poly_eval (hp : (f : ℤ[X]) = X^2 + 3) : ∃ p n, _root_.Prime p ∧ M ≤ p ∧ p ∣ f.eval n := by
  apply two.one
  case hf =>
    rw [hp]
    rw [x_squared_plus_three_degree_2]
    simp only
  done

theorem exists_prime_divisor_for_quad_plus_three_poly_eval : ∃ p n, _root_.Prime p ∧ M ≤ p ∧ p ∣ eval n (X^2 + 3 : ℤ[X]):= by
  apply exists_prime_div_of_poly_eval
  rfl
  done

lemma h_cong_1_mod_3 : (legendreSym 3 p : ZMod 3) = 1 → p % 3 = 1 := by
  rw [legendreSym.eq_pow, odd_int_div]
  norm_num
  · intro h
    exact Fin.mk_eq_mk.mp h
  · exact odd_iff.mpr rfl

theorem legendre_neg_q_p_eq_legendre_p_q_three_mod_four (hp : q % 4 = 3) (hp2 : p > 2) (hp3 : p % 4 = 3) : (legendreSym p (-q)) = legendreSym q p := by
  rw[<-neg_one_mul]
  rw[legendreSym.mul]
  rw[legendreSym.quadratic_reciprocity_three_mod_four]
  simp only [Int.cast_neg, mul_neg]
  rw[legendreSym.at_neg_one]
  simp only [Int.cast_one]
  rw [χ₄_nat_three_mod_four]
  simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_neg]
  apply hp3
  simp only [ne_eq]
  apply Nat.ne_of_gt
  apply hp2
  case hp => exact hp
  case hq => exact hp3
  done

theorem legendre_neg_q_p_eq_legendre_p_q_one_mod_four (hp : q % 4 = 3) (hp2 : p > 2) (hp3 : p % 4 = 1) : (legendreSym p (-q)) = legendreSym q p := by
  rw[<-neg_one_mul]
  rw[legendreSym.mul]
  rw[<-legendreSym.quadratic_reciprocity_one_mod_four]
  rw[legendreSym.at_neg_one]
  simp only [Int.cast_one]
  rw [χ₄_nat_one_mod_four]
  simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_neg]
  apply hp3
  simp only [ne_eq]
  apply Nat.ne_of_gt
  apply hp2
  case hp => exact hp3
  case hq => rename_i inst inst_1
             simp_all only [gt_iff_lt, ne_eq]
             apply Aesop.BuiltinRules.not_intro
             intro a
             aesop_subst a
             simp_all only
  done

theorem legendre_neg_q_p_eq_legendre_p_q (hp : q % 4 = 3) (hp2 : p > 2) (hp3 : Nat.Prime p) : legendreSym p (-q) = legendreSym q p := by
  have hp4 : (p % 4 = 1) ∨ (p % 4 = 3) := by
  {
    apply p_odd_then_one_or_three_mod_four
    apply prime_gt_two_is_odd
    case hp.hp => exact hp3
    case hp.hp2 => exact hp2
    done
  }
  cases hp4 with
  | inl hp4 =>
    rw[legendre_neg_q_p_eq_legendre_p_q_one_mod_four]
    case inl.hp => exact hp
    case inl.hp2 => exact hp2
    case inl.hp3 => exact hp4
    done
  | inr hp4 =>
    rw[legendre_neg_q_p_eq_legendre_p_q_three_mod_four]
    case inr.hp => exact hp
    case inr.hp2 => exact hp2
    case inr.hp3 => exact hp4
    done
  done

theorem legendre_neg_3_p_eq_legendre_p_3 (hp2 : p > 2) (hp3 : Nat.Prime p) : legendreSym p (-3) = legendreSym 3 p := by
  apply legendre_neg_q_p_eq_legendre_p_q
  case hp => rename_i inst _
             simp only
  case hp2 => exact hp2
  case hp3 => exact hp3
  done

lemma IsSqaure_neg_three_imp_legendre_p_neg_three_eq_one (hp : p.Prime) (hp2 : p > 3) : IsSquare (-3 : ZMod p) -> legendreSym p (-3) = 1 := by
  intro hs
  rw [legendreSym.eq_one_iff]
  simp only [Int.cast_neg, Int.int_cast_ofNat]
  exact hs
  case ha0 =>
    simp only [Int.cast_neg, Int.int_cast_ofNat, ne_eq, neg_eq_zero]
    rw [← @ne_eq]
    rw[three_mod_p_ne_eq_zero_iff_gcd_one_without_cast]
    apply gcd_three_prime_not_three_is_one
    exact hp
    exact Nat.ne_of_gt hp2
  done

theorem inf_p_6k_plus_one (hp : p.Prime) (hp2 : p > 3) (hs : IsSquare (-3 : ZMod p)) : (∃ (k : ℕ), p = 6*k+1) ∧ ∃ p n, _root_.Prime p ∧ M ≤ p ∧ p ∣ eval n (X^2 + 3 : ℤ[X]) := by
  have hp3 : p > 2 := by
    exact lt_of_succ_lt hp2
  have hp_odd : Odd p := by
    exact prime_gt_two_is_odd hp hp3
  have hp_cong_1_mod_2 : p % 2 = 1 := by
    exact n_odd_if_Odd hp_odd
  have h_leg_sym_1_rhs : legendreSym 3 p = 1 := by
    rw [<-legendre_neg_3_p_eq_legendre_p_3]
    exact IsSqaure_neg_three_imp_legendre_p_neg_three_eq_one p hp hp2 hs
    case hp2 =>
      exact hp3
    exact hp
  have h_cong_1_mod_3 : (legendreSym 3 p : ZMod 3) = 1 → p % 3 = 1 := by
    intro legendreHp
    exact h_cong_1_mod_3 p legendreHp
  have h_cong_1_mod_2_and_3 : p ≡ 1 [MOD 2] ∧ p ≡ 1 [MOD 3] := by
    rename_i inst _
    simp_all only [gt_iff_lt, odd_iff_not_even, forall_true_left, and_self]
    apply And.intro
    · exact hp_cong_1_mod_2
    · exact h_cong_1_mod_3
  have h_coprime_2_3 : Nat.Coprime 2 3 := by
    rename_i _ _
    simp_all only [gt_iff_lt, odd_iff_not_even, forall_true_left]
  have h_cong_1_2_mul_3 : p ≡ 1 [MOD 2 * 3] := by
    rw [← Nat.modEq_and_modEq_iff_modEq_mul]
    apply h_cong_1_mod_2_and_3
    exact h_coprime_2_3
  have h_p_cong_mod_6 : p % 6 = 1 := by
    rename_i _ _
    simp_all only [gt_iff_lt, odd_iff_not_even, forall_true_left]
    unhygienic with_reducible aesop_destruct_products
    exact h_cong_1_2_mul_3
  apply And.intro
  case left =>
    rw [← p_mod_n_eq_one_iff_p_eq_nk_plus_1']
    norm_num
    exact h_p_cong_mod_6
    exact hp
  case right =>
    exact exists_prime_divisor_for_quad_plus_three_poly_eval
  done

end TPwLDirichlet
