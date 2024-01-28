import Mathlib.Tactic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Polynomial.Degree.Lemmas

namespace TPwLDirichlet

open ZMod
open Polynomial
open Nat

set_option maxHeartbeats 0

---------------------------------------------------------------------------------------------------
-- Introduction:  The following namespace aims to prove some special cases of dirilichts theorem.
-- These cases are: There exists infinitely many primes p of the form p = 4k + 1, p = 6k + 1 and
-- p = 8k + 1.
---------------------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------------------
-- Section 1:  The lemma proved below is our fundamental lemma. This lemma is used in all three of
-- the cases which are proved in this namespace: 4k + 1, 6k + 1 and 8k + 1
---------------------------------------------------------------------------------------------------

-- A polynomial with constant term 0 is divisible by n when evaluated at n
theorem n_dvd_fn_if_const_zero {f : ℤ[X]} {g : ℤ[X]} (hp : coeff f 0 = 0) : n ∣ (f.eval n) := by
  let a := coeff f 0
  let g := Polynomial.divX f
  have hp2 : f = X * g + C a := by
    exact (X_mul_divX_add f).symm
  have hp3 : f = X * g := by
    rw[hp2]
    simp only [eq_intCast, add_right_eq_self, Int.cast_eq_zero]
    exact hp
  have hp4 : (X * g).eval n = n * g.eval n := by
    simp only [eval_mul, eval_X]
  rw [hp3]
  rw [hp4]
  exact Int.dvd_mul_right n (eval n g)
  done

-- Equivalence between the definition of prime in the mathlib library and the definition of prime
theorem root_prime_iff_nat_prime (p : ℕ): (_root_.Prime p) ↔ (Nat.Prime p) := by
  exact Iff.symm prime_iff
  done

-- If p is the smallest factor of f, then p divides f
theorem if_min_fac_then_p_dvd_f (hp : p = minFac f) : (p : ℤ) ∣ f := by
  have h_p_dvd_f : p ∣ f := by
    rw [hp]
    exact minFac_dvd f
  exact Int.ofNat_dvd.mpr h_p_dvd_f
  done

-- Product of three non-zero integers is non-zero
theorem mul_three_non_zero_ne_zero (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a * b * c ≠ 0 := by
  simp_all only [ne_eq, _root_.mul_eq_zero, or_self, not_false_eq_true]
  done

-- A proof of the trivial case of the fundamental lemma i.e. when the constant term of f is 0
theorem trivial_case {f : ℤ[X]} (M : ℕ) (hp : coeff f 0 = 0) : ∃ p n, _root_.Prime p ∧ M ≤ p ∧ (p : ℤ) ∣ f.eval n :=
  let p := minFac (M ! + 1)
  let n := p
  have f1 : M ! + 1 ≠ 1 := Nat.ne_of_gt <| succ_lt_succ <| factorial_pos _
  have pp : Nat.Prime p := minFac_prime f1
  have ppp : _root_.Prime p := by
    exact (root_prime_iff_nat_prime p).mpr pp
  have hp2 : (p : ℤ) ∣ f.eval p := by
    apply n_dvd_fn_if_const_zero hp
    exact f
  have np : M ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ M ! := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
      pp.not_dvd_one h₂
  ⟨p, n, ppp, np, hp2⟩

-- A proof of the non-trivial case of the fundamental lemma i.e. when the constant term of f is non-zero
theorem non_trivial_case {f : ℤ[X]} (hf : f.natDegree ≠ 0) (M : ℕ) (hp : coeff f 0 ≠ 0) : ∃ p n, _root_.Prime p ∧ M ≤ p ∧ (p : ℤ) ∣ f.eval n :=
  let a := coeff f 0
  let n := M ! * a ^ 2
  let g := Polynomial.divX f
  have hp3 : f = X * g + C a := by
    exact (X_mul_divX_add f).symm
  have hp4 : f.eval n = n * g.eval n + a := by
    rw[hp3]
    rw [@eval_add]
    rw [@eval_C]
    rw [@eval_mul]
    rw [eval_X]
  have hp5 : f.eval (M ! * a ^ 2) = (M ! * a ^ 2) * g.eval (M ! * a ^ 2) + a := by
    simp only
    exact hp4
  have hp6 : ((M ! * a ^ 2) * g.eval (M ! * a ^ 2) + a) = a * (a * (M !) * (g.eval (M ! * a ^ 2)) + 1) := by
    rw [@cast_comm]
    rw [sq a]
    ring
  have hp7 : (a * (M !) * (g.eval (M ! * a ^ 2)) + 1) ∣ a * (a * (M !) * (g.eval (M ! * a ^ 2)) + 1) := by
    exact Int.dvd_mul_left a (a * ↑M ! * eval (↑M ! * a ^ 2) g + 1)
  have hp8 : (f.eval n ) = a * (a * (M !) * (g.eval (M ! * a ^ 2)) + 1) := by
    rw[hp5]
    rw[hp6]
  let functionAbsolute := Int.natAbs (a * (M !) * (g.eval (M ! * a ^ 2)) + 1)
  let p := minFac (functionAbsolute)
  have f2 : a * (M !) * (g.eval (M ! * a ^ 2)) ≠ 0 := by
    have h_m : M ! ≠ 0 := by
      exact factorial_ne_zero M
    have h_a : a ≠ 0 := by
      exact hp
    have h_g : g.eval (M ! * a ^ 2) ≠ 0 := by
      sorry
    apply mul_three_non_zero_ne_zero a (M !) (g.eval (M ! * a ^ 2))
    exact h_a
    exact Int.ofNat_ne_zero.mpr h_m
    exact h_g
  have f1 : functionAbsolute ≠ 1 := by -- needs f2, we are assuming g ≠ 0 by choice of a and m
    -- rw [@ne_one_iff_exists_prime_dvd]
    -- rw [functionAbsolute]
    sorry
  have pp : Nat.Prime p := minFac_prime f1
  have np : M ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ functionAbsolute := minFac_dvd functionAbsolute
      have h₂ : p ∣ 1 := sorry
    pp.not_dvd_one h₂
  have ppp : _root_.Prime p := by
    exact (root_prime_iff_nat_prime p).mpr pp
  have hp9 : (p : ℤ) ∣ functionAbsolute := by
    exact if_min_fac_then_p_dvd_f rfl
  have hp10 : (functionAbsolute : ℤ) ∣ f.eval n := by
    refine Int.natAbs_dvd.mpr ?_
    rw [hp8]
    apply hp7
  have hp123 : ((p : ℤ) ∣ f.eval n) := by
    exact Int.dvd_trans hp9 hp10
  ⟨p, n, ppp, np, hp123⟩

-- Let p be a prime and f (x) ∈ Z[X] be non-constant. Then f (x) ≡ 0 mod p is solvable for infinitely many p
lemma two.one {f : ℤ[X]} (hf : f.natDegree ≠ 0) (M : ℕ) : ∃ p n, _root_.Prime p ∧ M ≤ p ∧ (p : ℤ) ∣ f.eval n := by
  have hp : coeff f 0 ≠ 0 ∨ coeff f 0 = 0 := by
    exact ne_or_eq (coeff f 0) 0
  cases hp with
  | inl h =>
    exact non_trivial_case hf M h
  | inr h =>
    exact trivial_case M h
  done

-- ---------------------------------------------------------------------------------------------------
-- -- Section 2: The following section contains some prelimnary theorems and lemmas which will be used
-- -- throughout the rest of the proofs.
-- ---------------------------------------------------------------------------------------------------

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

-- ---------------------------------------------------------------------------------------------------
-- -- Section 3: The following three theorems prove some equivalences between vaiour congruences which
-- -- are used to throughout later theorems
-- ---------------------------------------------------------------------------------------------------

-- Proving that if p is odd and is not congruent to 3 mod 4, then it is congruent to 1 mod 4
theorem p_not_three_mod_four_implies_p_one_mod_four {p : ℕ} (hp : Odd p) : ¬(p % 4 = 3) -> (p % 4 = 1) := by
  have h_imp_equiv_or : (p % 4 = 1) ∨ (p % 4 = 3) := by
    apply p_odd_then_one_or_three_mod_four
    exact hp
  cases h_imp_equiv_or with
  | inl hp2 => exact fun _ => hp2
  | inr hp3 => exact fun a => (a hp3).elim
  done

-- Proving that if p is odd and congruent to 1 mod 4, then it is not congruent to 3 mod 4
theorem p_one_mod_four_implies_p_not_three_mod_four {p : ℕ} : (p % 4 = 1) -> ¬(p % 4 = 3) := by
  intro h1
  rw [h1]
  exact ne_of_beq_eq_false rfl
  done

variable (p : ℕ) [Fact p.Prime]

-- Proving the quadratic congruence x^2 + 1 ≡ 0 mod p where p is an odd prime has a solution if and only if p ≡ 1 mod 4
-- Showing the forward implication (→)
theorem square_eq_neg_one_mod_p_imp_p_eq_one_mod_four (hp : p > 2) (hp2 : p.Prime): IsSquare (-1 : ZMod p) → p % 4 = 1 := by
  rw [ZMod.exists_sq_eq_neg_one_iff]
  simp only [ne_eq]
  apply p_not_three_mod_four_implies_p_one_mod_four
  apply prime_gt_two_is_odd
  case hp => apply hp2
  case hp2 => apply hp
  done

-- Showing the backward direction (←)
theorem p_eq_one_mod_four_imp_square_eq_neg_one_mod_p (hp3 : p % 4 = 1): IsSquare (-1 : ZMod p) := by
  have hp4 : ¬(p % 4 = 3) := by
    apply p_one_mod_four_implies_p_not_three_mod_four
    case a => apply hp3
    done
  rw [ZMod.exists_sq_eq_neg_one_iff]
  simp only [ne_eq]
  exact hp4
  done

-- Combining the forward and backward implications to get an ↔ statement
theorem square_eq_neg_one_mod_p_iff_p_eq_one_mod_four (hp : p > 2) (hp2 : p.Prime): IsSquare (-1 : ZMod p) ↔ p % 4 = 1 := by
  apply Iff.intro
  case mp =>
    apply square_eq_neg_one_mod_p_imp_p_eq_one_mod_four
    case hp => apply hp
    case hp2 => apply hp2
    done
  case mpr =>
    apply p_eq_one_mod_four_imp_square_eq_neg_one_mod_p
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
        rw [@one_le_iff_ne_zero]
        exact Nat.Prime.ne_zero hp
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
        rw [@one_le_iff_ne_zero]
        exact Nat.Prime.ne_zero hp
      exact Nat.eq_add_of_sub_eq this h
  done

-- ---------------------------------------------------------------------------------------------------
-- -- Section 4: The following theorem proves our first special case. That there exist infinitely many
-- -- primes p of the form 4k + 1.
-- ---------------------------------------------------------------------------------------------------

-- Degree of x^2 + 1 is 2
theorem x_squared_degree_2 : natDegree (X ^ 2 + 1 : ℤ[X]) = 2 := by
  rw [natDegree_add_eq_left_of_natDegree_lt] <;>
  simp
  done

-- Proving that there exists a pair p prime, n such that p | (n^2 + 1)
theorem exists_pn_st_p_div_fn (hp : (f : ℤ[X]) = X^2 + 1) : ∃ p n, _root_.Prime p ∧ (M : ℕ) ≤ p ∧ (p : ℤ) ∣ f.eval n := by
  apply two.one
  case hf =>
    rw [hp]
    rw [x_squared_degree_2]
    simp only
  done

-- Proving that there exists a pair p prime, n such that p | (n^2 + 1)
theorem exists_pn_st_p_div_fn' : ∃ p n, _root_.Prime p ∧ (M : ℕ) ≤ p ∧ (p : ℤ) ∣ eval n (X^2 + 1 : ℤ[X]):= by
  apply exists_pn_st_p_div_fn
  case hp => simp only
  done

-- Proving there exists infinite primes of the form p = 4k + 1
theorem inf_p_4k_plus_one (hp : p.Prime) (hp2 : p > 2) (hs : IsSquare (-1 : ZMod p)) : (∃ (k : ℕ), p = 4*k+1) ∧ ∃ p n, _root_.Prime p ∧ (M : ℕ) ≤ p ∧ (p : ℤ) ∣ eval n (X^2 + 1 : ℤ[X]) := by
  have h_cong_1 : p % 4 = 1 := by
    rw [← square_eq_neg_one_mod_p_iff_p_eq_one_mod_four]
    exact hs
    exact hp2
    exact hp
  rw [← p_mod_4_eq_one_iff_p_eq_4k_plus_1']
  apply And.intro
  case left =>
    apply h_cong_1
  case right =>
    apply exists_pn_st_p_div_fn'
  exact hp
  done

variable (q : ℕ) [Fact q.Prime]

-- ---------------------------------------------------------------------------------------------------
-- -- Section 5: The theorems split_fration and odd_int_div allow us to adapt eulers criterion to be
-- -- applicable to our case. Most notably, odd_int_div states that for an odd number p, when divided
-- -- by 2 using integer division, p / 2 = (p - 1) / 2.
-- ---------------------------------------------------------------------------------------------------

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

-- ---------------------------------------------------------------------------------------------------
-- -- Section 6: The following theorems establish the equality between various legendre symbols. These
-- -- are typically used in in the proof of the special case of 6k + 1, and allows us to use the throrems
-- -- in a form which applies correctly for our forms.
-- ---------------------------------------------------------------------------------------------------

-- a ∈ ZMod p is zero iff a and p not coprime
theorem eq_zero_iff_gcd_ne_one {a : ℤ} {p : ℕ} [pp : Fact p.Prime] : (a : ZMod p) = 0 ↔ a.gcd p ≠ 1 := by
  rw [Ne, Int.gcd_comm, Int.gcd_eq_one_iff_coprime,
    (Nat.prime_iff_prime_int.1 pp.1).coprime_iff_not_dvd, Classical.not_not,
    int_cast_zmod_eq_zero_iff_dvd]
  done

-- a ∈ ZMod p is non-zero iff a and p coprime
theorem ne_eq_zero_iff_gcd_one {a : ℤ} {p : ℕ} [pp : Fact p.Prime] : (a : ZMod p) ≠ 0 ↔ a.gcd p = 1 := by
  refine not_iff_comm.mpr ?_
  exact Iff.symm eq_zero_iff_gcd_ne_one
  done

-- 3 ≠ 0 in ZMod p iff 3 and p coprime
theorem three_mod_p_ne_eq_zero_iff_gcd_one : ((3 : ℤ) : ZMod p) ≠ 0 ↔ Int.gcd 3 p = 1 := by
  rw [ne_eq_zero_iff_gcd_one]
  done

-- 3 ≠ 0 in ZMod p iff 3 and p coprime
theorem three_mod_p_ne_eq_zero_iff_gcd_one_without_cast : (3 : ZMod p) ≠ 0 ↔ Int.gcd 3 p = 1 := by
  rw [← three_mod_p_ne_eq_zero_iff_gcd_one]
  simp only [ne_eq, Int.int_cast_ofNat]
  done

-- Two primes are coprime
lemma primes_coprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : Coprime p q := by
  exact (coprime_primes hp hq).mpr hpq
  done

-- 3 and p coprime if p ≠ 3
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

-- Degree of x^2 + 3 is 2
theorem x_squared_plus_three_degree_2 : natDegree (X ^ 2 + 3 : ℤ[X]) = 2 := by
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow 2
  have h : natDegree (3 : ℤ[X]) = 0 := by
    exact natDegree_C 3
  · rw [h]
    rename_i _ _
    simp_all only [natDegree_pow, natDegree_X, mul_one, zero_lt_two]
  done

-- Proving that there exists a pair p prime, n such that p | (n^2 + 3)
theorem exists_prime_div_of_poly_eval (hp : (f : ℤ[X]) = X^2 + 3) : ∃ p n, _root_.Prime p ∧ (M : ℕ) ≤ p ∧ (p : ℤ) ∣ f.eval n := by
  apply two.one
  case hf =>
    rw [hp]
    rw [x_squared_plus_three_degree_2]
    simp only
  done

-- Proving that there exists a pair p prime, n such that p | (n^2 + 3)
theorem exists_prime_divisor_for_quad_plus_three_poly_eval : ∃ p n, _root_.Prime p ∧ (M : ℕ) ≤ p ∧ (p : ℤ) ∣ eval n (X^2 + 3 : ℤ[X]):= by
  apply exists_prime_div_of_poly_eval
  rfl
  done

-- p % 3 = 1 if legendreSym 3 p = 1 in ZMod p
theorem legendreSym_3_p_eq_1_imp_p_mod_3_1 : (legendreSym 3 p : ZMod 3) = 1 → p % 3 = 1 := by
  rw [legendreSym.eq_pow, odd_int_div]
  norm_num
  · intro h
    exact Fin.mk_eq_mk.mp h
  · exact odd_iff.mpr rfl
  done

-- If p,q % 4 = 3 then (legendreSym p (-q)) = legendreSym q p
theorem legendre_neg_q_p_eq_legendre_p_q_three_mod_four (hp : q % 4 = 3) (hp2 : p > 2) (hp3 : p % 4 = 3) : (legendreSym p (-q)) = legendreSym q p := by
  rw [← neg_one_mul]
  rw [legendreSym.mul]
  rw [legendreSym.quadratic_reciprocity_three_mod_four]
  simp only [Int.cast_neg, mul_neg]
  rw [legendreSym.at_neg_one]
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

-- If q % 4 = 3 and p % 4 = 1 then (legendreSym p (-q)) = legendreSym q p
theorem legendre_neg_q_p_eq_legendre_p_q_one_mod_four (hp : q % 4 = 3) (hp2 : p > 2) (hp3 : p % 4 = 1) : (legendreSym p (-q)) = legendreSym q p := by
  rw [← neg_one_mul]
  rw [legendreSym.mul]
  rw [← legendreSym.quadratic_reciprocity_one_mod_four]
  rw [legendreSym.at_neg_one]
  simp only [Int.cast_one]
  rw [χ₄_nat_one_mod_four]
  simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_neg]
  apply hp3
  simp only [ne_eq]
  apply Nat.ne_of_gt
  apply hp2
  case hp =>
    exact hp3
  case hq =>
    rename_i inst inst_1
    simp_all only [gt_iff_lt, ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    aesop_subst a
    simp_all only
  done

-- If q % 4 = 3 then (legendreSym p (-q)) = legendreSym q p
theorem legendre_neg_q_p_eq_legendre_p_q (hp : q % 4 = 3) (hp2 : p > 2) (hp3 : Nat.Prime p) : legendreSym p (-q) = legendreSym q p := by
  have hp4 : (p % 4 = 1) ∨ (p % 4 = 3) := by
    apply p_odd_then_one_or_three_mod_four
    apply prime_gt_two_is_odd
    case hp.hp => exact hp3
    case hp.hp2 => exact hp2
    done
  cases hp4 with
  | inl hp4 =>
    rw [legendre_neg_q_p_eq_legendre_p_q_one_mod_four]
    case inl.hp => exact hp
    case inl.hp2 => exact hp2
    case inl.hp3 => exact hp4
    done
  | inr hp4 =>
    rw [legendre_neg_q_p_eq_legendre_p_q_three_mod_four]
    case inr.hp => exact hp
    case inr.hp2 => exact hp2
    case inr.hp3 => exact hp4
    done
  done

-- legendreSym p (-3) = legendreSym 3 p
theorem legendre_neg_3_p_eq_legendre_p_3 (hp2 : p > 2) (hp3 : Nat.Prime p) : legendreSym p (-3) = legendreSym 3 p := by
  apply legendre_neg_q_p_eq_legendre_p_q
  case hp =>
    rename_i inst _
    simp only
  case hp2 =>
    exact hp2
  case hp3 =>
    exact hp3
  done

-- If X^2 + 3 ≡ 0 mod p has a solution, then legendreSym p (-3) = 1
lemma IsSqaure_neg_three_imp_legendre_p_neg_three_eq_one (hp : p.Prime) (hp2 : p > 3) : IsSquare (-3 : ZMod p) -> legendreSym p (-3) = 1 := by
  intro hs
  rw [legendreSym.eq_one_iff]
  simp only [Int.cast_neg, Int.int_cast_ofNat]
  exact hs
  case ha0 =>
    simp only [Int.cast_neg, Int.int_cast_ofNat, ne_eq, neg_eq_zero]
    rw [← @ne_eq]
    rw [three_mod_p_ne_eq_zero_iff_gcd_one_without_cast]
    apply gcd_three_prime_not_three_is_one
    exact hp
    exact Nat.ne_of_gt hp2
  done

-- There exists infinitely many primes of the form p = 6k + 1
theorem inf_p_6k_plus_one (hp : p.Prime) (hp2 : p > 3) (hs : IsSquare (-3 : ZMod p)) : (∃ (k : ℕ), p = 6*k+1) ∧ ∃ p n, _root_.Prime p ∧ (M : ℕ) ≤ p ∧ (p : ℤ) ∣ eval n (X^2 + 3 : ℤ[X]) := by
  have hp3 : p > 2 := by
    exact lt_of_succ_lt hp2
  have hp_odd : Odd p := by
    exact prime_gt_two_is_odd hp hp3
  have hp_cong_1_mod_2 : p % 2 = 1 := by
    exact n_odd_if_Odd hp_odd
  have h_leg_sym_1_rhs : legendreSym 3 p = 1 := by
    rw [← legendre_neg_3_p_eq_legendre_p_3]
    exact IsSqaure_neg_three_imp_legendre_p_neg_three_eq_one p hp hp2 hs
    case hp2 =>
      exact hp3
    exact hp
  have h_cong_1_mod_3 : (legendreSym 3 p : ZMod 3) = 1 → p % 3 = 1 := by
    intro legendreHp
    exact legendreSym_3_p_eq_1_imp_p_mod_3_1 p legendreHp
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

-- ---------------------------------------------------------------------------------------------------
-- -- Section 7: The following theorems establish a key congruence relation, a consequence of Fermats Little
-- -- theorem, and then use such relation to prove the special case of 8k + 1.
-- ---------------------------------------------------------------------------------------------------

-- Degree of x^4 + 1 is 4
theorem x_fouth_plus_one_degree_4 : natDegree (X ^ 4 + 1 : ℤ[X]) = 4 := by
  rw [natDegree_add_eq_left_of_natDegree_lt] <;>
  simp
  done

-- Proving that there exists a pair p prime, n such that p | (n^4 + 1)
theorem exists_prime_div_of_x_fouth_poly_eval (hp : (f : ℤ[X]) = X^4 + 1) : ∃ p n, _root_.Prime p ∧ (M : ℕ) ≤ p ∧ (p : ℤ) ∣ f.eval n := by
  apply two.one
  case hf =>
    rw [hp]
    rw [x_fouth_plus_one_degree_4]
    simp only
  done

-- Proving that there exists a pair p prime, n such that p | (n^4 + 1)
theorem exists_prime_divisor_for_quart_plus_one_poly_eval : ∃ p n, _root_.Prime p ∧ (M : ℕ) ≤ p ∧ (p : ℤ) ∣ eval n (X^4 + 1 : ℤ[X]):= by
  apply exists_prime_div_of_x_fouth_poly_eval
  rfl
  done

-- (a^(p-1)) ≡ (a^4)^((p-1)/4) [ZMOD p], first in chain of congruences
theorem pow_equiv_to_pow_mul_4_div_4 (hp2 : 4 ∣ p - 1) (a : ZMod p) : (a^(p-1)) = (a^4)^((p-1)/4) := by
  rw [← @pow_mul, Nat.mul_comm, Nat.div_mul_cancel hp2]
  done

-- (a^4)^((p-1)/4) ≡ (-1)^((p-1)/4) [ZMOD p], second in chain of congruences
theorem pow_of_a_equiv_pow_of_neg_1 (a : ZMod p) (ha2 : a^4 = -1) : (a^4)^((p-1)/4) = (-1)^((p-1)/4) := by
  rw [ha2]
  done

-- 1 ≡ (a^4)^((p-1)/4) [ZMOD p], last part of chain of congruences
theorem one_equiv_pow_of_neg_one_zmod_p (hp3 : 4 ∣ p - 1) (a : ZMod p) (ha1 : a ≠ 0) (ha2 : a^4 = -1) : (1 : ZMod p) = (-1)^((p-1)/4) := by
  rw [← pow_of_a_equiv_pow_of_neg_1]
  rw [← pow_equiv_to_pow_mul_4_div_4 p]
  rw [pow_card_sub_one_eq_one ha1]
  exact hp3
  exact ha2
  done

-- n % 4 = 1 if n % 8 = 1
theorem one_mod_eight_then_one_mod_four {n : ℕ} : n % 8 = 1 → n % 4 = 1 := by
  simpa [ModEq, show 2 * 4 = 8 by norm_num] using @ModEq.of_mul_left 4 n 1 2
  done

-- n % 4 = 1 if n % 8 = 5
theorem five_mod_eight_then_one_mod_four {n : ℕ} : n % 8 = 5 → n % 4 = 1 := by
  simpa [ModEq, show 2 * 4 = 8 by norm_num, show 5 % 8 = 5 by norm_num] using
    @ModEq.of_mul_left 4 n 5 2
  done

-- n % 4 = 1 iff either n % 8 = 1 or n % 8 = 5
theorem one_mod_four_iff_one_or_five_mod_eight {n : ℕ} : n % 4 = 1 ↔ n % 8 = 1 ∨ n % 8 = 5 :=
  have help : ∀ m : ℕ, m < 8 → m % 4 = 1 → m = 1 ∨ m = 5 := by decide
  ⟨fun hn =>
    help (n % 8) (mod_lt n (by norm_num)) <| (mod_mod_of_dvd n (by decide : 4 ∣ 8)).trans hn,
    fun h => Or.elim h one_mod_eight_then_one_mod_four five_mod_eight_then_one_mod_four⟩

-- p = 8k + 5 iff p % 8 = 5
theorem p_mod_8_eq_one_iff_p_eq_8k_plus_5 {p : ℕ} (hp2 : p > 5): (p % 8 = 5) ↔ (∃ (k : ℕ), p = 8*k + 5) := by
  apply Iff.intro
  case mpr =>
    simp only [forall_exists_index]
    intro k h_4k_1
    rw [h_4k_1, add_mod, mul_mod_right, zero_add, mod_mod]
    exact rfl
  case mp =>
    intro hp_mod_4
    have h_mod_equiv : 5 ≡ p [MOD 8] := by
      rw [← hp_mod_4]
      exact mod_modEq p 8
    have h_four_div_p_minus_one : 8 ∣ (p - 5) := by
      rw [← modEq_iff_dvd']
      apply h_mod_equiv
      exact Nat.le_of_lt hp2
    have h_exists_k_p1_eq_k4 : ∃ (k : ℕ), p-5=k*8 := by
      apply exists_eq_mul_left_of_dvd
      exact h_four_div_p_minus_one
    cases h_exists_k_p1_eq_k4 with
    | intro k h =>
      use k
      rw [mul_comm]
      have : 5 ≤ p := by
        exact Nat.le_of_lt hp2
      exact Nat.eq_add_of_sub_eq this h
  done

-- 8k / 4 is even
theorem eight_k_div_4_even : ((8 * k) / 4) = 2 * k := by
  have hp : (4 * (2 * k)) / 4 = 2 * k := by
    refine mul_div_right (2 * k) ?H
    simp only
    done
  rw [← hp]
  rw [@Mathlib.Tactic.RingNF.mul_assoc_rev]
  done

-- (8k + 4) / 4 is odd
theorem eight_k_plus_4_div_4_odd : (((8 * k) + 4) / 4) = 2 * k + 1:= by
  simp only [zero_lt_four, add_div_right, succ.injEq]
  exact eight_k_div_4_even
  done

-- The power (p-1)/4 is odd if p % 8 = 5
theorem fraction_is_odd (hp : p % 8 = 5) (ha : p > 5) : Odd ((p - 1) / 4) := by
  have hp2 : (∃ (k : ℕ), p = 8*k + 5) := by
    rw [← p_mod_8_eq_one_iff_p_eq_8k_plus_5]
    exact hp
    exact ha
    done
  cases hp2 with
    | intro k h =>
      rw [h]
      simp only [ge_iff_le, succ_sub_succ_eq_sub, nonpos_iff_eq_zero, add_eq_zero,
        _root_.mul_eq_zero, false_or, and_false, tsub_zero, zero_lt_four]
      have hp3 : (((8 * k) + 4) / 4) = 2 * k + 1:= by
        apply eight_k_plus_4_div_4_odd
        done
      have hp4 : Odd (((8 * k) + 4) / 4) := by
        rw [hp3]
        exact odd_two_mul_add_one k
        done
      exact hp4
  done

-- Power of negative one is negative one if p % 8 = 5 i.e. power is odd
theorem pow_of_neg_one_eq_neg_one_if_p_mod_8_5 (hp : p % 8 = 5) (ha : p > 5) : ((-1) : ZMod p) ^ ((p - 1) / 4) = -1 := by
  refine Odd.neg_one_pow ?h
  exact fraction_is_odd p hp ha
  done

-- 1 ≠ -1 in ZMod p if p is odd
theorem neg_one_ne_one (ha : Odd p) : (1 :  ZMod p) ≠ -1 := by
  apply ne_neg_self
  exact ha
  exact one_ne_zero
  done

-- Power of negative one is negative one if p % 8 = 5 i.e. power is odd
theorem pow_of_neg_one_eq_neg_one_if_p_mod_8_5' (hp : p % 8 = 5) (hp2 : ((-1) : ZMod p) ^ ((p - 1) / 4) = 1) (ha3 : p > 5) (ha4 : Odd p) : False := by
  have hp3 : ((-1) : ZMod p) ^ ((p - 1) / 4) = -1 := by
    exact pow_of_neg_one_eq_neg_one_if_p_mod_8_5 p hp ha3
  have hp4 : (-1 : ZMod p) = 1 := by
    simp_all only [ge_iff_le, odd_iff_not_even, gt_iff_lt, one_pow]
    done
  have hp5 : (-1 : ZMod p) ≠ 1 := by
    exact Ne.symm (neg_one_ne_one p ha4)
    done
  simp_all only [ge_iff_le, one_pow, gt_iff_lt]
  done

-- p % 8 = 1 if power of -1 is equivalent to 1 in ZMod p
theorem pow_of_neg_one_eq_one_imp_p_mod_8_1 (hp : p % 4 = 1) (ha2 : p.Prime) (ha3 : p > 5) (ha5 : Odd p) : ((-1) : ZMod p) ^ ((p - 1) / 4) = 1 -> p % 8 = 1 := by
  rw [p_mod_n_eq_one_iff_p_eq_nk_plus_1']
  norm_num
  intro ha4
  have hp2 : p % 8 = 1 ∨ p % 8 = 5 := by
    exact one_mod_four_iff_one_or_five_mod_eight.mp hp
    done
  have hp3 : ¬(p % 8 = 5) := by
    by_contra hp3
    exact pow_of_neg_one_eq_neg_one_if_p_mod_8_5' p hp3 ha4 ha3 ha5
    done
  have hp4 : ¬(p % 8 = 5) -> (p % 8 = 1) := by
    intro _
    simp_all only [ge_iff_le, odd_iff_not_even, or_false, OfNat.one_ne_ofNat, not_false_eq_true]
  refine (p_mod_n_eq_one_iff_p_eq_nk_plus_1' ?hp).mp (hp4 hp3)
  exact ha2
  exact ha2
  done

-- There are infinite primes of the form 8k + 1
theorem inf_p_8k_plus_one (hp : p.Prime) (hp2 : p > 5) (hs : IsSquare (-1 : ZMod p)) (a : ZMod p) (ha1 : a ≠ 0) (ha2 : a^4 = -1) : (∃ (k : ℕ), p = 8*k+1) ∧ ∃ p n, _root_.Prime p ∧ (M : ℕ) ≤ p ∧ (p : ℤ) ∣ eval n (X^4 + 1 : ℤ[X]) := by
  have h_p_gt_three : p > 3 := by
    apply lt_of_succ_lt
    apply lt_of_succ_lt
    simp_all only [gt_iff_lt, ge_iff_le, Nat.isUnit_iff, ne_eq]
    done
  have h_cong_1 : p % 4 = 1 := by
    rw [← square_eq_neg_one_mod_p_iff_p_eq_one_mod_four]
    exact hs
    exact lt_of_succ_lt h_p_gt_three
    exact hp
  have h_mod_equiv : 1 ≡ p [MOD 4] := by
    rw [← h_cong_1]
    exact mod_modEq p 4
  have h_four_div_p_minus_one : 4 ∣ (p - 1) := by
    rw [← modEq_iff_dvd']
    apply h_mod_equiv
    refine one_le_iff_ne_zero.mpr ?_
    exact Nat.Prime.ne_zero hp
  have h_1_cong_pow_minus_one_div_four : (1 : ZMod p) = (-1) ^ ((p - 1) / 4) := by
    rw [← one_equiv_pow_of_neg_one_zmod_p]
    exact h_four_div_p_minus_one
    exact a
    exact ha1
    exact ha2
    done
  apply And.intro
  case left =>
    rw [← p_mod_n_eq_one_iff_p_eq_nk_plus_1']
    norm_num
    apply pow_of_neg_one_eq_one_imp_p_mod_8_1
    exact h_cong_1
    exact hp
    exact hp2
    refine prime_gt_two_is_odd hp ?ha5.hp2
    exact lt_of_succ_lt h_p_gt_three
    exact id h_1_cong_pow_minus_one_div_four.symm
    exact hp
    done
  case right =>
    exact exists_prime_divisor_for_quart_plus_one_poly_eval
  done

end TPwLDirichlet
