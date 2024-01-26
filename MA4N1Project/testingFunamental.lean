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

theorem james_trivial {f : ℤ[X]} {g : ℤ[X]} (hp : coeff f 0 = 0) : n ∣ (f.eval n) := by
  have hp2 : f.eval 0 = 0 := by
    rw[<-coeff_zero_eq_eval_zero]
    exact hp
    done
  have hp3 : f = X * g := by
    sorry
    done
  have hp4 : (X * g).eval n = n * g.eval n := by
    simp_all only [mul_coeff_zero, coeff_X_zero, zero_mul, eval_mul, eval_X]
    done
  rw [hp3]
  rw [hp4]
  exact Int.dvd_mul_right n (eval n g)
  done

theorem primeJames (p : ℕ): (_root_.Prime p) ↔ (Nat.Prime p) := by
  exact Iff.symm prime_iff
  done


theorem trivial_case (M : ℕ) {f : ℤ[X]} (hp : coeff f 0 = 0) : ∃ p n, _root_.Prime p ∧ M ≤ p ∧ (p : ℤ) ∣ f.eval n :=
  let p := minFac (M ! + 1)
  let n := p
  have f1 : M ! + 1 ≠ 1 := Nat.ne_of_gt <| succ_lt_succ <| factorial_pos _
  have pp : Nat.Prime p := minFac_prime f1
  have ppp : _root_.Prime p := by
    exact (primeJames p).mpr pp
  have hp2 : (p:ℤ) ∣ f.eval p := by
    apply james_trivial hp
    exact f
    done
  have np : M ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ M ! := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
      pp.not_dvd_one h₂
  ⟨p, n, ppp, np, hp2⟩

theorem if_min_fac_then_p_dvd_f (hp : p = minFac (f)) : p ∣ f := by
  sorry
  done

theorem non_trivial_case {f : ℤ[X]} {g : ℤ[X]} (hf : f.natDegree ≠ 0) (hp : coeff f 0 ≠ 0) (M : ℕ) : ∃ p n, _root_.Prime p ∧ M ≤ p ∧ (p : ℤ) ∣ f.eval n :=
  let a := coeff f 0
  let n := M ! * a ^ 2

  have hp3 : f = X * g + C a := by
    sorry
    done

  have simple : eval n X = n := by
    exact eval_X
    done

  have hp4 : f.eval n = n * g.eval n + a := by
    rw[hp3]
    rw [@eval_add]
    rw [@eval_C]
    rw [@eval_mul]
    rw [eval_X]
    done

  have hp5 : f.eval (M ! * a ^ 2) = (M ! * a ^ 2) * g.eval (M ! * a ^ 2) + a := by
    simp only
    exact hp4
    done

  have hp6 : ((M ! * a ^ 2) * g.eval (M ! * a ^ 2) + a) = a * (a * (M !) * (g.eval (M ! * a ^ 2)) + 1) := by
    rw [@cast_comm]
    rw [sq a]
    ring
    done

  have hp7 : (a * (M !) * (g.eval (M ! * a ^ 2)) + 1) ∣ a * (a * (M !) * (g.eval (M ! * a ^ 2)) + 1) := by
    exact Int.dvd_mul_left a (a * ↑M ! * eval (↑M ! * a ^ 2) g + 1)
    done

  have hp8 : (f.eval n ) = a * (a * (M !) * (g.eval (M ! * a ^ 2)) + 1) := by
    rw[hp5]
    rw[hp6]
    done

  let functionAbsolute := Int.natAbs (a * (M !) * (g.eval (M ! * a ^ 2)) + 1)
  let p := minFac (functionAbsolute)
  have f1 : functionAbsolute ≠ 1 := sorry
  have pp : Nat.Prime p := minFac_prime f1

  have np : M ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ functionAbsolute := minFac_dvd functionAbsolute
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2
    pp.not_dvd_one h₂

  have ppp : _root_.Prime p := by
    exact (primeJames p).mpr pp

  have hp2 : p ∣ functionAbsolute := by
    exact if_min_fac_then_p_dvd_f rfl
    done

  have hp123 : ((p:ℤ) ∣ f.eval n) := by

    done


  ⟨p, n, ppp, np, hp2⟩
