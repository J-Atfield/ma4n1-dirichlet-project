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
  let a := coeff f 0
  let g := Polynomial.divX f
  have hp3' : f = X * g + C a := by
    exact (X_mul_divX_add f).symm
    done

  have hp3 : f = X * g := by
    rw[hp3']
    simp only [eq_intCast, add_right_eq_self, Int.cast_eq_zero]
    exact hp
    done

  have hp4 : (X * g).eval n = n * g.eval n := by
    simp only [eval_mul, eval_X]
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


theorem if_min_fac_then_p_dvd_f (hp : p = minFac (f)) : (p : ℤ) ∣ f := by
  rw [hp]
  exact minFac_dvd f
  done

theorem non_trivial_case {f : ℤ[X]} (hf : f.natDegree ≠ 0) (hp : coeff f 0 ≠ 0) (M : ℕ) : ∃ p n, _root_.Prime p ∧ M ≤ p ∧ (p : ℤ) ∣ f.eval n :=
  let a := coeff f 0
  let n := M ! * a ^ 2
  let g := Polynomial.divX f

  have (notGreat : Int.natAbs (g.eval n) > 1) := sorry

  have hp3 : f = X * g + C a := by
    exact (X_mul_divX_add f).symm
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

  have f2 : a * (M !) * (g.eval (M ! * a ^ 2)) ≠ 0 := by
    have h_m : M ! ≠ 0 := by
        exact factorial_ne_zero M
    have h_a : a ≠ 0 := by
        exact hp
    have h_g : g.eval (M ! * a ^ 2) ≠ 0 := by
      sorry
    sorry
    done

  have f1 : functionAbsolute ≠ 1 := by
    apply?
    done


  have pp : Nat.Prime p := minFac_prime f1

  have np : M ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ functionAbsolute := minFac_dvd functionAbsolute
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2
    pp.not_dvd_one h₂

  have ppp : _root_.Prime p := by
    exact (primeJames p).mpr pp

  have hp9 : (p : ℤ) ∣ functionAbsolute := by
      exact if_min_fac_then_p_dvd_f rfl
      done

  have hp10 : (functionAbsolute : ℤ) ∣ f.eval n := by
    refine Int.natAbs_dvd.mpr ?_
    rw[hp8]
    apply hp7
    done

  have hp123 : ((p:ℤ) ∣ f.eval n) := by
    exact Int.dvd_trans hp9 hp10
    done


  ⟨p, n, ppp, np, hp123⟩
