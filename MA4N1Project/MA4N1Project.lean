import Mathlib.Tactic

namespace TPwLDirichlet

open ZMod
open Nat
open Polynomial

def exists_infinitely_many_P : Prop := ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n

lemma fundamental_lemma {f: Polynomial ℤ} (h : degree f > 0) : exists_infinitely_many_P ∧ (∃ x : ℤ, f.eval x ≡ 0 [ZMOD p]) := by
  sorry
  done

lemma x_mod_4_lt_4 {x : ℤ} : x % 4 < 4 := by
  refine Int.emod_lt_of_pos x ?H
  norm_num
  done
    -- intro h_not_congruent_3
    -- have hmod : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3

-- lemma x_not_cong_3_iff_cong_1_mod_4 {x : ℤ} : ¬(x ≡ 3 [ZMOD 4]) ↔ (x ≡ 1 [ZMOD 4]) := by
--   apply Iff.intro
--   · intro h

--   done

-- lemma x_not_cong_3_iff_cong_1_mod_4' {x : ℕ} : ¬(x ≡ 3 [MOD 4]) ↔ (x ≡ 1 [MOD 4]) := by
--   apply Iff.intro
--   {
--     intro h_not_congruent_3

--   }
--   done

-- lemma neq_one_quad_residue_mod_prime_iff_prime_cong_1_mod_4 {x : ℤ} {p : ℕ} (hp : p.Prime) (hp2 : p > 2) : x^2 + 1 ≡ 0 [ZMOD p] ↔ (p ≡ 1 [ZMOD 4]) := by
--   apply Iff.intro
--   · sorry
--   ·
--   done

def n_odd (n : ℕ) : Prop := n % 2 = 1

lemma n_odd_if_Odd {n : ℕ} (h : Odd n) : n % 2 = 1 := by
  rcases h with ⟨k, hk⟩
  rw [hk]

  done

theorem prime_gt_two_is_odd {p : ℕ} (hp : Nat.Prime p) (hp2 : p > 2) : Odd p := by
  refine Prime.odd_of_ne_two hp ?h_two
  norm_num
  exact Nat.ne_of_gt hp2
  done

theorem square_plus_one_implies_prime_mod_four {p : ℕ} (hp : p.Prime) (hp2 : p > 2) (x : ℕ) : (x ^ 2 + 1) % p = 0 → p % 4 = 1 := by
  intro h
  have hp_ne_2 : p ≠ 2 := by
  {
    norm_num
    exact Nat.ne_of_gt hp2
  }
  have hp_odd : p % 2 = 1 := by
  {

  }
  done

end TPwLDirichlet
