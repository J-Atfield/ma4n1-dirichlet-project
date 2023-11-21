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
  
--
theorem p_not_three_mod_four_implies_p_one_mod_four' {p : ℕ } (hp : Odd p) : ¬(p % 4 = 3) -> (p % 4 = 1) := by
  have h_imp_equiv_or : (p % 4 = 1) ∨ (p % 4 = 3) := by
  {
    apply p_odd_then_one_or_three_mod_four
    exact hp
  }
  {

  }
  done


variable {a b : Prop}

theorem imp_to_or_not (h: a -> b) : ¬a ∨ b :=
by
  exact not_or_of_imp h
  done

variable {a b : Prop}


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


-- For
theorem square_plus_one_implies_prime_mod_four {p : ℕ} (hp : p.Prime) (hp2 : p > 2) (x : ℕ) : (x ^ 2 + 1) % p = 0 → p % 4 = 1 := by
  intro h
  have hp_ne_2 : p ≠ 2 := by
  {
    norm_num
    exact Nat.ne_of_gt hp2
  }
  have hp_odd : p % 2 = 1 := by
  {
    sorry
  }
  {
    sorry
  }
  done

theorem neg_1_square_mod {p : ℕ} (h : IsSquare (-1)) : p % 4 = 1 := by
  have hp :
  done

-- theorem p_not_cong_3_mod_4_imp_cong_1_mod_4 {p : ℕ} (hp: Nat.Prime p) (hp2 : p > 2) : ¬(p % 4 = 3) → (p % 4 = 1) := by
--   have hp_odd : Odd p := by
--   {
--      apply prime_gt_two_is_odd
--      assumption
--      assumption
--   }
--   {
--     intro h_3_not_cong
--     have h_not_0 : p % 4 ≠ 0 := by
--     {
--       sorry
--     }
--     -- have h_not_1 : p % 4 ≠ 0 := by contradiction
--     have h_not_2 : p % 4 ≠ 2 :=
--     {
--       by_contradiction h
--       have hp_odd: Odd p := prime_gt_two_is_odd hp



--     }
--     have h_not_3 : p % 4 ≠ 3 := by assumption
--   }
--   done

end TPwLDirichlet
