import Mathlib.Tactic

namespace TPwLDirichlet

open ZMod
open Nat
open Polynomial

def exists_infinitely_many_P : Prop := ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n

lemma fundamental_lemma {f: Polynomial ℤ} (h : degree f > 0) : exists_infinitely_many_p ∧ (∃ x : ℤ, f.eval x ≡ 0 [ZMOD p]) := by
  sorry
  done

end TPwLDirichlet
