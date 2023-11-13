import Mathlib.Tactic

namespace Dirichlet

open ZMod
open Nat
open Polynomial

lemma fundamental_lemma {f: Polynomial ℤ} (h : degree f > 0) : ∃ p, Nat.Prime p ∧ (∃ x : ℤ, f.eval x ≡ 0 [ZMOD p]) := by
  sorry
  done

end Dirichlet
