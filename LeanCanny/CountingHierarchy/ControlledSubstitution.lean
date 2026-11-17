/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Controlled
public import LeanCanny.CountingHierarchy.PolynomialSubstitutionBounds

/-! # Controlled substitutions with native modular point readers -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

noncomputable def substitute {α : Type} {n m : α → ℕ}
    {P : (w : α) → MvPolynomial (Fin (n w)) ℤ} {enc : α ↪ List Bool} {a : ℕ}
    (C : Controlled P enc a) (hm : ComputableInPolyTime m enc encUnary)
    (s : (w : α) → Fin (n w) → MvPolynomial (Fin (m w)) ℤ)
    (K : α → ℕ) (hK : ComputableInPolyTime K enc encNat)
    (hdeg : ∀ w i, (s w i).totalDegree ≤ K w)
    (hmass : ∀ w i, LeanCanny.Algebra.MvMass.mass (s w i) ≤ 1)
    (read : α × (ℕ × List ℕ) → List ℕ)
    (hread : ComputableInPolyTime read (encEvaluation enc) (encList encNat))
    (hcoords : ∀ w p z (i : Fin (n w)), p.Prime →
      (read (w, p, z))[i.val]?.getD 0 % p = evaluation (s w i) p z) :
    Controlled (fun w => substitutePolynomial (s w) (P w)) enc a where
  arity_computable := hm
  degreeBound w := K w * C.degreeBound w
  degree_computable := ComputableInPolyTime.binary_mul' hK C.degree_computable
  degree_le w := (substitutePolynomial_degree_le _ _ (hdeg w) _).trans
    (Nat.mul_le_mul_left _ (C.degree_le w))
  massExponent := C.massExponent
  mass_computable := C.mass_computable
  mass_le w := (substitutePolynomial_mass_le _ (hmass w) _).trans (C.mass_le w)
  cutoff := C.cutoff
  cutoff_computable := C.cutoff_computable
  evaluate q := C.evaluate (q.1, q.2.1, read q)
  evaluate_mem := CountingFunction.preprocess C.evaluate_mem
    ((ComputableInPolyTime.fst _ _).prod
      (((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)).prod hread))
  evaluate_eq w p z hp hc := by
    let : NeZero p := ⟨hp.ne_zero⟩
    rw [C.evaluate_eq w p _ hp hc]
    unfold evaluation
    apply congrArg ZMod.val
    change MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) _ (P w) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) _
        (MvPolynomial.eval₂ MvPolynomial.C (s w) (P w))
    rw [← MvPolynomial.eval₂_assoc]
    congr 2
    funext i
    have h := congrArg (Nat.cast : ℕ → ZMod p) (hcoords w p z i hp)
    simpa only [ZMod.natCast_mod, evaluation, ZMod.natCast_zmod_val] using h

end LeanCanny.CountingHierarchy.Controlled
