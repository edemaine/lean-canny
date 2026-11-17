/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.UnivariateLift
public import LeanCanny.CountingHierarchy.PointBlocks

/-! # Controlled univariate families from uniform native residue programs -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

abbrev encUnivariateEvaluation {α : Type} (enc : α ↪ List Bool) : (α × (ℕ × ℕ)) ↪ List Bool :=
  encPair enc (encPair encNat encNat)

namespace Controlled

noncomputable def univariate {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (P : α → Polynomial ℤ) (D b cutoff : α → ℕ)
    (hD : ComputableInPolyTime D enc encNat) (hb : ComputableInPolyTime b enc encNat)
    (hcut : ComputableInPolyTime cutoff enc encNat)
    (hdeg : ∀ w, (P w).natDegree ≤ D w) (hmass : ∀ w, LeanCanny.Algebra.coefficientMass (P w) ≤ 2 ^ b w)
    (value : α × (ℕ × ℕ) → ℕ)
    (hvalue : value ∈ CountingFunction a (encUnivariateEvaluation enc) encNat)
    (hcorrect : ∀ w p t, p.Prime → cutoff w < p →
      value (w, p, t) = ((P w).eval₂ (Int.castRingHom (ZMod p)) (t : ZMod p)).val) :
    Controlled (fun w => liftUnivariate (P w)) enc a where
  arity_computable := .const 1
  degreeBound := D
  degree_computable := hD
  degree_le w := (liftUnivariate_degree_le (P w)).trans (hdeg w)
  massExponent := b
  mass_computable := hb
  mass_le w := (liftUnivariate_mass_le (P w)).trans (hmass w)
  cutoff := cutoff
  cutoff_computable := hcut
  evaluate q := value (q.1, q.2.1, q.2.2[0]?.getD 0)
  evaluate_mem := by
    have hw := ComputableInPolyTime.fst enc (encPair encNat (encList encNat))
    have hp : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.1) (encEvaluation enc) encNat := by fun_prop
    have hz : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.2) (encEvaluation enc) (encList encNat) := by fun_prop
    have ht : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.2[0]?.getD 0) (encEvaluation enc) encNat := by
      simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
        ComputableInPolyTime.listGetD_binary 0 hz (ComputableInPolyTime.const 0)
    exact CountingFunction.preprocess hvalue (hw.prod (hp.prod ht))
  evaluate_eq w p z hp hc := by
    rw [hcorrect w p _ hp hc]
    unfold evaluation
    rw [eval_liftUnivariate]
    rfl

end Controlled
end LeanCanny.CountingHierarchy
