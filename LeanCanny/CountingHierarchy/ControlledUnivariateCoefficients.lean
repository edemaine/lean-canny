/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledUnivariate
public import LeanCanny.CountingHierarchy.CoefficientEvaluation

/-! # Uniform coefficient residues of controlled univariate specifications -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial Polynomial

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ} {P : α → Polynomial ℤ}

noncomputable def univariateCoefficient (C : Controlled (fun w => liftUnivariate (P w)) enc a)
    (q : α × (ℕ × ℕ)) : ℕ :=
  coefficientResidue q.2.1 q.2.2 (fun t => C.evaluate (q.1, q.2.1, [t]))

theorem univariateCoefficient_mem (C : Controlled (fun w => liftUnivariate (P w)) enc a)
    (E : Decoder enc) :
    C.univariateCoefficient ∈ CountingFunction (a + 1) (encUnivariateEvaluation enc) encNat := by
  have hw : ComputableInPolyTime (fun q : (α × (ℕ × ℕ)) × ℕ => q.1.1)
      (encPair (encUnivariateEvaluation enc) encNat) enc := by fun_prop
  have hp : ComputableInPolyTime (fun q : (α × (ℕ × ℕ)) × ℕ => q.1.2.1)
      (encPair (encUnivariateEvaluation enc) encNat) encNat := by fun_prop
  have ht := ComputableInPolyTime.snd (encUnivariateEvaluation enc) encNat
  have hpoint := (ComputableTidilyInPolyTime.cons' ht.tidy (ComputableTidilyInPolyTime.const [])).computableInPolyTime
  have hv := CountingFunction.preprocess C.evaluate_mem (hw.prod (hp.prod hpoint))
  change (fun q => C.univariateCoefficient q) ∈ _
  simpa only [univariateCoefficient] using coefficientResidue_mem
    (Decoder.pair E (Decoder.pair Decoder.nat Decoder.nat)) (by fun_prop) (by fun_prop) hv

theorem univariateCoefficient_cast (C : Controlled (fun w => liftUnivariate (P w)) enc a)
    (w : α) (p k : ℕ) (hp : p.Prime)
    (hc : C.cutoff w < p) (hD : C.degreeBound w < p - 1) (hk : k < p - 1) :
    (C.univariateCoefficient (w, p, k) : ZMod p) = ((P w).coeff k : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hdeg : (P w).natDegree ≤ C.degreeBound w := by
    rw [← liftUnivariate_degree_eq]
    exact C.degree_le w
  have hv (t : ℕ) (_ht : t < p) :
      (C.evaluate (w, p, [t]) : ZMod p) = ((P w).map (Int.castRingHom (ZMod p))).eval (t : ZMod p) := by
    rw [C.evaluate_eq w p [t] hp hc]
    simp only [evaluation, ZMod.natCast_zmod_val, eval_liftUnivariate, Polynomial.eval_map,
      Fin.val_zero, List.getElem?_cons_zero, Option.getD_some]
  have h := coefficientResidue_cast ((P w).map (Int.castRingHom (ZMod p))) k _
    (Polynomial.natDegree_map_le.trans_lt (hdeg.trans_lt hD)) hk hv
  simpa only [univariateCoefficient, Polynomial.coeff_map, Int.coe_castRingHom] using h

end LeanCanny.CountingHierarchy.Controlled
