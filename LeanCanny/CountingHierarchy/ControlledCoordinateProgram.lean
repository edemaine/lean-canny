/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CoordinateCandidateEvaluation
public import LeanCanny.CountingHierarchy.ControlledUnivariate

/-! # Uniform coordinate-candidate programs composed with controlled source access -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial Polynomial

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}

noncomputable def coordinateProgram (C : Controlled F enc a) (d i j : α → ℕ)
    (q : α × (ℕ × ℕ)) : ℕ :=
  coordinateCandidateValue q.2.1 (n q.1) (d q.1) (i q.1) (j q.1) q.2.2
    (fun y => C.evaluate (q.1, q.2.1, y)) % q.2.1

theorem coordinateProgram_mem (C : Controlled F enc a) (E : Decoder enc)
    {d i j : α → ℕ} (hd : ComputableInPolyTime d enc encNat)
    (hi : ComputableInPolyTime i enc encNat) (hj : ComputableInPolyTime j enc encNat) :
    C.coordinateProgram d i j ∈ CountingFunction (a + 11) (encUnivariateEvaluation enc) encNat := by
  have hw := ComputableInPolyTime.fst enc (encPair encNat encNat)
  have hp : ComputableInPolyTime (fun q : α × (ℕ × ℕ) => q.2.1) (encUnivariateEvaluation enc) encNat := by fun_prop
  have ht : ComputableInPolyTime (fun q : α × (ℕ × ℕ) => q.2.2) (encUnivariateEvaluation enc) encNat := by fun_prop
  have hv := CountingFunction.preprocess (input := encPair (encUnivariateEvaluation enc) (encList encNat))
    C.evaluate_mem (g := fun q : (α × (ℕ × ℕ)) × List ℕ => (q.1.1, q.1.2.1, q.2)) (by fun_prop)
  have hc := coordinateCandidateValue_mem (Decoder.pair E (Decoder.pair Decoder.nat Decoder.nat)) hp
    (C.arity_computable.comp hw) (hd.comp hw) (hi.comp hw) (hj.comp hw) ht hv
  change (fun q => C.coordinateProgram d i j q) ∈ _
  simpa only [coordinateProgram, Function.comp_apply] using
    CountingFunction.nat_mod hc (CountingFunction.of_polyTime hp)

noncomputable def coordinateCutoff (C : Controlled F enc a) (d j : α → ℕ) (w : α) : ℕ :=
  max (C.cutoff w) (max (criticalCoefficientPrimeCutoff (n w) (d w))
    (max (coordinateParameterDegreeBound (n w) (d w)) (j w) + 1))

theorem coordinateCutoff_polyTime (C : Controlled F enc a) {d j : α → ℕ}
    (hd : ComputableInPolyTime d enc encNat) (hj : ComputableInPolyTime j enc encNat) :
    ComputableInPolyTime (C.coordinateCutoff d j) enc encNat :=
  ComputableInPolyTime.binary_max' C.cutoff_computable
    (ComputableInPolyTime.binary_max' (criticalCoefficientPrimeCutoff_polyTime C.arity_computable hd)
      (ComputableInPolyTime.binary_add'
        (ComputableInPolyTime.binary_max' (coordinateParameterDegreeBound_polyTime C.arity_computable hd) hj) (.const 1)))

theorem coordinateProgram_eq (C : Controlled F enc a) (d j : α → ℕ) (i : (w : α) → Fin (n w))
    (w : α) (p t : ℕ) (hp : p.Prime) (hcut : C.coordinateCutoff d j w < p)
    (hd : 1 ≤ d w) (hF : (F w).totalDegree ≤ d w + 1) :
    C.coordinateProgram d (fun w => (i w).val) j (w, p, t) =
      (((Bivariate.swap (parametricCoordinatePolynomial (d w) (F w) hF (i w))).coeff (j w)).eval₂
        (Int.castRingHom (ZMod p)) (t : ZMod p)).val := by
  let : Fact p.Prime := ⟨hp⟩
  have hc : C.cutoff w < p := (le_max_left _ _).trans_lt hcut
  have hcrit : criticalCoefficientPrimeCutoff (n w) (d w) < p :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hcut
  have hH : coordinateParameterDegreeBound (n w) (d w) < p - 1 := by
    change max (C.cutoff w) (max _ (max _ _ + 1)) < p at hcut
    omega
  have hj : j w < p - 1 := by
    change max (C.cutoff w) (max _ (max _ _ + 1)) < p at hcut
    omega
  have hv (y : List ℕ) : (C.evaluate (w, p, y) : ZMod p) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun k : Fin (n w) => (y[k.val]?.getD 0 : ZMod p)) (F w) := by
    rw [C.evaluate_eq w p y hp hc]
    exact ZMod.natCast_zmod_val _
  have h := congrArg ZMod.val (coordinateCandidateValue_cast (d w) hd (F w) hF (i w) (j w) t
    hcrit hH hj (fun y => C.evaluate (w, p, y)) hv)
  simpa only [coordinateProgram, ZMod.val_natCast] using h

end LeanCanny.CountingHierarchy.Controlled
