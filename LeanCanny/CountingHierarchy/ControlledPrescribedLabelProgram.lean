/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledUnivariateCoefficients
public import LeanCanny.CountingHierarchy.PrescribedRootLabelEvaluation
public import LeanCanny.CountingHierarchy.NativePrescribedLabelBounds

/-! # Prescribed-root label programs composed with controlled coefficient access -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial Polynomial

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ} {P : α → Polynomial ℤ}

noncomputable def prescribedLabelProgram (C : Controlled (fun w => liftUnivariate (P w)) enc a)
    (L : α → FingerprintLabelData) (q : α × (ℕ × ℕ)) : ℕ :=
  prescribedRootLabelResidue q.2.1 (C.degreeBound q.1) (C.massExponent q.1)
    (L q.1).modulus (L q.1).parameter q.2.2 (L q.1).target
    (fun j => C.univariateCoefficient (q.1, q.2.1, j)) % q.2.1

theorem prescribedLabelProgram_mem (C : Controlled (fun w => liftUnivariate (P w)) enc a)
    (E : Decoder enc) (L : α → FingerprintLabelData)
    (hmu : ComputableInPolyTime (fun w => (L w).modulus) enc encNat)
    (hgamma : ComputableInPolyTime (fun w => (L w).parameter) enc encNat)
    (htarget : ComputableInPolyTime (fun w => (L w).target) enc encIntBin) :
    C.prescribedLabelProgram L ∈ CountingFunction (max (a + 1) 3 + 8) (encUnivariateEvaluation enc) encNat := by
  have hw := ComputableInPolyTime.fst enc (encPair encNat encNat)
  have hp : ComputableInPolyTime (fun q : α × (ℕ × ℕ) => q.2.1) (encUnivariateEvaluation enc) encNat := by fun_prop
  have ht : ComputableInPolyTime (fun q : α × (ℕ × ℕ) => q.2.2) (encUnivariateEvaluation enc) encNat := by fun_prop
  have hc := CountingFunction.preprocess (input := encPair (encUnivariateEvaluation enc) encNat)
    (C.univariateCoefficient_mem E)
    (g := fun q : (α × (ℕ × ℕ)) × ℕ => (q.1.1, q.1.2.1, q.2)) (by fun_prop)
  have h := prescribedRootLabelResidue_mem (Decoder.pair E (Decoder.pair Decoder.nat Decoder.nat)) hp
    (C.degree_computable.comp hw) (C.mass_computable.comp hw) (hmu.comp hw) (hgamma.comp hw) ht
    (htarget.comp hw) hc
  change (fun q => C.prescribedLabelProgram L q) ∈ _
  simpa only [prescribedLabelProgram, Function.comp_apply] using
    CountingFunction.nat_mod h (CountingFunction.of_polyTime hp)

theorem prescribedLabelProgram_eq (C : Controlled (fun w => liftUnivariate (P w)) enc a)
    (L : α → FingerprintLabelData) (w : α) (p t : ℕ) (hp : p.Prime)
    (hc : max (C.cutoff w) (C.degreeBound w) + 1 < p) (hL : (L w).Bounded (C.degreeBound w)) :
    C.prescribedLabelProgram L (w, p, t) =
      ((fingerprintIntegerRootLabel (P w) 1 (C.degreeBound w) (C.massExponent w)
        (L w).modulus (L w).parameter (L w).target).eval₂ (Int.castRingHom (ZMod p)) (t : ZMod p)).val := by
  let : Fact p.Prime := ⟨hp⟩
  have hdeg : (P w).natDegree ≤ C.degreeBound w := by
    rw [← liftUnivariate_degree_eq]
    exact C.degree_le w
  have hmu : (L w).modulus ≠ 0 := by have := hL.1; omega
  have h := congrArg ZMod.val (prescribedRootLabelResidue_cast (P w) hdeg (by omega)
    (C.massExponent w) (L w).modulus (L w).parameter t hmu (L w).target _
    (fun j hj => C.univariateCoefficient_cast w p j hp (by omega) (by omega) (by omega)))
  simpa only [prescribedLabelProgram, ZMod.val_natCast] using h

end LeanCanny.CountingHierarchy.Controlled
