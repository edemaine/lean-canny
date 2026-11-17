/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledPrescribedLabelProgram

/-! # Controlled prescribed-root labels with source-only bounds -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial Polynomial LeanCanny.Algebra

noncomputable def prescribedLabel {α : Type} {enc : α ↪ List Bool} {a : ℕ} {P : α → Polynomial ℤ}
    (C : Controlled (fun w => liftUnivariate (P w)) enc a) (E : Decoder enc)
    (L : α → FingerprintLabelData) (hL : ∀ w, (L w).Bounded (C.degreeBound w))
    (hmu : ComputableInPolyTime (fun w => (L w).modulus) enc encNat)
    (hgamma : ComputableInPolyTime (fun w => (L w).parameter) enc encNat)
    (htarget : ComputableInPolyTime (fun w => (L w).target) enc encIntBin) :
    Controlled (fun w => liftUnivariate (fingerprintIntegerRootLabel (P w) 1
      (C.degreeBound w) (C.massExponent w) (L w).modulus (L w).parameter (L w).target))
      enc (max (a + 1) 3 + 8) := by
  have hb (w : α) : coefficientMass (P w) ≤ 2 ^ C.massExponent w := by
    rw [← liftUnivariate_mass_eq]
    exact C.mass_le w
  have hD (w : α) : (P w).natDegree ≤ C.degreeBound w := by
    rw [← liftUnivariate_degree_eq]
    exact C.degree_le w
  have hbound (w : α) := fingerprintIntegerRootLabel_bounds (P w) 1 (C.degreeBound w) (C.massExponent w)
    (L w) (hL w) (hD w) (by simp) (hb w) (by
      change coefficientMass (Polynomial.C (1 : ℤ)) ≤ _
      rw [coefficientMass_C]
      exact Nat.one_le_two_pow)
  exact univariate _ (fun w => prescribedRootLabelDegreeBound (C.degreeBound w) (C.massExponent w))
    (fun w => prescribedRootLabelMassExponent (C.degreeBound w) (C.massExponent w))
    (fun w => max (C.cutoff w) (C.degreeBound w) + 1)
    (prescribedRootLabelDegreeBound_polyTime C.degree_computable C.mass_computable)
    (prescribedRootLabelMassExponent_polyTime C.degree_computable C.mass_computable)
    (ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_max' C.cutoff_computable C.degree_computable) (.const 1))
    (fun w => (hbound w).1) (fun w => (hbound w).2)
    (C.prescribedLabelProgram L) (C.prescribedLabelProgram_mem E L hmu hgamma htarget)
    (fun w p t hp hc => C.prescribedLabelProgram_eq L w p t hp hc (hL w))

end LeanCanny.CountingHierarchy.Controlled
