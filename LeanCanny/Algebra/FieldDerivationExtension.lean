/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.TranscendentalDerivation
public import LeanCanny.Algebra.MvCoefficientDerivation

/-! # Extending derivations through characteristic-zero field extensions

Hold a transcendence basis fixed and differentiate coefficients on its
polynomial algebra. Localization and separability then extend this derivation
to the entire field. No finiteness assumption on the field extension is used.
-/

@[expose] public section

namespace LeanCanny.Algebra.FieldDerivationExtension
open MvPolynomial
open scoped IntermediateField.algebraAdjoinAdjoin

variable {K B L ι : Type*} [Field K] [Field B] [Field L]
  [Algebra K B] [Algebra K L] [Algebra B L] [IsScalarTower K B L]
  {v : ι → L}

noncomputable def onAdjoin (D : Derivation K B B) (hv : AlgebraicIndependent B v) :
    Derivation K (Algebra.adjoin B (Set.range v)) L where
  toLinearMap := ((MvPolynomial.aeval v).restrictScalars K).toLinearMap.comp
    ((MvCoefficientDerivation.derivation D).toLinearMap.comp (hv.repr.restrictScalars K).toLinearMap)
  map_one_eq_zero' := by
    change MvPolynomial.aeval v (MvCoefficientDerivation.derivation D (hv.repr 1)) = 0
    simp
  leibniz' a b := by
    change MvPolynomial.aeval v (MvCoefficientDerivation.derivation D (hv.repr (a * b))) =
      a • MvPolynomial.aeval v (MvCoefficientDerivation.derivation D (hv.repr b)) +
        b • MvPolynomial.aeval v (MvCoefficientDerivation.derivation D (hv.repr a))
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hv.aeval_repr, Algebra.smul_def]
    ac_rfl

theorem onAdjoin_algebraMap (D : Derivation K B B) (hv : AlgebraicIndependent B v) (b : B) :
    onAdjoin D hv (algebraMap B (Algebra.adjoin B (Set.range v)) b) = algebraMap B L (D b) := by
  change MvPolynomial.aeval v (MvCoefficientDerivation.derivation D (hv.repr (algebraMap B _ b))) = _
  rw [hv.repr.commutes]
  change MvPolynomial.aeval v (MvCoefficientDerivation.derivation D (C b)) = _
  rw [MvCoefficientDerivation.derivation_C, MvPolynomial.aeval_C]

theorem exists_of_basis [CharZero B] (D : Derivation K B B) (hv : IsTranscendenceBasis B v) :
    ∃ δ : Derivation K L L, ∀ b : B, δ (algebraMap B L b) = algebraMap B L (D b) := by
  let A := Algebra.adjoin B (Set.range v)
  let F := IntermediateField.adjoin B (Set.range v)
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap B F).injective
  let : Algebra.IsAlgebraic F L := hv.isAlgebraic_field
  let : Algebra.FormallyEtale A F := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  let : Algebra.FormallyEtale F L := Algebra.FormallyEtale.of_isSeparable F L
  let : Algebra.FormallyEtale A L := Algebra.FormallyEtale.comp A F L
  refine ⟨EtaleDerivation.extend (onAdjoin D hv.1), ?_⟩
  intro b
  have h := EtaleDerivation.extend_algebraMap (onAdjoin D hv.1) (algebraMap B A b)
  rw [onAdjoin_algebraMap] at h
  change EtaleDerivation.extend (onAdjoin D hv.1) (algebraMap A L (algebraMap B A b)) = _ at h
  rw [IsScalarTower.algebraMap_apply B A L] at h
  exact h

theorem exists_extension [CharZero B] (D : Derivation K B B) :
    ∃ δ : Derivation K L L, ∀ b : B, δ (algebraMap B L b) = algebraMap B L (D b) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis B L
  exact exists_of_basis D hs

end LeanCanny.Algebra.FieldDerivationExtension
