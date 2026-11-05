/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientMixedCutSpecialization
public import LeanCanny.Algebra.CoefficientRelativeLeadingNormalizationBounds
/-! # A fixed formal cut index specializes to the actual native quotient

The actual top multiplication-matrix entry bound supplies all trailing-index
guards beyond the characteristic budget. The formal index is chosen before
radius evaluation and is unchanged at every sufficiently large evaluation
for which the actual parent invariants hold. No whole-history bound is asserted.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientMixedCutAtInfinity
open IntegralMixedHistory IntegralMixedRelativeCuts Polynomial ParameterMatrixMassBounds
open scoped Classical
variable {A :Type*} [CommRing A] [Algebra ℤ[X] A] {n m N :ℕ} {P :SpatialSource n}

private theorem integer_survivor (q :ℤ[X]) (hq :q≠0) (bits :ℕ)
    (hMass :coefficientMass q≤2^bits) (t :ℤ) (ht :(2:ℝ)^(bits+1)≤(t:ℝ)) :q.eval t≠0:=by
  have H:=IntegralParameterInverseAtInfinity.nonzero_after_mass q hq bits hMass (t:ℝ) ht
  change q.eval₂ (Int.castRingHom ℝ) ((Int.castRingHom ℝ) t)≠0 at H
  rw [Polynomial.eval₂_at_apply] at H
  exact Int.cast_ne_zero.mp H

noncomputable def formalIndex (b :CoefficientCoordinateBasis ℤ[X] A m N)
    (bank :CoefficientHeightBank ℤ[X] A m) (low :MvPolynomial (Fin (n+1)) ℤ[X]) (a :ℤ[X])
    (r :IntegralMixedCriticalSweep.Rule n) (current :Bool) (c :Kind P r) (d :ℕ) :ℕ:=
  (Algebra.leftMulMatrix b.basis
    ((CoefficientMixedCutSpecialization.raw bank low a r current c d).coeff d)).charpoly.natTrailingDegree

theorem guards_after_radius (b :CoefficientCoordinateBasis ℤ[X] A m N)
    (bank :CoefficientHeightBank ℤ[X] A m) (low :MvPolynomial (Fin (n+1)) ℤ[X]) (a :ℤ[X])
    (r :IntegralMixedCriticalSweep.Rule n) (current :Bool) (c :Kind P r) (d entryBits radius :ℕ)
    (HE :∀i j,coefficientMass (Algebra.leftMulMatrix b.basis
      ((CoefficientMixedCutSpecialization.raw bank low a r current c d).coeff d) i j)≤2^entryBits)
    (HR :characteristicBudget (N^m) entryBits+1≤radius) :
    let χ:=(Algebra.leftMulMatrix b.basis
      ((CoefficientMixedCutSpecialization.raw bank low a r current c d).coeff d)).charpoly
    (∀k<formalIndex b bank low a r current c d,
      (Polynomial.evalRingHom ((2:ℤ)^radius)) (χ.coeff k)=0) ∧
    (Polynomial.evalRingHom ((2:ℤ)^radius)) (χ.coeff (formalIndex b bank low a r current c d))≠0:=by
  let M:=Algebra.leftMulMatrix b.basis
    ((CoefficientMixedCutSpecialization.raw bank low a r current c d).coeff d)
  change (∀k<M.charpoly.natTrailingDegree,
    (Polynomial.evalRingHom ((2:ℤ)^radius)) (M.charpoly.coeff k)=0) ∧
    (Polynomial.evalRingHom ((2:ℤ)^radius)) (M.charpoly.coeff M.charpoly.natTrailingDegree)≠0
  constructor
  · intro k hk
    rw [coeff_eq_zero_of_lt_natTrailingDegree hk,map_zero]
  · have HM :coefficientMass (M.charpoly.coeff M.charpoly.natTrailingDegree)≤
        2^characteristicBudget (N^m) entryBits:=by
      simpa only [Fintype.card_fun,Fintype.card_fin] using
        charpoly_coefficient_mass M entryBits HE M.charpoly.natTrailingDegree
    have HN :M.charpoly.coeff M.charpoly.natTrailingDegree≠0:=
      Polynomial.coeff_natTrailingDegree_ne_zero.mpr (Matrix.charpoly_monic M).ne_zero
    have HX :(2:ℝ)^(characteristicBudget (N^m) entryBits+1)≤
        (Int.castRingHom ℝ) ((2:ℤ)^radius):=by
      rw [map_pow,map_ofNat]
      exact pow_le_pow_right₀ (by norm_num :(1:ℝ)≤2) HR
    exact integer_survivor _ HN (characteristicBudget (N^m) entryBits) HM ((2:ℤ)^radius) HX

section Native
variable {cap width :ℕ} {ι :Type} [Fintype ι]
  (bank :CoefficientHeightBank ℤ[X] A m) (b :CoefficientCoordinateBasis ℤ[X] A m (2^width))
  (low :MvPolynomial (Fin (n+1)) ℤ[X]) (a :ℤ[X])
  (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
  (current :Bool) (c :Kind P r) (d radius entryBits :ℕ)
  (ψ :A→+*x.sampler.scalarPrefix.carrier)
  (HB :CoefficientHeightBank.Specializes (Polynomial.evalRingHom ((2:ℤ)^radius)) ψ bank
    (CoefficientHeightBank.ofState x))
  (Hb :CoefficientCoordinateBasis.Specializes (Polynomial.evalRingHom ((2:ℤ)^radius)) ψ b
    (CoefficientCoordinateBasis.ofIntegral x.sampler.scalarPrefix.basis))
  (HL :low.map (Polynomial.evalRingHom ((2:ℤ)^radius))=P.low)
  (HA :(Polynomial.evalRingHom ((2:ℤ)^radius)) a=P.leading)
  (HE :∀i j,coefficientMass (Algebra.leftMulMatrix b.basis
    ((CoefficientMixedCutSpecialization.raw bank low a r current c d).coeff d) i j)≤2^entryBits)
  (HR :characteristicBudget ((2^width)^m) entryBits+1≤radius)
include HB Hb HL HA HE HR

/-- The map uses one formal index, with no caller coefficient-survival guard. -/
noncomputable def specialize :
    PaddedIntegralParameterExtension.Extension
      (CoefficientMixedCutSpecialization.polynomial b bank low a r current c d
        (formalIndex b bank low a r current c d)) d (2^width)→+*
      (CoefficientMixedCutSpecialization.nativeStep x hm r current c d).sampler.scalarPrefix.carrier:=by
  have HG:=guards_after_radius b bank low a r current c d entryBits radius HE HR
  exact CoefficientMixedCutSpecialization.specialize bank b low a x hm r current c d
    (formalIndex b bank low a r current c d) (Polynomial.evalRingHom ((2:ℤ)^radius)) ψ
    HB Hb HL HA HG.1 HG.2

theorem basis_specializes [Nontrivial A] :
    CoefficientCoordinateBasis.Specializes (Polynomial.evalRingHom ((2:ℤ)^radius))
      (specialize bank b low a x hm r current c d radius entryBits ψ HB Hb HL HA HE HR)
      (b.paddedStep (CoefficientMixedCutSpecialization.polynomial b bank low a r current c d
        (formalIndex b bank low a r current c d)) d)
      (CoefficientCoordinateBasis.ofIntegral
        (CoefficientMixedCutSpecialization.nativeStep x hm r current c d).sampler.scalarPrefix.basis):=by
  have HG:=guards_after_radius b bank low a r current c d entryBits radius HE HR
  exact CoefficientMixedCutSpecialization.basis_specializes bank b low a x hm r current c d
    (formalIndex b bank low a r current c d) (Polynomial.evalRingHom ((2:ℤ)^radius)) ψ
    HB Hb HL HA HG.1 HG.2

theorem bank_specializes :
    CoefficientHeightBank.Specializes (Polynomial.evalRingHom ((2:ℤ)^radius))
      (specialize bank b low a x hm r current c d radius entryBits ψ HB Hb HL HA HE HR)
      (bank.rootStep (CoefficientMixedCutSpecialization.polynomial b bank low a r current c d
        (formalIndex b bank low a r current c d)) d (2^width)
        (CoefficientMixedCutSpecialization.leading b bank low a r current c d
          (formalIndex b bank low a r current c d)))
      (CoefficientHeightBank.ofState (CoefficientMixedCutSpecialization.nativeStep x hm r current c d)):=by
  have HG:=guards_after_radius b bank low a r current c d entryBits radius HE HR
  exact CoefficientMixedCutSpecialization.bank_specializes bank b low a x hm r current c d
    (formalIndex b bank low a r current c d) (Polynomial.evalRingHom ((2:ℤ)^radius)) ψ
    HB Hb HL HA HG.1 HG.2

end Native
end LeanCanny.Algebra.CoefficientMixedCutAtInfinity
