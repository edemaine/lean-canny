/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedTerminalTarskiFamily
public import LeanCanny.Algebra.IntegralMixedFramedTerminalCoordinateSelected
public import LeanCanny.Algebra.FixedWidthBivariateParameterPairEvaluation
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateOrderedQueries
public import LeanCanny.Geometry.IntegralMixedFramedWindowQuery
/-! # The native terminal heads and windows are the exact selected Near models

Only the actual older generator interpretation is required. All polynomial
identities use its literal terminal suffix and the same terminal raw tuple.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedTerminalTarskiSelected
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family RealIteratedTarski.evaluate

private theorem common_map (keep : Bool) (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (q : List Bool) (z : Fin (A q)→ℝ) :
    (FixedWidthBivariateParameterPairBits.lift keep A p q).map
      ((MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ) z).comp
        (MvPolynomial.rename (Fin.cast (FixedWidthBivariateParameterPairBits.arity_eq (A q)))).toRingHom)=
      (FixedWidthBivariateParameterPairBits.common keep A p q).map
        (MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ) z) :=by
  rw [FixedWidthBivariateParameterPairBits.common,Polynomial.map_map]

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (center selected : List Bool→ℕ) (q : List Bool)
local notation "G" => family P D H
local notation "oldKey" => IntegralMixedVirtualTaskBits.saved P (parent q)
local notation "x" => IntegralMixedCutSource.Family.state (family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q))
local notation "r" => IntegralMixedCutSource.Family.rule (family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q))
local notation "j" => IntegralMixedCoordinateCoefficientSnapshot.coordinate (family P D H)
  (IntegralMixedVirtualTaskBits.saved P (parent q)) (get P Field.slot13 (parent q))
local notation "d" => IntegralMixedSelectedCoordinateHead.fullDegree P (family P D H) parent
local notation "e" => IntegralMixedSelectedCoordinateHead.fullParameter P parent
local notation "A" => IntegralMixedFramedTerminalTarskiFamilyBits.arity P D H terminal

noncomputable def specialization (z : Fin (atKey P D H (terminal q)).count→ℝ) :
    MvPolynomial (Fin (1+((atKey P D H (terminal q)).count+1))) ℤ→+*Polynomial (Polynomial ℝ) :=
  (MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ) z).comp
    (MvPolynomial.rename (Fin.cast (FixedWidthBivariateParameterPairBits.arity_eq ((atKey P D H (terminal q)).count)))).toRingHom

noncomputable def allowance :=RationalMonomialParameterShift.sourceDegree
  (IntegralMixedFramedTerminalParameterShiftBits.endpointFamily P D H L F C hs terminal center)
  (IntegralMixedFramedCoordinateBivariateBits.nativeWidth P D H parent e) q

theorem head_selected (hcore : IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q)
    (hcount : IntegralMixedFramedTerminalCoordinateHeadBits.Valid P D H parent terminal q)
    (hi : center q<(atKey P D H (terminal q)).count)
    (φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P (parent q))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (z : Fin (atKey P D H (terminal q)).count→ℝ)
    (hφ : ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=z (UniformIntegralPowerSchedule.embed hcount i)^
      UniformIntegralPowerSchedule.weights ((G).cap oldKey) (2^(G).width oldKey) ((G).birth oldKey) i)
    (negative : Bool) :
    (IntegralMixedFramedTerminalTarskiFamilyBits.head P D H L F C hs parent terminal d e center negative q).map
      (specialization P D H terminal q z)=
      IntegralMixedSelectedCoordinateWindowDegree.head
        (IntegralMixedSelectedCoordinateAffineDegree.head x ((G).birth_bound oldKey) r j φ
          (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
            (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q)) z ⟨center q,hi⟩)
          negative (atKey P D H (terminal q)).common (allowance P D H L F C hs parent terminal center q)) :=by
  unfold IntegralMixedFramedTerminalTarskiFamilyBits.head specialization
  refine (common_map true (fun c=>(atKey P D H (terminal c)).count)
    (IntegralMixedFramedTerminalTarskiHeadBits.head P D H L F C hs parent terminal d e center negative) q z).trans ?_
  apply MvTwoParameterCoefficient.polynomial_ext
  intro ε δ
  refine (FixedWidthBivariateParameterPairBits.evaluated true (fun c=>(atKey P D H (terminal c)).count)
    (IntegralMixedFramedTerminalTarskiHeadBits.head P D H L F C hs parent terminal d e center negative) q z ε δ).trans ?_
  rw [IntegralMixedSelectedCoordinateOrderedQueries.evaluated_head]
  unfold IntegralMixedFramedTerminalTarskiHeadBits.head
  let Fη:=IntegralMixedFramedTerminalParameterShiftBits.endpointFamily P D H L F C hs terminal center
  let W:=IntegralMixedFramedCoordinateBivariateBits.nativeWidth P D H parent e
  have HA : (Fη.scalars.numerator q:ℝ)*z ⟨Fη.index q,hi⟩^Fη.weight q/(Fη.scalars.denominator q:ℝ)=
      LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
        (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q)) z ⟨center q,hi⟩ :=
    LeanCanny.Geometry.IntegralMixedFramedWindowQuery.coordinate P D H L F C hs terminal center q hi z
  refine (RationalMonomialBivariateShift.selected_head Fη negative W
    (IntegralMixedFramedTerminalCoordinateHeadBits.polynomial P D H parent terminal d e)
    (fun c y=>IntegralMixedFramedTerminalCoordinateHeadBits.source_fit P D H parent terminal d e (fun _=>y) c) q z hi
    (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.common_ne_zero P D H (terminal q)) δ).trans ?_
  have HT:=IntegralMixedFramedTerminalCoordinateSelected.full_selected P D H parent terminal q hcore hcount φ z hφ
    ((Fη.scalars.numerator q:ℝ)*z ⟨Fη.index q,hi⟩^Fη.weight q/(Fη.scalars.denominator q:ℝ)+if negative then -δ else δ)
  refine (congrArg (fun p : ℝ[X]=>Polynomial.C ((Fη.scalars.denominator q:ℝ)^
    (2*RationalMonomialParameterShift.sourceDegree Fη W q))*p) HT).trans ?_
  rw [HA]
  unfold IntegralMixedSelectedCoordinateAffineDegree.head
  rw [Polynomial.map_mul,Polynomial.map_C,Polynomial.coe_evalRingHom,Polynomial.eval_C,
    Polynomial.map_map,IntegralMixedSelectedCoordinateAffineDegree.shift_evaluate]
  rfl


theorem query_selected (hi : selected q<(atKey P D H (terminal q)).count)
    (z : Fin (atKey P D H (terminal q)).count→ℝ) (power : List Bool→Fin 3) (negative : Bool) :
    (IntegralMixedFramedTerminalTarskiFamilyBits.query P D H L F C hs terminal selected power negative q).map
      (specialization P D H terminal q z)=
      IntegralMixedSelectedCoordinateWindowDegree.query
        (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q)) z ⟨selected q,hi⟩)
        (((atKey P D H (terminal q)).common:ℝ)^2) negative (power q) :=by
  unfold IntegralMixedFramedTerminalTarskiFamilyBits.query IntegralMixedFramedTerminalTarskiFamilyBits.baseQuery specialization
  rw [Polynomial.map_pow]
  refine (congrArg (fun p : Polynomial (Polynomial (Polynomial ℝ))=>p^(power q).val)
    (common_map false (fun c=>(atKey P D H (terminal c)).count)
      (IntegralMixedFramedWindowQuery.polynomial P D H L F C hs terminal selected negative) q z)).trans ?_
  apply MvTwoParameterCoefficient.polynomial_ext
  intro ε δ
  rw [Polynomial.map_pow]
  refine (congrArg (fun p : ℝ[X]=>p^(power q).val)
    (FixedWidthBivariateParameterPairBits.evaluated false (fun c=>(atKey P D H (terminal c)).count)
      (IntegralMixedFramedWindowQuery.polynomial P D H L F C hs terminal selected negative) q z ε δ)).trans ?_
  rw [IntegralMixedSelectedCoordinateOrderedQueries.evaluated_query]
  have HW : (IntegralMixedFramedWindowQuery.polynomial P D H L F C hs terminal selected negative q).map
      (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons ε z))=
      Polynomial.C (((atKey P D H (terminal q)).common:ℝ)^2)*
        (Polynomial.X-Polynomial.C (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q)) z ⟨selected q,hi⟩)+
          Polynomial.C (if negative then -ε else ε)) :=by
    apply Polynomial.funext
    intro u
    rw [Polynomial.eval_map]
    have HE:=RationalMonomialWindowQuery.eval_cleared
      (IntegralMixedFramedWindowQuery.family P D H L F C hs terminal selected) negative q z hi
      (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.common_ne_zero P D H (terminal q)) ε u
    let Fw:=IntegralMixedFramedWindowQuery.family P D H L F C hs terminal selected
    have HA : (Fw.scalars.numerator q:ℝ)*z ⟨Fw.index q,hi⟩^Fw.weight q/(Fw.scalars.denominator q:ℝ)=
        LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q)) z ⟨selected q,hi⟩ :=
      LeanCanny.Geometry.IntegralMixedFramedWindowQuery.coordinate P D H L F C hs terminal selected q hi z
    have HF:=HE.trans (congrArg (fun a : ℝ=>(Fw.scalars.denominator q:ℝ)^2*
      (u-a+if negative then -ε else ε)) HA)
    simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_X,
      Fw,IntegralMixedFramedWindowQuery.polynomial,IntegralMixedFramedWindowQuery.family,
      IntegralMixedFramedBankScalars.scalars] using HF
  exact congrArg (fun p : ℝ[X]=>p^(power q).val) HW


theorem degree_eq : IntegralMixedFramedTerminalTarskiFamilyBits.degree d q=
    PurePowerReductionBounds.dimension ((G).ambient oldKey-(r).critical.offset.val+1) ((G).spatial oldKey).degree :=by
  rw [IntegralMixedFramedTerminalTarskiFamilyBits.degree,
    IntegralMixedFramedCoordinatePackedSelected.fullDegree_eq P D H parent q]
  exact max_eq_right (pow_pos (Nat.two_pow_pos _) _)

theorem model_selected (hcore : IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q)
    (hcount : IntegralMixedFramedTerminalCoordinateHeadBits.Valid P D H parent terminal q)
    (hi : center q<(atKey P D H (terminal q)).count) (hj : selected q<(atKey P D H (terminal q)).count)
    (φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P (parent q))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (z : Fin (atKey P D H (terminal q)).count→ℝ)
    (hφ : ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=z (UniformIntegralPowerSchedule.embed hcount i)^
      UniformIntegralPowerSchedule.weights ((G).cap oldKey) (2^(G).width oldKey) ((G).birth oldKey) i)
    (power : List Bool→Fin 3) (negativeEta negativeEpsilon : Bool) :
    RealIteratedTarski.value
      (((IntegralMixedFramedTerminalTarskiFamilyBits.family P D H L F C hs parent terminal d e center selected
        power negativeEta negativeEpsilon).head q).map (specialization P D H terminal q z))
      (((IntegralMixedFramedTerminalTarskiFamilyBits.family P D H L F C hs parent terminal d e center selected
        power negativeEta negativeEpsilon).query q).map (specialization P D H terminal q z))
      (IntegralMixedFramedTerminalTarskiFamilyBits.degree d q)
      (IntegralMixedFramedTerminalTarskiFamilyBits.inputBound d q)
      (IntegralMixedFramedTerminalTarskiFamilyBits.seedDegree d q)=
    IntegralMixedSelectedCoordinateOrderedQueries.value
      (IntegralMixedSelectedCoordinateAffineDegree.head x ((G).birth_bound oldKey) r j φ
        (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q)) z ⟨center q,hi⟩)
        negativeEta (atKey P D H (terminal q)).common (allowance P D H L F C hs parent terminal center q))
      (PurePowerReductionBounds.dimension ((G).ambient oldKey-(r).critical.offset.val+1) ((G).spatial oldKey).degree)
      (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
        (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q)) z ⟨selected q,hj⟩)
      (((atKey P D H (terminal q)).common:ℝ)^2) negativeEpsilon (power q) :=by
  change RealIteratedTarski.value
    ((IntegralMixedFramedTerminalTarskiFamilyBits.head P D H L F C hs parent terminal d e center negativeEta q).map
      (specialization P D H terminal q z))
    ((IntegralMixedFramedTerminalTarskiFamilyBits.query P D H L F C hs terminal selected power negativeEpsilon q).map
      (specialization P D H terminal q z)) _ _ _=_
  rw [head_selected P D H L F C hs parent terminal center q hcore hcount hi φ z hφ negativeEta,
    query_selected P D H L F C hs terminal selected q hj z power negativeEpsilon,
    IntegralMixedFramedTerminalTarskiFamilyBits.inputBound,IntegralMixedFramedTerminalTarskiFamilyBits.seedDegree,
    degree_eq P D H parent q]
  rfl


end LeanCanny.Algebra.IntegralMixedFramedTerminalTarskiSelected
