/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedZeroTarskiStatistic
public import LeanCanny.Algebra.IntegralMixedFramedZeroTarskiSelected
public import LeanCanny.Encoding.IntegralFramedPhysicalScalarRoots
public import LeanCanny.Encoding.IntegralFramedPhysicalOlderParent
/-! # The actual terminal statistic evaluates the same full scalar tuple -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedZeroTarskiStatistic
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  FixedWidthTarskiPrincipalBits.polynomial RealIteratedTarski.value

private noncomputable def castModel (MF : FixedWidthTarskiPrincipalBits.Family) (m : ℕ)
    (c : List Bool) (h : MF.arity c=m+2) (z : Fin m→ℝ) :=
  let χ:=(MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ) z).comp (MvPolynomial.rename (Fin.cast h)).toRingHom
  RealIteratedTarski.value ((MF.head c).map χ) ((MF.query c).map χ) (MF.degree c) (MF.bound c) (MF.seedDegree c)

private theorem castModel_context (MF : FixedWidthTarskiPrincipalBits.Family) (m : ℕ)
    (c c' : List Bool) (hcc : c=c') (h : MF.arity c=m+2) (h' : MF.arity c'=m+2) (z : Fin m→ℝ) :
    castModel MF m c h z=castModel MF m c' h' z :=by subst c';rfl

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (selected : List Bool→ℕ)
variable (hpos : ∀q,0<(family P D H).birth (terminal q))
local notation "d" => IntegralMixedSelectedCoordinateHead.fullDegree P (family P D H) parent
local notation "e" => IntegralMixedSelectedCoordinateHead.fullParameter P parent

noncomputable def rawTuple (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w) :
    Fin ((prefixInput P D H L F C hs terminal hpos).count q)→ℝ :=
  fun i=>(SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w hv).val
    (IntegralMixedFramedScalarEmbedding.scalarMap P D H (terminal q)
      (Fin.cast (prefix_count P D H L F C hs terminal hpos q) i))

theorem rawTuple_eq (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w) :
    rawTuple P D H L F C hs terminal hpos q w hv=
      IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv :=by
  funext i
  rw [IntegralFramedPhysicalSquare.scalarTuple_map]
  unfold rawTuple
  apply congrArg
  apply congrArg
  apply Fin.ext
  rfl

noncomputable def model (power : Fin 3) (negative : Bool) (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w) :=
  RealIteratedTarski.value
    (((mf P D H L F C hs parent terminal selected power negative).head q).map
      (MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ)
        (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv)))
    (((mf P D H L F C hs parent terminal selected power negative).query q).map
      (MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ)
        (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv)))
    (IntegralMixedFramedZeroTarskiBits.degree d q)
    (IntegralMixedFramedZeroTarskiBits.inputBound d q)
    (IntegralMixedFramedZeroTarskiBits.seedDegree d q)

theorem value_at (hf : ∀root,1≤F root)
    (hdefault : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (power : Fin 3) (negative : Bool) (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w) :
    value P D H L F C hs parent terminal selected hpos hf hdefault power negative (pair (pair q w) [])=
      model P D H L F C hs parent terminal selected hpos power negative q w hv :=by
  unfold value
  rw [IntegralFramedScalarTarskiStatistic.model_at (hv:=hv)]
  let MF:=mf P D H L F C hs parent terminal selected power negative
  have HT : MF.arity q=(prefixInput P D H L F C hs terminal hpos).count q+2 :=by
    rfl
  change castModel MF ((prefixInput P D H L F C hs terminal hpos).count q) (pairFst (pair q []))
    (dimensions P D H L F C hs parent terminal selected hpos power negative q [])
    (rawTuple P D H L F C hs terminal hpos q w hv)=_
  rw [castModel_context MF _ _ q (pairFst_pair q []) _ HT]
  rw [rawTuple_eq P D H L F C hs terminal hpos q w hv]
  have HC : (MvPolynomial.rename (Fin.cast HT)).toRingHom=RingHom.id (MvPolynomial (Fin (((prefixInput P D H L F C hs terminal hpos).count q)+2)) ℤ) :=by
    change (MvPolynomial.rename (id : Fin (((prefixInput P D H L F C hs terminal hpos).count q)+2)→_)).toRingHom=_
    rw [MvPolynomial.rename_id]
    rfl
  simp only [castModel,HC]
  rfl

theorem degree_full (q : List Bool) : IntegralMixedFramedZeroTarskiBits.degree d q=d q :=by
  have HD : 0<d q :=by
    rw [IntegralMixedFramedCoordinatePackedSelected.fullDegree_eq]
    unfold PurePowerReductionBounds.dimension FixedWidthPolynomial.count
    exact pow_pos (pow_pos (by decide) _) _
  unfold IntegralMixedFramedZeroTarskiBits.degree
  omega

variable (q : List Bool)
local notation "G" => family P D H
local notation "oldKey" => IntegralMixedVirtualTaskBits.saved P (parent q)
local notation "x" => IntegralMixedCutSource.Family.state (family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q))
local notation "r" => IntegralMixedCutSource.Family.rule (family P D H) (IntegralMixedVirtualTaskBits.saved P (parent q))
local notation "j" => IntegralMixedCoordinateCoefficientSnapshot.coordinate (family P D H)
  (IntegralMixedVirtualTaskBits.saved P (parent q)) (get P Field.slot13 (parent q))

theorem value_selected (hf : ∀root,1≤F root)
    (hdefault : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (power : Fin 3) (negative : Bool) (w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w)
    (hcore : IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q)
    (hcount : IntegralMixedFramedTerminalCoordinateHeadBits.Valid P D H parent terminal q)
    (hi : selected q<(IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count)
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv
        (UniformIntegralPowerSchedule.embed hcount i)^
        UniformIntegralPowerSchedule.weights ((G).cap oldKey) (2^(G).width oldKey) ((G).birth oldKey) i) :
    value P D H L F C hs parent terminal selected hpos hf hdefault power negative (pair (pair q w) [])=
      IntegralMixedSelectedCoordinateOrderedQueries.value
        (((IntegralMixedCriticalSweep.selected x ((G).birth_bound oldKey) r j φ).map (Polynomial.evalRingHom 0)).map Polynomial.C)
        (d q)
        (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q))
          (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨selected q,hi⟩)
        (((IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).common:ℝ)^2) negative power :=by
  rw [value_at P D H L F C hs parent terminal selected hpos hf hdefault power negative q w hv]
  unfold model
  change RealIteratedTarski.value
    ((IntegralMixedFramedZeroTarskiBits.head P D H parent terminal d e q).map _)
    ((IntegralMixedFramedZeroTarskiBits.query P D H L F C hs terminal selected (fun _=>power) negative q).map _)
    (IntegralMixedFramedZeroTarskiBits.degree d q)
    (IntegralMixedFramedZeroTarskiBits.inputBound d q)
    (IntegralMixedFramedZeroTarskiBits.seedDegree d q)=_
  rw [IntegralMixedFramedZeroTarskiBits.head_model P D H parent terminal q hcore hcount φ _ hφ,
    IntegralMixedFramedZeroTarskiBits.query_model P D H L F C hs terminal selected (fun _=>power) negative q hi _]
  unfold IntegralMixedFramedZeroTarskiBits.inputBound IntegralMixedFramedZeroTarskiBits.seedDegree
  rw [degree_full P D H parent q]
  rfl

theorem exists_selected (hf : ∀root,1≤F root)
    (hdefault : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w)
    (hcore : IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q)
    (hcount : IntegralMixedFramedTerminalCoordinateHeadBits.Valid P D H parent terminal q)
    (hroot : pairFst (terminal q)=pairFst oldKey)
    (hi : selected q<(IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀power : Fin 3,∀negative : Bool,
      value P D H L F C hs parent terminal selected hpos hf hdefault power negative (pair (pair q w) [])=
        IntegralMixedSelectedCoordinateOrderedQueries.value
          (((IntegralMixedCriticalSweep.selected x ((G).birth_bound oldKey) r j φ).map (Polynomial.evalRingHom 0)).map Polynomial.C)
          (d q)
          (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
            (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q))
            (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨selected q,hi⟩)
          (((IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).common:ℝ)^2) negative power :=by
  obtain ⟨φ,hφ⟩:=IntegralFramedPhysicalOlderParent.exists_interpretation P D H L F C hs terminal hpos q w hv
    oldKey hroot hcount
  exact ⟨φ,fun power negative=>value_selected P D H L F C hs parent terminal selected hpos q hf hdefault
    power negative w hv hcore hcount hi φ hφ⟩

end LeanCanny.Encoding.IntegralFramedZeroTarskiStatistic
