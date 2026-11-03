/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTerminalTarskiStatistic
public import LeanCanny.Algebra.IntegralMixedFramedTerminalTarskiSelected
public import LeanCanny.Encoding.IntegralFramedPhysicalScalarRoots
/-! # The actual terminal statistic evaluates the same full scalar tuple -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalTarskiStatistic
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
variable (parent terminal : List Bool→List Bool) (center selected : List Bool→ℕ)
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

noncomputable def model (power : Fin 3) (negativeEta negativeEpsilon : Bool) (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w) :=
  RealIteratedTarski.value
    (((mf P D H L F C hs parent terminal center selected power negativeEta negativeEpsilon).head q).map
      (IntegralMixedFramedTerminalTarskiSelected.specialization P D H terminal q
        (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv)))
    (((mf P D H L F C hs parent terminal center selected power negativeEta negativeEpsilon).query q).map
      (IntegralMixedFramedTerminalTarskiSelected.specialization P D H terminal q
        (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv)))
    (IntegralMixedFramedTerminalTarskiFamilyBits.degree d q)
    (IntegralMixedFramedTerminalTarskiFamilyBits.inputBound d q)
    (IntegralMixedFramedTerminalTarskiFamilyBits.seedDegree d q)

theorem value_at (hf : ∀root,1≤F root)
    (hdefault : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (power : Fin 3) (negativeEta negativeEpsilon : Bool) (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w) :
    value P D H L F C hs parent terminal center selected hpos hf hdefault power negativeEta negativeEpsilon (pair (pair q w) [])=
      model P D H L F C hs parent terminal center selected hpos power negativeEta negativeEpsilon q w hv :=by
  unfold value
  rw [IntegralFramedScalarTarskiStatistic.model_at (hv:=hv)]
  let MF:=mf P D H L F C hs parent terminal center selected power negativeEta negativeEpsilon
  have HT : MF.arity q=(prefixInput P D H L F C hs terminal hpos).count q+2 :=by
    change 1+((IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count+1)=
      (IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count+2
    omega
  change castModel MF ((prefixInput P D H L F C hs terminal hpos).count q) (pairFst (pair q []))
    (dimensions P D H L F C hs parent terminal center selected hpos power negativeEta negativeEpsilon q [])
    (rawTuple P D H L F C hs terminal hpos q w hv)=_
  rw [castModel_context MF _ _ q (pairFst_pair q []) _ HT]
  rw [rawTuple_eq P D H L F C hs terminal hpos q w hv]
  rfl

end LeanCanny.Encoding.IntegralFramedTerminalTarskiStatistic
