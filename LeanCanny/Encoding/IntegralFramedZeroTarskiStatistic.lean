/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedScalarTarskiStatisticValue
public import LeanCanny.Encoding.IntegralFramedCompleteSquare
public import LeanCanny.Algebra.IntegralMixedFramedZeroTarskiMass
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateHeadWidth
/-! # Zero-head-parameter epsilon-window principal statistics

The head is specialized at zero and independent of both dummy parameters.
The query retains epsilon at slot one. The actual full physical word is retained.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedZeroTarskiStatistic
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  FixedWidthTarskiPrincipalBits.polynomial IntegralFramedScalarTarskiStatistic.value

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (selected : List Bool→ℕ)
variable (hpos : ∀q,0<(family P D H).birth (terminal q))
local notation "d" => IntegralMixedSelectedCoordinateHead.fullDegree P (family P D H) parent
local notation "e" => IntegralMixedSelectedCoordinateHead.fullParameter P parent

noncomputable def mf (power : Fin 3) (negative : Bool) :=
  IntegralMixedFramedZeroTarskiBits.family P D H L F C hs parent terminal d e selected
    (fun _=>power) negative
noncomputable def prefixInput :=IntegralFramedCompleteSquare.input P D H L F C hs terminal hpos
noncomputable def budget :=IntegralMixedFramedZeroTarskiBits.wholeBound P D H L F C hs parent terminal d e selected
noncomputable def height :=IntegralMixedFramedZeroTarskiBits.principalHeight P D H L F C hs parent terminal d e selected

theorem prefix_count (q : List Bool) : (prefixInput P D H L F C hs terminal hpos).count q=
    (IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count :=rfl

theorem dimensions (power : Fin 3) (negative : Bool) (c b : List Bool) :
    (mf P D H L F C hs parent terminal selected power negative).arity (pairFst (pair c b))=
      (prefixInput P D H L F C hs terminal hpos).count c+2 :=by
  rw [pairFst_pair]
  rfl

theorem degree_bound (power : Fin 3) (negative : Bool) (c b : List Bool) (j : ℕ) :
    (FixedWidthTarskiPrincipalBits.polynomial
      (mf P D H L F C hs parent terminal selected power negative)
      (pairFst (pair c b)) j).totalDegree≤(budget P D H L F C hs parent terminal selected∘pairFst) (pair c b) :=by
  exact (congrArg (fun q=>(FixedWidthTarskiPrincipalBits.polynomial
    (mf P D H L F C hs parent terminal selected power negative) q j).totalDegree≤
      budget P D H L F C hs parent terminal selected q) (pairFst_pair c b)).mpr
    (IntegralMixedFramedZeroTarskiBits.principal_degree P D H L F C hs parent terminal d e selected
      (fun _=>power) negative c j)

theorem mass_bound (hf : ∀root,1≤F root)
    (hdefault : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (power : Fin 3) (negative : Bool) (c b : List Bool) (j : ℕ) :
    MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial
      (mf P D H L F C hs parent terminal selected power negative)
      (pairFst (pair c b)) j)≤2^((height P D H L F C hs parent terminal selected∘pairFst) (pair c b)) :=by
  exact (congrArg (fun q=>MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial
    (mf P D H L F C hs parent terminal selected power negative) q j)≤
      2^height P D H L F C hs parent terminal selected q) (pairFst_pair c b)).mpr
    (IntegralMixedFramedZeroTarskiBits.principal_mass P D H L F C hs parent terminal d e selected hf hdefault
      (fun _=>power) negative c j)

noncomputable def value (hf : ∀root,1≤F root)
    (hdefault : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (power : Fin 3) (negative : Bool) :=
  IntegralFramedScalarTarskiStatistic.value P D H L F C hs terminal hpos
    (prefixInput P D H L F C hs terminal hpos) (prefix_count P D H L F C hs terminal hpos)
    (mf P D H L F C hs parent terminal selected power negative) pairFst
    (budget P D H L F C hs parent terminal selected∘pairFst)
    (height P D H L F C hs parent terminal selected∘pairFst)
    (dimensions P D H L F C hs parent terminal selected hpos power negative)
    (degree_bound P D H L F C hs parent terminal selected power negative)
    (mass_bound P D H L F C hs parent terminal selected hf hdefault power negative)

end LeanCanny.Encoding.IntegralFramedZeroTarskiStatistic
