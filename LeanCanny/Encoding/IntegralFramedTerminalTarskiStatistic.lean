/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedScalarTarskiStatisticValue
public import LeanCanny.Encoding.IntegralFramedCompleteSquare
public import LeanCanny.Algebra.IntegralMixedFramedTerminalTarskiMass
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateHeadWidth
/-! # Actual terminal coordinate/window principal statistics

The source is the actual full physical sampler. The scalar-prefix input is
used only for its exact dimension, and contributes no root or reader cost.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalTarskiStatistic
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  FixedWidthTarskiPrincipalBits.polynomial IntegralFramedScalarTarskiStatistic.value

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (center selected : List Bool→ℕ)
variable (hpos : ∀q,0<(family P D H).birth (terminal q))
local notation "d" => IntegralMixedSelectedCoordinateHead.fullDegree P (family P D H) parent
local notation "e" => IntegralMixedSelectedCoordinateHead.fullParameter P parent

noncomputable def mf (power : Fin 3) (negativeEta negativeEpsilon : Bool) :=
  IntegralMixedFramedTerminalTarskiFamilyBits.family P D H L F C hs parent terminal d e center selected
    (fun _=>power) negativeEta negativeEpsilon
noncomputable def prefixInput :=IntegralFramedCompleteSquare.input P D H L F C hs terminal hpos
noncomputable def budget :=IntegralMixedFramedTerminalTarskiFamilyBits.wholeBound P D H L F C hs parent terminal d e center selected
noncomputable def height :=IntegralMixedFramedTerminalTarskiFamilyBits.principalHeight P D H L F C hs parent terminal d e center selected

theorem prefix_count (q : List Bool) : (prefixInput P D H L F C hs terminal hpos).count q=
    (IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal q)).count :=rfl

theorem dimensions (power : Fin 3) (negativeEta negativeEpsilon : Bool) (c b : List Bool) :
    (mf P D H L F C hs parent terminal center selected power negativeEta negativeEpsilon).arity (pairFst (pair c b))=
      (prefixInput P D H L F C hs terminal hpos).count c+2 :=by
  rw [pairFst_pair]
  change 1+((IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal c)).count+1)=
    (IntegralMixedFramedBankSnapshotBits.atKey P D H (terminal c)).count+2
  omega

theorem degree_bound (power : Fin 3) (negativeEta negativeEpsilon : Bool) (c b : List Bool) (j : ℕ) :
    (FixedWidthTarskiPrincipalBits.polynomial
      (mf P D H L F C hs parent terminal center selected power negativeEta negativeEpsilon)
      (pairFst (pair c b)) j).totalDegree≤(budget P D H L F C hs parent terminal center selected∘pairFst) (pair c b) :=by
  exact (congrArg (fun q=>(FixedWidthTarskiPrincipalBits.polynomial
    (mf P D H L F C hs parent terminal center selected power negativeEta negativeEpsilon) q j).totalDegree≤
      budget P D H L F C hs parent terminal center selected q) (pairFst_pair c b)).mpr
    (IntegralMixedFramedTerminalTarskiFamilyBits.principal_degree P D H L F C hs parent terminal d e center selected
      (fun _=>power) negativeEta negativeEpsilon c j)

theorem mass_bound (hf : ∀root,1≤F root)
    (hdefault : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (power : Fin 3) (negativeEta negativeEpsilon : Bool) (c b : List Bool) (j : ℕ) :
    MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial
      (mf P D H L F C hs parent terminal center selected power negativeEta negativeEpsilon)
      (pairFst (pair c b)) j)≤2^((height P D H L F C hs parent terminal center selected∘pairFst) (pair c b)) :=by
  exact (congrArg (fun q=>MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial
    (mf P D H L F C hs parent terminal center selected power negativeEta negativeEpsilon) q j)≤
      2^height P D H L F C hs parent terminal center selected q) (pairFst_pair c b)).mpr
    (IntegralMixedFramedTerminalTarskiFamilyBits.principal_mass P D H L F C hs parent terminal d e center selected hf hdefault
      (fun _=>power) negativeEta negativeEpsilon c j)

noncomputable def value (hf : ∀root,1≤F root)
    (hdefault : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (power : Fin 3) (negativeEta negativeEpsilon : Bool) :=
  IntegralFramedScalarTarskiStatistic.value P D H L F C hs terminal hpos
    (prefixInput P D H L F C hs terminal hpos) (prefix_count P D H L F C hs terminal hpos)
    (mf P D H L F C hs parent terminal center selected power negativeEta negativeEpsilon) pairFst
    (budget P D H L F C hs parent terminal center selected∘pairFst)
    (height P D H L F C hs parent terminal center selected∘pairFst)
    (dimensions P D H L F C hs parent terminal center selected hpos power negativeEta negativeEpsilon)
    (degree_bound P D H L F C hs parent terminal center selected power negativeEta negativeEpsilon)
    (mass_bound P D H L F C hs parent terminal center selected hf hdefault power negativeEta negativeEpsilon)

end LeanCanny.Encoding.IntegralFramedTerminalTarskiStatistic
