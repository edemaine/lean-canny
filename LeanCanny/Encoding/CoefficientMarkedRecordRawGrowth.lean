/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProfile
public import LeanCanny.Encoding.CoefficientMarkedRecordBirthSpecialization
/-! # Original affine raw bounds for the actual retargeted current-Q cut -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordRawGrowth
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Source retargeting and the computed current denominator give the original raw cut. -/
theorem nativeRaw_retarget {a S B m:ℕ} {P Q:SpatialSource a} {I:Type}
    (hd:P.degree=Q.degree) (x:State Q S B m I) (hm:m≤S) (c:Cut P B):
    CoefficientMixedCutSpecialization.nativeRaw x hm (c.rule 1 one_ne_zero) c.current
      (CoefficientMixedCutSourceDegree.kind hd (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero)) c.degree=
    IntegralMixedCutMatrix.raw x hm
      ((CoefficientMixedCutSourceDegree.cut hd c).rule (commonDenominator x) (commonDenominator_ne_zero x))
      ((CoefficientMixedCutSourceDegree.cut hd c).kind (commonDenominator x) (commonDenominator_ne_zero x))
      (CoefficientMixedCutSourceDegree.cut hd c).degree:=by
  cases P
  cases Q
  dsimp only at hd
  cases hd
  rcases c with ⟨cr,h,hf,tag,j,k,d,hs,hb,cur⟩
  cases cur <;> cases tag <;> rfl

theorem nativeTop_retarget {a S B m:ℕ} {P Q:SpatialSource a} {I:Type}
    (hd:P.degree=Q.degree) (x:State Q S B m I) (hm:m≤S) (c:Cut P B):
    (CoefficientMixedCutSpecialization.nativeRaw x hm (c.rule 1 one_ne_zero) c.current
      (CoefficientMixedCutSourceDegree.kind hd (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero)) c.degree).coeff c.degree=
    (IntegralMixedCutMatrix.raw x hm
      ((CoefficientMixedCutSourceDegree.cut hd c).rule (commonDenominator x) (commonDenominator_ne_zero x))
      ((CoefficientMixedCutSourceDegree.cut hd c).kind (commonDenominator x) (commonDenominator_ne_zero x))
      (CoefficientMixedCutSourceDegree.cut hd c).degree).coeff (CoefficientMixedCutSourceDegree.cut hd c).degree:=by
  rw [nativeRaw_retarget]
  rfl

variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

theorem raw_eq_original {S m:ℕ} {I:Type} (ctx:List Bool) (radius:List Bool→ℕ)
    (x:State (CoefficientMarkedRecordNative.source (n:=n) (t:=t) ctx radius)
      S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m I) (hm:m≤S) (code:List Bool):
    let c:=CoefficientMarkedRecordPrefix.cut hn ht ha ctx m code
    CoefficientMixedCutSpecialization.nativeRaw x hm (c.rule 1 one_ne_zero) c.current
      (CoefficientMixedCutSourceDegree.kind
        (CoefficientMarkedRecordNative.source_degree (n:=n) (t:=t) ctx radius)
        (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero)) c.degree=
    let actual:=CoefficientMarkedRecordNative.cut hn ht ha ctx radius m code
    IntegralMixedCutMatrix.raw x hm
      (actual.rule (commonDenominator x) (commonDenominator_ne_zero x))
      (actual.kind (commonDenominator x) (commonDenominator_ne_zero x)) actual.degree:=by
  dsimp only
  have H:=nativeRaw_retarget
    (CoefficientMarkedRecordNative.source_degree (n:=n) (t:=t) ctx radius) x hm
    (CoefficientMarkedRecordPrefix.cut hn ht ha ctx m code)
  rw [CoefficientMarkedRecordBirthSpecialization.cut_transport hn ht ha ctx radius m code] at H
  exact H

theorem raw_coefficient_eq_original {S m:ℕ} {I:Type} (ctx:List Bool) (radius:List Bool→ℕ)
    (x:State (CoefficientMarkedRecordNative.source (n:=n) (t:=t) ctx radius)
      S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m I) (hm:m≤S) (code:List Bool):
    let c:=CoefficientMarkedRecordPrefix.cut hn ht ha ctx m code
    (CoefficientMixedCutSpecialization.nativeRaw x hm (c.rule 1 one_ne_zero) c.current
      (CoefficientMixedCutSourceDegree.kind
        (CoefficientMarkedRecordNative.source_degree (n:=n) (t:=t) ctx radius)
        (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero)) c.degree).coeff c.degree=
    let actual:=CoefficientMarkedRecordNative.cut hn ht ha ctx radius m code
    (IntegralMixedCutMatrix.raw x hm
      (actual.rule (commonDenominator x) (commonDenominator_ne_zero x))
      (actual.kind (commonDenominator x) (commonDenominator_ne_zero x)) actual.degree).coeff actual.degree:=by
  dsimp only
  have H:=nativeTop_retarget
    (CoefficientMarkedRecordNative.source_degree (n:=n) (t:=t) ctx radius) x hm
    (CoefficientMarkedRecordPrefix.cut hn ht ha ctx m code)
  rw [CoefficientMarkedRecordBirthSpecialization.cut_transport hn ht ha ctx radius m code] at H
  exact H

attribute [local irreducible] CoefficientMarkedRecordNative.run
  CoefficientMarkedRecordPrefix.cut CoefficientMarkedRecordNative.cut

theorem finite_basis_bound (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ)
    (hk:k<IntegralMixedCausalRecordPlanBits.count ctx)
    (hc:IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k)=false)
    (i j:Fin (FixedWidthPolynomial.count
      ((CoefficientMarkedPreludeActual.indices n ctx).length+(CoefficientMarkedRecordActual.codes ctx k).length)
      (CoefficientMarkedIntegerBirth.width hn ht ha ctx))):
    let x:=CoefficientMarkedRecordNative.run hn ht ha ctx radius
      (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
      (CoefficientMarkedRecordActual.codes ctx k)
      (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk.le)
    let c:=CoefficientMarkedRecordPrefix.cut hn ht ha ctx
      ((CoefficientMarkedPreludeActual.indices n ctx).length+(CoefficientMarkedRecordActual.codes ctx k).length)
      (IntegralMixedCausalRecordPlanBits.code ctx k)
    (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
      ((CoefficientMixedCutSpecialization.nativeRaw x
        (by
          rw [CoefficientMarkedRecordActual.codes_length]
          exact CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk.le)
        (c.rule 1 one_ne_zero) c.current
        (CoefficientMixedCutSourceDegree.kind
          (CoefficientMarkedRecordNative.source_degree (n:=n) (t:=t) ctx radius)
          (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero)) c.degree).coeff c.degree) i j).natAbs≤
      2^(IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx*radius ctx+
        IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha ctx):=by
  dsimp only
  rw [raw_coefficient_eq_original]
  have H:=CoefficientMarkedRecordProfile.original_cut_top_bound hn ht ha ctx radius k hk hc i.val j.val
  dsimp only at H
  exact (congrArg Int.natAbs (IntegralCriticalTotalSnapshotBits.integerEntry_fin _ i j)).symm.trans_le H

end LeanCanny.Encoding.CoefficientMarkedRecordRawGrowth
