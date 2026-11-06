/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalWindowRetention
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGridRetention
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalCoefficient
/-! # The actual squarefree index persists along an actual joint stratum path -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointSquarefreeIndexRetention
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.ETR Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial
local notation "Raw"=>FormulaSignSlotRadialPrincipalRadiusSource.source
local notation "N"=>FormulaSignSlotRadialCutWindowSources.principalCenters
local notation "hd"=>FormulaSignSlotRadialCutWindowSources.principal_dimension
local notation "Space"=>FormulaSignSlotRadialJointStratumLabels.Space
local notation "S"=>FormulaSignSlotRadialJointStratum.source
local notation "env"=>FormulaSignSlotRadialJointDescriptorGeometry.environment
local notation "radial"=>FormulaSignSlotRadialJointPrincipalWindowRetention.radial
local notation "raw"=>FormulaSignSlotRadialJointPrincipalWindowRetention.raw

/-- The radius reader unflattens the actual signed principal, with no degree choice. -/
theorem radius_polynomial (z:List Bool):
    IntegralPolynomialRadiusReader.polynomial Raw N hd z=
      FormulaSignSlotRadialCenterPrincipalCoefficient.radiusPolynomial
        (FormulaSignSlotRadialPrincipalRadiusSource.family z)
        (FormulaSignSlotRadialPrincipalRadiusSource.order z):=by
  unfold IntegralPolynomialRadiusReader.polynomial IntegralPolynomialRadiusReader.castPolynomial
  have HC:Fin.cast (hd z)=id:=by funext i;exact Fin.ext rfl
  rw [HC,MvPolynomial.rename_id]
  change (MvPolynomial.finSuccEquiv ℤ _) (FormulaSignSlotRadialCenterPrincipalFamily.principal _ _)=_
  rw [FormulaSignSlotRadialCenterPrincipalFamily.principal_map]
  exact AlgEquiv.apply_symm_apply _ _

private def selected (u:List Bool) (v:ℕ→ℝ) (t d:ℕ):Prop:=
  FormulaSignSlotRadialCenterSelection.Guards u (fun i=>v (4*i.val)) t d
private noncomputable def signedValue (u:List Bool) (v:ℕ→ℝ) (p:ℕ):=
  FormulaSignSlotRadialCenterPrincipalCoefficient.specialized u (fun i=>v (4*i.val)) p
private theorem head_value (z:List Bool) (v:ℕ→ℝ):
    IntegralPolynomialWindowTarski.baseHead Raw N hd z (fun i=>v (4*i.val))=
      signedValue (FormulaSignSlotRadialPrincipalRadiusSource.family z) v
        (FormulaSignSlotRadialPrincipalRadiusSource.order z):=by
  unfold IntegralPolynomialWindowTarski.baseHead
  rw [radius_polynomial]
  rfl
attribute [local irreducible] signedValue
private theorem selected_packet (u:List Bool) (v:ℕ→ℝ) (t d p:ℕ):
    IntegralPolynomialWindowTarski.baseHead Raw N hd
      (FormulaSignSlotRadialPrincipalWindowBounds.rawContext u t d p) (fun i=>v (4*i.val))=
    signedValue (pair u (pair (BinaryNatCode.encode t) (BinaryNatCode.encode d))) v p:=by
  rw [head_value]
  simp only [FormulaSignSlotRadialPrincipalWindowBounds.rawContext,
    FormulaSignSlotRadialPrincipalRadiusSource.family,FormulaSignSlotRadialPrincipalRadiusSource.order,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

private noncomputable def unsignedValue (u:List Bool) (v:ℕ→ℝ) (t d p:ℕ):=
  (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst u) (fun i=>v (4*i.val)))
    (FormulaSignSlotRadialCenterSquarefreeSelection.principal u t d p)
private noncomputable def mappedPolynomial (u:List Bool) (v:ℕ→ℝ) (t d:ℕ):=
  (FormulaSignSlotRadialCenterSquarefreeSelection.polynomial u t d).map
    (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst u) (fun i=>v (4*i.val)))
private theorem mappedPolynomial_eq (u:List Bool) (v:ℕ→ℝ) (t d:ℕ)
    (HS:FormulaSignSlotRadialCenterSelection.Guards u (fun i=>v (4*i.val)) t d):
    mappedPolynomial u v t d=FormulaSignSlotRadialCenterSquarefreeSelection.coordinate u (fun i=>v (4*i.val)):=
  FormulaSignSlotRadialCenterSquarefreeSelection.polynomial_map u (fun i=>v (4*i.val)) t d HS
/-- The constructed radius polynomial is the actual signed PSC after specialization. -/
theorem principal_polynomial (u:List Bool) (v:ℕ→ℝ) (t d k:ℕ)
    (HS:FormulaSignSlotRadialCenterSelection.Guards u (fun i=>v (4*i.val)) t d):
    IntegralPolynomialWindowTarski.baseHead Raw N hd
      (FormulaSignSlotRadialPrincipalWindowBounds.rawContext u t d k) (fun i=>v (4*i.val))=
    PrincipalSubresultant.signedPsc
      (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate u (fun i=>v (4*i.val)))
      (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate u (fun i=>v (4*i.val))).derivative d (d-1) k:=by
  rw [selected_packet]
  unfold signedValue FormulaSignSlotRadialCenterPrincipalCoefficient.specialized
    FormulaSignSlotRadialCenterPrincipalCoefficient.radiusPolynomial
  simp only [FormulaSignSlotRadialCenterPrincipalFamily.original,
    FormulaSignSlotRadialCenterPrincipalFamily.tau,FormulaSignSlotRadialCenterPrincipalFamily.degree,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rw [←PrincipalSubresultant.signedPsc_map_map,←Polynomial.derivative_map]
  change PrincipalSubresultant.signedPsc (mappedPolynomial (pairFst (pair u (pair t.bits d.bits))) v t d)
    (mappedPolynomial (pairFst (pair u (pair t.bits d.bits))) v t d).derivative d (d-1) k=_
  have HM:mappedPolynomial (pairFst (pair u (pair t.bits d.bits))) v t d=mappedPolynomial u v t d:=
    congrArg (fun z=>mappedPolynomial z v t d) (pairFst_pair u (pair t.bits d.bits))
  rw [HM,mappedPolynomial_eq u v t d HS]

private theorem unsigned_packet (u:List Bool) (v:ℕ→ℝ) (t d p:ℕ) (hp:p<d):
    IntegralPolynomialWindowTarski.baseHead Raw N hd
      (FormulaSignSlotRadialPrincipalWindowBounds.rawContext u t d p) (fun i=>v (4*i.val))=0 ↔
    (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst u) (fun i=>v (4*i.val)))
      (FormulaSignSlotRadialCenterSquarefreeSelection.principal u t d p)=0:=by
  rw [selected_packet]
  unfold signedValue
  have H:=FormulaSignSlotRadialCenterPrincipalCoefficient.unsigned_zero_iff
    (pair u (pair (BinaryNatCode.encode t) (BinaryNatCode.encode d))) (fun i=>v (4*i.val)) p
    (by simpa only [FormulaSignSlotRadialCenterPrincipalFamily.degree,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits] using hp)
  simp only [FormulaSignSlotRadialCenterPrincipalFamily.original,
    FormulaSignSlotRadialCenterPrincipalFamily.tau,FormulaSignSlotRadialCenterPrincipalFamily.degree,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] at H
  change _ ↔ unsignedValue (pairFst (pair u (pair t.bits d.bits))) v t d p=0 at H
  have HN:unsignedValue (pairFst (pair u (pair t.bits d.bits))) v t d p=unsignedValue u v t d p:=
    congrArg (fun z=>unsignedValue z v t d p) (pairFst_pair u (pair t.bits d.bits))
  exact H.trans (iff_of_eq (congrArg (fun z:Polynomial ℝ=>z=0) HN))

private theorem guards_environment (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (j:Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c))) (t d:ℕ):
    selected (radial c j.val) (env c x) t d ↔ selected (radial c j.val) (env c y) t d:=by
  exact FormulaSignSlotRadialJointSelectionStratum.guards_iff_of_signs
    (FormulaSignSlotRadialJointStratum.header c) j.val j.isLt
    (FormulaSignSlotRadialJointStratum.oldPoint c x.val) (FormulaSignSlotRadialJointStratum.oldPoint c y.val)
    (FormulaSignSlotRadialJointGridRetention.raw_signs c x y h) t d

/-- All guards, including the selected GCD index, are derived on the same component. -/
theorem guards_iff_of_joined (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (j:Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c))) (t d k:ℕ):
    FormulaSignSlotRadialCenterSquarefreeSelection.Guards (radial c j.val) (fun i=>env c x (4*i.val)) t d k ↔
    FormulaSignSlotRadialCenterSquarefreeSelection.Guards (radial c j.val) (fun i=>env c y (4*i.val)) t d k:=by
  have HS:=guards_environment c x y h j t d
  by_cases HX:selected (radial c j.val) (env c x) t d
  · have ht:=HX.1
    have hD:=HX.2.1
    change t ≤ FormulaSignSlotRadialPrincipalWindowBounds.bound (radial c j.val) at ht
    change d ≤ FormulaSignSlotRadialPrincipalWindowBounds.bound (radial c j.val) at hD
    have HZ (p:ℕ) (hp:p<d):
        (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst (radial c j.val)) (fun i=>env c x (4*i.val)))
          (FormulaSignSlotRadialCenterSquarefreeSelection.principal (radial c j.val) t d p)=0 ↔
        (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst (radial c j.val)) (fun i=>env c y (4*i.val)))
          (FormulaSignSlotRadialCenterSquarefreeSelection.principal (radial c j.val) t d p)=0:=by
      exact (unsigned_packet _ _ _ _ _ hp).symm.trans
        ((FormulaSignSlotRadialJointPrincipalWindowRetention.zero_iff_of_joined c x y h j t d p ht hD
          (by omega)).trans (unsigned_packet _ _ _ _ _ hp))
    unfold FormulaSignSlotRadialCenterSquarefreeSelection.Guards
    apply and_congr HS
    split_ifs with HD
    · rfl
    · apply and_congr_right
      intro hk
      exact and_congr (forall_congr' (fun p=>forall_congr' (fun hp=>HZ p (lt_trans hp hk))))
        (not_congr (HZ k hk))
  · have HY:=HS.not.mp HX
    exact iff_of_false (fun H=>HX H.1) (fun H=>HY H.1)

end LeanCanny.Encoding.FormulaSignSlotRadialJointSquarefreeIndexRetention
