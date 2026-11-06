/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalWindowCatalogue
public import LeanCanny.Encoding.FormulaSignSlotRadialJointFeatureRetention
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGuardInclusions
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiIntervalSigns
public import LeanCanny.Connectivity.FormulaSignSlotRadialJointDescriptorGeometry
/-! # Actual principal-window queries retain their truth on a stratum path

Every sign receipt is derived from the same actual source component.
The two interval endpoints and centers may differ along that path.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalWindowRetention
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.ETR Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "Raw"=>FormulaSignSlotRadialPrincipalRadiusSource.source
local notation "N"=>FormulaSignSlotRadialCutWindowSources.principalCenters
local notation "hd"=>FormulaSignSlotRadialCutWindowSources.principal_dimension
local notation "W"=>FormulaSignSlotRadialCutWindowSources.principalSource
local notation "F"=>FormulaSignSlotRadialJointCoefficientCatalogue.family
local notation "Space"=>FormulaSignSlotRadialJointStratumLabels.Space
local notation "S"=>FormulaSignSlotRadialJointStratum.source
local notation "env"=>FormulaSignSlotRadialJointDescriptorGeometry.environment
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial

noncomputable def radial (c:List Bool) (j:ℕ):=FormulaSignSlotRadialCoordinatePacket.packet
  (FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialJointStratum.header c)) j
noncomputable def values (r:ℝ) (v:ℕ → ℝ) (i:ℕ):=if i=0 then r else v (4*(i-1))
private theorem cast_cons {n m:ℕ} (h:m=n+1) (r:ℝ) (v:ℕ → ℝ):
    (fun i:Fin m=>(Fin.cons r (fun j=>v (4*j.val)):Fin (n+1) → ℝ) (Fin.cast h i))=
      (fun i=>values r v i.val):=by
  subst m
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [Fin.cast_refl,id_eq,Fin.cons_zero,values,Fin.val_zero,ite_true]
  · simp only [Fin.cast_refl,id_eq,Fin.cons_succ,values,Fin.val_succ,show ¬j.val+1=0 from by omega,
      ite_false,Nat.add_sub_cancel]
private theorem tuple_values (z:List Bool) (r:ℝ) (v:ℕ → ℝ):
    IntegralPolynomialWindowTarski.sourceTuple Raw N hd z r (fun i=>v (4*i.val))=
      (fun i=>values r v i.val):=cast_cons (hd z) r v
private theorem values_column (v:ℕ → ℝ) (i:ℕ):values (v 3) v i=
    v (FormulaSignSlotRadialJointRadiusTarskiSource.column i):=by
  unfold values FormulaSignSlotRadialJointRadiusTarskiSource.column FormulaSignSlotRadialJointLayout.boundVariable
  split_ifs <;>rfl
private theorem eval_cast {a b:ℕ} (ha:a=b) (p:MvPolynomial (Fin a) ℤ) (v:ℕ → ℝ):
    (MvPolynomial.rename (Fin.cast ha) p).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      p.eval₂ (Int.castRingHom ℝ) (fun i=>v i.val):=by
  subst b
  simp only [Fin.cast_refl,MvPolynomial.rename_id,AlgHom.id_apply]

private noncomputable def row_value (z:List Bool) (v:ℕ → ℝ):=
  ((W).polynomial z).eval₂ (Int.castRingHom ℝ)
    (fun i=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column i.val))
private theorem outer_value (u:List Bool) (i:ℕ) (v:ℕ → ℝ):
    (FormulaSignSlotRadialPrincipalWindowCatalogue.family.feature u i).eval₂ (Int.castRingHom ℝ)
      (fun j=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column j.val))=
      row_value (FormulaSignSlotRadialPrincipalWindowCatalogue.row (pair u (BinaryNatCode.encode i))) v:=
  eval_cast (FormulaSignSlotRadialPrincipalWindowCatalogue.dimension u i) ((W).polynomial _)
    (fun j=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column j))
private theorem inner_value (z:List Bool) (i:ℕ) (v:ℕ → ℝ):
    ((IntegralPolynomialWindowTarskiCatalogue.family Raw N hd).feature z i).eval₂ (Int.castRingHom ℝ)
      (IntegralPolynomialWindowTarski.sourceTuple Raw N hd z (v 3) (fun j=>v (4*j.val)))=
      row_value (IntegralPolynomialWindowTarskiCatalogue.row Raw (pair z (BinaryNatCode.encode i))) v:=by
  rw [tuple_values]
  have HV:(fun j:Fin ((Raw).arity z)=>values (v 3) v j.val)=
      (fun j=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column j.val)):=funext fun j=>values_column v j.val
  rw [HV]
  exact eval_cast (IntegralPolynomialWindowTarskiCatalogue.dimension Raw N hd z i) ((W).polynomial _)
    (fun j=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column j))
attribute [local irreducible] row_value

private theorem feature_environment (c:List Bool) (x:Space c) (i:ℕ):
    ((F).feature (FormulaSignSlotRadialJointStratum.header c) i).eval₂ (Int.castRingHom ℝ)
      (fun j=>env c x j.val)=FormulaSignSlotRadialJointFeatureRetention.feature c i x:=by
  unfold FormulaSignSlotRadialJointFeatureRetention.feature
  apply congrArg (((F).feature (FormulaSignSlotRadialJointStratum.header c) i).eval₂ (Int.castRingHom ℝ))
  funext j
  have Hj:j.val<FormulaSignSlotRadialJointStratum.oldArity c:=j.isLt
  simp only [FormulaSignSlotRadialJointDescriptorGeometry.environment,Formula.extend]
  rw [dite_eq_left Hj]
  rfl

theorem outer_signs (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (j:Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c)))
    (k:Fin (FormulaSignSlotRadialPrincipalWindowCatalogue.count (radial c j.val))):
    SignType.sign ((FormulaSignSlotRadialPrincipalWindowCatalogue.family.feature (radial c j.val) k.val).eval₂
      (Int.castRingHom ℝ) (fun i=>env c x (FormulaSignSlotRadialJointRadiusTarskiSource.column i.val)))=
    SignType.sign ((FormulaSignSlotRadialPrincipalWindowCatalogue.family.feature (radial c j.val) k.val).eval₂
      (Int.castRingHom ℝ) (fun i=>env c y (FormulaSignSlotRadialJointRadiusTarskiSource.column i.val))):=by
  let H:=FormulaSignSlotRadialJointStratum.header c
  let i:=FormulaSignSlotRadialJointPrincipalWindowCatalogue.encode H j.val k.val
  have HK:k.val<FormulaSignSlotRadialJointPrincipalWindowCatalogue.innerLimit H:=
    k.isLt.trans_le (FormulaSignSlotRadialJointPrincipalWindowCatalogue.inner_count_le H _
      (FormulaSignSlotRadialJointPrincipalWindowCatalogue.packet_length H j.val j.isLt))
  have HI:i<FormulaSignSlotRadialJointPrincipalWindowCatalogue.family.count H:=
    FormulaSignSlotRadialJointPrincipalWindowCatalogue.encode_lt H j.val k.val j.isLt HK
  let ix:=FormulaSignSlotRadialJointCoefficientCatalogue.principalIndex H i
  have Hix:ix<(F).count H:=FormulaSignSlotRadialJointGuardInclusions.principal_index_lt H i HI
  have HE:=FormulaSignSlotRadialJointFeatureRetention.sign_eq_of_joined c x y h ⟨ix,Hix⟩
  rw [←feature_environment c x ix,←feature_environment c y ix,
    FormulaSignSlotRadialJointCoefficientCatalogue.principal_feature_eval H i HI (env c x),
    FormulaSignSlotRadialJointCoefficientCatalogue.principal_feature_eval H i HI (env c y),
    FormulaSignSlotRadialJointPrincipalWindowCatalogue.encoded_feature_eval H j.val k.val j.isLt k.isLt (env c x),
    FormulaSignSlotRadialJointPrincipalWindowCatalogue.encoded_feature_eval H j.val k.val j.isLt k.isLt (env c y)] at HE
  exact HE

noncomputable def raw (c:List Bool) (j t d p:ℕ):=
  FormulaSignSlotRadialPrincipalWindowBounds.rawContext (radial c j) t d p

theorem catalogue_signs (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (j:Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c)))
    (t d p:ℕ) (ht:t ≤ FormulaSignSlotRadialPrincipalWindowBounds.bound (radial c j.val))
    (hD:d ≤ FormulaSignSlotRadialPrincipalWindowBounds.bound (radial c j.val))
    (hp:p ≤ 2*FormulaSignSlotRadialPrincipalWindowBounds.bound (radial c j.val)+1):
    IntegralPolynomialWindowTarski.CatalogueSigns Raw N hd (raw c j.val t d p)
      (env c x 3) (fun i=>env c x (4*i.val)) (env c y 3) (fun i=>env c y (4*i.val)):=by
  intro k
  obtain ⟨i,hi,Hrow⟩:=FormulaSignSlotRadialPrincipalWindowCatalogue.covers (radial c j.val) t d p k.val ht hD hp k.isLt
  have HE:=outer_signs c x y h j ⟨i,hi⟩
  rw [outer_value,outer_value,Hrow] at HE
  rw [inner_value,inner_value]
  exact HE

private theorem literal_evaluation (z:List Bool) (v:ℕ → ℝ) (r:ℝ):
    (IntegralPolynomialWindowTarski.baseHead Raw N hd z (fun i=>v (4*i.val))).eval r=
      ((Raw).polynomial z).eval₂ (Int.castRingHom ℝ) (fun i=>values r v i.val):=
  (IntegralPolynomialRadiusReader.specialization Raw N hd z (fun i=>v (4*i.val)) r).trans
    (congrArg (((Raw).polynomial z).eval₂ (Int.castRingHom ℝ)) (cast_cons (hd z) r v))

noncomputable def NoRoots (z:List Bool) (v:ℕ → ℝ) (b:ℝ):Prop:=
  ∀r,((Raw).polynomial z).eval₂ (Int.castRingHom ℝ) (fun i=>values r v i.val)=0 → r ∉ Ioo 0 b
private theorem noRoots_iff (z:List Bool) (v:ℕ → ℝ) (b:ℝ):
    (∀r,(IntegralPolynomialWindowTarski.baseHead Raw N hd z (fun i=>v (4*i.val))).eval r=0 → r ∉ Ioo 0 b)↔NoRoots z v b:=by
  unfold NoRoots
  apply forall_congr'
  intro r
  rw [literal_evaluation]

/-- Literal full principal polynomials avoid the open radius interval at one
point iff they do at the other. Signs and all finite selections are internal. -/
theorem no_roots_iff_of_joined (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (j:Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c)))
    (t d p:ℕ) (ht:t ≤ FormulaSignSlotRadialPrincipalWindowBounds.bound (radial c j.val))
    (hD:d ≤ FormulaSignSlotRadialPrincipalWindowBounds.bound (radial c j.val))
    (hp:p ≤ 2*FormulaSignSlotRadialPrincipalWindowBounds.bound (radial c j.val)+1):
    NoRoots (raw c j.val t d p) (env c x) (env c x 3)↔NoRoots (raw c j.val t d p) (env c y) (env c y 3):=by
  have HBx:0<env c x 3:=(FormulaSignSlotRadialJointDescriptorGeometry.radius_bounds c x).1.trans
    (FormulaSignSlotRadialJointDescriptorGeometry.radius_bounds c x).2
  have HBy:0<env c y 3:=(FormulaSignSlotRadialJointDescriptorGeometry.radius_bounds c y).1.trans
    (FormulaSignSlotRadialJointDescriptorGeometry.radius_bounds c y).2
  have HI:=IntegralPolynomialWindowTarski.interval_iff_of_signs Raw N hd (raw c j.val t d p)
    (env c x 3) (fun i=>env c x (4*i.val)) (env c y 3) (fun i=>env c y (4*i.val))
      (catalogue_signs c x y h j t d p ht hD hp) HBx HBy
  exact (noRoots_iff _ _ _).symm.trans (HI.trans (noRoots_iff _ _ _))

theorem zero_iff_of_joined (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (j:Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c)))
    (t d p:ℕ) (ht:t ≤ FormulaSignSlotRadialPrincipalWindowBounds.bound (radial c j.val))
    (hD:d ≤ FormulaSignSlotRadialPrincipalWindowBounds.bound (radial c j.val))
    (hp:p ≤ 2*FormulaSignSlotRadialPrincipalWindowBounds.bound (radial c j.val)+1):
    IntegralPolynomialWindowTarski.baseHead Raw N hd (raw c j.val t d p) (fun i=>env c x (4*i.val))=0 ↔
    IntegralPolynomialWindowTarski.baseHead Raw N hd (raw c j.val t d p) (fun i=>env c y (4*i.val))=0:=by
  rw [←IntegralPolynomialWindowTarski.zero_iff,←IntegralPolynomialWindowTarski.zero_iff]
  exact IntegralPolynomialWindowTarski.zero_iff_of_signs Raw N hd _ _ _ _ _
    (catalogue_signs c x y h j t d p ht hD hp)

end LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalWindowRetention
