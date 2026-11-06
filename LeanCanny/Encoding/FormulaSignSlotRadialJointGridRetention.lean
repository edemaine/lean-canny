/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointFeatureRetention
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGuardInclusions
public import LeanCanny.Encoding.FormulaSignSlotRadialJointSelectionStratum
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitGridScan
public import LeanCanny.Connectivity.FormulaSignSlotRadialJointDescriptorGeometry
/-! # Actual parameter-grid membership is retained by a stratum path

The perturbation and degree guards are chosen from the actual nonzero
eliminant and transported using the retained raw coefficient signs.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointGridRetention
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F"=>FormulaSignSlotRadialJointCoefficientCatalogue.family
local notation "S"=>FormulaSignSlotRadialJointStratum.source
local notation "Space"=>FormulaSignSlotRadialJointStratumLabels.Space
local notation "env"=>FormulaSignSlotRadialJointDescriptorGeometry.environment

attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial

noncomputable def Grid (c:List Bool) (x:Space c):Prop:=
  FormulaSignSlotRadialJointGeometry.spatialPoint (FormulaSignSlotRadialJointStratum.header c) (env c x)∈
    FormulaSignSlotRadialParameterGrid.grid
      (FormulaSignSlotRadialJointStratumLabels.source true c)
      (FormulaSignSlotRadialJointGeometry.center (FormulaSignSlotRadialJointStratum.header c) (env c x))
      (FormulaSignSlotRadialJointGeometry.parameter (FormulaSignSlotRadialJointStratum.header c) (env c x))

theorem raw_signs (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val):
    FormulaSignSlotRadialJointSelectionStratum.Signs (FormulaSignSlotRadialJointStratum.header c)
      (FormulaSignSlotRadialJointStratum.oldPoint c x.val) (FormulaSignSlotRadialJointStratum.oldPoint c y.val):=by
  intro i
  exact FormulaSignSlotRadialJointFeatureRetention.sign_eq_of_joined c x y h
    ⟨i.val,i.isLt.trans_le (FormulaSignSlotRadialJointCoefficientCatalogue.raw_count_le _)⟩

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

theorem feature_zero_iff (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (i:ℕ) (hi:i<(F).count (FormulaSignSlotRadialJointStratum.header c)):
    ((F).feature (FormulaSignSlotRadialJointStratum.header c) i).eval₂ (Int.castRingHom ℝ) (fun j=>env c x j.val)=0 ↔
      ((F).feature (FormulaSignSlotRadialJointStratum.header c) i).eval₂ (Int.castRingHom ℝ) (fun j=>env c y j.val)=0:=by
  rw [feature_environment,feature_environment]
  have H:=FormulaSignSlotRadialJointFeatureRetention.sign_eq_of_joined c x y h ⟨i,hi⟩
  have HE:=Iff.of_eq (congrArg (fun t:SignType=>t=0) H)
  simpa only [sign_eq_zero_iff] using HE

theorem grid_polynomial_zero_iff (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (j:Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c)))
    (t:ℕ) (ht:t<FormulaSignSlotRadialJointGridCompleteCatalogue.limit (FormulaSignSlotRadialJointStratum.header c)):
    (FormulaSignSlotRadialJointGridSource.source.polynomial (pair (FormulaSignSlotRadialJointStratum.header c)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode t)))).eval₂ (Int.castRingHom ℝ) (fun i=>env c x i.val)=0 ↔
    (FormulaSignSlotRadialJointGridSource.source.polynomial (pair (FormulaSignSlotRadialJointStratum.header c)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode t)))).eval₂ (Int.castRingHom ℝ) (fun i=>env c y i.val)=0:=by
  let H:=FormulaSignSlotRadialJointStratum.header c
  let k:=FormulaSignSlotRadialJointGridCompleteCatalogue.encode H j.val t
  have hk:k<FormulaSignSlotRadialJointGridCompleteCatalogue.family.count H:=
    FormulaSignSlotRadialJointGridCompleteCatalogue.encode_lt H j.val t j.isLt ht
  have HB:FormulaSignSlotRadialJointCoefficientCatalogue.count H+k<(F).count H:=
    FormulaSignSlotRadialJointGuardInclusions.grid_index_lt H k hk
  have HE:=feature_zero_iff c x y h _ HB
  rw [FormulaSignSlotRadialJointCoefficientCatalogue.grid_feature_eval H k hk (env c x),
    FormulaSignSlotRadialJointCoefficientCatalogue.grid_feature_eval H k hk (env c y),
    FormulaSignSlotRadialJointGridCompleteCatalogue.feature_encode H j.val t ht (env c x),
    FormulaSignSlotRadialJointGridCompleteCatalogue.feature_encode H j.val t ht (env c y)] at HE
  exact HE

private theorem natural_point_heq {a b:ℕ} (ha:a=b) (v:ℕ→ℝ):
    HEq (fun i:Fin a=>v (4*i.val)) (fun i:Fin b=>v (4*i.val)):=by cases ha;rfl
private theorem guards_congr (c d:List Bool) (h:c=d)
    (a:Fin (FormulaSignSlotCenteredRadialGraph.d (pairFst c))→ℝ)
    (b:Fin (FormulaSignSlotCenteredRadialGraph.d (pairFst d))→ℝ) (hab:HEq a b) (t D:ℕ):
    FormulaSignSlotRadialCenterSelection.Guards c a t D↔FormulaSignSlotRadialCenterSelection.Guards d b t D:=by
  cases h
  have H:a=b:=eq_of_heq hab
  subst b
  rfl
private theorem radial_packet (H:List Bool) (j t:ℕ):
    FormulaSignSlotRadialJointGridLayout.radial (pair H (pair (BinaryNatCode.encode j) (BinaryNatCode.encode t)))=
      FormulaSignSlotRadialJointSelectionStratum.coordinateContext H j:=by
  unfold FormulaSignSlotRadialJointGridLayout.radial FormulaSignSlotRadialJointGridLayout.sliceContext
    FormulaSignSlotRadialJointSelectionStratum.coordinateContext
  simp only [FormulaSignSlotRadialJointGridLayout.header,FormulaSignSlotRadialJointGridLayout.coordinateWord,
    FormulaSignSlotRadialJointGridLayout.tauInput,pairFst_pair,pairSnd_pair,
    FormulaSignSlotRadialCoordinatePacket.writer_packet]

private theorem native_guards_iff (c:List Bool) (x:Space c) (j t D:ℕ):
    let H:=FormulaSignSlotRadialJointStratum.header c
    let z:=pair H (pair (BinaryNatCode.encode j) (BinaryNatCode.encode t))
    FormulaSignSlotRadialCenterSelection.Guards (FormulaSignSlotRadialJointGridLayout.radial z)
      (FormulaSignSlotRadialJointGridSource.center z (env c x))
      (Nat.fromBitsLE (FormulaSignSlotRadialJointGridLayout.tauWord z)) D ↔
    FormulaSignSlotRadialCenterSelection.Guards
      (FormulaSignSlotRadialJointSelectionStratum.coordinateContext H j)
      (FormulaSignSlotRadialJointSelectionStratum.center H j (FormulaSignSlotRadialJointStratum.oldPoint c x.val)) t D:=by
  let H:=FormulaSignSlotRadialJointStratum.header c
  let z:=pair H (pair (BinaryNatCode.encode j) (BinaryNatCode.encode t))
  have HP:=radial_packet H j t
  have HA:HEq (FormulaSignSlotRadialJointGridSource.center z (env c x))
      (fun i:Fin (FormulaSignSlotCenteredRadialGraph.d
        (pairFst (FormulaSignSlotRadialJointSelectionStratum.coordinateContext H j)))=>env c x (4*i.val)):=
    natural_point_heq (congrArg (fun u=>FormulaSignSlotCenteredRadialGraph.d (pairFst u)) HP) (env c x)
  have HB:HEq
      (fun i:Fin (FormulaSignSlotCenteredRadialGraph.d
        (pairFst (FormulaSignSlotRadialJointSelectionStratum.coordinateContext H j)))=>env c x (4*i.val))
      (FormulaSignSlotRadialJointSelectionStratum.center H j (FormulaSignSlotRadialJointStratum.oldPoint c x.val)):=by rfl
  have HT:Nat.fromBitsLE (FormulaSignSlotRadialJointGridLayout.tauWord z)=t:=by
    simp only [z,FormulaSignSlotRadialJointGridLayout.tauWord,FormulaSignSlotRadialJointGridLayout.sliceContext,
      FormulaSignSlotRadialJointGridLayout.tauInput,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  change FormulaSignSlotRadialCenterSelection.Guards (FormulaSignSlotRadialJointGridLayout.radial z)
      (FormulaSignSlotRadialJointGridSource.center z (env c x))
      (Nat.fromBitsLE (FormulaSignSlotRadialJointGridLayout.tauWord z)) D ↔_
  rw [HT]
  exact guards_congr _ _ HP _ _ (HA.trans HB) t D

private theorem bound_eq (H:List Bool) (j:ℕ):
    FormulaSignSlotRadialCenterSelection.bound (FormulaSignSlotRadialJointSelectionStratum.coordinateContext H j)=
      FormulaSignSlotRadialJointGridCompleteCatalogue.degree H:=by
  apply FormulaSignSlotRadialEliminantRootProfiles.degree_eq
  simp only [FormulaSignSlotRadialJointSelectionStratum.coordinateContext,FormulaSignSlotRadialCoordinatePacket.root,
    FormulaSignSlotRadialJointGridCompleteCatalogue.base,pairFst_pair]

/-- Genuine grid membership propagates along the actual source component.
The nonzero-eliminant selection guards are derived internally. -/
theorem grid_imp_of_joined (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (hx:Grid c x):Grid c y:=by
  intro j
  let H:=FormulaSignSlotRadialJointStratum.header c
  obtain ⟨t,ht,D,_,HG⟩:=FormulaSignSlotRadialCenterSelection.exists_guards
    (FormulaSignSlotRadialJointSelectionStratum.coordinateContext H j.val)
    (FormulaSignSlotRadialJointSelectionStratum.center H j.val (FormulaSignSlotRadialJointStratum.oldPoint c x.val))
  have HY:FormulaSignSlotRadialCenterSelection.Guards
      (FormulaSignSlotRadialJointSelectionStratum.coordinateContext H j.val)
      (FormulaSignSlotRadialJointSelectionStratum.center H j.val (FormulaSignSlotRadialJointStratum.oldPoint c y.val)) t D:=
    (FormulaSignSlotRadialJointSelectionStratum.guards_iff_of_signs H j.val j.isLt
      _ _ (raw_signs c x y h) t D).mp HG
  have ht0:t<FormulaSignSlotRadialJointGridCompleteCatalogue.limit H:=by
    rw [bound_eq H j.val] at ht
    change t<FormulaSignSlotRadialJointGridCompleteCatalogue.degree H+1
    omega
  have GX:=(native_guards_iff c x j.val t D).mpr HG
  have GY:=(native_guards_iff c y j.val t D).mpr HY
  have EX:=FormulaSignSlotRadialImplicitGridScan.selected_evaluation H j (BinaryNatCode.encode t) (env c x) D GX
  have EY:=FormulaSignSlotRadialImplicitGridScan.selected_evaluation H j (BinaryNatCode.encode t) (env c y) D GY
  exact EY.symm.trans ((grid_polynomial_zero_iff c x y h j t ht0).mp (EX.trans (hx j)))

theorem grid_iff_of_joined (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val):
    Grid c x↔Grid c y:=⟨grid_imp_of_joined c x y h,grid_imp_of_joined c y x h.symm⟩

private theorem radial_grid_iff (q:List Bool) (v:ℕ→ℝ)
    (hv:(FormulaSignSlotRadialJointCore.equation q).eval v=0):
    (FormulaSignSlotRadialJointGeometry.radialPoint q v hv).val.val∈
      FormulaSignSlotRadialParameterGrid.grid (FormulaSignSlotRadialJointLayout.source true q)
        (FormulaSignSlotRadialJointGeometry.center q v) (FormulaSignSlotRadialJointGeometry.parameter q v) ↔
    FormulaSignSlotRadialJointGeometry.spatialPoint q v∈
      FormulaSignSlotRadialParameterGrid.grid (FormulaSignSlotRadialJointLayout.source true q)
        (FormulaSignSlotRadialJointGeometry.center q v) (FormulaSignSlotRadialJointGeometry.parameter q v):=Iff.rfl

/-- The original radial descriptor's literal anchor has the same grid property. -/
theorem anchor_grid_iff_of_joined (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val):
    (FormulaSignSlotRadialJointDescriptorGeometry.anchor c x).val.val∈
      FormulaSignSlotRadialParameterGrid.grid (FormulaSignSlotRadialJointStratumLabels.source true c)
        (FormulaSignSlotRadialJointDescriptorGeometry.center c x) (FormulaSignSlotRadialJointDescriptorGeometry.radius c x) ↔
    (FormulaSignSlotRadialJointDescriptorGeometry.anchor c y).val.val∈
      FormulaSignSlotRadialParameterGrid.grid (FormulaSignSlotRadialJointStratumLabels.source true c)
        (FormulaSignSlotRadialJointDescriptorGeometry.center c y) (FormulaSignSlotRadialJointDescriptorGeometry.radius c y):=
  (radial_grid_iff _ _ (FormulaSignSlotRadialJointDescriptorGeometry.core_zero c x)).trans
    ((grid_iff_of_joined c x y h).trans
      (radial_grid_iff _ _ (FormulaSignSlotRadialJointDescriptorGeometry.core_zero c y)).symm)

/-- One fresh native word in the same actual component retains the genuine
initial grid condition. Both table and OWN-word bounds are constructed. -/
theorem component_hit_grid (c:List Bool) (x:Space c) (hx:Grid c x):
    ∃Gamma:List Bool,Gamma.length≤FormulaSignSlotRadialJointStratumSampler.tableBound c ∧
      ∃(w:List Bool) (hw:SquareSampleCompleteVertices.Valid
        FormulaSignSlotRadialJointStratumSampler.input (pair c Gamma) w),
        w.length=SquareSampleCompleteVertices.width FormulaSignSlotRadialJointStratumSampler.input (pair c Gamma) ∧
        w.length≤FormulaSignSlotRadialJointStratumSampler.ownwordBound c ∧
        pair (pair c Gamma) w∈FormulaSignSlotRadialJointStratumSampler.language ∧
        ∃a:Space c,
          JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val a.val ∧
          Grid c a ∧HEq (SquareSampleCompleteVertices.candidate FormulaSignSlotRadialJointStratumSampler.input
            (pair c Gamma) w hw).val a.val:=by
  obtain ⟨Gamma,hGamma,w,hw,hlen,hbound,hq,a,hpath,hpoint⟩:=
    FormulaSignSlotRadialJointStratumSampler.component_hit c x
  exact ⟨Gamma,hGamma,w,hw,hlen,hbound,hq,a,hpath,(grid_iff_of_joined c x a hpath).mp hx,hpoint⟩

end LeanCanny.Encoding.FormulaSignSlotRadialJointGridRetention
