/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointValueWindowCatalogue
public import LeanCanny.Encoding.FormulaSignSlotRadialValueWindowMeaning
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGridRetention
/-! # The actual value-certificate interval is retained by a stratum path -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointValueIntervalRetention
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "Raw"=>FormulaSignSlotRadialValueRadiusSource.source
local notation "S"=>FormulaSignSlotRadialJointStratum.source
local notation "Space"=>FormulaSignSlotRadialJointStratumLabels.Space
local notation "env"=>FormulaSignSlotRadialJointDescriptorGeometry.environment
local notation "Nraw"=>FormulaSignSlotRadialValueWindowCatalogue.centers
local notation "HD"=>FormulaSignSlotRadialValueWindowCatalogue.dimension_eq
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialFormalEliminant.eliminant
  FormulaSignSlotRadialValueCertificate.polynomial FormulaSignSlotRadialCenterValueFamily.Guards

noncomputable def root (c:List Bool):=FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialJointStratum.header c)
noncomputable def centerNat (c:List Bool) (x:Space c) (j:ℕ):=env c x (4*j)
noncomputable def bound (c:List Bool) (x:Space c):=FormulaSignSlotRadialJointDescriptorGeometry.bound c x
noncomputable def certificate (c:List Bool) (x:Space c):=FormulaSignSlotRadialValueWindowMeaning.certificate (root c) (centerNat c x)
noncomputable def CutFree (c:List Bool) (x:Space c):Prop:=
  ∀ r : ℝ, (certificate c x).trailingCoeff.eval r = 0 → r ∉ Ioo 0 (bound c x)

theorem bound_pos (c:List Bool) (x:Space c):0<bound c x:=
  (FormulaSignSlotRadialJointDescriptorGeometry.radius_bounds c x).1.trans
    (FormulaSignSlotRadialJointDescriptorGeometry.radius_bounds c x).2

private theorem cons_natural {n:ℕ} (b:ℝ) (a:ℕ→ℝ) (i:Fin (n+1)):
    (Fin.cons b (fun j:Fin n=>a j.val):Fin (n+1)→ℝ) i=(if i.val=0 then b else a (i.val-1)):=by
  refine Fin.cases ?_ (fun j=>?_) i
  · rfl
  · simp only [Fin.cons_succ,Fin.val_succ,Nat.add_sub_cancel_right]
    rw [ite_eq_right (by omega)]

private theorem source_tuple_natural (T:IntegralFramedBankPolynomialModel.Source) (N:List Bool→ℕ)
    (hd:∀c,T.arity c=N c+1) (q:List Bool) (v:ℕ→ℝ):
    IntegralPolynomialWindowTarski.sourceTuple T N hd q (v FormulaSignSlotRadialJointLayout.boundVariable)
      (fun j=>v (4*j.val))=(fun i=>v (FormulaSignSlotRadialJointValueWindowCatalogue.column i.val)):=by
  funext i
  unfold IntegralPolynomialWindowTarski.sourceTuple
  rw [cons_natural (n:=N q) (v FormulaSignSlotRadialJointLayout.boundVariable) (fun j=>v (4*j)) (Fin.cast (hd q) i)]
  simp only [Fin.val_cast]
  unfold FormulaSignSlotRadialJointValueWindowCatalogue.column
  split_ifs <;>rfl

private theorem catalogue_feature_tuple (T:IntegralFramedBankPolynomialModel.Source) (N:List Bool→ℕ)
    (hd:∀c,T.arity c=N c+1) (q:List Bool) (k:ℕ) (v:ℕ→ℝ):
    ((IntegralPolynomialWindowTarskiCatalogue.family T N hd).feature q k).eval₂ (Int.castRingHom ℝ)
      (IntegralPolynomialWindowTarski.sourceTuple T N hd q (v FormulaSignSlotRadialJointLayout.boundVariable)
        (fun j=>v (4*j.val)))=
    ((IntegralPolynomialWindowTarskiCatalogue.family T N hd).feature q k).eval₂ (Int.castRingHom ℝ)
      (fun j=>v (FormulaSignSlotRadialJointValueWindowCatalogue.column j.val)):=
  congrArg (fun a:Fin (T.arity q)→ℝ=>((IntegralPolynomialWindowTarskiCatalogue.family T N hd).feature q k).eval₂
    (Int.castRingHom ℝ) a) (source_tuple_natural T N hd q v)

theorem coordinate_guards_transfer (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (tau deg:Fin (FormulaSignSlotCenteredRadialGraph.N (root c)+FormulaSignSlotCenteredRadialGraph.d (root c)+1)→ℕ)
    (HG:FormulaSignSlotRadialCenterValueFamily.Guards (root c) (fun j=>centerNat c x j.val) tau deg):
    FormulaSignSlotRadialCenterValueFamily.Guards (root c) (fun j=>centerNat c y j.val) tau deg:=by
  have HX:=(FormulaSignSlotRadialCenterValueSelection.all_guards (root c) (centerNat c x) tau deg).mpr HG
  apply (FormulaSignSlotRadialCenterValueSelection.all_guards (root c) (centerNat c y) tau deg).mp
  intro i
  have HSigns:=FormulaSignSlotRadialJointGridRetention.raw_signs c x y h
  have H:=FormulaSignSlotRadialJointSelectionStratum.guards_iff_of_signs
    (FormulaSignSlotRadialJointStratum.header c) i.val i.isLt _ _ HSigns (tau i) (deg i)
  apply H.mp
  exact HX i


private def NoRoot (p:Polynomial ℝ) (b:ℝ):Prop:=∀ r : ℝ, p.eval r = 0 → r ∉ Ioo 0 b
private theorem trailing_transfer (P Q:Polynomial (Polynomial ℝ)) (b b':ℝ) (L:ℕ) (hP:P.natDegree≤L)
    (HZ:∀ell,ell≤L→(P.coeff ell=0↔Q.coeff ell=0))
    (HR:∀ell,ell≤L→(NoRoot (P.coeff ell) b↔NoRoot (Q.coeff ell) b'))
    (hb:0<b) (HN:NoRoot P.trailingCoeff b):NoRoot Q.trailingCoeff b':=by
  have hp:P≠0:=by
    intro hp0
    have hmid:b/2∈Ioo 0 b:=⟨by linarith,by linarith⟩
    have hz:P.trailingCoeff.eval (b/2)=0:=by rw [hp0];simp
    exact HN _ hz hmid
  let ell:=P.natTrailingDegree
  have hEll:ell≤L:=(Polynomial.natTrailingDegree_le_natDegree P).trans hP
  have hpe:P.coeff ell≠0:=Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp
  have hqe:Q.coeff ell≠0:=(HZ ell hEll).not.mp hpe
  have hq:Q≠0:=by intro hq0;exact hqe (by rw [hq0,Polynomial.coeff_zero])
  have hle:Q.natTrailingDegree≤ell:=Polynomial.natTrailingDegree_le_of_ne_zero hqe
  have hge:ell≤Q.natTrailingDegree:=by
    apply Nat.le_of_not_gt
    intro hlt
    have HP0:P.coeff Q.natTrailingDegree=0:=Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt
    exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hq) ((HZ _ (hlt.le.trans hEll)).mp HP0)
  have HE:Q.natTrailingDegree=ell:=Nat.le_antisymm hle hge
  have HN0:NoRoot (P.coeff ell) b:=HN
  have HN1:NoRoot (Q.coeff ell) b':=(HR ell hEll).mp HN0
  change NoRoot (Q.coeff Q.natTrailingDegree) b'
  rw [HE]
  exact HN1


private def extend_nat {n:ℕ} (f:Fin n→ℕ) (j:ℕ):ℕ:=if h:j<n then f ⟨j,h⟩ else 0
private theorem extend_nat_at {n:ℕ} (f:Fin n→ℕ) (i:Fin n):extend_nat f i.val=f i:=dite_eq_left i.isLt

private def OuterSigns (c:List Bool) (x y:Space c):Prop:=∀o:ℕ,
  o<FormulaSignSlotRadialValueCatalogueLayout.outerCount (root c)→
    IntegralPolynomialWindowTarski.CatalogueSigns Raw Nraw HD
      (FormulaSignSlotRadialValueCatalogueLayout.context (pair (root c) (BinaryNatCode.encode o)))
      (bound c x) (fun j=>centerNat c x j.val) (bound c y) (fun j=>centerNat c y j.val)

private theorem raw_zero_iff (q:List Bool) (a a':ℕ→ℝ) (b b':ℝ)
    (HS:IntegralPolynomialWindowTarski.CatalogueSigns Raw Nraw HD q b (fun j=>a j.val) b' (fun j=>a' j.val)):
    FormulaSignSlotRadialValueWindowMeaning.rawHead q a=0 ↔FormulaSignSlotRadialValueWindowMeaning.rawHead q a'=0:=
  (IntegralPolynomialWindowTarski.zero_iff Raw Nraw HD q (fun j=>a j.val)).symm.trans
    ((IntegralPolynomialWindowTarski.zero_iff_of_signs Raw Nraw HD q b (fun j=>a j.val) b' (fun j=>a' j.val) HS).trans
      (IntegralPolynomialWindowTarski.zero_iff Raw Nraw HD q (fun j=>a' j.val)))
private theorem raw_interval_iff (q:List Bool) (a a':ℕ→ℝ) (b b':ℝ)
    (HS:IntegralPolynomialWindowTarski.CatalogueSigns Raw Nraw HD q b (fun j=>a j.val) b' (fun j=>a' j.val))
    (hb:0<b) (hb':0<b'):
    NoRoot (FormulaSignSlotRadialValueWindowMeaning.rawHead q a) b ↔
      NoRoot (FormulaSignSlotRadialValueWindowMeaning.rawHead q a') b':=
  IntegralPolynomialWindowTarski.interval_iff_of_signs Raw Nraw HD q b (fun j=>a j.val) b' (fun j=>a' j.val) HS hb hb'

attribute [local irreducible] FormulaSignSlotRadialValueWindowMeaning.rawHead
  FormulaSignSlotRadialValueWindowMeaning.head FormulaSignSlotRadialValueWindowMeaning.certificate certificate

private theorem transfer_of_outer_signs (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (HS:OuterSigns c x y) (HX:CutFree c x):CutFree c y:=by
  let u:=root c
  obtain ⟨t,D,HB,HG⟩:=FormulaSignSlotRadialCenterValueSelection.exists_bounded_guards u (centerNat c x)
  have HG':=coordinate_guards_transfer c x y h t D HG
  let tau:ℕ→ℕ:=extend_nat t
  let deg:ℕ→ℕ:=extend_nat D
  have HT:(fun i:Fin (FormulaSignSlotCenteredRadialGraph.N u+FormulaSignSlotCenteredRadialGraph.d u+1)=>tau i.val)=t:=
    funext (extend_nat_at t)
  have HDeg:(fun i:Fin (FormulaSignSlotCenteredRadialGraph.N u+FormulaSignSlotCenteredRadialGraph.d u+1)=>deg i.val)=D:=
    funext (extend_nat_at D)
  have HBounds:∀j,j<FormulaSignSlotRadialValueCatalogueBounds.coordinates u→
      tau j≤FormulaSignSlotRadialValueCatalogueBounds.bound u ∧deg j≤FormulaSignSlotRadialValueCatalogueBounds.bound u:=by
    intro j hj
    have hj':j<FormulaSignSlotCenteredRadialGraph.N u+FormulaSignSlotCenteredRadialGraph.d u+1:=hj
    simpa only [tau,deg,extend_nat,dite_eq_left hj',FormulaSignSlotRadialValueCatalogueBounds.bound] using HB ⟨j,hj'⟩
  have Hgx:FormulaSignSlotRadialCenterValueFamily.Guards u (fun j=>centerNat c x j.val)
      (fun i=>tau i.val) (fun i=>deg i.val):=by rw [HT,HDeg];exact HG
  have Hgy:FormulaSignSlotRadialCenterValueFamily.Guards u (fun j=>centerNat c y j.val)
      (fun i=>tau i.val) (fun i=>deg i.val):=by rw [HT,HDeg];exact HG'
  let F:=FormulaSignSlotRadialValueCatalogueBounds.familyContext u tau deg
  have HO:FormulaSignSlotRadialCenterValueLayout.original F=u:=
    FormulaSignSlotRadialValueCatalogueBounds.family_original u tau deg
  have Gx:FormulaSignSlotRadialValueWindowMeaning.Guard F (centerNat c x):=
    FormulaSignSlotRadialValueWindowMeaning.guard_from_values F u HO _ tau deg
      (fun j hj=>FormulaSignSlotRadialValueCatalogueBounds.family_tau u tau deg j hj)
      (fun j hj=>FormulaSignSlotRadialValueCatalogueBounds.family_degree u tau deg j hj) Hgx
  have Gy:FormulaSignSlotRadialValueWindowMeaning.Guard F (centerNat c y):=
    FormulaSignSlotRadialValueWindowMeaning.guard_from_values F u HO _ tau deg
      (fun j hj=>FormulaSignSlotRadialValueCatalogueBounds.family_tau u tau deg j hj)
      (fun j hj=>FormulaSignSlotRadialValueCatalogueBounds.family_degree u tau deg j hj) Hgy
  have CX:FormulaSignSlotRadialValueWindowMeaning.certificate (FormulaSignSlotRadialCenterValueLayout.original F)
      (centerNat c x)=certificate c x:=by rw [HO];unfold certificate;rfl
  have CY:FormulaSignSlotRadialValueWindowMeaning.certificate (FormulaSignSlotRadialCenterValueLayout.original F)
      (centerNat c y)=certificate c y:=by rw [HO];unfold certificate;rfl
  have Hdegree:(certificate c x).natDegree≤FormulaSignSlotRadialCenterValuePacking.degree F:=by
    have H:=FormulaSignSlotRadialValueWindowMeaning.certificate_degree F _ Gx
    rw [CX] at H
    exact H
  apply trailing_transfer (certificate c x) (certificate c y) (bound c x) (bound c y)
    (FormulaSignSlotRadialCenterValuePacking.degree F) Hdegree ?_ ?_ (bound_pos c x) HX
  · intro ell hell
    obtain ⟨o,ho,HC⟩:=FormulaSignSlotRadialValueCatalogueLayout.covers u tau deg
      (fun j hj=>(HBounds j hj).1) (fun j hj=>(HBounds j hj).2) ell hell
    have H:=raw_zero_iff _ (centerNat c x) (centerNat c y) (bound c x) (bound c y) (HS o ho)
    rw [HC,FormulaSignSlotRadialValueWindowMeaning.raw_head_packet,
      FormulaSignSlotRadialValueWindowMeaning.raw_head_packet,
      FormulaSignSlotRadialValueWindowMeaning.head_specialization F ell _ Gx,
      FormulaSignSlotRadialValueWindowMeaning.head_specialization F ell _ Gy,CX,CY] at H
    exact H
  · intro ell hell
    obtain ⟨o,ho,HC⟩:=FormulaSignSlotRadialValueCatalogueLayout.covers u tau deg
      (fun j hj=>(HBounds j hj).1) (fun j hj=>(HBounds j hj).2) ell hell
    have H:=raw_interval_iff _ (centerNat c x) (centerNat c y) (bound c x) (bound c y) (HS o ho)
      (bound_pos c x) (bound_pos c y)
    rw [HC,FormulaSignSlotRadialValueWindowMeaning.raw_head_packet,
      FormulaSignSlotRadialValueWindowMeaning.raw_head_packet,
      FormulaSignSlotRadialValueWindowMeaning.head_specialization F ell _ Gx,
      FormulaSignSlotRadialValueWindowMeaning.head_specialization F ell _ Gy,CX,CY] at H
    exact H


private theorem feature_environment (c:List Bool) (x:Space c) (i:ℕ):
    (FormulaSignSlotRadialJointCoefficientCatalogue.family.feature (FormulaSignSlotRadialJointStratum.header c) i).eval₂
      (Int.castRingHom ℝ) (fun j=>env c x j.val)=FormulaSignSlotRadialJointFeatureRetention.feature c i x:=by
  unfold FormulaSignSlotRadialJointFeatureRetention.feature
  apply congrArg ((FormulaSignSlotRadialJointCoefficientCatalogue.family.feature
    (FormulaSignSlotRadialJointStratum.header c) i).eval₂ (Int.castRingHom ℝ))
  funext j
  have Hj:j.val<FormulaSignSlotRadialJointStratum.oldArity c:=j.isLt
  simp only [FormulaSignSlotRadialJointDescriptorGeometry.environment,Formula.extend]
  rw [dite_eq_left Hj]
  rfl

private theorem joint_value_sign (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (i:ℕ) (hi:i<FormulaSignSlotRadialJointValueWindowCatalogue.family.count (FormulaSignSlotRadialJointStratum.header c)):
    SignType.sign ((FormulaSignSlotRadialJointValueWindowCatalogue.family.feature
      (FormulaSignSlotRadialJointStratum.header c) i).eval₂ (Int.castRingHom ℝ) (fun j=>env c x j.val))=
    SignType.sign ((FormulaSignSlotRadialJointValueWindowCatalogue.family.feature
      (FormulaSignSlotRadialJointStratum.header c) i).eval₂ (Int.castRingHom ℝ) (fun j=>env c y j.val)):=by
  rw [←FormulaSignSlotRadialJointCoefficientCatalogue.value_feature_eval _ i hi (env c x),
    ←FormulaSignSlotRadialJointCoefficientCatalogue.value_feature_eval _ i hi (env c y),
    feature_environment,feature_environment]
  exact FormulaSignSlotRadialJointFeatureRetention.sign_eq_of_joined c x y h
    ⟨FormulaSignSlotRadialJointCoefficientCatalogue.valueIndex _ i,
      FormulaSignSlotRadialJointGuardInclusions.value_index_lt _ i hi⟩

private theorem outer_signs_of_joined (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val):OuterSigns c x y:=by
  unfold OuterSigns
  dsimp only [root]
  intro o ho k
  have hk:k.val<FormulaSignSlotRadialValueWindowCatalogue.innerCount (root c):=
    k.isLt.trans_le (FormulaSignSlotRadialValueWindowMeaning.inner_count_le (root c) o)
  have hi:FormulaSignSlotRadialValueWindowMeaning.flatIndex (root c) o k.val<
      FormulaSignSlotRadialJointValueWindowCatalogue.family.count (FormulaSignSlotRadialJointStratum.header c):=
    FormulaSignSlotRadialValueWindowMeaning.flat_lt (root c) o k.val ho hk
  have H:=joint_value_sign c x y h _ hi
  rw [FormulaSignSlotRadialJointValueWindowCatalogue.feature_value _ _ (env c x),
    FormulaSignSlotRadialJointValueWindowCatalogue.feature_value _ _ (env c y)] at H
  have FX:=FormulaSignSlotRadialValueWindowMeaning.feature_inner (root c) o k.val hk
    (fun j=>env c x (FormulaSignSlotRadialJointValueWindowCatalogue.column j))
  have FY:=FormulaSignSlotRadialValueWindowMeaning.feature_inner (root c) o k.val hk
    (fun j=>env c y (FormulaSignSlotRadialJointValueWindowCatalogue.column j))
  dsimp only [root,FormulaSignSlotRadialJointValueWindowCatalogue.base] at H FX FY
  rw [FX,FY] at H
  have HX:=catalogue_feature_tuple Raw Nraw HD
    (FormulaSignSlotRadialValueCatalogueLayout.context (pair (root c) (BinaryNatCode.encode o))) k.val (env c x)
  have HY:=catalogue_feature_tuple Raw Nraw HD
    (FormulaSignSlotRadialValueCatalogueLayout.context (pair (root c) (BinaryNatCode.encode o))) k.val (env c y)
  dsimp only [root] at HX HY
  have HE:=(congrArg SignType.sign HX).trans (H.trans (congrArg SignType.sign HY).symm)
  simpa only [bound,FormulaSignSlotRadialJointDescriptorGeometry.bound,centerNat] using HE

/-- The actual value-certificate cut condition is invariant on the same
implicit stratum component. Every selection table and trailing index is
chosen internally from the initial point's genuine certificate. -/
theorem cut_free_iff_of_joined (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val):
    CutFree c x↔CutFree c y:=
  ⟨transfer_of_outer_signs c x y h (outer_signs_of_joined c x y h),
    transfer_of_outer_signs c y x h.symm (outer_signs_of_joined c y x h.symm)⟩

theorem cut_free_actual (c:List Bool) (x:Space c):CutFree c x↔
    ∀ r:ℝ,(FormulaSignSlotRadialValueCertificate.polynomial
      (FormulaSignSlotRadialJointStratumLabels.source true c) (FormulaSignSlotRadialJointDescriptorGeometry.center c x)).trailingCoeff.eval r=0→
        r ∉ Ioo 0 (FormulaSignSlotRadialJointDescriptorGeometry.bound c x):=by
  unfold CutFree certificate FormulaSignSlotRadialValueWindowMeaning.certificate centerNat bound root
  rfl

theorem actual_interval_iff_of_joined (c:List Bool) (x y:Space c)
    (h:JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val):
    (∀ r:ℝ,(FormulaSignSlotRadialValueCertificate.polynomial
      (FormulaSignSlotRadialJointStratumLabels.source true c) (FormulaSignSlotRadialJointDescriptorGeometry.center c x)).trailingCoeff.eval r=0→
        r ∉ Ioo 0 (FormulaSignSlotRadialJointDescriptorGeometry.bound c x))↔
    (∀ r:ℝ,(FormulaSignSlotRadialValueCertificate.polynomial
      (FormulaSignSlotRadialJointStratumLabels.source true c) (FormulaSignSlotRadialJointDescriptorGeometry.center c y)).trailingCoeff.eval r=0→
        r ∉ Ioo 0 (FormulaSignSlotRadialJointDescriptorGeometry.bound c y)):=
  (cut_free_actual c x).symm.trans ((cut_free_iff_of_joined c x y h).trans (cut_free_actual c y))

end LeanCanny.Encoding.FormulaSignSlotRadialJointValueIntervalRetention
