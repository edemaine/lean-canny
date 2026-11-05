/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialExternalPrelude
public import LeanCanny.Encoding.FormulaSignSlotRadialJointStratumLabels
public import LeanCanny.Algebra.IntegerRootBound
/-! # The external own tuple is an actual bounded original point -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialExternalPoint
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.ETR
open FormulaSignSlotRadialExternalContext
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S" => FormulaSignSlotRadialJointStratum.source
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input

private theorem root_bound (p : Polynomial ℤ) (M : ℕ) (hp : p≠0)
    (hM : coefficientMass p≤2^M) (a : ℝ) (ha : p.eval₂ (Int.castRingHom ℝ) a=0) :
    |a|≤(2:ℝ)^(M+1) := by
  have H := abs_root_lt_coefficientMass_add_one p hp a ha
  have HM : (coefficientMass p : ℝ)≤(2:ℝ)^M := by exact_mod_cast hM
  have HP : (1:ℝ)≤2^M := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  linarith

attribute [local irreducible] FormulaSignSlotRadialExternalCoordinates.source
  ImplicitSourceGramGrid.polynomial CoerciveBoxGramEliminant.polynomial

theorem coordinate_bound (ctx : List Bool) (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid ctx)
    (i : Fin (number ctx)) :
    |FormulaSignSlotRadialExternalCoordinates.point ctx hw i.val|≤
      (2:ℝ)^(FormulaSignSlotRadialExternalCoordinates.massBound ctx+1) := by
  let q := pair ctx (BinaryNatCode.encode i.val)
  have HM := (FormulaSignSlotRadialExternalCoordinates.source.mass_bound q).trans
    (Nat.pow_le_pow_right (by omega : 1≤2) (FormulaSignSlotRadialExternalCoordinates.mass_le q))
  rw [pairFst_pair] at HM
  apply root_bound _ _ (FormulaSignSlotRadialExternalCoordinates.nonzero q) HM
  have HR := FormulaSignSlotRadialExternalCoordinates.roots ctx hw i.val
  simpa only [FormulaSignSlotRadialExternalCoordinates.values,ite_eq_left i.isLt] using HR

theorem radial_le (ctx : List Bool) (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid ctx) :
    BoundedZeroSource.radial (fun i : Fin (number ctx) => FormulaSignSlotRadialExternalCoordinates.point ctx hw i.val)≤
      (BoundedZeroSource.radiusSquared (FormulaSignSlotRadialExternalPrelude.radius ctx):ℝ) := by
  have HB := BoundedPositivePerturbation.penalty_bound 2
    (FormulaSignSlotRadialExternalCoordinates.massBound ctx+1)
    (fun i : Fin (number ctx) => FormulaSignSlotRadialExternalCoordinates.point ctx hw i.val)
    (coordinate_bound ctx hw)
  have HS := Nat.size_le_size (Nat.le_max_left (number ctx)
    (ImplicitSourceGramGrid.count S (gridContext ctx)))
  have HE : (FormulaSignSlotRadialExternalCoordinates.massBound ctx+1)*2+(number ctx).size≤2*FormulaSignSlotRadialExternalPrelude.radius ctx := by
    unfold FormulaSignSlotRadialExternalPrelude.radius FormulaSignSlotRadialExternalCoordinates.massBound
    dsimp only [FormulaSignSlotRadialExternalPrelude.number]
    omega
  have HP : (2:ℝ)^((FormulaSignSlotRadialExternalCoordinates.massBound ctx+1)*2+(number ctx).size)≤
      (2:ℝ)^(2*FormulaSignSlotRadialExternalPrelude.radius ctx) := pow_le_pow_right₀ (by norm_num) HE
  simpa only [BoundedZeroSource.radial,BoundedZeroSource.radiusSquared,Int.cast_pow,Int.cast_ofNat]
    using HB.trans HP

noncomputable def wordPoint (Q : IntegralFramedBankPolynomialModel.Source)
    (hp : ∀u,0<Q.arity u) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (ImplicitSourceGramGrid.input Q hp) c w)
    (hq : pair c w∈ImplicitSourceComponentSampler.language Q hp) :
    CoerciveComponentSampling.Zeros ((Q.polynomial (ImplicitSourceGramGrid.header c)).map (Int.castRingHom ℝ)) :=
  ⟨(SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input Q hp) c w hw).val,
    by
      change MvPolynomial.eval _ ((Q.polynomial (ImplicitSourceGramGrid.header c)).map (Int.castRingHom ℝ))=0
      simpa only [MvPolynomial.eval_map] using (ImplicitSourceComponentSampler.packet Q hp c w hw).mp hq⟩

noncomputable def wordPointAt (Q : IntegralFramedBankPolynomialModel.Source)
    (hp : ∀u,0<Q.arity u) (u c : List Bool) (hc : ImplicitSourceGramGrid.header c=u) (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (ImplicitSourceGramGrid.input Q hp) c w)
    (hq : pair c w∈ImplicitSourceComponentSampler.language Q hp) :
    CoerciveComponentSampling.Zeros ((Q.polynomial u).map (Int.castRingHom ℝ)) := by
  cases hc
  exact wordPoint Q hp c w hw hq

theorem wordPointAt_coordinate (Q : IntegralFramedBankPolynomialModel.Source)
    (hp : ∀u,0<Q.arity u) (u c : List Bool) (hc : ImplicitSourceGramGrid.header c=u) (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (ImplicitSourceGramGrid.input Q hp) c w)
    (hq : pair c w∈ImplicitSourceComponentSampler.language Q hp) (j : ℕ) (hj : j<Q.arity u) :
    (wordPointAt Q hp u c hc w hw hq).val ⟨j,hj⟩=
      (SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input Q hp) c w hw).val
        ⟨j,by change j<Q.arity (ImplicitSourceGramGrid.header c); rw [hc]; exact hj⟩ := by
  cases hc
  rfl

noncomputable def stratumPoint (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (w : List Bool)
    (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid (packet H K Gamma label s w))
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma) w∈
      FormulaSignSlotRadialJointStratumSampler.language) :
    FormulaSignSlotRadialJointStratumLabels.Space (FormulaSignSlotRadialJointStratum.packet H K) :=
  wordPointAt S FormulaSignSlotRadialJointStratumSampler.positive (FormulaSignSlotRadialJointStratum.packet H K)
    (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma) (pairFst_pair _ _) w
    (by simpa only [FormulaSignSlotRadialExternalCoordinates.OwnValid,gridContext_packet,ownWord_packet] using hw) hq

noncomputable def projectAt (H c : List Bool) (hc : FormulaSignSlotRadialJointStratum.header c=H)
    (s : Bool) (x : FormulaSignSlotRadialJointStratumLabels.Space c) :
    FormulaSignSlotCircularBoundedCover.Source (FormulaSignSlotRadialJointLayout.source s H) := by
  cases hc
  exact FormulaSignSlotRadialJointStratumLabels.project s c x

theorem projectAt_coordinate (H c : List Bool) (hc : FormulaSignSlotRadialJointStratum.header c=H)
    (s : Bool) (x : FormulaSignSlotRadialJointStratumLabels.Space c)
    (i : Fin (FormulaSignSlotRadialJointLayout.circleCount s H)) :
    (projectAt H c hc s x).val i=x.val
      ⟨FormulaSignSlotRadialJointLayout.column (if s then 1 else 0) i.val,by
        cases hc
        exact (FormulaSignSlotRadialJointComponentTransport.coordinate_lt s _ i).trans (Nat.lt_succ_self _)⟩ := by
  cases hc
  change (FormulaSignSlotRadialJointStratumLabels.project s c x).val i=_
  rw [FormulaSignSlotRadialJointStratumLabels.project,FormulaSignSlotRadialJointComponentTransport.project_coordinate]
  rfl

noncomputable def projected (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (w : List Bool)
    (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid (packet H K Gamma label s w))
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma) w∈
      FormulaSignSlotRadialJointStratumSampler.language) :
    FormulaSignSlotCircularBoundedCover.Source (FormulaSignSlotRadialJointLayout.source s H) :=
  projectAt H (FormulaSignSlotRadialJointStratum.packet H K) (pairFst_pair _ _) s
    (stratumPoint H K Gamma label s w hw hq)

private theorem candidate_value_eq (T : SquareSampleInput.Inputs) (c c' w w' : List Bool)
    (hc : c=c') (he : w=w') (hv : SquareSampleCompleteVertices.Valid T c w)
    (hv' : SquareSampleCompleteVertices.Valid T c' w') (i : Fin (T.count c)) (j : Fin (T.count c'))
    (hij : i.val=j.val) :
    (SquareSampleCompleteVertices.candidate T c w hv).val i=
      (SquareSampleCompleteVertices.candidate T c' w' hv').val j := by
  cases hc
  cases he
  have H : i=j := Fin.ext hij
  subst j
  rfl

theorem projected_coordinate (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (w : List Bool)
    (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid (packet H K Gamma label s w))
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma) w∈
      FormulaSignSlotRadialJointStratumSampler.language)
    (i : Fin (FormulaSignSlotRadialJointLayout.circleCount s H)) :
    (projected H K Gamma label s w hw hq).val i=
      FormulaSignSlotRadialExternalCoordinates.point (packet H K Gamma label s w) hw i.val := by
  rw [projected,projectAt_coordinate]
  unfold stratumPoint
  rw [wordPointAt_coordinate]
  unfold FormulaSignSlotRadialExternalCoordinates.point
  exact candidate_value_eq F _ _ _ _ (gridContext_packet H K Gamma label s w).symm
    (ownWord_packet H K Gamma label s w).symm _ _ _ _
    (FormulaSignSlotRadialExternalCoordinates.index_packet_val H K Gamma label s w i).symm

theorem radial_readback (m n : ℕ) (hm : m=n) (x : Fin m→ℝ) (y : Fin n→ℝ)
    (hxy : ∀i j,i.val=j.val→x i=y j) : BoundedZeroSource.radial x=BoundedZeroSource.radial y := by
  cases hm
  have H : x=y := funext (fun i => hxy i i rfl)
  rw [H]

noncomputable def boundedOriginal (u : List Bool) (r : ℕ)
    (x : FormulaSignSlotCircularBoundedCover.Source u)
    (hr : BoundedZeroSource.radial x.val≤(BoundedZeroSource.radiusSquared r:ℝ)) :
    BoundedZeroSource.Bounded (AuxiliaryCandidateRegularLift.original
      CanonicalAuxiliaryCandidateCover.dimension CanonicalAuxiliaryCandidateCover.equation u) r :=
  ⟨x.val,(Term.eval_finitePolynomial _ _ _).trans x.property,hr⟩

noncomputable def boundedPoint (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (w : List Bool)
    (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid (packet H K Gamma label s w))
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma) w∈
      FormulaSignSlotRadialJointStratumSampler.language) :
    BoundedZeroSource.Bounded (AuxiliaryCandidateRegularLift.original
      CanonicalAuxiliaryCandidateCover.dimension CanonicalAuxiliaryCandidateCover.equation
        (FormulaSignSlotRadialJointLayout.source s H))
      (FormulaSignSlotRadialExternalPrelude.radius (packet H K Gamma label s w)) := by
  apply boundedOriginal _ _ (projected H K Gamma label s w hw hq)
  have HE := radial_readback _ _ (number_packet H K Gamma label s w).symm
    (projected H K Gamma label s w hw hq).val
    (fun i : Fin (number (packet H K Gamma label s w)) =>
      FormulaSignSlotRadialExternalCoordinates.point (packet H K Gamma label s w) hw i.val)
    (by
      intro i j hij
      rw [projected_coordinate]
      exact congrArg (FormulaSignSlotRadialExternalCoordinates.point (packet H K Gamma label s w) hw) hij)
  rw [HE]
  exact radial_le _ hw

theorem boundedPoint_coordinate (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (w : List Bool)
    (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid (packet H K Gamma label s w))
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma) w∈
      FormulaSignSlotRadialJointStratumSampler.language)
    (i : Fin (FormulaSignSlotRadialJointLayout.circleCount s H)) :
    (boundedPoint H K Gamma label s w hw hq).val i=
      FormulaSignSlotRadialExternalCoordinates.point (packet H K Gamma label s w) hw i.val :=
  projected_coordinate H K Gamma label s w hw hq i

theorem jointHeader_packet (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (w : List Bool) :
    FormulaSignSlotRadialExternalPrelude.jointHeader (packet H K Gamma label s w)=H := by
  simp only [FormulaSignSlotRadialExternalPrelude.jointHeader,gridContext_packet,
    ImplicitSourceGramGrid.header,pairFst_pair,FormulaSignSlotRadialJointStratum.header,
    FormulaSignSlotRadialJointStratum.packet]

theorem radius_packet (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (w : List Bool) :
    FormulaSignSlotRadialExternalPrelude.radius (packet H K Gamma label s w)=
      FormulaSignSlotRadialExternalPrelude.jointRadius H+
      ImplicitSourceGramGrid.mass S (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma)+
      (ImplicitSourceGramGrid.count S (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma)).size+2+
      FormulaSignSlotRadialExternalPrelude.jointJoiningExponent H := by
  have HO : FormulaSignSlotRadialExternalPrelude.oldRadius (FormulaSignSlotRadialJointLayout.source s H)≤
      FormulaSignSlotRadialExternalPrelude.jointRadius H := by
    cases s <;> exact (by unfold FormulaSignSlotRadialExternalPrelude.jointRadius; omega)
  have HJ : FormulaSignSlotRadialExternalPrelude.joiningExponent (FormulaSignSlotRadialJointLayout.source s H)≤
      FormulaSignSlotRadialExternalPrelude.jointJoiningExponent H := by
    cases s <;> exact (by unfold FormulaSignSlotRadialExternalPrelude.jointJoiningExponent; omega)
  have HN : FormulaSignSlotRadialJointLayout.circleCount s H≤
      ImplicitSourceGramGrid.count S (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma) := by
    change FormulaSignSlotRadialJointLayout.circleCount s H≤(F).count (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma)
    rw [FormulaSignSlotRadialExternalCoordinates.count_packet]
    have HE := FormulaSignSlotRadialJointLayout.circle_lt_slots s H
    unfold FormulaSignSlotRadialJointLayout.dimension
    omega
  simp only [FormulaSignSlotRadialExternalPrelude.radius,FormulaSignSlotRadialExternalPrelude.number,
    FormulaSignSlotRadialExternalPrelude.original,original_packet,jointHeader_packet,gridContext_packet,number_packet,
    max_eq_right HO,max_eq_right HN,FormulaSignSlotRadialExternalPrelude.joiningCutoff,max_eq_right HJ]

end LeanCanny.Encoding.FormulaSignSlotRadialExternalPoint
