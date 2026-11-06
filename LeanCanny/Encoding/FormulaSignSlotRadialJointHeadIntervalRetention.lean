/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusWindowInterval
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGridRetention
/-! # Actual joint-stratum paths retain coordinate-leading and margin-trailing intervals -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointHeadIntervalRetention
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR Polynomial MvPolynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointCoefficientCatalogue.family
local notation "S" => FormulaSignSlotRadialJointStratum.source
local notation "Space" => FormulaSignSlotRadialJointStratumLabels.Space
local notation "env" => FormulaSignSlotRadialJointDescriptorGeometry.environment
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialFormalEliminant.eliminant
  FormulaSignSlotRadialParameterEliminant.coordinate

noncomputable def root (c : List Bool) := FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialJointStratum.header c)
noncomputable def radial (c : List Bool) (j : ℕ) := FormulaSignSlotRadialCoordinatePacket.packet (root c) j
noncomputable def center (c : List Bool) (x : Space c) (j : ℕ) : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount (radial c j)) → ℝ :=
  fun i => env c x (4*i.val)
noncomputable def bound (c : List Bool) (x : Space c) := FormulaSignSlotRadialJointDescriptorGeometry.bound c x
private theorem bound_pos (c : List Bool) (x : Space c) : 0 < bound c x :=
  (FormulaSignSlotRadialJointDescriptorGeometry.radius_bounds c x).1.trans
    (FormulaSignSlotRadialJointDescriptorGeometry.radius_bounds c x).2

private theorem feature_environment (c : List Bool) (x : Space c) (i : ℕ) :
    ((F).feature (FormulaSignSlotRadialJointStratum.header c) i).eval₂ (Int.castRingHom ℝ)
      (fun j => env c x j.val) = FormulaSignSlotRadialJointFeatureRetention.feature c i x := by
  unfold FormulaSignSlotRadialJointFeatureRetention.feature
  apply congrArg (((F).feature (FormulaSignSlotRadialJointStratum.header c) i).eval₂ (Int.castRingHom ℝ))
  funext j
  have Hj : j.val < FormulaSignSlotRadialJointStratum.oldArity c := j.isLt
  simp only [FormulaSignSlotRadialJointDescriptorGeometry.environment,Formula.extend]
  rw [dite_eq_left Hj]
  rfl
private theorem eval_cast {n m : ℕ} (h : n=m) (p : MvPolynomial (Fin n) ℤ) (v : ℕ → ℝ) :
    (MvPolynomial.rename (Fin.cast h) p).eval₂ (Int.castRingHom ℝ) (fun i => v i.val) =
      p.eval₂ (Int.castRingHom ℝ) (fun i => v i.val) := by
  cases h
  simp only [Fin.cast_refl,MvPolynomial.rename_id,AlgHom.id_apply]
private theorem old_feature_value (q : List Bool) (k : ℕ) (v : ℕ → ℝ) :
    ((FormulaSignSlotRadialRadiusTarskiCatalogue.family).feature q k).eval₂ (Int.castRingHom ℝ) (fun i => v i.val) =
      (FormulaSignSlotRadialRadiusTarskiKernelSource.polynomial (FormulaSignSlotRadialRadiusTarskiCatalogue.row (pair q (BinaryNatCode.encode k)))).eval₂
        (Int.castRingHom ℝ) (fun i => v i.val) :=
  eval_cast (FormulaSignSlotRadialRadiusTarskiCatalogue.dimension q k) _ v
private theorem cons_natural {n : ℕ} (b : ℝ) (a : ℕ → ℝ) (i : Fin (n+1)) :
    (Fin.cons b (fun j : Fin n => a j.val) : Fin (n+1) → ℝ) i = (if i.val=0 then b else a (i.val-1)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Fin.cons_succ,Fin.val_succ,Nat.add_sub_cancel_right]
    rw [ite_eq_right (by omega)]
private theorem tuple_natural (q : List Bool) (v : ℕ → ℝ) :
    FormulaSignSlotRadialRadiusWindowSigns.tuple q (v FormulaSignSlotRadialJointLayout.boundVariable) (fun i => v (4*i.val)) =
      (fun i => v (FormulaSignSlotRadialJointRadiusTarskiSource.column i.val)) := by
  funext i
  unfold FormulaSignSlotRadialRadiusWindowSigns.tuple
  rw [cons_natural (n:=FormulaSignSlotRadialRadiusWindowSigns.centerCount q) (v FormulaSignSlotRadialJointLayout.boundVariable) (fun j => v (4*j)) i]
  unfold FormulaSignSlotRadialJointRadiusTarskiSource.column
  split_ifs <;> rfl
private theorem read_packet (H : List Bool) (j k : ℕ) :
    FormulaSignSlotRadialJointRadiusTarskiCatalogue.read (pair H (pair (BinaryNatCode.encode j) (BinaryNatCode.encode k))) =
      FormulaSignSlotRadialRadiusTarskiCatalogue.row (pair (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j)
        (BinaryNatCode.encode k)) := by
  have HR : FormulaSignSlotRadialJointRadiusTarskiCatalogue.radial (pair H (pair (BinaryNatCode.encode j) (BinaryNatCode.encode k))) =
      FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j := by
    unfold FormulaSignSlotRadialJointRadiusTarskiCatalogue.radial
    simp only [FormulaSignSlotRadialJointRadiusTarskiCatalogue.header,FormulaSignSlotRadialJointRadiusTarskiCatalogue.coordinateWord,
      pairFst_pair,pairSnd_pair]
    exact FormulaSignSlotRadialCoordinatePacket.writer_packet _ j
  have HK : FormulaSignSlotRadialJointRadiusTarskiCatalogue.control (pair H (pair (BinaryNatCode.encode j) (BinaryNatCode.encode k))) = k := by
    simp only [FormulaSignSlotRadialJointRadiusTarskiCatalogue.control,FormulaSignSlotRadialJointRadiusTarskiCatalogue.controlWord,
      pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  unfold FormulaSignSlotRadialJointRadiusTarskiCatalogue.read
  rw [HR,HK]

private theorem count_radial (H : List Bool) (j : ℕ) :
    FormulaSignSlotRadialRadiusTarskiCatalogue.count (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j) = FormulaSignSlotRadialJointRadiusTarskiCatalogue.limit H := by
  apply FormulaSignSlotRadialRadiusTarskiCatalogue.count_eq
  rw [FormulaSignSlotRadialCoordinatePacket.root]
  simp only [FormulaSignSlotRadialJointRadiusTarskiCatalogue.base,pairFst_pair]
private theorem feature_packet (H : List Bool) (j k : ℕ) (hk : k < FormulaSignSlotRadialJointRadiusTarskiCatalogue.limit H) (v : ℕ → ℝ) :
    ((FormulaSignSlotRadialJointRadiusTarskiCatalogue.family).feature H (FormulaSignSlotRadialJointRadiusTarskiCatalogue.encode H j k)).eval₂ (Int.castRingHom ℝ) (fun i => v i.val) =
      ((FormulaSignSlotRadialRadiusTarskiCatalogue.family).feature (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j) k).eval₂
        (Int.castRingHom ℝ) (FormulaSignSlotRadialRadiusWindowSigns.tuple _ (v FormulaSignSlotRadialJointLayout.boundVariable) (fun i => v (4*i.val))) := by
  have HE := FormulaSignSlotRadialJointRadiusTarskiCatalogue.feature_encode H j k hk v
  have HC := congrArg (fun q => (FormulaSignSlotRadialRadiusTarskiKernelSource.polynomial q).eval₂ (Int.castRingHom ℝ)
    (fun i => v (FormulaSignSlotRadialJointRadiusTarskiSource.column i.val))) (read_packet H j k)
  have HT := congrArg (fun a => ((FormulaSignSlotRadialRadiusTarskiCatalogue.family).feature
    (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j) k).eval₂ (Int.castRingHom ℝ) a)
      (tuple_natural (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j) v)
  exact HE.trans (HC.trans (HT.trans (old_feature_value _ k (fun i => v (FormulaSignSlotRadialJointRadiusTarskiSource.column i)))).symm)

theorem signs_of_joined (c : List Bool) (x y : Space c)
    (h : JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (j : ℕ) (hj : j < FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c)) :
    FormulaSignSlotRadialRadiusWindowSigns.Signs (radial c j) (bound c x) (center c x j) (bound c y) (center c y j) := by
  intro k
  let H := FormulaSignSlotRadialJointStratum.header c
  have hk : k.val < FormulaSignSlotRadialJointRadiusTarskiCatalogue.limit H := k.isLt.trans_eq (count_radial H j)
  let i := FormulaSignSlotRadialJointRadiusTarskiCatalogue.encode H j k.val
  have hi : i < (FormulaSignSlotRadialJointRadiusTarskiCatalogue.family).count H := FormulaSignSlotRadialJointRadiusTarskiCatalogue.encode_lt H j k.val hj hk
  let n := FormulaSignSlotRadialJointCoefficientCatalogue.count H +
    FormulaSignSlotRadialJointGridCompleteCatalogue.family.count H + i
  have hn : n < (F).count H := FormulaSignSlotRadialJointGuardInclusions.tarski_index_lt H i hi
  have HS := FormulaSignSlotRadialJointFeatureRetention.sign_eq_of_joined c x y h ⟨n,hn⟩
  rw [←feature_environment c x n,←feature_environment c y n] at HS
  rw [FormulaSignSlotRadialJointGuardInclusions.tarski_feature_eval H i hi (env c x),
    FormulaSignSlotRadialJointGuardInclusions.tarski_feature_eval H i hi (env c y),
    feature_packet H j k.val hk (env c x),feature_packet H j k.val hk (env c y)] at HS
  dsimp only [H] at HS
  exact HS

theorem leading_interval_iff_of_joined (c : List Bool) (x y : Space c)
    (h : JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (j : ℕ) (hj : j < FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c)) :
    (∀ r, (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (radial c j) (center c x j)).leadingCoeff.eval r=0 → r ∉ Ioo 0 (bound c x)) ↔
      ∀ r, (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (radial c j) (center c y j)).leadingCoeff.eval r=0 → r ∉ Ioo 0 (bound c y) :=
  FormulaSignSlotRadialRadiusWindowInterval.leading_interval_iff _ _ _ _ _ (signs_of_joined c x y h j hj) (bound_pos c x) (bound_pos c y)

theorem trailing_interval_iff_of_joined (c : List Bool) (x y : Space c)
    (h : JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (j : ℕ) (hj : j < FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c)) :
    (∀ r, (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (radial c j) (center c x j)).trailingCoeff.eval r=0 → r ∉ Ioo 0 (bound c x)) ↔
      ∀ r, (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (radial c j) (center c y j)).trailingCoeff.eval r=0 → r ∉ Ioo 0 (bound c y) :=
  FormulaSignSlotRadialRadiusWindowInterval.trailing_interval_iff _ _ _ _ _ (signs_of_joined c x y h j hj) (bound_pos c x) (bound_pos c y)

private theorem natural_point_heq {n m : ℕ} (h : n=m) (v : ℕ → ℝ) :
    HEq (fun i : Fin n => v (4*i.val)) (fun i : Fin m => v (4*i.val)) := by cases h; rfl
private theorem coordinate_transport (u v : List Bool) (hu : u=v)
    (a : Fin (FormulaSignSlotCenteredRadialGraph.d u) → ℝ) (b : Fin (FormulaSignSlotCenteredRadialGraph.d v) → ℝ)
    (hab : HEq a b)
    (i : Fin (FormulaSignSlotCenteredRadialGraph.N u + FormulaSignSlotCenteredRadialGraph.d u + 1))
    (j : Fin (FormulaSignSlotCenteredRadialGraph.N v + FormulaSignSlotCenteredRadialGraph.d v + 1)) (hij : i.val=j.val) :
    FormulaSignSlotRadialParameterEliminant.coordinate u a i = FormulaSignSlotRadialParameterEliminant.coordinate v b j := by
  cases hu
  cases eq_of_heq hab
  have H : i=j := Fin.ext hij
  rw [H]

private theorem center_natural (c : List Bool) (x : Space c) (j : ℕ) : center c x j =
    (fun i : Fin (FormulaSignSlotCenteredRadialGraph.d (pairFst (radial c j))) => env c x (4*i.val)) := rfl
private theorem descriptor_center_natural (c : List Bool) (x : Space c) :
    FormulaSignSlotRadialJointDescriptorGeometry.center c x =
      (fun i : Fin (FormulaSignSlotCenteredRadialGraph.d (root c)) => env c x (4*i.val)) := by
  unfold FormulaSignSlotRadialJointDescriptorGeometry.center FormulaSignSlotRadialJointGeometry.center
  rfl

/-- The packet, original root, center and selected coordinate are all literal. -/
theorem actual_coordinate (c : List Bool) (x : Space c)
    (j : Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c))) :
    FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (radial c j.val) (center c x j.val) =
      FormulaSignSlotRadialParameterEliminant.coordinate (root c) (FormulaSignSlotRadialJointDescriptorGeometry.center c x) j := by
  have HC : pairFst (radial c j.val)=root c := FormulaSignSlotRadialCoordinatePacket.root (root c) j.val
  have HA := natural_point_heq (congrArg FormulaSignSlotCenteredRadialGraph.d HC) (env c x)
  have HAB : HEq (center c x j.val) (FormulaSignSlotRadialJointDescriptorGeometry.center c x) :=
    (heq_of_eq (center_natural c x j.val)).trans
      (HA.trans (heq_of_eq (descriptor_center_natural c x)).symm)
  have HI : (FormulaSignSlotRadialEliminantInput.coordinate (radial c j.val)).val=j.val := by
    change (FormulaSignSlotRadialEliminantInput.coordinate (FormulaSignSlotRadialCoordinatePacket.packet (root c) j.val)).val = j.val
    rw [FormulaSignSlotRadialCoordinatePacket.selected]
    exact Nat.min_eq_left (by have H := j.isLt; change j.val < FormulaSignSlotCenteredRadialGraph.N (root c) + FormulaSignSlotCenteredRadialGraph.d (root c) + 1 at H; omega)
  exact coordinate_transport _ _ HC _ _ HAB _ j HI

theorem actual_leading_interval_iff_of_joined (c : List Bool) (x y : Space c)
    (h : JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (j : Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c))) :
    (∀ r, (FormulaSignSlotRadialParameterEliminant.coordinate (root c)
      (FormulaSignSlotRadialJointDescriptorGeometry.center c x) j).leadingCoeff.eval r=0 →
        r ∉ Ioo 0 (FormulaSignSlotRadialJointDescriptorGeometry.bound c x)) ↔
    (∀ r, (FormulaSignSlotRadialParameterEliminant.coordinate (root c)
      (FormulaSignSlotRadialJointDescriptorGeometry.center c y) j).leadingCoeff.eval r=0 →
        r ∉ Ioo 0 (FormulaSignSlotRadialJointDescriptorGeometry.bound c y)) := by
  have H := leading_interval_iff_of_joined c x y h j.val j.isLt
  rw [actual_coordinate c x j,actual_coordinate c y j] at H
  exact H

theorem actual_trailing_interval_iff_of_joined (c : List Bool) (x y : Space c)
    (h : JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (j : Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c))) :
    (∀ r, (FormulaSignSlotRadialParameterEliminant.coordinate (root c)
      (FormulaSignSlotRadialJointDescriptorGeometry.center c x) j).trailingCoeff.eval r=0 →
        r ∉ Ioo 0 (FormulaSignSlotRadialJointDescriptorGeometry.bound c x)) ↔
    (∀ r, (FormulaSignSlotRadialParameterEliminant.coordinate (root c)
      (FormulaSignSlotRadialJointDescriptorGeometry.center c y) j).trailingCoeff.eval r=0 →
        r ∉ Ioo 0 (FormulaSignSlotRadialJointDescriptorGeometry.bound c y)) := by
  have H := trailing_interval_iff_of_joined c x y h j.val j.isLt
  rw [actual_coordinate c x j,actual_coordinate c y j] at H
  exact H

end LeanCanny.Encoding.FormulaSignSlotRadialJointHeadIntervalRetention
