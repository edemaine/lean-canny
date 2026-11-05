/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalMeaning
public import LeanCanny.Encoding.FormulaSignSlotRadialJointSelectionStratum
/-! # The actual squarefree index persists on the joint coefficient sign stratum -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalStratum
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Geometry LeanCanny.Computation MvPolynomial
open FormulaSignSlotRadialJointPrincipalCatalogue
open FormulaSignSlotRadialJointCoefficientCatalogue (degree limit)
open FormulaSignSlotRadialJointSelectionStratum (extend extend_val coordinateContext center)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Point (c : List Bool) := Fin (family.arity c) → ℝ
noncomputable def featureValue (c : List Bool) (i : ℕ) (x : Point c) :=
  (family.feature c i).eval₂ (Int.castRingHom ℝ) x
def Signs (c : List Bool) (x y : Point c) : Prop :=
  ∀ i : Fin (count c), SignType.sign (featureValue c i.val x)=SignType.sign (featureValue c i.val y)

theorem coefficient_zero_iff (c : List Bool) (x y : Point c) (HS : Signs c x y)
    (j s d k r : ℕ) (hj : j<FormulaSignSlotRadialJointLayout.spatialCount c)
    (hs : s<limit c) (hd : d<limit c) (hk : k<limit c) (hr : r<radiusLimit c) :
    principalValue c j s d k r (extend x)=0 ↔ principalValue c j s d k r (extend y)=0 := by
  let i := encode c j s d k r
  have HI : i<count c := encode_lt c j s d k r hj hs hd hk hr
  have HE (z : Point c) : (fun i : Fin (family.arity c) => extend z i.val)=z := funext (extend_val z)
  have HX := feature_principal c j s d k r hs hd hk hr (extend x)
  have HY := feature_principal c j s d k r hs hd hk hr (extend y)
  rw [HE x] at HX
  rw [HE y] at HY
  have HSign := HS ⟨i,HI⟩
  change SignType.sign ((family.feature c i).eval₂ (Int.castRingHom ℝ) x)=
    SignType.sign ((family.feature c i).eval₂ (Int.castRingHom ℝ) y) at HSign
  rw [HX,HY] at HSign
  have H0 := Iff.of_eq (congrArg (fun a : SignType => a=0) HSign)
  simpa only [sign_eq_zero_iff] using H0

noncomputable abbrev principalContext (c : List Bool) (j s d : ℕ) :=
  pair (coordinateContext c j) (pair (BinaryNatCode.encode s) (BinaryNatCode.encode d))
private theorem selected_degree (c : List Bool) (j s d : ℕ) :
    FormulaSignSlotRadialCenterPrincipalFamily.degree (principalContext c j s d)=d := by
  simp only [principalContext,FormulaSignSlotRadialCenterPrincipalFamily.degree,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
private theorem selected_tau (c : List Bool) (j s d : ℕ) :
    FormulaSignSlotRadialCenterPrincipalFamily.tau (principalContext c j s d)=s := by
  simp only [principalContext,FormulaSignSlotRadialCenterPrincipalFamily.tau,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
private theorem selected_original (c : List Bool) (j s d : ℕ) :
    FormulaSignSlotRadialCenterPrincipalFamily.original (principalContext c j s d)=coordinateContext c j := pairFst_pair _ _
private theorem selected_bound (c : List Bool) (j s d : ℕ) (hd : d ≤ degree c) :
    FormulaSignSlotRadialCenterPrincipalFamily.degreeBound (principalContext c j s d) < radiusLimit c := by
  apply Nat.lt_succ_of_le
  apply FormulaSignSlotRadialJointPrincipalBounds.degree_le
  · simp only [selected_original,coordinateContext,FormulaSignSlotRadialCoordinatePacket.root]
  · simpa only [selected_degree] using hd
private theorem original_bound (c : List Bool) (j : ℕ) :
    FormulaSignSlotRadialCenterSelection.bound (coordinateContext c j)=degree c := by
  apply FormulaSignSlotRadialEliminantRootProfiles.degree_eq
  simp only [coordinateContext,FormulaSignSlotRadialCoordinatePacket.root,
    FormulaSignSlotRadialJointCoefficientCatalogue.base,pairFst_pair]

private def selectionValue (c : List Bool) (v : ℕ → ℝ) (s d : ℕ) : Prop :=
  FormulaSignSlotRadialCenterSelection.Guards c (fun i => v (4*i.val)) s d

private theorem paired_selection (c : List Bool) (s d : ℕ) (v : ℕ → ℝ) :
    FormulaSignSlotRadialCenterSelection.Guards
      (FormulaSignSlotRadialCenterPrincipalFamily.original (pair c (pair (BinaryNatCode.encode s) (BinaryNatCode.encode d))))
      (fun i => v (4*i.val))
      (FormulaSignSlotRadialCenterPrincipalFamily.tau (pair c (pair (BinaryNatCode.encode s) (BinaryNatCode.encode d))))
      (FormulaSignSlotRadialCenterPrincipalFamily.degree (pair c (pair (BinaryNatCode.encode s) (BinaryNatCode.encode d)))) ↔
      FormulaSignSlotRadialCenterSelection.Guards c (fun i => v (4*i.val)) s d := by
  simp only [FormulaSignSlotRadialCenterPrincipalFamily.original,FormulaSignSlotRadialCenterPrincipalFamily.tau,
    FormulaSignSlotRadialCenterPrincipalFamily.degree,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  change selectionValue (pairFst (pair c (pair s.bits d.bits))) v s d ↔ selectionValue c v s d
  rw [pairFst_pair]

private theorem guards_transfer (C : List Bool)
    (a b : Fin (FormulaSignSlotCenteredRadialGraph.d (pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original C))) → ℝ)
    (k : ℕ)
    (HB : FormulaSignSlotRadialCenterSelection.Guards (FormulaSignSlotRadialCenterPrincipalFamily.original C) a
      (FormulaSignSlotRadialCenterPrincipalFamily.tau C) (FormulaSignSlotRadialCenterPrincipalFamily.degree C) ↔
      FormulaSignSlotRadialCenterSelection.Guards (FormulaSignSlotRadialCenterPrincipalFamily.original C) b
      (FormulaSignSlotRadialCenterPrincipalFamily.tau C) (FormulaSignSlotRadialCenterPrincipalFamily.degree C))
    (HZ : ∀ j < FormulaSignSlotRadialCenterPrincipalFamily.degree C,
      ∀ r < FormulaSignSlotRadialCenterPrincipalFamily.degreeBound C+1,
      FormulaSignSlotRadialCenterPrincipalGuards.Zero C a j r ↔ FormulaSignSlotRadialCenterPrincipalGuards.Zero C b j r) :
    FormulaSignSlotRadialCenterPrincipalGuards.Guards C a k ↔ FormulaSignSlotRadialCenterPrincipalGuards.Guards C b k := by
  unfold FormulaSignSlotRadialCenterPrincipalGuards.Guards
  apply and_congr HB
  split_ifs with HD
  · rfl
  · apply and_congr_right
    intro hk
    exact and_congr (forall_congr' (fun j => forall_congr' (fun hj => forall_congr' (fun r =>
      forall_congr' (fun hr => HZ j (lt_trans hj hk) r hr)))))
      (not_congr (forall_congr' (fun r => forall_congr' (fun hr => HZ k hk r hr))))

theorem guards_iff_of_signs (c : List Bool) (j : ℕ) (hj : j<FormulaSignSlotRadialJointLayout.spatialCount c)
    (x y : Point c) (HC : FormulaSignSlotRadialJointSelectionStratum.Signs c x y)
    (HP : Signs c x y) (tau d k : ℕ) :
    FormulaSignSlotRadialCenterPrincipalGuards.Guards (principalContext c j tau d) (fun i => extend x (4*i.val)) k ↔
      FormulaSignSlotRadialCenterPrincipalGuards.Guards (principalContext c j tau d) (fun i => extend y (4*i.val)) k := by
  have HB := FormulaSignSlotRadialJointSelectionStratum.guards_iff_of_signs c j hj x y HC tau d
  have BX := paired_selection (coordinateContext c j) tau d (extend x)
  have BY := paired_selection (coordinateContext c j) tau d (extend y)
  have HC0 := BX.trans (HB.trans BY.symm)
  by_cases HX : FormulaSignSlotRadialCenterSelection.Guards (coordinateContext c j) (center c j x) tau d
  · have HT : tau<limit c := by have := HX.1; rw [original_bound] at this; unfold limit; omega
    have HD : d<limit c := by have := HX.2.1; rw [original_bound] at this; unfold limit; omega
    have HDB : d ≤ degree c := by unfold limit at HD; omega
    have HRadius := selected_bound c j tau d HDB
    apply guards_transfer _ _ _ k HC0
    intro a ha r hr
    rw [selected_degree] at ha
    change r<FormulaSignSlotRadialCenterPrincipalFamily.degreeBound (principalContext c j tau d)+1 at hr
    exact coefficient_zero_iff c x y HP j tau d a r hj HT HD (by omega) (by omega)
  · have HY := HB.not.mp HX
    have HXX := BX.not.mpr HX
    have HYY := BY.not.mpr HY
    exact iff_of_false (fun H => HXX H.1) (fun H => HYY H.1)

private def squarefreeValue (c : List Bool) (v : ℕ → ℝ) (s d k : ℕ) : Prop :=
  FormulaSignSlotRadialCenterSquarefreeSelection.Guards c (fun i => v (4*i.val)) s d k
private theorem paired_squarefree (c : List Bool) (s d k : ℕ) (v : ℕ → ℝ) :
    FormulaSignSlotRadialCenterPrincipalGuards.Guards
      (pair c (pair (BinaryNatCode.encode s) (BinaryNatCode.encode d))) (fun i => v (4*i.val)) k ↔
      FormulaSignSlotRadialCenterSquarefreeSelection.Guards c (fun i => v (4*i.val)) s d k := by
  rw [FormulaSignSlotRadialCenterPrincipalGuards.guards_iff]
  simp only [FormulaSignSlotRadialCenterPrincipalFamily.original,FormulaSignSlotRadialCenterPrincipalFamily.tau,
    FormulaSignSlotRadialCenterPrincipalFamily.degree,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  change squarefreeValue (pairFst (pair c (pair s.bits d.bits))) v s d k ↔ squarefreeValue c v s d k
  rw [pairFst_pair]

theorem squarefree_guards_iff_of_signs (c : List Bool) (j : ℕ)
    (hj : j<FormulaSignSlotRadialJointLayout.spatialCount c) (x y : Point c)
    (HC : FormulaSignSlotRadialJointSelectionStratum.Signs c x y) (HP : Signs c x y) (tau d k : ℕ) :
    FormulaSignSlotRadialCenterSquarefreeSelection.Guards (coordinateContext c j) (center c j x) tau d k ↔
      FormulaSignSlotRadialCenterSquarefreeSelection.Guards (coordinateContext c j) (center c j y) tau d k :=
  (paired_squarefree (coordinateContext c j) tau d k (extend x)).symm.trans
    ((guards_iff_of_signs c j hj x y HC HP tau d k).trans
      (paired_squarefree (coordinateContext c j) tau d k (extend y)))

end LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalStratum
