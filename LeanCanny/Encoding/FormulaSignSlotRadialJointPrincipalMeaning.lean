/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalOrdinal
/-! # Literal same-center meaning of every principal feature -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalCatalogue
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MvPolynomial
open FormulaSignSlotRadialJointCoefficientCatalogue (limit)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def principalValue (c : List Bool) (j s d k r : ℕ) (v : ℕ → ℝ) : ℝ :=
  (FormulaSignSlotRadialCenterPrincipalCoefficient.polynomial
    (pair (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true c) j)
      (pair (BinaryNatCode.encode s) (BinaryNatCode.encode d))) k r).eval₂
      (Int.castRingHom ℝ) (fun i => v (4*i.val))
private noncomputable def entry (c : List Bool) (k r : ℕ) (v : ℕ → ℝ) : ℝ :=
  (FormulaSignSlotRadialCenterPrincipalCoefficient.polynomial c k r).eval₂ (Int.castRingHom ℝ) (fun i => v (4*i.val))
private noncomputable def rawValue (z : List Bool) (v : ℕ → ℝ) : ℝ :=
  (FormulaSignSlotRadialRetainedPrincipalTest.source.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i => v (4*i.val))
private noncomputable def jointValue (z : List Bool) (v : ℕ → ℝ) : ℝ :=
  (FormulaSignSlotRadialJointPrincipalSource.source.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i => v i.val)
private theorem joint_read (z : List Bool) (v : ℕ → ℝ) : jointValue z v=
    rawValue (FormulaSignSlotRadialJointPrincipalSource.read z) v :=
  FormulaSignSlotRadialJointPrincipalSource.evaluation z v
private theorem raw_entry (z : List Bool) (v : ℕ → ℝ) : rawValue z v = entry (pairFst z)
    (Nat.fromBitsLE (pairFst (pairSnd z))) (Nat.fromBitsLE (pairSnd (pairSnd z))) v := rfl
attribute [local irreducible] entry rawValue
private theorem raw_read (z : List Bool) (v : ℕ → ℝ) : rawValue (FormulaSignSlotRadialJointPrincipalSource.read z) v =
    entry (pair (FormulaSignSlotRadialCoordinatePacket.writer
      (pair (FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialJointPrincipalSource.header z))
        (FormulaSignSlotRadialJointPrincipalSource.slot 0 z)))
      (pair (FormulaSignSlotRadialJointPrincipalSource.slot 1 z) (FormulaSignSlotRadialJointPrincipalSource.slot 2 z)))
      (Nat.fromBitsLE (FormulaSignSlotRadialJointPrincipalSource.slot 3 z))
      (Nat.fromBitsLE (FormulaSignSlotRadialJointPrincipalSource.slot 4 z)) v := by
  rw [raw_entry]
  simp only [FormulaSignSlotRadialJointPrincipalSource.read,pairFst_pair,pairSnd_pair]
private theorem packet_value (c : List Bool) (j s d k r : ℕ) (v : ℕ → ℝ) :
    jointValue (pair c (WordList.encode [BinaryNatCode.encode j,BinaryNatCode.encode s,
      BinaryNatCode.encode d,BinaryNatCode.encode k,BinaryNatCode.encode r])) v = principalValue c j s d k r v := by
  rw [joint_read]
  rw [raw_read]
  simp only [FormulaSignSlotRadialJointPrincipalSource.header,FormulaSignSlotRadialJointPrincipalSource.slot,
    pairFst_pair,pairSnd_pair,WordList.reader,WordList.get_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rw [show FormulaSignSlotRadialCoordinatePacket.writer
      (pair (FormulaSignSlotRadialJointLayout.source true c) j.bits)=
    FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true c) j from
      FormulaSignSlotRadialCoordinatePacket.writer_packet _ j]
  unfold entry principalValue
  rfl

private theorem eval_cast {a b : ℕ} (h : a=b) (p : MvPolynomial (Fin a) ℤ) (v : ℕ → ℝ) :
    (rename (Fin.cast h) p).eval₂ (Int.castRingHom ℝ) (fun i => v i.val)=
      p.eval₂ (Int.castRingHom ℝ) (fun i => v i.val) := by
  subst b
  simp only [Fin.cast_refl,rename_id,AlgHom.id_apply]

private theorem feature_value (c : List Bool) (i : ℕ) (v : ℕ → ℝ) :
    (family.feature c i).eval₂ (Int.castRingHom ℝ) (fun j => v j.val)=
      jointValue (row (pair c (BinaryNatCode.encode i))) v := by
  unfold jointValue
  exact eval_cast (arity_eq c i) (FormulaSignSlotRadialJointPrincipalSource.source.polynomial _) v
attribute [local irreducible] jointValue

theorem feature_principal (c : List Bool) (j s d k r : ℕ)
    (hs : s<limit c) (hd : d<limit c) (hk : k<limit c) (hr : r<radiusLimit c) (v : ℕ → ℝ) :
    (family.feature c (encode c j s d k r)).eval₂ (Int.castRingHom ℝ) (fun i => v i.val)=
      principalValue c j s d k r v := by
  rw [feature_value,row_encode c j s d k r hs hd hk hr]
  exact packet_value c j s d k r v

end LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalCatalogue
