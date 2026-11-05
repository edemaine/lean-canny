/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientOrdinal
/-! # The bounded catalogue contains the literal same-center coefficient tests -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientCatalogue
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def coefficientValue (c : List Bool) (j s t r : ℕ) (v : ℕ → ℝ) : ℝ :=
  (FormulaSignSlotRadialCenterCoefficient.polynomial
    (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true c) j) s t r).eval₂
      (Int.castRingHom ℝ) (fun i => v (4*i.val))
private noncomputable def entry (c : List Bool) (s t r : ℕ) (v : ℕ → ℝ) : ℝ :=
  (FormulaSignSlotRadialCenterCoefficient.polynomial c s t r).eval₂ (Int.castRingHom ℝ) (fun i => v (4*i.val))
private noncomputable def rawValue (z : List Bool) (v : ℕ → ℝ) : ℝ :=
  (FormulaSignSlotRadialRetainedCoordinateTest.source.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i => v (4*i.val))
private noncomputable def jointValue (z : List Bool) (v : ℕ → ℝ) : ℝ :=
  (FormulaSignSlotRadialJointCoefficientSource.source.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i => v i.val)

private theorem joint_read (z : List Bool) (v : ℕ → ℝ) : jointValue z v=
    rawValue (FormulaSignSlotRadialJointCoefficientSource.read z) v :=
  FormulaSignSlotRadialJointCoefficientSource.evaluation z v

private theorem rawValue_entry (z : List Bool) (v : ℕ → ℝ) : rawValue z v = entry (pairFst z)
    (FormulaSignSlotRadialCenterCoefficientSource.selected 0 z)
    (FormulaSignSlotRadialCenterCoefficientSource.selected 1 z)
    (FormulaSignSlotRadialCenterCoefficientSource.selected 2 z) v := rfl
attribute [local irreducible] entry rawValue
private theorem rawValue_read (z : List Bool) (v : ℕ → ℝ) : rawValue (FormulaSignSlotRadialJointCoefficientSource.read z) v =
    entry (FormulaSignSlotRadialCoordinatePacket.writer
      (pair (FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialJointCoefficientSource.header z))
        (FormulaSignSlotRadialJointCoefficientSource.slot 0 z)))
      (Nat.fromBitsLE (FormulaSignSlotRadialJointCoefficientSource.slot 1 z))
      (Nat.fromBitsLE (FormulaSignSlotRadialJointCoefficientSource.slot 2 z))
      (Nat.fromBitsLE (FormulaSignSlotRadialJointCoefficientSource.slot 3 z)) v := by
  rw [rawValue_entry]
  simp only [FormulaSignSlotRadialJointCoefficientSource.read,FormulaSignSlotRadialCenterCoefficientSource.selected,
    pairFst_pair,pairSnd_pair,WordList.get_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

private theorem packet_value (c : List Bool) (j s t r : ℕ) (v : ℕ → ℝ) :
    jointValue (pair c (WordList.encode [BinaryNatCode.encode j,BinaryNatCode.encode s,
      BinaryNatCode.encode t,BinaryNatCode.encode r])) v = coefficientValue c j s t r v := by
  have H := joint_read
    (pair c (WordList.encode [BinaryNatCode.encode j,BinaryNatCode.encode s,BinaryNatCode.encode t,BinaryNatCode.encode r])) v
  refine H.trans ?_
  rw [rawValue_read]
  simp only [FormulaSignSlotRadialJointCoefficientSource.header,FormulaSignSlotRadialJointCoefficientSource.slot,
    pairFst_pair,pairSnd_pair,WordList.reader,WordList.get_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rw [show FormulaSignSlotRadialCoordinatePacket.writer
      (pair (FormulaSignSlotRadialJointLayout.source true c) j.bits)=
    FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true c) j from
      FormulaSignSlotRadialCoordinatePacket.writer_packet _ j]
  unfold entry coefficientValue
  rfl

private theorem eval_cast {a b : ℕ} (h : a=b) (p : MvPolynomial (Fin a) ℤ) (v : ℕ → ℝ) :
    (rename (Fin.cast h) p).eval₂ (Int.castRingHom ℝ) (fun i => v i.val)=
      p.eval₂ (Int.castRingHom ℝ) (fun i => v i.val) := by
  subst b
  simp only [Fin.cast_refl,MvPolynomial.rename_id,AlgHom.id_apply]
private theorem feature_value (c : List Bool) (i : ℕ) (v : ℕ → ℝ) :
    (family.feature c i).eval₂ (Int.castRingHom ℝ) (fun j => v j.val)=
      jointValue (row (pair c (BinaryNatCode.encode i))) v := by
  unfold jointValue
  exact eval_cast (arity_eq c i) (FormulaSignSlotRadialJointCoefficientSource.source.polynomial _) v
attribute [local irreducible] jointValue

theorem feature_coefficient (c : List Bool) (j s t r : ℕ) (hs : s<limit c) (ht : t<limit c) (hr : r<limit c)
    (v : ℕ → ℝ) : (family.feature c (encode c j s t r)).eval₂ (Int.castRingHom ℝ) (fun i => v i.val)=
      coefficientValue c j s t r v := by
  rw [feature_value,row_encode c j s t r hs ht hr]
  exact packet_value c j s t r v

end LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientCatalogue
