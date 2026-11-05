/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientCatalogue
/-! # Every bounded actual coefficient occurs in the binary catalogue -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientCatalogue
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false

noncomputable def encode (c : List Bool) (j s t r : ℕ) :=
  r+limit c*(t+limit c*(s+limit c*j))

private theorem digit_div (B a d : ℕ) (hd : d<B) : (d+B*a)/B=a := by
  have HB : 0<B := by omega
  rw [Nat.add_mul_div_left _ _ HB,Nat.div_eq_of_lt hd,Nat.zero_add]
private theorem digit_lt {a A B d : ℕ} (ha : a<A) (hd : d<B) : d+B*a<B*A := by
  calc
    _ < B+B*a := Nat.add_lt_add_right hd _
    _ = B*(a+1) := by ring
    _ ≤ B*A := Nat.mul_le_mul_left B (by omega)

theorem decode (c : List Bool) (j s t r : ℕ) (hs : s<limit c) (ht : t<limit c) (hr : r<limit c) :
    radiusIndex c (encode c j s t r)=r ∧ targetIndex c (encode c j s t r)=t ∧
      tauIndex c (encode c j s t r)=s ∧ coordinate c (encode c j s t r)=j := by
  have H0 : encode c j s t r/limit c=t+limit c*(s+limit c*j) := digit_div _ _ _ hr
  have H1 : (t+limit c*(s+limit c*j))/limit c=s+limit c*j := digit_div _ _ _ ht
  have H2 : (s+limit c*j)/limit c=j := digit_div _ _ _ hs
  refine ⟨?_,?_,?_,?_⟩
  · change encode c j s t r%limit c=r
    rw [encode,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr]
  · change (encode c j s t r/limit c)%limit c=t
    rw [H0,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ht]
  · change (encode c j s t r/limit c/limit c)%limit c=s
    rw [H0,H1,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hs]
  · change encode c j s t r/limit c/limit c/limit c=j
    rw [H0,H1,H2]

theorem encode_lt (c : List Bool) (j s t r : ℕ)
    (hj : j<FormulaSignSlotRadialJointLayout.spatialCount c)
    (hs : s<limit c) (ht : t<limit c) (hr : r<limit c) : encode c j s t r<count c := by
  have H1 := digit_lt hj hs
  have H2 := digit_lt H1 ht
  have H3 := digit_lt H2 hr
  have HE : limit c*(limit c*(limit c*FormulaSignSlotRadialJointLayout.spatialCount c))=count c := by
    unfold count
    ring
  exact H3.trans_eq HE

theorem row_encode (c : List Bool) (j s t r : ℕ) (hs : s<limit c) (ht : t<limit c) (hr : r<limit c) :
    row (pair c (BinaryNatCode.encode (encode c j s t r))) =
      pair c (WordList.encode [BinaryNatCode.encode j,BinaryNatCode.encode s,BinaryNatCode.encode t,BinaryNatCode.encode r]) := by
  obtain ⟨HR,HT,HS,HC⟩ := decode c j s t r hs ht hr
  simp only [row,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,HR,HT,HS,HC]

end LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientCatalogue
