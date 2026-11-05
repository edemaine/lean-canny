/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalCatalogue
/-! # The mixed-radix box contains every bounded actual principal coefficient -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalCatalogue
open LeanCanny.Computation
open FormulaSignSlotRadialJointCoefficientCatalogue (limit)
set_option backward.isDefEq.respectTransparency false

noncomputable def encode (c : List Bool) (j s d k r : ℕ) :=
  r+radiusLimit c*(k+limit c*(d+limit c*(s+limit c*j)))
private theorem digit_div (B a d : ℕ) (hd : d<B) : (d+B*a)/B=a := by
  have HB : 0<B := by omega
  rw [Nat.add_mul_div_left _ _ HB,Nat.div_eq_of_lt hd,Nat.zero_add]
private theorem digit_lt {a A B d : ℕ} (ha : a<A) (hd : d<B) : d+B*a<B*A := by
  calc
    _ < B+B*a := Nat.add_lt_add_right hd _
    _ = B*(a+1) := by ring
    _ ≤ B*A := Nat.mul_le_mul_left B (by omega)

theorem decode (c : List Bool) (j s d k r : ℕ)
    (hs : s<limit c) (hd : d<limit c) (hk : k<limit c) (hr : r<radiusLimit c) :
    radiusIndex c (encode c j s d k r)=r ∧ orderIndex c (encode c j s d k r)=k ∧
      declaredIndex c (encode c j s d k r)=d ∧ tauIndex c (encode c j s d k r)=s ∧
      coordinate c (encode c j s d k r)=j := by
  have H0 : encode c j s d k r/radiusLimit c=k+limit c*(d+limit c*(s+limit c*j)) := digit_div _ _ _ hr
  have H1 : (k+limit c*(d+limit c*(s+limit c*j)))/limit c=d+limit c*(s+limit c*j) := digit_div _ _ _ hk
  have H2 : (d+limit c*(s+limit c*j))/limit c=s+limit c*j := digit_div _ _ _ hd
  have H3 : (s+limit c*j)/limit c=j := digit_div _ _ _ hs
  refine ⟨?_,?_,?_,?_,?_⟩
  · change encode c j s d k r%radiusLimit c=r
    rw [encode,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr]
  · change (encode c j s d k r/radiusLimit c)%limit c=k
    rw [H0,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hk]
  · change (encode c j s d k r/radiusLimit c/limit c)%limit c=d
    rw [H0,H1,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hd]
  · change (encode c j s d k r/radiusLimit c/limit c/limit c)%limit c=s
    rw [H0,H1,H2,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hs]
  · change encode c j s d k r/radiusLimit c/limit c/limit c/limit c=j
    rw [H0,H1,H2,H3]

theorem encode_lt (c : List Bool) (j s d k r : ℕ)
    (hj : j<FormulaSignSlotRadialJointLayout.spatialCount c)
    (hs : s<limit c) (hd : d<limit c) (hk : k<limit c) (hr : r<radiusLimit c) :
    encode c j s d k r<count c := by
  have H1 := digit_lt hj hs
  have H2 := digit_lt H1 hd
  have H3 := digit_lt H2 hk
  have H4 := digit_lt H3 hr
  have HE : radiusLimit c*(limit c*(limit c*(limit c*FormulaSignSlotRadialJointLayout.spatialCount c)))=count c := by
    unfold count
    ring
  exact H4.trans_eq HE

theorem row_encode (c : List Bool) (j s d k r : ℕ)
    (hs : s<limit c) (hd : d<limit c) (hk : k<limit c) (hr : r<radiusLimit c) :
    row (pair c (BinaryNatCode.encode (encode c j s d k r))) = pair c
      (WordList.encode [BinaryNatCode.encode j,BinaryNatCode.encode s,BinaryNatCode.encode d,
        BinaryNatCode.encode k,BinaryNatCode.encode r]) := by
  obtain ⟨HR,HK,HD,HS,HC⟩ := decode c j s d k r hs hd hk hr
  simp only [row,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,HR,HK,HD,HS,HC]

end LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalCatalogue
