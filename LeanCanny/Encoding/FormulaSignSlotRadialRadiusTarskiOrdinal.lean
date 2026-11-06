/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiCatalogue
/-! # Every bounded coordinate-head window control occurs in the catalogue -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiCatalogue
open LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false

noncomputable def encode (c:List Bool) (role moment j s d e t:ℕ):=
  role+3*(moment+2*(j+limit c*(s+limit c*(d+limit c*(e+limit c*t)))))

private theorem digit_div (B a d:ℕ) (hd:d < B):(d+B*a)/B=a:=by
  rw [Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt hd,Nat.zero_add]
private theorem digit_lt {a A B d:ℕ} (ha:a < A) (hd:d < B):d+B*a < B*A:=by
  calc
    _ < B+B*a:=Nat.add_lt_add_right hd _
    _ = B*(a+1):=by ring
    _ ≤ B*A:=Nat.mul_le_mul_left B (by omega)

theorem decode (c:List Bool) (r m j s d e t:ℕ) (hr:r < 3) (hm:m < 2)
    (hj:j < limit c) (hs:s < limit c) (hd:d < limit c) (he:e < limit c) (ht:t < limit c):
    encode c r m j s d e t%3=r ∧(encode c r m j s d e t/3)%2=m ∧
      order c (encode c r m j s d e t)=j ∧seed c (encode c r m j s d e t)=s ∧
      declared c (encode c r m j s d e t)=d ∧eta c (encode c r m j s d e t)=e ∧
      tau c (encode c r m j s d e t)=t:=by
  let a:=j+limit c*(s+limit c*(d+limit c*(e+limit c*t)))
  have H3:encode c r m j s d e t/3=m+2*a:=digit_div _ _ _ hr
  have HE:encode c r m j s d e t=(r+3*m)+6*a:=by unfold encode a;ring
  have H0:encode c r m j s d e t/6=a:=by rw [HE];exact digit_div _ _ _ (by omega)
  have H1:a/limit c=s+limit c*(d+limit c*(e+limit c*t)):=digit_div _ _ _ hj
  have H2:(s+limit c*(d+limit c*(e+limit c*t)))/limit c=d+limit c*(e+limit c*t):=digit_div _ _ _ hs
  have H4:(d+limit c*(e+limit c*t))/limit c=e+limit c*t:=digit_div _ _ _ hd
  have H5:(e+limit c*t)/limit c=t:=digit_div _ _ _ he
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [encode,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr]
  · rw [H3,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hm]
  · change (encode c r m j s d e t/6)%limit c=j
    rw [H0]
    dsimp only [a]
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hj]
  · change (encode c r m j s d e t/6/limit c)%limit c=s
    rw [H0,H1,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hs]
  · change (encode c r m j s d e t/6/limit c/limit c)%limit c=d
    rw [H0,H1,H2,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hd]
  · change (encode c r m j s d e t/6/limit c/limit c/limit c)%limit c=e
    rw [H0,H1,H2,H4,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt he]
  · change (encode c r m j s d e t/6/limit c/limit c/limit c/limit c)%limit c=t
    rw [H0,H1,H2,H4,H5,Nat.mod_eq_of_lt ht]

theorem encode_lt (c:List Bool) (r m j s d e t:ℕ) (hr:r < 3) (hm:m < 2)
    (hj:j < limit c) (hs:s < limit c) (hd:d < limit c) (he:e < limit c) (ht:t < limit c):
    encode c r m j s d e t < count c:=by
  have H1:=digit_lt ht he
  have H2:=digit_lt H1 hd
  have H3:=digit_lt H2 hs
  have H4:=digit_lt H3 hj
  have H5:=digit_lt H4 hm
  have H6:=digit_lt H5 hr
  have HE:3*(2*(limit c*(limit c*(limit c*(limit c*limit c)))))=count c:=by unfold count;ring
  exact H6.trans_eq HE

theorem row_encode (c:List Bool) (r m j s d e t:ℕ) (hr:r < 3) (hm:m < 2)
    (hj:j < limit c) (hs:s < limit c) (hd:d < limit c) (he:e < limit c) (ht:t < limit c):
    row (pair c (BinaryNatCode.encode (encode c r m j s d e t)))=
      pair (if r=0 then [] else if r=1 then [false] else [true])
        (pair (familyContext c t e d s (decide (m=1))) (BinaryNatCode.encode j)):=by
  obtain ⟨HR,HM,HJ,HS,HD,HE,HT⟩:=decode c r m j s d e t hr hm hj hs hd he ht
  simp only [row,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    roleWord,square,HR,HM,HJ,HS,HD,HE,HT]

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiCatalogue
