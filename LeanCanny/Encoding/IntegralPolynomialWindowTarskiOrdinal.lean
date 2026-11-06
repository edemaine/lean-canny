/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiCatalogue
/-! # Exact bounded-control coverage for an actual-source window catalogue -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralPolynomialWindowTarskiCatalogue
open LeanCanny.Computation
open IntegralFramedBankPolynomialModel (Source)
set_option backward.isDefEq.respectTransparency false

noncomputable def encode (S:Source) (c:List Bool) (r m j s d:ℕ):=
  r+3*(m+2*(j+limit S c*(s+limit S c*d)))
private theorem digit_div (B a d:ℕ) (hd:d < B):(d+B*a)/B=a:=by
  rw [Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt hd,Nat.zero_add]
private theorem digit_lt {a A B d:ℕ} (ha:a < A) (hd:d < B):d+B*a < B*A:=by
  calc
    _ < B+B*a:=Nat.add_lt_add_right hd _
    _ = B*(a+1):=by ring
    _ ≤ B*A:=Nat.mul_le_mul_left B (by omega)

theorem decode (S:Source) (c:List Bool) (r m j s d:ℕ) (hr:r < 3) (hm:m < 2)
    (hj:j < limit S c) (hs:s < limit S c) (hd:d < limit S c):
    encode S c r m j s d%3=r ∧(encode S c r m j s d/3)%2=m ∧
      orderIndex S c (encode S c r m j s d)=j ∧seedIndex S c (encode S c r m j s d)=s ∧
      degreeIndex S c (encode S c r m j s d)=d:=by
  let a:=j+limit S c*(s+limit S c*d)
  have H3:encode S c r m j s d/3=m+2*a:=digit_div _ _ _ hr
  have HE:encode S c r m j s d=(r+3*m)+6*a:=by unfold encode a;ring
  have H0:encode S c r m j s d/6=a:=by rw [HE];exact digit_div _ _ _ (by omega)
  have H1:a/limit S c=s+limit S c*d:=digit_div _ _ _ hj
  have H2:(s+limit S c*d)/limit S c=d:=digit_div _ _ _ hs
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [encode,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr]
  · rw [H3,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hm]
  · change (encode S c r m j s d/6)%limit S c=j
    rw [H0]
    dsimp only [a]
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hj]
  · change (encode S c r m j s d/6/limit S c)%limit S c=s
    rw [H0,H1,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hs]
  · change (encode S c r m j s d/6/limit S c/limit S c)%limit S c=d
    rw [H0,H1,H2,Nat.mod_eq_of_lt hd]

theorem encode_lt (S:Source) (c:List Bool) (r m j s d:ℕ) (hr:r < 3) (hm:m < 2)
    (hj:j < limit S c) (hs:s < limit S c) (hd:d < limit S c):encode S c r m j s d < count S c:=by
  have H1:=digit_lt hd hs
  have H2:=digit_lt H1 hj
  have H3:=digit_lt H2 hm
  have H4:=digit_lt H3 hr
  have HE:3*(2*(limit S c*(limit S c*limit S c)))=count S c:=by unfold count;ring
  exact H4.trans_eq HE

theorem row_encode (S:Source) (c:List Bool) (r m j s d:ℕ) (hr:r < 3) (hm:m < 2)
    (hj:j < limit S c) (hs:s < limit S c) (hd:d < limit S c):
    row S (pair c (BinaryNatCode.encode (encode S c r m j s d)))=
      pair (BinaryNatCode.encode r) (pair (control c d s (decide (m=1))) (BinaryNatCode.encode j)):=by
  obtain ⟨HR,HM,HJ,HS,HD⟩:=decode S c r m j s d hr hm hj hs hd
  simp only [row,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,square,HR,HM,HJ,HS,HD]

end LeanCanny.Encoding.IntegralPolynomialWindowTarskiCatalogue
