/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialPrincipalWindowCatalogue
/-! # Every genuine principal/window control tuple has a literal row

The inner ordinal is encoded at its actual raw-source degree. Its safe
original outer allowance is proved rather than substituted into the row.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialPrincipalWindowCatalogue
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S"=>FormulaSignSlotRadialPrincipalRadiusSource.source

noncomputable def encode (u:List Bool) (t d j k:ℕ):=
  k+innerLimit u*(j+orderLimit u*(d+outerLimit u*t))
private theorem digit_div (B a d:ℕ) (hd:d < B):(d+B*a)/B=a:=by
  rw [Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt hd,Nat.zero_add]
private theorem digit_lt {a A B d:ℕ} (ha:a < A) (hd:d < B):d+B*a < B*A:=by
  calc
    _  <  B+B*a:=Nat.add_lt_add_right hd _
    _ = B*(a+1):=by ring
    _ ≤ B*A:=Nat.mul_le_mul_left B (by omega)

theorem decode (u:List Bool) (t d j k:ℕ) (ht:t < outerLimit u) (hd:d < outerLimit u)
    (hj:j < orderLimit u) (hk:k < innerLimit u):
    innerIndex u (encode u t d j k)=k ∧orderIndex u (encode u t d j k)=j ∧
      declaredIndex u (encode u t d j k)=d ∧tauIndex u (encode u t d j k)=t:=by
  have H0:encode u t d j k/innerLimit u=j+orderLimit u*(d+outerLimit u*t):=digit_div _ _ _ hk
  have H1:(j+orderLimit u*(d+outerLimit u*t))/orderLimit u=d+outerLimit u*t:=digit_div _ _ _ hj
  have H2:(d+outerLimit u*t)/outerLimit u=t:=digit_div _ _ _ hd
  refine ⟨?_,?_,?_,?_⟩
  · change encode u t d j k%innerLimit u=k
    rw [encode,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hk]
  · change (encode u t d j k/innerLimit u)%orderLimit u=j
    rw [H0,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hj]
  · change (encode u t d j k/innerLimit u/orderLimit u)%outerLimit u=d
    rw [H0,H1,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hd]
  · change (encode u t d j k/innerLimit u/orderLimit u/outerLimit u)%outerLimit u=t
    rw [H0,H1,H2,Nat.mod_eq_of_lt ht]

theorem encode_lt (u:List Bool) (t d j k:ℕ) (ht:t < outerLimit u) (hd:d < outerLimit u)
    (hj:j < orderLimit u) (hk:k < innerLimit u):encode u t d j k < count u:=by
  have H1:=digit_lt ht hd
  have H2:=digit_lt H1 hj
  have H3:=digit_lt H2 hk
  have HE:innerLimit u*(orderLimit u*(outerLimit u*outerLimit u))=count u:=by unfold count;ring
  exact H3.trans_eq HE

theorem row_encode (u:List Bool) (t d j k:ℕ) (ht:t < outerLimit u) (hd:d < outerLimit u)
    (hj:j < orderLimit u) (hk:k < innerLimit u):
    row (pair u (BinaryNatCode.encode (encode u t d j k)))=
      IntegralPolynomialWindowTarskiCatalogue.row S
        (pair (FormulaSignSlotRadialPrincipalWindowBounds.rawContext u t d j) (BinaryNatCode.encode k)):=by
  obtain ⟨HK,HJ,HD,HT⟩:=decode u t d j k ht hd hj hk
  rw [row_packet]
  simp only [raw,HK,HJ,HD,HT]

/-- Every genuine original PSC control and every actual inner ordinal occurs. -/
theorem covers (u:List Bool) (t d j k:ℕ)
    (ht:t ≤ FormulaSignSlotRadialPrincipalWindowBounds.bound u)
    (hd:d ≤ FormulaSignSlotRadialPrincipalWindowBounds.bound u)
    (hj:j ≤ 2*FormulaSignSlotRadialPrincipalWindowBounds.bound u+1)
    (hk:k < IntegralPolynomialWindowTarskiCatalogue.count S
      (FormulaSignSlotRadialPrincipalWindowBounds.rawContext u t d j)):
    ∃i < count u,row (pair u (BinaryNatCode.encode i))=
      IntegralPolynomialWindowTarskiCatalogue.row S
        (pair (FormulaSignSlotRadialPrincipalWindowBounds.rawContext u t d j) (BinaryNatCode.encode k)):=by
  have HK:k < innerLimit u:=hk.trans_le (FormulaSignSlotRadialPrincipalWindowBounds.inner_count_le u _
    (FormulaSignSlotRadialPrincipalWindowBounds.raw_length u t d j ht hd hj))
  have HT:t < outerLimit u:=by unfold outerLimit;omega
  have HD:d < outerLimit u:=by unfold outerLimit;omega
  have HJ:j < orderLimit u:=by unfold orderLimit;omega
  exact ⟨encode u t d j k,encode_lt u t d j k HT HD HJ HK,row_encode u t d j k HT HD HJ HK⟩

/-- All three roles and both moments are covered at the actual inner degree. -/
theorem covers_controls (u:List Bool) (t d j r m p s v:ℕ)
    (ht:t ≤ FormulaSignSlotRadialPrincipalWindowBounds.bound u)
    (hd:d ≤ FormulaSignSlotRadialPrincipalWindowBounds.bound u)
    (hj:j ≤ 2*FormulaSignSlotRadialPrincipalWindowBounds.bound u+1) (hr:r < 3) (hm:m < 2)
    (hp:p < IntegralPolynomialWindowTarskiCatalogue.limit S (FormulaSignSlotRadialPrincipalWindowBounds.rawContext u t d j))
    (hs:s < IntegralPolynomialWindowTarskiCatalogue.limit S (FormulaSignSlotRadialPrincipalWindowBounds.rawContext u t d j))
    (hv:v < IntegralPolynomialWindowTarskiCatalogue.limit S (FormulaSignSlotRadialPrincipalWindowBounds.rawContext u t d j)):
    ∃i < count u,row (pair u (BinaryNatCode.encode i))=
      pair (BinaryNatCode.encode r) (pair
        (IntegralPolynomialWindowTarskiCatalogue.control (FormulaSignSlotRadialPrincipalWindowBounds.rawContext u t d j)
          v s (decide (m=1))) (BinaryNatCode.encode p)):=by
  obtain ⟨i,hi,HE⟩:=covers u t d j
    (IntegralPolynomialWindowTarskiCatalogue.encode S (FormulaSignSlotRadialPrincipalWindowBounds.rawContext u t d j)
      r m p s v) ht hd hj
    (IntegralPolynomialWindowTarskiCatalogue.encode_lt S _ r m p s v hr hm hp hs hv)
  exact ⟨i,hi,HE.trans (IntegralPolynomialWindowTarskiCatalogue.row_encode S _ r m p s v hr hm hp hs hv)⟩

end LeanCanny.Encoding.FormulaSignSlotRadialPrincipalWindowCatalogue
