/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiCatalogue
/-! # Actual window rows have bounded length at every ordinal

The ordinal itself is not written into the row. All three numeric controls
are reduced modulo the actual input-degree box, and role and moment are
bounded. Thus excess ordinals do not enlarge the source context.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralPolynomialWindowTarskiCatalogue
open LeanCanny.Algebra LeanCanny.Computation
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem row_length (S:Source) (c:List Bool) (D i:ℕ) (hD:S.degree c≤D):
    (row S (pair c (BinaryNatCode.encode i))).length≤4*c.length+9*(D+2).size+22:=by
  have HL:0<limit S c:=by unfold limit;omega
  have bits_bound (k:ℕ):(BinaryNatCode.encode (k%limit S c)).length≤(D+2).size:=by
    rw [BinaryNatCode.length_encode]
    apply Nat.size_le_size
    exact (Nat.mod_lt k HL).le.trans (Nat.add_le_add_right hD 2)
  have HJ:(BinaryNatCode.encode (orderIndex S c i)).length≤(D+2).size:=bits_bound _
  have HS:(BinaryNatCode.encode (seedIndex S c i)).length≤(D+2).size:=bits_bound _
  have HD:(BinaryNatCode.encode (degreeIndex S c i)).length≤(D+2).size:=bits_bound _
  have HR:(BinaryNatCode.encode (i%3)).length≤2:=by
    rw [BinaryNatCode.length_encode]
    exact (Nat.size_le_size (Nat.le_of_lt_succ (Nat.mod_lt i (by decide)))).trans (by decide)
  have HM:(if square i then [true] else ([]:List Bool)).length≤1:=by
    split_ifs <;> decide
  have HE:Nat.fromBitsLE (BinaryNatCode.encode i)=i:=by simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits]
  simp only [row,pairFst_pair,pairSnd_pair,HE,control,pair_length]
  omega

end LeanCanny.Encoding.IntegralPolynomialWindowTarskiCatalogue
