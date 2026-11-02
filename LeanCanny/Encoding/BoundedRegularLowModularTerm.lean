/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.BoundedRegularModularTerm
public import LeanCanny.Algebra.IntegralMixedHistory
/-! # Original-only modular LOW syntax for the actual bounded regular source

The large scalar powers are reduced before writing syntax. Removing the
known Fermat leading part leaves the literal integer LOW polynomial.
-/
@[expose] public section
namespace LeanCanny.Encoding.BoundedRegularLowModularTerm
open LeanCanny.ETR LeanCanny.Geometry LeanCanny.Algebra LeanCanny.Computation MvPolynomial
open BoundedFullWriter
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def low (P : Readers) (c : List Bool) : MvPolynomial (Fin (P.dim c+4)) ℤ := BoundedSourceWriter.lower (controls P) c
noncomputable def leading (P : Readers) (c : List Bool) := BoundedSourceWriter.leading (controls P) c

noncomputable def source (P : Readers) (c : List Bool) : IntegralMixedHistory.SpatialSource (P.dim c+3) where
  low := low P c
  leading := leading P c
  degree := degree P c
  degree_two := Nat.succ_le_of_lt (BoundedRegularSource.powerDegree_gt_one (size P c))
  low_degree := IntegerRegularSource.lower_degree _ _ _
    (BoundedRegularSource.lower_degree _ _ _ _ (original_degree P c))
  leading_ne_zero := IntegerRegularSource.leading_ne_zero _ _ _ one_ne_zero

theorem source_polynomial (P : Readers) (c : List Bool) :
    FermatCriticalHomogenization.polynomial (source P c).low (source P c).leading (source P c).degree=
      BoundedRegularSource.polynomial (original P c) (size P c) (size P c) (P.radius c) := rfl

noncomputable def term (P : Readers) (modulus : List Bool → List Bool) (c : List Bool) : Term :=
  .add (BoundedRegularModularTerm.term P modulus c)
    (.mul (.const (-(BoundedRegularModularTerm.power (regularizationExponent P) modulus c : ℤ)))
      (TermPowerSum.term (P.dim c+4) (degree P c)))

theorem encode_mem_FP {P : Readers} {modulus : List Bool → List Bool}
    (h : P.PolyTime) (hm : modulus∈FP) : (fun c => (term P modulus c).toData.toBits)∈FP := by
  have HE := Term.negNat_toBits_mem_FP
    (BoundedRegularModularTerm.power_binary (regularizationExponent_binary h) hm)
  have HS := TermPowerSum.encode_mem_FP (h.dim.add (UnaryFn.const 4)) (BoundedRegularModularTerm.degree_unary h)
  simpa only [term,Term.add_toBits,Term.mul_toBits] using
    Codec.taggedTwo_mem_FP 2 (BoundedRegularModularTerm.encode_mem_FP h hm) (Codec.taggedTwo_mem_FP 3 HE HS)

theorem arity (P : Readers) (modulus : List Bool → List Bool) (c : List Bool)
    (ha : (TermView.term (P.source c)).arity≤P.dim c) : (term P modulus c).arity≤P.dim c+4 := by
  have HN : 0<degree P c := Nat.zero_lt_of_lt (BoundedRegularSource.powerDegree_gt_one (size P c))
  unfold term BoundedRegularModularTerm.term
  rw [Term.arity,BoundedRegularTerm.arity _ _ _ _ _ _ _ ha HN]
  simp only [Term.arity,TermPowerSum.arity _ _ HN]
  omega

theorem leading_cast (P : Readers) (modulus : List Bool → List Bool) (c : List Bool) :
    (leading P c : ZMod (Nat.fromBitsLE (modulus c)+1))=
      (BoundedRegularModularTerm.power (regularizationExponent P) modulus c : ZMod (Nat.fromBitsLE (modulus c)+1)) := by
  rw [BoundedRegularModularTerm.power_cast]
  simp only [leading,BoundedSourceWriter.leading,IntegerRegularSource.leading,IntegerRegularSource.scale,
    Int.cast_pow,Int.cast_ofNat,mul_one]
  rfl

theorem polynomial_map (P : Readers) (modulus : List Bool → List Bool) (c : List Bool)
    (ha : (TermView.term (P.source c)).arity≤P.dim c) :
    ((term P modulus c).finitePolynomial (P.dim c+4)).map (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus c)+1)))=
      (low P c).map (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus c)+1))) := by
  have HP := BoundedRegularModularTerm.polynomial_map P modulus c ha
  have HL := leading_cast P modulus c
  have HC (i : Fin (P.dim c+4)) : i.castLE (Nat.le_refl (P.dim c+4))=i := Fin.ext rfl
  simp only [term,Term.finitePolynomial,map_add,map_mul,map_C]
  rw [HP,TermPowerSum.finitePolynomial _ _ _ le_rfl]
  simp only [HC,map_sum,map_pow,map_X,Int.coe_castRingHom,Int.cast_neg,Int.cast_natCast]
  rw [←source_polynomial]
  rw [FermatCriticalHomogenization.polynomial,map_add,map_mul,map_C,map_sum]
  simp only [map_pow,map_X,source,Int.coe_castRingHom]
  rw [HL]
  simp only [map_neg]
  ring
end LeanCanny.Encoding.BoundedRegularLowModularTerm
