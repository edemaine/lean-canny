/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CRTWeightSpace

/-!
# Local CRT numerator preparation from a certified residue routine

Compute the selected modulus and inverse cofactor, retain the original query,
and call the supplied integer-residue routine. FP modular multiplication returns
the locally reduced numerator together with the modulus-minus-one code consumed
by the streamed sign evaluator. All three space computations are composed with
native space certificates.
-/

@[expose] public section

namespace LeanCanny.Algebra.ChineseRemainder.PreparationBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation

def weightQuery (bound : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (BinaryNat.normalize (bound (pairFst q))) (BinaryNat.normalize (pairSnd q))
def original (w : List Bool) : List Bool := pairFst (pairFst w)
def modulus (w : List Bool) : List Bool := pairFst (pairSnd w)
def inverse (w : List Bool) : List Bool := pairSnd (pairSnd w)
def residueQuery (w : List Bool) : List Bool := pair (original w) (BinaryNat.pred (modulus w))
def finish (z : List Bool) : List Bool :=
  pair (BinaryNat.mulMod (pair (modulus (pairFst z)) (pair (pairSnd z) (inverse (pairFst z)))))
    (BinaryNat.pred (modulus (pairFst z)))
def value (bound rho : List Bool → List Bool) (q : List Bool) : List Bool :=
  let w := pair q (WeightBits.value (weightQuery bound q))
  finish (pair w (rho (residueQuery w)))

theorem weightQuery_mem_FP {bound : List Bool → List Bool} (hb : bound ∈ FP) : weightQuery bound ∈ FP := by
  have hN := mem_FP_comp (mem_FP_comp pairFst_mem_FP hb) BinaryNat.normalize_mem_FP
  have hi := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP
  have h := mem_FP_pair hN hi
  refine mem_FP_of_eq (g := weightQuery bound) h ?_
  intro q
  simp only [Function.comp_apply, weightQuery]

theorem original_mem_FP : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem modulus_mem_FP : modulus ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem inverse_mem_FP : inverse ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

theorem residueQuery_mem_FP : residueQuery ∈ FP := by
  have hm := mem_FP_comp modulus_mem_FP BinaryNat.pred_mem_FP
  have h := mem_FP_pair original_mem_FP hm
  refine mem_FP_of_eq (g := residueQuery) h ?_
  intro w
  simp only [Function.comp_apply, residueQuery]

theorem finish_mem_FP : finish ∈ FP := by
  have hm := mem_FP_comp pairFst_mem_FP modulus_mem_FP
  have hi := mem_FP_comp pairFst_mem_FP inverse_mem_FP
  have hnum := mem_FP_comp (mem_FP_pair hm (mem_FP_pair pairSnd_mem_FP hi)) BinaryNat.mulMod_mem_FP
  have hb := mem_FP_comp hm BinaryNat.pred_mem_FP
  have h := mem_FP_pair hnum hb
  refine mem_FP_of_eq (g := finish) h ?_
  intro z
  simp only [Function.comp_apply, finish]

theorem evaluator {rho : List Bool → List Bool} (R : SpaceFunction rho)
    (bound : List Bool → List Bool) (hb : bound ∈ FP) : SpaceFunction (value bound rho) := by
  let W := (WeightBits.evaluator.precompose (weightQuery bound) (weightQuery_mem_FP hb)).withInput
  let P := ((R.precompose residueQuery residueQuery_mem_FP).withInput).postcompose finish finish_mem_FP
  let E := W.chain P
  refine E.congr (funext fun q => ?_)
  simp only [Function.comp_apply, value]

theorem value_pair (bound rho : List Bool → List Bool) (c : List Bool) (z : ℤ)
    (hres : ∀ m : ℕ, 0 < m → rho (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((z : ZMod m).val))
    (i : Fin (Nat.fromBitsLE (bound c) + 1)) :
    value bound rho (pair c (BinaryNatCode.encode i.val)) =
      pair (BinaryNatCode.encode ((indexedSystem (Nat.fromBitsLE (bound c))).numerator
        (fun j => (z : ZMod ((indexedSystem (Nat.fromBitsLE (bound c))).modulus j)).val) i))
        (BinaryNatCode.encode ((indexedSystem (Nat.fromBitsLE (bound c))).modulus i - 1)) := by
  let F := indexedSystem (Nat.fromBitsLE (bound c))
  have hq : weightQuery bound (pair c (BinaryNatCode.encode i.val)) =
      pair (BinaryNatCode.encode (Nat.fromBitsLE (bound c))) (BinaryNatCode.encode i.val) := by
    simp only [weightQuery, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [value, hq, WeightBits.value_pair]
  have hrq : residueQuery (pair (pair c (BinaryNatCode.encode i.val))
      (pair (BinaryNatCode.encode (F.modulus i)) (BinaryNatCode.encode (F.inverse i)))) =
      pair c (BinaryNatCode.encode (F.modulus i - 1)) := by
    simp only [residueQuery, original, modulus, pairFst_pair, pairSnd_pair,
      BinaryNat.pred_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [hrq, hres (F.modulus i) (F.positive i)]
  simp only [finish, modulus, inverse, pairFst_pair, pairSnd_pair, BinaryNat.mulMod_pair,
    BinaryNat.pred_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, System.numerator]

end LeanCanny.Algebra.ChineseRemainder.PreparationBits
