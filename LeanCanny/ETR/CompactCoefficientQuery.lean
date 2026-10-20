/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CollectedDegreeSpace
public import LeanCanny.Algebra.CubeFactorResidue

/-! # Compactification coefficient queries and actual-degree preparation

Factor queries are `pair context (pair monomialIndex variableIndex)`.
Requested exponents use blocks of width `4*N²+1`, enough for compactified
degrees. The variable index is capped only for FP block access; factor calls
within the source dimension recover the exact requested exponent.
-/

@[expose] public section

namespace LeanCanny.ETR.CompactCoefficient
open Complexity
open LeanCanny.Encoding LeanCanny.Computation

attribute [local irreducible] BinaryNat.mul BinaryNat.sub
  Algebra.CubeFactorResidue.computed CollectedDegree.degree

def width (source : List Bool → List Bool) (c : List Bool) : ℕ := 4 * CollectedCoefficient.dimension source c ^ 2 + 1
def exponent (source target : List Bool → List Bool) (c : List Bool) (i : ℕ) : ℕ :=
  Nat.fromBitsLE (((target c).drop (i * width source c)).take (width source c))
def monomialIndex (q : List Bool) : List Bool := pairFst (pairSnd q)
def coordinate (q : List Bool) : List Bool := pairSnd (pairSnd q)

theorem width_unary {source : List Bool → List Bool} (hs : source ∈ FP) : UnaryFn (width source) :=
  ((UnaryFn.const 4).mul ((CollectedCoefficient.dimension_unary hs).pow_const 2)).add (UnaryFn.const 1)
theorem monomialIndex_mem_FP : monomialIndex ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem coordinate_mem_FP : coordinate ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

def targetBlock (source target : List Bool → List Bool) (q : List Bool) : List Bool :=
  ((target (pairFst q)).drop (min (Nat.fromBitsLE (coordinate q)) (CollectedCoefficient.dimension source (pairFst q)) *
    width source (pairFst q))).take (width source (pairFst q))

theorem targetBlock_mem_FP {source target : List Bool → List Bool} (hs : source ∈ FP) (ht : target ∈ FP) :
    targetBlock source target ∈ FP := by
  have hi := UnaryFn.fromBitsLE_min coordinate_mem_FP (CollectedCoefficient.dimension_unary hs).lift
  have hw := (width_unary hs).lift
  have h := take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP ht) (hi.mul hw)) hw
  exact mem_FP_of_eq h (fun _ => rfl)

def sourceExponent (source : List Bool → List Bool) : List Bool → List Bool :=
  MonomialReader.exponentRead (source ∘ pairFst) monomialIndex coordinate

theorem sourceExponent_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : sourceExponent source ∈ FP :=
  MonomialReader.exponentRead_mem_FP (mem_FP_comp pairFst_mem_FP hs) monomialIndex_mem_FP coordinate_mem_FP

def prepareFactor (source target modulus : List Bool → List Bool) (z : List Bool) : List Bool :=
  let q := pairFst z
  let e := sourceExponent source q
  pair e (pair (BinaryNat.sub (pair (BinaryNat.mul (pair [false, true] (pairSnd z))) e))
    (pair (targetBlock source target q) (modulus (pairFst q))))

theorem prepareFactor_mem_FP {source target modulus : List Bool → List Bool}
    (hs : source ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) : prepareFactor source target modulus ∈ FP := by
  have he := mem_FP_comp pairFst_mem_FP (sourceExponent_mem_FP hs)
  have hd := mem_FP_comp (mem_FP_pair (constFn_mem_FP [false, true]) pairSnd_mem_FP) BinaryNat.mul_mem_FP
  have hsub := mem_FP_comp (mem_FP_pair hd he) BinaryNat.sub_mem_FP
  have hk := mem_FP_comp pairFst_mem_FP (targetBlock_mem_FP hs ht)
  have hm' := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hm
  have h := mem_FP_pair he (mem_FP_pair hsub (mem_FP_pair hk hm'))
  exact mem_FP_of_eq h (fun _ => rfl)

noncomputable def factorComputed (source target modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  Algebra.CubeFactorResidue.computed (prepareFactor source target modulus
    (pair q (BinaryNatCode.encode (CollectedDegree.degree (source ∘ pairFst) coordinate q))))

noncomputable def factorEvaluator (source target modulus : List Bool → List Bool)
    (hs : source ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) : SpaceFunction (factorComputed source target modulus) := by
  let D := CollectedDegree.evaluator (source ∘ pairFst) coordinate (mem_FP_comp pairFst_mem_FP hs) coordinate_mem_FP
  let E := (D.withInput.postcompose (prepareFactor source target modulus) (prepareFactor_mem_FP hs ht hm)).chain
    Algebra.CubeFactorResidue.evaluator
  exact E.congr (funext fun _ => rfl)

theorem sourceExponent_packet (source : List Bool → List Bool) (c : List Bool) (r i : ℕ) :
    sourceExponent source (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i))) =
      BinaryNatCode.encode ((TermView.term (source c)).monomialExponent r i) := by
  simp only [sourceExponent, MonomialReader.exponentRead_correct, Function.comp_apply,
    monomialIndex, coordinate, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem targetBlock_packet (source target : List Bool → List Bool) (c : List Bool) (r i : ℕ)
    (hi : i < CollectedCoefficient.dimension source c) :
    targetBlock source target (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i))) =
      ((target c).drop (i * width source c)).take (width source c) := by
  simp only [targetBlock, coordinate, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, min_eq_left hi.le]

theorem degree_packet (source : List Bool → List Bool) (c : List Bool) (r i : ℕ)
    (hi : i < CollectedCoefficient.dimension source c) :
    CollectedDegree.degree (source ∘ pairFst) coordinate (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i))) =
      (Term.finitePolynomial (CollectedCoefficient.dimension source c) (TermView.term (source c))).degreeOf ⟨i, hi⟩ := by
  classical
  have hd : CollectedCoefficient.dimension (source ∘ pairFst)
      (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i))) = CollectedCoefficient.dimension source c := by
    simp only [CollectedCoefficient.dimension, Function.comp_apply, pairFst_pair]
  unfold CollectedDegree.degree
  rw [hd]
  simp only [coordinate, pairFst_pair, pairSnd_pair, Function.comp_apply,
    show Nat.fromBitsLE (BinaryNatCode.encode i) = i from Nat.fromBitsLE_bits i, dite_eq_left hi]

theorem factorComputed_packet (source target modulus : List Bool → List Bool) (c : List Bool) (r i : ℕ)
    (hi : i < CollectedCoefficient.dimension source c) :
    factorComputed source target modulus (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i))) =
      Algebra.MatrixPower.residueBits
        (((Algebra.CubeFactor.polynomial (R := ℤ) ((TermView.term (source c)).monomialExponent r i)
          (2 * (Term.finitePolynomial (CollectedCoefficient.dimension source c) (TermView.term (source c))).degreeOf ⟨i, hi⟩ -
            (TermView.term (source c)).monomialExponent r i)).coeff (exponent source target c i) : ℤ) :
              ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  let q := pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i))
  let e := (TermView.term (source c)).monomialExponent r i
  let D := (Term.finitePolynomial (CollectedCoefficient.dimension source c) (TermView.term (source c))).degreeOf ⟨i, hi⟩
  let k := ((target c).drop (i * width source c)).take (width source c)
  have he : sourceExponent source q = BinaryNatCode.encode e := sourceExponent_packet source c r i
  have ht : targetBlock source target q = k := targetBlock_packet source target c r i hi
  have hd : CollectedDegree.degree (source ∘ pairFst) coordinate q = D := degree_packet source c r i hi
  have hp : prepareFactor source target modulus (pair q (BinaryNatCode.encode D)) =
      pair (BinaryNatCode.encode e) (pair (BinaryNatCode.encode (2 * D - e)) (pair k (modulus c))) := by
    simp only [prepareFactor, pairFst_pair, pairSnd_pair]
    rw [he, ht]
    simp only [q, pairFst_pair,
      show [false, true] = BinaryNatCode.encode 2 from rfl, BinaryNat.mul_pair, BinaryNat.sub_pair,
      Nat.fromBitsLE_bits, BinaryNatCode.encode]
  rw [factorComputed, hd, hp]
  have h := Algebra.CubeFactorResidue.computed_correct
    (pair (BinaryNatCode.encode e) (pair (BinaryNatCode.encode (2 * D - e)) (pair k (modulus c))))
  rw [Algebra.CubeFactorResidue.mValue, Algebra.CubeFactorResidue.mWord,
    pairSnd_pair, pairSnd_pair, pairSnd_pair] at h
  have hcode (n : ℕ) : Nat.fromBitsLE (BinaryNatCode.encode n) = n := Nat.fromBitsLE_bits n
  simp only [Algebra.CubeFactorResidue.eWord, Algebra.CubeFactorResidue.sWord, Algebra.CubeFactorResidue.kWord,
    pairFst_pair, pairSnd_pair, hcode] at h
  exact h

end LeanCanny.ETR.CompactCoefficient
