/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitutionSpace

/-! # Uniform coordinate readers and bounds for rational substitution

Correctness is required only below the supplied arity, for every coefficient
and positive modulus. Reader programs may use arbitrary certified space.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution.IntegerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower

structure CoordinateReaders (arity : List Bool → ℕ)
    (n d : List Bool → ℕ → Polynomial ℤ) where
  numerator : List Bool → List Bool
  denominator : List Bool → List Bool
  numeratorEvaluator : SpaceFunction numerator
  denominatorEvaluator : SpaceFunction denominator
  numerator_eq : ∀ c i, i < arity c → ∀ k m, 0 < m →
    numerator (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((n c i).coeff k : ℤ) : ZMod m)
  denominator_eq : ∀ c i, i < arity c → ∀ k m, 0 < m →
    denominator (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((d c i).coeff k : ℤ) : ZMod m)

/-- Change the semantic interface while retaining the reader programs definitionally. -/
def CoordinateReaders.congr {arity arity' : List Bool → ℕ}
    {n d n' d' : List Bool → ℕ → Polynomial ℤ} (C : CoordinateReaders arity n d)
    (hA : arity = arity') (hn : n = n') (hd : d = d') : CoordinateReaders arity' n' d' where
  numerator := C.numerator
  denominator := C.denominator
  numeratorEvaluator := C.numeratorEvaluator
  denominatorEvaluator := C.denominatorEvaluator
  numerator_eq c i hi k m hm := by
    simpa only [hn] using C.numerator_eq c i (by simpa only [hA] using hi) k m hm
  denominator_eq c i hi k m hm := by
    simpa only [hd] using C.denominator_eq c i (by simpa only [hA] using hi) k m hm

/-- Reindex the context while retaining coordinate, degree, and modulus words. -/
def coordinateQuery (f : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (f (pairFst (pairFst q))) (pairSnd (pairFst q))) (pairSnd q)

theorem coordinateQuery_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) : coordinateQuery f ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hf)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

def CoordinateReaders.precompose {arity : List Bool → ℕ}
    {n d : List Bool → ℕ → Polynomial ℤ} (C : CoordinateReaders arity n d)
    (f : List Bool → List Bool) (hf : f ∈ FP) :
    CoordinateReaders (arity ∘ f) (fun c => n (f c)) (fun c => d (f c)) where
  numerator := C.numerator ∘ coordinateQuery f
  denominator := C.denominator ∘ coordinateQuery f
  numeratorEvaluator := C.numeratorEvaluator.precompose _ (coordinateQuery_mem_FP hf)
  denominatorEvaluator := C.denominatorEvaluator.precompose _ (coordinateQuery_mem_FP hf)
  numerator_eq c i hi k m hm := by
    simpa only [Function.comp_apply, coordinateQuery, pairFst_pair, pairSnd_pair] using
      C.numerator_eq (f c) i hi k m hm
  denominator_eq c i hi k m hm := by
    simpa only [Function.comp_apply, coordinateQuery, pairFst_pair, pairSnd_pair] using
      C.denominator_eq (f c) i hi k m hm

structure CoordinateBounds (arity : List Bool → ℕ)
    (n d : List Bool → ℕ → Polynomial ℤ) where
  degree : List Bool → List Bool
  bits : List Bool → List Bool
  degreeFP : degree ∈ FP
  bitsFP : bits ∈ FP
  numerator_degree : ∀ c i, i < arity c → (n c i).natDegree ≤ Nat.fromBitsLE (degree c)
  denominator_degree : ∀ c i, i < arity c → (d c i).natDegree ≤ Nat.fromBitsLE (degree c)
  numerator_coeff : ∀ c i, i < arity c → ∀ k, ((n c i).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE (bits c)
  denominator_coeff : ∀ c i, i < arity c → ∀ k, ((d c i).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE (bits c)

/-- Semantic transport keeps both allowance writers definitionally unchanged. -/
def CoordinateBounds.congr {arity arity' : List Bool → ℕ}
    {n d n' d' : List Bool → ℕ → Polynomial ℤ} (B : CoordinateBounds arity n d)
    (hA : arity = arity') (hn : n = n') (hd : d = d') : CoordinateBounds arity' n' d' where
  degree := B.degree
  bits := B.bits
  degreeFP := B.degreeFP
  bitsFP := B.bitsFP
  numerator_degree c i hi := by
    simpa only [hn] using B.numerator_degree c i (by simpa only [hA] using hi)
  denominator_degree c i hi := by
    simpa only [hd] using B.denominator_degree c i (by simpa only [hA] using hi)
  numerator_coeff c i hi k := by
    simpa only [hn] using B.numerator_coeff c i (by simpa only [hA] using hi) k
  denominator_coeff c i hi k := by
    simpa only [hd] using B.denominator_coeff c i (by simpa only [hA] using hi) k

def CoordinateBounds.precompose {arity : List Bool → ℕ}
    {n d : List Bool → ℕ → Polynomial ℤ} (B : CoordinateBounds arity n d)
    (f : List Bool → List Bool) (hf : f ∈ FP) :
    CoordinateBounds (arity ∘ f) (fun c => n (f c)) (fun c => d (f c)) where
  degree := B.degree ∘ f
  bits := B.bits ∘ f
  degreeFP := mem_FP_comp hf B.degreeFP
  bitsFP := mem_FP_comp hf B.bitsFP
  numerator_degree c := B.numerator_degree (f c)
  denominator_degree c := B.denominator_degree (f c)
  numerator_coeff c := B.numerator_coeff (f c)
  denominator_coeff c := B.denominator_coeff (f c)

end LeanCanny.Algebra.RationalSubstitution.IntegerBits
