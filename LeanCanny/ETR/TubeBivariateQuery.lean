/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeBivariateCoefficients

/-! # Certified row queries for the full bivariate tube source

The packet is `pair context (pair row (pair rank (pair inner outer)))`.
Parameter coordinates and integer directions are read in the original context;
the matrix row, monomial rank and coefficient degrees do not change them.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeBivariate.Query
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Algebra.RationalSubstitution

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.rawCoefficient rawLinear

def packet (c : List Bool) (i k u v : ℕ) : List Bool :=
  pair c (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))

def base : List Bool → List Bool := pairFst
def rowCode (q : List Bool) : List Bool := pairFst (pairSnd q)
def rankCode (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd q))
def innerCode (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd (pairSnd q)))
def outerCode (q : List Bool) : List Bool := pairSnd (pairSnd (pairSnd (pairSnd q)))

theorem base_mem_FP : base ∈ FP := pairFst_mem_FP
theorem rowCode_mem_FP : rowCode ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem rankCode_mem_FP : rankCode ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem innerCode_mem_FP : innerCode ∈ FP := mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairFst_mem_FP
theorem outerCode_mem_FP : outerCode ∈ FP := mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairSnd_mem_FP

@[simp] theorem base_packet (c : List Bool) (i k u v : ℕ) : base (packet c i k u v) = c := by simp only [base, packet, pairFst_pair]
@[simp] theorem rowCode_packet (c : List Bool) (i k u v : ℕ) : rowCode (packet c i k u v) = BinaryNatCode.encode i := by
  simp only [rowCode, packet, pairFst_pair, pairSnd_pair]
@[simp] theorem rankCode_packet (c : List Bool) (i k u v : ℕ) : rankCode (packet c i k u v) = BinaryNatCode.encode k := by
  simp only [rankCode, packet, pairFst_pair, pairSnd_pair]
@[simp] theorem innerCode_packet (c : List Bool) (i k u v : ℕ) : innerCode (packet c i k u v) = BinaryNatCode.encode u := by
  simp only [innerCode, packet, pairFst_pair, pairSnd_pair]
@[simp] theorem outerCode_packet (c : List Bool) (i k u v : ℕ) : outerCode (packet c i k u v) = BinaryNatCode.encode v := by
  simp only [outerCode, packet, pairSnd_pair]

def regularIndex (q : List Bool) : List Bool := BinaryNat.sub (pair (rowCode q) [true])
def rowInput (q : List Bool) : List Bool := pair q (rankCode q)
def directionQuery (q : List Bool) : List Bool := pair (base (pairFst q)) (pairSnd q)

theorem regularIndex_mem_FP : regularIndex ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair rowCode_mem_FP (constFn_mem_FP [true])) BinaryNat.sub_mem_FP
  exact mem_FP_of_eq (g := regularIndex) h (fun _ => by simp only [regularIndex, Function.comp_apply])
theorem rowInput_mem_FP : rowInput ∈ FP := mem_FP_pair id_mem_FP rankCode_mem_FP
theorem directionQuery_mem_FP : directionQuery ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP base_mem_FP) pairSnd_mem_FP

theorem regularIndex_packet (c : List Bool) (i k u v : ℕ) :
    regularIndex (packet c i k u v) = BinaryNatCode.encode (i - 1) := by
  simp only [regularIndex, rowCode_packet, BinaryNat.sub_pair, MacaulayBits.fromBits_encode]
  rfl

noncomputable def regularValue (source active modulus : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) : List Bool → List Bool :=
  TubeCleared.wideValue (source ∘ base) (active ∘ base) regularIndex innerCode (modulus ∘ base)
    (fun q => n (base q)) (fun q => d (base q)) ∘ rowInput

theorem regularEvaluator (source active modulus : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ)
    (C : TubeParameter.CoordinateReaders source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hs : source ∈ FP) (ha : active ∈ FP) (hm : modulus ∈ FP) : SpaceFunction (regularValue source active modulus n d) :=
  (TubeCleared.wideEvaluator (source ∘ base) (active ∘ base) regularIndex innerCode (modulus ∘ base)
    (fun q => n (base q)) (fun q => d (base q)) (C.precomposeUniform base base_mem_FP)
    (mem_FP_comp base_mem_FP hs) (mem_FP_comp base_mem_FP ha) regularIndex_mem_FP innerCode_mem_FP
    (mem_FP_comp base_mem_FP hm)).precompose rowInput rowInput_mem_FP

theorem regular_packet (source active modulus : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (c : List Bool) (i k u v : ℕ) :
    regularValue source active modulus n d (packet c i k u v) =
      IntegerBits.coefficientResidue ((TubeCleared.rawCoefficient (source c) (active c) (BinaryNatCode.encode (i - 1))
        (n c) (d c) (TubeCleared.matrixWidth (source c)) k).coeff u) (Nat.fromBitsLE (modulus c) + 1) := by
  have h := TubeCleared.wide_packet_raw (source ∘ base) (active ∘ base) regularIndex innerCode (modulus ∘ base)
    (fun q => n (base q)) (fun q => d (base q)) (packet c i k u v) k
  simp only [Function.comp_apply, base_packet, regularIndex_packet, innerCode_packet, MacaulayBits.fromBits_encode] at h
  simpa only [regularValue, Function.comp_apply, rowInput, rankCode_packet] using h

noncomputable def linearValue (source modulus : List Bool → List Bool) (ell : List Bool → ℕ → ℤ) : List Bool → List Bool :=
  LinearCoefficientBits.value (TubeParameter.spatialCount ∘ source ∘ base) (TubeCleared.matrixWidth ∘ source ∘ base)
    (TubeLinear.scalar (fun q => ell (base q))) outerCode (modulus ∘ base) ∘ rowInput

theorem linearEvaluator (source modulus read : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
    (hs : source ∈ FP) (hm : modulus ∈ FP) (he : read ∈ FP)
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits) :
    SpaceFunction (linearValue source modulus ell) := by
  have E := TubeLinear.evaluator (source ∘ base) (fun q => ell (base q)) (read ∘ directionQuery) outerCode (modulus ∘ base)
    (mem_FP_comp base_mem_FP hs) (mem_FP_comp directionQuery_mem_FP he) outerCode_mem_FP (mem_FP_comp base_mem_FP hm)
    (by
      intro q i hi
      simp only [Function.comp_apply, directionQuery, pairFst_pair, pairSnd_pair]
      exact hr (base q) i hi)
  exact E.precompose rowInput rowInput_mem_FP

theorem linear_packet (source modulus : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
    (c : List Bool) (i k u v : ℕ) :
    linearValue source modulus ell (packet c i k u v) =
      IntegerBits.coefficientResidue (rawLinear (source c) (ell c) (TubeCleared.matrixWidth (source c)) k v)
        (Nat.fromBitsLE (modulus c) + 1) := by
  have h := TubeBivariate.linear_packet (source ∘ base) (fun q => ell (base q)) outerCode (modulus ∘ base) (packet c i k u v) k
  simp only [Function.comp_apply, base_packet, outerCode_packet, MacaulayBits.fromBits_encode] at h
  simpa only [linearValue, Function.comp_apply, rowInput, rankCode_packet] using h

end LeanCanny.ETR.TubeBivariate.Query
