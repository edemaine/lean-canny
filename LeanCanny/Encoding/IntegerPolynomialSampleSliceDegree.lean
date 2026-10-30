/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegerPolynomialSampleSliceSource
public import LeanCanny.Encoding.BoundedAlgebraicSliceReindex

/-! # Native degree records for slices at complete algebraic samples

Zero-aware scans distinguish zero slices from nonzero constants. Attaching
computed degree records preserves the same algebraic sample and its validity.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegerPolynomialSampleSlice
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegerPolynomialRootQueriesBits (Source)
open BoundedAlgebraicSlice (Family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def degree (S : Source) (F : Family) (u : List Bool) : ℕ := (specialized S F u).natDegree
noncomputable def offset (S : Source) (F : Family) (u : List Bool) : ℕ :=
  if specialized S F u = 0 then 0 else degree S F u + 1

theorem offsetEvaluator {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    {F : Family} (B : F.Access) : SpaceFunction (fun u => BinaryNatCode.encode (offset S F u)) := by
  have hD : BinaryFn (fun u => F.degree (context u)) := B.degree_binary.comp context_FP
  exact PolynomialDegreeBits.offsetEvaluator (coefficientSignEvaluator A B)
    (fun u => BinaryNatCode.encode (F.degree (context u))) hD.bits_mem_FP (specialized S F)
    (by intro u; rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact specialized_degree S F u)
    (coefficient_zero S F)

noncomputable def leading (S : Source) (F : Family) (u : List Bool) : List Bool :=
  coefficientSign S F (pair u (BinaryNatCode.encode (degree S F u)))

theorem leadingEvaluator {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    {F : Family} (B : F.Access) : SpaceFunction (leading S F) :=
  (degreeEvaluator A B).withInput.chain (coefficientSignEvaluator A B)

theorem leading_packet (S : Source) (F : Family) (u : List Bool) :
    leading S F u = InfinitesimalSign.encode (SignType.sign (specialized S F u).leadingCoeff) := by
  rw [leading, coefficientSign_packet, degree, Polynomial.coeff_natDegree]

theorem degree_valid (S : Source) (F : Family) (u : List Bool) (hu : 0 < degree S F u) : u ∈ valid S := by
  by_contra hv
  have hz : degree S F u = 0 := by rw [degree, specialized, ite_eq_right hv, natDegree_zero]
  omega

noncomputable def nonzeroLanguage (S : Source) (F : Family) : Language := {u | specialized S F u ≠ 0}

theorem nonzeroDecider {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    {F : Family} (B : F.Access) : SpaceDecider (nonzeroLanguage S F) := by
  apply (offsetEvaluator A B).decider (fun z => decide (z ≠ []))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [])).not.flag_mem_FP
  intro u
  simp only [nonzeroLanguage, Set.mem_ofPred_eq, decide_eq_true_eq, BinaryNatCode.encode,
    ne_eq, BinaryNat.bits_eq_nil_iff, offset]
  split_ifs <;> simp_all

def attach (u r : List Bool) : List Bool := pair (pairFst u) (pair (pairSnd u) r)
def dropRecord (v : List Bool) : List Bool := pair (pairFst v) (pairFst (pairSnd v))
theorem dropRecord_FP : dropRecord ∈ FP := by polytime [dropRecord]

theorem attach_valid (S : Source) (u r : List Bool) : attach u r ∈ valid S ↔ u ∈ valid S := by
  simp only [valid, attach, Set.mem_ofPred_eq, pairFst_pair]

theorem point_attach (S : Source) (u r : List Bool) : point S (attach u r) = point S u := by
  let valueAt (p : List Bool) : ℝ := if hp : SquareSampleCompleteVertices.Valid
      (IntegerPolynomialSampleInput.input S) (pairFst p) (pairSnd p) then
    (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input S)
      (pairFst p) (pairSnd p) hp).val (0 : Fin 1) else 0
  change valueAt (pairFst (attach u r)) = valueAt (pairFst u)
  exact congrArg valueAt (pairFst_pair (pairFst u) (pair (pairSnd u) r))

theorem specialized_attach (S : Source) (F : Family) (u r : List Bool) :
    specialized S (F.comp dropRecord) (attach u r) = specialized S F u := by
  simp only [specialized, attach_valid, Family.slice_comp, point_attach]
  congr 1
  simp only [dropRecord, context, attach, pairFst_pair, pairSnd_pair]

end LeanCanny.Encoding.IntegerPolynomialSampleSlice
