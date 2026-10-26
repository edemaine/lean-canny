/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullCoefficient
public import LeanCanny.Encoding.BoundedCriticalSampleQuery
public import LeanCanny.Algebra.FixedWidthCriticalSpace

/-! # Native coefficients of full-source critical-sample equations -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalCoefficient
open LeanCanny.ETR LeanCanny.Geometry LeanCanny.Algebra LeanCanny.Computation
open BoundedFullWriter MatrixPower RationalSubstitution.Indexed MvPolynomial Brackets
open LeanCanny.ETR.ComplexCircuit FixedWidthPolynomial
open scoped Classical

noncomputable def value (P : Readers) (record : List Bool → List Bool)
    (row : (c : List Bool) → Fin (P.dim c + 4)) (W : List Bool → ℕ)
    (target modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits (((BoundedCriticalSampleQuery.equations P record c (row c)).coeff
    (exponentVector (P.dim c + 4) (FixedWidthQuery.coordinate W target c)) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus c) + 1))

noncomputable def valueData (source : List Bool) (dim radius : ℕ) (record : List Bool)
    (i W : ℕ) (target modulus : List Bool) : List Bool :=
  let P : Readers := ⟨fun _ => source, fun _ => dim, fun _ => radius⟩
  value P (fun _ => record) (fun _ => ⟨min i (dim + 3), by change min i (dim + 3) < dim + 4; omega⟩) (fun _ => W)
    (fun _ => target) (fun _ => modulus) []

theorem value_data (P : Readers) (record : List Bool → List Bool)
    (row : (c : List Bool) → Fin (P.dim c + 4)) (W : List Bool → ℕ)
    (target modulus : List Bool → List Bool) (c : List Bool) :
    value P record row W target modulus c = valueData (P.source c) (P.dim c) (P.radius c)
      (record c) (row c).val (W c) (target c) (modulus c) := by
  unfold valueData
  simp only [Nat.min_eq_left (show (row c).val ≤ P.dim c + 3 by have := (row c).isLt; omega)]
  rfl

noncomputable def direction (P : Readers) (record : List Bool → List Bool)
    (row : (c : List Bool) → Fin (P.dim c + 4)) (c : List Bool) : ℕ :=
  FixedWidthQuery.coordinate (BoundedFullDirectionQueries.width P) record c ((row c).val - 1)

theorem direction_binary {P : Readers} {record : List Bool → List Bool}
    {row : (c : List Bool) → Fin (P.dim c + 4)} (h : P.PolyTime) (hr : record ∈ FP)
    (hi : UnaryFn (fun c => (row c).val)) : BinaryFn (direction P record row) :=
  BinaryFn.fromBits (take_mem_FP (drop_mem_FP hr
    ((hi.sub (UnaryFn.const 1)).mul (BoundedFullDirectionQueries.width_unary h)))
      (BoundedFullDirectionQueries.width_unary h))

theorem row_eq (P : Readers) (record : List Bool → List Bool) (c : List Bool) (i : Fin (P.dim c + 4)) :
    BoundedCriticalSampleQuery.equations P record c i = if i = 0 then BoundedFullCriticalSamples.polynomial P c
      else pderiv i (BoundedFullCriticalSamples.polynomial P c) -
        C (FixedWidthQuery.coordinate (BoundedFullDirectionQueries.width P) record c (i.val - 1) : ℤ) *
          pderiv 0 (BoundedFullCriticalSamples.polynomial P c) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [BoundedCriticalSampleQuery.equations, CriticalKernel.finiteRows, Fin.cons_zero, ite_true]
  · simp only [BoundedCriticalSampleQuery.equations, CriticalKernel.finiteRows, Fin.cons_succ,
      Fin.succ_ne_zero, ite_false, Fin.val_succ, Nat.add_sub_cancel_right]
    rfl

private theorem exponent_eq (A : ℕ) (W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) :
    exponentVector A (FixedWidthQuery.coordinate W target c) =
      nativeExponent (Equiv.refl (Fin A)) (W c) (Nat.fromBitsLE (target c)) :=
  FixedWidthCriticalBits.exponent_eq_native W target (Equiv.refl (Fin A)) c

theorem evaluator {P : Readers} {record : List Bool → List Bool}
    {row : (c : List Bool) → Fin (P.dim c + 4)} {W : List Bool → ℕ} {target modulus : List Bool → List Bool}
    (h : P.PolyTime) (hr : record ∈ FP) (hi : UnaryFn (fun c => (row c).val)) (hW : UnaryFn W)
    (ht : target ∈ FP) (hm : modulus ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hfit : ∀ c, degree P c < 2 ^ W c) : SpaceFunction (value P record row W target modulus) := by
  let reader := BoundedFullCoefficient.value (P.comp pairFst) (W ∘ pairFst) pairSnd (modulus ∘ pairFst)
  have hreader : SpaceFunction reader := BoundedFullCoefficient.evaluator (h.comp pairFst_mem_FP)
    (hW.comp pairFst_mem_FP) pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hm) (fun p => ha (pairFst p))
  let mword := BinaryNat.succ ∘ modulus
  have hmword : mword ∈ FP := mem_FP_comp hm BinaryNat.succ_mem_FP
  have hv := (direction_binary h hr hi).bits_mem_FP
  have he := FixedWidthCriticalBits.evaluator (fun c => P.dim c + 4) W (degree P) (fun _ => 0)
    (fun c => (row c).val) target mword (fun c => BinaryNatCode.encode (direction P record row c))
    hreader (h.dim.add (UnaryFn.const 4)) hW (degree_binary h) (UnaryFn.const 0) hi ht hmword hv
  apply he.congr
  funext c
  have hpos : 0 < degree P c := by
    have := BoundedRegularSource.powerDegree_gt_one (size P c)
    change 0 < BoundedZeroSource.powerDegree (size P c)
    omega
  have hp := FixedWidthCriticalBits.packet (fun c => P.dim c + 4) W (degree P) (fun _ => 0)
    (fun c => (row c).val) target mword (fun c => BinaryNatCode.encode (direction P record row c))
    (Equiv.refl (Fin (P.dim c + 4))) (BoundedFullCriticalSamples.polynomial P c) 0 (row c)
    (direction P record row c) (Nat.fromBitsLE (modulus c)) reader c rfl rfl rfl hpos
    (BoundedFullCriticalSamples.source_degree P c) (hfit c)
    (by simp only [mword, Function.comp_apply, BinaryNat.succ_eq_bits]; rfl) rfl
    (fun r => by
      simp only [reader, BoundedFullCoefficient.value_data, Readers.comp,
        Function.comp_apply, pairFst_pair, pairSnd_pair]
      change residueBits (((BoundedFullCriticalSamples.polynomial P c).coeff
        (exponentVector (P.dim c + 4) (FixedWidthQuery.coordinate (fun _ => W c) (fun _ => BinaryNatCode.encode r) [])) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) = _
      rw [exponent_eq]
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits])
  rw [hp]
  unfold value
  rw [row_eq]
  rw [exponent_eq]
  rfl

/-- The actual critical-direction search is included in the coefficient
reader's space bound, rather than assumed to be a polynomial-time field. -/
theorem selected_evaluator {P : Readers} {row : (c : List Bool) → Fin (P.dim c + 4)}
    {W : List Bool → ℕ} {target modulus : List Bool → List Bool}
    (h : P.PolyTime) (hi : UnaryFn (fun c => (row c).val)) (hW : UnaryFn W)
    (ht : target ∈ FP) (hm : modulus ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hfit : ∀ c, degree P c < 2 ^ W c) :
    SpaceFunction (value P (BoundedFullDirectionChoice.record P) row W target modulus) := by
  have hc := evaluator (row := fun p => row (pairFst p)) (h.comp pairFst_mem_FP) pairSnd_mem_FP
    (hi.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP ht) (mem_FP_comp pairFst_mem_FP hm)
    (fun p => ha (pairFst p)) (fun p => hfit (pairFst p))
  have he : SpaceFunction _ := ⟨hc.computable.comp (BoundedFullDirectionChoice.evaluator h ha).withInput.computable⟩
  apply he.congr
  funext c
  have hi' : (row (pairFst (pair c (BoundedFullDirectionChoice.record P c)))).val = (row c).val :=
    congrArg (fun p => (row p).val) (pairFst_pair c (BoundedFullDirectionChoice.record P c))
  simp only [value_data, Readers.comp, Function.comp_apply, pairFst_pair, pairSnd_pair, hi']

end LeanCanny.Encoding.BoundedCriticalCoefficient
