/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleSliceIndexed
public import LeanCanny.Encoding.BoundedAlgebraicSliceUnit

/-! # Native factors for a zero-aware root product

The context contains the original source and a base-root query. Each factor
is replaced by one exactly when its polynomial vanishes identically at that
base root. The original coefficient reader and a native specialized zero
test supply the chosen coefficients. Uniform bounds hold on all raw contexts.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleSliceRootProductSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice (unitAccess unit ofTest unitTest)
open scoped Classical

noncomputable def factor (P : Readers) (Q : BivariateQueryProductBits.Family) (v : List Bool) (i : ℕ) : (ℤ[X])[X] :=
  if BoundedCriticalSampleSliceIndexed.value P Q (pairSnd v) i = 0 then 1 else Q.polynomial (pairFst v) i

noncomputable def family (P : Readers) (Q : BivariateQueryProductBits.Family) : BivariateQueryProductBits.Family where
  polynomial := factor P Q
  exponent _ _ := 1
  count v := Q.count (pairFst v)
  degree v := Q.degree (pairFst v)
  parameterDegree v := Q.parameterDegree (pairFst v)
  mass v := Q.mass (pairFst v)
  polynomial_degree v i := by
    unfold factor
    split_ifs
    · simp only [Polynomial.natDegree_one, Nat.zero_le]
    · exact Q.polynomial_degree (pairFst v) i
  coefficient_degree v i j := by
    unfold factor
    split_ifs
    · simp only [Polynomial.coeff_one]
      split_ifs <;> simp only [Polynomial.natDegree_one, Polynomial.natDegree_zero, Nat.zero_le]
    · exact Q.coefficient_degree (pairFst v) i j
  coefficient_mass v i j := by
    unfold factor
    split_ifs
    · simp only [Polynomial.coeff_one]
      split_ifs
      · rw [← Polynomial.C_1, coefficientMass_C, Int.natAbs_one]
        exact Nat.one_le_two_pow
      · simp only [coefficientMass_zero, Nat.zero_le]
    · exact Q.coefficient_mass (pairFst v) i j

theorem count_eq (P : Readers) (Q : BivariateQueryProductBits.Family) (v : List Bool) :
    (family P Q).count v = Q.count (pairFst v) := rfl

theorem polynomial_eq (P : Readers) (Q : BivariateQueryProductBits.Family) (v : List Bool) (i : ℕ) :
    (family P Q).polynomial v i = factor P Q v i := rfl

theorem exponent_eq (P : Readers) (Q : BivariateQueryProductBits.Family) (v : List Bool) (i : ℕ) :
    (family P Q).exponent v i = 1 := rfl

def source (z : List Bool) : List Bool := pairFst (pairFst z)
theorem source_FP : source ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

def selector (w : List Bool) : List Bool := pair (pairSnd (pairFst w)) (pairSnd w)
theorem selector_FP : selector ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

def zeroQuery (z : List Bool) : List Bool := selector (source z)
theorem zeroQuery_FP : zeroQuery ∈ FP := mem_FP_comp source_FP selector_FP

def originalSource (w : List Bool) : List Bool := pair (pairFst (pairFst w)) (pairSnd w)
theorem originalSource_FP : originalSource ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

def readerQuery (z : List Bool) : List Bool :=
  pair (pair (originalSource (source z)) (pairSnd (pairFst z))) (pairSnd z)
theorem readerQuery_FP : readerQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp source_FP originalSource_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

noncomputable def coefficient (P : Readers) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (z : List Bool) : List Bool :=
  if zeroQuery z ∈ BoundedCriticalSampleSliceIndexed.nonzeroLanguage P Q then A.reader.coefficient (readerQuery z)
    else ((unitAccess).reader).coefficient z

theorem coefficient_evaluator {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (coefficient P A) := by
  have D := (BoundedCriticalSampleSliceIndexed.nonzero_decider h A ha).precompose zeroQuery zeroQuery_FP
  have O := A.reader.evaluator.precompose readerQuery readerQuery_FP
  have E := SpaceFunction.branchDecider D O ((unitAccess).reader).evaluator
  exact E

noncomputable def reader {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    CertifiedPolynomial.BivariateReader (fun w => factor P Q (pairFst w) (Nat.fromBitsLE (pairSnd w))) where
  coefficient := coefficient P A
  evaluator := coefficient_evaluator h A ha
  coefficient_eq q u v := by
    have hflag : zeroQuery (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) ∈
        BoundedCriticalSampleSliceIndexed.nonzeroLanguage P Q ↔
      BoundedCriticalSampleSliceIndexed.value P Q (pairSnd (pairFst (pairFst q))) (Nat.fromBitsLE (pairSnd (pairFst q))) ≠ 0 := by
      simp only [zeroQuery, source, selector, pairFst_pair, pairSnd_pair, BoundedCriticalSampleSliceIndexed.nonzero_packet]
    rw [coefficient, hflag]
    by_cases hv : BoundedCriticalSampleSliceIndexed.value P Q (pairSnd (pairFst (pairFst q)))
        (Nat.fromBitsLE (pairSnd (pairFst q))) ≠ 0
    · rw [ite_eq_left hv]
      simp only [readerQuery, source, pairFst_pair, pairSnd_pair]
      rw [A.reader.coefficient_eq]
      exact congrArg₂ (fun (z : ℤ) (n : ℕ) => MatrixPower.residueBits (z : ZMod n))
        (by simp only [originalSource, pairFst_pair, pairSnd_pair, factor, hv, ite_false])
        (by rw [pairSnd_pair])
    · rw [ite_eq_right hv]
      have H := ((unitAccess).reader).coefficient_eq q u v
      have hz := not_ne_iff.mp hv
      simpa only [factor, hz, ite_true, unit, ofTest, unitTest, Polynomial.map_one] using H

noncomputable def access {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    BivariateQueryProductBits.Access (family P Q) where
  reader := reader h A ha
  exponent _ := BinaryNatCode.encode 1
  exponent_eq _ _ := rfl
  exponent_FP := constFn_mem_FP _
  count_binary := A.count_binary.comp pairFst_mem_FP
  degree_binary := A.degree_binary.comp pairFst_mem_FP
  parameterDegree_binary := A.parameterDegree_binary.comp pairFst_mem_FP
  mass_binary := A.mass_binary.comp pairFst_mem_FP

end LeanCanny.Encoding.BoundedCriticalSampleSliceRootProductSource
