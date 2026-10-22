/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteLeafSignResidue
public import LeanCanny.ETR.TubeRegularSpace
public import LeanCanny.Algebra.FixedWidthPolynomialFP

/-! # Native finite-algebraic sign testing for the integer regular tube system

All reciprocal, point, direction, and perturbation coordinates remain variables.
The streamed zero-sign rows are exactly the integer regular tube equations.
The only external algebraic data are the original univariate annihilants for
these coordinates, with native residues and degree/mass upper bounds.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRegularFiniteSigns
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open RationalSubstitution
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeRegularSource.polynomial
  TubeHomogenization.outputEquiv

variable (input active : List Bool → List Bool)

noncomputable abbrev arity (c : List Bool) : ℕ := TubeIndexed.projectionDimension (input c) + 1

theorem arity_unary (hi : input ∈ FP) : UnaryFn (arity input) :=
  (TubeIndexed.projectionDimension_unary.comp hi).add (UnaryFn.const 1)

noncomputable def row (c : List Bool) (j : ℕ) : TubeRegularSource.Index (input c) :=
  TubeRegularBits.decodedIndex input (fun _ => BinaryNatCode.encode j) c

noncomputable def coefficient (c : List Bool) (j r : ℕ) : ℤ :=
  (TubeRegularSource.polynomial (input c) (activeSet (TubeIndexed.arity (input c)) (active c))
    (row input c j)).coeff (FixedWidthPolynomial.nativeExponent
      (TubeHomogenization.outputEquiv (input c)) (TubeIndexed.blockWidth (input c)) r)

noncomputable def source : FiniteLeafSignBits.Source (arity input) where
  count c := pointCount (TubeIndexed.arity (input c)) + 1
  terms c := FixedWidthPolynomial.count (arity input c) (TubeIndexed.blockWidth (input c))
  degree c := TubeIndexed.degreeBound (input c)
  height c := TubeRegularSource.coefficientBudget (input c)
  coefficient := coefficient input active
  exponent c _ r i := FixedWidthPolynomial.entry (TubeIndexed.blockWidth (input c)) r i
  pattern _ _ := 0
  exponent_le c _ r _ i _ := (FixedWidthPolynomial.entry_lt (TubeIndexed.blockWidth (input c)) r i).le.trans (TubeIndexed.clearingWidth_le (input c))
  coefficient_le c j _r _ := TubeRegularSource.coefficient_bound (input c) _ (row input c j) _

theorem polynomial_eq (c : List Bool) (j : ℕ) :
    (source input active).polynomial c j =
      MvPolynomial.rename (TubeHomogenization.outputEquiv (input c))
        (TubeRegularSource.polynomial (input c) (activeSet (TubeIndexed.arity (input c)) (active c))
          (row input c j)) := by
  exact FixedWidthPolynomial.indexed_source_eq_rename _ _ _ _
    (TubeRegularSource.degree_le _ _ _) (TubeIndexed.degreeBound_lt _)

theorem eval_polynomial {R : Type*} [CommSemiring R] (c : List Bool) (j : ℕ)
    (phi : ℤ →+* R) (z : Fin (arity input c) → R) :
    ((source input active).polynomial c j).eval₂ phi z =
      (TubeRegularSource.polynomial (input c) (activeSet (TubeIndexed.arity (input c)) (active c))
        (row input c j)).eval₂ phi (fun i => z (TubeHomogenization.outputEquiv (input c) i)) := by
  rw [polynomial_eq]
  exact MvPolynomial.eval₂_rename _ _ _ _

/-- Move the binary modulus beside the original context, retaining the rank. -/
def coefficientQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (pairSnd q)) (pairSnd (pairFst q))

theorem coefficientQuery_FP : coefficientQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def value : List Bool → List Bool :=
  TubeRegularBits.value (input ∘ pairFst ∘ pairFst) (active ∘ pairFst ∘ pairFst)
    (pairSnd ∘ pairFst) pairSnd ∘ coefficientQuery

theorem valueEvaluator (hi : input ∈ FP) (ha : active ∈ FP) : SpaceFunction (value input active) :=
  (TubeRegularBits.evaluator _ _ _ _
    ((hi.comp pairFst_mem_FP).comp pairFst_mem_FP)
    ((ha.comp pairFst_mem_FP).comp pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP).precompose
      coefficientQuery coefficientQuery_FP

noncomputable def nativeCoefficient (rowBits : List Bool → List Bool) (c : List Bool) (r : ℕ) : ℤ :=
  (TubeRegularSource.polynomial (input c) (activeSet (TubeIndexed.arity (input c)) (active c))
    (TubeRegularBits.decodedIndex input rowBits c)).coeff
      (FixedWidthPolynomial.nativeExponent (TubeHomogenization.outputEquiv (input c))
        (TubeIndexed.blockWidth (input c)) r)

theorem nativeCoefficient_comp (rowBits f : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    nativeCoefficient (input ∘ f) (active ∘ f) (rowBits ∘ f) c r =
      nativeCoefficient input active rowBits (f c) r := rfl

theorem nativeCoefficient_index (q : List Bool) (r : ℕ) :
    nativeCoefficient (input ∘ pairFst) (active ∘ pairFst) pairSnd q r =
      coefficient input active (pairFst q) (Nat.fromBitsLE (pairSnd q)) r := by
  have hr : TubeRegularBits.decodedIndex (input ∘ pairFst) pairSnd q =
      TubeRegularBits.decodedIndex input
        (fun _ => BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q))) (pairFst q) := by
    simp only [TubeRegularBits.decodedIndex, BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode]
    split_ifs
    · rfl
    · apply congrArg some
      unfold TubeProjection.decodedRow TubeRegularBits.oldRow TubeProjectionRow.index
      simp only [BinaryNat.sub_pair, MacaulayBits.fromBits_encode]
      rfl
  exact congrArg (fun j : TubeRegularSource.Index (input (pairFst q)) =>
    (TubeRegularSource.polynomial (input (pairFst q))
      (activeSet (TubeIndexed.arity (input (pairFst q))) (active (pairFst q))) j).coeff
        (FixedWidthPolynomial.nativeExponent (TubeHomogenization.outputEquiv (input (pairFst q)))
          (TubeIndexed.blockWidth (input (pairFst q))) r)) hr

theorem value_packet (q : List Bool) (r m : ℕ) (hm : 0 < m) :
    value input active (pair (pair q (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      MatrixPower.residueBits ((coefficient input active (pairFst q) (Nat.fromBitsLE (pairSnd q)) r : ℤ) : ZMod m) := by
  simp only [value, Function.comp_apply, coefficientQuery, pairFst_pair, pairSnd_pair]
  rw [TubeRegularBits.value_packet]
  change MatrixPower.residueBits
    ((nativeCoefficient ((input ∘ pairFst) ∘ pairFst) ((active ∘ pairFst) ∘ pairFst)
      (pairSnd ∘ pairFst) (pair q (BinaryNatCode.encode (m - 1))) r : ℤ) :
        ZMod (Nat.fromBitsLE (pairSnd (pair q (BinaryNatCode.encode (m - 1)))) + 1)) = _
  rw [nativeCoefficient_comp]
  simp only [pairFst_pair]
  rw [nativeCoefficient_index]
  exact congrArg (fun n : ℕ => MatrixPower.residueBits
    ((coefficient input active (pairFst q) (Nat.fromBitsLE (pairSnd q)) r : ℤ) : ZMod n))
      (by simp only [pairSnd_pair, MacaulayBits.fromBits_encode, Nat.sub_add_cancel hm])

noncomputable def access (hi : input ∈ FP) (ha : active ∈ FP) : (source input active).Access where
  coefficient := value input active
  exponent := FixedWidthPolynomial.exponentRead ((arity input) ∘ pairFst)
    ((TubeIndexed.blockWidth ∘ input) ∘ pairFst)
  pattern _ := []
  count_unary := (TubeProjectionQuery.pointCount_unary (TubeIndexed.arity_unary.comp hi)).add (UnaryFn.const 1)
  terms_binary := BinaryFn.of_bits (mem_FP_of_eq
    (FixedWidthPolynomial.countCode_mem_FP (arity_unary input hi) (TubeIndexed.blockWidth_unary.comp hi))
    (FixedWidthPolynomial.countCode_code _ _))
  degree_binary := BinaryFn.of_bits (bits_mem_FP (TubeIndexed.degreeBound_unary.comp hi))
  height_binary := BinaryFn.of_bits (bits_mem_FP (TubeRegularSource.coefficientBudget_unary.comp hi))
  coefficientEvaluator := valueEvaluator input active hi ha
  exponent_FP := FixedWidthPolynomial.exponentRead_mem_FP
    ((arity_unary input hi).comp pairFst_mem_FP)
    ((TubeIndexed.blockWidth_unary.comp hi).comp pairFst_mem_FP)
  pattern_FP := constFn_mem_FP []
  coefficient_eq q r _ m hm := value_packet input active q r m hm
  exponent_eq q r _ i hi := by
    rw [FixedWidthPolynomial.exponentRead_packet _ _ q r i hi]
    exact Nat.fromBitsLE_bits _
  pattern_eq _ _ := rfl

noncomputable def rowCode (c : List Bool) : TubeRegularSource.Index (input c) → ℕ
  | none => 0
  | some j => TubeProjectionRow.code (TubeIndexed.arity (input c)) j + 1

theorem rowCode_lt (c : List Bool) (j : TubeRegularSource.Index (input c)) :
    rowCode input c j < (source input active).count c := by
  cases j with
  | none => simp only [rowCode, source]; omega
  | some j => exact Nat.succ_lt_succ (TubeProjectionRow.code_lt _ j)

theorem row_rowCode (c : List Bool) (j : TubeRegularSource.Index (input c)) :
    row input c (rowCode input c j) = j := by
  cases j with
  | none =>
    unfold row
    apply TubeRegularBits.decodedIndex_reciprocal
    simp only [rowCode, BinaryNat.normalize_eq_bits]
    rfl
  | some j =>
    unfold row
    apply TubeRegularBits.decodedIndex_of_code
    rfl

theorem all_rows_iff {K : Type*} [Field K] (c : List Bool) (phi : ℤ →+* K)
    (z : Fin (arity input c) → K) :
    (∀ j : Fin ((source input active).count c),
      ((source input active).polynomial c j.val).eval₂ phi z = 0) ↔
    ∀ j, (TubeRegularSource.polynomial (input c)
      (activeSet (TubeIndexed.arity (input c)) (active c)) j).eval₂ phi
        (fun i => z (TubeHomogenization.outputEquiv (input c) i)) = 0 := by
  simp_rw [eval_polynomial]
  constructor
  · intro h j
    have hj := h ⟨rowCode input c j, rowCode_lt input active c j⟩
    rw [row_rowCode] at hj
    exact hj
  · intro h j
    exact h _

theorem all_rows_iff_regular {K : Type*} [Field K] (c : List Bool) (phi : ℤ →+* K)
    (x : TubeSource.IntegerProjectionVariable (input c) → K) (u : K) :
    (∀ j : Fin ((source input active).count c),
      ((source input active).polynomial c j.val).eval₂ phi
        (fun i => ((TubeHomogenization.outputEquiv (input c)).symm i).elim u x) = 0) ↔
      TubeRegularSource.RegularRoot (input c)
        (activeSet (TubeIndexed.arity (input c)) (active c)) phi x ∧
      u = ((MvPolynomial.pderiv (TubeRegularSource.base (CompactSource.term (input c)).arity)
        (TubeSource.integerProjection (input c)
          (activeSet (TubeIndexed.arity (input c)) (active c)) none)).eval₂ phi x)⁻¹ := by
  refine (all_rows_iff input active c phi
    (fun i : Fin (arity input c) => ((TubeHomogenization.outputEquiv (input c)).symm i).elim u x)).trans ?_
  simp only [Equiv.symm_apply_apply]
  exact TubeRegularSource.root_iff _ _ _ _ _

/-- Feasibility of the regular tube equations on the supplied algebraic coordinates. -/
noncomputable def language (B : SeparableBits.Family) : Language :=
  FiniteLeafSignBits.finiteSignLanguage B (arity input) (source input active)

theorem language_iff (B : SeparableBits.Family) (c : List Bool) :
    c ∈ language input active B ↔
      ∃ z : TubeRegularSource.Variable (input c) → ℝ,
        (∀ i, (B.polynomial (pair c (BinaryNatCode.encode
          (TubeHomogenization.outputEquiv (input c) i).val))).eval₂ (Int.castRingHom ℝ) (z i) = 0) ∧
        ∀ j, (TubeRegularSource.polynomial (input c)
          (activeSet (TubeIndexed.arity (input c)) (active c)) j).eval₂ (Int.castRingHom ℝ) z = 0 := by
  constructor
  · rintro ⟨z, hz, hs⟩
    refine ⟨fun i => z (TubeHomogenization.outputEquiv (input c) i), fun i => hz _, ?_⟩
    apply (all_rows_iff input active c (Int.castRingHom ℝ) z).mp
    intro j
    exact sign_eq_zero_iff.mp (hs j)
  · rintro ⟨z, hz, hs⟩
    let w : Fin (arity input c) → ℝ := fun i => z ((TubeHomogenization.outputEquiv (input c)).symm i)
    refine ⟨w, ?_, ?_⟩
    · intro i
      simpa only [w, Equiv.apply_symm_apply] using hz ((TubeHomogenization.outputEquiv (input c)).symm i)
    · have hn : ∀ j, (TubeRegularSource.polynomial (input c)
          (activeSet (TubeIndexed.arity (input c)) (active c)) j).eval₂ (Int.castRingHom ℝ)
            (fun i => w (TubeHomogenization.outputEquiv (input c) i)) = 0 := by
        simpa only [w, Equiv.symm_apply_apply] using hs
      have hr := (all_rows_iff input active c (Int.castRingHom ℝ) w).mpr hn
      intro j
      exact sign_eq_zero_iff.mpr (hr j)

theorem language_mem_PSPACE (B : SeparableBits.Family) (D b : List Bool → ℕ)
    (hne : ∀ c i, i < arity input c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
    (hd : ∀ c i, i < arity input c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (hbnd : ∀ c i, i < arity input c → coefficientMass (B.polynomial (pair c (BinaryNatCode.encode i))) ≤ 2 ^ b c)
    (hi : input ∈ FP) (ha : active ∈ FP) (hD : BinaryFn D) (hb : BinaryFn b)
    (E : SpaceFunction (PrimitivePairBits.coefficient B.polynomial)) :
    language input active B ∈ PSPACE :=
  FiniteLeafSignBits.finiteSignLanguage_mem_PSPACE_from_residues B (arity input) D b hne hd hbnd
    (source input active) (access input active hi ha) (arity_unary input hi) hD hb E

end LeanCanny.ETR.TubeRegularFiniteSigns
