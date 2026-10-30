/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineValueGramSpace
public import LeanCanny.Algebra.DiagonalPolynomialParameterSpace

/-! # Native value annihilators from coordinate-grid readers

Original bivariate coordinate readers and the original multivariate test
reader supply the affine rows. Homogenization, reciprocal rows, and the
complete Gram determinant are computed internally. Degree allowances remain
explicit binary metadata; no computation of an actual spatial degree is used.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegerGridValueGramBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower MvPolynomial
open MacaulayFullBoxBits (ctx idx shift uv ctx_FP idx_FP shift_FP uv_FP)
open AffineValueGramBits (base base_FP prepare prepare_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Family where
  arity : List Bool → ℕ
  width : List Bool → ℕ
  degree : List Bool → ℕ → ℕ
  testDegree : List Bool → ℕ
  coordinate : (c : List Bool) → Fin (arity c) → Polynomial (Polynomial ℤ)
  test : (c : List Bool) → MvPolynomial (Fin (arity c)) (Polynomial ℤ)

noncomputable def Family.affine (F : Family) : AffineValueGramBits.Family where
  arity := F.arity
  width := F.width
  degree := F.degree
  testDegree := F.testDegree
  rows c i := (F.coordinate c i).toMvPolynomial i
  test := F.test

noncomputable def Family.coordinateIndex (F : Family) (q : List Bool) : ℕ :=
  (F.affine.row q).val - 1

noncomputable def Family.testCoefficient (F : Family) (q : List Bool) : List Bool :=
  residueBits (((((F.test (base q)).coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _)
    (F.width (base q)) (Nat.fromBitsLE (shift q)))).coeff
      (Nat.fromBitsLE (pairFst (uv q)))) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd (ctx q)) + 1))

lemma Family.original_zero (F : Family) (q : List Bool) (h : (F.affine.row q).val = 0) :
    F.affine.original (base q) (F.affine.row q) = F.test (base q) := by
  have he : F.affine.row q = 0 := Fin.ext h
  rw [he]
  rfl

lemma Family.original_coordinate (F : Family) (q : List Bool) (h : (F.affine.row q).val ≠ 0) :
    DiagonalParameterBits.polynomial (F.arity ∘ base) (fun q => F.coordinate (base q))
      F.coordinateIndex q = F.affine.original (base q) (F.affine.row q) := by
  have hi : F.coordinateIndex q < F.arity (base q) := by
    have hr := (F.affine.row q).isLt
    change (F.affine.row q).val - 1 < F.arity (base q)
    change (F.affine.row q).val < F.arity (base q) + 1 at hr
    omega
  have he : (⟨F.coordinateIndex q, hi⟩ : Fin (F.arity (base q))).succ = F.affine.row q := by
    apply Fin.ext
    change (F.affine.row q).val - 1 + 1 = (F.affine.row q).val
    omega
  exact (dite_eq_left hi).trans (congrArg (F.affine.original (base q)) he)

lemma Family.coordinate_query_eq (F : Family) (q : List Bool) (h : (F.affine.row q).val ≠ 0) :
    HomogenizationParameterBits.source (F.arity ∘ base) (F.width ∘ base)
      (DiagonalParameterBits.polynomial (F.arity ∘ base) (fun q => F.coordinate (base q)) F.coordinateIndex)
      (fun q => pairFst (uv q)) (fun q => pairSnd (ctx q)) (prepare q) =
        F.affine.sourceCoefficient q := by
  rw [prepare, BinaryNat.normalize_eq_bits]
  change HomogenizationParameterBits.source (F.arity ∘ base) (F.width ∘ base)
    (DiagonalParameterBits.polynomial (F.arity ∘ base) (fun q => F.coordinate (base q)) F.coordinateIndex)
    (fun q => pairFst (uv q)) (fun q => pairSnd (ctx q))
    (pair q (BinaryNatCode.encode (Nat.fromBitsLE (shift q)))) = _
  rw [HomogenizationParameterBits.source_packet, F.original_coordinate q h]
  rfl

lemma Family.test_query_eq (F : Family) (q : List Bool) (h : (F.affine.row q).val = 0) :
    F.testCoefficient q = F.affine.sourceCoefficient q := by
  change _ = residueBits (((((F.affine.original (base q) (F.affine.row q)).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (F.width (base q))
      (Nat.fromBitsLE (shift q)))).coeff (Nat.fromBitsLE (pairFst (uv q)))) : ℤ) :
        ZMod (Nat.fromBitsLE (pairSnd (ctx q)) + 1))
  rw [F.original_zero q h]
  rfl

/-- Both original readers are charged. The coordinate reader rejects invalid
indices and the test reader uses the same raw source packet conventions. -/
theorem Family.sourceEvaluator (F : Family) (h : F.affine.homogeneous.layout.Controls)
    (EC : SpaceFunction (SymbolicFixedTableEntryBits.coefficient
      (DiagonalParameterBits.selected F.arity F.coordinate)))
    (ET : SpaceFunction F.testCoefficient) : SpaceFunction F.affine.sourceCoefficient := by
  have hn : UnaryFn (F.arity ∘ base) := (F.affine.arity_unary h).comp base_FP
  have hw : UnaryFn (F.width ∘ base) := h.width.comp base_FP
  have hr : UnaryFn F.coordinateIndex := (F.affine.row_unary h).sub (UnaryFn.const 1)
  have EC' := DiagonalParameterBits.coefficient_comp_evaluator F.arity F.coordinate base base_FP EC
  have ED := DiagonalParameterBits.evaluator hn hw (BinaryFn.ofUnary hr)
    (fun q => F.coordinate (base q)) (fun q => pairFst (uv q)) (fun q => pairSnd (ctx q))
    (mem_FP_comp uv_FP pairFst_mem_FP) (mem_FP_comp ctx_FP pairSnd_mem_FP) EC'
  have hz := (BinaryFn.ofUnary (F.affine.row_unary h)).eq (BinaryFn.const 0)
  have R := SpaceFunction.branch (fun q => decide ((F.affine.row q).val = 0)) hz.flag_mem_FP
    ET (ED.precompose prepare prepare_FP)
  refine R.congr (funext fun q => ?_)
  simp only [decide_eq_true_eq, Function.comp_apply]
  split_ifs with hq
  · exact F.test_query_eq q hq
  · exact F.coordinate_query_eq q hq

theorem Family.coefficientEvaluator (F : Family) (h : F.affine.homogeneous.layout.Controls)
    (B : List Bool → ℕ) (hB : BinaryFn B)
    (hbound : ∀ c i u, ((F.affine.original c i).coeff u).natDegree ≤ B c)
    (EC : SpaceFunction (SymbolicFixedTableEntryBits.coefficient
      (DiagonalParameterBits.selected F.arity F.coordinate)))
    (ET : SpaceFunction F.testCoefficient) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient F.affine.homogeneous.annihilator) :=
  F.affine.coefficientEvaluator h B hB hbound (F.sourceEvaluator h EC ET)

lemma Family.original_inner_bound (F : Family) (B : List Bool → ℕ)
    (hp : ∀ c i k, ((F.coordinate c i).coeff k).natDegree ≤ B c)
    (hq : ∀ c u, ((F.test c).coeff u).natDegree ≤ B c)
    (c : List Bool) (i : Fin (F.arity c + 1)) (u : Fin (F.arity c) →₀ ℕ) :
    ((F.affine.original c i).coeff u).natDegree ≤ B c := by
  refine Fin.cases (hq c u) (fun j => ?_) i
  change (((F.coordinate c j).toMvPolynomial j).coeff u).natDegree ≤ B c
  rw [DiagonalParameterBits.coefficient]
  split_ifs
  · exact hp c j _
  · simp

noncomputable def Family.reader (F : Family) (h : F.affine.homogeneous.layout.Controls)
    (B : List Bool → ℕ) (hB : BinaryFn B)
    (hp : ∀ c i k, ((F.coordinate c i).coeff k).natDegree ≤ B c)
    (hq : ∀ c u, ((F.test c).coeff u).natDegree ≤ B c)
    (EC : SpaceFunction (SymbolicFixedTableEntryBits.coefficient
      (DiagonalParameterBits.selected F.arity F.coordinate)))
    (ET : SpaceFunction F.testCoefficient) :
    CertifiedPolynomial.BivariateReader F.affine.homogeneous.annihilator :=
  F.affine.reader h B hB (F.original_inner_bound B hp hq) (F.sourceEvaluator h EC ET)

end LeanCanny.Algebra.IntegerGridValueGramBits
