/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineValueGramSpace
public import LeanCanny.Algebra.PolynomialParameterVariableSpace
public import LeanCanny.Algebra.HomogenizationAdditive

/-! # Native coordinate annihilators over polynomial parameter rings

A coordinate test is read internally. The original affine row reader alone
supplies all remaining coefficients, retaining their parameter coefficients.
The resulting value determinant is exactly the complete reciprocal coordinate
Gram annihilator, with the requested width and mixed degree allowances.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineParameterCoordinateBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower MvPolynomial
open MacaulayFullBoxBits (ctx idx shift uv ctx_FP idx_FP shift_FP uv_FP)
open AffineValueGramBits (base base_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Family where
  arity : List Bool → ℕ
  width : List Bool → ℕ
  degree : List Bool → ℕ → ℕ
  rows : (c : List Bool) → Fin (arity c) → MvPolynomial (Fin (arity c)) (Polynomial ℤ)
  coordinate : (c : List Bool) → Fin (arity c)

noncomputable def Family.affine (F : Family) : AffineValueGramBits.Family where
  arity := F.arity
  width := F.width
  degree := F.degree
  testDegree _ := 1
  rows := F.rows
  test c := X (F.coordinate c)

lemma Family.positive (F : Family) (c : List Bool) : 0 < F.arity c :=
  Nat.zero_lt_of_lt (F.coordinate c).isLt

noncomputable def Family.rowAt (F : Family) (c : List Bool) (i r u : ℕ) (modulus : List Bool) : List Bool :=
  residueBits (((((F.rows c ⟨min i (F.arity c - 1), by have := F.positive c; omega⟩).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (F.width c) r)).coeff u) : ℤ) :
      ZMod (Nat.fromBitsLE modulus + 1))

noncomputable def Family.rowCoefficient (F : Family) (q : List Bool) : List Bool :=
  F.rowAt (base q) (Nat.fromBitsLE (idx q)) (Nat.fromBitsLE (shift q))
    (Nat.fromBitsLE (pairFst (uv q))) (pairSnd (ctx q))

noncomputable def Family.tailQuery (F : Family) (q : List Bool) : List Bool :=
  pair (ctx q) (pair (BinaryNatCode.encode ((F.affine.row q).val - 1)) (pair (shift q) (uv q)))

lemma Family.tailQuery_FP (F : Family) (h : F.affine.homogeneous.layout.Controls) : F.tailQuery ∈ FP :=
  mem_FP_pair ctx_FP (mem_FP_pair (bits_mem_FP ((F.affine.row_unary h).sub (UnaryFn.const 1)))
    (mem_FP_pair shift_FP uv_FP))

lemma Family.original_tail (F : Family) (c : List Bool) (j : Fin (F.arity c + 1)) (hj : j.val ≠ 0) :
    F.affine.original c j = F.rows c ⟨min (j.val - 1) (F.arity c - 1), by have := F.positive c; omega⟩ := by
  have he : (⟨min (j.val - 1) (F.arity c - 1), by have := F.positive c; omega⟩ : Fin (F.arity c)).succ = j := by
    apply Fin.ext
    change min (j.val - 1) (F.arity c - 1) + 1 = j.val
    have := j.isLt
    omega
  exact (congrArg (F.affine.original c) he).symm

lemma Family.tail_query_eq (F : Family) (q : List Bool) (hq : (F.affine.row q).val ≠ 0) :
    F.rowCoefficient (F.tailQuery q) = F.affine.sourceCoefficient q := by
  simp only [Family.rowCoefficient, Family.tailQuery, base, ctx, idx, shift, uv,
    pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode]
  change F.rowAt (base q) ((F.affine.row q).val - 1) (Nat.fromBitsLE (shift q))
    (Nat.fromBitsLE (pairFst (uv q))) (pairSnd (ctx q)) = F.affine.sourceCoefficient q
  unfold Family.rowAt AffineValueGramBits.Family.sourceCoefficient AffineValueGramBits.Family.sourceAt
  change _ = residueBits (((((F.affine.original (base q) (F.affine.row q)).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (F.width (base q)) (Nat.fromBitsLE (shift q)))).coeff
      (Nat.fromBitsLE (pairFst (uv q)))) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd (ctx q)) + 1))
  rw [F.original_tail (base q) (F.affine.row q) hq]
  rfl

noncomputable def Family.testCoefficient (F : Family) : List Bool → List Bool :=
  PolynomialParameterVariableBits.value (F.arity ∘ base) (F.width ∘ base)
    (fun q => F.coordinate (base q)) shift (fun q => pairFst (uv q)) (fun q => pairSnd (ctx q))

theorem Family.testEvaluator (F : Family) (h : F.affine.homogeneous.layout.Controls)
    (hc : UnaryFn (fun c => (F.coordinate c).val)) : SpaceFunction F.testCoefficient :=
  PolynomialParameterVariableBits.evaluator ((F.affine.arity_unary h).comp base_FP) (h.width.comp base_FP)
    (fun q => F.coordinate (base q)) (hc.comp base_FP) _ _ _ shift_FP
    (mem_FP_comp uv_FP pairFst_mem_FP) (mem_FP_comp ctx_FP pairSnd_mem_FP)

lemma Family.test_query_eq (F : Family) (q : List Bool) (hq : (F.affine.row q).val = 0) :
    F.testCoefficient q = F.affine.sourceCoefficient q := by
  have he : F.affine.row q = 0 := Fin.ext hq
  change _ = residueBits (((((F.affine.original (base q) (F.affine.row q)).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (F.width (base q)) (Nat.fromBitsLE (shift q)))).coeff
      (Nat.fromBitsLE (pairFst (uv q)))) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd (ctx q)) + 1))
  rw [he]
  rfl

theorem Family.sourceEvaluator (F : Family) (h : F.affine.homogeneous.layout.Controls)
    (hc : UnaryFn (fun c => (F.coordinate c).val)) (ER : SpaceFunction F.rowCoefficient) :
    SpaceFunction F.affine.sourceCoefficient := by
  have hz := (BinaryFn.ofUnary (F.affine.row_unary h)).eq (BinaryFn.const 0)
  have E := SpaceFunction.branch (fun q => decide ((F.affine.row q).val = 0)) hz.flag_mem_FP
    (F.testEvaluator h hc) (ER.precompose F.tailQuery (F.tailQuery_FP h))
  refine E.congr (funext fun q => ?_)
  simp only [decide_eq_true_eq, Function.comp_apply]
  split_ifs with hq
  · exact F.test_query_eq q hq
  · exact F.tail_query_eq q hq

lemma Family.original_inner_bound (F : Family) (B : List Bool → ℕ)
    (hB : ∀ c i u, ((F.rows c i).coeff u).natDegree ≤ B c)
    (c : List Bool) (j : Fin (F.arity c + 1)) (u : Fin (F.arity c) →₀ ℕ) :
    ((F.affine.original c j).coeff u).natDegree ≤ B c := by
  refine Fin.cases ?_ (fun i => hB c i u) j
  change ((X (F.coordinate c) : MvPolynomial _ (Polynomial ℤ)).coeff u).natDegree ≤ B c
  simp only [coeff_X]
  split_ifs <;> simp

noncomputable def Family.valueReader (F : Family) (h : F.affine.homogeneous.layout.Controls)
    (hc : UnaryFn (fun c => (F.coordinate c).val)) (B : List Bool → ℕ) (hB : BinaryFn B)
    (hbound : ∀ c i u, ((F.rows c i).coeff u).natDegree ≤ B c)
    (ER : SpaceFunction F.rowCoefficient) : CertifiedPolynomial.BivariateReader F.affine.homogeneous.annihilator :=
  F.affine.reader h B hB (F.original_inner_bound B hbound) (F.sourceEvaluator h hc ER)

lemma Family.test_eq (F : Family) (c : List Bool) :
    F.affine.homogeneous.test c = X (F.coordinate c).succ := by
  change rename AffineCoordinateSystem.layout (WeightedHomogenization.homogenize (fun _ => 1) 1
    (X (F.coordinate c) : MvPolynomial _ (Polynomial ℤ))) = _
  have hx := WeightedHomogenization.homogenize_X_pow (R := Polynomial ℤ) (F.coordinate c) 1
  rw [show WeightedHomogenization.homogenize (fun _ => 1) 1
      (X (F.coordinate c) : MvPolynomial _ (Polynomial ℤ)) = X (some (F.coordinate c)) from
        by simpa only [pow_one] using hx, rename_X]
  apply congrArg X
  apply Fin.ext
  exact HomogenizationLayout.variableEquiv_some (Equiv.refl _) (F.coordinate c)

lemma coordinate_value_eq {n : ℕ}
    (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial ℤ)) (d : Fin n → ℕ) (W : ℕ)
    (i : Fin (n + 1)) :
    ProjectiveValueGram.annihilator H (X i) d 1 W = AffineRingGramEliminant.annihilator H d W i := by
  have hs : ProjectiveValueGram.system H (X i) 1 = AffineRingGramEliminant.system H i := by
    funext j
    refine Fin.cases ?_ (fun _ => rfl) j
    simp [ProjectiveValueGram.system, AffineRingGramEliminant.system]
  unfold ProjectiveValueGram.annihilator ProjectiveValueGram.polynomial ProjectiveBoxGramEliminant.polynomial
  rw [hs]
  rfl

noncomputable def Family.annihilator (F : Family) (c : List Bool) : Polynomial (Polynomial ℤ) :=
  AffineRingGramEliminant.annihilator (AffineRingCoordinates.homogeneousRows (F.rows c)
    (fun i => F.degree c i.val)) (fun i => F.degree c i.val) (F.width c) (F.coordinate c).succ

lemma Family.annihilator_eq (F : Family) (c : List Bool) : F.affine.homogeneous.annihilator c = F.annihilator c := by
  change ProjectiveValueGram.annihilator _ (F.affine.homogeneous.test c) _ 1 _ = _
  rw [F.test_eq, coordinate_value_eq]
  rfl

/-- A complete reciprocal coordinate reader from the original affine rows.
The coordinate test is native and is not an additional reader premise. -/
noncomputable def Family.reader (F : Family) (h : F.affine.homogeneous.layout.Controls)
    (hc : UnaryFn (fun c => (F.coordinate c).val)) (B : List Bool → ℕ) (hB : BinaryFn B)
    (hbound : ∀ c i u, ((F.rows c i).coeff u).natDegree ≤ B c)
    (ER : SpaceFunction F.rowCoefficient) : CertifiedPolynomial.BivariateReader F.annihilator := by
  have he : F.affine.homogeneous.annihilator = F.annihilator := funext F.annihilator_eq
  exact he ▸ F.valueReader h hc B hB hbound ER

end LeanCanny.Algebra.AffineParameterCoordinateBits
