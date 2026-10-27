/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberHashChoice
public import LeanCanny.Encoding.BoundedProjectionRationalCount

/-! # Native rational cuts and individual roots of the weighted Gram pencil

One linear sign query counts roots below, at, or above a signed rational
threshold. The source determinant retains all its native coefficient calls.
The zero-sign query gives a total native test for an individual root value.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberPencilCuts
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicFiberPencilEntries
open scoped Classical

theorem cut_sign_zero_iff (q : List Bool) (x : ℝ) :
    SignType.sign (((RationalCutBits.polynomial q).map (algebraMap ℤ ℝ)).eval x) = 0 ↔
      x = RationalCutBits.threshold q := by
  rw [sign_eq_zero_iff, RationalCutBits.eval_real]
  have hd : (RationalCutBits.divisor q : ℝ) ≠ 0 := by
    have h : 0 < RationalCutBits.divisor q := Nat.succ_pos _
    exact_mod_cast h.ne'
  rw [RationalCutBits.threshold, eq_div_iff hd]
  constructor <;> intro h <;> linarith

noncomputable def family (P : Readers) (F : BoundedAlgebraicSlice.Family) (σ : SignType) : SignPatternBits.Family where
  root q := (matrix P F (pairFst q)).det
  polynomial q _ := RationalCutBits.polynomial q
  pattern _ _ := σ
  count _ := BinaryNatCode.encode 1
  rootDegree q := BinaryNatCode.encode (BoundedAlgebraicFiberPencilRootCount.degree (pairFst q))
  degree _ := BinaryNatCode.encode 1
  rootMass q := BinaryNatCode.encode (BoundedAlgebraicFiberPencilRootCount.massExponent F (pairFst q))
  mass q := BinaryNatCode.encode (RationalCutBits.massExponent q)
  rootDegree_pos q := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, BoundedAlgebraicFiberPencilRootCount.degree]; omega
  root_degree q := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (BoundedAlgebraicFiberPencilBounds.determinant_degree P F (pairFst q)).trans (Nat.le_succ _)
  root_mass q := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact BoundedAlgebraicFiberPencilRootCount.mass_bound P F (pairFst q)
  polynomial_degree q _ _ := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact RationalCutBits.polynomial_degree q
  polynomial_mass q _ _ := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact RationalCutBits.polynomial_mass q

theorem controls (P : Readers) {F : BoundedAlgebraicSlice.Family} (A : F.Access) (σ : SignType) : SignPatternBits.ControlsPolyTime (family P F σ) := by
  have hD := BinaryFn.bits_mem_FP (BoundedAlgebraicFiberPencilRootCount.degree_binary.comp pairFst_mem_FP)
  have hM := BinaryFn.bits_mem_FP ((BoundedAlgebraicFiberPencilRootCount.massExponent_binary A).comp pairFst_mem_FP)
  exact ⟨constFn_mem_FP _, UnaryFn.const 1, hD, constFn_mem_FP _, hM, bits_mem_FP RationalCutBits.massExponent_unary⟩

noncomputable def coefficient (P : Readers) (F : BoundedAlgebraicSlice.Family) : List Bool → List Bool :=
  BoundedAlgebraicFiberPencilCoefficient.value P F ∘ SignPatternBits.sourceQuery

noncomputable def access (P : Readers) (F : BoundedAlgebraicSlice.Family) (σ : SignType) : SignPatternBits.Access (family P F σ) where
  rootCoefficient := coefficient P F
  polynomialCoefficient := RationalCutBits.coefficient ∘ BoundedProjectionRationalCount.cutQuery
  pattern _ := InfinitesimalSign.encode σ
  root_eq q k m hm := by
    simp only [coefficient, Function.comp_apply, SignPatternBits.sourceQuery, pairFst_pair, pairSnd_pair]
    generalize hw : BinaryNatCode.encode (m - 1) = w
    have he : Nat.fromBitsLE w + 1 = m := by
      rw [← hw]
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      omega
    subst m
    exact BoundedAlgebraicFiberPencilCoefficient.value_packet P F (pairFst q) k w
  polynomial_eq q _ _ k m hm := by
    simp only [Function.comp_apply, BoundedProjectionRationalCount.cutQuery, pairFst_pair, pairSnd_pair]
    exact RationalCutBits.coefficient_packet q k m hm
  pattern_eq _ _ := rfl

noncomputable def rootSet (P : Readers) (F : BoundedAlgebraicSlice.Family) (b : List Bool) : Finset ℝ :=
  ((matrix P F b).det.map (Int.castRingHom ℝ)).roots.toFinset
noncomputable def count (P : Readers) (F : BoundedAlgebraicSlice.Family) (σ : SignType) (q : List Bool) : ℕ :=
  ((rootSet P F (pairFst q)).filter (fun x =>
    SignType.sign (((RationalCutBits.polynomial q).map (algebraMap ℤ ℝ)).eval x) = σ)).card

theorem family_count (P : Readers) (F : BoundedAlgebraicSlice.Family) (σ : SignType) (q : List Bool) : SignPatternBits.rootCount (family P F σ) q = count P F σ q := by
  simp only [SignPatternBits.rootCount, family, RootSignQueries.signCount, count, rootSet,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, forall_const, algebraMap_int_eq]

attribute [local irreducible] coefficient BoundedAlgebraicFiberPencilCoefficient.value RationalCutBits.coefficient

theorem evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (σ : SignType) :
    SpaceFunction (fun q => BinaryNatCode.encode (count P F σ q)) := by
  have H0 := (BoundedAlgebraicFiberPencilCoefficient.evaluator h A ha).precompose _ SignPatternBits.sourceQuery_mem_FP
  have H : SpaceFunction (coefficient P F) := H0.congr (funext fun _ => by simp only [coefficient, Function.comp_apply])
  have Q := SpaceFunction.ofFP _ (mem_FP_comp BoundedProjectionRationalCount.cutQuery_FP RationalCutBits.coefficient_FP)
  have E := SignPatternBits.rootCountEvaluator (access P F σ) (controls P A σ)
    (constFn_mem_FP (InfinitesimalSign.encode σ)) H Q
  exact E.congr (funext fun q => congrArg BinaryNatCode.encode (family_count P F σ q))

theorem count_below (P : Readers) (F : BoundedAlgebraicSlice.Family) (q : List Bool) : count P F .neg q =
    ((rootSet P F (pairFst q)).filter (fun x => x < RationalCutBits.threshold q)).card := by
  simp only [count, RationalCutBits.sign_neg_iff]

theorem count_zero_pos_iff (P : Readers) (F : BoundedAlgebraicSlice.Family) (q : List Bool) :
    0 < count P F 0 q ↔ RationalCutBits.threshold q ∈ rootSet P F (pairFst q) := by
  rw [count, Finset.card_pos, Finset.filter_nonempty_iff]
  simp only [cut_sign_zero_iff]
  constructor
  · rintro ⟨x, hx, he⟩
    rwa [he] at hx
  · intro h
    exact ⟨_, h, rfl⟩

noncomputable def language (P : Readers) (F : BoundedAlgebraicSlice.Family) : Language := {q | RationalCutBits.threshold q ∈ rootSet P F (pairFst q)}
theorem decider {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (language P F) := by
  have E := evaluator h A ha 0
  have hc := ((BinaryFn.const 0).lt (BinaryFn.fromBits id_mem_FP)).flag_mem_FP
  apply E.decider (fun z => decide (0 < Nat.fromBitsLE z)) hc
  intro q
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq, language, Set.mem_ofPred_eq]
  exact (count_zero_pos_iff P F q).symm

end LeanCanny.Encoding.BoundedAlgebraicFiberPencilCuts
