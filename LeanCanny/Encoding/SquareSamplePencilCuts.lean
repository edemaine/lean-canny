/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleHashChoice
public import LeanCanny.Algebra.RationalCutSpace

/-! # Native rational cuts and individual roots of the weighted Gram pencil

One linear sign query counts roots below, at, or above a signed rational
threshold. The source determinant retains all its native coefficient calls.
The zero-sign query gives a total native test for an individual root value.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSamplePencilCuts
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open SquareSamplePencilEntries
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SquareSampleRecords.length SquareSampleThom.labelWidth
  SquareSampleCoordinates.parameterDegree SquareSampleCoordinates.baseHeight
  SquareSampleQueries.roots SquareSampleRegularCount.count

theorem cut_sign_zero_iff (q : List Bool) (x : ℝ) :
    SignType.sign (((RationalCutBits.polynomial q).map (algebraMap ℤ ℝ)).eval x) = 0 ↔
      x = RationalCutBits.threshold q := by
  rw [sign_eq_zero_iff, RationalCutBits.eval_real]
  have hd : (RationalCutBits.divisor q : ℝ) ≠ 0 := by
    have h : 0 < RationalCutBits.divisor q := Nat.succ_pos _
    exact_mod_cast h.ne'
  rw [RationalCutBits.threshold, eq_div_iff hd]
  constructor <;> intro h <;> linarith

noncomputable def family (P : Inputs) (σ : SignType) : SignPatternBits.Family where
  root q := (matrix P (pairFst q)).det
  polynomial q _ := RationalCutBits.polynomial q
  pattern _ _ := σ
  count _ := BinaryNatCode.encode 1
  rootDegree q := BinaryNatCode.encode (SquareSamplePencilRootCount.degree (pairFst q))
  degree _ := BinaryNatCode.encode 1
  rootMass q := BinaryNatCode.encode (SquareSamplePencilRootCount.massExponent P (pairFst q))
  mass q := BinaryNatCode.encode (RationalCutBits.massExponent q)
  rootDegree_pos q := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, SquareSamplePencilRootCount.degree]; omega
  root_degree q := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (SquareSamplePencilBounds.determinant_degree P (pairFst q)).trans (Nat.le_succ _)
  root_mass q := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact SquareSamplePencilRootCount.mass_bound P (pairFst q)
  polynomial_degree q _ _ := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact RationalCutBits.polynomial_degree q
  polynomial_mass q _ _ := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact RationalCutBits.polynomial_mass q

theorem controls {P : Inputs} (h : P.Access) (σ : SignType) : SignPatternBits.ControlsPolyTime (family P σ) := by
  have hD := BinaryFn.bits_mem_FP (SquareSamplePencilRootCount.degree_binary.comp pairFst_mem_FP)
  have hM := BinaryFn.bits_mem_FP ((SquareSamplePencilRootCount.massExponent_binary h).comp pairFst_mem_FP)
  exact ⟨constFn_mem_FP _, UnaryFn.const 1, hD, constFn_mem_FP _, hM, bits_mem_FP RationalCutBits.massExponent_unary⟩

def cutQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (pairSnd (pairSnd (pairFst q)))) (pairSnd q)
theorem cutQuery_FP : cutQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)) pairSnd_mem_FP

noncomputable def coefficient (P : Inputs) : List Bool → List Bool :=
  SquareSamplePencilCoefficient.value P ∘ SignPatternBits.sourceQuery

noncomputable def access (P : Inputs) (σ : SignType) : SignPatternBits.Access (family P σ) where
  rootCoefficient := coefficient P
  polynomialCoefficient := RationalCutBits.coefficient ∘ cutQuery
  pattern _ := InfinitesimalSign.encode σ
  root_eq q k m hm := by
    simp only [coefficient, Function.comp_apply, SignPatternBits.sourceQuery, pairFst_pair, pairSnd_pair]
    generalize hw : BinaryNatCode.encode (m - 1) = w
    have he : Nat.fromBitsLE w + 1 = m := by
      rw [← hw]
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      omega
    subst m
    exact SquareSamplePencilCoefficient.value_packet P (pairFst q) k w
  polynomial_eq q _ _ k m hm := by
    simp only [Function.comp_apply, cutQuery, pairFst_pair, pairSnd_pair]
    exact RationalCutBits.coefficient_packet q k m hm
  pattern_eq _ _ := rfl

noncomputable def rootSet (P : Inputs) (b : List Bool) : Finset ℝ :=
  ((matrix P b).det.map (Int.castRingHom ℝ)).roots.toFinset
noncomputable def count (P : Inputs) (σ : SignType) (q : List Bool) : ℕ :=
  ((rootSet P (pairFst q)).filter (fun x =>
    SignType.sign (((RationalCutBits.polynomial q).map (algebraMap ℤ ℝ)).eval x) = σ)).card

theorem family_count (P : Inputs) (σ : SignType) (q : List Bool) : SignPatternBits.rootCount (family P σ) q = count P σ q := by
  simp only [SignPatternBits.rootCount, family, RootSignQueries.signCount, count, rootSet,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, forall_const, algebraMap_int_eq]

attribute [local irreducible] coefficient SquareSamplePencilCoefficient.value RationalCutBits.coefficient

theorem evaluator {P : Inputs} (h : P.Access) (σ : SignType) :
    SpaceFunction (fun q => BinaryNatCode.encode (count P σ q)) := by
  have H0 := (SquareSamplePencilCoefficient.evaluator h).precompose _ SignPatternBits.sourceQuery_mem_FP
  have H : SpaceFunction (coefficient P) := H0.congr (funext fun _ => by simp only [coefficient, Function.comp_apply])
  have Q := SpaceFunction.ofFP _ (mem_FP_comp cutQuery_FP RationalCutBits.coefficient_FP)
  have E := SignPatternBits.rootCountEvaluator (access P σ) (controls h σ)
    (constFn_mem_FP (InfinitesimalSign.encode σ)) H Q
  exact E.congr (funext fun q => congrArg BinaryNatCode.encode (family_count P σ q))

theorem count_below (P : Inputs) (q : List Bool) : count P .neg q =
    ((rootSet P (pairFst q)).filter (fun x => x < RationalCutBits.threshold q)).card := by
  simp only [count, RationalCutBits.sign_neg_iff]

theorem count_zero_pos_iff (P : Inputs) (q : List Bool) :
    0 < count P 0 q ↔ RationalCutBits.threshold q ∈ rootSet P (pairFst q) := by
  rw [count, Finset.card_pos, Finset.filter_nonempty_iff]
  simp only [cut_sign_zero_iff]
  constructor
  · rintro ⟨x, hx, he⟩
    rwa [he] at hx
  · intro h
    exact ⟨_, h, rfl⟩

noncomputable def language (P : Inputs) : Language := {q | RationalCutBits.threshold q ∈ rootSet P (pairFst q)}
theorem decider {P : Inputs} (h : P.Access) : SpaceDecider (language P) := by
  have E := evaluator h 0
  have hc := ((BinaryFn.const 0).lt (BinaryFn.fromBits id_mem_FP)).flag_mem_FP
  apply E.decider (fun z => decide (0 < Nat.fromBitsLE z)) hc
  intro q
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq, language, Set.mem_ofPred_eq]
  exact (count_zero_pos_iff P q).symm

end LeanCanny.Encoding.SquareSamplePencilCuts
