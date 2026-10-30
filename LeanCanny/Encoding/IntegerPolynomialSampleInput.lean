/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompletePolynomialTest
public import LeanCanny.Encoding.SquareSampleAccess
public import LeanCanny.Algebra.IntegerPolynomialRootQueriesSpace
public import LeanCanny.Algebra.ZeroAwarePolynomialSpace
public import LeanCanny.Algebra.UnivariateRowSpace

/-! # Complete native labels for implicit integer polynomial roots

One-dimensional complete square sampling gives short labels and native
validity for every real root, including repeated roots. The zero polynomial
is replaced by one, matching the finite root-list convention. No root digits,
squarefreeness, actual degree, or root-isolation oracle is assumed.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegerPolynomialSampleInput
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open IntegerPolynomialRootQueriesBits (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def polynomial (S : Source) := ZeroAwarePolynomialBits.polynomial S.polynomial

theorem coefficientEvaluator {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial S)) :=
  ZeroAwarePolynomialBits.coefficientEvaluator S.polynomial A.coefficient S.degree S.mass A.degree A.mass S.degree_bound S.mass_bound

theorem height_le (S : Source) (u : List Bool) (k : ℕ) : ((polynomial S u).coeff k).natAbs.size ≤ S.mass u + 1 := by
  have hm := (coeff_natAbs_le_coefficientMass (polynomial S u) k).trans
    (ZeroAwarePolynomialBits.mass_le S.polynomial S.mass S.mass_bound u)
  exact (Nat.size_le_size hm).trans_eq (by simp only [Nat.size_pow])

noncomputable def input (S : Source) : SquareSampleInput.Inputs where
  count _ := 1
  degree u := S.degree u + 1
  mass := S.mass
  system u _ := (polynomial S u).toMvPolynomial (0 : Fin 1)
  count_pos _ := Nat.zero_lt_one
  degree_pos _ := Nat.zero_lt_succ _
  system_degree u _ := (DiagonalUnivariateSystem.degree_le _ _).trans
    ((ZeroAwarePolynomialBits.degree_le S.polynomial S.degree S.degree_bound u).trans (Nat.le_succ _))
  system_mass u _ := (DiagonalUnivariateSystem.mass_le _ _).trans
    (ZeroAwarePolynomialBits.mass_le S.polynomial S.mass S.mass_bound u)
  annihilator u _ := polynomial S u
  annDegree := S.degree
  annHeight u := S.mass u + 1
  ann_nonzero u _ := ZeroAwarePolynomialBits.ne_zero S.polynomial u
  ann_degree u _ := ZeroAwarePolynomialBits.degree_le S.polynomial S.degree S.degree_bound u
  ann_height u _ := height_le S u
  ann_root u z hz _ i := by
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simpa only [DiagonalUnivariateSystem.eval] using hz 0

theorem complete (S : Source) : SquareSampleComplete.Complete (input S) := by
  intro u z hz i
  have hi : i = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance i 0
  change (polynomial S u).eval₂ (Int.castRingHom ℝ) (z i) = 0
  rw [hi]
  simpa only [input, DiagonalUnivariateSystem.eval] using hz (0 : Fin 1)

theorem rowEvaluator {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S) :
    SpaceFunction (SquareSampleInput.rowCoefficient (input S)) := by
  have P := PolynomialFamilyProductBits.reindexEvaluator (coefficientEvaluator A) SquareSampleInput.source SquareSampleInput.source_FP
  have E := UnivariateRowBits.evaluator (UnaryFn.const 1) (UnaryFn.length SquareSampleInput.widthWord_FP)
    (fun _ => (0 : Fin 1)) (UnaryFn.const 0) (polynomial S ∘ SquareSampleInput.source) P
    SquareSampleInput.rankWord_FP SquareSampleInput.modulusWord_FP
  exact E.congr (funext fun _ => rfl)

def annQuery (q : List Bool) : List Bool :=
  pair (pair (SquareSampleInput.source q) (SquareSampleInput.rankWord q)) (SquareSampleInput.modulusWord q)
theorem annQuery_FP : annQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair SquareSampleInput.source_FP SquareSampleInput.rankWord_FP) SquareSampleInput.modulusWord_FP

theorem annEvaluator {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S) :
    SpaceFunction (SquareSampleInput.annCoefficient (input S)) := by
  refine ((coefficientEvaluator A).precompose annQuery annQuery_FP).congr (funext fun q => ?_)
  simp only [Function.comp_apply, annQuery, PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue, pairFst_pair, pairSnd_pair]
  rfl

theorem access {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S) : (input S).Access :=
  ⟨UnaryFn.const 1, A.degree.add (BinaryFn.const 1), A.mass, A.degree, A.mass.add (BinaryFn.const 1), rowEvaluator A, annEvaluator A⟩

theorem roots_iff (S : Source) (u : List Bool) (hu : S.polynomial u ≠ 0) (z : Fin 1 → ℝ) :
    (∀ i, ((input S).system u i).eval₂ (Int.castRingHom ℝ) z = 0) ↔
      (S.polynomial u).eval₂ (Int.castRingHom ℝ) (z 0) = 0 := by
  simp only [input, polynomial, ZeroAwarePolynomialBits.polynomial, hu, ite_false, DiagonalUnivariateSystem.eval,
    Fin.forall_fin_one]

theorem width_unary {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S) :
    UnaryFn (SquareSampleCompleteVertices.width (input S)) :=
  SquareSampleCompleteVertices.width_unary (access A)

theorem vertex_mem_PSPACE {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S) :
    SquareSampleCompleteVertices.language (input S) ∈ PSPACE :=
  SquareSampleCompleteVertices.mem_PSPACE (access A)

theorem root_complete (S : Source) (u : List Bool) (hu : S.polynomial u ≠ 0) (a : ℝ)
    (ha : (S.polynomial u).eval₂ (Int.castRingHom ℝ) a = 0) :
    ∃ w, ∃ hw : SquareSampleCompleteVertices.Valid (input S) u w,
      (SquareSampleCompleteVertices.candidate (input S) u w hw).val (0 : Fin 1) = a := by
  let z : SquareSampleComplete.Roots (input S) u := ⟨fun _ => a, (roots_iff S u hu (fun _ => a)).mpr ha⟩
  exact ⟨SquareSampleCompleteVertices.word (input S) (complete S) u z,
    SquareSampleCompleteVertices.word_valid (input S) (complete S) u z,
    congrArg (fun x : SquareSampleComplete.Roots (input S) u => x.val (0 : Fin 1))
      (SquareSampleCompleteVertices.candidate_word (input S) (complete S) u z)⟩

noncomputable def test (S Q : Source) : SquareSamplePolynomialTest.Test (input S) where
  polynomial u := (Q.polynomial u).toMvPolynomial (0 : Fin 1)
  degree := Q.degree
  mass := Q.mass
  polynomial_degree u := (DiagonalUnivariateSystem.degree_le _ _).trans (Q.degree_bound u)
  polynomial_mass u := (DiagonalUnivariateSystem.mass_le _ _).trans (Q.mass_bound u)

theorem testAccess (S : Source) {Q : Source} (B : IntegerPolynomialRootQueriesBits.Access Q) : (test S Q).Access := by
  have hW : UnaryFn (fun u => (Q.degree u).size) :=
    (UnaryFn.length B.degree.bits_mem_FP).of_eq (fun u => BinaryNatCode.length_encode (Q.degree u))
  have P := PolynomialFamilyProductBits.reindexEvaluator B.coefficient
    RationalSubstitution.IntegerBits.context RationalSubstitution.IntegerBits.context_mem_FP
  have E := UnivariateRowBits.evaluator (UnaryFn.const 1) (hW.comp RationalSubstitution.IntegerBits.context_mem_FP)
    (fun _ => (0 : Fin 1)) (UnaryFn.const 0) (Q.polynomial ∘ RationalSubstitution.IntegerBits.context) P
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
  refine ⟨B.degree, B.mass, E.congr (funext fun q => ?_)⟩
  dsimp only [FixedWidthRowBits.value]
  rw [FixedWidthPolynomial.nativeExponent_refl]
  rfl

theorem signEvaluator {S Q : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    (B : IntegerPolynomialRootQueriesBits.Access Q) :
    SpaceFunction (SquareSampleCompletePolynomialTest.value (input S) (test S Q)) :=
  SquareSampleCompletePolynomialTest.evaluator (access A) (testAccess S B)

theorem sign_mem_PSPACE {S Q : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    (B : IntegerPolynomialRootQueriesBits.Access Q) (s : SignType) :
    SquareSampleCompletePolynomialTest.language (input S) (test S Q) s ∈ PSPACE :=
  SquareSampleCompletePolynomialTest.mem_PSPACE (access A) (testAccess S B) s

theorem sign_packet (S Q : Source) (s : SignType) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input S) u w) :
    pair u w ∈ SquareSampleCompletePolynomialTest.language (input S) (test S Q) s ↔
      SignType.sign ((Q.polynomial u).eval₂ (Int.castRingHom ℝ)
        ((SquareSampleCompleteVertices.candidate (input S) u w hw).val (0 : Fin 1))) = s := by
  rw [SquareSampleCompletePolynomialTest.language_packet _ _ _ _ _ hw]
  exact Iff.of_eq (congrArg (fun z : ℝ => SignType.sign z = s)
    (DiagonalUnivariateSystem.eval (Q.polynomial u) (0 : Fin 1) (Int.castRingHom ℝ)
      (SquareSampleCompleteVertices.candidate (input S) u w hw).val))

end LeanCanny.Encoding.IntegerPolynomialSampleInput
