/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleGridAccess
public import LeanCanny.Encoding.SquareSampleEquationTest
public import LeanCanny.Encoding.SquareSampleVertices

/-! # Native vertices for every captured square-system root

Grid ordinals give short labels. The original equations select actual roots
without a Jacobian condition. Complete annihilators make these vertices
bijective with the whole original root set, including singular roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteVertices
open LeanCanny.Algebra LeanCanny.Computation Brackets
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

abbrev GridValid (F : Inputs) := SquareSampleVertices.Valid (SquareSampleGrid.input F)
noncomputable def width (F : Inputs) := SquareSampleVertices.width (SquareSampleGrid.input F)

theorem width_unary {F : Inputs} (h : F.Access) : UnaryFn (width F) :=
  SquareSampleVertices.width_unary (SquareSampleGrid.access h)

noncomputable def point (F : Inputs) (u w : List Bool) (hw : GridValid F u w) : Fin (F.count u) → ℝ :=
  (SquareSampleVertices.sample (SquareSampleGrid.input F) u w hw).val.val

def Valid (F : Inputs) (u w : List Bool) : Prop :=
  ∃ hw : GridValid F u w, ∀ i, (F.system u i).eval₂ (Int.castRingHom ℝ) (point F u w hw) = 0

noncomputable def candidate (F : Inputs) (u w : List Bool) (hw : Valid F u w) : SquareSampleComplete.Roots F u :=
  ⟨point F u w (Classical.choose hw), Classical.choose_spec hw⟩

noncomputable def gridCandidate (F : Inputs) (hF : SquareSampleComplete.Complete F) (u : List Bool)
    (z : SquareSampleComplete.Roots F u) : SquareSampleParameters.Candidates (SquareSampleGrid.input F) u := by
  have hz : ∀ i, (SquareSampleGrid.system F u i).eval₂ (Int.castRingHom ℝ) z.val = 0 :=
    (SquareSampleGrid.roots_iff F u z.val).mpr (hF u z.val z.property)
  exact ⟨⟨z.val, hz⟩, SquareSampleGrid.regular F u z.val hz⟩

noncomputable def word (F : Inputs) (hF : SquareSampleComplete.Complete F) (u : List Bool)
    (z : SquareSampleComplete.Roots F u) : List Bool :=
  SquareSampleVertices.word (SquareSampleGrid.input F) u (gridCandidate F hF u z)

lemma word_valid (F : Inputs) (hF : SquareSampleComplete.Complete F) (u : List Bool)
    (z : SquareSampleComplete.Roots F u) : Valid F u (word F hF u z) := by
  have hw := SquareSampleVertices.word_valid (SquareSampleGrid.input F) u (gridCandidate F hF u z)
  refine ⟨hw, ?_⟩
  have he := congrArg (fun x : SquareSampleParameters.Candidates (SquareSampleGrid.input F) u => x.val.val)
    (SquareSampleVertices.sample_word (SquareSampleGrid.input F) u (gridCandidate F hF u z))
  change point F u (word F hF u z) hw = z.val at he
  rw [he]
  exact z.property

lemma candidate_word (F : Inputs) (hF : SquareSampleComplete.Complete F) (u : List Bool)
    (z : SquareSampleComplete.Roots F u) :
    candidate F u (word F hF u z) (word_valid F hF u z) = z := by
  apply Subtype.ext
  exact congrArg (fun x : SquareSampleParameters.Candidates (SquareSampleGrid.input F) u => x.val.val)
    (SquareSampleVertices.sample_word (SquareSampleGrid.input F) u (gridCandidate F hF u z))

lemma candidate_injective (F : Inputs) (u w v : List Bool) (hw : Valid F u w) (hv : Valid F u v)
    (he : candidate F u w hw = candidate F u v hv) : w = v := by
  apply SquareSampleVertices.sample_injective (SquareSampleGrid.input F) u w v (Classical.choose hw) (Classical.choose hv)
  have hp : point F u w (Classical.choose hw) = point F u v (Classical.choose hv) :=
    congrArg (fun z : SquareSampleComplete.Roots F u => z.val) he
  exact Subtype.ext (Subtype.ext hp)

noncomputable def vertexEquiv (F : Inputs) (hF : SquareSampleComplete.Complete F) (u : List Bool) :
    {w : List Bool // Valid F u w} ≃ SquareSampleComplete.Roots F u :=
  Equiv.ofBijective (fun w => candidate F u w.val w.property)
    ⟨fun x y h => Subtype.ext (candidate_injective F u x.val y.val x.property y.property h),
      fun z => ⟨⟨word F hF u z, word_valid F hF u z⟩, candidate_word F hF u z⟩⟩

noncomputable def theta (F : Inputs) (u w : List Bool) (hw : GridValid F u w) :
    SquareSampleRecordSpan.Root (SquareSampleGrid.input F) u :=
  SquareSampleHashEnumeration.root (SquareSampleGrid.input F) u ⟨Nat.fromBitsLE w, hw.2⟩

lemma point_decode (F : Inputs) (u w : List Bool) (hw : GridValid F u w) :
    point F u w hw = SquareSampleParameters.decode F u (theta F u w hw).val := rfl

lemma sign_zero_iff (F : Inputs) (u w : List Bool) (hw : GridValid F u w) :
    SquareSampleVertices.signValue (SquareSampleGrid.input F) (SquareSampleEquationTest.test F) (pair u w) = [] ↔
      ∀ i, (F.system u i).eval₂ (Int.castRingHom ℝ) (point F u w hw) = 0 := by
  rw [SquareSampleVertices.sign_packet _ _ _ _ hw]
  change InfinitesimalSign.encode (SquareSampleTestMoments.sign (SquareSampleEquationTest.test F) u (theta F u w hw).val) =
    InfinitesimalSign.encode 0 ↔ _
  rw [SquareSampleTestSign.encode_eq_iff]
  unfold SquareSampleTestMoments.sign
  rw [sign_eq_zero_iff, Polynomial.eval_map]
  have ht := (SquareSampleQueries.mem_roots (SquareSampleGrid.input F) u (theta F u w hw).val).mp (theta F u w hw).property
  rw [SquareSampleGrid.parameter_eq] at ht
  rw [point_decode]
  exact SquareSampleEquationTest.zero_iff F u _ ht.1

lemma valid_iff (F : Inputs) (u w : List Bool) : Valid F u w ↔ GridValid F u w ∧
    SquareSampleVertices.signValue (SquareSampleGrid.input F) (SquareSampleEquationTest.test F) (pair u w) = [] := by
  constructor
  · rintro ⟨hw, hz⟩
    exact ⟨hw, (sign_zero_iff F u w hw).mpr hz⟩
  · rintro ⟨hw, hz⟩
    exact ⟨hw, (sign_zero_iff F u w hw).mp hz⟩

noncomputable def signValue (F : Inputs) (T : SquareSampleTestMoments.Test) : List Bool → List Bool :=
  SquareSampleVertices.signValue (SquareSampleGrid.input F) T

theorem sign_evaluator {F : Inputs} (h : F.Access) {T : SquareSampleTestMoments.Test} (A : T.Access) :
    SpaceFunction (signValue F T) := SquareSampleVertices.sign_evaluator (SquareSampleGrid.access h) A

lemma sign_packet (F : Inputs) (T : SquareSampleTestMoments.Test) (u w : List Bool) (hw : Valid F u w) :
    signValue F T (pair u w) = InfinitesimalSign.encode
      (SquareSampleTestMoments.sign T u (theta F u w (Classical.choose hw)).val) :=
  SquareSampleVertices.sign_packet _ _ _ _ (Classical.choose hw)

def language (F : Inputs) : Language := {q | Valid F (pairFst q) (pairSnd q)}
def accept (q : List Bool) : Bool := decide (pairFst q = [true] ∧ pairSnd q = [])

theorem accept_FP : (fun q => [accept q]) ∈ FP :=
  ((stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).and (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP []))).flag_mem_FP

theorem decider {F : Inputs} (h : F.Access) : SpaceDecider (language F) := by
  have hG := SquareSampleGrid.access h
  have V := (SquareSampleVertices.decider hG).flagEvaluator
  have S := SquareSampleVertices.sign_evaluator hG (SquareSampleEquationTest.access h)
  refine (V.pairOutputs S).decider accept accept_FP (fun q => ?_)
  simp only [accept, pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq]
  change Valid F (pairFst q) (pairSnd q) ↔ _
  rw [valid_iff]
  simp only [SquareSampleVertices.language, Set.mem_ofPred_eq]
  have he : SquareSampleVertices.signValue (SquareSampleGrid.input F) (SquareSampleEquationTest.test F)
      (pair (pairFst q) (pairSnd q)) =
      SquareSampleVertices.signValue (SquareSampleGrid.input F) (SquareSampleEquationTest.test F) q := by
    simp only [SquareSampleVertices.signValue, Function.comp_apply, SquareSampleVertices.normalizeQuery,
      pairFst_pair, pairSnd_pair]
  rw [he]

theorem mem_PSPACE {F : Inputs} (h : F.Access) : language F ∈ PSPACE := (decider h).mem_PSPACE

end LeanCanny.Encoding.SquareSampleCompleteVertices
