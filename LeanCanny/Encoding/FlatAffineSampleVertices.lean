/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSampleInput
public import LeanCanny.Encoding.SquareSamplePolynomialTest
public import LeanCanny.Encoding.SquareSampleIndexedSign
public import LeanCanny.Encoding.SquareSampleDerivativeSigns

/-! # Native samples of every regular complete affine tower root

The generic square sampler uses the actual affine rows and coordinate
annihilators. Removing the unique zero dummy gives exactly the regular
original tower roots. Counts, short vertex validity, and parameter sign
queries require only the original source and direction/level access.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSampleVertices
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatAffineFullSourcePositive.system FlatAffineFullSourceTower.system

abbrev Candidates (F : Inputs) (u : List Bool) :=
  SquareSampleParameters.Candidates (FlatAffineSampleInput.input F) u
abbrev OriginalCandidates (F : Inputs) (u : List Bool) :=
  RegularAffineRootCount.RegularRoots (FlatAffineFullSourceTower.system F u)

noncomputable def padded (F : Inputs) (u : List Bool) (z : OriginalCandidates F u) : Candidates F u := by
  have he : PositivePolynomialSystem.extend z.val.val ∘ Fin.castSucc = z.val.val :=
    funext (PositivePolynomialSystem.extend_old z.val.val)
  refine ⟨⟨PositivePolynomialSystem.extend z.val.val,
    (FlatAffineFullSourcePositive.roots_extend_iff (Int.castRingHom ℝ) F u z.val.val).mpr z.val.property⟩, ?_⟩
  apply (FlatAffineFullSourcePositive.analytic_regular_iff F u (PositivePolynomialSystem.extend z.val.val)).mpr
  have hr := z.property
  rw [← he] at hr
  exact hr

noncomputable def unpadded (F : Inputs) (u : List Bool) (z : Candidates F u) : OriginalCandidates F u :=
  ⟨⟨z.val.val ∘ Fin.castSucc, (FlatAffineFullSourcePositive.roots_iff (Int.castRingHom ℝ) F u z.val.val).mp z.val.property |>.1⟩,
    (FlatAffineFullSourcePositive.analytic_regular_iff F u z.val.val).mp z.property⟩

noncomputable def paddingEquiv (F : Inputs) (u : List Bool) : OriginalCandidates F u ≃ Candidates F u where
  toFun := padded F u
  invFun := unpadded F u
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact PositivePolynomialSystem.extend_old z.val.val i
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact FlatAffineFullSourcePositive.extension_unique (Int.castRingHom ℝ) F u z.val.val z.val.property

noncomputable def originalEquiv (F : Inputs) (u : List Bool) :
    SquareSampleParameters.RegularParameters (FlatAffineSampleInput.input F) u ≃ OriginalCandidates F u :=
  (SquareSampleParameters.regularEquiv (FlatAffineSampleInput.input F) u).trans (paddingEquiv F u).symm

noncomputable def count (F : Inputs) := SquareSampleRegularCount.count (FlatAffineSampleInput.input F)
noncomputable def width (F : Inputs) := SquareSampleVertices.width (FlatAffineSampleInput.input F)

theorem count_eq_candidates (F : Inputs) (u : List Bool) : count F u = Nat.card (OriginalCandidates F u) :=
  Nat.card_congr (originalEquiv F u)

theorem count_evaluator {F : Inputs} (h : F.Access) :
    SpaceFunction (fun u => BinaryNatCode.encode (count F u)) :=
  SquareSampleRegularCount.evaluator (FlatAffineSampleInput.access h)

theorem width_unary {F : Inputs} (h : F.Access) : UnaryFn (width F) :=
  SquareSampleVertices.width_unary (FlatAffineSampleInput.access h)

abbrev Valid (F : Inputs) := SquareSampleVertices.Valid (FlatAffineSampleInput.input F)

noncomputable def ordinalEquiv (F : Inputs) (u : List Bool) : Fin (count F u) ≃ OriginalCandidates F u :=
  (SquareSampleHashEnumeration.candidateEquiv (FlatAffineSampleInput.input F) u).trans (paddingEquiv F u).symm

noncomputable def sample (F : Inputs) (u w : List Bool) (h : Valid F u w) : OriginalCandidates F u :=
  (paddingEquiv F u).symm (SquareSampleVertices.sample (FlatAffineSampleInput.input F) u w h)

noncomputable def word (F : Inputs) (u : List Bool) (z : OriginalCandidates F u) : List Bool :=
  SquareSampleVertices.word (FlatAffineSampleInput.input F) u (paddingEquiv F u z)

theorem word_valid (F : Inputs) (u : List Bool) (z : OriginalCandidates F u) : Valid F u (word F u z) :=
  SquareSampleVertices.word_valid (FlatAffineSampleInput.input F) u (paddingEquiv F u z)

theorem sample_word (F : Inputs) (u : List Bool) (z : OriginalCandidates F u) :
    sample F u (word F u z) (word_valid F u z) = z := by
  unfold sample word
  rw [SquareSampleVertices.sample_word, Equiv.symm_apply_apply]

noncomputable def vertexEquiv (F : Inputs) (u : List Bool) :
    {w : List Bool // Valid F u w} ≃ OriginalCandidates F u :=
  (SquareSampleVertices.vertexEquiv (FlatAffineSampleInput.input F) u).trans (paddingEquiv F u).symm

noncomputable def language (F : Inputs) := SquareSampleVertices.language (FlatAffineSampleInput.input F)

theorem decider {F : Inputs} (h : F.Access) : SpaceDecider (language F) :=
  SquareSampleVertices.decider (FlatAffineSampleInput.access h)

theorem mem_PSPACE {F : Inputs} (h : F.Access) : language F ∈ PSPACE := (decider h).mem_PSPACE

def existenceLanguage (F : Inputs) : Language := {u | Nonempty (OriginalCandidates F u)}

theorem existence_mem_PSPACE {F : Inputs} (h : F.Access) : existenceLanguage F ∈ PSPACE := by
  have he : existenceLanguage F = SquareSampleRegularCount.language (FlatAffineSampleInput.input F) := by
    ext u
    exact (originalEquiv F u).nonempty_congr.symm
  rw [he]
  exact SquareSampleRegularCount.language_mem_PSPACE (FlatAffineSampleInput.access h)


end LeanCanny.Encoding.FlatAffineSampleVertices
