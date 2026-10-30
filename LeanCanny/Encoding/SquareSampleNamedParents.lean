/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleRationalCoordinates
public import LeanCanny.Encoding.NamedRationalParents
public import LeanCanny.Algebra.IntegerPolynomialIteratedDerivativeSource

/-! # Complete square-system point labels supply actual named rational parents

The primitive equation is separable even when the original system is singular.
Actual parents are precisely its parameters decoding to original roots. Their
names are the original complete point labels, with native validity and indexed
derivative probes. This feeds the existing ancestry-aware child sampling
interface without assuming regularity of the original parent system.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleNamedParents
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open SquareSampleCompleteParameterTest (theta)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def roots (F : Inputs) (c : List Bool) : Set ℝ :=
  {a | (SquareSampleCoordinates.parameter F c).eval₂ (Int.castRingHom ℝ) a = 0 ∧
    ∀ i, (F.system c i).eval₂ (Int.castRingHom ℝ) (SquareSampleParameters.decode F c a) = 0}

abbrev Root (F : Inputs) (c : List Bool) := {a : ℝ // a ∈ roots F c}
noncomputable def point (F : Inputs) (c : List Bool) (a : Root F c) : SquareSampleComplete.Roots F c :=
  ⟨SquareSampleParameters.decode F c a.val, a.property.2⟩

noncomputable def root (F : Inputs) (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) : Root F c :=
  ⟨theta F c w, SquareSampleCompleteParameterTest.theta_root F c w hw, by
    rw [SquareSampleCompleteParameterTest.decode_theta F c w hw]
    exact (SquareSampleCompleteVertices.candidate F c w hw).property⟩

noncomputable def word (F : Inputs) (complete : SquareSampleComplete.Complete F) (c : List Bool) (a : Root F c) : List Bool :=
  SquareSampleCompleteVertices.word F complete c (point F c a)

theorem word_valid (F : Inputs) (complete : SquareSampleComplete.Complete F) (c : List Bool) (a : Root F c) :
    SquareSampleCompleteVertices.Valid F c (word F complete c a) :=
  SquareSampleCompleteVertices.word_valid F complete c (point F c a)

theorem theta_word (F : Inputs) (complete : SquareSampleComplete.Complete F) (c : List Bool) (a : Root F c) :
    theta F c (word F complete c a) = a.val := by
  have H := (SquareSampleCompleteParameterTest.decode_theta F c (word F complete c a) (word_valid F complete c a)).trans
    (congrArg (fun z : SquareSampleComplete.Roots F c => z.val)
      (SquareSampleCompleteVertices.candidate_word F complete c (point F c a)))
  exact SquareSampleCoordinates.parameter_roots_ext F c _ a.val
    (SquareSampleCompleteParameterTest.theta_root F c _ (word_valid F complete c a)) a.property.1 (fun i => congrFun H i)

theorem word_root (F : Inputs) (complete : SquareSampleComplete.Complete F) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid F c w) : word F complete c (root F c w hw) = w := by
  apply SquareSampleCompleteVertices.candidate_injective F c _ w (word_valid F complete c _) hw
  apply Subtype.ext
  exact (congrArg (fun z : SquareSampleComplete.Roots F c => z.val)
    (SquareSampleCompleteVertices.candidate_word F complete c (point F c (root F c w hw)))).trans
      (SquareSampleCompleteParameterTest.decode_theta F c w hw)

noncomputable def derivativeValue (F : Inputs) : List Bool → List Bool :=
  SquareSampleCompleteParameterTest.value F
    (IntegerPolynomialIteratedDerivativeBits.source (SquareSampleCompleteParameterTest.source F))

attribute [local irreducible] SquareSampleCompleteParameterTest.value

theorem derivativeEvaluator {F : Inputs} (h : F.Access) : SpaceFunction (derivativeValue F) :=
  SquareSampleCompleteParameterTest.evaluator
    (Q := IntegerPolynomialIteratedDerivativeBits.source (SquareSampleCompleteParameterTest.source F)) h
    (IntegerPolynomialIteratedDerivativeBits.access (SquareSampleCompleteParameterTest.sourceAccess h))

noncomputable def source (F : Inputs) (complete : SquareSampleComplete.Complete F) : NamedRationalParents.Source where
  equation := SquareSampleRationalCoordinates.equation F
  coordinates := SquareSampleRationalCoordinates.coordinates F
  roots := roots F
  root_zero _ _ ha := ha.1
  defined c a ha := SquareSampleRationalCoordinates.defined F c a ha.1
  descriptor := word F complete
  descriptor_injective c x y he := Subtype.ext
    ((theta_word F complete c x).symm.trans ((congrArg (theta F c) he).trans (theta_word F complete c y)))
  width := SquareSampleCompleteVertices.width F
  descriptor_length c a := (Classical.choose (word_valid F complete c a)).1.le
  derivativeValue := derivativeValue F
  derivative_packet c a k := by
    rw [derivativeValue, SquareSampleCompleteParameterTest.packet F _ c (word F complete c a)
      (BinaryNatCode.encode k) (word_valid F complete c a), IntegerPolynomialIteratedDerivativeBits.packet, theta_word F complete c a]
    rfl

theorem language_iff (F : Inputs) (complete : SquareSampleComplete.Complete F) (q : List Bool) :
    q ∈ NamedRationalParents.language (source F complete) ↔ q ∈ SquareSampleCompleteVertices.language F := by
  constructor
  · rintro ⟨a, ha⟩
    have H := word_valid F complete (pairFst q) a
    change word F complete (pairFst q) a = pairSnd q at ha
    rw [ha] at H
    exact H
  · intro hw
    change SquareSampleCompleteVertices.Valid F (pairFst q) (pairSnd q) at hw
    exact ⟨root F (pairFst q) (pairSnd q) hw, word_root F complete _ _ hw⟩

theorem access {F : Inputs} (h : F.Access) (complete : SquareSampleComplete.Complete F) :
    NamedRationalParents.Access (source F complete) := by
  refine ⟨SquareSampleRationalCoordinates.equationAccess h, SquareSampleRationalCoordinates.coordinatesAccess h,
    SquareSampleCompleteVertices.width_unary h, ?_, ?_⟩
  · apply (SquareSampleCompleteVertices.decider h).congr
    ext q
    exact (language_iff F complete q).symm
  · exact derivativeEvaluator h

theorem original_point (F : Inputs) (complete : SquareSampleComplete.Complete F) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid F c w) (i : Fin (F.count c)) :
    RationalCoordinateFamily.point (source F complete).coordinates c (root F c w hw).val i.val =
      (SquareSampleCompleteVertices.candidate F c w hw).val i := by
  exact (SquareSampleRationalCoordinates.point F c (theta F c w) i).trans
    (congrFun (SquareSampleCompleteParameterTest.decode_theta F c w hw) i)

end LeanCanny.Encoding.SquareSampleNamedParents
