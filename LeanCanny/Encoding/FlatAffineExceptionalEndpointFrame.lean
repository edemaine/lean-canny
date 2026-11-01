/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointCanonicalParent
public import LeanCanny.Algebra.FlatAffineShiftedLevels
public import LeanCanny.Encoding.IntegerPolynomialSampleSlicePoint
public import LeanCanny.Encoding.FlatAffineSlicePresentation
public import LeanCanny.Computation.SpaceFunctionChain

/-! # Exceptional endpoints as frozen affine parameter frames

An exceptional scalar need not be an ordinary critical sample. This frame
retains its complete integer joint marker and the computed original parent
word. Its extra frozen coordinate is the actual exceptional scalar, rather
than an asserted critical block. Affine level polynomials remain linear.

The native writer and guard below construct this representation; they do
not supply a critical sampler or a recursive connection algorithm for the
new parameter frame. In particular this is a separate frame kind from the
one-bit ordinary-critical/midpoint trace.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalEndpointFrame
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry MvPolynomial
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (row parentCone)
open scoped Classical BigOperators
attribute [local irreducible] SquareSampleCompleteVertices.candidate FlatAffineEndpointCanonicalParent.value

def marker (q : List Bool) : List Bool := pairFst q
def parentWord (q : List Bool) : List Bool := pairSnd q
def original (q : List Bool) : List Bool :=
  FlatAffineJointPrefixChoice.original (FlatAffineEndpointMarkers.source (marker q))

theorem original_FP : original ∈ FP := by
  polytime [original, marker, FlatAffineJointPrefixChoice.original, FlatAffineEndpointMarkers.source]

noncomputable def language (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) : Language :=
  FlatAffineEndpointCanonicalParent.language F C h

noncomputable def frame (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) : List Bool :=
  pair q (FlatAffineEndpointCanonicalParent.value F C h q)

theorem evaluator {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    SpaceFunction (frame F C h) :=
  (FlatAffineEndpointCanonicalParent.evaluator hF C h hh).withInput

theorem decider {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    SpaceDecider (language F C h) :=
  FlatAffineEndpointCanonicalParent.decider hF C h hh

theorem frame_valid (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointMarkers.language (next F) C (row F h)) :
    frame F C h q ∈ language F C h := by
  exact ⟨by simpa only [frame, pairFst_pair] using hq, by simp only [frame, pairFst_pair, pairSnd_pair]⟩

theorem frame_original (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) :
    original (frame F C h q) = FlatAffineJointPrefixChoice.original (FlatAffineEndpointMarkers.source q) := by
  simp only [original, marker, frame, pairFst_pair]

theorem marker_valid (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) (hq : q ∈ language F C h) :
    marker q ∈ FlatAffineEndpointMarkers.language (next F) C (row F h) := hq.1

noncomputable def parent (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) (hq : q ∈ language F C h) :
    FlatAffinePowerSampleInput.OriginalRoots F (original q) :=
  FlatAffineEndpointCanonicalParent.parent F C h (marker q) (marker_valid F C h q hq)

theorem parentWord_valid (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) (hq : q ∈ language F C h) :
    FlatAffineCompleteVertices.Valid F (parentCone F C) (original q) (parentWord q) := by
  have hv := FlatAffineEndpointCanonicalParent.value_valid F C h (marker q) (marker_valid F C h q hq)
  have he : FlatAffineEndpointCanonicalParent.value F C h (marker q) = parentWord q := hq.2
  exact he ▸ hv

theorem parent_eq_decode (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) (hq : q ∈ language F C h) :
    parent F C h q hq = FlatAffineCompleteVertices.vertexEquiv F (parentCone F C) (original q)
      ⟨parentWord q, parentWord_valid F C h q hq⟩ := by
  apply congrArg (FlatAffineCompleteVertices.vertexEquiv F (parentCone F C) (original q))
  exact Subtype.ext hq.2

noncomputable def scalar (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) (_hq : q ∈ language F C h) : ℝ :=
  IntegerPolynomialSampleSlice.point (FlatAffineEndpointAdjacentSamples.heightSource (next F) C (row F h))
    (pair (pair (pairFst (FlatAffineEndpointMarkers.source (marker q)))
      (FlatAffineEndpointMarkers.endpointWord (marker q))) [])

theorem frame_scalar (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (s a w : List Bool)
    (hq : pair (pair s a) w ∈ FlatAffineEndpointMarkers.language (next F) C (row F h)) :
    scalar F C h (frame F C h (pair (pair s a) w)) (frame_valid F C h _ hq) =
      (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
        (FlatAffineEndpointAdjacentSamples.heightSource (next F) C (row F h))) (pairFst s) a
        (by simpa only [FlatAffineEndpointMarkers.source, FlatAffineEndpointMarkers.endpointWord,
          pairFst_pair, pairSnd_pair] using FlatAffineEndpointMarkers.endpoint_valid (next F) C (row F h) _ hq)).val (0 : Fin 1) := by
  simp only [scalar, frame, marker, FlatAffineEndpointMarkers.source,
    FlatAffineEndpointMarkers.endpointWord, pairFst_pair, pairSnd_pair]
  exact IntegerPolynomialSampleSlice.point_packet _ _ _ [] _

theorem scalar_joint (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) (hq : q ∈ language F C h) :
    scalar F C h q hq = FlatAffineEndpointFiniteProjection.endpoint (next F)
      (FlatAffineEndpointMarkers.source (marker q))
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input (next F) C (row F h))
        (FlatAffineEndpointMarkers.source (marker q)) (FlatAffineEndpointMarkers.jointWord (marker q))
        (FlatAffineEndpointMarkers.joint_valid (next F) C (row F h) (marker q) (marker_valid F C h q hq))).val := by
  have hm := marker_valid F C h q hq
  have H := (FlatAffineEndpointFiniteHeights.endpoint_packet (next F) C (row F h)
    (FlatAffineEndpointMarkers.source (marker q)) (FlatAffineEndpointMarkers.jointWord (marker q))
    (FlatAffineEndpointMarkers.endpointWord (marker q))
    (FlatAffineEndpointMarkers.frame_valid (next F) C (row F h) (marker q) hm)
    (FlatAffineEndpointMarkers.joint_valid (next F) C (row F h) (marker q) hm)
    (FlatAffineEndpointMarkers.endpoint_valid (next F) C (row F h) (marker q) hm)).mp hm.2
  exact (IntegerPolynomialSampleSlice.point_packet _ _ _ []
    (FlatAffineEndpointMarkers.endpoint_valid (next F) C (row F h) (marker q) hm)).trans H.symm

/-- One additional frozen parameter, not an additional critical stage. -/
abbrev Parameters (F : Inputs) (u : List Bool) :=
  FlatAffineCriticalTower.Ancestors (arity F u) (F.depth u) ⊕ Unit

noncomputable def levels (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool)
    (j : Fin (arity F u)) : MvPolynomial (Parameters F u) ℤ :=
  FlatAffineShiftedLevels.levels (fun j => (FlatAffineFullSourceTower.level F u (F.depth u) j).polynomial) (h u) j

noncomputable def parameters (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) (hq : q ∈ language F C h) :
    Parameters F (original q) → ℝ :=
  FlatAffineShiftedLevels.point ((parent F C h q hq).val ∘
    TriangularPolynomialIndexing.enumerate (stageWidth F (original q)) (F.depth (original q))) (scalar F C h q hq)

theorem levels_eval (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) (hq : q ∈ language F C h)
    (j : Fin (arity F (original q))) :
    (levels F h (original q) j).eval₂ (Int.castRingHom ℝ) (parameters F C h q hq) =
      (FlatAffineFullSourceTower.level F (original q) (F.depth (original q)) j).polynomial.eval₂ (Int.castRingHom ℝ)
        ((parent F C h q hq).val ∘ TriangularPolynomialIndexing.enumerate (stageWidth F (original q)) (F.depth (original q))) +
        if j = h (original q) then scalar F C h q hq else 0 :=
  FlatAffineShiftedLevels.eval _ _ _ _ _ _

theorem levels_degree (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool)
    (j : Fin (arity F u)) : (levels F h u j).totalDegree ≤ 1 := by
  unfold levels FlatAffineShiftedLevels.levels
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_rename_le _ _).trans (FlatAffineCriticalTower.Level.degree_le _)
  · split_ifs <;> simp

noncomputable def presentation (F : Inputs) (h : (u : List Bool) → Fin (arity F u))
    (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u) (a : ℝ) : Set (Fin (arity F u) → ℝ) :=
  {y | (BoundedFullCriticalSamples.polynomial F.source u).eval₂ (Int.castRingHom ℝ) y = 0 ∧
    ∀ j ∈ FlatAffineFullSourceTower.free F u (F.depth u),
      ∑ i, (FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i : ℝ) * y i =
        (levels F h u j).eval₂ (Int.castRingHom ℝ)
          (FlatAffineShiftedLevels.point (x.val ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u)) a)}

theorem presentation_eq_slice (F : Inputs) (h : (u : List Bool) → Fin (arity F u))
    (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u) (a : ℝ) :
    presentation F h u x a = FlatAffineShiftedSlice.slice F u x (h u) a := by
  have HL (j : Fin (arity F u)) :
      (levels F h u j).eval₂ (Int.castRingHom ℝ)
        (FlatAffineShiftedLevels.point (x.val ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u)) a) =
      (FlatAffineFullSourceTower.level F u (F.depth u) j).polynomial.eval₂ (Int.castRingHom ℝ)
        (x.val ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u)) + if j = h u then a else 0 :=
    FlatAffineShiftedLevels.eval _ _ _ _ _ _
  ext y
  simp only [presentation, Set.mem_ofPred_eq, HL]
  rfl

noncomputable def slice (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) (hq : q ∈ language F C h) :
    Set (Fin (arity F (original q)) → ℝ) :=
  presentation F h (original q) (parent F C h q hq) (scalar F C h q hq)

theorem slice_eq (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) (hq : q ∈ language F C h) :
    slice F C h q hq = FlatAffineShiftedSlice.slice F (original q) (parent F C h q hq)
      (h (original q)) (scalar F C h q hq) := by
  exact presentation_eq_slice F h (original q) (parent F C h q hq) (scalar F C h q hq)

def rank (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) : ℕ :=
  F.source.dim (original q) + 3 - ((h (original q)).val + 1)

theorem rank_unary {F : Inputs} (hF : F.Access)
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) : UnaryFn (rank F h) :=
  ((hF.source.dim.add (UnaryFn.const 3)).sub (hh.add (UnaryFn.const 1))).comp original_FP

theorem rank_decreases (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (q : List Bool)
    (hn : (h (original q)).val < F.source.dim (original q) + 3) :
    rank F h q < F.source.dim (original q) + 3 - (h (original q)).val := by
  unfold rank
  omega

theorem frame_length_polynomial {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    ∃ p : Polynomial ℕ, ∀ q, (frame F C h q).length ≤ p.eval q.length :=
  (evaluator hF C h hh).exists_output_length_poly

end LeanCanny.Encoding.FlatAffineExceptionalEndpointFrame
