/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleProjectionChoice

/-! # Correctness of native projected labels at a validated source

The existing native search only needs the projected point to satisfy the
target equations at the current source and label. This form applies to
guarded joint samplers without imposing a projection promise on invalid
source records. No additional computational reader is used.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleProjectionChoice
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] word width SquareSampleProjectionEquality.language

theorem exists_candidate_at (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w)
    (projects : ∀ i, (G.system c i).eval₂ (Int.castRingHom ℝ)
      ((SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c) = 0) :
    ∃ n < bound G (pair c w), pair (pair c w) (BinaryNatCode.encode n) ∈ language F G projection := by
  let x : SquareSampleComplete.Roots G c :=
    ⟨(SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c, projects⟩
  let v := SquareSampleCompleteVertices.word G completeG c x
  have hv := SquareSampleCompleteVertices.word_valid G completeG c x
  have HL : v.length = width G (pair c w) := by
    unfold width
    rw [pairFst_pair]
    exact (Classical.choose hv).1
  have HE := (SquareSampleProjectionEquality.packet F G completeG projection c w v hw hv).mpr
    (congrArg (fun z : SquareSampleComplete.Roots G c => z.val)
      (SquareSampleCompleteVertices.candidate_word G completeG c x)).symm
  refine ⟨Nat.fromBitsLE v, ?_, ?_⟩
  · unfold bound
    rw [← HL]
    exact Nat.fromBitsLE_lt_pow_length v
  · have HW : word G (pair (pair c w) (BinaryNatCode.encode (Nat.fromBitsLE v))) = v := by
      unfold word
      rw [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, ← HL, ImplicitGraph.word_fromBitsLE]
    apply (language_packet F G projection _).mpr
    simpa only [candidate, pairFst_pair, pairSnd_pair, HW] using HE

attribute [local irreducible] language bound

theorem value_related_at (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w)
    (projects : ∀ i, (G.system c i).eval₂ (Int.castRingHom ℝ)
      ((SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c) = 0) :
    pair c (pair w (value F G projection (pair c w))) ∈ SquareSampleProjectionEquality.language F G projection := by
  have H := (BoundedChoice.witness (language F G projection) (pair c w) _
    (exists_candidate_at F G completeG projection c w hw projects)).2
  have P := (language_packet F G projection _).mp H
  simpa only [candidate, pairFst_pair, pairSnd_pair, value, index] using P

theorem value_valid_at (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w)
    (projects : ∀ i, (G.system c i).eval₂ (Int.castRingHom ℝ)
      ((SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c) = 0) :
    SquareSampleCompleteVertices.Valid G c (value F G projection (pair c w)) :=
  (SquareSampleProjectionEquality.valid F G projection c w _ (value_related_at F G completeG projection c w hw projects)).2

theorem value_point_at (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w)
    (projects : ∀ i, (G.system c i).eval₂ (Int.castRingHom ℝ)
      ((SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c) = 0) :
    (SquareSampleCompleteVertices.candidate G c (value F G projection (pair c w))
      (value_valid_at F G completeG projection c w hw projects)).val =
      (SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c :=
  ((SquareSampleProjectionEquality.packet F G completeG projection c w _ hw
    (value_valid_at F G completeG projection c w hw projects)).mp
    (value_related_at F G completeG projection c w hw projects)).symm

end LeanCanny.Encoding.SquareSampleProjectionChoice
