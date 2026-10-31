/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleContextProjectionChoice

/-! # Native context conversion at a validated source record

The computation is the existing native bounded search. Correctness needs
only the current guarded source point to satisfy the target equations.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleContextProjectionChoice
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] word width SquareSampleContextProjectionEquality.language

theorem exists_candidate_at (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (target : List Bool → List Bool)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w)
    (projects : ∀ i, (G.system (target c) i).eval₂ (Int.castRingHom ℝ)
      ((SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c) = 0) :
    ∃ n < bound G target (pair c w), pair (pair c w) (BinaryNatCode.encode n) ∈ language F G target projection := by
  let x : SquareSampleComplete.Roots G (target c) :=
    ⟨(SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c,
      projects⟩
  let v := SquareSampleCompleteVertices.word G completeG (target c) x
  have hv := SquareSampleCompleteVertices.word_valid G completeG (target c) x
  have HL : v.length = width G target (pair c w) := by
    unfold width
    rw [pairFst_pair]
    exact (Classical.choose hv).1
  have HE := (SquareSampleContextProjectionEquality.packet F G completeG target projection c w v hw hv).mpr
    (congrArg (fun z : SquareSampleComplete.Roots G (target c) => z.val)
      (SquareSampleCompleteVertices.candidate_word G completeG (target c) x)).symm
  refine ⟨Nat.fromBitsLE v, ?_, ?_⟩
  · unfold bound
    rw [← HL]
    exact Nat.fromBitsLE_lt_pow_length v
  · have HW : word G target (pair (pair c w) (BinaryNatCode.encode (Nat.fromBitsLE v))) = v := by
      unfold word
      rw [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, ← HL, ImplicitGraph.word_fromBitsLE]
    apply (language_packet F G target projection _).mpr
    simpa only [candidate, pairFst_pair, pairSnd_pair, HW] using HE

attribute [local irreducible] language bound

theorem value_related_at (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (target : List Bool → List Bool)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w)
    (projects : ∀ i, (G.system (target c) i).eval₂ (Int.castRingHom ℝ)
      ((SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c) = 0) :
    pair c (pair w (value F G target projection (pair c w))) ∈
      SquareSampleContextProjectionEquality.language F G target projection := by
  have H := (BoundedChoice.witness (language F G target projection) (pair c w) _
    (exists_candidate_at F G completeG target projection c w hw projects)).2
  have P := (language_packet F G target projection _).mp H
  simpa only [candidate, pairFst_pair, pairSnd_pair, value, index] using P

theorem value_valid_at (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (target : List Bool → List Bool)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w)
    (projects : ∀ i, (G.system (target c) i).eval₂ (Int.castRingHom ℝ)
      ((SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c) = 0) :
    SquareSampleCompleteVertices.Valid G (target c) (value F G target projection (pair c w)) :=
  (SquareSampleContextProjectionEquality.valid F G target projection c w _
    (value_related_at F G completeG target projection c w hw projects)).2

theorem value_point_at (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (target : List Bool → List Bool)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w)
    (projects : ∀ i, (G.system (target c) i).eval₂ (Int.castRingHom ℝ)
      ((SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c) = 0) :
    (SquareSampleCompleteVertices.candidate G (target c) (value F G target projection (pair c w))
      (value_valid_at F G completeG target projection c w hw projects)).val =
        (SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c :=
  ((SquareSampleContextProjectionEquality.packet F G completeG target projection c w _ hw
    (value_valid_at F G completeG target projection c w hw projects)).mp
      (value_related_at F G completeG target projection c w hw projects)).symm

end LeanCanny.Encoding.SquareSampleContextProjectionChoice
