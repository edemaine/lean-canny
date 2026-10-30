/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleProjectionEquality
public import LeanCanny.Computation.BoundedChoice

/-! # Computing complete labels for projected points

Bounded native search produces a target label with exactly the projected
source coordinates. A proof that the projection preserves the equations is
used for correctness only. The computation uses the two original sampler
access certificates and a native coordinate-index map.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleProjectionChoice
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def width (G : Inputs) (q : List Bool) : ℕ := SquareSampleCompleteVertices.width G (pairFst q)
theorem width_unary {G : Inputs} (hG : G.Access) : UnaryFn (width G) :=
  (SquareSampleCompleteVertices.width_unary hG).comp pairFst_mem_FP
noncomputable def word (G : Inputs) (r : List Bool) : List Bool :=
  ImplicitGraph.word (width G (pairFst r)) (Nat.fromBitsLE (pairSnd r))
theorem word_FP {G : Inputs} (hG : G.Access) : word G ∈ FP :=
  ImplicitGraph.word_computable ((width_unary hG).comp pairFst_mem_FP) (BinaryFn.fromBits pairSnd_mem_FP)
noncomputable def candidate (G : Inputs) (r : List Bool) : List Bool :=
  pair (pairFst (pairFst r)) (pair (pairSnd (pairFst r)) (word G r))
theorem candidate_FP {G : Inputs} (hG : G.Access) : candidate G ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) (word_FP hG))

attribute [local irreducible] word width SquareSampleProjectionEquality.language

noncomputable def language (F G : Inputs) (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c)) : Language :=
  candidate G ⁻¹' SquareSampleProjectionEquality.language F G projection
theorem decider {F G : Inputs} (hF : F.Access) (hG : G.Access)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (hi : UnaryFn (fun z => (SquareSampleProjectedThom.coordinate F G projection (pairFst z) (pairSnd z)).val)) :
    SpaceDecider (language F G projection) :=
  (SquareSampleProjectionEquality.decider hF hG projection hi).precompose (candidate G) (candidate_FP hG)
theorem language_packet (F G : Inputs) (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c)) (r : List Bool) :
    r ∈ language F G projection ↔ candidate G r ∈ SquareSampleProjectionEquality.language F G projection := Iff.rfl

noncomputable def bound (G : Inputs) (q : List Bool) : ℕ := 2 ^ width G q
theorem bound_binary {G : Inputs} (hG : G.Access) : BinaryFn (bound G) :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow.comp (width_unary hG)

theorem exists_candidate (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (projects : ∀ c (x : SquareSampleComplete.Roots F c),
      ∀ i, (G.system c i).eval₂ (Int.castRingHom ℝ) (x.val ∘ projection c) = 0)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    ∃ n < bound G (pair c w), pair (pair c w) (BinaryNatCode.encode n) ∈ language F G projection := by
  let x : SquareSampleComplete.Roots G c :=
    ⟨(SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c,
      projects c (SquareSampleCompleteVertices.candidate F c w hw)⟩
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

noncomputable def index (F G : Inputs) (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c)) (q : List Bool) : ℕ :=
  BoundedChoice.search (language F G projection) q (bound G q) - 1
noncomputable def value (F G : Inputs) (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c)) (q : List Bool) : List Bool :=
  word G (pair q (BinaryNatCode.encode (index F G projection q)))

theorem evaluator {F G : Inputs} (hF : F.Access) (hG : G.Access)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (hi : UnaryFn (fun z => (SquareSampleProjectedThom.coordinate F G projection (pairFst z) (pairSnd z)).val)) :
    SpaceFunction (value F G projection) := by
  have E := BoundedChoice.evaluator (decider hF hG projection hi) (fun q => BinaryNatCode.encode (bound G q)) (bound_binary hG).bits_mem_FP
  exact (E.withInput.postcompose (word G) (word_FP hG)).congr (funext fun q => by
    simp only [value, index, Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits])

attribute [local irreducible] language bound

theorem value_related (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (projects : ∀ c (x : SquareSampleComplete.Roots F c),
      ∀ i, (G.system c i).eval₂ (Int.castRingHom ℝ) (x.val ∘ projection c) = 0)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    pair c (pair w (value F G projection (pair c w))) ∈ SquareSampleProjectionEquality.language F G projection := by
  have H := (BoundedChoice.witness (language F G projection) (pair c w) _ (exists_candidate F G completeG projection projects c w hw)).2
  have P := (language_packet F G projection _).mp H
  simpa only [candidate, pairFst_pair, pairSnd_pair, value, index] using P

theorem value_valid (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (projects : ∀ c (x : SquareSampleComplete.Roots F c),
      ∀ i, (G.system c i).eval₂ (Int.castRingHom ℝ) (x.val ∘ projection c) = 0)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    SquareSampleCompleteVertices.Valid G c (value F G projection (pair c w)) :=
  (SquareSampleProjectionEquality.valid F G projection c w _ (value_related F G completeG projection projects c w hw)).2

theorem value_point (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (projects : ∀ c (x : SquareSampleComplete.Roots F c),
      ∀ i, (G.system c i).eval₂ (Int.castRingHom ℝ) (x.val ∘ projection c) = 0)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    (SquareSampleCompleteVertices.candidate G c (value F G projection (pair c w))
      (value_valid F G completeG projection projects c w hw)).val =
        (SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c :=
  ((SquareSampleProjectionEquality.packet F G completeG projection c w _ hw (value_valid F G completeG projection projects c w hw)).mp
    (value_related F G completeG projection projects c w hw)).symm

end LeanCanny.Encoding.SquareSampleProjectionChoice
