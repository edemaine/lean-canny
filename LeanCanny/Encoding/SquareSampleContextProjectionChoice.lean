/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleContextProjectionEquality
public import LeanCanny.Computation.BoundedChoice

/-! # Computing projected labels in a different native context

Bounded native search produces a target label with exactly the projected
source coordinates. A proof that the projection preserves the equations is
used for correctness only. The computation uses the two original sampler
access certificates and a native coordinate-index map.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleContextProjectionChoice
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def width (G : Inputs) (target : List Bool → List Bool) (q : List Bool) : ℕ := SquareSampleCompleteVertices.width G (target (pairFst q))
theorem width_unary {G : Inputs} (hG : G.Access) {target : List Bool → List Bool} (ht : target ∈ FP) : UnaryFn (width G target) :=
  (SquareSampleCompleteVertices.width_unary hG).comp (mem_FP_comp pairFst_mem_FP ht)
noncomputable def word (G : Inputs) (target : List Bool → List Bool) (r : List Bool) : List Bool :=
  ImplicitGraph.word (width G target (pairFst r)) (Nat.fromBitsLE (pairSnd r))
theorem word_FP {G : Inputs} (hG : G.Access) {target : List Bool → List Bool} (ht : target ∈ FP) : word G target ∈ FP :=
  ImplicitGraph.word_computable ((width_unary hG ht).comp pairFst_mem_FP) (BinaryFn.fromBits pairSnd_mem_FP)
noncomputable def candidate (G : Inputs) (target : List Bool → List Bool) (r : List Bool) : List Bool :=
  pair (pairFst (pairFst r)) (pair (pairSnd (pairFst r)) (word G target r))
theorem candidate_FP {G : Inputs} (hG : G.Access) {target : List Bool → List Bool} (ht : target ∈ FP) : candidate G target ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) (word_FP hG ht))

attribute [local irreducible] word width SquareSampleContextProjectionEquality.language

noncomputable def language (F G : Inputs) (target : List Bool → List Bool) (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c)) : Language :=
  candidate G target ⁻¹' SquareSampleContextProjectionEquality.language F G target projection
theorem decider {F G : Inputs} (hF : F.Access) (hG : G.Access)
    {target : List Bool → List Bool} (ht : target ∈ FP)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (hi : UnaryFn (fun z => (SquareSampleContextThom.coordinate F G target projection (pairFst z) (pairSnd z)).val)) :
    SpaceDecider (language F G target projection) :=
  (SquareSampleContextProjectionEquality.decider hF hG ht projection hi).precompose (candidate G target) (candidate_FP hG ht)
theorem language_packet (F G : Inputs) (target : List Bool → List Bool) (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c)) (r : List Bool) :
    r ∈ language F G target projection ↔ candidate G target r ∈ SquareSampleContextProjectionEquality.language F G target projection := Iff.rfl

noncomputable def bound (G : Inputs) (target : List Bool → List Bool) (q : List Bool) : ℕ := 2 ^ width G target q
theorem bound_binary {G : Inputs} (hG : G.Access) {target : List Bool → List Bool} (ht : target ∈ FP) : BinaryFn (bound G target) :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow.comp (width_unary hG ht)

theorem exists_candidate (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (target : List Bool → List Bool)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (projects : ∀ c (x : SquareSampleComplete.Roots F c),
      ∀ i, (G.system (target c) i).eval₂ (Int.castRingHom ℝ) (x.val ∘ projection c) = 0)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    ∃ n < bound G target (pair c w), pair (pair c w) (BinaryNatCode.encode n) ∈ language F G target projection := by
  let x : SquareSampleComplete.Roots G (target c) :=
    ⟨(SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c,
      projects c (SquareSampleCompleteVertices.candidate F c w hw)⟩
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

noncomputable def index (F G : Inputs) (target : List Bool → List Bool) (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c)) (q : List Bool) : ℕ :=
  BoundedChoice.search (language F G target projection) q (bound G target q) - 1
noncomputable def value (F G : Inputs) (target : List Bool → List Bool) (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c)) (q : List Bool) : List Bool :=
  word G target (pair q (BinaryNatCode.encode (index F G target projection q)))

theorem evaluator {F G : Inputs} (hF : F.Access) (hG : G.Access)
    {target : List Bool → List Bool} (ht : target ∈ FP)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (hi : UnaryFn (fun z => (SquareSampleContextThom.coordinate F G target projection (pairFst z) (pairSnd z)).val)) :
    SpaceFunction (value F G target projection) := by
  have E := BoundedChoice.evaluator (decider hF hG ht projection hi) (fun q => BinaryNatCode.encode (bound G target q)) (bound_binary hG ht).bits_mem_FP
  exact (E.withInput.postcompose (word G target) (word_FP hG ht)).congr (funext fun q => by
    simp only [value, index, Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits])

attribute [local irreducible] language bound

theorem value_related (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (target : List Bool → List Bool)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (projects : ∀ c (x : SquareSampleComplete.Roots F c),
      ∀ i, (G.system (target c) i).eval₂ (Int.castRingHom ℝ) (x.val ∘ projection c) = 0)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    pair c (pair w (value F G target projection (pair c w))) ∈ SquareSampleContextProjectionEquality.language F G target projection := by
  have H := (BoundedChoice.witness (language F G target projection) (pair c w) _ (exists_candidate F G completeG target projection projects c w hw)).2
  have P := (language_packet F G target projection _).mp H
  simpa only [candidate, pairFst_pair, pairSnd_pair, value, index] using P

theorem value_valid (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (target : List Bool → List Bool)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (projects : ∀ c (x : SquareSampleComplete.Roots F c),
      ∀ i, (G.system (target c) i).eval₂ (Int.castRingHom ℝ) (x.val ∘ projection c) = 0)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    SquareSampleCompleteVertices.Valid G (target c) (value F G target projection (pair c w)) :=
  (SquareSampleContextProjectionEquality.valid F G target projection c w _ (value_related F G completeG target projection projects c w hw)).2

theorem value_point (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (target : List Bool → List Bool)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (projects : ∀ c (x : SquareSampleComplete.Roots F c),
      ∀ i, (G.system (target c) i).eval₂ (Int.castRingHom ℝ) (x.val ∘ projection c) = 0)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    (SquareSampleCompleteVertices.candidate G (target c) (value F G target projection (pair c w))
      (value_valid F G completeG target projection projects c w hw)).val =
        (SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c :=
  ((SquareSampleContextProjectionEquality.packet F G completeG target projection c w _ hw (value_valid F G completeG target projection projects c w hw)).mp
    (value_related F G completeG target projection projects c w hw)).symm

end LeanCanny.Encoding.SquareSampleContextProjectionChoice
