/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzTaskOrbitBounds
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Uniform native space evaluation of mixed determinant tasks

Local source-controller certificates and semantic contracts replace an assumed
space certificate for original coefficient answers. Ranked query closure and
common word/metadata/source bounds close the complete mixed-stage evaluator.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
open LeanCanny.Encoding LeanCanny.Encoding.Brackets LeanCanny.Computation
open Turing.MultiTapeTM

variable {F : ModularFamily} (a : ModularAccess F)
variable {S : Type} [Inhabited S] (source : RecursiveController.Controller (List Bool) S)
attribute [local irreducible] ModularAccess.factorValue ModularFamily.value PolynomialMoment.ModularFamily.value
  MatrixPower.Controller.halted MatrixPower.Controller.needsEntry payload isZero isDeterminant isFactor isMoment
  BinaryNat.div BinaryNat.mod BinaryNat.normalize BinaryNat.mul BinaryNat.add BinaryNat.sub BinaryNat.succ

def RankedQueries (sourceBudget : List Bool → ℕ) (tasks : List Bool → List Bool → Prop)
    (rank : List Bool → ℕ) : Prop :=
  ∀ root q t, tasks root q → t ≤ budget (F := F) sourceBudget q →
    (controller a source).halted (((controller a source).reference (answer a))^[t] ((controller a source).initial q)) = false →
    (controller a source).needs (((controller a source).reference (answer a))^[t] ((controller a source).initial q)) = true →
    tasks root ((controller a source).query
      (((controller a source).reference (answer a))^[t] ((controller a source).initial q))) ∧
    rank ((controller a source).query
      (((controller a source).reference (answer a))^[t] ((controller a source).initial q))) < rank q

theorem ranked_queries_closed (sourceBudget : List Bool → ℕ) (tasks : List Bool → List Bool → Prop)
    (rank : List Bool → ℕ) (h : RankedQueries a source sourceBudget tasks rank) :
    QueriesClosed a source sourceBudget tasks :=
  fun root q t hq ht hh hn => (h root q t hq ht hh hn).1

/-- One native space machine handles a graph of determinant, factor, moment,
and source tasks with input-dependent depth. The internal state sizes and
logical budgets are derived. Clients supply ranked query closure and common
word, metadata, and source-controller bounds, not child execution clocks. -/
theorem evaluator {eS : S ↪ List Bool} (ha : a.ControlsPolyTime)
    (hC : source.Certificates (encQ := encBits) (encS := eS)) (sourceBudget : List Bool → ℕ)
    (hstop : ∀ p, source.halted ((source.reference (answer a))^[sourceBudget p] (source.initial p)) = true)
    (hcorrect : ∀ p t, source.halted ((source.reference (answer a))^[t] (source.initial p)) = true →
      source.output ((source.reference (answer a))^[t] (source.initial p)) = a.entry p)
    (tasks : List Bool → List Bool → Prop) (rank R K M V N : List Bool → ℕ)
    (hR : UnaryFn R) (hK : UnaryFn K) (hM : UnaryFn M) (hV : UnaryFn V) (hN : BinaryFn N)
    (hroot : ∀ q, tasks q q)
    (hrank : ∀ root q, tasks root q → rank q ≤ R root)
    (hword : ∀ root q, tasks root q → q.length ≤ K root)
    (hanswer : ∀ root q, tasks root q → (answer a q).length ≤ K root)
    (hgraph : RankedQueries a source sourceBudget tasks rank)
    (hdet : ∀ root q, tasks root q → SelectedDeterminant q → determinantFields (F := F) (payload q) ≤ M root)
    (hmoment : ∀ root q, tasks root q → SelectedMoment q → momentFields (F := F) (payload q) ≤ M root)
    (hsourceBudget : ∀ root q, tasks root q → SelectedSource q → sourceBudget (payload q) ≤ N root)
    (hsourceState : ∀ root q, tasks root q → SelectedSource q → ∀ t ≤ sourceBudget (payload q),
      (eS ((source.reference (answer a))^[t] (source.initial (payload q)))).length ≤ V root) :
    SpaceFunction (answer a) := by
  let commonBudget := fun root => N root + 2 ^ ((M root + 2) * M root + 1)
  let commonState := fun root => 32 + 2 * stageBound (K root) (M root) (V root) + (eS default).length
  have hn : BinaryFn commonBudget := hN.add (ComputableTidilyInPolyTime.binary_two_pow.comp
    (((hM.add (UnaryFn.const 2)).mul hM).add (UnaryFn.const 1)))
  have hstage : UnaryFn (fun root => stageBound (K root) (M root) (V root)) :=
    ((((UnaryFn.const 3).mul hK).add (UnaryFn.const 4)).add
      ((UnaryFn.const 64).mul ((hM.add (UnaryFn.const 1)).pow_const 2))).add hV
  have hb : UnaryFn commonState :=
    ((UnaryFn.const 32).add ((UnaryFn.const 2).mul hstage)).add (UnaryFn.const (eS default).length)
  have hb' : PolyBounded List.length commonState := by
    simpa only [encBits_apply, encUnary_apply, List.length_replicate] using hb.polyBounded_length
  have hclosed := ranked_queries_closed a source sourceBudget tasks rank hgraph
  refine ⟨(controller a source).evaluatorOfOrbits (certificates a ha source hC) (answer a) rank
    (budget (F := F) sourceBudget) tasks commonBudget R commonState hn hR hb' hroot
    (fun _ q _ => halted_after a source sourceBudget hstop q) ?_ ?_ ?_ hrank ?_ ?_ ?_⟩
  · intro root q hq
    exact budget_le sourceBudget q (M root) (N root) (hdet root q hq) (hmoment root q hq) (hsourceBudget root q hq)
  · intro root q t _ _ hh
    exact output_correct a source hcorrect q t hh
  · exact hgraph
  · intro root q hq
    change q.length ≤ commonState root
    have h := hword root q hq
    dsimp only [commonState, stageBound]
    omega
  · intro root q hq t ht
    exact orbit_length_bound a source eS sourceBudget tasks hclosed K M V hword hanswer hdet hmoment hsourceState root q hq t ht
  · intro root q hq
    have h := hanswer root q hq
    dsimp only [commonState, stageBound]
    omega

omit [Inhabited S] in
theorem determinant_reader (E : SpaceFunction (answer a)) : SpaceFunction F.value := by
  have h := E.precompose determinantTask (tag_FP false false)
  exact h.congr (funext (answer_determinant a))

omit [Inhabited S] in
theorem determinant_decider (E : SpaceFunction (answer a)) : SpaceDecider F.zeroLanguage := by
  let accept := fun w : List Bool => decide (w = [])
  have hc : (fun w => [accept w]) ∈ FP := (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  refine (determinant_reader a E).decider accept hc ?_
  intro c
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  have hz : MatrixPower.residueBits (0 : ZMod (F.modulus c)) = [] := by simp [MatrixPower.residueBits, BinaryNatCode.encode]
  change (F.matrix c).det.coeff (F.degree c) = 0 ↔ decide (F.value c = []) = true
  rw [decide_eq_true_eq]
  simp only [ModularFamily.value]
  rw [← hz, (MatrixPower.residueBits_injective (F.modulus c)).eq_iff]

end LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
