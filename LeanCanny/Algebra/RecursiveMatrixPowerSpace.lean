/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RecursiveMatrixPower
public import LeanCanny.Computation.ControllerRequests

/-! # One native space machine for input-dependent matrix-power nesting -/

@[expose] public section

namespace LeanCanny.Algebra.RecursiveMatrixPower.Source
open MatrixPower MatrixPower.Controller
open LeanCanny.Encoding LeanCanny.Computation
open Turing.MultiTapeTM

variable (S : Source)

structure Controls : Prop where
  metadata : S.access.ControlsPolyTime
  leaf : (fun q => [S.leaf q]) ∈ FP
  base : SpaceFunction S.base
  entryTask : S.entryTask ∈ FP

theorem initialEvaluator (h : S.Controls) : SpaceFunction S.initial := by
  have hd := doneBits_mem_FP id_mem_FP
  have E := SpaceFunction.branch S.leaf h.leaf
    ((h.base.postcompose doneBits hd).withInput)
    (SpaceFunction.ofFP _ (initialPacket_mem_FP h.metadata.exponent h.metadata.row h.metadata.col))
  exact E.congr (funext fun _ => rfl)

theorem certificates (h : S.Controls) : S.controller.Certificates (encQ := encBits) (encS := encBits) := by
  have ho := modularCallbacks_polyTime h.metadata.dimension h.metadata.modulus (constFn_mem_FP [])
  exact RecursiveStage.certificates S.ops ⟨ho.dimension, ho.zero, ho.one, ho.combine⟩
    S.initial S.entryTask (S.initialEvaluator h) h.entryTask

/-- Nested matrix-power tasks are evaluated uniformly. Only base tasks have an
answer certificate. Entry requests call lower-rank tasks, whose certificates are
constructed by this theorem. Task sizes and binary metadata lengths must have
common unary FP bounds in the original input; there is no fixed-depth parameter. -/
theorem evaluator (h : S.Controls) (rank : List Bool → ℕ) (tasks : List Bool → List Bool → Prop)
    (R K M : List Bool → ℕ) (hR : UnaryFn R) (hK : UnaryFn K) (hM : UnaryFn M)
    (hroot : ∀ q, tasks q q)
    (hrank : ∀ root q, tasks root q → rank q ≤ R root)
    (htask : ∀ root q, tasks root q → q.length ≤ K root)
    (hbase : ∀ root q, tasks root q → (S.base q).length ≤ K root)
    (hbits : ∀ root q, tasks root q →
      (S.family.dimension q).size + (S.family.exponent q).size + (S.family.modulus q).size ≤ M root)
    (hgraph : ∀ root q, tasks root q → S.leaf q = false → ∀ i j : Fin (S.family.dimension q),
      tasks root (S.entryTask (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) ∧
        rank (S.entryTask (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) < rank q) :
    SpaceFunction S.answer := by
  let N := fun root => 2 ^ ((M root + 2) * M root + 1)
  let B := fun root => 3 * K root + M root + 3 + 64 * (M root + 1) ^ 2
  have hN : ComputableTidilyInPolyTime N encBits encNat := ComputableTidilyInPolyTime.binary_two_pow.comp
    (((hM.add (UnaryFn.const 2)).mul hM).add (UnaryFn.const 1))
  have hB' : UnaryFn B :=
    ((((UnaryFn.const 3).mul hK).add hM).add (UnaryFn.const 3)).add
      ((UnaryFn.const 64).mul ((hM.add (UnaryFn.const 1)).pow_const 2))
  have hB : PolyBounded List.length B := by
    simpa only [encBits_apply, encUnary_apply, List.length_replicate] using hB'.polyBounded_length
  refine ⟨S.controller.evaluatorOfOrbits (S.certificates h) S.answer rank S.budget tasks N R B hN hR hB hroot
    (fun _ q _ => S.budget_halts q) ?_ ?_ ?_ hrank ?_ ?_ ?_⟩
  · intro root q hq
    have hbq : S.budget q ≤ work (S.family.dimension q) (S.family.exponent q).size (S.family.exponent q) + 1 := by
      unfold budget
      split_ifs <;> omega
    have hw := work_add_one_le_two_pow (S.family.dimension q) (S.family.exponent q).size (S.family.exponent q)
    have hm := hbits root q hq
    have he : ((S.family.dimension q).size + 2) * (S.family.exponent q).size + 1 ≤
        (M root + 2) * M root + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 1
    exact hbq.trans (hw.trans (Nat.pow_le_pow_right (by decide) he))
  · intro root q t _ _ hh
    exact S.output_correct q t hh
  · intro root q t hq _ _ hn
    obtain ⟨hl, i, j, hij⟩ := S.query_indices q t hn
    rw [show S.controller.initial q = S.initial q from rfl, hij]
    exact hgraph root q hq hl i j
  · intro root q hq
    change q.length ≤ B root
    have hq' := htask root q hq
    dsimp only [B]
    omega
  · intro root q hq t _
    change ((S.controller.reference S.answer)^[t] (S.initial q)).length ≤ B root
    have hs := S.state_length q t
    have hq' := htask root q hq
    have hb' := hbase root q hq
    have hm := hbits root q hq
    have hp := Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) 2)
    dsimp only [B]
    omega
  · intro root q hq
    have hm := hbits root q hq
    have hb' := hbase root q hq
    cases hl : S.leaf q with
    | true =>
      rw [← S.base_eq q hl]
      dsimp only [B]
      omega
    | false =>
      rw [← S.power_eq q hl]
      let : NeZero (S.family.modulus q) := ⟨S.family.modulus_ne_zero q⟩
      have hv := residueBits_length_le (S.family.modulus q)
        ((S.family.matrix q ^ S.family.exponent q) (S.family.row q) (S.family.col q))
      change (residueBits _).length ≤ B root
      dsimp only [B]
      omega

end LeanCanny.Algebra.RecursiveMatrixPower.Source
