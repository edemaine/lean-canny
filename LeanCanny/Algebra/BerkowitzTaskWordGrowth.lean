/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzTaskReachability
public import LeanCanny.Algebra.BerkowitzTaskMetadata

/-! # Polynomial growth between successive source descents

Local metadata and native query output lengths give one monotone polynomial
envelope for internal requests. The stage priority strictly decreases on
these requests. If source requests rebuild a task of commonly bounded size,
four iterations of that envelope bound every reachable task word.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
open LeanCanny.Encoding LeanCanny.Computation Turing.MultiTapeTM

variable {F : ModularFamily} (a : ModularAccess F)
variable {S : Type} [Inhabited S] (source : RecursiveController.Controller (List Bool) S)

attribute [local irreducible] BinaryNat.normalize BinaryNat.add BinaryNat.sub BinaryNat.mul BinaryNat.succ
  BinaryNat.div BinaryNat.mod isZero isDeterminant isFactor isMoment payload
  ModularAccess.factorValue ModularFamily.value PolynomialMoment.ModularFamily.value

theorem internal_word_growth {eS : S ↪ List Bool} (ha : a.ControlsPolyTime)
    (hC : source.Certificates (encQ := encBits) (encS := eS)) (sourceBudget : List Bool → ℕ)
    (hanswer : ∀ root q, Reachable a source sourceBudget root q → (answer a q).length ≤ root.length + 1) :
    ∃ growth : ℕ → ℕ, Monotone growth ∧ (∀ n, n ≤ growth n) ∧
      (∀ K : List Bool → ℕ, UnaryFn K → UnaryFn (fun root => growth (K root))) ∧
      ∀ root q child n, Reachable a source sourceBudget root q → Requests a source sourceBudget q child →
        ¬SelectedSource q → q.length ≤ n → root.length ≤ n → child.length ≤ growth n := by
  obtain ⟨c, d, hmeta⟩ := ((determinantFields_unary a ha).add (momentFields_unary a ha)).polyBounded_length.exists_le
  obtain ⟨e, f, hquery⟩ := (certificates a ha source hC).query.polyBounded_length.exists_le
  let fields := fun n : ℕ => c * (n + 1) ^ d
  let stage := fun n : ℕ => 3 * n + 5 + 64 * (fields n + 1) ^ 2
  let growth := fun n : ℕ => n + e * (32 + 2 * stage n + (eS default).length + 1) ^ f
  refine ⟨growth, ?_, ?_, ?_, ?_⟩
  · intro n m hnm
    dsimp only [growth, stage, fields]
    gcongr
  · intro n
    exact Nat.le_add_right _ _
  · intro K hK
    have hfields := (UnaryFn.const c).mul ((hK.add (UnaryFn.const 1)).pow_const d)
    have hstage := (((UnaryFn.const 3).mul hK).add (UnaryFn.const 5)).add
      ((UnaryFn.const 64).mul ((hfields.add (UnaryFn.const 1)).pow_const 2))
    exact hK.add ((UnaryFn.const e).mul (((((UnaryFn.const 32).add ((UnaryFn.const 2).mul hstage)).add
      (UnaryFn.const (eS default).length)).add (UnaryFn.const 1)).pow_const f))
  · intro root q child n hq hstep hs hqn hrn
    obtain ⟨t, ht, _, hn, he⟩ := hstep
    have hp : (payload q).length ≤ n := by
      simp only [payload, List.length_drop]
      omega
    have hb : determinantFields (F := F) (payload q) ≤ fields n ∧ momentFields (F := F) (payload q) ≤ fields n := by
      have hm : determinantFields (F := F) (payload q) + momentFields (F := F) (payload q) ≤
          c * ((payload q).length + 1) ^ d := by
        simpa only [encBits_apply, encUnary_apply, List.length_replicate] using hmeta (payload q)
      have hg := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hp 1) d)
      dsimp only [fields]
      omega
    have hw : 64 * (determinantFields (F := F) (payload q) + 1) ^ 2 ≤ 64 * (fields n + 1) ^ 2 :=
      Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left (Nat.add_le_add_right hb.1 1) 2)
    have hm : 64 * (momentFields (F := F) (payload q) + 1) ^ 2 ≤ 64 * (fields n + 1) ^ 2 :=
      Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left (Nat.add_le_add_right hb.2 1) 2)
    have hstate := encoded_length_le a eS source (answer a) q t (stage n)
      (fun hz => by have hz' := requested_nonzero a source (answer a) q t hn; rw [hz] at hz'; contradiction)
      (fun _ => by
        have hd := DeterminantStage.state_length a factorTask (answer a) [] (answer_factor a) (answer_zero a) (payload q) t
        change _ ≤ 2 * (payload q).length + 2 + 64 * (determinantFields (F := F) (payload q) + 1) ^ 2 at hd
        dsimp only [stage]
        omega)
      (fun hf => by
        have hd := (FactorStage.program a sourceTask momentTask).state_length_of_bound (answer a) (payload q) t (root.length + 1)
          (factor_reply_bound a source sourceBudget (Reachable a source sourceBudget) (reachable_closed a source sourceBudget)
            (fun root => root.length + 1) hanswer root q hq hf)
        dsimp only [stage]
        omega)
      (fun _ => by
        have hd := MomentStage.state_length a sourceTask (answer a) [] (answer_source a) (answer_zero a) (payload q) t
        change _ ≤ 2 * (payload q).length + 2 + 64 * (momentFields (F := F) (payload q) + 1) ^ 2 at hd
        dsimp only [stage]
        omega)
      (fun hsource => False.elim (hs hsource))
    have hout := hquery (((controller a source).reference (answer a))^[t] ((controller a source).initial q))
    simp only [encBits_apply] at hout
    have hpow := Nat.mul_le_mul_left e (Nat.pow_le_pow_left (Nat.add_le_add_right hstate 1) f)
    rw [he]
    dsimp only [growth]
    omega

theorem bounded_words_of_source_reset (sourceBudget : List Bool → ℕ) (base : List Bool → ℕ)
    (hbase : ∀ root, root.length ≤ base root) (growth : ℕ → ℕ) (hext : ∀ n, n ≤ growth n)
    (hlocal : ∀ root q child n, Reachable a source sourceBudget root q → Requests a source sourceBudget q child →
      ¬SelectedSource q → q.length ≤ n → root.length ≤ n → child.length ≤ growth n)
    (hreset : ∀ root q child, Reachable a source sourceBudget root q → Requests a source sourceBudget q child →
      SelectedSource q → child.length ≤ base root)
    (root q : List Bool) (hq : Reachable a source sourceBudget root q) : q.length ≤ growth^[4] (base root) := by
  have hmono (b : ℕ) : Monotone (fun k : ℕ => growth^[k] b) :=
    monotone_nat_of_le_succ fun k => by rw [Function.iterate_succ_apply']; exact hext _
  have hb (k : ℕ) : base root ≤ growth^[k] (base root) := (hmono _ (Nat.zero_le k))
  have hi : q.length ≤ growth^[4 - priority q] (base root) := by
    induction hq with
    | refl => exact (hbase root).trans (hb _)
    | @tail q child hq hstep ih =>
      by_cases hs : SelectedSource q
      · exact (hreset root q child hq hstep hs).trans (hb _)
      · obtain ⟨t, ht, hh, hn, he⟩ := hstep
        have hp := internal_query_priority a source (answer a) q t hn hs
        rw [← he] at hp
        have hle : 4 - priority q + 1 ≤ 4 - priority child := by
          have hq' := priority_le q
          omega
        have hstep' : Requests a source sourceBudget q child := ⟨t, ht, hh, hn, he⟩
        have hlen := hlocal root q child (growth^[4 - priority q] (base root)) hq hstep' hs ih
          ((hbase root).trans (hb _))
        rw [← Function.iterate_succ_apply' growth (4 - priority q) (base root)] at hlen
        exact hlen.trans (hmono _ hle)
  exact hi.trans (hmono _ (Nat.sub_le _ _))

end LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
