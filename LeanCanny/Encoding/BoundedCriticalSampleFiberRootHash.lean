/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberRankBasis
public import LeanCanny.Algebra.FiniteFeatureSeparator

/-! # Short separating labels from a selected fiber-sign basis

Selected record values lie in {-1,0,1} and distinguish every fiber root.
One bounded prime and parameter give distinct residue labels; the associated
integer weighted sums also have polynomial binary width. This module proves
existence and bounds. `BoundedCriticalSampleFiberHashChoice` supplies native parameter
selection, and `BoundedCriticalSampleFiberSignatureRead` supplies pointwise readout.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberRootHash
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedAlgebraicSlice (Family)
open BoundedCriticalSampleSlice BoundedCriticalSampleFiberRankBasis
open scoped Classical BigOperators

noncomputable def record (P : Readers) (F : Family) (c : List Bool) (r : Fin (RootCount.count P F c)) :
    List Bool := ImplicitGraph.word (BoundedAlgebraicFiberRecords.length F (BoundedCriticalSampleSlice.context c)) (chosen P F c r.val)

noncomputable def sign (P : Readers) (F : Family) (c : List Bool) (r : Fin (RootCount.count P F c))
    (x : BoundedCriticalSampleFiberRecordSpan.Root P F c) : SignType :=
  SparseFeatureRecords.value (Nat.succ_pos _) (BoundedAlgebraicFiberRecords.slots F (BoundedCriticalSampleSlice.context c))
    (BoundedAlgebraicFiberRecords.width F (BoundedCriticalSampleSlice.context c)) (BoundedCriticalSampleFiberThom.signature P F c x) (record P F c r)

theorem sign_cast (P : Readers) (F : Family) (c : List Bool) (r : Fin (RootCount.count P F c))
    (x : BoundedCriticalSampleFiberRecordSpan.Root P F c) : (sign P F c r x : ℚ) = selected P F c r x := by
  change SignType.castHom (sign P F c r x) = _
  rw [selected, Matrix.row, BoundedCriticalSampleFiberRecordSpan.matrix, BoundedCriticalSampleFiberRecordSpan.row_apply]
  unfold sign SparseFeatureRecords.value
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  change SignType.castHom (SparseFeatureRecords.factor _ _ _) = SparseFeatureRecords.factor _ _ _
  simp only [record, selectedIndex]
  unfold SparseFeatureRecords.factor
  split_ifs <;> rfl

noncomputable def integerVector (P : Readers) (F : Family) (c : List Bool) (x : BoundedCriticalSampleFiberRecordSpan.Root P F c)
    (r : Fin (RootCount.count P F c)) : ℤ := sign P F c r x

theorem vector_injective (P : Readers) (F : Family) (c : List Bool) : Function.Injective (integerVector P F c) := by
  intro x y he
  apply selected_separates P F c
  intro r
  rw [← sign_cast, ← sign_cast]
  have hr := congrFun he r
  have hc := congrArg (Int.castRingHom ℚ) hr
  simpa only [integerVector, Int.coe_castRingHom, SignType.intCast_cast] using hc

noncomputable def residue (P : Readers) (F : Family) (c : List Bool) (p : ℕ) (t : ZMod p)
    (x : BoundedCriticalSampleFiberRecordSpan.Root P F c) : ZMod p :=
  ∑ r, (integerVector P F c x r : ZMod p) * t ^ r.val

noncomputable def label (P : Readers) (F : Family) (c : List Bool) (p : ℕ) (t : ZMod p)
    (x : BoundedCriticalSampleFiberRecordSpan.Root P F c) : ℕ := (residue P F c p t x).val

noncomputable def integerValue (P : Readers) (F : Family) (c : List Bool) (p t : ℕ)
    (x : BoundedCriticalSampleFiberRecordSpan.Root P F c) : ℤ :=
  ∑ r : Fin (RootCount.count P F c), integerVector P F c x r * (t ^ r.val % p : ℕ)

theorem residue_integerValue (P : Readers) (F : Family) (c : List Bool) (p t : ℕ)
    (x : BoundedCriticalSampleFiberRecordSpan.Root P F c) :
    (integerValue P F c p t x : ZMod p) = residue P F c p (t : ZMod p) x := by
  simp only [integerValue, residue, Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_mod, Nat.cast_pow]

theorem integerValue_bound (P : Readers) (F : Family) (c : List Bool) {p : ℕ} (hp : 0 < p) (t : ℕ)
    (x : BoundedCriticalSampleFiberRecordSpan.Root P F c) :
    (integerValue P F c p t x).natAbs ≤ RootCount.count P F c * p := by
  apply (Int.natAbs_sum_le _ _).trans
  calc
    ∑ r : Fin (RootCount.count P F c),
        (integerVector P F c x r * (t ^ r.val % p : ℕ)).natAbs ≤ ∑ _r : Fin (RootCount.count P F c), p := by
      apply Finset.sum_le_sum
      intro r _
      have hs : (integerVector P F c x r).natAbs ≤ 1 := by
        unfold integerVector
        cases sign P F c r x <;> decide
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact (Nat.mul_le_mul_right _ hs).trans (by simpa only [one_mul] using (Nat.mod_lt (t ^ r.val) hp).le)
    _ = RootCount.count P F c * p := by simp

theorem integerValue_injective (P : Readers) (F : Family) (c : List Bool) (p t : ℕ)
    (h : Function.Injective (label P F c p (t : ZMod p))) : Function.Injective (integerValue P F c p t) := by
  intro x y he
  apply h
  have hc := congrArg (Int.castRingHom (ZMod p)) he
  have hr : residue P F c p (t : ZMod p) x = residue P F c p (t : ZMod p) y := by
    simpa only [Int.coe_castRingHom, residue_integerValue] using hc
  exact congrArg ZMod.val hr

theorem label_lt (P : Readers) (F : Family) (c : List Bool) {p : ℕ} (hp : 0 < p) (t : ZMod p)
    (x : BoundedCriticalSampleFiberRecordSpan.Root P F c) : label P F c p t x < p := by
  let : NeZero p := ⟨by omega⟩
  exact ZMod.val_lt _

theorem exists_labels (P : Readers) (F : Family) (c : List Bool) :
    ∃ p : ℕ, p.Prime ∧ RootCount.count P F c ^ 3 + 2 < p ∧
      p ≤ 2 * (RootCount.count P F c ^ 3 + 2) ∧
      ∃ t : ZMod p, Function.Injective (label P F c p t) := by
  have hb : ∀ x r, -1 ≤ integerVector P F c x r ∧ integerVector P F c x r ≤ 1 := by
    intro x r
    unfold integerVector
    cases sign P F c r x <;> decide
  obtain ⟨p, hp, hl, hu, t, ht⟩ := FiniteFeatureSeparator.exists_prime_parameter
    (integerVector P F c) (vector_injective P F c) hb
  have hcard : Fintype.card (BoundedCriticalSampleFiberRecordSpan.Root P F c) = RootCount.count P F c :=
    Fintype.card_coe _
  rw [hcard] at hl hu
  have he : RootCount.count P F c * RootCount.count P F c ^ 2 =
      RootCount.count P F c ^ 3 := by ring
  rw [he] at hl hu
  let : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨p, hp, hl, hu, t, ?_⟩
  intro x y hxy
  apply ht
  apply ZMod.val_injective
  exact hxy

noncomputable def bitWidth (F : Family) (c : List Bool) : ℕ :=
  3 * (F.degree (BoundedCriticalSampleSlice.context c)).size + 4

theorem bitWidth_unary {F : Family} (A : F.Access) : UnaryFn (bitWidth F) :=
  ((UnaryFn.const 3).mul ((BoundedAlgebraicFiberRecords.size_unary A).comp BoundedCriticalSampleSlice.context_FP)).add (UnaryFn.const 4)

noncomputable def valueBits (F : Family) (c : List Bool) : ℕ :=
  (F.degree (BoundedCriticalSampleSlice.context c)).size + bitWidth F c

theorem valueBits_unary {F : Family} (A : F.Access) : UnaryFn (valueBits F) :=
  ((BoundedAlgebraicFiberRecords.size_unary A).comp BoundedCriticalSampleSlice.context_FP).add (bitWidth_unary A)

theorem integerValue_bits (P : Readers) (F : Family) (c : List Bool) {p : ℕ} (hp : 0 < p)
    (hs : p < 2 ^ bitWidth F c) (t : ℕ) (x : BoundedCriticalSampleFiberRecordSpan.Root P F c) :
    (integerValue P F c p t x).natAbs.size ≤ valueBits F c := by
  have hn : RootCount.count P F c ≤ 2 ^ (F.degree (BoundedCriticalSampleSlice.context c)).size :=
    (BoundedCriticalSampleFiberRoot.count_le_degree P F c).trans (Nat.lt_size_self (F.degree (BoundedCriticalSampleSlice.context c))).le
  have hb := (integerValue_bound P F c hp t x).trans (Nat.mul_le_mul_right p hn)
  have hl := Nat.mul_lt_mul_of_pos_left hs (Nat.two_pow_pos ((F.degree (BoundedCriticalSampleSlice.context c)).size))
  rw [← pow_add] at hl
  exact Nat.size_le.mpr (hb.trans_lt hl)

theorem exists_short_labels (P : Readers) (F : Family) (c : List Bool) :
    ∃ p t : ℕ, p.Prime ∧ p < 2 ^ bitWidth F c ∧ t < p ∧
      Function.Injective (label P F c p (t : ZMod p)) := by
  obtain ⟨p, hp, _, hu, t, ht⟩ := exists_labels P F c
  let : NeZero p := ⟨hp.ne_zero⟩
  have hN : RootCount.count P F c ≤ 2 ^ (F.degree (BoundedCriticalSampleSlice.context c)).size :=
    (BoundedCriticalSampleFiberRoot.count_le_degree P F c).trans (Nat.lt_size_self (F.degree (BoundedCriticalSampleSlice.context c))).le
  have hpow := Nat.pow_le_pow_left hN 3
  have he : (2 ^ (F.degree (BoundedCriticalSampleSlice.context c)).size) ^ 3 =
      2 ^ (3 * (F.degree (BoundedCriticalSampleSlice.context c)).size) := by rw [← pow_mul, Nat.mul_comm]
  rw [he] at hpow
  have hpos := Nat.one_le_two_pow (n := 3 * (F.degree (BoundedCriticalSampleSlice.context c)).size)
  have hwidth : 2 ^ bitWidth F c = 16 * 2 ^ (3 * (F.degree (BoundedCriticalSampleSlice.context c)).size) := by
    rw [bitWidth, pow_add, Nat.mul_comm]
    rfl
  have hsmall : p < 2 ^ bitWidth F c := by rw [hwidth]; omega
  refine ⟨p, t.val, hp, hsmall, ZMod.val_lt t, ?_⟩
  simpa only [ZMod.natCast_zmod_val] using ht

end LeanCanny.Encoding.BoundedCriticalSampleFiberRootHash
