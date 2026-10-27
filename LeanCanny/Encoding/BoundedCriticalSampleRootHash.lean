/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleRankBasis
public import LeanCanny.Algebra.FiniteFeatureSeparator

/-! # Bounded labels from the selected actual-sample sign basis

Every selected sparse monomial is a sign. A prime of size at most twice the
cube of the root count plus four admits a single parameter whose weighted
basis sums distinguish all actual sample roots. The label is one residue, not
the full derivative-sign vector. These are existence and size theorems;
native selection of parameters for an injective integer hash is supplied by
`BoundedCriticalSampleHashChoice`. `BoundedCriticalSampleHashEnumeration`
enumerates those integer values; individual sample sign queries remain required.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleRootHash
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedCriticalSampleRankBasis
open scoped Classical BigOperators

noncomputable def record (P : Readers) (c : List Bool) (r : Fin (BoundedCriticalSampleCount.count P c)) :
    List Bool := ImplicitGraph.word (BoundedCriticalSampleRecords.length P c) (chosen P c r.val)

noncomputable def sign (P : Readers) (c : List Bool) (r : Fin (BoundedCriticalSampleCount.count P c))
    (x : BoundedCriticalSampleRecordSpan.Root P c) : SignType :=
  SparseFeatureRecords.value (Nat.succ_pos _) (BoundedCriticalSampleRecords.slots P c)
    (BoundedCriticalSampleRecords.width P c) (BoundedCriticalSampleThom.signature P c x) (record P c r)

theorem sign_cast (P : Readers) (c : List Bool) (r : Fin (BoundedCriticalSampleCount.count P c))
    (x : BoundedCriticalSampleRecordSpan.Root P c) : (sign P c r x : ℚ) = selected P c r x := by
  change SignType.castHom (sign P c r x) = _
  rw [selected, Matrix.row, BoundedCriticalSampleRecordSpan.matrix, BoundedCriticalSampleRecordSpan.row_apply]
  unfold sign SparseFeatureRecords.value
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  change SignType.castHom (SparseFeatureRecords.factor _ _ _) = SparseFeatureRecords.factor _ _ _
  simp only [record, selectedIndex]
  unfold SparseFeatureRecords.factor
  split_ifs <;> rfl

noncomputable def integerVector (P : Readers) (c : List Bool) (x : BoundedCriticalSampleRecordSpan.Root P c)
    (r : Fin (BoundedCriticalSampleCount.count P c)) : ℤ := sign P c r x

theorem vector_injective (P : Readers) (c : List Bool) : Function.Injective (integerVector P c) := by
  intro x y he
  apply selected_separates P c
  intro r
  rw [← sign_cast, ← sign_cast]
  have hr := congrFun he r
  have hc := congrArg (Int.castRingHom ℚ) hr
  simpa only [integerVector, Int.coe_castRingHom, SignType.intCast_cast] using hc

noncomputable def residue (P : Readers) (c : List Bool) (p : ℕ) (t : ZMod p)
    (x : BoundedCriticalSampleRecordSpan.Root P c) : ZMod p :=
  ∑ r, (integerVector P c x r : ZMod p) * t ^ r.val

noncomputable def label (P : Readers) (c : List Bool) (p : ℕ) (t : ZMod p)
    (x : BoundedCriticalSampleRecordSpan.Root P c) : ℕ := (residue P c p t x).val

noncomputable def integerValue (P : Readers) (c : List Bool) (p t : ℕ)
    (x : BoundedCriticalSampleRecordSpan.Root P c) : ℤ :=
  ∑ r : Fin (BoundedCriticalSampleCount.count P c), integerVector P c x r * (t ^ r.val % p : ℕ)

theorem residue_integerValue (P : Readers) (c : List Bool) (p t : ℕ)
    (x : BoundedCriticalSampleRecordSpan.Root P c) :
    (integerValue P c p t x : ZMod p) = residue P c p (t : ZMod p) x := by
  simp only [integerValue, residue, Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_mod, Nat.cast_pow]

theorem integerValue_bound (P : Readers) (c : List Bool) {p : ℕ} (hp : 0 < p) (t : ℕ)
    (x : BoundedCriticalSampleRecordSpan.Root P c) :
    (integerValue P c p t x).natAbs ≤ BoundedCriticalSampleCount.count P c * p := by
  apply (Int.natAbs_sum_le _ _).trans
  calc
    ∑ r : Fin (BoundedCriticalSampleCount.count P c),
        (integerVector P c x r * (t ^ r.val % p : ℕ)).natAbs ≤ ∑ _r : Fin (BoundedCriticalSampleCount.count P c), p := by
      apply Finset.sum_le_sum
      intro r _
      have hs : (integerVector P c x r).natAbs ≤ 1 := by
        unfold integerVector
        cases sign P c r x <;> decide
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact (Nat.mul_le_mul_right _ hs).trans (by simpa only [one_mul] using (Nat.mod_lt (t ^ r.val) hp).le)
    _ = BoundedCriticalSampleCount.count P c * p := by simp

theorem integerValue_injective (P : Readers) (c : List Bool) (p t : ℕ)
    (h : Function.Injective (label P c p (t : ZMod p))) : Function.Injective (integerValue P c p t) := by
  intro x y he
  apply h
  have hc := congrArg (Int.castRingHom (ZMod p)) he
  have hr : residue P c p (t : ZMod p) x = residue P c p (t : ZMod p) y := by
    simpa only [Int.coe_castRingHom, residue_integerValue] using hc
  exact congrArg ZMod.val hr

theorem label_lt (P : Readers) (c : List Bool) {p : ℕ} (hp : 0 < p) (t : ZMod p)
    (x : BoundedCriticalSampleRecordSpan.Root P c) : label P c p t x < p := by
  let : NeZero p := ⟨by omega⟩
  exact ZMod.val_lt _

theorem exists_labels (P : Readers) (c : List Bool) :
    ∃ p : ℕ, p.Prime ∧ BoundedCriticalSampleCount.count P c ^ 3 + 2 < p ∧
      p ≤ 2 * (BoundedCriticalSampleCount.count P c ^ 3 + 2) ∧
      ∃ t : ZMod p, Function.Injective (label P c p t) := by
  have hb : ∀ x r, -1 ≤ integerVector P c x r ∧ integerVector P c x r ≤ 1 := by
    intro x r
    unfold integerVector
    cases sign P c r x <;> decide
  obtain ⟨p, hp, hl, hu, t, ht⟩ := FiniteFeatureSeparator.exists_prime_parameter
    (integerVector P c) (vector_injective P c) hb
  have hcard : Fintype.card (BoundedCriticalSampleRecordSpan.Root P c) = BoundedCriticalSampleCount.count P c :=
    (Fintype.card_coe _).trans (BoundedCriticalSampleLabels.rootSet_card P c)
  rw [hcard] at hl hu
  have he : BoundedCriticalSampleCount.count P c * BoundedCriticalSampleCount.count P c ^ 2 =
      BoundedCriticalSampleCount.count P c ^ 3 := by ring
  rw [he] at hl hu
  let : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨p, hp, hl, hu, t, ?_⟩
  intro x y hxy
  apply ht
  apply ZMod.val_injective
  exact hxy

noncomputable def bitWidth (P : Readers) (c : List Bool) : ℕ :=
  3 * BoundedFullCriticalSamples.labelWidth P c + 4

theorem bitWidth_unary {P : Readers} (h : P.PolyTime) : UnaryFn (bitWidth P) :=
  ((UnaryFn.const 3).mul (BoundedFullCriticalSamples.labelWidth_unary h)).add (UnaryFn.const 4)

noncomputable def valueBits (P : Readers) (c : List Bool) : ℕ :=
  BoundedFullCriticalSamples.labelWidth P c + bitWidth P c

theorem valueBits_unary {P : Readers} (h : P.PolyTime) : UnaryFn (valueBits P) :=
  (BoundedFullCriticalSamples.labelWidth_unary h).add (bitWidth_unary h)

theorem integerValue_bits (P : Readers) (c : List Bool) {p : ℕ} (hp : 0 < p)
    (hs : p < 2 ^ bitWidth P c) (t : ℕ) (x : BoundedCriticalSampleRecordSpan.Root P c) :
    (integerValue P c p t x).natAbs.size ≤ valueBits P c := by
  have hn : BoundedCriticalSampleCount.count P c ≤ 2 ^ BoundedFullCriticalSamples.labelWidth P c :=
    (BoundedFullCriticalSamples.finite_samples P c).2
  have hb := (integerValue_bound P c hp t x).trans (Nat.mul_le_mul_right p hn)
  have hl := Nat.mul_lt_mul_of_pos_left hs (Nat.two_pow_pos (BoundedFullCriticalSamples.labelWidth P c))
  rw [← pow_add] at hl
  exact Nat.size_le.mpr (hb.trans_lt hl)

theorem exists_short_labels (P : Readers) (c : List Bool) :
    ∃ p t : ℕ, p.Prime ∧ p < 2 ^ bitWidth P c ∧ t < p ∧
      Function.Injective (label P c p (t : ZMod p)) := by
  obtain ⟨p, hp, _, hu, t, ht⟩ := exists_labels P c
  let : NeZero p := ⟨hp.ne_zero⟩
  have hN : BoundedCriticalSampleCount.count P c ≤ 2 ^ BoundedFullCriticalSamples.labelWidth P c :=
    (BoundedFullCriticalSamples.finite_samples P c).2
  have hpow := Nat.pow_le_pow_left hN 3
  have he : (2 ^ BoundedFullCriticalSamples.labelWidth P c) ^ 3 =
      2 ^ (3 * BoundedFullCriticalSamples.labelWidth P c) := by rw [← pow_mul, Nat.mul_comm]
  rw [he] at hpow
  have hpos := Nat.one_le_two_pow (n := 3 * BoundedFullCriticalSamples.labelWidth P c)
  have hwidth : 2 ^ bitWidth P c = 16 * 2 ^ (3 * BoundedFullCriticalSamples.labelWidth P c) := by
    rw [bitWidth, pow_add, Nat.mul_comm]
    rfl
  have hsmall : p < 2 ^ bitWidth P c := by rw [hwidth]; omega
  refine ⟨p, t.val, hp, hsmall, ZMod.val_lt t, ?_⟩
  simpa only [ZMod.natCast_zmod_val] using ht

end LeanCanny.Encoding.BoundedCriticalSampleRootHash
