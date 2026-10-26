/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalProjection
public import Mathlib.Data.Finset.Sort

/-! # Ordered finite labels for the actual critical samples

Labels are the binary indices of the selected projections among the distinct
real roots of the concrete projection polynomial. Extraneous polynomial roots
remain invalid labels; every sample has exactly one label. This file proves
boundedness and exact decoding, not a native label-query evaluator.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalLabels
open LeanCanny.Computation LeanCanny.Geometry LeanCanny.ETR BoundedFullWriter
open scoped Classical

noncomputable def rootSet (P : Readers) (c : List Bool) : Finset ℝ :=
  ((BoundedCriticalProjection.polynomial P c).map (Int.castRingHom ℝ)).roots.toFinset

theorem mapped_ne_zero (P : Readers) (c : List Bool) :
    (BoundedCriticalProjection.polynomial P c).map (Int.castRingHom ℝ) ≠ 0 :=
  (Polynomial.map_ne_zero_iff Int.cast_injective).mpr (BoundedCriticalProjection.polynomial_ne_zero P c)

noncomputable def projectedRoot (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    {t // t ∈ rootSet P c} :=
  ⟨BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) c x.val, by
    rw [rootSet, Multiset.mem_toFinset, Polynomial.mem_roots (mapped_ne_zero P c)]
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    exact BoundedCriticalProjection.polynomial_eval_sample P c x⟩

noncomputable def rank (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) : ℕ :=
  ((rootSet P c).orderIsoOfFin rfl).symm (projectedRoot P c x) |>.val

theorem rootSet_card_le (P : Readers) (c : List Bool) :
    (rootSet P c).card ≤ 2 ^ BoundedCriticalProjection.labelWidth P c := by
  exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans
    (Polynomial.natDegree_map_le.trans (BoundedCriticalProjection.polynomial_degree P c)))

theorem rank_lt (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    rank P c x < 2 ^ BoundedCriticalProjection.labelWidth P c :=
  (((rootSet P c).orderIsoOfFin rfl).symm (projectedRoot P c x)).isLt.trans_le (rootSet_card_le P c)

theorem rank_injective (P : Readers) (c : List Bool) : Function.Injective (rank P c) := by
  intro a b he
  have hi : ((rootSet P c).orderIsoOfFin rfl).symm (projectedRoot P c a) =
      ((rootSet P c).orderIsoOfFin rfl).symm (projectedRoot P c b) := Fin.ext he
  exact BoundedCriticalSeparator.value_injective P c
    (congrArg Subtype.val (((rootSet P c).orderIsoOfFin rfl).symm.injective hi))

theorem rank_lt_iff (P : Readers) (c : List Bool) (a b : BoundedFullCriticalSamples.Samples P c) :
    rank P c a < rank P c b ↔
      BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) c a.val <
        BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) c b.val :=
  ((rootSet P c).orderIsoOfFin rfl).symm.lt_iff_lt

noncomputable def label (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) : List Bool :=
  ImplicitGraph.word (BoundedCriticalProjection.labelWidth P c) (rank P c x)

theorem label_length (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    (label P c x).length = BoundedCriticalProjection.labelWidth P c := ImplicitGraph.length_word _ _

theorem label_value (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    Nat.fromBitsLE (label P c x) = rank P c x := by
  have he := FixedWidthNatVector.decode_block 1 (BoundedCriticalProjection.labelWidth P c)
    (fun _ => rank P c x) 0 (by decide) (rank_lt P c x)
  simp only [Nat.zero_mul, List.drop_zero] at he
  change Nat.fromBitsLE ((label P c x).take (BoundedCriticalProjection.labelWidth P c)) = rank P c x at he
  simpa only [List.take_of_length_le (label_length P c x).le] using he

theorem label_injective (P : Readers) (c : List Bool) : Function.Injective (label P c) := by
  intro a b he
  apply rank_injective P c
  simpa only [label_value] using congrArg Nat.fromBitsLE he

def Valid (P : Readers) (c r : List Bool) : Prop := ∃ x, label P c x = r

noncomputable def decode (P : Readers) (c r : List Bool) : Option (BoundedFullCriticalSamples.Samples P c) :=
  if hr : Valid P c r then some (Classical.choose hr) else none

theorem decode_label (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    decode P c (label P c x) = some x := by
  rw [decode, dite_eq_left (show Valid P c (label P c x) from ⟨x, rfl⟩)]
  congr 1
  exact label_injective P c (Classical.choose_spec (show Valid P c (label P c x) from ⟨x, rfl⟩))

theorem decode_some_iff (P : Readers) (c r : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    decode P c r = some x ↔ label P c x = r := by
  constructor
  · intro he
    unfold decode at he
    split_ifs at he with hr
    · obtain rfl := Option.some.inj he
      exact Classical.choose_spec hr
  · rintro rfl
    exact decode_label P c x

theorem valid_length (P : Readers) (c r : List Bool) (hr : Valid P c r) :
    r.length = BoundedCriticalProjection.labelWidth P c := by
  obtain ⟨x, rfl⟩ := hr
  exact label_length P c x

/-- A raw label denotes a sample exactly when its binary value is that
sample's ordered projection-root index and its width is canonical. -/
theorem label_eq_iff (P : Readers) (c r : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    label P c x = r ↔ r.length = BoundedCriticalProjection.labelWidth P c ∧ Nat.fromBitsLE r = rank P c x := by
  constructor
  · rintro rfl
    exact ⟨label_length P c x, label_value P c x⟩
  · rintro ⟨hlen, hvalue⟩
    rw [label, ← hvalue, ← hlen, ImplicitGraph.word_fromBitsLE]

end LeanCanny.Encoding.BoundedCriticalLabels
