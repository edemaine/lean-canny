/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCommandHeader
/-! # Native field and chronological reads in encoded mixed headers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCommandHeaderBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

 theorem get_FP (i : ℕ) : (fun w => WordList.get w i) ∈ FP := by
  have H := mem_FP_comp (mem_FP_pair id_mem_FP (constFn_mem_FP (BinaryNatCode.encode i))) WordList.reader_FP
  exact mem_FP_of_eq H (fun w => WordList.reader_packet w i)

structure Readers (headers : List Bool → Header) : Prop where
  context : BinaryFn (fun q => (headers q).context)
  coordinate : BinaryFn (fun q => (headers q).coordinate)
  offset : BinaryFn (fun q => (headers q).offset)
  objective : BinaryFn (fun q => (headers q).objective)
  degree : BinaryFn (fun q => (headers q).degree)
  choice : BinaryFn (fun q => (headers q).choice)
  rawTag : BinaryFn (fun q => (headers q).rawTag)

theorem decode_readers : Readers decode :=
  ⟨BinaryFn.fromBits (get_FP 0), BinaryFn.fromBits (get_FP 1), BinaryFn.fromBits (get_FP 2),
    BinaryFn.fromBits (get_FP 3), BinaryFn.fromBits (get_FP 4), BinaryFn.fromBits (get_FP 5),
    BinaryFn.fromBits (get_FP 6)⟩

theorem Readers.comp {headers : List Bool → Header} (h : Readers headers)
    (f : List Bool → List Bool) (hf : f ∈ FP) : Readers (fun q => headers (f q)) :=
  ⟨h.context.comp hf, h.coordinate.comp hf, h.offset.comp hf, h.objective.comp hf, h.degree.comp hf, h.choice.comp hf, h.rawTag.comp hf⟩

theorem Readers.choose (p : List Bool → Prop) [∀ q, Decidable (p q)]
    {left right : List Bool → Header} (hp : FPPred p) (hl : Readers left) (hr : Readers right) :
    Readers (fun q => if p q then left q else right q) :=
  ⟨(BinaryFn.ite hp hl.context hr.context).of_eq (fun q => by split_ifs <;> rfl),
    (BinaryFn.ite hp hl.coordinate hr.coordinate).of_eq (fun q => by split_ifs <;> rfl),
    (BinaryFn.ite hp hl.offset hr.offset).of_eq (fun q => by split_ifs <;> rfl),
    (BinaryFn.ite hp hl.objective hr.objective).of_eq (fun q => by split_ifs <;> rfl),
    (BinaryFn.ite hp hl.degree hr.degree).of_eq (fun q => by split_ifs <;> rfl),
    (BinaryFn.ite hp hl.choice hr.choice).of_eq (fun q => by split_ifs <;> rfl),
    (BinaryFn.ite hp hl.rawTag hr.rawTag).of_eq (fun q => by split_ifs <;> rfl)⟩

def fetched (table : List Bool → List Bool) (index : List Bool → ℕ) (q : List Bool) : List Bool :=
  WordList.get (table q) (index q)
theorem fetched_FP (table : List Bool → List Bool) (index : List Bool → ℕ)
    (ht : table ∈ FP) (hi : BinaryFn index) : fetched table index ∈ FP := by
  have H := mem_FP_comp (mem_FP_pair ht hi.bits_mem_FP) WordList.reader_FP
  exact mem_FP_of_eq H (fun q => WordList.reader_packet (table q) (index q))

theorem lookup_readers (table : List Bool → List Bool) (index : List Bool → ℕ)
    (ht : table ∈ FP) (hi : BinaryFn index) : Readers (fun q => lookup (table q) (index q)) :=
  decode_readers.comp (fetched table index) (fetched_FP table index ht hi)

def isCut (h : Header) : Prop := 2 ≤ h.context ∧ h.context ≤ 4
instance (h : Header) : Decidable (isCut h) := inferInstanceAs (Decidable (_ ∧ _))
theorem isCut_FP (headers : List Bool → Header) (h : Readers headers) : FPPred (fun q => isCut (headers q)) :=
  ((BinaryFn.const 2).le h.context).and (h.context.le (BinaryFn.const 4))

def table (headers : List Header) : List Bool := WordList.encode (headers.map encode)

theorem table_length (headers : List Header) (W : ℕ)
    (h : ∀ h ∈ headers, h.context.size ≤ W ∧ h.coordinate.size ≤ W ∧ h.offset.size ≤ W ∧
      h.objective.size ≤ W ∧ h.degree.size ≤ W ∧ h.choice.size ≤ W ∧ h.rawTag.size ≤ W) :
    (table headers).length ≤ (28 * W + 30) * headers.length := by
  have H := WordList.length_le (headers.map encode) ((2 * W + 2) * 7) (by
    intro w hw
    obtain ⟨h1, hh1, rfl⟩ := List.mem_map.mp hw
    have HH := h h1 hh1
    exact encode_length h1 W HH.1 HH.2.1 HH.2.2.1 HH.2.2.2.1 HH.2.2.2.2.1 HH.2.2.2.2.2.1 HH.2.2.2.2.2.2)
  simpa only [table, List.length_map, show 2 * ((2 * W + 2) * 7) + 2 = 28 * W + 30 by omega] using H

end LeanCanny.Algebra.IntegralMixedCommandHeaderBits
