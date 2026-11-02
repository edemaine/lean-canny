/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRootPullback
public import LeanCanny.Algebra.IntegralMixedFramedIntegerSource
public import LeanCanny.Algebra.IntegralMixedFramedHeaders

/-! # Dependent creating-instruction transport through the original-root map

A root and birth normal form separates dependent instruction types from key
encoding. Equal root/birth metadata gives the actual same instruction, not a
reinterpretation of its polynomial under another source.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRootPullback
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedHistoryScript (Instruction chronological)
open IntegralMixedHistory
open scoped Classical

noncomputable def instructionAt (P : Parameters) (D : Plan P) (root : List Bool) (birth : ℕ) :
    Instruction (P.ambient root) (P.width root) :=
  (chronological (D.rules root) birth).getD (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root)

theorem instructionAt_congr (P : Parameters) (D : Plan P) (r s : List Bool) (i j : ℕ)
    (hr : r=s) (hb : i=j) : HEq (instructionAt P D r i) (instructionAt P D s j) := by
  cases hr
  cases hb
  rfl

theorem instructionAt_pullback (P : Parameters) (D : Plan P) (project : List Bool→List Bool)
    (extra : List Bool→ℕ) (root : List Bool) (birth : ℕ) :
    instructionAt (parameters P project extra) (plan P D project extra) root birth=
      instructionAt P D (project root) birth := rfl

theorem instruction_heq (P : Parameters) (D : Plan P) (project : List Bool→List Bool)
    (extra : List Bool→ℕ) (q : List Bool) :
    HEq (IntegralMixedFramedHistoryFamilyBits.instruction (parameters P project extra) (plan P D project extra) q)
      (IntegralMixedFramedHistoryFamilyBits.instruction P D (key project q)) := by
  exact (heq_of_eq (instructionAt_pullback P D project extra (pairFst q)
    (IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters P project extra) q))).trans
      (instructionAt_congr P D _ _ _ _ (key_root project q).symm (key_prefix P project extra q).symm)

theorem instruction_read {α : Type} (read : ∀ n B, Instruction n B→α)
    {n n' B B' : ℕ} (x : Instruction n B) (y : Instruction n' B')
    (hn : n=n') (hB : B=B') (hxy : HEq x y) : read n B x=read n' B' y := by
  cases hn
  cases hB
  have H : x=y := eq_of_heq hxy
  cases H
  rfl

theorem instruction_read_heq {α : ℕ→ℕ→Type} (read : ∀ n B, Instruction n B→α n B)
    {n n' B B' : ℕ} (x : Instruction n B) (y : Instruction n' B')
    (hn : n=n') (hB : B=B') (hxy : HEq x y) : HEq (read n B x) (read n' B' y) := by
  cases hn
  cases hB
  have H : x=y := eq_of_heq hxy
  cases H
  rfl

theorem instruction_source (P : Parameters) (D : Plan P) (project : List Bool→List Bool)
    (extra : List Bool→ℕ) (q : List Bool) :
    HEq (IntegralMixedFramedHistoryFamilyBits.instruction (parameters P project extra) (plan P D project extra) q).source
      (IntegralMixedFramedHistoryFamilyBits.instruction P D (key project q)).source :=
  instruction_read_heq (fun _ _ I=>I.source) _ _
    (congrArg P.ambient (key_root project q).symm) (congrArg P.width (key_root project q).symm)
    (instruction_heq P D project extra q)

theorem instruction_degree (P : Parameters) (D : Plan P) (project : List Bool→List Bool)
    (extra : List Bool→ℕ) (q : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.instruction (parameters P project extra) (plan P D project extra) q).source.degree=
      (IntegralMixedFramedHistoryFamilyBits.instruction P D (key project q)).source.degree :=
  instruction_read (fun _ _ I=>I.source.degree) _ _
    (congrArg P.ambient (key_root project q).symm) (congrArg P.width (key_root project q).symm)
    (instruction_heq P D project extra q)

theorem instruction_leading (P : Parameters) (D : Plan P) (project : List Bool→List Bool)
    (extra : List Bool→ℕ) (q : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.instruction (parameters P project extra) (plan P D project extra) q).source.leading=
      (IntegralMixedFramedHistoryFamilyBits.instruction P D (key project q)).source.leading :=
  instruction_read (fun _ _ I=>I.source.leading) _ _
    (congrArg P.ambient (key_root project q).symm) (congrArg P.width (key_root project q).symm)
    (instruction_heq P D project extra q)

noncomputable def transportSelection {n m : ℕ} {P : SpatialSource n} {Q : SpatialSource m}
    (hn : n=m) (hPQ : HEq P Q) (s : IntegralMixedFullHistoryFamilyBits.Selection Q) :
    IntegralMixedFullHistoryFamilyBits.Selection P := by
  cases hn
  have H : P=Q := eq_of_heq hPQ
  cases H
  exact s

theorem transportSelection_header {n m : ℕ} {P : SpatialSource n} {Q : SpatialSource m}
    (hn : n=m) (hPQ : HEq P Q) (s : IntegralMixedFullHistoryFamilyBits.Selection Q) :
    IntegralMixedCommandHeaderBits.selection (transportSelection hn hPQ s)=IntegralMixedCommandHeaderBits.selection s := by
  cases hn
  have H : P=Q := eq_of_heq hPQ
  cases H
  rfl

end LeanCanny.Algebra.IntegralMixedFramedRootPullback
