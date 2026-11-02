/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackData

/-! # Original header tables follow the complete projected root -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRootPullback
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

noncomputable def tables (T : IntegralMixedHeaderTablesBits.Tables) (project : List Bool→List Bool) :
    IntegralMixedHeaderTablesBits.Tables where
  commands := T.commands ∘ project
  fallback := T.fallback ∘ project

theorem tablesAccess (T : IntegralMixedHeaderTablesBits.Tables) (h : IntegralMixedHeaderTablesBits.Access T)
    (project : List Bool→List Bool) (hp : project∈FP) : IntegralMixedHeaderTablesBits.Access (tables T project) := by
  constructor
  · change (T.commands ∘ project)∈FP
    exact mem_FP_comp hp h.commands
  · change (T.fallback ∘ project)∈FP
    exact mem_FP_comp hp h.fallback

theorem fallbackIndex_key (P : Parameters) (project : List Bool→List Bool) (extra : List Bool→ℕ) (q : List Bool) :
    IntegralMixedHeaderTablesBits.fallbackIndex P (key project q)=
      IntegralMixedHeaderTablesBits.fallbackIndex (parameters P project extra) q := by
  unfold IntegralMixedHeaderTablesBits.fallbackIndex
  have HC : pairSnd (pairSnd (key project q))=pairSnd (pairSnd q) :=
    congrArg pairSnd (pairSnd_pair _ _)
  exact congrArg₂ (fun b c=>5*b+min (Nat.fromBitsLE c) 4) (key_prefix P project extra q) HC

theorem represents (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (h : IntegralMixedFramedHeaderBits.Represents P D H T)
    (project : List Bool→List Bool) (extra : List Bool→ℕ) :
    IntegralMixedFramedHeaderBits.Represents (parameters P project extra) (plan P D project extra)
      (data P D H project extra) (tables T project) where
  commands root := h.commands (project root)
  fallback q := by
    have HH := h.fallback (key project q)
    have HL := congrArg₂ (fun root i=>WordList.get (T.fallback root) i)
      (key_root project q).symm (fallbackIndex_key P project extra q).symm
    exact HL.trans (HH.trans (congrArg IntegralMixedCommandHeaderBits.encode (fallback_header P D H project extra q)).symm)

end LeanCanny.Algebra.IntegralMixedFramedRootPullback
