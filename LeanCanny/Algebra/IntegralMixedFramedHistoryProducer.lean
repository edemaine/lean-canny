/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryFamily
/-! # Earlier same-root queries recover the actual source-framed producer

The fresh producer key selects its literal older instruction prefix. Its state
is the creator state with the original source, retained sampler and bank.
Heterogeneous equality records only the root-indexed type transports; the
integer leading agreement is an ordinary equality.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryFamilyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical

private theorem prefix_congr (P : Parameters) (D : Plan P) (root root' : List Bool) (birth birth' : ℕ)
    (hr : root=root') (hb : birth=birth') :
    HEq (paddedPast (defaultInstruction P D root) (D.rules root) birth)
      (paddedPast (defaultInstruction P D root') (D.rules root') birth') := by
  cases hr
  cases hb
  rfl

theorem older_commands_key (P : Parameters) (D : Plan P) (H : Data P D) (key : List Bool)
    (i : Fin ((family P D H).birth key)) (context : List Bool) :
    HEq (older (commands P D key) i)
      (commands P D (keyAt (pairFst key) (prefixLength P key-1-i.val) context)) := by
  have HB : prefixLength P key-1-i.val≤P.cap (pairFst key)+1 :=
    (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (min_le_right _ _))
  have HO := heq_of_eq (paddedPast_older (defaultInstruction P D (pairFst key))
    (D.rules (pairFst key)) (prefixLength P key) ⟨i.val,i.isLt⟩)
  exact HO.trans (prefix_congr P D _ _ _ _
    (keyAt_root (pairFst key) (prefixLength P key-1-i.val) context).symm
    (keyAt_prefix P (pairFst key) (prefixLength P key-1-i.val) context HB).symm)

noncomputable def creatorState (P : Parameters) (D : Plan P) (root : List Bool)
    (cs : List (Instruction (P.ambient root) (P.width root))) (c : Instruction (P.ambient root) (P.width root))
    (h : cs.length≤P.cap root+1+1) :=
  reframe (run (initial P D root) cs h) c.source c.source_cap

private theorem creatorState_congr (P : Parameters) (D : Plan P) (root root' : List Bool)
    (cs : List (Instruction (P.ambient root) (P.width root)))
    (cs' : List (Instruction (P.ambient root') (P.width root')))
    (c : Instruction (P.ambient root) (P.width root)) (c' : Instruction (P.ambient root') (P.width root'))
    (h : cs.length≤P.cap root+1+1) (h' : cs'.length≤P.cap root'+1+1)
    (hr : root=root') (hs : HEq cs cs') (hc : HEq c c') :
    HEq (creatorState P D root cs c h) (creatorState P D root' cs' c' h') := by
  cases hr
  cases hs
  cases hc
  rfl

theorem creator_state_key (P : Parameters) (D : Plan P) (H : Data P D) (key : List Bool)
    (i : Fin ((family P D H).birth key)) (context : List Bool) :
    HEq (birthState (initial P D (pairFst key)) (commands P D key)
      (((family P D H).birth_bound key).trans (Nat.le_succ _)) i)
      ((family P D H).state (keyAt (pairFst key) (prefixLength P key-1-i.val) context)) := by
  exact creatorState_congr P D _ _ _ _ _ _ _ _
    (keyAt_root (pairFst key) (prefixLength P key-1-i.val) context).symm
    (older_commands_key P D H key i context) (origin_instruction_key P D H key i context)

noncomputable def creatorLeading (P : Parameters) (D : Plan P) (root : List Bool)
    (cs : List (Instruction (P.ambient root) (P.width root))) (c : Instruction (P.ambient root) (P.width root))
    (h : cs.length≤P.cap root+1) : ℤ :=
  IntegralMixedFullHistoryScript.leading (creatorState P D root cs c (h.trans (Nat.le_succ _))) h c.command

private theorem creatorLeading_congr (P : Parameters) (D : Plan P) (root root' : List Bool)
    (cs : List (Instruction (P.ambient root) (P.width root)))
    (cs' : List (Instruction (P.ambient root') (P.width root')))
    (c : Instruction (P.ambient root) (P.width root)) (c' : Instruction (P.ambient root') (P.width root'))
    (h : cs.length≤P.cap root+1) (h' : cs'.length≤P.cap root'+1)
    (hr : root=root') (hs : HEq cs cs') (hc : HEq c c') :
    creatorLeading P D root cs c h=creatorLeading P D root' cs' c' h' := by
  cases hr
  cases hs
  cases hc
  rfl

theorem retained_leading_key (P : Parameters) (D : Plan P) (H : Data P D) (key : List Bool)
    (i : Fin ((family P D H).birth key)) (context : List Bool) :
    ((family P D H).state key).bank.denominator i=
      IntegralMixedFullHistoryScript.leading
        ((family P D H).state (keyAt (pairFst key) (prefixLength P key-1-i.val) context))
        ((family P D H).birth_bound _) (instruction P D (keyAt (pairFst key) (prefixLength P key-1-i.val) context)).command := by
  exact (origin_denominator P D H key i).trans
    (creatorLeading_congr P D _ _ _ _ _ _ _ _
      (keyAt_root (pairFst key) (prefixLength P key-1-i.val) context).symm
      (older_commands_key P D H key i context) (origin_instruction_key P D H key i context))

end LeanCanny.Algebra.IntegralMixedFramedHistoryFamilyBits
