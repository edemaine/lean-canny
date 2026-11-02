/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedFramedCompanionKeyTransport
public import LeanCanny.Algebra.PaddedIntegralRowSpace
public import LeanCanny.Algebra.IntegralMixedFramedRowOrigin

/-! # Actual creating-source cells for persistent framed rows

The entire source cell packages its arity, algebra, basis and polynomial.
Equality of original root, older instruction list and creating instruction
therefore transports the literal equation, rather than only its matrix value.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralGeneratorSource

def Source.cell (S : Source) (c : List Bool) : Source where
  arity _ := S.arity c
  width _ := S.width c
  carrier _ := S.carrier c
  ring _ := S.ring c
  nontrivial _ := S.nontrivial c
  basis _ := S.basis c
  polynomial _ := S.polynomial c
  degree _ := S.degree c

end LeanCanny.Algebra.PaddedIntegralGeneratorSource

namespace LeanCanny.Algebra.IntegralMixedFramedCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan commands instruction initial creatorState)
open IntegralMixedHistory IntegralMixedFramedHistoryScript PaddedIntegralGeneratorSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def creatorSource (P : Parameters) (D : Plan P) (root : List Bool)
    (cs : List (Instruction (P.ambient root) (P.width root)))
    (c : Instruction (P.ambient root) (P.width root)) (hc : cs.length≤P.cap root+1) : Source where
  arity _ := cs.length
  width _ := P.width root
  carrier _ := (creatorState P D root cs c (hc.trans (Nat.le_succ _))).sampler.scalarPrefix.carrier
  ring _ := (creatorState P D root cs c (hc.trans (Nat.le_succ _))).sampler.scalarPrefix.ring
  nontrivial _ := (creatorState P D root cs c (hc.trans (Nat.le_succ _))).sampler.scalarPrefix.nontrivial
  basis _ := (creatorState P D root cs c (hc.trans (Nat.le_succ _))).sampler.scalarPrefix.basis
  polynomial _ := IntegralMixedFullHistoryScript.polynomial (creatorState P D root cs c (hc.trans (Nat.le_succ _))) hc c.command
  degree _ := IntegralMixedFullHistoryScript.degree (creatorState P D root cs c (hc.trans (Nat.le_succ _))) hc c.command

theorem creatorSource_congr (P : Parameters) (D : Plan P) (root root' : List Bool)
    (cs : List (Instruction (P.ambient root) (P.width root)))
    (cs' : List (Instruction (P.ambient root') (P.width root')))
    (c : Instruction (P.ambient root) (P.width root))
    (c' : Instruction (P.ambient root') (P.width root'))
    (hc : cs.length≤P.cap root+1) (hc' : cs'.length≤P.cap root'+1)
    (hr : root=root') (hs : HEq cs cs') (hi : HEq c c') :
    creatorSource P D root cs c hc=creatorSource P D root' cs' c' hc' := by
  cases hr
  cases hs
  cases hi
  rfl

theorem source_cell (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) :
    (source P D H).cell key=creatorSource P D (pairFst key) (commands P D key) (instruction P D key)
      ((bank P D H).birth_bound key) := rfl

theorem source_creator_cell (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : Fin ((bank P D H).birth key)) (context : List Bool) :
    (source P D H).cell (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst key)
      (IntegralMixedFramedHistoryFamilyBits.prefixLength P key-1-i.val) context) =
    creatorSource P D (pairFst key) (older (commands P D key) i) (chosen (commands P D key) i)
      (older_bound (commands P D key) (((bank P D H).birth_bound key).trans (Nat.le_succ _)) i) := by
  rw [source_cell]
  exact creatorSource_congr P D _ _ _ _ _ _ _ _
    (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _)
    (IntegralMixedFramedHistoryFamilyBits.older_commands_key P D H key i context).symm
    (IntegralMixedFramedHistoryFamilyBits.origin_instruction_key P D H key i context).symm

end LeanCanny.Algebra.IntegralMixedFramedCompanionBits
