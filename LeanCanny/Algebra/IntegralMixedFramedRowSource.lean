/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedFramedCompanionCreatorSource

/-! # A retained row reads the literal source at its original creating key

The full arity, algebra, basis and polynomial are transported together. The
result connects the persistent canonical row to the same source consumed by
the native monic-row reader, without a coefficient agreement premise.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralGeneratorSource

theorem Source.cell_row (S : Source) (cap : List Bool→ℕ) (key : List Bool) :
    HEq (PaddedIntegralRowBits.polynomial S cap key)
      (PaddedIntegralRowBits.polynomial (S.cell key) (fun _=>cap key) []) := by
  rfl

end LeanCanny.Algebra.PaddedIntegralGeneratorSource

namespace LeanCanny.Algebra.IntegralMixedFramedCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan commands instruction initial creatorState)
open IntegralMixedHistory IntegralMixedFramedHistoryScript PaddedIntegralGeneratorSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem creatorSource_row (P : Parameters) (D : Plan P) (root : List Bool)
    (cs : List (Instruction (P.ambient root) (P.width root)))
    (c : Instruction (P.ambient root) (P.width root)) (hc : cs.length≤P.cap root+1) :
    PaddedIntegralRowBits.polynomial (creatorSource P D root cs c hc) (fun _=>P.cap root+1) [] =
    (UniformIntegralPrefix.step (creatorState P D root cs c (hc.trans (Nat.le_succ _))).sampler.scalarPrefix
      hc (Nat.two_pow_pos (P.width root))
      (IntegralMixedFullHistoryScript.polynomial (creatorState P D root cs c (hc.trans (Nat.le_succ _))) hc c.command)
      (IntegralMixedFullHistoryScript.degree (creatorState P D root cs c (hc.trans (Nat.le_succ _))) hc c.command)).rows 0 := by
  rfl

private theorem row_congr (S T : Source) (s t : ℕ) (hS : S=T) (hs : s=t) :
    HEq (PaddedIntegralRowBits.polynomial S (fun _=>s) [])
      (PaddedIntegralRowBits.polynomial T (fun _=>t) []) := by
  cases hS
  cases hs
  rfl

theorem source_creator_row (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : Fin ((bank P D H).birth key)) (context : List Bool) :
    HEq (PaddedIntegralRowBits.polynomial (source P D H) (fun key=>P.cap (pairFst key)+1)
      (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst key)
        (IntegralMixedFramedHistoryFamilyBits.prefixLength P key-1-i.val) context))
    ((birthPrefix (initial P D (pairFst key)) (commands P D key)
      (((bank P D H).birth_bound key).trans (Nat.le_succ _)) i).rows 0) := by
  let k := IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst key)
    (IntegralMixedFramedHistoryFamilyBits.prefixLength P key-1-i.val) context
  have HS := source_creator_cell P D H key i context
  have HR : P.cap (pairFst k)+1=P.cap (pairFst key)+1 := congrArg (fun root=>P.cap root+1)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _)
  have H1 := (source P D H).cell_row (fun key=>P.cap (pairFst key)+1) k
  have H2 := row_congr _ _ _ _ HS HR
  have H3 := creatorSource_row P D (pairFst key) (older (commands P D key) i) (chosen (commands P D key) i)
    (older_bound (commands P D key) (((bank P D H).birth_bound key).trans (Nat.le_succ _)) i)
  exact H1.trans (H2.trans (heq_of_eq H3))

end LeanCanny.Algebra.IntegralMixedFramedCompanionBits
