/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SquareSampleCompleteSuffixSourceReindex
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
/-! # Source evaluation retains one literal terminal tuple under reindexing -/
@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteSuffixPolynomialTest
open LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def Source.evaluation {F : SquareSampleInput.Inputs} (S : Source F)
    (c d : List Bool) (z : ℕ→ℝ) : ℝ :=
  (S.polynomial c d).eval₂ (Int.castRingHom ℝ) (fun i=>z (i.val+S.newer c d))

theorem Source.reindex_evaluation {F G : SquareSampleInput.Inputs} (S : Source F)
    (index : List Bool→List Bool) (hc : ∀ c d,F.count (pairFst (index (pair c d)))=G.count c)
    (c d : List Bool) (z : ℕ→ℝ) :
    (S.reindex index hc).evaluation c d z=S.evaluation (pairFst (index (pair c d))) (pairSnd (index (pair c d))) z := rfl

theorem packet_evaluation {F : SquareSampleInput.Inputs} (S : Source F) (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid F c w) :
    SquareSampleCompleteIndexedPolynomialTest.value F (test S) (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign (S.evaluation c d (IntegralMixedFramedBankObservation.extend
        (SquareSampleCompleteVertices.candidate F c w hv).val))) := by
  rw [packet S c w d hv]
  congr 2
  unfold Source.evaluation
  apply congrArg ((S.polynomial c d).eval₂ (Int.castRingHom ℝ))
  funext i
  have H:=Fin.isLt (Fin.cast (S.dimension c d) (FixedWidthSuffixLiftBits.shift (S.newer c d) i))
  change S.newer c d+i.val<F.count c at H
  simp only [IntegralMixedFramedBankObservation.extend,Nat.add_comm i.val,dite_eq_left H]
  rfl

end LeanCanny.Encoding.SquareSampleCompleteSuffixPolynomialTest
