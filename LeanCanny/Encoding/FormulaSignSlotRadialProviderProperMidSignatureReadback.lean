/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignature
public import LeanCanny.Encoding.IntegralMixedRoadmapMidSignatureLookup
/-! # Literal paired-signature lookups and their chronological bounds -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignature
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem signature_plain (n initial : ℕ) (q : List Bool) :
    signature n initial q=IntegralMixedRoadmapProperMidSignature.signature n initial q := rfl

theorem signature_bounded_before_clock (n initial : ℕ) (q : List Bool)
    (HK : IntegralMixedRoadmapProper.levelIndex q≤n)
    (HG : IntegralMixedChronologicalMidpointCode.Good n (IntegralMixedRoadmapProper.midBirth n initial q)
      (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapProper.producer false q)
      (IntegralMixedRoadmapProper.producer true q) (IntegralMixedRoadmapProper.levelIndex q+1)
      (IntegralMixedRoadmapProper.levelIndex q+1))
    (idx : ℕ) (hidx : idx<n+2) :
    Nat.fromBitsLE (WordList.get (signature n initial q) idx)<
      IntegralMixedRoadmapProper.midBirth n initial q+1+(n-IntegralMixedRoadmapProper.levelIndex q) := by
  rw [signature_plain]
  by_cases hi : idx<n+1
  · by_cases hf : idx<IntegralMixedRoadmapProper.levelIndex q
    · rw [IntegralMixedRoadmapProperMidSignature.signature_lookup_frozen _ _ _ idx hf HK]
      have HF := HG.1.2 idx (by rw [IntegralMixedRoadmapProper.labels_count];exact hf)
      omega
    · by_cases he : idx=IntegralMixedRoadmapProper.levelIndex q
      · rw [he,IntegralMixedRoadmapProperMidSignature.signature_lookup_left _ _ _ HK]
        have HL := HG.2.1
        omega
      · rw [IntegralMixedRoadmapProperMidSignature.signature_lookup_free _ _ _ idx (by omega) (by omega)]
        unfold IntegralMixedRoadmapProper.midProducer IntegralMixedRoadmapProper.midFirst
        omega
  · have HE : idx=n+1 := by omega
    rw [HE,IntegralMixedRoadmapProperMidSignature.signature_lookup_right]
    have HR := HG.2.2.1
    omega

theorem table_pair_count (a b : List Bool) :
    WordListRecords.count (table (pair a b))=FormulaSignSlotRadialProviderAtomic.dimension a+2 := by
  unfold table
  rw [IntegralMixedPhysicalPointSignatureComparison.pairs_count]
  simp only [left,pairFst_pair,Nat.add_assoc]

theorem table_pair_lookup (a b : List Bool) (i : Fin (FormulaSignSlotRadialProviderAtomic.dimension a+2)) :
    WordList.get (table (pair a b)) i.val=
      pair (WordList.get (ownSignature a) i.val) (WordList.get (ownSignature b) i.val) := by
  unfold table
  simp only [left,right,pairFst_pair,pairSnd_pair]
  exact IntegralMixedPhysicalPointSignatureComparison.pairs_lookup _ _ _ i

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignature
