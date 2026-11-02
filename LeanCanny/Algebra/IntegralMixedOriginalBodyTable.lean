/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOriginalHeightCells
/-! # Chronological original-body tables supply scalar syntax access

The remaining frontend obligation is a total original table writer and its
literal agreement with creating rules, including padded and fallback words.
This interface does not charge a coefficient or interpreted-state evaluator.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOriginalRuleBodyBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask

def access_of_table (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (table : List Bool → List Bool) (index : List Bool → ℕ) (ht : table ∈ FP) (hi : BinaryFn index)
    (he : ∀ key, WordList.get (table key) (index key) = encode P D key) : Access P D where
  writer := IntegralMixedCommandHeaderBits.fetched table index
  writer_FP := IntegralMixedCommandHeaderBits.fetched_FP table index ht hi
  agrees := he

theorem controls_of_table (P : Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (D : IntegralMixedFullHistoryFamilyBits.Data P) (full : IntegralMixedFullHistoryFamilyBits.Metadata P D)
    (physical : IntegralMixedPhysicalQueryBits.InputMetadata (IntegralMixedFullScalarBits.physicalFamily P D))
    (table : List Bool → List Bool) (index : List Bool → ℕ) (ht : table ∈ FP) (hi : BinaryFn index)
    (he : ∀ key, WordList.get (table key) (index key) = encode P D key) : IntegralMixedFullScalarBits.Controls P D :=
  controls P a D full physical (access_of_table P D table index ht hi he)
end LeanCanny.Algebra.IntegralMixedOriginalRuleBodyBits
