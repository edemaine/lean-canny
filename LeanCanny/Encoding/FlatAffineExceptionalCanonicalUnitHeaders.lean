/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCanonicalUnitHeaderFP
public import LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitData
public import LeanCanny.Encoding.FlatAffineExceptionalIntegerHeaders
/-! # Native full header tables for the actual canonical changing-source plan -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitHeaders
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (keyAt prefixLength)
open FlatAffineFullSourceTower (Inputs)
open FlatAffineExceptionalCanonicalUnitPlan (records code count seedCount selectedCode)
open scoped Classical

noncomputable def laterTable (P : Parameters) (root : List Bool) :=
  WordList.encode ((List.range (count root)).map fun i => IntegralMixedCommandHeaderBits.encode
    (IntegralMixedCanonicalUnitHeaderBits.command (P.ambient root) (P.degree root) (code root i)))
noncomputable def commands (P : Parameters) (F : Inputs) (root : List Bool) :=
  FlatAffineExceptionalIntegerHeaders.prepend^[seedCount F root] (laterTable P root)

def laterWord (z : List Bool) := code (pairFst z) (pairSnd z).length

theorem laterWord_FP : laterWord ∈ FP := by
  have HP := mem_FP_pair (mem_FP_comp pairFst_mem_FP FlatAffineExceptionalCanonicalUnitPlan.records_FP)
    (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP
  exact mem_FP_of_eq (mem_FP_comp HP WordList.reader_FP) (fun z => by
    simp only [Function.comp_apply,WordList.reader,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]; rfl)

noncomputable def laterEntry (P : Parameters) (z : List Bool) :=
  pair (IntegralMixedCommandHeaderBits.encode (IntegralMixedCanonicalUnitHeaderBits.command
    (P.ambient (pairFst z)) (P.degree (pairFst z)) (laterWord z))) []

theorem laterTable_FP (P : Parameters) (a : Access P) : laterTable P ∈ FP := by
  have HE : laterEntry P ∈ FP := mem_FP_pair (IntegralMixedCanonicalUnitHeaderBits.command_FP
    (a.ambient.comp pairFst_mem_FP) (a.degree.comp pairFst_mem_FP) laterWord laterWord_FP) (constFn_mem_FP [])
  apply mem_FP_of_eq (flatMap_range_mem_FP HE (FlatAffineExceptionalCanonicalUnitPlan.count_unary.replicate_mem_FP true))
  intro root
  simp only [laterTable,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    laterEntry,laterWord,pairFst_pair,pairSnd_pair,List.length_replicate]

theorem commands_FP (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access) : commands P F ∈ FP :=
  FlatAffineExceptionalIntegerHeaders.prepend_native _ (FlatAffineExceptionalCanonicalUnitPlan.seedCount_unary hF) _ (laterTable_FP P a)

def fallbackKey (root : List Bool) (i : ℕ) := keyAt root (i/5) (BinaryNatCode.encode (i%5))
noncomputable def fallback (P : Parameters) (F : Inputs) (root : List Bool) :=
  WordList.encode ((List.range (5*(P.cap root+2))).map fun i => IntegralMixedCommandHeaderBits.encode
    (IntegralMixedCanonicalUnitHeaderBits.selection (P.ambient root) (P.degree root) (selectedCode P F (fallbackKey root i))))

def fallbackPacket (z : List Bool) := fallbackKey (pairFst z) (pairSnd z).length

theorem fallbackPacket_FP : fallbackPacket ∈ FP := by
  have HI := BinaryFn.ofUnary UnaryFn.index
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair (HI.div (BinaryFn.const 5)).bits_mem_FP (HI.mod (BinaryFn.const 5)).bits_mem_FP)

noncomputable def fallbackEntry (P : Parameters) (F : Inputs) (z : List Bool) :=
  pair (IntegralMixedCommandHeaderBits.encode (IntegralMixedCanonicalUnitHeaderBits.selection
    (P.ambient (pairFst z)) (P.degree (pairFst z)) (selectedCode P F (fallbackPacket z)))) []

theorem fallback_FP (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access) : fallback P F ∈ FP := by
  have HW := mem_FP_comp fallbackPacket_FP (FlatAffineExceptionalCanonicalUnitPlan.selectedCode_FP P a hF)
  have HE : fallbackEntry P F ∈ FP := mem_FP_pair (IntegralMixedCanonicalUnitHeaderBits.selection_FP
    (a.ambient.comp pairFst_mem_FP) (a.degree.comp pairFst_mem_FP) _ HW) (constFn_mem_FP [])
  have HN := ((UnaryFn.const 5).mul (a.cap.add (UnaryFn.const 2))).replicate_mem_FP true
  apply mem_FP_of_eq (flatMap_range_mem_FP HE HN)
  intro root
  simp only [fallback,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    fallbackEntry,fallbackPacket,pairFst_pair,pairSnd_pair,List.length_replicate]

noncomputable def tables (P : Parameters) (F : Inputs) : IntegralMixedHeaderTablesBits.Tables :=
  ⟨commands P F,fallback P F⟩
theorem native (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access) : IntegralMixedHeaderTablesBits.Access (tables P F) :=
  ⟨commands_FP P a hF,fallback_FP P a hF⟩

end LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitHeaders
