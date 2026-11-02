/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedHeaders
public import LeanCanny.Encoding.FlatAffineExceptionalIntegerHeaders
public import LeanCanny.Algebra.IntegralMixedHeaderPhysicalMetadata
/-! # Exact native header tables for the actual total supplied-mask Data -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open FlatAffineFullSourceTower (Inputs)
open IntegralMixedCommandHeaderBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def repeatHeader (n : ℕ) (w : List Bool) := WordList.encode (List.replicate n w)

theorem repeatHeader_eq (n : ℕ) (w : List Bool) : repeatHeader n w = (List.range n).flatMap (fun _ => pair w []) := by
  have H : (List.range n).map (fun _ => w) = List.replicate n w := by simp only [List.map_const', List.length_range]
  rw [repeatHeader, ← H, FrozenCoordinatePermutationBits.encode_flatMap, List.flatMap_map]

theorem repeatHeader_FP (n : List Bool → ℕ) (hn : UnaryFn n) (w : List Bool → List Bool) (hw : w ∈ FP) :
    (fun root => repeatHeader (n root) (w root)) ∈ FP := by
  have HG := mem_FP_pair (mem_FP_comp pairFst_mem_FP hw) (constFn_mem_FP [])
  have H := flatMap_range_mem_FP HG hn.mem_FP
  exact mem_FP_of_eq H (fun root => by simp only [List.length_replicate, Function.comp_apply, pairFst_pair, repeatHeader_eq])

noncomputable def tables (P : Parameters) {F : Inputs} (D : Description P F) : IntegralMixedHeaderTablesBits.Tables where
  commands root := FlatAffineExceptionalIntegerHeaders.prepend^[(D.base.rules root).length]
    (pair (encode (coarseHeader D.source root)) (pair (encode (cutHeader P D root)) []))
  fallback root := repeatHeader (5 * (P.cap root + 2)) (encode (cutHeader P D root))

theorem tables_access (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access) (D : Description P F)
    (hS : FlatAffineExceptionalSuppliedRules.Access D.source) (hn : UnaryFn (fun root => (D.base.rules root).length))
    (hK : KindAccess P D) : IntegralMixedHeaderTablesBits.Access (tables P D) where
  commands := FlatAffineExceptionalIntegerHeaders.prepend_native _ hn _
    (mem_FP_pair (coarseHeader_readers hF D.source hS).writer_FP
      (mem_FP_pair (cutHeader_readers P hF D hS hK).writer_FP (constFn_mem_FP [])))
  fallback := repeatHeader_FP _ ((UnaryFn.const 5).mul (a.cap.add (UnaryFn.const 2))) _
    (cutHeader_readers P hF D hS hK).writer_FP

theorem base_headerList (P : Parameters) {F : Inputs} (D : Description P F) (root : List Bool) :
    (D.base.rules root).reverse.map (fun c => encode (command c)) = List.replicate (D.base.rules root).length (encode zero) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_reverse, List.length_replicate]
  · intro i hi hj
    rw [List.getElem_map, List.getElem_replicate]
    have hidx : i < (D.base.rules root).reverse.length := by simpa only [List.length_map] using hi
    have HI := D.integers root ((D.base.rules root).reverse[i]'hidx)
      (List.mem_reverse.mp (List.getElem_mem hidx))
    generalize ((D.base.rules root).reverse[i]'hidx) = c at HI ⊢
    cases c with
    | integer => rfl
    | critical => cases HI
    | cut => cases HI

theorem commands_table (P : Parameters) {F : Inputs} (D : Description P F) (root : List Bool) :
    (tables P D).commands root = words ((backend P D).rules root) := by
  change FlatAffineExceptionalIntegerHeaders.prepend^[(D.base.rules root).length]
    (WordList.encode [encode (coarseHeader D.source root), encode (cutHeader P D root)]) = _
  rw [FlatAffineExceptionalIntegerHeaders.prepend_encode]
  unfold words backend data
  simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
  rw [base_headerList, ← coarseHeader_command P D root, ← cutHeader_command P D root, List.append_assoc]
  rfl

theorem tables_represent (P : Parameters) {F : Inputs} (D : Description P F) :
    IntegralMixedHeaderTablesBits.Represents (parameters P D.source) (backend P D) (tables P D) where
  commands := commands_table P D
  fallback := by
    intro key
    change WordList.get (repeatHeader (5 * (P.cap (pairFst key) + 2)) (encode (cutHeader P D (pairFst key))))
      (IntegralMixedHeaderTablesBits.fallbackIndex (parameters P D.source) key) = _
    rw [repeatHeader, WordList.get_encode, List.getElem?_eq_getElem (by
      simpa only [List.length_replicate, parameters] using IntegralMixedHeaderTablesBits.fallbackIndex_lt (parameters P D.source) key), Option.getD_some, List.getElem_replicate]
    rfl

theorem fullMetadata (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access) (D : Description P F)
    (hS : FlatAffineExceptionalSuppliedRules.Access D.source) (hn : UnaryFn (fun root => (D.base.rules root).length))
    (hK : KindAccess P D) : IntegralMixedFullHistoryFamilyBits.Metadata (parameters P D.source) (backend P D) :=
  IntegralMixedHeaderTablesBits.fullMetadata (parameters P D.source) (parameters_access P a hF D.source hS)
    (backend P D) (tables P D) (tables_access P a hF D hS hn hK) (tables_represent P D)

theorem physicalMetadata (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access) (D : Description P F)
    (hS : FlatAffineExceptionalSuppliedRules.Access D.source) (hn : UnaryFn (fun root => (D.base.rules root).length))
    (hK : KindAccess P D) : IntegralMixedPhysicalQueryBits.InputMetadata (IntegralMixedFullScalarBits.physicalFamily (parameters P D.source) (backend P D)) :=
  IntegralMixedHeaderTablesBits.physicalInputMetadata (parameters P D.source) (parameters_access P a hF D.source hS)
    (backend P D) (tables P D) (tables_access P a hF D hS hn hK) (tables_represent P D)
end LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
