/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatCreating

/-! # Native metadata for actual creating queries

Only the original selected command's offset and degree are additional
metadata inputs. Query ranks, selected birth, row, column and modulus are
derived from the shared root script and the flat task fields.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem creating_older_length (F : Scripts) (q : List Bool)
    (h : IntegralCriticalHistoryTask.birth F.toParameters q < (F.rules (root q)).length) :
    (older (F.rules (root q)) (creatingIndex F q h)).length = IntegralCriticalHistoryTask.birth F.toParameters q := by
  rw [older_length]
  simp only [creatingIndex]
  omega

theorem generator_controls (F : Scripts) (a : Access F) (query : List Bool → List Bool) (hq : query ∈ FP)
    (h : ∀ c, IntegralCriticalHistoryTask.birth F.toParameters (query c) < (F.rules (root (query c))).length)
    (ho : BinaryFn (fun c => (chosen ((generatorQueries F query h).rules c) ((generatorQueries F query h).selected c)).offset.val))
    (hd : BinaryFn (fun c => (chosen ((generatorQueries F query h).rules c) ((generatorQueries F query h).selected c)).degree)) :
    IntegralCriticalScriptGeneratorBits.Controls (generatorQueries F query h) := by
  have HR : (fun c => root (query c)) ∈ FP := mem_FP_comp hq RankedHistoryTask.root_FP
  have HB : UnaryFn (fun c => IntegralCriticalHistoryTask.birth F.toParameters (query c)) :=
    (RankedHistoryTask.birth_unary _ (IntegralCriticalHistoryTask.birthCap_unary _ a.toAccess)).comp hq
  have HN : BinaryFn (fun c => count (IntegralCriticalHistoryTask.birth F.toParameters (query c) + 1) (F.width (root (query c)))) :=
    ((BinaryFn.const 2).powUnary (a.width.comp HR)).powUnary (HB.add (UnaryFn.const 1))
  refine {
    count := a.count.comp HR
    selected := ((BinaryFn.ofUnary (a.count.comp HR)).sub (BinaryFn.const 1)).sub (BinaryFn.ofUnary HB)
    width := a.width.comp HR
    ambient := a.ambient.comp HR
    offset := ho
    degree := hd
    modulus := (IntegralCriticalHistoryTask.modulus_binary _ a.toAccess).comp hq
    row := ?_
    col := ?_ }
  · apply BinaryFn.of_eq (BinaryFn.mod ((IntegralCriticalHistoryTask.get_binary _ a.toAccess .row).comp hq) HN)
    intro c
    change IntegralCriticalHistoryTask.get F.toParameters .row (query c) %
      count (IntegralCriticalHistoryTask.birth F.toParameters (query c) + 1) (F.width (root (query c))) = _
    simp only [generatorQueries, creating_older_length]
  · apply BinaryFn.of_eq (BinaryFn.mod ((IntegralCriticalHistoryTask.get_binary _ a.toAccess .col).comp hq) HN)
    intro c
    change IntegralCriticalHistoryTask.get F.toParameters .col (query c) %
      count (IntegralCriticalHistoryTask.birth F.toParameters (query c) + 1) (F.width (root (query c))) = _
    simp only [generatorQueries, creating_older_length]

end LeanCanny.Algebra.IntegralCriticalFlatHeightBits
