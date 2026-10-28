/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleDirectionChoice
public import LeanCanny.Encoding.BoundedCriticalSampleChildSource

/-! # Passing selected common directions to child-sample queries

The child source expects a full normalized direction vector. Prepending a
single fixed-width field containing one adapts the common-direction record
without changing any of its free entries. The packet is generated in native
space; every child-source reader is polynomial time on this explicit packet.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleDirectionPacket
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR LeanCanny.ETR.ComplexCircuit MvPolynomial
open BoundedCriticalSampleDirectionChoice (Inputs width direction record)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair pairFst pairSnd

noncomputable def unitField (F : Inputs) : List Bool → List Bool :=
  FixedWidthQuery.repack (fun _ => 1) (fun _ => 1) (fun _ => 1) (width F) (fun _ => [true])

theorem unitField_FP {F : Inputs} (h : F.PolyTime) : unitField F ∈ FP :=
  FixedWidthQuery.repack_mem_FP (UnaryFn.const 1) (UnaryFn.const 1) (UnaryFn.const 1)
    (BoundedCriticalSampleDirectionChoice.width_unary h) (constFn_mem_FP [true])

theorem unitField_length (F : Inputs) (c : List Bool) : (unitField F c).length = width F c := by
  simp only [unitField, FixedWidthQuery.repack_length, one_mul]

theorem unitField_value (F : Inputs) (c : List Bool) : Nat.fromBitsLE (unitField F c) = 1 := by
  have H := FixedWidthQuery.coordinate_repack_of_width_le (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (width F) (fun _ => [true]) c
    (BoundedCriticalSampleDirectionChoice.width_pos F c) 0 (by decide)
  have hb : FixedWidthQuery.entry (fun _ => 1) (fun _ => 1) (fun _ => [true]) c 0 = 1 := by
    norm_num [FixedWidthQuery.entry, FixedWidthQuery.coordinate, Nat.fromBitsLE, Nat.fromBits]
  rw [hb] at H
  simp only [FixedWidthQuery.coordinate, Nat.zero_mul, List.drop_zero] at H
  change Nat.fromBitsLE ((unitField F c).take (width F c)) = 1 at H
  simpa only [← unitField_length, List.take_length] using H

noncomputable def normalized (F : Inputs) (q : List Bool) : List Bool := unitField F (pairFst q) ++ pairSnd q

theorem normalized_FP {F : Inputs} (h : F.PolyTime) : normalized F ∈ FP :=
  appendFn_mem_FP (mem_FP_comp pairFst_mem_FP (unitField_FP h)) pairSnd_mem_FP

theorem normalized_zero (F : Inputs) (c r : List Bool) :
    FixedWidthQuery.coordinate (width F ∘ pairFst) (normalized F) (pair c r) 0 = 1 := by
  simp only [FixedWidthQuery.coordinate, normalized, Function.comp_apply, pairFst_pair, pairSnd_pair,
    Nat.zero_mul, List.drop_zero]
  rw [← unitField_length, List.take_left, unitField_value]

theorem normalized_succ (F : Inputs) (c r : List Bool) (i : ℕ) :
    FixedWidthQuery.coordinate (width F ∘ pairFst) (normalized F) (pair c r) (i + 1) =
      FixedWidthQuery.coordinate (width F) (fun _ => r) c i := by
  simp only [FixedWidthQuery.coordinate, normalized, Function.comp_apply, pairFst_pair, pairSnd_pair]
  rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (i * width F c), ← unitField_length,
    ← List.drop_drop, List.drop_left, unitField_length]

noncomputable def child (F : Inputs) : BoundedCriticalSampleChildSource.Inputs where
  parent := F.parent
  term := F.source ∘ pairFst
  offset := F.offset ∘ pairFst
  dim q := F.free (pairFst q) + 1
  directionWidth := width F ∘ pairFst
  direction := pairSnd
  pivot _ := ⟨0, Nat.zero_lt_succ _⟩

theorem child_polyTime {F : Inputs} (h : F.PolyTime)
    (ht : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c) : (child F).PolyTime :=
  ⟨h.parent, mem_FP_comp (f := pairFst) (g := F.source) pairFst_mem_FP h.source,
    h.offset.comp pairFst_mem_FP, (h.free.comp pairFst_mem_FP).add (UnaryFn.const 1),
    (BoundedCriticalSampleDirectionChoice.width_unary h).comp pairFst_mem_FP,
    pairSnd_mem_FP, BinaryFn.const 0, ht⟩

noncomputable def prepare (F : Inputs) (c : List Bool) : List Bool :=
  pair c (normalized F (pair c (record F c)))

theorem prepare_evaluator {F : Inputs} (h : F.PolyTime)
    (ht : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c) : SpaceFunction (prepare F) := by
  have hp := mem_FP_pair pairFst_mem_FP (normalized_FP h)
  exact ((BoundedCriticalSampleDirectionChoice.evaluator h ht).withInput.postcompose
    (fun q => pair (pairFst q) (normalized F q)) hp).congr
    (funext fun c => by simp only [Function.comp_apply, pairFst_pair, prepare])

@[simp] theorem prepare_source (F : Inputs) (c : List Bool) : pairFst (prepare F c) = c := pairFst_pair _ _

theorem prepare_direction (F : Inputs) (c : List Bool) :
    pairSnd (prepare F c) = normalized F (pair c (record F c)) := pairSnd_pair _ _

theorem prepare_length (F : Inputs) (c : List Bool) :
    (pairSnd (prepare F c)).length = (F.free c + 1) * width F c := by
  rw [prepare_direction]
  simp only [normalized, pairFst_pair, pairSnd_pair, List.length_append, unitField_length,
    BoundedCriticalSampleDirectionChoice.record_length, BoundedCriticalSampleDirectionChoice.recordLength]
  ring

end LeanCanny.Encoding.BoundedCriticalSampleDirectionPacket
