/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedScalarCells
public import LeanCanny.Algebra.IntegralMixedCommandHeaderNative
/-! # Total native unit-selector source-record syntax

The writer receives the complete saved birth key. Field0 is a bounded height
coordinate, field1 physical row words, and field2 virtual row words. A row is
pair flag referenceIndex; absent rows are zero. Indices stay binary, so even
malformed huge references require no unary term serialization.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedUnitBodyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def field (writer : List Bool → List Bool) (i : ℕ) (key : List Bool) := WordList.get (writer key) i

theorem field_FP (writer : List Bool → List Bool) (hw : writer ∈ FP) (i : ℕ) : field writer i ∈ FP :=
  mem_FP_comp (f := writer) (g := fun w => WordList.get w i) hw (IntegralMixedCommandHeaderBits.get_FP i)

def rowWord (writer : List Bool → List Bool) (physical : Bool) (key : List Bool) (i : ℕ) :=
  WordList.get (field writer (if physical then 1 else 2) key) i

def rowReader (writer : List Bool → List Bool) (physical : Bool) (p : List Bool) :=
  rowWord writer physical (pairFst p) (Nat.fromBitsLE (pairSnd p))

theorem rowReader_FP (writer : List Bool → List Bool) (hw : writer ∈ FP) (physical : Bool) : rowReader writer physical ∈ FP := by
  have HF := mem_FP_comp (f := pairFst) (g := field writer (if physical then 1 else 2)) pairFst_mem_FP (field_FP writer hw _)
  have H := mem_FP_comp (mem_FP_pair HF pairSnd_mem_FP) WordList.reader_FP
  exact mem_FP_of_eq H (fun p => by simp only [Function.comp_apply, WordList.reader, pairFst_pair, pairSnd_pair]; rfl)

def active (writer : List Bool → List Bool) (physical : Bool) (key : List Bool) (i : ℕ) :=
  (pairFst (rowWord writer physical key i))[0]?.getD false

def reference (writer : List Bool → List Bool) (physical : Bool) (key : List Bool) (i : ℕ) :=
  Nat.fromBitsLE (pairSnd (rowWord writer physical key i))

noncomputable def expression (writer : List Bool → List Bool) (physical : Bool) (key : List Bool) (i : ℕ) : AffineExpr :=
  if active writer physical key i then .reference (reference writer physical key i) else .constant 0

theorem active_FP (writer : List Bool → List Bool) (hw : writer ∈ FP) (physical : Bool) :
    (fun p => [active writer physical (pairFst p) (Nat.fromBitsLE (pairSnd p))]) ∈ FP := by
  have H := FPPred.getBit (mem_FP_comp (rowReader_FP writer hw physical) pairFst_mem_FP) (UnaryFn.const 0)
  exact mem_FP_of_eq H.flag_mem_FP (fun p => by simp only [Function.comp_apply, rowReader, active]; simp only [Bool.decide_eq_true])

theorem reference_binary (writer : List Bool → List Bool) (hw : writer ∈ FP) (physical : Bool) :
    BinaryFn (fun p => reference writer physical (pairFst p) (Nat.fromBitsLE (pairSnd p))) :=
  BinaryFn.fromBits (mem_FP_comp (rowReader_FP writer hw physical) pairSnd_mem_FP)

def height (P : Parameters) (writer : List Bool → List Bool) (key : List Bool) :=
  Nat.fromBitsLE (field writer 0 key) % (P.ambient (pairFst key) + 1)

theorem height_binary (P : Parameters) (a : Access P) (writer : List Bool → List Bool) (hw : writer ∈ FP) :
    BinaryFn (height P writer) :=
  (BinaryFn.fromBits (field_FP writer hw 0)).mod (BinaryFn.ofUnary ((a.ambient.comp pairFst_mem_FP).add (UnaryFn.const 1)))

theorem height_lt (P : Parameters) (writer : List Bool → List Bool) (key : List Bool) : height P writer key < P.ambient (pairFst key) + 1 :=
  Nat.mod_lt _ (Nat.succ_pos _)

noncomputable def critical (P : Parameters) (writer : List Bool → List Bool) (physical : Bool) (key : List Bool)
    (offset : Fin (P.ambient (pairFst key) + 1)) (objective coordinate : ℕ) : CriticalRule (P.ambient (pairFst key)) where
  offset := offset
  objective := objective
  coordinate := coordinate
  scales _ := 1
  scales_ne_zero _ := one_ne_zero
  heights i := expression writer physical key i.val

noncomputable def sweep (P : Parameters) (writer : List Bool → List Bool) (key : List Bool)
    (offset : Fin (P.ambient (pairFst key) + 1)) (objective coordinate : ℕ)
    (hf : height P writer key < offset.val) : IntegralMixedCriticalSweep.Rule (P.ambient (pairFst key)) where
  critical := critical P writer false key offset objective coordinate
  height := ⟨height P writer key, height_lt P writer key⟩
  height_frozen := hf
  slope := 1
  slope_ne_zero := one_ne_zero
end LeanCanny.Algebra.IntegralMixedFramedUnitBodyBits
