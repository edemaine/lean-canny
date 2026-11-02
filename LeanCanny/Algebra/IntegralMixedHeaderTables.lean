/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCommandHeaderNative
/-! # Exact mixed-history metadata from two original syntactic tables

The two charged interfaces are FP word writers for command and fallback
headers. Representation states literal agreement with typed command syntax;
it contains no coefficient, leading, matrix or interpreted-state reader.
Fallbacks use a bounded prefix/context address. A frontend must construct
and totalize these tables: an empty raw projection alone does not represent
a typed fallback on malformed original inputs.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeaderTablesBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFullHistoryScript IntegralMixedFullHistoryFamilyBits
open IntegralMixedCommandHeaderBits
open scoped Classical

structure Tables where
  commands : List Bool → List Bool
  fallback : List Bool → List Bool
structure Access (T : Tables) : Prop where
  commands : T.commands ∈ FP
  fallback : T.fallback ∈ FP

def fallbackIndex (P : Parameters) (key : List Bool) : ℕ :=
  5 * prefixLength P key + min (Nat.fromBitsLE (pairSnd (pairSnd key))) 4

theorem fallbackIndex_binary (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) : BinaryFn (fallbackIndex P) := by
  have HC : BinaryFn (fun key => Nat.fromBitsLE (pairSnd (pairSnd key))) :=
    BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have HM : BinaryFn (fun key => min (Nat.fromBitsLE (pairSnd (pairSnd key))) 4) :=
    (BinaryFn.ite (HC.le (BinaryFn.const 4)) HC (BinaryFn.const 4)).of_eq (fun key => Nat.min_def.symm)
  exact ((BinaryFn.const 5).mul (BinaryFn.ofUnary (prefix_unary P a))).add HM

theorem fallbackIndex_lt (P : Parameters) (key : List Bool) :
    fallbackIndex P key < 5 * (P.cap (pairFst key) + 2) := by
  have HB : prefixLength P key ≤ P.cap (pairFst key) + 1 := min_le_right _ _
  have HC : min (Nat.fromBitsLE (pairSnd (pairSnd key))) 4 ≤ 4 := min_le_right _ _
  unfold fallbackIndex
  omega

def producer (P : Parameters) (T : Tables) (key : List Bool) : Header :=
  lookup (T.commands (pairFst key)) (prefixLength P key)
def fallback (P : Parameters) (T : Tables) (key : List Bool) : Header :=
  lookup (T.fallback (pairFst key)) (fallbackIndex P key)
def selected (P : Parameters) (T : Tables) (key : List Bool) : Header :=
  if isCut (producer P T key) then producer P T key else fallback P T key

theorem producer_readers (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (T : Tables) (h : Access T) :
    Readers (producer P T) :=
  lookup_readers _ _ (mem_FP_comp pairFst_mem_FP h.commands) (BinaryFn.ofUnary (prefix_unary P a))
theorem fallback_readers (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (T : Tables) (h : Access T) :
    Readers (fallback P T) :=
  lookup_readers _ _ (mem_FP_comp pairFst_mem_FP h.fallback) (fallbackIndex_binary P a)
theorem selected_readers (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (T : Tables) (h : Access T) :
    Readers (selected P T) :=
  Readers.choose _ (isCut_FP _ (producer_readers P a T h)) (producer_readers P a T h) (fallback_readers P a T h)

structure Represents (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (T : Tables) : Prop where
  commands : ∀ root, T.commands root = words (D.rules root)
  fallback : ∀ key, WordList.get (T.fallback (pairFst key)) (fallbackIndex P key) =
    encode (IntegralMixedCommandHeaderBits.selection (D.fallback key))

theorem producer_eq (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (T : Tables) (h : Represents P D T) (key : List Bool) :
    producer P T key = command (creatingCommand P D key) := by
  unfold producer
  rw [h.commands, lookup_words]
  rfl

theorem fallback_eq (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (T : Tables) (h : Represents P D T) (key : List Bool) :
    fallback P T key = IntegralMixedCommandHeaderBits.selection (D.fallback key) := by
  unfold fallback lookup
  rw [h.fallback, decode_encode]

theorem selected_eq (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (T : Tables) (h : Represents P D T) (key : List Bool) :
    selected P T key = IntegralMixedCommandHeaderBits.selection (IntegralMixedFullHistoryFamilyBits.selection P D key) := by
  unfold selected
  rw [producer_eq P D T h key, fallback_eq P D T h key]
  unfold creatingCommand IntegralMixedFullHistoryFamilyBits.selection
  cases hc : creating P D key with
  | none => simp [command_default, isCut, zero]
  | some c =>
    cases c with
    | integer => simp [command, isCut, zero]
    | critical => simp [command, isCut]
    | cut r k d ha hd => cases k <;> simp [command, IntegralMixedCommandHeaderBits.selection, kindContext, isCut]

end LeanCanny.Algebra.IntegralMixedHeaderTablesBits
