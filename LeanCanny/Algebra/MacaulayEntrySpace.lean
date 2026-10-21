/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayEntryControl
public import LeanCanny.Algebra.MatrixPowerArithmeticFP
public import LeanCanny.Computation.SpaceFunctionBranch

/-! # Streamed source coefficient selection for Macaulay entries

All entry controls and query preparation are FP. Only the selected source
coefficient needs a space certificate. Identity padding uses the query's actual
modulus, including modulus one, and every child state is included in the bound.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayBits

open LeanCanny.Encoding LeanCanny.Computation

def differenceAt (L : Layout) (p : List Bool) (i : ℕ) : ℕ := colAt L p i - remainderAt L p i

def differenceRead (L : Layout) (q : List Bool) : List Bool :=
  BinaryNat.sub (pair (colRead L q) (remainderRead L q))

theorem differenceRead_mem_FP {L : Layout} (h : L.PolyTime) : differenceRead L ∈ FP :=
  mem_FP_comp (mem_FP_pair (colRead_mem_FP h) (remainderRead_mem_FP h)) BinaryNat.sub_mem_FP

theorem differenceRead_packet (L : Layout) (p : List Bool) (i : ℕ) :
    differenceRead L (pair p (BinaryNatCode.encode i)) = BinaryNatCode.encode (differenceAt L p i) := by
  simp only [differenceRead, colRead, FixedWidthQuery.read_packet, remainderRead_packet,
    BinaryNat.sub_pair, fromBits_encode, differenceAt, colAt]
  rfl

def differenceWord (L : Layout) (p : List Bool) : List Bool :=
  FixedWidthNatVector.encode (L.arity (context p)) (L.width (context p)) (differenceAt L p)

theorem differenceWord_mem_FP {L : Layout} (h : L.PolyTime) : differenceWord L ∈ FP :=
  FixedWidthNatVector.encode_mem_FP _ _ _ (h.arity.comp context_mem_FP) (h.width.comp context_mem_FP)
    (differenceRead L) (differenceRead_mem_FP h) (differenceRead_packet L)

def admissible (L : Layout) (p : List Bool) : Prop :=
  ∀ i < L.arity (context p), remainderAt L p i ≤ colAt L p i

instance (L : Layout) (p : List Bool) : Decidable (admissible L p) :=
  inferInstanceAs (Decidable (∀ i < L.arity (context p), remainderAt L p i ≤ colAt L p i))

theorem admissible_fppred {L : Layout} (h : L.PolyTime) : FPPred (admissible L) := by
  have hr := mem_FP_comp loopQuery_mem_FP (remainderRead_mem_FP h)
  have hc := mem_FP_comp loopQuery_mem_FP (colRead_mem_FP h)
  have hf := (BinaryNat.le_fppred hr hc).forall_lt (h.arity.comp context_mem_FP)
  apply hf.of_iff
  intro p
  simp only [loopQuery, Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate,
    remainderRead_packet, colRead, FixedWidthQuery.read_packet, fromBits_encode, admissible, colAt]

def active (L : Layout) (p : List Bool) : Prop := rowTotal L p = L.level (context p)

instance (L : Layout) (p : List Bool) : Decidable (active L p) := inferInstanceAs (Decidable (_ = _))

theorem active_fppred {L : Layout} (h : L.PolyTime) : FPPred (active L) :=
  FPPred.eq (rowTotal_unary h) ((Layout.level_unary h).comp context_mem_FP)

def sourceQuery (L : Layout) (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (BinaryNatCode.encode (pivot L p)) (BinaryNat.normalize (differenceWord L p)))

theorem sourceQuery_mem_FP {L : Layout} (h : L.PolyTime) : sourceQuery L ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair (bits_mem_FP (pivot_unary h))
    (mem_FP_comp (differenceWord_mem_FP h) BinaryNat.normalize_mem_FP))

def sameIndex (p : List Bool) : Prop := Nat.fromBitsLE (row p) = Nat.fromBitsLE (col p)

instance (p : List Bool) : Decidable (sameIndex p) := inferInstanceAs (Decidable (_ = _))

theorem sameIndex_fppred : FPPred sameIndex :=
  ((BinaryNat.le_fppred row_mem_FP col_mem_FP).and
    (BinaryNat.le_fppred col_mem_FP row_mem_FP)).of_iff (fun _ => by unfold sameIndex; omega)

def identityEntry (p : List Bool) : List Bool :=
  if sameIndex p then MatrixPower.ArithmeticBits.one (BinaryNat.succ (pairSnd (pairFst p))) else []

theorem identityEntry_mem_FP : identityEntry ∈ FP := by
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.succ_mem_FP
  have ho := mem_FP_comp hm MatrixPower.ArithmeticBits.one_mem_FP
  have hb := sameIndex_fppred.ite_mem_FP ho (constFn_mem_FP [])
  exact mem_FP_of_eq hb (fun _ => rfl)

def entry (L : Layout) (coefficient : List Bool → List Bool) (p : List Bool) : List Bool :=
  if active L p then
    if admissible L p then coefficient (sourceQuery L p) else []
  else identityEntry p

theorem entryEvaluator {L : Layout} (h : L.PolyTime)
    {coefficient : List Bool → List Bool} (E : SpaceFunction coefficient) : SpaceFunction (entry L coefficient) := by
  have EC := E.precompose (sourceQuery L) (sourceQuery_mem_FP h)
  have EA := SpaceFunction.branch (fun p => decide (admissible L p)) (admissible_fppred h).flag_mem_FP
    EC (SpaceFunction.ofFP _ (constFn_mem_FP []))
  have ER := SpaceFunction.branch (fun p => decide (active L p)) (active_fppred h).flag_mem_FP
    EA (SpaceFunction.ofFP _ identityEntry_mem_FP)
  exact ER.congr (funext fun p => by simp only [entry, decide_eq_true_eq, Function.comp_apply])

end LeanCanny.Algebra.MacaulayBits
