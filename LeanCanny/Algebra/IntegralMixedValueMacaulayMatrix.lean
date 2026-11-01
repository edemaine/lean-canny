/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueMacaulayRequest
public import LeanCanny.Algebra.IntegralMixedValueGramFromRows

/-! # Actual rectangular value Macaulay entries with guarded finite labels -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueMacaulayMatrix
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualSweepSource
open scoped Classical

noncomputable abbrev arity (F : Family) (q : List Bool) := (IntegralMixedValueMacaulayEntry.layout F).arity q
noncomputable abbrev width (F : Family) (q : List Bool) := (IntegralMixedValueMacaulayEntry.layout F).width q
noncomputable abbrev columns (F : Family) (q : List Bool) := count (arity F q) (width F q)
noncomputable abbrev rows (F : Family) (q : List Bool) := (arity F q + 1) * columns F q
abbrev rank (F : Family) (q : List Bool) := count (F.birth q + 2) (F.width q)

noncomputable def entry (F : Family) (I : Indices F) (q : List Bool)
    (a : Fin (rows F q)) (b : Fin (columns F q)) (r t : Fin (rank F q)) : ℤ :=
  Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
    (IntegralMixedValueGramEntry.rectangular F I q a b) r t

def Labels (F : Family) (q : List Bool) (a b r t : ℕ) : Prop :=
  a < rows F q ∧ b < columns F q ∧ r < rank F q ∧ t < rank F q
noncomputable instance (F : Family) (q : List Bool) (a b r t : ℕ) : Decidable (Labels F q a b r t) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem valid_packet_iff (L : MacaulayFullBoxBits.Layout) (q : List Bool) (a b r t : ℕ) :
    MacaulayIntegralEntryRequest.valid L (MacaulayFullBoxBits.entryPacket q a b r t) ↔
      a < (L.arity q + 1) * count (L.arity q) (L.width q) ∧ b < count (L.arity q) (L.width q) := by
  simp only [MacaulayIntegralEntryRequest.valid, MacaulayFullBoxBits.ctx_entryPacket,
    MacaulayFullBoxBits.idx_entryPacket, MacaulayFullBoxBits.shift_entryPacket,
    MacaulayFullBoxBits.rowCut_eq, MacaulayFullBoxBits.columnsCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def totalEntry (F : Family) (I : Indices F) (q : List Bool) (a b r t : ℕ) : ℤ :=
  if H : Labels F q a b r t then entry F I q ⟨a, H.1⟩ ⟨b, H.2.1⟩ ⟨r, H.2.2.1⟩ ⟨t, H.2.2.2⟩ else 0

theorem total_finite (F : Family) (I : Indices F) (q : List Bool)
    (a : Fin (rows F q)) (b : Fin (columns F q)) (r t : Fin (rank F q)) :
    totalEntry F I q a.val b.val r.val t.val = entry F I q a b r t := by
  rw [totalEntry, dite_eq_left (show Labels F q a.val b.val r.val t.val from ⟨a.isLt, b.isLt, r.isLt, t.isLt⟩)]

theorem total_invalid (F : Family) (I : Indices F) (q : List Bool) (a b r t : ℕ)
    (h : ¬Labels F q a b r t) : totalEntry F I q a b r t = 0 := dite_eq_right h

noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (totalEntry (IntegralMixedVirtualTaskBits.family P F) (IntegralMixedVirtualTaskBits.indices P F) q
    (get P .slot8 q) (get P .slot9 q) (get P .row q) (get P .col q) : ZMod (modulus P q))

end LeanCanny.Algebra.IntegralMixedValueMacaulayMatrix
