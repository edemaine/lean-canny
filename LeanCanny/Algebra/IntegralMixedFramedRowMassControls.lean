/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRowMass
public import LeanCanny.Algebra.IntegralMixedFramedPrefixHeight

/-! # Native uniform row mass for actual total framed prefixes

The same original ScriptBounds and default-instruction bounds already used
for bank growth imply a row-mass ceiling for every saved prefix. No all-key
bank bound or row-mass premise is added.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedStepHeight
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical

def globalRowMass (n S B W D L F C : ℕ) : ℕ := rowMass n S B W D L F C (S+1)

theorem rowMass_binary {n S B W D L F C j : List Bool→ℕ}
    (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B) (hW : UnaryFn W)
    (hD : BinaryFn D) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) (hj : UnaryFn j) :
    BinaryFn (fun q=>rowMass (n q) (S q) (B q) (W q) (D q) (L q) (F q) (C q) (j q)) :=
  PaddedIntegralParameterExtension.rowMassHeight_binary (BinaryFn.ofUnary hS) (BinaryFn.ofUnary hB)
    (height_binary hn hS hB hW hD hL hF hC hj)

theorem globalRowMass_binary {n S B W D L F C : List Bool→ℕ}
    (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B) (hW : UnaryFn W)
    (hD : BinaryFn D) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) :
    BinaryFn (fun q=>globalRowMass (n q) (S q) (B q) (W q) (D q) (L q) (F q) (C q)) :=
  rowMass_binary hn hS hB hW hD hL hF hC (hS.add (UnaryFn.const 1))

theorem run_row_mass_global {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (cs : List (Instruction n B)) (hcs : cs.length≤S+1)
    (W D L F C : ℕ) (hb : ScriptBounds S W D L F C cs) (i : Fin cs.length) :
    MvMass.mass ((run initial cs hcs).sampler.scalarPrefix.rows i)≤2^globalRowMass n S B W D L F C := by
  apply (run_row_mass initial cs hcs W D L F C hb i).trans
  exact Nat.pow_le_pow_right (by decide) (by
    unfold rowMass globalRowMass PaddedIntegralParameterExtension.rowMassHeight
    exact Nat.add_le_add_right (Nat.add_le_add_right (height_mono n S B W D L F C hcs) _) _)

open IntegralCriticalHistoryTask

def familyRowMass (P : Parameters) (L F C : List Bool→ℕ) (root : List Bool) : ℕ :=
  globalRowMass (P.ambient root) (P.cap root+1) (P.width root) (P.sourceWidth root)
    (P.degree root) (L root) (F root) (C root)

theorem familyRowMass_binary (P : Parameters) (a : Access P) {L F C : List Bool→ℕ}
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : BinaryFn (familyRowMass P L F C) :=
  globalRowMass_binary a.ambient (a.cap.add (UnaryFn.const 1)) a.width a.sourceWidth a.degree hL hF hC

theorem family_row_mass (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool→ℕ)
    (h : FamilyInputs P D L F C) (key : List Bool)
    (i : Fin ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth key)) :
    MvMass.mass (((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).sampler.scalarPrefix.rows i)≤
      2^familyRowMass P L F C (pairFst key) := by
  have HB := padded_bounds (h.script (pairFst key))
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst key)) (h.default (pairFst key))
    (IntegralMixedFramedHistoryFamilyBits.prefixLength P key)
  exact run_row_mass_global (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst key))
    (IntegralMixedFramedHistoryFamilyBits.commands P D key)
    (((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound key).trans (Nat.le_succ _))
    (P.sourceWidth (pairFst key)) (P.degree (pairFst key)) (L (pairFst key)) (F (pairFst key)) (C (pairFst key)) HB i

end LeanCanny.Algebra.IntegralMixedFramedStepHeight
