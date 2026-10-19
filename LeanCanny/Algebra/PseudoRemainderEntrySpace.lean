/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PseudoRemainderMatrix
public import LeanCanny.Algebra.ModularNegFP
public import LeanCanny.Computation.SpaceFunctionBranch
public import LeanCanny.Encoding.BinarySubFP

/-! # Streamed entries of the pseudo-remainder reduction matrix

An entry reads one coefficient of the original head, then selects that residue,
its modular negation, or zero. The original context and query stay available
throughout the suspended coefficient call.
-/

@[expose] public section

namespace LeanCanny.Algebra.PseudoRemainderBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower
open Polynomial

structure Access where
  headDegree : List Bool → List Bool
  modulus : List Bool → List Bool
  coefficient : List Bool → List Bool

def row (q : List Bool) : List Bool := pairFst (pairSnd q)
def col (q : List Bool) : List Bool := pairSnd (pairSnd q)

theorem row_mem_FP : row ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem col_mem_FP : col ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

def positive (a : Access) (q : List Bool) : Prop :=
  Nat.fromBitsLE (row q) = Nat.fromBitsLE (col q) ∧
    Nat.fromBitsLE (col q) < Nat.fromBitsLE (a.headDegree (pairFst q))
def negative (a : Access) (q : List Bool) : Prop :=
  Nat.fromBitsLE (row q) < Nat.fromBitsLE (col q) ∧
    Nat.fromBitsLE (a.headDegree (pairFst q)) ≤ Nat.fromBitsLE (col q) ∧
      Nat.fromBitsLE (col q) - Nat.fromBitsLE (a.headDegree (pairFst q)) ≤ Nat.fromBitsLE (row q)
instance (a : Access) (q : List Bool) : Decidable (positive a q) := inferInstanceAs (Decidable (_ ∧ _))
instance (a : Access) (q : List Bool) : Decidable (negative a q) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def shift (a : Access) (q : List Bool) : List Bool :=
  BinaryNat.sub (pair (col q) (a.headDegree (pairFst q)))
def index (a : Access) (q : List Bool) : List Bool :=
  if positive a q then a.headDegree (pairFst q) else BinaryNat.sub (pair (row q) (shift a q))
def query (a : Access) (q : List Bool) : List Bool := pair (pairFst q) (index a q)
def finish (a : Access) (z : List Bool) : List Bool :=
  if positive a (pairFst z) then pairSnd z
  else if negative a (pairFst z) then
    ArithmeticBits.negate (pair (a.modulus (pairFst (pairFst z))) (pairSnd z))
  else []
def entry (a : Access) (q : List Bool) : List Bool :=
  finish a (pair q (a.coefficient (query a q)))

theorem positive_fppred (a : Access) (hd : a.headDegree ∈ FP) : FPPred (positive a) := by
  have he : FPPred (fun q => Nat.fromBitsLE (row q) = Nat.fromBitsLE (col q)) :=
    ((BinaryNat.le_fppred row_mem_FP col_mem_FP).and
      (BinaryNat.le_fppred col_mem_FP row_mem_FP)).of_iff (fun q => by omega)
  exact he.and (BinaryNat.lt_fppred col_mem_FP (mem_FP_comp pairFst_mem_FP hd))

theorem shift_mem_FP (a : Access) (hd : a.headDegree ∈ FP) : shift a ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair col_mem_FP (mem_FP_comp pairFst_mem_FP hd)) BinaryNat.sub_mem_FP
  refine mem_FP_of_eq (g := shift a) h ?_
  intro q
  simp only [shift, Function.comp_apply]

theorem negative_fppred (a : Access) (hd : a.headDegree ∈ FP) : FPPred (negative a) := by
  have h := (BinaryNat.lt_fppred row_mem_FP col_mem_FP).and
    ((BinaryNat.le_fppred (mem_FP_comp pairFst_mem_FP hd) col_mem_FP).and
      (BinaryNat.le_fppred (shift_mem_FP a hd) row_mem_FP))
  exact h.of_iff fun q => by
    simp only [negative, shift, BinaryNat.sub_pair, Nat.fromBitsLE_bits, Function.comp_apply]

theorem index_mem_FP (a : Access) (hd : a.headDegree ∈ FP) : index a ∈ FP := by
  have hs := mem_FP_comp (mem_FP_pair row_mem_FP (shift_mem_FP a hd)) BinaryNat.sub_mem_FP
  have h := (positive_fppred a hd).ite_mem_FP (mem_FP_comp pairFst_mem_FP hd) hs
  refine mem_FP_of_eq (g := index a) h ?_
  intro q
  simp only [index, Function.comp_apply]

theorem query_mem_FP (a : Access) (hd : a.headDegree ∈ FP) : query a ∈ FP :=
  mem_FP_pair pairFst_mem_FP (index_mem_FP a hd)

theorem finish_mem_FP (a : Access) (hd : a.headDegree ∈ FP) (hm : a.modulus ∈ FP) :
    finish a ∈ FP := by
  have hmod := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hm
  have hn := mem_FP_comp (mem_FP_pair hmod pairSnd_mem_FP) ArithmeticBits.negate_mem_FP
  have hp := (positive_fppred a hd).comp pairFst_mem_FP
  have hneg := (negative_fppred a hd).comp pairFst_mem_FP
  have h := hp.ite_mem_FP pairSnd_mem_FP (hneg.ite_mem_FP hn (constFn_mem_FP []))
  refine mem_FP_of_eq (g := finish a) h ?_
  intro q
  simp only [finish, Function.comp_apply]

noncomputable def entryEvaluator (a : Access) (hd : a.headDegree ∈ FP) (hm : a.modulus ∈ FP)
    (P : SpaceFunction a.coefficient) : SpaceFunction (entry a) := by
  let E := ((P.precompose (query a) (query_mem_FP a hd)).withInput).postcompose
    (finish a) (finish_mem_FP a hd hm)
  refine E.congr (funext fun q => ?_)
  simp only [entry, Function.comp_apply]

/-- The entry controller supplies the actual reduction matrix, including modulus one. -/
theorem entry_correct (a : Access) (c : List Bool) (m d D : ℕ) [NeZero m]
    (p : (ZMod m)[X]) (hp : p.natDegree ≤ d)
    (hd : a.headDegree c = BinaryNatCode.encode d)
    (hm : a.modulus c = BinaryNatCode.encode m)
    (hc : ∀ k, a.coefficient (pair c (BinaryNatCode.encode k)) = residueBits (p.coeff k))
    (i j : Fin (D + 1)) :
    entry a (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits (PseudoRemainder.matrix p d D i j) := by
  let q := pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have hpos : positive a q ↔ i = j ∧ j.val < d := by
    simp only [positive, q, row, col, pairFst_pair, pairSnd_pair, hd,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Fin.ext_iff]
  have hneg : negative a q ↔ i.val < j.val ∧ d ≤ j.val ∧ j.val - d ≤ i.val := by
    simp only [negative, q, row, col, pairFst_pair, pairSnd_pair, hd,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hidx : index a q =
      if positive a q then BinaryNatCode.encode d
      else BinaryNatCode.encode (i.val - (j.val - d)) := by
    simp only [index, q, row, col, shift, pairFst_pair, pairSnd_pair, hd,
      BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rfl
  change finish a (pair q (a.coefficient (query a q))) = _
  rw [PseudoRemainder.matrix_apply_sparse p d D hp]
  by_cases h : positive a q
  · rw [ite_eq_left (hpos.mp h)]
    simp only [finish, pairFst_pair, pairSnd_pair, query, hidx, ite_eq_left h,
      q, pairFst_pair, hc]
  · rw [ite_eq_right (fun hn => h (hpos.mpr hn))]
    by_cases hn : negative a q
    · rw [ite_eq_left (hneg.mp hn)]
      simp only [finish, pairFst_pair, pairSnd_pair, ite_eq_left hn,
        query, hidx, ite_eq_right h, q, pairFst_pair, hc, hm]
      exact ArithmeticBits.negate_residueBits m _
    · rw [ite_eq_right (fun h' => hn (hneg.mpr h'))]
      simp only [finish, pairFst_pair, pairSnd_pair, ite_eq_right h, ite_eq_right hn]
      simp [residueBits, BinaryNatCode.encode]

end LeanCanny.Algebra.PseudoRemainderBits
