/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixProductSpace
public import LeanCanny.Computation.SpaceFunctionBranch
public import LeanCanny.Computation.PolyTimeBinaryArithmetic

/-! # Native lifting of an old matrix through a new scalar basis digit

The new basis digit is least significant. Equal new digits read the old
matrix entry at the quotient ranks; unequal digits give zero. Binary
division and remainder suffice, with the old reader's full space charge.
-/

@[expose] public section
namespace LeanCanny.Algebra.MatrixDigitLiftBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Family where
  dimension : List Bool → ℕ
  radix : List Bool → ℕ
  modulus : List Bool → ℕ
  matrix : (c : List Bool) → Matrix (Fin (dimension c)) (Fin (dimension c)) (ZMod (modulus c))
  row : (c : List Bool) → Fin (dimension c * radix c)
  col : (c : List Bool) → Fin (dimension c * radix c)

noncomputable def Family.value (F : Family) (c : List Bool) : List Bool :=
  residueBits (if (F.row c).modNat = (F.col c).modNat then
    F.matrix c (F.row c).divNat (F.col c).divNat else 0)

structure Access (F : Family) where
  radix : BinaryFn F.radix
  row : BinaryFn (fun c => (F.row c).val)
  col : BinaryFn (fun c => (F.col c).val)
  entry : List Bool → List Bool
  entry_eq : ∀ c (i j : Fin (F.dimension c)),
    entry (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) = residueBits (F.matrix c i j)

def query (F : Family) (c : List Bool) : List Bool :=
  pair c (pair (BinaryNatCode.encode (F.row c).divNat.val) (BinaryNatCode.encode (F.col c).divNat.val))

theorem query_FP (F : Family) (a : Access F) : query F ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair (a.row.div a.radix).bits_mem_FP (a.col.div a.radix).bits_mem_FP)

theorem guard_FP (F : Family) (a : Access F) : FPPred (fun c => (F.row c).modNat = (F.col c).modNat) :=
  ((a.row.mod a.radix).eq (a.col.mod a.radix)).of_iff (fun c =>
    (show (F.row c).modNat = (F.col c).modNat ↔ (F.row c).modNat.val = (F.col c).modNat.val from Fin.ext_iff).symm)

theorem evaluator (F : Family) (a : Access F) (E : SpaceFunction a.entry) : SpaceFunction F.value := by
  have H := SpaceFunction.branch (fun c => decide ((F.row c).modNat = (F.col c).modNat))
    (guard_FP F a).flag_mem_FP (E.precompose (query F) (query_FP F a)) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine H.congr (funext fun c => ?_)
  simp only [Family.value, decide_eq_true_eq]
  by_cases h : (F.row c).modNat = (F.col c).modNat
  · rw [ite_eq_left h, ite_eq_left h]
    exact a.entry_eq _ _ _
  · simp only [h, ite_false, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

theorem value_packet {m N q : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod q))
    (r t : Fin m) (i j : Fin N) :
    residueBits (if (finProdFinEquiv (r, i) : Fin (m * N)).modNat = (finProdFinEquiv (t, j) : Fin (m * N)).modNat then
      A (finProdFinEquiv (r, i)).divNat (finProdFinEquiv (t, j)).divNat else 0) =
      residueBits (if i = j then A r t else 0) := by
  have HR := finProdFinEquiv.symm_apply_apply (r, i)
  have HC := finProdFinEquiv.symm_apply_apply (t, j)
  change ((finProdFinEquiv (r, i) : Fin (m * N)).divNat, (finProdFinEquiv (r, i) : Fin (m * N)).modNat) = (r, i) at HR
  change ((finProdFinEquiv (t, j) : Fin (m * N)).divNat, (finProdFinEquiv (t, j) : Fin (m * N)).modNat) = (t, j) at HC
  exact congrArg₂ (fun u v : Fin m × Fin N => residueBits (if u.2 = v.2 then A u.1 v.1 else 0)) HR HC

end LeanCanny.Algebra.MatrixDigitLiftBits
