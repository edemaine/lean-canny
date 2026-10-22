/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.LayeredMatrix
public import LeanCanny.Algebra.MatrixPowerSpaceEntries
public import LeanCanny.Computation.PolyTimeBinaryNat
public import LeanCanny.Encoding.BinaryDivFP

/-! # Native ordered matrix products with space-bounded factor entries

The layered reduction uses binary width and product length. Each factor
entry may use polynomial space and arbitrary time; its cost is included in
the final native certificate. No matrix or coefficient vector is stored.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixProductBits
open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Encoding.Brackets
open MatrixPower

structure Family where
  width : List Bool → ℕ
  count : List Bool → ℕ
  modulus : List Bool → ℕ
  row : (c : List Bool) → Fin (width c)
  col : (c : List Bool) → Fin (width c)
  factor : (c : List Bool) → ℕ → Matrix (Fin (width c)) (Fin (width c)) (ZMod (modulus c))
  modulus_ne_zero : ∀ c, modulus c ≠ 0

noncomputable def Family.value (F : Family) (c : List Bool) : List Bool :=
  residueBits (MatrixProduct.product (F.factor c) 0 (F.count c) (F.row c) (F.col c))

noncomputable def Family.power (F : Family) : MatrixPower.ModularFamily where
  dimension c := (F.count c + 1) * F.width c
  modulus := F.modulus
  exponent := F.count
  row c := finProdFinEquiv (⟨0, by omega⟩, F.row c)
  col c := finProdFinEquiv (⟨F.count c, by omega⟩, F.col c)
  matrix c := MatrixProduct.layeredFin (F.factor c) (F.count c + 1)
  modulus_ne_zero := F.modulus_ne_zero

theorem Family.power_value (F : Family) : F.power.value = F.value := by
  funext c
  have h := MatrixProduct.layeredFin_pow_apply (F.factor c) (F.count c + 1) (F.count c)
    (⟨0, by omega⟩ : Fin (F.count c + 1)) (⟨F.count c, by omega⟩ : Fin (F.count c + 1)) (F.row c) (F.col c)
  have h' : (MatrixProduct.layeredFin (F.factor c) (F.count c + 1) ^ F.count c)
      (finProdFinEquiv (⟨0, by omega⟩, F.row c)) (finProdFinEquiv (⟨F.count c, by omega⟩, F.col c)) =
        MatrixProduct.product (F.factor c) 0 (F.count c) (F.row c) (F.col c) := by
    simpa only [Nat.zero_add, ite_true] using h
  exact congrArg residueBits h'

structure Access (F : Family) where
  width : BinaryFn F.width
  count : BinaryFn F.count
  modulus : BinaryFn F.modulus
  row : BinaryFn (fun c => (F.row c).val)
  col : BinaryFn (fun c => (F.col c).val)
  entry : List Bool → List Bool
  entry_eq : ∀ c s (i j : Fin (F.width c)),
    entry (pair c (pair (BinaryNatCode.encode s) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (F.factor c s i j)

def rowWord (p : List Bool) : List Bool := pairFst (pairSnd p)
def colWord (p : List Bool) : List Bool := pairSnd (pairSnd p)
def rowLayer (F : Family) (p : List Bool) : List Bool := BinaryNat.div (pair (rowWord p) (BinaryNatCode.encode (F.width (pairFst p))))
def colLayer (F : Family) (p : List Bool) : List Bool := BinaryNat.div (pair (colWord p) (BinaryNatCode.encode (F.width (pairFst p))))
def rowOffset (F : Family) (p : List Bool) : List Bool := BinaryNat.mod (pair (rowWord p) (BinaryNatCode.encode (F.width (pairFst p))))
def colOffset (F : Family) (p : List Bool) : List Bool := BinaryNat.mod (pair (colWord p) (BinaryNatCode.encode (F.width (pairFst p))))
def factorQuery (F : Family) (p : List Bool) : List Bool := pair (pairFst p) (pair (rowLayer F p) (pair (rowOffset F p) (colOffset F p)))

def powerEntry (F : Family) (a : Access F) (p : List Bool) : List Bool :=
  if BinaryNat.succ (rowLayer F p) = colLayer F p then a.entry (factorQuery F p) else []

attribute [local irreducible] BinaryNat.div BinaryNat.mod BinaryNat.succ

theorem query_controls (F : Family) (a : Access F) :
    rowLayer F ∈ FP ∧ colLayer F ∈ FP ∧ rowOffset F ∈ FP ∧ colOffset F ∈ FP := by
  have hw := mem_FP_comp pairFst_mem_FP a.width.bits_mem_FP
  have hr := mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) hw
  have hc := mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) hw
  exact ⟨mem_FP_comp hr BinaryNat.div_mem_FP, mem_FP_comp hc BinaryNat.div_mem_FP,
    mem_FP_comp hr BinaryNat.mod_mem_FP, mem_FP_comp hc BinaryNat.mod_mem_FP⟩

theorem factorQuery_FP (F : Family) (a : Access F) : factorQuery F ∈ FP := by
  obtain ⟨hr, _, hi, hj⟩ := query_controls F a
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair hr (mem_FP_pair hi hj))

theorem powerEntryEvaluator (F : Family) (a : Access F) (E : SpaceFunction a.entry) : SpaceFunction (powerEntry F a) := by
  obtain ⟨hr, hc, _, _⟩ := query_controls F a
  have hp := stringEq_fppred (mem_FP_comp hr BinaryNat.succ_mem_FP) hc
  have R := SpaceFunction.branch (fun p => decide (BinaryNat.succ (rowLayer F p) = colLayer F p)) hp.flag_mem_FP
    (E.precompose (factorQuery F) (factorQuery_FP F a)) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact R.congr (funext fun p => by simp only [powerEntry, Function.comp_apply, decide_eq_true_eq])

theorem powerEntry_packet (F : Family) (a : Access F) (c : List Bool) (i j : Fin ((F.count c + 1) * F.width c)) :
    powerEntry F a (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) = residueBits (F.power.matrix c i j) := by
  change powerEntry F a (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
    residueBits (MatrixProduct.layeredFin (F.factor c) (F.count c + 1) i j)
  simp only [powerEntry, factorQuery, rowLayer, colLayer, rowOffset, colOffset, rowWord, colWord,
    pairFst_pair, pairSnd_pair, BinaryNat.div_pair, BinaryNat.mod_pair, BinaryNat.succ_eq_bits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  change (if BinaryNatCode.encode (i.divNat.val + 1) = BinaryNatCode.encode j.divNat.val then
    a.entry (pair c (pair (BinaryNatCode.encode i.divNat.val) (pair (BinaryNatCode.encode i.modNat.val) (BinaryNatCode.encode j.modNat.val))))
    else []) = residueBits (F.power.matrix c i j)
  simp only [BinaryNatCode.encode_injective.eq_iff]
  change _ = residueBits (if i.divNat.val + 1 = j.divNat.val then F.factor c i.divNat.val i.modNat j.modNat else 0)
  split_ifs
  · exact a.entry_eq c i.divNat.val i.modNat j.modNat
  · simp only [residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

noncomputable def powerAccess (F : Family) (a : Access F) : MatrixPower.ModularAccess F.power where
  dimension c := BinaryNatCode.encode ((F.count c + 1) * F.width c)
  modulus c := BinaryNatCode.encode (F.modulus c)
  exponent c := BinaryNatCode.encode (F.count c)
  row c := BinaryNatCode.encode (F.row c).val
  col c := BinaryNatCode.encode (F.width c * F.count c + (F.col c).val)
  entry := powerEntry F a
  dimension_eq _ := rfl
  modulus_eq _ := rfl
  exponent_eq _ := rfl
  row_eq c := by simp only [Family.power, finProdFinEquiv, Equiv.coe_fn_mk, Nat.mul_zero, Nat.add_zero]
  col_eq c := by simp only [Family.power, finProdFinEquiv, Equiv.coe_fn_mk, Nat.add_comm]
  entry_eq := powerEntry_packet F a

theorem evaluator (F : Family) (a : Access F) (E : SpaceFunction a.entry) : SpaceFunction F.value := by
  have hdim := ((a.count.add (BinaryFn.const 1)).mul a.width).bits_mem_FP
  have hcol := ((a.width.mul a.count).add a.col).bits_mem_FP
  have hc : (powerAccess F a).ControlsPolyTime := ⟨hdim, a.modulus.bits_mem_FP, a.count.bits_mem_FP, a.row.bits_mem_FP, hcol⟩
  exact ((powerAccess F a).evaluatorWithEntry hc (powerEntryEvaluator F a E)).congr (Family.power_value F)

end LeanCanny.Algebra.MatrixProductBits
