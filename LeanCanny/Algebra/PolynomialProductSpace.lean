/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialProductPower
public import LeanCanny.Algebra.PolynomialPowerSpace

/-!
# Space-bounded coefficients of an indexed polynomial product

FP binary fields supply the factor count, positive modulus, and selected degree.
A suspended routine supplies factor coefficients. A polynomial shift-matrix
power computes the selected product coefficient without storing any factor,
coefficient vector, or partial product. Factor counts and degrees may be
exponential in input length. Empty products use the same evaluator.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialProduct
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower
open Polynomial
open scoped BigOperators

structure ModularFamily where
  count : List Bool → ℕ
  modulus : List Bool → ℕ
  degree : List Bool → ℕ
  factor : (c : List Bool) → ℕ → (ZMod (modulus c))[X]
  modulus_ne_zero : ∀ c, modulus c ≠ 0

noncomputable def ModularFamily.value (F : ModularFamily) (c : List Bool) : List Bool :=
  residueBits ((∏ i ∈ Finset.range (F.count c), F.factor c i).coeff (F.degree c))

def ModularFamily.zeroLanguage (F : ModularFamily) : Language :=
  {c | (∏ i ∈ Finset.range (F.count c), F.factor c i).coeff (F.degree c) = 0}

noncomputable def ModularFamily.power (F : ModularFamily) : PolynomialPower.ModularFamily where
  dimension := fun c => F.count c + 1
  modulus := F.modulus
  exponent := F.count
  row := fun _ => 0
  col := fun c => Fin.last (F.count c)
  degree := F.degree
  matrix := fun c => shift (F.factor c) (F.count c + 1)
  modulus_ne_zero := F.modulus_ne_zero

structure ModularAccess (F : ModularFamily) where
  count : List Bool → List Bool
  modulus : List Bool → List Bool
  degree : List Bool → List Bool
  coefficient : List Bool → List Bool
  count_eq : ∀ c, count c = BinaryNatCode.encode (F.count c)
  modulus_eq : ∀ c, modulus c = BinaryNatCode.encode (F.modulus c)
  degree_eq : ∀ c, degree c = BinaryNatCode.encode (F.degree c)
  coefficient_eq : ∀ c i, i < F.count c → ∀ k,
    coefficient (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) =
      residueBits ((F.factor c i).coeff k)

structure ModularAccess.ControlsPolyTime {F : ModularFamily} (a : ModularAccess F) : Prop where
  count : a.count ∈ FP
  modulus : a.modulus ∈ FP
  degree : a.degree ∈ FP

namespace EntryBits

def row (p : List Bool) : List Bool := pairFst (pairSnd p)
def col (p : List Bool) : List Bool := pairFst (pairSnd (pairSnd p))
def degree (p : List Bool) : List Bool := pairSnd (pairSnd (pairSnd p))
def query (p : List Bool) : List Bool := pair (pairFst p) (pair (row p) (degree p))
def adjacent (p : List Bool) : Bool := decide (col p = BinaryNat.succ (row p))
def value (f : List Bool → List Bool) (p : List Bool) : List Bool := if adjacent p then f (query p) else []

theorem row_mem_FP : row ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem col_mem_FP : col ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem degree_mem_FP : degree ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
theorem query_mem_FP : query ∈ FP := mem_FP_pair pairFst_mem_FP (mem_FP_pair row_mem_FP degree_mem_FP)
theorem adjacent_mem_FP : (fun p => [adjacent p]) ∈ FP :=
  (stringEq_fppred col_mem_FP (mem_FP_comp row_mem_FP BinaryNat.succ_mem_FP)).flag_mem_FP

noncomputable def evaluator {f : List Bool → List Bool} (E : SpaceFunction f) : SpaceFunction (value f) := by
  let Q := SpaceFunction.branch adjacent adjacent_mem_FP (E.precompose query query_mem_FP)
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  refine Q.congr (funext fun p => ?_)
  simp only [value, Function.comp_apply]

theorem succ_code (i : ℕ) : BinaryNat.succ (BinaryNatCode.encode i) = BinaryNatCode.encode (i + 1) := by
  simp only [BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]

end EntryBits

namespace ModularAccess

noncomputable def power {F : ModularFamily} (a : ModularAccess F) : PolynomialPower.ModularAccess F.power where
  bits := {
    dimension := BinaryNat.succ ∘ a.count
    modulus := a.modulus
    exponent := a.count
    row := fun _ => []
    col := a.count
    degree := a.degree
    coefficient := EntryBits.value a.coefficient }
  dimension_eq := fun c => by simp only [Function.comp_apply, a.count_eq, EntryBits.succ_code, ModularFamily.power]
  modulus_eq := a.modulus_eq
  exponent_eq := a.count_eq
  row_eq := fun _ => rfl
  col_eq := a.count_eq
  degree_eq := a.degree_eq
  coefficient_eq := by
    intro c i j k
    change Fin (F.count c + 1) at i j
    change EntryBits.value a.coefficient (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode k)))) =
      residueBits ((shift (F.factor c) (F.count c + 1) i j).coeff k)
    have hs := shift_apply (F.factor c) (F.count c + 1) i j
    rw [hs]
    simp only [EntryBits.value, EntryBits.adjacent, EntryBits.query, EntryBits.row, EntryBits.col,
      EntryBits.degree, pairFst_pair, pairSnd_pair, EntryBits.succ_code,
      BinaryNatCode.encode_injective.eq_iff, decide_eq_true_eq]
    by_cases h : i.val + 1 = j.val
    · rw [ite_eq_left h.symm, ite_eq_left h]
      exact a.coefficient_eq c i.val (by have := j.isLt; omega) k
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
      simp [residueBits, BinaryNatCode.encode]

theorem power_controls {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) :
    a.power.bits.ControlsPolyTime := by
  have hd := mem_FP_comp ha.count BinaryNat.succ_mem_FP
  constructor
  · exact hd
  · exact ha.modulus
  · exact ha.count
  · exact constFn_mem_FP []
  · exact ha.count
  · exact ha.degree

noncomputable def evaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.coefficient) : SpaceFunction F.value := by
  let Q := PolynomialPower.ModularAccess.evaluator a.power (power_controls a ha) (EntryBits.evaluator E)
  refine Q.congr (funext fun c => ?_)
  change residueBits (((shift (F.factor c) (F.count c + 1) ^ F.count c) 0 (Fin.last (F.count c))).coeff
    (F.degree c)) = _
  rw [shift_pow_product]
  rfl

noncomputable def decider {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.coefficient) : SpaceDecider F.zeroLanguage := by
  let accept := fun bits : List Bool => decide (bits = [])
  have haccept : (fun bits => [accept bits]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  refine (evaluator a ha E).decider accept haccept ?_
  intro c
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  have hz : residueBits (0 : ZMod (F.modulus c)) = [] := by simp [residueBits, BinaryNatCode.encode]
  change (∏ i ∈ Finset.range (F.count c), F.factor c i).coeff (F.degree c) = 0 ↔
    decide (residueBits ((∏ i ∈ Finset.range (F.count c), F.factor c i).coeff (F.degree c)) = []) = true
  rw [decide_eq_true_eq, ← hz, (residueBits_injective (F.modulus c)).eq_iff]

theorem zeroLanguage_mem_PSPACE {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.coefficient) : F.zeroLanguage ∈ PSPACE := (decider a ha E).mem_PSPACE

end ModularAccess
end LeanCanny.Algebra.PolynomialProduct
