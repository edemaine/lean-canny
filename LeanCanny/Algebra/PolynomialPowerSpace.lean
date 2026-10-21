/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialPowerAccessFP
public import LeanCanny.Algebra.PolynomialCoefficientMatrix
public import LeanCanny.Algebra.MatrixPowerSpaceEntries

/-!
# Space-certified polynomial matrix-power coefficients

The coefficient-matrix representation is accessed by FP binary query writers
and a certified routine for original entry coefficients. The scalar power
evaluator returns the selected polynomial coefficient without storing a
polynomial vector. Both the matrix dimension and degree may be exponential
in the input length; their binary control fields are required to be FP.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialPower
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower
open Polynomial

structure ModularFamily where
  dimension : List Bool → ℕ
  modulus : List Bool → ℕ
  exponent : List Bool → ℕ
  row : (c : List Bool) → Fin (dimension c)
  col : (c : List Bool) → Fin (dimension c)
  degree : List Bool → ℕ
  matrix : (c : List Bool) → Matrix (Fin (dimension c)) (Fin (dimension c)) (ZMod (modulus c))[X]
  modulus_ne_zero : ∀ c, modulus c ≠ 0

noncomputable def ModularFamily.value (F : ModularFamily) (c : List Bool) : List Bool :=
  residueBits (((F.matrix c ^ F.exponent c) (F.row c) (F.col c)).coeff (F.degree c))

def ModularFamily.zeroLanguage (F : ModularFamily) : Complexity.Language :=
  {c | ((F.matrix c ^ F.exponent c) (F.row c) (F.col c)).coeff (F.degree c) = 0}

noncomputable def ModularFamily.power (F : ModularFamily) : MatrixPower.ModularFamily where
  dimension := fun c => F.dimension c * (F.degree c + 1)
  modulus := F.modulus
  exponent := F.exponent
  row := fun c => finProdFinEquiv (F.row c, Fin.last (F.degree c))
  col := fun c => finProdFinEquiv (F.col c, 0)
  matrix := fun c => PolynomialCoefficientMatrix.finHom (F.dimension c) (F.degree c) (F.matrix c)
  modulus_ne_zero := F.modulus_ne_zero

structure ModularAccess (F : ModularFamily) where
  bits : Access
  dimension_eq : ∀ c, bits.dimension c = BinaryNatCode.encode (F.dimension c)
  modulus_eq : ∀ c, bits.modulus c = BinaryNatCode.encode (F.modulus c)
  exponent_eq : ∀ c, bits.exponent c = BinaryNatCode.encode (F.exponent c)
  row_eq : ∀ c, bits.row c = BinaryNatCode.encode (F.row c).val
  col_eq : ∀ c, bits.col c = BinaryNatCode.encode (F.col c).val
  degree_eq : ∀ c, bits.degree c = BinaryNatCode.encode (F.degree c)
  coefficient_eq : ∀ c (i j : Fin (F.dimension c)) (d : ℕ),
    bits.coefficient (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d)))) = residueBits ((F.matrix c i j).coeff d)

namespace ModularAccess

theorem liftedEntry_correct {F : ModularFamily} (a : ModularAccess F) (c : List Bool)
    (i j : Fin (F.dimension c * (F.degree c + 1))) :
    Access.liftedEntry a.bits (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits (F.power.matrix c i j) := by
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  rw [Access.liftedEntry, Access.lower_code a.bits c (F.degree c) i.val j.val (a.degree_eq c),
    Access.coefficientInput_code a.bits c (F.degree c) i.val j.val (a.degree_eq c)]
  change (if decide (j.modNat.val ≤ i.modNat.val) then
    a.bits.coefficient (pair c (pair (BinaryNatCode.encode i.divNat.val)
      (pair (BinaryNatCode.encode j.divNat.val) (BinaryNatCode.encode (i.modNat.val - j.modNat.val))))) else []) =
    residueBits (PolynomialCoefficientMatrix.finHom (F.dimension c) (F.degree c) (F.matrix c) i j)
  rw [PolynomialCoefficientMatrix.finHom_apply]
  by_cases h : j.modNat.val ≤ i.modNat.val
  · simp only [h, decide_true, ↓reduceIte, a.coefficient_eq]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    simp [residueBits, BinaryNatCode.encode]

noncomputable def power {F : ModularFamily} (a : ModularAccess F) : MatrixPower.ModularAccess F.power where
  dimension := Access.liftedDimension a.bits
  modulus := a.bits.modulus
  exponent := a.bits.exponent
  row := Access.liftedRow a.bits
  col := Access.liftedCol a.bits
  entry := Access.liftedEntry a.bits
  dimension_eq := fun c => Access.liftedDimension_code a.bits c (F.dimension c) (F.degree c)
    (a.dimension_eq c) (a.degree_eq c)
  modulus_eq := a.modulus_eq
  exponent_eq := a.exponent_eq
  row_eq := fun c => by
    simpa only [ModularFamily.power, finProdFinEquiv, Equiv.coe_fn_mk, Fin.val_last, Nat.mul_comm, Nat.add_comm] using
      Access.liftedRow_code a.bits c (F.row c).val (F.degree c) (a.row_eq c) (a.degree_eq c)
  col_eq := fun c => by
    simpa only [ModularFamily.power, finProdFinEquiv, Equiv.coe_fn_mk, Fin.val_zero, Nat.mul_comm, Nat.zero_add] using
      Access.liftedCol_code a.bits c (F.col c).val (F.degree c) (a.col_eq c) (a.degree_eq c)
  entry_eq := liftedEntry_correct a

theorem power_controls {F : ModularFamily} (a : ModularAccess F) (ha : a.bits.ControlsPolyTime) :
    a.power.ControlsPolyTime := by
  have hd := Access.liftedDimension_mem_FP a.bits ha
  have hr := Access.liftedRow_mem_FP a.bits ha
  have hc := Access.liftedCol_mem_FP a.bits ha
  constructor
  · simpa only [power] using hd
  · simpa only [power] using ha.modulus
  · simpa only [power] using ha.exponent
  · simpa only [power] using hr
  · simpa only [power] using hc

theorem evaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.bits.ControlsPolyTime)
    (E : SpaceFunction a.bits.coefficient) : SpaceFunction F.value := by
  have P := MatrixPower.ModularAccess.evaluatorWithEntry a.power (power_controls a ha)
    (Access.entryEvaluator a.bits ha E)
  refine P.congr ?_
  funext c
  change residueBits ((PolynomialCoefficientMatrix.finHom (F.dimension c) (F.degree c) (F.matrix c) ^
    F.exponent c) (finProdFinEquiv (F.row c, Fin.last (F.degree c))) (finProdFinEquiv (F.col c, 0))) = _
  rw [PolynomialCoefficientMatrix.finHom_pow_last_zero]
  rfl

theorem decider {F : ModularFamily} (a : ModularAccess F) (ha : a.bits.ControlsPolyTime)
    (E : SpaceFunction a.bits.coefficient) : SpaceDecider F.zeroLanguage := by
  let accept := fun bits : List Bool => decide (bits = [])
  have haccept : (fun bits => [accept bits]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  refine (evaluator a ha E).decider accept haccept ?_
  intro c
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  have hz : residueBits (0 : ZMod (F.modulus c)) = [] := by simp [residueBits, BinaryNatCode.encode]
  change ((F.matrix c ^ F.exponent c) (F.row c) (F.col c)).coeff (F.degree c) = 0 ↔
    decide (residueBits (((F.matrix c ^ F.exponent c) (F.row c) (F.col c)).coeff (F.degree c)) = []) = true
  rw [decide_eq_true_eq, ← hz, (residueBits_injective (F.modulus c)).eq_iff]

theorem zeroLanguage_mem_PSPACE_of_evaluator {F : ModularFamily} (a : ModularAccess F)
    (ha : a.bits.ControlsPolyTime) (E : SpaceFunction a.bits.coefficient) : F.zeroLanguage ∈ PSPACE :=
  (decider a ha E).mem_PSPACE

end ModularAccess
end LeanCanny.Algebra.PolynomialPower
