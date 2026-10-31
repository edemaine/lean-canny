/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerSpaceEntries
public import LeanCanny.Algebra.ModularSumSpace
public import LeanCanny.Algebra.ModularResidueSpace
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Streamed matrix polynomial entries from original readers

One requested entry of a bounded coefficient sum of matrix powers is
computed by binary matrix powering and a modular accumulator. The matrix
dimension and coefficient count remain binary. Both original readers
retain their space charges; no matrix or coefficient vector is stored.
-/

@[expose] public section
namespace LeanCanny.Algebra.MatrixPolynomialEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

structure Family where
  dimension : List Bool → ℕ
  count : List Bool → ℕ
  modulus : List Bool → ℕ
  row : (c : List Bool) → Fin (dimension c)
  col : (c : List Bool) → Fin (dimension c)
  matrix : (c : List Bool) → Matrix (Fin (dimension c)) (Fin (dimension c)) (ZMod (modulus c))
  coefficient : (c : List Bool) → ℕ → ZMod (modulus c)
  modulus_ne_zero : ∀ c, modulus c ≠ 0

noncomputable def Family.value (F : Family) (c : List Bool) : List Bool :=
  residueBits (∑ k ∈ Finset.range (F.count c), F.coefficient c k * (F.matrix c ^ k) (F.row c) (F.col c))

structure Access (F : Family) where
  dimension : BinaryFn F.dimension
  count : BinaryFn F.count
  modulus : BinaryFn F.modulus
  row : BinaryFn (fun c => (F.row c).val)
  col : BinaryFn (fun c => (F.col c).val)
  entry : List Bool → List Bool
  coefficient : List Bool → List Bool
  entry_eq : ∀ c (i j : Fin (F.dimension c)),
    entry (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) = residueBits (F.matrix c i j)
  coefficient_eq : ∀ c k, coefficient (pair c (BinaryNatCode.encode k)) = residueBits (F.coefficient c k)

noncomputable def powerFamily (F : Family) : MatrixPower.ModularFamily where
  dimension q := F.dimension (pairFst q)
  modulus q := F.modulus (pairFst q)
  exponent q := Nat.fromBitsLE (pairSnd q)
  row q := F.row (pairFst q)
  col q := F.col (pairFst q)
  matrix q := F.matrix (pairFst q)
  modulus_ne_zero q := F.modulus_ne_zero (pairFst q)

def entryQuery (r : List Bool) : List Bool := pair (pairFst (pairFst r)) (pairSnd r)
theorem entryQuery_FP : entryQuery ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

noncomputable def powerAccess (F : Family) (a : Access F) : MatrixPower.ModularAccess (powerFamily F) where
  dimension q := BinaryNatCode.encode (F.dimension (pairFst q))
  modulus q := BinaryNatCode.encode (F.modulus (pairFst q))
  exponent q := BinaryNat.normalize (pairSnd q)
  row q := BinaryNatCode.encode (F.row (pairFst q)).val
  col q := BinaryNatCode.encode (F.col (pairFst q)).val
  entry := a.entry ∘ entryQuery
  dimension_eq _ := rfl
  modulus_eq _ := rfl
  exponent_eq q := BinaryNat.normalize_eq_bits _
  row_eq _ := rfl
  col_eq _ := rfl
  entry_eq q i j := by
    simp only [Function.comp_apply, entryQuery, pairFst_pair, pairSnd_pair]
    exact a.entry_eq (pairFst q) i j

theorem power_controls (F : Family) (a : Access F) : (powerAccess F a).ControlsPolyTime := by
  have hD : BinaryFn (fun q => F.dimension (pairFst q)) := a.dimension.comp pairFst_mem_FP
  have hM : BinaryFn (fun q => F.modulus (pairFst q)) := a.modulus.comp pairFst_mem_FP
  have hR : BinaryFn (fun q => (F.row (pairFst q)).val) := a.row.comp pairFst_mem_FP
  have hC : BinaryFn (fun q => (F.col (pairFst q)).val) := a.col.comp pairFst_mem_FP
  exact ⟨hD.bits_mem_FP, hM.bits_mem_FP,
    mem_FP_comp (f := pairSnd) (g := BinaryNat.normalize) pairSnd_mem_FP BinaryNat.normalize_mem_FP,
    hR.bits_mem_FP, hC.bits_mem_FP⟩

def coefficientQuery (q : List Bool) : List Bool := pair (pairFst q) (BinaryNat.normalize (pairSnd q))
theorem coefficientQuery_FP : coefficientQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)

def finish (F : Family) (r : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (BinaryNatCode.encode (F.modulus (pairFst (pairFst r)))) (pairSnd r))

theorem finish_FP (F : Family) (a : Access F) : finish F ∈ FP := by
  have hM : BinaryFn (fun r => F.modulus (pairFst (pairFst r))) :=
    a.modulus.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  exact mem_FP_comp (f := fun r => pair (BinaryNatCode.encode (F.modulus (pairFst (pairFst r)))) (pairSnd r))
    (g := BinaryNat.mulMod) (mem_FP_pair hM.bits_mem_FP pairSnd_mem_FP) BinaryNat.mulMod_mem_FP

noncomputable def term (F : Family) (q : List Bool) : List Bool :=
  residueBits (F.coefficient (pairFst q) (Nat.fromBitsLE (pairSnd q)) *
    (F.matrix (pairFst q) ^ Nat.fromBitsLE (pairSnd q)) (F.row (pairFst q)) (F.col (pairFst q)))

theorem term_packet (F : Family) (c : List Bool) (k : ℕ) :
    term F (pair c (BinaryNatCode.encode k)) =
      residueBits (F.coefficient c k * (F.matrix c ^ k) (F.row c) (F.col c)) := by
  generalize hz : pair c (BinaryNatCode.encode k) = q
  have hc : pairFst q = c := by rw [← hz, pairFst_pair]
  have hk : Nat.fromBitsLE (pairSnd q) = k := by rw [← hz, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst c
  subst k
  rfl

theorem term_evaluator (F : Family) (a : Access F) (E : SpaceFunction a.entry) (C : SpaceFunction a.coefficient) :
    SpaceFunction (term F) := by
  have HP := (powerAccess F a).evaluatorWithEntry (power_controls F a) (E.precompose entryQuery entryQuery_FP)
  have HC := C.precompose coefficientQuery coefficientQuery_FP
  have HT := (HC.pairOutputs HP).withInput.postcompose (finish F) (finish_FP F a)
  refine HT.congr (funext fun q => ?_)
  have HE : a.coefficient (coefficientQuery q) = residueBits (F.coefficient (pairFst q) (Nat.fromBitsLE (pairSnd q))) := by
    rw [coefficientQuery, BinaryNat.normalize_eq_bits]
    exact a.coefficient_eq _ _
  let : NeZero (F.modulus (pairFst q)) := ⟨F.modulus_ne_zero (pairFst q)⟩
  simp only [Function.comp_apply, finish, pairFst_pair, pairSnd_pair, HE,
    MatrixPower.ModularFamily.value, powerFamily]
  exact ArithmeticBits.mulMod_residueBits _ _ _

theorem evaluator (F : Family) (a : Access F) (E : SpaceFunction a.entry) (C : SpaceFunction a.coefficient) :
    SpaceFunction F.value := by
  have HM : (fun c => Nat.fromBitsLE (BinaryNatCode.encode (F.modulus c))) = F.modulus :=
    funext (fun c => Nat.fromBitsLE_bits _)
  have HS := ModularSum.evaluatorWithModulus (term_evaluator F a E C)
    (fun c => BinaryNatCode.encode (F.count c)) (fun c => BinaryNatCode.encode (F.modulus c))
    a.count.bits_mem_FP a.modulus.bits_mem_FP F.modulus HM
    (fun c k => F.coefficient c k * (F.matrix c ^ k) (F.row c) (F.col c))
    (fun c => Nat.pos_of_ne_zero (F.modulus_ne_zero c)) (fun c k _ => term_packet F c k)
  exact HS.congr (funext fun c => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Family.value])

end LeanCanny.Algebra.MatrixPolynomialEntryBits
