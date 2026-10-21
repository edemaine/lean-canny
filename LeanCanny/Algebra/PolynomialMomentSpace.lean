/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixMomentSpaceEntries
public import LeanCanny.Algebra.PolynomialPowerSpace

/-!
# Space-certified coefficients of polynomial scalar moments

The source/sink augmentation commutes with taking an entry coefficient. A
query carries its degree through the augmented-entry guards, selecting one
coefficient of a border vector or the original matrix. The polynomial power
evaluator then returns a coefficient of `r A^k c` with its full space bound.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixMoment
open Polynomial

theorem matrixFin_coeff {R : Type*} [Semiring R] {n : ℕ}
    (r c : Fin n → R[X]) (A : Matrix (Fin n) (Fin n) R[X]) (d : ℕ)
    (i j : Fin (n + 2)) :
    (matrixFin r c A i j).coeff d =
      matrixFin (fun k => (r k).coeff d) (fun k => (c k).coeff d) (fun k l => (A k l).coeff d) i j := by
  obtain ⟨p, rfl⟩ := (vertexEquiv n).surjective i
  obtain ⟨q, rfl⟩ := (vertexEquiv n).surjective j
  calc
    _ = (matrix r c A p q).coeff d := congrArg (fun f : R[X] => f.coeff d) (matrixFin_apply_vertex r c A p q)
    _ = matrix (fun k => (r k).coeff d) (fun k => (c k).coeff d) (fun k l => (A k l).coeff d) p q := by
      rcases p with ⟨⟩ | (i | ⟨⟩) <;> rcases q with ⟨⟩ | (j | ⟨⟩) <;>
        simp [matrix, sourceRow, withSink, Matrix.fromBlocks]
    _ = _ := (matrixFin_apply_vertex _ _ _ p q).symm

end LeanCanny.Algebra.MatrixMoment

namespace LeanCanny.Algebra.PolynomialMoment
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower
open Polynomial Matrix

structure ModularFamily where
  dimension : List Bool → ℕ
  modulus : List Bool → ℕ
  exponent : List Bool → ℕ
  degree : List Bool → ℕ
  row : (c : List Bool) → Fin (dimension c) → (ZMod (modulus c))[X]
  column : (c : List Bool) → Fin (dimension c) → (ZMod (modulus c))[X]
  matrix : (c : List Bool) → Matrix (Fin (dimension c)) (Fin (dimension c)) (ZMod (modulus c))[X]
  modulus_ne_zero : ∀ c, modulus c ≠ 0

noncomputable def ModularFamily.value (F : ModularFamily) (c : List Bool) : List Bool :=
  residueBits ((F.row c ⬝ᵥ (F.matrix c ^ F.exponent c *ᵥ F.column c)).coeff (F.degree c))

noncomputable def ModularFamily.power (F : ModularFamily) : PolynomialPower.ModularFamily where
  dimension := fun c => F.dimension c + 2
  modulus := F.modulus
  exponent := fun c => F.exponent c + 2
  row := fun _ => 0
  col := fun c => Fin.last (F.dimension c + 1)
  degree := F.degree
  matrix := fun c => MatrixMoment.matrixFin (F.row c) (F.column c) (F.matrix c)
  modulus_ne_zero := F.modulus_ne_zero

structure ModularAccess (F : ModularFamily) where
  bits : MatrixMoment.EntryBits.Access
  modulus : List Bool → List Bool
  exponent : List Bool → List Bool
  degree : List Bool → List Bool
  dimension_eq : ∀ c, bits.dimension c = BinaryNatCode.encode (F.dimension c)
  modulus_eq : ∀ c, modulus c = BinaryNatCode.encode (F.modulus c)
  exponent_eq : ∀ c, exponent c = BinaryNatCode.encode (F.exponent c)
  degree_eq : ∀ c, degree c = BinaryNatCode.encode (F.degree c)
  row_eq : ∀ c j d, bits.row (pair c (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d))) =
    residueBits ((F.row c j).coeff d)
  column_eq : ∀ c i d, bits.column (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode d))) =
    residueBits ((F.column c i).coeff d)
  entry_eq : ∀ c i j d, bits.entry (pair c (pair (BinaryNatCode.encode i.val)
    (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d)))) = residueBits ((F.matrix c i j).coeff d)

structure ModularAccess.ControlsPolyTime {F : ModularFamily} (a : ModularAccess F) : Prop where
  dimension : a.bits.dimension ∈ FP
  modulus : a.modulus ∈ FP
  exponent : a.exponent ∈ FP
  degree : a.degree ∈ FP

def vectorInput (p : List Bool) : List Bool :=
  pair (pairFst (pairFst p)) (pair (pairSnd p) (pairSnd (pairFst p)))

def matrixInput (p : List Bool) : List Bool :=
  pair (pairFst (pairFst p)) (pair (pairFst (pairSnd p)) (pair (pairSnd (pairSnd p)) (pairSnd (pairFst p))))

def augmentedInput (p : List Bool) : List Bool :=
  pair (pair (pairFst p) (pairSnd (pairSnd (pairSnd p))))
    (pair (pairFst (pairSnd p)) (pairFst (pairSnd (pairSnd p))))

theorem vectorInput_mem_FP : vectorInput ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hd := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have h := mem_FP_pair hc (mem_FP_pair pairSnd_mem_FP hd)
  refine mem_FP_of_eq (g := vectorInput) h ?_
  intro p
  simp only [Function.comp_apply, vectorInput]

theorem matrixInput_mem_FP : matrixInput ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hj := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hd := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have h := mem_FP_pair hc (mem_FP_pair hi (mem_FP_pair hj hd))
  refine mem_FP_of_eq (g := matrixInput) h ?_
  intro p
  simp only [Function.comp_apply, matrixInput]

theorem augmentedInput_mem_FP : augmentedInput ∈ FP := by
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have ht := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hj := mem_FP_comp ht pairFst_mem_FP
  have hd := mem_FP_comp ht pairSnd_mem_FP
  have h := mem_FP_pair (mem_FP_pair pairFst_mem_FP hd) (mem_FP_pair hi hj)
  refine mem_FP_of_eq (g := augmentedInput) h ?_
  intro p
  simp only [Function.comp_apply, augmentedInput]

namespace ModularAccess

def scalarBits {F : ModularFamily} (a : ModularAccess F) : MatrixMoment.EntryBits.Access where
  dimension := a.bits.dimension ∘ pairFst
  row := a.bits.row ∘ vectorInput
  column := a.bits.column ∘ vectorInput
  entry := a.bits.entry ∘ matrixInput

def augmentedCoefficient {F : ModularFamily} (a : ModularAccess F) : List Bool → List Bool :=
  MatrixMoment.EntryBits.entry a.scalarBits ∘ augmentedInput

theorem coefficientEvaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (R : SpaceFunction a.bits.row) (C : SpaceFunction a.bits.column) (A : SpaceFunction a.bits.entry) :
    SpaceFunction a.augmentedCoefficient := by
  have hd := mem_FP_comp pairFst_mem_FP ha.dimension
  have ER := R.precompose vectorInput vectorInput_mem_FP
  have EC := C.precompose vectorInput vectorInput_mem_FP
  have EA := A.precompose matrixInput matrixInput_mem_FP
  have E := MatrixMoment.EntryBits.entryEvaluator a.scalarBits hd ER EC EA
  exact E.precompose augmentedInput augmentedInput_mem_FP

theorem augmentedCoefficient_correct {F : ModularFamily} (a : ModularAccess F) (c : List Bool)
    (i j : Fin (F.dimension c + 2)) (d : ℕ) :
    a.augmentedCoefficient (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d)))) =
      residueBits ((MatrixMoment.matrixFin (F.row c) (F.column c) (F.matrix c) i j).coeff d) := by
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  simp only [augmentedCoefficient, augmentedInput, Function.comp_apply, pairFst_pair, pairSnd_pair]
  rw [MatrixMoment.matrixFin_coeff]
  apply MatrixMoment.EntryBits.entry_correct a.scalarBits (pair c (BinaryNatCode.encode d))
    (F.modulus c) (F.dimension c)
    (fun k => (F.row c k).coeff d) (fun k => (F.column c k).coeff d)
    (fun k l => (F.matrix c k l).coeff d)
  · simpa only [scalarBits, Function.comp_apply, pairFst_pair] using a.dimension_eq c
  · intro k
    simpa only [scalarBits, Function.comp_apply, vectorInput, pairFst_pair, pairSnd_pair] using a.row_eq c k d
  · intro k
    simpa only [scalarBits, Function.comp_apply, vectorInput, pairFst_pair, pairSnd_pair] using a.column_eq c k d
  · intro k l
    simpa only [scalarBits, Function.comp_apply, matrixInput, pairFst_pair, pairSnd_pair] using a.entry_eq c k l d

noncomputable def power {F : ModularFamily} (a : ModularAccess F) : PolynomialPower.ModularAccess F.power where
  bits := {
    dimension := MatrixMoment.EntryBits.dimension a.bits
    modulus := a.modulus
    exponent := fun c => BinaryNat.succ (BinaryNat.succ (a.exponent c))
    row := fun _ => []
    col := MatrixMoment.EntryBits.sinkIndex a.bits
    degree := a.degree
    coefficient := a.augmentedCoefficient }
  dimension_eq := fun c => by simp [MatrixMoment.EntryBits.dimension, MatrixMoment.EntryBits.sinkIndex,
    a.dimension_eq, ModularFamily.power, Nat.add_assoc]
  modulus_eq := a.modulus_eq
  exponent_eq := fun c => by simp [a.exponent_eq, ModularFamily.power, Nat.add_assoc]
  row_eq := fun _ => rfl
  col_eq := fun c => by simp [MatrixMoment.EntryBits.sinkIndex, a.dimension_eq, ModularFamily.power]
  degree_eq := a.degree_eq
  coefficient_eq := augmentedCoefficient_correct a

theorem power_controls {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) :
    a.power.bits.ControlsPolyTime := by
  have hd := MatrixMoment.EntryBits.dimension_mem_FP_of_dimension a.bits ha.dimension
  have he := mem_FP_comp (mem_FP_comp ha.exponent BinaryNat.succ_mem_FP) BinaryNat.succ_mem_FP
  have hc := MatrixMoment.EntryBits.sinkIndex_mem_FP_of_dimension a.bits ha.dimension
  exact ⟨hd, ha.modulus, he, constFn_mem_FP [], hc, ha.degree⟩

theorem evaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (R : SpaceFunction a.bits.row) (C : SpaceFunction a.bits.column) (A : SpaceFunction a.bits.entry) :
    SpaceFunction F.value := by
  have E := PolynomialPower.ModularAccess.evaluator a.power (power_controls a ha) (coefficientEvaluator a ha R C A)
  refine E.congr ?_
  funext c
  change residueBits (((MatrixMoment.matrixFin (F.row c) (F.column c) (F.matrix c) ^ (F.exponent c + 2))
    0 (Fin.last (F.dimension c + 1))).coeff (F.degree c)) = _
  rw [MatrixMoment.matrixFin_pow_moment]
  rfl

end ModularAccess
end LeanCanny.Algebra.PolynomialMoment
