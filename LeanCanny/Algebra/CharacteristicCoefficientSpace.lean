/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzSpaceEntries

/-! # Native modular characteristic coefficients from space-bounded entries

The layered Berkowitz power already contains every characteristic coefficient.
Only its selected row changes; the complete factor and original-entry child
computations retain their space certificates. The selected index is reduced
modulo dimension plus one, also for an empty matrix.
-/

@[expose] public section
namespace LeanCanny.Algebra.Berkowitz.CharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower

def selected (a : FactorChild.Access) (index : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.mod (pair (index c) (BinaryNat.succ (a.dimension c)))

theorem selected_FP (a : FactorChild.Access) (ha : a.dimension ∈ FP)
    {index : List Bool → List Bool} (hi : index ∈ FP) : selected a index ∈ FP := by
  have H := mem_FP_comp (mem_FP_pair hi (mem_FP_comp ha BinaryNat.succ_mem_FP)) BinaryNat.mod_mem_FP
  exact mem_FP_of_eq H (fun _ => by simp only [selected, Function.comp_apply])

def indexFin (F : ModularFamily) (index : List Bool → List Bool) (c : List Bool) : Fin (F.dimension c + 1) :=
  ⟨Nat.fromBitsLE (index c) % (F.dimension c + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

noncomputable def powerFamily (F : ModularFamily) (index : List Bool → List Bool) : MatrixPower.ModularFamily where
  dimension c := (F.dimension c + 1) * (F.dimension c + 1)
  modulus := F.modulus
  exponent := F.dimension
  row c := (powerQuery (F.dimension c) (indexFin F index c)).row
  col c := (powerQuery (F.dimension c) (indexFin F index c)).col
  matrix c := powerMatrix (F.matrix c)
  modulus_ne_zero := F.modulus_ne_zero

noncomputable def powerAccess {F : ModularFamily} (a : ModularAccess F) (index : List Bool → List Bool) :
    MatrixPower.ModularAccess (powerFamily F index) where
  dimension := PowerAccessBits.dimension a.access
  modulus := a.access.modulus
  exponent := a.access.dimension
  row := selected a.access index
  col := PowerAccessBits.target a.access
  entry := a.factorValue
  dimension_eq c := PowerAccessBits.dimension_code a.access c (F.dimension c) (a.correct c).dimension
  modulus_eq c := (a.correct c).modulus
  exponent_eq c := (a.correct c).dimension
  row_eq c := by
    simp only [selected, (a.correct c).dimension, BinaryNat.succ_eq_bits, BinaryNat.mod_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
    simp [powerFamily, powerQuery, indexFin, finProdFinEquiv]
  col_eq c := by
    simpa [powerFamily, powerQuery, finProdFinEquiv, Nat.mul_comm] using
      PowerAccessBits.target_code a.access c (F.dimension c) (a.correct c).dimension
  entry_eq := a.factorValue_packet

theorem controls {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    {index : List Bool → List Bool} (hi : index ∈ FP) : (powerAccess a index).ControlsPolyTime := by
  have H := a.powerControls ha
  exact ⟨H.dimension, H.modulus, H.exponent, selected_FP a.access ha.dimension hi, H.col⟩

noncomputable def value (F : ModularFamily) (index : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits ((F.matrix c).charpoly.coeff (indexFin F index c).val)

theorem evaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    {index : List Bool → List Bool} (hi : index ∈ FP) (E : SpaceFunction a.access.entry) :
    SpaceFunction (value F index) := by
  have H := MatrixPower.ModularAccess.evaluatorWithEntry (powerAccess a index) (controls a ha hi)
    (a.factorEvaluator ha E)
  apply H.congr
  funext c
  change residueBits ((powerMatrix (F.matrix c) ^ F.dimension c)
    (powerQuery (F.dimension c) (indexFin F index c)).row
    (powerQuery (F.dimension c) (indexFin F index c)).col) = _
  rw [powerMatrix_pow]
  rfl

end LeanCanny.Algebra.Berkowitz.CharacteristicBits
