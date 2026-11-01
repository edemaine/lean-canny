/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGramUpperCorrect
/-! # The Gram characteristic output is the actual relative value factor

The reflected second nilpotent digit selects the prescribed value factor.
This statement changes neither the selected old parent nor its scalar
embedding, and uses the original fixed nilpotent width.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueCharacteristicExtraction
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedCutSource IntegralMixedValueDoubleNilpotent IntegralMixedValueDeterminantSource
open scoped Classical
attribute [local irreducible] IntegralMixedValueDoubleNilpotent.basis IntegralMixedValueDoubleNilpotent.matrix

theorem coefficient_entry_integer (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (q : List Bool) (hk : 0 < (index q).val) :
    (source F I (IntegralMixedGramCharacteristicSource.zeroChoice F)).coefficientMatrix q 0
      (row F I index q) (col F I q) =
      Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
        (IntegralMixedCutNilpotent.value (F.state q) (F.birth_bound q) (F.rule q)
          (.value (I.coordinate q) (index q))) (I.row q) (I.col q) := by
  let read (z : Second (F.state q)) : ℤ :=
    Algebra.leftMulMatrix (basis (F.state q)) z (row F I index q) (col F I q)
  have HS : (source F I (IntegralMixedGramCharacteristicSource.zeroChoice F)).coefficientMatrix q 0
      (row F I index q) (col F I q) =
      read ((-matrix (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q)).charpoly.coeff 0) := rfl
  rw [HS, negative_charpoly_constant]
  exact determinant_entry (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q) (index q) hk
    (F.scalar_cap q) (I.row q) (I.col q)

theorem coefficient_entry (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (q : List Bool) (hk : 0 < (index q).val) :
    residueBits (((source F I (IntegralMixedGramCharacteristicSource.zeroChoice F)).coefficientMatrix q 0
      (row F I index q) (col F I q) : ℤ) : ZMod (I.modulus q)) =
      residueBits ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
        (IntegralMixedCutNilpotent.value (F.state q) (F.birth_bound q) (F.rule q)
          (.value (I.coordinate q) (index q))) (I.row q) (I.col q) : ℤ) : ZMod (I.modulus q)) := by
  exact source_value F I index q hk

noncomputable def integerValue (F : Family) (key : List Bool) (j r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry
    ((IntegralMixedGramCharacteristicSnapshot.physical F j).coefficientMatrix key 0) r t

theorem integerValue_pull (F : Family) (base : List Bool → List Bool) (q : List Bool) (j r t : ℕ) :
    integerValue (IntegralMixedVirtualQueryBits.pull F base) q j r t = integerValue F (base q) j r t := rfl

theorem characteristic_snapshot (P : IntegralCriticalHistoryTask.Parameters) (F : Family) (q : List Bool) :
    IntegralMixedGramUpperBits.characteristicValue P F q = residueBits
      (integerValue F (IntegralMixedVirtualTaskBits.saved P q) (IntegralCriticalHistoryTask.get P .slot13 q)
        (IntegralCriticalHistoryTask.get P .row q) (IntegralCriticalHistoryTask.get P .col q) :
          ZMod (IntegralCriticalHistoryTask.modulus P q)) := rfl

noncomputable def selectedIndices (F : Family) (j : ℕ)
    (r t : ∀ q, Fin (count (F.birth q + 1) (F.width q)))
    (m : List Bool → ℕ) (hm : ∀ q, m q ≠ 0) : IntegralMixedVirtualSweepSource.Indices F :=
  { IntegralMixedValueHomogeneousSnapshot.pointIndices F j with
    row := r
    col := t
    modulus := m
    modulus_ne_zero := hm }

theorem integerValue_selected_integer (F : Family) (j : ℕ)
    (r t : ∀ q, Fin (count (F.birth q + 1) (F.width q)))
    (m : List Bool → ℕ) (hm : ∀ q, m q ≠ 0)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (q : List Bool) (hk : 0 < (index q).val) :
    integerValue F q j (row F (selectedIndices F j r t m hm) index q).val
      (col F (selectedIndices F j r t m hm) q).val =
      Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
        (IntegralMixedCutNilpotent.value (F.state q) (F.birth_bound q) (F.rule q)
          (.value ((IntegralMixedValueHomogeneousSnapshot.pointIndices F j).coordinate q) (index q)))
        (r q) (t q) := by
  let I := selectedIndices F j r t m hm
  exact (IntegralCriticalTotalSnapshotBits.integerEntry_fin
    ((IntegralMixedGramCharacteristicSnapshot.physical F j).coefficientMatrix q 0)
    (row F I index q) (col F I q)).trans (coefficient_entry_integer F I index q hk)

theorem integerValue_selected (F : Family) (j : ℕ)
    (r t : ∀ q, Fin (count (F.birth q + 1) (F.width q)))
    (m : List Bool → ℕ) (hm : ∀ q, m q ≠ 0)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (q : List Bool) (hk : 0 < (index q).val) :
    residueBits (integerValue F q j (row F (selectedIndices F j r t m hm) index q).val
      (col F (selectedIndices F j r t m hm) q).val : ZMod (m q)) =
      residueBits ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
        (IntegralMixedCutNilpotent.value (F.state q) (F.birth_bound q) (F.rule q)
          (.value ((IntegralMixedValueHomogeneousSnapshot.pointIndices F j).coordinate q) (index q)))
        (r q) (t q) : ℤ) : ZMod (m q)) := by
  let I := selectedIndices F j r t m hm
  have H := IntegralCriticalTotalSnapshotBits.integerEntry_fin
    ((IntegralMixedGramCharacteristicSnapshot.physical F j).coefficientMatrix q 0)
    (row F I index q) (col F I q)
  exact (congrArg (fun z : ℤ => residueBits (z : ZMod (m q))) H).trans
    (coefficient_entry F I index q hk)

end LeanCanny.Algebra.IntegralMixedValueCharacteristicExtraction
