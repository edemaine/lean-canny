/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueDoubleNilpotent
public import LeanCanny.Algebra.IntegralMixedVirtualSweepSource
public import LeanCanny.Algebra.IntegralBerkowitzBlockSource
public import LeanCanny.Algebra.IntegralMixedCutQueries

/-! # An actual finite-algebra determinant source for value cuts

The source is the negative of the double-nilpotent Gram matrix. Its
constant characteristic coefficient is exactly the original determinant,
so no parity correction is hidden in the interface. The second basis
digit selects the reflected reciprocal-value coefficient. Label zero is
an explicit immediate-zero case; positive labels preserve the actual
relative cut over the same old algebra and require no physical sample.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueDeterminantSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCoordinateBasis
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource IntegralMixedValueDoubleNilpotent
open scoped Classical
attribute [local irreducible] IntegralMixedValueDoubleNilpotent.basis IntegralMixedValueDoubleNilpotent.matrix

theorem negative_charpoly_constant {A : Type*} [CommRing A] {d : ℕ} (M : Matrix (Fin d) (Fin d) A) :
    (-M).charpoly.coeff 0 = M.det := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.charpoly, _root_.eval_det, Matrix.matPolyEquiv_charmatrix]
  simp

noncomputable def row (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (q : List Bool) : Fin (count (F.birth q + 2) (F.width q)) :=
  pairIndex (F.birth q + 1) (F.width q) (I.row q,
    ⟨reflectedIndex (F.spatial q) (F.rule q) (index q),
      reflectedIndex_lt (F.spatial q) (F.rule q) (index q) (F.scalar_cap q)⟩)

def col (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (q : List Bool) : Fin (count (F.birth q + 2) (F.width q)) :=
  pairIndex (F.birth q + 1) (F.width q) (I.col q, 0)

noncomputable def source (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q))) : IntegralBerkowitzBlockBits.Source where
  dimension q := count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
    (IntegralMixedGridValue.width (F.spatial q) (F.rule q))
  rank q := count (F.birth q + 2) (F.width q)
  carrier q := Second (F.state q)
  ring _ := inferInstance
  nontrivial q := nontrivial_of_ne _ _ ((basis (F.state q)).ne_zero (row F I index q))
  basis q := (basis (F.state q))
  matrix q := -matrix (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q)
  modulus := I.modulus
  modulus_ne_zero := I.modulus_ne_zero
  coefficient _ := 0
  basisRow := row F I index
  basisCol := col F I

theorem source_value (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (q : List Bool) (hk : 0 < (index q).val) :
    (source F I index).value q = residueBits ((Algebra.leftMulMatrix
      (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      (IntegralMixedCutNilpotent.value (F.state q) (F.birth_bound q) (F.rule q)
        (.value (I.coordinate q) (index q))) (I.row q) (I.col q) : ℤ) : ZMod (I.modulus q)) := by
  let read (a : Second (F.state q)) : List Bool := residueBits
    ((Algebra.leftMulMatrix (basis (F.state q)) a (row F I index q) (col F I q) : ℤ) : ZMod (I.modulus q))
  have HS : (source F I index).value q =
      read ((-matrix (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q)).charpoly.coeff 0) := rfl
  rw [HS, negative_charpoly_constant]
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (I.modulus q)))
    (determinant_entry (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q) (index q) hk
      (F.scalar_cap q) (I.row q) (I.col q))

noncomputable def value (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q))) (q : List Bool) : List Bool :=
  if (index q).val = 0 then [] else (source F I index).value q

theorem value_eq (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q))) (q : List Bool) :
    value F I index q = residueBits ((Algebra.leftMulMatrix
      (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      (IntegralMixedCutNilpotent.value (F.state q) (F.birth_bound q) (F.rule q)
        (.value (I.coordinate q) (index q))) (I.row q) (I.col q) : ℤ) : ZMod (I.modulus q)) := by
  unfold value
  split_ifs with H
  · have HE : index q = ⟨0, by change 0 < IntegralMixedGridValue.dimension (F.spatial q) (F.rule q) + 2; omega⟩ := Fin.ext H
    have HZ : IntegralMixedCutNilpotent.value (F.state q) (F.birth_bound q) (F.rule q)
        (.value (I.coordinate q) (index q)) = 0 := by
      rw [HE]
      exact IntegralMixedValueMatrixSource.nilpotent_value_zero _ _ _ _
    let read (a : First (F.state q)) : List Bool := residueBits
      ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis a (I.row q) (I.col q) : ℤ) :
        ZMod (I.modulus q))
    change [] = read _
    rw [HZ]
    simp only [read, map_zero, Matrix.zero_apply, Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]
  · exact source_value F I index q (by omega)

theorem source_rank_cap (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q))) (q : List Bool) :
    (source F I index).rank q ≤ count (F.cap q + 2) (F.width q) := rank_cap (F.birth_bound q)

theorem source_rank_bits (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q))) (q : List Bool) :
    ((source F I index).rank q).size ≤ F.width q * (F.cap q + 2) + 1 := rank_bits (F.birth_bound q)

theorem source_dimension_cap (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q))) (q : List Bool) :
    (source F I index).dimension q ≤
      IntegralMixedExceptionalBounds.valueDimension (F.ambient q + 1) (F.spatial q).degree := by
  simpa only [source, Fintype.card_fin] using
    IntegralMixedValueMatrixSource.matrix_size_le (F.spatial q) (F.rule q)

theorem cut_packet (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (q mw : List Bool) (hkind : F.kind q = .value (I.coordinate q) (index q))
    (hmodulus : I.modulus q = Nat.fromBitsLE mw + 1) :
    value F I index q = IntegralMixedCutQueries.value F
      (pair (pair q mw) (pair (BinaryNatCode.encode (I.row q).val) (BinaryNatCode.encode (I.col q).val))) := by
  have HP := IntegralMixedCutQueries.value_packet F q mw (I.row q) (I.col q)
  rw [hkind] at HP
  exact (value_eq F I index q).trans ((congrArg (fun modulus : ℕ => residueBits
    ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      (IntegralMixedCutNilpotent.value (F.state q) (F.birth_bound q) (F.rule q)
        (.value (I.coordinate q) (index q))) (I.row q) (I.col q) : ℤ) : ZMod modulus)) hmodulus).trans HP.symm)

end LeanCanny.Algebra.IntegralMixedValueDeterminantSource
