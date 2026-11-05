/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValueTestQuery
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientQuery
public import LeanCanny.Algebra.IntegralOriginalTermCoefficientSpace
/-! # One original-term call reads the literal frozen radial test row -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterValueTestSource
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MatrixPower FixedWidthPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local instance radialValueTestParameterNeZero (z : List Bool) :
    NeZero (FormulaSignSlotRadialCenterValueTestQuery.parameterCount z) :=
  ⟨by unfold FormulaSignSlotRadialCenterValueTestQuery.parameterCount FormulaSignSlotRadialCenterValuePacking.arity; omega⟩

noncomputable def spatial (z : List Bool) := nativeExponent
  (Equiv.refl (Fin (FormulaSignSlotRadialFormalInput.spatial (FormulaSignSlotRadialCenterValueTestQuery.original z))))
  (FormulaSignSlotRadialCenterValueTestQuery.spatialWidth z) (Nat.fromBitsLE (MacaulayFullBoxBits.shift z))
noncomputable def parameter (z : List Bool) := nativeExponent
  (Equiv.refl (Fin (d (FormulaSignSlotRadialCenterValueTestQuery.original z) + 1)))
  (FormulaSignSlotRadialCenterValueTestQuery.parameterWidth z)
  (Nat.fromBitsLE (FormulaSignSlotRadialCenterValueTestQuery.parameter z))

private theorem spatial_entry (z : List Bool) (i : Fin (FormulaSignSlotRadialCenterValueTestQuery.spatialCount z)) :
    FormulaSignSlotRadialCenterValueTestQuery.spatialEntry z i.val = spatial z i := by
  rw [FormulaSignSlotRadialCenterValueTestQuery.spatialEntry, FixedWidthQuery.entry, ite_eq_left i.isLt]
  simp only [spatial, nativeExponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.refl_apply,
    FixedWidthBlockRenameBits.entry_bits, FixedWidthQuery.coordinate]
private theorem parameter_entry (z : List Bool) (i : Fin (FormulaSignSlotRadialCenterValueTestQuery.parameterCount z)) :
    FormulaSignSlotRadialCenterValueTestQuery.parameterEntry z i.val = parameter z i := by
  rw [FormulaSignSlotRadialCenterValueTestQuery.parameterEntry, FixedWidthQuery.entry, ite_eq_left i.isLt]
  simp only [parameter, nativeExponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.refl_apply,
    FixedWidthBlockRenameBits.entry_bits, FixedWidthQuery.coordinate]

private theorem parameter_entry_succ (z : List Bool) (i : Fin (d (FormulaSignSlotRadialCenterValueTestQuery.original z))) :
    FormulaSignSlotRadialCenterValueTestQuery.parameterEntry z (i.val + 1) = (parameter z).tail i := by
  have HI : i.val + 1 < FormulaSignSlotRadialCenterValueTestQuery.parameterCount z := Nat.succ_lt_succ i.isLt
  rw [FormulaSignSlotRadialCenterValueTestQuery.parameterEntry, FixedWidthQuery.entry, ite_eq_left HI]
  simp only [Finsupp.tail_apply, parameter, nativeExponent, Finsupp.coe_equivFunOnFinite_symm,
    Equiv.refl_apply, FixedWidthBlockRenameBits.entry_bits, FixedWidthQuery.coordinate, Fin.val_succ]

section
attribute [local irreducible] FormulaSignSlotRadialFormalInput.spatial

private theorem spatial_index_value (c : List Bool) (i : Fin (FormulaSignSlotRadialFormalInput.spatial c)) :
    (FormulaSignSlotRadialFormalInput.spatialIndex c i).val = i.val := rfl
private theorem center_index_value (c : List Bool) (i : Fin (d c)) :
    (FormulaSignSlotRadialFormalInput.formalCenterIndex c i).val = FormulaSignSlotRadialFormalInput.spatial c + i.val := rfl
private theorem radius_index_value (c : List Bool) :
    (FormulaSignSlotRadialFormalInput.formalRadiusIndex c).val = FormulaSignSlotRadialFormalInput.spatial c + d c := rfl
private theorem spatial_count (z : List Bool) : FormulaSignSlotRadialFormalInput.spatial
    (FormulaSignSlotRadialCenterValueTestQuery.original z) = FormulaSignSlotRadialCenterValueTestQuery.spatialCount z := rfl
private theorem center_count (z : List Bool) : d (FormulaSignSlotRadialCenterValueTestQuery.original z) =
    FormulaSignSlotRadialCenterValueTestQuery.centers z := rfl

theorem spatial_projection (z : List Bool) : FormulaSignSlotRadialEliminantCoefficientQuery.spatial
    (FormulaSignSlotRadialCenterValueTestQuery.original z) (FormulaSignSlotRadialCenterValueTestQuery.exponent z) = spatial z := by
  ext i
  dsimp only [FormulaSignSlotRadialEliminantCoefficientQuery.spatial, Finsupp.coe_equivFunOnFinite_symm]
  refine (FormulaSignSlotRadialCenterValueTestQuery.exponent_entry z
    (FormulaSignSlotRadialFormalInput.spatialIndex (FormulaSignSlotRadialCenterValueTestQuery.original z) i)).trans ?_
  refine (congrArg (FormulaSignSlotRadialCenterValueTestQuery.entry z) (spatial_index_value _ i)).trans ?_
  have HI : i.val < FormulaSignSlotRadialCenterValueTestQuery.spatialCount z := i.isLt
  rw [FormulaSignSlotRadialCenterValueTestQuery.entry, ite_eq_left HI]
  exact spatial_entry z i

private theorem entry_center (z : List Bool) (i : ℕ)
    (hi : i < FormulaSignSlotRadialCenterValueTestQuery.centers z) :
    FormulaSignSlotRadialCenterValueTestQuery.entry z
      (FormulaSignSlotRadialCenterValueTestQuery.spatialCount z + i) =
        FormulaSignSlotRadialCenterValueTestQuery.parameterEntry z (i + 1) := by
  rw [FormulaSignSlotRadialCenterValueTestQuery.entry, ite_eq_right (by omega),
    ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem center_projection (z : List Bool) : FormulaSignSlotRadialEliminantCoefficientQuery.center
    (FormulaSignSlotRadialCenterValueTestQuery.original z) (FormulaSignSlotRadialCenterValueTestQuery.exponent z) =
      (parameter z).tail := by
  ext i
  dsimp only [FormulaSignSlotRadialEliminantCoefficientQuery.center, Finsupp.coe_equivFunOnFinite_symm]
  refine (FormulaSignSlotRadialCenterValueTestQuery.exponent_entry z
    (FormulaSignSlotRadialFormalInput.formalCenterIndex (FormulaSignSlotRadialCenterValueTestQuery.original z) i)).trans ?_
  refine (congrArg (FormulaSignSlotRadialCenterValueTestQuery.entry z) (center_index_value _ i)).trans ?_
  refine (congrArg (FormulaSignSlotRadialCenterValueTestQuery.entry z)
    (congrArg (fun a : ℕ => a + i.val) (spatial_count z))).trans ?_
  refine (entry_center z i.val i.isLt).trans ?_
  exact parameter_entry_succ z i

theorem radius_projection (z : List Bool) : FormulaSignSlotRadialEliminantCoefficientQuery.radius
    (FormulaSignSlotRadialCenterValueTestQuery.original z) (FormulaSignSlotRadialCenterValueTestQuery.exponent z) =
      parameter z 0 := by
  dsimp only [FormulaSignSlotRadialEliminantCoefficientQuery.radius]
  refine (FormulaSignSlotRadialCenterValueTestQuery.exponent_entry z
    (FormulaSignSlotRadialFormalInput.formalRadiusIndex (FormulaSignSlotRadialCenterValueTestQuery.original z))).trans ?_
  refine (congrArg (FormulaSignSlotRadialCenterValueTestQuery.entry z) (radius_index_value _)).trans ?_
  refine (congrArg (FormulaSignSlotRadialCenterValueTestQuery.entry z)
    (congrArg₂ (fun a b : ℕ => a + b) (spatial_count z) (center_count z))).trans ?_
  rw [FormulaSignSlotRadialCenterValueTestQuery.entry, ite_eq_right (by omega), ite_eq_right (by omega)]
  exact parameter_entry z 0

theorem exponent_eq (z : List Bool) : FormulaSignSlotRadialCenterValueTestQuery.exponent z =
    FormulaSignSlotRadialEliminantSource.exponent (FormulaSignSlotRadialCenterValueTestQuery.original z)
      (spatial z) (parameter z 0) (parameter z).tail := by
  have H := FormulaSignSlotRadialEliminantCoefficientQuery.reconstruct
    (FormulaSignSlotRadialCenterValueTestQuery.original z) (FormulaSignSlotRadialCenterValueTestQuery.exponent z)
  rw [spatial_projection, radius_projection, center_projection] at H
  exact H.symm

end

noncomputable def integer (z : List Bool) : MvPolynomial
    (Fin (FormulaSignSlotRadialCenterValueTestQuery.fullCount z)) ℤ :=
  FormulaSignSlotRadialFormalInput.polynomial (FormulaSignSlotRadialCenterValueTestQuery.original z)
noncomputable def termWord (z : List Bool) :=
  (FormulaSignSlotRadialFormalInput.equation (FormulaSignSlotRadialCenterValueTestQuery.original z)).toData.toBits
noncomputable def value (z : List Bool) := residueBits ((integer z).coeff
  (FormulaSignSlotRadialCenterValueTestQuery.exponent z) :
    ZMod (Nat.fromBitsLE (FormulaSignSlotRadialCenterValueTestQuery.modulus z) + 1))

private theorem scalar_packet (A W M : List Bool → ℕ)
    (p : (z : List Bool) → MvPolynomial (Fin (A z)) ℤ) (z bits : List Bool) :
    IntegralOriginalTermCoefficientBits.scalar A W M p (pair z bits) = residueBits
      ((p z).coeff (nativeExponent (Equiv.refl _) (W z) (Nat.fromBitsLE bits)) : ZMod (M z)) := by
  generalize HZ : pair z bits = q
  have HC : pairFst q = z := by rw [← HZ, pairFst_pair]
  have HT : Nat.fromBitsLE (pairSnd q) = Nat.fromBitsLE bits := by rw [← HZ, pairSnd_pair]
  subst z
  unfold IntegralOriginalTermCoefficientBits.scalar
  rw [← HT]
  apply congrArg (fun e => residueBits ((p (pairFst q)).coeff e : ZMod (M (pairFst q))))
  ext i
  rfl

theorem evaluator : SpaceFunction value := by
  have HWord : termWord ∈ FP := mem_FP_comp FormulaSignSlotRadialCenterValueTestQuery.original_FP
    FormulaSignSlotRadialFormalInput.equation_FP
  have HA : ∀ z, (ETR.TermView.term (termWord z)).arity ≤ FormulaSignSlotRadialCenterValueTestQuery.fullCount z := by
    intro z
    rw [termWord, ETR.TermView.term_toBits]
    exact FormulaSignSlotRadialFormalInput.scope _
  have HE : ∀ z, (ETR.TermView.term (termWord z)).finitePolynomial
      (FormulaSignSlotRadialCenterValueTestQuery.fullCount z) = integer z := by
    intro z
    rw [termWord, ETR.TermView.term_toBits]
    exact FormulaSignSlotRadialFormalInput.finitePolynomial_eq _
  have E := IntegralOriginalTermCoefficientBits.evaluator
    FormulaSignSlotRadialCenterValueTestQuery.fullCount FormulaSignSlotRadialCenterValueTestQuery.width
    (fun z => Nat.fromBitsLE (FormulaSignSlotRadialCenterValueTestQuery.modulus z) + 1)
    FormulaSignSlotRadialCenterValueTestQuery.fullCount_unary FormulaSignSlotRadialCenterValueTestQuery.width_unary
    ((BinaryFn.fromBits FormulaSignSlotRadialCenterValueTestQuery.modulus_FP).add (BinaryFn.const 1))
    (fun _ => Nat.succ_ne_zero _) integer termWord HWord HA HE
  have EQ := E.precompose (fun z => pair z (FormulaSignSlotRadialCenterValueTestQuery.word z))
    (mem_FP_pair id_mem_FP FormulaSignSlotRadialCenterValueTestQuery.word_FP)
  exact EQ.congr (funext fun z => by
    simp only [Function.comp_apply]
    rw [scalar_packet]
    rfl)

theorem coefficient (z : List Bool) : value z = residueBits
    (((((FormulaSignSlotRadialFormalCenter.polynomial (FormulaSignSlotRadialCenterValueTestQuery.original z)).coeff
      (spatial z)).coeff (parameter z 0)).coeff (parameter z).tail : ℤ) :
        ZMod (Nat.fromBitsLE (FormulaSignSlotRadialCenterValueTestQuery.modulus z) + 1)) := by
  have HF : FormulaSignSlotRadialEliminantSource.flatten (FormulaSignSlotRadialCenterValueTestQuery.original z)
      (FormulaSignSlotRadialFormalCenter.polynomial (FormulaSignSlotRadialCenterValueTestQuery.original z)) = integer z :=
    FormulaSignSlotRadialEliminantSource.flatten_eq _ _
  rw [value, ← HF, exponent_eq]
  exact congrArg (fun a : ℤ => residueBits (a :
    ZMod (Nat.fromBitsLE (FormulaSignSlotRadialCenterValueTestQuery.modulus z) + 1)))
      (FormulaSignSlotRadialEliminantSource.coefficient _ _ (spatial z) (parameter z 0) (parameter z).tail)

end LeanCanny.Encoding.FormulaSignSlotRadialCenterValueTestSource
