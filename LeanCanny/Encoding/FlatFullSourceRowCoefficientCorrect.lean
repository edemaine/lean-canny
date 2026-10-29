/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceRowCoefficient

/-! # Exact collected-coefficient semantics of the complete flat reader

The native dispatcher reads the previously constructed indexed system itself.
Its critical branch uses the charged direction record, and its copy branches
retain exactly the preceding ambient coordinate. No row coefficient oracle
or constant-depth assumption is introduced.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceRowCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatFullSourceTower (Inputs arity count degree)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullCriticalSamples.polynomial

def localCoordinate (F : Inputs) (q : List Bool) : Fin (arity F (FlatFullSourceRowQuery.source q)) :=
  ⟨FlatFullSourceRowQuery.localIndex F q, FlatFullSourceRowQuery.localIndex_lt F q⟩

def block (F : Inputs) (z : List Bool) (h : FlatFullSourceRowQuery.Valid F (pairFst z)) :
    Fin (arity F (origin z)) → Fin (count F (origin z)) :=
  TriangularPolynomialRows.block (arity F (origin z)) (FlatFullSourceRowQuery.stageIndex F (pairFst z))
    (F.depth (origin z)) (FlatFullSourceRowQuery.stageIndex_lt F (pairFst z) h)

theorem frame_degree (F : Inputs) (z : List Bool) : degree (frame F) z = degree F (origin z) := rfl

theorem frame_count (F : Inputs) (z : List Bool) : count (frame F) z = count F (origin z) := rfl

theorem frame_polynomial (F : Inputs) (z : List Bool) :
    BoundedFullCriticalSamples.polynomial (frame F).source z =
      BoundedFullCriticalSamples.polynomial F.source (origin z) :=
  FlatFullSourceContext.polynomial_comp F origin z

theorem critical_packet (F : Inputs) (W : List Bool → ℕ) (z : List Bool)
    (h : FlatFullSourceRowQuery.Valid F (pairFst z)) (hW : degree F (origin z) < 2 ^ W (origin z)) :
    criticalValue F W z = MatrixPower.residueBits
      (((rename (block F z h) (ProjectionCriticalFamily.spatialEquation
        (BoundedFullCriticalSamples.polynomial F.source (origin z))
        (F.pivot (origin z) (FlatFullSourceRowQuery.stageIndex F (pairFst z)))
        (fun _ => (directionNat F z : ℤ)) (localCoordinate F (pairFst z)))).coeff
          (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (count F (origin z)))) (W (origin z))
            (Nat.fromBitsLE (target z))) : ℤ) : ZMod (Nat.fromBitsLE (modulus z) + 1)) := by
  have H := FlatFullSourceCriticalCoefficient.packet (frame F) (offset F) (width W) (base F) (current F)
    target modulus (direction F) z (FlatFullSourceRowQuery.block_fit F (pairFst z) h)
    (F.pivot (origin z) (FlatFullSourceRowQuery.stageIndex F (pairFst z))) (localCoordinate F (pairFst z))
    (directionNat F z) rfl (FlatFullSourceRowQuery.split_row F (pairFst z)).symm
    (by simpa only [frame_degree, width] using hW) (direction_eq F z)
  have hb : BlockRenameCoefficient.shift (arity (frame F) z) (count (frame F) z) (offset F z)
      (FlatFullSourceRowQuery.block_fit F (pairFst z) h) = block F z h := by
    funext i
    exact Fin.ext rfl
  rw [frame_polynomial] at H
  simp only [hb] at H
  simpa only [criticalValue, width, count, arity, frame, FlatFullSourceContext.comp,
    BoundedFullWriter.Readers.comp, Function.comp_apply] using H

theorem copy_packet (F : Inputs) (W : List Bool → ℕ) (z : List Bool)
    (h : FlatFullSourceRowQuery.Valid F (pairFst z)) :
    copyValue F W z = MatrixPower.residueBits
      ((((X (block F z h (localCoordinate F (pairFst z))) -
        FlatCriticalIndexedRows.previousPolynomial (FlatFullSourceRowQuery.stageIndex F (pairFst z))
          (F.depth (origin z)) (FlatFullSourceRowQuery.stageIndex_lt F (pairFst z) h)
          (localCoordinate F (pairFst z)) : MvPolynomial (Fin (count F (origin z))) ℤ)).coeff
            (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (count F (origin z)))) (W (origin z))
              (Nat.fromBitsLE (target z))) : ℤ) : ZMod (Nat.fromBitsLE (modulus z) + 1)) := by
  have hc : current F z = (block F z h (localCoordinate F (pairFst z))).val :=
    (FlatFullSourceRowQuery.split_row F (pairFst z)).symm
  by_cases h0 : FlatFullSourceRowQuery.stageIndex F (pairFst z) = 0
  · rw [copyValue, ite_eq_left h0]
    have hp : FlatCriticalIndexedRows.previousPolynomial (FlatFullSourceRowQuery.stageIndex F (pairFst z))
        (F.depth (origin z)) (FlatFullSourceRowQuery.stageIndex_lt F (pairFst z) h)
        (localCoordinate F (pairFst z)) = (0 : MvPolynomial (Fin (count F (origin z))) ℤ) := by
      unfold FlatCriticalIndexedRows.previousPolynomial
      exact ite_eq_left h0
    rw [hp, sub_zero]
    exact FixedWidthLinearCoefficientBits.packet (count (frame F)) (width W) (current F) target
      (FlatFullSourceCriticalCoefficient.modulusCode modulus) z _ hc _
      (FlatFullSourceCriticalCoefficient.modulusCode_eq modulus z)
  · rw [copyValue, ite_eq_right h0]
    let old : Fin (count F (origin z)) := TriangularPolynomialRows.block (arity F (origin z))
      (FlatFullSourceRowQuery.stageIndex F (pairFst z) - 1) (F.depth (origin z))
      (by
        have hh : FlatFullSourceRowQuery.stageIndex F (pairFst z) < F.depth (origin z) :=
          FlatFullSourceRowQuery.stageIndex_lt F (pairFst z) h
        omega) (localCoordinate F (pairFst z))
    have hp : FlatCriticalIndexedRows.previousPolynomial (FlatFullSourceRowQuery.stageIndex F (pairFst z))
        (F.depth (origin z)) (FlatFullSourceRowQuery.stageIndex_lt F (pairFst z) h)
        (localCoordinate F (pairFst z)) = (X old : MvPolynomial (Fin (count F (origin z))) ℤ) := by
      unfold FlatCriticalIndexedRows.previousPolynomial
      rw [ite_eq_right h0]
      rfl
    rw [hp]
    exact FixedWidthLinearCoefficientBits.difference_packet (count (frame F)) (width W) (current F) target
      (FlatFullSourceCriticalCoefficient.modulusCode modulus) (previous F) z _ old hc rfl _
      (FlatFullSourceCriticalCoefficient.modulusCode_eq modulus z)

theorem consumer_packet (F : Inputs) (W : List Bool → ℕ) (z : List Bool)
    (i : Fin (count F (origin z))) (hi : FlatFullSourceRowQuery.rawRow (pairFst z) = i.val)
    (hW : degree F (origin z) < 2 ^ W (origin z))
    (hrecord : pairSnd z = F.direction (FlatFullSourceRowQuery.stageQuery F (pairFst z))) :
    consumer F W z = MatrixPower.residueBits
      (((FlatFullSourceTower.system F (origin z) i).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (count F (origin z)))) (W (origin z))
          (Nat.fromBitsLE (target z))) : ℤ) : ZMod (Nat.fromBitsLE (modulus z) + 1)) := by
  have h : FlatFullSourceRowQuery.Valid F (pairFst z) := by
    change FlatFullSourceRowQuery.rawRow (pairFst z) < count F (origin z)
    rw [hi]
    exact i.isLt
  have hr : block F z h (localCoordinate F (pairFst z)) = i := by
    apply Fin.ext
    exact (FlatFullSourceRowQuery.split_row F (pairFst z)).trans
      ((FlatFullSourceRowQuery.rowIndex_of_valid F (pairFst z) h).trans hi)
  have hrow := FlatCriticalIndexedRows.system_row (BoundedFullCriticalSamples.polynomial F.source (origin z))
    (FlatFullSourceTower.free F (origin z)) (F.pivot (origin z)) (FlatFullSourceTower.direction F (origin z))
    (FlatFullSourceRowQuery.stageIndex F (pairFst z)) (F.depth (origin z))
    (FlatFullSourceRowQuery.stageIndex_lt F (pairFst z) h) (localCoordinate F (pairFst z))
  change FlatFullSourceTower.system F (origin z) (block F z h (localCoordinate F (pairFst z))) = _ at hrow
  rw [hr] at hrow
  rw [consumer, ite_eq_left h, hrow]
  by_cases hs : FlatFullSourceRowQuery.InFree F (pairFst z)
  · have hm : localCoordinate F (pairFst z) ∈ FlatFullSourceTower.free F (origin z)
        (FlatFullSourceRowQuery.stageIndex F (pairFst z)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    rw [ite_eq_left hs, critical_packet F W z h hW, FlatCriticalIndexedRows.row, ite_eq_left hm]
    have hv : (directionNat F z : ℤ) = FlatFullSourceTower.direction F (origin z)
        (FlatFullSourceRowQuery.stageIndex F (pairFst z)) (localCoordinate F (pairFst z)) := by
      unfold directionNat directionBits
      rw [hrecord]
      rfl
    have hp : ProjectionCriticalFamily.spatialEquation (BoundedFullCriticalSamples.polynomial F.source (origin z))
        (F.pivot (origin z) (FlatFullSourceRowQuery.stageIndex F (pairFst z))) (fun _ => (directionNat F z : ℤ))
        (localCoordinate F (pairFst z)) =
      ProjectionCriticalFamily.spatialEquation (BoundedFullCriticalSamples.polynomial F.source (origin z))
        (F.pivot (origin z) (FlatFullSourceRowQuery.stageIndex F (pairFst z)))
        (FlatFullSourceTower.direction F (origin z) (FlatFullSourceRowQuery.stageIndex F (pairFst z)))
        (localCoordinate F (pairFst z)) := by
      unfold ProjectionCriticalFamily.spatialEquation
      split_ifs
      · rfl
      · rw [hv]
    exact congrArg (fun p : MvPolynomial (Fin (arity F (origin z))) ℤ => MatrixPower.residueBits
      (((rename (block F z h) p).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (count F (origin z)))) (W (origin z))
          (Nat.fromBitsLE (target z))) : ℤ) : ZMod (Nat.fromBitsLE (modulus z) + 1))) hp
  · have hm : localCoordinate F (pairFst z) ∉ FlatFullSourceTower.free F (origin z)
        (FlatFullSourceRowQuery.stageIndex F (pairFst z)) := fun hm => hs (Finset.mem_filter.mp hm).2
    rw [ite_eq_right hs, copy_packet F W z h, FlatCriticalIndexedRows.row, ite_eq_right hm]
    rfl

theorem value_at_row (F : Inputs) (W : List Bool → ℕ) (q : List Bool)
    (i : Fin (count F (FlatFullSourceRowQuery.source q))) (hi : FlatFullSourceRowQuery.rawRow q = i.val)
    (hW : degree F (FlatFullSourceRowQuery.source q) < 2 ^ W (FlatFullSourceRowQuery.source q)) :
    value F W q = MatrixPower.residueBits
      (((FlatFullSourceTower.system F (FlatFullSourceRowQuery.source q) i).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (count F (FlatFullSourceRowQuery.source q))))
          (W (FlatFullSourceRowQuery.source q)) (Nat.fromBitsLE (FlatFullSourceRowQuery.target q))) : ℤ) :
            ZMod (Nat.fromBitsLE (FlatFullSourceRowQuery.modulus q) + 1)) := by
  unfold value
  generalize hz : FlatFullSourceRowQuery.prepare F q = z
  have hq : pairFst z = q := by rw [← hz, FlatFullSourceRowQuery.prepare, pairFst_pair]
  have hd : pairSnd z = F.direction (FlatFullSourceRowQuery.stageQuery F (pairFst z)) := by
    rw [hq, ← hz, FlatFullSourceRowQuery.prepare, pairSnd_pair]
    rfl
  subst q
  exact consumer_packet F W z i hi hW hd

end LeanCanny.Encoding.FlatFullSourceRowCoefficient
