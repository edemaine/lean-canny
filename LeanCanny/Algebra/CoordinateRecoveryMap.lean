/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitivePairCoordinates

/-! # Injective coefficient extension of the actual recovery formulas

Injectivity preserves the integer source degrees and the direct linear branches.
Thus the native integer resultant and coordinate formulas agree with the field
formulas used in the root-recovery theorem.
-/

@[expose] public section

namespace LeanCanny.Algebra.CoordinateRecoveryMap
open Polynomial
variable {R S : Type*} [CommRing R] [CommRing S]

theorem shift (phi : R →+* S) (p : R[X]) (c : ℕ) :
    (shiftFamily p c).map (Polynomial.mapRingHom phi) = shiftFamily (p.map phi) c := by
  simp [shiftFamily, Polynomial.map_comp, Polynomial.map_map, Polynomial.mapRingHom_comp_C]

theorem constant (phi : R →+* S) (p : R[X]) :
    (p.map C).map (Polynomial.mapRingHom phi) = (p.map phi).map C := by
  simp only [Polynomial.map_map, Polynomial.mapRingHom_comp_C]

theorem subresultant (phi : R →+* S) (hi : Function.Injective phi) (p q : R[X]) (c : ℕ) :
    (recoverySubresultant p q c).map (Polynomial.mapRingHom phi) = recoverySubresultant (p.map phi) (q.map phi) c := by
  unfold recoverySubresultant
  rw [← Subresultant.polynomial_map, shift, constant,
    Polynomial.natDegree_map_eq_of_injective hi, Polynomial.natDegree_map_eq_of_injective hi]

theorem resultant (phi : R →+* S) (hi : Function.Injective phi) (p q : R[X]) (c : ℕ) :
    (cannyResultant p q c).map phi = cannyResultant (p.map phi) (q.map phi) c := by
  unfold cannyResultant
  have he := (Polynomial.resultant_map_map (shiftFamily p c) (q.map C) p.natDegree q.natDegree
    (Polynomial.mapRingHom phi)).symm
  have hx := congrArg₂ (fun f g : Polynomial (Polynomial S) => f.resultant g p.natDegree q.natDegree)
    (shift phi p c) (constant phi q)
  simpa only [Polynomial.coe_mapRingHom, Polynomial.natDegree_map_eq_of_injective hi] using he.trans hx

theorem coefficient (phi : R →+* S) (hi : Function.Injective phi) (p q : R[X]) (c r : ℕ) :
    (coordinateCoefficient p q c r).map phi = coordinateCoefficient (p.map phi) (q.map phi) c r := by
  unfold coordinateCoefficient
  rw [Polynomial.natDegree_map_eq_of_injective hi, Polynomial.natDegree_map_eq_of_injective hi]
  split_ifs
  · simp only [Polynomial.map_C, Polynomial.coeff_map]
  · simpa only [Polynomial.coeff_map, Polynomial.coe_mapRingHom] using
      congrArg (fun P : Polynomial (Polynomial S) => P.coeff r) (shift phi p c)
  · simpa only [Polynomial.coeff_map, Polynomial.coe_mapRingHom] using
      congrArg (fun P : Polynomial (Polynomial S) => P.coeff r) (subresultant phi hi p q c)

theorem numerator (phi : R →+* S) (hi : Function.Injective phi) (p q : R[X]) (c : ℕ) :
    (coordinateNumerator p q c).map phi = coordinateNumerator (p.map phi) (q.map phi) c :=
  coefficient phi hi p q c 0

theorem denominator (phi : R →+* S) (hi : Function.Injective phi) (p q : R[X]) (c : ℕ) :
    (PrimitivePair.denominator p q c).map phi = PrimitivePair.denominator (p.map phi) (q.map phi) c :=
  coefficient phi hi p q c 1

theorem rightNumerator (phi : R →+* S) (hi : Function.Injective phi) (p q : R[X]) (c : ℕ) :
    (PrimitivePair.rightNumerator p q c).map phi = PrimitivePair.rightNumerator (p.map phi) (q.map phi) c := by
  rw [PrimitivePair.rightNumerator, Polynomial.map_neg, numerator phi hi]
  rfl

theorem leftNumerator (phi : R →+* S) (hi : Function.Injective phi) (p q : R[X]) (c : ℕ) :
    (PrimitivePair.leftNumerator p q c).map phi = PrimitivePair.leftNumerator (p.map phi) (q.map phi) c := by
  rw [PrimitivePair.leftNumerator, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_X, denominator phi hi, numerator phi hi, Polynomial.map_C, map_natCast]
  rfl

end LeanCanny.Algebra.CoordinateRecoveryMap
