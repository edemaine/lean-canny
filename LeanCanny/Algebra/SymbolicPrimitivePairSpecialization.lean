/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicPrimitivePairBounds

/-! # Specialization of symbolic primitive-pair formulas

Ordinary parameter evaluation may have a kernel. Preserved source degrees
suffice to map the actual fixed-order determinant and every recovery branch.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicPrimitivePair
open Polynomial SymbolicScaledSquarefree
open scoped Classical
attribute [local irreducible] Matrix.det

section Maps
variable {R : Type*} [CommRing R]

theorem resultant_map_of_degrees (φ : Coefficient →+* R) (p q : Polynomial Coefficient) (c : ℕ)
    (hp : (p.map φ).natDegree = p.natDegree) (hq : (q.map φ).natDegree = q.natDegree) :
    (cannyResultant p q c).map φ = cannyResultant (p.map φ) (q.map φ) c := by
  unfold cannyResultant
  have he := (Polynomial.resultant_map_map (shiftFamily p c) (q.map C) p.natDegree q.natDegree
    (Polynomial.mapRingHom φ)).symm
  have hx := congrArg₂ (fun f g : Polynomial (Polynomial R) => f.resultant g p.natDegree q.natDegree)
    (CoordinateRecoveryMap.shift φ p c) (CoordinateRecoveryMap.constant φ q)
  simpa only [Polynomial.coe_mapRingHom, hp, hq] using he.trans hx

theorem coefficient_map_of_degrees (φ : Coefficient →+* R) (p q : Polynomial Coefficient) (c r : ℕ)
    (hp : (p.map φ).natDegree = p.natDegree) (hq : (q.map φ).natDegree = q.natDegree) :
    (coordinateCoefficient p q c r).map φ = coordinateCoefficient (p.map φ) (q.map φ) c r := by
  unfold coordinateCoefficient
  rw [hp, hq]
  split_ifs
  · simp only [Polynomial.map_C, Polynomial.coeff_map]
  · simpa only [Polynomial.coeff_map, Polynomial.coe_mapRingHom] using
      congrArg (fun P : Polynomial (Polynomial R) => P.coeff r) (CoordinateRecoveryMap.shift φ p c)
  · have he : (recoverySubresultant p q c).map (Polynomial.mapRingHom φ) =
        recoverySubresultant (p.map φ) (q.map φ) c := by
      unfold recoverySubresultant
      rw [← Subresultant.polynomial_map, CoordinateRecoveryMap.shift,
        CoordinateRecoveryMap.constant, hp, hq]
    simpa only [Polynomial.coeff_map, Polynomial.coe_mapRingHom] using
      congrArg (fun P : Polynomial (Polynomial R) => P.coeff r) he

theorem denominator_map_of_degrees (φ : Coefficient →+* R) (p q : Polynomial Coefficient) (c : ℕ)
    (hp : (p.map φ).natDegree = p.natDegree) (hq : (q.map φ).natDegree = q.natDegree) :
    (PrimitivePair.denominator p q c).map φ = PrimitivePair.denominator (p.map φ) (q.map φ) c :=
  coefficient_map_of_degrees φ p q c 1 hp hq

theorem numerator_map_of_degrees (φ : Coefficient →+* R) (p q : Polynomial Coefficient) (c : ℕ)
    (hp : (p.map φ).natDegree = p.natDegree) (hq : (q.map φ).natDegree = q.natDegree) :
    (coordinateNumerator p q c).map φ = coordinateNumerator (p.map φ) (q.map φ) c :=
  coefficient_map_of_degrees φ p q c 0 hp hq

theorem rightNumerator_map_of_degrees (φ : Coefficient →+* R) (p q : Polynomial Coefficient) (c : ℕ)
    (hp : (p.map φ).natDegree = p.natDegree) (hq : (q.map φ).natDegree = q.natDegree) :
    (PrimitivePair.rightNumerator p q c).map φ = PrimitivePair.rightNumerator (p.map φ) (q.map φ) c := by
  rw [PrimitivePair.rightNumerator, Polynomial.map_neg]
  exact congrArg Neg.neg (coefficient_map_of_degrees φ p q c 0 hp hq)

theorem leftNumerator_map_of_degrees (φ : Coefficient →+* R) (p q : Polynomial Coefficient) (c : ℕ)
    (hp : (p.map φ).natDegree = p.natDegree) (hq : (q.map φ).natDegree = q.natDegree) :
    (PrimitivePair.leftNumerator p q c).map φ = PrimitivePair.leftNumerator (p.map φ) (q.map φ) c := by
  rw [PrimitivePair.leftNumerator, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_X, denominator_map_of_degrees φ p q c hp hq,
    numerator_map_of_degrees φ p q c hp hq, Polynomial.map_C, map_natCast]
  rfl

end Maps

noncomputable def fieldDecode {L : Type*} [Field L] (p q : L[X]) (c : ℕ) (theta : L) : L × L :=
  ((PrimitivePair.leftNumerator p q c).eval theta / (PrimitivePair.denominator p q c).eval theta,
    (PrimitivePair.rightNumerator p q c).eval theta / (PrimitivePair.denominator p q c).eval theta)

private theorem map_eval {L M : Type*} [Field L] [Field M] (f : L →+* M) (p : L[X]) (a : L) :
    f (p.eval a) = p.eval₂ f (f a) := by
  change f (p.eval₂ (RingHom.id L) a) = _
  rw [Polynomial.hom_eval₂]
  rfl

theorem field_decode_root {L : Type*} [Field L] [CharZero L]
    (p q : L[X]) (c : ℕ) (theta : L) (hp : p.Separable) (hq : q.Separable)
    (hs : (cannyResultant p q c).Separable) (ht : (cannyResultant p q c).eval theta = 0) :
    p.eval (fieldDecode p q c theta).1 = 0 ∧ q.eval (fieldDecode p q c theta).2 = 0 ∧
      shear c (fieldDecode p q c theta) = theta ∧ (PrimitivePair.denominator p q c).eval theta ≠ 0 := by
  let f : L →+* AlgebraicClosure L := algebraMap L (AlgebraicClosure L)
  have hi := (PrimitivePair.resultant_separable_iff (L := AlgebraicClosure L) p q c hp hq
    (IsAlgClosed.splits _) (IsAlgClosed.splits _)).mp hs
  have ht' : Polynomial.aeval (f theta) (cannyResultant p q c) = 0 := by
    change (cannyResultant p q c).eval₂ f (f theta) = 0
    rw [← map_eval, ht, map_zero]
  have h := PrimitivePair.decode_root p q c (f theta) hp.ne_zero hq (IsAlgClosed.splits _) hi ht'
  have hd : (f (fieldDecode p q c theta).1, f (fieldDecode p q c theta).2) =
      PrimitivePair.decode p q c (f theta) := by
    simp only [fieldDecode, PrimitivePair.decode, map_div₀, map_eval, Polynomial.aeval_def]
    rfl
  rw [← hd] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply f.injective
    rw [map_zero, map_eval]
    exact h.1
  · apply f.injective
    rw [map_zero, map_eval]
    exact h.2.1
  · apply f.injective
    simpa only [shear, map_add, map_mul, map_natCast] using h.2.2.1
  · intro hz
    apply h.2.2.2
    change (PrimitivePair.denominator p q c).eval₂ f (f theta) = 0
    rw [← map_eval, hz, map_zero]

noncomputable def evaluatedCoordinates {L : Type*} [Field L] (φ : Coefficient →+* L)
    (p q : SeparablePolynomial) (theta : L) : L × L :=
  ((leftNumerator p q).eval₂ φ theta / (denominator p q).eval₂ φ theta,
    (rightNumerator p q).eval₂ φ theta / (denominator p q).eval₂ φ theta)

theorem field_encode_roots {L : Type*} [Field L] [CharZero L]
    (p q : L[X]) (c : ℕ) (a b : L) (hp : p.Separable) (hq : q.Separable)
    (hs : (cannyResultant p q c).Separable) (ha : p.eval a = 0) (hb : q.eval b = 0) :
    (cannyResultant p q c).eval (shear c (a, b)) = 0 ∧
      fieldDecode p q c (shear c (a, b)) = (a, b) := by
  let f : L →+* AlgebraicClosure L := algebraMap L (AlgebraicClosure L)
  have hi := (PrimitivePair.resultant_separable_iff (L := AlgebraicClosure L) p q c hp hq
    (IsAlgClosed.splits _) (IsAlgClosed.splits _)).mp hs
  have ha' : Polynomial.aeval (f a) p = 0 := by
    change p.eval₂ f (f a) = 0
    rw [← map_eval, ha, map_zero]
  have hb' : Polynomial.aeval (f b) q = 0 := by
    change q.eval₂ f (f b) = 0
    rw [← map_eval, hb, map_zero]
  have he : f (shear c (a, b)) = shear c (f a, f b) := by
    simp only [shear, map_add, map_mul, map_natCast]
  have ht := (cannyResultant_roots p q c (shear c (f a, f b)) hq.ne_zero (IsAlgClosed.splits _)).mpr
    ⟨f a, f b, ha', hb', rfl⟩
  have hd : (f (fieldDecode p q c (shear c (a, b))).1,
      f (fieldDecode p q c (shear c (a, b))).2) =
      PrimitivePair.decode p q c (f (shear c (a, b))) := by
    simp only [fieldDecode, PrimitivePair.decode, map_div₀, map_eval, Polynomial.aeval_def]
    rfl
  rw [he, PrimitivePair.decode_shear p q c (f a) (f b) hp.ne_zero hq
    (IsAlgClosed.splits _) hi ha' hb'] at hd
  refine ⟨?_, Prod.ext (f.injective (congrArg Prod.fst hd)) (f.injective (congrArg Prod.snd hd))⟩
  apply f.injective
  rw [map_zero, map_eval, he]
  exact ht

theorem evaluatedCoordinates_eq {L : Type*} [Field L] (φ : Coefficient →+* L)
    (p q : SeparablePolynomial) (theta : L)
    (hp : (p.polynomial.map φ).natDegree = p.polynomial.natDegree)
    (hq : (q.polynomial.map φ).natDegree = q.polynomial.natDegree) :
    evaluatedCoordinates φ p q theta = fieldDecode (p.polynomial.map φ) (q.polynomial.map φ) (direction p q) theta := by
  simp only [evaluatedCoordinates, fieldDecode, leftNumerator, rightNumerator, denominator,
    ← leftNumerator_map_of_degrees φ _ _ _ hp hq,
    ← rightNumerator_map_of_degrees φ _ _ _ hp hq,
    ← denominator_map_of_degrees φ _ _ _ hp hq, Polynomial.eval_map]

theorem specialized_decode_root {L : Type*} [Field L] [CharZero L]
    (φ : Coefficient →+* L) (p q : SeparablePolynomial) (theta : L)
    (hpd : (p.polynomial.map φ).natDegree = p.polynomial.natDegree)
    (hqd : (q.polynomial.map φ).natDegree = q.polynomial.natDegree)
    (hp : (p.polynomial.map φ).Separable) (hq : (q.polynomial.map φ).Separable)
    (hs : ((parameter p q).map φ).Separable) (ht : (parameter p q).eval₂ φ theta = 0) :
    p.polynomial.eval₂ φ (evaluatedCoordinates φ p q theta).1 = 0 ∧
      q.polynomial.eval₂ φ (evaluatedCoordinates φ p q theta).2 = 0 ∧
      shear (direction p q) (evaluatedCoordinates φ p q theta) = theta ∧
      (denominator p q).eval₂ φ theta ≠ 0 := by
  have hm := resultant_map_of_degrees φ p.polynomial q.polynomial (direction p q) hpd hqd
  change (parameter p q).map φ = _ at hm
  rw [hm] at hs
  have ht' : (cannyResultant (p.polynomial.map φ) (q.polynomial.map φ) (direction p q)).eval theta = 0 := by
    rw [← hm, Polynomial.eval_map]
    exact ht
  have h := field_decode_root _ _ (direction p q) theta hp hq hs ht'
  rw [← evaluatedCoordinates_eq φ p q theta hpd hqd] at h
  simpa only [Polynomial.eval_map, denominator,
    ← denominator_map_of_degrees φ _ _ _ hpd hqd] using h

theorem specialized_encode_roots {L : Type*} [Field L] [CharZero L]
    (φ : Coefficient →+* L) (p q : SeparablePolynomial) (a b : L)
    (hpd : (p.polynomial.map φ).natDegree = p.polynomial.natDegree)
    (hqd : (q.polynomial.map φ).natDegree = q.polynomial.natDegree)
    (hp : (p.polynomial.map φ).Separable) (hq : (q.polynomial.map φ).Separable)
    (hs : ((parameter p q).map φ).Separable)
    (ha : p.polynomial.eval₂ φ a = 0) (hb : q.polynomial.eval₂ φ b = 0) :
    (parameter p q).eval₂ φ (shear (direction p q) (a, b)) = 0 ∧
      evaluatedCoordinates φ p q (shear (direction p q) (a, b)) = (a, b) := by
  have hm := resultant_map_of_degrees φ p.polynomial q.polynomial (direction p q) hpd hqd
  change (parameter p q).map φ = _ at hm
  rw [hm] at hs
  have h := field_encode_roots (p.polynomial.map φ) (q.polynomial.map φ) (direction p q) a b hp hq hs
    (by simpa only [Polynomial.eval_map] using ha) (by simpa only [Polynomial.eval_map] using hb)
  rw [← hm, ← evaluatedCoordinates_eq φ p q _ hpd hqd] at h
  simpa only [Polynomial.eval_map] using h

end LeanCanny.Algebra.SymbolicPrimitivePair
