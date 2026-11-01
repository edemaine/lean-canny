/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedSweepBounds
public import LeanCanny.Algebra.ValidatedSquarefreeSpecialization
public import LeanCanny.Geometry.UnivariateRootFamily

/-! # Selected-component squarefree cuts for actual relative coordinates

A bounded principal-subresultant choice is validated by polynomial-zero
queries on the selected old algebra component. The resulting relative
scaled quotient keeps exactly the selected coordinate roots and is
separable away from a constructed nonzero relative exceptional factor.
No algebraic conjugate or other old component is included in the claim.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCoordinateSquarefree
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedCriticalSweep
open Polynomial PrincipalSubresultant
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

abbrev coordinateDegree (P : SpatialSource n) (r : Rule n) :=
  PurePowerReductionBounds.dimension (n - r.critical.offset.val + 1) P.degree

noncomputable def principal (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (k : ℕ) : Polynomial x.sampler.scalarPrefix.carrier :=
  psc (coordinate x hm r j) (coordinate x hm r j).derivative
    (coordinateDegree P r) (coordinateDegree P r - 1) k

def Valid (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (i : Fin (coordinateDegree P r)) : Prop :=
  (∀ k < i.val, (principal x hm r j k).map φ.toRingHom = 0) ∧
    (principal x hm r j i.val).map φ.toRingHom ≠ 0

noncomputable def auxiliary (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (coordinateDegree P r)) :=
  ValidatedSquarefreeSpecialization.polynomial (coordinate x hm r j) (coordinateDegree P r) i.val

noncomputable def exceptional (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (coordinateDegree P r)) : Polynomial x.sampler.scalarPrefix.carrier :=
  (coordinate x hm r j).coeff (coordinateDegree P r) * principal x hm r j i.val

theorem selected_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    (selected x hm r j φ).natDegree = coordinateDegree P r := by
  apply Nat.le_antisymm (Polynomial.natDegree_map_le.trans (coordinate_degree x hm r j))
  have H := Polynomial.natDegree_map_le (p := selected x hm r j φ) (f := Polynomial.evalRingHom 0)
  rw [specialized_degree x hm r j φ 0] at H
  exact H

theorem selected_leading_nonzero (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    ((coordinate x hm r j).coeff (coordinateDegree P r)).map φ.toRingHom ≠ 0 := by
  have H := Polynomial.leadingCoeff_ne_zero.mpr (selected_ne_zero x hm r j φ)
  rw [Polynomial.leadingCoeff, selected_degree] at H
  have HC : (selected x hm r j φ).coeff (coordinateDegree P r) =
      ((coordinate x hm r j).coeff (coordinateDegree P r)).map φ.toRingHom := Polynomial.coeff_map _ _
  exact HC ▸ H

noncomputable def fractionEvaluation (x : State P S B m ι)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    Polynomial x.sampler.scalarPrefix.carrier →+* FractionRing (Polynomial ℝ) :=
  (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ))).comp (Polynomial.mapRingHom φ.toRingHom)

theorem exists_valid (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    ∃ i : Fin (coordinateDegree P r), Valid x hm r j φ i := by
  have HD : ((coordinate x hm r j).map (fractionEvaluation x φ)).natDegree = coordinateDegree P r := by
    rw [fractionEvaluation, ← Polynomial.map_map]
    rw [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial ℝ) (FractionRing (Polynomial ℝ)))]
    exact selected_degree x hm r j φ
  obtain ⟨i, v⟩ := ValidatedSquarefreeSpecialization.exists_valid (fractionEvaluation x φ) (coordinate x hm r j)
    (coordinateDegree P r) HD (pow_pos (Nat.two_pow_pos _) _)
  have Hzero (q : Polynomial x.sampler.scalarPrefix.carrier) : fractionEvaluation x φ q = 0 ↔ q.map φ.toRingHom = 0 := by
    change (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ))) (q.map φ.toRingHom) = 0 ↔ _
    exact (map_eq_zero_iff _ (IsFractionRing.injective (Polynomial ℝ) (FractionRing (Polynomial ℝ))))
  exact ⟨i, ⟨fun k hk => (Hzero _).mp (v.lower k hk), fun H => v.selected ((Hzero _).mpr H)⟩⟩

theorem exceptional_nonzero (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (i : Fin (coordinateDegree P r)) (hi : Valid x hm r j φ i) :
    (exceptional x hm r j i).map φ.toRingHom ≠ 0 := by
  rw [exceptional, Polynomial.map_mul]
  exact mul_ne_zero (selected_leading_nonzero x hm r j φ) hi.2

theorem finite_cuts (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (i : Fin (coordinateDegree P r)) (hi : Valid x hm r j φ i) :
    {t : ℝ | (exceptional x hm r j i).eval₂ φ.toRingHom t = 0}.Finite := by
  simpa only [Polynomial.IsRoot, Polynomial.eval_map] using
    Polynomial.finite_setOfPred_isRoot (exceptional_nonzero x hm r j φ i hi)

theorem field_valid (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (i : Fin (coordinateDegree P r)) (hi : Valid x hm r j φ i) (t : ℝ)
    (ht : (exceptional x hm r j i).eval₂ φ.toRingHom t ≠ 0) :
    ValidatedSquarefreeSpecialization.Valid (evaluation x φ t) (coordinate x hm r j) (coordinateDegree P r) i.val := by
  have HT : evaluation x φ t (exceptional x hm r j i) ≠ 0 := by
    change ((exceptional x hm r j i).map φ.toRingHom).eval t ≠ 0
    rw [Polynomial.eval_map]
    exact ht
  rw [exceptional, map_mul] at HT
  refine ⟨i.isLt, (mul_ne_zero_iff.mp HT).1, ?_, (mul_ne_zero_iff.mp HT).2⟩
  intro k hk
  have H := congrArg (fun q : Polynomial ℝ => q.eval t) (hi.1 k hk)
  simp only [Polynomial.eval_zero] at H
  convert H using 1
  rfl

theorem separable_away (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (i : Fin (coordinateDegree P r)) (hi : Valid x hm r j φ i) (t : ℝ)
    (ht : (exceptional x hm r j i).eval₂ φ.toRingHom t ≠ 0) :
    ((auxiliary x hm r j i).map (evaluation x φ t)).Separable :=
  ValidatedSquarefreeSpecialization.separable (evaluation x φ t) (coordinate x hm r j) (coordinateDegree P r) i.val
    (coordinate_degree x hm r j) (field_valid x hm r j φ i hi t ht)

theorem roots_away (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (i : Fin (coordinateDegree P r)) (hi : Valid x hm r j φ i) (t a : ℝ)
    (ht : (exceptional x hm r j i).eval₂ φ.toRingHom t ≠ 0) :
    (auxiliary x hm r j i).eval₂ (evaluation x φ t) a = 0 ↔
      (selected x hm r j φ).eval₂ (Polynomial.evalRingHom t) a = 0 := by
  rw [selected, Polynomial.eval₂_map]
  exact ValidatedSquarefreeSpecialization.roots_iff (evaluation x φ t) (coordinate x hm r j) (coordinateDegree P r) i.val
    (coordinate_degree x hm r j) (field_valid x hm r j φ i hi t ht) a

end LeanCanny.Algebra.IntegralMixedCoordinateSquarefree
