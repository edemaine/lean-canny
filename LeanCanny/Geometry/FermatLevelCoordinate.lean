/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FermatLevelCritical
public import LeanCanny.Algebra.CoordinateFrozenCriticalElimination

/-! # Actual frozen coordinate equations for bounded level lifts

The relative coordinate polynomial is constructed by the existing kernel.
The additional last coordinate is its free objective; every old free derivative
is supplied by the original unconstrained critical point. The selected old hom
and every old frozen height remain fixed.
-/
@[expose] public section
namespace LeanCanny.Geometry.FermatLevelCoordinate
open LeanCanny.Algebra IntegralMixedHistory MvPolynomial
variable {R : Type*} [CommRing R] [Nontrivial R] {n k : ℕ}

def scales (c : Fin (n+1) → ℤ) : Fin (n+2) → ℤ := Fin.snoc c 1
noncomputable def heights (H : Fin (n+1) → R) : Fin (n+2) → R := Fin.snoc H 0

theorem fit (offset : ℕ) (hfit : offset+(k+1)=n+1) : offset+(k+1+1)=n+2 := by omega

theorem scales_ne (c : Fin (n+1) → ℤ) (hc : ∀ i, c i≠0) (i : Fin (n+2)) : scales c i≠0 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [scales]
  · simpa only [scales,Fin.snoc_castSucc] using hc j

noncomputable def polynomial (P : SpatialSource n) (A : ℤ) (c : Fin (n+1) → ℤ)
    (H : Fin (n+1) → R) (offset : ℕ) (hfit : offset+(k+1)=n+1) (j : Fin (k+1)) : Polynomial R :=
  CoordinateFrozenCriticalElimination.polynomial P.degree (scales c) (heights H) offset (fit offset hfit)
    ((FermatLevelLift.source P A).low.map (Int.castRingHom R)) (P.leading:R) (Fin.last (k+1)) j.castSucc

omit [Nontrivial R] in
private theorem integer_eval (φ : R →+* ℝ) {m : ℕ} (p : MvPolynomial (Fin m) ℤ) (x : Fin m → ℝ) :
    (p.map (Int.castRingHom R)).eval₂ φ x=p.eval₂ (Int.castRingHom ℝ) x := by
  rw [eval₂_map]
  have H : φ.comp (Int.castRingHom R)=Int.castRingHom ℝ := RingHom.ext_int _ _
  rw [H]

theorem root (P : SpatialSource n) (A : ℤ) (hP : P.leading=1) (hd : Even P.degree)
    (c : Fin (n+1) → ℤ) (hc : ∀ i, c i≠0) (H : Fin (n+1) → R)
    (offset : ℕ) (hfit : offset+(k+1)=n+1) (j : Fin (k+1)) (φ : R →+* ℝ) (x : Fin (n+1) → ℝ)
    (hfrozen : ∀ i, i.val<offset → (c i:ℝ)*x i=φ (H i))
    (hw : |(FermatLevelLift.polynomial P).eval₂ (Int.castRingHom ℝ) x| ≤ (A:ℝ)-1)
    (hg : ∀ i : Fin (n+1), offset ≤ i.val →
      (pderiv i (FermatLevelLift.polynomial P)).eval₂ (Int.castRingHom ℝ) x=0) :
    (polynomial P A c H offset hfit j).eval₂ φ
      (x (ClearedCoordinateCritical.freeIndex offset hfit.le j))=0 := by
  obtain ⟨v,_hv,HP,HG⟩ := FermatLevelCritical.lift_critical P A hP hd x hw offset hg
  let Q := FermatLevelLift.source P A
  have HM : FermatCriticalHomogenization.polynomial (Q.low.map (Int.castRingHom R)) (P.leading:R) P.degree =
      (FermatLevelLift.polynomial Q).map (Int.castRingHom R) := by
    exact (FermatCriticalHomogenization.map_polynomial (Int.castRingHom R) Q.low Q.leading Q.degree).symm
  have HC := CoordinateFrozenCriticalElimination.root φ P.degree P.degree_two (scales c) (scales_ne c hc)
    (heights H) offset (fit offset hfit) (Q.low.map (Int.castRingHom R)) (P.leading:R)
    ((PolynomialMapDegree.degree_le _ Q.low).trans_lt Q.low_degree)
    (Fin.last (k+1)) (Fin.snoc x v) ?_ ?_ ?_ j.castSucc
  · have HE : ClearedCoordinateCritical.freeIndex offset (fit offset hfit).le j.castSucc =
        (ClearedCoordinateCritical.freeIndex offset hfit.le j).castSucc := Fin.ext rfl
    simpa only [polynomial,Q,HE,Fin.snoc_castSucc] using HC
  · intro i hi
    let a : Fin (n+1) := ⟨i.val,by omega⟩
    have HE : i=a.castSucc := Fin.ext rfl
    rw [HE]
    simpa only [scales,heights,Fin.snoc_castSucc] using hfrozen a hi
  · rw [HM,integer_eval]
    exact HP
  · intro i hi
    have HI : i.val<k+1 := by
      have HN : i.val≠k+1 := fun h => hi (Fin.ext h)
      have HB := i.isLt
      omega
    let a : Fin (n+1) := ⟨offset+i.val,by omega⟩
    have HE : ClearedCoordinateCritical.freeIndex offset (fit offset hfit).le i=a.castSucc := Fin.ext rfl
    rw [HM,pderiv_map,integer_eval,HE]
    exact HG a (by simp only [a]; omega)

end LeanCanny.Geometry.FermatLevelCoordinate
