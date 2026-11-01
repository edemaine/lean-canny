/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoerciveCoordinateEliminant
public import LeanCanny.Algebra.TiltedCoerciveCriticalFibers
/-! # Coercive coordinate eliminants over the retained coefficient ring

Additional center/radius parameters remain coefficients. Every specialization
uses the same coefficient homomorphism; no absolute root is lifted to a
prescribed parent. One complex specialization proves nonvanishing.
-/
@[expose] public section
namespace LeanCanny.Algebra.ParametricTiltedCoerciveEliminant
open MvPolynomial
open CoerciveCriticalHomogenization
open scoped Classical Matrix
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {n : ℕ}

abbrev Coefficient (R : Type*) [CommRing R] := Polynomial (Polynomial R)
noncomputable def constants : R →+* Coefficient R := Polynomial.C.comp Polynomial.C
noncomputable def specialize {K : Type*} [CommRing K] (φ : R →+* K) (s t : K) : Coefficient R →+* K :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom φ t) s

noncomputable def system (q : MvPolynomial (Fin n) R) (D : ℕ) (u i : Fin n)
    (j : Fin (n+1)) : MvPolynomial (Fin (n+1)) (Coefficient R) :=
  rename layout (TiltedCoerciveCriticalFibers.nativeSystem (q.map constants) D u Polynomial.X (Polynomial.C Polynomial.X) i (layout.symm j))

theorem homogeneous (q : MvPolynomial (Fin n) R) (D : ℕ) (u i : Fin n) (j : Fin (n+1)) :
    (system q D u i j).IsHomogeneous (finDegree D j) :=
  (TiltedCoerciveCriticalFibers.homogeneous _ _ _ _ _ _ _).rename_isHomogeneous

theorem map_system {K : Type*} [CommRing K] (φ : R →+* K) (s t : K)
    (q : MvPolynomial (Fin n) R) (D : ℕ) (u i : Fin n) (j : Fin (n+1)) :
    (system q D u i j).map (specialize φ s t)=
      rename layout (TiltedCoerciveCriticalFibers.nativeSystem (q.map φ) D u s t i (layout.symm j)) := by
  rw [system,map_rename,TiltedCoerciveCriticalFibers.map_nativeSystem,MvPolynomial.map_map]
  have HC : (specialize φ s t).comp constants=φ := by ext; simp [specialize,constants]
  rw [HC]
  simp [specialize]

theorem critical_root {K : Type*} [Field K] (φ : R →+* K)
    (q : MvPolynomial (Fin n) R) (D : ℕ) (hD : q.totalDegree≤D)
    (u i : Fin n) (s : K) (x : Fin n → K)
    (hx : ∀ j, eval x (pderiv j (TiltedCoerciveCriticalFibers.polynomial (q.map φ) D u s))=0)
    (j : Fin (n+1)) : eval₂ (specialize φ s (x i)) (finPoint x) (system q D u i j)=0 := by
  have HD : (q.map φ).totalDegree≤D := (PolynomialMapDegree.degree_le _ _).trans hD
  rw [← eval_map,map_system]
  simp only [eval_rename,Function.comp_def,finPoint,Equiv.symm_apply_apply]
  cases HJ : layout.symm j with
  | none => simp [TiltedCoerciveCriticalFibers.nativeSystem]
  | some k =>
    rw [TiltedCoerciveCriticalFibers.eval_chart _ D HD u s (x i) i x k]
    exact hx k

theorem exists_root_free (φ : R →+* ℂ) (q : MvPolynomial (Fin n) R) (D : ℕ)
    (hD : q.totalDegree≤D) (u i : Fin n) :
    ∃ t : ℂ, ∀ x : Fin (n+1) → ℂ,
      (∀ j, eval₂ (specialize φ 1 t) x (system q D u i j)=0) → x=0 := by
  have HD : (q.map φ).totalDegree≤D := (PolynomialMapDegree.degree_le _ _).trans hD
  obtain ⟨t,HT⟩ := TiltedCoerciveCriticalFibers.exists_root_free (q.map φ) D HD u i
  refine ⟨t,?_⟩
  intro x hx
  have H : (fun j => x (layout j))=0 := by
    apply HT
    intro j
    have HH := hx (layout j)
    rw [← eval_map,map_system] at HH
    simpa only [Equiv.symm_apply_apply,eval_rename,Function.comp_def] using HH
  funext j
  simpa only [Equiv.apply_symm_apply,Pi.zero_apply] using congrFun H (layout.symm j)

noncomputable def polynomial (q : MvPolynomial (Fin n) R) (D : ℕ) (u i : Fin n) : Coefficient R :=
  MacaulayUniversal.polynomialValue (finDegree D) (CoerciveCoordinateEliminant.width n D)
    (CoerciveCoordinateEliminant.degree_lt n D) (CoerciveCoordinateEliminant.level_lt n D) (system q D u i)

theorem ne_zero (φ : R →+* ℂ) (q : MvPolynomial (Fin n) R) (D : ℕ)
    (hD : q.totalDegree≤D) (u i : Fin n) : polynomial q D u i≠0 := by
  obtain ⟨t,HT⟩ := exists_root_free φ q D hD u i
  let ψ := specialize φ 1 t
  let A := Macaulay.fullMatrix (system q D u i) (finDegree D) (CoerciveCoordinateEliminant.width n D)
  have HA : Function.Surjective (fun v => Matrix.vecMul v (A.map ψ)) := by
    rw [show A.map ψ=Macaulay.fullMatrix (fun j => (system q D u i j).map ψ)
      (finDegree D) (CoerciveCoordinateEliminant.width n D) from Macaulay.fullMatrix_map _ _ _ _]
    apply Macaulay.fullMatrix_surjective_of_no_nonzero_root _ _ _
      (fun j => (homogeneous q D u i j).map ψ) (finDegree_pos D) (CoerciveCoordinateEliminant.level_lt n D)
    intro x hx
    apply HT x
    intro j
    simpa only [eval_map] using hx j
  obtain ⟨f,HF⟩ := RowSpanSpecialization.exists_nonzero_minor ψ A HA
  have HD := MacaulayUniversal.polynomialValue_dvd_fullMinor (finDegree D) (CoerciveCoordinateEliminant.width n D)
    (CoerciveCoordinateEliminant.degree_lt n D) (CoerciveCoordinateEliminant.level_lt n D)
    (system q D u i) (homogeneous q D u i) (finDegree_pos D) f
  intro HZ
  change polynomial q D u i ∣ (A.submatrix f id).det at HD
  rw [HZ,zero_dvd_iff] at HD
  exact HF HD

theorem eval_eq_zero {K : Type*} [Field K] (φ : R →+* K) (q : MvPolynomial (Fin n) R)
    (D : ℕ) (hD : q.totalDegree≤D) (u i : Fin n) (s : K) (x : Fin n → K)
    (hx : ∀ j, eval x (pderiv j (TiltedCoerciveCriticalFibers.polynomial (q.map φ) D u s))=0) :
    specialize φ s (x i) (polynomial q D u i)=0 :=
  MacaulayUniversal.map_polynomialValue_eq_zero_of_common_root (specialize φ s (x i))
    (finDegree D) (CoerciveCoordinateEliminant.width n D) (CoerciveCoordinateEliminant.degree_lt n D)
    (CoerciveCoordinateEliminant.level_lt n D) (system q D u i) (homogeneous q D u i) (finDegree_pos D)
    (finPoint x) (critical_root φ q D hD u i s x hx) (finPoint_nonzero x)

end LeanCanny.Algebra.ParametricTiltedCoerciveEliminant
