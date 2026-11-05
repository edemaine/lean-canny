/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ParametricCoerciveEliminant
public import LeanCanny.Algebra.CoerciveBoxGramEliminant
/-! # Fixed coercive Gram determinants retaining an extra coefficient parameter

The matrix and determinant use the actual homogeneous coercive system over
the retained coefficient ring. Mapping that ring maps the same determinant.
For integer-polynomial coefficients, evaluation at zero proves nonvanishing
by the existing integer Gram determinant. No row selector or supplied
annihilator is used.
-/
@[expose] public section
namespace LeanCanny.Algebra.ParametricCoerciveBoxGramEliminant
open MvPolynomial CoerciveCriticalHomogenization
open ProjectiveGramEliminant
open scoped Classical Matrix
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

noncomputable def coefficientMap (φ : R →+* S) :
    Polynomial (Polynomial R) →+* Polynomial (Polynomial S) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom φ)

theorem system_map (φ : R →+* S) (q : MvPolynomial (Fin n) R) (D : ℕ)
    (i : Fin n) (j : Fin (n+1)) :
    (ParametricCoerciveEliminant.system q D i j).map (coefficientMap φ) =
      ParametricCoerciveEliminant.system (q.map φ) D i j := by
  rw [ParametricCoerciveEliminant.system,map_rename,map_nativeSystem,MvPolynomial.map_map]
  have HC : (coefficientMap φ).comp ParametricCoerciveEliminant.constants =
      ParametricCoerciveEliminant.constants.comp φ := by
    ext a
    simp [coefficientMap,ParametricCoerciveEliminant.constants]
  rw [HC,←MvPolynomial.map_map]
  simp only [coefficientMap,Polynomial.coe_mapRingHom,Polynomial.map_X,Polynomial.map_C]
  rfl

noncomputable def matrix (q : MvPolynomial (Fin n) R) (D : ℕ) (i : Fin n) :
    Matrix (Fin (CoerciveBoxGramEliminant.blockDimension n D))
      (Fin (CoerciveBoxGramEliminant.blockDimension n D)) (Polynomial (Polynomial R)) :=
  MacaulayFullBoxFinite.matrix (ParametricCoerciveEliminant.system q D i) (finDegree D)
    (CoerciveCoordinateEliminant.width n D)

noncomputable def polynomial (q : MvPolynomial (Fin n) R) (D : ℕ) (i : Fin n) :
    Polynomial (Polynomial R) :=
  (gram (MacaulayFullBox.matrix (ParametricCoerciveEliminant.system q D i) (finDegree D)
    (CoerciveCoordinateEliminant.width n D))).det

private theorem det_finite {m W : ℕ} (p : Fin m → MvPolynomial (Fin m) R) (d : Fin m → ℕ) :
    (MacaulayFullBoxFinite.matrix p d W).det = (gram (MacaulayFullBox.matrix p d W)).det := by
  rw [MacaulayFullBoxFinite.matrix,Matrix.det_submatrix_equiv_self,block_det]

private theorem block_map {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    (φ : R →+* S) (A : Matrix a b R) : (block A).map φ = block (A.map φ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [block,Matrix.one_apply]
  · rfl
  · simp [block]
  · exact map_zero φ

private theorem finite_matrix_map {m W : ℕ} (φ : R →+* S)
    (p : Fin m → MvPolynomial (Fin m) R) (d : Fin m → ℕ) :
    (MacaulayFullBoxFinite.matrix p d W).map φ =
      MacaulayFullBoxFinite.matrix (fun j => (p j).map φ) d W := by
  rw [MacaulayFullBoxFinite.matrix,←Matrix.submatrix_map,block_map,MacaulayFullBox.matrix_map]
  rfl

theorem det_matrix (q : MvPolynomial (Fin n) R) (D : ℕ) (i : Fin n) :
    (matrix q D i).det = polynomial q D i := by
  exact det_finite (ParametricCoerciveEliminant.system q D i) (finDegree D)

theorem matrix_map (φ : R →+* S) (q : MvPolynomial (Fin n) R) (D : ℕ) (i : Fin n) :
    (matrix q D i).map (coefficientMap φ) = matrix (q.map φ) D i := by
  change (MacaulayFullBoxFinite.matrix _ _ _).map (coefficientMap φ) = _
  rw [finite_matrix_map]
  simp only [system_map]
  rfl

theorem polynomial_map (φ : R →+* S) (q : MvPolynomial (Fin n) R) (D : ℕ) (i : Fin n) :
    coefficientMap φ (polynomial q D i) = polynomial (q.map φ) D i := by
  rw [polynomial,RingHom.map_det]
  change ((gram (MacaulayFullBox.matrix _ _ _)).map (coefficientMap φ)).det = _
  rw [gram_map,MacaulayFullBox.matrix_map]
  simp only [system_map]
  rfl

theorem system_integer (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (i : Fin n) (j : Fin (n+1)) :
    ParametricCoerciveEliminant.system q D i j = finSystem q D i j := by
  have HC : ParametricCoerciveEliminant.constants (R := ℤ) =
      Int.castRingHom (Polynomial (Polynomial ℤ)) := Subsingleton.elim _ _
  rw [ParametricCoerciveEliminant.system,finSystem,CoerciveCriticalHomogenization.system,HC]
  rfl

theorem polynomial_integer (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (i : Fin n) :
    polynomial q D i = CoerciveBoxGramEliminant.polynomial q D i := by
  unfold polynomial CoerciveBoxGramEliminant.polynomial ProjectiveBoxGramEliminant.polynomial
  rw [show ParametricCoerciveEliminant.system q D i = finSystem q D i from
    funext (system_integer q D i)]

theorem ne_zero (q : MvPolynomial (Fin n) (Polynomial ℤ)) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) : polynomial q D i ≠ 0 := by
  let φ : Polynomial ℤ →+* ℤ := Polynomial.evalRingHom 0
  have HQ : (q.map φ).totalDegree ≤ D := (PolynomialMapDegree.degree_le _ _).trans hD
  have H := CoerciveBoxGramEliminant.ne_zero (q.map φ) D HQ i
  intro H0
  have HE := polynomial_map φ q D i
  rw [H0,map_zero,polynomial_integer] at HE
  exact H HE.symm

private theorem eval_polynomial {K : Type*} [CommRing K]
    (φ : Polynomial (Polynomial R) →+* K) (q : MvPolynomial (Fin n) R) (D : ℕ) (i : Fin n) :
    φ (polynomial q D i) =
      (gram ((MacaulayFullBox.matrix (ParametricCoerciveEliminant.system q D i) (finDegree D)
        (CoerciveCoordinateEliminant.width n D)).map φ)).det := by
  rw [polynomial,RingHom.map_det]
  change ((gram (MacaulayFullBox.matrix _ _ _)).map φ).det = _
  rw [gram_map]

theorem eval_eq_zero {K : Type*} [Field K] (φ : R →+* K)
    (q : MvPolynomial (Fin n) R) (D : ℕ) (hD : q.totalDegree ≤ D)
    (i : Fin n) (s : K) (x : Fin n → K)
    (hx : ∀ j, eval x (pderiv j (CoerciveCriticalFibers.polynomial (q.map φ) D s)) = 0) :
    ParametricCoerciveEliminant.specialize φ s (x i) (polynomial q D i) = 0 := by
  let ψ := ParametricCoerciveEliminant.specialize φ s (x i)
  let p := ParametricCoerciveEliminant.system q D i
  let W := CoerciveCoordinateEliminant.width n D
  have HP : ∀ j, (p j).IsHomogeneous (finDegree D j) :=
    ParametricCoerciveEliminant.homogeneous q D i
  have HR : ∀ j, eval₂ ψ (finPoint x) (p j) = 0 :=
    ParametricCoerciveEliminant.critical_root φ q D hD i s x hx
  by_contra H
  change ψ (polynomial q D i) ≠ 0 at H
  rw [eval_polynomial,MacaulayFullBox.matrix_map] at H
  let A := MacaulayFullBox.matrix (fun j => (p j).map ψ) (finDegree D) W
  have HZ : A *ᵥ Macaulay.evaluationVector (finDegree D) W (finPoint x) = 0 := by
    apply MacaulayFullBox.mulVec_evaluation_eq_zero _ _ _
      (fun j => (HP j).map ψ) (CoerciveCoordinateEliminant.level_lt n D) (finPoint x)
    intro j
    simpa only [MvPolynomial.eval_map] using HR j
  have HI := Matrix.mulVec_injective_of_det_ne_zero H
  have HV : gram A *ᵥ Macaulay.evaluationVector (finDegree D) W (finPoint x) = 0 := by
    rw [gram,←Matrix.mulVec_mulVec,HZ,Matrix.mulVec_zero]
  have HE := HI (HV.trans (Matrix.mulVec_zero _).symm)
  obtain ⟨j,hj⟩ := finPoint_nonzero x
  obtain ⟨r,hr⟩ := Macaulay.evaluationVector_ne_zero (finDegree D) W
    (CoerciveCoordinateEliminant.level_lt n D) (finPoint x) j hj
  exact hr (congrFun HE r)

end LeanCanny.Algebra.ParametricCoerciveBoxGramEliminant
