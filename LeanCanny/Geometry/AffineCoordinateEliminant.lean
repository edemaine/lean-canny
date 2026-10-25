/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineCoordinateSystem
public import LeanCanny.Algebra.AffineCoordinateParameterBounds
public import LeanCanny.Algebra.MacaulayLowestBounds
public import LeanCanny.Algebra.PolynomialMapDegree
public import LeanCanny.Geometry.MacaulayRegularPersistence
public import LeanCanny.Geometry.ProjectionCritical

/-! # Concrete bounded coordinate equations at regular affine roots

Adding the coordinate parameter to a square system preserves Jacobian
invertibility. Its homogeneous Macaulay numerator supplies a nonzero
coordinate polynomial, whose degree and integer coefficient sizes have
explicit bounds. No finiteness or elimination certificate is assumed.
-/

@[expose] public section

namespace LeanCanny.Geometry.AffineCoordinateEliminant
open MvPolynomial
open LeanCanny.Algebra
open AffineCoordinateSystem
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def polynomial (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (coordinate : Fin n) (W : ℕ) : Polynomial R :=
  MacaulayLowestBounds.polynomial (rows q d coordinate) (degrees d) W

theorem ne_zero [IsDomain R] (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (coordinate : Fin n) (W : ℕ) : polynomial q d coordinate W ≠ 0 := MacaulayLowestBounds.ne_zero _ _ _

theorem degree_le (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (coordinate : Fin n) (W : ℕ) :
    (polynomial q d coordinate W).natDegree ≤ FixedWidthPolynomial.count (n + 1) W := by
  simpa only [polynomial, Nat.mul_one] using
    MacaulayLowestBounds.degree_le (rows q d coordinate) (degrees d) W 1 (coefficient_degree q d coordinate)

omit [CommRing R] in
theorem coefficient_size_le (q : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (coordinate : Fin n) (W b : ℕ) (hq : ∀ j e, ((q j).coeff e).natAbs ≤ 2 ^ b) (k : ℕ) :
    ((polynomial q d coordinate W).coeff k).natAbs.size ≤
      (FixedWidthPolynomial.count (n + 1) W).size * FixedWidthPolynomial.count (n + 1) W +
        FixedWidthPolynomial.count (n + 1) W * (b + 3) + 1 := by
  simpa only [polynomial, Nat.add_assoc] using
    MacaulayLowestBounds.coefficient_size_le (rows q d coordinate) (degrees d) W (b + 2)
      (coefficient_mass q d coordinate b hq) k

theorem parameter_degree_le (q : Fin n → MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ)
    (coordinate : Fin n) (W E : ℕ) (hq : ∀ j e, ((q j).coeff e).natDegree ≤ E) (k : ℕ) :
    ((polynomial q d coordinate W).coeff k).natDegree ≤ FixedWidthPolynomial.count (n + 1) W * E := by
  simpa only [polynomial, MacaulayLowestBounds.polynomial, Fintype.card_fin] using
    CharacteristicLowestBounds.lowest_inner_degree_le
      (Macaulay.matrix (rows q d coordinate) (degrees d) W) E
      (Macaulay.matrix_inner_degree _ _ _ E (coefficient_inner_degree q d coordinate E hq)) k

omit [CommRing R] in
theorem parameter_coefficient_size_le (q : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (d : Fin n → ℕ) (coordinate : Fin n) (W E b : ℕ)
    (hdegree : ∀ j e, ((q j).coeff e).natDegree ≤ E)
    (hmass : ∀ j e, coefficientMass ((q j).coeff e) ≤ 2 ^ b) (k l : ℕ) :
    (((polynomial q d coordinate W).coeff k).coeff l).natAbs.size ≤
      (FixedWidthPolynomial.count (n + 1) W).size * FixedWidthPolynomial.count (n + 1) W +
        FixedWidthPolynomial.count (n + 1) W * (b + 3) + 1 := by
  simpa only [polynomial, MacaulayLowestBounds.polynomial, Fintype.card_fin, Nat.add_assoc] using
    CharacteristicLowestBounds.lowest_bivariate_coefficient_size_le
      (Macaulay.matrix (rows q d coordinate) (degrees d) W) E (b + 2)
      (Macaulay.matrix_inner_degree _ _ _ E (coefficient_inner_degree q d coordinate E hdegree))
      (Macaulay.matrix_entry_nested_mass_le _ _ _ (b + 2) (coefficient_nested_mass q d coordinate b hmass)) k l

noncomputable def coefficientMap (φ : R →+* ℝ) (a : ℝ × (Fin n → ℝ)) : Polynomial R →+* ℝ :=
  Polynomial.eval₂RingHom φ a.1

def chart (a : ℝ × (Fin n → ℝ)) (j : Fin (n + 1)) : ℝ :=
  (layout.symm j).elim 1 a.2

theorem coefficientMap_contDiff (φ : R →+* ℝ) (p : Polynomial R) :
    ContDiff ℝ 1 (fun a : ℝ × (Fin n → ℝ) => coefficientMap φ a p) :=
  ParametricPolynomialCalculus.polynomial_eval₂ p (fun _ => φ) Prod.fst 1
    (fun _ => contDiff_const) contDiff_fst

omit [CommRing R] in
theorem chart_contDiff (j : Fin (n + 1)) :
    ContDiff ℝ 1 (fun a : ℝ × (Fin n → ℝ) => chart a j) := by
  cases hj : layout.symm j with
  | none => simpa only [chart, hj, Option.elim_none] using
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ × (Fin n → ℝ) => (1 : ℝ)))
  | some i => simpa only [chart, hj, Option.elim_some, Function.comp_def] using
      (contDiff_apply ℝ (fun _ : Fin n => ℝ) i).comp contDiff_snd

omit [CommRing R] in
theorem chart_nonzero (a : ℝ × (Fin n → ℝ)) : ∃ j, chart a j ≠ 0 := by
  refine ⟨layout none, ?_⟩
  simp only [chart, Equiv.symm_apply_apply, Option.elim_none, ne_eq, one_ne_zero, not_false_eq_true]

theorem family_eq (φ : R →+* ℝ) (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ d j) (coordinate : Fin n) (a : ℝ × (Fin n → ℝ)) :
    MacaulayRegularPersistence.family (rows q d coordinate) (coefficientMap φ) chart a =
      Fin.cons (a.1 - a.2 coordinate) (fun j => (q j).eval₂ φ a.2) := by
  exact AffineCoordinateSystem.eval_rows φ q d hD coordinate a.1 a.2

omit [CommRing R] in
/-- The extra coordinate equation gives a triangular derivative with the
original Jacobian as its spatial block. -/
theorem augment_isInvertible (f : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) (coordinate : Fin n)
    (hf : DifferentiableAt ℝ f x) (hJac : (fderiv ℝ f x).IsInvertible) :
    (fderiv ℝ (fun a : ℝ × (Fin n → ℝ) => (Fin.cons (a.1 - a.2 coordinate) (f a.2) : Fin (n + 1) → ℝ))
      (x coordinate, x)).IsInvertible := by
  let a := (x coordinate, x)
  let D : (ℝ × (Fin n → ℝ)) →L[ℝ] (Fin (n + 1) → ℝ) := ContinuousLinearMap.pi
    (Fin.cons (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ) -
      (ContinuousLinearMap.proj coordinate).comp (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)))
      (fun j => (ContinuousLinearMap.proj j).comp ((fderiv ℝ f x).comp
        (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)))))
  have hfst : HasFDerivAt (Prod.fst : ℝ × (Fin n → ℝ) → ℝ)
      (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)) a := hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : ℝ × (Fin n → ℝ) → Fin n → ℝ)
      (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)) a := hasFDerivAt_snd
  have hder : HasFDerivAt (fun a : ℝ × (Fin n → ℝ) =>
      (Fin.cons (a.1 - a.2 coordinate) (f a.2) : Fin (n + 1) → ℝ)) D a := by
    apply hasFDerivAt_pi.mpr
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · convert hfst.sub ((hasFDerivAt_apply (𝕜 := ℝ) coordinate x).comp a hsnd) using 1 <;> rfl
    · exact ((hasFDerivAt_apply (𝕜 := ℝ) j (f x)).comp x hf.hasFDerivAt).comp a hsnd
  rw [hder.fderiv]
  have hinj : Function.Injective D := by
    intro u v huv
    have htail : fderiv ℝ f x u.2 = fderiv ℝ f x v.2 := by
      funext j
      exact congrFun huv j.succ
    have hsp := hJac.injective htail
    have hhead := congrFun huv 0
    change u.1 - u.2 coordinate = v.1 - v.2 coordinate at hhead
    rw [hsp] at hhead
    exact Prod.ext (sub_left_inj.mp hhead) hsp
  have hdim : Module.finrank ℝ (ℝ × (Fin n → ℝ)) = Module.finrank ℝ (Fin (n + 1) → ℝ) := by
    simp [Module.finrank_prod, Nat.add_comm]
  refine ⟨(LinearEquiv.ofInjectiveOfFinrankEq D.toLinearMap hinj hdim).toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.coe_injective
  exact LinearEquiv.coe_ofInjectiveOfFinrankEq _ hinj hdim

/-- Every regular affine root annihilates the same concrete nonzero bounded
coordinate polynomial, without a finite-solution-set hypothesis. -/
theorem eval_eq_zero [IsDomain R] (φ : R →+* ℝ)
    (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ d j) (hd : ∀ j, 0 < d j) (coordinate : Fin n) (W : ℕ)
    (hW : Macaulay.level (degrees d) < 2 ^ W) (x : Fin n → ℝ)
    (hroot : ∀ j, (q j).eval₂ φ x = 0)
    (hJac : (fderiv ℝ (fun y => fun j => (q j).eval₂ φ y) x).IsInvertible) :
    (polynomial q d coordinate W).eval₂ φ (x coordinate) = 0 := by
  let f := fun y : Fin n → ℝ => fun j => (q j).eval₂ φ y
  have hf : ContDiff ℝ 1 f := contDiff_pi.mpr
    (fun j => (ProjectionCritical.contDiff_eval φ (q j)).of_le le_top)
  have hfamily : MacaulayRegularPersistence.family (rows q d coordinate) (coefficientMap φ) chart =
      (fun a : ℝ × (Fin n → ℝ) => Fin.cons (a.1 - a.2 coordinate) (f a.2)) :=
    funext (family_eq φ q d hD coordinate)
  have he := MacaulayRegularPersistence.numerator_trailingCoeff_eq_zero_of_regular_root
    (rows q d coordinate) (degrees d) W
    (MacaulayUniversal.degree_lt_width _ _ (degrees_pos d hd) hW) hW
    (homogeneous q d coordinate) (degrees_pos d hd) (coefficientMap φ) chart
    (coefficientMap_contDiff φ) chart_contDiff chart_nonzero (x coordinate, x)
    (by rw [hfamily]; ext j; refine Fin.cases (by simp) (fun j => hroot j) j)
    (by
      rw [hfamily]
      exact augment_isInvertible f x coordinate (hf.contDiffAt.differentiableAt one_ne_zero) hJac)
  change (coefficientMap φ (x coordinate, x))
    (MacaulayLowestBounds.polynomial (rows q d coordinate) (degrees d) W) = 0
  rw [MacaulayLowestBounds.polynomial_eq]
  exact he

end LeanCanny.Geometry.AffineCoordinateEliminant
