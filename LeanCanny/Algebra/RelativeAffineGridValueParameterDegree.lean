/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RelativeAffineGridValueGram
public import LeanCanny.Algebra.TriplePolynomialParameterFlatten
public import LeanCanny.Algebra.MultivariateTarskiDegreeBounds
/-! # Joint radius and center degree for the actual affine value certificate -/
@[expose] public section
namespace LeanCanny.Algebra.RelativeAffineGridValueParameterDegree
open Polynomial MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {σ R : Type*} [CommRing R]

private theorem sum_bound {I : Type*} (s : Finset I) (p : I → Polynomial (MvPolynomial σ R)) (E : ℕ)
    (hp : ∀ i ∈ s, ∀ j, ((p i).coeff j).totalDegree ≤ E) :
    ∀ j, ((∑ i ∈ s, p i).coeff j).totalDegree ≤ E := by
  induction s using Finset.induction_on with
  | empty => intro j; simp
  | @insert i s hi ih =>
    intro j
    rw [Finset.sum_insert hi, Polynomial.coeff_add]
    exact (MvPolynomial.totalDegree_add _ _).trans
      (max_le (hp i (Finset.mem_insert_self _ _) j)
        (ih (fun k hk => hp k (Finset.mem_insert_of_mem hk)) j))

private theorem product_bound {I : Type*} (s : Finset I) (p : I → Polynomial (MvPolynomial σ R)) (D : I → ℕ)
    (hp : ∀ i ∈ s, ∀ j, ((p i).coeff j).totalDegree ≤ D i) :
    ∀ j, ((∏ i ∈ s, p i).coeff j).totalDegree ≤ ∑ i ∈ s, D i := by
  induction s using Finset.induction_on with
  | empty => intro j; simp only [Finset.prod_empty, Finset.sum_empty, Polynomial.coeff_one]; split_ifs <;> simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact MultivariateTarskiDegreeBounds.mul_coefficient _ _ _ _
      (hp i (Finset.mem_insert_self _ _)) (ih (fun k hk => hp k (Finset.mem_insert_of_mem hk)))

private theorem determinant_bound {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (Polynomial (MvPolynomial σ R))) (E : ℕ)
    (hM : ∀ a b j, ((M a b).coeff j).totalDegree ≤ E) (j : ℕ) :
    (M.det.coeff j).totalDegree ≤ Fintype.card I * E := by
  rw [Matrix.det_apply]
  apply sum_bound
  intro e _ k
  rw [Polynomial.coeff_smul]
  apply (MvPolynomial.totalDegree_smul_le _ _).trans
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using
    product_bound Finset.univ (fun i => M (e i) i) (fun _ => E) (fun i _ => hM (e i) i) k

private theorem block_property {C : Type*} [CommRing C] {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) C) (d : Fin n → ℕ) (W : ℕ)
    (P : C → Prop) (h0 : P 0) (h1 : P 1) (hn : ∀ a, P a → P (-a))
    (hp : ∀ i v, P ((p i).coeff v)) :
    ∀ a b, P (ProjectiveGramEliminant.block (MacaulayFullBox.matrix p d W) a b) := by
  have HA : ∀ a b, P (MacaulayFullBox.matrix p d W a b) := by
    intro a b
    rcases MacaulayFullBox.entry_cases p d W a b with H | H | ⟨i, v, H⟩
    · rw [H]; exact h0
    · rw [H]; exact h1
    · rw [H]; exact hp i v
  intro a b
  rcases a with a | a <;> rcases b with b | b
  · change P ((1 : Matrix (MacaulayFullBox.Row n W) (MacaulayFullBox.Row n W) C) a b)
    by_cases H : a = b
    · simpa only [Matrix.one_apply, ite_eq_left H] using h1
    · simpa only [Matrix.one_apply, ite_eq_right H] using h0
  · exact HA a b
  · exact hn _ (HA b a)
  · exact h0

private theorem box_bound {C : Type*} [CommRing C] {n : ℕ}
    (φ : C →+* MvPolynomial σ R)
    (p : Fin n → MvPolynomial (Fin n) (Polynomial C)) (d : Fin n → ℕ) (W E : ℕ)
    (hp : ∀ i v j, (φ (((p i).coeff v).coeff j)).totalDegree ≤ E) (j : ℕ) :
    (φ ((RelativeProjectiveBoxGram.polynomial p d W).coeff j)).totalDegree ≤
      (n + 2) * FixedWidthPolynomial.count n W * E := by
  let M := ProjectiveGramEliminant.block (MacaulayFullBox.matrix p d W)
  have HB : ∀ a b k, (((M a b).map φ).coeff k).totalDegree ≤ E := by
    intro a b k
    simp only [Polynomial.coeff_map]
    exact block_property p d W (fun a => (φ (a.coeff k)).totalDegree ≤ E)
      (by simp) (by simp only [Polynomial.coeff_one]; split_ifs <;> simp)
      (fun a ha => by simpa only [Polynomial.coeff_neg, map_neg, MvPolynomial.totalDegree_neg] using ha)
      (fun i v => hp i v k) a b
  have HD := determinant_bound (M.map (Polynomial.mapRingHom φ)) E HB j
  have HE : (M.map (Polynomial.mapRingHom φ)).det = M.det.map φ :=
    (RingHom.map_det (Polynomial.mapRingHom φ) M).symm
  rw [HE] at HD
  dsimp only [M] at HD
  rw [ProjectiveGramEliminant.block_det] at HD
  simpa only [M, RelativeProjectiveBoxGram.polynomial, Polynomial.coeff_map, Polynomial.coe_mapRingHom,
    ProjectiveBoxGramEliminant.card_block] using HD

section Value
variable {C : Type*} [CommRing C] {n : ℕ}

private theorem system_bound (φ : Polynomial C →+* MvPolynomial σ R)
    (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial C))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial C)) (e E : ℕ)
    (hH : ∀ i v, (φ ((H i).coeff v)).totalDegree ≤ E)
    (hF : ∀ v, (φ (F.coeff v)).totalDegree ≤ E)
    (j : Fin (n + 1)) (v : Fin (n + 1) →₀ ℕ) (k : ℕ) :
    (φ (((RelativeProjectiveValueGram.system H F e j).coeff v).coeff k)).totalDegree ≤ E := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [RelativeProjectiveValueGram.system, Fin.cases_zero, MvPolynomial.coeff_sub,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, MvPolynomial.coeff_X_pow, Polynomial.coeff_sub, map_sub]
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · cases k with
      | zero => simp
      | succ k =>
        rw [Polynomial.coeff_X_mul, Polynomial.coeff_C]
        split_ifs
        · exact hF v
        · simp
    · split_ifs
      · simp only [Polynomial.coeff_one]
        split_ifs <;> simp
      · simp
  · simp only [RelativeProjectiveValueGram.system, Fin.cases_succ, MvPolynomial.coeff_map, Polynomial.coeff_C]
    split_ifs
    · exact hH i v
    · simp

private theorem projective_bound (φ : Polynomial C →+* MvPolynomial σ R)
    (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial C))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial C)) (d : Fin n → ℕ) (e W E : ℕ)
    (hH : ∀ i v, (φ ((H i).coeff v)).totalDegree ≤ E)
    (hF : ∀ v, (φ (F.coeff v)).totalDegree ≤ E) (k : ℕ) :
    (φ ((RelativeProjectiveValueGram.annihilator H F d e W).coeff k)).totalDegree ≤
      RelativeProjectiveValueGram.dimension n W * E := by
  cases k with
  | zero => simp [RelativeProjectiveValueGram.annihilator]
  | succ k =>
    rw [RelativeProjectiveValueGram.annihilator, Polynomial.coeff_X_mul, Polynomial.coeff_reflect]
    simpa only [RelativeProjectiveValueGram.dimension, RelativeProjectiveValueGram.polynomial, Nat.add_assoc] using
      box_bound φ (RelativeProjectiveValueGram.system H F e) (RelativeProjectiveValueGram.degrees d e) W E
        (system_bound φ H F e E hH hF) _

private theorem homogenized_bound (φ : Polynomial C →+* MvPolynomial σ R)
    (q : MvPolynomial (Fin n) (Polynomial C)) (e E : ℕ)
    (hq : ∀ v, (φ (q.coeff v)).totalDegree ≤ E) (v : Fin (n + 1) →₀ ℕ) :
    (φ ((RelativeAffineGridValueGram.test q e).coeff v)).totalDegree ≤ E := by
  by_cases HZ : (RelativeAffineGridValueGram.test q e).coeff v = 0
  · simp only [HZ, map_zero, MvPolynomial.totalDegree_zero, Nat.zero_le]
  · obtain ⟨w, hw, _⟩ := MvPolynomial.coeff_rename_ne_zero (AffineFiniteCoordinates.layout n) _ v HZ
    rw [← hw, RelativeAffineGridValueGram.test,
      MvPolynomial.coeff_rename_mapDomain _ (AffineFiniteCoordinates.layout n).injective,
      WeightedHomogenization.coefficient]
    split_ifs
    · exact hq _
    · simp

/-- Every coefficient homomorphism can measure a joint finite parameter box;
there are no nonvanishing, exact-degree or center-specialization premises. -/
theorem mapped_degree (φ : Polynomial C →+* MvPolynomial σ R)
    (p : Fin n → Polynomial (Polynomial C)) (q : MvPolynomial (Fin n) (Polynomial C))
    (d : Fin n → ℕ) (e E : ℕ)
    (hp : ∀ i j, (φ ((p i).coeff j)).totalDegree ≤ E)
    (hq : ∀ v, (φ (q.coeff v)).totalDegree ≤ E) (j : ℕ) :
    (φ ((RelativeAffineGridValueGram.annihilator p q d e).coeff j)).totalDegree ≤
      RelativeProjectiveValueGram.dimension n (RelativeAffineGridValueGram.width d e) * E := by
  apply projective_bound
  · intro i v
    apply homogenized_bound
    intro w
    rw [RelativeAffineGridValueGram.rows, DiagonalParameterBits.coefficient]
    split_ifs
    · exact hp i _
    · simp
  · exact homogenized_bound φ q e E hq

end Value

/-- Radius and ALL center variables stay formal in the literal value certificate. -/
theorem degree {n A : ℕ}
    (p : Fin n → Polynomial (Polynomial (MvPolynomial (Fin A) ℤ)))
    (q : MvPolynomial (Fin n) (Polynomial (MvPolynomial (Fin A) ℤ)))
    (d : Fin n → ℕ) (e E : ℕ)
    (hp : ∀ i j, (TriplePolynomialParameterFlatten.one ((p i).coeff j)).totalDegree ≤ E)
    (hq : ∀ v, (TriplePolynomialParameterFlatten.one (q.coeff v)).totalDegree ≤ E) (j : ℕ) :
    (TriplePolynomialParameterFlatten.one ((RelativeAffineGridValueGram.annihilator p q d e).coeff j)).totalDegree ≤
      RelativeProjectiveValueGram.dimension n (RelativeAffineGridValueGram.width d e) * E :=
  mapped_degree TriplePolynomialParameterFlatten.one p q d e E hp hq j

end LeanCanny.Algebra.RelativeAffineGridValueParameterDegree
