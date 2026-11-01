/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.ClosedFormulaWitnessBounds
/-! # One actual integer equation preserves components of a closed Boolean formula

AND becomes a sum of two squares and OR becomes a product. The witness
coordinates have already been proved connected through one common section,
so this step introduces no Boolean selector or additional components.
-/
@[expose] public section
namespace LeanCanny.Connectivity.ClosedFormulaWitness
open ETR Set MvPolynomial LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Variables (n : ℕ) (p : Formula) := Fin n ⊕ (Slot p × Fin 2)

noncomputable def atomPolynomial (n : ℕ) (p q : Formula) : MvPolynomial (Variables n p) ℤ :=
  if h : q∈atoms p then polynomial n p ⟨q,h⟩ else C 1

noncomputable def aggregate (n : ℕ) (p : Formula) : Formula → MvPolynomial (Variables n p) ℤ
  | .falsum => C 1
  | .not .falsum => 0
  | .eqZero t => atomPolynomial n p (.eqZero t)
  | .not (.ltZero t) => atomPolynomial n p (.not (.ltZero t))
  | .and a b => aggregate n p a ^ 2 + aggregate n p b ^ 2
  | .or a b => aggregate n p a * aggregate n p b
  | _ => C 1

private theorem squares_zero (a b : ℝ) : a^2+b^2=0 ↔ a=0 ∧ b=0 := by
  constructor
  · intro H
    constructor <;> nlinarith [sq_nonneg a,sq_nonneg b]
  · rintro ⟨rfl,rfl⟩
    norm_num

theorem aggregate_zero_iff (n : ℕ) (p : Formula) {q : Formula} (hq : Closed q) (z : Variables n p → ℝ) :
    (aggregate n p q).eval₂ (Int.castRingHom ℝ) z=0 ↔
      eval (fun a => (atomPolynomial n p a).eval₂ (Int.castRingHom ℝ) z=0) q := by
  induction hq with
  | falsum => simp [aggregate,eval]
  | verum => simp [aggregate,eval]
  | eqZero _ => rfl
  | nonnegative _ => rfl
  | and _ _ HA HB =>
    simp only [aggregate,MvPolynomial.eval₂_add,MvPolynomial.eval₂_pow,squares_zero,eval]
    exact and_congr HA HB
  | or _ _ HA HB =>
    simp only [aggregate,MvPolynomial.eval₂_mul,mul_eq_zero,eval]
    exact or_congr HA HB

theorem single_zero_iff {p : Formula} (hp : Closed p) (n : ℕ)
    (z : (Fin n → ℝ) × (Slot p → CircularWitness.Plane)) :
    (aggregate n p p).eval₂ (Int.castRingHom ℝ) (coordinates z)=0 ↔
      predicate p (fun i => family n p i z.1=‖z.2 i‖^2) := by
  rw [aggregate_zero_iff n p hp]
  apply (eval_congr hp _ _ ?_).trans (witness_polynomials_iff p n z)
  intro q hq
  simp only [atomPolynomial,dite_eq_left hq]

noncomputable def coordinateHomeomorph (n : ℕ) (p : Formula) :
    ((Fin n → ℝ) × (Slot p → CircularWitness.Plane)) ≃ₜ (Variables n p → ℝ) where
  toFun := coordinates
  invFun z := (fun i => z (Sum.inl i),fun i => WithLp.toLp 2 (fun j => z (Sum.inr (i,j))))
  left_inv z := by
    apply Prod.ext
    · rfl
    · rfl
  right_inv z := by
    funext i
    cases i <;> rfl
  continuous_toFun := by
    apply continuous_pi
    intro i
    cases i with
    | inl i => exact (continuous_apply i).comp continuous_fst
    | inr i =>
      exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i.2).comp ((continuous_apply i.1).comp (continuous_snd : Continuous (fun z : (Fin n → ℝ) × (Slot p → CircularWitness.Plane) => z.2)))
  continuous_invFun := (continuous_pi (fun i => continuous_apply (Sum.inl i))).prodMk
    (continuous_pi (fun i => (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      (continuous_pi (fun j => continuous_apply (Sum.inr (i,j))))))

abbrev ZeroSet (n : ℕ) (p : Formula) :=
  {z : Variables n p → ℝ // (aggregate n p p).eval₂ (Int.castRingHom ℝ) z=0}

noncomputable def algebraicHomeomorph {p : Formula} (hp : Closed p) (n : ℕ) : Witness n p ≃ₜ ZeroSet n p :=
  (coordinateHomeomorph n p).subtype (fun z => (single_zero_iff hp n z).symm)

noncomputable def algebraicProjection {p : Formula} (hp : Closed p) (n : ℕ) (z : ZeroSet n p) :
    (Description.mk n p).realization := projection hp n ((algebraicHomeomorph hp n).symm z)

theorem algebraicProjection_apply {p : Formula} (hp : Closed p) (n : ℕ) (z : ZeroSet n p) (i : Fin n) :
    (algebraicProjection hp n z).val i = z.val (Sum.inl i) := rfl

private theorem homeomorph_joined' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x y : X) : JoinedIn univ x y ↔ JoinedIn univ (e x) (e y) := by
  constructor
  · intro H
    exact (H.map e.continuous.continuousOn).mono (subset_univ _)
  · intro H
    simpa only [Homeomorph.symm_apply_apply] using (H.map e.symm.continuous.continuousOn).mono (subset_univ _)

theorem algebraic_joined_iff {p : Formula} (hp : Closed p) (n : ℕ) (y z : ZeroSet n p) :
    JoinedIn univ y z ↔ JoinedIn univ (algebraicProjection hp n y) (algebraicProjection hp n z) :=
  (homeomorph_joined' (algebraicHomeomorph hp n).symm y z).trans (joined_iff hp n _ _)

theorem algebraic_preconnected_iff {p : Formula} (hp : Closed p) (n : ℕ) :
    IsPreconnected (univ : Set (ZeroSet n p)) ↔ IsPreconnected (Description.mk n p).realization := by
  have HE := (algebraicHomeomorph hp n).symm.isPreconnected_image (s := univ)
  rw [Set.image_univ_of_surjective (algebraicHomeomorph hp n).symm.surjective] at HE
  exact HE.symm.trans (preconnected_iff hp n)

end LeanCanny.Connectivity.ClosedFormulaWitness
