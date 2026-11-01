/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.WeakBooleanWitness
public import LeanCanny.Connectivity.FormulaStrictWitness
public import LeanCanny.ETR.FinitePolynomial
/-! # Component-preserving polynomial witnesses for actual closed Boolean formulas

Equality, nonnegativity, conjunction and disjunction use the original ETR
syntax. Every distinct atom has two real witness coordinates. The output
retains the positive Boolean structure, with literal integer-polynomial
zero tests in place of its atoms. All clauses share one continuous witness
section, so unions meeting at their closed boundaries preserve components.
-/
@[expose] public section
namespace LeanCanny.Connectivity.ClosedFormulaWitness
open ETR Set LeanCanny.Geometry MvPolynomial CircularWitness
open scoped Classical
set_option backward.isDefEq.respectTransparency false

inductive Closed : Formula → Prop where
  | falsum : Closed .falsum
  | verum : Closed (.not .falsum)
  | eqZero (t : Term) : Closed (.eqZero t)
  | nonnegative (t : Term) : Closed (.not (.ltZero t))
  | and {p q} : Closed p → Closed q → Closed (.and p q)
  | or {p q} : Closed p → Closed q → Closed (.or p q)

def atoms : Formula → List Formula
  | .eqZero t => [.eqZero t]
  | .not (.ltZero t) => [.not (.ltZero t)]
  | .and p q | .or p q => atoms p ++ atoms q
  | _ => []

def eval (σ : Formula → Prop) : Formula → Prop
  | .falsum => False
  | .eqZero t => σ (.eqZero t)
  | .not .falsum => True
  | .not (.ltZero t) => σ (.not (.ltZero t))
  | .and p q => eval σ p ∧ eval σ q
  | .or p q => eval σ p ∨ eval σ q
  | _ => False

def atomTerm : Formula → Term
  | .eqZero t => .mul (.const (-1)) (.mul t t)
  | .not (.ltZero t) => t
  | _ => .const (-1)

theorem eval_mono {p : Formula} (hp : Closed p) (σ τ : Formula → Prop)
    (H : ∀ q ∈ atoms p, σ q → τ q) : eval σ p → eval τ p := by
  induction hp with
  | falsum => exact False.elim
  | verum => exact fun _ => trivial
  | eqZero t => exact H _ (List.mem_singleton_self _)
  | nonnegative t => exact H _ (List.mem_singleton_self _)
  | and _ _ HA HB =>
    exact fun h => ⟨HA (fun q hq => H q (List.mem_append_left _ hq)) h.1,
      HB (fun q hq => H q (List.mem_append_right _ hq)) h.2⟩
  | or _ _ HA HB =>
    exact Or.imp (HA (fun q hq => H q (List.mem_append_left _ hq)))
      (HB (fun q hq => H q (List.mem_append_right _ hq)))

theorem eval_congr {p : Formula} (hp : Closed p) (σ τ : Formula → Prop)
    (H : ∀ q ∈ atoms p, σ q ↔ τ q) : eval σ p ↔ eval τ p :=
  ⟨eval_mono hp σ τ (fun q hq => (H q hq).mp),eval_mono hp τ σ (fun q hq => (H q hq).mpr)⟩

theorem eval_values {p : Formula} (hp : Closed p) (n : ℕ) (x : Fin n → ℝ) :
    eval (fun q => 0≤(atomTerm q).eval (Formula.extend x)) p ↔ p.Holds (Formula.extend x) := by
  induction hp with
  | falsum => rfl
  | verum => simp [eval,Formula.Holds]
  | eqZero t =>
    simp only [eval,atomTerm,Term.eval,Formula.Holds,Int.cast_neg,Int.cast_one]
    constructor
    · intro H
      nlinarith [sq_nonneg (t.eval (Formula.extend x))]
    · intro H
      rw [H]
      norm_num
  | nonnegative t => exact not_lt.symm
  | and _ _ HA HB => exact and_congr HA HB
  | or _ _ HA HB => exact or_congr HA HB

abbrev Slot (p : Formula) := {q : Formula // q∈atoms p}
instance (p : Formula) : Finite (Slot p) := (atoms p).finite_toSet.to_subtype

def predicate (p : Formula) (a : Slot p → Prop) : Prop :=
  eval (fun q => if h : q∈atoms p then a ⟨q,h⟩ else False) p

theorem predicate_mono {p : Formula} (hp : Closed p) :
    ∀ a b : Slot p → Prop, (∀ i, a i → b i) → predicate p a → predicate p b := by
  intro a b H
  apply eval_mono hp
  intro q hq
  simp only [dite_eq_left hq]
  exact H ⟨q,hq⟩

noncomputable def family (n : ℕ) (p : Formula) (i : Slot p) (x : Fin n → ℝ) : ℝ :=
  (atomTerm i.val).eval (Formula.extend x)

theorem base_holds {p : Formula} (hp : Closed p) (n : ℕ) (x : Fin n → ℝ) :
    predicate p (fun i => 0≤family n p i x) ↔ p.Holds (Formula.extend x) := by
  apply (eval_congr hp _ (fun q => 0≤(atomTerm q).eval (Formula.extend x)) ?_).trans (eval_values hp n x)
  intro q hq
  simp only [dite_eq_left hq,family]

noncomputable def baseHomeomorph {p : Formula} (hp : Closed p) (n : ℕ) :
    WeakBooleanWitness.Base (family n p) (predicate p) ≃ₜ (Description.mk n p).realization := by
  change {x : Fin n → ℝ // predicate p (fun i => 0≤family n p i x)} ≃ₜ
    {x : Fin n → ℝ // p.Holds (Formula.extend x)}
  have HE : {x : Fin n → ℝ | predicate p (fun i => 0≤family n p i x)} =
      {x : Fin n → ℝ | p.Holds (Formula.extend x)} := Set.ext (fun x => base_holds hp n x)
  exact Homeomorph.setCongr HE

abbrev Witness (n : ℕ) (p : Formula) := WeakBooleanWitness.Space (family n p) (predicate p)

noncomputable def projection {p : Formula} (hp : Closed p) (n : ℕ) (z : Witness n p) :
    (Description.mk n p).realization :=
  baseHomeomorph hp n (WeakBooleanWitness.projection _ _ (predicate_mono hp) z)

private theorem homeomorph_joined {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x y : X) : JoinedIn univ x y ↔ JoinedIn univ (e x) (e y) := by
  constructor
  · intro H
    exact (H.map e.continuous.continuousOn).mono (subset_univ _)
  · intro H
    simpa only [Homeomorph.symm_apply_apply] using (H.map e.symm.continuous.continuousOn).mono (subset_univ _)

theorem joined_iff {p : Formula} (hp : Closed p) (n : ℕ) (y z : Witness n p) :
    JoinedIn univ y z ↔ JoinedIn univ (projection hp n y) (projection hp n z) := by
  exact (WeakBooleanWitness.joined_iff _ _ (predicate_mono hp)
    (fun i => FormulaStrictWitness.continuous_eval n (atomTerm i.val)) y z).trans
    (homeomorph_joined (baseHomeomorph hp n) _ _)

theorem preconnected_iff {p : Formula} (hp : Closed p) (n : ℕ) :
    IsPreconnected (univ : Set (Witness n p)) ↔ IsPreconnected (Description.mk n p).realization := by
  have H := WeakBooleanWitness.preconnected_iff _ _ (predicate_mono hp)
    (fun i => FormulaStrictWitness.continuous_eval n (atomTerm i.val))
  have HE := (baseHomeomorph hp n).isPreconnected_image (s := univ)
  rw [Set.image_univ_of_surjective (baseHomeomorph hp n).surjective] at HE
  exact H.trans (HE.symm.trans (preconnectedSpace_iff_univ.symm.trans isPreconnected_iff_preconnectedSpace.symm))

noncomputable def polynomial (n : ℕ) (p : Formula) (i : Slot p) :
    MvPolynomial (Fin n ⊕ (Slot p × Fin 2)) ℤ :=
  rename Sum.inl ((atomTerm i.val).finitePolynomial n) - X (Sum.inr (i,0))^2 - X (Sum.inr (i,1))^2

noncomputable def coordinates {n : ℕ} {p : Formula} (z : (Fin n → ℝ) × (Slot p → Plane)) :
    Fin n ⊕ (Slot p × Fin 2) → ℝ := Sum.elim z.1 (fun j => z.2 j.1 j.2)

theorem polynomial_zero_iff (n : ℕ) (p : Formula) (i : Slot p)
    (z : (Fin n → ℝ) × (Slot p → Plane)) :
    (polynomial n p i).eval₂ (Int.castRingHom ℝ) (coordinates z) = 0 ↔ family n p i z.1=‖z.2 i‖^2 := by
  simp only [polynomial,MvPolynomial.eval₂_sub,MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_rename,Term.eval_finitePolynomial,family,coordinates,Function.comp_def,Sum.elim_inl,Sum.elim_inr]
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  constructor <;> intro H <;> linarith

theorem witness_polynomials_iff (p : Formula) (n : ℕ)
    (z : (Fin n → ℝ) × (Slot p → Plane)) :
    predicate p (fun i => (polynomial n p i).eval₂ (Int.castRingHom ℝ) (coordinates z)=0) ↔
      predicate p (fun i => family n p i z.1=‖z.2 i‖^2) := by
  have H : (fun i => (polynomial n p i).eval₂ (Int.castRingHom ℝ) (coordinates z)=0) =
      (fun i => family n p i z.1=‖z.2 i‖^2) := by
    funext i
    exact propext (polynomial_zero_iff n p i z)
  rw [H]

end LeanCanny.Connectivity.ClosedFormulaWitness
