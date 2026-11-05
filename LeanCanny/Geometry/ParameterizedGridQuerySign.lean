/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RelativeAffineGridValueGram
public import LeanCanny.Geometry.ParameterizedOrderedRootBranches

/-! # Constructed query-sign transport on independent coordinate grids

The query annihilator applies to the Cartesian grid of coordinate roots.
No additional row or guard is assumed in order to preserve its own truth.
The outer cutoff here is an actual finite cut mass, without a complexity bound.
-/

@[expose] public section
namespace LeanCanny.Geometry.ParameterizedGridQuerySign
open Set Polynomial LeanCanny.Algebra
open SymbolicScaledSquarefree (scalarEvaluation)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

noncomputable def annihilator (p : Fin n → (ℤ[X])[X]) (q : MvPolynomial (Fin n) ℤ[X]) : (ℤ[X])[X] :=
  RelativeAffineGridValueGram.annihilator p q (fun i => (p i).natDegree) (q.totalDegree + 1)

theorem annihilator_ne_zero (p : Fin n → (ℤ[X])[X]) (q : MvPolynomial (Fin n) ℤ[X])
    (hp : ∀ i, (p i).Monic) (hpos : ∀ i, 0 < (p i).natDegree) : annihilator p q ≠ 0 := by
  have h := RelativeAffineGridValueGram.selected_ne_zero p q (fun i => (p i).natDegree)
    (q.totalDegree + 1) (fun _ => rfl) hpos (Nat.succ_pos _) (Int.castRingHom ℝ) 0
    (fun i => by simpa only [(hp i).leadingCoeff, map_one] using (one_ne_zero : (1 : ℂ) ≠ 0))
  intro hz
  apply h
  change (annihilator p q).map _ = 0
  rw [hz, Polynomial.map_zero]

theorem annihilator_root (p : Fin n → (ℤ[X])[X]) (q : MvPolynomial (Fin n) ℤ[X])
    (r : ℝ) (z : Fin n → ℝ) (hz : ∀ i, (p i).eval₂ (scalarEvaluation r) (z i) = 0) :
    (annihilator p q).eval₂ (scalarEvaluation r) (q.eval₂ (scalarEvaluation r) z) = 0 :=
  RelativeAffineGridValueGram.root p q (fun i => (p i).natDegree) (q.totalDegree + 1)
    (fun _ => le_rfl) (Nat.le_succ _) (scalarEvaluation r) z hz

theorem continuous_query {a b : ℝ} (q : MvPolynomial (Fin n) ℤ[X]) (x : C(Ioo a b, Fin n → ℝ)) :
    Continuous (fun t : Ioo a b => q.eval₂ (scalarEvaluation t.val) (x t)) := by
  induction q using MvPolynomial.induction_on with
  | C r =>
    apply ((r.continuous_eval₂ (Int.castRingHom ℝ)).comp continuous_subtype_val).congr
    intro t
    simp only [MvPolynomial.eval₂_C, scalarEvaluation, Function.comp_apply, Polynomial.coe_eval₂RingHom]
  | add p q hp hq =>
    apply (hp.add hq).congr
    intro t
    simp only [MvPolynomial.eval₂_add, Pi.add_apply]
  | mul_X p i hp =>
    apply (hp.mul ((continuous_apply i).comp x.continuous)).congr
    intro t
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Pi.mul_apply, Function.comp_apply]

noncomputable def valuePath {a b : ℝ} (q : MvPolynomial (Fin n) ℤ[X])
    (x : C(Ioo a b, Fin n → ℝ)) : C(Ioo a b, ℝ) :=
  ⟨fun t => q.eval₂ (scalarEvaluation t.val) (x t), continuous_query q x⟩

theorem sign_transport {a b : ℝ} (p : Fin n → (ℤ[X])[X]) (q : MvPolynomial (Fin n) ℤ[X])
    (h : ParameterizedRootQuerySign.Avoids (annihilator p q) (fun _ : Unit => Polynomial.X) a b)
    (x : C(Ioo a b, Fin n → ℝ))
    (hx : ∀ t i, (p i).eval₂ (scalarEvaluation t.val) (x t i) = 0) (s t : Ioo a b) :
    SignType.sign (q.eval₂ (scalarEvaluation s.val) (x s)) =
      SignType.sign (q.eval₂ (scalarEvaluation t.val) (x t)) :=
  ParameterizedRootQuerySign.root_path_sign_value (annihilator p q) h (valuePath q x)
    (fun r => annihilator_root p q r.val (x r) (hx r)) s t

theorem exists_sign_cutoff (p : Fin n → (ℤ[X])[X]) (q : MvPolynomial (Fin n) ℤ[X])
    (hp : ∀ i, (p i).Monic) (hpos : ∀ i, 0 < (p i).natDegree) :
    ∃ M : ℕ, ∀ a b : ℝ, (M : ℝ) + 1 ≤ a →
      ∀ x : C(Ioo a b, Fin n → ℝ),
        (∀ t i, (p i).eval₂ (scalarEvaluation t.val) (x t i) = 0) →
        ∀ s t : Ioo a b,
          SignType.sign (q.eval₂ (scalarEvaluation s.val) (x s)) =
            SignType.sign (q.eval₂ (scalarEvaluation t.val) (x t)) := by
  refine ⟨ParameterizedOrderedRootBranches.cutMass (annihilator p q) (fun _ : Unit => Polynomial.X), ?_⟩
  intro a b ha x hx s t
  exact sign_transport p q
    (ParameterizedOrderedRootBranches.avoids_after_cutMass (annihilator p q)
      (annihilator_ne_zero p q hp hpos) (fun _ : Unit => Polynomial.X) a b ha) x hx s t

end LeanCanny.Geometry.ParameterizedGridQuerySign
