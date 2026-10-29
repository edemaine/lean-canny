/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexAffineStageCorrect
public import LeanCanny.Algebra.FlatAffineCriticalStage

/-! # The affine circuit computes the original stage rows

Normal and ancestral-level wires may have been computed by preceding shared
programs. At every satisfying assignment their prescribed values give exactly
the original ambient-coordinate Lagrange equations, without multiplier powers.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.AffineStage
open MvPolynomial LeanCanny.Algebra
open scoped Classical BigOperators

/-- Source identity and the actual normal/level values identify every output
with its original affine-stage polynomial at the same assignment. -/
theorem original_row {ι : Type*} (C : Inputs) (h : C.Valid) (wire : ℕ → MvPolynomial ℕ ℤ)
    (hr : Differential.Realizes wire C.start C.source) (hin : ∀ i < C.start, wire i = X i)
    (p : MvPolynomial (Fin C.count) ℤ)
    (hsource : wire C.sourceOutput = rename (fun i : Fin C.count => C.ambient + i.val) p)
    (s : Finset (Fin C.count)) (a : Fin (C.count + 1) → Fin C.count → ℤ)
    (b : Fin C.count → MvPolynomial ι ℤ) (env : ℕ → ℂ) (hg : ∀ g ∈ gates C, g.Holds env)
    (z : ι ⊕ FlatAffineCriticalStage.Variables C.count → ℂ)
    (hspace : ∀ i : Fin C.count, env (C.ambient + i.val) = z (FlatAffineCriticalStage.ambient i))
    (hμ : ∀ j : Fin (C.count + 1), env (C.multipliers + j.val) = z (FlatAffineCriticalStage.multiplier j))
    (ha : ∀ r i, env (C.normal r.val i.val) = (a r i : ℂ))
    (hb : ∀ r, env (C.level r.val) = (b r).eval₂ (Int.castRingHom ℂ) (z ∘ Sum.inl))
    (hs : ∀ r : Fin C.count, C.active r.val = true ↔ r ∈ s)
    (r : FlatAffineCriticalStage.Variables C.count) :
    env (port C r) = (FlatAffineCriticalStage.row p s a b r).eval₂ (Int.castRingHom ℂ) z := by
  have hpoint : (fun i : Fin C.count => env (C.ambient + i.val)) = z ∘ FlatAffineCriticalStage.ambient := funext hspace
  cases r with
  | inl i =>
    have hd : (pderiv (C.ambient + i.val) (wire C.sourceOutput)).eval₂ (Int.castRingHom ℂ) env =
        (pderiv i p).eval₂ (Int.castRingHom ℂ) (z ∘ FlatAffineCriticalStage.ambient) := by
      rw [hsource, pderiv_rename (fun i j H => Fin.val_injective (Nat.add_left_cancel H)), eval₂_rename]
      exact congrArg ((pderiv i p).eval₂ (Int.castRingHom ℂ)) hpoint
    change env (gradientOutput C i.val) = (FlatAffineCriticalStage.gradient p a i).eval₂ (Int.castRingHom ℂ) z
    rw [gradient_sound C h wire hr hin env hg i.val i.isLt, FlatAffineCriticalStage.eval_gradient, hd]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg₂ (· * ·) (ha j i) (hμ j)
  | inr j =>
    refine Fin.cases ?_ (fun r => ?_) j
    · change env (sourceOutput C) = (rename FlatAffineCriticalStage.ambient p).eval₂ (Int.castRingHom ℂ) z
      rw [source_sound C h wire hr hin env hg, hsource, eval₂_rename, eval₂_rename]
      exact congrArg (p.eval₂ (Int.castRingHom ℂ)) hpoint
    · change env (heightOutput C r.val) = (FlatAffineCriticalStage.row p s a b (Sum.inr r.succ)).eval₂ (Int.castRingHom ℂ) z
      cases hc : C.active r.val with
      | true =>
        have hrs : r ∈ s := (hs r).mp hc
        rw [height_sound C env hg r.val r.isLt, hc]
        simp only [ite_true, FlatAffineCriticalStage.row, Fin.cases_succ, hrs, AffineHeightPolynomial.eval,
          eval₂_sub, eval₂_rename]
        rw [hb r]
        congr 1
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg₂ (· * ·) (ha r.succ i) (hspace i)
      | false =>
        have hrs : r ∉ s := by
          intro H
          have H' := (hs r).mpr H
          simp only [hc, Bool.false_eq_true] at H'
        rw [height_sound C env hg r.val r.isLt, hc]
        simpa only [Bool.false_eq_true, ite_false, FlatAffineCriticalStage.row, Fin.cases_succ, hrs, eval₂_X, Fin.val_succ] using hμ r.succ

/-- Every original stage root extends to the circuit, retaining all existing
inputs. This includes singular roots and zero multipliers. -/
theorem original_completion {ι : Type*} (C : Inputs) (h : C.Valid) (wire : ℕ → MvPolynomial ℕ ℤ)
    (hr : Differential.Realizes wire C.start C.source) (hin : ∀ i < C.start, wire i = X i)
    (p : MvPolynomial (Fin C.count) ℤ)
    (hsource : wire C.sourceOutput = rename (fun i : Fin C.count => C.ambient + i.val) p)
    (s : Finset (Fin C.count)) (a : Fin (C.count + 1) → Fin C.count → ℤ)
    (b : Fin C.count → MvPolynomial ι ℤ) (x : ℕ → ℂ)
    (z : ι ⊕ FlatAffineCriticalStage.Variables C.count → ℂ)
    (hspace : ∀ i : Fin C.count, x (C.ambient + i.val) = z (FlatAffineCriticalStage.ambient i))
    (hμ : ∀ j : Fin (C.count + 1), x (C.multipliers + j.val) = z (FlatAffineCriticalStage.multiplier j))
    (ha : ∀ r i, x (C.normal r.val i.val) = (a r i : ℂ))
    (hb : ∀ r, x (C.level r.val) = (b r).eval₂ (Int.castRingHom ℂ) (z ∘ Sum.inl))
    (hs : ∀ r : Fin C.count, C.active r.val = true ↔ r ∈ s)
    (hz : ∀ r, (FlatAffineCriticalStage.row p s a b r).eval₂ (Int.castRingHom ℂ) z = 0) :
    ∃ env : ℕ → ℂ, (∀ i < C.base, env i = x i) ∧
      (∀ g ∈ gates C, g.Holds env) ∧ ∀ j < C.count + (C.count + 1), env (output C j) = 0 := by
  obtain ⟨env, hp, hg⟩ := StraightLine.exists_completion x C.base (program C) (wellFormed C h)
  refine ⟨env, hp, hg, (outputs_zero_iff_ports C env).mpr ?_⟩
  intro r
  apply (original_row C h wire hr hin p hsource s a b env hg z ?_ ?_ ?_ ?_ hs r).trans (hz r)
  · intro i
    rw [hp _ (by have H := h.ambient; have Hi := i.isLt; omega)]
    exact hspace i
  · intro j
    rw [hp _ (by have H := h.multipliers; have Hj := j.isLt; omega)]
    exact hμ j
  · intro j i
    rw [hp _ (h.normal j.val j.isLt i.val i.isLt)]
    exact ha j i
  · intro j
    rw [hp _ (h.level j.val j.isLt)]
    exact hb j

end LeanCanny.ETR.ComplexCircuit.AffineStage
