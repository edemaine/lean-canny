import LeanCanny.Connectivity.FiniteFiberMidpoint
import LeanCanny.Geometry.SymbolicRootCurveOrder
import LeanCanny.Encoding.CoordinateBranchOrdinals
import LeanCanny.Geometry.FrozenAffineBranches

/-! Finite endpoint selection, tied coordinates, and zero midpoint tests.
Run with `lake env lean -DwarningAsError=true scripts/CheckEndpointMidpoints.lean`.
-/

open LeanCanny.Geometry LeanCanny.Connectivity Set Filter
open scoped Topology

namespace EndpointMidpointRegression
open LeanCanny.Algebra
open scoped Classical

-- A midpoint test can vanish identically on a third branch. Strict-side
-- matching still rejects the incorrect endpoint candidate.
example : ¬EndpointMidpoint.Matches
    ({fun _ : Fin 1 => (0 : ℝ), fun _ => 1, fun _ => 2})
    (fun _ => 0) (fun _ => 1) := by
  intro h
  have hh := (h (fun _ => 2) (by simp) 0).1 (by norm_num)
  norm_num at hh

-- Two different endpoint roots may agree in one coordinate.
example : EndpointMidpoint.Matches
    ({fun _ : Fin 2 => (0 : ℝ), fun i => if i = 0 then 0 else 2})
    (fun _ => 0) (fun i => if i = 0 then 0 else 1 / 4) := by
  intro y hy i
  rcases hy with (rfl | hy)
  · simp
  · have he : y = (fun i => if i = 0 then 0 else 2) := hy
    subst y
    by_cases hi : i = 0
    all_goals norm_num [hi]

-- Identically zero algebraic value tests retain a nonzero trailing factor.
example (s t : ℝ) : ((0 : ℝ) < 0 ↔ (0 : ℝ) < 0) ∧ (0 < (0 : ℝ) ↔ 0 < (0 : ℝ)) := by
  exact AlgebraicBranchSign.sign_iff Polynomial.X (fun _ : ℝ => 0) (fun _ => 0)
    continuous_const continuous_const (by intro x; simp)
    (by intro x; simp [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_X]) s t

-- A convergent branch identifies the correct endpoint without nearby digits.
example : ∀ᶠ t : ℝ in 𝓝 0, ∀ x ∈ ({fun _ : Fin 1 => (0 : ℝ), fun _ => 2} : Set (Fin 1 → ℝ)),
    EndpointMidpoint.Matches ({fun _ : Fin 1 => (0 : ℝ), fun _ => 2}) x (fun _ => t ^ 2) ↔
      x = (fun _ => 0) := by
  apply EndpointMidpoint.eventually_matches_iff (by simp) (by simp)
  simpa using ((continuous_pi (fun _ : Fin 1 => continuous_id.pow 2)).tendsto (0 : ℝ))

private noncomputable def repeated : Polynomial (Polynomial ℤ) :=
  (Polynomial.X * (Polynomial.X - Polynomial.C 1)) ^ 2

private lemma repeated_ne_zero : repeated ≠ 0 :=
  ((Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1)).pow 2).ne_zero

private lemma avoid_repeated (t : ℝ) : SymbolicScaledSquarefree.scalarEvaluation t
    (SymbolicScaledSquarefree.exceptional repeated) ≠ 0 := by
  have he : repeated = ((Polynomial.X * (Polynomial.X - Polynomial.C 1) : Polynomial ℤ) ^ 2).map Polynomial.C := by
    simp [repeated]
  have hd : (SymbolicScaledSquarefree.exceptional repeated).natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    have h := SymbolicScaledSquarefree.exceptional_degree repeated 0 (fun k => by
      rw [he, Polynomial.coeff_map]
      simp)
    simpa only [Nat.mul_zero] using h
  have hn := SymbolicScaledSquarefree.exceptional_ne_zero repeated repeated_ne_zero
  have hc := Polynomial.eq_C_of_natDegree_eq_zero hd
  rw [hc] at hn ⊢
  simpa [SymbolicScaledSquarefree.scalarEvaluation] using
    (Int.cast_ne_zero.mpr (Polynomial.C_ne_zero.mp hn) :
      ((SymbolicScaledSquarefree.exceptional repeated).coeff 0 : ℝ) ≠ 0)

-- Scalar covering and persistent order use the constructed exceptional factor,
-- even though both original roots are repeated at every parameter.
example (a b : ℝ) : IsCoveringMap (RootBranches.projection
    (SymbolicUnivariateRootFamily.value (SymbolicScaledSquarefree.polynomial repeated)) a b) :=
  SymbolicRootCurveOrder.covering repeated a b (fun t _ => avoid_repeated t)

example (t : ℝ) : ScalarRootTransport.rank repeated t 0 < ScalarRootTransport.rank repeated t 1 := by
  apply ScalarRootTransport.rank_lt_rank repeated t 0 1 (avoid_repeated t)
  · rw [repeated, Polynomial.eval₂_pow, Polynomial.eval₂_mul, Polynomial.eval₂_X]
    simp
  · norm_num

-- The tuple of distinct-root ordinals is constant along a grid branch.
example {a b : ℝ} (f : C(Ioo a b, Fin 2 → ℝ))
    (hf : ∀ u i, repeated.eval₂ (SymbolicScaledSquarefree.scalarEvaluation u.val) (f u i) = 0)
    (s t : Ioo a b) :
    LeanCanny.Encoding.CoordinateBranchOrdinals.word 2 (fun _ => repeated) s.val (f s) =
      LeanCanny.Encoding.CoordinateBranchOrdinals.word 2 (fun _ => repeated) t.val (f t) :=
  LeanCanny.Encoding.CoordinateBranchOrdinals.word_eq 2 (fun _ => repeated)
    (fun u _ _ => avoid_repeated u) f hf s t

-- Empty grids have one zero-length record even when a positive width is allowed.
example (W : ℕ) (p : Fin 0 → Polynomial (Polynomial ℤ)) (t : ℝ) (x : Fin 0 → ℝ) :
    LeanCanny.Encoding.CoordinateBranchOrdinals.word W p t x = [] := by
  apply List.length_eq_zero_iff.mp
  exact (LeanCanny.Encoding.CoordinateBranchOrdinals.length_word W p t x).trans (Nat.zero_mul W)

private noncomputable def collision : Polynomial (Polynomial ℤ) :=
  (Polynomial.X ^ 2 - Polynomial.C Polynomial.X) * (Polynomial.X - Polynomial.C 1)

private lemma collision_specialized : collision.map (SymbolicScaledSquarefree.scalarEvaluation 0) =
    (Polynomial.X : Polynomial ℝ) ^ 2 * (Polynomial.X - Polynomial.C 1) := by
  simp [collision, SymbolicScaledSquarefree.scalarEvaluation]

private lemma collision_specialized_ne_zero : collision.map (SymbolicScaledSquarefree.scalarEvaluation 0) ≠ 0 := by
  rw [collision_specialized]
  exact ((Polynomial.monic_X.pow 2).mul (Polynomial.monic_X_sub_C 1)).ne_zero

-- At the collision parameter, the repeated root zero is singular. Distinct
-- root ordinals still distinguish zero from one without exception avoidance.
example : (collision.map (SymbolicScaledSquarefree.scalarEvaluation 0)).derivative.eval 0 = 0 := by
  rw [collision_specialized]
  simp

example : ScalarRootTransport.rank collision 0 0 < ScalarRootTransport.rank collision 0 1 := by
  apply ScalarRootTransport.rank_lt_rank_of_ne_zero collision 0 0 1 collision_specialized_ne_zero
  · simp [collision, SymbolicScaledSquarefree.scalarEvaluation]
  · norm_num

private noncomputable def squareRows (i : Fin 1) : MvPolynomial (Fin 1) ℤ := MvPolynomial.X i ^ 2

private lemma squareRows_noInfinity : AffineFiniteCoordinates.NoInfinity squareRows (fun _ => 2) := by
  intro y hy hz
  funext j
  cases j with
  | none => exact hy
  | some i =>
    have H := hz i
    rw [squareRows, WeightedHomogenization.homogenize_X_pow, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X] at H
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp H

-- Both the retained height and the original affine root may be repeated.
-- The frozen construction still excludes roots at infinity.
example : AffineFiniteCoordinates.NoInfinity
    (FrozenAffineCopies.system squareRows (Polynomial.X ^ 2) 0 (fun k : Fin 3 => decide (k.val ≠ 0)))
    (FrozenAffineCopies.degrees (fun _ : Fin 1 => 2) 2) := by
  have H := FrozenAffineCopies.noInfinity squareRows (Polynomial.X ^ 2) 0
    (fun k : Fin 3 => decide (k.val ≠ 0)) (fun _ => 2)
    (by simp : 0 < (Polynomial.X ^ 2 : Polynomial ℤ).natDegree) squareRows_noInfinity
  simpa only [Polynomial.natDegree_X_pow] using H

end EndpointMidpointRegression
