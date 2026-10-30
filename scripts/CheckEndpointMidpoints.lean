import LeanCanny.Connectivity.FiniteFiberMidpoint
import LeanCanny.Geometry.SymbolicRootCurveOrder
import LeanCanny.Encoding.CoordinateBranchOrdinals
import LeanCanny.Geometry.FrozenAffineBranches
import LeanCanny.Geometry.OrderedRealCellNeighborhood
import LeanCanny.Geometry.OrderedRealCellDerivativeSample
import LeanCanny.Encoding.IntegerPolynomialSampleInput
import LeanCanny.Encoding.IntegerPolynomialAdjacentSamplesComplete
import LeanCanny.Algebra.FrozenRetainedMidpointSpace
import LeanCanny.Encoding.SquareSampleCompletePrefixEquality
import LeanCanny.Encoding.SquareSampleScalarCoordinateEquality
import LeanCanny.Encoding.SquareSampleCompleteCoordinateOrder
import LeanCanny.Geometry.AlgebraicFiberImageRank

/-! Finite endpoint selection, tied coordinates, and zero midpoint tests.
Run with `lake env lean -DwarningAsError=true scripts/CheckEndpointMidpoints.lean`.
-/

open LeanCanny.Geometry LeanCanny.Connectivity Set Filter
open scoped Topology

namespace EndpointMidpointRegression
open LeanCanny.Algebra
open scoped Classical

-- Adjacent gaps approach every retained root, including either extreme.
example (s : Finset ℝ) (i : Fin s.card) (b : ℝ) (hb : OrderedRealCells.root s i < b) :
    ∃ t ∈ OrderedRealCells.gap s (OrderedRealCells.rightGap s i), t < b :=
  OrderedRealCells.exists_rightGap_before s i hb

example (s : Finset ℝ) (i : Fin s.card) (a : ℝ) (ha : a < OrderedRealCells.root s i) :
    ∃ t ∈ OrderedRealCells.gap s (OrderedRealCells.leftGap s i), a < t :=
  OrderedRealCells.exists_leftGap_after s i ha

-- Repeated roots still admit algebraic samples between consecutive roots.
example (p : Polynomial ℝ) (s : Finset ℝ) (hs : ∀ t ∈ s, p.eval t = 0)
    (k : Fin (s.card + 1)) (h0 : 0 < k.val) (hk : k.val < s.card) :
    ∃ t ∈ OrderedRealCells.gap s k, p.derivative.eval t = 0 :=
  OrderedRealCells.exists_derivative_in_gap p s hs k h0 hk

private noncomputable def singularSource : IntegerPolynomialRootQueriesBits.Source where
  polynomial _ := Polynomial.X ^ 2
  degree _ := 2
  mass _ := 0
  degree_bound _ := by simp
  mass_bound _ := by simp

-- A root rejected by a regular-root sampler has a complete vertex label.
example : ∃ w, ∃ hw : LeanCanny.Encoding.SquareSampleCompleteVertices.Valid
    (LeanCanny.Encoding.IntegerPolynomialSampleInput.input singularSource) [] w,
    (LeanCanny.Encoding.SquareSampleCompleteVertices.candidate
      (LeanCanny.Encoding.IntegerPolynomialSampleInput.input singularSource) [] w hw).val (0 : Fin 1) = 0 :=
  LeanCanny.Encoding.IntegerPolynomialSampleInput.root_complete singularSource []
    (by change (Polynomial.X ^ 2 : Polynomial ℤ) ≠ 0; exact pow_ne_zero _ Polynomial.X_ne_zero) 0 (by simp [singularSource])

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

-- Retaining a second repeated height preserves finiteness without a
-- Jacobian promise on any of the three spatial copies.
example : AffineFiniteCoordinates.NoInfinity
    (FrozenAffineCopies.system
      (FrozenAffineCopies.system squareRows (Polynomial.X ^ 2) 0 (fun k : Fin 3 => decide (k.val ≠ 0)))
      (Polynomial.X ^ 2) (FrozenAffineCopies.block (0 : Fin 3) (0 : Fin 1)) (fun _ : Fin 1 => true))
    (FrozenAffineCopies.degrees (FrozenAffineCopies.degrees (fun _ : Fin 1 => 2) 2) 2) := by
  have inner := FrozenAffineCopies.noInfinity squareRows (Polynomial.X ^ 2) 0
    (fun k : Fin 3 => decide (k.val ≠ 0)) (fun _ => 2)
    (by simp : 0 < (Polynomial.X ^ 2 : Polynomial ℤ).natDegree) squareRows_noInfinity
  have outer := FrozenAffineCopies.noInfinity _ (Polynomial.X ^ 2)
    (FrozenAffineCopies.block (0 : Fin 3) (0 : Fin 1)) (fun _ : Fin 1 => true) _
    (by simp : 0 < (Polynomial.X ^ 2 : Polynomial ℤ).natDegree) inner
  simpa only [Polynomial.natDegree_X_pow] using outer

-- Tied midpoint coordinates remain exactly zero after both embeddings.
example : (FrozenRetainedMidpointBits.polynomial (0 : Fin 1)).eval₂ (Int.castRingHom ℝ)
    (FrozenAffineCopies.point 7 (fun _ : Fin 1 =>
      FrozenAffineCopies.point 3 ![fun _ => (1 : ℝ), fun _ => 0, fun _ => 2])) = 0 := by
  rw [FrozenRetainedMidpointBits.polynomial, MvPolynomial.eval₂_rename]
  have he : (FrozenAffineCopies.point 7 (fun _ : Fin 1 =>
      FrozenAffineCopies.point 3 ![fun _ => (1 : ℝ), fun _ => 0, fun _ => 2])) ∘
        FrozenAffineCopies.block (0 : Fin 1) =
      FrozenAffineCopies.point 3 ![fun _ : Fin 1 => (1 : ℝ), fun _ => 0, fun _ => 2] := by
    funext j
    exact FrozenAffineCopies.point_block _ _ _ j
  rw [he, FrozenAffineCopies.midpoint_eval]
  norm_num [FrozenAffineCopies.point_block, Matrix.vecHead, Matrix.vecTail]

end EndpointMidpointRegression

namespace NativeAdjacentSampleRegression
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding
set_option backward.isDefEq.respectTransparency false

private noncomputable def zeroSource : IntegerPolynomialRootQueriesBits.Source where
  polynomial _ := Polynomial.X ^ 2
  degree _ := 2
  mass _ := 0
  degree_bound _ := by simp
  mass_bound _ := by simp

private noncomputable def oneSource : IntegerPolynomialRootQueriesBits.Source where
  polynomial _ := Polynomial.X - Polynomial.C 1
  degree _ := 1
  mass _ := 2
  degree_bound _ := (Polynomial.natDegree_sub_le _ _).trans (by simp)
  mass_bound _ := by
    apply (coefficientMass_sub_le _ _).trans
    have hx : coefficientMass (Polynomial.X : Polynomial ℤ) = 1 := by
      simpa only [pow_one] using coefficientMass_X_pow 1
    simp only [hx, coefficientMass_C, Int.natAbs_one]
    decide

-- A singular endpoint zero and an algebraic sample one have native adjacent labels.
example : ∃ w v, pair (pair [] w) v ∈ IntegerPolynomialAdjacentSamples.language zeroSource oneSource zeroSource true := by
  have hz : zeroSource.polynomial [] ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  obtain ⟨w, hw, he⟩ := IntegerPolynomialSampleInput.root_complete zeroSource [] hz 0 (by simp [zeroSource])
  have hR : IntegerPolynomialRootQueriesBits.rootSet zeroSource [] = {0} := by
    simp [IntegerPolynomialRootQueriesBits.rootSet, zeroSource]
  obtain ⟨i, hi⟩ := Geometry.OrderedRealCells.exists_root (IntegerPolynomialRootQueriesBits.rootSet zeroSource []) 0 (by rw [hR]; simp)
  have hgap : (1 : ℝ) ∈ Geometry.OrderedRealCells.gap (IntegerPolynomialRootQueriesBits.rootSet zeroSource [])
      (Geometry.OrderedRealCells.rightGap _ i) := by
    rw [Geometry.OrderedRealCells.mem_rightGap_iff_rank, hi, hR]
    norm_num [Geometry.OrderedRealCells.lowerCount, Finset.filter_singleton]
  obtain ⟨v, hv⟩ := IntegerPolynomialAdjacentSamples.sample_label_complete zeroSource oneSource zeroSource true [] w hw i
    (hi.trans he.symm) 1 (by exact (Polynomial.monic_X_sub_C (1 : ℤ)).ne_zero) (by simp [oneSource]) hgap
  exact ⟨w, v, hv⟩

end NativeAdjacentSampleRegression

namespace NativeCoordinateEqualityRegression
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding
set_option backward.isDefEq.respectTransparency false

private noncomputable def source : IntegerPolynomialRootQueriesBits.Source where
  polynomial _ := (Polynomial.X * (Polynomial.X - Polynomial.C 1)) ^ 2
  degree _ := 4
  mass _ := 4
  degree_bound _ := by
    apply Polynomial.natDegree_pow_le.trans
    apply (Nat.mul_le_mul_left 2 (Polynomial.natDegree_mul_le)).trans
    simp only [Polynomial.natDegree_X, Polynomial.natDegree_X_sub_C]
    decide
  mass_bound _ := by
    have hx : coefficientMass (Polynomial.X : Polynomial ℤ) = 1 := by
      simpa only [pow_one] using coefficientMass_X_pow 1
    have hs : coefficientMass (Polynomial.X - Polynomial.C 1 : Polynomial ℤ) ≤ 2 := by
      simpa only [hx, coefficientMass_C, Int.natAbs_one] using
        coefficientMass_sub_le (Polynomial.X : Polynomial ℤ) (Polynomial.C 1)
    have hm : coefficientMass (Polynomial.X * (Polynomial.X - Polynomial.C 1) : Polynomial ℤ) ≤ 2 :=
      (coefficientMass_mul_le _ _).trans (by simpa only [hx, one_mul] using hs)
    exact (coefficientMass_pow_le _ _).trans ((Nat.pow_le_pow_left hm _).trans (by decide))

-- Both coordinate values are repeated roots. Thom scans still reject
-- their equality; an empty fixed prefix permits both complete labels.
example : ∃ w v,
    pair (pair [] (pair w v)) (BinaryNatCode.encode 0) ∉
      SquareSampleCompleteCoordinateEquality.language (IntegerPolynomialSampleInput.input source) ∧
    pair [] (pair w v) ∈ SquareSampleCompletePrefixEquality.language (IntegerPolynomialSampleInput.input source) (fun _ => 0) ∧
    pair (pair [] w) v ∉ SquareSampleScalarCoordinateEquality.language (IntegerPolynomialSampleInput.input source)
      source id (fun _ => (0 : Fin 1)) ∧
    SquareSampleCompleteCoordinateOrder.value (IntegerPolynomialSampleInput.input source)
      (pair (pair [] (pair w v)) (BinaryNatCode.encode 0)) = [true] := by
  have hn : source.polynomial [] ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero Polynomial.X_ne_zero (Polynomial.monic_X_sub_C (1 : ℤ)).ne_zero)
  obtain ⟨w, hw, hew⟩ := IntegerPolynomialSampleInput.root_complete source [] hn 0 (by
    change (((Polynomial.X * (Polynomial.X - Polynomial.C 1)) ^ 2 : Polynomial ℤ).eval₂ (Int.castRingHom ℝ) (0 : ℝ)) = 0
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_mul, Polynomial.eval₂_X, zero_mul]
    norm_num)
  obtain ⟨v, hv, hev⟩ := IntegerPolynomialSampleInput.root_complete source [] hn 1 (by
    change (((Polynomial.X * (Polynomial.X - Polynomial.C 1)) ^ 2 : Polynomial ℤ).eval₂ (Int.castRingHom ℝ) (1 : ℝ)) = 0
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
    norm_num)
  refine ⟨w, v, ?_, ?_, ?_, ?_⟩
  · intro h
    have H := SquareSampleCompleteCoordinateEquality.packet _ (IntegerPolynomialSampleInput.complete source) [] w v hw hv (0 : Fin 1)
    have h0 : (0 : Fin 1).val = 0 := rfl
    rw [h0] at H
    have heq := H.mp h
    rw [hew, hev] at heq
    norm_num at heq
  · apply (SquareSampleCompletePrefixEquality.packet _ (IntegerPolynomialSampleInput.complete source) (fun _ => 0)
      [] w v hw hv (by decide)).mpr
    intro i hi
    exact (Nat.not_lt_zero i.val hi).elim
  · intro h
    have hr := (IntegerPolynomialSampleInput.roots_iff source [] hn _).mp
      (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input source) [] w hw).property
    have H := SquareSampleScalarCoordinateEquality.packet (IntegerPolynomialSampleInput.input source) source id
      (fun _ => (0 : Fin 1)) [] w v hw hv hn hr
    have h01 : (0 : ℝ) = 1 := hew.symm.trans ((H.mp h).trans hev)
    exact zero_ne_one h01
  · have H := SquareSampleCompleteCoordinateOrder.packet (IntegerPolynomialSampleInput.input source)
      (IntegerPolynomialSampleInput.complete source) [] w v hw hv (0 : Fin 1)
    have h0 : (0 : Fin 1).val = 0 := rfl
    rw [h0] at H
    rw [H, hew, hev]
    norm_num

-- Repeated coordinate values contribute only one rank step.
example : Geometry.FiniteImageRank.rank ({0, 1, 2} : Finset ℕ)
    (fun k => if k < 2 then (0 : ℝ) else 2) 2 = 1 := by
  rw [Geometry.FiniteImageRank.rank_eq]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

end NativeCoordinateEqualityRegression
