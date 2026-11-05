import LeanCanny.Geometry.EffectivePolynomialBallConnections

open LeanCanny LeanCanny.Algebra LeanCanny.Geometry MvPolynomial Set
open scoped BigOperators
open EffectivePolynomialBallConnections

example {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D H R : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^H)
    (hR : ParameterizedBoundaryRadiusHead.radiusExponent n D H ≤ R)
    (x y : Fin n → ℝ) (hx : x ∈ BoundedZeroSource.Bounded q R) (hy : y ∈ BoundedZeroSource.Bounded q R) :
    JoinedIn (BoundedZeroSource.Original q) x y ↔ JoinedIn (BoundedZeroSource.Bounded q R) x y :=
  joined_iff_after_cutoff q D H R hD hq hR x y hx hy

example {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D H R : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^H)
    (hR : ParameterizedBoundaryRadiusHead.radiusExponent n D H ≤ R)
    (x y : Fin n → ℝ) (hx : x ∈ BoundedZeroSource.Bounded q R) (hy : y ∈ BoundedZeroSource.Bounded q R) :
    y ∈ connectedComponentIn (BoundedZeroSource.Original q) x ↔
      y ∈ connectedComponentIn (BoundedZeroSource.Bounded q R) x :=
  component_iff_after_cutoff q D H R hD hq hR x y hx hy

example {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D H R T : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^H)
    (hR : ParameterizedBoundaryRadiusHead.radiusExponent n D H ≤ R)
    (hT : ParameterizedBoundaryRadiusHead.radiusExponent n D H ≤ T)
    (x y : Fin n → ℝ) (hxR : x ∈ BoundedZeroSource.Bounded q R) (hyR : y ∈ BoundedZeroSource.Bounded q R)
    (hxT : x ∈ BoundedZeroSource.Bounded q T) (hyT : y ∈ BoundedZeroSource.Bounded q T) :
    y ∈ connectedComponentIn (BoundedZeroSource.Bounded q R) x ↔
      y ∈ connectedComponentIn (BoundedZeroSource.Bounded q T) x :=
  (component_iff_after_cutoff q D H R hD hq hR x y hxR hyR).symm.trans
    (component_iff_after_cutoff q D H T hD hq hT x y hxT hyT)

example {N D H : List Bool → ℕ} (hN : UnaryFn N) (hD : BinaryFn D) (hH : BinaryFn H) :
    BinaryFn (fun u => ParameterizedBoundaryRadiusHead.radiusExponent (N u) (D u) (H u)) :=
  ParameterizedBoundaryRadiusBudget.radiusExponent_binary hN hD hH

example (R : ℕ) (hR : ParameterizedBoundaryRadiusHead.radiusExponent 2 2 0 ≤ R)
    (x y : Fin 2 → ℝ)
    (hx : x ∈ BoundedZeroSource.Bounded ((X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ)^2) R)
    (hy : y ∈ BoundedZeroSource.Bounded ((X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ)^2) R) :
    JoinedIn (BoundedZeroSource.Original ((X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ)^2)) x y ↔
      JoinedIn (BoundedZeroSource.Bounded ((X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ)^2) R) x y := by
  apply joined_iff_after_cutoff _ 2 0 R (by simp) ?_ hR x y hx hy
  simpa only [MvMass.X,one_pow,pow_zero] using
    MvMass.pow_le (X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) 2

#print axioms EffectivePolynomialBallConnections.zero_component_transport
#print axioms EffectivePolynomialBallConnections.zero_window
#print axioms EffectivePolynomialBallConnections.joined_iff_section
#print axioms EffectivePolynomialBallConnections.joined_iff_bounded
#print axioms EffectivePolynomialBallConnections.joined_iff_after_cutoff
#print axioms EffectivePolynomialBallConnections.component_iff_after_cutoff
