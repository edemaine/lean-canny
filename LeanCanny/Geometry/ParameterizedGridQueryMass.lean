/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.ParameterizedGridQuerySign
public import LeanCanny.Geometry.ParameterizedRootQueryCutMass
public import LeanCanny.Algebra.ProjectiveValueGram
public import LeanCanny.Algebra.IntegralParameterInverseAtInfinity
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Derived mass and sign cutoffs for actual Cartesian-grid queries

The mass estimate consumes coordinate-head and query coefficients. The actual
reciprocal Gram annihilator and its sign-preserving cut family are bounded
internally. The logarithmic mass budget is affine in the input height.
-/

@[expose] public section
namespace LeanCanny.Geometry.ParameterizedGridQuerySign
open Polynomial LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

private theorem homogenized_mass (q : MvPolynomial (Fin n) ℤ[X]) (e H : ℕ)
    (hq : ∀ v, coefficientMass (q.coeff v) ≤ 2 ^ H) (v : Fin (n + 1) →₀ ℕ) :
    coefficientMass ((RelativeAffineGridValueGram.test q e).coeff v) ≤ 2 ^ H := by
  by_cases hz : (RelativeAffineGridValueGram.test q e).coeff v = 0
  · simp only [hz, coefficientMass_zero, Nat.zero_le]
  · obtain ⟨w, hw, _⟩ := MvPolynomial.coeff_rename_ne_zero (AffineFiniteCoordinates.layout n) _ v hz
    rw [← hw, RelativeAffineGridValueGram.test,
      MvPolynomial.coeff_rename_mapDomain _ (AffineFiniteCoordinates.layout n).injective,
      WeightedHomogenization.coefficient]
    split_ifs
    · exact hq _
    · simp

def massBudget (n W H : ℕ) :=
  let L := FixedWidthPolynomial.count (n + 1) W
  L * (2 * H + 2 + (n + 2).size + 2 * L.size)

theorem massBudget_affine (n W H : ℕ) :
    massBudget n W H = 2 * FixedWidthPolynomial.count (n + 1) W * H + massBudget n W 0 := by
  unfold massBudget
  ring

theorem massBudget_binary {n W H : List Bool → ℕ}
    (hn : UnaryFn n) (hW : UnaryFn W) (hH : BinaryFn H) :
    BinaryFn (fun q => massBudget (n q) (W q) (H q)) := by
  have hL := ((BinaryFn.const 2).powUnary hW).powUnary (hn.add (UnaryFn.const 1))
  exact hL.mul (((((BinaryFn.const 2).mul hH).add (BinaryFn.const 2)).add
    (((BinaryFn.ofUnary hn).add (BinaryFn.const 2)).size)).add ((BinaryFn.const 2).mul hL.size))

theorem annihilator_mass (p : Fin n → (ℤ[X])[X]) (q : MvPolynomial (Fin n) ℤ[X]) (H : ℕ)
    (hp : ∀ i k, coefficientMass ((p i).coeff k) ≤ 2 ^ H)
    (hq : ∀ v, coefficientMass (q.coeff v) ≤ 2 ^ H) :
    NestedMass.mass (annihilator p q) ≤ 2 ^ massBudget n
      (RelativeAffineGridValueGram.width (fun i => (p i).natDegree) (q.totalDegree + 1)) H := by
  let d := fun i => (p i).natDegree
  let e := q.totalDegree + 1
  let W := RelativeAffineGridValueGram.width d e
  let L := FixedWidthPolynomial.count (n + 1) W
  have hRows (i : Fin n) (v : Fin (n + 1) →₀ ℕ) :
      coefficientMass ((AffineRingCoordinates.homogeneousRows (RelativeAffineGridValueGram.rows p) d i).coeff v) ≤ 2 ^ H := by
    change coefficientMass ((RelativeAffineGridValueGram.test (RelativeAffineGridValueGram.rows p i) (d i)).coeff v) ≤ _
    apply homogenized_mass _ _ H _ v
    intro w
    rw [RelativeAffineGridValueGram.rows, DiagonalParameterBits.coefficient]
    split_ifs
    · exact hp i _
    · simp
  have hm : NestedMass.mass (annihilator p q) ≤
      L.factorial * ((n + 2) * L * (2 ^ H + 1) ^ 2) ^ L := by
    change NestedMass.mass (ProjectiveValueGram.annihilator
      (AffineRingCoordinates.homogeneousRows (RelativeAffineGridValueGram.rows p) d)
      (RelativeAffineGridValueGram.test q e) d e W) ≤ _
    exact ProjectiveValueGram.annihilator_mass_le _ _ d e W (2 ^ H) hRows (homogenized_mass q e H hq)
  have hf : L.factorial ≤ 2 ^ (L.size * L) :=
    (Nat.factorial_le_pow _).trans
      ((Nat.pow_le_pow_left (Nat.lt_size_self _).le _).trans_eq (pow_mul _ _ _).symm)
  have htwo : 2 ^ H + 1 ≤ 2 ^ (H + 1) := by
    rw [pow_succ]
    have h := Nat.one_le_two_pow (n := H)
    omega
  have ht : (n + 2) * L * (2 ^ H + 1) ^ 2 ≤
      2 ^ ((n + 2).size + L.size + 2 * (H + 1)) := by
    calc
      _ ≤ 2 ^ (n + 2).size * 2 ^ L.size * (2 ^ (H + 1)) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.lt_size_self _).le (Nat.lt_size_self _).le)
          (Nat.pow_le_pow_left htwo _)
      _ = _ := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
  calc
    _ ≤ L.factorial * ((n + 2) * L * (2 ^ H + 1) ^ 2) ^ L := hm
    _ ≤ 2 ^ (L.size * L) * (2 ^ ((n + 2).size + L.size + 2 * (H + 1))) ^ L :=
      Nat.mul_le_mul hf (Nat.pow_le_pow_left ht _)
    _ = _ := by
      rw [← pow_mul, ← pow_add]
      congr 1
      change _ = L * (2 * H + 2 + (n + 2).size + 2 * L.size)
      ring

theorem annihilator_ne_zero_of_mass (p : Fin n → (ℤ[X])[X]) (q : MvPolynomial (Fin n) ℤ[X])
    (hpos : ∀ i, 0 < (p i).natDegree) (H : ℕ)
    (hp : ∀ i k, coefficientMass ((p i).coeff k) ≤ 2 ^ H) : annihilator p q ≠ 0 := by
  have h := RelativeAffineGridValueGram.selected_ne_zero p q (fun i => (p i).natDegree)
    (q.totalDegree + 1) (fun _ => rfl) hpos (Nat.succ_pos _) (Int.castRingHom ℝ)
    ((2 : ℝ) ^ (H + 1)) (fun i => ?_)
  · intro hz
    apply h
    change (annihilator p q).map _ = 0
    rw [hz, Polynomial.map_zero]
  · have hn : p i ≠ 0 := by
      intro hz
      have hi := hpos i
      rw [hz, Polynomial.natDegree_zero] at hi
      omega
    have hs := IntegralParameterInverseAtInfinity.nonzero_after_mass (p i).leadingCoeff
      (Polynomial.leadingCoeff_ne_zero.mpr hn) H (hp i (p i).natDegree)
      ((2 : ℝ) ^ (H + 1)) le_rfl
    change ((IntegralParameterInverseAtInfinity.parameterEval ((2 : ℝ) ^ (H + 1)))
      (p i).leadingCoeff : ℂ) ≠ 0
    exact Complex.ofReal_ne_zero.mpr hs

def cutoffBudget (n W H : ℕ) :=
  ParameterizedRootQuerySign.cutMassBound (RelativeProjectiveValueGram.dimension n W + 1)
    (massBudget n W H) + 1

theorem cutoffBudget_binary {n W H : List Bool → ℕ}
    (hn : UnaryFn n) (hW : UnaryFn W) (hH : BinaryFn H) :
    BinaryFn (fun q => cutoffBudget (n q) (W q) (H q)) := by
  have hL := ((BinaryFn.const 2).powUnary hW).powUnary (hn.add (UnaryFn.const 1))
  have hd := (((BinaryFn.ofUnary hn).add (BinaryFn.const 3)).mul hL).add (BinaryFn.const 1)
  exact (ParameterizedRootQuerySign.cutMassBound_binary hd (massBudget_binary hn hW hH)).add (BinaryFn.const 1)

theorem sign_after_input_bounds {a b : ℝ} (p : Fin n → (ℤ[X])[X]) (q : MvPolynomial (Fin n) ℤ[X])
    (hpos : ∀ i, 0 < (p i).natDegree) (H : ℕ)
    (hp : ∀ i k, coefficientMass ((p i).coeff k) ≤ 2 ^ H)
    (hq : ∀ v, coefficientMass (q.coeff v) ≤ 2 ^ H)
    (ha : (2 : ℝ) ^ cutoffBudget n
      (RelativeAffineGridValueGram.width (fun i => (p i).natDegree) (q.totalDegree + 1)) H ≤ a)
    (x : C(Set.Ioo a b, Fin n → ℝ))
    (hx : ∀ t i, (p i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation t.val) (x t i) = 0)
    (s t : Set.Ioo a b) :
    SignType.sign (q.eval₂ (SymbolicScaledSquarefree.scalarEvaluation s.val) (x s)) =
      SignType.sign (q.eval₂ (SymbolicScaledSquarefree.scalarEvaluation t.val) (x t)) := by
  apply sign_transport p q _ x hx s t
  apply ParameterizedRootQuerySign.avoids_after_input_bounds (annihilator p q)
    (annihilator_ne_zero_of_mass p q hpos H hp) (fun _ : Unit => Polynomial.X)
    (RelativeProjectiveValueGram.dimension n
      (RelativeAffineGridValueGram.width (fun i => (p i).natDegree) (q.totalDegree + 1)) + 1) _
  · exact RelativeAffineGridValueGram.degree_le p q _ _
  · intro j
    rw [Polynomial.natDegree_X]
    omega
  · intro k
    exact (NestedMass.coeff_le _ k).trans (annihilator_mass p q H hp hq)
  · intro j k
    simp only [Polynomial.coeff_X]
    split_ifs
    · change coefficientMass (Polynomial.C (1 : ℤ)) ≤ _
      rw [coefficientMass_C, Int.natAbs_one]
      exact Nat.one_le_two_pow
    · simp
  · exact ha

end LeanCanny.Geometry.ParameterizedGridQuerySign
