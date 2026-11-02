/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralEquationReadback
public import LeanCanny.Algebra.PaddedIntegralHeightBounds
public import LeanCanny.Algebra.CoordinatePowerCoefficients
public import LeanCanny.Algebra.MonicParameterRows

/-! # Derived mass bounds for actual monic sampler rows

A companion entry bound controls the coefficient mass of each canonical old
basis representative. Coordinate powers and variable renaming preserve this
bound, so no expanded polynomial or row-mass oracle is required.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralParameterExtension
open IntegralCoordinateBasis FixedWidthPolynomial MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] [Nontrivial A] {m B : ℕ}

omit [Nontrivial A] in
theorem representative_mass (b : IntegralCoordinateBasis A m (2 ^ B)) (a : A) (H : ℕ)
    (ha : ∀ r : Fin (count m B), (Algebra.leftMulMatrix b.finBasis a r (zeroFin m B)).natAbs ≤ 2 ^ H) :
    MvMass.mass (b.representative a) ≤ count m B * 2 ^ H := by
  rw [representative]
  apply (MvMass.sum_le _ _).trans
  simp only [MvMass.monomial]
  calc
    _ ≤ ∑ _e : Fin m → Fin (2 ^ B), 2 ^ H := by
      apply Finset.sum_le_sum
      intro e _
      have HE := coefficient_finMatrix b a (boxEquiv m B e)
      have HV : vector m B (boxEquiv m B e) = exponent e := by
        change exponent ((boxEquiv m B).symm (boxEquiv m B e)) = exponent e
        rw [Equiv.symm_apply_apply]
      rw [HV, representative_coefficient] at HE
      rw [HE]
      exact ha _
    _ = _ := by simp [count]

theorem equation_lower_mass (b : IntegralCoordinateBasis A m (2 ^ B))
    (p : Polynomial A) (d H k : ℕ) (hk : k < 2 ^ B)
    (hM : ∀ r s, (Algebra.leftMulMatrix (coordinateBasis b p d).finBasis
      (AdjoinRoot.root _) r s).natAbs ≤ 2 ^ H) :
    MvMass.mass ((equation b p d).coeff k) ≤ count m B * 2 ^ H := by
  rw [equation, polynomial_coefficient]
  apply representative_mass
  intro r
  have HE := equation_coefficient_companion b p d r ⟨k,hk⟩
  rw [equation, polynomial_coefficient, coefficient_finMatrix] at HE
  rw [HE, Int.natAbs_neg]
  exact hM _ _

theorem monic_row_mass {ι : Type*} [Fintype ι]
    (p : Polynomial (MvPolynomial ι ℤ)) (N R H : ℕ) (hp : p.Monic)
    (hd : p.natDegree = N) (w : ι → ℕ) (W : ℕ)
    (hM : ∀ k < N, MvMass.mass (p.coeff k) ≤ R * 2 ^ H) :
    MvMass.mass (MonicParameterRows.row p N w W) ≤ 1 + N * R * 2 ^ H := by
  have HT : p.coeff N = 1 := by
    calc
      p.coeff N = p.coeff p.natDegree := congrArg (fun k => p.coeff k) hd.symm
      _ = 1 := by rw [Polynomial.coeff_natDegree,hp.leadingCoeff]
  unfold MonicParameterRows.row MonicParameterRows.lower
  apply (MvMass.add_le _ _).trans
  have HX : MvMass.mass ((X (Sum.inr ()) : MvPolynomial (ι ⊕ Unit) ℤ) ^ (N*W)) ≤ 1 := by
    simpa only [MvMass.X,one_pow] using MvMass.pow_le (X (Sum.inr ()) : MvPolynomial (ι ⊕ Unit) ℤ) (N*W)
  apply (Nat.add_le_add HX (MvMass.sum_le _ _)).trans
  have HL : ∀ k∈Finset.range N,
      MvMass.mass (rename Sum.inl (CoordinatePowerSubstitution.substitute w
        (MonicParameterRows.coefficient p N k)) * X (Sum.inr ()) ^ (k*W)) ≤ R*2^H := by
    intro k hk
    apply (MvMass.mul_le _ _).trans
    have HC : MonicParameterRows.coefficient p N k = p.coeff k := by
      simp only [MonicParameterRows.coefficient,HT,one_pow,mul_one]
    have HR : MvMass.mass (rename Sum.inl (CoordinatePowerSubstitution.substitute w
        (MonicParameterRows.coefficient p N k))) ≤ R*2^H :=
      (MvMass.rename_le (Sum.inl : ι → ι ⊕ Unit) _).trans
        ((CoordinatePowerSubstitution.mass_le w _).trans (by rw [HC]; exact hM k (Finset.mem_range.mp hk)))
    exact (Nat.mul_le_mul HR (MvMass.pow_le _ _)).trans (by simp)
  have HS := Finset.sum_le_sum HL
  simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul,Nat.mul_assoc] using Nat.add_le_add_left HS 1


def rowMassHeight (m B H : ℕ) : ℕ := H+B*(m+1)+1

theorem rowMassHeight_binary {m B H : List Bool → ℕ}
    (hm : BinaryFn m) (hB : BinaryFn B) (hH : BinaryFn H) :
    BinaryFn (fun q => rowMassHeight (m q) (B q) (H q)) :=
  (hH.add (hB.mul (hm.add (BinaryFn.const 1)))).add (BinaryFn.const 1)

theorem equation_row_mass (b : IntegralCoordinateBasis A m (2 ^ B))
    (p : Polynomial A) (d H : ℕ) (w : Fin m → ℕ) (W : ℕ)
    (hM : ∀ r s, (Algebra.leftMulMatrix (coordinateBasis b p d).finBasis
      (AdjoinRoot.root _) r s).natAbs ≤ 2 ^ H) :
    MvMass.mass (MonicParameterRows.row (equation b p d) (2^B) w W) ≤
      2 ^ rowMassHeight m B H := by
  have HE := equation_monic b p d (Nat.two_pow_pos B)
  have HM := monic_row_mass (equation b p d) (2^B) (count m B) H HE.1 HE.2 w W
    (fun k hk => equation_lower_mass b p d H k hk hM)
  apply HM.trans
  have HP : 2^B * count m B * 2^H = 2^(H+B*(m+1)) := by
    unfold count
    rw [← pow_mul,← pow_add,← pow_add]
    congr 1
    ring
  rw [HP,rowMassHeight,pow_succ]
  have HT : 1 ≤ 2^(H+B*(m+1)) := Nat.one_le_two_pow
  omega

theorem equation_row_mass_of_coefficient (b : IntegralCoordinateBasis A m (2 ^ B))
    (p : Polynomial A) (d H : ℕ) (w : Fin m → ℕ) (W : ℕ)
    (hp : ∀ k r s, (Algebra.leftMulMatrix b.finBasis (p.coeff k) r s).natAbs ≤ 2 ^ H) :
    MvMass.mass (MonicParameterRows.row (equation b p d) (2^B) w W) ≤
      2 ^ rowMassHeight m B (rootHeight (count m B) (2^B) H) :=
  equation_row_mass b p d _ w W (root_height b p d H hp)

end LeanCanny.Algebra.PaddedIntegralParameterExtension
