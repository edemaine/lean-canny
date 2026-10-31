/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MonicParameterRows
public import LeanCanny.Algebra.HomogenizationRename
public import LeanCanny.Algebra.TriangularPolynomialSystem

/-! # Appending a scalar height preserves exclusion at infinity

Old equations keep their degrees and coordinates. The new monic row excludes
its own new infinity coordinate. This gives exclusion for the full appended
system without any smoothness or reducedness requirement.
-/

@[expose] public section
namespace LeanCanny.Algebra.MonicParameterAppend
open MvPolynomial WeightedHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {ι R K : Type*} [CommRing R] [Field K]

noncomputable def rows (q : ι → MvPolynomial ι R) (p : Polynomial (MvPolynomial ι R))
    (d : ℕ) (w : ι → ℕ) (W : ℕ) : (ι ⊕ Unit) → MvPolynomial (ι ⊕ Unit) R :=
  TriangularPolynomialSystem.append q (fun _ => MonicParameterRows.row p d w W)

def degrees (e : ι → ℕ) (d W : ℕ) : (ι ⊕ Unit) → ℕ := Sum.elim e (fun _ => d * W)

theorem roots_iff (φ : R →+* K) (q : ι → MvPolynomial ι R) (p : Polynomial (MvPolynomial ι R))
    (d : ℕ) (w : ι → ℕ) (W : ℕ) (z : (ι ⊕ Unit) → K) :
    (∀ i, (rows q p d w W i).eval₂ φ z = 0) ↔
      (∀ i, (q i).eval₂ φ (z ∘ Sum.inl) = 0) ∧
      (FixedDegreeIntegralNormalization.polynomial p d).eval₂
        (MvPolynomial.eval₂Hom φ (fun i => z (Sum.inl i) ^ w i)) (z (Sum.inr ()) ^ W) = 0 := by
  rw [rows, TriangularPolynomialSystem.roots_append]
  simp only [MonicParameterRows.eval_row, forall_const]

theorem noInfinity [Fintype ι] (φ : R →+* K) (q : ι → MvPolynomial ι R) (e : ι → ℕ)
    (hq : ∀ y : Option ι → K, y none = 0 →
      (∀ i, (homogenize (fun _ => 1) (e i) (q i)).eval₂ φ y = 0) → y = 0)
    (p : Polynomial (MvPolynomial ι R)) (d B : ℕ) (w : ι → ℕ) (W : ℕ)
    (hd : 0 < d) (hW : d * B < W)
    (hp : ∀ j, (CoordinatePowerSubstitution.substitute w (p.coeff j)).totalDegree ≤ B)
    (y : Option (ι ⊕ Unit) → K) (hy : y none = 0)
    (hz : ∀ i, (homogenize (fun _ => 1) (degrees e d W i) (rows q p d w W i)).eval₂ φ y = 0) :
    y = 0 := by
  have hold : y ∘ Option.map (Sum.inl : ι → ι ⊕ Unit) = 0 := by
    apply hq
    · exact hy
    · intro i
      have H := hz (Sum.inl i)
      simp only [rows, degrees, TriangularPolynomialSystem.append, Sum.elim_inl] at H
      rw [homogenize_rename, eval₂_rename] at H
      exact H
  have Hnew := hz (Sum.inr ())
  simp only [rows, degrees, TriangularPolynomialSystem.append, Sum.elim_inr] at Hnew
  have hn := MonicParameterRows.new_coordinate_zero φ p d B w W hd hW hp y hy Hnew
  funext j
  cases j with
  | none => exact hy
  | some i =>
    cases i with
    | inl i => exact congrFun hold (some i)
    | inr u => cases u; exact hn

end LeanCanny.Algebra.MonicParameterAppend
