/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UniformIntegralPrefixRows
public import LeanCanny.Algebra.TriangularPolynomialSystem

/-! # Scalar births retain every ancestral physical coordinate

The old square system can contain physical and multiplier coordinates in
addition to its scalar prefix. The new scalar equation reads only the scalar
slots, with their original powers. Appending it preserves the old equations,
degree bounds, exclusion at infinity, and exact algebra interpretation.
-/

@[expose] public section
namespace LeanCanny.Algebra.CanonicalIntegralScalarAppend
open MvPolynomial WeightedHomogenization UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {ι A K : Type*} [CommRing A] {m N : ℕ}

def layout (f : Fin m → ι) : (Fin m ⊕ Unit) → (ι ⊕ Unit) := Sum.map f id

noncomputable def rows (S : ℕ) (q : ι → MvPolynomial ι ℤ) (f : Fin m → ι)
    (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ) :
    (ι ⊕ Unit) → MvPolynomial (ι ⊕ Unit) ℤ :=
  TriangularPolynomialSystem.append q (fun _ => rename (layout f) (MonicParameterRows.row
    (PaddedIntegralParameterExtension.equation b p d) N (weights S N m) (birth S N m)))

def degrees (S N m : ℕ) (e : ι → ℕ) : (ι ⊕ Unit) → ℕ := Sum.elim e (fun _ => N * birth S N m)

theorem row_degree (S : ℕ) (hm : m ≤ S) (hN : 0 < N)
    (q : ι → MvPolynomial ι ℤ) (e : ι → ℕ) (hq : ∀ i, (q i).totalDegree ≤ e i)
    (f : Fin m → ι) (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (j : ι ⊕ Unit) : (rows S q f b p d j).totalDegree ≤ degrees S N m e j := by
  cases j with
  | inl i => exact (totalDegree_rename_le _ _).trans (hq i)
  | inr u =>
    apply (totalDegree_rename_le _ _).trans
    apply (totalDegree_add _ _).trans
    apply max_le ?_ (scalar_lower_degree S hm hN b p d).le
    simpa only [Nat.one_mul] using
      ((isHomogeneous_X (R := ℤ) (Sum.inr () : Fin m ⊕ Unit)).pow (N * birth S N m)).totalDegree_le

theorem degrees_pos (S : ℕ) (hN : 0 < N) (e : ι → ℕ) (he : ∀ i, 0 < e i)
    (j : ι ⊕ Unit) : 0 < degrees S N m e j := by
  cases j with
  | inl i => exact he i
  | inr u => exact Nat.mul_pos hN (birth_pos S N m)

theorem noInfinity [Fintype ι] [Field K] (φ : ℤ →+* K) (S : ℕ) (hm : m ≤ S) (hN : 0 < N)
    (q : ι → MvPolynomial ι ℤ) (e : ι → ℕ)
    (hq : ∀ y : Option ι → K, y none = 0 →
      (∀ i, (homogenize (fun _ => 1) (e i) (q i)).eval₂ φ y = 0) → y = 0)
    (f : Fin m → ι) (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (y : Option (ι ⊕ Unit) → K) (hy : y none = 0)
    (hz : ∀ j, (homogenize (fun _ => 1) (degrees S N m e j) (rows S q f b p d j)).eval₂ φ y = 0) :
    y = 0 := by
  have hold : y ∘ Option.map (Sum.inl : ι → ι ⊕ Unit) = 0 := by
    apply hq
    · exact hy
    · intro i
      have HI := hz (Sum.inl i)
      simp only [rows, degrees, TriangularPolynomialSystem.append, Sum.elim_inl] at HI
      rw [homogenize_rename, eval₂_rename] at HI
      exact HI
  have Hnew := hz (Sum.inr ())
  simp only [rows, degrees, TriangularPolynomialSystem.append, Sum.elim_inr] at Hnew
  rw [homogenize_rename, eval₂_rename,
    scalar_infinity φ S hm hN b p d (y ∘ Option.map (layout f)) hy] at Hnew
  have Hzero : y (some (Sum.inr ())) = 0 :=
    (pow_eq_zero_iff (Nat.mul_pos hN (birth_pos S N m)).ne').mp Hnew
  funext i
  cases i with
  | none => exact hy
  | some i =>
    cases i with
    | inl j => exact congrFun hold (some j)
    | inr u => cases u; exact Hzero

theorem roots_iff [CommRing K] (S : ℕ) (q : ι → MvPolynomial ι ℤ) (f : Fin m → ι)
    (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ) (z : (ι ⊕ Unit) → K) :
    (∀ j, (rows S q f b p d j).eval₂ (Int.castRingHom K) z = 0) ↔
      (∀ i, (q i).eval₂ (Int.castRingHom K) (z ∘ Sum.inl) = 0) ∧
      (MonicParameterRows.row (PaddedIntegralParameterExtension.equation b p d) N
        (weights S N m) (birth S N m)).eval₂ (Int.castRingHom K) (z ∘ layout f) = 0 := by
  rw [rows, TriangularPolynomialSystem.roots_append]
  simp only [eval₂_rename, forall_const]

theorem interpret [Nontrivial A] [CommRing K] (S : ℕ) (hN : 0 < N)
    (q : ι → MvPolynomial ι ℤ) (f : Fin m → ι) (b : IntegralCoordinateBasis A m N)
    (p : Polynomial A) (d : ℕ)
    (hq : ∀ z : ι → K, (∀ i, (q i).eval₂ (Int.castRingHom K) z = 0) →
      ∃ φ : A →ₐ[ℤ] K, ∀ i, φ (b.generator i) = z (f i) ^ weights S N m i)
    (z : (ι ⊕ Unit) → K) (hz : ∀ j, (rows S q f b p d j).eval₂ (Int.castRingHom K) z = 0) :
    ∃ φ : PaddedIntegralParameterExtension.Extension p d N →ₐ[ℤ] K,
      ∀ i, φ ((PaddedIntegralParameterExtension.coordinateBasis b p d).generator i) =
        (Fin.cons (z (Sum.inr ())) (fun j => z (Sum.inl (f j))) : Fin (m + 1) → K) i ^ weights S N (m + 1) i := by
  obtain ⟨hold, hnew⟩ := (roots_iff S q f b p d z).mp hz
  obtain ⟨φ, hφ⟩ := hq (z ∘ Sum.inl) hold
  let ψ := PaddedIntegralParameterExtension.liftAtPoweredRoot b p d hN φ
    (weights S N m) (birth S N m) (z ∘ layout f) hφ hnew
  refine ⟨ψ, ?_⟩
  intro i
  have HE := congrFun (PaddedIntegralParameterExtension.liftAtPoweredRoot_generators b p d hN φ
    (weights S N m) (birth S N m) (z ∘ layout f) hφ hnew) i
  change ψ ((PaddedIntegralParameterExtension.coordinateBasis b p d).generator i) = _ at HE
  rw [HE]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero, layout, Function.comp_apply, Sum.map_inr, id_eq, head]
  · simp only [Fin.cons_succ, layout, Function.comp_apply, Sum.map_inl, old]

end LeanCanny.Algebra.CanonicalIntegralScalarAppend
