/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PhysicalPowerCriticalCone
public import LeanCanny.Algebra.PhysicalPowerCriticalDegree
public import LeanCanny.Algebra.HomogenizationRename
public import LeanCanny.Algebra.TriangularPolynomialSystem

/-! # Appending coordinate-critical blocks preserves exclusion at infinity

The old system may retain arbitrary ancestral coordinates. Its equations
are renamed without changing degrees; the new coordinate-critical block
excludes its physical and multiplier coordinates independently of the old
parameter values. No regularity or reducedness hypothesis is used.
-/

@[expose] public section
namespace LeanCanny.Algebra.PhysicalPowerCriticalAppend
open MvPolynomial FlatAffineCriticalStage WeightedHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {ι R K : Type*} {n : ℕ} [Fintype ι] [CommRing R] [Field K] [CharZero K]

noncomputable def rows (q : ι → MvPolynomial ι R) (low : MvPolynomial (Fin (n + 1)) R)
    (a b : R) (c : Fin (n + 1) → R) (s : Finset (Fin (n + 1))) (r : Fin (n + 1))
    (H : Fin (n + 1) → MvPolynomial ι R) (w : ι → ℕ) (D W : ℕ) :
    (ι ⊕ Variables (n + 1)) → MvPolynomial (ι ⊕ Variables (n + 1)) R :=
  TriangularPolynomialSystem.append q (PhysicalPowerCriticalRows.rows
    (FermatCriticalHomogenization.polynomial low a D) s
    (PhysicalPowerCriticalRows.coordinateNormals b c r) H w D W)

def degrees (e : ι → ℕ) (s : Finset (Fin (n + 1))) (D W : ℕ) : (ι ⊕ Variables (n + 1)) → ℕ :=
  Sum.elim e (PhysicalPowerCriticalRows.degrees s D W)

omit [Fintype ι] [Field K] [CharZero K] in
theorem row_degree (q : ι → MvPolynomial ι R) (e : ι → ℕ) (hq : ∀ i, (q i).totalDegree ≤ e i)
    (low : MvPolynomial (Fin (n + 1)) R) (a b : R) (c : Fin (n + 1) → R)
    (s : Finset (Fin (n + 1))) (r : Fin (n + 1)) (H : Fin (n + 1) → MvPolynomial ι R)
    (w : ι → ℕ) (D W : ℕ) (hD : 2 ≤ D) (hW : 0 < W) (hlow : low.totalDegree < D)
    (hH : ∀ i ∈ s, (CoordinatePowerSubstitution.substitute w (H i)).totalDegree < W)
    (j : ι ⊕ Variables (n + 1)) :
    (rows q low a b c s r H w D W j).totalDegree ≤ degrees e s D W j := by
  cases j with
  | inl i => exact (totalDegree_rename_le _ _).trans (hq i)
  | inr j => exact PhysicalPowerCriticalRows.row_degree low a s _ H w D W hD hW hlow hH j

theorem noInfinity (φ : R →+* K) (q : ι → MvPolynomial ι R) (e : ι → ℕ)
    (hq : ∀ y : Option ι → K, y none = 0 →
      (∀ i, (homogenize (fun _ => 1) (e i) (q i)).eval₂ φ y = 0) → y = 0)
    (low : MvPolynomial (Fin (n + 1)) R) (a b : R) (c : Fin (n + 1) → R)
    (s : Finset (Fin (n + 1))) (r : Fin (n + 1)) (hr : r ∉ s)
    (H : Fin (n + 1) → MvPolynomial ι R) (w : ι → ℕ) (D W : ℕ)
    (hD : 2 ≤ D) (hW : 0 < W) (hlow : low.totalDegree < D)
    (ha : φ a ≠ 0) (hb : φ b ≠ 0) (hc : ∀ i, φ (c i) ≠ 0)
    (hH : ∀ i ∈ s, (CoordinatePowerSubstitution.substitute w (H i)).totalDegree < W)
    (y : Option (ι ⊕ Variables (n + 1)) → K) (hy : y none = 0)
    (hz : ∀ j, (homogenize (fun _ => 1) (degrees e s D W j)
      (rows q low a b c s r H w D W j)).eval₂ φ y = 0) : y = 0 := by
  have hold : y ∘ Option.map (Sum.inl : ι → ι ⊕ Variables (n + 1)) = 0 := by
    apply hq
    · exact hy
    · intro i
      have HI := hz (Sum.inl i)
      simp only [rows, degrees, TriangularPolynomialSystem.append, Sum.elim_inl] at HI
      rw [homogenize_rename, eval₂_rename] at HI
      exact HI
  have hnew := PhysicalPowerCriticalRows.physical_zero φ low a b c s r hr H w D W
    hD hW hlow ha hb hc hH y hy (fun j => hz (Sum.inr j))
  funext j
  cases j with
  | none => exact hy
  | some j =>
    cases j with
    | inl i => exact congrFun hold (some i)
    | inr j =>
      cases j with
      | inl i => exact congrFun hnew.1 i
      | inr i => exact congrFun hnew.2 i

end LeanCanny.Algebra.PhysicalPowerCriticalAppend
