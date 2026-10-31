/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UniformIntegralPowerSchedule
public import LeanCanny.Algebra.PaddedIntegralRootLift
public import LeanCanny.Algebra.HomogenizationRename

/-! # Actual scalar-prefix rows in the persistent new-head layout

Each step retains every old equation and adjoins the canonical padded
equation with the fixed global schedule. Exclusion at infinity and the
interpretation of every root extend to the new prefix, including padding
roots. The old powers agree literally with the tail of the new schedule.
-/

@[expose] public section
namespace LeanCanny.Algebra.UniformIntegralPrefixRows
open MvPolynomial WeightedHomogenization UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] {m N : ℕ}

def layout (m : ℕ) : (Fin m ⊕ Unit) → Fin (m + 1) := Sum.elim Fin.succ (fun _ => 0)

noncomputable def rows (S : ℕ) (q : Fin m → MvPolynomial (Fin m) ℤ)
    (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ) :
    Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℤ :=
  Fin.cons (rename (layout m) (MonicParameterRows.row
    (PaddedIntegralParameterExtension.equation b p d) N (weights S N m) (birth S N m)))
    (fun i => rename Fin.succ (q i))

def degrees (S N : ℕ) (e : Fin m → ℕ) : Fin (m + 1) → ℕ := Fin.cons (N * birth S N m) e

theorem row_degree (S : ℕ) (hm : m ≤ S) (hN : 0 < N)
    (q : Fin m → MvPolynomial (Fin m) ℤ) (e : Fin m → ℕ) (hq : ∀ i, (q i).totalDegree ≤ e i)
    (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ) (j : Fin (m + 1)) :
    (rows S q b p d j).totalDegree ≤ degrees S N e j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · apply (totalDegree_rename_le _ _).trans
    apply (totalDegree_add _ _).trans
    apply max_le ?_ (scalar_lower_degree S hm hN b p d).le
    simpa only [Nat.one_mul] using
      ((isHomogeneous_X (R := ℤ) (Sum.inr () : Fin m ⊕ Unit)).pow (N * birth S N m)).totalDegree_le
  · exact (totalDegree_rename_le _ _).trans (hq i)

theorem degrees_pos (S : ℕ) (hN : 0 < N) (e : Fin m → ℕ) (he : ∀ i, 0 < e i)
    (j : Fin (m + 1)) : 0 < degrees S N e j :=
  Fin.cases (Nat.mul_pos hN (birth_pos S N m)) he j

theorem noInfinity {K : Type*} [Field K] (φ : ℤ →+* K) (S : ℕ) (hm : m ≤ S) (hN : 0 < N)
    (q : Fin m → MvPolynomial (Fin m) ℤ) (e : Fin m → ℕ)
    (hq : ∀ y : Option (Fin m) → K, y none = 0 →
      (∀ i, (homogenize (fun _ => 1) (e i) (q i)).eval₂ φ y = 0) → y = 0)
    (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (y : Option (Fin (m + 1)) → K) (hy : y none = 0)
    (hz : ∀ j, (homogenize (fun _ => 1) (degrees S N e j) (rows S q b p d j)).eval₂ φ y = 0) :
    y = 0 := by
  have hold : y ∘ Option.map (Fin.succ : Fin m → Fin (m + 1)) = 0 := by
    apply hq
    · exact hy
    · intro i
      have HI := hz i.succ
      simp only [rows, degrees, Fin.cons_succ] at HI
      rw [homogenize_rename, eval₂_rename] at HI
      exact HI
  have Hnew := hz 0
  simp only [rows, degrees, Fin.cons_zero] at Hnew
  rw [homogenize_rename, eval₂_rename,
    scalar_infinity φ S hm hN b p d (y ∘ Option.map (layout m)) hy] at Hnew
  have Hzero : y (some 0) = 0 :=
    (pow_eq_zero_iff (Nat.mul_pos hN (birth_pos S N m)).ne').mp Hnew
  funext i
  cases i with
  | none => exact hy
  | some i => exact Fin.cases Hzero (fun j => congrFun hold (some j)) i

theorem interpret [Nontrivial A] {K : Type*} [CommRing K] (S : ℕ) (hN : 0 < N)
    (q : Fin m → MvPolynomial (Fin m) ℤ) (b : IntegralCoordinateBasis A m N)
    (p : Polynomial A) (d : ℕ)
    (hq : ∀ z : Fin m → K, (∀ i, (q i).eval₂ (Int.castRingHom K) z = 0) →
      ∃ φ : A →ₐ[ℤ] K, ∀ i, φ (b.generator i) = z i ^ weights S N m i)
    (z : Fin (m + 1) → K) (hz : ∀ i, (rows S q b p d i).eval₂ (Int.castRingHom K) z = 0) :
    ∃ φ : PaddedIntegralParameterExtension.Extension p d N →ₐ[ℤ] K,
      ∀ i, φ ((PaddedIntegralParameterExtension.coordinateBasis b p d).generator i) =
        z i ^ weights S N (m + 1) i := by
  have hold : ∀ i, (q i).eval₂ (Int.castRingHom K) (z ∘ Fin.succ) = 0 := by
    intro i
    have HI := hz i.succ
    simpa only [rows, Fin.cons_succ, eval₂_rename] using HI
  obtain ⟨φ, hφ⟩ := hq (z ∘ Fin.succ) hold
  have Hnew := hz 0
  simp only [rows, Fin.cons_zero, eval₂_rename] at Hnew
  let ψ := PaddedIntegralParameterExtension.liftAtPoweredRoot b p d hN φ
    (weights S N m) (birth S N m) (z ∘ layout m) hφ Hnew
  refine ⟨ψ, ?_⟩
  intro i
  have HE := congrFun (PaddedIntegralParameterExtension.liftAtPoweredRoot_generators b p d hN φ
    (weights S N m) (birth S N m) (z ∘ layout m) hφ Hnew) i
  change ψ ((PaddedIntegralParameterExtension.coordinateBasis b p d).generator i) = _ at HE
  rw [HE]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero, layout, Function.comp_apply, Sum.elim_inr, head]
  · simp only [Fin.cons_succ, layout, Function.comp_apply, Sum.elim_inl, old]

end LeanCanny.Algebra.UniformIntegralPrefixRows
