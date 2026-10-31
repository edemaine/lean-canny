/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CanonicalIntegralScalarAppend
public import LeanCanny.Algebra.UniformIntegralPrefix
public import LeanCanny.Algebra.PolynomialSystemReindex

/-! # Square samplers retaining ancestral coordinates

A history sampler keeps a scalar prefix inside a larger square system.
Every root interprets that actual algebra, and exclusion at infinity makes
the full root set finite, including singular roots. Scalar extension retains
all the old physical coordinates and equations.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralHistorySampler
open MvPolynomial WeightedHomogenization UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Sampler (S N m : ℕ) (ι : Type) where
  scalarPrefix : UniformIntegralPrefix.Prefix S N m
  scalar : Fin m → ι
  rows : ι → MvPolynomial ι ℤ
  degrees : ι → ℕ
  row_degree : ∀ i, (rows i).totalDegree ≤ degrees i
  degree_pos : ∀ i, 0 < degrees i
  noInfinity : ∀ y : Option ι → ℂ, y none = 0 →
    (∀ i, (homogenize (fun _ => 1) (degrees i) (rows i)).eval₂ (Int.castRingHom ℂ) y = 0) → y = 0
  interpret : ∀ (K : Type) [CommRing K] (z : ι → K),
    (∀ i, (rows i).eval₂ (Int.castRingHom K) z = 0) →
    ∃ φ : scalarPrefix.carrier →ₐ[ℤ] K,
      ∀ i, φ (scalarPrefix.basis.generator i) = z (scalar i) ^ weights S N m i

variable {S N m : ℕ} {ι : Type}

noncomputable def ofPrefix (P : UniformIntegralPrefix.Prefix S N m) : Sampler S N m (Fin m) where
  scalarPrefix := P
  scalar := id
  rows := P.rows
  degrees := P.degrees
  row_degree := P.row_degree
  degree_pos := P.degree_pos
  noInfinity := P.noInfinity
  interpret := P.interpret

noncomputable def base (S N : ℕ) : Sampler S N 0 (Fin 0) := ofPrefix (UniformIntegralPrefix.base S N)

noncomputable def scalarStep [Fintype ι] (F : Sampler S N m ι) (hm : m ≤ S) (hN : 0 < N)
    (p : Polynomial F.scalarPrefix.carrier) (d : ℕ) : Sampler S N (m + 1) (ι ⊕ Unit) where
  scalarPrefix := UniformIntegralPrefix.step F.scalarPrefix hm hN p d
  scalar := Fin.cons (Sum.inr ()) (fun i => Sum.inl (F.scalar i))
  rows := CanonicalIntegralScalarAppend.rows S F.rows F.scalar F.scalarPrefix.basis p d
  degrees := CanonicalIntegralScalarAppend.degrees S N m F.degrees
  row_degree := CanonicalIntegralScalarAppend.row_degree S hm hN F.rows F.degrees F.row_degree F.scalar F.scalarPrefix.basis p d
  degree_pos := CanonicalIntegralScalarAppend.degrees_pos S hN F.degrees F.degree_pos
  noInfinity := CanonicalIntegralScalarAppend.noInfinity (Int.castRingHom ℂ) S hm hN
    F.rows F.degrees F.noInfinity F.scalar F.scalarPrefix.basis p d
  interpret := by
    intro K instK z hz
    obtain ⟨φ, hφ⟩ := CanonicalIntegralScalarAppend.interpret S hN F.rows F.scalar F.scalarPrefix.basis p d
      (F.interpret K) z hz
    refine ⟨φ, fun i => ?_⟩
    change φ ((PaddedIntegralParameterExtension.coordinateBasis F.scalarPrefix.basis p d).generator i) = _
    rw [hφ i]
    exact Fin.cases rfl (fun _ => rfl) i

theorem scalarStep_old_roots [Fintype ι] {K : Type*} [CommRing K]
    (F : Sampler S N m ι) (hm : m ≤ S) (hN : 0 < N) (p : Polynomial F.scalarPrefix.carrier) (d : ℕ)
    (z : (ι ⊕ Unit) → K) (hz : ∀ j, ((scalarStep F hm hN p d).rows j).eval₂ (Int.castRingHom K) z = 0) :
    ∀ i, (F.rows i).eval₂ (Int.castRingHom K) (z ∘ Sum.inl) = 0 :=
  ((CanonicalIntegralScalarAppend.roots_iff S F.rows F.scalar F.scalarPrefix.basis p d z).mp hz).1

noncomputable def reindex {κ : Type} [Fintype ι] [Fintype κ]
    (F : Sampler S N m ι) (e : ι ≃ κ) : Sampler S N m κ where
  scalarPrefix := F.scalarPrefix
  scalar := e ∘ F.scalar
  rows := PolynomialSystemReindex.system e F.rows
  degrees := F.degrees ∘ e.symm
  row_degree i := (totalDegree_rename_le _ _).trans (F.row_degree (e.symm i))
  degree_pos i := F.degree_pos (e.symm i)
  noInfinity := by
    intro y hy hz
    have HE : y ∘ Option.map e = 0 := by
      apply F.noInfinity _ hy
      intro i
      have HI := hz (e i)
      simp only [PolynomialSystemReindex.system, Function.comp_apply, Equiv.symm_apply_apply] at HI
      rw [homogenize_rename, eval₂_rename] at HI
      exact HI
    funext i
    cases i with
    | none => exact hy
    | some i => simpa only [Function.comp_apply, Option.map_some, Equiv.apply_symm_apply, Pi.zero_apply]
        using congrFun HE (some (e.symm i))
  interpret := by
    intro K instK z hz
    exact F.interpret K (z ∘ e) ((PolynomialSystemReindex.roots_iff (Int.castRingHom K) e F.rows z).mp hz)

theorem finite_roots [Fintype ι] {K : Type*} [Field K] [CharZero K] (F : Sampler S N m ι) :
    {z : ι → K | ∀ i, (F.rows i).eval₂ (Int.castRingHom K) z = 0}.Finite := by
  let e := Fintype.equivFin ι
  let G := reindex F e
  have HF := AffineFiniteCoordinates.finite_roots (K := K) G.rows G.degrees G.row_degree G.degree_pos G.noInfinity
  have HI : Function.Injective (fun z : ι → K => z ∘ e.symm) := by
    intro z w h
    funext i
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using congrFun h (e i)
  apply (HF.preimage HI.injOn).subset
  intro z hz
  change ∀ i, (F.rows i).eval₂ (Int.castRingHom K) z = 0 at hz
  change ∀ j, (PolynomialSystemReindex.system e F.rows j).eval₂ (Int.castRingHom K) (z ∘ e.symm) = 0
  apply (PolynomialSystemReindex.roots_iff (Int.castRingHom K) e F.rows _).mpr
  simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using hz

end LeanCanny.Algebra.IntegralHistorySampler
