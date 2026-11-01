/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateStatus
public import LeanCanny.Geometry.FlatAffineSingularComponentSampling
/-! # Compact selected frozen fibers meet the actual critical sections

The sample stays in the connected component of the supplied physical
point. Slice regularity and an absolute norm-root lift are unnecessary.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedComponentSampling
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation MvPolynomial
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def polynomial (P : SpatialSource n) : MvPolynomial (Fin (n+1)) ℝ :=
  (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).map (Int.castRingHom ℝ)

theorem polynomial_eval (P : SpatialSource n) (y : Fin (n+1) → ℝ) :
    (polynomial P).eval₂ (RingHom.id ℝ) y =
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y := by
  rw [polynomial, eval₂_map]
  rfl

noncomputable def fiber (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) : Set (Fin (n+1) → ℝ) :=
  {y | (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y = 0 ∧
    ∀ i, i.val < r.critical.offset.val → ((data x hm r.critical).scales i : ℝ) * y i = heightValue x r φ t i}

noncomputable def normals (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) :=
  PhysicalPowerCriticalRows.coordinateNormals (2 : ℝ) (fun i => ((data x hm r.critical).scales i : ℝ)) (data x hm r.critical).free

theorem frozen_mem (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (i : Fin (n+1)) :
    i ∈ (data x hm r.critical).frozen ↔ i.val < r.critical.offset.val := by
  simp only [data, Finset.mem_filter, Finset.mem_univ, true_and]

theorem normal_height (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (y : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    (∑ j, normals x hm r i.succ j * y j) = ((data x hm r.critical).scales i : ℝ) * y i := by
  simpa only [normals, RingHom.id_apply, pow_one] using PhysicalPowerCriticalRows.normal_height_sum (RingHom.id ℝ)
    2 (fun i => ((data x hm r.critical).scales i : ℝ)) (data x hm r.critical).free i y 1

theorem normal_independent {N : ℕ} (s : Finset (Fin (N+1))) (q : Fin (N+1) → ℝ) (hq : ∀ i, q i ≠ 0)
    (r : Fin (N+1)) (c : s → ℝ)
    (H : ∀ i, ∑ j : s, c j * PhysicalPowerCriticalRows.coordinateNormals 2 q r j.val.succ i = 0) : ∀ j, c j = 0 := by
  intro j
  have HJ := H j.val
  have HE : (∑ k : s, c k * PhysicalPowerCriticalRows.coordinateNormals 2 q r k.val.succ j.val) = c j * q j.val := by
    rw [Finset.sum_eq_single j]
    · simp [PhysicalPowerCriticalRows.coordinateNormals]
    · intro k _ hk
      have HK : j.val ≠ k.val := fun h => hk (Subtype.ext h.symm)
      simp [PhysicalPowerCriticalRows.coordinateNormals, HK]
    · simp
  rw [HE] at HJ
  exact (mul_eq_zero.mp HJ).resolve_right (hq j.val)

theorem objective_independent {N : ℕ} (s : Finset (Fin (N+1))) (q : Fin (N+1) → ℝ)
    (r : Fin (N+1)) (hr : r ∉ s) : ¬ ∃ c : s → ℝ, ∀ i,
      PhysicalPowerCriticalRows.coordinateNormals 2 q r 0 i =
        ∑ j : s, c j * PhysicalPowerCriticalRows.coordinateNormals 2 q r j.val.succ i := by
  rintro ⟨c,H⟩
  have HR := H r
  have HJ (j : s) : r ≠ j.val := fun h => hr (h.symm ▸ j.property)
  simp [PhysicalPowerCriticalRows.coordinateNormals, HJ] at HR

theorem exists_component_critical (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ)
    (hc : IsCompact (fiber x hm r φ t)) (z : Fin (n+1) → ℝ) (hz : z ∈ fiber x hm r φ t) :
    ∃ y : Fin (n+1) → ℝ, y ∈ connectedComponentIn (fiber x hm r φ t) z ∧
      y ∈ IntegralMixedSelectedPhysicalFiber.physical x hm r φ t := by
  let s := (data x hm r.critical).frozen
  let a := normals x hm r
  let b : Fin (n+1) → MvPolynomial (Fin 0) ℝ := fun j => C (heightValue x r φ t j)
  have HE : {y : Fin (n+1) → ℝ | (polynomial P).eval₂ (RingHom.id ℝ) y = 0 ∧
      ∀ j ∈ s, ∑ i, (RingHom.id ℝ) (a j.succ i) * y i = (b j).eval₂ (RingHom.id ℝ) (fun i => Fin.elim0 i)} = fiber x hm r φ t := by
    ext y
    simp only [polynomial_eval, RingHom.id_apply, b, eval₂_C]
    apply and_congr_right
    intro _
    constructor
    · intro H i hi
      exact (normal_height x hm r y i).symm.trans (H i ((frozen_mem x hm r i).mpr hi))
    · intro H i hi
      exact (normal_height x hm r y i).trans (H i ((frozen_mem x hm r i).mp hi))
  have Hscale (i : Fin (n+1)) : ((data x hm r.critical).scales i : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr ((data x hm r.critical).scales_ne i)
  have Hheights := normal_independent s (fun i => ((data x hm r.critical).scales i : ℝ)) Hscale (data x hm r.critical).free
  have Hobjective := objective_independent s (fun i => ((data x hm r.critical).scales i : ℝ))
    (data x hm r.critical).free (data x hm r.critical).free_not_frozen
  obtain ⟨y,mu,HY,HR⟩ := FlatAffineSingularComponentSampling.exists_component_stage_root (RingHom.id ℝ)
    (polynomial P) s a b (fun i => Fin.elim0 i) (HE.symm ▸ hc) Hheights Hobjective z
    (by rw [polynomial_eval]; exact hz.1) (fun i hi => by
      simpa only [RingHom.id_apply, b, eval₂_C] using
        (normal_height x hm r z i).trans (hz.2 i ((frozen_mem x hm r i).mp hi)))
  rw [HE] at HY
  have HYfiber : y ∈ fiber x hm r φ t := connectedComponentIn_subset _ _ HY
  have HG := (FlatAffineCriticalStage.roots_iff (RingHom.id ℝ) (polynomial P) s a b
    (Sum.elim (fun i : Fin 0 => Fin.elim0 i) (Sum.elim y mu))).mp HR
  refine ⟨y,HY,HYfiber.2,?_⟩
  intro j
  unfold IntegralMixedSweepRows.integerRow
  split_ifs with hj
  · exact HYfiber.1
  · let i := ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j
    have HI : i ∉ s := by
      intro HM
      have HH := (frozen_mem x hm r i).mp HM
      change r.critical.offset.val + j.val < r.critical.offset.val at HH
      omega
    have HJ : i ≠ (data x hm r.critical).free := by
      intro HH
      apply hj
      apply Fin.ext
      have HV := congrArg Fin.val HH
      change r.critical.offset.val + j.val = r.critical.offset.val + (objective r).val at HV
      omega
    have HH := HG.2.2.1 i
    have HU := HG.2.2.2 i HI
    change (pderiv i (polynomial P)).eval₂ (RingHom.id ℝ) y = ∑ j, normals x hm r j i * mu j at HH
    change mu i.succ = 0 at HU
    have HS := PhysicalPowerCriticalRows.normal_power_sum (RingHom.id ℝ) 2
      (fun i => ((data x hm r.critical).scales i : ℝ)) (data x hm r.critical).free i mu 1
    simp only [RingHom.id_apply, pow_one, ite_eq_right HJ, HU, mul_zero, zero_add] at HS
    have HP : (pderiv i (polynomial P)).eval₂ (RingHom.id ℝ) y = 0 := HH.trans (by simpa only [normals] using HS)
    simpa only [polynomial, pderiv_map, eval₂_map, RingHom.id_comp] using HP

end LeanCanny.Connectivity.IntegralMixedSelectedComponentSampling
