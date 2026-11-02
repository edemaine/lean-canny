/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCoordinateSquarefree
public import LeanCanny.Algebra.BoundedClearedDilation
public import LeanCanny.Algebra.ClearedDilationLimit

/-! # Selected limit-coordinate factors over the actual mixed history

The degree allowance is the original relative spatial degree. Denominator
clearing uses the bank product, and the first surviving deformation coefficient
is selected only after the actual old hom is fixed. No absolute norm root or
universal trailing-coefficient survival is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitCoordinate
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

abbrev degree (P : SpatialSource n) (r : Rule n) := IntegralMixedCoordinateSquarefree.coordinateDegree P r
abbrev ChoiceBound (P : SpatialSource n) (r : Rule n) := degree P r+1

noncomputable def series (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) : Polynomial (Polynomial x.sampler.scalarPrefix.carrier) :=
  Bivariate.swap (BoundedClearedDilation.rescale (coordinate x hm r j) (commonDenominator x : _) (degree P r))

noncomputable def coefficient (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (c : ℕ) : Polynomial x.sampler.scalarPrefix.carrier :=
  (series x hm r j).coeff c

noncomputable def factor (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (c : Fin (ChoiceBound P r)) : Polynomial x.sampler.scalarPrefix.carrier :=
  coefficient x hm r j c.val

noncomputable def selectedSeries (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    Polynomial (Polynomial ℝ) := (series x hm r j).map (mapRingHom φ.toRingHom)

def Valid (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (c : Fin (ChoiceBound P r)) : Prop :=
  (∀ k < c.val, (coefficient x hm r j k).map φ.toRingHom=0) ∧ (factor x hm r j c).map φ.toRingHom≠0

theorem selected_coefficient (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (c : ℕ) :
    (selectedSeries x hm r j φ).coeff c=(coefficient x hm r j c).map φ.toRingHom := by
  rw [selectedSeries,coefficient,coeff_map,coe_mapRingHom]

theorem top_survives (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    ((selectedSeries x hm r j φ).coeff (degree P r)).coeff (degree P r)≠0 := by
  let p := (selected x hm r j φ).map (evalRingHom 0)
  have HD : p.natDegree=degree P r := specialized_degree x hm r j φ 0
  have HP : p≠0 := by
    intro HZ
    rw [HZ,natDegree_zero] at HD
    have HPos : 0 < degree P r := pow_pos (Nat.two_pow_pos _) _
    omega
  have HC : p.coeff (degree P r)≠0 := by
    rw [← HD]
    exact leadingCoeff_ne_zero.mpr HP
  have HE : φ.toRingHom (((coordinate x hm r j).coeff (degree P r)).coeff 0)≠0 := by
    simpa only [p,selected,coeff_map,coe_mapRingHom,coe_evalRingHom,eval_map,eval₂_at_zero] using HC
  rw [selected_coefficient,coeff_map,coefficient,series,
    BoundedClearedDilation.swapped_coefficient _ _ _ (coordinate_degree x hm r j),
    ite_eq_left (Nat.le_refl _),Nat.sub_self,pow_zero,mul_one]
  exact HE

theorem selected_ne_zero (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    selectedSeries x hm r j φ≠0 := by
  intro HZ
  have H := top_survives x hm r j φ
  rw [HZ,coeff_zero,coeff_zero] at H
  exact H rfl

theorem index_le (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    (selectedSeries x hm r j φ).natTrailingDegree ≤ degree P r := by
  apply natTrailingDegree_le_of_ne_zero
  intro HZ
  exact top_survives x hm r j φ (by rw [HZ,coeff_zero])

theorem exists_valid (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    ∃ c : Fin (ChoiceBound P r), Valid x hm r j φ c := by
  let c : Fin (ChoiceBound P r) := ⟨(selectedSeries x hm r j φ).natTrailingDegree,by
    have H := index_le x hm r j φ; change _ < degree P r+1; omega⟩
  refine ⟨c,?_,?_⟩
  · intro k hk
    rw [← selected_coefficient]
    exact coeff_eq_zero_of_lt_natTrailingDegree hk
  · rw [factor,← selected_coefficient]
    exact coeff_natTrailingDegree_ne_zero.mpr (selected_ne_zero x hm r j φ)

theorem factor_nonzero (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (c : Fin (ChoiceBound P r)) (hc : Valid x hm r j φ c) : factor x hm r j c≠0 := by
  intro HZ
  exact hc.2 (by rw [HZ,Polynomial.map_zero])

theorem factor_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (c : Fin (ChoiceBound P r)) :
    (factor x hm r j c).natDegree ≤ c.val :=
  BoundedClearedDilation.coefficient_degree _ _ _ _ (coordinate_degree x hm r j)

theorem selected_degree_bound (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (c : Fin (ChoiceBound P r)) : ((factor x hm r j c).map φ.toRingHom).natDegree ≤ degree P r :=
  natDegree_map_le.trans ((factor_degree x hm r j c).trans (by have H : c.val<degree P r+1:=c.isLt; omega))

end LeanCanny.Algebra.IntegralMixedLimitCoordinate
