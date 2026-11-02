/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameLineContinue
public import LeanCanny.Connectivity.ClopenPathCover

/-! # The last free coordinate has a finite singleton cover

The whole rank-one coarse slice injects into the roots of its actual
selected ordinary relative polynomial. Fully frozen fibers have at most
one point. Neither statement assumes finite roots or component covers.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory Set Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem last_coordinate_injective {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (Hfrozen : ∀ i,i≠h→i∈F.frozen) :
    Function.Injective (fun y : slice P F values=>y.val h) := by
  intro y z H
  apply Subtype.ext
  funext i
  by_cases HI : i=h
  · subst i
    exact H
  · apply mul_left_cancel₀ (Int.cast_ne_zero.mpr (F.scales_ne_zero i) : (F.scales i:ℝ)≠0)
    exact (y.property.2 i (Hfrozen i HI)).trans (z.property.2 i (Hfrozen i HI)).symm

theorem last_free_finite_card (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen)
    (Hfrozen : ∀ i,i≠h→i∈F.frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i) :
    Finite (slice P F values) ∧ Nat.card (slice P F values)≤2^B := by
  let p:=(linePolynomial x hm F h hh).map φ.toRingHom
  have HP : p≠0:=IntegralMixedCriticalRoot.selected_nonzero
    (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm (coordinateRule F h hh) φ
  let f : slice P F values→p.rootSet ℝ:=fun y=>⟨y.val h,by
    apply (Polynomial.mem_rootSet_of_ne HP).mpr
    have HR:=relative_coordinate_root x hm φ F h hh values H y.val y.property
      (fun i hi hih=>False.elim (hi (Hfrozen i hih)))
    rw [Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id]
    change ((linePolynomial x hm F h hh).map φ.toRingHom).eval (y.val h)=0
    rw [Polynomial.eval_map]
    exact HR⟩
  have HF : Function.Injective f := by
    intro y z he
    exact last_coordinate_injective P F values h Hfrozen (congrArg Subtype.val he)
  have HD : p.natDegree≤2^B:=IntegralMixedCriticalRoot.selected_degree_cap
    (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm (coordinateRule F h hh) φ
  have HC : Nat.card (p.rootSet ℝ)≤p.natDegree := by
    simpa only [Nat.card_coe_set_eq] using p.ncard_rootSet_le ℝ
  exact ⟨Finite.of_injective f HF,(Nat.card_le_card_of_injective f HF).trans (HC.trans HD)⟩

noncomputable def last_free_cover (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen)
    (Hfrozen : ∀ i,i≠h→i∈F.frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i) :
    ClopenPathCover (slice P F values) (slice P F values) := by
  let : Finite (slice P F values):=(last_free_finite_card x hm φ F h hh Hfrozen values H).1
  let : DiscreteTopology (slice P F values):=inferInstance
  exact {
    piece i:={i}
    clopen i:=isClopen_discrete _
    cover y:=⟨y,mem_singleton y⟩
    paths i y hy z hz:=by
      have HY : y=i:=mem_singleton_iff.mp hy
      have HZ : z=i:=mem_singleton_iff.mp hz
      subst y
      subst z
      exact JoinedIn.refl (mem_singleton i) }

theorem last_free_component_iff (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen)
    (Hfrozen : ∀ i,i≠h→i∈F.frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (z y : Fin (n+1)→ℝ) (hz : z∈slice P F values) :
    y∈connectedComponentIn (slice P F values) z↔y=z := by
  let : Finite (slice P F values):=(last_free_finite_card x hm φ F h hh Hfrozen values H).1
  let : TotallyDisconnectedSpace (slice P F values):=inferInstance
  constructor
  · intro HY
    rw [connectedComponentIn_eq_image hz] at HY
    obtain ⟨a,ha,rfl⟩:=HY
    have HE : a=(⟨z,hz⟩ : slice P F values) := by
      exact isPreconnected_connectedComponent.subsingleton ha mem_connectedComponent
    exact congrArg Subtype.val HE
  · rintro rfl
    exact mem_connectedComponentIn hz

theorem fully_frozen_subsingleton {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (Hfrozen : ∀ i,i∈F.frozen) : Subsingleton (slice P F values) := by
  constructor
  intro y z
  apply Subtype.ext
  funext i
  apply mul_left_cancel₀ (Int.cast_ne_zero.mpr (F.scales_ne_zero i) : (F.scales i:ℝ)≠0)
  exact (y.property.2 i (Hfrozen i)).trans (z.property.2 i (Hfrozen i)).symm

noncomputable def fully_frozen_cover {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (Hfrozen : ∀ i,i∈F.frozen) : ClopenPathCover (slice P F values) Unit := by
  let : Subsingleton (slice P F values):=fully_frozen_subsingleton P F values Hfrozen
  exact {
    piece _:=univ
    clopen _:=isClopen_univ
    cover y:=⟨(),mem_univ y⟩
    paths _ y _ z _:=by
      have HE : y=z:=Subsingleton.elim y z
      subst z
      exact JoinedIn.refl (mem_univ y) }

end LeanCanny.Geometry.IntegralMixedFrozenFrame
