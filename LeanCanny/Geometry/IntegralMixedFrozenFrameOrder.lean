/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameLevel

/-! # Frozen-first ordering preserves the actual old mixed frame

Only the spatial coordinate tuple and integer LOW names are permuted. The
sampler, bank, hom, leading coefficient and original degree remain literal.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory Set
open scoped Classical
variable {n : ℕ}

def permute (F : Frame n) (e : Equiv.Perm (Fin (n+1))) : Frame n where
  frozen := Finset.univ.filter (fun i=>e i∈F.frozen)
  scales i := F.scales (e i)
  scales_ne_zero i := F.scales_ne_zero (e i)
  heights i := F.heights (e i)

noncomputable def ordered (F : Frame n) := permute F (FrozenCoordinateOrdering.permutation F.frozen)

theorem ordered_frozen (F : Frame n) :
    (ordered F).frozen=Finset.univ.filter (fun i=>i.val<F.frozen.card) := by
  ext i
  simp only [ordered,permute,Finset.mem_filter,Finset.mem_univ,true_and,FrozenCoordinateOrdering.permutation_mem_iff]

theorem slice_permute {m : ℕ} (P : SpatialSource n) (F : Frame n) (e : Equiv.Perm (Fin (n+1))) (values : Fin m→ℝ) :
    slice (IntegralMixedCoordinateRename.spatial P e) (permute F e) values=
      {z | z ∘ e.symm∈slice P F values} := by
  ext z
  constructor
  · intro h
    refine ⟨(IntegralMixedCoordinateRename.source_eval P e z).symm.trans h.1,?_⟩
    intro j hj
    have HI : e.symm j∈(permute F e).frozen := by simp only [permute,Finset.mem_filter,Finset.mem_univ,true_and,Equiv.apply_symm_apply]; exact hj
    have HJ:=h.2 (e.symm j) HI
    simpa only [permute,Equiv.apply_symm_apply,Function.comp_apply] using HJ
  · intro h
    refine ⟨(IntegralMixedCoordinateRename.source_eval P e z).trans h.1,?_⟩
    intro i hi
    have HI : e i∈F.frozen := (Finset.mem_filter.mp hi).2
    have HJ:=h.2 (e i) HI
    simpa only [permute,Function.comp_apply,Equiv.symm_apply_apply] using HJ

theorem actualSlice_permute {S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n)
    (e : Equiv.Perm (Fin (n+1))) :
    actualSlice (IntegralMixedCoordinateRename.state x e) φ (permute F e)=
      {z | z ∘ e.symm∈actualSlice x φ F} := by
  let values : Fin m→ℝ:=fun i=>φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)
  rw [actualSlice_eq (IntegralMixedCoordinateRename.state x e) φ (permute F e) values (fun _=>rfl),
    actualSlice_eq x φ F values (fun _=>rfl)]
  exact slice_permute P F e values

noncomputable def spatialHomeomorph (e : Equiv.Perm (Fin (n+1))) : (Fin (n+1)→ℝ) ≃ₜ (Fin (n+1)→ℝ) where
  toFun z:=z ∘ e
  invFun z:=z ∘ e.symm
  left_inv z:=by funext i; simp only [Function.comp_apply,Equiv.apply_symm_apply]
  right_inv z:=by funext i; simp only [Function.comp_apply,Equiv.symm_apply_apply]
  continuous_toFun:=continuous_pi (fun i=>continuous_apply (e i))
  continuous_invFun:=continuous_pi (fun i=>continuous_apply (e.symm i))

noncomputable def actualSliceHomeomorph {S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n)
    (e : Equiv.Perm (Fin (n+1))) :
    actualSlice x φ F ≃ₜ actualSlice (IntegralMixedCoordinateRename.state x e) φ (permute F e) :=
  (spatialHomeomorph e).sets (by
    ext z
    rw [actualSlice_permute]
    change z∈actualSlice x φ F↔(z ∘ e) ∘ e.symm∈actualSlice x φ F
    simp only [Function.comp_def,Equiv.apply_symm_apply])

theorem old_sampler {S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (e : Equiv.Perm (Fin (n+1))) :
    (IntegralMixedCoordinateRename.state x e).sampler=x.sampler := rfl

theorem original_source_bounds (P : SpatialSource n) (e : Equiv.Perm (Fin (n+1))) :
    (IntegralMixedCoordinateRename.spatial P e).leading=P.leading ∧
    (IntegralMixedCoordinateRename.spatial P e).degree=P.degree := ⟨rfl,rfl⟩

end LeanCanny.Geometry.IntegralMixedFrozenFrame
