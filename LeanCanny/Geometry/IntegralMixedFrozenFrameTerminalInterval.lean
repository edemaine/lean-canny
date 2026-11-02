/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameTerminal

/-! # Rank-one interval slabs have finite point covers

These are restrictions of the last-free-coordinate coarse slice. They are
not identified with the rank-zero full fiber. Between consecutive ordinary
coordinate cut values their open interiors are empty.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

def coordinateInterval {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (left right : ℝ) : Set (slice P F values) := {y | y.val h∈Icc left right}

theorem last_free_interval_finite_card (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen)
    (Hfrozen : ∀ i,i≠h→i∈F.frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i) (left right : ℝ) :
    Finite (coordinateInterval P F values h left right) ∧ Nat.card (coordinateInterval P F values h left right)≤2^B := by
  have HC:=last_free_finite_card x hm φ F h hh Hfrozen values H
  let : Finite (slice P F values):=HC.1
  exact ⟨inferInstance,(Nat.card_le_card_of_injective
    (Subtype.val : coordinateInterval P F values h left right→slice P F values) Subtype.val_injective).trans HC.2⟩

noncomputable def last_free_interval_cover (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen)
    (Hfrozen : ∀ i,i≠h→i∈F.frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i) (left right : ℝ) :
    ClopenPathCover (coordinateInterval P F values h left right) (coordinateInterval P F values h left right) := by
  let : Finite (coordinateInterval P F values h left right):=
    (last_free_interval_finite_card x hm φ F h hh Hfrozen values H left right).1
  let : DiscreteTopology (coordinateInterval P F values h left right):=inferInstance
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

theorem last_free_open_slab_empty (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen)
    (Hfrozen : ∀ i,i≠h→i∈F.frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i) (left right : ℝ)
    (havoid : ∀ t∈Ioo left right,(linePolynomial x hm F h hh).eval₂ φ.toRingHom t≠0) :
    {y : slice P F values | y.val h∈Ioo left right}=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  apply havoid (y.val h) hy
  exact relative_coordinate_root x hm φ F h hh values H y.val y.property
    (fun i hi hih=>False.elim (hi (Hfrozen i hih)))

end LeanCanny.Geometry.IntegralMixedFrozenFrame
