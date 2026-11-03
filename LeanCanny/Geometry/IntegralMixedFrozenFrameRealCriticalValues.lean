/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameLineContinue
public import LeanCanny.Geometry.IntegralMixedFrozenFrameEndpointFiber
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRegularity
/-! # Real critical values have physical witnesses; annihilator roots need not

These are the values where the actual shifted fiber has vanishing free
gradients. They form a finite subset of the existing height-polynomial roots.
Avoiding this smaller set already gives the regularity used by slab charts.
At a normalized free-coordinate line, every such value has an actual real
projection-critical point, as required by a full physical critical birth.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

def realCriticalValues {k : ℕ} (P : SpatialSource n) (F : Frame n)
    (values : Fin k→ℝ) (h : Fin (n+1)) : Set ℝ :=
  {t | ∃ y : Fin (n+1)→ℝ,y∈shiftedSlice P F values h t ∧
    ∀ i,i∉F.frozen→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) y=0}

theorem realCriticalValues_subset (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i) :
    realCriticalValues P F values h⊆{t | (heightCut x hm F h).eval₂ φ.toRingHom t=0} := by
  rintro t ⟨y,hy,hg⟩
  exact heightCut_root x hm φ F h hh values H t y hy hg

theorem realCriticalValues_finite (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i) :
    (realCriticalValues P F values h).Finite :=
  (heightCut_finite x hm F h φ).subset (realCriticalValues_subset x hm φ F h hh values H)

theorem regular_of_not_realCriticalValue {k : ℕ} (P : SpatialSource n) (F : Frame n)
    (values : Fin k→ℝ) (h : Fin (n+1)) (t : ℝ) (ht : t∉realCriticalValues P F values h)
    (y : Fin (n+1)→ℝ) (hy : y∈shiftedSlice P F values h t) :
    Function.Surjective (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ)
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree) F.frozen (coordinateNormals F) y) := by
  by_contra HS
  apply ht
  exact ⟨y,hy,CoordinateConstraintSingularity.outside_zero _ F.frozen (coordinateNormals F) F.scales
    F.scales_ne_zero (fun _ _=>rfl) y hy.1 HS⟩

theorem line_realCriticalValues_iff {k : ℕ} (P : SpatialSource n) (F : Frame n)
    (values : Fin k→ℝ) (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F) (t : ℝ) :
    t∈realCriticalValues P (line F h) values h ↔
      ∃ y : Fin (n+1)→ℝ,y∈slice P F values ∧ y h=t ∧
        ∀ i,i∉F.frozen→i≠h→
          (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
            (Int.castRingHom ℝ) y=0 := by
  constructor
  · rintro ⟨y,hy,hg⟩
    have HY : y∈slice P F values∩{u | u h=t}:=
      (Set.ext_iff.mp (line_slice P F h hh HF values t) y).mp hy
    refine ⟨y,HY.1,HY.2,?_⟩
    intro i hi hih
    exact hg i (by simpa only [line,Finset.mem_insert,not_or] using And.intro hih hi)
  · rintro ⟨y,hy,hyt,hg⟩
    refine ⟨y,(Set.ext_iff.mp (line_slice P F h hh HF values t) y).mpr ⟨hy,hyt⟩,?_⟩
    intro i hi
    have HI : i≠h ∧ i∉F.frozen:=by simpa only [line,Finset.mem_insert,not_or] using hi
    exact hg i HI.2 HI.1

theorem line_realCriticalValues_root (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen)
    (HF : FreeNormal F) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (ht : t∈realCriticalValues P (line F h) values h) :
    (linePolynomial x hm F h hh).eval₂ φ.toRingHom t=0 :=
  (normal_cut_root_iff x hm φ F h hh HF t).mp
    (realCriticalValues_subset x hm φ (line F h) h (Finset.mem_insert_self h F.frozen) values H ht)

end LeanCanny.Geometry.IntegralMixedFrozenFrame
