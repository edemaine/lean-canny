/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameNormal
public import LeanCanny.Algebra.IntegralMixedCriticalScalarShadow
public import LeanCanny.Algebra.IntegralMixedSourceReframe

/-! # Free-slot endpoint births reuse the exact native critical prefix

The shadow birth omits physical critical rows. After the spatial source is
reframed back, its actual selected scalar roots freeze original coordinates.
Only coefficient prefixes and banks are identified with the native command.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory Set
open UniformIntegralPowerSchedule
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def linePolynomial (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen) :
    Polynomial x.sampler.scalarPrefix.carrier :=
  criticalPolynomial (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm (coordinateRule F h hh)

noncomputable def lineState [Fintype ι] (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen) :
    State P S B (m+1) (ι⊕Unit) :=
  reframe (relativeScalarStep (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
    (coordinateRule F h hh)) P x.critical_cap

theorem lineState_native_prefix [Fintype ι] (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen) :
    (lineState x hm F h hh).sampler.scalarPrefix=
      (criticalStep (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm (coordinateRule F h hh)).sampler.scalarPrefix := rfl

theorem lineState_native_bank [Fintype ι] (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen) :
    (lineState x hm F h hh).bank=
      (criticalStep (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm (coordinateRule F h hh)).bank := rfl

theorem linePolynomial_congr (x : State P S B m ι) (hm : m≤S) (F G : Frame n)
    (h : Fin (n+1)) (hF : h∉F.frozen) (hG : h∉G.frozen) (H : F=G) :
    linePolynomial x hm F h hF=linePolynomial x hm G h hG := by
  subst G
  rfl

theorem heightRelative_line (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen) :
    heightRelative x hm (line F h) h=linePolynomial x hm F h hh := by
  change linePolynomial x hm (coarse (line F h) h) h (Finset.notMem_erase h (line F h).frozen)=_
  exact linePolynomial_congr x hm _ F h _ hh (coarse_line F h hh)

theorem normal_cut_root_iff (x : State P S B m ι) (hm : m≤S) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F) (a : ℝ) :
    (heightCut x hm (line F h) h).eval₂ φ.toRingHom a=0↔(linePolynomial x hm F h hh).eval₂ φ.toRingHom a=0 := by
  rw [line_cut_root_iff x hm φ F h (HF h hh) a,heightRelative_line x hm F h hh]

theorem continue_line [Fintype ι] (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (z : ι→ℝ)
    (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : ℝ) (ha : (linePolynomial x hm F h hh).eval₂ φ.toRingHom a=0) :
    let born:=lineState x hm F h hh
    ∃ y : (ι⊕Unit)→ℝ,∃ ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀ i,y (Sum.inl i)=z i) ∧ ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
      (∀ i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+1) i) ∧
      (∀ i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=(Fin.cons a values : Fin (m+1)→ℝ) i) ∧
      actualSlice born ψ (advance F h)=actualSlice x φ F∩{u | u h=a} ∧
      actualSlice born ψ (coarse (advance F h) h)=actualSlice x φ F := by
  obtain ⟨y,ψ,hy,hold,hψ,Hnew⟩:=relativeScalar_real_extend_recover
    (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm (coordinateRule F h hh)
    z hz φ hφ values H a ha
  have HR : ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ := by
    apply x.sampler.scalarPrefix.basis.algHom_ext
    intro i
    have HI:=hψ i.succ
    change ψ (AdjoinRoot.of _ (x.sampler.scalarPrefix.basis.generator i))=
      y (Sum.inl (x.sampler.scalar i))^weights S (2^B) (m+1) i.succ at HI
    rw [UniformIntegralPowerSchedule.old,hold] at HI
    exact HI.trans (hφ i).symm
  refine ⟨y,ψ,hy,hold,HR,hψ,Hnew,?_,?_⟩
  · rw [actualSlice_eq (lineState x hm F h hh) ψ _ (Fin.cons a values) Hnew,actualSlice_eq x φ F values H]
    exact slice_advance P F h hh values a
  · rw [actualSlice_eq (lineState x hm F h hh) ψ _ (Fin.cons a values) Hnew,actualSlice_eq x φ F values H]
    exact slice_coarse_advance P F h hh values a

end LeanCanny.Geometry.IntegralMixedFrozenFrame
