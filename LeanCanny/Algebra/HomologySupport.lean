/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Support

/-! # Finiteness and support of module homology

Over a Noetherian ring, finite chain modules have finite homology.
An ideal sending cycles into boundaries annihilates homology, so the
homology is supported on the ideal's zero locus.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
universe u
namespace LeanCanny.Algebra.HomologySupport
variable {R : Type u} [CommRing R]
theorem finite (S : ShortComplex (ModuleCat.{u} R)) [IsNoetherian R S.X₂] : Module.Finite R S.homology := by
  let : Module.Finite R S.cycles := Module.Finite.of_injective S.iCycles.hom
    ((ModuleCat.mono_iff_injective S.iCycles).mp inferInstance)
  exact Module.Finite.of_surjective S.homologyπ.hom
    ((ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance)

theorem annihilator (S : ShortComplex (ModuleCat.{u} R)) (I : Ideal R)
    (h : I • LinearMap.ker S.g.hom ≤ LinearMap.range S.f.hom) :
    I ≤ Module.annihilator R S.homology := by
  intro f hf
  rw [Module.mem_annihilator]
  intro x
  obtain ⟨c, rfl⟩ := ((ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance) x
  have hc : S.iCycles c ∈ LinearMap.ker S.g.hom := by
    exact congrArg (fun φ : S.cycles ⟶ S.X₃ => φ c) S.iCycles_g
  obtain ⟨b, hb⟩ := h (Submodule.smul_mem_smul hf hc)
  have he : f • c = S.toCycles b := by
    apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
    rw [map_smul]
    have ht := congrArg (fun φ : S.X₁ ⟶ S.X₂ => φ b) S.toCycles_i
    exact hb.symm.trans ht.symm
  rw [← map_smul, he]
  exact congrArg (fun φ : S.X₁ ⟶ S.homology => φ b) S.toCycles_comp_homologyπ

theorem support (S : ShortComplex (ModuleCat.{u} R)) (I : Ideal R)
    [IsNoetherian R S.X₂]
    (h : I • LinearMap.ker S.g.hom ≤ LinearMap.range S.f.hom) :
    Module.support R S.homology ⊆ PrimeSpectrum.zeroLocus I := by
  let : Module.Finite R S.homology := finite S
  rw [Module.support_eq_zeroLocus]
  exact PrimeSpectrum.zeroLocus_anti_mono (annihilator S I h)

end LeanCanny.Algebra.HomologySupport
