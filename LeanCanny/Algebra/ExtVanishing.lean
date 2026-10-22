/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Ext vanishing in finite free targets and short exact sequences

A finite basis expresses the identity as a sum of coordinate projections
and inclusions. Thus vanishing into the base ring implies vanishing into
any finite free module. The long exact Ext sequence propagates vanishing
to a cokernel with the usual loss of one degree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian

universe u

namespace LeanCanny.Algebra.ExtVanishing
variable {R : Type u} [CommRing R]

theorem finite_free (N M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M] (i : ℕ)
    (h : Subsingleton (Ext N (ModuleCat.of R R) i)) : Subsingleton (Ext N M i) := by
  let b := Module.Free.chooseBasis R M
  let π (j : Module.Free.ChooseBasisIndex R M) : M ⟶ ModuleCat.of R R := ModuleCat.ofHom (b.coord j)
  let ι (j : Module.Free.ChooseBasisIndex R M) : ModuleCat.of R R ⟶ M :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b j))
  have hsum : ∑ j, π j ≫ ι j = 𝟙 M := by
    ext x
    simp [π, ι]
  have hz (e : Ext N M i) : e = 0 := by
    calc
      e = e.comp (Ext.mk₀ (∑ j, π j ≫ ι j)) (add_zero i) := by rw [hsum]; simp
      _ = 0 := by
        simp only [Ext.mk₀_sum, Ext.comp_sum, ← Ext.mk₀_comp_mk₀,
          ← Ext.comp_assoc_of_second_deg_zero]
        have he (j : Module.Free.ChooseBasisIndex R M) : e.comp (Ext.mk₀ (π j)) (add_zero i) = 0 :=
          h.elim _ _
        simp only [he, Ext.zero_comp, Finset.sum_const_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem cokernel (N : ModuleCat.{u} R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) (i : ℕ)
    (h₂ : Subsingleton (Ext N S.X₂ i)) (h₁ : Subsingleton (Ext N S.X₁ (i + 1))) :
    Subsingleton (Ext N S.X₃ i) := by
  have hz (e : Ext N S.X₃ i) : e = 0 := by
    obtain ⟨e₂, he₂⟩ := Ext.covariant_sequence_exact₃ N hS e rfl (h₁.elim _ _)
    rw [← he₂, h₂.elim e₂ 0, Ext.zero_comp]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem of_isZero (N M : ModuleCat.{u} R) (hM : Limits.IsZero M) (i : ℕ) :
    Subsingleton (Ext N M i) := by
  have hz (e : Ext N M i) : e = 0 := by
    calc
      e = e.comp (Ext.mk₀ (𝟙 M)) (add_zero i) := by simp
      _ = 0 := by rw [hM.eq_of_tgt (𝟙 M) 0]; simp
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end LeanCanny.Algebra.ExtVanishing
