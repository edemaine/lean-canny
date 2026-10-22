/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ExtVanishing
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
/-! # Acyclicity of bounded complexes from Ext vanishing

Starting from the zero module above the top degree, descend through the
cokernels of the differentials. Each short exact sequence loses one degree
of Ext vanishing. Positive homology embeds into the corresponding cokernel,
and vanishing of Hom forces that homology to be zero.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u
namespace LeanCanny.Algebra.FiniteComplexAcyclicity

variable {R : Type u} [CommRing R]

noncomputable def opcyclesSequence (C : ChainComplex (ModuleCat.{u} R) ℕ) (k : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (C.fromOpcycles (k + 1) k) (C.pOpcycles k) (by
    rw [← cancel_epi (C.pOpcycles (k + 1))]
    simp)

theorem opcyclesSequence_shortExact (C : ChainComplex (ModuleCat.{u} R) ℕ) (k : ℕ) (h : C.ExactAt (k + 1)) :
    (opcyclesSequence C k).ShortExact := by
  have hp : (ComplexShape.down ℕ).prev (k + 1) = k + 2 :=
    (ComplexShape.down ℕ).prev_eq' rfl
  have hn : (ComplexShape.down ℕ).next (k + 1) = k :=
    (ComplexShape.down ℕ).next_eq' rfl
  have hs : (C.sc' (k + 2) (k + 1) k).Exact := (C.exactAt_iff' _ _ _ hp hn).mp h
  have hm : Mono (C.fromOpcycles (k + 1) k) := by
    have hh : Mono ((C.opcyclesIsoSc' (k + 2) (k + 1) k hp hn).inv ≫ C.fromOpcycles (k + 1) k) := by
      rw [C.opcyclesIsoSc'_inv_fromOpcycles (k + 2) (k + 1) k hp hn]
      exact hs.mono_fromOpcycles
    exact (mono_comp_iff_of_isIso _ _).mp hh
  let : Mono (opcyclesSequence C k).f := hm
  let : Epi (opcyclesSequence C k).g := inferInstanceAs (Epi (C.pOpcycles k))
  refine { exact := ?_ }
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hb : x ∈ LinearMap.range (C.d (k + 1) k).hom := by
    have he := ((C.sc k).moduleCat_pOpcycles_eq_zero_iff x).mp hx
    change x ∈ LinearMap.range (C.d ((ComplexShape.down ℕ).prev k) k).hom at he
    rwa [(ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (k + 1) k from rfl)] at he
  obtain ⟨y, hy⟩ := hb
  refine ⟨C.pOpcycles (k + 1) y, ?_⟩
  have he := congrArg (fun f : C.X (k + 1) ⟶ C.X k => f y) (C.p_fromOpcycles (k + 1) k)
  exact he.trans hy

theorem exactAt_of_ext_zero (C : ChainComplex (ModuleCat.{u} R) ℕ) (k : ℕ)
    (h : Subsingleton (Ext (C.homology k) (C.opcycles k) 0)) : C.ExactAt k := by
  have hh : Subsingleton (C.homology k ⟶ C.opcycles k) := Ext.addEquiv₀.subsingleton_congr.mp h
  exact (C.exactAt_iff_isZero_homology k).mpr
    (IsZero.of_mono_eq_zero (C.homologyι k) (hh.elim _ _))

theorem exactAt_of_bounded_ext (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (htop : IsZero (C.X (n + 1)))
    (hExt : ∀ t, 0 < t → t ≤ n → ∀ k, k ≤ n → ∀ j, j < n →
      Subsingleton (Ext (C.homology t) (C.X k) j)) :
    ∀ k, 0 < k → k ≤ n → C.ExactAt k := by
  let P (k : ℕ) : Prop :=
    (∀ t, 0 < t → t ≤ n → ∀ j, j < k → Subsingleton (Ext (C.homology t) (C.opcycles k) j)) ∧
      (0 < k → C.ExactAt k)
  have hb : P (n + 1) := by
    refine ⟨?_, fun _ => HomologicalComplex.ExactAt.of_isZero htop⟩
    intro t _ _ j _
    exact LeanCanny.Algebra.ExtVanishing.of_isZero _ _ (IsZero.of_epi (C.pOpcycles (n + 1)) htop) j
  have hs (k : ℕ) (hk : k < n + 1) (ih : P (k + 1)) : P k := by
    have he := opcyclesSequence_shortExact C k (ih.2 (Nat.succ_pos k))
    have hv : ∀ t, 0 < t → t ≤ n → ∀ j, j < k →
        Subsingleton (Ext (C.homology t) (C.opcycles k) j) := by
      intro t ht htn j hj
      exact LeanCanny.Algebra.ExtVanishing.cokernel (C.homology t) he j
        (hExt t ht htn k (by omega) j (by omega)) (ih.1 t ht htn (j + 1) (by omega))
    exact ⟨hv, fun hpos => exactAt_of_ext_zero C k (hv k hpos (by omega) 0 hpos)⟩
  intro k hk hkn
  have hP : P k := Nat.decreasingInduction' (m := k) (n := n + 1) (P := P) (fun l hl _ ih => hs l hl ih) (by omega) hb
  exact hP.2 hk

end LeanCanny.Algebra.FiniteComplexAcyclicity
