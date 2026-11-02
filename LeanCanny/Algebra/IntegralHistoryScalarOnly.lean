/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralHistorySampler

/-! # Scalar-only samplers have the literal newest-first prefix layout

Every physical variable is an actual scalar slot. Reindexing by that slot map
recovers the prefix equations, degrees and exclusion at infinity, even for an
empty prefix. No regularity or nonsingularity hypothesis is needed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralHistorySampler
open MvPolynomial
open scoped Classical
variable {S N m : ℕ} {ι : Type}

structure ScalarOnly (F : Sampler S N m ι) : Prop where
  bijective : Function.Bijective F.scalar
  rows : ∀ i, F.rows (F.scalar i)=rename F.scalar (F.scalarPrefix.rows i)
  degrees : ∀ i, F.degrees (F.scalar i)=F.scalarPrefix.degrees i

theorem base_scalarOnly (S N : ℕ) : ScalarOnly (base S N) where
  bijective := Function.bijective_id
  rows i := Fin.elim0 i
  degrees i := Fin.elim0 i

noncomputable def ScalarOnly.equiv {F : Sampler S N m ι} (H : ScalarOnly F) : Fin m ≃ ι :=
  Equiv.ofBijective F.scalar H.bijective

@[simp] theorem ScalarOnly.equiv_apply {F : Sampler S N m ι} (H : ScalarOnly F) (i : Fin m) :
    H.equiv i=F.scalar i := rfl

theorem scalarStep_scalarOnly [Fintype ι] (F : Sampler S N m ι) (H : ScalarOnly F)
    (hm : m≤S) (hN : 0<N) (p : Polynomial F.scalarPrefix.carrier) (d : ℕ) :
    ScalarOnly (scalarStep F hm hN p d) := by
  constructor
  · constructor
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases (fun _ => rfl) (fun j hij => ?_) j
        exact False.elim (Sum.inr_ne_inl hij)
      · intro j
        refine Fin.cases (fun hij => ?_) (fun j hij => ?_) j
        · exact False.elim (Sum.inl_ne_inr hij)
        · exact congrArg Fin.succ (H.bijective.1 (Sum.inl.inj hij))
    · intro y
      cases y with
      | inr u => cases u; exact ⟨0,rfl⟩
      | inl y => obtain ⟨i,hi⟩ := H.bijective.2 y; exact ⟨i.succ,congrArg Sum.inl hi⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change rename (CanonicalIntegralScalarAppend.layout F.scalar) _ =
        rename (Fin.cons (Sum.inr ()) (fun i => Sum.inl (F.scalar i)))
          (rename (UniformIntegralPrefixRows.layout m) _)
      rw [rename_rename]
      have HE : CanonicalIntegralScalarAppend.layout F.scalar =
          (Fin.cons (Sum.inr ()) (fun i => Sum.inl (F.scalar i))) ∘ UniformIntegralPrefixRows.layout m := by
        funext j
        cases j with
        | inl j => rfl
        | inr u => cases u; rfl
      rw [HE]
    · change rename Sum.inl (F.rows (F.scalar j)) =
        rename (Fin.cons (Sum.inr ()) (fun i => Sum.inl (F.scalar i))) (rename Fin.succ _)
      rw [H.rows j,rename_rename,rename_rename]
      rfl
  · intro i
    exact Fin.cases rfl (fun j => H.degrees j) i

theorem ScalarOnly.reindexed_rows {F : Sampler S N m ι} (H : ScalarOnly F) (i : Fin m) :
    PolynomialSystemReindex.system H.equiv.symm F.rows i=F.scalarPrefix.rows i := by
  change rename H.equiv.symm (F.rows (F.scalar i))=_
  rw [H.rows i,rename_rename]
  have HI : H.equiv.symm ∘ F.scalar=id := by funext j; exact H.equiv.symm_apply_apply j
  rw [HI,rename_id]
  rfl

theorem ScalarOnly.reindexed_degrees {F : Sampler S N m ι} (H : ScalarOnly F) (i : Fin m) :
    F.degrees (H.equiv i)=F.scalarPrefix.degrees i := H.degrees i

theorem ScalarOnly.roots_iff {F : Sampler S N m ι} (H : ScalarOnly F)
    {K : Type*} [CommRing K] (z : Fin m→K) :
    (∀ i, (F.scalarPrefix.rows i).eval₂ (Int.castRingHom K) z=0) ↔
      ∀ j, (F.rows j).eval₂ (Int.castRingHom K) (z ∘ H.equiv.symm)=0 := by
  have HR := PolynomialSystemReindex.roots_iff (Int.castRingHom K) H.equiv.symm F.rows z
  simpa only [H.reindexed_rows] using HR

end LeanCanny.Algebra.IntegralHistorySampler
