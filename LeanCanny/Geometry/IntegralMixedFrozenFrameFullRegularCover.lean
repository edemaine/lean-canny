/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameFullDescending
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRegularCover

/-! # Actual bounded regular sources have constructed recursive covers

The initial interpreting hom and joint tuple come from the empty sampler.
Real-height endpoints use full physical critical births; exceptional-factor
endpoints use correlated scalar cuts. No
sampler, hom, recursive cover, or path/component oracle is a premise.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Connectivity IntegralMixedHistory Set
open scoped Classical

theorem regular_zero_full_cover (R : BoundedFullWriter.Readers) (q : List Bool) (B : ℕ)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (R.dim q+4) (BoundedRegularLowModularTerm.source R q).degree≤2^B) :
    ∃ I : Type,Finite I ∧ Nonempty (ClopenPathCover
      {y : Fin (R.dim q+4)→ℝ |
        (FermatCriticalHomogenization.polynomial (BoundedRegularLowModularTerm.source R q).low
          (BoundedRegularLowModularTerm.source R q).leading (BoundedRegularLowModularTerm.source R q).degree).eval₂ (Int.castRingHom ℝ) y=0} I) := by
  let P:=BoundedRegularLowModularTerm.source R q
  let initial : State P (R.dim q+3) B 0 (Fin 0):=
    IntegralMixedHistory.base P (IntegralHistorySampler.base (R.dim q+3) (2^B)) (by
      apply le_trans _ hcap
      change PurePowerReductionBounds.dimension (R.dim q+4) (BoundedRegularLowModularTerm.source R q).degree≤_
      unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K
      omega)
  obtain ⟨φ,hφ⟩:=initial.sampler.interpret ℝ (Fin.elim0 : Fin 0→ℝ) (fun i=>Fin.elim0 i)
  let F : Frame (R.dim q+3):={
    frozen:=∅
    scales _:=1
    scales_ne_zero _:=one_ne_zero
    heights _:=.constant 0 }
  have Hbudget : 0+(R.dim q+3+1-F.frozen.card)≤R.dim q+3+1 := by
    simp only [F,Finset.card_empty,Nat.sub_zero,Nat.zero_add]
    exact le_rfl
  have HF : FreeNormal F:=fun _ _=>⟨rfl,rfl⟩
  obtain ⟨I,Hfin,⟨C⟩⟩:=exists_full_recursive_cover initial F Hbudget HF (AtomicRows.initial _ _) (PrefixFrozen.of_empty F rfl)
    (by omega) (BoundedFullWriter.size R q) rfl hcap (regular_source_proper R q) φ
    Fin.elim0 (fun i=>Fin.elim0 i) hφ Fin.elim0 (fun i=>Fin.elim0 i)
  have HE : slice P F (Fin.elim0 : Fin 0→ℝ)={y : Fin (R.dim q+4)→ℝ |
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y=0} := by
    ext y
    simp [slice,F]
  exact ⟨I,Hfin,⟨C.comap (Homeomorph.setCongr HE.symm)⟩⟩

theorem regular_zero_full_cover_original (R : BoundedFullWriter.Readers) (q : List Bool) :
    ∃ I : Type,Finite I ∧ Nonempty (ClopenPathCover
      {y : Fin (R.dim q+4)→ℝ | (BoundedRegularSource.polynomial (BoundedFullWriter.original R q)
        (BoundedFullWriter.size R q) (BoundedFullWriter.size R q) (R.radius q)).eval₂ (Int.castRingHom ℝ) y=0} I) := by
  obtain ⟨I,Hfin,⟨C⟩⟩:=regular_zero_full_cover R q (originalWidth R q) (originalWidth_cap R q)
  rw [BoundedRegularLowModularTerm.source_polynomial] at C
  exact ⟨I,Hfin,⟨C⟩⟩

end LeanCanny.Geometry.IntegralMixedFrozenFrame
