/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameCritical
public import LeanCanny.Algebra.IntegralMixedCriticalDegree

/-! # Ordinary relative coordinate roots in the literal current frame -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def coordinateRule (F : Frame n) (j : Fin (n+1)) (hj : j∉F.frozen) : CriticalRule n :=
  { critical F j hj with coordinate := (freeCoordinate F j hj).val }

theorem coordinateRule_index (F : Frame n) (j : Fin (n+1)) (hj : j∉F.frozen) :
    ClearedCoordinateCritical.freeIndex (coordinateRule F j hj).offset.val
      (IntegralMixedCriticalRoot.fit (coordinateRule F j hj)).le
      (IntegralMixedCriticalRoot.coordinate (coordinateRule F j hj))=
      (FrozenCoordinateOrdering.permutation F.frozen).symm j := by
  apply Fin.ext
  have HJ : ¬((FrozenCoordinateOrdering.permutation F.frozen).symm j).val<F.frozen.card:=
    fun H=>hj ((FrozenCoordinateOrdering.inverse_mem_iff F.frozen j).mp H)
  have HB:=((FrozenCoordinateOrdering.permutation F.frozen).symm j).isLt
  change F.frozen.card+(((FrozenCoordinateOrdering.permutation F.frozen).symm j).val-F.frozen.card)%
    (n-F.frozen.card+1)=_
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem coordinateRule_objective (F : Frame n) (j : Fin (n+1)) (hj : j∉F.frozen) :
    IntegralMixedCriticalRoot.objective (coordinateRule F j hj)=
      IntegralMixedCriticalRoot.coordinate (coordinateRule F j hj) := by
  apply Fin.ext
  rfl

theorem relative_coordinate_root (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (j : Fin (n+1)) (hj : j∉F.frozen)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (y : Fin (n+1)→ℝ) (hy : y∈slice P F values)
    (hgrad : ∀ i, i∉F.frozen→i≠j→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) y=0) :
    let e:=FrozenCoordinateOrdering.permutation F.frozen
    (criticalPolynomial (IntegralMixedCoordinateRename.state x e) hm (coordinateRule F j hj)).eval₂ φ.toRingHom (y j)=0 := by
  let e:=FrozenCoordinateOrdering.permutation F.frozen
  let r:=coordinateRule F j hj
  let x':=IntegralMixedCoordinateRename.state x e
  let z:=y ∘ e
  have HY : z∈actualSlice x' φ (permute F e) := by
    rw [actualSlice_permute]
    change z ∘ e.symm∈actualSlice x φ F
    rw [actualSlice_eq x φ F values H]
    simpa only [z,Function.comp_def,Equiv.apply_symm_apply] using hy
  have HF (i : Fin (n+1)) (hi : i.val<r.offset.val) :
      ((data x' hm r).scales i:ℝ)*z i=φ ((data x' hm r).heights i) := by
    have HI : i∈(permute F e).frozen := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (FrozenCoordinateOrdering.permutation_mem_iff F.frozen i).mpr hi⟩
    exact HY.2 i HI
  have Hroot:=IntegralMixedCriticalRoot.root x' hm r φ z HF HY.1 (fun i hi=>?G)
  · have HE : z (ClearedCoordinateCritical.freeIndex r.offset.val (IntegralMixedCriticalRoot.fit r).le
        (IntegralMixedCriticalRoot.coordinate r))=y j := by
      have HI:=coordinateRule_index F j hj
      exact (congrArg (fun a=>y (e a)) HI).trans (congrArg y (e.apply_symm_apply j))
    rw [HE] at Hroot
    exact Hroot
  case G =>
    let k:=ClearedCoordinateCritical.freeIndex r.offset.val (IntegralMixedCriticalRoot.fit r).le i
    have HK : e k∉F.frozen := by
      intro hk
      have HL:=(FrozenCoordinateOrdering.permutation_mem_iff F.frozen k).mp hk
      change F.frozen.card+i.val<F.frozen.card at HL
      omega
    have Hkj : e k≠j := by
      intro he
      have HE : e (ClearedCoordinateCritical.freeIndex r.offset.val (IntegralMixedCriticalRoot.fit r).le
          (IntegralMixedCriticalRoot.objective r))=j := by
        rw [coordinateRule_objective F j hj]
        exact (congrArg e (coordinateRule_index F j hj)).trans (e.apply_symm_apply j)
      have HF:=e.injective (he.trans HE.symm)
      have HV:=congrArg Fin.val HF
      apply hi
      apply Fin.ext
      change F.frozen.card+i.val=F.frozen.card+(IntegralMixedCriticalRoot.objective r).val at HV
      omega
    rw [IntegralMixedCoordinateRename.derivative_eval]
    have HZ : z ∘ e.symm=y := by funext a; exact congrArg y (e.apply_symm_apply a)
    rw [HZ]
    exact hgrad (e k) HK Hkj

end LeanCanny.Geometry.IntegralMixedFrozenFrame
