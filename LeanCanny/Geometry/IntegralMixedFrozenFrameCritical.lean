/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameSweep
public import LeanCanny.Algebra.IntegralMixedCoordinateRenameDerivative

/-! # Actual critical-coordinate readback after frozen-first ordering -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def freeCoordinate (F : Frame n) (j : Fin (n+1)) (hj : j∉F.frozen) :
    Fin (n-F.frozen.card+1) :=
  ⟨((FrozenCoordinateOrdering.permutation F.frozen).symm j).val-F.frozen.card,by
    have H:=((FrozenCoordinateOrdering.permutation F.frozen).symm j).isLt
    have HJ : ¬((FrozenCoordinateOrdering.permutation F.frozen).symm j).val<F.frozen.card:=
      fun H=>hj ((FrozenCoordinateOrdering.inverse_mem_iff F.frozen j).mp H)
    omega⟩

theorem freeCoordinate_readback (F : Frame n) (j : Fin (n+1)) (hj : j∉F.frozen)
    (hfit : F.frozen.card+(n-F.frozen.card+1)≤n+1) :
    ClearedCoordinateCritical.freeIndex F.frozen.card hfit (freeCoordinate F j hj)=
      (FrozenCoordinateOrdering.permutation F.frozen).symm j := by
  apply Fin.ext
  have HJ : ¬((FrozenCoordinateOrdering.permutation F.frozen).symm j).val<F.frozen.card:=
    fun H=>hj ((FrozenCoordinateOrdering.inverse_mem_iff F.frozen j).mp H)
  change F.frozen.card+(((FrozenCoordinateOrdering.permutation F.frozen).symm j).val-F.frozen.card)=_
  omega

theorem objective_readback (x : State P S B m ι)
    (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen) (g : Fin (n+1)) (hg : g∉F.frozen) :
    objective (sweep x F h hh g hg)=freeCoordinate F g hg := by
  apply Fin.ext
  have HG : ¬((FrozenCoordinateOrdering.permutation F.frozen).symm g).val<F.frozen.card:=
    fun H=>hg ((FrozenCoordinateOrdering.inverse_mem_iff F.frozen g).mp H)
  have HB:=((FrozenCoordinateOrdering.permutation F.frozen).symm g).isLt
  change (((FrozenCoordinateOrdering.permutation F.frozen).symm g).val-F.frozen.card)%
    (n-F.frozen.card+1)=_
  rw [Nat.mod_eq_of_lt (by omega)]
  rfl

theorem objective_physical (x : State P S B m ι)
    (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen) (g : Fin (n+1)) (hg : g∉F.frozen) :
    FrozenCoordinateOrdering.permutation F.frozen
      (ClearedCoordinateCritical.freeIndex (sweep x F h hh g hg).critical.offset.val
        (fit (sweep x F h hh g hg)).le (objective (sweep x F h hh g hg)))=g := by
  let e:=FrozenCoordinateOrdering.permutation F.frozen
  have HE : ClearedCoordinateCritical.freeIndex (sweep x F h hh g hg).critical.offset.val
      (fit (sweep x F h hh g hg)).le (objective (sweep x F h hh g hg))=e.symm g := by
    apply Fin.ext
    have HG : ¬(e.symm g).val<F.frozen.card:=
      fun H=>hg ((FrozenCoordinateOrdering.inverse_mem_iff F.frozen g).mp H)
    have HB:=(e.symm g).isLt
    change F.frozen.card+((e.symm g).val-F.frozen.card)%(n-F.frozen.card+1)=_
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  exact (congrArg e HE).trans (e.apply_symm_apply g)

/-- A critical point in the original coarse fiber gives actual selected coordinate roots.
The old hom is fixed; only spatial names are permuted. -/
theorem selected_coordinate_root (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (g : Fin (n+1)) (hg : g∉F.frozen) (values : Fin m→ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (y : Fin (n+1)→ℝ)
    (hy : y∈slice P (coarse F h) values∩{y | projection F values h y=t})
    (hgrad : ∀ j, j∉F.frozen→j≠g→
      (MvPolynomial.pderiv j (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) y=0)
    (j : Fin (n+1)) (hj : j∉F.frozen) :
    let e:=FrozenCoordinateOrdering.permutation F.frozen
    let x':=IntegralMixedCoordinateRename.state x e
    (selected x' hm (sweep x F h hh g hg) (freeCoordinate F j hj) φ).eval₂
      (Polynomial.evalRingHom t) (y j)=0 := by
  let e:=FrozenCoordinateOrdering.permutation F.frozen
  let r:=sweep x F h hh g hg
  let x':=IntegralMixedCoordinateRename.state x e
  let z:=y ∘ e
  have hz : z∈sweepSlice x hm φ F h hh g hg t := by
    rw [sweepSlice_eq x hm φ F h hh g hg values H t]
    change ((y ∘ e) ∘ e.symm)∈slice P (coarse F h) values∩{y | projection F values h y=t}
    simpa only [Function.comp_def,Equiv.apply_symm_apply] using hy
  have Hroot:=coordinate_root x' hm r (freeCoordinate F j hj) φ t z hz.2 hz.1 (fun i hi=>?G)
  · have HE : z (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le
        (freeCoordinate F j hj))=y j := by
      have HK : ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le
          (freeCoordinate F j hj)=e.symm j := by
        apply Fin.ext
        have HJ : ¬(e.symm j).val<F.frozen.card:=
          fun H=>hj ((FrozenCoordinateOrdering.inverse_mem_iff F.frozen j).mp H)
        change F.frozen.card+((e.symm j).val-F.frozen.card)=_
        omega
      exact (congrArg (fun a=>y (e a)) HK).trans (congrArg y (e.apply_symm_apply j))
    rw [HE] at Hroot
    exact Hroot
  case G =>
    let k:=ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i
    have HK : e k∉F.frozen := by
      intro hk
      have HL:=(FrozenCoordinateOrdering.permutation_mem_iff F.frozen k).mp hk
      change F.frozen.card+i.val<F.frozen.card at HL
      omega
    have Hkg : e k≠g := by
      intro he
      have HE:=objective_physical x F h hh g hg
      have HF:=e.injective (he.trans HE.symm)
      have HV:=congrArg Fin.val HF
      apply hi
      apply Fin.ext
      change F.frozen.card+i.val=F.frozen.card+(objective r).val at HV
      omega
    rw [IntegralMixedCoordinateRename.derivative_eval]
    have HZ : z ∘ e.symm=y := by funext a; exact congrArg y (e.apply_symm_apply a)
    rw [HZ]
    exact hgrad (e k) HK Hkg

end LeanCanny.Geometry.IntegralMixedFrozenFrame
