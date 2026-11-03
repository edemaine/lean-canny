/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCriticalReadback
public import LeanCanny.Geometry.IntegralMixedFrozenFramePointScalar
/-! # A literal point-rule block recovers the original frozen-frame point

This is the inverse readback for the actual frozen-first coordinate
permutation. No absolute annihilator root is lifted to a physical point.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory MvPolynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem pointRule_readback (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n)
    (g : Fin (n+1)) (hg : g∉F.frozen) (j : Fin (n+1)) (hj : j∉F.frozen)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : Fin (n+1)→ℝ)
    (ha : IntegralMixedCriticalReadback.CriticalPoint
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm
      (pointRule F g hg j hj) φ a) :
    (a∘(FrozenCoordinateOrdering.permutation F.frozen).symm)∈slice P F values ∧
    ∀i,i∉F.frozen→i≠g→
      (pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ)
        (a∘(FrozenCoordinateOrdering.permutation F.frozen).symm)=0 :=by
  let e:=FrozenCoordinateOrdering.permutation F.frozen
  let r:=pointRule F g hg j hj
  let x':=IntegralMixedCoordinateRename.state x e
  rcases ha with ⟨hp,hf,hgrad⟩
  have HO : e (data x' hm r).free=g :=by
    have HE : (data x' hm r).free=e.symm g :=by
      apply Fin.ext
      have HG : ¬(e.symm g).val<F.frozen.card:=
        fun h=>hg ((FrozenCoordinateOrdering.inverse_mem_iff F.frozen g).mp h)
      have HB:=(e.symm g).isLt
      change F.frozen.card+((e.symm g).val-F.frozen.card)%(n-F.frozen.card+1)=(e.symm g).val
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    exact (congrArg e HE).trans (e.apply_symm_apply g)
  refine ⟨⟨(IntegralMixedCoordinateRename.source_eval P e a).symm.trans hp,?_⟩,?_⟩
  · intro i hi
    have Hk : (e.symm i).val<r.offset.val:=(FrozenCoordinateOrdering.inverse_mem_iff F.frozen i).mpr hi
    have HF:=hf (e.symm i) Hk
    change ((commonDenominator x*F.scales (e (e.symm i)):ℤ):ℝ)*a (e.symm i)=
      φ (expression x' (F.heights (e (e.symm i)))) at HF
    rw [e.apply_symm_apply,IntegralMixedCoordinateRename.expression_eq] at HF
    exact (constraint_iff x φ F values H (a∘e.symm) i).mp HF
  · intro i hi hig
    have Hk : r.offset.val ≤ (e.symm i).val:=by
      have HK : ¬(e.symm i).val<F.frozen.card:=
        fun h=>hi ((FrozenCoordinateOrdering.inverse_mem_iff F.frozen i).mp h)
      change F.frozen.card ≤ (e.symm i).val
      omega
    have Hne : e.symm i≠(data x' hm r).free :=by
      intro HE
      have HH:=(congrArg e HE).trans HO
      exact hig ((e.apply_symm_apply i).symm.trans HH)
    have HG:=hgrad (e.symm i) Hk Hne
    rw [IntegralMixedCoordinateRename.derivative_eval P e (e.symm i) a] at HG
    simpa only [Equiv.apply_symm_apply] using HG

theorem pointRule_selected_readback (F : Frame n)
    (g : Fin (n+1)) (hg : g∉F.frozen) (j : Fin (n+1)) (hj : j∉F.frozen) (a : Fin (n+1)→ℝ) :
    a (ClearedCoordinateCritical.freeIndex (pointRule F g hg j hj).offset.val
      (IntegralMixedCriticalRoot.fit (pointRule F g hg j hj)).le
      (IntegralMixedCriticalRoot.coordinate (pointRule F g hg j hj)))=
        (a∘(FrozenCoordinateOrdering.permutation F.frozen).symm) j :=by
  rw [pointRule_index F g hg j hj]
  rfl

end LeanCanny.Geometry.IntegralMixedFrozenFrame
