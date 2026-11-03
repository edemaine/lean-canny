/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFramePointReadback
public import LeanCanny.Geometry.IntegralMixedFrozenFrameCutContinue
public import LeanCanny.Connectivity.IntegralMixedSelectedPhysicalFiber
/-! # A retained midpoint point-rule block anchors the earlier virtual sweep

The two banks retain the same old values and one midpoint head. Their
clearing integers may differ. Frozen equations are transported through the
actual advance frame; no old hom extension or annihilator lift is assumed.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι κ : Type}

theorem advance_point_anchors_sweep (x : State P S B m ι) (hm : m≤S)
    (next : State P S B (m+1) κ) (hnm : m+1≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : next.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F)
    (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (j : Fin (n+1)) (hj : j∉(line F h).frozen)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (midpoint : ℝ) (HN : ∀i,ψ (next.bank.numerator i)/(next.bank.denominator i:ℝ)=(Fin.cons midpoint values : Fin (m+1)→ℝ) i)
    (a : Fin (n+1)→ℝ)
    (HA : IntegralMixedCriticalReadback.CriticalPoint
      (IntegralMixedCoordinateRename.state next (FrozenCoordinateOrdering.permutation (advance F h).frozen)) hnm
      (pointRule (advance F h) g hg j hj) ψ a) :
    a∈IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ midpoint :=by
  let e:=FrozenCoordinateOrdering.permutation (line F h).frozen
  let r:=cutRule x F h g hg
  let y:=a∘e.symm
  have HY:=pointRule_readback next hnm ψ (advance F h) g hg j hj (Fin.cons midpoint values) HN a HA
  have HS : y∈slice P F values∩{y | y h=midpoint}:=by
    exact (Set.ext_iff.mp (slice_advance P F h hh values midpoint) y).mp HY.1
  have HC : y∈slice P (coarse (line F h) h) values∩{y | projection (line F h) values h y=midpoint}:=by
    rw [coarse_line F h hh]
    exact ⟨HS.1,(line_projection F h (HF h hh) values y).trans HS.2⟩
  have HW : a∈sweepSlice x hm φ (line F h) h (Finset.mem_insert_self h F.frozen) g hg midpoint:=by
    rw [sweepSlice_eq x hm φ (line F h) h (Finset.mem_insert_self h F.frozen) g hg values H midpoint]
    exact HC
  refine ⟨HW.2,fun k=>?_⟩
  unfold IntegralMixedSweepRows.integerRow
  split_ifs with hk
  · exact HW.1
  · let index:=ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le k
    have HI : e index∉(advance F h).frozen:=by
      intro hi
      have HL:=(FrozenCoordinateOrdering.permutation_mem_iff (line F h).frozen index).mp hi
      change (line F h).frozen.card+k.val<(line F h).frozen.card at HL
      omega
    have Hne : e index≠g:=by
      intro HE
      have HO:=objective_physical x (line F h) h (Finset.mem_insert_self h F.frozen) g hg
      have HK:=e.injective (HE.trans HO.symm)
      have HV:=congrArg Fin.val HK
      apply hk
      apply Fin.ext
      change (line F h).frozen.card+k.val=(line F h).frozen.card+(objective r).val at HV
      exact Nat.add_left_cancel HV
    have HG:=HY.2 (e index) HI Hne
    rw [IntegralMixedCoordinateRename.derivative_eval P e index a]
    exact HG

end LeanCanny.Geometry.IntegralMixedFrozenFrame
