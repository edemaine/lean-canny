/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameHeightCut

/-! # Free-slot normal form reduces new sweep cuts to ordinary relative roots -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

def FreeNormal (F : Frame n) : Prop := ∀ i,i∉F.frozen→F.scales i=1 ∧ F.heights i=.constant 0

def line (F : Frame n) (h : Fin (n+1)) : Frame n := {F with frozen:=insert h F.frozen}

theorem coarse_line (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen) : coarse (line F h) h=F := by
  cases F
  simp only [line,coarse,Finset.erase_insert hh]

theorem FreeNormal.advance {F : Frame n} (H : FreeNormal F) (h : Fin (n+1)) : FreeNormal (advance F h) := by
  intro i hi
  have HI : i≠h ∧ i∉F.frozen:=by simpa only [IntegralMixedFrozenFrame.advance,Finset.mem_insert,not_or] using hi
  obtain ⟨HS,HH⟩:=H i HI.2
  simp only [IntegralMixedFrozenFrame.advance,ite_eq_right HI.1,HS,HH,later,and_self]

theorem FreeNormal.level {F : Frame n} (H : FreeNormal F) (h : Fin (n+1)) : FreeNormal (level F h) := by
  intro i hi
  have HI : i≠h ∧ i∉F.frozen:=by simpa only [IntegralMixedFrozenFrame.level,Finset.mem_insert,not_or] using hi
  obtain ⟨HS,HH⟩:=H i HI.2
  simp only [IntegralMixedFrozenFrame.level,ite_eq_right HI.1,HS,HH,later,and_self]

theorem line_projection {k : ℕ} (F : Frame n) (h : Fin (n+1)) (HH : F.scales h=1 ∧ F.heights h=.constant 0)
    (values : Fin k→ℝ) (y : Fin (n+1)→ℝ) : projection (line F h) values h y=y h := by
  simp only [projection,line,HH.1,HH.2,AffineExpr.evaluate,Int.cast_one,one_mul,Int.cast_zero,sub_zero]

theorem line_cut_eval (x : State P S B m ι) (hm : m≤S) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (h : Fin (n+1)) (HH : F.scales h=1 ∧ F.heights h=.constant 0) (t : ℝ) :
    (heightCut x hm (line F h) h).eval₂ φ.toRingHom t=
      (commonDenominator x:ℝ)^heightDegree x hm (line F h) h *
        (heightRelative x hm (line F h) h).eval₂ φ.toRingHom t := by
  have HQ : φ.toRingHom ((commonDenominator x*F.scales h:ℤ):x.sampler.scalarPrefix.carrier)≠0 := by
    rw [HH.1,mul_one,map_intCast]
    exact Int.cast_ne_zero.mpr (commonDenominator_ne_zero x)
  have HE:=ClearedAffinePolynomial.eval φ.toRingHom (heightDegree x hm (line F h) h)
    (heightRelative x hm (line F h) h) (expression x (F.heights h))
    (commonDenominator x : x.sampler.scalarPrefix.carrier)
    ((commonDenominator x*F.scales h:ℤ):x.sampler.scalarPrefix.carrier)
    (heightRelative_degree x hm (line F h) h) HQ t
  change (heightCut x hm (line F h) h).eval₂ φ.toRingHom t=_ at HE
  have Hnz : (commonDenominator x:ℝ)≠0:=Int.cast_ne_zero.mpr (commonDenominator_ne_zero x)
  simpa only [HH.1,HH.2,expression,mul_one,Int.cast_zero,mul_zero,map_zero,map_intCast,zero_add,mul_div_cancel_left₀ _ Hnz] using HE

theorem line_cut_root_iff (x : State P S B m ι) (hm : m≤S) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (h : Fin (n+1)) (HH : F.scales h=1 ∧ F.heights h=.constant 0) (t : ℝ) :
    (heightCut x hm (line F h) h).eval₂ φ.toRingHom t=0↔
      (heightRelative x hm (line F h) h).eval₂ φ.toRingHom t=0 := by
  rw [line_cut_eval x hm φ F h HH t]
  exact mul_eq_zero_iff_left (pow_ne_zero _ (Int.cast_ne_zero.mpr (commonDenominator_ne_zero x)))

end LeanCanny.Geometry.IntegralMixedFrozenFrame
