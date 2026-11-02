/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RealIteratedInfinitesimalSignSpace
/-! # One ordered parameter neighborhood for finitely many principal tests -/
@[expose] public section
namespace LeanCanny.Algebra.RealIteratedInfinitesimalSignSpace
open Polynomial

private theorem encode_injective : Function.Injective InfinitesimalSign.encode :=by
  intro a b H
  cases a <;> cases b <;> simp_all [InfinitesimalSign.encode]

theorem eventually_sign_correct (p : (ℝ[X])[X]) : ∃ η : ℝ,0<η ∧ ∀ ε : ℝ,0<ε→ε<η→
    ∃ ζ : ℝ,0<ζ ∧ ∀ δ : ℝ,0<δ→δ<ζ→
      SignType.sign (p.eval₂ (Polynomial.evalRingHom ε) δ)=SignType.sign p.trailingCoeff.trailingCoeff :=by
  obtain ⟨η,Hη,HS⟩:=eventually_correct p
  refine ⟨η,Hη,fun ε Hε Hεη=>?_⟩
  obtain ⟨ζ,Hζ,HD⟩:=HS ε Hε Hεη
  exact ⟨ζ,Hζ,fun δ Hδ Hδζ=>encode_injective (HD δ Hδ Hδζ)⟩

theorem finite_sign_correct {J : Type*} (s : Finset J) (p : J→(ℝ[X])[X]) :
    ∃ η : ℝ,0<η ∧ ∀ ε : ℝ,0<ε→ε<η→∃ ζ : ℝ,0<ζ ∧
      ∀ j∈s,∀ δ : ℝ,0<δ→δ<ζ→
        SignType.sign ((p j).eval₂ (Polynomial.evalRingHom ε) δ)=SignType.sign (p j).trailingCoeff.trailingCoeff :=by
  classical
  induction s using Finset.induction_on with
  | empty=>exact ⟨1,by norm_num,fun _ _ _=>⟨1,by norm_num,by simp⟩⟩
  | @insert j s hj ih=>
    obtain ⟨η,Hη,HS⟩:=ih
    obtain ⟨ηj,Hηj,HSj⟩:=eventually_sign_correct (p j)
    refine ⟨min η ηj,lt_min Hη Hηj,fun ε Hε Hεη=>?_⟩
    obtain ⟨ζ,Hζ,HD⟩:=HS ε Hε (Hεη.trans_le (min_le_left _ _))
    obtain ⟨ζj,Hζj,HDj⟩:=HSj ε Hε (Hεη.trans_le (min_le_right _ _))
    refine ⟨min ζ ζj,lt_min Hζ Hζj,?_⟩
    intro i hi δ Hδ Hδζ
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact HDj δ Hδ (Hδζ.trans_le (min_le_right _ _))
    · exact HD i hi δ Hδ (Hδζ.trans_le (min_le_left _ _))

end LeanCanny.Algebra.RealIteratedInfinitesimalSignSpace
