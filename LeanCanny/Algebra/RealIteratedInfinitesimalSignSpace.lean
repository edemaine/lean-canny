/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RealInfinitesimalSignSpace
/-! # Charged two-parameter coefficient-sign scans

The outer polynomial variable is the smaller parameter delta. Its coefficient
polynomials use epsilon. Every coefficient query keeps one original context.
-/
@[expose] public section
namespace LeanCanny.Algebra.RealIteratedInfinitesimalSignSpace
open Polynomial LeanCanny.Encoding LeanCanny.Computation

noncomputable def tag (p : (ℝ[X])[X]) :=RealInfinitesimalSignSpace.tag p.trailingCoeff.trailingCoeff

def inner (f : List Bool→List Bool) (epsilon : List Bool→ℕ) : List Bool→List Bool :=
  RealInfinitesimalSignSpace.value f (epsilon∘pairFst)

def value (f : List Bool→List Bool) (delta epsilon : List Bool→ℕ) :=
  RealInfinitesimalSignSpace.value (inner f epsilon) delta

theorem inner_length (f : List Bool→List Bool) (Hf : ∀ q,(f q).length≤2)
    (epsilon : List Bool→ℕ) (q : List Bool) : (inner f epsilon q).length≤2 :=
  RealInfinitesimalSignSpace.fold_length f Hf q _

theorem evaluator {f : List Bool→List Bool} (E : SpaceFunction f) (Hf : ∀ q,(f q).length≤2)
    (delta epsilon : List Bool→ℕ) (hd : BinaryFn delta) (he : BinaryFn epsilon) :
    SpaceFunction (value f delta epsilon) :=
  RealInfinitesimalSignSpace.evaluator
    (RealInfinitesimalSignSpace.evaluator E Hf (epsilon∘pairFst) (he.comp pairFst_mem_FP))
    (inner_length f Hf epsilon) delta hd

theorem value_at (f : List Bool→List Bool) (delta epsilon : List Bool→ℕ) (c : List Bool) (p : (ℝ[X])[X])
    (hd : p.natDegree≤delta c) (he : ∀ k,(p.coeff k).natDegree≤epsilon c)
    (hf : ∀ k j,f (pair (pair c (BinaryNatCode.encode k)) (BinaryNatCode.encode j))=
      RealInfinitesimalSignSpace.tag ((p.coeff k).coeff j)) : value f delta epsilon c=tag p :=by
  have HI (k : ℕ) : inner f epsilon (pair c (BinaryNatCode.encode k))=
      RealInfinitesimalSignSpace.tag (p.coeff k).trailingCoeff :=
    RealInfinitesimalSignSpace.value_at f (epsilon∘pairFst) _ (p.coeff k)
      (by simpa only [Function.comp_apply,pairFst_pair] using he k) (hf k)
  unfold value RealInfinitesimalSignSpace.value
  rw [RealInfinitesimalSignSpace.fold_scan _ c (fun k=>(p.coeff k).trailingCoeff) HI]
  by_cases hp : p=0
  · subst p
    rw [RealInfinitesimalSignSpace.scan_zero _ _ (by simp)]
    exact (RealInfinitesimalSignSpace.tag_nil _).mpr (by simp) |>.symm
  · have HN : (p.coeff p.natTrailingDegree).trailingCoeff≠0 :=
      Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp)
    exact RealInfinitesimalSignSpace.scan_first _ p.natTrailingDegree (delta c+1)
      ((p.natTrailingDegree_le_natDegree.trans hd).trans_lt (Nat.lt_succ_self _)) HN
      (fun i hi=>by rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi,Polynomial.trailingCoeff_zero])

theorem trailingCoeff_map_local {R S : Type*} [Semiring R] [Semiring S]
    (φ : R→+*S) (p : R[X]) (h : φ p.trailingCoeff≠0) : (p.map φ).trailingCoeff=φ p.trailingCoeff :=by
  have HC : (p.map φ).coeff p.natTrailingDegree≠0 :=by rwa [Polynomial.coeff_map]
  have HN : p.map φ≠0 :=by intro H; exact HC (by rw [H,Polynomial.coeff_zero])
  have HE : (p.map φ).natTrailingDegree=p.natTrailingDegree :=
    le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero HC)
      (Polynomial.le_natTrailingDegree HN (fun i hi=>by
        rw [Polynomial.coeff_map,Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi,map_zero]))
  rw [Polynomial.trailingCoeff,HE,Polynomial.coeff_map]
  rfl

theorem eventually_correct (p : (ℝ[X])[X]) : ∃ η : ℝ,0<η ∧ ∀ ε : ℝ,0<ε→ε<η→
    ∃ ζ : ℝ,0<ζ ∧ ∀ δ : ℝ,0<δ→δ<ζ→
      RealInfinitesimalSignSpace.tag (p.eval₂ (Polynomial.evalRingHom ε) δ)=tag p :=by
  by_cases hp : p=0
  · exact ⟨1,by norm_num,fun _ _ _=>⟨1,by norm_num,fun _ _ _=>by simp [hp,tag,RealInfinitesimalSignSpace.tag]⟩⟩
  obtain ⟨η,Hη,HS⟩:=InfinitesimalSign.sign_eval_eq_trailingCoeff p.trailingCoeff
  refine ⟨η,Hη,?_⟩
  intro ε Hε Hεη
  have HE : p.trailingCoeff.eval ε≠0 :=by
    intro HZ
    have H:=HS ε Hε Hεη
    rw [HZ,sign_zero] at H
    exact (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
      (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hp)) (sign_eq_zero_iff.mp H.symm)
  obtain ⟨ζ,Hζ,HD⟩:=InfinitesimalSign.sign_eval_eq_trailingCoeff (p.map (Polynomial.evalRingHom ε))
  refine ⟨ζ,Hζ,fun δ Hδ Hδζ=>?_⟩
  have H:=HD δ Hδ Hδζ
  rw [Polynomial.eval_map,trailingCoeff_map_local (Polynomial.evalRingHom ε) p HE] at H
  exact congrArg InfinitesimalSign.encode (H.trans (HS ε Hε Hεη))

end LeanCanny.Algebra.RealIteratedInfinitesimalSignSpace
