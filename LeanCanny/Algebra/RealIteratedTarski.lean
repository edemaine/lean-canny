/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RealIteratedInfinitesimalSignFinite
public import LeanCanny.Algebra.PseudoRemainderQuery
/-! # Selected real Tarski queries with delta smaller than epsilon

Declared outer degrees are semantic identities for the actual head and seed.
All required coefficient signs stabilize on one ordered parameter region.
-/
@[expose] public section
namespace LeanCanny.Algebra.RealIteratedTarski
open Polynomial PrincipalSubresultant
open scoped Classical

noncomputable def evaluate (ε δ : ℝ) : ((ℝ[X])[X])→+*ℝ :=
  (Polynomial.evalRingHom δ).comp (Polynomial.mapRingHom (Polynomial.evalRingHom ε))

theorem evaluate_apply (ε δ : ℝ) (p : (ℝ[X])[X]) :
    evaluate ε δ p=p.eval₂ (Polynomial.evalRingHom ε) δ :=by
  rw [evaluate,RingHom.comp_apply,Polynomial.coe_mapRingHom,Polynomial.coe_evalRingHom,Polynomial.eval_map]

noncomputable def lex (p : (ℝ[X])[X]) :=p.trailingCoeff.trailingCoeff

noncomputable def seed (p f : ((ℝ[X])[X])[X]) (d D : ℕ) :=PseudoRemainder.seed p f d D
noncomputable def principal (p f : ((ℝ[X])[X])[X]) (d D s j : ℕ) :=signedPsc p (seed p f d D) d s j
noncomputable def tests (p f : ((ℝ[X])[X])[X]) (d D s : ℕ) : List ((ℝ[X])[X]) :=
  p.coeff d::(seed p f d D).coeff s::(List.range (d+1)).map (principal p f d D s)
noncomputable def value (p f : ((ℝ[X])[X])[X]) (d D s : ℕ) : ℤ :=
  permanencesMinusVariations ((List.range (d+1)).reverse.map (fun j=>lex (principal p f d D s j)))

theorem degree_eval (p : ((ℝ[X])[X])[X]) (ε δ : ℝ)
    (hs : SignType.sign (evaluate ε δ p.leadingCoeff)=SignType.sign (lex p.leadingCoeff)) :
    (p.map (evaluate ε δ)).natDegree=p.natDegree :=by
  by_cases hp : p=0
  · subst p
    rw [Polynomial.map_zero,Polynomial.natDegree_zero,Polynomial.natDegree_zero]
  have HN : lex p.leadingCoeff≠0 :=Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
    (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp))
  have HE : evaluate ε δ p.leadingCoeff≠0 :=by
    intro HZ
    rw [HZ,sign_zero] at hs
    exact HN (sign_eq_zero_iff.mp hs.symm)
  have HC : (p.map (evaluate ε δ)).coeff p.natDegree≠0 :=by
    rw [Polynomial.coeff_map,Polynomial.coeff_natDegree]
    exact HE
  exact le_antisymm Polynomial.natDegree_map_le (Polynomial.le_natDegree_of_ne_zero HC)

theorem query_eq_value (p f : ((ℝ[X])[X])[X]) (d D s : ℕ) (hd : 0<d)
    (hp : p.natDegree=d) (hseed : (seed p f d D).natDegree=s)
    (hD : (f*p.derivative).natDegree≤D) (ε δ : ℝ)
    (hs : ∀ q∈tests p f d D s,SignType.sign (evaluate ε δ q)=SignType.sign (lex q)) :
    RootSignQueries.tarskiQuery (p.map (evaluate ε δ)) (f.map (evaluate ε δ))=value p f d D s :=by
  have HPlead : SignType.sign (evaluate ε δ p.leadingCoeff)=SignType.sign (lex p.leadingCoeff) :=by
    simpa only [Polynomial.leadingCoeff,hp] using (hs _ List.mem_cons_self)
  have HP : (p.map (evaluate ε δ)).natDegree=d :=(degree_eval p ε δ HPlead).trans hp
  have HSlead : SignType.sign (evaluate ε δ (seed p f d D).leadingCoeff)=
      SignType.sign (lex (seed p f d D).leadingCoeff) :=by
    simpa only [Polynomial.leadingCoeff,hseed] using (hs _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have HS : ((seed p f d D).map (evaluate ε δ)).natDegree=s :=
    (degree_eval (seed p f d D) ε δ HSlead).trans hseed
  have HF : ((f.map (evaluate ε δ))*(p.map (evaluate ε δ)).derivative).natDegree≤D :=by
    rw [Polynomial.derivative_map,←Polynomial.map_mul]
    exact Polynomial.natDegree_map_le.trans hD
  rw [RootSignQueries.tarskiQuery_eq_pseudoPrincipalQuery _ _ d D HP hd HF,
    PseudoRemainder.principalQuery,PseudoRemainder.seed_map]
  change permanencesMinusVariations ((List.range (d+1)).reverse.map
    (signedPsc (p.map (evaluate ε δ)) ((seed p f d D).map (evaluate ε δ))
      d ((seed p f d D).map (evaluate ε δ)).natDegree))=_
  rw [HS]
  apply permanencesMinusVariations_congr
  simp only [List.map_map]
  apply List.map_congr_left
  intro j hj
  change SignType.sign (signedPsc (p.map (evaluate ε δ)) ((seed p f d D).map (evaluate ε δ)) d s j)=
    SignType.sign (lex (principal p f d D s j))
  rw [signedPsc_map_map]
  exact hs _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr
    ⟨j,List.mem_reverse.mp hj,rfl⟩)))

theorem eventually_query_eq_value (p f : ((ℝ[X])[X])[X]) (d D s : ℕ) (hd : 0<d)
    (hp : p.natDegree=d) (hseed : (seed p f d D).natDegree=s)
    (hD : (f*p.derivative).natDegree≤D) : ∃ η : ℝ,0<η ∧ ∀ ε : ℝ,0<ε→ε<η→
      ∃ ζ : ℝ,0<ζ ∧ ∀ δ : ℝ,0<δ→δ<ζ→
        RootSignQueries.tarskiQuery (p.map (evaluate ε δ)) (f.map (evaluate ε δ))=value p f d D s :=by
  obtain ⟨η,Hη,HS⟩:=RealIteratedInfinitesimalSignSpace.finite_sign_correct (tests p f d D s).toFinset id
  refine ⟨η,Hη,fun ε Hε Hεη=>?_⟩
  obtain ⟨ζ,Hζ,HD⟩:=HS ε Hε Hεη
  exact ⟨ζ,Hζ,fun δ Hδ Hδζ=>query_eq_value p f d D s hd hp hseed hD ε δ
    (fun q hq=>by simpa only [id_eq,←evaluate_apply,lex] using HD q (List.mem_toFinset.mpr hq) δ Hδ Hδζ)⟩

end LeanCanny.Algebra.RealIteratedTarski
