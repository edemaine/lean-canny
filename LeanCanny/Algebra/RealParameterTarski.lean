/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.InfinitesimalSign
public import LeanCanny.Algebra.PseudoRemainderQuery

/-! # Eventual parameter Tarski queries over a selected real coefficient field

Finite leading/principal tests supply a common interval of validity. The
coefficients may be real algebraic values from one fixed old hom; no integer
mass bound or absolute norm-root identification is required for this semantic
statement. Native access to these selected coefficient signs is separate.
-/
@[expose] public section
namespace LeanCanny.Algebra.RealParameterTarski
open Polynomial PrincipalSubresultant
open scoped Classical

noncomputable def seed (p f : (ℝ[X])[X]) :=
  PseudoRemainder.seed p f p.natDegree (p.natDegree+f.natDegree)

noncomputable def principal (p f : (ℝ[X])[X]) (j : ℕ) : ℝ[X] :=
  signedPsc p (seed p f) p.natDegree (seed p f).natDegree j

noncomputable def tests (p f : (ℝ[X])[X]) : List ℝ[X] :=
  p.leadingCoeff::(seed p f).leadingCoeff::(List.range (p.natDegree+1)).map (principal p f)

noncomputable def value (p f : (ℝ[X])[X]) : ℤ :=
  if p.natDegree=0 then 0 else permanencesMinusVariations
    ((List.range (p.natDegree+1)).reverse.map (fun j=>(principal p f j).trailingCoeff))

theorem natDegree_eval (p : (ℝ[X])[X]) (x : ℝ)
    (hs : SignType.sign (p.leadingCoeff.eval x)=SignType.sign p.leadingCoeff.trailingCoeff) :
    (p.map (Polynomial.evalRingHom x)).natDegree=p.natDegree := by
  by_cases hp : p=0
  · subst p
    rw [Polynomial.map_zero,Polynomial.natDegree_zero,Polynomial.natDegree_zero]
  have HL : p.leadingCoeff.trailingCoeff≠0:=Polynomial.trailingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have HE : p.leadingCoeff.eval x≠0 := by
    intro Hzero
    rw [Hzero,sign_zero] at hs
    exact HL (sign_eq_zero_iff.mp hs.symm)
  have HC : (p.map (Polynomial.evalRingHom x)).coeff p.natDegree≠0 := by
    rw [Polynomial.coeff_map,Polynomial.coeff_natDegree]
    exact HE
  exact le_antisymm Polynomial.natDegree_map_le (Polynomial.le_natDegree_of_ne_zero HC)

theorem query_eq_value (p f : (ℝ[X])[X]) (x : ℝ)
    (hs : ∀ q∈tests p f,SignType.sign (q.eval x)=SignType.sign q.trailingCoeff) :
    RootSignQueries.tarskiQuery (p.map (Polynomial.evalRingHom x)) (f.map (Polynomial.evalRingHom x))=value p f := by
  by_cases hp : p.natDegree=0
  · have HD : (p.map (Polynomial.evalRingHom x)).natDegree=0:=by have H:=Polynomial.natDegree_map_le (p:=p) (f:=Polynomial.evalRingHom x); omega
    rw [value,ite_eq_left hp,Polynomial.eq_C_of_natDegree_eq_zero HD]
    simp only [RootSignQueries.tarskiQuery,Polynomial.roots_C,RootSignQueries.signSum,Multiset.toFinset_zero,Finset.sum_empty]
  have HD:=natDegree_eval p x (hs _ List.mem_cons_self)
  have Hseed:=natDegree_eval (seed p f) x (hs _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have HF : ((f.map (Polynomial.evalRingHom x))*(p.map (Polynomial.evalRingHom x)).derivative).natDegree≤p.natDegree+f.natDegree := by
    have Hf : (f.map (Polynomial.evalRingHom x)).natDegree≤f.natDegree:=Polynomial.natDegree_map_le
    have Hp := (Polynomial.natDegree_derivative_le (p.map (Polynomial.evalRingHom x))).trans (Nat.sub_le _ _)
    exact Polynomial.natDegree_mul_le.trans (by omega)
  rw [RootSignQueries.tarskiQuery_eq_pseudoPrincipalQuery _ _ _ _ HD (by omega) HF,
    PseudoRemainder.principalQuery,PseudoRemainder.seed_map]
  change permanencesMinusVariations ((List.range (p.natDegree+1)).reverse.map
    (signedPsc (p.map (Polynomial.evalRingHom x)) ((seed p f).map (Polynomial.evalRingHom x))
      p.natDegree ((seed p f).map (Polynomial.evalRingHom x)).natDegree))=_
  rw [Hseed,value,ite_eq_right hp]
  apply permanencesMinusVariations_congr
  simp only [List.map_map]
  apply List.map_congr_left
  intro j hj
  have HJ : j<p.natDegree+1:=List.mem_range.mp (List.mem_reverse.mp hj)
  change SignType.sign (signedPsc (p.map (Polynomial.evalRingHom x)) ((seed p f).map (Polynomial.evalRingHom x))
    p.natDegree (seed p f).natDegree j)=SignType.sign (principal p f j).trailingCoeff
  rw [signedPsc_map_map]
  exact hs _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,List.mem_range.mpr HJ,rfl⟩)))

theorem eventual_query_eq_value (p f : (ℝ[X])[X]) :
    ∃ δ : ℝ,0<δ ∧ ∀ x,0<x→x<δ→
      RootSignQueries.tarskiQuery (p.map (Polynomial.evalRingHom x)) (f.map (Polynomial.evalRingHom x))=value p f := by
  obtain ⟨δ,Hδ,HS⟩:=InfinitesimalSign.finite_sign_eval_eq_trailingCoeff (tests p f).toFinset id
  exact ⟨δ,Hδ,fun x Hx Hδx=>query_eq_value p f x (fun q Hq=>HS q (List.mem_toFinset.mpr Hq) x Hx Hδx)⟩

theorem selected_eventual {A : Type} [CommRing A] (φ : A→+*ℝ) (p f : Polynomial (Polynomial A)) :
    ∃ δ : ℝ,0<δ ∧ ∀ x,0<x→x<δ→
      RootSignQueries.tarskiQuery
        ((p.map (Polynomial.mapRingHom φ)).map (Polynomial.evalRingHom x))
        ((f.map (Polynomial.mapRingHom φ)).map (Polynomial.evalRingHom x))=
      value (p.map (Polynomial.mapRingHom φ)) (f.map (Polynomial.mapRingHom φ)) :=
  eventual_query_eq_value _ _

end LeanCanny.Algebra.RealParameterTarski
