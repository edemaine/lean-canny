/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ParameterizedSignPatterns
public import LeanCanny.Algebra.IntegerPolynomialOuterSign
/-! # Uniform sign-pattern counts at a large outer parameter

The head and queries are fixed integer bivariate polynomials. A common
coefficient-mass bound on their actual pseudo-principal tests gives one
outer cutoff. There is no interpreting hom or varying-family premise.
Constructing this presentation for a recursive framed graph is separate.
-/
@[expose] public section
namespace LeanCanny.Algebra.ParameterTarski
open Polynomial PrincipalSubresultant RootSignQueries
open scoped Classical BigOperators

private theorem natDegree_eval_outer (p : (ℤ[X])[X]) (b : ℕ)
    (hm : coefficientMass p.leadingCoeff≤2^b) (x : ℝ) (hx : (2:ℝ)^(b+1)≤x) :
    (p.map (evalHom x)).natDegree=p.natDegree :=by
  by_cases hp : p=0
  · simp [hp]
  · have hl : p.leadingCoeff≠0:=leadingCoeff_ne_zero.mpr hp
    have he:=IntegerPolynomialOuterSign.sign_after_binary_mass p.leadingCoeff b hm x hx
    have hn : evalHom x p.leadingCoeff≠0 :=by
      intro hz
      change SignType.sign (evalHom x p.leadingCoeff)=_ at he
      rw [hz,sign_zero] at he
      have HC : (p.leadingCoeff.leadingCoeff:ℝ)=0:=sign_eq_zero_iff.mp he.symm
      exact (leadingCoeff_ne_zero.mpr hl) (Int.cast_eq_zero.mp HC)
    have hc : (p.map (evalHom x)).coeff p.natDegree≠0 :=by
      rw [coeff_map,coeff_natDegree]
      exact hn
    exact le_antisymm natDegree_map_le (le_natDegree_of_ne_zero hc)

noncomputable def outerValue (p f : (ℤ[X])[X]) : ℤ :=
  if p.natDegree=0 then 0 else permanencesMinusVariations
    ((List.range (p.natDegree+1)).reverse.map fun j=>(principal p f j).leadingCoeff)

theorem query_eq_outerValue (p f : (ℤ[X])[X]) (b : ℕ) (h : Bounded p f b)
    (x : ℝ) (hx : (2:ℝ)^(b+1)≤x) :
    tarskiQuery (p.map (evalHom x)) (f.map (evalHom x))=outerValue p f :=by
  by_cases hp : p.natDegree=0
  · have hz : (p.map (evalHom x)).natDegree=0:=by
      have hd : (p.map (evalHom x)).natDegree≤p.natDegree:=natDegree_map_le
      omega
    rw [outerValue,ite_eq_left hp,eq_C_of_natDegree_eq_zero hz]
    simp only [tarskiQuery,roots_C,signSum,Multiset.toFinset_zero,Finset.sum_empty]
  · have hd:=natDegree_eval_outer p b h.head x hx
    have hn:=natDegree_eval_outer (seed p f) b h.seed x hx
    have hD : (f.map (evalHom x)*(p.map (evalHom x)).derivative).natDegree≤p.natDegree+f.natDegree :=by
      have hf : (f.map (evalHom x)).natDegree≤f.natDegree:=natDegree_map_le
      have hpd :=(natDegree_derivative_le (p.map (evalHom x))).trans (Nat.sub_le _ _)
      exact natDegree_mul_le.trans (by omega)
    rw [tarskiQuery_eq_pseudoPrincipalQuery _ _ _ _ hd (by omega) hD,
      PseudoRemainder.principalQuery,PseudoRemainder.seed_map]
    change permanencesMinusVariations ((List.range (p.natDegree+1)).reverse.map
      (signedPsc (p.map (evalHom x)) ((seed p f).map (evalHom x)) p.natDegree
        ((seed p f).map (evalHom x)).natDegree))=_
    rw [hn,outerValue,ite_eq_right hp]
    apply permanencesMinusVariations_congr
    simp only [List.map_map]
    apply List.map_congr_left
    intro j hj
    have hj' : j≤p.natDegree:=by have H:=List.mem_range.mp (List.mem_reverse.mp hj);omega
    change SignType.sign (signedPsc (p.map (evalHom x)) ((seed p f).map (evalHom x))
      p.natDegree (seed p f).natDegree j)=SignType.sign (principal p f j).leadingCoeff
    rw [signedPsc_map_map]
    simpa only [principal,evalHom,Polynomial.coe_eval₂RingHom,sign_intCast] using
      IntegerPolynomialOuterSign.sign_after_binary_mass (principal p f j) b (h.principal j hj') x hx

theorem query_stable_outer (p f : (ℤ[X])[X]) (b : ℕ) (h : Bounded p f b)
    (x y : ℝ) (hx : (2:ℝ)^(b+1)≤x) (hy : (2:ℝ)^(b+1)≤y) :
    tarskiQuery (p.map (evalHom x)) (f.map (evalHom x))=
      tarskiQuery (p.map (evalHom y)) (f.map (evalHom y)) :=
  (query_eq_outerValue p f b h x hx).trans (query_eq_outerValue p f b h y hy).symm

/-- Every distinct-root sign-pattern count agrees beyond one actual test-mass
bound. The size of the finite feature set need not be unary or small. The zero
head uses the finite-root convention, not its infinite real zero set. -/
theorem rootCount_stable_outer {J : Type*} [Fintype J]
    (p : (ℤ[X])[X]) (Q : J→(ℤ[X])[X]) (b : ℕ)
    (h : ∀ e : J→Fin 3,Bounded p (queryPolynomial Q e) b)
    (x y : ℝ) (hx : (2:ℝ)^(b+1)≤x) (hy : (2:ℝ)^(b+1)≤y) (σ : J→SignType) :
    signCount (p.map (evalHom x)).roots.toFinset (fun i=>(Q i).map (evalHom x)) σ=
      signCount (p.map (evalHom y)).roots.toFinset (fun i=>(Q i).map (evalHom y)) σ :=by
  have HE : scaledRootCount (p.map (evalHom x)) (fun i=>(Q i).map (evalHom x)) σ=
      scaledRootCount (p.map (evalHom y)) (fun i=>(Q i).map (evalHom y)) σ :=by
    unfold scaledRootCount
    apply Finset.sum_congr rfl
    intro e _
    rw [←map_queryPolynomial,←map_queryPolynomial]
    exact congrArg (patternWeight σ e*·) (query_stable_outer p (queryPolynomial Q e) b (h e) x y hx hy)
  rw [scaledRootCount_eq,scaledRootCount_eq] at HE
  exact Int.natCast_inj.mp (mul_left_cancel₀ (pow_ne_zero _ (by decide : (2:ℤ)≠0)) HE)

end LeanCanny.Algebra.ParameterTarski
