/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNumericalSweepComparison
public import LeanCanny.Algebra.PurePowerAnnihilatorMap
/-! # Selected coordinate polynomials at equal numerical frozen slices

The sweep parameters and integer scales may differ. Only their specialized
normalized frozen heights are compared; complete sample words are not moved.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNumericalSweep
open IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ClearedCoordinateCritical.annihilator
variable {n m l : ℕ}

noncomputable def coordinateAt (P : SpatialSource n) (r : Rule n)
    (values : Fin m→ℝ) (t : ℝ) (j : Fin (n-r.critical.offset.val+1)) : Polynomial ℝ :=
  ClearedCoordinateCritical.annihilator P.degree 1 (fun i=>(normalized r values i).eval t)
    r.critical.offset.val (fit r).le (P.low.map (Int.castRingHom ℝ))
    (P.leading:ℝ) (objective r) j

theorem coordinate_specialize (P : SpatialSource n) (r : Rule n)
    (values : Fin m→ℝ) (t : ℝ) (j : Fin (n-r.critical.offset.val+1)) :
    (coordinate P r values j).map (evalRingHom t)=coordinateAt P r values t j :=by
  unfold coordinate coordinateAt
  rw [PurePowerAnnihilatorMap.cleared]
  have HF : (evalRingHom t).comp (Int.castRingHom (Polynomial ℝ))=Int.castRingHom ℝ:=Subsingleton.elim _ _
  simp only [map_one,Polynomial.coe_evalRingHom,eval_intCast,MvPolynomial.map_map,HF]

theorem normalized_eval (r : Rule n) (values : Fin m→ℝ) (t : ℝ) (i : Fin (n+1)) :
    (normalized r values i.val).eval t=
      ((r.critical.heights i).evaluate values+if i=r.height then t else 0)/
        (r.critical.scales i:ℝ) :=by
  rw [normalized_at]
  by_cases hi : i=r.height
  · simp only [hi,ite_true,eval_add,eval_C,eval_mul,eval_X,div_eq_mul_inv]
    ring
  · simp only [ite_eq_right hi,eval_C,add_zero]

theorem coordinateAt_congr (P : SpatialSource n) (r s : Rule n)
    (hoff : r.critical.offset=s.critical.offset)
    (hobj : r.critical.objective=s.critical.objective)
    (values : Fin m→ℝ) (other : Fin l→ℝ) (t u : ℝ)
    (H : ∀i,i<r.critical.offset.val→
      (normalized r values i).eval t=(normalized s other i).eval u)
    (j : Fin (n-r.critical.offset.val+1)) :
    coordinateAt P r values t j=coordinateAt P s other u (indexCast r s hoff j) :=by
  rcases r with ⟨⟨o,b,c,sc,hsc,heights⟩,height,hheight,slope,hslope⟩
  rcases s with ⟨⟨o',b',c',sc',hsc',heights'⟩,height',hheight',slope',hslope'⟩
  dsimp only at hoff hobj
  subst o'
  subst b'
  exact ClearedCoordinateFrozenCongruence.annihilator P.degree 1 _ _ o.val
    (by dsimp only;have :=o.isLt;omega) H _ (P.leading:ℝ) _ j

variable {S B T C : ℕ} {P : SpatialSource n} {ι κ : Type}

theorem selected_specialize (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (hr : r.slope=commonDenominator x) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (j : Fin (n-r.critical.offset.val+1)) :
    (selected x hm r j φ).map (evalRingHom t)=
      Polynomial.C (coordinateScale x hm r)*coordinateAt P r values t j :=by
  rw [selected_eq x hm r hr φ values H,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.coe_evalRingHom,eval_C,coordinate_specialize]

theorem specialized_selected_scaling (x : State P S B m ι) (hm : m≤S)
    (y : State P T C l κ) (hl : l≤T) (r s : Rule n)
    (hr : r.slope=commonDenominator x) (hs : s.slope=commonDenominator y)
    (hoff : r.critical.offset=s.critical.offset)
    (hobj : r.critical.objective=s.critical.objective)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : y.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (other : Fin l→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (K : ∀i,ψ (y.bank.numerator i)/(y.bank.denominator i:ℝ)=other i)
    (t u : ℝ)
    (HN : ∀i,i<r.critical.offset.val→
      (normalized r values i).eval t=(normalized s other i).eval u)
    (j : Fin (n-r.critical.offset.val+1)) :
    (selected y hl s (indexCast r s hoff j) ψ).map (evalRingHom u)=
      Polynomial.C (coordinateScale y hl s/coordinateScale x hm r)*
        (selected x hm r j φ).map (evalRingHom t) :=by
  rw [selected_specialize y hl s hs ψ other K,selected_specialize x hm r hr φ values H,
    ←coordinateAt_congr P r s hoff hobj values other t u HN j]
  rw [←mul_assoc,←map_mul,div_mul_cancel₀ _ (coordinateScale_ne_zero x hm r)]

theorem specialized_selected_roots (x : State P S B m ι) (hm : m≤S)
    (y : State P T C l κ) (hl : l≤T) (r s : Rule n)
    (hr : r.slope=commonDenominator x) (hs : s.slope=commonDenominator y)
    (hoff : r.critical.offset=s.critical.offset)
    (hobj : r.critical.objective=s.critical.objective)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : y.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (other : Fin l→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (K : ∀i,ψ (y.bank.numerator i)/(y.bank.denominator i:ℝ)=other i)
    (t u : ℝ)
    (HN : ∀i,i<r.critical.offset.val→
      (normalized r values i).eval t=(normalized s other i).eval u)
    (j : Fin (n-r.critical.offset.val+1)) :
    ((selected y hl s (indexCast r s hoff j) ψ).map (evalRingHom u)).roots=
      ((selected x hm r j φ).map (evalRingHom t)).roots :=by
  rw [specialized_selected_scaling x hm y hl r s hr hs hoff hobj φ ψ values other H K t u HN j]
  exact Polynomial.roots_C_mul _ (div_ne_zero (coordinateScale_ne_zero y hl s) (coordinateScale_ne_zero x hm r))

end LeanCanny.Algebra.IntegralMixedNumericalSweep
