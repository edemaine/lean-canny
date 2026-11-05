/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MvIndexedRationalClearing
public import LeanCanny.ETR.IndexedExpansion
/-! # The literal indexed clearing recipe over a coefficient ring -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientIndexedRationalClearing
open scoped Classical BigOperators
variable {R S:Type*} [CommRing R] [CommRing S] {σ:Type*}

noncomputable def cleared (A M W:ℕ) (a:ℕ→R) (e:ℕ→ℕ→ℕ)
    (n d:ℕ→MvPolynomial σ R):MvPolynomial σ R:=
  ∑ r∈Finset.range M,MvPolynomial.C (a r)*∏ i∈Finset.range A,n i^e r i*d i^(W-e r i)

theorem cleared_map (φ:R→+*S) (A M W:ℕ) (a:ℕ→R) (e:ℕ→ℕ→ℕ)
    (n d:ℕ→MvPolynomial σ R):
    MvPolynomial.map φ (cleared A M W a e n d)=
      cleared A M W (fun r=>φ (a r)) e
        (fun i=>MvPolynomial.map φ (n i)) (fun i=>MvPolynomial.map φ (d i)):=by
  simp only [cleared,map_sum,map_mul,map_prod,map_pow,MvPolynomial.map_C]

theorem cleared_int (A M W:ℕ) (a:ℕ→ℤ) (e:ℕ→ℕ→ℕ) (n d:ℕ→MvPolynomial σ ℤ):
    cleared A M W a e n d=MvIndexedRationalClearing.cleared A M W a e n d:=rfl

noncomputable def term (p:LeanCanny.ETR.Term) (n d:ℕ→MvPolynomial σ R):MvPolynomial σ R:=
  cleared p.toData.size p.monomialCount (2*p.toData.size)
    (fun r=>(p.monomialCoefficient r:R)) p.monomialExponent n d

theorem term_map (φ:R→+*S) (p:LeanCanny.ETR.Term) (n d:ℕ→MvPolynomial σ R):
    MvPolynomial.map φ (term p n d)=
      term p (fun i=>MvPolynomial.map φ (n i)) (fun i=>MvPolynomial.map φ (d i)):=by
  simp only [term,cleared_map,map_intCast]

theorem term_int (p:LeanCanny.ETR.Term) (n d:ℕ→MvPolynomial σ ℤ):
    term p n d=MvIndexedRationalClearing.cleared p.toData.size p.monomialCount (2*p.toData.size)
      p.monomialCoefficient p.monomialExponent n d:=rfl

theorem cleared_rename {τ:Type*} (f:σ→τ) (A M W:ℕ) (a:ℕ→R) (e:ℕ→ℕ→ℕ)
    (n d:ℕ→MvPolynomial σ R):
    MvPolynomial.rename f (cleared A M W a e n d)=
      cleared A M W a e (fun i=>MvPolynomial.rename f (n i)) (fun i=>MvPolynomial.rename f (d i)):=by
  simp only [cleared,map_sum,map_mul,map_prod,map_pow,MvPolynomial.rename_C]

theorem term_rename {τ:Type*} (f:σ→τ) (p:LeanCanny.ETR.Term) (n d:ℕ→MvPolynomial σ R):
    MvPolynomial.rename f (term p n d)=
      term p (fun i=>MvPolynomial.rename f (n i)) (fun i=>MvPolynomial.rename f (d i)):=by
  exact cleared_rename f _ _ _ _ _ n d

end LeanCanny.Algebra.CoefficientIndexedRationalClearing
