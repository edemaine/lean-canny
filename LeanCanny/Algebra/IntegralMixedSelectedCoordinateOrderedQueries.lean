/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateWindowDegree
public import LeanCanny.Algebra.RealIteratedTarski
/-! # One ordered parameter region for all six actual window queries

The Y degree and seed degree are exact. The independent epsilon and delta
axes retain their order after swapping the coefficient representation.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSelectedCoordinateOrderedQueries
open Polynomial IntegralMixedSelectedCoordinateWindowDegree
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem evaluate_swap_C (q : ℝ[X]) (ε δ : ℝ) :
    RealIteratedTarski.evaluate ε δ (Polynomial.Bivariate.swap (Polynomial.C q))=q.eval δ :=by
  rw [Polynomial.Bivariate.swap_C,RealIteratedTarski.evaluate_apply,Polynomial.eval₂_map]
  have HC : (Polynomial.evalRingHom ε).comp Polynomial.C=RingHom.id ℝ :=by ext a;simp
  rw [HC,Polynomial.eval₂_id]

theorem evaluated_head (p : (ℝ[X])[X]) (ε δ : ℝ) :
    (head p).map (RealIteratedTarski.evaluate ε δ)=p.map (Polynomial.evalRingHom δ) :=by
  ext k
  simp only [head,Polynomial.coeff_map]
  exact evaluate_swap_C (p.coeff k) ε δ

theorem evaluated_query (y scale : ℝ) (negative : Bool) (e : Fin 3) (ε δ : ℝ) :
    (query y scale negative e).map (RealIteratedTarski.evaluate ε δ)=
      (Polynomial.C scale*(Polynomial.X-Polynomial.C y+
        Polynomial.C (if negative then -ε else ε)))^e.val :=by
  let χ:=(RealIteratedTarski.evaluate ε δ).comp Polynomial.Bivariate.swap.toRingHom
  have HC : χ.comp Polynomial.C=Polynomial.evalRingHom δ :=by
    apply RingHom.ext
    intro q
    exact evaluate_swap_C q ε δ
  have HX : χ Polynomial.X=ε :=by
    change RealIteratedTarski.evaluate ε δ (Polynomial.Bivariate.swap Polynomial.X)=ε
    rw [Polynomial.Bivariate.swap_Y,RealIteratedTarski.evaluate_apply]
    simp
  unfold query
  rw [Polynomial.map_map]
  change ((WindowTarskiSeedDegree.affineQuery (Polynomial.C (Polynomial.C scale)*
    (Polynomial.X-Polynomial.C (Polynomial.C y)) : (ℝ[X])[X])
      (Polynomial.C (if negative then -scale else scale)))^e.val).map χ=_
  rw [Polynomial.map_pow,WindowTarskiSeedDegree.affineQuery,Polynomial.map_add,
    Polynomial.map_map,HC,Polynomial.map_C,map_mul,show χ (Polynomial.C (Polynomial.C (if negative then -scale else scale)))=
      (Polynomial.C (if negative then -scale else scale)).eval δ from congrArg (fun f=>f (Polynomial.C (if negative then -scale else scale))) HC,HX]
  cases negative <;> simp only [ite_false,Bool.false_eq_true,ite_true,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_sub,Polynomial.map_X,Polynomial.coe_evalRingHom,Polynomial.eval_C]
  all_goals
    congr 1
    simp [map_mul]
    ring

noncomputable def value (p : (ℝ[X])[X]) (d : ℕ) (y scale : ℝ) (negative : Bool) (e : Fin 3) :=
  RealIteratedTarski.value (head p) (query y scale negative e) d (d+2) (d-1)

theorem eventually_queries (p : (ℝ[X])[X]) (d : ℕ) (hd : 0<d) (hp : p.natDegree=d)
    (y scale : ℝ) (hs : scale≠0) :
    ∃η : ℝ,0<η ∧ ∀ε : ℝ,0<ε→ε<η→∃ζ : ℝ,0<ζ ∧ ∀negative : Bool,∀e : Fin 3,
      ∀δ : ℝ,0<δ→δ<ζ→
        RootSignQueries.tarskiQuery ((head p).map (RealIteratedTarski.evaluate ε δ))
          ((query y scale negative e).map (RealIteratedTarski.evaluate ε δ))=value p d y scale negative e :=by
  let tests:=Finset.univ.biUnion (fun k : Bool×Fin 3=>
    (RealIteratedTarski.tests (head p) (query y scale k.1 k.2) d (d+2) (d-1)).toFinset)
  obtain ⟨η,hη,HE⟩:=RealIteratedInfinitesimalSignSpace.finite_sign_correct tests id
  refine ⟨η,hη,fun ε he heη=>?_⟩
  obtain ⟨ζ,hζ,HD⟩:=HE ε he heη
  refine ⟨ζ,hζ,fun negative e δ hdδ hdζ=>?_⟩
  apply RealIteratedTarski.query_eq_value (head p) (query y scale negative e) d (d+2) (d-1) hd
    ((head_degree p).trans hp) (seed_degree p d hd hp y scale hs negative e)
    (input_degree p d hp y scale negative e)
  intro q hq
  have HM : q∈tests:=Finset.mem_biUnion.mpr ⟨(negative,e),Finset.mem_univ _,List.mem_toFinset.mpr hq⟩
  simpa only [id_eq,RealIteratedTarski.evaluate_apply,RealIteratedTarski.lex] using HD q HM δ hdδ hdζ

end LeanCanny.Algebra.IntegralMixedSelectedCoordinateOrderedQueries
