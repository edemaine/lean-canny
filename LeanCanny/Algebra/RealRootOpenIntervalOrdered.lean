/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RealRootOpenIntervalQueries
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateOrderedQueries
public import LeanCanny.Algebra.DyadicTarskiSpace
/-! # Two ordered principal statistics certify an empty open root interval

The head is independent of both parameters. Independent epsilon gives
exact seed degree d-1; delta stays unused in the common native layout.
-/
@[expose] public section
namespace LeanCanny.Algebra.RealRootOpenIntervalOrdered
open Polynomial IntegralMixedSelectedCoordinateWindowDegree
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def constantHead (p : ℝ[X]) : (ℝ[X])[X]:=p.map Polynomial.C
noncomputable def value (p : ℝ[X]) (d : ℕ) (y scale : ℝ) (negative : Bool) :=
  IntegralMixedSelectedCoordinateOrderedQueries.value (constantHead p) d y scale negative 1

theorem head_degree (p : ℝ[X]) : (constantHead p).natDegree=p.natDegree:=
  Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective p

theorem evaluated_head (p : ℝ[X]) (ε δ : ℝ) :
    (head (constantHead p)).map (RealIteratedTarski.evaluate ε δ)=p :=by
  rw [IntegralMixedSelectedCoordinateOrderedQueries.evaluated_head]
  ext k
  simp only [constantHead,Polynomial.coeff_map,Polynomial.coe_evalRingHom,Polynomial.eval_C]

private theorem query_value (p : ℝ[X]) (y scale : ℝ) (hs : 0<scale) (negative : Bool) (ε δ : ℝ) :
    RootSignQueries.tarskiQuery ((head (constantHead p)).map (RealIteratedTarski.evaluate ε δ))
      ((query y scale negative 1).map (RealIteratedTarski.evaluate ε δ))=
      RootSignQueries.tarskiQuery p (X-C (y+if negative then ε else -ε)) :=by
  rw [evaluated_head,IntegralMixedSelectedCoordinateOrderedQueries.evaluated_query]
  simp only [show (1:Fin 3).val=1 from rfl,pow_one]
  have HQ : X-C y+C (if negative then -ε else ε)=(X-C (y+if negative then ε else -ε) : ℝ[X]) :=by
    cases negative <;> simp [map_add,map_neg] <;> ring
  rw [HQ]
  simpa only [map_one,one_mul] using RootSignQueries.tarskiQuery_C_mul p (X-C (y+if negative then ε else -ε)) 1 scale (by norm_num) hs

theorem empty_iff (p : ℝ[X]) (d : ℕ) (hd : 0<d) (hdegree : p.natDegree=d)
    {a b : ℝ} (hab : a<b) (scale : ℝ) (hs : 0<scale) :
    (∀ r, p.eval r=0 → r ∉ Set.Ioo a b)↔value p d a scale true=value p d b scale false :=by
  have HP : (constantHead p).natDegree=d:=(head_degree p).trans hdegree
  have hp : p≠0:=by
    intro HZ
    rw [HZ,Polynomial.natDegree_zero] at hdegree
    omega
  obtain ⟨η0,hη0,H0⟩:=RealRootOpenIntervalQueries.empty_iff p hp hab
  obtain ⟨ηL,hηL,HL⟩:=IntegralMixedSelectedCoordinateOrderedQueries.eventually_queries (constantHead p) d hd HP a scale (ne_of_gt hs)
  obtain ⟨ηR,hηR,HR⟩:=IntegralMixedSelectedCoordinateOrderedQueries.eventually_queries (constantHead p) d hd HP b scale (ne_of_gt hs)
  let η:=min η0 (min ηL ηR)
  have hη : 0<η:=lt_min hη0 (lt_min hηL hηR)
  let ε:=η/2
  have he : 0<ε:=half_pos hη
  have heη : ε<η:=half_lt_self hη
  have he0 : ε<η0:=heη.trans_le (min_le_left _ _)
  have heL : ε<ηL:=heη.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heR : ε<ηR:=heη.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨ζL,hζL,HL⟩:=HL ε he heL
  obtain ⟨ζR,hζR,HR⟩:=HR ε he heR
  let δ:=min ζL ζR/2
  have hδ : 0<δ:=half_pos (lt_min hζL hζR)
  have hδL : δ<ζL:=(half_lt_self (lt_min hζL hζR)).trans_le (min_le_left _ _)
  have hδR : δ<ζR:=(half_lt_self (lt_min hζL hζR)).trans_le (min_le_right _ _)
  have HLeft:=(query_value p a scale hs true ε δ).symm.trans (HL true 1 δ hδ hδL)
  have HRight:=(query_value p b scale hs false ε δ).symm.trans (HR false 1 δ hδ hδR)
  have HE:=H0 ε he he0
  simp only [ite_true,Bool.false_eq_true,ite_false,←sub_eq_add_neg] at HLeft HRight
  rw [HLeft,HRight] at HE
  exact HE

end LeanCanny.Algebra.RealRootOpenIntervalOrdered
