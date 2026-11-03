/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateNearQueries
/-! # A constant coordinate head checks its actual distinct-root ordinal

The head's degree is exact. Repeated roots count once, and empty root sets
reject every ordinal. Positive scaling may be nonunit before specialization.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedCoordinateRank
open LeanCanny.Algebra LeanCanny.Geometry Polynomial
open IntegralMixedSelectedCoordinateOrderedQueries
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem finite_rank_closed (s : Finset ℝ) (code : ℕ) :
    IsClosed {z : ℝ | z∈s ∧OrderedRealRootWindow.rank s z=code} :=by
  have H:=(s.filter (fun z=>OrderedRealRootWindow.rank s z=code)).isClosed
  simpa only [Finset.coe_filter,Set.ofPred_and] using H

theorem rank_iff_small_windows (p : ℝ[X]) (code : ℕ) (y : ℝ) :
    (y∈p.roots.toFinset ∧ OrderedRealRootWindow.rank p.roots.toFinset y=code) ↔
      ∃η : ℝ,0<η ∧∀ε : ℝ,0<ε→ε<η→IntegralMixedSelectedCoordinateWindow.Window p code y ε :=by
  constructor
  · intro H
    refine ⟨1,by norm_num,fun ε hε _=>?_⟩
    exact (IntegralMixedSelectedCoordinateWindow.window_iff p code y ε).mpr
      ⟨y,H.1,H.2,by simpa only [dist_self] using hε⟩
  · rintro ⟨η,hη,H⟩
    apply (finite_rank_closed p.roots.toFinset code).closure_subset
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    have HE : 0<min ε η/2:=div_pos (lt_min hε hη) (by norm_num)
    obtain ⟨z,hz,hr,hd⟩:=(IntegralMixedSelectedCoordinateWindow.window_iff p code y (min ε η/2)).mp
      (H _ HE (by have HM:=min_le_right ε η;linarith))
    have Hdist : dist z y<ε:=hd.trans_le (by have HM:=min_le_left ε η;linarith)
    exact ⟨z,⟨hz,hr⟩,by simpa only [dist_comm] using Hdist⟩

noncomputable def queryValue (p : ℝ[X]) (d : ℕ) (y scale : ℝ) (negative : Bool) (e : Fin 3) :=
  IntegralMixedSelectedCoordinateOrderedQueries.value (p.map Polynomial.C) d y scale negative e
noncomputable def Test (p : ℝ[X]) (d : ℕ) (y scale : ℝ) (code : ℕ) : Prop :=
  2*queryValue p d y scale false 0≤2*(code:ℤ)+queryValue p d y scale false 2+queryValue p d y scale false 1 ∧
  2*(code:ℤ)<queryValue p d y scale true 2-queryValue p d y scale true 1

private theorem evaluated_constant (p : ℝ[X]) (ε δ : ℝ) :
    ((IntegralMixedSelectedCoordinateWindowDegree.head (p.map Polynomial.C)).map
      (RealIteratedTarski.evaluate ε δ))=p :=by
  rw [evaluated_head,Polynomial.map_map]
  have HC : (Polynomial.evalRingHom δ).comp Polynomial.C=RingHom.id ℝ:=by ext a;simp
  rw [HC,Polynomial.map_id]

private theorem clear_query (p : ℝ[X]) (y scale ε δ : ℝ) (hs : 0<scale)
    (negative : Bool) (e : Fin 3) :
    RootSignQueries.tarskiQuery
      ((IntegralMixedSelectedCoordinateWindowDegree.head (p.map Polynomial.C)).map (RealIteratedTarski.evaluate ε δ))
      ((IntegralMixedSelectedCoordinateWindowDegree.query y scale negative e).map (RealIteratedTarski.evaluate ε δ))=
    RootSignQueries.tarskiQuery p ((Polynomial.X-Polynomial.C (y+if negative then ε else -ε))^e.val) :=by
  rw [evaluated_constant,evaluated_query,mul_pow,
    show (Polynomial.C scale : ℝ[X])^e.val=Polynomial.C (scale^e.val) from (map_pow Polynomial.C scale e.val).symm]
  have HQ : Polynomial.X-Polynomial.C y+Polynomial.C (if negative then -ε else ε)=
      (Polynomial.X-Polynomial.C (y+if negative then ε else -ε) : ℝ[X]) :=by
    cases negative <;> simp [map_add,map_neg] <;> ring
  rw [HQ]
  simpa only [map_one,one_mul] using
    RootSignQueries.tarskiQuery_C_mul p ((Polynomial.X-Polynomial.C (y+if negative then ε else -ε))^e.val)
      1 (scale^e.val) one_ne_zero (pow_pos hs _)


theorem window_stable (p : ℝ[X]) (d : ℕ) (hd : 0<d) (hp : p.natDegree=d)
    (y scale : ℝ) (hs : 0<scale) (code : ℕ) :
    ∃η : ℝ,0<η ∧∀ε : ℝ,0<ε→ε<η→
      (IntegralMixedSelectedCoordinateWindow.Window p code y ε↔Test p d y scale code) :=by
  have HD : (p.map Polynomial.C).natDegree=d:=by
    rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective,hp]
  obtain ⟨η,hη,HE⟩:=eventually_queries (p.map Polynomial.C) d hd HD y scale (ne_of_gt hs)
  refine ⟨η,hη,fun ε he heη=>?_⟩
  obtain ⟨ζ,hζ,H⟩:=HE ε he heη
  have Hδ : 0<ζ/2:=half_pos hζ
  have Hζ : ζ/2<ζ:=by linarith
  have HQ (negative : Bool) (e : Fin 3):=
    (clear_query p y scale ε (ζ/2) hs negative e).symm.trans (H negative e (ζ/2) Hδ Hζ)
  have H0:=HQ false 0
  have HL1:=HQ false 1
  have HL2:=HQ false 2
  have HH1:=HQ true 1
  have HH2:=HQ true 2
  simp only [Bool.false_eq_true,ite_false,ite_true,show (0 : Fin 3).val=0 from rfl,
    show (1 : Fin 3).val=1 from rfl,show (2 : Fin 3).val=2 from rfl,
    pow_zero,pow_one,←sub_eq_add_neg] at H0 HL1 HL2 HH1 HH2
  rw [IntegralMixedSelectedWindowQueries.window_iff,H0,HL1,HL2,HH1,HH2]
  rfl

theorem test_iff_rank (p : ℝ[X]) (d : ℕ) (hd : 0<d) (hp : p.natDegree=d)
    (y scale : ℝ) (hs : 0<scale) (code : ℕ) :
    Test p d y scale code ↔y∈p.roots.toFinset ∧OrderedRealRootWindow.rank p.roots.toFinset y=code :=by
  obtain ⟨η,hη,H⟩:=window_stable p d hd hp y scale hs code
  constructor
  · intro HT
    exact (rank_iff_small_windows p code y).mpr ⟨η,hη,fun ε he heη=>(H ε he heη).mpr HT⟩
  · intro HR
    apply (H (η/2) (half_pos hη) (by linarith)).mp
    exact (IntegralMixedSelectedCoordinateWindow.window_iff p code y (η/2)).mpr
      ⟨y,HR.1,HR.2,by simpa only [dist_self] using half_pos hη⟩

end LeanCanny.Connectivity.IntegralMixedSelectedCoordinateRank
