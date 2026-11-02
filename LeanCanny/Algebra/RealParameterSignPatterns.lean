/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RealParameterTarski
public import LeanCanny.Algebra.SignQueryBounds

/-! # Eventual root-sign patterns over the selected real coefficient field

One finite interval works for all ternary product queries and every desired
sign pattern. This is semantic stability over the fixed selected hom, without
an effective radius or native coefficient-sign access premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.RealParameterTarski
open Polynomial RootSignQueries
open scoped Classical BigOperators
variable {J : Type} [Fintype J]

noncomputable def patternThreshold (p : (ℝ[X])[X]) (Q : J→(ℝ[X])[X]) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun e : J→Fin 3=>Classical.choose (eventual_query_eq_value p (queryPolynomial Q e)))

theorem patternThreshold_pos (p : (ℝ[X])[X]) (Q : J→(ℝ[X])[X]) : 0<patternThreshold p Q := by
  apply (Finset.lt_inf'_iff _).mpr
  intro e _
  exact (Classical.choose_spec (eventual_query_eq_value p (queryPolynomial Q e))).1

noncomputable def scaledValue (p : (ℝ[X])[X]) (Q : J→(ℝ[X])[X]) (σ : J→SignType) : ℤ :=
  ∑ e : J→Fin 3,patternWeight σ e*value p (queryPolynomial Q e)

theorem scaled_eq_value (p : (ℝ[X])[X]) (Q : J→(ℝ[X])[X]) (σ : J→SignType)
    (x : ℝ) (Hx : 0<x) (Hbound : x<patternThreshold p Q) :
    scaledRootCount (p.map (Polynomial.evalRingHom x)) (fun i=>(Q i).map (Polynomial.evalRingHom x)) σ=scaledValue p Q σ := by
  unfold scaledRootCount scaledValue
  apply Finset.sum_congr rfl
  intro e _
  rw [←map_queryPolynomial]
  apply congrArg (patternWeight σ e*·)
  exact (Classical.choose_spec (eventual_query_eq_value p (queryPolynomial Q e))).2 x Hx
    (Hbound.trans_le (Finset.inf'_le _ (Finset.mem_univ e)))

theorem rootCount_stable (p : (ℝ[X])[X]) (Q : J→(ℝ[X])[X]) (σ : J→SignType)
    (x y : ℝ) (Hx : 0<x) (Hy : 0<y) (Hxb : x<patternThreshold p Q) (Hyb : y<patternThreshold p Q) :
    signCount (p.map (Polynomial.evalRingHom x)).roots.toFinset (fun i=>(Q i).map (Polynomial.evalRingHom x)) σ=
      signCount (p.map (Polynomial.evalRingHom y)).roots.toFinset (fun i=>(Q i).map (Polynomial.evalRingHom y)) σ := by
  have H:=(scaled_eq_value p Q σ x Hx Hxb).trans (scaled_eq_value p Q σ y Hy Hyb).symm
  rw [scaledRootCount_eq,scaledRootCount_eq] at H
  exact Int.natCast_inj.mp (mul_left_cancel₀ (pow_ne_zero _ (by decide : (2:ℤ)≠0)) H)

theorem exists_realizable_interval (p : (ℝ[X])[X]) (hp : p≠0) (Q : J→(ℝ[X])[X]) :
    ∃ δ : ℝ,0<δ ∧ ∀ σ : J→SignType,∀ x y : ℝ,0<x→x<δ→0<y→y<δ→
      ((∃ a : ℝ,(p.map (Polynomial.evalRingHom x)).eval a=0 ∧
        ∀ i,SignType.sign (((Q i).map (Polynomial.evalRingHom x)).eval a)=σ i) ↔
       (∃ a : ℝ,(p.map (Polynomial.evalRingHom y)).eval a=0 ∧
        ∀ i,SignType.sign (((Q i).map (Polynomial.evalRingHom y)).eval a)=σ i)) := by
  obtain ⟨η,Hη,HS⟩:=InfinitesimalSign.sign_eval_eq_trailingCoeff p.leadingCoeff
  let δ:=min η (patternThreshold p Q)
  have Hδ : 0<δ:=lt_min Hη (patternThreshold_pos p Q)
  have Hnonzero (x : ℝ) (Hx : 0<x) (Hxd : x<δ) : p.map (Polynomial.evalRingHom x)≠0 := by
    have HL : p.leadingCoeff.trailingCoeff≠0:=Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
    have HE:=HS x Hx (Hxd.trans_le (min_le_left _ _))
    intro Hzero
    have HC:=congrArg (fun q : Polynomial ℝ=>q.coeff p.natDegree) Hzero
    rw [Polynomial.coeff_map,Polynomial.coeff_natDegree,Polynomial.coeff_zero] at HC
    change p.leadingCoeff.eval x=0 at HC
    rw [HC,sign_zero] at HE
    exact HL (sign_eq_zero_iff.mp HE.symm)
  refine ⟨δ,Hδ,?_⟩
  intro σ x y Hx Hxd Hy Hyd
  rw [←root_signCount_pos _ (Hnonzero x Hx Hxd),←root_signCount_pos _ (Hnonzero y Hy Hyd),
    rootCount_stable p Q σ x y Hx Hy (Hxd.trans_le (min_le_right _ _)) (Hyd.trans_le (min_le_right _ _))]

theorem selected_realizable_interval {A : Type} [CommRing A] (φ : A→+*ℝ)
    (p : Polynomial (Polynomial A)) (hp : p.map (Polynomial.mapRingHom φ)≠0)
    (Q : J→Polynomial (Polynomial A)) :
    ∃ δ : ℝ,0<δ ∧ ∀ σ : J→SignType,∀ x y : ℝ,0<x→x<δ→0<y→y<δ→
      ((∃ a : ℝ,((p.map (Polynomial.mapRingHom φ)).map (Polynomial.evalRingHom x)).eval a=0 ∧
        ∀ i,SignType.sign ((((Q i).map (Polynomial.mapRingHom φ)).map (Polynomial.evalRingHom x)).eval a)=σ i) ↔
       (∃ a : ℝ,((p.map (Polynomial.mapRingHom φ)).map (Polynomial.evalRingHom y)).eval a=0 ∧
        ∀ i,SignType.sign ((((Q i).map (Polynomial.mapRingHom φ)).map (Polynomial.evalRingHom y)).eval a)=σ i)) :=
  exists_realizable_interval _ hp _

end LeanCanny.Algebra.RealParameterTarski
