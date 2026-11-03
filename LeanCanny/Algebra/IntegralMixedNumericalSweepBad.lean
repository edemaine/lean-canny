/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNumericalSweepValue
public import LeanCanny.Algebra.IntegralMixedSelectedBadChoiceUnique
/-! # The actual slab bad set depends on numerical frozen equations

The histories and their valid selected indices may differ. All three actual
ordinary cut families agree as real zero sets. Limit-coordinate cuts are
not included in the slab bad set.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNumericalSweep
open IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
open LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m T C l : ℕ} {P : SpatialSource n} {ι κ : Type}

private theorem first_unique {A : Type*} [Zero A] (f : ℕ→A) (i j : ℕ)
    (hi : ∀ k < i, f k=0) (hi' : f i≠0)
    (hj : ∀ k < j, f k=0) (hj' : f j≠0) : i=j :=by
  rcases lt_trichotomy i j with h|h|h
  · exact False.elim (hi' (hj i h))
  · exact h
  · exact False.elim (hj' (hi j h))

theorem bad_iff (x : State P S B m ι) (hm : m≤S) (y : State P T C l κ) (hl : l≤T)
    (r s : Rule n) (hr : r.slope=commonDenominator x) (hs : s.slope=commonDenominator y)
    (hoff : r.critical.offset=s.critical.offset) (hobj : r.critical.objective=s.critical.objective)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (ψ : y.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (other : Fin l→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (K : ∀i,ψ (y.bank.numerator i)/(y.bank.denominator i:ℝ)=other i)
    (HN : ∀i,i<r.critical.offset.val→normalized r values i=normalized s other i)
    (old : IntegralMixedRelativeCuts.Choices x hm r φ)
    (next : IntegralMixedRelativeCuts.Choices y hl s ψ) (t : ℝ) :
    t∈bad y hl s ψ next ↔ t∈bad x hm r φ old :=by
  rcases r with ⟨⟨o,b,c,sc,hsc,heights⟩,height,hheight,slope,hslope⟩
  rcases s with ⟨⟨o',b',c',sc',hsc',heights'⟩,height',hheight',slope',hslope'⟩
  dsimp only at hoff hobj
  subst o'
  subst b'
  let r : Rule n:=⟨⟨o,b,c,sc,hsc,heights⟩,height,hheight,slope,hslope⟩
  let s : Rule n:=⟨⟨o,b,c',sc',hsc',heights'⟩,height',hheight',slope',hslope'⟩
  have HC (j : Fin (n-o.val+1)) (i : ℕ) :
      ((IntegralMixedCriticalSweep.coordinate y hl s j).coeff i).map ψ.toRingHom=0 ↔
        ((IntegralMixedCriticalSweep.coordinate x hm r j).coeff i).map φ.toRingHom=0:=
    coefficient_zero_iff x hm y hl r s hr hs rfl rfl φ ψ values other H K HN j i
  have HP (j : Fin (n-o.val+1)) (i : ℕ) :
      (IntegralMixedCoordinateSquarefree.principal y hl s j i).map ψ.toRingHom=0 ↔
        (IntegralMixedCoordinateSquarefree.principal x hm r j i).map φ.toRingHom=0:=
    principal_zero_iff x hm y hl r s hr hs rfl rfl φ ψ values other H K HN j i
  have HR (tag : Tag r) :
      (cut y hl s ψ next tag).eval₂ ψ.toRingHom t=0 ↔
        (cut x hm r φ old tag).eval₂ φ.toRingHom t=0:=by
    rcases tag with ⟨tag,j⟩
    fin_cases tag
    · have HE : next.coordinateIndex j=old.coordinateIndex j:=by
        apply Fin.ext
        exact first_unique (fun i=>((IntegralMixedCriticalSweep.coordinate x hm r j).coeff i).map φ.toRingHom)
          _ _ (fun i hi=>(HC j i).mp ((next.coordinateValid j).1 i hi))
          ((not_congr (HC j _)).mp (next.coordinateValid j).2)
          (old.coordinateValid j).1 (old.coordinateValid j).2
      change (IntegralMixedCoordinateTrailing.factor y hl s j (next.coordinateIndex j)).eval₂ ψ.toRingHom t=0 ↔
        (IntegralMixedCoordinateTrailing.factor x hm r j (old.coordinateIndex j)).eval₂ φ.toRingHom t=0
      rw [HE]
      exact coefficient_root_iff x hm y hl r s hr hs rfl rfl φ ψ values other H K HN j _ t
    · have HE : next.squarefreeIndex j=old.squarefreeIndex j:=by
        apply Fin.ext
        exact first_unique (fun i=>(IntegralMixedCoordinateSquarefree.principal x hm r j i).map φ.toRingHom)
          _ _ (fun i hi=>(HP j i).mp ((next.squarefreeValid j).1 i hi))
          ((not_congr (HP j _)).mp (next.squarefreeValid j).2)
          (old.squarefreeValid j).1 (old.squarefreeValid j).2
      change (IntegralMixedCoordinateSquarefree.exceptional y hl s j (next.squarefreeIndex j)).eval₂ ψ.toRingHom t=0 ↔
        (IntegralMixedCoordinateSquarefree.exceptional x hm r j (old.squarefreeIndex j)).eval₂ φ.toRingHom t=0
      rw [HE]
      have H₁ : ((IntegralMixedCriticalSweep.coordinate y hl s j).coeff
          (IntegralMixedCoordinateSquarefree.coordinateDegree P r)).eval₂ ψ.toRingHom t=0 ↔
          ((IntegralMixedCriticalSweep.coordinate x hm r j).coeff
            (IntegralMixedCoordinateSquarefree.coordinateDegree P r)).eval₂ φ.toRingHom t=0:=
        coefficient_root_iff x hm y hl r s hr hs rfl rfl φ ψ values other H K HN j _ t
      have H₂ : (IntegralMixedCoordinateSquarefree.principal y hl s j (old.squarefreeIndex j).val).eval₂ ψ.toRingHom t=0 ↔
          (IntegralMixedCoordinateSquarefree.principal x hm r j (old.squarefreeIndex j).val).eval₂ φ.toRingHom t=0:=
        principal_root_iff x hm y hl r s hr hs rfl rfl φ ψ values other H K HN j _ t
      change (((IntegralMixedCriticalSweep.coordinate y hl s j).coeff
        (IntegralMixedCoordinateSquarefree.coordinateDegree P r))*
          IntegralMixedCoordinateSquarefree.principal y hl s j (old.squarefreeIndex j).val).eval₂ ψ.toRingHom t=0 ↔ _
      simp only [IntegralMixedCoordinateSquarefree.exceptional,Polynomial.eval₂_mul,mul_eq_zero]
      rw [H₁,H₂]
    · change (IntegralMixedValueTrailing.factor y hl s j (next.valueIndex j)).eval₂ ψ.toRingHom t=0 ↔
        (IntegralMixedValueTrailing.factor x hm r j (old.valueIndex j)).eval₂ φ.toRingHom t=0
      rw [←Polynomial.eval_map,←Polynomial.eval_map,
        IntegralMixedValueTrailing.factor_specialization y hl s j ψ _ (next.valueValid j),
        IntegralMixedValueTrailing.factor_specialization x hm r j φ _ (old.valueValid j)]
      exact value_trailing_zero x hm y hl r s hr hs rfl rfl φ ψ values other H K HN j t
  constructor
  · rintro ⟨tag,htag⟩
    exact ⟨tag,(HR tag).mp htag⟩
  · rintro ⟨tag,htag⟩
    exact ⟨tag,(HR tag).mpr htag⟩

theorem bad_iff_of_levels (x : State P S B m ι) (hm : m≤S) (y : State P T C l κ) (hl : l≤T)
    (r s : Rule n) (hr : r.slope=commonDenominator x) (hs : s.slope=commonDenominator y)
    (hoff : r.critical.offset=s.critical.offset) (hobj : r.critical.objective=s.critical.objective)
    (hh : r.height=s.height)
    (hscale : r.critical.scales r.height=s.critical.scales s.height)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (ψ : y.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (other : Fin l→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (K : ∀i,ψ (y.bank.numerator i)/(y.bank.denominator i:ℝ)=other i)
    (HN : ∀i : Fin (n+1),i.val<r.critical.offset.val→
      (r.critical.heights i).evaluate values/(r.critical.scales i:ℝ)=
        (s.critical.heights i).evaluate other/(s.critical.scales i:ℝ))
    (old : IntegralMixedRelativeCuts.Choices x hm r φ)
    (next : IntegralMixedRelativeCuts.Choices y hl s ψ) (t : ℝ) :
    t∈bad y hl s ψ next ↔ t∈bad x hm r φ old :=
  bad_iff x hm y hl r s hr hs hoff hobj φ ψ values other H K
    (normalized_frozen_eq_of_levels r s hh hscale values other HN) old next t

end LeanCanny.Algebra.IntegralMixedNumericalSweep
