/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCurrentQBadCuts
/-! # Valid slab factor choices are unique; the actual bad set is choice independent

Native records need not reproduce a classical Choices witness. Their exact
coefficient-zero guards force the same index for each of the actual three
slab classes. The fourth limit-coordinate choice is unused here.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
open IntegralMixedHistory IntegralMixedFullHistoryScript IntegralMixedCriticalSweep Polynomial
open LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
set_option backward.isDefEq.respectTransparency false

private theorem first_nonzero_unique {A : Type*} [Zero A] (p : ℕ→A) (i j : ℕ)
    (HL : ∀ k < i,p k=0) (HT : p i≠0) (HlowOther : ∀ k < j,p k=0) (HtopOther : p j≠0) : i=j :=by
  rcases lt_trichotomy i j with hij|hij|hij
  · exact False.elim (HT (HlowOther i hij))
  · exact hij
  · exact False.elim (HtopOther (HL j hij))

theorem coordinate_index_unique (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (i k : Fin (IntegralMixedCoordinateTrailing.ChoiceBound P r))
    (hi : IntegralMixedCoordinateTrailing.Valid x hm r j φ i)
    (hk : IntegralMixedCoordinateTrailing.Valid x hm r j φ k) : i=k :=by
  apply Fin.ext
  exact first_nonzero_unique _ i.val k.val hi.1 hi.2 hk.1 hk.2

theorem squarefree_index_unique (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (i k : Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r))
    (hi : IntegralMixedCoordinateSquarefree.Valid x hm r j φ i)
    (hk : IntegralMixedCoordinateSquarefree.Valid x hm r j φ k) : i=k :=by
  apply Fin.ext
  exact first_nonzero_unique _ i.val k.val hi.1 hi.2 hk.1 hk.2

theorem value_index_unique (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (i k : Fin (IntegralMixedValueTrailing.ChoiceBound P r))
    (hi : IntegralMixedValueTrailing.Valid x hm r j φ i)
    (hk : IntegralMixedValueTrailing.Valid x hm r j φ k) : i=k :=by
  apply Fin.ext
  exact first_nonzero_unique _ i.val k.val hi.1 hi.2 hk.1 hk.2

theorem bad_choices_eq (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c d : IntegralMixedRelativeCuts.Choices x hm r φ) :
    bad x hm r φ c=bad x hm r φ d :=by
  have HK (j : Tag r) : kind x hm r φ c j=kind x hm r φ d j:=by
    rcases j with ⟨tag,j⟩
    fin_cases tag
    · change IntegralMixedRelativeCuts.Kind.coordinate j (c.coordinateIndex j)=
        IntegralMixedRelativeCuts.Kind.coordinate j (d.coordinateIndex j)
      exact congrArg _ (coordinate_index_unique x hm r j φ _ _ (c.coordinateValid j) (d.coordinateValid j))
    · change IntegralMixedRelativeCuts.Kind.squarefree j (c.squarefreeIndex j)=
        IntegralMixedRelativeCuts.Kind.squarefree j (d.squarefreeIndex j)
      exact congrArg _ (squarefree_index_unique x hm r j φ _ _ (c.squarefreeValid j) (d.squarefreeValid j))
    · change IntegralMixedRelativeCuts.Kind.value j (c.valueIndex j)=
        IntegralMixedRelativeCuts.Kind.value j (d.valueIndex j)
      exact congrArg _ (value_index_unique x hm r j φ _ _ (c.valueValid j) (d.valueValid j))
  have HE (j : Tag r) : cut x hm r φ c j=cut x hm r φ d j:=congrArg (IntegralMixedRelativeCuts.factor x hm r) (HK j)
  ext t
  constructor
  · rintro ⟨j,Hj⟩
    exact ⟨j,by rw [←HE j]; exact Hj⟩
  · rintro ⟨j,Hj⟩
    exact ⟨j,by rw [HE j]; exact Hj⟩

variable [Fintype ι]

theorem retained_bad_iff_any_choices (x : State P S B m ι) (hm : m≤S) (c : Command P B) (hn : m+1≤S)
    (r : Rule n) (hr : r.slope=commonDenominator x)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : (step x hm c).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (a : ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (HN : ∀ i,ψ ((step x hm c).bank.numerator i)/((step x hm c).bank.denominator i:ℝ)=
      (Fin.cons a values : Fin (m+1)→ℝ) i)
    (old : IntegralMixedRelativeCuts.Choices x hm r φ)
    (next : IntegralMixedRelativeCuts.Choices (step x hm c) hn (shiftRule x hm c r) ψ) (t : ℝ) :
    t∈bad (step x hm c) hn (shiftRule x hm c r) ψ next ↔ t∈bad x hm r φ old :=by
  rw [bad_choices_eq (step x hm c) hn (shiftRule x hm c r) ψ next
    (retainedChoices x hm c hn r hr φ ψ values a H HN old)]
  exact retained_bad_iff x hm c hn r hr φ ψ values a H HN old t

end LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
