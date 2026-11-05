/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ImplicitSourceGramGridWordBudget
public import LeanCanny.Encoding.SquareSampleSourceTest
public import LeanCanny.Encoding.SquareSampleCompletePolynomialTest
/-! # Native implicit component samples with a same-point source filter

The grid, its complete square system and the source test are constructed
from the original implicit polynomial. The accepted point is the grid's
own decoded point, and every original component has a bounded accepted word.
-/
@[expose] public section
namespace LeanCanny.Encoding.ImplicitSourceComponentSampler
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open IntegralFramedBankPolynomialModel (Source)
open CoerciveComponentSampling
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def test (S : Source) (hp : ∀ u, 0 < S.arity u) :
    SquareSamplePolynomialTest.Test (ImplicitSourceGramGrid.input S hp) :=
  SquareSampleSourceTest.test (ImplicitSourceGramGrid.input S hp)
    (ImplicitSourceCoerciveBoxGram.reindex S ImplicitSourceGramGrid.header) (fun _ => rfl)

theorem test_access (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) : (test S hp).Access :=
  SquareSampleSourceTest.access (ImplicitSourceGramGrid.input S hp)
    (ImplicitSourceCoerciveBoxGram.reindex S ImplicitSourceGramGrid.header) (fun _ => rfl)
    (ImplicitSourceCoerciveBoxGram.reindex_access S A ImplicitSourceGramGrid.header pairFst_mem_FP)

noncomputable def language (S : Source) (hp : ∀ u, 0 < S.arity u) : Language :=
  SquareSampleCompletePolynomialTest.language (ImplicitSourceGramGrid.input S hp) (test S hp) 0

theorem decider (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) : SpaceDecider (language S hp) :=
  SquareSampleCompletePolynomialTest.decider (ImplicitSourceGramGrid.access S A hp) (test_access S A hp) 0

theorem mem_PSPACE (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) : language S hp ∈ PSPACE := (decider S A hp).mem_PSPACE

theorem packet (S : Source) (hp : ∀ u, 0 < S.arity u) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (ImplicitSourceGramGrid.input S hp) c w) :
    pair c w ∈ language S hp ↔
      (S.polynomial (ImplicitSourceGramGrid.header c)).eval₂ (Int.castRingHom ℝ)
        (SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp) c w hw).val = 0 := by
  rw [language, SquareSampleCompletePolynomialTest.language_packet _ _ _ _ _ hw]
  change SignType.sign ((S.polynomial (ImplicitSourceGramGrid.header c)).eval₂ (Int.castRingHom ℝ)
    (SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp) c w hw).val) = 0 ↔ _
  exact sign_eq_zero_iff

private theorem source_zero_at_context (S : Source) (hp : ∀ u, 0 < S.arity u)
    (u c w : List Bool) (hc : ImplicitSourceGramGrid.header c = u)
    (hw : SquareSampleCompleteVertices.Valid (ImplicitSourceGramGrid.input S hp) c w)
    (a : Zeros ((S.polynomial u).map (Int.castRingHom ℝ)))
    (he : HEq (SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp) c w hw).val a.val) :
    pair c w ∈ language S hp := by
  cases hc
  apply (packet S hp c w hw).mpr
  rw [eq_of_heq he]
  have ha := a.property
  change MvPolynomial.eval a.val ((S.polynomial (ImplicitSourceGramGrid.header c)).map (Int.castRingHom ℝ)) = 0 at ha
  simpa only [MvPolynomial.eval_map] using ha

/-- One original-header budget covers an accepted own word in every component. -/
theorem component_hit (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) (u : List Bool)
    (x : Zeros ((S.polynomial u).map (Int.castRingHom ℝ))) :
    ∃ Gamma : List Bool, Gamma.length ≤ ImplicitSourceGramGridWordBudget.tableBound S u ∧
      ∃ (w : List Bool) (hw : SquareSampleCompleteVertices.Valid
          (ImplicitSourceGramGrid.input S hp) (pair u Gamma) w),
        w.length = SquareSampleCompleteVertices.width (ImplicitSourceGramGrid.input S hp) (pair u Gamma) ∧
        w.length ≤ ImplicitSourceGramGridWordBudget.ownwordBound S A hp u ∧
        pair (pair u Gamma) w ∈ language S hp ∧
        ∃ a : Zeros ((S.polynomial u).map (Int.castRingHom ℝ)),
          JoinedIn (Zeros ((S.polynomial u).map (Int.castRingHom ℝ))) x.val a.val ∧
            HEq (SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp)
              (pair u Gamma) w hw).val a.val := by
  obtain ⟨Gamma,hGamma,_,w,hw,hlen,hbound,a,hpath,hpoint⟩ :=
    ImplicitSourceGramGridWordBudget.exists_bounded_word S A hp u x
  exact ⟨Gamma,hGamma,w,hw,hlen,hbound,
    source_zero_at_context S hp u (pair u Gamma) w (pairFst_pair _ _) hw a hpoint,a,hpath,hpoint⟩

theorem source_nonempty (S : Source) (hp : ∀ u, 0 < S.arity u)
    (u c w : List Bool) (hc : ImplicitSourceGramGrid.header c = u)
    (hq : pair c w ∈ language S hp) :
    Nonempty (Zeros ((S.polynomial u).map (Int.castRingHom ℝ))) := by
  cases hc
  have hw : SquareSampleCompleteVertices.Valid (ImplicitSourceGramGrid.input S hp) c w := by
    simpa only [pairFst_pair, pairSnd_pair] using hq.1
  refine ⟨⟨(SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp) c w hw).val, ?_⟩⟩
  change MvPolynomial.eval _ ((S.polynomial (ImplicitSourceGramGrid.header c)).map (Int.castRingHom ℝ)) = 0
  simpa only [MvPolynomial.eval_map] using (packet S hp c w hw).mp hq

theorem nonempty_iff (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) (u : List Bool) :
    Nonempty (Zeros ((S.polynomial u).map (Int.castRingHom ℝ))) ↔
      ∃ Gamma : List Bool, Gamma.length ≤ ImplicitSourceGramGridWordBudget.tableBound S u ∧
        ∃ w : List Bool, w.length ≤ ImplicitSourceGramGridWordBudget.ownwordBound S A hp u ∧
          pair (pair u Gamma) w ∈ language S hp := by
  constructor
  · rintro ⟨x⟩
    obtain ⟨Gamma,hGamma,w,_hw,_hlen,hbound,hq,_⟩ := component_hit S A hp u x
    exact ⟨Gamma,hGamma,w,hbound,hq⟩
  · rintro ⟨Gamma,_,w,_,hq⟩
    exact source_nonempty S hp u (pair u Gamma) w (pairFst_pair _ _) hq

end LeanCanny.Encoding.ImplicitSourceComponentSampler
