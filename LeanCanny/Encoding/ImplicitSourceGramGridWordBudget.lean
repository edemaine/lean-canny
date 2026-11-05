/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ImplicitSourceGramGridAccess
public import LeanCanny.Encoding.ImplicitSourceGramGridWords
public import LeanCanny.Computation.WordResourceEnvelope
/-! # Original-header budgets for witnessed Gram-grid certificates

One unary header allowance bounds the grid's own sample word over every
coefficient-witness table of the proved size. The component-hitting tuple
and its own word are those of the original witnessed-grid construction.
-/
@[expose] public section
namespace LeanCanny.Encoding.ImplicitSourceGramGridWordBudget
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralFramedBankPolynomialModel (Source)
open CoerciveComponentSampling
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def tableBound (S : Source) (u : List Bool) : ℕ :=
  (6 * (ImplicitSourceCoerciveBoxGram.degreeBound S u + 1).size + 6) * S.arity u

theorem tableBound_unary (S : Source) (A : IntegralFramedBankPolynomialModel.Access S) :
    UnaryFn (tableBound S) := by
  have HD := (ImplicitSourceCoerciveBoxGram.degreeBound_binary S A).add (BinaryFn.const 1)
  have HS : UnaryFn (fun u => (ImplicitSourceCoerciveBoxGram.degreeBound S u + 1).size) :=
    (UnaryFn.length HD.bits_mem_FP).of_eq (fun u => BinaryNatCode.length_encode _)
  exact (((UnaryFn.const 6).mul HS).add (UnaryFn.const 6)).mul A.arity

def contextBound (S : Source) (u : List Bool) : ℕ := 2 * u.length + tableBound S u + 2

theorem contextBound_unary (S : Source) (A : IntegralFramedBankPolynomialModel.Access S) :
    UnaryFn (contextBound S) :=
  ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (tableBound_unary S A)).add (UnaryFn.const 2))

theorem budget_exists (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) :
    ∃ B : List Bool → ℕ, UnaryFn B ∧ ∀ u c, c.length ≤ contextBound S u →
      SquareSampleCompleteVertices.width (ImplicitSourceGramGrid.input S hp) c ≤ B u :=
  (SquareSampleCompleteVertices.width_unary (ImplicitSourceGramGrid.access S A hp)).wordEnvelope
    (contextBound_unary S A)

noncomputable def ownwordBound (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) : List Bool → ℕ := Classical.choose (budget_exists S A hp)

theorem ownwordBound_unary (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) : UnaryFn (ownwordBound S A hp) :=
  (Classical.choose_spec (budget_exists S A hp)).1

theorem width_le (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) (u Gamma : List Bool) (hGamma : Gamma.length ≤ tableBound S u) :
    SquareSampleCompleteVertices.width (ImplicitSourceGramGrid.input S hp) (pair u Gamma) ≤
      ownwordBound S A hp u := by
  apply (Classical.choose_spec (budget_exists S A hp)).2 u (pair u Gamma)
  rw [pair_length]
  unfold contextBound
  omega

theorem exists_bounded_word (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) (u : List Bool)
    (x : Zeros ((S.polynomial u).map (Int.castRingHom ℝ))) :
    ∃ Gamma : List Bool, Gamma.length ≤ tableBound S u ∧
      (∀ i : Fin (S.arity u),
        ImplicitSourceGramGrid.slice (pair u Gamma) i.val ≤ ImplicitSourceCoerciveBoxGram.degreeBound S u ∧
        ImplicitSourceGramGrid.witness (pair u Gamma) i.val ≤ ImplicitSourceCoerciveBoxGram.degreeBound S u) ∧
      ∃ (w : List Bool) (hw : SquareSampleCompleteVertices.Valid
          (ImplicitSourceGramGrid.input S hp) (pair u Gamma) w),
        w.length = SquareSampleCompleteVertices.width (ImplicitSourceGramGrid.input S hp) (pair u Gamma) ∧
        w.length ≤ ownwordBound S A hp u ∧
        ∃ a : Zeros ((S.polynomial u).map (Int.castRingHom ℝ)),
          JoinedIn (Zeros ((S.polynomial u).map (Int.castRingHom ℝ))) x.val a.val ∧
            HEq (SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp)
              (pair u Gamma) w hw).val a.val := by
  obtain ⟨Gamma,hGamma,hindices,w,hw,hlen,a,hpath,hpoint⟩ :=
    ImplicitSourceGramGridWords.exists_word S hp u x
  exact ⟨Gamma,hGamma,hindices,w,hw,hlen,hlen.le.trans (width_le S A hp u Gamma hGamma),a,hpath,hpoint⟩

end LeanCanny.Encoding.ImplicitSourceGramGridWordBudget
