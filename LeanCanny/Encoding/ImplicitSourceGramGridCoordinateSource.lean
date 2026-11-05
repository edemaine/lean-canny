/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ImplicitSourceGramGridAccess
public import LeanCanny.Algebra.IntegerPolynomialRootQueriesSpace
/-! # Actual coordinate sources for external implicit Gram-grid samples

The coordinate source depends on the literal grid context and selected slot,
never on the sample word. Its root theorem refers to that context's OWN word.
-/
@[expose] public section
namespace LeanCanny.Encoding.ImplicitSourceGramGridCoordinateSource
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ImplicitSourceGramGrid.polynomial

noncomputable def selected (S : Source) (hp : ∀ u, 0<S.arity u) (q : List Bool) :
    Fin (ImplicitSourceGramGrid.count S (pairFst q)) :=
  SquareSampleInput.selected (ImplicitSourceGramGrid.input S hp) (pairFst q) (pairSnd q)

theorem selected_unary (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0<S.arity u) : UnaryFn (fun q => (selected S hp q).val) :=
  UnaryFn.fromBitsLE_min pairSnd_mem_FP
    (((ImplicitSourceGramGrid.count_unary S A).comp pairFst_mem_FP).sub (UnaryFn.const 1))

noncomputable def source (S : Source) (hp : ∀ u, 0<S.arity u) : IntegerPolynomialRootQueriesBits.Source where
  polynomial q := ImplicitSourceGramGrid.polynomial S (pairFst q) (selected S hp q)
  degree q := ImplicitSourceGramGrid.degree S (pairFst q)
  mass q := ImplicitSourceGramGrid.mass S (pairFst q)
  degree_bound q := ImplicitSourceGramGrid.polynomial_degree S (pairFst q) (selected S hp q)
  mass_bound q := ImplicitSourceGramGrid.polynomial_mass S (pairFst q) (selected S hp q)

theorem nonzero (S : Source) (hp : ∀ u, 0<S.arity u) (q : List Bool) :
    (source S hp).polynomial q ≠ 0 := ImplicitSourceGramGrid.nonzero S (pairFst q) (selected S hp q)

theorem polynomial_query (S : Source) (hp : ∀ u, 0<S.arity u) (c bits : List Bool) :
    (source S hp).polynomial (pair c bits) = ImplicitSourceGramGrid.polynomial S c
      (SquareSampleInput.selected (ImplicitSourceGramGrid.input S hp) c bits) := by
  let f (c b : List Bool) : Polynomial ℤ := ImplicitSourceGramGrid.polynomial S c
    (SquareSampleInput.selected (ImplicitSourceGramGrid.input S hp) c b)
  change f (pairFst (pair c bits)) (pairSnd (pair c bits)) = f c bits
  rw [pairFst_pair,pairSnd_pair]

theorem polynomial_packet (S : Source) (hp : ∀ u, 0<S.arity u) (c : List Bool)
    (i : Fin (ImplicitSourceGramGrid.count S c)) :
    (source S hp).polynomial (pair c (BinaryNatCode.encode i.val)) =
      ImplicitSourceGramGrid.polynomial S c i := by
  let f (c b : List Bool) : Polynomial ℤ := ImplicitSourceGramGrid.polynomial S c
    (SquareSampleInput.selected (ImplicitSourceGramGrid.input S hp) c b)
  change f (pairFst (pair c (BinaryNatCode.encode i.val)))
    (pairSnd (pair c (BinaryNatCode.encode i.val))) = _
  rw [pairFst_pair,pairSnd_pair]
  change ImplicitSourceGramGrid.polynomial S c
    (SquareSampleInput.selected (ImplicitSourceGramGrid.input S hp) c (BinaryNatCode.encode i.val)) = _
  rw [SquareSampleInput.selected_encode]

theorem coefficient_evaluator (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0<S.arity u) : SpaceFunction (PrimitivePairBits.coefficient (source S hp).polynomial) := by
  let C := RationalSubstitution.IntegerBits.context
  have HI : BinaryFn (fun q => (selected S hp (C q)).val) :=
    (BinaryFn.ofUnary (selected_unary S A hp)).comp RationalSubstitution.IntegerBits.context_mem_FP
  have E := ImplicitSourceGramSliceNative.evaluator S A (pairFst ∘ C)
    (fun q => (selected S hp (C q)).val)
    (fun q => Nat.fromBitsLE (RationalSubstitution.IntegerBits.selectedDegree q)) pairSnd
    (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP) HI
    (BinaryFn.fromBits RationalSubstitution.IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP
  refine E.congr (funext fun q => ?_)
  unfold ImplicitSourceGramSliceNative.value PrimitivePairBits.coefficient
  rw [ImplicitSourceGramSliceNative.polynomial_eq]
  rfl

theorem access (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0<S.arity u) : IntegerPolynomialRootQueriesBits.Access (source S hp) :=
  ⟨coefficient_evaluator S A hp,(ImplicitSourceGramGrid.degree_binary S A).comp pairFst_mem_FP,
    (ImplicitSourceGramGrid.mass_binary S A).comp pairFst_mem_FP⟩

theorem point_root (S : Source) (hp : ∀ u, 0<S.arity u) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (ImplicitSourceGramGrid.input S hp) c w)
    (i : Fin (ImplicitSourceGramGrid.count S c)) :
    ((source S hp).polynomial (pair c (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom ℝ)
      ((SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp) c w hw).val i)=0 := by
  rw [polynomial_packet]
  exact ImplicitSourceGramGrid.complete S hp c _
    (SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp) c w hw).property i

theorem point_root_query (S : Source) (hp : ∀ u, 0<S.arity u) (c w bits : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (ImplicitSourceGramGrid.input S hp) c w) :
    ((source S hp).polynomial (pair c bits)).eval₂ (Int.castRingHom ℝ)
      ((SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp) c w hw).val
        (SquareSampleInput.selected (ImplicitSourceGramGrid.input S hp) c bits))=0 := by
  rw [polynomial_query]
  exact ImplicitSourceGramGrid.complete S hp c _
    (SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp) c w hw).property _

end LeanCanny.Encoding.ImplicitSourceGramGridCoordinateSource
