/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteCoordinateThom
public import LeanCanny.Encoding.SquareSampleCompleteUnivariateTest

/-! # Native coordinate Thom probes across two complete square samplers

A coordinate annihilator from the target sampler is evaluated at a projected
coordinate of a source root. Both original coefficient programs are charged.
This permits exact ancestor comparison without assuming regular source roots
or storing their coordinate digits.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleProjectedThom
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def source (G : Inputs) : IntegerPolynomialRootQueriesBits.Source where
  polynomial := SquareSampleCompleteCoordinateThom.polynomial G
  degree z := G.annDegree (pairFst z)
  mass := SquareSampleCompleteCoordinateThom.mass G
  degree_bound := SquareSampleCompleteCoordinateThom.polynomial_degree G
  mass_bound := SquareSampleCompleteCoordinateThom.polynomial_mass G

theorem sourceAccess {G : Inputs} (h : G.Access) : IntegerPolynomialRootQueriesBits.Access (source G) :=
  ⟨SquareSampleCompleteCoordinateThom.coefficientEvaluator h, h.annDegree.comp pairFst_mem_FP,
    SquareSampleCompleteCoordinateThom.mass_binary h⟩

def coordinate (F G : Inputs) (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (c d : List Bool) : Fin (F.count c) :=
  projection c (SquareSampleInput.selected G c (pairFst d))

noncomputable def value (F G : Inputs) (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c)) :
    List Bool → List Bool := SquareSampleCompleteUnivariateTest.value F (source G) (coordinate F G projection)

theorem evaluator {F G : Inputs} (hF : F.Access) (hG : G.Access)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (hi : UnaryFn (fun z => (coordinate F G projection (pairFst z) (pairSnd z)).val)) :
    SpaceFunction (value F G projection) :=
  SquareSampleCompleteUnivariateTest.evaluator hF (sourceAccess hG) (coordinate F G projection) hi

theorem packet (F G : Inputs) (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) (i : Fin (G.count c)) (k : ℕ) :
    value F G projection (pair (pair c w) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) =
      InfinitesimalSign.encode (ThomEncoding.sign ((G.annihilator c i).map (Int.castRingHom ℝ))
        ((SquareSampleCompleteVertices.candidate F c w hw).val (projection c i)) k) := by
  rw [value, SquareSampleCompleteUnivariateTest.packet F (source G) _ c w _ hw]
  have HI : coordinate F G projection c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k)) = projection c i := by
    simp only [coordinate, pairFst_pair, SquareSampleInput.selected_encode]
  have HP : (source G).polynomial (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) =
      Polynomial.derivative^[k] (G.annihilator c i) := by
    unfold source SquareSampleCompleteCoordinateThom.polynomial IndexedIntegerDerivativeBits.polynomial
    simp only [SquareSampleCompleteCoordinateThom.base, SquareSampleCompleteCoordinateThom.order,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    change Polynomial.derivative^[k] (SquareSampleCompleteCoordinateThom.baseAt G c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) = _
    rw [SquareSampleCompleteCoordinateThom.baseAt, SquareSampleCompleteCoordinateThom.coordinate,
      pairFst_pair, SquareSampleInput.selected_encode]
  rw [HI, HP]
  simp only [ThomEncoding.sign, Polynomial.iterate_derivative_map, Polynomial.eval_map]

end LeanCanny.Encoding.SquareSampleProjectedThom
