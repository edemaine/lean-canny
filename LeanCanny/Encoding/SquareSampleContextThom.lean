/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleProjectedThom

/-! # Thom probes between different native sampling contexts

The source label is decoded in its own context. Metadata selects the target
context's annihilator while leaving that source decoder unchanged. This
supports explicit label conversion without a context-invariance assumption
on either sampler's native enumeration.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleContextThom
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def reindex (target : List Bool → List Bool) (z : List Bool) : List Bool :=
  pair (target (pairFst (pairSnd z))) (pairSnd (pairSnd z))
theorem reindex_FP {target : List Bool → List Bool} (ht : target ∈ FP) : reindex target ∈ FP := by
  exact mem_FP_pair (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) ht)
    (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def source (G : Inputs) (target : List Bool → List Bool) : IntegerPolynomialRootQueriesBits.Source where
  polynomial := (SquareSampleProjectedThom.source G).polynomial ∘ reindex target
  degree := (SquareSampleProjectedThom.source G).degree ∘ reindex target
  mass := (SquareSampleProjectedThom.source G).mass ∘ reindex target
  degree_bound z := (SquareSampleProjectedThom.source G).degree_bound (reindex target z)
  mass_bound z := (SquareSampleProjectedThom.source G).mass_bound (reindex target z)

theorem sourceAccess {G : Inputs} (hG : G.Access) {target : List Bool → List Bool} (ht : target ∈ FP) :
    IntegerPolynomialRootQueriesBits.Access (source G target) := by
  let A := SquareSampleProjectedThom.sourceAccess hG
  exact ⟨PolynomialFamilyProductBits.reindexEvaluator A.coefficient (reindex target) (reindex_FP ht),
    A.degree.comp (reindex_FP ht), A.mass.comp (reindex_FP ht)⟩

def coordinate (F G : Inputs) (target : List Bool → List Bool)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (c d : List Bool) : Fin (F.count c) :=
  projection c (SquareSampleInput.selected G (target c) (pairFst (pairSnd d)))

noncomputable def value (F G : Inputs) (target : List Bool → List Bool)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c)) : List Bool → List Bool :=
  SquareSampleCompleteUnivariateTest.value F (source G target) (coordinate F G target projection)

theorem evaluator {F G : Inputs} (hF : F.Access) (hG : G.Access) {target : List Bool → List Bool}
    (ht : target ∈ FP) (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (hi : UnaryFn (fun z => (coordinate F G target projection (pairFst z) (pairSnd z)).val)) :
    SpaceFunction (value F G target projection) :=
  SquareSampleCompleteUnivariateTest.evaluator hF (sourceAccess hG ht) _ hi

theorem packet (F G : Inputs) (target : List Bool → List Bool)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w)
    (i : Fin (G.count (target c))) (k : ℕ) :
    value F G target projection (pair (pair c w) (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k)))) =
      InfinitesimalSign.encode (ThomEncoding.sign ((G.annihilator (target c) i).map (Int.castRingHom ℝ))
        ((SquareSampleCompleteVertices.candidate F c w hw).val (projection c i)) k) := by
  rw [value, SquareSampleCompleteUnivariateTest.packet F (source G target) _ c w _ hw]
  have HI : coordinate F G target projection c
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) = projection c i := by
    simp only [coordinate, pairSnd_pair, pairFst_pair, SquareSampleInput.selected_encode]
  have HP : (source G target).polynomial
      (pair c (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k)))) =
      Polynomial.derivative^[k] (G.annihilator (target c) i) := by
    unfold source reindex SquareSampleProjectedThom.source SquareSampleCompleteCoordinateThom.polynomial
      IndexedIntegerDerivativeBits.polynomial
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair,
      SquareSampleCompleteCoordinateThom.base, SquareSampleCompleteCoordinateThom.order,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
    change Polynomial.derivative^[k] (SquareSampleCompleteCoordinateThom.baseAt G (target c)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) = _
    rw [SquareSampleCompleteCoordinateThom.baseAt, SquareSampleCompleteCoordinateThom.coordinate,
      pairFst_pair, SquareSampleInput.selected_encode]
  rw [HI, HP]
  simp only [ThomEncoding.sign, Polynomial.iterate_derivative_map, Polynomial.eval_map]

end LeanCanny.Encoding.SquareSampleContextThom
