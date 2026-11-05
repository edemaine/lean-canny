/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValuePacking
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalReader
public import LeanCanny.Algebra.FixedWidthBivariateRebox
/-! # Native actual coordinate rows for the same-center value system

The unused second eliminant packet field retains the value-system context.
It supplies one common parameter width to every coordinate reader without
changing any coordinate equation or sampling a different center.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterValueCoordinateReader
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation Polynomial MatrixPower
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def metadata (c : List Bool) := WordList.get
  (pairSnd (FormulaSignSlotRadialCenterPrincipalFamily.original c)) 1
noncomputable def width (c : List Bool) := (FormulaSignSlotRadialCenterPrincipalFamily.inputBound c).size +
  (FormulaSignSlotRadialCenterValuePacking.degree (metadata c)).size

theorem metadata_FP : metadata ∈ FP := by
  apply mem_FP_of_eq (mem_FP_comp (mem_FP_pair
    (mem_FP_comp FormulaSignSlotRadialCenterPrincipalFamily.original_FP pairSnd_mem_FP)
    (constFn_mem_FP (BinaryNatCode.encode 1))) WordList.reader_FP)
  intro q
  simp only [Function.comp_apply, WordList.reader_packet, metadata]
theorem width_unary : UnaryFn width := by
  have HD : BinaryFn (fun c => FormulaSignSlotRadialCenterValuePacking.degree (metadata c)) :=
    FormulaSignSlotRadialCenterValuePacking.degree_binary.comp metadata_FP
  exact ((UnaryFn.length FormulaSignSlotRadialCenterPrincipalFamily.inputBound_binary.bits_mem_FP).of_eq
    (fun _ => BinaryNatCode.length_encode _)).add
      ((UnaryFn.length HD.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _))

theorem input_fit (c : List Bool) : FormulaSignSlotRadialCenterPrincipalFamily.inputBound c < 2 ^ width c :=
  (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
noncomputable def reader := FixedWidthBivariateRebox.reader
  FormulaSignSlotRadialCenterPrincipalFamily.arity FormulaSignSlotRadialCenterPrincipalFamily.width width
  FormulaSignSlotRadialCenterPrincipalFamily.inputBound FormulaSignSlotRadialCenterPrincipalFamily.polynomial
  FormulaSignSlotRadialCenterPrincipalReader.reader FormulaSignSlotRadialCenterPrincipalFamily.arity_unary
  FormulaSignSlotRadialCenterPrincipalFamily.width_unary width_unary
  FormulaSignSlotRadialCenterPrincipalFamily.polynomial_degree FormulaSignSlotRadialCenterPrincipalFamily.input_fit input_fit

def eliminantContext (q : List Bool) := pair (FormulaSignSlotRadialCenterValueLayout.original (pairFst q))
  (WordList.encode [BinaryNat.normalize (pairSnd q), pairFst q])
def tableQuery (table : List Bool → List Bool) (q : List Bool) :=
  WordList.reader (pair (table (pairFst q)) (BinaryNat.normalize (pairSnd q)))
def inputContext (q : List Bool) := pair (eliminantContext q)
  (pair (tableQuery FormulaSignSlotRadialCenterValueLayout.tauTable q)
    (tableQuery FormulaSignSlotRadialCenterValueLayout.degreeTable q))
theorem eliminantContext_FP : eliminantContext ∈ FP := by
  unfold eliminantContext WordList.encode
  exact mem_FP_pair (mem_FP_comp pairFst_mem_FP FormulaSignSlotRadialCenterValueLayout.original_FP)
    (mem_FP_pair (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP) (mem_FP_pair pairFst_mem_FP (constFn_mem_FP [])))
theorem tableQuery_FP (table : List Bool → List Bool) (ht : table ∈ FP) : tableQuery table ∈ FP :=
  mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP ht)
    (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)) WordList.reader_FP
theorem inputContext_FP : inputContext ∈ FP := mem_FP_pair eliminantContext_FP
  (mem_FP_pair (tableQuery_FP _ FormulaSignSlotRadialCenterValueLayout.tauTable_FP)
    (tableQuery_FP _ FormulaSignSlotRadialCenterValueLayout.degreeTable_FP))

private theorem inputBound_root (c : List Bool) : FormulaSignSlotRadialCenterPrincipalFamily.inputBound c =
    FormulaSignSlotRadialCenterValueSelection.bound (pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original c)) := by
  simp only [FormulaSignSlotRadialCenterPrincipalFamily.inputBound, FormulaSignSlotRadialCenterSelection.bound,
    FormulaSignSlotRadialCenterValueSelection.bound, FormulaSignSlotRadialEliminantPacked.resultDegree,
    FormulaSignSlotRadialEliminantPackingLayout.columns, FormulaSignSlotRadialEliminantPackingLayout.width,
    FormulaSignSlotRadialEliminantPackingLayout.spatial, FormulaSignSlotRadialEliminantPackingLayout.sourceDegree,
    FormulaSignSlotRadialEliminantPackingLayout.parameterDegree, FormulaSignSlotRadialCoordinatePacket.root]

theorem width_packet (q : List Bool) : width (inputContext q) = FormulaSignSlotRadialCenterValuePacking.width (pairFst q) := by
  have HM : metadata (inputContext q) = pairFst q := by
    simp only [metadata, inputContext, FormulaSignSlotRadialCenterPrincipalFamily.original, eliminantContext,
      pairFst_pair, pairSnd_pair, WordList.get_encode, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  rw [width, inputBound_root, HM]
  simp only [inputContext, FormulaSignSlotRadialCenterPrincipalFamily.original, eliminantContext, pairFst_pair]
  rfl

theorem coordinate_value (q : List Bool) : (FormulaSignSlotRadialEliminantInput.coordinate (eliminantContext q)).val =
    min (Nat.fromBitsLE (pairSnd q)) (FormulaSignSlotRadialCenterValueLayout.arity (pairFst q) - 1) := by
  dsimp only [FormulaSignSlotRadialEliminantInput.coordinate]
  simp only [FormulaSignSlotRadialEliminantInput.field, FormulaSignSlotRadialEliminantInput.spatialCount,
    eliminantContext, pairFst_pair, pairSnd_pair, WordList.get_encode, List.getElem?_cons_zero, Option.getD_some,
    BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits]
  rfl

private noncomputable def encodedAt (q : List Bool) (tau D W : ℕ) : Polynomial (Polynomial ℤ) :=
  (FormulaSignSlotRadialCenterSquarefreeSelection.truncate
    ((FormulaSignSlotRadialFormalEliminant.eliminant (pairFst q)
      (FormulaSignSlotRadialEliminantInput.coordinate q)).coeff tau) D).map
        ((FixedWidthKronecker.encode (d (pairFst q) + 1) W).comp TriplePolynomialParameterFlatten.one)
noncomputable def packed (q : List Bool) : Polynomial (Polynomial ℤ) :=
  FixedWidthBivariateReader.polynomial FormulaSignSlotRadialCenterPrincipalFamily.arity width
    FormulaSignSlotRadialCenterPrincipalFamily.polynomial (inputContext q)
private theorem packed_encoded (q : List Bool) : packed q = encodedAt
    (FormulaSignSlotRadialCenterPrincipalFamily.original (inputContext q))
    (FormulaSignSlotRadialCenterPrincipalFamily.tau (inputContext q))
    (FormulaSignSlotRadialCenterPrincipalFamily.degree (inputContext q)) (width (inputContext q)) := by
  unfold packed FixedWidthBivariateReader.polynomial FormulaSignSlotRadialCenterPrincipalFamily.polynomial
    FormulaSignSlotRadialCenterPrincipalFamily.arity FormulaSignSlotRadialCenterSquarefreeSelection.polynomial encodedAt
  rw [Polynomial.map_map]

private theorem encoded_actual (q c : List Bool) (hc : pairFst q = c)
    (i : Fin (N c + d c + 1)) (hi : (FormulaSignSlotRadialEliminantInput.coordinate q).val = i.val)
    (tau D W : ℕ) : encodedAt q tau D W =
      (FormulaSignSlotRadialCenterSquarefreeSelection.truncate
        ((FormulaSignSlotRadialFormalEliminant.eliminant c i).coeff tau) D).map
          ((FixedWidthKronecker.encode (d c + 1) W).comp TriplePolynomialParameterFlatten.one) := by
  cases hc
  have HI : FormulaSignSlotRadialEliminantInput.coordinate q = i := Fin.ext hi
  unfold encodedAt
  rw [HI]

attribute [local irreducible] encodedAt

theorem packed_packet (c : List Bool) (i : Fin (FormulaSignSlotRadialCenterValueLayout.arity c)) :
    packed (pair c (BinaryNatCode.encode i.val)) =
      (FormulaSignSlotRadialCenterValueFamily.input (FormulaSignSlotRadialCenterValueLayout.original c)
        (fun j => FormulaSignSlotRadialCenterValueLayout.tau c j.val)
        (fun j => FormulaSignSlotRadialCenterValueLayout.degree c j.val) i).map
          (FormulaSignSlotRadialCenterValuePacking.parameterMap c) := by
  rw [packed_encoded, width_packet]
  simp only [inputContext, FormulaSignSlotRadialCenterPrincipalFamily.original,
    FormulaSignSlotRadialCenterPrincipalFamily.tau, FormulaSignSlotRadialCenterPrincipalFamily.degree,
    pairFst_pair, pairSnd_pair]
  have HC : pairFst (eliminantContext (pair c (BinaryNatCode.encode i.val))) =
      FormulaSignSlotRadialCenterValueLayout.original c := by simp only [eliminantContext, pairFst_pair]
  have HI : (FormulaSignSlotRadialEliminantInput.coordinate (eliminantContext (pair c (BinaryNatCode.encode i.val)))).val = i.val := by
    rw [coordinate_value]
    simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact Nat.min_eq_left (by have H := i.isLt; omega)
  rw [encoded_actual _ _ HC i HI]
  simp only [tableQuery, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [show i.val.bits = BinaryNatCode.encode i.val from rfl, WordList.reader_packet, WordList.reader_packet]
  rfl

private def reindexQuery (f : List Bool → List Bool) (z : List Bool) :=
  pair (pair (f (pairFst (pairFst z))) (pairSnd (pairFst z))) (pairSnd z)
private theorem reindexQuery_FP (f : List Bool → List Bool) (hf : f ∈ FP) : reindexQuery f ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hf)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP
private noncomputable def reindexReader {p : List Bool → Polynomial (Polynomial ℤ)}
    (R : CertifiedPolynomial.BivariateReader p) (f : List Bool → List Bool) (hf : f ∈ FP) :
    CertifiedPolynomial.BivariateReader (p ∘ f) where
  coefficient := R.coefficient ∘ reindexQuery f
  evaluator := R.evaluator.precompose (reindexQuery f) (reindexQuery_FP f hf)
  coefficient_eq q u v := by
    simp only [Function.comp_apply, reindexQuery, pairFst_pair, pairSnd_pair]
    have H := R.coefficient_eq (pair (f (pairFst q)) (pairSnd q)) u v
    simp only [pairFst_pair] at H
    refine H.trans ?_
    exact congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m)) rfl (by rw [pairSnd_pair])
private noncomputable def packed_reader : CertifiedPolynomial.BivariateReader packed :=
  reindexReader reader inputContext inputContext_FP

private def canonicalQuery (z : List Bool) := pair (pairFst z)
  (pair (BinaryNat.normalize (pairFst (pairSnd z))) (BinaryNat.normalize (pairSnd (pairSnd z))))
private theorem canonicalQuery_FP : canonicalQuery ∈ FP := mem_FP_pair pairFst_mem_FP
  (mem_FP_pair (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) BinaryNat.normalize_mem_FP)
    (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP))
private theorem reader_function {p : List Bool → Polynomial (Polynomial ℤ)}
    (R : CertifiedPolynomial.BivariateReader p) : SpaceFunction (SymbolicFixedTableEntryBits.coefficient p) := by
  have E := R.evaluator.precompose canonicalQuery canonicalQuery_FP
  refine E.congr (funext fun z => ?_)
  dsimp only [Function.comp_apply, canonicalQuery]
  rw [BinaryNat.normalize_eq_bits, BinaryNat.normalize_eq_bits]
  exact (R.coefficient_eq (pairFst z) (Nat.fromBitsLE (pairFst (pairSnd z)))
    (Nat.fromBitsLE (pairSnd (pairSnd z)))).trans (by
      unfold SymbolicFixedTableEntryBits.coefficient SymbolicFixedTableEntryBits.integerResidue
      rfl)

def normalizeIndex (q : List Bool) := pair (pairFst q) (BinaryNat.normalize (pairSnd q))
theorem normalizeIndex_FP : normalizeIndex ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)
noncomputable def coordinate (c : List Bool) (i : Fin (FormulaSignSlotRadialCenterValueLayout.arity c)) :=
  packed (pair c (BinaryNatCode.encode i.val))
noncomputable def selected := DiagonalParameterBits.selected FormulaSignSlotRadialCenterValueLayout.arity coordinate
private def Fits (q : List Bool) : Prop := Nat.fromBitsLE (pairSnd q) < FormulaSignSlotRadialCenterValueLayout.arity (pairFst q)
private theorem fits_FP : FPPred Fits :=
  (BinaryFn.fromBits pairSnd_mem_FP).lt (BinaryFn.ofUnary (FormulaSignSlotRadialCenterValueLayout.arity_unary.comp pairFst_mem_FP))

theorem evaluator : SpaceFunction (SymbolicFixedTableEntryBits.coefficient selected) := by
  have E := (reader_function packed_reader).precompose (reindexQuery normalizeIndex)
    (reindexQuery_FP normalizeIndex normalizeIndex_FP)
  have HC := fits_FP.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have EB := SpaceFunction.branch (fun z => decide (Fits (pairFst (pairFst z)))) HC.flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine EB.congr (funext fun z => ?_)
  simp only [Function.comp_apply, decide_eq_true_eq]
  unfold SymbolicFixedTableEntryBits.coefficient selected DiagonalParameterBits.selected
    DiagonalParameterBits.selectedAt
  by_cases H : Fits (pairFst (pairFst z))
  · rw [ite_eq_left H]
    dsimp only [Fits] at H
    rw [dite_eq_left H]
    simp only [coordinate, reindexQuery, normalizeIndex, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits]
    rfl
  · rw [ite_eq_right H]
    dsimp only [Fits] at H
    rw [dite_eq_right H]
    simp [SymbolicFixedTableEntryBits.integerResidue, residueBits, BinaryNatCode.encode]

end LeanCanny.Encoding.FormulaSignSlotRadialCenterValueCoordinateReader
