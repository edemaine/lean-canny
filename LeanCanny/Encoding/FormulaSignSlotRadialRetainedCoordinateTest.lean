/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankPolynomialTest
public import LeanCanny.Encoding.FormulaSignSlotRadialCoordinatePacket
/-! # All coordinate coefficient tests on one unchanged retained center

Only the datum chooses the coordinate, perturbation, target and radius
indices. The sampler context, its word and the chronological references stay
fixed for the whole family.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRetainedCoordinateTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialCenterCoefficientSource.arity
  FormulaSignSlotRadialCenterCoefficientSource.width FormulaSignSlotRadialCenterCoefficientSource.degree
  FormulaSignSlotRadialCenterCoefficientSource.mass FormulaSignSlotRadialCenterCoefficientSource.polynomial
  FormulaSignSlotRadialCenterCoefficient.polynomial

noncomputable def source : IntegralFramedBankPolynomialModel.Source where
  arity := FormulaSignSlotRadialCenterCoefficientSource.arity
  width := FormulaSignSlotRadialCenterCoefficientSource.width
  degree := FormulaSignSlotRadialCenterCoefficientSource.degree
  mass := FormulaSignSlotRadialCenterCoefficientSource.mass
  polynomial := FormulaSignSlotRadialCenterCoefficientSource.polynomial
  fit z i := by
    apply (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt
    apply (FormulaSignSlotRadialCenterCoefficientSource.polynomial_degree z).trans_lt
    unfold FormulaSignSlotRadialCenterCoefficientSource.width
    exact Nat.lt_size_self _
  polynomial_degree := FormulaSignSlotRadialCenterCoefficientSource.polynomial_degree
  polynomial_mass := FormulaSignSlotRadialCenterCoefficientSource.polynomial_mass
noncomputable def access : IntegralFramedBankPolynomialModel.Access source where
  arity := by dsimp only [source]; exact FormulaSignSlotRadialCenterCoefficientSource.arity_unary
  width := by dsimp only [source]; exact FormulaSignSlotRadialCenterCoefficientSource.width_unary
  degree := by dsimp only [source]; exact FormulaSignSlotRadialCenterCoefficientSource.degree_binary
  mass := by dsimp only [source]; exact FormulaSignSlotRadialCenterCoefficientSource.mass_binary
  coefficient := FormulaSignSlotRadialCenterCoefficientSource.coefficient
  evaluator := FormulaSignSlotRadialCenterCoefficientSource.evaluator
  packet z bits modulus := by
    dsimp only [source]
    unfold FormulaSignSlotRadialCenterCoefficientSource.width
    exact FormulaSignSlotRadialCenterCoefficientSource.packet z bits modulus

def slot (i : ℕ) (z : List Bool) := WordList.reader (pair (pairSnd z) (BinaryNatCode.encode i))
theorem slot_FP (i : ℕ) : slot i ∈ FP :=
  mem_FP_comp (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP _)) WordList.reader_FP
def coordinateContext (radial : List Bool → List Bool) (z : List Bool) :=
  FormulaSignSlotRadialCoordinatePacket.writer (pair (radial (pairFst z)) (slot 0 z))
def read (radial : List Bool → List Bool) (z : List Bool) :=
  pair (coordinateContext radial z) (WordList.encode [slot 1 z, slot 2 z, slot 3 z])
theorem read_FP (radial : List Bool → List Bool) (hr : radial ∈ FP) : read radial ∈ FP := by
  have HC : coordinateContext radial ∈ FP := mem_FP_comp
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP hr) (slot_FP 0)) FormulaSignSlotRadialCoordinatePacket.writer_FP
  unfold read WordList.encode
  exact mem_FP_pair HC (mem_FP_pair (slot_FP 1) (mem_FP_pair (slot_FP 2) (mem_FP_pair (slot_FP 3) (constFn_mem_FP []))))

noncomputable def coefficientValue (c : List Bool) (s t r : ℕ) (x : ℕ → ℝ) :=
  (FormulaSignSlotRadialCenterCoefficient.polynomial c s t r).eval₂ (Int.castRingHom ℝ) (fun i => x i.val)
private noncomputable def selectedValue (c indices : List Bool) (x : ℕ → ℝ) :=
  coefficientValue (FormulaSignSlotRadialCoordinatePacket.writer (pair c (WordList.get indices 0)))
    (Nat.fromBitsLE (WordList.get indices 1)) (Nat.fromBitsLE (WordList.get indices 2))
      (Nat.fromBitsLE (WordList.get indices 3)) x
private noncomputable def sourceValue (z : List Bool) (x : ℕ → ℝ) :=
  (source.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i => x i.val)
private theorem sourceValue_entry (z : List Bool) (x : ℕ → ℝ) : sourceValue z x =
    coefficientValue (pairFst z) (Nat.fromBitsLE (WordList.get (pairSnd z) 0))
      (Nat.fromBitsLE (WordList.get (pairSnd z) 1)) (Nat.fromBitsLE (WordList.get (pairSnd z) 2)) x := by
  unfold sourceValue source FormulaSignSlotRadialCenterCoefficientSource.polynomial
    FormulaSignSlotRadialCenterCoefficientSource.arity FormulaSignSlotRadialCenterCoefficientSource.selected coefficientValue
  rfl
attribute [local irreducible] coefficientValue
private theorem sourceValue_read (radial : List Bool → List Bool) (z : List Bool) (x : ℕ → ℝ) :
    sourceValue (read radial z) x = selectedValue (radial (pairFst z)) (pairSnd z) x := by
  rw [sourceValue_entry]
  simp only [read, pairFst_pair, pairSnd_pair, WordList.get_encode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, slot, WordList.reader_packet]
  unfold selectedValue coordinateContext
  simp only [slot, WordList.reader_packet]
attribute [local irreducible] selectedValue

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R) (outer : Bool) (radial refs : List Bool → List Bool)
noncomputable def value := IntegralFramedMarkedPolynomialTest.value source hn ht ha hR outer (read radial) refs
theorem evaluator (hr : radial ∈ FP) (hf : refs ∈ FP) : SpaceFunction (value hn ht ha hR outer radial refs) :=
  IntegralFramedMarkedPolynomialTest.evaluator source hn ht ha hR outer (read radial) refs access (read_FP radial hr) hf
noncomputable def center (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w) : ℕ → ℝ :=
  FormulaSignSlotRadialBankCenterTest.center (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer)
    (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR outer) (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR outer)
    refs c w hv

private theorem packet (c w indices : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w) :
    value hn ht ha hR outer radial refs (pair (pair c w) indices) = InfinitesimalSign.encode
      (SignType.sign (selectedValue (radial c) indices (center hn ht ha hR outer refs c w hv))) := by
  have H := IntegralFramedMarkedPolynomialTest.packet source hn ht ha hR outer (read radial) refs c w indices hv
  change value hn ht ha hR outer radial refs (pair (pair c w) indices) = InfinitesimalSign.encode
    (SignType.sign (sourceValue (read radial (pair c indices)) (center hn ht ha hR outer refs c w hv))) at H
  rw [sourceValue_read] at H
  simpa only [pairFst_pair, pairSnd_pair] using H

def indices (i s t r : ℕ) := WordList.encode
  [BinaryNatCode.encode i, BinaryNatCode.encode s, BinaryNatCode.encode t, BinaryNatCode.encode r]
theorem coordinate_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (i s t r : ℕ) :
    value hn ht ha hR outer radial refs (pair (pair c w) (indices i s t r)) = InfinitesimalSign.encode
      (SignType.sign (coefficientValue (FormulaSignSlotRadialCoordinatePacket.packet (radial c) i) s t r
        (center hn ht ha hR outer refs c w hv))) := by
  rw [packet hn ht ha hR outer radial refs c w (indices i s t r) hv]
  apply congrArg (fun a : ℝ => InfinitesimalSign.encode (SignType.sign a))
  unfold selectedValue
  simp only [indices, WordList.get_encode, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  rw [FormulaSignSlotRadialCoordinatePacket.writer_packet]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.Encoding.FormulaSignSlotRadialRetainedCoordinateTest
