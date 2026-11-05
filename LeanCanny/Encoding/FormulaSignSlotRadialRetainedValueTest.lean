/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankPolynomialTest
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValueSource
/-! # Actual branch-cut coefficients at unchanged chronological bank references -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRetainedValueTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialCenterValueSource.arity
  FormulaSignSlotRadialCenterValueSource.width FormulaSignSlotRadialCenterValueSource.degree
  FormulaSignSlotRadialCenterValueSource.mass FormulaSignSlotRadialCenterValueSource.polynomial
  FormulaSignSlotRadialCenterValueCoefficient.polynomial

noncomputable def source : IntegralFramedBankPolynomialModel.Source where
  arity := FormulaSignSlotRadialCenterValueSource.arity
  width := FormulaSignSlotRadialCenterValueSource.width
  degree := FormulaSignSlotRadialCenterValueSource.degree
  mass := FormulaSignSlotRadialCenterValueSource.mass
  polynomial := FormulaSignSlotRadialCenterValueSource.polynomial
  fit z i := (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt (FormulaSignSlotRadialCenterValueSource.fit z)
  polynomial_degree := FormulaSignSlotRadialCenterValueSource.polynomial_degree
  polynomial_mass := FormulaSignSlotRadialCenterValueSource.polynomial_mass
noncomputable def access : IntegralFramedBankPolynomialModel.Access source where
  arity := by dsimp only [source]; exact FormulaSignSlotRadialCenterValueSource.arity_unary
  width := by dsimp only [source]; exact FormulaSignSlotRadialCenterValueSource.width_unary
  degree := by dsimp only [source]; exact FormulaSignSlotRadialCenterValueSource.degree_binary
  mass := by dsimp only [source]; exact FormulaSignSlotRadialCenterValueSource.mass_binary
  coefficient := FormulaSignSlotRadialCenterValueSource.coefficient
  evaluator := FormulaSignSlotRadialCenterValueSource.evaluator
  packet := FormulaSignSlotRadialCenterValueSource.packet

def slot (i : ℕ) (z : List Bool) := WordList.reader (pair (pairSnd z) (BinaryNatCode.encode i))
theorem slot_FP (i : ℕ) : slot i ∈ FP :=
  mem_FP_comp (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP _)) WordList.reader_FP
def read (radial : List Bool → List Bool) (z : List Bool) :=
  pair (radial (pairFst z)) (pair (slot 0 z) (slot 1 z))
theorem read_FP (radial : List Bool → List Bool) (hr : radial ∈ FP) : read radial ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP hr) (mem_FP_pair (slot_FP 0) (slot_FP 1))

private noncomputable def principalValue (c : List Bool) (j r : ℕ) (x : ℕ → ℝ) :=
  (FormulaSignSlotRadialCenterValueCoefficient.polynomial c j r).eval₂ (Int.castRingHom ℝ) (fun i => x i.val)
private noncomputable def selectedValue (c indices : List Bool) (x : ℕ → ℝ) := principalValue
  c (Nat.fromBitsLE (WordList.get indices 0)) (Nat.fromBitsLE (WordList.get indices 1)) x

private noncomputable def sourceValue (z : List Bool) (x : ℕ → ℝ) :=
  (source.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i => x i.val)
private theorem sourceValue_principal (z : List Bool) (x : ℕ → ℝ) : sourceValue z x =
    principalValue (pairFst z) (Nat.fromBitsLE (pairFst (pairSnd z))) (Nat.fromBitsLE (pairSnd (pairSnd z))) x := by
  unfold sourceValue source FormulaSignSlotRadialCenterValueSource.polynomial
    FormulaSignSlotRadialCenterValueSource.arity FormulaSignSlotRadialCenterValueSource.order
    FormulaSignSlotRadialCenterValueSource.radius principalValue
  rfl
attribute [local irreducible] principalValue
private theorem sourceValue_selected (radial : List Bool → List Bool) (z : List Bool) (x : ℕ → ℝ) :
    sourceValue (read radial z) x = selectedValue (radial (pairFst z)) (pairSnd z) x := by
  rw [sourceValue_principal]
  simp only [read, pairFst_pair, pairSnd_pair, slot, WordList.reader_packet]
  unfold selectedValue
  rfl

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

private theorem selected_packet (c w indices : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w) :
    value hn ht ha hR outer radial refs (pair (pair c w) indices) = InfinitesimalSign.encode
      (SignType.sign (selectedValue (radial c) indices (center hn ht ha hR outer refs c w hv))) := by
  have H := IntegralFramedMarkedPolynomialTest.packet source hn ht ha hR outer (read radial) refs c w indices hv
  change value hn ht ha hR outer radial refs (pair (pair c w) indices) = InfinitesimalSign.encode
    (SignType.sign (sourceValue (read radial (pair c indices)) (center hn ht ha hR outer refs c w hv))) at H
  rw [sourceValue_selected] at H
  simp only [pairFst_pair, pairSnd_pair] at H
  exact H

theorem packet (c w indices : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w) :
    value hn ht ha hR outer radial refs (pair (pair c w) indices) = InfinitesimalSign.encode
      (SignType.sign ((FormulaSignSlotRadialCenterValueCoefficient.polynomial (radial c)
        (Nat.fromBitsLE (WordList.get indices 0)) (Nat.fromBitsLE (WordList.get indices 1))).eval₂
          (Int.castRingHom ℝ) (fun i => center hn ht ha hR outer refs c w hv i.val))) := by
  have H := selected_packet hn ht ha hR outer radial refs c w indices hv
  unfold selectedValue principalValue at H
  exact H

def indices (j r : ℕ) := WordList.encode [BinaryNatCode.encode j, BinaryNatCode.encode r]

noncomputable def actualCoefficient (c : List Bool) (x : ℕ → ℝ) (j r : ℕ) :=
  (((FormulaSignSlotRadialValueCertificate.polynomial
    (FormulaSignSlotRadialCenterValueLayout.original c) (fun i => x i.val)).coeff j).coeff r)

theorem value_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (j r : ℕ)
    (h : FormulaSignSlotRadialCenterValueFamily.Guards (FormulaSignSlotRadialCenterValueLayout.original (radial c))
      (fun i => center hn ht ha hR outer refs c w hv i.val)
      (fun i => FormulaSignSlotRadialCenterValueLayout.tau (radial c) i.val)
      (fun i => FormulaSignSlotRadialCenterValueLayout.degree (radial c) i.val)) :
    value hn ht ha hR outer radial refs (pair (pair c w) (indices j r)) = InfinitesimalSign.encode
      (SignType.sign (actualCoefficient (radial c) (center hn ht ha hR outer refs c w hv) j r)) := by
  rw [selected_packet]
  unfold selectedValue
  simp only [indices, WordList.get_encode, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, MacaulayBits.fromBits_encode]
  apply congrArg (fun a : ℝ => InfinitesimalSign.encode (SignType.sign a))
  unfold principalValue actualCoefficient
  exact (FormulaSignSlotRadialCenterValueCoefficient.specialization (radial c) _ j r h).symm

end LeanCanny.Encoding.FormulaSignSlotRadialRetainedValueTest
