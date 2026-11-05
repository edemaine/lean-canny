/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankPolynomialTest
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalSource
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalGuards
/-! # Actual principal center signs at unchanged chronological bank references -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRetainedPrincipalTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialCenterPrincipalSource.arity
  FormulaSignSlotRadialCenterPrincipalSource.width FormulaSignSlotRadialCenterPrincipalSource.degree
  FormulaSignSlotRadialCenterPrincipalSource.mass FormulaSignSlotRadialCenterPrincipalSource.polynomial
  FormulaSignSlotRadialCenterPrincipalCoefficient.polynomial

noncomputable def source : IntegralFramedBankPolynomialModel.Source where
  arity := FormulaSignSlotRadialCenterPrincipalSource.arity
  width := FormulaSignSlotRadialCenterPrincipalSource.width
  degree := FormulaSignSlotRadialCenterPrincipalSource.degree
  mass := FormulaSignSlotRadialCenterPrincipalSource.mass
  polynomial := FormulaSignSlotRadialCenterPrincipalSource.polynomial
  fit z i := (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt (FormulaSignSlotRadialCenterPrincipalSource.fit z)
  polynomial_degree := FormulaSignSlotRadialCenterPrincipalSource.polynomial_degree
  polynomial_mass := FormulaSignSlotRadialCenterPrincipalSource.polynomial_mass
noncomputable def access : IntegralFramedBankPolynomialModel.Access source where
  arity := by dsimp only [source]; exact FormulaSignSlotRadialCenterPrincipalSource.arity_unary
  width := by dsimp only [source]; exact FormulaSignSlotRadialCenterPrincipalSource.width_unary
  degree := by dsimp only [source]; exact FormulaSignSlotRadialCenterPrincipalSource.degree_binary
  mass := by dsimp only [source]; exact FormulaSignSlotRadialCenterPrincipalSource.mass_binary
  coefficient := FormulaSignSlotRadialCenterPrincipalSource.coefficient
  evaluator := FormulaSignSlotRadialCenterPrincipalSource.evaluator
  packet := FormulaSignSlotRadialCenterPrincipalSource.packet

def slot (i : ℕ) (z : List Bool) := WordList.reader (pair (pairSnd z) (BinaryNatCode.encode i))
theorem slot_FP (i : ℕ) : slot i ∈ FP :=
  mem_FP_comp (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP _)) WordList.reader_FP
def read (radial : List Bool → List Bool) (z : List Bool) :=
  pair (pair (radial (pairFst z)) (pair (slot 0 z) (slot 1 z))) (pair (slot 2 z) (slot 3 z))
theorem read_FP (radial : List Bool → List Bool) (hr : radial ∈ FP) : read radial ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP hr) (mem_FP_pair (slot_FP 0) (slot_FP 1)))
    (mem_FP_pair (slot_FP 2) (slot_FP 3))

private noncomputable def principalValue (c : List Bool) (j r : ℕ) (x : ℕ → ℝ) :=
  (FormulaSignSlotRadialCenterPrincipalCoefficient.polynomial c j r).eval₂ (Int.castRingHom ℝ) (fun i => x i.val)
private noncomputable def selectedValue (c indices : List Bool) (x : ℕ → ℝ) := principalValue
  (pair c (pair (WordList.get indices 0) (WordList.get indices 1)))
    (Nat.fromBitsLE (WordList.get indices 2)) (Nat.fromBitsLE (WordList.get indices 3)) x
private noncomputable def sourceValue (z : List Bool) (x : ℕ → ℝ) :=
  (source.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i => x i.val)
private theorem sourceValue_principal (z : List Bool) (x : ℕ → ℝ) : sourceValue z x =
    principalValue (pairFst z) (Nat.fromBitsLE (pairFst (pairSnd z))) (Nat.fromBitsLE (pairSnd (pairSnd z))) x := by
  unfold sourceValue source FormulaSignSlotRadialCenterPrincipalSource.polynomial
    FormulaSignSlotRadialCenterPrincipalSource.arity FormulaSignSlotRadialCenterPrincipalSource.order
    FormulaSignSlotRadialCenterPrincipalSource.radius principalValue
  rfl
private theorem principal_zero (c : List Bool) (j r : ℕ) (x : ℕ → ℝ) : principalValue c j r x = 0 ↔
    FormulaSignSlotRadialCenterPrincipalGuards.Zero c (fun i => x i.val) j r := Iff.rfl
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
      (SignType.sign ((FormulaSignSlotRadialCenterPrincipalCoefficient.polynomial
        (pair (radial c) (pair (WordList.get indices 0) (WordList.get indices 1)))
        (Nat.fromBitsLE (WordList.get indices 2)) (Nat.fromBitsLE (WordList.get indices 3))).eval₂
          (Int.castRingHom ℝ) (fun i => center hn ht ha hR outer refs c w hv i.val))) := by
  have H := selected_packet hn ht ha hR outer radial refs c w indices hv
  unfold selectedValue principalValue at H
  exact H

def indices (tau D j r : ℕ) := WordList.encode
  [BinaryNatCode.encode tau, BinaryNatCode.encode D, BinaryNatCode.encode j, BinaryNatCode.encode r]

private theorem selected_indices (c : List Bool) (tau D j r : ℕ) (x : ℕ → ℝ) :
    selectedValue c (indices tau D j r) x =
      principalValue (pair c (pair (BinaryNatCode.encode tau) (BinaryNatCode.encode D))) j r x := by
  unfold selectedValue
  simp only [indices, WordList.get_encode, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem zero_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (tau D j r : ℕ) :
    value hn ht ha hR outer radial refs (pair (pair c w) (indices tau D j r)) = InfinitesimalSign.encode 0 ↔
      FormulaSignSlotRadialCenterPrincipalGuards.Zero (pair (radial c) (pair (BinaryNatCode.encode tau) (BinaryNatCode.encode D)))
        (fun i => center hn ht ha hR outer refs c w hv i.val) j r := by
  rw [selected_packet hn ht ha hR outer radial refs c w (indices tau D j r) hv, selected_indices]
  exact ((SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff).trans (principal_zero _ _ _ _)

end LeanCanny.Encoding.FormulaSignSlotRadialRetainedPrincipalTest
