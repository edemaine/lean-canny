/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialBankCenterTest
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterSelection
/-! # Concrete radial coefficient signs at one unchanged retained center -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRetainedCenterTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR MatrixPower
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def read (radial : List Bool → List Bool) (z : List Bool) := pair (radial (pairFst z)) (pairSnd z)
theorem read_FP (radial : List Bool → List Bool) (hr : radial ∈ FP) : read radial ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP hr) pairSnd_mem_FP

private noncomputable def selectedValue (c indices : List Bool) (x : ℕ → ℝ) :=
  (FormulaSignSlotRadialCenterCoefficient.polynomial c
    (Nat.fromBitsLE (WordList.get indices 0)) (Nat.fromBitsLE (WordList.get indices 1))
    (Nat.fromBitsLE (WordList.get indices 2))).eval₂ (Int.castRingHom ℝ) (fun i => x i.val)
private noncomputable def sourceValue (z : List Bool) (x : ℕ → ℝ) :=
  (FormulaSignSlotRadialCenterCoefficientSource.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i => x i.val)
private theorem sourceValue_selected (z : List Bool) (x : ℕ → ℝ) :
    sourceValue z x = selectedValue (pairFst z) (pairSnd z) x := rfl

attribute [local irreducible] selectedValue

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R) (outer : Bool) (radial refs : List Bool → List Bool)

noncomputable def value := FormulaSignSlotRadialMarkedCenterTest.value hn ht ha hR outer (read radial) refs
theorem evaluator (hs : radial ∈ FP) (hf : refs ∈ FP) : SpaceFunction (value hn ht ha hR outer radial refs) :=
  FormulaSignSlotRadialMarkedCenterTest.evaluator hn ht ha hR outer (read radial) refs (read_FP radial hs) hf

noncomputable def center (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (i : Fin (d (pairFst (radial c)))) : ℝ :=
  FormulaSignSlotRadialBankCenterTest.center (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer)
    (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR outer) (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR outer)
    refs c w hv i.val

theorem packet (c w indices : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w) :
    value hn ht ha hR outer radial refs (pair (pair c w) indices) = InfinitesimalSign.encode
      (SignType.sign ((FormulaSignSlotRadialCenterCoefficient.polynomial (radial c)
        (Nat.fromBitsLE (WordList.get indices 0)) (Nat.fromBitsLE (WordList.get indices 1))
        (Nat.fromBitsLE (WordList.get indices 2))).eval₂ (Int.castRingHom ℝ)
          (center hn ht ha hR outer radial refs c w hv))) := by
  let x : ℕ → ℝ := FormulaSignSlotRadialBankCenterTest.center
    (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer) (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR outer)
      (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR outer) refs c w hv
  have H := FormulaSignSlotRadialMarkedCenterTest.packet hn ht ha hR outer (read radial) refs c w indices hv
  change value hn ht ha hR outer radial refs (pair (pair c w) indices) =
    InfinitesimalSign.encode (SignType.sign (sourceValue (read radial (pair c indices)) x)) at H
  rw [sourceValue_selected] at H
  simp only [read, pairFst_pair, pairSnd_pair] at H
  unfold selectedValue at H
  exact H

def indices (s t r : ℕ) := WordList.encode [BinaryNatCode.encode s, BinaryNatCode.encode t, BinaryNatCode.encode r]

theorem zero_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (s t r : ℕ) :
    value hn ht ha hR outer radial refs (pair (pair c w) (indices s t r)) = InfinitesimalSign.encode 0 ↔
      FormulaSignSlotRadialCenterSelection.Zero (radial c) (center hn ht ha hR outer radial refs c w hv) s t r := by
  rw [packet hn ht ha hR outer radial refs c w (indices s t r) hv]
  simp only [indices, WordList.get_encode, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff

end LeanCanny.Encoding.FormulaSignSlotRadialRetainedCenterTest
