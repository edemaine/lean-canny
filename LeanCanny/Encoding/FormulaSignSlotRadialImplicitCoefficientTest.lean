/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitSourceTest
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientSource
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientMeaning
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitGridTest
/-! # Actual radial coefficient zero tests on the stratum's same own word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitCoefficientTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input
local notation "G" => FormulaSignSlotRadialJointCoefficientSource.source

def header (c : List Bool) := FormulaSignSlotRadialImplicitGridTest.header c
def read (z : List Bool) := pair (header (pairFst z)) (pairSnd z)
theorem read_FP : read ∈ FP := mem_FP_pair
  (mem_FP_comp pairFst_mem_FP FormulaSignSlotRadialImplicitGridTest.header_FP) pairSnd_mem_FP
theorem source_dimension (z : List Bool) : (G).arity (read z)+1=(F).count (pairFst z) := by
  change FormulaSignSlotRadialJointLayout.dimension (pairFst (read z))+1 =
    FormulaSignSlotRadialJointLayout.dimension (header (pairFst z))+1
  rw [read,LeanCanny.pairFst_pair]
theorem degree_fit (z : List Bool) : (G).degree z < 2^(G).width z :=
  FormulaSignSlotRadialJointCoefficientCatalogue.source_fit z

noncomputable def value := FormulaSignSlotRadialImplicitSourceTest.value G read source_dimension degree_fit
theorem evaluator : SpaceFunction value :=
  FormulaSignSlotRadialImplicitSourceTest.evaluator G read source_dimension degree_fit read_FP
    FormulaSignSlotRadialJointCoefficientSource.access
noncomputable def env := FormulaSignSlotRadialImplicitSourceTest.env

def indices (j s t r : ℕ) := WordList.encode
  [BinaryNatCode.encode j,BinaryNatCode.encode s,BinaryNatCode.encode t,BinaryNatCode.encode r]

private noncomputable def entry (c : List Bool) (s t r : ℕ) (v : ℕ → ℝ) : ℝ :=
  (FormulaSignSlotRadialCenterCoefficient.polynomial c s t r).eval₂ (Int.castRingHom ℝ) (fun i => v (4*i.val))
private noncomputable def rawValue (z : List Bool) (v : ℕ → ℝ) : ℝ :=
  (FormulaSignSlotRadialRetainedCoordinateTest.source.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i => v (4*i.val))
private noncomputable def jointValue (z : List Bool) (v : ℕ → ℝ) : ℝ :=
  (FormulaSignSlotRadialJointCoefficientSource.source.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i => v i.val)

private theorem joint_read (z : List Bool) (v : ℕ → ℝ) : jointValue z v=
    rawValue (FormulaSignSlotRadialJointCoefficientSource.read z) v :=
  FormulaSignSlotRadialJointCoefficientSource.evaluation z v

private theorem rawValue_entry (z : List Bool) (v : ℕ → ℝ) : rawValue z v = entry (pairFst z)
    (FormulaSignSlotRadialCenterCoefficientSource.selected 0 z)
    (FormulaSignSlotRadialCenterCoefficientSource.selected 1 z)
    (FormulaSignSlotRadialCenterCoefficientSource.selected 2 z) v := rfl
attribute [local irreducible] entry rawValue
private theorem rawValue_read (z : List Bool) (v : ℕ → ℝ) : rawValue (FormulaSignSlotRadialJointCoefficientSource.read z) v =
    entry (FormulaSignSlotRadialCoordinatePacket.writer
      (pair (FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialJointCoefficientSource.header z))
        (FormulaSignSlotRadialJointCoefficientSource.slot 0 z)))
      (Nat.fromBitsLE (FormulaSignSlotRadialJointCoefficientSource.slot 1 z))
      (Nat.fromBitsLE (FormulaSignSlotRadialJointCoefficientSource.slot 2 z))
      (Nat.fromBitsLE (FormulaSignSlotRadialJointCoefficientSource.slot 3 z)) v := by
  rw [rawValue_entry]
  simp only [FormulaSignSlotRadialJointCoefficientSource.read,FormulaSignSlotRadialCenterCoefficientSource.selected,
    pairFst_pair,pairSnd_pair,WordList.get_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

private theorem source_packet (c : List Bool) (j s t r : ℕ) (v : ℕ → ℝ) :
    ((G).polynomial (pair c (indices j s t r))).eval₂ (Int.castRingHom ℝ) (fun i => v i.val) =
      FormulaSignSlotRadialJointCoefficientCatalogue.coefficientValue c j s t r v := by
  have H := joint_read
    (pair c (WordList.encode [BinaryNatCode.encode j,BinaryNatCode.encode s,BinaryNatCode.encode t,BinaryNatCode.encode r])) v
  refine H.trans ?_
  rw [rawValue_read]
  simp only [FormulaSignSlotRadialJointCoefficientSource.header,FormulaSignSlotRadialJointCoefficientSource.slot,
    pairFst_pair,pairSnd_pair,WordList.reader,WordList.get_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rw [show FormulaSignSlotRadialCoordinatePacket.writer
      (pair (FormulaSignSlotRadialJointLayout.source true c) j.bits)=
    FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true c) j from
      FormulaSignSlotRadialCoordinatePacket.writer_packet _ j]
  unfold entry FormulaSignSlotRadialJointCoefficientCatalogue.coefficientValue
  rfl

theorem packet (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) (j s t r : ℕ) :
    value (pair (pair c w) (indices j s t r)) = InfinitesimalSign.encode
      (SignType.sign (FormulaSignSlotRadialJointCoefficientCatalogue.coefficientValue
        (header c) j s t r (env c w hw))) := by
  rw [value,FormulaSignSlotRadialImplicitSourceTest.packet _ _ _ _ c w _ hw]
  have HR : read (pair c (indices j s t r)) = pair (header c) (indices j s t r) := by
    simp only [read,LeanCanny.pairFst_pair,LeanCanny.pairSnd_pair]
  have HE := source_packet (header c) j s t r (env c w hw)
  change InfinitesimalSign.encode (SignType.sign (jointValue (read (pair c (indices j s t r))) (env c w hw))) = _
  rw [HR]
  exact congrArg (fun a : ℝ => InfinitesimalSign.encode (SignType.sign a)) HE

theorem zero_packet (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) (j s t r : ℕ) :
    value (pair (pair c w) (indices j s t r)) = InfinitesimalSign.encode 0 ↔
      FormulaSignSlotRadialJointCoefficientCatalogue.coefficientValue (header c) j s t r (env c w hw) = 0 := by
  rw [packet c w hw j s t r]
  exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff

end LeanCanny.Encoding.FormulaSignSlotRadialImplicitCoefficientTest
