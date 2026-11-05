/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientSource
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantRootProfiles
public import LeanCanny.Encoding.ChargedPolynomialCatalogue
/-! # Every bounded actual radial coefficient is a joint-center feature

The count is binary; coordinates, perturbation, target, and radius indices
are decoded from one mixed-radix ordinal. No product term is expanded.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientCatalogue
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S" => FormulaSignSlotRadialJointCoefficientSource.source

noncomputable def base (c : List Bool) := pair (FormulaSignSlotRadialJointLayout.source true c) []
noncomputable def degree (c : List Bool) := FormulaSignSlotRadialEliminantPacked.resultDegree (base c)
noncomputable def mass (c : List Bool) := FormulaSignSlotRadialCenterCoefficient.massBudget (base c)
noncomputable def limit (c : List Bool) := degree c+1
noncomputable def count (c : List Bool) := FormulaSignSlotRadialJointLayout.spatialCount c*(limit c*(limit c*limit c))
noncomputable def radiusIndex (c : List Bool) (i : ℕ) := i%limit c
noncomputable def targetIndex (c : List Bool) (i : ℕ) := (i/limit c)%limit c
noncomputable def tauIndex (c : List Bool) (i : ℕ) := (i/limit c/limit c)%limit c
noncomputable def coordinate (c : List Bool) (i : ℕ) := i/limit c/limit c/limit c
noncomputable def row (q : List Bool) := pair (pairFst q) (WordList.encode
  [BinaryNatCode.encode (coordinate (pairFst q) (Nat.fromBitsLE (pairSnd q))),
   BinaryNatCode.encode (tauIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))),
   BinaryNatCode.encode (targetIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))),
   BinaryNatCode.encode (radiusIndex (pairFst q) (Nat.fromBitsLE (pairSnd q)))])

theorem root_eq (c : List Bool) (i : ℕ) :
    pairFst (FormulaSignSlotRadialJointCoefficientSource.radial (row (pair c (BinaryNatCode.encode i))))=pairFst (base c) := by
  rw [FormulaSignSlotRadialJointCoefficientSource.radial_root]
  simp only [FormulaSignSlotRadialJointCoefficientSource.header,row,base,pairFst_pair]
theorem arity_eq (c : List Bool) (i : ℕ) :
    (S).arity (row (pair c (BinaryNatCode.encode i)))=FormulaSignSlotRadialJointLayout.dimension c := by
  change FormulaSignSlotRadialJointLayout.dimension
    (FormulaSignSlotRadialJointCoefficientSource.header (row (pair c (BinaryNatCode.encode i))))=_
  simp only [FormulaSignSlotRadialJointCoefficientSource.header,row,pairFst_pair]
theorem degree_eq (c : List Bool) (i : ℕ) : (S).degree (row (pair c (BinaryNatCode.encode i)))=degree c :=
  FormulaSignSlotRadialEliminantRootProfiles.degree_eq _ _ (root_eq c i)
private theorem mass_root (c e : List Bool) (H : pairFst c=pairFst e) :
    FormulaSignSlotRadialCenterCoefficient.massBudget c=FormulaSignSlotRadialCenterCoefficient.massBudget e := by
  simp only [FormulaSignSlotRadialCenterCoefficient.massBudget,FormulaSignSlotRadialEliminantRootProfiles.width_eq c e H,
    FormulaSignSlotRadialEliminantRootProfiles.mass_eq c e H,H]
theorem mass_eq (c : List Bool) (i : ℕ) : (S).mass (row (pair c (BinaryNatCode.encode i)))=mass c := mass_root _ _ (root_eq c i)

noncomputable def input : ChargedPolynomialCatalogue.Input where
  source := S
  row := row
  arity := FormulaSignSlotRadialJointLayout.dimension
  count := count
  degree := degree
  mass := mass
  dimension := arity_eq
  degree_bound c i := (degree_eq c i).le
  mass_bound c i := (mass_eq c i).le
noncomputable def family := ChargedPolynomialCatalogue.family input

theorem base_FP : base ∈ FP := mem_FP_pair (FormulaSignSlotRadialJointLayout.source_FP true) (constFn_mem_FP [])
theorem degree_binary : BinaryFn degree := FormulaSignSlotRadialEliminantFormalMass.degree_binary.comp base_FP
theorem mass_binary : BinaryFn mass := FormulaSignSlotRadialCenterCoefficient.massBudget_binary.comp base_FP
theorem limit_binary : BinaryFn limit := degree_binary.add (BinaryFn.const 1)
theorem count_binary : BinaryFn count := (BinaryFn.ofUnary FormulaSignSlotRadialJointLayout.spatialCount_unary).mul
  (limit_binary.mul (limit_binary.mul limit_binary))
theorem row_FP : row ∈ FP := by
  have HI : BinaryFn (fun q => Nat.fromBitsLE (pairSnd q)) := BinaryFn.fromBits pairSnd_mem_FP
  have HL : BinaryFn (fun q => limit (pairFst q)) := limit_binary.comp pairFst_mem_FP
  have HR : BinaryFn (fun q => radiusIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))) := HI.mod HL
  have HT : BinaryFn (fun q => targetIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))) := (HI.div HL).mod HL
  have HS : BinaryFn (fun q => tauIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))) := ((HI.div HL).div HL).mod HL
  have HC : BinaryFn (fun q => coordinate (pairFst q) (Nat.fromBitsLE (pairSnd q))) := ((HI.div HL).div HL).div HL
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair HC.bits_mem_FP (mem_FP_pair HS.bits_mem_FP
    (mem_FP_pair HT.bits_mem_FP (mem_FP_pair HR.bits_mem_FP (constFn_mem_FP [])))))

theorem source_fit (z : List Bool) : FormulaSignSlotRadialJointCoefficientSource.source.degree z <
    2^FormulaSignSlotRadialJointCoefficientSource.source.width z := by
  dsimp only [FormulaSignSlotRadialJointCoefficientSource.source,IntegralFramedBankPolynomialEmbedding.source]
  exact FormulaSignSlotRadialJointCoefficientSource.degree_fit z

noncomputable def input_access : ChargedPolynomialCatalogue.Access input where
  source := FormulaSignSlotRadialJointCoefficientSource.access
  row := row_FP
  arity := FormulaSignSlotRadialJointLayout.dimension_unary
  count := count_binary
  degree := degree_binary
  mass := mass_binary
  fit := source_fit
noncomputable def access : SquareFeatureProductFamily.Access family := ChargedPolynomialCatalogue.access input input_access

end LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientCatalogue
