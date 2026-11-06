/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientSource
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantRootProfiles
public import LeanCanny.Encoding.ChargedPolynomialCatalogue
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGuardFeatures
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
noncomputable def rawFamily := ChargedPolynomialCatalogue.family input
noncomputable def family := SquareFeatureProductAppend.family rawFamily
  FormulaSignSlotRadialJointGuardFeatures.family (fun _ => rfl)

theorem raw_feature (c : List Bool) (i : ℕ) (hi : i < count c) :
    family.feature c i = rawFamily.feature c i :=
  SquareFeatureProductAppend.feature_left rawFamily FormulaSignSlotRadialJointGuardFeatures.family
    (fun _ => rfl) c i hi

theorem raw_count_le (c : List Bool) : count c ≤ family.count c := Nat.le_add_right _ _

private theorem evaluate_cast {n m : ℕ} (h : n = m) (p : MvPolynomial (Fin n) ℤ)
    (v : ℕ → ℝ) :
    (MvPolynomial.rename (Fin.cast h) p).eval₂ (Int.castRingHom ℝ) (fun i => v i.val) =
      p.eval₂ (Int.castRingHom ℝ) (fun i => v i.val) := by
  subst m
  simp only [Fin.cast_refl, MvPolynomial.rename_id, AlgHom.id_apply]

theorem guard_feature_eval (c : List Bool) (i : ℕ)
    (hi : i < FormulaSignSlotRadialJointGuardFeatures.family.count c) (v : ℕ → ℝ) :
    (family.feature c (count c + i)).eval₂ (Int.castRingHom ℝ) (fun j => v j.val) =
      (FormulaSignSlotRadialJointGuardFeatures.family.feature c i).eval₂ (Int.castRingHom ℝ) (fun j => v j.val) := by
  have H := SquareFeatureProductAppend.feature_right rawFamily FormulaSignSlotRadialJointGuardFeatures.family
    (fun _ => rfl) c i hi
  exact (congrArg (fun p => p.eval₂ (Int.castRingHom ℝ) (fun j => v j.val)) H).trans
    (evaluate_cast rfl _ v)

theorem grid_feature_eval (c : List Bool) (i : ℕ)
    (hi : i < FormulaSignSlotRadialJointGridCompleteCatalogue.family.count c) (v : ℕ → ℝ) :
    (family.feature c (count c + i)).eval₂ (Int.castRingHom ℝ) (fun j => v j.val) =
      (FormulaSignSlotRadialJointGridCompleteCatalogue.family.feature c i).eval₂ (Int.castRingHom ℝ) (fun j => v j.val) := by
  have H : i < FormulaSignSlotRadialJointGuardFeatures.family.count c :=
    hi.trans_le (FormulaSignSlotRadialJointGuardFeatures.grid_count_le c)
  exact (guard_feature_eval c i H v).trans
    (congrArg (fun p => p.eval₂ (Int.castRingHom ℝ) (fun j => v j.val))
      (FormulaSignSlotRadialJointGuardFeatures.grid_feature c i hi))

noncomputable def principalIndex (c : List Bool) (i : ℕ) :=
  count c + FormulaSignSlotRadialJointGuardFeatures.principalIndex c i
noncomputable def valueIndex (c : List Bool) (i : ℕ) :=
  count c + FormulaSignSlotRadialJointGuardFeatures.valueIndex c i

theorem principal_feature_eval (c : List Bool) (i : ℕ)
    (hi : i < FormulaSignSlotRadialJointPrincipalWindowCatalogue.family.count c) (v : ℕ → ℝ) :
    (family.feature c (principalIndex c i)).eval₂ (Int.castRingHom ℝ) (fun j => v j.val) =
      (FormulaSignSlotRadialJointPrincipalWindowCatalogue.family.feature c i).eval₂ (Int.castRingHom ℝ) (fun j => v j.val) :=
  (guard_feature_eval c _ (FormulaSignSlotRadialJointGuardFeatures.principal_index_lt c i hi) v).trans
    (FormulaSignSlotRadialJointGuardFeatures.principal_feature_eval c i hi v)

theorem value_feature_eval (c : List Bool) (i : ℕ)
    (hi : i < FormulaSignSlotRadialJointValueWindowCatalogue.family.count c) (v : ℕ → ℝ) :
    (family.feature c (valueIndex c i)).eval₂ (Int.castRingHom ℝ) (fun j => v j.val) =
      (FormulaSignSlotRadialJointValueWindowCatalogue.family.feature c i).eval₂ (Int.castRingHom ℝ) (fun j => v j.val) :=
  (guard_feature_eval c _ (FormulaSignSlotRadialJointGuardFeatures.value_index_lt c i hi) v).trans
    (FormulaSignSlotRadialJointGuardFeatures.value_feature_eval c i hi v)

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
noncomputable def raw_access : SquareFeatureProductFamily.Access rawFamily :=
  ChargedPolynomialCatalogue.access input input_access
noncomputable def access : SquareFeatureProductFamily.Access family :=
  SquareFeatureProductAppend.access rawFamily FormulaSignSlotRadialJointGuardFeatures.family
    (fun _ => rfl) raw_access FormulaSignSlotRadialJointGuardFeatures.access

end LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientCatalogue
