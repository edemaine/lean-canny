/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiKernelSource
public import LeanCanny.Encoding.ChargedPolynomialCatalogue
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantRootProfiles
/-! # Complete finite controls for actual coordinate-head radius queries

This catalogue covers coordinate leading/trailing heads and their window
principals. Separate PSC and value-certificate radius families are needed
for the other cut classes. Every variable is still [endpoint,center].
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiCatalogue
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def inputDegree (c:List Bool):=FormulaSignSlotRadialEliminantPacked.resultDegree c
noncomputable def inputMass (c:List Bool):=FormulaSignSlotRadialCenterCoefficient.massBudget c
noncomputable def limit (c:List Bool):=inputDegree c+2
noncomputable def count (c:List Bool):=6*(limit c*(limit c*(limit c*(limit c*limit c))))
noncomputable def arity (c:List Bool):=FormulaSignSlotCenteredRadialGraph.d (pairFst c)+1
noncomputable def degree (c:List Bool):=MultivariateTarskiDegreeBounds.principalDegreeBound
  (inputDegree c+1) (inputDegree c) (inputDegree c+5) (inputDegree c) 2
noncomputable def mass (c:List Bool):=
  FixedWidthTarskiMass.principalMass (inputDegree c+1) (inputDegree c) (inputDegree c+5)
    (inputDegree c) 4 (inputMass c) 2+
  (inputMass c+FixedWidthTarskiMass.seedMass (inputDegree c+5) (inputDegree c) 4 (inputMass c) 2)

noncomputable def headContext (c:List Bool) (tau eta:ℕ):=pair c (pair (BinaryNatCode.encode tau) (BinaryNatCode.encode eta))
noncomputable def familyContext (c:List Bool) (tau eta d s:ℕ) (square:Bool):=
  pair (headContext c tau eta) (pair (BinaryNatCode.encode d) (pair (BinaryNatCode.encode s) (if square then [true] else [])))
noncomputable def roleWord (i:ℕ):=if i%3=0 then [] else if i%3=1 then [false] else [true]
noncomputable def order (c:List Bool) (i:ℕ):=i/6%limit c
noncomputable def seed (c:List Bool) (i:ℕ):=i/6/limit c%limit c
noncomputable def declared (c:List Bool) (i:ℕ):=i/6/limit c/limit c%limit c
noncomputable def eta (c:List Bool) (i:ℕ):=i/6/limit c/limit c/limit c%limit c
noncomputable def tau (c:List Bool) (i:ℕ):=i/6/limit c/limit c/limit c/limit c%limit c
noncomputable def square (i:ℕ):Bool:=decide ((i/3)%2=1)
noncomputable def row (q:List Bool):=pair (roleWord (Nat.fromBitsLE (pairSnd q)))
  (pair (familyContext (pairFst q) (tau (pairFst q) (Nat.fromBitsLE (pairSnd q)))
    (eta (pairFst q) (Nat.fromBitsLE (pairSnd q))) (declared (pairFst q) (Nat.fromBitsLE (pairSnd q)))
    (seed (pairFst q) (Nat.fromBitsLE (pairSnd q))) (square (Nat.fromBitsLE (pairSnd q))))
      (BinaryNatCode.encode (order (pairFst q) (Nat.fromBitsLE (pairSnd q)))))

theorem inputDegree_binary:BinaryFn inputDegree:=FormulaSignSlotRadialEliminantFormalMass.degree_binary
theorem inputMass_binary:BinaryFn inputMass:=FormulaSignSlotRadialCenterCoefficient.massBudget_binary
theorem limit_binary:BinaryFn limit:=inputDegree_binary.add (BinaryFn.const 2)
theorem count_binary:BinaryFn count:=(BinaryFn.const 6).mul
  (limit_binary.mul (limit_binary.mul (limit_binary.mul (limit_binary.mul limit_binary))))
theorem arity_unary:UnaryFn arity:=(FormulaSignSlotSource.dimension_unary.comp pairFst_mem_FP).add (UnaryFn.const 1)
theorem degree_binary:BinaryFn degree:=MultivariateTarskiDegreeBounds.principalDegreeBound_binary
  (inputDegree_binary.add (BinaryFn.const 1)) inputDegree_binary (inputDegree_binary.add (BinaryFn.const 5))
  inputDegree_binary (BinaryFn.const 2)
theorem mass_binary:BinaryFn mass:=
  (FixedWidthTarskiMass.principalMass_binary (inputDegree_binary.add (BinaryFn.const 1)) inputDegree_binary
    (inputDegree_binary.add (BinaryFn.const 5)) inputDegree_binary (BinaryFn.const 4) inputMass_binary (BinaryFn.const 2)).add
  (inputMass_binary.add (FixedWidthTarskiMass.seedMass_binary (inputDegree_binary.add (BinaryFn.const 5))
    inputDegree_binary (BinaryFn.const 4) inputMass_binary (BinaryFn.const 2)))

theorem context_input (c:List Bool) (t e d s:ℕ) (b:Bool):
    FormulaSignSlotRadialRadiusTarskiFamily.inputBound (familyContext c t e d s b)=inputDegree c:=by
  simp only [FormulaSignSlotRadialRadiusTarskiFamily.inputBound,FormulaSignSlotRadialRadiusTarskiFamily.original,
    FormulaSignSlotRadialRadiusHeadReader.degree,FormulaSignSlotRadialRadiusHeadReader.original,
    familyContext,headContext,pairFst_pair,inputDegree]
theorem context_mass (c:List Bool) (t e d s:ℕ) (b:Bool):
    FormulaSignSlotRadialRadiusTarskiFamily.headInputMass (familyContext c t e d s b)=inputMass c:=by
  simp only [FormulaSignSlotRadialRadiusTarskiFamily.headInputMass,FormulaSignSlotRadialRadiusTarskiFamily.original,
    familyContext,headContext,pairFst_pair,inputMass]
theorem context_arity (c:List Bool) (t e d s:ℕ) (b:Bool):
    FormulaSignSlotRadialRadiusTarskiFamily.arity (familyContext c t e d s b)=arity c:=by
  simp only [FormulaSignSlotRadialRadiusTarskiFamily.arity,FormulaSignSlotRadialRadiusTarskiFamily.original,
    FormulaSignSlotRadialRadiusHeadReader.arity,FormulaSignSlotRadialRadiusHeadReader.original,
    familyContext,headContext,pairFst_pair,arity]

private theorem parameter_mass_mono (R S a:ℕ) (H:R ≤ S):
    PrincipalSubresultant.parameterMassBound R a ≤ PrincipalSubresultant.parameterMassBound S a:=by
  unfold PrincipalSubresultant.parameterMassBound
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul (Nat.size_le_size H) H)
    (Nat.mul_le_mul_right _ H)) a

theorem family_degree_bound (c z:List Bool) (HI:FormulaSignSlotRadialRadiusTarskiFamily.inputBound z=inputDegree c):
    FormulaSignSlotRadialRadiusTarskiFamily.outputBound z ≤ degree c:=by
  have HD:FormulaSignSlotRadialRadiusTarskiFamily.degree z ≤ inputDegree c+1:=by
    unfold FormulaSignSlotRadialRadiusTarskiFamily.degree
    rw [HI]
    exact Nat.add_le_add_right (Nat.min_le_right _ _) 1
  have HS:FormulaSignSlotRadialRadiusTarskiFamily.seedDegree z ≤ inputDegree c:=by
    unfold FormulaSignSlotRadialRadiusTarskiFamily.seedDegree
    rw [HI]
    exact Nat.min_le_right _ _
  unfold FormulaSignSlotRadialRadiusTarskiFamily.outputBound FormulaSignSlotRadialRadiusTarskiFamily.bound degree
    MultivariateTarskiDegreeBounds.principalDegreeBound
  rw [HI]
  exact Nat.mul_le_mul_right _ (by omega)

theorem family_mass_bound (c z:List Bool) (HI:FormulaSignSlotRadialRadiusTarskiFamily.inputBound z=inputDegree c)
    (HM:FormulaSignSlotRadialRadiusTarskiFamily.headInputMass z=inputMass c):
    FormulaSignSlotRadialRadiusTarskiFamily.massBudget z+FormulaSignSlotRadialRadiusTarskiFamily.selectionMass z ≤ mass c:=by
  have HD:FormulaSignSlotRadialRadiusTarskiFamily.degree z ≤ inputDegree c+1:=by
    unfold FormulaSignSlotRadialRadiusTarskiFamily.degree
    rw [HI]
    exact Nat.add_le_add_right (Nat.min_le_right _ _) 1
  have HS:FormulaSignSlotRadialRadiusTarskiFamily.seedDegree z ≤ inputDegree c:=by
    unfold FormulaSignSlotRadialRadiusTarskiFamily.seedDegree
    rw [HI]
    exact Nat.min_le_right _ _
  unfold FormulaSignSlotRadialRadiusTarskiFamily.massBudget FormulaSignSlotRadialRadiusTarskiFamily.selectionMass
    FormulaSignSlotRadialRadiusTarskiFamily.seedInputMass FormulaSignSlotRadialRadiusTarskiFamily.bound mass
  rw [HI,HM]
  apply Nat.add_le_add_right
  unfold FixedWidthTarskiMass.principalMass
  exact parameter_mass_mono _ _ _ (by omega)

local notation "S"=>FormulaSignSlotRadialRadiusTarskiKernelSource.source

theorem dimension (c:List Bool) (i:ℕ):(S).arity (row (pair c (BinaryNatCode.encode i)))=arity c:=by
  simp only [FormulaSignSlotRadialRadiusTarskiKernelSource.source,FormulaSignSlotRadialRadiusTarskiKernelSource.payload,
    FormulaSignSlotRadialRadiusTarskiSource.arity,FormulaSignSlotRadialRadiusTarskiSource.original,row,pairFst_pair,pairSnd_pair]
  exact context_arity _ _ _ _ _ _
theorem degree_bound (c:List Bool) (i:ℕ):(S).degree (row (pair c (BinaryNatCode.encode i))) ≤ degree c:=by
  simp only [FormulaSignSlotRadialRadiusTarskiKernelSource.source,FormulaSignSlotRadialRadiusTarskiKernelSource.payload,
    FormulaSignSlotRadialRadiusTarskiSource.degree,FormulaSignSlotRadialRadiusTarskiSource.original,row,pairFst_pair,pairSnd_pair]
  exact family_degree_bound _ _ (context_input _ _ _ _ _ _)
theorem mass_bound (c:List Bool) (i:ℕ):(S).mass (row (pair c (BinaryNatCode.encode i))) ≤ mass c:=by
  simp only [FormulaSignSlotRadialRadiusTarskiKernelSource.source,FormulaSignSlotRadialRadiusTarskiKernelSource.mass,
    FormulaSignSlotRadialRadiusTarskiKernelSource.payload,FormulaSignSlotRadialRadiusTarskiSource.mass,
    FormulaSignSlotRadialRadiusTarskiSelectionSource.mass,FormulaSignSlotRadialRadiusTarskiSource.original,row,pairFst_pair,pairSnd_pair]
  exact family_mass_bound _ _ (context_input _ _ _ _ _ _) (context_mass _ _ _ _ _ _)

theorem row_FP:row∈FP:=by
  have HI:BinaryFn (fun q=>Nat.fromBitsLE (pairSnd q)):=BinaryFn.fromBits pairSnd_mem_FP
  have HL:BinaryFn (fun q=>limit (pairFst q)):=limit_binary.comp pairFst_mem_FP
  have H0:BinaryFn (fun q=>Nat.fromBitsLE (pairSnd q)/6):=HI.div (BinaryFn.const 6)
  have HO:BinaryFn (fun q=>order (pairFst q) (Nat.fromBitsLE (pairSnd q))):=H0.mod HL
  have H1:=H0.div HL
  have HSeed:BinaryFn (fun q=>seed (pairFst q) (Nat.fromBitsLE (pairSnd q))):=H1.mod HL
  have H2:=H1.div HL
  have HD:BinaryFn (fun q=>declared (pairFst q) (Nat.fromBitsLE (pairSnd q))):=H2.mod HL
  have H3:=H2.div HL
  have HE:BinaryFn (fun q=>eta (pairFst q) (Nat.fromBitsLE (pairSnd q))):=H3.mod HL
  have H4:=H3.div HL
  have HT:BinaryFn (fun q=>tau (pairFst q) (Nat.fromBitsLE (pairSnd q))):=H4.mod HL
  have HRole:BinaryFn (fun q=>Nat.fromBitsLE (pairSnd q)%3):=HI.mod (BinaryFn.const 3)
  have HM:BinaryFn (fun q=>(Nat.fromBitsLE (pairSnd q)/3)%2):=(HI.div (BinaryFn.const 3)).mod (BinaryFn.const 2)
  have HR:(fun q=>roleWord (Nat.fromBitsLE (pairSnd q)))∈FP:=
    (HRole.eq (BinaryFn.const 0)).ite_mem_FP (constFn_mem_FP [])
      ((HRole.eq (BinaryFn.const 1)).ite_mem_FP (constFn_mem_FP [false]) (constFn_mem_FP [true]))
  have HB:(fun q=>if square (Nat.fromBitsLE (pairSnd q)) then [true] else [])∈FP:=by
    simpa only [square,decide_eq_true_eq] using
      (HM.eq (BinaryFn.const 1)).ite_mem_FP (constFn_mem_FP [true]) (constFn_mem_FP [])
  exact mem_FP_pair HR (mem_FP_pair
    (mem_FP_pair (mem_FP_pair pairFst_mem_FP (mem_FP_pair HT.bits_mem_FP HE.bits_mem_FP))
      (mem_FP_pair HD.bits_mem_FP (mem_FP_pair HSeed.bits_mem_FP HB))) HO.bits_mem_FP)

noncomputable def input:ChargedPolynomialCatalogue.Input where
  source:=S
  row:=row
  arity:=arity
  count:=count
  degree:=degree
  mass:=mass
  dimension:=dimension
  degree_bound:=degree_bound
  mass_bound:=mass_bound
noncomputable def family:=ChargedPolynomialCatalogue.family input
noncomputable def input_access:ChargedPolynomialCatalogue.Access input where
  source:=FormulaSignSlotRadialRadiusTarskiKernelSource.access
  row:=row_FP
  arity:=arity_unary
  count:=count_binary
  degree:=degree_binary
  mass:=mass_binary
  fit:=FormulaSignSlotRadialRadiusTarskiKernelSource.degree_fit
noncomputable def access:SquareFeatureProductFamily.Access family:=ChargedPolynomialCatalogue.access input input_access

theorem arity_eq (c:List Bool) (i:ℕ):(S).arity (row (pair c (BinaryNatCode.encode i)))=arity c:=dimension c i

theorem inputDegree_eq (c e:List Bool) (H:pairFst c=pairFst e):inputDegree c=inputDegree e:=
  FormulaSignSlotRadialEliminantRootProfiles.degree_eq c e H
theorem inputMass_eq (c e:List Bool) (H:pairFst c=pairFst e):inputMass c=inputMass e:=by
  simp only [inputMass,FormulaSignSlotRadialCenterCoefficient.massBudget,
    FormulaSignSlotRadialEliminantRootProfiles.width_eq c e H,
    FormulaSignSlotRadialEliminantRootProfiles.mass_eq c e H,H]
theorem count_eq (c e:List Bool) (H:pairFst c=pairFst e):count c=count e:=by
  simp only [count,limit,inputDegree_eq c e H]
theorem degree_eq (c e:List Bool) (H:pairFst c=pairFst e):degree c=degree e:=by
  simp only [degree,inputDegree_eq c e H]
theorem mass_eq (c e:List Bool) (H:pairFst c=pairFst e):mass c=mass e:=by
  simp only [mass,inputDegree_eq c e H,inputMass_eq c e H]

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiCatalogue
