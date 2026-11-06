/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiSource
public import LeanCanny.Encoding.ChargedPolynomialCatalogue
/-! # A complete window-control catalogue for one actual radius-first source

The raw source context is retained verbatim. Only the bounded head degree,
seed degree, principal/coefficient index, role and moment are enumerated.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralPolynomialWindowTarskiCatalogue
open LeanCanny.Algebra LeanCanny.Computation
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def limit (S:Source) (c:List Bool):=S.degree c+2
noncomputable def count (S:Source) (c:List Bool):=6*(limit S c*(limit S c*limit S c))
noncomputable def degree (S:Source) (c:List Bool):=MultivariateTarskiDegreeBounds.principalDegreeBound
  (S.degree c+1) (S.degree c) (S.degree c+5) (S.degree c) 2
noncomputable def mass (S:Source) (c:List Bool):=
  FixedWidthTarskiMass.principalMass (S.degree c+1) (S.degree c) (S.degree c+5) (S.degree c) 4 (S.mass c) 2+
    (S.mass c+FixedWidthTarskiMass.seedMass (S.degree c+5) (S.degree c) 4 (S.mass c) 2)
noncomputable def control (c:List Bool) (d s:ℕ) (square:Bool):=
  pair c (pair (BinaryNatCode.encode d) (pair (BinaryNatCode.encode s) (if square then [true] else [])))
noncomputable def orderIndex (S:Source) (c:List Bool) (i:ℕ):=i/6%limit S c
noncomputable def seedIndex (S:Source) (c:List Bool) (i:ℕ):=i/6/limit S c%limit S c
noncomputable def degreeIndex (S:Source) (c:List Bool) (i:ℕ):=i/6/limit S c/limit S c%limit S c
noncomputable def square (i:ℕ):Bool:=decide ((i/3)%2=1)
noncomputable def row (S:Source) (q:List Bool):=pair (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q)%3))
  (pair (control (pairFst q) (degreeIndex S (pairFst q) (Nat.fromBitsLE (pairSnd q)))
    (seedIndex S (pairFst q) (Nat.fromBitsLE (pairSnd q))) (square (Nat.fromBitsLE (pairSnd q))))
    (BinaryNatCode.encode (orderIndex S (pairFst q) (Nat.fromBitsLE (pairSnd q)))))

theorem count_binary (S:Source) (A:IntegralFramedBankPolynomialModel.Access S):BinaryFn (count S):=by
  have HL:BinaryFn (limit S):=A.degree.add (BinaryFn.const 2)
  exact (BinaryFn.const 6).mul (HL.mul (HL.mul HL))
theorem degree_binary (S:Source) (A:IntegralFramedBankPolynomialModel.Access S):BinaryFn (degree S):=
  MultivariateTarskiDegreeBounds.principalDegreeBound_binary (A.degree.add (BinaryFn.const 1)) A.degree
    (A.degree.add (BinaryFn.const 5)) A.degree (BinaryFn.const 2)
theorem mass_binary (S:Source) (A:IntegralFramedBankPolynomialModel.Access S):BinaryFn (mass S):=
  (FixedWidthTarskiMass.principalMass_binary (A.degree.add (BinaryFn.const 1)) A.degree
    (A.degree.add (BinaryFn.const 5)) A.degree (BinaryFn.const 4) A.mass (BinaryFn.const 2)).add
    (A.mass.add (FixedWidthTarskiMass.seedMass_binary (A.degree.add (BinaryFn.const 5)) A.degree (BinaryFn.const 4) A.mass (BinaryFn.const 2)))

private theorem parameter_mass_mono (R T a:ℕ) (H:R ≤ T):
    PrincipalSubresultant.parameterMassBound R a ≤ PrincipalSubresultant.parameterMassBound T a:=by
  unfold PrincipalSubresultant.parameterMassBound
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul (Nat.size_le_size H) H) (Nat.mul_le_mul_right _ H)) a

theorem family_degree_bound (S:Source) (c z:List Bool) (HI:IntegralPolynomialWindowTarski.inputBound S z=S.degree c):
    IntegralPolynomialWindowTarski.outputBound S z ≤ degree S c:=by
  have HD:IntegralPolynomialWindowTarski.degree S z ≤ S.degree c+1:=by
    unfold IntegralPolynomialWindowTarski.degree
    rw [HI]
    exact Nat.add_le_add_right (Nat.min_le_right _ _) 1
  have HS:IntegralPolynomialWindowTarski.seedDegree S z ≤ S.degree c:=by
    unfold IntegralPolynomialWindowTarski.seedDegree
    rw [HI]
    exact Nat.min_le_right _ _
  unfold IntegralPolynomialWindowTarski.outputBound IntegralPolynomialWindowTarski.bound degree
    MultivariateTarskiDegreeBounds.principalDegreeBound
  rw [HI]
  exact Nat.mul_le_mul_right _ (by omega)

theorem family_mass_bound (S:Source) (c z:List Bool) (HO:IntegralPolynomialWindowTarski.original z=c):
    IntegralPolynomialWindowTarski.massBudget S z+IntegralPolynomialWindowTarski.selectionMass S z ≤ mass S c:=by
  have HI:IntegralPolynomialWindowTarski.inputBound S z=S.degree c:=by unfold IntegralPolynomialWindowTarski.inputBound;rw [HO]
  have HD:IntegralPolynomialWindowTarski.degree S z ≤ S.degree c+1:=by
    unfold IntegralPolynomialWindowTarski.degree
    rw [HI]
    exact Nat.add_le_add_right (Nat.min_le_right _ _) 1
  have HS:IntegralPolynomialWindowTarski.seedDegree S z ≤ S.degree c:=by
    unfold IntegralPolynomialWindowTarski.seedDegree
    rw [HI]
    exact Nat.min_le_right _ _
  unfold IntegralPolynomialWindowTarski.massBudget IntegralPolynomialWindowTarski.selectionMass
    IntegralPolynomialWindowTarski.seedInputMass IntegralPolynomialWindowTarski.bound mass
  rw [HI,HO]
  apply Nat.add_le_add_right
  unfold FixedWidthTarskiMass.principalMass
  exact parameter_mass_mono _ _ _ (by omega)

theorem controls_original (S:Source) (c:List Bool) (i:ℕ):
    IntegralPolynomialWindowTarski.original (IntegralPolynomialWindowTarski.control (row S (pair c (BinaryNatCode.encode i))))=c:=by
  simp only [IntegralPolynomialWindowTarski.control,IntegralPolynomialWindowTarski.original,
    FormulaSignSlotRadialRadiusTarskiFamily.original,row,control,pairFst_pair,pairSnd_pair]

theorem dimension (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (c:List Bool) (i:ℕ):
    (IntegralPolynomialWindowTarski.source S N hd).arity (row S (pair c (BinaryNatCode.encode i)))=S.arity c:=by
  change N (IntegralPolynomialWindowTarski.original (IntegralPolynomialWindowTarski.control
    (row S (pair c (BinaryNatCode.encode i)))))+1=S.arity c
  rw [controls_original]
  exact (hd c).symm

theorem degree_bound (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (c:List Bool) (i:ℕ):
    (IntegralPolynomialWindowTarski.source S N hd).degree (row S (pair c (BinaryNatCode.encode i))) ≤ degree S c:=by
  apply family_degree_bound S c
  unfold IntegralPolynomialWindowTarski.inputBound
  rw [controls_original]
theorem mass_bound (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (c:List Bool) (i:ℕ):
    (IntegralPolynomialWindowTarski.source S N hd).mass (row S (pair c (BinaryNatCode.encode i))) ≤ mass S c:=
  family_mass_bound S c _ (controls_original S c i)

theorem row_FP (S:Source) (A:IntegralFramedBankPolynomialModel.Access S):row S∈FP:=by
  have HI:BinaryFn (fun q=>Nat.fromBitsLE (pairSnd q)):=BinaryFn.fromBits pairSnd_mem_FP
  have HL:BinaryFn (fun q=>limit S (pairFst q)):=(A.degree.add (BinaryFn.const 2)).comp pairFst_mem_FP
  have H0:BinaryFn (fun q=>Nat.fromBitsLE (pairSnd q)/6):=HI.div (BinaryFn.const 6)
  have HJ:BinaryFn (fun q=>orderIndex S (pairFst q) (Nat.fromBitsLE (pairSnd q))):=H0.mod HL
  have H1:=H0.div HL
  have HS:BinaryFn (fun q=>seedIndex S (pairFst q) (Nat.fromBitsLE (pairSnd q))):=H1.mod HL
  have H2:=H1.div HL
  have HD:BinaryFn (fun q=>degreeIndex S (pairFst q) (Nat.fromBitsLE (pairSnd q))):=H2.mod HL
  have HR:BinaryFn (fun q=>Nat.fromBitsLE (pairSnd q)%3):=HI.mod (BinaryFn.const 3)
  have HM:BinaryFn (fun q=>(Nat.fromBitsLE (pairSnd q)/3)%2):=(HI.div (BinaryFn.const 3)).mod (BinaryFn.const 2)
  have HB:(fun q=>if square (Nat.fromBitsLE (pairSnd q)) then [true] else [])∈FP:=by
    simpa only [square,decide_eq_true_eq] using
      (HM.eq (BinaryFn.const 1)).ite_mem_FP (constFn_mem_FP [true]) (constFn_mem_FP [])
  exact mem_FP_pair HR.bits_mem_FP (mem_FP_pair
    (mem_FP_pair pairFst_mem_FP (mem_FP_pair HD.bits_mem_FP (mem_FP_pair HS.bits_mem_FP HB))) HJ.bits_mem_FP)

noncomputable def input (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1):ChargedPolynomialCatalogue.Input where
  source:=IntegralPolynomialWindowTarski.source S N hd
  row:=row S
  arity:=S.arity
  count:=count S
  degree:=degree S
  mass:=mass S
  dimension:=dimension S N hd
  degree_bound:=degree_bound S N hd
  mass_bound:=mass_bound S N hd
noncomputable def family (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1):=ChargedPolynomialCatalogue.family (input S N hd)
noncomputable def input_access (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1)
    (A:IntegralFramedBankPolynomialModel.Access S) (HN:UnaryFn N) (hfit:∀c,S.degree c < 2^S.width c):
    ChargedPolynomialCatalogue.Access (input S N hd) where
  source:=IntegralPolynomialWindowTarski.sourceAccess S N hd A HN hfit
  row:=row_FP S A
  arity:=A.arity
  count:=count_binary S A
  degree:=degree_binary S A
  mass:=mass_binary S A
  fit:=IntegralPolynomialWindowTarski.degree_fit S N hd
noncomputable def access (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1)
    (A:IntegralFramedBankPolynomialModel.Access S) (HN:UnaryFn N) (hfit:∀c,S.degree c < 2^S.width c):
    SquareFeatureProductFamily.Access (family S N hd):=
  ChargedPolynomialCatalogue.access (input S N hd) (input_access S N hd A HN hfit)

end LeanCanny.Encoding.IntegralPolynomialWindowTarskiCatalogue
