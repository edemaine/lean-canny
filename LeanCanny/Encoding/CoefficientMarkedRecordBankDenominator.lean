/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordBankProducts
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardSpace
/-! # The literal single retained denominator as an integer parameter polynomial -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordBankDenominator
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open IntegralMixedFramedPhysicalLayoutCongruence
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def zeroExtended {R:Type*} [Zero R] {m:ℕ} (d:Fin m→R) (i:ℕ):R:=
  if hi:i<m then d ⟨i,hi⟩ else 0

private noncomputable def stateDenominator {n S B m:ℕ} {P:SpatialSource n} {I:Type}
    (x:State P S B m I) (i:ℕ):ℤ:=zeroExtended x.bank.denominator i

private theorem stateDenominator_transport {a b S T B C m k:ℕ} {P:SpatialSource a} {Q:SpatialSource b}
    {I J:Type} (x:State P S B m I) (y:State Q T C k J)
    (en:a=b) (eS:S=T) (eB:B=C) (em:m=k) (eP:HEq P Q) (eI:I=J) (he:HEq x y) (i:ℕ):
    stateDenominator x i=stateDenominator y i:=by
  cases en
  cases eS
  cases eB
  cases em
  cases eI
  cases eq_of_heq eP
  cases eq_of_heq he
  rfl

private theorem stateDenominator_family (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key:List Bool) (i:ℕ):
    stateDenominator ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key) i=
      IntegralMixedFramedCriticalGuardBits.atKey (IntegralMixedFramedHistoryFamilyBits.family P D H) key i:=rfl

variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

noncomputable def polynomial (ctx:List Bool) (k i:ℕ):ℤ[X]:=
  zeroExtended (CoefficientMarkedRecordBankProducts.symbolicPrefix hn ht ha ctx k).bank.denominator i

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  IntegralMixedSourceIntegerRecordAppend.plan CoefficientMarkedRecordRowLayout.commands

private theorem native_denominator (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool) (i:ℕ):
    stateDenominator (CoefficientMarkedRecordNative.run hn ht ha ctx R (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
      (CoefficientMarkedRecordActual.codes ctx k) (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk)) i=
      IntegralMixedFramedCriticalGuardBits.atKey (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R)
        (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux) i:=by
  have HL:=(CoefficientMarkedRecordRowLayout.family_layout hn ht ha ctx R k hk aux).symm
  exact (stateDenominator_transport _ _
    (CoefficientMarkedRecordRows.family_ambient hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_cap hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_width hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_birth hn ht ha ctx R k hk aux)
    (CoefficientMarkedRecordRows.family_source hn ht ha ctx R k aux)
    (congrArg Layout.index HL) (CoefficientMarkedRecordActual.native_family hn ht ha ctx R k hk aux) i).trans
      (stateDenominator_family _ _ _ _ i)

theorem specializes (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool)
    (hlarge:CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx≤R ctx) (i:ℕ):
    (polynomial hn ht ha ctx k i).eval ((2:ℤ)^R ctx)=
      IntegralMixedFramedCriticalGuardBits.atKey (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R)
        (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux) i:=by
  obtain ⟨ψ,_,HB,_,_⟩:=CoefficientMarkedRecordEffectiveCutoff.specializes_above_effective hn ht ha ctx R k hk hlarge
  let x:=CoefficientMarkedRecordNative.run hn ht ha ctx R (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
    (CoefficientMarkedRecordActual.codes ctx k) (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk)
  have HP:(polynomial hn ht ha ctx k i).eval ((2:ℤ)^R ctx)=stateDenominator x i:=by
    unfold polynomial stateDenominator zeroExtended
    split_ifs
    · exact HB.denominator _
    · exact Polynomial.eval_zero
  exact HP.trans (native_denominator hn ht ha ctx R k hk aux i)

noncomputable def coefficientBudget (ctx:List Bool):ℕ:=
  IntegerPolynomialDyadic.massBudget (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankSlope hn ht ha ctx)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankOffset hn ht ha ctx)

theorem coefficientBudget_binary:BinaryFn (coefficientBudget hn ht ha):=
  IntegerPolynomialDyadic.massBudget_binary (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankSlope_binary hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankOffset_binary hn ht ha)

private theorem native_bound (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ) (aux:List Bool) (i:ℕ):
    (IntegralMixedFramedCriticalGuardBits.atKey (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R)
      (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux) i).natAbs≤
      2^(IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankSlope hn ht ha ctx*R ctx+
        IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankOffset hn ht ha ctx):=by
  unfold IntegralMixedFramedCriticalGuardBits.atKey
  split_ifs
  · have HB:=IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bank_bounds hn ht ha R
      (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux)
    simpa only [CoefficientMarkedRecordRowLayout.key_root] using HB.denominator _
  · exact Nat.zero_le _

theorem degree_mass (ctx:List Bool) (k:ℕ) (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (i:ℕ):
    (polynomial hn ht ha ctx k i).natDegree≤IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankSlope hn ht ha ctx ∧
      coefficientMass (polynomial hn ht ha ctx k i)≤2^coefficientBudget hn ht ha ctx:=by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  rw [specializes hn ht ha ctx (fun _=>r) k hk [] hr i]
  exact native_bound hn ht ha ctx (fun _=>r) k [] i

end LeanCanny.Encoding.CoefficientMarkedRecordBankDenominator
