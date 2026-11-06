/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiOrdinal
public import LeanCanny.Encoding.FormulaSignSlotRadialPrincipalRadiusSource
public import LeanCanny.Encoding.FormulaSignSlotRadialValueRadiusSource
/-! # Actual PSC and value-certificate window factories

Every source, coefficient reader, dimension and bound is constructed from
the literal full-radius source. No abstract polynomial or access receipt is
an input to these concrete factories.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCutWindowSources
open LeanCanny.Algebra LeanCanny.Computation Polynomial MvPolynomial
open LeanCanny.Connectivity
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def principalRoot (c:List Bool):=pairFst (pairFst (pairFst c))
def valueRoot (c:List Bool):=pairFst (pairFst c)
noncomputable def principalCenters (c:List Bool):=FormulaSignSlotSource.dimension (principalRoot c)
noncomputable def valueCenters (c:List Bool):=FormulaSignSlotSource.dimension (valueRoot c)

theorem principalRoot_FP:principalRoot∈FP:=mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP
theorem valueRoot_FP:valueRoot∈FP:=mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem principalCenters_unary:UnaryFn principalCenters:=FormulaSignSlotSource.dimension_unary.comp principalRoot_FP
theorem valueCenters_unary:UnaryFn valueCenters:=FormulaSignSlotSource.dimension_unary.comp valueRoot_FP

theorem principal_dimension (c:List Bool):FormulaSignSlotRadialPrincipalRadiusSource.source.arity c=principalCenters c+1:=rfl
theorem value_dimension (c:List Bool):FormulaSignSlotRadialValueRadiusSource.source.arity c=valueCenters c+1:=rfl

attribute [local irreducible] FormulaSignSlotRadialPrincipalRadiusSource.degree
  FormulaSignSlotRadialPrincipalRadiusSource.width FormulaSignSlotRadialValueRadiusSource.degree
  FormulaSignSlotRadialValueRadiusSource.width

theorem principal_degree_fit (c:List Bool):FormulaSignSlotRadialPrincipalRadiusSource.source.degree c <
    2^FormulaSignSlotRadialPrincipalRadiusSource.source.width c:=FormulaSignSlotRadialPrincipalRadiusSource.degree_fit c
theorem value_degree_fit (c:List Bool):FormulaSignSlotRadialValueRadiusSource.source.degree c <
    2^FormulaSignSlotRadialValueRadiusSource.source.width c:=FormulaSignSlotRadialValueRadiusSource.degree_fit c

noncomputable def principalSource:IntegralFramedBankPolynomialModel.Source:=IntegralPolynomialWindowTarski.source
  FormulaSignSlotRadialPrincipalRadiusSource.source principalCenters principal_dimension
noncomputable def principalAccess:IntegralFramedBankPolynomialModel.Access principalSource:=IntegralPolynomialWindowTarski.sourceAccess
  FormulaSignSlotRadialPrincipalRadiusSource.source principalCenters principal_dimension
    FormulaSignSlotRadialPrincipalRadiusSource.access principalCenters_unary principal_degree_fit
noncomputable def principalFamily:=IntegralPolynomialWindowTarskiCatalogue.family
  FormulaSignSlotRadialPrincipalRadiusSource.source principalCenters principal_dimension
noncomputable def principalFamilyAccess:SquareFeatureProductFamily.Access principalFamily:=IntegralPolynomialWindowTarskiCatalogue.access
  FormulaSignSlotRadialPrincipalRadiusSource.source principalCenters principal_dimension
    FormulaSignSlotRadialPrincipalRadiusSource.access principalCenters_unary principal_degree_fit

noncomputable def valueSource:IntegralFramedBankPolynomialModel.Source:=IntegralPolynomialWindowTarski.source
  FormulaSignSlotRadialValueRadiusSource.source valueCenters value_dimension
noncomputable def valueAccess:IntegralFramedBankPolynomialModel.Access valueSource:=IntegralPolynomialWindowTarski.sourceAccess
  FormulaSignSlotRadialValueRadiusSource.source valueCenters value_dimension
    FormulaSignSlotRadialValueRadiusSource.access valueCenters_unary value_degree_fit
noncomputable def valueFamily:=IntegralPolynomialWindowTarskiCatalogue.family
  FormulaSignSlotRadialValueRadiusSource.source valueCenters value_dimension
noncomputable def valueFamilyAccess:SquareFeatureProductFamily.Access valueFamily:=IntegralPolynomialWindowTarskiCatalogue.access
  FormulaSignSlotRadialValueRadiusSource.source valueCenters value_dimension
    FormulaSignSlotRadialValueRadiusSource.access valueCenters_unary value_degree_fit

theorem principal_specialization (c:List Bool) (a:Fin (principalCenters c)→ℝ) (r:ℝ):
    ((IntegralPolynomialRadiusReader.polynomial FormulaSignSlotRadialPrincipalRadiusSource.source principalCenters
      principal_dimension c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) a)).eval r=
    (FormulaSignSlotRadialCenterPrincipalFamily.principal (FormulaSignSlotRadialPrincipalRadiusSource.family c)
      (FormulaSignSlotRadialPrincipalRadiusSource.order c)).eval₂ (Int.castRingHom ℝ)
        (fun i=>(Fin.cons r a:Fin (principalCenters c+1)→ℝ) (Fin.cast (principal_dimension c) i)):=
  IntegralPolynomialRadiusReader.specialization FormulaSignSlotRadialPrincipalRadiusSource.source principalCenters principal_dimension c a r

theorem value_specialization (c:List Bool) (a:Fin (valueCenters c)→ℝ) (r:ℝ):
    ((IntegralPolynomialRadiusReader.polynomial FormulaSignSlotRadialValueRadiusSource.source valueCenters
      value_dimension c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) a)).eval r=
    (TriplePolynomialParameterFlatten.one ((FormulaSignSlotRadialCenterValuePacking.source
      (FormulaSignSlotRadialValueRadiusSource.family c)).coeff (FormulaSignSlotRadialValueRadiusSource.order c))).eval₂
        (Int.castRingHom ℝ) (fun i=>(Fin.cons r a:Fin (valueCenters c+1)→ℝ) (Fin.cast (value_dimension c) i)):=
  IntegralPolynomialRadiusReader.specialization FormulaSignSlotRadialValueRadiusSource.source valueCenters value_dimension c a r

end LeanCanny.Encoding.FormulaSignSlotRadialCutWindowSources
