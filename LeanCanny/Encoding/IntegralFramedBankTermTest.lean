/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankTermCoefficient
public import LeanCanny.Geometry.IntegralMixedFramedBankTermSign
public import LeanCanny.Encoding.IntegralFramedCompleteSquareSpace
public import LeanCanny.Encoding.SquareSampleCompleteIndexedPolynomialTest
/-! # Native original-equation tests at actual complete joint-prefix vertices

Original syntax derives the sampling rows and every test coefficient. The
sample label retains its original source and vertex while the test reads the
same joint tuple through actual bank denominators and fixed coordinate powers.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankTermTest
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical

noncomputable abbrev input (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (key : List Bool → List Bool)
    (hpos : ∀ c,0<(atKey P D H (key c)).count) :=
  IntegralFramedCompleteSquare.input P D H s.nodes s.factor s.seed hs key hpos

noncomputable def test (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (key : List Bool → List Bool)
    (hpos : ∀ c,0<(atKey P D H (key c)).count) (word : List Bool → List Bool) :
    SquareSampleCompleteIndexedPolynomialTest.Test (input P D H s hs key hpos) where
  polynomial c _ := IntegralMixedFramedBankTermBits.polynomial P D H word (key c)
  degree z := IntegralMixedFramedBankTermBits.degree P D H word (key (pairFst z))
  mass z := IntegralMixedFramedBankTermBits.mass P D H word s.nodes s.factor s.seed (key (pairFst z))
  polynomial_degree z := IntegralMixedFramedBankTermBits.polynomial_degree P D H word (key (pairFst z))
  polynomial_mass z := IntegralMixedFramedBankTermBits.polynomial_mass P D H word s.nodes s.factor s.seed hs (key (pairFst z))

def coefficientQuery (key : List Bool → List Bool) (q : List Bool) :=
  pair (pair (key (pairFst (RationalSubstitution.IntegerBits.context q))) (RationalSubstitution.IntegerBits.selectedDegree q)) (pairSnd q)
theorem coefficientQuery_FP (key : List Bool → List Bool) (hk : key∈FP) : coefficientQuery key∈FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP) hk)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP

theorem coefficient_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (key : List Bool → List Bool)
    (hpos : ∀ c,0<(atKey P D H (key c)).count) (word : List Bool → List Bool) (q : List Bool) :
    IntegralMixedFramedBankTermBits.coefficient P D H word (coefficientQuery key q)=
      SquareSampleCompleteIndexedPolynomialTest.coefficient (test P D H s hs key hpos word) q := by
  unfold coefficientQuery
  rw [IntegralMixedFramedBankTermBits.coefficient_std,FixedWidthPolynomial.nativeExponent_refl]
  rfl

theorem test_access (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    (key : List Bool → List Bool) (hk : key∈FP) (hpos : ∀ c,0<(atKey P D H (key c)).count)
    (word : List Bool → List Bool) (hw : word∈FP) : (test P D H s hs key hpos word).Access where
  degree := (IntegralMixedFramedBankTermBits.degree_binary P a D H word hw).comp (mem_FP_comp pairFst_mem_FP hk)
  mass := (IntegralMixedFramedBankTermBits.mass_binary P a D H word hw s.nodes_native s.factor_native s.seed_native).comp
    (mem_FP_comp pairFst_mem_FP hk)
  coefficient := ((IntegralMixedFramedBankTermBits.coefficient_evaluator P a D H s hs hF hL word hw).precompose
    (coefficientQuery key) (coefficientQuery_FP key hk)).congr (funext fun q => coefficient_eq P D H s hs key hpos word q)

theorem input_access (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    (key : List Bool → List Bool) (hk : key∈FP) (hpos : ∀ c,0<(atKey P D H (key c)).count) :
    (input P D H s hs key hpos).Access :=
  IntegralFramedCompleteSquare.access P a D H s.nodes s.factor s.seed hs s.nodes_native s.factor_native s.seed_native key hk hpos
    (IntegralFramedCompleteSquare.row_evaluator P a D H s.nodes s.factor s.seed hs key hk hpos
      (IntegralMixedFramedCompanionUniformBits.original_evaluator P a D H s hs hF hL))

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (key : List Bool → List Bool)
    (hpos : ∀ c,0<(atKey P D H (key c)).count) (word : List Bool → List Bool) :=
  SquareSampleCompleteIndexedPolynomialTest.value (input P D H s hs key hpos) (test P D H s hs key hpos word)

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    (key : List Bool → List Bool) (hk : key∈FP) (hpos : ∀ c,0<(atKey P D H (key c)).count)
    (word : List Bool → List Bool) (hw : word∈FP) : SpaceFunction (value P D H s hs key hpos word) :=
  SquareSampleCompleteIndexedPolynomialTest.evaluator (input_access P a D H s hs hF hL key hk hpos)
    (test_access P a D H s hs hF hL key hk hpos word hw)

theorem packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (key : List Bool → List Bool)
    (hpos : ∀ c,0<(atKey P D H (key c)).count) (word : List Bool → List Bool) (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input P D H s hs key hpos) c w) :
    value P D H s hs key hpos word (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign (((IntegralMixedFramedBankTermBits.source word).syntax (key c)).eval
        (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.point P D H (key c)
          (SquareSampleCompleteVertices.candidate (input P D H s hs key hpos) c w hv).val))) := by
  rw [value,SquareSampleCompleteIndexedPolynomialTest.packet _ _ c w d hv]
  exact congrArg InfinitesimalSign.encode
    (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.sign P D H word (key c) _)

end LeanCanny.Encoding.IntegralFramedBankTermTest
