/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankTermTest
/-! # Original-equation membership at complete joint vertices is in PSPACE

The predicate includes the actual complete-vertex validity guard. Its equation
is evaluated at the decoded original bank coordinates of that same joint
vertex. No evaluator or relative-root validity premise remains.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankTermTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical

theorem value_packetized (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (key : List Bool → List Bool)
    (hpos : ∀ c,0<(atKey P D H (key c)).count) (word : List Bool → List Bool) (q : List Bool) :
    value P D H s hs key hpos word q=
      value P D H s hs key hpos word (pair (pair (pairFst (pairFst q)) (pairSnd (pairFst q))) (pairSnd q)) := by
  unfold value SquareSampleCompleteIndexedPolynomialTest.value
  simp only [Function.comp_apply,SquareSampleCompleteIndexedPolynomialTest.query,pairFst_pair,pairSnd_pair]

theorem value_semantic (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (key : List Bool → List Bool)
    (hpos : ∀ c,0<(atKey P D H (key c)).count) (word : List Bool → List Bool) (q : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input P D H s hs key hpos) (pairFst (pairFst q)) (pairSnd (pairFst q))) :
    value P D H s hs key hpos word q=InfinitesimalSign.encode
      (SignType.sign (((IntegralMixedFramedBankTermBits.source word).syntax (key (pairFst (pairFst q)))).eval
        (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.point P D H (key (pairFst (pairFst q)))
          (SquareSampleCompleteVertices.candidate (input P D H s hs key hpos) (pairFst (pairFst q)) (pairSnd (pairFst q)) hv).val))) :=
  (value_packetized P D H s hs key hpos word q).trans
    (packet P D H s hs key hpos word _ _ _ hv)

noncomputable def zeroLanguage (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (key : List Bool → List Bool)
    (hpos : ∀ c,0<(atKey P D H (key c)).count) (word : List Bool → List Bool) : Language :=
  {q | ∃ hv : SquareSampleCompleteVertices.Valid (input P D H s hs key hpos) (pairFst (pairFst q)) (pairSnd (pairFst q)),
    ((IntegralMixedFramedBankTermBits.source word).syntax (key (pairFst (pairFst q)))).eval
      (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.point P D H (key (pairFst (pairFst q)))
        (SquareSampleCompleteVertices.candidate (input P D H s hs key hpos) (pairFst (pairFst q)) (pairSnd (pairFst q)) hv).val)=0}

theorem zero_language_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (key : List Bool → List Bool)
    (hpos : ∀ c,0<(atKey P D H (key c)).count) (word : List Bool → List Bool) :
    SquareSampleCompleteIndexedPolynomialTest.language (input P D H s hs key hpos) (test P D H s hs key hpos word) 0=
      zeroLanguage P D H s hs key hpos word := by
  ext q
  change (_ ∧ value P D H s hs key hpos word q=InfinitesimalSign.encode 0)↔_
  constructor
  · rintro ⟨hv,hz⟩
    refine ⟨hv,?_⟩
    exact sign_eq_zero_iff.mp ((SquareSampleTestSign.encode_eq_iff _ _).mp
      ((value_semantic P D H s hs key hpos word q hv).symm.trans hz))
  · rintro ⟨hv,hz⟩
    refine ⟨hv,?_⟩
    rw [value_semantic P D H s hs key hpos word q hv,sign_eq_zero_iff.mpr hz]

theorem zero_decider (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    (key : List Bool → List Bool) (hk : key∈FP) (hpos : ∀ c,0<(atKey P D H (key c)).count)
    (word : List Bool → List Bool) (hw : word∈FP) : SpaceDecider (zeroLanguage P D H s hs key hpos word) :=
  (SquareSampleCompleteIndexedPolynomialTest.decider (input_access P a D H s hs hF hL key hk hpos)
    (test_access P a D H s hs hF hL key hk hpos word hw) 0).congr
      (zero_language_eq P D H s hs key hpos word)

theorem zero_mem_PSPACE (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    (key : List Bool → List Bool) (hk : key∈FP) (hpos : ∀ c,0<(atKey P D H (key c)).count)
    (word : List Bool → List Bool) (hw : word∈FP) : zeroLanguage P D H s hs key hpos word∈PSPACE :=
  (zero_decider P a D H s hs hF hL key hk hpos word hw).mem_PSPACE

end LeanCanny.Encoding.IntegralFramedBankTermTest
