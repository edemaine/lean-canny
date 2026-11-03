/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalSquare
public import LeanCanny.Encoding.SquareSampleCompleteVertices
public import LeanCanny.Geometry.IntegralMixedFullBankPoint
/-! # Complete full-system vertices read one actual retained bank point

The same decoded joint tuple satisfies every physical and scalar row.
Its actual scalar injection determines one old interpreting hom and every
bank quotient. No scalar-prefix sampler or independent root label is used.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSquare
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family commands)
open IntegralMixedFramedPhysicalIndex (enumerate)
open UniformIntegralPowerSchedule
open LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c))
  (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) c w)
local notation "G" => family P D H
local notation "x" => IntegralMixedCutSource.Family.state G (key c)

noncomputable def joint : Fin (count P D (key c))→ℝ :=
  (SquareSampleCompleteVertices.candidate (input P D H L F C hs key hpos) c w hv).val
noncomputable def rawPoint : (G).physical (key c)→ℝ :=joint P D H L F C hs key hpos c w hv ∘ enumerate (commands P D (key c))
noncomputable def point : Fin ((G).birth (key c))→ℝ :=
  letI : Fintype ((G).physical (key c)):=Fintype.ofEquiv (Fin (count P D (key c))) (enumerate (commands P D (key c))).symm
  IntegralMixedFullBankPoint.indexedPoint x (enumerate (commands P D (key c))) (joint P D H L F C hs key hpos c w hv)

include hv in
theorem joint_roots : ∀i,((sampler P D H (key c)).rows i).eval₂ (Int.castRingHom ℝ)
    (joint P D H L F C hs key hpos c w hv)=0 :=
  (SquareSampleCompleteVertices.candidate (input P D H L F C hs key hpos) c w hv).property

include hv in
theorem raw_roots : ∀i,((x).sampler.rows i).eval₂ (Int.castRingHom ℝ) (rawPoint P D H L F C hs key hpos c w hv)=0 :=
  (PolynomialSystemReindex.roots_iff (Int.castRingHom ℝ) (enumerate (commands P D (key c))) (x).sampler.rows
    (joint P D H L F C hs key hpos c w hv)).mp (joint_roots P D H L F C hs key hpos c w hv)

include hv in
theorem exists_interpretation :
    ∃ φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
        joint P D H L F C hs key hpos c w hv ((enumerate (commands P D (key c))) ((x).sampler.scalar i))^
          weights ((G).cap (key c)) (2^(G).width (key c)) ((G).birth (key c)) i) ∧
      ∀i,φ ((x).bank.numerator i)/((x).bank.denominator i:ℝ)=point P D H L F C hs key hpos c w hv i := by
  let _ : Fintype ((G).physical (key c)):=Fintype.ofEquiv (Fin (count P D (key c))) (enumerate (commands P D (key c))).symm
  exact IntegralMixedFullBankPoint.indexed_interprets x (IntegralMixedFramedHistoryFamilyBits.family_canonical P D H (key c))
    (enumerate (commands P D (key c))) (joint P D H L F C hs key hpos c w hv)
    (joint_roots P D H L F C hs key hpos c w hv)

include hv in
/-- Readback uses the SAME full joint tuple and original native column. -/
theorem point_column (T : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents P D H T) (i : Fin (commands P D (key c)).length) :
    point P D H L F C hs key hpos c w hv i=
      joint P D H L F C hs key hpos c w hv
        ⟨IntegralMixedFramedPhysicalIndex.scalarColumn P T (pair (key c) (BinaryNatCode.encode i.val)),by
          rw [IntegralMixedFramedPhysicalIndex.scalarColumn_actual P D H T hr (key c) i]
          exact (enumerate _ ((x).sampler.scalar i)).isLt⟩^
          weights (P.cap (pairFst (key c))+1) (2^P.width (pairFst (key c))) (commands P D (key c)).length i /
        ((x).bank.denominator i:ℝ) :=
  IntegralMixedFullBankPoint.framed_point P D H T hr (key c) (joint P D H L F C hs key hpos c w hv) i
/-- Every actual full joint root has one complete label with literal tuple readback. -/
theorem exists_joint (z : Fin (count P D (key c))→ℝ)
    (hz : ∀i,((sampler P D H (key c)).rows i).eval₂ (Int.castRingHom ℝ) z=0) :
    ∃w,∃hv : SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) c w,
      joint P D H L F C hs key hpos c w hv=z := by
  let root : SquareSampleComplete.Roots (input P D H L F C hs key hpos) c:=⟨z,hz⟩
  refine ⟨SquareSampleCompleteVertices.word _ (complete P D H L F C hs key hpos) c root,
    SquareSampleCompleteVertices.word_valid _ (complete P D H L F C hs key hpos) c root,?_⟩
  exact congrArg (fun r : SquareSampleComplete.Roots (input P D H L F C hs key hpos) c=>r.val)
    (SquareSampleCompleteVertices.candidate_word _ (complete P D H L F C hs key hpos) c root)
end LeanCanny.Encoding.IntegralFramedPhysicalSquare
