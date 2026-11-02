/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankTermTest
public import LeanCanny.Geometry.IntegralMixedFramedBankOrder
/-! # Native order replies for two retained quotients of the same joint root

The original syntax and chronological source bounds derive every reader.
Binary retained labels are guarded; their bounded unary AST is only an
internal writer. A valid vertex is the existing complete joint-prefix label.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankOrderTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankOrderBits (Labels count)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (key : List Bool→List Bool)
    (hpos : ∀ c,0<(atKey P D H (key c)).count) (left right : List Bool→ℕ) (q : List Bool) :=
  if decide (Labels P D H key left right (pairFst (pairFst q))) then
    IntegralFramedBankTermTest.value P D H s hs key hpos (IntegralMixedFramedBankOrderBits.word P D H key left right) q
  else []

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    (key : List Bool→List Bool) (hk : key∈FP) (hpos : ∀ c,0<(atKey P D H (key c)).count)
    (left right : List Bool→ℕ) (hl : BinaryFn left) (hr : BinaryFn right) :
    SpaceFunction (value P D H s hs key hpos left right) :=
  SpaceFunction.branch (fun q=>decide (Labels P D H key left right (pairFst (pairFst q))))
    ((IntegralMixedFramedBankOrderBits.labels_FP P a D H key hk left right hl hr).comp
      (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).flag_mem_FP
    (IntegralFramedBankTermTest.evaluator P a D H s hs hF hL key hk hpos _
      (IntegralMixedFramedBankOrderBits.word_FP P a D H key hk left right hl hr))
    (SpaceFunction.ofFP _ (constFn_mem_FP []))

theorem outside (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (key : List Bool→List Bool)
    (hpos : ∀ c,0<(atKey P D H (key c)).count) (left right : List Bool→ℕ) (q : List Bool)
    (h : ¬Labels P D H key left right (pairFst (pairFst q))) :
    value P D H s hs key hpos left right q=[] := by simp only [value,h,decide_false,Bool.false_eq_true,ite_false]

theorem packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (key : List Bool→List Bool)
    (hpos : ∀ c,0<(atKey P D H (key c)).count) (hroot : ∀ c,pairFst (key c)=c)
    (left right : List Bool→ℕ) (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedBankTermTest.input P D H s hs key hpos) c w)
    (hl : left c<count P D H key c) (hr : right c<count P D H key c) :
    value P D H s hs key hpos left right (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
        (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (key c))
        (SquareSampleCompleteVertices.candidate (IntegralFramedBankTermTest.input P D H s hs key hpos) c w hv).val ⟨left c,hl⟩-
        LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
        (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (key c))
        (SquareSampleCompleteVertices.candidate (IntegralFramedBankTermTest.input P D H s hs key hpos) c w hv).val ⟨right c,hr⟩)) := by
  have HL : Labels P D H key left right c := ⟨hl,hr⟩
  simp only [value,pairFst_pair,HL,decide_true,ite_true]
  have HE:=IntegralFramedBankTermTest.packet P D H s hs key hpos
    (IntegralMixedFramedBankOrderBits.word P D H key left right) c w d hv
  rw [LeanCanny.Geometry.IntegralMixedFramedBankOrder.word_syntax P D H key hroot left right c] at HE
  exact HE.trans (congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v))
    (LeanCanny.Geometry.IntegralMixedFramedBankOrder.term_eval P D H key left right c hl hr _))

theorem packet_positive_polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (key : List Bool→List Bool)
    (hpos : ∀ c,0<(atKey P D H (key c)).count) (hroot : ∀ c,pairFst (key c)=c)
    (left right : List Bool→ℕ) (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedBankTermTest.input P D H s hs key hpos) c w)
    (hl : left c<count P D H key c) (hr : right c<count P D H key c) :
    value P D H s hs key hpos left right (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign ((LeanCanny.Geometry.IntegralMixedFramedBankOrder.polynomial P D H key left right c).eval₂ (Int.castRingHom ℝ)
        (SquareSampleCompleteVertices.candidate (IntegralFramedBankTermTest.input P D H s hs key hpos) c w hv).val)) :=
  (packet P D H s hs key hpos hroot left right c w d hv hl hr).trans
    (congrArg InfinitesimalSign.encode (LeanCanny.Geometry.IntegralMixedFramedBankOrder.polynomial_sign P D H key left right c hl hr _)).symm

end LeanCanny.Encoding.IntegralFramedBankOrderTest
