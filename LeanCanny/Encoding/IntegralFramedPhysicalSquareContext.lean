/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SquareSampleCompleteNaturality
public import LeanCanny.Encoding.IntegralFramedPhysicalSquare
public import LeanCanny.Algebra.IntegralMixedFramedCompanionKeyTransport
public import LeanCanny.Encoding.IntegralFramedPhysicalNaturalPoint
/-! # Full physical sampling ignores the auxiliary saved-key context -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSquareContext
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

open IntegralMixedFramedCompanionBits (PrefixKey profile)
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedPhysicalIndex (arity enumerate)

private structure Presentation where
  count : List Bool→ℕ
  degree : List Bool→ℕ
  mass : List Bool→ℕ
  rowDegree : List Bool→ℕ→ℕ
  rows : ∀c,Fin (count c)→MvPolynomial (Fin (count c)) ℤ

private noncomputable def presentation (F : NoInfinitySquareSample.Family) : Presentation:=
  ⟨F.count,F.degree,F.mass,F.rowDegree,F.rows⟩

private theorem family_ext (F G : NoInfinitySquareSample.Family)
    (h : presentation F=presentation G) : F=G:=by
  cases F
  cases G
  simp only [presentation,Presentation.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl,rfl,hrows⟩
  cases hrows
  rfl

private noncomputable def prefixSampler (P : Parameters) (D : Plan P) (k : PrefixKey P) :=
  let cs:=paddedPast (defaultInstruction P D k.root) (D.rules k.root) k.birth
  letI : Fintype (Index (Fin 0) cs):=Fintype.ofEquiv (Fin (arity cs)) (enumerate cs).symm
  IntegralHistorySampler.reindex
    (run (initial P D k.root) cs (by
      dsimp only [cs]
      rw [paddedPast_length]
      exact k.bounded.trans (Nat.le_succ _))).sampler (enumerate cs)

private noncomputable def presentationAt (P : Parameters) (D : Plan P)
    (L F C : List Bool→ℕ) (k : List Bool→PrefixKey P) : Presentation where
  count c:=arity (paddedPast (defaultInstruction P D (k c).root) (D.rules (k c).root) (k c).birth)
  degree c:=(∑i,(prefixSampler P D (k c)).degrees i)+1
  mass c:=IntegralMixedPhysicalRowBudget.familyMass P L F C (k c).root
  rowDegree c j:=if hj : j<arity (paddedPast (defaultInstruction P D (k c).root)
      (D.rules (k c).root) (k c).birth) then (prefixSampler P D (k c)).degrees ⟨j,hj⟩ else 1
  rows c:=(prefixSampler P D (k c)).rows

private theorem presentation_view (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool→ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (key : List Bool→List Bool)
    (hpos : ∀c,0<(family P D H).birth (key c)) :
    presentation (IntegralFramedPhysicalSquare.finite P D H L F C hs key hpos)=
      presentationAt P D L F C (fun c=>profile P (key c)) :=rfl

theorem input_aux_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (root : List Bool→List Bool) (birth : List Bool→ℕ) (a b : List Bool→List Bool)
    (ha : ∀c,0<(family P D H).birth (keyAt (root c) (birth c) (a c)))
    (hb : ∀c,0<(family P D H).birth (keyAt (root c) (birth c) (b c))) :
    IntegralFramedPhysicalSquare.input P D H L F C hs (fun c=>keyAt (root c) (birth c) (a c)) ha=
      IntegralFramedPhysicalSquare.input P D H L F C hs (fun c=>keyAt (root c) (birth c) (b c)) hb :=by
  have HE : (fun c=>profile P (keyAt (root c) (birth c) (a c)))=
      (fun c=>profile P (keyAt (root c) (birth c) (b c))):=by
    funext c
    apply PrefixKey.ext
    · simp only [profile,keyAt,pairFst_pair]
    · simp only [profile,prefixLength,IntegralMixedFullHistoryFamilyBits.prefixLength,
        keyAt,pairFst_pair,pairSnd_pair]
  apply congrArg NoInfinitySquareSample.input
  apply family_ext
  rw [presentation_view,presentation_view,HE]

theorem positive_aux (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (root : List Bool) (birth : ℕ) (a b : List Bool)
    (ha : 0<(family P D H).birth (keyAt root birth a)) :
    0<(family P D H).birth (keyAt root birth b) :=by
  rw [family_birth] at ha ⊢
  simpa only [prefixLength,IntegralMixedFullHistoryFamilyBits.prefixLength,keyAt,
    pairFst_pair,pairSnd_pair] using ha

noncomputable def rootInput (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (birth : List Bool→ℕ) (hpos : ∀r,0<(family P D H).birth (keyAt r (birth r) [])) :=
  IntegralFramedPhysicalSquare.input P D H L F C hs (fun r=>keyAt r (birth r) []) hpos

noncomputable def contextInput (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (birth : List Bool→ℕ) (a : List Bool→List Bool)
    (hpos : ∀r,0<(family P D H).birth (keyAt r (birth r) [])) :=
  IntegralFramedPhysicalSquare.input P D H L F C hs (fun q=>keyAt (pairFst q) (birth (pairFst q)) (a q))
    (fun q=>positive_aux P D H (pairFst q) (birth (pairFst q)) [] (a q) (hpos (pairFst q)))

theorem input_root_factor (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (birth : List Bool→ℕ) (a : List Bool→List Bool)
    (hpos : ∀r,0<(family P D H).birth (keyAt r (birth r) [])) :
    contextInput P D H L F C hs birth a hpos=
      SquareSampleInput.comp (rootInput P D H L F C hs birth hpos) pairFst :=by
  exact (input_aux_eq P D H L F C hs pairFst (birth∘pairFst) a (fun _=>[]) _
    (fun q=>hpos (pairFst q))).trans rfl

noncomputable def naturalValue (I : SquareSampleInput.Inputs) (u w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid I u w) (i : ℕ) : ℝ:=
  if hi : i<I.count u then (SquareSampleCompleteVertices.candidate I u w hv).val ⟨i,hi⟩ else 0

private theorem naturalValue_input_eq (I J : SquareSampleInput.Inputs) (hI : I=J) (u w : List Bool)
    (hi : SquareSampleCompleteVertices.Valid I u w) (hj : SquareSampleCompleteVertices.Valid J u w) :
    naturalValue I u w hi=naturalValue J u w hj :=by
  cases hI
  rfl

private theorem naturalValue_comp (I : SquareSampleInput.Inputs) (f : List Bool→List Bool) (u w : List Bool)
    (hi : SquareSampleCompleteVertices.Valid (SquareSampleInput.comp I f) u w)
    (hj : SquareSampleCompleteVertices.Valid I (f u) w) :
    naturalValue (SquareSampleInput.comp I f) u w hi=naturalValue I (f u) w hj :=by
  funext i
  unfold naturalValue
  change (if h : i<I.count (f u) then
    (SquareSampleCompleteVertices.candidate (SquareSampleInput.comp I f) u w hi).val ⟨i,h⟩ else 0)=_
  split_ifs with h
  · exact congrFun (SquareSampleCompleteNaturality.candidate_comp I f u w hi hj) ⟨i,h⟩
  · rfl

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (birth : List Bool→ℕ) (a : List Bool→List Bool)
    (hpos : ∀r,0<(family P D H).birth (keyAt r (birth r) []))

theorem width_root (q : List Bool) :
    SquareSampleCompleteVertices.width (contextInput P D H L F C hs birth a hpos) q=
      SquareSampleCompleteVertices.width (rootInput P D H L F C hs birth hpos) (pairFst q) :=by
  rw [input_root_factor]
  exact SquareSampleCompleteNaturality.complete_width_comp _ _ _

theorem valid_root (q w : List Bool) :
    SquareSampleCompleteVertices.Valid (contextInput P D H L F C hs birth a hpos) q w↔
      SquareSampleCompleteVertices.Valid (rootInput P D H L F C hs birth hpos) (pairFst q) w :=by
  rw [input_root_factor]
  exact SquareSampleCompleteNaturality.complete_valid_comp _ _ _ _

theorem natural_root (q w : List Bool)
    (hq : SquareSampleCompleteVertices.Valid (contextInput P D H L F C hs birth a hpos) q w)
    (hr : SquareSampleCompleteVertices.Valid (rootInput P D H L F C hs birth hpos) (pairFst q) w) :
    naturalValue (contextInput P D H L F C hs birth a hpos) q w hq=
      naturalValue (rootInput P D H L F C hs birth hpos) (pairFst q) w hr :=by
  have HE:=input_root_factor P D H L F C hs birth a hpos
  have hc : SquareSampleCompleteVertices.Valid
      (SquareSampleInput.comp (rootInput P D H L F C hs birth hpos) pairFst) q w:=HE ▸ hq
  exact (naturalValue_input_eq _ _ HE q w hq hc).trans (naturalValue_comp _ _ q w hc hr)

theorem natural_actual (q w : List Bool)
    (hq : SquareSampleCompleteVertices.Valid (contextInput P D H L F C hs birth a hpos) q w) :
    naturalValue (contextInput P D H L F C hs birth a hpos) q w hq=
      IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs
        (fun q=>keyAt (pairFst q) (birth (pairFst q)) (a q))
        (fun q=>positive_aux P D H (pairFst q) (birth (pairFst q)) [] (a q) (hpos (pairFst q))) q w hq :=rfl

end LeanCanny.Encoding.IntegralFramedPhysicalSquareContext
