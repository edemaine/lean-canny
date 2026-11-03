/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCutLocalInterpretation
public import LeanCanny.Encoding.IntegralFramedPhysicalBankOrderSource
/-! # Ordered same-word guards for an actual selected full cut factor

This frontend retains the full context and vertex word in every query. It
checks actual strict endpoint order, not just the numerical retained labels.
The older normalized-context language is not identified with this language.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutOrderedInterval
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank native tables tables_native represents)
open IntegralMixedPhysicalCutOpenInterval (selected parent degree Bounds comparison)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] bank native tables IntegralMixedFramedHistoryFamilyBits.family
  IntegralFramedPhysicalBankOrderSource.value
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

def packet (root birth left right vertex : List Bool) :=
  pair (pair root (pair birth (pair left right))) vertex
theorem packet_FP : (fun z=>packet (pairFst z) (pairFst (pairSnd z))
    (pairFst (pairSnd (pairSnd z))) (pairFst (pairSnd (pairSnd (pairSnd z))))
    (pairSnd (pairSnd (pairSnd (pairSnd z)))))∈FP :=by polytime [packet]
theorem packet_context (root birth left right vertex : List Bool) :
    pairFst (packet root birth left right vertex)=pair root (pair birth (pair left right)) :=pairFst_pair _ _
theorem packet_vertex (root birth left right vertex : List Bool) :
    pairSnd (packet root birth left right vertex)=vertex :=pairSnd_pair _ _
theorem packet_birth (root birth left right vertex : List Bool) :
    IntegralMixedPhysicalCutOpenInterval.birthWord (pairFst (packet root birth left right vertex))=birth :=by
  simp only [packet,IntegralMixedPhysicalCutOpenInterval.birthWord,pairFst_pair,pairSnd_pair]
theorem packet_selected (root birth left right vertex : List Bool) (side : Bool) :
    selected side (pairFst (packet root birth left right vertex))=
      Nat.fromBitsLE (if side then right else left) :=by
  cases side <;> simp only [packet,selected,pairFst_pair,pairSnd_pair,Bool.false_eq_true,ite_false,ite_true]

noncomputable def order (z : List Bool) :=IntegralFramedPhysicalBankOrderSource.value
  (bank hn ht ha hR outer) (selected false) (selected true) (tables hn ht ha hR outer)
  (represents hn ht ha hR outer) (pair z [])

theorem order_evaluator : SpaceFunction (order hn ht ha hR outer) :=by
  unfold order
  have E:=IntegralFramedPhysicalBankOrderSource.evaluator (bank hn ht ha hR outer)
    (selected false) (selected true) (tables hn ht ha hR outer) (represents hn ht ha hR outer)
    (native hn ht ha hR outer)
    (tables_native hn ht ha hR outer) (IntegralMixedPhysicalCutOpenInterval.selected_binary false)
    (IntegralMixedPhysicalCutOpenInterval.selected_binary true)
    (IntegralMixedPhysicalMarkedNative.row_evaluator hn ht ha hR outer)
  exact E.precompose (fun z=>pair z []) (mem_FP_pair id_mem_FP (constFn_mem_FP []))

noncomputable def language : Language := {z |
  z∈comparison hn ht ha hR outer ∧
  SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) (pairFst z) (pairSnd z) ∧
  Bounds hn ht ha hR outer z ∧
  IntegralMixedPhysicalCutLocalGuards.Guards hn ht ha hR outer z ∧
  order hn ht ha hR outer z=InfinitesimalSign.encode 1}

theorem decider : SpaceDecider (language hn ht ha hR outer) :=by
  have EC:=(IntegralMixedPhysicalCutOpenInterval.comparison_decider hn ht ha hR outer).flagEvaluator
  have EV:=(SquareSampleCompleteVertices.decider (IntegralMixedPhysicalMarkedNative.access hn ht ha hR outer)).flagEvaluator
  have EB:=SpaceFunction.ofFP _ (IntegralMixedPhysicalCutOpenInterval.bounds_FP hn ht ha hR outer).flag_mem_FP
  have EG:=IntegralMixedPhysicalCutLocalGuards.evaluator hn ht ha hR outer
  have OD : SpaceDecider {z | order hn ht ha hR outer z=InfinitesimalSign.encode 1} :=by
    apply (order_evaluator hn ht ha hR outer).decider (fun v=>decide (v=InfinitesimalSign.encode 1))
      (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP (InfinitesimalSign.encode 1))).flag_mem_FP
    intro z
    simp only [Set.mem_ofPred_eq,decide_eq_true_eq]
  have EO:=OD.flagEvaluator
  apply (EC.andFlags (EV.andFlags (EB.andFlags (EG.andFlags EO)))).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,
    List.cons.injEq,and_true,decide_eq_true_eq]

theorem mem_PSPACE : language hn ht ha hR outer∈PSPACE :=(decider hn ht ha hR outer).mem_PSPACE

local notation "B" => bank hn ht ha hR outer
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "D" => IntegralFramedBankQuery.Bank.plan B
local notation "H" => IntegralFramedBankQuery.Bank.data B
local notation "G" => IntegralMixedFramedHistoryFamilyBits.family P D H

noncomputable def endpoint (side : Bool) (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) q w)
    (hi : selected side q<IntegralMixedPhysicalCutOpenInterval.count hn ht ha hR outer q) : ℝ :=
  LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
    (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H ((B).key q))
    (IntegralFramedPhysicalSquare.scalarTuple P D H (B).nodes (B).factor (B).seed (B).bounds
      (B).key (B).positive q w hv) ⟨selected side q,hi⟩

theorem order_iff (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) q w)
    (hl : selected false q<IntegralMixedPhysicalCutOpenInterval.count hn ht ha hR outer q)
    (hr : selected true q<IntegralMixedPhysicalCutOpenInterval.count hn ht ha hR outer q) :
    order hn ht ha hR outer (pair q w)=InfinitesimalSign.encode 1 ↔
      endpoint hn ht ha hR outer false q w hv hl<endpoint hn ht ha hR outer true q w hv hr :=by
  unfold order
  rw [IntegralFramedPhysicalBankOrderSource.packet B (selected false) (selected true)
    (tables hn ht ha hR outer) (represents hn ht ha hR outer) q w [] hv hl hr]
  exact (SquareSampleTestSign.encode_eq_iff _ _).trans (sign_eq_one_iff.trans sub_pos)

theorem left_bound (q w : List Bool) (hb : Bounds hn ht ha hR outer (pair q w)) :
    selected false q<IntegralMixedPhysicalCutOpenInterval.count hn ht ha hR outer q :=by
  simpa only [pairFst_pair] using hb.1
theorem right_bound (q w : List Bool) (hb : Bounds hn ht ha hR outer (pair q w)) :
    selected true q<IntegralMixedPhysicalCutOpenInterval.count hn ht ha hR outer q :=by
  simpa only [pairFst_pair] using hb.2.1

theorem reject_unordered (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) q w)
    (hb : Bounds hn ht ha hR outer (pair q w))
    (horder : endpoint hn ht ha hR outer true q w hv (right_bound hn ht ha hR outer q w hb)≤
      endpoint hn ht ha hR outer false q w hv (left_bound hn ht ha hR outer q w hb)) :
    pair q w∉language hn ht ha hR outer :=by
  intro h
  have HO:=(order_iff hn ht ha hR outer q w hv (left_bound hn ht ha hR outer q w hb)
    (right_bound hn ht ha hR outer q w hb)).mp h.2.2.2.2
  exact (not_lt_of_ge horder) HO

theorem reject_left (z : List Bool)
    (hbad : IntegralMixedPhysicalCutOpenInterval.count hn ht ha hR outer (pairFst z)≤selected false (pairFst z)) :
    z∉language hn ht ha hR outer :=by
  intro h
  exact (Nat.not_lt_of_ge hbad) h.2.2.1.1

theorem interpreted_empty_iff (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) q w)
    (hb : Bounds hn ht ha hR outer (pair q w))
    (hg : IntegralMixedPhysicalCutLocalGuards.Guards hn ht ha hR outer (pair q w)) :
    ∃φ : ((G).state (IntegralMixedVirtualTaskBits.saved P (parent hn ht ha hR outer q))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ (((G).state (IntegralMixedVirtualTaskBits.saved P (parent hn ht ha hR outer q))).sampler.scalarPrefix.basis.generator i)=
        IntegralFramedPhysicalSquare.scalarTuple P D H (B).nodes (B).factor (B).seed (B).bounds
          (B).key (B).positive q w hv
          (UniformIntegralPowerSchedule.embed (IntegralMixedPhysicalCutLocalInterpretation.fits hn ht ha hR outer q w hb) i)^
          UniformIntegralPowerSchedule.weights
            ((P).cap (pairFst (IntegralMixedVirtualTaskBits.saved P (parent hn ht ha hR outer q)))+1)
            (2^(G).width (IntegralMixedVirtualTaskBits.saved P (parent hn ht ha hR outer q)))
            ((G).birth (IntegralMixedVirtualTaskBits.saved P (parent hn ht ha hR outer q))) i) ∧
      IntegralMixedRelativeCuts.Valid ((G).state (IntegralMixedVirtualTaskBits.saved P (parent hn ht ha hR outer q)))
        ((G).birth_bound _) ((G).rule _) φ ((G).kind _) ∧
      IntegralMixedFramedFullCutIntervalSelected.factor P D H (parent hn ht ha hR outer) q φ≠0 ∧
      (IntegralMixedFramedFullCutIntervalSelected.factor P D H (parent hn ht ha hR outer) q φ).natDegree=
        degree hn ht ha hR outer q ∧
      (pair q w∈language hn ht ha hR outer ↔
        endpoint hn ht ha hR outer false q w hv (left_bound hn ht ha hR outer q w hb)<
          endpoint hn ht ha hR outer true q w hv (right_bound hn ht ha hR outer q w hb) ∧
        ∀r,(IntegralMixedFramedFullCutIntervalSelected.factor P D H (parent hn ht ha hR outer) q φ).eval r=0→
          r∉Set.Ioo (endpoint hn ht ha hR outer false q w hv (left_bound hn ht ha hR outer q w hb))
            (endpoint hn ht ha hR outer true q w hv (right_bound hn ht ha hR outer q w hb))) :=by
  obtain ⟨φ,hφ,HV,HZ,HD⟩:=IntegralMixedPhysicalCutLocalInterpretation.interpreted_guards hn ht ha hR outer q w hv hb hg
  refine ⟨φ,hφ,HV,HZ,HD,?_⟩
  have HO:=order_iff hn ht ha hR outer q w hv (left_bound hn ht ha hR outer q w hb)
    (right_bound hn ht ha hR outer q w hb)
  have HM : pair q w∈language hn ht ha hR outer ↔
      pair q w∈comparison hn ht ha hR outer ∧
        endpoint hn ht ha hR outer false q w hv (left_bound hn ht ha hR outer q w hb)<
          endpoint hn ht ha hR outer true q w hv (right_bound hn ht ha hR outer q w hb) :=by
    constructor
    · intro h
      exact ⟨h.1,HO.mp h.2.2.2.2⟩
    · intro h
      refine ⟨h.1,?_,hb,hg,HO.mpr h.2⟩
      simpa only [pairFst_pair,pairSnd_pair] using hv
  by_cases hab : endpoint hn ht ha hR outer false q w hv (left_bound hn ht ha hR outer q w hb)<
      endpoint hn ht ha hR outer true q w hv (right_bound hn ht ha hR outer q w hb)
  · have HE:=IntegralFramedFullCutOpenInterval.empty_iff P D H (B).nodes (B).factor (B).seed (B).bounds
      (parent hn ht ha hR outer) (B).key (degree hn ht ha hR outer) (selected false) (selected true) (B).positive
      (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha hR outer)
      (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha hR outer) q w hv
      (IntegralMixedPhysicalCutLocalInterpretation.fits hn ht ha hR outer q w hb)
      (IntegralMixedPhysicalCutLocalInterpretation.active hn ht ha hR outer q w hb) φ hφ HZ HD
      (IntegralMixedPhysicalCutOpenInterval.degree_cap hn ht ha hR outer q)
      (left_bound hn ht ha hR outer q w hb) (right_bound hn ht ha hR outer q w hb) hab
    have HE' : pair q w∈comparison hn ht ha hR outer ↔
        ∀r,(IntegralMixedFramedFullCutIntervalSelected.factor P D H (parent hn ht ha hR outer) q φ).eval r=0→
          r∉Set.Ioo (endpoint hn ht ha hR outer false q w hv (left_bound hn ht ha hR outer q w hb))
            (endpoint hn ht ha hR outer true q w hv (right_bound hn ht ha hR outer q w hb)) :=by
      simpa only [comparison,endpoint] using HE
    rw [HM]
    exact ⟨fun h=>⟨hab,HE'.mp h.1⟩,fun h=>⟨HE'.mpr h.2,hab⟩⟩
  · rw [HM]
    simp only [hab,and_false,false_and]

end LeanCanny.Encoding.IntegralMixedPhysicalCutOrderedInterval
