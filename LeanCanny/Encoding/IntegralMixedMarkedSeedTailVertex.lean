/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerSeedTail
public import LeanCanny.Encoding.IntegralMixedMarkedReservedCutView
/-! # Honest meaningful prefixes complete to fresh actual marked vertices

Every unused record, including the terminal record, is a canonical seed.
The fixed original sampler and its full context are sampled anew.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedSeedTailVertex
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "V"=>IntegralMixedMarkedReservedCutView.plan hn ht ha hR0
local notation "Q"=>IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0
attribute [local irreducible] IntegralMixedMarkedReservedParent.bank
 IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedSourceIntegerRecordAppend.plan

variable (root : List Bool) (codes : List (List Bool)) (k : ℕ)
 (hcodes : IntegralMixedCausalRecordPlanBits.records root=WordList.encode
   (codes++List.replicate k (IntegralMixedChronologicalFrameCode.code ((IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters.ambient root) [] 0 0)))

include hcodes in
theorem full_length : ((V).rules root).length=number n root+8+IntegralMixedCausalRecordPlanBits.count root :=by
  have HR:=IntegralMixedSourceIntegerSeedTail.full_seed_tail P Q
    (IntegralMixedMarkedReservedCutView.positive hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.degree hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.scalar_cap hn ht ha hR0) (fun root=>number n root+8)
    (IntegralMixedMarkedReservedCutView.integerSource hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.integer_nonzero hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.integer_cap hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.room hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.data hn ht ha hR0) root [] codes k hcodes
  have HL:=congrArg List.length HR
  simp only [List.length_append,List.length_replicate,IntegralMixedFramedHistoryScript.paddedPast_length] at HL
  have HC : IntegralMixedCausalRecordPlanBits.count root=codes.length+k:=by
    simp only [IntegralMixedCausalRecordPlanBits.count,hcodes,WordListRecords.count_encode,List.length_append,List.length_replicate]
  change ((V).rules root).length=k+(number n root+8+codes.length) at HL
  omega

include hcodes in
theorem exists_vertex (v : ℕ→ℝ)
    (hv : IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedFamilyRunView.runAt P V root (number n root+8+codes.length)
        (IntegralMixedSourceIntegerSeedTail.before_bound P (fun root=>number n root+8)
          (IntegralMixedMarkedReservedCutView.room hn ht ha hR0) root codes k hcodes)) v)
    (charge : ℕ) (hcharge : (Q root).degree=BoundedZeroSource.powerDegree charge)
    (p : Fin ((P).ambient root+1)→ℝ)
    (hp : (FermatCriticalHomogenization.polynomial (Q root).low (Q root).leading (Q root).degree).eval₂
      (Int.castRingHom ℝ) p=0)
    (hg : ∀i,i≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q root).low (Q root).leading (Q root).degree)).eval₂
        (Int.castRingHom ℝ) p=0) :
    ∃w,∃hw : SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
      (IntegralMixedMarkedReservedParent.context root) w,
      w.length=SquareSampleCompleteVertices.width (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
        (IntegralMixedMarkedReservedParent.context root) ∧
      ∀i : Fin ((family P (B).plan (B).data).birth ((B).key (IntegralMixedMarkedReservedParent.context root))),
        IntegralFramedPhysicalSquare.point P (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
          (B).key (B).positive (IntegralMixedMarkedReservedParent.context root) w hw i=
            IntegralMixedCanonicalPadding.values (p 0) v k i.val :=by
  have HR:=IntegralMixedSourceIntegerSeedTail.full_realizes P Q
    (IntegralMixedMarkedReservedCutView.positive hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.degree hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.scalar_cap hn ht ha hR0) (fun root=>number n root+8)
    (IntegralMixedMarkedReservedCutView.integerSource hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.integer_nonzero hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.integer_cap hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.room hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.data hn ht ha hR0) root [] codes k hcodes charge hcharge v hv p hp hg
  have HF:=IntegralMixedMarkedReservedCutView.full_realizes hn ht ha hR0 root _ HR
  have HC : prefixLength P ((B).key (IntegralMixedMarkedReservedParent.context root))=((B).plan.rules root).length:=by
    rw [IntegralMixedMarkedReservedParent.full_prefix,←IntegralMixedMarkedReservedCutView.plan_eq,
      full_length hn ht ha hR0 root codes k hcodes]
    rfl
  exact IntegralMixedReservedCutActualVertex.vertex_from_full_run P (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive
    (IntegralMixedMarkedReservedParent.context root) root
    (IntegralMixedMarkedReservedParent.key_root hn ht ha hR0 root) HC _ HF

end LeanCanny.Encoding.IntegralMixedMarkedSeedTailVertex
