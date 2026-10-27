/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleHashCuts
public import LeanCanny.Computation.BoundedChoice
public import LeanCanny.Algebra.IntegerSumSpace

/-! # Native ordered enumeration of individual actual-sample hash values

The signed search interval comes from the proved hash bit bound. A candidate
is accepted exactly when it is a root and has the requested number of roots
below it. Every valid ordinal has a unique value and a unique underlying
actual sample root. Invalid ordinals retain a total fallback computation.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleHashEnumeration
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open scoped Classical

noncomputable def radius (P : Readers) (c : List Bool) : ℕ := 2 ^ BoundedCriticalSampleHashChoice.hashBits P c
theorem radius_binary {P : Readers} (h : P.PolyTime) : BinaryFn (radius P) :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow.comp (BoundedCriticalSampleHashChoice.hashBits_unary h)

noncomputable def cut (P : Readers) (s : List Bool) : List Bool := pair (pairFst (pairFst s))
  (pair (pairSnd s) (pair (BinaryNatCode.encode (radius P (pairFst (pairFst s)))) []))
theorem cut_FP {P : Readers} (h : P.PolyTime) : cut P ∈ FP := by
  have ho := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hr := BinaryFn.bits_mem_FP ((radius_binary h).comp ho)
  exact mem_FP_pair ho (mem_FP_pair pairSnd_mem_FP (mem_FP_pair hr (constFn_mem_FP [])))

noncomputable def offset (P : Readers) (s : List Bool) : ℤ :=
  (Nat.fromBitsLE (pairSnd s) : ℤ) - radius P (pairFst (pairFst s))
theorem cut_source (P : Readers) (s : List Bool) : pairFst (cut P s) = pairFst (pairFst s) := pairFst_pair _ _
theorem cut_threshold (P : Readers) (s : List Bool) : RationalCutBits.threshold (cut P s) = (offset P s : ℝ) := by
  simp only [cut, offset, RationalCutBits.threshold, RationalCutBits.numerator, RationalCutBits.positive,
    RationalCutBits.negative, RationalCutBits.divisor, RationalCutBits.denominatorMinusOne,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    show Nat.fromBitsLE ([] : List Bool) = 0 from rfl, Nat.zero_add, Nat.cast_one, div_one]

noncomputable def language (P : Readers) : Language := {s |
  BoundedCriticalSampleHashCuts.count P .neg (cut P s) = Nat.fromBitsLE (pairSnd (pairFst s)) ∧
    0 < BoundedCriticalSampleHashCuts.count P 0 (cut P s)}

theorem language_spec (P : Readers) (s : List Bool) : s ∈ language P ↔
    BoundedCriticalSampleHashRoots.rank P (pairFst (pairFst s)) (offset P s) = Nat.fromBitsLE (pairSnd (pairFst s)) ∧
      offset P s ∈ BoundedCriticalSampleHashRoots.values P (pairFst (pairFst s)) := by
  change _ ∧ _ ↔ _
  rw [BoundedCriticalSampleHashCuts.count_below_at_integer P (cut P s) _ _ (cut_source P s) (cut_threshold P s),
    BoundedCriticalSampleHashCuts.count_zero_pos_iff,
    BoundedCriticalSampleHashCuts.language_at_integer P (cut P s) _ _ (cut_source P s) (cut_threshold P s)]

def accept (z : List Bool) : Bool := decide
  (Nat.fromBitsLE (pairFst (pairSnd z)) = Nat.fromBitsLE (pairSnd (pairFst (pairFst z))) ∧
    0 < Nat.fromBitsLE (pairSnd (pairSnd z)))
theorem accept_FP : (fun z => [accept z]) ∈ FP := by
  have hL := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hR := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have hO := BinaryFn.fromBits (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
  exact ((hL.eq hO).and ((BinaryFn.const 0).lt hR)).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (language P) := by
  have L := (BoundedCriticalSampleHashCuts.evaluator h ha .neg).precompose (cut P) (cut_FP h)
  have R := (BoundedCriticalSampleHashCuts.evaluator h ha 0).precompose (cut P) (cut_FP h)
  have E := (L.pairOutputs R).withInput
  apply E.decider accept accept_FP
  intro s
  simp only [language, Set.mem_ofPred_eq, accept, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

noncomputable def bound (P : Readers) (u : List Bool) : ℕ := 2 * radius P (pairFst u) + 1
theorem bound_binary {P : Readers} (h : P.PolyTime) : BinaryFn (bound P) :=
  ((BinaryFn.const 2).mul ((radius_binary h).comp pairFst_mem_FP)).add (BinaryFn.const 1)

attribute [local irreducible] language radius offset

theorem exists_candidate (P : Readers) (c : List Bool) (r : ℕ) (hr : r < BoundedCriticalSampleCount.count P c) :
    ∃ k < bound P (pair c (BinaryNatCode.encode r)),
      pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode k) ∈ language P := by
  obtain ⟨z, hz, hrank⟩ := BoundedCriticalSampleHashRoots.exists_rank P c r hr
  have hsize : z.natAbs < radius P c := by
    unfold radius
    exact BoundedCriticalSampleHashRoots.values_bound P c z hz
  let k := (z + (radius P c : ℤ)).toNat
  have he : (k : ℤ) - radius P c = z := by dsimp only [k]; omega
  have hk : k < bound P (pair c (BinaryNatCode.encode r)) := by
    simp only [bound, pairFst_pair]
    dsimp only [k]
    omega
  refine ⟨k, hk, ?_⟩
  rw [language_spec]
  have ho : offset P (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode k)) = z := by
    simp only [offset, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact he
  rw [ho]
  simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact ⟨hrank, hz⟩

noncomputable def index (P : Readers) (u : List Bool) : ℕ := BoundedChoice.search (language P) u (bound P u) - 1
noncomputable def value (P : Readers) (u : List Bool) : ℤ := (index P u : ℤ) - radius P (pairFst u)

attribute [local irreducible] BoundedChoice.search

noncomputable def finish (P : Readers) (z : List Bool) : List Bool := IntegerSumBits.difference
  (pair (pairSnd z) (BinaryNatCode.encode (radius P (pairFst (pairFst z)))))
theorem finish_FP {P : Readers} (h : P.PolyTime) : finish P ∈ FP := by
  have hr := BinaryFn.bits_mem_FP ((radius_binary h).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))
  exact mem_FP_comp (mem_FP_pair pairSnd_mem_FP hr) IntegerSumBits.difference_mem_FP

theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => SignStatisticBits.integerCode (value P u)) := by
  have E := BoundedChoice.evaluator (decider h ha) (fun u => BinaryNatCode.encode (bound P u)) (bound_binary h).bits_mem_FP
  have H := E.withInput.postcompose (finish P) (finish_FP h)
  apply H.congr
  funext u
  simp only [finish, Function.comp_apply, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, value, index]
  exact IntegerSumBits.difference_parts _ _

theorem value_spec (P : Readers) (c : List Bool) (r : ℕ) (hr : r < BoundedCriticalSampleCount.count P c) :
    value P (pair c (BinaryNatCode.encode r)) ∈ BoundedCriticalSampleHashRoots.values P c ∧
      BoundedCriticalSampleHashRoots.rank P c (value P (pair c (BinaryNatCode.encode r))) = r := by
  let u := pair c (BinaryNatCode.encode r)
  have hex := exists_candidate P c r hr
  obtain ⟨_, hm⟩ := BoundedChoice.witness (language P) u (bound P u) hex
  change pair u (BinaryNatCode.encode (index P u)) ∈ language P at hm
  rw [language_spec] at hm
  have ho : offset P (pair u (BinaryNatCode.encode (index P u))) = value P u := by
    simp only [offset, value, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [ho] at hm
  simp only [pairFst_pair] at hm
  have hc : pairFst u = c := pairFst_pair _ _
  have hr' : Nat.fromBitsLE (pairSnd u) = r := by
    simp only [u, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [hc, hr'] at hm
  exact ⟨hm.2, hm.1⟩

theorem unique_root (P : Readers) (c : List Bool) (r : ℕ) (hr : r < BoundedCriticalSampleCount.count P c) :
    ∃! x : BoundedCriticalSampleRecordSpan.Root P c,
      BoundedCriticalSampleHashChoice.hash P c x = value P (pair c (BinaryNatCode.encode r)) := by
  obtain ⟨x, hx⟩ := (BoundedCriticalSampleHashRoots.mem_values P c _).mp (value_spec P c r hr).1
  exact ⟨x, hx, fun y hy => BoundedCriticalSampleHashChoice.hash_injective P c (hy.trans hx.symm)⟩

noncomputable def root (P : Readers) (c : List Bool) (r : Fin (BoundedCriticalSampleCount.count P c)) :
    BoundedCriticalSampleRecordSpan.Root P c := Classical.choose (unique_root P c r.val r.isLt)

theorem hash_root (P : Readers) (c : List Bool) (r : Fin (BoundedCriticalSampleCount.count P c)) :
    BoundedCriticalSampleHashChoice.hash P c (root P c r) = value P (pair c (BinaryNatCode.encode r.val)) :=
  (Classical.choose_spec (unique_root P c r.val r.isLt)).1

theorem root_injective (P : Readers) (c : List Bool) : Function.Injective (root P c) := by
  intro r s he
  have hv : value P (pair c (BinaryNatCode.encode r.val)) = value P (pair c (BinaryNatCode.encode s.val)) :=
    (hash_root P c r).symm.trans ((congrArg (BoundedCriticalSampleHashChoice.hash P c) he).trans (hash_root P c s))
  have hr := congrArg (BoundedCriticalSampleHashRoots.rank P c) hv
  rw [(value_spec P c r.val r.isLt).2, (value_spec P c s.val s.isLt).2] at hr
  exact Fin.ext hr

theorem root_surjective (P : Readers) (c : List Bool) : Function.Surjective (root P c) := by
  intro x
  have hx : BoundedCriticalSampleHashChoice.hash P c x ∈ BoundedCriticalSampleHashRoots.values P c :=
    (BoundedCriticalSampleHashRoots.mem_values P c _).mpr ⟨x, rfl⟩
  let r : Fin (BoundedCriticalSampleCount.count P c) :=
    ⟨BoundedCriticalSampleHashRoots.rank P c (BoundedCriticalSampleHashChoice.hash P c x), BoundedCriticalSampleHashRoots.rank_lt P c _ hx⟩
  obtain ⟨hv, hr⟩ := value_spec P c r.val r.isLt
  have he : value P (pair c (BinaryNatCode.encode r.val)) = BoundedCriticalSampleHashChoice.hash P c x :=
    BoundedCriticalSampleHashRoots.rank_unique P c hv hx hr
  exact ⟨r, BoundedCriticalSampleHashChoice.hash_injective P c ((hash_root P c r).trans he)⟩

noncomputable def rootEquiv (P : Readers) (c : List Bool) :
    Fin (BoundedCriticalSampleCount.count P c) ≃ BoundedCriticalSampleRecordSpan.Root P c :=
  Equiv.ofBijective (root P c) ⟨root_injective P c, root_surjective P c⟩

noncomputable def sampleEquiv (P : Readers) (c : List Bool) :
    Fin (BoundedCriticalSampleCount.count P c) ≃ BoundedFullCriticalSamples.Samples P c :=
  (rootEquiv P c).trans (BoundedCriticalSampleLabels.rootEquiv P c)

theorem sampleHash_sample (P : Readers) (c : List Bool) (r : Fin (BoundedCriticalSampleCount.count P c)) :
    BoundedCriticalSampleHashChoice.sampleHash P c (sampleEquiv P c r) =
      value P (pair c (BinaryNatCode.encode r.val)) := by
  simp only [BoundedCriticalSampleHashChoice.sampleHash, sampleEquiv, Equiv.trans_apply,
    BoundedCriticalSampleLabels.parameter, Equiv.symm_apply_apply]
  exact hash_root P c r

theorem descriptor_sample (P : Readers) (c : List Bool) (r : Fin (BoundedCriticalSampleCount.count P c)) :
    BoundedCriticalSampleHashChoice.descriptor P c (sampleEquiv P c r) =
      SignStatisticBits.integerCode (value P (pair c (BinaryNatCode.encode r.val))) := by
  rw [BoundedCriticalSampleHashChoice.descriptor, sampleHash_sample]

theorem unique_sample_descriptor (P : Readers) (c : List Bool) (r : ℕ)
    (hr : r < BoundedCriticalSampleCount.count P c) :
    ∃! x : BoundedFullCriticalSamples.Samples P c, BoundedCriticalSampleHashChoice.descriptor P c x =
      SignStatisticBits.integerCode (value P (pair c (BinaryNatCode.encode r))) := by
  refine ⟨sampleEquiv P c ⟨r, hr⟩, descriptor_sample P c ⟨r, hr⟩, ?_⟩
  intro y hy
  exact BoundedCriticalSampleHashChoice.descriptor_injective P c (hy.trans (descriptor_sample P c ⟨r, hr⟩).symm)

end LeanCanny.Encoding.BoundedCriticalSampleHashEnumeration
