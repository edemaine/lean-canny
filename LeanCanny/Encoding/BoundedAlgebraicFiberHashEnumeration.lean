/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberHashCuts
public import LeanCanny.Computation.BoundedChoice
public import LeanCanny.Algebra.IntegerSumSpace

/-! # Native ordered enumeration of individual fiber-root hash values

The signed search interval comes from the proved hash bit bound. A candidate
is accepted exactly when it is a root and has the requested number of roots
below it. Every valid ordinal has a unique value and a unique underlying
fiber root. Invalid ordinals retain a total fallback computation.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberHashEnumeration
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open scoped Classical

noncomputable def radius (F : BoundedAlgebraicSlice.Family) (c : List Bool) : ℕ := 2 ^ BoundedAlgebraicFiberHashChoice.hashBits F c
theorem radius_binary {F : BoundedAlgebraicSlice.Family} (A : F.Access) : BinaryFn (radius F) :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow.comp (BoundedAlgebraicFiberHashChoice.hashBits_unary A)

noncomputable def cut (F : BoundedAlgebraicSlice.Family) (s : List Bool) : List Bool := pair (pairFst (pairFst s))
  (pair (pairSnd s) (pair (BinaryNatCode.encode (radius F (pairFst (pairFst s)))) []))
theorem cut_FP {F : BoundedAlgebraicSlice.Family} (A : F.Access) : cut F ∈ FP := by
  have ho := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hr := BinaryFn.bits_mem_FP ((radius_binary A).comp ho)
  exact mem_FP_pair ho (mem_FP_pair pairSnd_mem_FP (mem_FP_pair hr (constFn_mem_FP [])))

noncomputable def offset (F : BoundedAlgebraicSlice.Family) (s : List Bool) : ℤ :=
  (Nat.fromBitsLE (pairSnd s) : ℤ) - radius F (pairFst (pairFst s))
theorem cut_source (F : BoundedAlgebraicSlice.Family) (s : List Bool) : pairFst (cut F s) = pairFst (pairFst s) := pairFst_pair _ _
theorem cut_threshold (F : BoundedAlgebraicSlice.Family) (s : List Bool) : RationalCutBits.threshold (cut F s) = (offset F s : ℝ) := by
  simp only [cut, offset, RationalCutBits.threshold, RationalCutBits.numerator, RationalCutBits.positive,
    RationalCutBits.negative, RationalCutBits.divisor, RationalCutBits.denominatorMinusOne,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    show Nat.fromBitsLE ([] : List Bool) = 0 from rfl, Nat.zero_add, Nat.cast_one, div_one]

noncomputable def language (P : Readers) (F : BoundedAlgebraicSlice.Family) : Language := {s |
  BoundedAlgebraicFiberHashCuts.count P F .neg (cut F s) = Nat.fromBitsLE (pairSnd (pairFst s)) ∧
    0 < BoundedAlgebraicFiberHashCuts.count P F 0 (cut F s)}

theorem language_spec (P : Readers) (F : BoundedAlgebraicSlice.Family) (s : List Bool) : s ∈ language P F ↔
    BoundedAlgebraicFiberHashRoots.rank P F (pairFst (pairFst s)) (offset F s) = Nat.fromBitsLE (pairSnd (pairFst s)) ∧
      offset F s ∈ BoundedAlgebraicFiberHashRoots.values P F (pairFst (pairFst s)) := by
  change _ ∧ _ ↔ _
  rw [BoundedAlgebraicFiberHashCuts.count_below_at_integer P F (cut F s) _ _ (cut_source F s) (cut_threshold F s),
    BoundedAlgebraicFiberHashCuts.count_zero_pos_iff,
    BoundedAlgebraicFiberHashCuts.language_at_integer P F (cut F s) _ _ (cut_source F s) (cut_threshold F s)]

def accept (z : List Bool) : Bool := decide
  (Nat.fromBitsLE (pairFst (pairSnd z)) = Nat.fromBitsLE (pairSnd (pairFst (pairFst z))) ∧
    0 < Nat.fromBitsLE (pairSnd (pairSnd z)))
theorem accept_FP : (fun z => [accept z]) ∈ FP := by
  have hL := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hR := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have hO := BinaryFn.fromBits (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
  exact ((hL.eq hO).and ((BinaryFn.const 0).lt hR)).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (language P F) := by
  have L := (BoundedAlgebraicFiberHashCuts.evaluator h A ha .neg).precompose (cut F) (cut_FP A)
  have R := (BoundedAlgebraicFiberHashCuts.evaluator h A ha 0).precompose (cut F) (cut_FP A)
  have E := (L.pairOutputs R).withInput
  apply E.decider accept accept_FP
  intro s
  simp only [language, Set.mem_ofPred_eq, accept, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

noncomputable def bound (F : BoundedAlgebraicSlice.Family) (u : List Bool) : ℕ := 2 * radius F (pairFst u) + 1
theorem bound_binary {F : BoundedAlgebraicSlice.Family} (A : F.Access) : BinaryFn (bound F) :=
  ((BinaryFn.const 2).mul ((radius_binary A).comp pairFst_mem_FP)).add (BinaryFn.const 1)

attribute [local irreducible] language radius offset

theorem exists_candidate (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (r : ℕ) (hr : r < BoundedAlgebraicSlice.RootCount.count P F c) :
    ∃ k < bound F (pair c (BinaryNatCode.encode r)),
      pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode k) ∈ language P F := by
  obtain ⟨z, hz, hrank⟩ := BoundedAlgebraicFiberHashRoots.exists_rank P F c r hr
  have hsize : z.natAbs < radius F c := by
    unfold radius
    exact BoundedAlgebraicFiberHashRoots.values_bound P F c z hz
  let k := (z + (radius F c : ℤ)).toNat
  have he : (k : ℤ) - radius F c = z := by dsimp only [k]; omega
  have hk : k < bound F (pair c (BinaryNatCode.encode r)) := by
    simp only [bound, pairFst_pair]
    dsimp only [k]
    omega
  refine ⟨k, hk, ?_⟩
  rw [language_spec]
  have ho : offset F (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode k)) = z := by
    simp only [offset, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact he
  rw [ho]
  simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact ⟨hrank, hz⟩

noncomputable def index (P : Readers) (F : BoundedAlgebraicSlice.Family) (u : List Bool) : ℕ := BoundedChoice.search (language P F) u (bound F u) - 1
noncomputable def value (P : Readers) (F : BoundedAlgebraicSlice.Family) (u : List Bool) : ℤ := (index P F u : ℤ) - radius F (pairFst u)

attribute [local irreducible] BoundedChoice.search

noncomputable def finish (F : BoundedAlgebraicSlice.Family) (z : List Bool) : List Bool := IntegerSumBits.difference
  (pair (pairSnd z) (BinaryNatCode.encode (radius F (pairFst (pairFst z)))))
theorem finish_FP {F : BoundedAlgebraicSlice.Family} (A : F.Access) : finish F ∈ FP := by
  have hr := BinaryFn.bits_mem_FP ((radius_binary A).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))
  exact mem_FP_comp (mem_FP_pair pairSnd_mem_FP hr) IntegerSumBits.difference_mem_FP

theorem evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => SignStatisticBits.integerCode (value P F u)) := by
  have E := BoundedChoice.evaluator (decider h A ha) (fun u => BinaryNatCode.encode (bound F u)) (bound_binary A).bits_mem_FP
  have H := E.withInput.postcompose (finish F) (finish_FP A)
  apply H.congr
  funext u
  simp only [finish, Function.comp_apply, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, value, index]
  exact IntegerSumBits.difference_parts _ _

theorem value_spec (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (r : ℕ) (hr : r < BoundedAlgebraicSlice.RootCount.count P F c) :
    value P F (pair c (BinaryNatCode.encode r)) ∈ BoundedAlgebraicFiberHashRoots.values P F c ∧
      BoundedAlgebraicFiberHashRoots.rank P F c (value P F (pair c (BinaryNatCode.encode r))) = r := by
  let u := pair c (BinaryNatCode.encode r)
  have hex := exists_candidate P F c r hr
  obtain ⟨_, hm⟩ := BoundedChoice.witness (language P F) u (bound F u) hex
  change pair u (BinaryNatCode.encode (index P F u)) ∈ language P F at hm
  rw [language_spec] at hm
  have ho : offset F (pair u (BinaryNatCode.encode (index P F u))) = value P F u := by
    simp only [offset, value, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [ho] at hm
  simp only [pairFst_pair] at hm
  have hc : pairFst u = c := pairFst_pair _ _
  have hr' : Nat.fromBitsLE (pairSnd u) = r := by
    simp only [u, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [hc, hr'] at hm
  exact ⟨hm.2, hm.1⟩

theorem unique_root (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (r : ℕ) (hr : r < BoundedAlgebraicSlice.RootCount.count P F c) :
    ∃! x : BoundedAlgebraicFiberRecordSpan.Root P F c,
      BoundedAlgebraicFiberHashChoice.hash P F c x = value P F (pair c (BinaryNatCode.encode r)) := by
  obtain ⟨x, hx⟩ := (BoundedAlgebraicFiberHashRoots.mem_values P F c _).mp (value_spec P F c r hr).1
  exact ⟨x, hx, fun y hy => BoundedAlgebraicFiberHashChoice.hash_injective P F c (hy.trans hx.symm)⟩

noncomputable def root (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (r : Fin (BoundedAlgebraicSlice.RootCount.count P F c)) :
    BoundedAlgebraicFiberRecordSpan.Root P F c := Classical.choose (unique_root P F c r.val r.isLt)

theorem hash_root (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (r : Fin (BoundedAlgebraicSlice.RootCount.count P F c)) :
    BoundedAlgebraicFiberHashChoice.hash P F c (root P F c r) = value P F (pair c (BinaryNatCode.encode r.val)) :=
  (Classical.choose_spec (unique_root P F c r.val r.isLt)).1

theorem root_injective (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) : Function.Injective (root P F c) := by
  intro r s he
  have hv : value P F (pair c (BinaryNatCode.encode r.val)) = value P F (pair c (BinaryNatCode.encode s.val)) :=
    (hash_root P F c r).symm.trans ((congrArg (BoundedAlgebraicFiberHashChoice.hash P F c) he).trans (hash_root P F c s))
  have hr := congrArg (BoundedAlgebraicFiberHashRoots.rank P F c) hv
  rw [(value_spec P F c r.val r.isLt).2, (value_spec P F c s.val s.isLt).2] at hr
  exact Fin.ext hr

theorem root_surjective (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) : Function.Surjective (root P F c) := by
  intro x
  have hx : BoundedAlgebraicFiberHashChoice.hash P F c x ∈ BoundedAlgebraicFiberHashRoots.values P F c :=
    (BoundedAlgebraicFiberHashRoots.mem_values P F c _).mpr ⟨x, rfl⟩
  let r : Fin (BoundedAlgebraicSlice.RootCount.count P F c) :=
    ⟨BoundedAlgebraicFiberHashRoots.rank P F c (BoundedAlgebraicFiberHashChoice.hash P F c x), BoundedAlgebraicFiberHashRoots.rank_lt P F c _ hx⟩
  obtain ⟨hv, hr⟩ := value_spec P F c r.val r.isLt
  have he : value P F (pair c (BinaryNatCode.encode r.val)) = BoundedAlgebraicFiberHashChoice.hash P F c x :=
    BoundedAlgebraicFiberHashRoots.rank_unique P F c hv hx hr
  exact ⟨r, BoundedAlgebraicFiberHashChoice.hash_injective P F c ((hash_root P F c r).trans he)⟩

noncomputable def rootEquiv (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) :
    Fin (BoundedAlgebraicSlice.RootCount.count P F c) ≃ BoundedAlgebraicFiberRecordSpan.Root P F c :=
  Equiv.ofBijective (root P F c) ⟨root_injective P F c, root_surjective P F c⟩

end LeanCanny.Encoding.BoundedAlgebraicFiberHashEnumeration
