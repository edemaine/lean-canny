/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberProbeSource
public import LeanCanny.Computation.SpaceFunctionBranch

/-! # Native streamed derivative signs at enumerated fiber roots

Input is `pair (pair sourceContext rootOrdinal) derivativeOrder`. The hash
parameters, root label, and both determinant signs are computed internally.
Only one sign tag is output; no complete derivative signature is stored.
Orders above the fiber degree bound return zero.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberSignatureRead
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets
open scoped Classical

def original (q : List Bool) : List Bool := pairFst (pairFst q)
theorem original_FP : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

noncomputable def descriptor (P : Readers) (F : BoundedAlgebraicSlice.Family) (q : List Bool) : List Bool :=
  BoundedAlgebraicFiberProbeSource.context P F (original q)
    (BoundedAlgebraicFiberHashEnumeration.value P F (pairFst q)) (Nat.fromBitsLE (pairSnd q))

theorem descriptor_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (descriptor P F) := by
  have B := (BoundedAlgebraicFiberHashChoice.evaluator h A ha).precompose original original_FP
  have H := (BoundedAlgebraicFiberHashEnumeration.evaluator h A ha).precompose pairFst pairFst_mem_FP
  have D := SpaceFunction.ofFP (BinaryNat.normalize ∘ pairSnd) (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)
  have E := B.pairOutputs (H.pairOutputs D)
  exact E.congr (funext fun q => by
    simp only [descriptor, BoundedAlgebraicFiberProbeSource.context, BoundedAlgebraicFiberProbeEntries.context,
      Function.comp_apply, BinaryNat.normalize_eq_bits, BinaryNatCode.encode])

def multiplyTags (z : List Bool) : List Bool :=
  if pairFst z = [] ∨ pairSnd z = [] then []
  else if pairFst z = pairSnd z then [false, true] else [true]

theorem multiplyTags_FP : multiplyTags ∈ FP := by
  have hz := (stringEq_fppred pairFst_mem_FP (constFn_mem_FP [])).or
    (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP []))
  have he := (stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).ite_mem_FP
    (constFn_mem_FP [false, true]) (constFn_mem_FP [true])
  exact hz.ite_mem_FP (constFn_mem_FP []) he

theorem multiplyTags_packet (a b : SignType) :
    multiplyTags (pair (InfinitesimalSign.encode a) (InfinitesimalSign.encode b)) =
      InfinitesimalSign.encode (a * b) := by
  cases a <;> cases b <;> decide

noncomputable def probe (P : Readers) (F : BoundedAlgebraicSlice.Family) (q : List Bool) : List Bool :=
  InfinitesimalSign.encode
    (SignType.sign (BoundedAlgebraicFiberProbeCoefficient.firstCoefficient P F false (descriptor P F q)) *
      SignType.sign (BoundedAlgebraicFiberProbeCoefficient.firstCoefficient P F true (descriptor P F q)))

attribute [local irreducible] BoundedAlgebraicFiberProbeCoefficient.firstCoefficient descriptor

theorem probe_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (probe P F) := by
  have D := descriptor_evaluator h A ha
  have L := D.chain (BoundedAlgebraicFiberProbeCoefficient.sign_evaluator h A ha false)
  have R := D.chain (BoundedAlgebraicFiberProbeCoefficient.sign_evaluator h A ha true)
  have E := (L.pairOutputs R).postcompose multiplyTags multiplyTags_FP
  exact E.congr (funext fun q => by
    simp only [Function.comp_apply, multiplyTags_packet, probe])

noncomputable def inRange (F : BoundedAlgebraicSlice.Family) (q : List Bool) : Bool :=
  decide (Nat.fromBitsLE (pairSnd q) ≤ F.degree (pairFst (original q)))
theorem inRange_FP {F : BoundedAlgebraicSlice.Family} (A : F.Access) : (fun q => [inRange F q]) ∈ FP :=
  ((BinaryFn.fromBits pairSnd_mem_FP).le (A.degree_binary.comp (mem_FP_comp original_FP pairFst_mem_FP))).flag_mem_FP

noncomputable def value (P : Readers) (F : BoundedAlgebraicSlice.Family) (q : List Bool) : List Bool :=
  if inRange F q then probe P F q else []

theorem evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P F) :=
  SpaceFunction.branch (inRange F) (inRange_FP A) (probe_evaluator h A ha) (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))

theorem descriptor_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (r k : ℕ) :
    descriptor P F (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode k)) =
      BoundedAlgebraicFiberProbeSource.context P F c
        (BoundedAlgebraicFiberHashEnumeration.value P F (pair c (BinaryNatCode.encode r))) k := by
  simp only [descriptor, original, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem signature_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (r : Fin (BoundedAlgebraicSlice.RootCount.count P F c))
    (d : BoundedAlgebraicFiberThom.Feature F c) :
    value P F (pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode d.val)) =
      InfinitesimalSign.encode (BoundedAlgebraicFiberThom.signature P F c (BoundedAlgebraicFiberHashEnumeration.root P F c r) d) := by
  have hd : d.val ≤ F.degree (pairFst c) := by have := d.isLt; omega
  have hg : inRange F (pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode d.val)) = true := by
    simp only [inRange, original, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, hd, decide_true]
  rw [value, hg, ite_eq_left rfl]
  unfold probe
  rw [descriptor_packet P F c r.val d.val, BoundedAlgebraicFiberProbeSource.sign_packet P F false c _ d,
    BoundedAlgebraicFiberProbeSource.sign_packet P F true c _ d]
  simp only [BoundedAlgebraicFiberProbeSource.featureFunction, Bool.false_eq_true, ↓reduceIte]
  rw [BoundedAlgebraicFiberSignatureProbe.signature_at_ordinal]

theorem derivative_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool)
    (r : Fin (BoundedAlgebraicSlice.RootCount.count P F c)) (k : ℕ) :
    value P F (pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign
        (((Polynomial.derivative^[k]) (BoundedAlgebraicSlice.specialized P F c)).eval
          (BoundedAlgebraicFiberHashEnumeration.root P F c r).val)) := by
  by_cases hk : k ≤ F.degree (pairFst c)
  · exact signature_packet P F c r ⟨k, by omega⟩
  · have hp : (Polynomial.derivative^[k]) (BoundedAlgebraicSlice.specialized P F c) = 0 :=
      Polynomial.iterate_derivative_eq_zero ((BoundedAlgebraicSlice.specialized_degree P F c).trans_lt (by omega))
    simp only [value, inRange, original, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      hk, decide_false, Bool.false_eq_true, ↓reduceIte, hp, Polynomial.eval_zero, sign_zero,
      InfinitesimalSign.encode]

/-- Short root ordinals label every distinct realizable signature, even though
the full signature may have exponentially many coordinates. -/
noncomputable def signature (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (r : Fin (BoundedAlgebraicSlice.RootCount.count P F c)) :
    BoundedAlgebraicFiberThom.Feature F c → SignType :=
  BoundedAlgebraicFiberThom.signature P F c (BoundedAlgebraicFiberHashEnumeration.root P F c r)

theorem signature_injective (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) : Function.Injective (signature P F c) := by
  intro r s hs
  exact BoundedAlgebraicFiberHashEnumeration.root_injective P F c
    (BoundedAlgebraicFiberThom.signature_injective P F c hs)

theorem signature_range (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) :
    Set.range (signature P F c) = Set.range (BoundedAlgebraicFiberThom.signature P F c) := by
  ext s
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨BoundedAlgebraicFiberHashEnumeration.root P F c r, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨r, rfl⟩ := BoundedAlgebraicFiberHashEnumeration.root_surjective P F c x
    exact ⟨r, rfl⟩

end LeanCanny.Encoding.BoundedAlgebraicFiberSignatureRead
