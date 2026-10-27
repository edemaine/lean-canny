/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionProbeSource
public import LeanCanny.Computation.SpaceFunctionBranch

/-! # Native streamed derivative signs at enumerated projection roots

Input is `pair (pair sourceContext rootOrdinal) derivativeOrder`. The hash
parameters, root label, and both determinant signs are computed internally.
Only one sign tag is output; no complete derivative signature is stored.
Orders above the projection degree bound return zero.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionSignatureRead
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets
open scoped Classical

def original (q : List Bool) : List Bool := pairFst (pairFst q)
theorem original_FP : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

noncomputable def descriptor (P : Readers) (q : List Bool) : List Bool :=
  BoundedProjectionProbeSource.context P (original q)
    (BoundedProjectionHashEnumeration.value P (pairFst q)) (Nat.fromBitsLE (pairSnd q))

theorem descriptor_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (descriptor P) := by
  have B := (BoundedProjectionHashChoice.evaluator h ha).precompose original original_FP
  have H := (BoundedProjectionHashEnumeration.evaluator h ha).precompose pairFst pairFst_mem_FP
  have D := SpaceFunction.ofFP (BinaryNat.normalize ∘ pairSnd) (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)
  have E := B.pairOutputs (H.pairOutputs D)
  exact E.congr (funext fun q => by
    simp only [descriptor, BoundedProjectionProbeSource.context, BoundedProjectionProbeEntries.context,
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

noncomputable def probe (P : Readers) (q : List Bool) : List Bool :=
  InfinitesimalSign.encode
    (SignType.sign (BoundedProjectionProbeCoefficient.firstCoefficient P false (descriptor P q)) *
      SignType.sign (BoundedProjectionProbeCoefficient.firstCoefficient P true (descriptor P q)))

attribute [local irreducible] BoundedProjectionProbeCoefficient.firstCoefficient descriptor

theorem probe_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (probe P) := by
  have D := descriptor_evaluator h ha
  have L := D.chain (BoundedProjectionProbeCoefficient.sign_evaluator h ha false)
  have R := D.chain (BoundedProjectionProbeCoefficient.sign_evaluator h ha true)
  have E := (L.pairOutputs R).postcompose multiplyTags multiplyTags_FP
  exact E.congr (funext fun q => by
    simp only [Function.comp_apply, multiplyTags_packet, probe])

noncomputable def inRange (P : Readers) (q : List Bool) : Bool :=
  decide (Nat.fromBitsLE (pairSnd q) ≤ BoundedProjectionRootCount.degree P (original q))
theorem inRange_FP {P : Readers} (h : P.PolyTime) : (fun q => [inRange P q]) ∈ FP :=
  ((BinaryFn.fromBits pairSnd_mem_FP).le ((BoundedProjectionRootCount.degree_binary h).comp original_FP)).flag_mem_FP

noncomputable def value (P : Readers) (q : List Bool) : List Bool :=
  if inRange P q then probe P q else []

theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P) :=
  SpaceFunction.branch (inRange P) (inRange_FP h) (probe_evaluator h ha) (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))

theorem descriptor_packet (P : Readers) (c : List Bool) (r k : ℕ) :
    descriptor P (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode k)) =
      BoundedProjectionProbeSource.context P c
        (BoundedProjectionHashEnumeration.value P (pair c (BinaryNatCode.encode r))) k := by
  simp only [descriptor, original, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem signature_packet (P : Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c))
    (d : BoundedProjectionMoments.Feature P c) :
    value P (pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode d.val)) =
      InfinitesimalSign.encode (BoundedProjectionMoments.signature P c (BoundedProjectionHashEnumeration.root P c r) d) := by
  have hd : d.val ≤ BoundedProjectionRootCount.degree P c := by have := d.isLt; omega
  have hg : inRange P (pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode d.val)) = true := by
    simp only [inRange, original, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, hd, decide_true]
  rw [value, hg, ite_eq_left rfl]
  unfold probe
  rw [descriptor_packet P c r.val d.val, BoundedProjectionProbeSource.sign_packet P false c _ d,
    BoundedProjectionProbeSource.sign_packet P true c _ d]
  simp only [BoundedProjectionProbeSource.featureFunction, Bool.false_eq_true, ↓reduceIte]
  rw [BoundedProjectionSignatureProbe.signature_at_ordinal]

theorem derivative_packet (P : Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) (k : ℕ) :
    value P (pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign
        (((BoundedProjectionThom.polynomial P c k).map (Int.castRingHom ℝ)).eval
          (BoundedProjectionHashEnumeration.root P c r).val)) := by
  by_cases hk : k ≤ BoundedProjectionRootCount.degree P c
  · exact (signature_packet P c r ⟨k, by omega⟩).trans
      (congrArg InfinitesimalSign.encode (BoundedProjectionRecordSpan.signature_apply P c _ ⟨k, by omega⟩))
  · have hdeg : (BoundedCriticalProjection.polynomial P c).natDegree ≤ BoundedProjectionRootCount.degree P c :=
      BoundedCriticalProjection.polynomial_degree P c
    have hp : BoundedProjectionThom.polynomial P c k = 0 :=
      Polynomial.iterate_derivative_eq_zero (hdeg.trans_lt (by omega))
    simp only [value, inRange, original, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      hk, decide_false, Bool.false_eq_true, ↓reduceIte, hp, Polynomial.map_zero, Polynomial.eval_zero, sign_zero,
      InfinitesimalSign.encode]

/-- Short root ordinals label every distinct realizable signature, even though
the full signature may have exponentially many coordinates. -/
noncomputable def signature (P : Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    BoundedProjectionMoments.Feature P c → SignType :=
  BoundedProjectionMoments.signature P c (BoundedProjectionHashEnumeration.root P c r)

theorem signature_injective (P : Readers) (c : List Bool) : Function.Injective (signature P c) := by
  intro r s hs
  exact BoundedProjectionHashEnumeration.root_injective P c
    (BoundedProjectionMoments.signature_injective P c hs)

theorem signature_range (P : Readers) (c : List Bool) :
    Set.range (signature P c) = Set.range (BoundedProjectionMoments.signature P c) := by
  ext s
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨BoundedProjectionHashEnumeration.root P c r, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨r, rfl⟩ := BoundedProjectionHashEnumeration.root_surjective P c x
    exact ⟨r, rfl⟩

end LeanCanny.Encoding.BoundedProjectionSignatureRead
