/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SignStatisticSpace
public import LeanCanny.Computation.PolyTimeBinaryNat
/-! # Total sign statistics with local semantic contracts

Malformed sign words decode to zero. The native scan is total; correctness
at a valid source needs only that source's actual selected signs.
-/
@[expose] public section
namespace LeanCanny.Algebra.CanonicalSignStatisticBits
open LeanCanny.Encoding LeanCanny.Computation PrincipalSubresultant

def decode (w : List Bool) : SignType :=
  if w=[true] then .neg else if w=[false,true] then .pos else .zero

def normalize (w : List Bool) : List Bool :=
  if w=[true] then [true] else if w=[false,true] then [false,true] else []

theorem normalize_decode (w : List Bool) : normalize w=InfinitesimalSign.encode (decode w) :=by
  unfold normalize decode
  split_ifs <;> rfl

theorem decode_encode (s : SignType) : decode (InfinitesimalSign.encode s)=s :=by cases s <;> decide

theorem normalize_FP : normalize∈FP :=by
  have H1:=Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])
  have H2:=Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [false,true])
  exact H1.ite_mem_FP (constFn_mem_FP [true])
    (H2.ite_mem_FP (constFn_mem_FP [false,true]) (constFn_mem_FP []))

noncomputable def value (f : List Bool→List Bool) (count : List Bool→ℕ) (c : List Bool) : ℤ :=
  permanencesMinusVariations ((List.range (count c)).map
    (fun i=>decode (f (pair c (BinaryNatCode.encode i)))))

theorem evaluator {f : List Bool→List Bool} (E : SpaceFunction f)
    (count : List Bool→ℕ) (hc : BinaryFn count) :
    SpaceFunction (fun c=>SignStatisticBits.integerCode (value f count c)) :=by
  have E0:=SignStatisticBits.evaluator (E.postcompose normalize normalize_FP)
    (fun c=>BinaryNatCode.encode (count c)) hc.bits_mem_FP
    (fun c i=>decode (f (pair c (BinaryNatCode.encode i)))) (fun _ _=>normalize_decode _)
  apply E0.congr
  funext c
  simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rfl

theorem value_at (f : List Bool→List Bool) (count : List Bool→ℕ) (c : List Bool) (a : ℕ→ℝ)
    (hf : ∀i<count c,f (pair c (BinaryNatCode.encode i))=InfinitesimalSign.encode (SignType.sign (a i))) :
    value f count c=permanencesMinusVariations ((List.range (count c)).map a) :=by
  unfold value
  have HH : ((List.range (count c)).map (fun i=>decode (f (pair c (BinaryNatCode.encode i)))))=
      ((List.range (count c)).map a).map SignType.sign :=by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    rw [hf i (List.mem_range.mp hi),decode_encode]
    rfl
  rw [HH,permanencesMinusVariations_map_sign]

end LeanCanny.Algebra.CanonicalSignStatisticBits
