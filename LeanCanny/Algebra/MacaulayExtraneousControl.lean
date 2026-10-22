/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayExtraneous
public import LeanCanny.Algebra.MacaulayEntryCorrect
public import LeanCanny.Algebra.PolynomialAffineEntrySpace

/-! # Polynomial-time selection of extraneous Macaulay indices

The arity bounds a count of coordinate powers dividing the queried monomial.
Together with the existing exact total-degree guard, count greater than one
selects precisely the extraneous principal indices. No monomial enumeration
or index-set cardinality computation is needed.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayBits
open LeanCanny.Encoding
open scoped BigOperators

def eligibleLoop (L : Layout) (q : List Bool) : Prop :=
  degreeLoop L q ≤ rowAt L (pairFst q) (pairSnd q).length

instance (L : Layout) (q : List Bool) : Decidable (eligibleLoop L q) := inferInstanceAs (Decidable (_ ≤ _))

theorem eligibleLoop_fppred {L : Layout} (h : L.PolyTime) : FPPred (eligibleLoop L) := by
  have hr := mem_FP_comp loopQuery_mem_FP (rowRead_mem_FP h)
  have hf := BinaryNat.le_fppred (bits_mem_FP (degreeLoop_unary h)) hr
  refine hf.of_iff (fun q => ?_)
  simp only [loopQuery, Function.comp_apply,
    rowRead, FixedWidthQuery.read_packet, fromBits_encode, Nat.fromBitsLE_bits, eligibleLoop, rowAt]

def eligibleCount (L : Layout) (p : List Bool) : ℕ :=
  ((Finset.range (L.arity (context p))).filter (fun i => L.degree (context p) i ≤ rowAt L p i)).card

theorem eligibleCount_unary {L : Layout} (h : L.PolyTime) : UnaryFn (eligibleCount L) := by
  have hc := (h.arity.comp context_mem_FP).count (eligibleLoop_fppred h)
  refine hc.of_eq (fun p => ?_)
  simp only [eligibleLoop, degreeLoop, pairFst_pair, pairSnd_pair, List.length_replicate, eligibleCount]

theorem eligibleCount_packet (L : Layout) (q : List Bool) (r : Indices L q) (s : ℕ) :
    eligibleCount L (packet q r.val s) =
      (Macaulay.eligible (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r)).card := by
  simp only [eligibleCount, context_packet, Macaulay.eligible, Finset.card_filter]
  rw [Finset.sum_range]
  simp only [rowAt_packet, Degrees]

def extraneous (L : Layout) (p : List Bool) : Prop := active L p ∧ 1 < eligibleCount L p

instance (L : Layout) (p : List Bool) : Decidable (extraneous L p) := inferInstanceAs (Decidable (_ ∧ _))

theorem extraneous_fppred {L : Layout} (h : L.PolyTime) : FPPred (extraneous L) :=
  (active_fppred h).and (FPPred.lt (UnaryFn.const 1) (eligibleCount_unary h))

theorem extraneous_packet (L : Layout) (q : List Bool) (r : Indices L q) (s : ℕ) :
    extraneous L (packet q r.val s) ↔ r ∈ Macaulay.extraneousIndices (Degrees L (pairFst q)) (L.width (pairFst q)) := by
  rw [Macaulay.mem_extraneousIndices]
  simp only [extraneous, active_packet, eligibleCount_packet, Macaulay.Unreduced]

def extraneousRowQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst q) []) (pair (PolynomialAffineEntryBits.row q) [])

theorem extraneousRowQuery_mem_FP : extraneousRowQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair pairFst_mem_FP (constFn_mem_FP []))
    (mem_FP_pair PolynomialAffineEntryBits.row_mem_FP (constFn_mem_FP []))

def extraneousEntry (L : Layout) (q : List Bool) : Prop := extraneous L (extraneousRowQuery q)

instance (L : Layout) (q : List Bool) : Decidable (extraneousEntry L q) := inferInstanceAs (Decidable (extraneous L _))

theorem extraneousEntry_fppred {L : Layout} (h : L.PolyTime) : FPPred (extraneousEntry L) :=
  (extraneous_fppred h).comp extraneousRowQuery_mem_FP

theorem extraneousRowQuery_packet (c : List Bool) (r s d : ℕ) :
    extraneousRowQuery (PolynomialAffineEntryBits.packet c r s d) = packet (pair c []) r 0 := by
  simp only [extraneousRowQuery, PolynomialAffineEntryBits.row, PolynomialAffineEntryBits.packet,
    pairFst_pair, pairSnd_pair, packet, BinaryNatCode.encode]
  rfl

theorem extraneousEntry_packet (L : Layout) (c : List Bool)
    (r : Macaulay.Index (L.arity c) (L.width c)) (s d : ℕ) :
    extraneousEntry L (PolynomialAffineEntryBits.packet c r.val s d) ↔
      r ∈ Macaulay.extraneousIndices (Degrees L c) (L.width c) := by
  rw [extraneousEntry, extraneousRowQuery_packet]
  have h := extraneous_packet L (pair c [])
  dsimp only [Indices] at h
  rw [pairFst_pair] at h
  exact h r 0

end LeanCanny.Algebra.MacaulayBits
