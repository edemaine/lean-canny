/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayEntryCorrect
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Native selection of arbitrary monomial-multiple coefficients -/

@[expose] public section
namespace LeanCanny.Algebra.MacaulayFullBoxBits
open LeanCanny.Encoding LeanCanny.Computation
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

structure Layout where
  arity : List Bool → ℕ
  width : List Bool → ℕ
  level : List Bool → ℕ
  degree : List Bool → ℕ → ℕ

structure Layout.Controls (L : Layout) : Prop where
  arity : UnaryFn L.arity
  width : UnaryFn L.width
  level : UnaryFn L.level
  degree : BinaryFn (fun q => L.degree (pairFst q) (Nat.fromBitsLE (pairSnd q)))

def ctx (q : List Bool) := pairFst q
def idx (q : List Bool) := pairFst (pairSnd q)
def shift (q : List Bool) := pairFst (pairSnd (pairSnd q))
def target (q : List Bool) := pairFst (pairSnd (pairSnd (pairSnd q)))
def parameters (q : List Bool) := pairSnd (pairSnd (pairSnd (pairSnd q)))

@[program_certificate] lemma ctx_FP : Turing.MultiTapeTM.ComputableTidilyInPolyTime
    ctx Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits := by polytime [ctx]
@[program_certificate] lemma idx_FP : Turing.MultiTapeTM.ComputableTidilyInPolyTime
    idx Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits := by polytime [idx]
@[program_certificate] lemma shift_FP : Turing.MultiTapeTM.ComputableTidilyInPolyTime
    shift Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits := by polytime [shift]
@[program_certificate] lemma target_FP : Turing.MultiTapeTM.ComputableTidilyInPolyTime
    target Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits := by polytime [target]
@[program_certificate] lemma parameters_FP : Turing.MultiTapeTM.ComputableTidilyInPolyTime
    parameters Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits := by polytime [parameters]

def packet (c : List Bool) (i a b u v : ℕ) : List Bool :=
  pair c (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode a)
    (pair (BinaryNatCode.encode b) (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))))

@[simp] lemma ctx_packet (c : List Bool) (i a b u v : ℕ) : ctx (packet c i a b u v) = c := by
  simp only [ctx, packet, pairFst_pair]
@[simp] lemma idx_packet (c : List Bool) (i a b u v : ℕ) : idx (packet c i a b u v) = BinaryNatCode.encode i := by
  simp only [idx, packet, pairFst_pair, pairSnd_pair]
@[simp] lemma parameters_packet (c : List Bool) (i a b u v : ℕ) :
    parameters (packet c i a b u v) = pair (BinaryNatCode.encode u) (BinaryNatCode.encode v) := by
  simp only [parameters, packet, pairSnd_pair]

def shiftAt (L : Layout) (q : List Bool) (i : ℕ) :=
  FixedWidthQuery.entry (L.arity ∘ ctx) (L.width ∘ ctx) shift q i

def targetAt (L : Layout) (q : List Bool) (i : ℕ) :=
  FixedWidthQuery.entry (L.arity ∘ ctx) (L.width ∘ ctx) target q i

def shiftRead (L : Layout) := FixedWidthQuery.read (L.arity ∘ ctx) (L.width ∘ ctx) shift

def targetRead (L : Layout) := FixedWidthQuery.read (L.arity ∘ ctx) (L.width ∘ ctx) target

lemma shiftRead_FP {L : Layout} (h : L.Controls) : shiftRead L ∈ FP :=
  FixedWidthQuery.read_mem_FP (h.arity.comp ctx_FP) (h.width.comp ctx_FP) shift_FP
lemma targetRead_FP {L : Layout} (h : L.Controls) : targetRead L ∈ FP :=
  FixedWidthQuery.read_mem_FP (h.arity.comp ctx_FP) (h.width.comp ctx_FP) target_FP

def differenceAt (L : Layout) (q : List Bool) (i : ℕ) := targetAt L q i - shiftAt L q i

def differenceRead (L : Layout) (q : List Bool) :=
  BinaryNat.sub (pair (targetRead L q) (shiftRead L q))

lemma differenceRead_FP {L : Layout} (h : L.Controls) : differenceRead L ∈ FP :=
  mem_FP_comp (mem_FP_pair (targetRead_FP h) (shiftRead_FP h)) BinaryNat.sub_mem_FP

lemma differenceRead_packet (L : Layout) (q : List Bool) (i : ℕ) :
    differenceRead L (pair q (BinaryNatCode.encode i)) = BinaryNatCode.encode (differenceAt L q i) := by
  simp only [differenceRead, targetRead, shiftRead, FixedWidthQuery.read_packet,
    BinaryNat.sub_pair, MacaulayBits.fromBits_encode, differenceAt, targetAt, shiftAt]
  rfl

def differenceWord (L : Layout) (q : List Bool) :=
  FixedWidthNatVector.encode (L.arity (ctx q)) (L.width (ctx q)) (differenceAt L q)

lemma differenceWord_FP {L : Layout} (h : L.Controls) : differenceWord L ∈ FP :=
  FixedWidthNatVector.encode_mem_FP _ _ _ (h.arity.comp ctx_FP) (h.width.comp ctx_FP)
    (differenceRead L) (differenceRead_FP h) (differenceRead_packet L)

def total (L : Layout) (q : List Bool) : ℕ :=
  ∑ i ∈ Finset.range (L.arity (ctx q)), min (shiftAt L q i) (L.level (ctx q) + 1)

lemma total_unary {L : Layout} (h : L.Controls) : UnaryFn (total L) := by
  have hr := mem_FP_comp MacaulayBits.loopQuery_mem_FP (shiftRead_FP h)
  have hc := (((h.level.comp ctx_FP).add (UnaryFn.const 1))).comp pairFst_mem_FP
  have hs := (h.arity.comp ctx_FP).sum (UnaryFn.fromBitsLE_min hr hc)
  refine hs.of_eq (fun q => ?_)
  simp only [MacaulayBits.loopQuery, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.length_replicate, shiftRead, FixedWidthQuery.read_packet, MacaulayBits.fromBits_encode,
    total, shiftAt]

def degreeCode (L : Layout) (q : List Bool) :=
  BinaryNatCode.encode (L.degree (ctx q) (Nat.fromBitsLE (idx q)))

lemma degreeCode_FP {L : Layout} (h : L.Controls) : degreeCode L ∈ FP := by
  have H := mem_FP_comp (mem_FP_pair ctx_FP idx_FP) h.degree.bits_mem_FP
  exact mem_FP_of_eq H (fun q => by simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, degreeCode])

def active (L : Layout) (q : List Bool) : Prop :=
  total L q + L.degree (ctx q) (Nat.fromBitsLE (idx q)) = L.level (ctx q)

instance (L : Layout) : DecidablePred (active L) := fun _ => inferInstanceAs (Decidable (_ = _))

lemma active_FP {L : Layout} (h : L.Controls) : FPPred (active L) := by
  have hs := mem_FP_comp (mem_FP_pair (bits_mem_FP (total_unary h)) (degreeCode_FP h)) BinaryNat.add_mem_FP
  have hl := bits_mem_FP (h.level.comp ctx_FP)
  exact (BinaryNat.eq_fppred hs hl).of_iff (fun q => by
    simp only [Function.comp_apply, BinaryNat.add_pair, Nat.fromBitsLE_bits, degreeCode, BinaryNatCode.encode, active] <;> omega)

def admissible (L : Layout) (q : List Bool) : Prop :=
  ∀ i < L.arity (ctx q), shiftAt L q i ≤ targetAt L q i

instance (L : Layout) : DecidablePred (admissible L) := fun _ => inferInstanceAs (Decidable (∀ i < _, _))

lemma admissible_FP {L : Layout} (h : L.Controls) : FPPred (admissible L) := by
  have hr := mem_FP_comp MacaulayBits.loopQuery_mem_FP (shiftRead_FP h)
  have hc := mem_FP_comp MacaulayBits.loopQuery_mem_FP (targetRead_FP h)
  apply ((BinaryNat.le_fppred hr hc).forall_lt (h.arity.comp ctx_FP)).of_iff
  intro q
  simp only [MacaulayBits.loopQuery, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.length_replicate, shiftRead, targetRead, FixedWidthQuery.read_packet,
    MacaulayBits.fromBits_encode, admissible, shiftAt, targetAt]

def sourceInput (L : Layout) (q : List Bool) :=
  pair (ctx q) (pair (idx q) (pair (BinaryNat.normalize (differenceWord L q)) (parameters q)))

lemma sourceInput_FP {L : Layout} (h : L.Controls) : sourceInput L ∈ FP :=
  mem_FP_pair ctx_FP (mem_FP_pair idx_FP (mem_FP_pair
    (mem_FP_comp (differenceWord_FP h) BinaryNat.normalize_mem_FP) parameters_FP))

def shifted (L : Layout) (coefficient : List Bool → List Bool) (q : List Bool) :=
  if active L q ∧ admissible L q then coefficient (sourceInput L q) else []

lemma shiftedEvaluator {L : Layout} (h : L.Controls) {coefficient : List Bool → List Bool}
    (E : SpaceFunction coefficient) : SpaceFunction (shifted L coefficient) := by
  have ES := E.precompose (sourceInput L) (sourceInput_FP h)
  have EB := SpaceFunction.branch (fun q => decide (active L q ∧ admissible L q))
    ((active_FP h).and (admissible_FP h)).flag_mem_FP ES (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact EB.congr (funext fun q => by simp only [shifted, decide_eq_true_eq, Function.comp_apply])

lemma shiftAt_packet (L : Layout) (c : List Bool) (i u v : ℕ)
    (a b : Macaulay.Index (L.arity c) (L.width c)) (k : Fin (L.arity c)) :
    shiftAt L (packet c i a.val b.val u v) k.val = FixedWidthPolynomial.vector _ _ a k := by
  simp only [shiftAt, FixedWidthQuery.entry, Function.comp_apply, packet, ctx, shift,
    pairFst_pair, pairSnd_pair, k.isLt, ite_true, FixedWidthQuery.coordinate, BinaryNatCode.encode]
  exact (FixedWidthPolynomial.entry_eq_digit _ _ _).trans (FixedWidthPolynomial.vector_apply _ _ a k).symm

lemma targetAt_packet (L : Layout) (c : List Bool) (i u v : ℕ)
    (a b : Macaulay.Index (L.arity c) (L.width c)) (k : Fin (L.arity c)) :
    targetAt L (packet c i a.val b.val u v) k.val = FixedWidthPolynomial.vector _ _ b k := by
  simp only [targetAt, FixedWidthQuery.entry, Function.comp_apply, packet, ctx, target,
    pairFst_pair, pairSnd_pair, k.isLt, ite_true, FixedWidthQuery.coordinate, BinaryNatCode.encode]
  exact (FixedWidthPolynomial.entry_eq_digit _ _ _).trans (FixedWidthPolynomial.vector_apply _ _ b k).symm

private lemma sum_min_add_eq_iff {ι : Type*} (s : Finset ι) (f : ι → ℕ) (T d : ℕ) :
    (∑ i ∈ s, min (f i) (T + 1)) + d = T ↔ (∑ i ∈ s, f i) + d = T := by
  constructor
  · intro h
    have he : ∀ i ∈ s, min (f i) (T + 1) = f i := by
      intro i hi
      have hh := Finset.single_le_sum (f := fun i => min (f i) (T + 1)) (fun _ _ => Nat.zero_le _) hi
      have hle : min (f i) (T + 1) ≤ T := hh.trans (by omega)
      omega
    simpa only [Finset.sum_congr rfl he] using h
  · intro h
    have he : ∀ i ∈ s, min (f i) (T + 1) = f i := by
      intro i hi
      have hh := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) hi
      have hle : f i ≤ T := hh.trans (by omega)
      exact min_eq_left (by omega)
    simpa only [Finset.sum_congr rfl he] using h

lemma active_packet (L : Layout) (c : List Bool) (i u v : ℕ)
    (a b : Macaulay.Index (L.arity c) (L.width c)) :
    active L (packet c i a.val b.val u v) ↔
      (FixedWidthPolynomial.vector _ _ a).degree + L.degree c i = L.level c := by
  simp only [active, total, ctx_packet, idx_packet, MacaulayBits.fromBits_encode]
  rw [sum_min_add_eq_iff, Finset.sum_range]
  simp only [shiftAt_packet, Finsupp.degree_eq_sum]

lemma admissible_packet (L : Layout) (c : List Bool) (i u v : ℕ)
    (a b : Macaulay.Index (L.arity c) (L.width c)) :
    admissible L (packet c i a.val b.val u v) ↔
      FixedWidthPolynomial.vector _ _ a ≤ FixedWidthPolynomial.vector _ _ b := by
  constructor
  · intro h k
    have H := h k.val (by simpa only [ctx, packet, pairFst_pair] using k.isLt)
    simpa only [shiftAt_packet, targetAt_packet] using H
  · intro h k hk
    have hk' : k < L.arity c := by simpa only [ctx, packet, pairFst_pair] using hk
    change shiftAt L (packet c i a.val b.val u v) (⟨k, hk'⟩ : Fin (L.arity c)).val ≤
      targetAt L (packet c i a.val b.val u v) (⟨k, hk'⟩ : Fin (L.arity c)).val
    rw [shiftAt_packet, targetAt_packet]
    exact h ⟨k, hk'⟩

lemma difference_exponent (L : Layout) (c : List Bool) (i u v : ℕ)
    (a b : Macaulay.Index (L.arity c) (L.width c)) :
    RationalSubstitution.Indexed.exponentVector (L.arity c)
      (FixedWidthPolynomial.entry (L.width c)
        (Nat.fromBitsLE (differenceWord L (packet c i a.val b.val u v)))) =
      FixedWidthPolynomial.vector _ _ b - FixedWidthPolynomial.vector _ _ a := by
  ext k
  change FixedWidthPolynomial.entry _ _ k.val = _
  simp only [differenceWord, ctx_packet]
  rw [MacaulayBits.entry_encoded_vector]
  · rw [differenceAt, targetAt_packet, shiftAt_packet, Finsupp.tsub_apply]
  · exact k.isLt
  · exact (Nat.sub_le _ _).trans_lt (by
      rw [targetAt_packet]
      exact FixedWidthPolynomial.vector_lt _ _ b k)

lemma sourceInput_packet (L : Layout) (c : List Bool) (i a b u v : ℕ) :
    sourceInput L (packet c i a b u v) =
      pair c (pair (BinaryNatCode.encode i) (pair
        (BinaryNatCode.encode (Nat.fromBitsLE (differenceWord L (packet c i a b u v))))
        (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))) := by
  simp only [sourceInput, ctx_packet, idx_packet, parameters_packet]
  rw [BinaryNat.normalize_eq_bits]
  rfl

/-- The shift selection uses the actual source coefficient reader. -/
lemma shifted_packet {R : Type*} [CommRing R] (L : Layout) (c : List Bool) (u v : ℕ)
    (p : Fin (L.arity c) → MvPolynomial (Fin (L.arity c)) R) (enc : R → List Bool)
    (coefficient : List Bool → List Bool) (hz : enc 0 = [])
    (hc : ∀ (i : Fin (L.arity c)) r, coefficient
      (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode r)
        (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))) =
      enc ((p i).coeff (RationalSubstitution.Indexed.exponentVector (L.arity c)
        (FixedWidthPolynomial.entry (L.width c) r))))
    (i : Fin (L.arity c)) (a b : Macaulay.Index (L.arity c) (L.width c)) :
    shifted L coefficient (packet c i.val a.val b.val u v) =
      if (FixedWidthPolynomial.vector _ _ a).degree + L.degree c i.val = L.level c then
        enc ((MvPolynomial.monomial (FixedWidthPolynomial.vector _ _ a) 1 * p i).coeff
          (FixedWidthPolynomial.vector _ _ b)) else [] := by
  rw [MvPolynomial.coeff_monomial_mul']
  simp only [one_mul, shifted, active_packet, admissible_packet]
  by_cases ha : (FixedWidthPolynomial.vector _ _ a).degree + L.degree c i.val = L.level c
  · by_cases hb : FixedWidthPolynomial.vector _ _ a ≤ FixedWidthPolynomial.vector _ _ b
    · simp only [ha, hb, and_self, ite_true]
      rw [sourceInput_packet, hc, difference_exponent]
    · simp only [ha, hb, and_false, ite_true, ite_false, hz]
  · simp only [ha, false_and, ite_false]

end LeanCanny.Algebra.MacaulayFullBoxBits
