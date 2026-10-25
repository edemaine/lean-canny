/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FermatValidity
public import LeanCanny.Encoding.CriticalRegularLevel
public import LeanCanny.Geometry.IntegerRegularSweepCertificate

/-! # Native bounded selection of a valid sweep record

The fixed-width search uses the actual affine/infinity circuit checker. The
constructed regular integer source supplies a valid candidate, so selection
returns a valid record without an assumed validity algorithm or direction.
-/

@[expose] public section
namespace LeanCanny.Encoding.FermatDirectionChoice
open LeanCanny.ETR LeanCanny.Computation LeanCanny.Geometry LeanCanny.Algebra
open FermatSweepCertificate MvPolynomial Turing.MultiTapeTM LeanCanny.Encoding.Brackets
open scoped Classical

noncomputable def test (source : List Bool → List Bool) (dim degree exponent : List Bool → ℕ)
    (a : List Bool → ℤ) (p : List Bool × List Bool) : Bool :=
  decide (FermatValidity.check (source ∘ pairFst) pairSnd (dim ∘ pairFst) (degree ∘ pairFst)
    (exponent ∘ pairFst) (a ∘ pairFst) (pair p.1 p.2) = [true])

noncomputable def record (source : List Bool → List Bool) (dim degree exponent : List Bool → ℕ)
    (a : List Bool → ℤ) : List Bool → List Bool :=
  ImplicitGraph.findWord (test source dim degree exponent a) (fun c => (dim c + 1) * width (dim c) (degree c))

theorem test_computable {source : List Bool → List Bool} {dim degree exponent : List Bool → ℕ}
    {a : List Bool → ℤ} (ht : source ∈ FP) (hd : UnaryFn dim) (hN : BinaryFn degree) (hE : BinaryFn exponent)
    (ha : (fun c => (Term.const (a c)).toData.toBits) ∈ FP) :
    ComputableTidilyInPolySpace (test source dim degree exponent a) (encPair encBits encBits) encBool := by
  have hcheck := FermatValidity.evaluator (mem_FP_comp pairFst_mem_FP ht) pairSnd_mem_FP
    (UnaryFn.comp hd pairFst_mem_FP) (hN.comp (FP.computable pairFst_mem_FP))
    (hE.comp (FP.computable pairFst_mem_FP)) (mem_FP_comp pairFst_mem_FP ha)
  have hpacket := pair_computable (ComputableTidilyInPolyTime.fst encBits encBits)
    (ComputableTidilyInPolyTime.snd encBits encBits)
  have heq := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).computable
  have h := (ComputableTidilyInPolySpace.of_polyTime heq).comp (hcheck.computable.comp (.of_polyTime hpacket))
  apply h.congr
  intro p
  apply Bool.eq_iff_iff.mpr
  simp only [test, decide_eq_true_eq, id_eq]
  rfl

theorem evaluator {source : List Bool → List Bool} {dim degree exponent : List Bool → ℕ}
    {a : List Bool → ℤ} (ht : source ∈ FP) (hd : UnaryFn dim) (hN : BinaryFn degree) (hE : BinaryFn exponent)
    (ha : (fun c => (Term.const (a c)).toData.toBits) ∈ FP) :
    SpaceFunction (record source dim degree exponent a) :=
  ⟨ImplicitGraph.findWord_computable (test_computable ht hd hN hE ha) (recordLength_unary hd hN)⟩

theorem record_length (source : List Bool → List Bool) (dim degree exponent : List Bool → ℕ)
    (a : List Bool → ℤ) (c : List Bool) :
    (record source dim degree exponent a c).length = (dim c + 1) * width (dim c) (degree c) :=
  ImplicitGraph.findWord_length _ _ _

theorem test_correct (source : List Bool → List Bool) (dim degree exponent : List Bool → ℕ)
    (a : List Bool → ℤ) (c r : List Bool) (low : MvPolynomial (Fin (dim c + 2)) ℤ)
    (ht : (TermView.term (source c)).toPolynomial = rename Fin.val low) (ha : a c ≠ 0)
    (hlow : low.totalDegree < degree c) (hN : 1 < degree c) :
    test source dim degree exponent a (c, r) = true ↔
      Valid (dyadicLow low (exponent c)) (dyadicLeading (a c) (exponent c)) (degree c) r := by
  have hv := FermatValidity.correct source (fun _ => r) dim degree exponent a c low ht ha hlow hN
  simp only [test, FermatValidity.check_packet, hv]
  simp

theorem record_valid (source : List Bool → List Bool) (dim degree exponent : List Bool → ℕ)
    (a : List Bool → ℤ) (c : List Bool) (low : MvPolynomial (Fin (dim c + 2)) ℤ)
    (ht : (TermView.term (source c)).toPolynomial = rename Fin.val low) (ha : a c ≠ 0)
    (hlow : low.totalDegree < degree c) (hN : 1 < degree c)
    (hex : ∃ r : List Bool, r.length = (dim c + 1) * width (dim c) (degree c) ∧
      Valid (dyadicLow low (exponent c)) (dyadicLeading (a c) (exponent c)) (degree c) r) :
    Valid (dyadicLow low (exponent c)) (dyadicLeading (a c) (exponent c)) (degree c)
      (record source dim degree exponent a c) := by
  apply (test_correct source dim degree exponent a c _ low ht ha hlow hN).mp
  apply ImplicitGraph.findWord_correct
  obtain ⟨r, hr, hv⟩ := hex
  exact ⟨r, hr, (test_correct source dim degree exponent a c r low ht ha hlow hN).mpr hv⟩

def regularExponent (dim degree mass : List Bool → ℕ) (c : List Bool) : ℕ :=
  IntegerRegularSource.exponent (dim c + 1) (degree c) (mass c)

theorem regularExponent_binary {dim degree mass : List Bool → ℕ}
    (hd : UnaryFn dim) (hN : BinaryFn degree) (hb : BinaryFn mass) : BinaryFn (regularExponent dim degree mass) :=
  (LeanCanny.Encoding.CriticalRegularLevel.exponent_binary (hd.add (UnaryFn.const 1)) hN hb).of_eq (fun _ => rfl)

theorem regular_evaluator {source : List Bool → List Bool} {dim degree mass : List Bool → ℕ}
    {a : List Bool → ℤ} (ht : source ∈ FP) (hd : UnaryFn dim) (hN : BinaryFn degree) (hb : BinaryFn mass)
    (ha : (fun c => (Term.const (a c)).toData.toBits) ∈ FP) :
    SpaceFunction (record source dim degree (regularExponent dim degree mass) a) :=
  evaluator ht hd hN (regularExponent_binary hd hN hb) ha

theorem regular_record_valid (source : List Bool → List Bool) (dim degree mass : List Bool → ℕ)
    (a : List Bool → ℤ) (c : List Bool) (low : MvPolynomial (Fin (dim c + 2)) ℤ)
    (ht : (TermView.term (source c)).toPolynomial = rename Fin.val low) (ha : a c ≠ 0)
    (hlow : low.totalDegree < degree c) (hN : 1 < degree c)
    (hp : MvMass.mass (FermatCriticalHomogenization.polynomial low (a c) (degree c)) ≤ 2 ^ mass c) :
    Valid ((IntegerRegularSource.lower low (degree c) (mass c)).map (Int.castRingHom ℚ))
      (IntegerRegularSource.leading (dim c + 1) (a c) (degree c) (mass c) : ℚ) (degree c)
        (record source dim degree (regularExponent dim degree mass) a c) := by
  have hex := IntegerRegularSweepCertificate.exists_valid_record low (a c) (degree c) (mass c) hlow ha hN hp
  have he : ∃ r : List Bool, r.length = (dim c + 1) * width (dim c) (degree c) ∧
      Valid (dyadicLow low (regularExponent dim degree mass c))
        (dyadicLeading (a c) (regularExponent dim degree mass c)) (degree c) r := by
    simpa only [dyadicLow, dyadicLeading, regularExponent, IntegerRegularSource.lower,
      IntegerRegularSource.leading, IntegerRegularSource.scale] using hex
  have hv := record_valid source dim degree (regularExponent dim degree mass) a c low ht ha hlow hN he
  simpa only [dyadicLow, dyadicLeading, regularExponent, IntegerRegularSource.lower,
    IntegerRegularSource.leading, IntegerRegularSource.scale] using hv

end LeanCanny.Encoding.FermatDirectionChoice
