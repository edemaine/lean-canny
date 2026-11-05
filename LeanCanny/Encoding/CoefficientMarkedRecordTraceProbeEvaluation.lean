/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceProbePhysical
public import LeanCanny.Encoding.IntegralFramedTerminalCutReadback
public import LeanCanny.Encoding.IntegralFramedPhysicalSuffixPoint
public import LeanCanny.Algebra.CoefficientFinitePhysicalQuery
/-! # Native cut coefficients evaluated on the SAME later physical tuple -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTraceProbeEvaluation
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedFramedHistoryFamilyBits IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem eval_natural_heq {a b : ℕ} (p : MvPolynomial (Fin a) ℤ) (q : MvPolynomial (Fin b) ℤ)
    (h : a = b) (hp : HEq p q) (z : ℕ → ℝ) :
    p.eval₂ (Int.castRingHom ℝ) (fun i => z i.val) = q.eval₂ (Int.castRingHom ℝ) (fun i => z i.val) := by
  cases h
  cases eq_of_heq hp
  rfl

/-- This reads the full relative factor, with the caller's exact coefficient
and clipped creating choice, before any stored-degree truncation. -/
theorem terminal_evaluation (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool → List Bool) (c : List Bool) (e k : ℕ)
    (hc : IntegralMixedFramedFullCutProbeBits.Active P c)
    (he : e ≤ 2^P.width (RankedHistoryTask.root c)) (hk : k ≤ 2^P.width (RankedHistoryTask.root c))
    (hfit : IntegralFramedTerminalCutTest.oldArity P D H c (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)) ≤
      IntegralFramedTerminalCutTest.count P D H key c) (z : ℕ → ℝ) :
    (IntegralFramedTerminalCutTest.polynomial P D H key c
      (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k))).eval₂ (Int.castRingHom ℝ) (fun i => z i.val) =
    (IntegralMixedCutCoefficientPolynomialKey.polynomial (family P D H)
      (IntegralMixedFramedChoiceProbeSourceBits.horizon P c) (IntegralMixedVirtualTaskBits.saved P c) e k).eval₂
        (Int.castRingHom ℝ) (fun i => z i.val) := by
  let d := pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)
  have hq : IntegralFramedCutCoefficientTest.query P (pair c d) =
      IntegralMixedCutCoefficientQueryBits.query P (pair c d) := by
    simp only [IntegralFramedCutCoefficientTest.query, pairFst_pair, pairSnd_pair]
  have hp := IntegralMixedCutCoefficientPolynomialKey.packet P D H c e k hc he hk
  have hsource : HEq (IntegralMixedFramedChoiceProbeSourceBits.polynomial P D H
      (IntegralFramedCutCoefficientTest.query P (pair c d)))
      (IntegralMixedCutCoefficientPolynomialKey.polynomial (family P D H)
        (IntegralMixedFramedChoiceProbeSourceBits.horizon P c) (IntegralMixedVirtualTaskBits.saved P c) e k) := by
    rw [hq]
    exact hp
  have hd := IntegralFramedTerminalCutTest.oldArity_parent P D H c d
  have hev := eval_natural_heq _ _ hd hsource z
  unfold IntegralFramedTerminalCutTest.polynomial
  rw [dite_eq_left hfit]
  refine (MvPolynomial.eval₂_rename (Int.castRingHom ℝ) (Fin.cast (Nat.min_eq_left hfit).symm)
    (fun i => z i.val) _).trans ?_
  exact hev

private theorem scalar_column (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedFramedHeaderBits.Represents P D H T)
    (key : List Bool) (i : Fin ((family P D H).birth key)) :
    ((IntegralFramedPhysicalSquare.sampler P D H key).scalar i).val =
      IntegralMixedFramedPhysicalIndex.scalarColumn P T (pair key (BinaryNatCode.encode i.val)) :=
  (IntegralMixedFramedPhysicalIndex.scalarColumn_actual P D H T ht key i).symm

private theorem natural_fin {N : ℕ} (z : Fin N → ℝ) (i : Fin N) :
    CoefficientFinitePhysicalQuery.natural z i.val = z i := by
  unfold CoefficientFinitePhysicalQuery.natural
  exact dite_eq_left i.isLt

private theorem raw_column (B : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
    (ht : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
    (j : Fin ((family B.parameters B.plan B.data).birth (B.key c))) :
    IntegralFramedPhysicalSuffixTest.rawTuple B c w hw j.val =
      CoefficientFinitePhysicalQuery.natural
        (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hw).val
        (IntegralMixedFramedPhysicalIndex.scalarColumn B.parameters T (pair (B.key c) (BinaryNatCode.encode j.val))) := by
  unfold IntegralFramedPhysicalSuffixTest.rawTuple IntegralMixedFramedBankObservation.extend
  rw [dite_eq_left j.isLt, IntegralFramedPhysicalSquare.scalarTuple_map]
  have hc := scalar_column B.parameters B.plan B.data T ht (B.key c) j
  rw [← hc]
  let i : Fin ((IntegralFramedPhysicalBankTerm.input B).count c) :=
    (IntegralFramedPhysicalSquare.sampler B.parameters B.plan B.data (B.key c)).scalar j
  change (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hw).val i =
    CoefficientFinitePhysicalQuery.natural
      (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hw).val i.val
  exact (natural_fin _ i).symm

/-- Earlier and later samplers refer to exactly the same old raw digit. This
is a value statement on the later sampler's OWN complete decoded word. -/
theorem physical_at_later (B : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
    (ht : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
    (older : List Bool) (hr : pairFst older = pairFst (B.key c))
    (hfit : (family B.parameters B.plan B.data).birth older ≤
      (family B.parameters B.plan B.data).birth (B.key c)) (requested tau : ℕ) :
    (CoefficientMarkedRecordTraceProbePhysical.polynomial B.parameters B.plan B.data older requested tau).eval₂
      (Int.castRingHom ℝ) (CoefficientFinitePhysicalQuery.natural
        (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hw).val) =
    (IntegralMixedCutCoefficientPolynomialKey.polynomial (family B.parameters B.plan B.data)
      (B.parameters.cap (pairFst older)+1) older tau requested).eval₂ (Int.castRingHom ℝ)
      (fun i => IntegralFramedPhysicalSuffixTest.rawTuple B c w hw
        ((family B.parameters B.plan B.data).birth (B.key c)-(family B.parameters B.plan B.data).birth older+i.val)) := by
  unfold CoefficientMarkedRecordTraceProbePhysical.polynomial
  rw [MvPolynomial.eval₂_rename, MvPolynomial.eval₂_rename]
  apply congrArg (fun f => (IntegralMixedCutCoefficientPolynomialKey.polynomial (family B.parameters B.plan B.data)
    (B.parameters.cap (pairFst older)+1) older tau requested).eval₂ (Int.castRingHom ℝ) f)
  funext i
  have hprefix : prefixLength B.parameters older ≤ prefixLength B.parameters (B.key c) := by
    simpa only [family_birth] using hfit
  have hi : i.val < prefixLength B.parameters older := by
    simpa only [family_birth] using i.isLt
  have hc := CoefficientMarkedRecordTraceProbePhysical.scalar_suffix B.parameters T older (B.key c) hr hprefix i.val hi
  rw [← scalar_column B.parameters B.plan B.data T ht older i] at hc
  have hage : (family B.parameters B.plan B.data).birth (B.key c)-
      (family B.parameters B.plan B.data).birth older+i.val < (family B.parameters B.plan B.data).birth (B.key c) := by
    have := i.isLt
    omega
  let j : Fin ((family B.parameters B.plan B.data).birth (B.key c)) := ⟨_, hage⟩
  have hv := raw_column B T ht c w hw j
  have hs : IntegralMixedFramedPhysicalIndex.scalarColumn B.parameters T (pair (B.key c) (BinaryNatCode.encode j.val)) =
      ((IntegralFramedPhysicalSquare.sampler B.parameters B.plan B.data older).scalar i).val := by
    simpa only [j, family_birth] using hc
  rw [hs] at hv
  exact hv.symm

/-- The literal terminal coefficient test and the earlier-prefix physical
polynomial evaluate identically on ONE later decoded word. AUX is arbitrary. -/
theorem terminal_at_later (B : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
    (ht : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (key : List Bool → List Bool) (p c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
    (hkey : key p = B.key c)
    (hroot : pairFst (IntegralMixedVirtualTaskBits.saved B.parameters p) = pairFst (B.key c))
    (e k : ℕ) (hc : IntegralMixedFramedFullCutProbeBits.Active B.parameters p)
    (he : e ≤ 2^B.parameters.width (RankedHistoryTask.root p))
    (hk : k ≤ 2^B.parameters.width (RankedHistoryTask.root p))
    (hfit : IntegralFramedTerminalCutTest.oldArity B.parameters B.plan B.data p
      (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)) ≤
      IntegralFramedTerminalCutTest.count B.parameters B.plan B.data key p) :
    (IntegralFramedTerminalCutTest.polynomial B.parameters B.plan B.data key p
      (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k))).eval₂ (Int.castRingHom ℝ)
      (fun i => IntegralFramedPhysicalSuffixTest.rawTuple B c w hw
        (IntegralFramedTerminalCutTest.count B.parameters B.plan B.data key p -
          IntegralFramedTerminalCutTest.arity B.parameters B.plan B.data key p
            (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)) + i.val)) =
    (CoefficientMarkedRecordTraceProbePhysical.polynomial B.parameters B.plan B.data
      (IntegralMixedVirtualTaskBits.saved B.parameters p) k e).eval₂ (Int.castRingHom ℝ)
      (CoefficientFinitePhysicalQuery.natural
        (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hw).val) := by
  let d := pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)
  let old := IntegralMixedVirtualTaskBits.saved B.parameters p
  let delta := IntegralFramedTerminalCutTest.count B.parameters B.plan B.data key p -
    IntegralFramedTerminalCutTest.arity B.parameters B.plan B.data key p d
  have ho := IntegralFramedTerminalCutTest.oldArity_parent B.parameters B.plan B.data p d
  have hf : (family B.parameters B.plan B.data).birth old ≤ (family B.parameters B.plan B.data).birth (B.key c) := by
    rw [ho] at hfit
    simpa only [IntegralFramedTerminalCutTest.count, hkey] using hfit
  have hd : delta = (family B.parameters B.plan B.data).birth (B.key c) -
      (family B.parameters B.plan B.data).birth old := by
    dsimp only [delta]
    unfold IntegralFramedTerminalCutTest.arity
    rw [min_eq_left hfit, ho]
    simp only [IntegralFramedTerminalCutTest.count, hkey, old]
  have hh : IntegralMixedFramedChoiceProbeSourceBits.horizon B.parameters p = B.parameters.cap (pairFst old)+1 :=
    congrArg (fun root => B.parameters.cap root + 1)
      (IntegralMixedFullHistoryFamilyBits.saved_root B.parameters p).symm
  have hp := terminal_evaluation B.parameters B.plan B.data key p e k hc he hk hfit
    (fun j => IntegralFramedPhysicalSuffixTest.rawTuple B c w hw (delta+j))
  have hv := physical_at_later B T ht c w hw old hroot hf k e
  rw [hh, hd] at hp
  simpa only [← hd] using hp.trans hv.symm

end LeanCanny.Encoding.CoefficientMarkedRecordTraceProbeEvaluation
