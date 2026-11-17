/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FingerprintModularCorrectness
public import LeanCanny.CountingHierarchy.FingerprintRootSelection
public import LeanCanny.CountingHierarchy.SignTestEvaluation

/-! # Uniform evaluation of fingerprint labels from implicit sign tests -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

noncomputable def fingerprintLabelResidue (p B s m mu gamma target : ℕ) (value : ℕ → ℕ) : ℕ :=
  modularFingerprintLabel p m (fun i => signDenominatorResidue p B s (value i))
    (fun i => signNumeratorResidue p B s (value i)) (fun i => powMod mu gamma i) target

/-- A binary number of uniformly accessible sign tests gives a label evaluator
at seven additional levels. The three fingerprint integers are short data. -/
theorem fingerprintLabelResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p B s m mu gamma target : α → ℕ} {value : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hB : ComputableInPolyTime B enc encNat)
    (hs : ComputableInPolyTime s enc encNat) (hm : ComputableInPolyTime m enc encNat)
    (hmu : ComputableInPolyTime mu enc encNat) (hgamma : ComputableInPolyTime gamma enc encNat)
    (htarget : ComputableInPolyTime target enc encNat)
    (hv : value ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => fingerprintLabelResidue (p w) (B w) (s w) (m w) (mu w) (gamma w) (target w)
      (fun i => value (w, i))) ∈ CountingFunction (a + 7) enc encNat := by
  have hf := ComputableInPolyTime.fst enc encNat
  have htests := signTestResidues_mem (Decoder.pair E Decoder.nat) (hp.comp hf) (hB.comp hf) (hs.comp hf) hv
  have hw : ComputableInPolyTime (fun q : α × ℕ => powMod (mu q.1) (gamma q.1) q.2)
      (encPair enc encNat) encNat :=
    computableInPolyTime_powMod (hmu.comp hf) (hgamma.comp hf) (ComputableInPolyTime.snd enc encNat)
  have h := modularFingerprintLabel_mem (a := a + 3) E hp hm htests.1 htests.2
    (CountingFunction.of_polyTime hw) (CountingFunction.of_polyTime htarget)
  simpa only [fingerprintLabelResidue, Nat.add_assoc, Function.comp_apply] using h

/-- The evaluator computes the actual fingerprint label at every prime, even
if the fingerprint modulus is composite or fails to separate roots. -/
theorem fingerprintLabelResidue_cast {p m : ℕ} [Fact p.Prime] (B s mu gamma : ℕ)
    (hmu : mu ≠ 0) (g : Fin (m + 1) → Polynomial ℤ) (target : ℤ) (targetValue : ℕ)
    (x : ZMod p) (value : ℕ → ℕ)
    (hv : ∀ i : Fin (m + 1), (value i.val : ZMod p) = (g i).eval₂ (Int.castRingHom (ZMod p)) x)
    (ht : (targetValue : ZMod p) = (target : ZMod p)) :
    (fingerprintLabelResidue p B s m mu gamma targetValue value : ZMod p) =
      (fingerprintLabelPolynomial B s g (fun i => fingerprintWeight mu gamma i.val) target).eval₂
        (Int.castRingHom (ZMod p)) x := by
  exact modularFingerprintLabel_cast B s g _ target x _ _ _ targetValue
    (fun i => (signTestResidues_cast B s (value i.val) (g i) x (hv i)).1)
    (fun i => (signTestResidues_cast B s (value i.val) (g i) x (hv i)).2)
    (fun i => by rw [powMod_of_ne_zero hmu]; rfl) ht

end LeanCanny.CountingHierarchy
