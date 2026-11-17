/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RootLabelModularCorrectness
public import LeanCanny.CountingHierarchy.SignTestEvaluation

/-! # Total native evaluators for integer root-label polynomials -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- A zero input modulus is replaced by one, ensuring bounded loop storage
on every input. At prime moduli this is the actual cleared integer score. -/
@[expose] noncomputable def rootLabelResidue (p B s m : ℕ)
    (value target : ℕ → ℕ) : ℕ :=
  let q := max 1 p
  modularRootLabel q m (fun i => signDenominatorResidue q B s (value i))
    (fun i => signNumeratorResidue q B s (value i)) target

/-- Polynomially many tests add no further counting levels beyond the
three needed for the binary-width dyadic product. -/
theorem rootLabelResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p B s m : α → ℕ} {value target : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hB : ComputableInPolyTime B enc encNat)
    (hs : ComputableInPolyTime s enc encNat)
    (hm : ComputableInPolyTime m enc encUnary)
    (hv : value ∈ CountingFunction a (encPair enc encNat) encNat)
    (ht : target ∈ CountingFunction (a + 3) (encPair enc encNat) encNat) :
    (fun w => rootLabelResidue (p w) (B w) (s w) (m w)
      (fun i => value (w, i)) (fun i => target (w, i))) ∈
        CountingFunction (a + 3) enc encNat := by
  have hq := ComputableInPolyTime.binary_max' (ComputableInPolyTime.const 1) hp
  have hq' := hq.comp (ComputableInPolyTime.fst enc encNat)
  have hB' := hB.comp (ComputableInPolyTime.fst enc encNat)
  have hs' := hs.comp (ComputableInPolyTime.fst enc encNat)
  have htests := signTestResidues_mem (Decoder.pair E Decoder.nat) hq' hB' hs' hv
  simpa only [rootLabelResidue, Function.comp_apply] using
    modularRootLabel_mem hq hm (fun w => lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _))
      htests.1 htests.2 ht

/-- The uniform evaluator realizes the label polynomial at every prime.
Its arguments are test values and target residues, never expanded labels. -/
theorem rootLabelResidue_cast {p m : ℕ} [Fact p.Prime] (B s : ℕ)
    (g : Fin m → Polynomial ℤ) (t : Fin m → SignType) (x : ZMod p)
    (value target : ℕ → ℕ)
    (hv : ∀ i : Fin m, (value i.val : ZMod p) =
      (g i).eval₂ (Int.castRingHom (ZMod p)) x)
    (ht : ∀ i : Fin m, (target i.val : ZMod p) = ((t i : ℤ) : ZMod p)) :
    (rootLabelResidue p B s m value target : ZMod p) =
      (rootLabelPolynomial B s g t).eval₂ (Int.castRingHom (ZMod p)) x := by
  rw [rootLabelResidue, max_eq_right (Fact.out : p.Prime).one_le]
  exact modularRootLabel_cast B s g t x _ _ target
    (fun i => (signTestResidues_cast B s (value i.val) (g i) x (hv i)).1)
    (fun i => (signTestResidues_cast B s (value i.val) (g i) x (hv i)).2) ht

end LeanCanny.CountingHierarchy
