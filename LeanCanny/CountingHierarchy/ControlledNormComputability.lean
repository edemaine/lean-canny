/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledNormAccess

/-! # The final integer norm has a constructed sign algorithm in F_(a+24) -/

public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

variable {α : Type} {n : α → ℕ} {P : (w : α) → MvPolynomial (Fin (n w)) ℤ}
  {enc : α ↪ List Bool} {a : ℕ}

theorem normCutoff_polyTime (C : Controlled P enc a) {d : α → ℕ}
    (hd : ComputableInPolyTime d enc encNat) :
    ComputableInPolyTime (C.normCutoff d) enc encNat :=
  ComputableInPolyTime.binary_max' C.cutoff_computable
    (sourceNormPrimeCutoff_polyTime C.arity_computable hd C.mass_computable)

theorem normAccess_mem (C : Controlled P enc a) (E : Decoder enc) {d : α → ℕ}
    (hdpos : ∀ w, 1 ≤ d w) (hdeg : ∀ w, (P w).totalDegree ≤ d w + 1)
    {data : α → List (ℕ × ℕ)} {e : α → ℕ}
    (hd : ComputableInPolyTime d enc encNat)
    (hdata : ComputableInPolyTime data enc encRootLabelCode)
    (he : ComputableInPolyTime e enc encNat) :
    (C.normAccess d hdpos hdeg data e).InCountingFunction (a + 21) enc := by
  refine ⟨criticalNormMassExponent_polyTime C.arity_computable hd C.mass_computable, ?_⟩
  have hf := ComputableInPolyTime.fst enc encNat
  have hp := ComputableInPolyTime.snd enc encNat
  have hv := CountingFunction.preprocess
    (input := encPair (encPair enc encNat) (encList encNat)) C.evaluate_mem
    (g := fun q : (α × ℕ) × List ℕ => (q.1.1, q.1.2, q.2)) (by fun_prop)
  have hres := sourceNormDeterminantValue_mem (Decoder.pair E Decoder.nat)
    hp (C.arity_computable.comp hf) (hd.comp hf) (C.mass_computable.comp hf)
    (he.comp hf) (hdata.comp hf) hv
  simpa only [normAccess, Function.comp_apply] using hres

/-- This sign theorem has only source polynomial access and short code data
as hypotheses. It assumes neither a determinant oracle nor a trace oracle. -/
theorem normSign_mem (C : Controlled P enc a) (E : Decoder enc) {d : α → ℕ}
    (hdpos : ∀ w, 1 ≤ d w) (hdeg : ∀ w, (P w).totalDegree ≤ d w + 1)
    {data : α → List (ℕ × ℕ)} {e : α → ℕ}
    (hd : ComputableInPolyTime d enc encNat)
    (hdata : ComputableInPolyTime data enc encRootLabelCode)
    (he : ComputableInPolyTime e enc encNat) :
    (fun w => (C.normInteger d hdeg data e w).sign) ∈ CountingFunction (a + 24) enc encIntBin := by
  have hsign := IntegerResidueAccess.sign_mem_CountingFunction E
    (C.normAccess d hdpos hdeg data e) (C.normAccess_mem E hdpos hdeg hd hdata he)
    (C.normCutoff_polyTime hd) (fun w p hp =>
      ⟨Cslib.PrimeWindowSign.prime _ _ ⟨p, hp⟩,
        (Nat.mem_primesLE_sdiff_primesLE_iff.mp hp).2.1⟩)
  have hmax : max (a + 21) 5 = a + 21 := by omega
  simpa only [hmax, Nat.add_assoc] using hsign

end LeanCanny.CountingHierarchy.Controlled
