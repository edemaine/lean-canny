/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.BinaryModularProduct
public import LeanCanny.CountingHierarchy.ModularArithmetic
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Aggregation

/-! # Fixed-level evaluation of compressed sign-label scores -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

noncomputable def binaryClearedNumerator (p m : ℕ) (den num : ℕ → ℕ) (i : ℕ) : ℕ :=
  (num i * binaryModularProduct p m (fun j => if j = i then 1 else den j)) % p

theorem binaryClearedNumerator_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p m : α → ℕ} {den num : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hm : ComputableInPolyTime m enc encNat)
    (hden : den ∈ CountingFunction a (encPair enc encNat) encNat)
    (hnum : num ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun q : α × ℕ => binaryClearedNumerator (p q.1) (m q.1)
      (fun j => den (q.1, j)) (fun j => num (q.1, j)) q.2) ∈
        CountingFunction (a + 3) (encPair enc encNat) encNat := by
  have hp' := hp.comp (ComputableInPolyTime.fst enc encNat)
  have hm' := hm.comp (ComputableInPolyTime.fst enc encNat)
  have hden' := CountingFunction.preprocess (input := encPair (encPair enc encNat) encNat)
    hden (g := fun q : (α × ℕ) × ℕ => (q.1.1, q.2)) (by fun_prop)
  have ht : ComputableInPolyTime (fun q : (α × ℕ) × ℕ => decide (q.2 = q.1.2))
      (encPair (encPair enc encNat) encNat) encBool := by fun_prop
  have hf := CountingFunction.ite (CountingFunction.of_polyTime ht)
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 1)) hden'
  simp only [decide_eq_true_eq] at hf
  have hprod := binaryModularProduct_mem (Decoder.pair E Decoder.nat) hp' hm' hf
  simpa only [binaryClearedNumerator, Function.comp_apply] using CountingFunction.nat_mod
    (CountingFunction.nat_mul (CountingFunction.mono (by omega : a ≤ a + 3) hnum) hprod)
    (CountingFunction.of_polyTime hp')

noncomputable def modularFingerprintLabel (p m : ℕ) (den num weight : ℕ → ℕ) (target : ℕ) : ℕ :=
  let E := binaryModularProduct p (m + 1) den
  let T := binaryClearedNumerator p (m + 1) den num
  let S := (∑ i ∈ Finset.range m, weight i * T (i + 1)) % p
  modularSub p (modularSub p (powMod p E 2) (4 * powMod p (modularSub p S (target * E)) 2))
    (4 * powMod p (modularSub p (T 0) E) 2)

/-- A binary number of derivatives costs four additional levels, from a
finite-field product and one bounded sum. Indices remain uniformly addressed. -/
theorem modularFingerprintLabel_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p m target : α → ℕ} {den num weight : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hm : ComputableInPolyTime m enc encNat)
    (hden : den ∈ CountingFunction a (encPair enc encNat) encNat)
    (hnum : num ∈ CountingFunction a (encPair enc encNat) encNat)
    (hw : weight ∈ CountingFunction (a + 3) (encPair enc encNat) encNat)
    (htarget : target ∈ CountingFunction (a + 3) enc encNat) :
    (fun w => modularFingerprintLabel (p w) (m w) (fun j => den (w, j))
      (fun j => num (w, j)) (fun j => weight (w, j)) (target w)) ∈
        CountingFunction (a + 4) enc encNat := by
  have hm' := ComputableInPolyTime.binary_add' hm (.const 1)
  have hE := binaryModularProduct_mem E hp hm' hden
  have hT := binaryClearedNumerator_mem E hp hm' hden hnum
  have hnext : ComputableInPolyTime (fun q : α × ℕ => (q.1, q.2 + 1))
      (encPair enc encNat) (encPair enc encNat) :=
    (ComputableInPolyTime.fst _ _).prod
      (ComputableInPolyTime.binary_add' (ComputableInPolyTime.snd _ _) (.const 1))
  have hS := CountingFunction.sum_range E
    (CountingFunction.nat_mul hw (CountingFunction.preprocess hT hnext)) hm
  have hSmod := CountingFunction.nat_mod hS (CountingFunction.of_polyTime hp)
  have hTzero := CountingFunction.preprocess hT
    ((ComputableInPolyTime.id').prod (ComputableInPolyTime.const 0))
  have hE4 := CountingFunction.mono (by omega : a + 3 ≤ a + 4) hE
  have ht4 := CountingFunction.mono (by omega : a + 3 ≤ a + 4) htarget
  have hz4 := CountingFunction.mono (by omega : a + 3 ≤ a + 4) hTzero
  have hdiff := modularSub_mem (CountingFunction.of_polyTime hp) hSmod (CountingFunction.nat_mul ht4 hE4)
  have hzero := modularSub_mem (CountingFunction.of_polyTime hp) hz4 hE4
  have hpow (f : α → ℕ) (hf : f ∈ CountingFunction (a + 4) enc encNat) :=
    CountingFunction.powMod (CountingFunction.of_polyTime hp) hf
      (CountingFunction.of_polyTime (ComputableInPolyTime.const 2))
  have hfour (f : α → ℕ) (hf : f ∈ CountingFunction (a + 4) enc encNat) :=
    CountingFunction.nat_mul (CountingFunction.of_polyTime (ComputableInPolyTime.const 4)) hf
  have hleft := modularSub_mem (CountingFunction.of_polyTime hp) (hpow _ hE4) (hfour _ (hpow _ hdiff))
  simpa only [modularFingerprintLabel, Function.comp_apply] using
    modularSub_mem (CountingFunction.of_polyTime hp) hleft (hfour _ (hpow _ hzero))

end LeanCanny.CountingHierarchy
