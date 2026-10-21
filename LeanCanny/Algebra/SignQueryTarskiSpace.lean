/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignQuerySource

/-! # Tarski evaluation of streamed ternary product queries

Uniform positive-modulus coefficient access to the root and the original
polynomial family suffices. The product coefficient reader is constructed
internally, and all its space-bounded calls are included in the Tarski certificate.
-/

@[expose] public section

namespace LeanCanny.Algebra.SignQueryBits
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower
open scoped BigOperators

def origin (q : List Bool) : List Bool := pairFst (pairFst q)
def index (q : List Bool) : List Bool := pairSnd (pairFst q)
def modulus (q : List Bool) : ℕ := Nat.fromBitsLE (pairSnd q) + 1
def sourceQuery (p : List Bool) : List Bool :=
  pair (pair (origin (pairFst p)) (pairSnd p)) (BinaryNat.normalize (pairSnd (pairFst p)))
def exponentQuery (p : List Bool) : List Bool := pair (origin (pairFst p)) (pairSnd p)

theorem origin_mem_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem index_mem_FP : index ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
theorem sourceQuery_mem_FP : sourceQuery ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP origin_mem_FP
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  have h := mem_FP_pair (mem_FP_pair hc pairSnd_mem_FP) hm
  refine mem_FP_of_eq (g := sourceQuery) h ?_
  intro p
  simp only [sourceQuery, Function.comp_apply]
theorem exponentQuery_mem_FP : exponentQuery ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP origin_mem_FP
  have h := mem_FP_pair hc pairSnd_mem_FP
  refine mem_FP_of_eq (g := exponentQuery) h ?_
  intro p
  simp only [exponentQuery, Function.comp_apply]

theorem sourceQuery_packet (q : List Bool) (i k : ℕ) :
    sourceQuery (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) =
      pair (pair (origin q) (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))
        (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q))) := by
  simp only [sourceQuery, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]

noncomputable def Family.residue (F : Family) (q : List Bool) : List Bool :=
  IntegerTarskiSeedBits.integerResidue ((F.product (origin q)).coeff (Nat.fromBitsLE (index q))) (modulus q)

theorem residueEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (he : a.exponent ∈ FP) (P : SpaceFunction a.polynomialCoefficient) : SpaceFunction F.residue := by
  let e := fun q i => F.exponent (origin q) i
  let Q := fun q i => (F.polynomial (origin q) i).map (Int.castRingHom (ZMod (modulus q)))
  have hc := mem_FP_comp origin_mem_FP hF.count
  have hx := mem_FP_comp exponentQuery_mem_FP he
  let R := P.precompose sourceQuery sourceQuery_mem_FP
  let E := RootSignQueries.queryProductEvaluator R (F.count ∘ origin) (a.exponent ∘ exponentQuery)
    pairSnd index hc hx pairSnd_mem_FP index_mem_FP e Q
    (by
      intro q i hi
      simpa only [Function.comp_apply, exponentQuery, pairFst_pair, pairSnd_pair] using
        a.exponent_eq (origin q) i hi)
    (by
      intro q i hi k
      simp only [Function.comp_apply, sourceQuery_packet]
      change _ = residueBits (((F.polynomial (origin q) i).map
        (Int.castRingHom (ZMod (modulus q)))).coeff k)
      rw [Polynomial.coeff_map]
      change _ = IntegerTarskiSeedBits.integerResidue ((F.polynomial (origin q) i).coeff k) (modulus q)
      have h := a.polynomial_eq (origin q) i hi k (modulus q) (by dsimp [modulus]; omega)
      simpa only [modulus, Nat.add_sub_cancel] using h)
  refine E.congr (funext fun q => ?_)
  change residueBits ((∏ i ∈ Finset.range (Nat.fromBitsLE (F.count (origin q))),
    (F.polynomial (origin q) i).map (Int.castRingHom (ZMod (modulus q))) ^ (F.exponent (origin q) i).val).coeff
      (Nat.fromBitsLE (index q))) = _
  have hm : (∏ i ∈ Finset.range (Nat.fromBitsLE (F.count (origin q))),
      (F.polynomial (origin q) i).map (Int.castRingHom (ZMod (modulus q))) ^ (F.exponent (origin q) i).val) =
      (F.product (origin q)).map (Int.castRingHom (ZMod (modulus q))) := by
    simp only [Family.product, Polynomial.map_prod, Polynomial.map_pow]
  rw [hm, coeff_map]
  rfl

noncomputable def tarskiAccess {F : Family} (a : Access F) : IntegerTarskiSeedBits.Access F.tarski where
  headCoefficient := a.rootCoefficient
  queryCoefficient := F.residue
  head_eq := a.root_eq
  query_eq := by
    intro c k m hm
    simp only [Family.residue, origin, index, modulus, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel (by omega : 1 ≤ m), Family.tarski]

noncomputable def Family.value (F : Family) (c : List Bool) : ℤ := RootSignQueries.tarskiQuery
  ((F.root c).map (algebraMap ℤ ℝ)) ((F.product c).map (algebraMap ℤ ℝ))

theorem evaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (he : a.exponent ∈ FP) (H : SpaceFunction a.rootCoefficient)
    (P : SpaceFunction a.polynomialCoefficient) :
    SpaceFunction (fun c => SignStatisticBits.integerCode (F.value c)) := by
  let E := TarskiQueryBits.evaluator (tarskiAccess a) (tarski_controls F hF) H (residueEvaluator a hF he P)
  refine E.congr (funext fun c => ?_)
  rfl

def Family.zeroLanguage (F : Family) : Language := {c | F.value c = 0}
def Family.positiveLanguage (F : Family) : Language := {c | 0 < F.value c}
def Family.negativeLanguage (F : Family) : Language := {c | F.value c < 0}

theorem zeroLanguage_mem_PSPACE {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (he : a.exponent ∈ FP) (H : SpaceFunction a.rootCoefficient) (P : SpaceFunction a.polynomialCoefficient) :
    F.zeroLanguage ∈ PSPACE := by
  change TarskiQueryBits.zeroLanguage F.tarski ∈ PSPACE
  exact TarskiQueryBits.zeroLanguage_mem_PSPACE (tarskiAccess a) (tarski_controls F hF) H
    (residueEvaluator a hF he P)

theorem positiveLanguage_mem_PSPACE {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (he : a.exponent ∈ FP) (H : SpaceFunction a.rootCoefficient) (P : SpaceFunction a.polynomialCoefficient) :
    F.positiveLanguage ∈ PSPACE := by
  change TarskiQueryBits.positiveLanguage F.tarski ∈ PSPACE
  exact TarskiQueryBits.positiveLanguage_mem_PSPACE (tarskiAccess a) (tarski_controls F hF) H
    (residueEvaluator a hF he P)

theorem negativeLanguage_mem_PSPACE {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (he : a.exponent ∈ FP) (H : SpaceFunction a.rootCoefficient) (P : SpaceFunction a.polynomialCoefficient) :
    F.negativeLanguage ∈ PSPACE := by
  change TarskiQueryBits.negativeLanguage F.tarski ∈ PSPACE
  exact TarskiQueryBits.negativeLanguage_mem_PSPACE (tarskiAccess a) (tarski_controls F hF) H
    (residueEvaluator a hF he P)

end LeanCanny.Algebra.SignQueryBits
