/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteAnnihilatorHeight
public import LeanCanny.Computation.TidyBoundedFold

/-! # Uniform native degree computation for finite annihilator parameters

The exact degree is the product of the square-free leaf degrees. One native
fold computes it for an input-dependent family size. The leaf computation may
take arbitrary time in polynomial space; no execution clock is supplied.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteAnnihilatorBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open Turing.MultiTapeTM
open scoped BigOperators
open SeparableBits (Family Readers)

noncomputable def leafDegree (F : Family) (c : List Bool) (i : ℕ) : ℕ :=
  (ScaledSquarefree.polynomial (F.polynomial (LeanCanny.pair c (BinaryNatCode.encode i)))).natDegree

noncomputable def degreeProduct (F : Family) (c : List Bool) (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, leafDegree F c i

noncomputable def parameter (F : Family) (count : List Bool → ℕ)
    (hne : ∀ c, F.polynomial c ≠ 0) (c : List Bool) : ℤ[X] :=
  (FiniteAnnihilatorTree.parameter (fun i => F.polynomial (LeanCanny.pair c (BinaryNatCode.encode i)))
    (count c) (fun i _ => hne (LeanCanny.pair c (BinaryNatCode.encode i)))).polynomial

theorem parameter_degree (F : Family) (count : List Bool → ℕ) (hne : ∀ c, F.polynomial c ≠ 0) (c : List Bool) :
    (parameter F count hne c).natDegree = degreeProduct F c (count c) :=
  FiniteAnnihilatorTree.parameter_degree _ _ _

theorem degreeProduct_bound (F : Family) (count D : List Bool → ℕ) (hne : ∀ c, F.polynomial c ≠ 0)
    (hD : ∀ c i, i < count c → (F.polynomial (LeanCanny.pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (c : List Bool) (k : ℕ) (hk : k ≤ count c) : degreeProduct F c k ≤ (D c + 1) ^ k := by
  induction k with
  | zero => simp only [degreeProduct, Finset.range_zero, Finset.prod_empty, pow_zero, le_refl]
  | succ k ih =>
    have hl : leafDegree F c k ≤ D c + 1 :=
      ((ScaledSquarefree.polynomial_natDegree_le _ (hne _)).trans (hD c k (by omega))).trans (Nat.le_succ _)
    rw [degreeProduct, Finset.prod_range_succ]
    exact (Nat.mul_le_mul (ih (by omega)) hl).trans_eq (pow_succ _ _).symm

theorem degreeEvaluator (F : Family) (A : Readers F) (hne : ∀ c, F.polynomial c ≠ 0)
    (count D : List Bool → ℕ) (hn : UnaryFn count) (hD : BinaryFn D)
    (hdegree : ∀ c i, i < count c → (F.polynomial (LeanCanny.pair c (BinaryNatCode.encode i))).natDegree ≤ D c) :
    SpaceFunction (fun c => BinaryNatCode.encode (parameter F count hne c).natDegree) := by
  let child (p : List Bool × ℕ × ℕ) : ℕ := p.2.2 * leafDegree F p.1 p.2.1
  have hc := ComputableTidilyInPolyTime.fst encBits (encPair encNat encNat)
  have hr := ComputableTidilyInPolyTime.snd encBits (encPair encNat encNat)
  have hquery := pair_computable hc (natBits_computable.comp hr.fst')
  have hd0 := (ComputableTidilyInPolySpace.of_polyTime fromBitsLE_computable).comp
    (SeparableBits.scaledSquarefreeDegreeEvaluator F A hne).computable
  have hd : ComputableTidilyInPolySpace
      (fun c => (ScaledSquarefree.polynomial (F.polynomial c)).natDegree) encBits encNat :=
    hd0.congr fun c => Nat.fromBitsLE_bits _
  have hacc := ComputableTidilyInPolySpace.of_polyTime hr.snd'
  have hleaf := hd.comp (ComputableTidilyInPolySpace.of_polyTime hquery)
  have hchild : ComputableTidilyInPolySpace child (TidyBoundedFold.encPacket encBits encNat) encNat :=
    ((ComputableTidilyInPolySpace.of_polyTime ComputableTidilyInPolyTime.binary_mul).comp (hacc.prod hleaf)).congr (fun _ => rfl)
  have hfold (c : List Bool) (k : ℕ) : TidyBoundedFold.fold child (fun _ => 1) c k = degreeProduct F c k := by
    induction k with
    | zero => simp only [TidyBoundedFold.fold, degreeProduct, Finset.range_zero, Finset.prod_empty]
    | succ k ih => simp only [TidyBoundedFold.fold, child, ih, degreeProduct, Finset.prod_range_succ]
  have hbound : BinaryFn (fun c => (D c + 1) ^ count c) := (hD.add (BinaryFn.const 1)).powUnary hn
  have hcount := ComputableTidilyInPolyTime.unary_to_binary.comp hn
  have hout := TidyBoundedFold.evaluator hchild hcount
    (ComputableTidilyInPolySpace.of_polyTime (ComputableTidilyInPolyTime.const 1)) hbound.polyBounded_length
    (fun c k hk => by
      rw [hfold]
      exact ComputableTidilyInO.length_encNat_mono ((degreeProduct_bound F count D hne hdegree c k hk).trans
        (Nat.pow_le_pow_right (by omega) hk)))
  have hparam : ComputableTidilyInPolySpace (fun c => (parameter F count hne c).natDegree) encBits encNat :=
    hout.congr fun c => (hfold c _).trans (parameter_degree F count hne c).symm
  exact ⟨((ComputableTidilyInPolySpace.of_polyTime natBits_computable).comp hparam).congr fun _ => rfl⟩

end LeanCanny.Algebra.FiniteAnnihilatorBits
