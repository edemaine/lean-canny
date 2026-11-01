/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralIntegerRootBank
public import LeanCanny.Algebra.IntegralScalarGeneratorOrigin

/-! # Actual integer-companion origins for retained initial scalars

Each retained root has an actual creating prefix and original integer
polynomial, rather than an arbitrary relative polynomial. Its degree is
the original exact degree and its leading denominator is the original
integer leading coefficient. The chain records every later extension.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralIntegerRootBank
open LeanCanny.Encoding LeanCanny.Computation IntegralHistorySampler UniformIntegralPrefix
open IntegralScalarRootHistoryBounds
open scoped Classical

structure IntegerOrigin {S B m : ℕ} (P : Prefix S (2 ^ B) m) (bank : HeightBank P)
    (i : Fin m) (p : Polynomial ℤ) extends GeneratorOrigin P bank i where
  original : polynomial = p.map (Int.castRingHom oldPrefix.carrier)
  actual_degree : degree = p.natDegree

noncomputable def origin {S B : ℕ} {ι : Type} [Fintype ι] (F : Sampler S (2 ^ B) 0 ι)
    (m : ℕ) (p : Fin m → Polynomial ℤ) (hp : ∀ i, p i ≠ 0) (hm : m ≤ S + 1)
    (hcap : ∀ i, (p i).natDegree ≤ 2 ^ B) (i : Fin m) :
    IntegerOrigin (run F m p hp hm).sampler.scalarPrefix (run F m p hp hm).bank i (p i) := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    let x := run F m (fun i => p i.succ) (fun i => hp i.succ) (by omega : m ≤ S + 1)
    refine Fin.cases ?_ (fun j => ?_) i
    · refine {
        birth := m
        order := by simp only [Fin.val_zero, Nat.add_zero]
        oldPrefix := x.sampler.scalarPrefix
        birth_bound := by omega
        polynomial := (p 0).map (Int.castRingHom x.sampler.scalarPrefix.carrier)
        degree := (p 0).natDegree
        degree_bound := hcap 0
        leading := (p 0).leadingCoeff
        leading_eq := ?_
        leading_ne_zero := Polynomial.leadingCoeff_ne_zero.mpr (hp 0)
        chain := .refl _
        generator_eq := rfl
        denominator_eq := rfl
        original := rfl
        actual_degree := rfl }
      rw [Polynomial.coeff_map, Polynomial.coeff_natDegree]
      rfl
    · let o := ih (fun i => p i.succ) (fun i => hp i.succ) (by omega) (fun i => hcap i.succ) j
      refine {
        birth := o.birth
        order := by have H := o.order; simp only [Fin.val_succ]; omega
        oldPrefix := o.oldPrefix
        birth_bound := o.birth_bound
        polynomial := o.polynomial
        degree := o.degree
        degree_bound := o.degree_bound
        leading := o.leading
        leading_eq := o.leading_eq
        leading_ne_zero := o.leading_ne_zero
        chain := o.chain.step (by omega) ((p 0).map (Int.castRingHom x.sampler.scalarPrefix.carrier)) (p 0).natDegree
        generator_eq := ?_
        denominator_eq := o.denominator_eq
        original := o.original
        actual_degree := o.actual_degree }
      change AdjoinRoot.of _ (o.chain.embed (AdjoinRoot.root _)) =
        AdjoinRoot.of _ (x.sampler.scalarPrefix.basis.generator j)
      rw [o.generator_eq]

end LeanCanny.Algebra.IntegralIntegerRootBank
