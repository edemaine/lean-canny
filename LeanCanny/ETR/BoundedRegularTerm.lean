/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TermPowerSumFP
public import LeanCanny.ETR.NumericLiteralFP
public import LeanCanny.ETR.FinitePolynomialPadding

/-! # Polynomial-sized terms for the regular source with supplied scalars

The scalar inputs may be modular representatives. Spatial degrees and the
number of coordinates are unary controls; scalar magnitudes remain binary.
-/

@[expose] public section
namespace LeanCanny.ETR.BoundedRegularTerm
open MvPolynomial
open scoped BigOperators

def sphere (n r : ℕ) : Term := .add (TermPowerSum.term (n + 2) 2) (.const (-(r : ℤ)))
def energy (t : Term) (n r : ℕ) : Term := .add (.mul t t) (.mul (sphere n r) (sphere n r))
def lower (t : Term) (n r f b : ℕ) : Term := .add (.mul (.const (f : ℤ)) (energy t n r)) (.const (-(b : ℤ)))
def term (t : Term) (n N r f b e : ℕ) : Term :=
  .add (.mul (.const (e : ℤ)) (.add (lower t n r f b) (TermPowerSum.term (n + 4) N))) (.const (-1))

theorem arity (t : Term) (n N r f b e : ℕ) (ht : t.arity ≤ n) (hN : 0 < N) :
    (term t n N r f b e).arity = n + 4 := by
  simp only [term, lower, energy, sphere, Term.arity, TermPowerSum.arity _ 2 (by decide),
    TermPowerSum.arity _ N hN]
  omega

theorem finitePolynomial (t : Term) (n N r f b e : ℕ) :
    (term t n N r f b e).finitePolynomial (n + 4) =
      C (e : ℤ) * (C (f : ℤ) * ((t.finitePolynomial (n + 4)) ^ 2 +
        ((∑ i : Fin (n + 2), (X (i.castAdd 2) : MvPolynomial (Fin (n + 4)) ℤ) ^ 2) - C (r : ℤ)) ^ 2) -
        C (b : ℤ) + ∑ i : Fin (n + 4), X i ^ N) - 1 := by
  simp only [term, lower, energy, sphere, Term.finitePolynomial]
  have hn : n + 2 ≤ n + 4 := by omega
  rw [TermPowerSum.finitePolynomial (n + 2) 2 (n + 4) hn,
    TermPowerSum.finitePolynomial (n + 4) N (n + 4) le_rfl]
  have hc (i : Fin (n + 2)) : i.castLE hn = i.castAdd 2 := Fin.ext rfl
  have hd (i : Fin (n + 4)) : i.castLE le_rfl = i := Fin.ext rfl
  simp only [hc, hd, map_neg, C_1, ← pow_two, sub_eq_add_neg]

private theorem add_FP {t u : List Bool → Term}
    (ht : (fun c => (t c).toData.toBits) ∈ FP) (hu : (fun c => (u c).toData.toBits) ∈ FP) :
    (fun c => (Term.add (t c) (u c)).toData.toBits) ∈ FP := by
  simpa only [Term.add_toBits] using Codec.taggedTwo_mem_FP 2 ht hu

private theorem mul_FP {t u : List Bool → Term}
    (ht : (fun c => (t c).toData.toBits) ∈ FP) (hu : (fun c => (u c).toData.toBits) ∈ FP) :
    (fun c => (Term.mul (t c) (u c)).toData.toBits) ∈ FP := by
  simpa only [Term.mul_toBits] using Codec.taggedTwo_mem_FP 3 ht hu

theorem encode_mem_FP {t : List Bool → Term} {n N r f b e : List Bool → ℕ}
    (ht : (fun c => (t c).toData.toBits) ∈ FP) (hn : UnaryFn n) (hN : UnaryFn N)
    (hr : BinaryFn r) (hf : BinaryFn f) (hb : BinaryFn b) (he : BinaryFn e) :
    (fun c => (term (t c) (n c) (N c) (r c) (f c) (b c) (e c)).toData.toBits) ∈ FP := by
  have hs : (fun c => (sphere (n c) (r c)).toData.toBits) ∈ FP :=
    add_FP (TermPowerSum.encode_mem_FP (hn.add (UnaryFn.const 2)) (UnaryFn.const 2)) (Term.negNat_toBits_mem_FP hr)
  have henergy : (fun c => (energy (t c) (n c) (r c)).toData.toBits) ∈ FP :=
    add_FP (mul_FP ht ht) (mul_FP hs hs)
  have hlower : (fun c => (lower (t c) (n c) (r c) (f c) (b c)).toData.toBits) ∈ FP :=
    add_FP (mul_FP (Term.nat_toBits_mem_FP hf) henergy) (Term.negNat_toBits_mem_FP hb)
  exact add_FP (mul_FP (Term.nat_toBits_mem_FP he)
    (add_FP hlower (TermPowerSum.encode_mem_FP (hn.add (UnaryFn.const 4)) hN))) (constFn_mem_FP _)

end LeanCanny.ETR.BoundedRegularTerm
