/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ImplicitSourceGramGridCoordinateSource
public import LeanCanny.Algebra.IntegerPolynomialIteratedDerivativeSource
/-! # One external grid polynomial for both sides of Replay

The datum holds the literal external grid context, coordinate and derivative.
The target sampler context cannot select a different polynomial. All orders
are streamed; no explicit integer polynomial is serialized.
-/
@[expose] public section
namespace LeanCanny.Encoding.ImplicitSourceGramGridReplayDatum
open LeanCanny.Algebra LeanCanny.Computation
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ImplicitSourceGramGrid.polynomial
  ImplicitSourceGramGridCoordinateSource.source IntegerPolynomialIteratedDerivativeBits.source

def packet (c : List Bool) (i k : ℕ) := pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))
def gridContext (d : List Bool) := pairFst d
def index (d : List Bool) := Nat.fromBitsLE (pairFst (pairSnd d))
def derivative (d : List Bool) := pairSnd (pairSnd d)
def baseKey (d : List Bool) := pair (gridContext d) (pairFst (pairSnd d))
def query (z : List Bool) := pair (baseKey (pairSnd z)) (derivative (pairSnd z))

theorem baseKey_FP : baseKey ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)

theorem query_FP : query ∈ FP :=
  mem_FP_pair (mem_FP_comp pairSnd_mem_FP baseKey_FP)
    (mem_FP_comp (f := pairSnd) (g := derivative) pairSnd_mem_FP
      (mem_FP_comp (f := pairSnd) (g := pairSnd) pairSnd_mem_FP pairSnd_mem_FP))

noncomputable def source (S : Source) (hp : ∀ u, 0 < S.arity u) : IntegerPolynomialRootQueriesBits.Source :=
  IntegerPolynomialIteratedDerivativeBits.comp
    (IntegerPolynomialIteratedDerivativeBits.source (ImplicitSourceGramGridCoordinateSource.source S hp)) query

theorem access (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) : IntegerPolynomialRootQueriesBits.Access (source S hp) :=
  IntegerPolynomialIteratedDerivativeBits.compAccess
    (IntegerPolynomialIteratedDerivativeBits.access (ImplicitSourceGramGridCoordinateSource.access S A hp)) query_FP

theorem query_packet (target c : List Bool) (i k : ℕ) :
    query (pair target (packet c i k)) =
      pair (pair c (BinaryNatCode.encode i)) (BinaryNatCode.encode k) := by
  simp only [query, baseKey, gridContext, derivative, packet, pairFst_pair, pairSnd_pair]

theorem polynomial_packet (S : Source) (hp : ∀ u, 0 < S.arity u) (target c : List Bool)
    (i : Fin (ImplicitSourceGramGrid.count S c)) (k : ℕ) :
    (source S hp).polynomial (pair target (packet c i.val k)) =
      Polynomial.derivative^[k] (ImplicitSourceGramGrid.polynomial S c i) := by
  unfold source IntegerPolynomialIteratedDerivativeBits.comp
  change (IntegerPolynomialIteratedDerivativeBits.source
    (ImplicitSourceGramGridCoordinateSource.source S hp)).polynomial (query (pair target (packet c i.val k))) = _
  rw [query_packet, IntegerPolynomialIteratedDerivativeBits.packet,
    ImplicitSourceGramGridCoordinateSource.polynomial_packet]

theorem target_independent (S : Source) (hp : ∀ u, 0 < S.arity u)
    (left right datum : List Bool) :
    (source S hp).polynomial (pair left datum) = (source S hp).polynomial (pair right datum) := by
  unfold source IntegerPolynomialIteratedDerivativeBits.comp
  simp only [Function.comp_apply, query, pairSnd_pair]

end LeanCanny.Encoding.ImplicitSourceGramGridReplayDatum
