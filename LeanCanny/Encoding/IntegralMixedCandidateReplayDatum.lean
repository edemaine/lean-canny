/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateCoordinateRoot
public import LeanCanny.Algebra.IntegerPolynomialIteratedDerivativeSource
/-! # Shared derivative polynomials selected entirely by test datum

Both complete samplers stay fixed. The datum holds the literal old candidate,
an original coordinate and a derivative index. Its polynomial ignores the
sampler context, so two different samplers test exactly the same derivative.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCandidateReplayDatum
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def packet (p : List Bool) (i k : ℕ) := pair p (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))
def candidate (d : List Bool) := pairFst d
def index (d : List Bool) := Nat.fromBitsLE (pairFst (pairSnd d))
def derivative (d : List Bool) := pairSnd (pairSnd d)
def retained (n : List Bool→ℕ) (d : List Bool) := n (pairFst (candidate d))-index d

def baseContext (n : List Bool→ℕ) (d : List Bool) := pair (candidate d) (BinaryNatCode.encode (retained n d))
def query (n : List Bool→ℕ) (z : List Bool) := pair (baseContext n (pairSnd z)) (derivative (pairSnd z))

theorem retained_binary {n : List Bool→ℕ} (hn : UnaryFn n) : BinaryFn (retained n) := by
  have HN : BinaryFn (fun d=>n (pairFst (pairFst d))) := (BinaryFn.ofUnary hn).comp
    (mem_FP_comp (f:=pairFst) (g:=pairFst) pairFst_mem_FP pairFst_mem_FP)
  have HI : BinaryFn index := BinaryFn.fromBits
    (mem_FP_comp (f:=pairSnd) (g:=pairFst) pairSnd_mem_FP pairFst_mem_FP)
  exact HN.sub HI

theorem baseContext_FP {n : List Bool→ℕ} (hn : UnaryFn n) : baseContext n∈FP :=
  mem_FP_pair pairFst_mem_FP (retained_binary hn).bits_mem_FP

theorem query_FP {n : List Bool→ℕ} (hn : UnaryFn n) : query n∈FP := by
  have HD : derivative∈FP:=mem_FP_comp (f:=pairSnd) (g:=pairSnd) pairSnd_mem_FP pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_comp (f:=pairSnd) (g:=baseContext n) pairSnd_mem_FP (baseContext_FP hn))
    (mem_FP_comp (f:=pairSnd) (g:=derivative) pairSnd_mem_FP HD)

noncomputable def source {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :=
  IntegerPolynomialIteratedDerivativeBits.comp
    (IntegerPolynomialIteratedDerivativeBits.source (IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha)) (query n)

theorem access {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    IntegerPolynomialRootQueriesBits.Access (source hn ht ha) :=
  IntegerPolynomialIteratedDerivativeBits.compAccess
    (IntegerPolynomialIteratedDerivativeBits.access (IntegralMixedAuxiliaryCandidateCoordinate.native_access hn ht ha)) (query_FP hn)

attribute [local irreducible] IntegralMixedAuxiliaryCandidateCoordinate.source IntegerPolynomialIteratedDerivativeBits.source

theorem polynomial_packet {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (c p : List Bool) (i k : ℕ) :
    (source hn ht ha).polynomial (pair c (packet p i k))=
      Polynomial.derivative^[k] ((IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).polynomial
        (pair p (BinaryNatCode.encode (n (pairFst p)-i)))) := by
  unfold source IntegerPolynomialIteratedDerivativeBits.comp
  change (IntegerPolynomialIteratedDerivativeBits.source (IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha)).polynomial (query n (pair c (packet p i k)))=_
  have HQ : query n (pair c (packet p i k))=
      pair (pair p (BinaryNatCode.encode (n (pairFst p)-i))) (BinaryNatCode.encode k) := by
    simp only [query,baseContext,retained,candidate,index,derivative,packet,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rw [HQ,IntegerPolynomialIteratedDerivativeBits.packet]

end LeanCanny.Encoding.IntegralMixedCandidateReplayDatum
