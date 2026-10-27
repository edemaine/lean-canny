/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberTestSign
public import LeanCanny.Encoding.BoundedAlgebraicFiberRootReindex

/-! # Native derivatives of arbitrary tests at ordered fiber roots

Input is a fiber-root query paired with a binary derivative order. Attaching
the order to the source retains both the original algebraic parameter and
the original ordered fiber root. Only the queried derivative sign is read.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberTestDerivatives
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice

noncomputable def family (G : Family) : Family := iterateDerivative (G.comp pairFst) pairSnd
noncomputable def access {G : Family} (B : G.Access) : (family G).Access :=
  iterateDerivativeAccess (B.comp pairFst pairFst_mem_FP) pairSnd pairSnd_mem_FP

def query (q : List Bool) : List Bool := pair
  (signQuery (pair (pairFst (pairFst q)) (pairSnd q))) (pairSnd (pairFst q))
theorem query_FP : query ∈ FP := by
  have ho := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hs := mem_FP_comp (mem_FP_pair ho pairSnd_mem_FP) signQuery_FP
  exact mem_FP_pair hs (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def value (P : Readers) (F G : Family) : List Bool → List Bool :=
  BoundedAlgebraicFiberTestSign.value (P.comp pairFst) (F.comp pairFst) (family G) ∘ query

theorem evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P F G) :=
  (BoundedAlgebraicFiberTestSign.evaluator (h.comp pairFst_mem_FP) (A.comp pairFst pairFst_mem_FP)
    (access B) (fun c => ha (pairFst c))).precompose query query_FP

theorem packet (P : Readers) (F G : Family) (u : List Bool) (r : Fin (RootCount.count P F u)) (k : ℕ) :
    value P F G (pair (pair u (BinaryNatCode.encode r.val)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign (((Polynomial.derivative^[k]) (specialized P G u)).eval
        (BoundedAlgebraicFiberRoot.root P F u r).val)) := by
  let v := signQuery (pair u (BinaryNatCode.encode k))
  let s : Fin (RootCount.count (P.comp pairFst) (F.comp pairFst) v) :=
    ⟨r.val, by simpa only [v, BoundedAlgebraicFiberRoot.count_attach] using r.isLt⟩
  have hq : query (pair (pair u (BinaryNatCode.encode r.val)) (BinaryNatCode.encode k)) =
      pair v (BinaryNatCode.encode s.val) := by
    simp only [query, v, s, pairFst_pair, pairSnd_pair]
  rw [value, Function.comp_apply, hq, BoundedAlgebraicFiberTestSign.value_original]
  have hr := BoundedAlgebraicFiberRoot.root_value_attach P F u (BinaryNatCode.encode k) s r rfl
  rw [hr]
  have hp : specialized (P.comp pairFst) (family G) v =
      (Polynomial.derivative^[k]) (specialized P G u) := by
    rw [family, iterateDerivative_specialized]
    have hk : Nat.fromBitsLE (pairSnd (pairFst v)) = k := by
      simp only [v, signQuery, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [hk, specialized_attach_comp]
  rw [hp]

theorem value_length (P : Readers) (F G : Family) (q : List Bool) : (value P F G q).length ≤ 2 := by
  unfold value BoundedAlgebraicFiberTestSign.value
  simp only [Function.comp_apply]
  cases SignType.sign (BoundedAlgebraicFiberTestProbe.firstCoefficient (P.comp pairFst) (F.comp pairFst) (family G)
      (BoundedAlgebraicFiberTestSign.descriptor (P.comp pairFst) (F.comp pairFst) (query q))) *
    SignType.sign (BoundedAlgebraicFiberProbeCoefficient.firstCoefficient (P.comp pairFst) (F.comp pairFst) true
      (BoundedAlgebraicFiberTestSign.descriptor (P.comp pairFst) (F.comp pairFst) (query q))) <;> decide

end LeanCanny.Encoding.BoundedAlgebraicFiberTestDerivatives
