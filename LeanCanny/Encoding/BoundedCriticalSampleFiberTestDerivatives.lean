/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberTestSign
public import LeanCanny.Encoding.BoundedCriticalSampleFiberRootReindex

/-! # Native test derivatives at ordered actual-sample child roots

Only the derivative order is attached. The actual sample descriptor,
original record, and ordered child coordinate all remain fixed.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberTestDerivatives
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice (Family)
open BoundedCriticalSampleSlice

noncomputable def family (G : Family) : Family := BoundedCriticalSampleFiberThom.derivativeFamily G
noncomputable def access {G : Family} (B : G.Access) : (family G).Access :=
  BoundedCriticalSampleFiberThom.derivativeAccess B

def query (q : List Bool) : List Bool := pair
  (attach (pairFst (pairFst q)) (pairSnd q)) (pairSnd (pairFst q))
theorem query_FP : query ∈ FP := by polytime [query, attach]

noncomputable def value (P : Readers) (F G : Family) : List Bool → List Bool :=
  BoundedCriticalSampleFiberTestSign.value P (F.comp dropRecord) (family G) ∘ query

theorem evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P F G) :=
  (BoundedCriticalSampleFiberTestSign.evaluator h (A.comp dropRecord dropRecord_FP) (access B) ha).precompose query query_FP

theorem packet (P : Readers) (F G : Family) (u : List Bool) (r : Fin (RootCount.count P F u)) (k : ℕ) :
    value P F G (pair (pair u (BinaryNatCode.encode r.val)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign (((Polynomial.derivative^[k]) (specialized P G u)).eval
        (BoundedCriticalSampleFiberRoot.root P F u r).val)) := by
  let v := attach u (BinaryNatCode.encode k)
  let s : Fin (RootCount.count P (F.comp dropRecord) v) :=
    ⟨r.val, by simpa only [v, BoundedCriticalSampleFiberRoot.count_attach] using r.isLt⟩
  have hq : query (pair (pair u (BinaryNatCode.encode r.val)) (BinaryNatCode.encode k)) =
      pair v (BinaryNatCode.encode s.val) := by
    simp only [query, v, s, pairFst_pair, pairSnd_pair]
  rw [value, Function.comp_apply, hq, BoundedCriticalSampleFiberTestSign.value_original]
  have hr := BoundedCriticalSampleFiberRoot.root_value_attach P F u (BinaryNatCode.encode k) s r rfl
  rw [hr]
  have hp : specialized P (family G) v = (Polynomial.derivative^[k]) (specialized P G u) := by
    change specialized P (BoundedCriticalSampleFiberThom.derivativeFamily G) (attach u (BinaryNatCode.encode k)) = _
    rw [BoundedCriticalSampleFiberThom.derivative_specialized]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [hp]

theorem value_length (P : Readers) (F G : Family) (q : List Bool) : (value P F G q).length ≤ 2 := by
  unfold value BoundedCriticalSampleFiberTestSign.value
  simp only [Function.comp_apply]
  cases SignType.sign (BoundedCriticalSampleFiberTestProbe.firstCoefficient P (F.comp dropRecord) (family G)
      (BoundedCriticalSampleFiberTestSign.descriptor P (F.comp dropRecord) (query q))) *
    SignType.sign (BoundedCriticalSampleFiberProbeCoefficient.firstCoefficient P (F.comp dropRecord) true
      (BoundedCriticalSampleFiberTestSign.descriptor P (F.comp dropRecord) (query q))) <;> decide

end LeanCanny.Encoding.BoundedCriticalSampleFiberTestDerivatives
