/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SubresultantAccessFP
public import LeanCanny.Computation.SpaceFunctionBranch

/-!
# Certified subresultant entry access with space-bounded coefficient children

The FP index transformation feeds the existing Sylvester entry evaluator.
Out-of-range subresultant orders and coefficient indices return zero, giving
a total routine on all strings while the valid branch uses the minor embedding.
-/

@[expose] public section

namespace LeanCanny.Algebra.SubresultantBits.Access
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation

def entry (a : SubresultantBits.Access) (p : List Bool) : List Bool :=
  if a.enabled (pairFst p) then a.base.entry (a.query p) else []

noncomputable def entryEvaluator (a : SubresultantBits.Access) (ha : a.ControlsPolyTime)
    (L : SpaceFunction a.base.leftCoefficient) (R : SpaceFunction a.base.rightCoefficient) : SpaceFunction a.entry := by
  have hflag := ((a.enabled_fppred ha).comp pairFst_mem_FP).flag_mem_FP
  let E := (a.base.entryEvaluator ha.base L R).precompose a.query (a.query_mem_FP ha)
  let S := SpaceFunction.branch (fun p => decide (a.enabled (pairFst p))) hflag E (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  refine S.congr (funext fun p => ?_)
  simp only [entry, decide_eq_true_eq, Function.comp_apply]

theorem enabled_eq (a : SubresultantBits.Access) (c : List Bool) (m n k r : ℕ)
    (hm : a.base.leftDegree c = BinaryNatCode.encode m) (hn : a.base.rightDegree c = BinaryNatCode.encode n)
    (hk : a.order c = BinaryNatCode.encode k) (hr : a.coefficient c = BinaryNatCode.encode r) :
    a.enabled c ↔ k < m ∧ k < n ∧ r ≤ k := by
  simp only [enabled, hm, hn, hk, hr, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem entry_correct {R : Type*} [Semiring R] (a : SubresultantBits.Access) (c : List Bool)
    (f g : Polynomial (Polynomial R)) (m n k r D : ℕ) (enc : R → List Bool)
    (hm : a.base.leftDegree c = BinaryNatCode.encode m) (hn : a.base.rightDegree c = BinaryNatCode.encode n)
    (hk : a.order c = BinaryNatCode.encode k) (hr : a.coefficient c = BinaryNatCode.encode r)
    (hf : ∀ i, a.base.leftCoefficient (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode D))) = enc ((f.coeff i).coeff D))
    (hg : ∀ i, a.base.rightCoefficient (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode D))) = enc ((g.coeff i).coeff D))
    (hz : enc 0 = []) (hv : k < m ∧ k < n ∧ r ≤ k)
    (i j : Fin ((m - k) + (n - k))) :
    a.entry (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode D)))) =
      enc ((Subresultant.minor f g m n k r i j).coeff D) := by
  have hen := (a.enabled_eq c m n k r hm hn hk hr).mpr hv
  rw [entry, pairFst_pair, ite_eq_left hen, a.query_packet c m k r i.val j.val D hm hk hr]
  rw [Subresultant.minor_eq_submatrix f g m n k r hv.1 hv.2.1 hv.2.2, Matrix.submatrix_apply]
  have h := a.base.entry_correct c f g m n D enc hm hn hf hg hz
    (Subresultant.rowEmbedding m n k r hv.1 hv.2.1 hv.2.2 i) (Subresultant.colEmbedding m n k hv.1 hv.2.1 j)
  simpa only [Subresultant.rowEmbedding, Subresultant.colEmbedding] using h

end LeanCanny.Algebra.SubresultantBits.Access
