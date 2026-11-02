/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.InfinitesimalSignSpace
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Charged bounded scans of selected real coefficient signs

The native reader returns encoded signs, not binary real coefficients.
The total machine stores two bits and scans the original binary degree
bound. Semantic correctness is local to the actual selected polynomial;
invalid labels need no interpreting hom or arbitrary algebra evaluator.
-/
@[expose] public section
namespace LeanCanny.Algebra.RealInfinitesimalSignSpace
open LeanCanny.Encoding LeanCanny.Computation InfinitesimalSign Polynomial

noncomputable def tag (x : ℝ) := InfinitesimalSign.encode (SignType.sign x)

theorem tag_nil (x : ℝ) : tag x=[]↔x=0 := by
  have HE (s : SignType) : InfinitesimalSign.encode s=[]↔s=0 := by cases s <;> decide
  exact (HE _).trans sign_eq_zero_iff

noncomputable def scan (a : ℕ→ℝ) : ℕ→List Bool
  | 0=>[]
  | k+1=>if scan a k=[] then tag (a k) else scan a k

theorem scan_zero (a : ℕ→ℝ) (k : ℕ) (H : ∀ i<k,a i=0) : scan a k=[] := by
  induction k with
  | zero=>rfl
  | succ k ih=>simp only [scan,ih (fun i hi=>H i (by omega)),↓reduceIte,(tag_nil _).mpr (H k (by omega))]

theorem scan_first (a : ℕ→ℝ) (n k : ℕ) (hn : n<k) (HA : a n≠0) (HZ : ∀ i<n,a i=0) :
    scan a k=tag (a n) := by
  induction k with
  | zero=>omega
  | succ k ih=>
    by_cases HE : n=k
    · subst n
      simp only [scan,scan_zero a k HZ,↓reduceIte]
    · rw [scan,ih (by omega),ite_eq_right ((tag_nil _).not.mpr HA)]

theorem scan_polynomial (p : Polynomial ℝ) (k : ℕ) (hk : p.natDegree<k) : scan p.coeff k=tag p.trailingCoeff := by
  by_cases HP : p=0
  · subst p
    rw [scan_zero _ k (by simp)]
    exact ((tag_nil _).mpr (by simp)).symm
  · exact scan_first _ p.natTrailingDegree k (p.natTrailingDegree_le_natDegree.trans_lt hk)
      (Polynomial.coeff_natTrailingDegree_ne_zero.mpr HP)
      (fun i hi=>Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi)

def value (f : List Bool→List Bool) (degree : List Bool→ℕ) (c : List Bool) :=
  BoundedFold.fold (InfinitesimalSign.update f) (fun _=>[]) c (degree c+1)

theorem fold_length (f : List Bool→List Bool) (Hf : ∀ z,(f z).length≤2) (c : List Bool) (k : ℕ) :
    (BoundedFold.fold (InfinitesimalSign.update f) (fun _=>[]) c k).length≤2 := by
  induction k with
  | zero=>exact Nat.zero_le _
  | succ k ih=>
    simp only [BoundedFold.fold,InfinitesimalSign.update,InfinitesimalSign.finish,pairFst_pair,pairSnd_pair,
      BoundedFold.accumulator_packet]
    split_ifs
    · exact Hf _
    · exact ih

theorem evaluator {f : List Bool→List Bool} (E : SpaceFunction f) (Hf : ∀ z,(f z).length≤2)
    (degree : List Bool→ℕ) (hd : BinaryFn degree) : SpaceFunction (value f degree) := by
  let Q := BoundedFold.evaluator (InfinitesimalSign.updateEvaluator E)
    (fun c=>BinaryNatCode.encode (degree c+1)) (fun _=>[])
    (hd.add (BinaryFn.const 1)).bits_mem_FP (constFn_mem_FP []) 2
    (fun c i _=>by simpa only [Polynomial.eval_ofNat] using fold_length f Hf c i)
  exact Q.congr (funext fun c=>by simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits]; rfl)

theorem fold_scan (f : List Bool→List Bool) (c : List Bool) (a : ℕ→ℝ)
    (Hf : ∀ k,f (pair c (BinaryNatCode.encode k))=tag (a k)) (k : ℕ) :
    BoundedFold.fold (InfinitesimalSign.update f) (fun _=>[]) c k=scan a k := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [BoundedFold.fold,ih]
    simp only [InfinitesimalSign.update,InfinitesimalSign.finish,InfinitesimalSign.query,pairFst_pair,pairSnd_pair,
      BoundedFold.context_packet,BoundedFold.counter_packet,BoundedFold.accumulator_packet,Hf,scan]

theorem value_at (f : List Bool→List Bool) (degree : List Bool→ℕ) (c : List Bool) (p : Polynomial ℝ)
    (hd : p.natDegree≤degree c) (hf : ∀ k,f (pair c (BinaryNatCode.encode k))=tag (p.coeff k)) :
    value f degree c=tag p.trailingCoeff := by
  rw [value,fold_scan f c p.coeff hf]
  exact scan_polynomial p _ (by omega)

theorem eventually_correct (p : Polynomial ℝ) :
    ∃ δ : ℝ,0<δ ∧ ∀ x,0<x→x<δ→tag p.trailingCoeff=tag (p.eval x) := by
  obtain ⟨δ,Hδ,HS⟩:=InfinitesimalSign.sign_eval_eq_trailingCoeff p
  exact ⟨δ,Hδ,fun x Hx Hxd=>congrArg InfinitesimalSign.encode (HS x Hx Hxd).symm⟩

end LeanCanny.Algebra.RealInfinitesimalSignSpace
