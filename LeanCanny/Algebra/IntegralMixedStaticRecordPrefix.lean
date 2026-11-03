/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalPrefixCongruence
public import LeanCanny.Algebra.IntegralMixedCausalUnitRecord
/-! # Static-source original records before an unused future probe

The original integer polynomials and chronological code prefix determine
the actual causal record prefix. Current Q is inserted by serialization.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedStaticRecordPrefix
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedCausalRecordBits IntegralMixedFramedHistoryScript
open scoped Classical
variable {n B : ℕ} (Q : SpatialSource n) (hn : 0<n)
  (hQ : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)

include hQ in
theorem cap : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B :=
  (by unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K;omega :
    PurePowerReductionBounds.dimension (n+1) Q.degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree).trans hQ

variable (N C : ℕ) (p : ℕ→Polynomial ℤ) (hp : ∀i,p i≠0) (hd : ∀i,(p i).natDegree≤2^B)

noncomputable def originals : List (Record n B) :=List.ofFn (fun i : Fin N=>
  ⟨Q,cap Q hQ,.integer (p (N-1-i.val)) (hp _) (hd _)⟩)
noncomputable def later (w : ℕ→List Bool) : List (Record n B) :=
  ((List.range C).map (fun i=>IntegralMixedCausalUnitRecordBits.record Q hn (N+i) (w i) hQ)).reverse
noncomputable def records (w : ℕ→List Bool) :=later Q hn hQ N C w++originals Q hQ N p hp hd

theorem originals_length : (originals Q hQ N p hp hd).length=N:=List.length_ofFn
theorem later_length (w : ℕ→List Bool) : (later Q hn hQ N C w).length=C:=by
  simp only [later,List.length_reverse,List.length_map,List.length_range]
theorem records_length (w : ℕ→List Bool) : (records Q hn hQ N C p hp hd w).length=C+N:=by
  rw [records,List.length_append,later_length,originals_length]

theorem prefix_form (w : ℕ→List Bool) (j : ℕ) (hj : j≤C) :
    (records Q hn hQ N C p hp hd w).reverse.take (N+j)=
      (originals Q hQ N p hp hd).reverse++
        (List.range j).map (fun i=>IntegralMixedCausalUnitRecordBits.record Q hn (N+i) (w i) hQ) :=by
  rw [records,List.reverse_append,later,List.reverse_reverse,List.take_append]
  have HL : (originals Q hQ N p hp hd).reverse.length=N:=by rw [List.length_reverse,originals_length]
  rw [List.take_of_length_le (by rw [HL];omega),HL,Nat.add_sub_cancel_left,←List.map_take,List.take_range,min_eq_left hj]

theorem prefix_eq (w v : ℕ→List Bool) (j : ℕ) (hj : j≤C) (he : ∀i,i<j→w i=v i) :
    (records Q hn hQ N C p hp hd w).reverse.take (N+j)=
      (records Q hn hQ N C p hp hd v).reverse.take (N+j) :=by
  rw [prefix_form Q hn hQ N C p hp hd w j hj,prefix_form Q hn hQ N C p hp hd v j hj]
  apply congrArg (List.append _)
  apply List.map_congr_left
  intro i hi
  rw [he i (List.mem_range.mp hi)]

theorem prefix_heq {n' B' : ℕ} (Q' : SpatialSource n') (hn' : 0<n')
    (hQ' : IntegralMixedExceptionalBounds.auxiliaryCap (n'+1) Q'.degree≤2^B')
    (N' C' : ℕ) (p' : ℕ→Polynomial ℤ) (hp' : ∀i,p' i≠0) (hd' : ∀i,(p' i).natDegree≤2^B')
    (w w' : ℕ→List Bool) (j : ℕ) (hj : j≤C)
    (en : n=n') (eB : B=B') (eN : N=N') (eC : C=C') (eQ : HEq Q Q')
    (ep : ∀i,p i=p' i) (ew : ∀i,i<j→w i=w' i) :
    HEq ((records Q hn hQ N C p hp hd w).reverse.take (N+j))
      ((records Q' hn' hQ' N' C' p' hp' hd' w').reverse.take (N'+j)) :=by
  subst n'
  subst B'
  subst N'
  subst C'
  cases eq_of_heq eQ
  have EP :p=p':=funext ep
  subst p'
  exact heq_of_eq (prefix_eq Q hn hQ N C p hp hd w w' j hj ew)

theorem run_heq {n' B' S S' : ℕ} (Q' : SpatialSource n') (hn' : 0<n')
    (hQ' : IntegralMixedExceptionalBounds.auxiliaryCap (n'+1) Q'.degree≤2^B')
    (N' C' : ℕ) (p' : ℕ→Polynomial ℤ) (hp' : ∀i,p' i≠0) (hd' : ∀i,(p' i).natDegree≤2^B')
    (x : State Q S B 0 (Fin 0)) (y : State Q' S' B' 0 (Fin 0))
    (w w' : ℕ→List Bool) (j : ℕ) (hj : j≤C)
    (hr : C+N≤S+1) (hr' : C'+N'≤S'+1) (fr : Instruction n B) (fr' : Instruction n' B')
    (en : n=n') (eB : B=B') (eS : S=S') (eN : N=N') (eC : C=C') (eQ : HEq Q Q') (ex : HEq x y)
    (ep : ∀i,p i=p' i) (ew : ∀i,i<j→w i=w' i) :
    HEq (IntegralMixedCausalPrefixCongruence.prefixRun x (records Q hn hQ N C p hp hd w)
      (by rw [records_length];exact hr) fr (N+j) (by rw [records_length];omega))
      (IntegralMixedCausalPrefixCongruence.prefixRun y (records Q' hn' hQ' N' C' p' hp' hd' w')
        (by rw [records_length];exact hr') fr' (N'+j) (by rw [records_length];omega)) :=by
  subst n'
  subst B'
  subst S'
  subst N'
  subst C'
  cases eq_of_heq eQ
  cases eq_of_heq ex
  have EP :p=p':=funext ep
  subst p'
  exact IntegralMixedCausalPrefixCongruence.run_prefix x _ _ _ _ fr fr' (N+j)
    (by rw [records_length];omega) (by rw [records_length];omega)
    (prefix_eq Q hn hQ N C p hp hd w w' j hj ew)
end LeanCanny.Algebra.IntegralMixedStaticRecordPrefix
