/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaStrictWitness
/-! # Unique polynomial gate graphs are homeomorphic to their original coordinates -/
@[expose] public section
namespace LeanCanny.Geometry.TriangularTermGraph
open LeanCanny.ETR Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def extend (n : ℕ) (b : ℕ → Term) (x : Fin n → ℝ) : (m : ℕ) → Fin (n+m) → ℝ
  | 0 => x
  | m+1 => Fin.snoc (extend n b x m) ((b m).eval (Formula.extend (extend n b x m)))

theorem stable (n : ℕ) (b : ℕ → Term) (x : Fin n → ℝ) (m M : ℕ) (hm : m≤M)
    (j : ℕ) (hj : j<n+m) : extend n b x M ⟨j,hj.trans_le (Nat.add_le_add_left hm n)⟩ = extend n b x m ⟨j,hj⟩ := by
  induction M with
  | zero =>
    have H : m=0 := by omega
    subst m
    rfl
  | succ M IH =>
    by_cases H : m≤M
    · change Fin.snoc _ _ (Fin.castSucc ⟨j,hj.trans_le (Nat.add_le_add_left H n)⟩) = _
      rw [Fin.snoc_castSucc]
      exact IH H
    · have HE : m=M+1 := by omega
      subst m
      rfl

theorem old (n : ℕ) (b : ℕ → Term) (x : Fin n → ℝ) (m : ℕ) (i : Fin n) :
    extend n b x m (Fin.castAdd m i) = x i := stable n b x 0 m (Nat.zero_le _) i.val i.isLt

theorem coordinate (n : ℕ) (b : ℕ → Term) (x : Fin n → ℝ) (m i : ℕ) (hi : i<m) :
    extend n b x m ⟨n+i,by omega⟩ = (b i).eval (Formula.extend (extend n b x i)) := by
  rw [stable n b x (i+1) m (by omega) (n+i) (by omega)]
  exact Fin.snoc_last _ _

theorem equations (n : ℕ) (b : ℕ → Term) (m : ℕ) (hb : ∀ i<m, (b i).arity≤n+i) (x : Fin n → ℝ) :
    ∀ i : Fin m, extend n b x m ⟨n+i.val,by have H:=i.isLt; omega⟩ =
      (b i.val).eval (Formula.extend (extend n b x m)) := by
  intro i
  rw [coordinate n b x m i.val i.isLt]
  apply Term.eval_congr
  intro j hj
  have HJ : j<n+i.val := hj.trans_le (hb i.val i.isLt)
  have HJM : j<n+m := HJ.trans_le (Nat.add_le_add_left i.isLt.le n)
  simp only [Formula.extend,dite_eq_left HJ,dite_eq_left HJM]
  exact (stable n b x i.val m i.isLt.le j HJ).symm

def projection (n m : ℕ) (y : Fin (n+m) → ℝ) : Fin n → ℝ := fun i => y (Fin.castAdd m i)

def Solutions (n : ℕ) (b : ℕ → Term) (m : ℕ) : Set (Fin (n+m) → ℝ) :=
  {y | ∀ i : Fin m, y ⟨n+i.val,by have H:=i.isLt; omega⟩ = (b i.val).eval (Formula.extend y)}

theorem unique (n : ℕ) (b : ℕ → Term) (m : ℕ) (hb : ∀ i<m, (b i).arity≤n+i)
    (y : Solutions n b m) : extend n b (projection n m y.val) m = y.val := by
  have HE : ∀ j (hj : j<n+m), y.val ⟨j,hj⟩ = extend n b (projection n m y.val) m ⟨j,hj⟩ := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j IH =>
      intro hj
      by_cases H : j<n
      · exact (old n b (projection n m y.val) m ⟨j,H⟩).symm
      · let i := j-n
        have HI : i<m := by dsimp [i]; omega
        have HJ : n+i=j := by dsimp [i]; omega
        have HB := hb i HI
        calc
          y.val ⟨j,hj⟩ = (b i).eval (Formula.extend y.val) := by
            convert y.property ⟨i,HI⟩ using 1
            exact congrArg y.val (Fin.ext HJ.symm)
          _ = (b i).eval (Formula.extend (extend n b (projection n m y.val) m)) := by
            apply Term.eval_congr
            intro k hk
            have HK : k<j := by omega
            have HKM : k<n+m := by omega
            simp only [Formula.extend,dite_eq_left HKM]
            exact IH k HK HKM
          _ = extend n b (projection n m y.val) m ⟨j,hj⟩ := by
            have HQ := equations n b m hb (projection n m y.val) ⟨i,HI⟩
            simpa only [HJ] using HQ.symm
  funext i
  exact (HE i.val i.isLt).symm

theorem continuous_extend (n : ℕ) (b : ℕ → Term) (m : ℕ) : Continuous (fun x : Fin n → ℝ => extend n b x m) := by
  induction m with
  | zero => exact continuous_id
  | succ m IH =>
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [extend,Fin.snoc_last,Function.comp_def] using
        (LeanCanny.Connectivity.FormulaStrictWitness.continuous_eval (n+m) (b m)).comp IH
    · simpa only [extend,Fin.snoc_castSucc,Function.comp_def] using (continuous_apply j).comp IH

noncomputable def homeomorph (n : ℕ) (b : ℕ → Term) (m : ℕ) (hb : ∀ i<m, (b i).arity≤n+i) :
    Solutions n b m ≃ₜ (Fin n → ℝ) where
  toFun y := projection n m y.val
  invFun x := ⟨extend n b x m,equations n b m hb x⟩
  left_inv y := Subtype.ext (unique n b m hb y)
  right_inv x := by funext i; exact old n b x m i
  continuous_toFun := continuous_pi (fun i => (continuous_apply (Fin.castAdd m i)).comp continuous_subtype_val)
  continuous_invFun := (continuous_extend n b m).subtype_mk _

end LeanCanny.Geometry.TriangularTermGraph
