/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.TriangularTermGraph
/-! # Unique continuous graphs whose successive coordinates include positive-part gates -/
@[expose] public section
namespace LeanCanny.Geometry.TriangularContinuousGraph
open Set

noncomputable def extend (n : ℕ) (b : (i : ℕ) → (Fin (n+i) → ℝ) → ℝ) (x : Fin n → ℝ) :
    (m : ℕ) → (Fin (n+m) → ℝ)
  | 0 => x
  | m+1 => Fin.snoc (extend n b x m) (b m (extend n b x m))

theorem stable (n : ℕ) (b : (i : ℕ) → (Fin (n+i) → ℝ) → ℝ) (x : Fin n → ℝ)
    (m M : ℕ) (hm : m≤M) (j : ℕ) (hj : j<n+m) :
    extend n b x M ⟨j,hj.trans_le (Nat.add_le_add_left hm n)⟩=extend n b x m ⟨j,hj⟩ := by
  induction M with
  | zero =>
    have H : m=0 := by omega
    subst m
    rfl
  | succ M IH =>
    by_cases H : m≤M
    · change Fin.snoc _ _ (Fin.castSucc ⟨j,hj.trans_le (Nat.add_le_add_left H n)⟩)=_
      rw [Fin.snoc_castSucc]
      exact IH H
    · have HE : m=M+1 := by omega
      subst m
      rfl

theorem old (n : ℕ) (b : (i : ℕ) → (Fin (n+i) → ℝ) → ℝ) (x : Fin n → ℝ) (m : ℕ) (i : Fin n) :
    extend n b x m (Fin.castAdd m i)=x i := stable n b x 0 m (Nat.zero_le _) i.val i.isLt

def truncate (n m i : ℕ) (hi : i≤m) (y : Fin (n+m) → ℝ) : Fin (n+i) → ℝ :=
  fun j => y ⟨j.val,j.isLt.trans_le (Nat.add_le_add_left hi n)⟩

theorem truncate_extend (n : ℕ) (b : (i : ℕ) → (Fin (n+i) → ℝ) → ℝ) (x : Fin n → ℝ)
    (m i : ℕ) (hi : i≤m) : truncate n m i hi (extend n b x m)=extend n b x i := by
  funext j
  exact stable n b x i m hi j.val j.isLt

def projection (n m : ℕ) (y : Fin (n+m) → ℝ) : Fin n → ℝ := fun i => y (Fin.castAdd m i)
def Solutions (n : ℕ) (b : (i : ℕ) → (Fin (n+i) → ℝ) → ℝ) (m : ℕ) : Set (Fin (n+m) → ℝ) :=
  {y | ∀ i : Fin m, y ⟨n+i.val,by have HI:=i.isLt; omega⟩=b i.val (truncate n m i.val i.isLt.le y)}

theorem equations (n : ℕ) (b : (i : ℕ) → (Fin (n+i) → ℝ) → ℝ) (x : Fin n → ℝ) (m : ℕ) :
    extend n b x m∈Solutions n b m := by
  intro i
  rw [truncate_extend,stable n b x (i.val+1) m (by have HI:=i.isLt; omega) (n+i.val) (by omega)]
  exact Fin.snoc_last _ _

theorem unique (n : ℕ) (b : (i : ℕ) → (Fin (n+i) → ℝ) → ℝ) (m : ℕ) (y : Solutions n b m) :
    extend n b (projection n m y.val) m=y.val := by
  have HE : ∀ j (hj : j<n+m), y.val ⟨j,hj⟩=extend n b (projection n m y.val) m ⟨j,hj⟩ := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j IH =>
      intro hj
      by_cases H : j<n
      · exact (old n b (projection n m y.val) m ⟨j,H⟩).symm
      · let i:=j-n
        have HI : i<m := by dsimp [i]; omega
        have HJ : n+i=j := by dsimp [i]; omega
        calc
          y.val ⟨j,hj⟩=b i (truncate n m i HI.le y.val) := by
            convert y.property ⟨i,HI⟩ using 1
            exact congrArg y.val (Fin.ext HJ.symm)
          _=b i (extend n b (projection n m y.val) i) := by
            apply congrArg (b i)
            funext k
            have HK : k.val<j := by have HK:=k.isLt; omega
            have HKM : k.val<n+m := by omega
            exact (IH k.val HK HKM).trans
              (stable n b (projection n m y.val) i m HI.le k.val k.isLt)
          _=extend n b (projection n m y.val) m ⟨j,hj⟩ := by
            have HQ:=equations n b (projection n m y.val) m ⟨i,HI⟩
            rw [truncate_extend] at HQ
            simpa only [HJ] using HQ.symm
  funext i
  exact (HE i.val i.isLt).symm

theorem continuous_extend (n : ℕ) (b : (i : ℕ) → (Fin (n+i) → ℝ) → ℝ)
    (hb : ∀ i,Continuous (b i)) (m : ℕ) : Continuous (fun x : Fin n → ℝ => extend n b x m) := by
  induction m with
  | zero => exact continuous_id
  | succ m IH =>
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [extend,Fin.snoc_last,Function.comp_def] using (hb m).comp IH
    · simpa only [extend,Fin.snoc_castSucc,Function.comp_def] using (continuous_apply j).comp IH

noncomputable def homeomorph (n : ℕ) (b : (i : ℕ) → (Fin (n+i) → ℝ) → ℝ)
    (hb : ∀ i,Continuous (b i)) (m : ℕ) : Solutions n b m ≃ₜ (Fin n → ℝ) where
  toFun y := projection n m y.val
  invFun x := ⟨extend n b x m,equations n b x m⟩
  left_inv y := Subtype.ext (unique n b m y)
  right_inv x := by funext i; exact old n b x m i
  continuous_toFun := continuous_pi (fun i => (continuous_apply (Fin.castAdd m i)).comp continuous_subtype_val)
  continuous_invFun := (continuous_extend n b hb m).subtype_mk _

end LeanCanny.Geometry.TriangularContinuousGraph
