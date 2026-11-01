/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CircularWitness
public import LeanCanny.Connectivity.Problem
public import Mathlib.Topology.Homeomorph.Lemmas
/-! # Flat finite-coordinate layout of a family of circular witnesses -/
@[expose] public section
namespace LeanCanny.Geometry.FiniteCircularCoordinates
open CircularWitness LeanCanny.ETR
open scoped Classical

def freshIndex (n m : ℕ) (i : Fin m) (j : Fin 2) : Fin (n+2*m) :=
  Fin.natAdd n ⟨2*i.val+j.val,by have HI:=i.isLt; have HJ:=j.isLt; omega⟩

theorem freshIndex_val (n m : ℕ) (i : Fin m) (j : Fin 2) :
    (freshIndex n m i j).val=n+2*i.val+j.val := by dsimp [freshIndex]; omega

noncomputable def encode (n m : ℕ) (z : (Fin n → ℝ) × (Fin m → Plane)) : Fin (n+2*m) → ℝ :=
  Fin.append z.1 (fun k => z.2 ⟨k.val/2,by have H:=k.isLt; omega⟩ ⟨k.val%2,Nat.mod_lt _ (by decide)⟩)

noncomputable def decode (n m : ℕ) (y : Fin (n+2*m) → ℝ) : (Fin n → ℝ) × (Fin m → Plane) :=
  (fun i => y (Fin.castAdd (2*m) i),fun i => WithLp.toLp 2 (fun j => y (freshIndex n m i j)))

theorem encode_old (n m : ℕ) (z : (Fin n → ℝ) × (Fin m → Plane)) (i : Fin n) :
    encode n m z (Fin.castAdd (2*m) i)=z.1 i := Fin.append_left _ _ _

theorem encode_fresh (n m : ℕ) (z : (Fin n → ℝ) × (Fin m → Plane)) (i : Fin m) (j : Fin 2) :
    encode n m z (freshIndex n m i j)=z.2 i j := by
  simp only [encode,freshIndex,Fin.append_right]
  have HI:=i.isLt
  have HJ:=j.isLt
  have HQ : (2*i.val+j.val)/2=i.val := by omega
  have HR : (2*i.val+j.val)%2=j.val := by omega
  simp only [HQ,HR]

theorem decode_encode (n m : ℕ) (z : (Fin n → ℝ) × (Fin m → Plane)) : decode n m (encode n m z)=z := by
  apply Prod.ext
  · funext i
    exact encode_old n m z i
  · funext i
    apply (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).injective
    funext j
    exact encode_fresh n m z i j

theorem encode_decode (n m : ℕ) (y : Fin (n+2*m) → ℝ) : encode n m (decode n m y)=y := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · exact Fin.append_left _ _ _
  · rw [encode,Fin.append_right]
    change y (freshIndex n m ⟨j.val/2,by have H:=j.isLt; omega⟩ ⟨j.val%2,Nat.mod_lt _ (by decide)⟩)=y (Fin.natAdd n j)
    apply congrArg y
    apply Fin.ext
    dsimp [freshIndex]
    omega

noncomputable def homeomorph (n m : ℕ) : ((Fin n → ℝ) × (Fin m → Plane)) ≃ₜ (Fin (n+2*m) → ℝ) where
  toFun := encode n m
  invFun := decode n m
  left_inv := decode_encode n m
  right_inv := encode_decode n m
  continuous_toFun := by
    have HP : Continuous (fun z : (Fin n → ℝ) × (Fin m → Plane) =>
        (z.1,fun k : Fin (2*m) => z.2 ⟨k.val/2,by have H:=k.isLt; omega⟩ ⟨k.val%2,Nat.mod_lt _ (by decide)⟩)) := by
      apply continuous_fst.prodMk
      apply continuous_pi
      intro k
      exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) _).comp ((continuous_apply _).comp continuous_snd)
    exact (Fin.continuous_append n (2*m)).comp HP
  continuous_invFun := (continuous_pi (fun i => continuous_apply (Fin.castAdd (2*m) i))).prodMk
    (continuous_pi (fun i => (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      (continuous_pi (fun j => continuous_apply (freshIndex n m i j)))))

theorem fresh_eval (n m : ℕ) (z : (Fin n → ℝ) × (Fin m → Plane)) (i : Fin m) (j : Fin 2) :
    Formula.extend (encode n m z) (n+2*i.val+j.val)=z.2 i j := by
  rw [← freshIndex_val n m i j]
  simp only [Formula.extend,dite_eq_left (freshIndex n m i j).isLt]
  exact encode_fresh n m z i j

theorem old_eval (n m : ℕ) (z : (Fin n → ℝ) × (Fin m → Plane)) (t : Term) (ht : t.arity≤n) :
    t.eval (Formula.extend (encode n m z))=t.eval (Formula.extend z.1) := by
  apply Term.eval_congr
  intro i hi
  have HI : i < n := hi.trans_le ht
  have HN : i < n+2*m := by omega
  simp only [Formula.extend,dite_eq_left HI,dite_eq_left HN]
  exact encode_old n m z ⟨i,HI⟩

end LeanCanny.Geometry.FiniteCircularCoordinates
