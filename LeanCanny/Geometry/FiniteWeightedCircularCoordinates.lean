/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FiniteCircularCoordinates
/-! # Flat coordinates for old points, simplex weights and circular witnesses -/
@[expose] public section
namespace LeanCanny.Geometry.FiniteWeightedCircularCoordinates
open LeanCanny.ETR CircularWitness

noncomputable def homeomorph (n m : ℕ) :
    ((Fin n → ℝ) × ((Fin m → ℝ) × (Fin m → Plane))) ≃ₜ (Fin ((n+m)+2*m) → ℝ) :=
  (Homeomorph.prodAssoc (Fin n → ℝ) (Fin m → ℝ) (Fin m → Plane) : (((Fin n → ℝ) × (Fin m → ℝ)) × (Fin m → Plane)) ≃ₜ
    ((Fin n → ℝ) × ((Fin m → ℝ) × (Fin m → Plane)))).symm.trans
      (((Fin.appendHomeomorph n m).prodCongr (Homeomorph.refl (Fin m → Plane))).trans
        (FiniteCircularCoordinates.homeomorph (n+m) m))

noncomputable def encode (n m : ℕ)
    (z : (Fin n → ℝ) × ((Fin m → ℝ) × (Fin m → Plane))) : Fin ((n+m)+2*m) → ℝ :=
  homeomorph n m z

theorem encode_eq (n m : ℕ) (z : (Fin n → ℝ) × ((Fin m → ℝ) × (Fin m → Plane))) :
    encode n m z=FiniteCircularCoordinates.encode (n+m) m (Fin.append z.1 z.2.1,z.2.2) := rfl

theorem old_eval (n m : ℕ) (z : (Fin n → ℝ) × ((Fin m → ℝ) × (Fin m → Plane)))
    (t : Term) (ht : t.arity≤n) : t.eval (Formula.extend (encode n m z))=t.eval (Formula.extend z.1) := by
  rw [encode_eq,FiniteCircularCoordinates.old_eval _ _ _ t (ht.trans (Nat.le_add_right n m))]
  apply Term.eval_congr
  intro i hi
  have HI : i<n := hi.trans_le ht
  have HM : i<n+m := by omega
  simp only [Formula.extend,dite_eq_left HI,dite_eq_left HM]
  change Fin.append z.1 z.2.1 (Fin.castAdd m ⟨i,HI⟩)=z.1 ⟨i,HI⟩
  exact Fin.append_left _ _ _

theorem weight_eval (n m : ℕ) (z : (Fin n → ℝ) × ((Fin m → ℝ) × (Fin m → Plane))) (i : Fin m) :
    Formula.extend (encode n m z) (n+i.val)=z.2.1 i := by
  have HI : n+i.val<n+m := by have H:=i.isLt; omega
  have HT : n+i.val<(n+m)+2*m := by omega
  simp only [encode_eq,Formula.extend,dite_eq_left HT]
  rw [show (⟨n+i.val,HT⟩ : Fin ((n+m)+2*m))=Fin.castAdd (2*m) (Fin.natAdd n i) by rfl]
  rw [FiniteCircularCoordinates.encode_old]
  exact Fin.append_right _ _ _

theorem circle_eval (n m : ℕ) (z : (Fin n → ℝ) × ((Fin m → ℝ) × (Fin m → Plane))) (i : Fin m) (j : Fin 2) :
    Formula.extend (encode n m z) ((n+m)+2*i.val+j.val)=z.2.2 i j := by
  rw [encode_eq]
  exact FiniteCircularCoordinates.fresh_eval _ _ _ i j

end LeanCanny.Geometry.FiniteWeightedCircularCoordinates
