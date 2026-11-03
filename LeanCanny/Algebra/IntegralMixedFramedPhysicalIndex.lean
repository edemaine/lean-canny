/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryScript
/-! # Explicit oldest-first indices for full physical framed histories

Old physical columns keep their exact natural index. The fresh scalar is
last in each creating prefix, after that command's critical physical block.
This enumeration uses only command tags, never an algebra or root value.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
open IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedFramedHistoryScript (Instruction Index)
open scoped Classical
variable {n B : ℕ}

def block (n : ℕ) := (n+1)+(n+2)
def added {P : SpatialSource n} (c : Command P B) := if c.isCritical then block n+1 else 1

def arity : List (Instruction n B)→ℕ
  | []=>0
  | c::cs=>arity cs+added c.command

def old {P : SpatialSource n} {ι : Type} (c : Command P B) : ι→NextIndex ι c :=
  match c with
  | .integer .. =>Sum.inl
  | .critical _ =>Sum.inl ∘ Sum.inl
  | .cut .. =>Sum.inl

def fresh {P : SpatialSource n} {ι : Type} (c : Command P B) : NextIndex ι c :=
  match c with
  | .integer .. =>Sum.inr ()
  | .critical _ =>Sum.inr ()
  | .cut .. =>Sum.inr ()

def unitEquiv : Unit≃Fin 1 := Equiv.ofUnique _ _
def criticalEquiv : FlatAffineCriticalStage.Variables (n+1)≃Fin (block n) := finSumFinEquiv

noncomputable def stepEquiv {P : SpatialSource n} {ι : Type} {m : ℕ}
    (c : Command P B) (e : ι≃Fin m) : NextIndex ι c≃Fin (m+added c) :=
  match c with
  | .integer .. =>(Equiv.sumCongr e unitEquiv).trans finSumFinEquiv
  | .critical _ =>((Equiv.sumCongr ((Equiv.sumCongr e criticalEquiv).trans finSumFinEquiv)
      unitEquiv).trans finSumFinEquiv).trans (finCongr (Nat.add_assoc m (block n) 1))
  | .cut .. =>(Equiv.sumCongr e unitEquiv).trans finSumFinEquiv

noncomputable def enumerate : (cs : List (Instruction n B))→Index (Fin 0) cs≃Fin (arity cs)
  | []=>Equiv.refl _
  | c::cs=>stepEquiv c.command (enumerate cs)

theorem step_old {P : SpatialSource n} {ι : Type} {m : ℕ} (c : Command P B) (e : ι≃Fin m) (i : ι) :
    (stepEquiv c e (old c i)).val=(e i).val := by
  cases c <;> rfl

theorem step_fresh {P : SpatialSource n} {ι : Type} {m : ℕ} (c : Command P B) (e : ι≃Fin m) :
    (stepEquiv c e (fresh c)).val=m+added c-1 := by
  cases c <;> simp only [added,Command.isCritical,Bool.false_eq_true,ite_true,ite_false]
  all_goals change m+_=_
  all_goals omega

theorem arity_eq (cs : List (Instruction n B)) :
    arity cs=cs.length+(2*n+3)*cs.countP (fun c=>c.command.isCritical) := by
  induction cs with
  | nil=>simp only [arity,List.length_nil,List.countP_nil,Nat.mul_zero,Nat.add_zero]
  | cons c cs ih=>
    rw [arity,ih,List.length_cons,List.countP_cons]
    unfold added block
    cases hc:c.command.isCritical <;> simp only [ite_true,ite_false,Bool.false_eq_true,Nat.add_zero,Nat.mul_add,Nat.mul_one]
    all_goals omega

def scalarSlot : (cs : List (Instruction n B))→Fin cs.length→Index (Fin 0) cs
  | [],i=>Fin.elim0 i
  | c::cs,i=>Fin.cases (fresh c.command) (fun j=>old c.command (scalarSlot cs j)) i

def slotNumber : List (Instruction n B)→ℕ→ℕ
  | [],_=>0
  | c::cs,i=>if i=0 then arity (c::cs)-1 else slotNumber cs (i-1)

theorem enumerate_scalar (cs : List (Instruction n B)) (i : Fin cs.length) :
    (enumerate cs (scalarSlot cs i)).val=slotNumber cs i.val := by
  induction cs with
  | nil=>exact Fin.elim0 i
  | cons c cs ih=>
    refine Fin.cases ?_ (fun j=>?_) i
    · change (stepEquiv c.command (enumerate cs) (fresh c.command)).val=arity (c::cs)-1
      exact step_fresh c.command (enumerate cs)
    · change (stepEquiv c.command (enumerate cs) (old c.command (scalarSlot cs j))).val=slotNumber cs j.val
      exact (step_old c.command (enumerate cs) (scalarSlot cs j)).trans (ih j)
end LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
