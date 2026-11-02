/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHistorySemantics
public import LeanCanny.Algebra.IntegralMixedCoordinateRename
public import LeanCanny.Algebra.IntegralMixedExpressionBounds
public import LeanCanny.Geometry.FrozenCoordinateOrdering

/-! # Literal next frozen frames over a retained mixed bank

Adding one retained endpoint coordinate keeps every old affine level after
shifting its newest-first references. Erasing the new coordinate recovers the
old slice exactly. Spatial ordering changes only coordinate names and LOW;
the interpreting hom, old sampler and bank remain the same.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory Set
open scoped Classical
variable {n : ℕ}

def later : AffineExpr→AffineExpr
  | .constant c=>.constant c
  | .reference i=>.reference (i+1)
  | .add a b=>.add (later a) (later b)
  | .scale c a=>.scale c (later a)

theorem evaluate_later {m : ℕ} (e : AffineExpr) (values : Fin m→ℝ) (a : ℝ) :
    (later e).evaluate (Fin.cons a values)=e.evaluate values := by
  induction e with
  | constant c=>rfl
  | reference j=>
    by_cases hj : j<m
    · simp only [later,AffineExpr.evaluate,dite_eq_left hj,dite_eq_left (Nat.succ_lt_succ hj)]
      rfl
    · simp only [later,AffineExpr.evaluate,dite_eq_right hj,dite_eq_right (show ¬j+1<m+1 by omega)]
  | add a b ha hb=>exact congrArg₂ (·+·) ha hb
  | scale c a ha=>exact congrArg ((c:ℝ)*·) ha

theorem evaluate_reference_zero {m : ℕ} (values : Fin m→ℝ) (a : ℝ) :
    (AffineExpr.reference 0).evaluate (Fin.cons a values)=a := by
  change (if h : 0<m+1 then (Fin.cons (α:=fun _ : Fin (m+1)=>ℝ) a values) ⟨0,h⟩ else 0)=a
  rw [dite_eq_left (Nat.zero_lt_succ m)]
  rfl

theorem nodes_later (e : AffineExpr) : (later e).nodes=e.nodes := by
  induction e with
  | constant c=>rfl
  | reference j=>rfl
  | add a b ha hb=>simp only [later,AffineExpr.nodes,ha,hb]
  | scale c a ha=>simp only [later,AffineExpr.nodes,ha]

theorem coefficients_later (e : AffineExpr) (C : ℕ) : (later e).CoefficientsBound C↔e.CoefficientsBound C := by
  induction e with
  | constant c=>rfl
  | reference j=>rfl
  | add a b ha hb=>simp only [later,AffineExpr.CoefficientsBound,ha,hb]
  | scale c a ha=>simp only [later,AffineExpr.CoefficientsBound,ha]

structure Frame (n : ℕ) where
  frozen : Finset (Fin (n+1))
  scales : Fin (n+1)→ℤ
  scales_ne_zero : ∀ i,scales i≠0
  heights : Fin (n+1)→AffineExpr

noncomputable def slice {m : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin m→ℝ) : Set (Fin (n+1)→ℝ) :=
  {y | (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y=0 ∧
    ∀ i∈F.frozen,(F.scales i:ℝ)*y i=(F.heights i).evaluate values}

noncomputable def actualSlice {S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) : Set (Fin (n+1)→ℝ) :=
  {y | (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y=0 ∧
    ∀ i∈F.frozen,((commonDenominator x*F.scales i:ℤ):ℝ)*y i=φ (expression x (F.heights i))}

theorem constraint_iff {S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (y : Fin (n+1)→ℝ) (i : Fin (n+1)) :
    ((commonDenominator x*F.scales i:ℤ):ℝ)*y i=φ (expression x (F.heights i)) ↔
      (F.scales i:ℝ)*y i=(F.heights i).evaluate values := by
  rw [expression_recover x φ values H,Int.cast_mul,mul_assoc]
  exact ⟨mul_left_cancel₀ (Int.cast_ne_zero.mpr (commonDenominator_ne_zero x)),congrArg ((commonDenominator x:ℝ)*·)⟩

theorem actualSlice_eq {S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i) :
    actualSlice x φ F=slice P F values := by
  ext y
  constructor
  · intro h
    exact ⟨h.1,fun i hi=>(constraint_iff x φ F values H y i).mp (h.2 i hi)⟩
  · intro h
    exact ⟨h.1,fun i hi=>(constraint_iff x φ F values H y i).mpr (h.2 i hi)⟩

def advance (F : Frame n) (r : Fin (n+1)) : Frame n where
  frozen := insert r F.frozen
  scales i := if i=r then 1 else F.scales i
  scales_ne_zero i := by split_ifs; exact one_ne_zero; exact F.scales_ne_zero i
  heights i := if i=r then .reference 0 else later (F.heights i)

def coarse (F : Frame n) (r : Fin (n+1)) : Frame n := {F with frozen:=F.frozen.erase r}

theorem advance_rank (F : Frame n) (r : Fin (n+1)) (hr : r∉F.frozen) :
    n+1-(advance F r).frozen.card+1=n+1-F.frozen.card := by
  have H:=FrozenCoordinateOrdering.card_lt F.frozen r hr
  simp only [advance,Finset.card_insert_of_notMem hr]
  omega

theorem slice_advance {m : ℕ} (P : SpatialSource n) (F : Frame n) (r : Fin (n+1)) (hr : r∉F.frozen)
    (values : Fin m→ℝ) (a : ℝ) :
    slice P (advance F r) (Fin.cons a values)=slice P F values∩{y | y r=a} := by
  ext y
  constructor
  · intro h
    have Hnew:=h.2 r (Finset.mem_insert_self r F.frozen)
    have Hcoord : y r=a := by simpa only [advance,ite_true,evaluate_reference_zero,Int.cast_one,one_mul] using Hnew
    refine ⟨⟨h.1,fun i hi=>?_⟩,Hcoord⟩
    have Hne : i≠r := by intro HE; exact hr (HE ▸ hi)
    have Hold:=h.2 i (Finset.mem_insert_of_mem hi)
    simpa only [advance,ite_eq_right Hne,evaluate_later] using Hold
  · rintro ⟨h,Hcoord⟩
    refine ⟨h.1,fun i hi=>?_⟩
    rcases Finset.mem_insert.mp hi with rfl|hi
    · simpa only [advance,ite_true,evaluate_reference_zero,Int.cast_one,one_mul] using (show y i=a from Hcoord)
    · have Hne : i≠r := by intro HE; exact hr (HE ▸ hi)
      simpa only [advance,ite_eq_right Hne,evaluate_later] using h.2 i hi

theorem slice_coarse_advance {m : ℕ} (P : SpatialSource n) (F : Frame n) (r : Fin (n+1)) (hr : r∉F.frozen)
    (values : Fin m→ℝ) (a : ℝ) :
    slice P (coarse (advance F r) r) (Fin.cons a values)=slice P F values := by
  have HF : (coarse (advance F r) r).frozen=F.frozen := by simp only [coarse,advance,Finset.erase_insert hr]
  ext y
  constructor
  · intro h
    refine ⟨h.1,fun i hi=>?_⟩
    have Hne : i≠r := by intro HE; exact hr (HE ▸ hi)
    have Hold:=h.2 i (HF.symm ▸ hi)
    simpa only [coarse,advance,ite_eq_right Hne,evaluate_later] using Hold
  · intro h
    refine ⟨h.1,fun i hi=>?_⟩
    have Hmem : i∈F.frozen := HF ▸ hi
    have Hne : i≠r := by intro HE; exact hr (HE ▸ Hmem)
    simpa only [coarse,advance,ite_eq_right Hne,evaluate_later] using h.2 i Hmem

end LeanCanny.Geometry.IntegralMixedFrozenFrame
