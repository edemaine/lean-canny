/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameCutCard

/-! # Actual physical critical sections have an original-width product bound

Each free coordinate satisfies its actual relative eliminant over the same
old hom. Frozen coordinates are recovered literally. Singular/repeated
roots are included; no squarefree or regularity premise is required.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set Polynomial
open IntegralMixedSelectedGeometry IntegralMixedSelectedPhysicalFiber
open scoped Classical BigOperators
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem physical_coordinate_root (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (a : physical x hm r φ t) (j : Free r) :
    ((selected x hm r j φ).map (Polynomial.evalRingHom t)).eval
      (a.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j))=0 := by
  rw [Polynomial.eval_map]
  have HS:=a.property.2 (objective r)
  rw [IntegralMixedSweepRows.integerRow,ite_eq_left rfl] at HS
  apply coordinate_root x hm r j φ t a.val a.property.1 HS
  intro i hi
  have HG:=a.property.2 i
  rw [IntegralMixedSweepRows.integerRow,ite_eq_right hi] at HG
  exact HG

theorem physical_finite_card (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) :
    Finite (physical x hm r φ t) ∧ Nat.card (physical x hm r φ t)≤2^(B*(n+1)) := by
  let p (j : Free r):=(selected x hm r j φ).map (Polynomial.evalRingHom t)
  let R (j : Free r):={a : ℝ //a∈(p j).roots.toFinset}
  have HD (j : Free r) : (p j).natDegree=PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree:=
    specialized_degree x hm r j φ t
  have HP (j : Free r) : p j≠0 := by
    intro Hzero
    have HE:=HD j
    rw [Hzero,Polynomial.natDegree_zero] at HE
    have Hpos : 0<PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree:=
      pow_pos (Nat.two_pow_pos _) _
    omega
  let enc : physical x hm r φ t→∀ j,R j:=fun a j=>
    ⟨a.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j),
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (HP j)).mpr (physical_coordinate_root x hm r φ t a j))⟩
  have HE : Function.Injective enc := by
    intro a b Hab
    have HF : freeCoordinates r a.val=freeCoordinates r b.val := by
      funext j
      exact congrArg Subtype.val (congrFun Hab j)
    apply Subtype.ext
    calc
      _=IntegralMixedSweepRows.point x hm r φ t (freeCoordinates r a.val):=(reconstruct x hm r φ t a.val a.property.1).symm
      _=IntegralMixedSweepRows.point x hm r φ t (freeCoordinates r b.val):=congrArg (IntegralMixedSweepRows.point x hm r φ t) HF
      _=b.val:=reconstruct x hm r φ t b.val b.property.1
  have HR (j : Free r) : Nat.card (R j)≤2^B := by
    change Nat.card {a : ℝ //a∈(p j).roots.toFinset}≤_
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    apply (Multiset.toFinset_card_le _).trans
    apply (Polynomial.card_roots' _).trans
    rw [HD]
    exact criticalDegree_cap x hm r.critical
  refine ⟨Finite.of_injective enc HE,(Nat.card_le_card_of_injective enc HE).trans ?_⟩
  rw [Nat.card_pi]
  calc
    _≤∏ _j : Free r,2^B:=Finset.prod_le_prod (fun j _=>HR j)
    _=(2^B)^(n-r.critical.offset.val+1):=by simp only [Free,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    _≤(2^B)^(n+1):=Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by decide : 1≤2)) (by omega)
    _=2^(B*(n+1)):=by rw [←pow_mul]

end LeanCanny.Geometry.IntegralMixedFrozenFrame
