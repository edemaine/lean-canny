/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.SymbolicRootCurveOrder

/-! # Ordered transport and ranks of original scalar roots

The explicit exceptional factor supplies an order isomorphism between any
two original scalar fibers in a retained interval. Every continuous original
root branch follows that isomorphism. Consequently its ordinal among distinct
real roots is constant, even when the original polynomial has multiplicities.
-/

@[expose] public section
namespace LeanCanny.Geometry.ScalarRootTransport
open Set LeanCanny.Algebra
open SymbolicScaledSquarefree (Coefficient scalarEvaluation exceptional)
open scoped Classical

abbrev Root (p : Polynomial Coefficient) (t : ℝ) :=
  {x : ℝ // p.eval₂ (scalarEvaluation t) x = 0}

noncomputable def rank (p : Polynomial Coefficient) (t y : ℝ) : ℕ :=
  Nat.card {x : Root p t // x.val < y}

theorem finite_card_root (p : Polynomial Coefficient) (t : ℝ)
    (ht : scalarEvaluation t (exceptional p) ≠ 0) :
    Finite (Root p t) ∧ Nat.card (Root p t) ≤ p.natDegree := by
  have hl := (SymbolicScaledSquarefree.exceptional_conditions (scalarEvaluation t) p ht).1
  have hn : p.map (scalarEvaluation t) ≠ 0 := by
    intro hz
    have h := congrArg Polynomial.leadingCoeff hz
    rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hl, Polynomial.leadingCoeff_zero] at h
    exact hl h
  let roots := (p.map (scalarEvaluation t)).roots.toFinset
  let enc : Root p t → {x // x ∈ roots} := fun x =>
    ⟨x.val, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hn).mpr (by
      change (p.map (scalarEvaluation t)).eval x.val = 0
      rw [Polynomial.eval_map]
      exact x.property))⟩
  have hi : Function.Injective enc := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : {x // x ∈ roots} => z.val) he)
  refine ⟨Finite.of_injective enc hi, ?_⟩
  calc
    Nat.card (Root p t) ≤ Nat.card {x // x ∈ roots} := Nat.card_le_card_of_injective enc hi
    _ = roots.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ (p.map (scalarEvaluation t)).natDegree :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
    _ ≤ p.natDegree := Polynomial.natDegree_map_le

theorem rank_lt_degree (p : Polynomial Coefficient) (t y : ℝ)
    (ht : scalarEvaluation t (exceptional p) ≠ 0) (hy : p.eval₂ (scalarEvaluation t) y = 0) :
    rank p t y < p.natDegree := by
  have h := finite_card_root p t ht
  have : Finite (Root p t) := h.1
  let := Fintype.ofFinite (Root p t)
  have hr : rank p t y < Nat.card (Root p t) := by
    rw [rank, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_lt (x := (⟨y, hy⟩ : Root p t)) (lt_irrefl y)
  exact hr.trans_le h.2

theorem rank_lt_rank (p : Polynomial Coefficient) (t x y : ℝ)
    (ht : scalarEvaluation t (exceptional p) ≠ 0) (hx : p.eval₂ (scalarEvaluation t) x = 0)
    (hxy : x < y) : rank p t x < rank p t y := by
  have : Finite (Root p t) := (finite_card_root p t ht).1
  let := Fintype.ofFinite (Root p t)
  let incl : {z : Root p t // z.val < x} → {z : Root p t // z.val < y} :=
    fun z => ⟨z.val, z.property.trans hxy⟩
  have hi : Function.Injective incl := by
    intro u v h
    exact Subtype.ext (congrArg (fun z : {z : Root p t // z.val < y} => z.val) h)
  have hn : (⟨⟨x, hx⟩, hxy⟩ : {z : Root p t // z.val < y}) ∉ Set.range incl := by
    rintro ⟨z, hz⟩
    have he := congrArg (fun u : {z : Root p t // z.val < y} => u.val.val) hz
    have hl := z.property
    change z.val.val = x at he
    exact (ne_of_lt hl) he
  rw [rank, rank, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_of_notMem incl hi hn

theorem rank_injective (p : Polynomial Coefficient) (t : ℝ)
    (ht : scalarEvaluation t (exceptional p) ≠ 0) :
    Function.Injective (fun x : Root p t => rank p t x.val) := by
  intro x y he
  apply Subtype.ext
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact (ne_of_lt (rank_lt_rank p t x.val y.val ht x.property hlt)) he
  · exact (ne_of_lt (rank_lt_rank p t y.val x.val ht y.property hgt)) he.symm

theorem exists_orderIso (p : Polynomial Coefficient) {a b : ℝ}
    (havoid : ∀ t ∈ Ioo a b, scalarEvaluation t (exceptional p) ≠ 0) (s t : Ioo a b) :
    ∃ e : Root p s.val ≃o Root p t.val,
      ∀ (f : C(Ioo a b, Fin 1 → ℝ)) (hf : ∀ u, p.eval₂ (scalarEvaluation u.val) (f u 0) = 0),
        (e ⟨f s 0, hf s⟩).val = f t 0 := by
  let H := SymbolicUnivariateRootFamily.value (SymbolicScaledSquarefree.polynomial p)
  have hcover := SymbolicRootCurveOrder.covering p a b havoid
  obtain ⟨curve, _, hroot, hcomplete⟩ := RootBranches.exists_anchored_branches_of_covering H a b s hcover
  have horiginal (j : RootBranches.Index H a b s) (u : Ioo a b) :
      p.eval₂ (scalarEvaluation u.val) (curve j u 0) = 0 := by
    apply (SymbolicUnivariateRootFamily.value_zero_iff p u.val _).mp
    exact (SymbolicUnivariateRootFamily.roots_away p u.val _ (havoid _ u.property)).mpr (hroot j u)
  let read (u : Ioo a b) (j : RootBranches.Index H a b s) : Root p u.val :=
    ⟨curve j u 0, horiginal j u⟩
  have hbij (u : Ioo a b) : Function.Bijective (read u) := by
    constructor
    · intro j k he
      have hv : curve j u = curve k u := by
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        simpa only [hi] using congrArg Subtype.val he
      obtain ⟨l, _, huniq⟩ := (hcomplete u (curve j u)).mp (hroot j u)
      exact (huniq j rfl).trans (huniq k hv.symm).symm
    · intro x
      have hx : H (u.val, fun _ => x.val) = 0 :=
        (SymbolicUnivariateRootFamily.roots_away p u.val _ (havoid _ u.property)).mp
          ((SymbolicUnivariateRootFamily.value_zero_iff p u.val _).mpr x.property)
      obtain ⟨j, hj, _⟩ := (hcomplete u (fun _ => x.val)).mp hx
      exact ⟨j, Subtype.ext (congrFun hj 0)⟩
  let eqv (u : Ioo a b) := Equiv.ofBijective (read u) (hbij u)
  let transport := (eqv s).symm.trans (eqv t)
  have hread (u : Ioo a b) (j : RootBranches.Index H a b s) : (eqv u j).val = curve j u 0 := rfl
  have hcompare (j k : RootBranches.Index H a b s) : curve j s 0 ≤ curve k s 0 ↔ curve j t 0 ≤ curve k t 0 := by
    have h := (SymbolicRootCurveOrder.coordinate_comparison_iff p havoid (curve k) (curve j) 0
      (horiginal k) (horiginal j) s t).2
    simpa only [not_lt] using not_congr h
  let e : Root p s.val ≃o Root p t.val :=
    { toEquiv := transport
      map_rel_iff' := by
        intro x y
        have hx := (eqv s).apply_symm_apply x
        have hy := (eqv s).apply_symm_apply y
        change curve ((eqv s).symm x) t 0 ≤ curve ((eqv s).symm y) t 0 ↔ x.val ≤ y.val
        have h := (hcompare ((eqv s).symm x) ((eqv s).symm y)).symm
        simpa only [← hread, hx, hy] using h }
  refine ⟨e, ?_⟩
  intro f hf
  let x : Root p s.val := ⟨f s 0, hf s⟩
  let j := (eqv s).symm x
  have hj : curve j s 0 = f s 0 := congrArg Subtype.val ((eqv s).apply_symm_apply x)
  have haux (u : Ioo a b) : H (u.val, f u) = 0 :=
    (SymbolicUnivariateRootFamily.roots_away p u.val _ (havoid _ u.property)).mp
      ((SymbolicUnivariateRootFamily.value_zero_iff p u.val _).mpr (hf u))
  have he : curve j = f := RootBranches.curves_eq_of_anchor H hcover (curve j) f (hroot j) haux s (by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using hj)
  change curve j t 0 = f t 0
  exact congrArg (fun g : C(Ioo a b, Fin 1 → ℝ) => g t 0) he

theorem rank_eq (p : Polynomial Coefficient) {a b : ℝ}
    (havoid : ∀ t ∈ Ioo a b, scalarEvaluation t (exceptional p) ≠ 0)
    (f : C(Ioo a b, Fin 1 → ℝ)) (hf : ∀ u, p.eval₂ (scalarEvaluation u.val) (f u 0) = 0)
    (s t : Ioo a b) : rank p s.val (f s 0) = rank p t.val (f t 0) := by
  obtain ⟨e, he⟩ := exists_orderIso p havoid s t
  let x : Root p s.val := ⟨f s 0, hf s⟩
  have hx : (e x).val = f t 0 := he f hf
  let eb : {y : Root p s.val // y.val < f s 0} ≃ {y : Root p t.val // y.val < f t 0} :=
    e.toEquiv.subtypeEquiv (fun y => by
      change y < x ↔ (e y).val < f t 0
      rw [← hx]
      exact e.lt_iff_lt.symm)
  exact Nat.card_congr eb

end LeanCanny.Geometry.ScalarRootTransport
