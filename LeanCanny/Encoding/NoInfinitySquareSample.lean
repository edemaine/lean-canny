/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.AffineFiniteCoordinates
public import LeanCanny.Encoding.SquareSampleComplete
public import LeanCanny.Encoding.SquareSampleAccess

/-! # Complete square sampling from literal finite affine rows

Positive square systems carry exact advertised row degrees and exclusion at
infinity. The reciprocal Gram annihilators retain all roots, including singular
ones. Their height allowance is derived from original row mass, not supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.NoInfinitySquareSample
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical

structure Family where
  count : List Bool→ℕ
  degree : List Bool→ℕ
  mass : List Bool→ℕ
  rowDegree : List Bool→ℕ→ℕ
  rows : (u : List Bool)→Fin (count u)→MvPolynomial (Fin (count u)) ℤ
  count_pos : ∀ u, 0<count u
  degree_pos : ∀ u, 0<degree u
  row_degree : ∀ u i, (rows u i).totalDegree≤rowDegree u i.val
  rowDegree_pos : ∀ u (i : Fin (count u)), 0<rowDegree u i.val
  rowDegree_le : ∀ u (i : Fin (count u)), rowDegree u i.val≤degree u
  row_mass : ∀ u i, MvMass.mass (rows u i)≤2^mass u
  noInfinity : ∀ u, AffineFiniteCoordinates.NoInfinity (rows u) (fun i=>rowDegree u i.val)

def width (F : Family) (u : List Bool) : ℕ := AffineFiniteCoordinates.width (fun i : Fin (F.count u)=>F.rowDegree u i.val)
def dimension (F : Family) (u : List Bool) : ℕ := AffineFiniteCoordinates.dimension (fun i : Fin (F.count u)=>F.rowDegree u i.val)
def annDegree (F : Family) (u : List Bool) : ℕ := dimension F u+1
def annHeight (F : Family) (u : List Bool) : ℕ :=
  (dimension F u).size*dimension F u+dimension F u*(F.mass u+1)+1

noncomputable def polynomial (F : Family) (u : List Bool) (i : Fin (F.count u)) : Polynomial ℤ :=
  AffineFiniteCoordinates.annihilator (F.rows u) (fun j=>F.rowDegree u j.val) i

theorem polynomial_height (F : Family) (u : List Bool) (i : Fin (F.count u)) (j : ℕ) :
    ((polynomial F u i).coeff j).natAbs.size≤annHeight F u := by
  let N := dimension F u
  let b := F.mass u+1
  have hM : 2≤2^b := by simpa only [pow_one] using Nat.pow_le_pow_right (n:=2) (by decide) (show 1≤b by omega)
  have HM := AffineFiniteCoordinates.mass_le (F.rows u) (fun j=>F.rowDegree u j.val) (2^b) hM
    (fun k e=>(MvMass.coeff_le _ _).trans ((F.row_mass u k).trans
      (Nat.pow_le_pow_right (n:=2) (by decide) (show F.mass u≤b by omega)))) i
  have HF : N.factorial≤2^(N.size*N) := (Nat.factorial_le_pow N).trans
    ((Nat.pow_le_pow_left (Nat.lt_size_self N).le N).trans_eq (pow_mul _ _ _).symm)
  have HB : ((polynomial F u i).coeff j).natAbs≤2^(N.size*N+N*b) := by
    calc
      _ ≤ coefficientMass (polynomial F u i) := coeff_natAbs_le_coefficientMass _ _
      _ ≤ N.factorial*(2^b)^N := HM
      _ ≤ 2^(N.size*N)*(2^b)^N := Nat.mul_le_mul_right _ HF
      _ = _ := by rw [←pow_mul,←pow_add,Nat.mul_comm b]
  simpa only [annHeight,N,b,Nat.size_pow] using Nat.size_le_size HB

noncomputable def input (F : Family) : SquareSampleInput.Inputs where
  count := F.count
  degree := F.degree
  mass := F.mass
  system := F.rows
  count_pos := F.count_pos
  degree_pos := F.degree_pos
  system_degree u i := (F.row_degree u i).trans (F.rowDegree_le u i)
  system_mass := F.row_mass
  annihilator := polynomial F
  annDegree := annDegree F
  annHeight := annHeight F
  ann_nonzero u i := AffineFiniteCoordinates.ne_zero _ _ (F.rowDegree_pos u) (F.noInfinity u) i
  ann_degree _ i := AffineFiniteCoordinates.degree_le _ _ i
  ann_height := polynomial_height F
  ann_root u z hz _ i := AffineFiniteCoordinates.eval_eq_zero _ _ (F.row_degree u) z hz i

theorem complete (F : Family) : SquareSampleComplete.Complete (input F) :=
  fun u z hz i=>AffineFiniteCoordinates.eval_eq_zero _ _ (F.row_degree u) z hz i

structure Access (F : Family) : Prop where
  count : UnaryFn F.count
  degree : BinaryFn F.degree
  mass : BinaryFn F.mass
  rowDegree : BinaryFn (fun q=>F.rowDegree (pairFst q) (Nat.fromBitsLE (pairSnd q)))
  row : SpaceFunction (SquareSampleInput.rowCoefficient (input F))

noncomputable abbrev comp (F : Family) (f : List Bool→List Bool) : Family where
  count := F.count ∘ f
  degree := F.degree ∘ f
  mass := F.mass ∘ f
  rowDegree u := F.rowDegree (f u)
  rows u := F.rows (f u)
  count_pos u := F.count_pos (f u)
  degree_pos u := F.degree_pos (f u)
  row_degree u := F.row_degree (f u)
  rowDegree_pos u := F.rowDegree_pos (f u)
  rowDegree_le u := F.rowDegree_le (f u)
  row_mass u := F.row_mass (f u)
  noInfinity u := F.noInfinity (f u)

theorem input_comp (F : Family) (f : List Bool→List Bool) : input (comp F f)=SquareSampleInput.comp (input F) f := rfl

theorem access_comp {F : Family} (h : Access F) {f : List Bool→List Bool} (hf : f∈FP) : Access (comp F f) := by
  refine ⟨h.count.comp hf,h.degree.comp hf,h.mass.comp hf,?_,?_⟩
  · exact BinaryFn.of_eq (h.rowDegree.comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) pairSnd_mem_FP))
      (fun q=>by simp only [Function.comp_apply,pairFst_pair,pairSnd_pair])
  · rw [input_comp]
    exact (h.row.precompose _ (SquareSampleInput.mapSource_FP hf)).congr
      (funext fun q=>(SquareSampleInput.row_comp (input F) f q).symm)

end LeanCanny.Encoding.NoInfinitySquareSample
