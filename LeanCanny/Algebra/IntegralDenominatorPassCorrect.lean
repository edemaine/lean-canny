/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralDenominatorPassFP

/-! # Integer semantics of the forward denominator pass

The bounded residue table is the pointwise cast of the integer denominator
recurrence, including nonunit leading scalars and arbitrary positive caller
moduli. Only residues are retained by the native FP program.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralDenominatorPass
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

def integerNext (F : Family) (c : List Bool) (i : ℕ) (v : List ℤ) : ℤ :=
  (F.leading c i * (∏ j ∈ Finset.range (F.arity c i), scale v (F.index c i j)) ^ F.degree c i *
    (F.degree c i : ℤ)) ^ F.exponent c i

def integers (F : Family) (c : List Bool) : ℕ → List ℤ
  | 0 => []
  | i + 1 => integerNext F c i (integers F c i) :: integers F c i

theorem integers_length (F : Family) (c : List Bool) (i : ℕ) : (integers F c i).length = i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [integers, List.length_cons, ih]

theorem scale_map {R T : Type*} [One R] [One T] (f : R → T) (hf : f 1 = 1) (v : List R) (j : ℕ) :
    scale (v.map f) j = f (scale v j) := by
  unfold scale
  rw [List.getElem?_map]
  cases v[j]? <;> simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some, hf]

theorem integerNext_cast (F : Family) (c : List Bool) (i : ℕ) (v : List ℤ) :
    (integerNext F c i v : ZMod (F.modulus c)) = next F c i (v.map (Int.castRingHom _)) := by
  simp only [integerNext, next, Int.cast_pow, Int.cast_mul, Int.cast_natCast, Int.cast_prod]
  congr 4
  apply Finset.prod_congr rfl
  intro j _hj
  exact (scale_map (Int.castRingHom _) (map_one _) v (F.index c i j)).symm

theorem values_cast (F : Family) (c : List Bool) (i : ℕ) :
    (pass F).values c i = (integers F c i).map (Int.castRingHom _) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [ModularHistoryPass.Family.values, integers, List.map_cons, ih]
    congr 1
    exact (integerNext_cast F c i _).symm

theorem table_eq (F : Family) (a : Access F) (c : List Bool) :
    ModularHistoryPass.run (pass F) (access F a) c =
      WordList.encode ((integers F c (F.count c)).map (fun (z : ℤ) => residueBits (z : ZMod (F.modulus c)))) := by
  rw [ModularHistoryPass.run_eq, values_cast, List.map_map]
  rfl

theorem reader_eq (F : Family) (a : Access F) (j : List Bool → ℕ) (c : List Bool) :
    ModularHistoryPass.read (pass F) (access F a) j c =
      residueBits (((integers F c (F.count c))[j c]?).getD 0 : ZMod (F.modulus c)) := by
  rw [ModularHistoryPass.read_eq, values_cast, List.map_map, List.getElem?_map]
  change (Option.map (fun z : ℤ => residueBits (z : ZMod (F.modulus c)))
    ((integers F c (F.count c))[j c]?)).getD [] = _
  cases (integers F c (F.count c))[j c]? with
  | none =>
    simp only [Option.map_none, Option.getD_none, Int.cast_zero]
    exact ArithmeticBits.zero_residueBits _
  | some z => rfl

theorem integer_reader_FP (F : Family) (a : Access F) (j : List Bool → ℕ) (hj : BinaryFn j) :
    (fun c => residueBits (((integers F c (F.count c))[j c]?).getD 0 : ZMod (F.modulus c))) ∈ FP :=
  mem_FP_of_eq (reader_FP F a j hj) (reader_eq F a j)

end LeanCanny.Algebra.IntegralDenominatorPass
