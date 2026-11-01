/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CommonIntegerDenominator
public import LeanCanny.Algebra.ModularScalarFP
public import LeanCanny.Algebra.IntegralCoefficientBlocks
public import LeanCanny.Algebra.ModularFoldFP
public import LeanCanny.Computation.ControllerRequests

/-! # Common-denominator residues and recursive scaled height entries

A unary scan multiplies integer scales, omitting the selected coordinate
for its cofactor. All multiplication is reduced modulo the caller modulus;
no inverse is used. A single recursive numerator entry is scaled locally.
-/

@[expose] public section
namespace LeanCanny.Algebra.CommonHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

structure Scalars where
  count : List Bool → ℕ
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0
  scale : List Bool → ℕ → ℤ
  selected : List Bool → ℕ

structure Access (F : Scalars) where
  count : UnaryFn F.count
  modulus : BinaryFn F.modulus
  selected : BinaryFn F.selected
  scalar : List Bool → List Bool
  scalar_FP : scalar ∈ FP
  scalar_eq : ∀ c i, i < F.count c → scalar (pair c (BinaryNatCode.encode i)) = residueBits (F.scale c i : ZMod (F.modulus c))

def Scalars.denominator (F : Scalars) (c : List Bool) : ℤ := ∏ i ∈ Finset.range (F.count c), F.scale c i
def Scalars.cofactor (F : Scalars) (c : List Bool) : ℤ :=
  ∏ i ∈ Finset.range (F.count c), if i = F.selected c then 1 else F.scale c i

noncomputable def cofactorTerm (F : Scalars) (a : Access F) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd p) = F.selected (pairFst p) then
    ArithmeticBits.one (BinaryNatCode.encode (F.modulus (pairFst p))) else a.scalar p

theorem cofactorTerm_FP (F : Scalars) (a : Access F) : cofactorTerm F a ∈ FP := by
  have HM : BinaryFn (fun p => F.modulus (pairFst p)) := a.modulus.comp pairFst_mem_FP
  exact ((BinaryFn.fromBits pairSnd_mem_FP).eq (a.selected.comp pairFst_mem_FP)).ite_mem_FP
    (mem_FP_comp (g := ArithmeticBits.one) HM.bits_mem_FP ArithmeticBits.one_mem_FP) a.scalar_FP

theorem cofactorTerm_packet (F : Scalars) (a : Access F) (c : List Bool) (i : ℕ) (hi : i < F.count c) :
    cofactorTerm F a (pair c (BinaryNatCode.encode i)) =
      residueBits ((if i = F.selected c then 1 else F.scale c i : ℤ) : ZMod (F.modulus c)) := by
  have HE : Nat.fromBitsLE (BinaryNatCode.encode i) = i := Nat.fromBitsLE_bits i
  simp only [cofactorTerm, pairFst_pair, pairSnd_pair, HE]
  split_ifs
  · simpa only [Int.cast_one] using ArithmeticBits.one_residueBits (F.modulus c)
  · exact a.scalar_eq c i hi

theorem denominator_FP (F : Scalars) (a : Access F) :
    (fun c => residueBits (F.denominator c : ZMod (F.modulus c))) ∈ FP := by
  have H := ModularProduct.evaluatorWithModulus_FP a.scalar (fun c => BinaryNatCode.encode (F.modulus c)) F.count
    a.scalar_FP a.modulus.bits_mem_FP a.count F.modulus (funext fun _ => Nat.fromBitsLE_bits _)
    (fun c i => (F.scale c i : ZMod (F.modulus c))) (fun c => Nat.pos_of_ne_zero (F.modulus_ne_zero c)) a.scalar_eq
  exact mem_FP_of_eq H (fun c => by rw [← Int.cast_prod]; rfl)

theorem cofactor_FP (F : Scalars) (a : Access F) :
    (fun c => residueBits (F.cofactor c : ZMod (F.modulus c))) ∈ FP := by
  have H := ModularProduct.evaluatorWithModulus_FP (cofactorTerm F a) (fun c => BinaryNatCode.encode (F.modulus c)) F.count
    (cofactorTerm_FP F a) a.modulus.bits_mem_FP a.count F.modulus (funext fun _ => Nat.fromBitsLE_bits _)
    (fun c i => ((if i = F.selected c then 1 else F.scale c i : ℤ) : ZMod (F.modulus c)))
    (fun c => Nat.pos_of_ne_zero (F.modulus_ne_zero c)) (cofactorTerm_packet F a)
  exact mem_FP_of_eq H (fun c => by rw [← Int.cast_prod]; rfl)

theorem cofactor_eq_erase (N : ℕ) (scale : ℕ → ℤ) (i : Fin N) :
    (∏ j ∈ Finset.range N, if j = i.val then 1 else scale j) =
      CommonIntegerDenominator.denominator (Finset.univ.erase i) (fun j : Fin N => scale j.val) := by
  rw [Finset.prod_range]
  change (∏ j : Fin N, if j.val = i.val then 1 else scale j.val) = _
  simp only [Fin.val_inj]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [ite_true, mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  exact ite_eq_right (Finset.mem_erase.mp hj).1

structure Source extends Scalars where
  rank : List Bool → ℕ
  carrier : List Bool → Type
  ring : ∀ c, CommRing (carrier c)
  basis : ∀ c, @Module.Basis (Fin (rank c)) ℤ (carrier c) _ _ ((ring c).toIntAlgebra.toModule)
  numerator : ∀ c, carrier c
  row : ∀ c, Fin (rank c)
  col : ∀ c, Fin (rank c)

noncomputable def Source.rawValue (S : Source) (c : List Bool) : List Bool := by
  let := S.ring c
  exact residueBits ((Algebra.leftMulMatrix (S.basis c) (S.numerator c) (S.row c) (S.col c) : ℤ) : ZMod (S.modulus c))

noncomputable def Source.value (S : Source) (c : List Bool) : List Bool := by
  let := S.ring c
  exact residueBits ((Algebra.leftMulMatrix (S.basis c)
    (S.numerator c * (S.toScalars.cofactor c : S.carrier c)) (S.row c) (S.col c) : ℤ) : ZMod (S.modulus c))

theorem numerator_matrix {A : Type*} [CommRing A] {N : ℕ} (b : Module.Basis (Fin N) ℤ A) (x : A) (z : ℤ) (r t : Fin N) :
    Algebra.leftMulMatrix b (x * (z : A)) r t = z * Algebra.leftMulMatrix b x r t := by
  rw [mul_comm x, ← zsmul_eq_mul, map_zsmul, Matrix.smul_apply, zsmul_eq_mul]
  simp only [Int.cast_id]

noncomputable def finish (S : Source) (z : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (BinaryNatCode.encode (S.modulus (pairFst z)))
    (pair (residueBits (S.toScalars.cofactor (pairFst z) : ZMod (S.modulus (pairFst z)))) (pairSnd z)))

theorem finish_FP (S : Source) (a : Access S.toScalars) : finish S ∈ FP := by
  have HM : BinaryFn (fun z => S.modulus (pairFst z)) := a.modulus.comp pairFst_mem_FP
  exact mem_FP_comp (mem_FP_pair HM.bits_mem_FP (mem_FP_pair
    (mem_FP_comp pairFst_mem_FP (cofactor_FP S.toScalars a)) pairSnd_mem_FP)) BinaryNat.mulMod_mem_FP

theorem finish_value (S : Source) (c : List Bool) : finish S (pair c (S.rawValue c)) = S.value c := by
  let := S.ring c
  unfold finish
  rw [pairFst_pair, pairSnd_pair]
  unfold Source.rawValue Source.value
  dsimp only
  calc
    _ = residueBits ((S.cofactor c : ZMod (S.modulus c)) *
        ((Algebra.leftMulMatrix (S.basis c) (S.numerator c) (S.row c) (S.col c) : ℤ) : ZMod (S.modulus c))) :=
      ArithmeticBits.mulMod_residueBits _ _ _
    _ = _ := by rw [numerator_matrix, Int.cast_mul]

noncomputable def program (S : Source) (present : List Bool → Bool) (task : List Bool → List Bool) : SingleCall.Program where
  request := present
  query := task
  immediate _ := []
  finish := finish S

theorem controls (S : Source) (a : Access S.toScalars) (present : List Bool → Bool) (hp : (fun c => [present c]) ∈ FP)
    (task : List Bool → List Bool) (ht : task ∈ FP) : (program S present task).Controls :=
  ⟨hp, ht, constFn_mem_FP [], finish_FP S a⟩

attribute [local irreducible] Source.rawValue Source.value

theorem program_value (S : Source) (present : List Bool → Bool) (task answer : List Bool → List Bool)
    (he : ∀ c, present c = true → answer (task c) = S.rawValue c)
    (hz : ∀ c, present c = false → letI := S.ring c; S.numerator c = 0) (c : List Bool) :
    (program S present task).value answer c = S.value c := by
  cases h : present c
  · simp only [SingleCall.Program.value, program, h, Bool.false_eq_true, ite_false]
    let := S.ring c
    unfold Source.value
    dsimp only
    rw [hz c h, zero_mul, map_zero, Matrix.zero_apply, Int.cast_zero]
    simp [residueBits, ZMod.val_zero, BinaryNatCode.encode]
  · simp only [SingleCall.Program.value, program, h, ite_true, he c h]
    exact finish_value S c

theorem requests_iff (S : Source) (present : List Bool → Bool) (task answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (c child : List Bool) :
    (program S present task).controller.Requests answer budget c child ↔ present c = true ∧ child = task c :=
  SingleCall.Program.requests_iff _ _ _ c child

end LeanCanny.Algebra.CommonHeightBits
