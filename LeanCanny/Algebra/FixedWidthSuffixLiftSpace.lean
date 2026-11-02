/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthHeadLiftSpace
public import LeanCanny.Algebra.UniformIntegralPowerSchedule
/-! # Native coefficient access on a literal terminal suffix

Adjoining any unary number of unused newer variables preserves one old
coefficient query. The original polynomial is read only after every new
head exponent has been checked to be zero. Evaluation uses the tail of
the same joint tuple, without choosing or resampling old roots.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthSuffixLiftBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def shift (d : ℕ) {a : ℕ} (i : Fin a) : Fin (d+a) := ⟨d+i.val,by omega⟩

theorem shift_injective (d a : ℕ) : Function.Injective (shift d : Fin a→Fin (d+a)) := by
  intro i j hij
  apply Fin.ext
  have H:=congrArg Fin.val hij
  change d+i.val=d+j.val at H
  omega

theorem range_shift {d a : ℕ} (j : Fin (d+a)) : j∈Set.range (shift d : Fin a→Fin (d+a)) ↔ d≤j.val := by
  constructor
  · rintro ⟨i,rfl⟩
    exact Nat.le_add_right _ _
  · intro hj
    refine ⟨⟨j.val-d,by omega⟩,?_⟩
    apply Fin.ext
    simp only [shift]
    omega

theorem support_shift {d a : ℕ} (e : Fin (d+a)→₀ℕ) :
    (↑e.support : Set (Fin (d+a)))⊆Set.range (shift d : Fin a→Fin (d+a)) ↔
      ∀ i : Fin d,e ⟨i.val,by omega⟩=0 := by
  constructor
  · intro h i
    by_contra hi
    have HI:=i.isLt
    have H:= (range_shift ⟨i.val,by omega⟩).mp (h (Finsupp.mem_support_iff.mpr hi))
    change d ≤ i.val at H
    omega
  · intro h j hj
    apply range_shift j |>.mpr
    by_contra H
    have hi:j.val<d:=by omega
    have HZ:=h ⟨j.val,hi⟩
    have HE : (⟨(⟨j.val,hi⟩ : Fin d).val,by omega⟩ : Fin (d+a))=j := by apply Fin.ext; rfl
    rw [HE] at HZ
    exact (Finsupp.mem_support_iff.mp hj) HZ

theorem rename_coefficient {d a : ℕ} (p : MvPolynomial (Fin a) ℤ) (e : Fin (d+a)→₀ℕ) :
    (rename (shift d) p).coeff e=
      if ∀ i : Fin d,e ⟨i.val,by omega⟩=0 then p.coeff (e.comapDomain (shift d) (shift_injective d a).injOn) else 0 := by
  rw [EmbeddedCoefficient.coeff_rename (shift d) (shift_injective d a)]
  simp only [EmbeddedCoefficient.value,support_shift]

def spatial (D W : List Bool→ℕ) (target : List Bool→List Bool) (c : List Bool) :=
  BinaryNat.normalize ((target c).drop (D c*W c))

theorem spatial_FP (D W : List Bool→ℕ) (target : List Bool→List Bool)
    (hD : UnaryFn D) (hW : UnaryFn W) (ht : target∈FP) : spatial D W target∈FP :=
  mem_FP_comp (drop_mem_FP ht (hD.mul hW)) BinaryNat.normalize_mem_FP

private theorem entry_fromBits (w : ℕ) (bits : List Bool) (i : ℕ) :
    entry w (Nat.fromBitsLE bits) i=Nat.fromBitsLE ((bits.drop (i*w)).take w) := by
  rw [entry_eq_digit,BinaryNat.value_take,drop_value]

theorem tail_nativeExponent (a d w : ℕ) (bits : List Bool) :
    (nativeExponent (Equiv.refl (Fin (d+a))) w (Nat.fromBitsLE bits)).comapDomain
      (shift d) (shift_injective d a).injOn=
      nativeExponent (Equiv.refl (Fin a)) w (Nat.fromBitsLE (BinaryNat.normalize (bits.drop (d*w)))) := by
  ext i
  simp only [Finsupp.comapDomain_apply,nativeExponent,Finsupp.coe_equivFunOnFinite_symm,Equiv.refl_apply,
    shift,BinaryNat.normalize_eq_bits,Nat.fromBitsLE_bits]
  rw [entry_fromBits,entry_fromBits,List.drop_drop]
  congr 2
  simp only [Nat.add_mul]

theorem head_zero_iff (D A W : List Bool→ℕ) (target : List Bool→List Bool) (c : List Bool) :
    FixedWidthQuery.Bounded D W target (fun _=>0) c ↔
      ∀ i : Fin (D c),nativeExponent (Equiv.refl (Fin (D c+A c))) (W c) (Nat.fromBitsLE (target c)) ⟨i.val,by omega⟩=0 := by
  have hv (i : Fin (D c)) :
      nativeExponent (Equiv.refl (Fin (D c+A c))) (W c) (Nat.fromBitsLE (target c)) ⟨i.val,by omega⟩=
      FixedWidthQuery.coordinate W target c i.val := FixedWidthBlockRenameBits.entry_bits _ _ _
  constructor
  · intro h i
    rw [hv]
    exact Nat.eq_zero_of_le_zero (h i.val i.isLt)
  · intro h i hi
    have HX:=h ⟨i,hi⟩
    rw [hv] at HX
    exact HX.le

theorem evaluator (D A W : List Bool→ℕ) (p : (c : List Bool)→MvPolynomial (Fin (A c)) ℤ)
    (target modulus : List Bool→List Bool) (hD : UnaryFn D) (hW : UnaryFn W) (ht : target∈FP)
    (E : SpaceFunction (FixedWidthRowBits.value A W p (spatial D W target) modulus)) :
    SpaceFunction (FixedWidthRowBits.value (fun c=>D c+A c) W (fun c=>rename (shift (D c)) (p c)) target modulus) := by
  have HG:=FixedWidthQuery.bounded_fppred hD hW (UnaryFn.const 0) ht
  have H:=SpaceFunction.branch (fun c=>decide (FixedWidthQuery.Bounded D W target (fun _=>0) c)) HG.flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  apply H.congr
  funext c
  unfold FixedWidthRowBits.value
  rw [rename_coefficient,tail_nativeExponent]
  simp only [←head_zero_iff D A W target c]
  by_cases hz:FixedWidthQuery.Bounded D W target (fun _=>0) c
  · simp only [hz,decide_true,ite_true,spatial]
  · simp only [hz,decide_false,Bool.false_eq_true,ite_false,Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

theorem evaluation {d a : ℕ} (p : MvPolynomial (Fin a) ℤ) (z : Fin (d+a)→ℝ) :
    (rename (shift d) p).eval₂ (Int.castRingHom ℝ) z=p.eval₂ (Int.castRingHom ℝ) (fun i=>z (shift d i)) := by
  rw [eval₂_rename]
  rfl

theorem shift_weights (S N a d : ℕ) (i : Fin a) :
    UniformIntegralPowerSchedule.weights S N (d+a) (shift d i)=UniformIntegralPowerSchedule.weights S N a i := by
  have H:=UniformIntegralPowerSchedule.old_embed S N (show a≤d+a by omega) i
  have HE:UniformIntegralPowerSchedule.embed (show a≤d+a by omega) i=shift d i := by
    apply Fin.ext
    simp only [UniformIntegralPowerSchedule.embed,shift]
    omega
  rw [HE] at H
  exact H

end LeanCanny.Algebra.FixedWidthSuffixLiftBits
