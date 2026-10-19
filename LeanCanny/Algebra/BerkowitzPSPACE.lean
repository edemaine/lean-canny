/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzSuspendedBounds

/-!
# Polynomial-space modular determinant zero testing

The input describes a matrix over a nonzero, varying modulus through FP field
and original-entry access. The dimension may be exponential in the input length.
Factor entries are computed by suspended polynomial-space children; their whole
computation is not assumed to be FP.
-/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz
open Complexity
open LeanCanny.Encoding
open MatrixPower
open LeanCanny.Computation

structure ModularFamily where
  dimension : List Bool → ℕ
  modulus : List Bool → ℕ
  matrix : (c : List Bool) → Matrix (Fin (dimension c)) (Fin (dimension c)) (ZMod (modulus c))
  modulus_ne_zero : ∀ c, modulus c ≠ 0

def ModularFamily.zeroLanguage (F : ModularFamily) : Language := {c | (F.matrix c).det = 0}

/-- Canonical access on every input context. A concrete encoding must provide
validation or defaults satisfying this contract. -/
structure ModularAccess (F : ModularFamily) where
  access : FactorChild.Access
  correct : ∀ c, FactorChild.CorrectAt access c (F.modulus c) (F.matrix c)

namespace ModularAccess

noncomputable def decider {F : ModularFamily} (a : ModularAccess F)
    (ha : a.access.PolyTime) : SpaceDecider F.zeroLanguage := by
  let ac := a.access
  let P := Suspended.program ac
  let T := Suspended.childTime ac
  let N := fun c => Suspended.parentTime (F.dimension c)
  let f := SubroutineIteration.abstractStep P T
  have hbitsFP := mem_FP_comp (mem_FP_comp ha.dimension BinaryNat.succ_mem_FP)
    BinaryNat.succ_mem_FP
  let pd := Classical.choose (Cobham.output_length_poly_of_mem_FP ha.dimension)
  have hd : ∀ c, (a.access.dimension c).length ≤ pd.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP ha.dimension)
  let pm := Classical.choose (Cobham.output_length_poly_of_mem_FP ha.modulus)
  have hm : ∀ c, (a.access.modulus c).length ≤ pm.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP ha.modulus)
  let pq := Classical.choose (Cobham.output_length_poly_of_mem_FP hbitsFP)
  have hq : ∀ c, ((BinaryNat.succ ∘ BinaryNat.succ ∘ a.access.dimension) c).length ≤ pq.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP hbitsFP)
  let pe := Classical.choose (Cobham.output_length_poly_of_mem_FP Controller.entryInput_mem_FP)
  have he : ∀ c, (Controller.entryInput c).length ≤ pe.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP Controller.entryInput_mem_FP)
  let p := pd + pm + pq
  let r := 2 * Polynomial.X + 2 + 64 * (4 * p + 2) ^ 2
  let u := 2 * pe.comp r + 2 + 64 * (3 * p + 1) ^ 2
  have hbits (c : List Bool) : (F.dimension c).size + (F.modulus c).size +
      (F.dimension c + 2).size ≤ p.eval c.length := by
    have hdc := hd c
    have hmc := hm c
    have hqc := hq c
    rw [(a.correct c).dimension, BinaryNatCode.length_encode] at hdc
    rw [(a.correct c).modulus, BinaryNatCode.length_encode] at hmc
    simp only [Function.comp_apply, (a.correct c).dimension, MatrixMoment.EntryBits.succ_code,
      show F.dimension c + 1 + 1 = F.dimension c + 2 from by omega,
      BinaryNatCode.length_encode] at hqc
    simp only [p, Polynomial.eval_add]
    omega
  have hp (c : List Bool) (j : ℕ) :
      (f^[j] (Suspended.init ac c)).length ≤ r.eval c.length := by
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    have hl := Suspended.parent_length ac c (F.modulus c) (F.dimension c) (F.matrix c)
      (a.correct c) j
    have hb := hbits c
    have hpow := Nat.pow_le_pow_left
      (show 3 * (F.dimension c).size + (F.modulus c).size + 2 ≤ 4 * p.eval c.length + 2 by omega) 2
    simp only [r, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_pow]
    exact hl.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 64 hpow) _)
  refine SubroutineIteration.decider P (Suspended.program_polyTime ac ha)
    (Suspended.init ac) (Suspended.init_mem_FP ac ha) Controller.halted Controller.zeroAnswer
    Controller.halted_mem_FP Controller.zeroAnswer_mem_FP T N r u
    ((2 * p + 3) * p + 1) ((p + 2) * p + 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro c j _ hr
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    exact Suspended.requested_first_halt ac c (F.modulus c) (F.dimension c)
      (F.matrix c) (a.correct c) j hr
  · intro c j _
    exact hp c j
  · intro c j _ hr v hv
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    have hl := Suspended.requested_length ac c (F.modulus c) (F.dimension c)
      (F.matrix c) (a.correct c) j hr v hv
    have hquery : (Controller.entryInput (f^[j] (Suspended.init ac c))).length ≤
        (pe.comp r).eval c.length := by
      have hle := (he (f^[j] (Suspended.init ac c))).trans (polynomial_eval_mono_nat pe (hp c j))
      simpa only [Polynomial.eval_comp] using hle
    have hb := hbits c
    have hpow := Nat.pow_le_pow_left
      (show 2 * (F.dimension c + 2).size + (F.modulus c).size + 1 ≤ 3 * p.eval c.length + 1 by omega) 2
    simp only [u, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_pow, Polynomial.eval_one]
    exact hl.trans (Nat.add_le_add
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hquery) 2) (Nat.mul_le_mul_left 64 hpow))
  · intro c
    have hb := hbits c
    have hw := power_work_bound (F.dimension c)
    have hprod : (2 * (F.dimension c).size + 3) * (F.dimension c).size ≤
        (2 * p.eval c.length + 3) * p.eval c.length := Nat.mul_le_mul (by omega) (by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_one]
    exact hw.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hprod 1))
  · intro c j _ hr
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    have ht := Suspended.requested_time_le ac c (F.modulus c) (F.dimension c)
      (F.matrix c) (a.correct c) j hr
    have hb := hbits c
    have hprod : ((F.dimension c + 2).size + 2) * (F.dimension c + 2).size ≤
        (p.eval c.length + 2) * p.eval c.length := Nat.mul_le_mul (by omega) (by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_one]
    exact ht.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hprod 1))
  · intro c j hj
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    rw [Suspended.iterate_eq, Suspended.init_encode ac c (F.modulus c) (F.dimension c)
      (a.correct c).dimension]
    exact Controller.halted_before _ c (powerMatrix (F.matrix c)) residueBits
      (Suspended.ops_correctAt ac c (F.modulus c) (F.dimension c) (F.matrix c) (a.correct c))
      (F.dimension c) j (powerQuery (F.dimension c) 0).row (powerQuery (F.dimension c) 0).col hj
  · intro c
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    rw [Suspended.iterate_eq, Suspended.init_encode ac c (F.modulus c) (F.dimension c)
      (a.correct c).dimension]
    exact Controller.halted_after _ c (powerMatrix (F.matrix c)) residueBits
      (Suspended.ops_correctAt ac c (F.modulus c) (F.dimension c) (F.matrix c) (a.correct c))
      (F.dimension c) (powerQuery (F.dimension c) 0).row (powerQuery (F.dimension c) 0).col
  · intro c
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    rw [Suspended.iterate_eq, Suspended.init_encode ac c (F.modulus c) (F.dimension c)
      (a.correct c).dimension]
    exact (controller_zero_iff _ c (F.modulus c) (F.matrix c)
      (Suspended.ops_correctAt ac c (F.modulus c) (F.dimension c) (F.matrix c) (a.correct c))).symm

theorem zeroLanguage_mem_PSPACE {F : ModularFamily} (a : ModularAccess F)
    (ha : a.access.PolyTime) : F.zeroLanguage ∈ PSPACE := (decider a ha).mem_PSPACE

end ModularAccess
end LeanCanny.Algebra.Berkowitz
