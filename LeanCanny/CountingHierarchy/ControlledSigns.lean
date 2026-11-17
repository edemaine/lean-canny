/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Controlled
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ResidueSign

/-!
# Signs of controlled integer families

A zero-variable controlled polynomial supplies all the data required by
Frontier's residue-sign theorem. No explicit expansion of the integer or
recognizer for the admissible domain is required. The result is a fixed
`F_(max(a,5)+3)` function-level certificate.
-/

public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ}
  {P : α → MvPolynomial (Fin 0) ℤ}

/-- The constant coefficient is a mathematical specification; only its modular
evaluator and short bound are used by the sign algorithm. -/
@[expose] noncomputable def integerAccess (C : Controlled P enc a) :
    IntegerResidueAccess (fun w => (P w).coeff 0) where
  magnitudeExponent := C.massExponent
  admissible := fun w p => p.Prime ∧ C.cutoff w < p
  modulus_pos := fun _ _ hp => hp.1.pos
  residue := fun q => C.evaluate (q.1, q.2, [])
  magnitude_le w := (Algebra.MvMass.coeff_le _ _).trans (C.mass_le w)
  residue_eq w p hp := by
    rw [C.evaluate_eq w p [] hp.1 hp.2]
    let : NeZero p := ⟨hp.1.ne_zero⟩
    rw [evaluation, (P w).eq_C_of_isEmpty]
    simpa only [eval₂_C, Int.coe_castRingHom, Int.toNat_natCast, coeff_C, ite_true] using
      congrArg Int.toNat (ZMod.val_intCast (n := p) ((P w).coeff 0))

/-- Preparing an empty evaluation point is ordinary polynomial-time work. -/
theorem integerAccess_mem (C : Controlled P enc a) :
    C.integerAccess.InCountingFunction a enc :=
  ⟨C.mass_computable, CountingFunction.preprocess (input := encPair enc encNat)
    C.evaluate_mem (g := fun q => (q.1, q.2, [])) (by fun_prop)⟩

/-- Signs of controlled integer families lie at a fixed counting level, even
when their coefficient expansions have exponentially many bits. -/
theorem sign_mem (C : Controlled P enc a) (D : Decoder enc) :
    (fun w => ((P w).coeff 0).sign) ∈
      CountingFunction (max a 5 + 3) enc encIntBin := by
  apply IntegerResidueAccess.sign_mem_CountingFunction D C.integerAccess
    C.integerAccess_mem C.cutoff_computable
  intro w p hp
  exact ⟨Cslib.PrimeWindowSign.prime _ _ ⟨p, hp⟩,
    (Nat.mem_primesLE_sdiff_primesLE_iff.mp hp).2.1⟩

end LeanCanny.CountingHierarchy.Controlled
