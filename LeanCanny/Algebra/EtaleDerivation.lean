/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Etale.Kaehler

/-! # Extending derivations through formally etale algebras

The base-change isomorphism for Kahler differentials extends an R-derivation
S → T to T → T when T is formally etale over S. This applies both to
localizations and to separable algebraic field extensions.
-/

@[expose] public section

namespace LeanCanny.Algebra.EtaleDerivation

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Algebra.FormallyEtale S T]

noncomputable def extend (δ : Derivation R S T) : Derivation R T T :=
  ((δ.liftKaehlerDifferential.liftBaseChange T).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer
      (KaehlerDifferential.D R T)

theorem extend_algebraMap (δ : Derivation R S T) (s : S) : extend δ (algebraMap S T s) = δ s := by
  change (δ.liftKaehlerDifferential.liftBaseChange T)
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm
      (KaehlerDifferential.D R T (algebraMap S T s))) = δ s
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]

end LeanCanny.Algebra.EtaleDerivation
