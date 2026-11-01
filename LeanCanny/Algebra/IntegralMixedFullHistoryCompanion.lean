/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHistoryPhysicalBridge
public import LeanCanny.Algebra.PaddedIntegralGeneratorSource
/-! # Literal creating companions for every full mixed-history command -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullHistoryCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev bank (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) := IntegralMixedFullHistoryFamilyBits.family P D

noncomputable def source (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) : PaddedIntegralGeneratorSource.Source where
  arity := (bank P D).birth
  width := (bank P D).width
  carrier key := ((bank P D).state key).sampler.scalarPrefix.carrier
  ring key := ((bank P D).state key).sampler.scalarPrefix.ring
  nontrivial key := ((bank P D).state key).sampler.scalarPrefix.nontrivial
  basis key := ((bank P D).state key).sampler.scalarPrefix.basis
  polynomial key := IntegralMixedFullHistoryScript.polynomial ((bank P D).state key) ((bank P D).birth_bound key)
    (IntegralMixedFullHistoryFamilyBits.creatingCommand P D key)
  degree key := IntegralMixedFullHistoryScript.degree ((bank P D).state key) ((bank P D).birth_bound key)
    (IntegralMixedFullHistoryFamilyBits.creatingCommand P D key)

noncomputable def rank (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : ℕ :=
  count ((source P D).arity (IntegralMixedVirtualTaskBits.saved P q) + 1) ((source P D).width (IntegralMixedVirtualTaskBits.saved P q))

noncomputable def row (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : Fin (rank P D q) :=
  ⟨get P .row q % rank P D q, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩

noncomputable def col (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : Fin (rank P D q) :=
  ⟨get P .col q % rank P D q, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩

noncomputable def value (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : List Bool :=
  residueBits ((source P D).matrix (IntegralMixedVirtualTaskBits.saved P q) (row P D q) (col P D q) : ZMod (modulus P q))

theorem value_canonical (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = value P D q := ⟨_, rfl⟩

theorem row_val (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    (row P D q).val = get P .row q % rank P D q := rfl

theorem col_val (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    (col P D q).val = get P .col q % rank P D q := rfl

end LeanCanny.Algebra.IntegralMixedFullHistoryCompanionBits
