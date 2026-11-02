/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackUnit
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackSyntaxFields

/-! # Native original syntax survives an honest root projection

Term/body/integer words are queried at the projected full saved key. Root
height profiles compose with the original-root map. Enlarging the caller
modulus budget changes none of these represented source polynomials.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRootPullback
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

noncomputable def pullSyntax (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H) (project : List Bool→List Bool) (hp : project∈FP)
    (extra : List Bool→ℕ) :
    IntegralMixedFramedNativeBits.Syntax (parameters P project extra) (plan P D project extra) (data P D H project extra) where
  unit := unit P D H s.unit project hp extra
  term := s.term ∘ key project
  frozen := s.frozen ∘ key project
  tilt := s.tilt ∘ key project
  exponent := s.exponent ∘ key project
  term_FP := mem_FP_comp (key_FP project hp) s.term_FP
  frozen_native := s.frozen_native.comp (key_FP project hp)
  tilt_native := s.tilt_native.comp (key_FP project hp)
  exponent_native := s.exponent_native.comp (key_FP project hp)
  term_scope q := by
    simpa only [FermatLevelFramedSpatialBits.ambient,parameters,Function.comp_apply,key_root] using s.term_scope (key project q)
  tilt_scope q := by
    simpa only [FermatLevelFramedSpatialBits.ambient,parameters,Function.comp_apply,key_root] using s.tilt_scope (key project q)
  low q := eq_of_heq ((source_low_heq P D project extra q).trans
    ((heq_of_eq (s.low (key project q))).trans (low_formula_heq P project extra s.term s.frozen s.tilt s.exponent q).symm))
  integerWord := s.integerWord ∘ key project
  integer_FP := mem_FP_comp (key_FP project hp) s.integer_FP
  integer q := (s.integer (key project q)).trans (integer_polynomial P D project extra q).symm
  nodes := s.nodes ∘ project
  factor := s.factor ∘ project
  seed := s.seed ∘ project
  nodes_native := s.nodes_native.comp hp
  factor_native := s.factor_native.comp hp
  seed_native := s.seed_native.comp hp

end LeanCanny.Algebra.IntegralMixedFramedRootPullback
