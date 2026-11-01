/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationMatrixContexts
/-! # The whole normalization controller preserves request contexts -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationContextBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedNormalizationTopBits
set_option backward.isDefEq.respectTransparency false

theorem requests_context (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (g : IntegralMixedVirtualCaps.RootGeometry P F) (height : List Bool → ℕ) (hb : BinaryFn height)
    (answer : List Bool → List Bool) (hm : IntegralMixedNormalizationDispatcherBits.Matches P a F h hd height hb answer) :
    RequestsSatisfy (IntegralMixedNormalizationDispatcherBits.machine P a F h hd height hb) answer (ContextEq P) := by
  unfold IntegralMixedNormalizationDispatcherBits.machine
  apply requestsSatisfy_choose _ _ answer _ (context0 P a F hd answer)
  apply requestsSatisfy_choose _ _ answer _ (context1 P a F h hd g height hb answer hm)
  apply requestsSatisfy_choose _ _ answer _ (context2 P a F answer)
  apply requestsSatisfy_choose _ _ answer _ (context3 P a F h answer)
  apply requestsSatisfy_choose _ _ answer _ (context4 P a F h hd g height hb answer hm)
  apply requestsSatisfy_choose _ _ answer _ (context5 P a F h answer)
  apply requestsSatisfy_choose _ _ answer _ (context6 P a F h hd g height hb answer hm)
  apply requestsSatisfy_choose _ _ answer _ (context7 P a F height hb answer)
  apply requestsSatisfy_choose _ _ answer _ (context8 P a F h answer)
  apply requestsSatisfy_choose _ _ answer _ (context9 P a F h answer)
  apply requestsSatisfy_choose _ _ answer _ (context10 P a F h answer)
  apply requestsSatisfy_choose _ _ answer _ (context11 P a F h answer)
  apply requestsSatisfy_choose _ _ answer _ (context12 P a F h answer)
  apply requestsSatisfy_choose _ _ answer _ (context13 P a F h answer)
  exact context14 P a F h hd answer
end LeanCanny.Algebra.IntegralMixedNormalizationContextBits
