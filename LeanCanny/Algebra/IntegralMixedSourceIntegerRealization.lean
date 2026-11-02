/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
public import LeanCanny.Algebra.IntegralMixedFramedIntegerRealization
/-! # Correlated prescribed roots in a charged-source integer prelude

The root vector is chosen once. A single interpreting hom realizes every
coordinate in the new bank, without independent sampler correlation claims.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem realizes (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (Q root).degree≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (root : List Bool) {horizon : ℕ} {ι : Type} [Fintype ι]
    (initial : State (Q root) horizon (P.width root) 0 ι) (z : ι → ℝ)
    (hrows : ∀i,(initial.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hc : (commands P Q hq S count hz hd root).length≤horizon+1)
    (values : ℕ → ℝ)
    (hvalues : ∀i<count root,(S.polynomial (pair root (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (values i)=0) :
    IntegralMixedIntegerRealization.Realizes
      (run initial (commands P Q hq S count hz hd root) hc)
      (fun i=>values (count root-1-i)) := by
  apply IntegralMixedFramedIntegerRealization.realizes initial z hrows _ hc
  intro i
  have HI : i.val<count root := by simpa only [commands,List.length_ofFn] using i.isLt
  have HE : (commands P Q hq S count hz hd root)[i.val]=instruction P Q hq S count hz hd root ⟨i.val,HI⟩ := by
    simp only [commands,List.getElem_ofFn]
  simp only [Fin.getElem_fin]
  rw [HE]
  exact hvalues _ (by omega)

end LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
