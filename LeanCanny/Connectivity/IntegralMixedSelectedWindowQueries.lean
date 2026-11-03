/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateWindow
public import LeanCanny.Algebra.SingleRootSignCount
/-! # A selected ordinal window uses five integer Tarski queries -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedWindowQueries
open LeanCanny.Algebra Polynomial IntegralMixedSelectedCoordinateWindow
open scoped Classical

private theorem single_count (p q : ℝ[X]) (s : SignType) :
    RootSignQueries.signCount p.roots.toFinset (fun _ : Fin 1=>q) (fun _=>s)=
      RootSignQueries.singleSignCount p q s :=by
  unfold RootSignQueries.signCount RootSignQueries.singleSignCount
  congr 1
  ext z
  simp only [Finset.mem_filter,Fin.forall_fin_one]

/-- The unit query counts all distinct roots, including unused coordinate roots. -/
theorem window_iff (p : ℝ[X]) (code : ℕ) (y ε : ℝ) :
    Window p code y ε↔
      2*RootSignQueries.tarskiQuery p 1≤2*(code:ℤ)+
        RootSignQueries.tarskiQuery p ((X-C (y-ε))^2)+RootSignQueries.tarskiQuery p (X-C (y-ε)) ∧
      2*(code:ℤ)<RootSignQueries.tarskiQuery p ((X-C (y+ε))^2)-RootSignQueries.tarskiQuery p (X-C (y+ε)) :=by
  rw [Window,single_count,single_count,RootSignQueries.tarskiQuery_one]
  have HL:=RootSignQueries.singleSignCount_positive p (X-C (y-ε))
  have HH:=RootSignQueries.singleSignCount_negative p (X-C (y+ε))
  omega

end LeanCanny.Connectivity.IntegralMixedSelectedWindowQueries
