/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapChainPrefix
/-! # Meaningful ancestor prefixes retain room for their free coordinates

Padding is excluded. The remaining quadratic program reserve pays for at
least the free rank, at every legal prefix including the terminal rank.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapChain
open scoped Classical

theorem rawStart_free_bound (n : ℕ) (q : List Bool) (i : ℕ) (hi : i≤n+1) :
    rawStart n q i+(n+1-i)≤IntegralMixedRoadmapRecordChain.recordBound n :=by
  have HH:=prefixCount_bound n q i hi
  have HR : n+1-i≤(n+1-i)*(n+4-i):=by
    calc
      n+1-i=(n+1-i)*1:=by omega
      _≤(n+1-i)*(n+4-i):=Nat.mul_le_mul_left _ (by omega)
  unfold rawStart IntegralMixedRoadmapRecordChain.recordBound
  omega

theorem meaningful_free_room (n initial S : ℕ) (q : List Bool) (i : ℕ) (hi : i≤n+1)
    (hroom : initial+IntegralMixedRoadmapRecordChain.recordBound n≤S+1) :
    initial+rawStart n q i+(n+1-i)≤S+1 :=by
  have HH:=rawStart_free_bound n q i hi
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapChain
