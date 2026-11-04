/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedPointCompanionReadback
/-! # Scalar positions of distinct midpoint and child captures -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalLevelScalarValues
open IntegralMixedPointCompanion IntegralMixedFrozenFrame
open scoped Classical
variable {n m :ℕ} {frozen :Finset (Fin (n+1))}
  (pMID pChild :Fin (n+1)→ℝ) (old :Fin m→ℝ)
  (g :Fin (n+1)) (js :List (Free frozen))

noncomputable def levelValues :Fin (m+1+js.length+1+js.length)→ℝ:=
  values pChild (Fin.cons (pChild g) (values pMID (Fin.cons (pMID g) old) js)) js

private theorem cons_offset {k :ℕ} (a :ℝ) (f :Fin k→ℝ) (i :Fin k):
    (Fin.cons a f :Fin (k+1)→ℝ) ⟨1+i.val,by have :=i.isLt;omega⟩=f i:=by
  have HE :(⟨1+i.val,by omega⟩ :Fin (k+1))=i.succ:=Fin.ext (by simp only [Fin.val_succ];omega)
  rw [HE]
  rfl

theorem child_capture (k :Fin js.length):
    levelValues pMID pChild old g js ⟨k.val,by have :=k.isLt;omega⟩=pChild (js.get k).val:=
  values_get pChild _ js k

theorem child_anchor :
    levelValues pMID pChild old g js ⟨js.length,by omega⟩=pChild g:=by
  exact values_old pChild (Fin.cons (pChild g) (values pMID (Fin.cons (pMID g) old) js)) js
    (⟨0,by omega⟩ :Fin (m+1+js.length+1))

theorem midpoint_capture (k :Fin js.length):
    levelValues pMID pChild old g js ⟨js.length+1+k.val,by have :=k.isLt;omega⟩=pMID (js.get k).val:=by
  let i :Fin (m+1+js.length):=⟨k.val,by have :=k.isLt;omega⟩
  have H:=values_old pChild (Fin.cons (pChild g) (values pMID (Fin.cons (pMID g) old) js)) js
    ⟨1+i.val,by have :=i.isLt;omega⟩
  simpa only [levelValues,i,Nat.add_assoc] using
    H.trans ((cons_offset (pChild g) _ i).trans (values_get pMID _ js k))

theorem midpoint_anchor :
    levelValues pMID pChild old g js ⟨js.length+1+js.length,by omega⟩=pMID g:=by
  let i :Fin (m+1+js.length):=⟨js.length,by omega⟩
  have H:=values_old pChild (Fin.cons (pChild g) (values pMID (Fin.cons (pMID g) old) js)) js
    ⟨1+i.val,by have :=i.isLt;omega⟩
  have HM :values pMID (Fin.cons (pMID g) old) js i=pMID g:=
    by simpa only [i,Nat.add_zero,Fin.mk_zero,Fin.cons_zero] using
      values_old pMID (Fin.cons (pMID g) old) js (⟨0,by omega⟩ :Fin (m+1))
  simpa only [levelValues,i,Nat.add_assoc] using H.trans ((cons_offset (pChild g) _ i).trans HM)

theorem endpoint_value (k :Fin m):
    levelValues pMID pChild old g js ⟨js.length+1+(js.length+1+k.val),by have :=k.isLt;omega⟩=old k:=by
  let i :Fin (m+1+js.length):=⟨js.length+1+k.val,by have :=k.isLt;omega⟩
  have H:=values_old pChild (Fin.cons (pChild g) (values pMID (Fin.cons (pMID g) old) js)) js
    ⟨1+i.val,by have :=i.isLt;omega⟩
  have HM :values pMID (Fin.cons (pMID g) old) js i=old k:=by
    simpa only [i,Nat.add_assoc] using
      (values_old pMID (Fin.cons (pMID g) old) js ⟨1+k.val,by have :=k.isLt;omega⟩).trans
        (cons_offset (pMID g) old k)
  simpa only [levelValues,i,Nat.add_assoc] using H.trans ((cons_offset (pChild g) _ i).trans HM)

end LeanCanny.Geometry.IntegralMixedChronologicalLevelScalarValues
