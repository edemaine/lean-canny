/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatRelativeFactor
public import LeanCanny.Algebra.IntegralBerkowitzBlockControllerLocal
/-! # Flat factor correctness on bounded actual requests

The outer packet normalizes old-basis ranks before the fresh writer.
The reply contract is confined to that packet, so oversized unrelated
legacy packets are not additional semantic obligations.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatRelativeFactorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalFlatBerkowitzQuery.entryWriter IntegralCriticalFlatBerkowitzQuery.momentWriter

theorem value_at (P : Parameters) (S : Source) (a : IntegralBerkowitzBlockBits.Access S)
    (answer : List Bool → List Bool) (c : List Bool)
    (hd : selector S (outerPacket S (packet P c)) = [false, true] →
      answer (IntegralCriticalFlatBerkowitzQuery.entryWriter P S (diagonalQuery S (outerPacket S (packet P c)))) =
        a.entry (diagonalQuery S (outerPacket S (packet P c))))
    (hm : selector S (outerPacket S (packet P c)) = [true, true] →
      answer (IntegralCriticalFlatBerkowitzQuery.momentWriter P (outerPacket S (packet P c))) =
        (momentFamily S).value (outerPacket S (packet P c))) :
    (program P S).value answer c = entryProgram S a (packet P c) := by
  rw [program, SingleCall.Program.requery_value]
  exact entryController_value_at S a (IntegralCriticalFlatBerkowitzQuery.entryWriter P S)
    (IntegralCriticalFlatBerkowitzQuery.momentWriter P) answer (packet P c) hd hm

end LeanCanny.Algebra.IntegralCriticalFlatRelativeFactorBits
