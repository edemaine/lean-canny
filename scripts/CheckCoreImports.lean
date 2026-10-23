import LeanCanny

/-! The default library must keep the completed endpoint independent of the
optional tube development. The complete development is audited separately. -/

open Lean in
run_cmd do
  for name in (← getEnv).header.moduleNames do
    if name == `LeanCanny.Alternatives ||
        name.toString.startsWith "LeanCanny.ETR.Tube" then
      throwError "Core imports an alternative construction: {name}"
  logInfo "Core import boundary checked: completed coercive proof only."

example : LeanCanny.ETR.language ∈ LeanCanny.PSPACE := LeanCanny.ETR.etr_mem_PSPACE
