import LeanCanny.ETR.CoercivePSPACE

/-! The ETR endpoint must remain independent of the optional tube route.
The formal abstract also imports connectivity, which reuses some tube algebra;
the complete development is audited separately. -/

open Lean in
run_cmd do
  for name in (← getEnv).header.moduleNames do
    if name == `LeanCanny.Alternatives ||
        name.toString.startsWith "LeanCanny.ETR.Tube" then
      throwError "Core imports an alternative construction: {name}"
  logInfo "ETR import boundary checked: completed coercive proof only."

example : LeanCanny.ETR.language ∈ LeanCanny.PSPACE := LeanCanny.ETR.etr_mem_PSPACE
