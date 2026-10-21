import Lake

open Lake DSL

package lean_canny where
  version := v!"0.1.0"
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩, ⟨`maxHeartbeats, 2000000⟩]

require complexitylib2 from git
  "https://github.com/SamuelSchlesinger/complexitylib2" @
  "cb1b7ce8ca0757db30ec29c8365b88d86b78c80a"

-- Retained while existing FP proofs and legacy space certificates are ported.
require complexitylib from git
  "https://github.com/SamuelSchlesinger/complexitylib" @
  "add0aca8ee0d71e68969f2cb45cf91554a50f787"

-- Both dependencies must use the new foundation's common CSLib/Mathlib versions.
require cslib from git
  "https://github.com/leanprover/cslib" @
  "b5f3b77d9f045ed8f2dfec05505b159c2417e1c6"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "625d8914199bc567cca9b91f90e8e5afafa5ae51"

@[default_target]
lean_lib LeanCanny

/-- Apply the checked forward port of the pinned legacy dependency, idempotently. -/
post_update pkg do
  let dependency := pkg.dir / ".lake" / "packages" / "complexitylib"
  let patch := pkg.dir / "scripts" / "complexitylib-lean436.patch"
  let revision ← IO.Process.output {
    cmd := "git", args := #["-C", dependency.toString, "rev-parse", "HEAD"] }
  unless revision.exitCode == 0 &&
      revision.stdout.trimAscii.toString == "add0aca8ee0d71e68969f2cb45cf91554a50f787" do
    error "Legacy compatibility patch requires the pinned Complexitylib revision."
  let applied ← IO.Process.output {
    cmd := "git", args := #["-C", dependency.toString, "apply", "--reverse", "--check", patch.toString] }
  if applied.exitCode == 0 then return
  let check ← IO.Process.output {
    cmd := "git", args := #["-C", dependency.toString, "apply", "--check", patch.toString] }
  unless check.exitCode == 0 do
    error s!"Cannot apply legacy compatibility patch:\n{check.stderr}"
  let result ← IO.Process.output {
    cmd := "git", args := #["-C", dependency.toString, "apply", patch.toString] }
  unless result.exitCode == 0 do
    error s!"Legacy compatibility patch failed:\n{result.stderr}"
