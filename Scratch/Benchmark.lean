import Lean
import Lean.Meta
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/benchmarking.20commands/near/249677507


section
open Lean Elab Command

syntax (name := timeCmd)  "#time " command : command

@[commandElab timeCmd] def elabTimeCmd : CommandElab
  | `(#time%$tk $stx:command) => do
    let start ← IO.monoMsNow
    elabCommand stx
    logInfoAt tk m!"time: {(← IO.monoMsNow) - start}ms"
  | _ => throwUnsupportedSyntax

end
/-
set_option maxRecDepth 200000 in
#time example : (List.range 5100).length = 5100 := rfl
-/
