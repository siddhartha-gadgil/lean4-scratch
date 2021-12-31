import Lake
open Lake DSL

package scratch {
  dependencies := #[{
    name := "mathlib",
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "1e27f0dee2b602d6bc3ea82ef961cd76d63053e1"
  }],
  supportInterpreter := true
  -- add configuration options here
}
