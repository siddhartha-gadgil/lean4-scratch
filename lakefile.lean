import Lake
open Lake DSL

package scratch {
  dependencies := #[{
    name := "mathlib",
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "80905943d92abcd01ec69b6054f6dbc2a718c76d"
  }],
  supportInterpreter := true
  -- add configuration options here
}
