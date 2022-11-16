import Lake
open Lake DSL

package «lean-souffle» {
  -- add package configuration options here
}

lean_lib Souffle {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean-souffle» {
  root := `Main
}
