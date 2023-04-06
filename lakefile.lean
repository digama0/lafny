import Lake
open Lake DSL

package «lafny» {
  -- add package configuration options here
}

lean_lib «Lafny» {
  -- add library configuration options here
}

@[default_target]
lean_exe «lafny» {
  root := `Main
}
