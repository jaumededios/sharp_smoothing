import Lean

open Lean

/-- Run the configured `leanprover/comparator` binary as Lake's test driver. -/
def main : IO UInt32 := do
  let comparatorBin := (← IO.getEnv "COMPARATOR_BIN").getD "comparator"
  try
    let child ← IO.Process.spawn {
      cmd := "lake"
      args := #["env", comparatorBin, "Comparator/config.json"]
    }
    child.wait
  catch err =>
    IO.eprintln s!"Failed to run comparator via `{comparatorBin}`."
    IO.eprintln "Install comparator or set COMPARATOR_BIN=/path/to/comparator."
    IO.eprintln s!"Original error: {err}"
    pure 1
