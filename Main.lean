import Toyprover

def main (args : List String) : IO Unit := do
  if args.isEmpty then
    IO.println "Usage: toyprover [-v|--verbose] <path>"
    return
  let verbose := args.contains "-v" || args.contains "--verbose"
  let fileArgs := args.filter (fun arg => !arg.startsWith "-")
  if fileArgs.isEmpty then
    IO.println "Error: No file path provided."
    IO.println "Usage: toyprover [-v|--verbose] <path>"
    return
  ToyProver.solver (fileArgs.get! 0) (verbose := verbose)
