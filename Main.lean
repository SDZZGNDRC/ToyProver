import Toyprover

def main (args : List String) : IO Unit := do
  if args.isEmpty then
    IO.println "Usage: toyprover <path>"
    return
  ToyProver.solver (args.get! 0)
