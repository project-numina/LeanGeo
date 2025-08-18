import Lake
open Lake DSL

package «lib» where
  leanOptions := #[⟨`relaxedAutoImplicit, true⟩]
  supportInterpreter := true

@[default_target]
lean_lib SystemE {
}

lean_lib LeanGeo {
}

lean_lib Book {
}

lean_lib E3 {

}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "9837ca9d65d9de6fad1ef4381750ca688774e608"

require smt from git "https://github.com/ufmg-smite/lean-smt.git" @ "9b81e91cc9ea3833203317a7f425267112083672"

def tmpFileDir := "tmp"

def checkAvailable (cmd : String) : IO Unit := do
  let proc ← IO.Process.output {
    cmd := "which",
    args := #[cmd]
  }
  if proc.exitCode != 0 then
    throw $ IO.userError s!"Cannot find `{cmd}`."

script check do
  checkAvailable "smt-portfolio"
  checkAvailable "z3"
  checkAvailable "cvc5"
  println! "All requirements are satisfied."
  return 0

script cleanup do
  IO.FS.removeDirAll tmpFileDir
  return 0

script aggregate do
  let bookDir := (← IO.currentDir) / "Book"
  let leanPaths := (← System.FilePath.walkDir bookDir) |>.filter fun p => p.extension = some "lean"
  let sortedPaths := leanPaths.qsort (fun p₁ p₂ => p₁.toString < p₂.toString) |>.toList
  println! sortedPaths
  let code ← sortedPaths.mapM fun p => do
    let lines := (← IO.FS.lines p) |>.filter fun l =>
      ¬(l.startsWith "import" ∨ l.startsWith "namespace" ∨ l.startsWith "end")
    return (String.join $ (lines.map fun l => l ++ "\n").toList).trim ++ "\n\n"
  let codeAll := "import SystemE\n\nnamespace Elements\n\n" ++ String.join code ++ "\nend Elements\n"

  let outFile := bookDir / "All.lean"
  if ← outFile.pathExists then
    IO.FS.removeFile outFile
  IO.FS.writeFile outFile codeAll
  println! codeAll

  return 0

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git" @ "e2285d36490b9315a215564e6d34a2c88cccfc33"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "v4.15.0"

require REPL from git "https://github.com/leanprover-community/repl.git" @ "21966799da3691a0912b5a15193585bd2dd7165d"
