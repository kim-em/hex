import Lake

open System Lake DSL

package Hex where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0-rc2"

require verso from git
  "https://github.com/leanprover/verso.git" @ "v4.30.0-rc2"

private def clmulOTarget (pkg : Package) : FetchM (Job FilePath) := do
  let oFile := pkg.dir / defaultBuildDir / "HexGF2" / "ffi" / "clmul.o"
  let srcTarget ← inputTextFile <| pkg.dir / "HexGF2" / "ffi" / "clmul.c"
  buildFileAfterDep oFile srcTarget fun srcFile => do
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
    compileO oFile srcFile flags

extern_lib hexgf2ffi (pkg) := do
  let name := nameToStaticLib "hexgf2ffi"
  let oTarget ← clmulOTarget pkg
  buildStaticLib (pkg.staticLibDir / name) #[oTarget]

lean_lib HexArith where

lean_lib HexPoly where

lean_lib HexMatrix where

lean_lib HexModArith where
  moreLinkArgs := #["HexModArith/ffi/zmod64_mul.c"]

lean_lib HexGramSchmidt where

lean_lib HexGF2 where

lean_lib HexPolyZ where

lean_lib HexLLL where

lean_lib HexPolyFp where

lean_lib HexGfqRing where

lean_lib HexGfqField where

lean_lib HexBerlekamp where

lean_lib HexHensel where

lean_lib HexConway where

lean_lib HexGfq where

lean_lib HexBerlekampZassenhaus where

lean_lib HexPolyMathlib where

lean_lib HexMatrixMathlib where

lean_lib HexModArithMathlib where

lean_lib HexGramSchmidtMathlib where

lean_lib HexPolyZMathlib where

lean_lib HexLLLMathlib where

lean_lib HexBerlekampMathlib where

lean_lib HexHenselMathlib where

lean_lib HexGF2Mathlib where

lean_lib HexGfqMathlib where

lean_lib HexBerlekampZassenhausMathlib where

@[default_target]
lean_lib HexManual where
