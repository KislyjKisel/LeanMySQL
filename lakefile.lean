import Lake

open System Lake DSL

def leanSoureDir := "lib"
def cCompiler := get_config? cc
def cDir : FilePath := "c"
def ffiSrc := cDir / "ffi.c"
def ffiO := "ffi.o"
def ffiLib := "libffi.a"
def includesDir := "/usr/include/"
def libsDir := "/usr/lib/x86_64-linux-gnu/"
def mySQLLinkArg := "-lmysqlclient"

require std from git
  "https://github.com/leanprover/std4" @ "409a644"

package mysql {
  srcDir := leanSoureDir
}

lean_lib MySql

@[default_target]
lean_exe Main {
  moreLinkArgs := #["-L", libsDir, mySQLLinkArg]
}

extern_lib «mysql-ffi» pkg := do
  let libFile := pkg.dir / defaultBuildDir / cDir / ffiLib
  let oFile := pkg.dir / defaultBuildDir / cDir / ffiO
  let srcTarget ← inputFile <| pkg.dir / ffiSrc
  let mut weakArgs := #["-I", (← getLeanIncludeDir).toString]
  let traceArgs := #["-I", includesDir]
  let mut cc ← getLeanCc
  match cCompiler with
  | some cCompiler => cc := cCompiler
  | none => weakArgs := weakArgs ++ #["-I", (← getLeanIncludeDir) / "clang" |>.toString]
  buildStaticLib libFile #[← buildO "ffi.c" oFile srcTarget weakArgs traceArgs cc]
