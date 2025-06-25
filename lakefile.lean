import Lake
open Lake DSL

package «fourier-mukai» where
  version := v!"0.1.0"
  keywords := #["mathematics", "algebraic-geometry", "category-theory", "fourier-mukai"]
  description := "Formalization of the Fourier-Mukai transform in Lean 4"
  -- Repository information
  homepage := "https://github.com/SteveWmoc/fourier-mukai"
  repository := "https://github.com/SteveWmoc/fourier-mukai"
  -- License
  license := "Apache-2.0"
  -- Lean version constraint
  leanVersion := "4.21.0-rc3"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- Main library target
@[default_target]
lean_lib «FourierMukai» where
  -- Source directory (default is the package name)
  srcDir := "FourierMukai"
  -- Build all .lean files in the directory
  globs := #[.andSubmodules `FourierMukai]

-- Optional: Executable for examples/demos
lean_exe «fourier-mukai-demo» where
  root := `Main
  -- Uncomment when you create a Main.lean file
  -- supportInterpreter := true

-- Optional: Test library (uncomment when you add tests)
-- lean_lib «Test» where
--   srcDir := "test"
--   globs := #[.andSubmodules `Test]

-- Lake script for getting mathlib cache
script cache do
  let args := ["exe", "cache", "get"]
  let proc := Process.spawn {
    cmd := "lake"
    args := args
    cwd := some "."
  }
  let exitCode ← proc.wait
  if exitCode != 0 then
    IO.eprintln "Failed to get cache"
    return exitCode
  return 0

-- Lake script for cleaning build
script clean do
  let proc := Process.spawn {
    cmd := "lake"
    args := ["clean"]
    cwd := some "."
  }
  let exitCode ← proc.wait
  if exitCode != 0 then
    IO.eprintln "Failed to clean"
    return exitCode
  return 0
