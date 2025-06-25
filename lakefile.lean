import Lake
open Lake DSL

package «fourier-mukai» where
  version := v!"0.1.0"
  keywords := #["mathematics", "algebraic-geometry", "category-theory", "fourier-mukai"]
  description := "Formalization of the Fourier-Mukai transform in Lean 4"
  -- Repository information
  homepage := "https://github.com/SteveWmoc/fourier-mukai"
  -- License
  license := "Apache-2.0"

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
  IO.println "Getting mathlib cache..."
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["exe", "cache", "get"]
  }
  if out.exitCode == 0 then
    IO.println "Cache retrieved successfully"
    return 0
  else
    IO.eprintln s!"Failed to get cache: {out.stderr}"
    return out.exitCode

-- Lake script for cleaning build  
script clean do
  IO.println "Cleaning build..."
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["clean"]
  }
  if out.exitCode == 0 then
    IO.println "Clean completed successfully"
    return 0
  else
    IO.eprintln s!"Failed to clean: {out.stderr}"
    return out.exitCode
