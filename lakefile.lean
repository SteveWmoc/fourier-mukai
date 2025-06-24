import Lake
open Lake DSL

package "fourierMukai" {
  description := "Formalizing Fourier-Mukai transform in Lean 4"
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.20.1"

@[default_target]
lean_lib "FourierMukai" {
}

lean_exe "fourierMukai" {
  root := `Main
}
