/-
Copyright 2025 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-! # The Problem Status Linter

The `problemStatusLinter` is a linter to aid with formatting contributions to
the Formal Conjectures repository by ensuring that results in a file have
the appropriate tags in order to distinguish between open/already solved
problems and background results/sanity checks.

We do this by requiring that
1) Benchmark problems should be stated using the `theorem` command
2) Easy background results/API should use `lemma`
3) Sanity checks should use `example`.

-/

open Lean Elab Meta Linter Command Parser Term

/-- Convert a syntax node to an array of syntax nodes representing the
attributes of a declaration. -/
private def getProblemStatusAttr
  (stx : TSyntax ``Command.declModifiers) :
    CommandElabM (Array <| TSyntax ``attrInstance) := do
  match stx with
  | `(declModifiers| @[$[$atts],*]) =>
    atts.filterM fun att ↦ do
      match att with
      | `(attrInstance | problem_status $_) => return true
      | _ => return false
  | _ => return #[]


/-- The problem status linter checks that each theorem has precisely
one problem status attribute and that lemmas/examples do not have any
attribute. -/
def problemStatusLinter : Linter where
  --TODO(lezeau): do we also want to lint on e.g. definitions and instances?
  run := fun stx => do
    match stx with
      | `(command| $a:declModifiers theorem $_ : $_ := $_) =>
        let prob_status ← getProblemStatusAttr a
        match prob_status.size with
        | 0 => logWarningAt stx "Theorems should have a problem status attribute"
        | 1 => pure ()
        | _ => logWarningAt stx "Theorems should have no more than one problem status attribute."
      | `(command| $a:declModifiers lemma $_ : $_ := $_) =>
        let prob_status ← getProblemStatusAttr a
        unless prob_status.size ≥ 1 do return
        logWarningAt stx "Lemmas shouldn't have a problem status attribute."
      | `(command| $a:declModifiers example : $_ := $_) =>
        let prob_status ← getProblemStatusAttr a
        unless prob_status.size ≥ 1 do return
        logWarningAt stx "Examples shouldn't have a problem status attribute."
      | _ => return

initialize do
  addLinter problemStatusLinter
