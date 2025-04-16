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

import Lean.Elab.Command
import Mathlib.Init
import Mathlib.Util.CompileInductive
import Qq

open Lean Elab Meta Qq

/-!

The `open_problem` tag:
A tag to mark formalizations of open problems in our benchmarks.

This is still a prototype (we will probably want to add some features
to this tag in the feature.)

The `problem_status` tag:
A tag to mark the status of a problem statement. This currently allows for two
values: `open` and `solved`.

The tag should be used as follows:
```
@[problem_status open]
theorem foo : MyOpenProblem := by
  sorry

@[problem_status solved]
theorem bar : 1 + 1 = 2 := by
  sorry
```

-/

section

inductive ProblemStatus
  | open
  | solved
  deriving Inhabited


syntax problemStatus := &"open" <|> &"solved"

/-- Convert from a syntax node to a name. -/
private def problemStatus.toName (stx : TSyntax ``problemStatus) : Option Name :=
  match stx with
    | `(problemStatus| open) => ``ProblemStatus.open
    | `(problemStatus| solved) => ``ProblemStatus.solved
    | _ => none

syntax (name := problem_status) "problem_status" problemStatus : attr

/-- Specifies whether a given problem statement is for an open or solved problem -/
initialize problemStatusAttr : ParametricAttribute ProblemStatus ←
  registerParametricAttribute {
    name := `problem_status
    descr := "Annotation of status of a problem"
    getParam := fun _ => fun
      | `(attr| problem_status $s) => withRef s <| do
        let .some n := problemStatus.toName s | Elab.throwUnsupportedSyntax
        Elab.addConstInfo s n
        Lean.Meta.MetaM.run' <|
          unsafe Meta.evalExpr ProblemStatus q(ProblemStatus) (.const n [])
      | _ => Elab.throwUnsupportedSyntax
  }

end

compile_inductive% ProblemStatus
