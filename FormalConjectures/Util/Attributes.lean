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

import FormalConjectures.Util.OpenProblemAttr
import FormalConjectures.Util.Attributes.AMS

open Lean Elab Meta Qq

/-! # Problem Formalisation Attributes

## The Category Attribute:

### Overview
Provides information of the type of a statement. This can be:
- A mathematical problem (high school/undergraduate/graduate/research level).
  If this is a research problem then the user is also required to specify
  whether the problem has already been solved.
- An API statement
- A "test" statement

### Values
The values of this attribute are
- `@[category high_school]` : a high school level math problem.
- `@[category undergraduate]` : an undergraduate level math problem.
- `@[category graduate]` : a graduate level math problem.
- `@[category research open]` : an open reseach level math problem.
- `@[category research solved]` : a solved reseach level math problem.
- `@[category test]` : a statement that serves as a sanity check (e.g. for a new definition).
- `@[category API]` : a statement that constructs basic theory around a new definition

### Usage examples
The tag should be used as follows:
```
@[category high_school]
theorem imo_2024_p6
    (IsAquaesulian : (ℚ → ℚ) → Prop)
    (IsAquaesulian_def : ∀ f, IsAquaesulian f ↔
      ∀ x y, f (x + f y) = f x + y ∨ f (f x + y) = x + f y) :
    IsLeast {(c : ℤ) | ∀ f, IsAquaesulian f → {(f r + f (-r)) | (r : ℚ)}.Finite ∧
      {(f r + f (-r)) | (r : ℚ)}.ncard ≤ c} 2 := by
  sorry

@[category research open]
theorem an_open_problem : Transcendental ℝ (π + rexp 1) := by
  sorry

@[category test]
theorem a_test_to_sanity_check_some_definition : ¬ FermatLastTheoremWith 1 := by
  sorry
```

## The Problem Subject Attribute

Provides information about the subject of a mathematical problem, via a
numeral corresponding to the AMS subject classification of the problem.
This can be used as follows:
```
@[AMS 11] -- 11 correponds to Number Theory in the AMS classification
theorem FLT : FermatLastTheorem := by
  sorry
```

-/

open Lean PrettyPrinter Delaborator

/-- A type to capture the various types of statements that appear in our Lean files. -/
inductive Category
  /-- A high school level math problem. -/
  | highSchool
  /-- An undegraduate level math problem. -/
  | undergraduate
  /-- A graduate level math problem. -/
  | graduate
  /-- A reseach level math problem. This can be open, or already solved -/
  | research : ProblemStatus → Category
  /-- A test statement that serves as a sanity check (e.g. for a new definition)-/
  | test
  /-- An "API" statement, i.e. a statement that constructs basic theory around a new definition -/
  | API

syntax CategorySyntax := &"high_school" <|> &"undergraduate" <|> &"graduate" <|> (&"research" problemStatus) <|> &"test" <|> &"API"

/-- Convert from a syntax node to a name. -/
private def problemStatus.toName (stx : TSyntax ``problemStatus) : Option Name :=
  match stx with
    | `(problemStatus| open) => ``ProblemStatus.open
    | `(problemStatus| solved) => ``ProblemStatus.solved
    | _ => none

/-- Convert from a syntax node to a term of type `Category` and annotate the syntax
with the corresponding name's docstring. -/
private def Syntax.toCategory (stx : TSyntax ``CategorySyntax) : CoreM Category := do
  match stx with
  | `(CategorySyntax| high_school) =>
    Elab.addConstInfo stx ``Category.highSchool
    return Category.highSchool
  | `(CategorySyntax| undergraduate) =>
    Elab.addConstInfo stx ``Category.undergraduate
    return Category.undergraduate
  | `(CategorySyntax| graduate) =>
    Elab.addConstInfo stx ``Category.graduate
    return Category.graduate
  | `(CategorySyntax| research $status) =>
    let some n := problemStatus.toName status | throwUnsupportedSyntax
    Elab.addConstInfo status n
    let status ← Lean.Meta.MetaM.run' <|
      unsafe Meta.evalExpr ProblemStatus q(ProblemStatus) (.const n [])
    Elab.addConstInfo stx ``Category.research
    return Category.research status
  | `(CategorySyntax| test) =>
    Elab.addConstInfo stx ``Category.test
    return Category.test
  | `(CategorySyntax| API) =>
    Elab.addConstInfo stx ``Category.API
    return Category.API
  | _ => throwUnsupportedSyntax

syntax (name := Category_attr) "category" CategorySyntax : attr

/-- Specifies the type of a statement, i.e. a math problem, or some API, or some test statement. -/
initialize CategoryAttr : ParametricAttribute Category ←
  registerParametricAttribute {
    name := `Category_attr
    descr := "Annotation of the Category of a given statement"
    getParam _ := fun
      | `(attr| category $s) => withRef s <| do
        Syntax.toCategory s
      | _ => throwUnsupportedSyntax
  }

syntax (name := problemSubject) "AMS" num : attr

/-- Specifies the subject of a math problem. -/
initialize problemSubjectAttr : ParametricAttribute AMS ←
  registerParametricAttribute {
    name := `problemSubject
    descr := "Annotation of the subject of a given problem statement"
    getParam := fun _  stx =>
      match stx with
      | `(attr| AMS $n) => withRef n <| do
        let nVal := n.getNat
        let subject ← Lean.Meta.MetaM.run' <| do
          let name ← numToAMSName nVal
          Elab.addConstInfo stx name
          unsafe Meta.evalExpr AMS q(AMS) (.const name [])
        return subject
      | _ => throwUnsupportedSyntax
  }
