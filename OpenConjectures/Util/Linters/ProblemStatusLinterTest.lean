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

import OpenConjectures.Util.Linters.ProblemStatusLinter

/-- warning: Theorems should have a problem status attribute -/
#guard_msgs in
theorem test_0 : 1 + 1 = 2 := by
  rfl

/-- warning: Theorems should have no more than one problem status attribute. -/
#guard_msgs in
@[problem_status open, problem_status solved]
theorem test_2 : 1 + 1 = 2 := by
  rfl

--The linter is compatible with theorems having other attributes.
#guard_msgs in
@[simp, problem_status open]
theorem test_1 : 1 + 1 = 2 := by
  rfl

--The order of attributes is irrelevant.
#guard_msgs in
@[problem_status open, simp]
theorem test_3 : 1 + 1 = 2 := by
  rfl

/-- warning: Lemmas shouldn't have a problem status attribute. -/
#guard_msgs in
@[problem_status open]
lemma test_4 : 1 + 1 = 2 := by
  rfl


/-- warning: Examples shouldn't have a problem status attribute. -/
#guard_msgs in
@[problem_status open]
example : 1 + 1 = 2 := by
  rfl
