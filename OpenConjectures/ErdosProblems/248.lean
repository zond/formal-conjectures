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

-- Erdos Problems URL: https://www.erdosproblems.com/248
import OpenConjectures.Util.ProblemImports

open scoped ArithmeticFunction

/--
Are there infinitely many $n$ such that, for all $k\geq 1$
$$
  \omega(n + k) \ll k?
$$
(Here $\omega(n)$ is the number of distinct prime divisors
of $n$.)
-/
@[problem_status open]
theorem erdos_826 : ∃ C > (0 : ℝ), { n | ∀ k ≥ 1, ω (n + k) ≤ C * k }.Infinite :=
  sorry
