/-
Copyright 2025 The Formal Conjectures Authors.

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

/-!
# Erdős Problem 1059

*Reference:* [erdosproblems.com/1059](https://www.erdosproblems.com/1059)
-/

namespace Erdos1059

/-- A prime $p$ satisfies the condition if $p - k!$ is composite
for all factorials $k!$ with $1 \leq k! < p$. -/
def SatisfiesCondition (p : ℕ) : Prop :=
  p.Prime ∧
  ∀ k : ℕ, 1 ≤ k.factorial → k.factorial < p → ¬(p - k.factorial).Prime

/--
Are there infinitely many primes $p$ such that $p - k!$ is composite
for each $k$ such that $1 \leq k! < p$?

This is problem A2 in Guy's collection [Gu04].

[Gu04] Guy, R. K., _Unsolved problems in number theory_. Third edition. Problem Books in Mathematics. Springer-Verlag, New York, 2004.
-/
@[category research open, AMS 11]
theorem erdos_1059 :
    Set.Infinite {p : ℕ | SatisfiesCondition p} ↔ answer(sorry) := by
  sorry

/-- Erdős observed that $p = 101$ satisfies the condition. -/
@[category test, AMS 11]
theorem erdos_1059_example_101 :
    SatisfiesCondition 101 := by
  sorry

/-- Erdős observed that $p = 211$ satisfies the condition. -/
@[category test, AMS 11]
theorem erdos_1059_example_211 :
    SatisfiesCondition 211 := by
  sorry

/-- An integer $n$ satisfies the alternative condition if, for some $l$,
we have $l! < n \leq (l+1)!$, all prime factors of $n$ exceed $l$,
and $n - k!$ is composite for all $1 \leq k \leq l$. -/
def SatisfiesAlternativeCondition (n : ℕ) : Prop :=
  ∃ l : ℕ,
    l.factorial < n ∧
    n ≤ (l + 1).factorial ∧
    (∀ p : ℕ, p.Prime → p ∣ n → p > l) ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ l → n > k.factorial → ¬(n - k.factorial).Prime

/--
Erdős suggested it may be easier to show that there are infinitely many $n$ such that,
if $l! < n \leq (l+1)!$, then all prime factors of $n$ exceed $l$, and all numbers
$n - k!$ are composite for $1 \leq k \leq l$.
-/
@[category research open, AMS 11]
theorem erdos_1059.alternative :
    Set.Infinite {n : ℕ | SatisfiesAlternativeCondition n} ↔ answer(sorry) := by
  sorry

end Erdos1059
