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

-- Erdős Problems URL: https://www.erdosproblems.com/817
import FormalConjectures.Util.ProblemImports

open Filter

/-- A finite arithmetic progression of length $k$ and difference $d$ is a set of the form
$\{a_0, a_0 + d, a_0 + 2d, ..., a_0 + (k - 1) d\}$. -/
def IsFiniteAPWith (k d : ℕ) (s : Set ℕ) := ∃ (a₀ : ℕ), s = { a₀ + i * d | (i : Fin k) }

/- Triviality conditions -/

/-- Only the empty set is a finite arithmetic progression of length $0$. -/
theorem IsFiniteAP.zero {d : ℕ} {s : Set ℕ} : IsFiniteAPWith 0 d s ↔ s = ∅ := by
  simp [IsFiniteAPWith]

/-- Only singletons are finite arithmetic progressions of length $1$. -/
theorem IsFiniteAP.one {d : ℕ} {s : Set ℕ} : IsFiniteAPWith 1 d s ↔ ∃ a₀, s = {a₀} := by
  simp [IsFiniteAPWith]

/-- Only singletons are finite arithmetic progressions of difference $0$. -/
theorem IsFiniteAP.zero_diff {k : ℕ} [NeZero k] {s : Set ℕ} :
    IsFiniteAPWith k 0 s ↔ ∃ a₀, s = {a₀} := by
  simp [IsFiniteAPWith]

/--
A set $s$ contains a non-trivial $k$-term, if there is a difference $d$ such that $s$ is a $k$-term progression with that difference and it contains more than 1 element.
-/
def ContainsNontrivialAP (k : ℕ) (s : Set ℕ) := ∃ d, IsFiniteAPWith k d s ∧ 1 < s.ncard


open scoped Classical in
/-- Define $g_k(n)$ to be the minimal $N$ such that $\{1, ..., N\}$ contains some $A$ of
size $|A| = n$ such that
$$
  \langle A\rangle = \left\{\sum_{a \in A} \epsilon_a a : \epsilon_a \in\{0, 1\}\right\}
$$
contains no non-trivial $k$-term arithmetic progression. -/
noncomputable
def g (k : ℕ) (n : ℕ) : ℕ := sInf { N | ∃ A ⊆ Finset.Icc 1 N, A.card = n ∧
    ∀ s, s ⊆ { ∑ a ∈ B, a | B ∈ A.powerset } → ¬ ContainsNontrivialAP k s }

/-- Let $k\geq 3$. Define $g_k(n)$ to be the minimal $N$ such that
$\{1, ..., N\}$ contains some $A$ of size $|A| = n$ such that
$$
  \langle A\rangle = \left\{\sum_{a \in A} \epsilon_a a : \epsilon_a \in\{0, 1\}\right\}
$$
contains no non-trivial $k$-term arithmetic progression. Estimate $g_k(n)$. In
particular, is it true that
$$
  g_3(n) \gg 3^n
$$ -/
-- Formalisation note : only formalising the "In particular" part
@[problem_status open]
theorem erdos_817 :
    (fun n => (3 ^ n : ℝ)) =O[atTop] fun n => (g 3 n : ℝ) :=
  sorry

/-- A problem of Erd\"{o}s and Sa\'{a}rk\"{o}zy who proved
$$
  g_3(n) \gg \frac{3^n}{n^{O(1)}}.
$$ -/
@[problem_status solved]
theorem erdos_817.variants.bdd_power : ∃ O > (0 : ℝ),
    (fun (n : ℕ) => (3 ^ n : ℝ) / n ^ O) =O[atTop] fun n => (g 3 n : ℝ) :=
  sorry
