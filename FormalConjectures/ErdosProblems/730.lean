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

-- Erdős Problems URL: https://www.erdosproblems.com/730
import FormalConjectures.Util.ProblemImports

abbrev S := {(n, m) : ℕ × ℕ | n ≠ m ∧ ((2*n).choose n).primeFactors = ((2*m).choose m).primeFactors}


/--
Are there infinitely many pairs of integers $n ≠ m$ such that $\binom{2n}{n}$
and $\binom{2m}{m}$ have the same set of prime divisors?
-/
@[category research open]
theorem erdos_730 : S.Infinite := by
  sorry


/--
For example, $(87,88)$ and $(607,608)$ are such pairs.
-/
@[category research solved]
theorem erdos_730.variants.explicit_pairs :
    {(87, 88), (607, 608)} ⊆ S := by
  sorry

/--
Show that for all $n$, the binomial coefficient $\binom{2n}{n}$ is even.
-/
@[category research solved]
theorem erdos_730.variants.two_div_forall (n : ℕ) (h : 0 < n) : 2 ∣ (2*n).choose n := by
  sorry

/--
Show that $(n, n+1) ∈ S$ if and only if for all odd primes $p ≤ n$ we have $n ∉ \{\frac {p−1} 2, p−1\} \mod p$.
-/
@[category research solved]
theorem erdos_730.variants.succ_pair_criterion (n : ℕ) (h : 2 < n) :
    (n, n+1) ∈ S ↔ ∀ p ∈ Set.Ioc 2 n, ∀ [hp : Fact p.Prime], (n : ZMod p) ≠ (p-1) / 2 ∧
      (n : ZMod p) ≠ p-1 := by
  sorry

open scoped Topology in
/--
Standard heuristics then predict there should be $≫ \frac x {(\log x)^2}$
many $n ≤ x$ such that $(n, n+1) ∈ S$.
-/
@[category research open]
theorem erdos_730.variants.succ_pair_growth :
    let C (x : ℝ) : ℝ := (Finset.Icc 0 ⌊x⌋₊ |>.filter fun n => (n, n+1) ∈ S).card
    Filter.Tendsto (fun (x : ℝ) => x / (x.log^2) / C x) Filter.atTop (𝓝 0) := by
  sorry
