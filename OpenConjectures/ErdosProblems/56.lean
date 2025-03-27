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

-- Erdos Problems URL: https://www.erdosproblems.com/go_to/56
import OpenConjectures.Util.ProblemImports

/--
Say a set of natural numbers is `k`-weakly divisible if any `k+1` elements
of `A` are not relatively prime.
-/
def WeaklyDivisible (k : ℕ) (A : Finset ℕ) : Prop :=
    ∀ s ∈ A.powersetCard (k+1),
    ∃ᵉ (a ∈ s) (b ∈ s), ¬ a.Coprime b

--TODO(lezeau): we shouldn't need to open `Classical` here!
open Classical in
/--
`MaxWeaklyDivisible N k` is the size of the largest k-weakly divisible subset of `{1,..., N}`
-/
noncomputable def MaxWeaklyDivisible (N : ℕ) (k : ℕ) : ℕ :=
    (Finset.Icc 1 N).powerset.filter (WeaklyDivisible k) |>.sup
    Finset.card

/--
`FirstPrimesMultiples N k` is the set of numbers in `{1,..., N}` that are
a multiple of one of the first `k` primes.
-/
noncomputable def FirstPrimesMultiples (N k : ℕ) : Finset ℕ :=
    (Finset.Icc 1 N).filter fun i => ∃ j < k, (j.nth Nat.Prime ∣ i)

/--
An example of a `k`-weakly divisible set is the subset of `{1, ..., N}`
containing the multiples of the first `k` primes.
-/
lemma weaklyDivisible_firstPrimesMultiples (N k : ℕ) (hN : 1 ≤ N) :
    WeaklyDivisible k (FirstPrimesMultiples N k) := by
  sorry


/--
Suppose `A⊆{1,…,N}` is such that there are no `k+1` elements of `A`
which are relatively prime. An example is the set of all multiples of
the first `k` primes. Is this the largest such set?
-/
@[problem_status solved]
theorem erdos_56 (N : ℕ) (hN : 1 ≤ N)
    (k : ℕ) : MaxWeaklyDivisible N k = (FirstPrimesMultiples N k).card := by
  sorry
