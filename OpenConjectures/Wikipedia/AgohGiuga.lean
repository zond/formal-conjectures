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

--Wikipedia URL: https://en.wikipedia.org/wiki/Agoh-Giuga_conjecture
import OpenConjectures.Util.ProblemImports

/-!

The **Agoh-Giuga Conjecture**.

References:
* Wikipedia: https://en.wikipedia.org/wiki/Agoh-Giuga_conjecture
* G. Giuga, _Su una presumibile proprieta caratteristica dei numeri primi_
* E. Bedocchi, _Note on a conjecture about prime numbers_
* D. Borwein, J. M. Borwein, P. B. Borwein, and R. Girgensohn, _Giuga’s conjecture on primality_
* V. Tipu, _A Note on Giuga’s Conjecture_

-/

/--
The **Agoh-Giuga Conjecture**, Agoh's formulation.
An integer `p ≥ 2` is prime if and only if we have
`p*B_{p-1} ≡ -1 [MOD p]`
-/
def AgohGiugaCongr : Prop :=
  ∀ p ≥ 2, p.Prime ↔ ∃ (k : ℤ), p*k = p*bernoulli' (p-1 : ℕ) + 1

/--
The **Agoh-Giuga Conjecture**, Giuga's formulation.
An integer `p ≥ 2` is prime if and only if it satifies the congruence
`∑_{i=1}^{p-1} i^{p-1} ≡ -1 [MOD p]`.
-/
def AgohGiugaSum : Prop := ∀ p ≥ 2, p.Prime ↔
  p ∣ 1 + ∑ i in Finset.Ioo 0 p, i^(p - 1 : ℕ)


/--The **Agoh-Giuga Conjecture**, Agoh's formulation-/
@[problem_status open]
theorem agoh_giuga : AgohGiugaCongr := by
  sorry


/--The **Agoh-Giuga Conjecture**, Giuga's formulation-/
@[problem_status open]
theorem agoh_giuga.variants.giuga : AgohGiugaSum := by
  sorry


/--The two statements of the conjecture are equivalent.-/
@[problem_status solved]
theorem agoh_giuga.variants.equivalence : AgohGiugaCongr ↔ AgohGiugaSum := by
  sorry


/--
A Giuga number is a counterexample to Giuga's conjecture.
-/
def IsGiuga (p : ℕ) : Prop :=
    ¬ p.Prime ∧ p ∣ 1 + ∑ i in Finset.Ioo 0 p, i^(p - 1 : ℕ)

/--
A Carmichael number is a natural number `n` such that for all `b ≥ 1`,
we have `b^n ≡ b (mod n)`.
-/
def IsCarmichael (n : ℕ) : Prop :=
  ∀ b ≥ 1, n.FermatPsp b

/--
A natural number `a` is Carmichael if and only it it is squarefree and
for all primes `p` that divide it, we have `p^2(p-1) | (a - p)`.
-/
@[problem_status solved]
theorem agoh_giuga.variants.nat_fermatPsp_iff (a : ℕ) :
    IsCarmichael a ↔ Squarefree a ∧
      ∀ p, p.Prime → p ∣ a → p^2 * (p-1 : ℕ) ∣ (a - p : ℕ) := by
  --This should probably be in Mathlib
  sorry

/--
Every Giuga number is a Carmichael number.
-/
@[problem_status solved]
theorem agoh_giuga.variants.isGiuga_implies_nat_fermatPsp
    (a : ℕ) (ha : IsGiuga a) : IsCarmichael a := by
  sorry

/--
Giuga showed that a number `n` is Giuga if and only if it is
Carmichael and `∑_{p|n} 1/p - 1/n ∈ ℕ`
Ref: G. Giuga, _Su una presumibile proprieta caratteristica dei numeri primi_
-/
@[problem_status solved]
theorem agoh_giuga.variants.isGiuga_iff (a : ℕ) :
    IsGiuga a ↔ IsCarmichael a ∧ ∃ n, ∑ p in a.primeFactors, (1 / p : ℚ) - 1 / a = n := by
  sorry


/--
Giuga showed that a Giuga number has at least 9 prime factors.
Ref: G. Giuga, _Su una presumibile proprieta caratteristica dei numeri primi_
-/
@[problem_status solved]
theorem agoh_giuga.variants.le_primeFactors_card_of_isGiuga
    (a : ℕ) (ha : IsGiuga a) : 9 ≤ a.primeFactors.card := by
  sorry


/--
Giuga showed that any Giuga number has at least 1000 digits.
Ref: G. Giuga, _Su una presumibile proprieta caratteristica dei numeri primi_
-/
@[problem_status solved]
theorem agoh_giuga.variants._1000_le_digits_length_of_isGiuga
    (a : ℕ) (ha : IsGiuga a) : 1000 ≤ (Nat.digits 10 a).length := by
  sorry


/--
Bedocchi showed that any Giuga number has at least 1700 digits.
Ref: E. Bedocchi, _Note on a conjecture about prime numbers_
-/
@[problem_status solved]
theorem agoh_giuga.variants._1700_le_digits_length_of_isGiuga
    (a : ℕ) (ha : IsGiuga a) : 1700 ≤ (Nat.digits 10 a).length := by
  sorry


/--
Borwein, Borwein, Borwein and Girgensohn showed that any Giuga
number has at least 13000 digits.
Ref: D. Borwein, J. M. Borwein, P. B. Borwein, and R. Girgensohn, _Giuga’s conjecture on primality_
-/
@[problem_status solved]
theorem agoh_giuga.variants._13000_le_digits_length_of_isGiuga
    (a : ℕ) (ha : IsGiuga a) : 13000 ≤ (Nat.digits 10 a).length := by
  sorry


open Classical in
/--
Let `G(X)` denote the number of exceptions `n ≤ X` to Giuga’s conjecture.
Then for `X` larger than an absolute constant which can be made
explicit, `G(X) ≪ X^{1/2} log X`.
Ref: Vicentiu Tipu, _A Note on Giuga’s Conjecture_
-/
@[problem_status solved]
theorem agoh_giuga.variants.isGiuga_growth
    (G : ℕ → ℕ) (hG : G = fun x => Finset.Icc 1 x |>.filter IsGiuga |>.card) :
    ∃ N O, ∀ n ≥ N, G n ≤ O * (n : ℝ).sqrt * (n : ℝ).log := by
  sorry
