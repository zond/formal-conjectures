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

/-!
# Conjecture 6.2

Definitions from the beginning of the paper, conjecture from the end.

*Reference:* [arxiv/2410.22607](https://arxiv.org/abs/2410.22607)
**Packing Designs with large block size**
by *Andrea C. Burgess, Peter Danziger, Muhammad Tariq Javed*

-/

variable (v k t l n : ℕ) (ht: 0 < t) (hl : 0 < l) (htk : t ≤ k) (hkv : k ≤ v)

/--
Given positive integers $v,k,t$ and $\lambda$ with $v \geq k \geq t$,
a _packing design_ $PD_{\lambda}(t,k,v)$ is a pair $(V,\mathcal{B})$,
where $V$ is a $v$-set and $\mathcal{B}$ is a collection of $k$-subsets of $V$
such that each $t$-subset of $V$ appears in at most $\lambda$ elements of $\mathcal{B}$.
The elements of $V$ are called _points_ and the elements of $\mathcal{B}$ are
_blocks_.
-/
structure PackingDesign where
  𝓑 : Finset (Finset (Fin v))
  blocks_contains_only_k_sets : ∀ b ∈ 𝓑,  b.card = k
  condition : ∀ T : Finset (Fin v), T.card = t →
    (𝓑.filter fun B => T ⊆ B).card ≤ l


/-- We denote by $PD_{\lambda}(n;t,k,v)$ a $PD_{\lambda}(t,k,v)$ of size $n$. -/
local notation "PD_"l"("t ", " k ", " v  ")" => PackingDesign v k t l

/-- The maximum size of a $PD_{\lambda}(t,k,v)$ is called the _packing number_ ...-/
noncomputable def PackingNumber := sSup <| { (p.𝓑.card : ℕ)| (p : PD_(l)(t, k, v)) }

/-- .. $PDN_{\lambda}(t,k,v)$.-/
local notation "PDN_"l"("t ", " k ", " v  ")" => PackingNumber v k t l


/--
We primarily consider the case $t=2$, and in this case will
remove $t$ from the notation, and write $PD_{\lambda}(k,v)$, ...
-/
local notation "PD_"l"(" k ", " v ")" => PackingDesign v k 2 l
/-- [...] and $PDN_{\lambda}(k,v)$.-/
local notation "PDN_"l"("k ", " v  ")" => PackingNumber v k 2 l

/--
If $\lambda=1$, we will also drop it from the notation.
-/
local notation "PD(" k ", " v ")" => PackingDesign v k 2 1
local notation "PD("t ", " k ", " v  ")" => PackingDesign v k t 1
local notation "PDN(" k ", " v  ")" => PackingNumber v k 2 1


/--
The following blocks form a $PD(4;3,6)$.
$$
\begin{array}{l}
\{0,1,2\} \\
\{0,3,4\} \\
\{1,3,5\} \\
\{2,4,5\}
\end{array}
$$
-/
def examplePackingDesign : PD(3, 6) where
  𝓑 := {{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}}
  blocks_contains_only_k_sets b hb := by
    simp_all only [Fin.isValue, Finset.mem_insert, Finset.mem_singleton]
    rcases hb with h | h | h | h <;>
    subst h <;>
    simp_all only [Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self,
      not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton]
  condition T := by
    intro hT
    fin_cases T
    all_goals try {absurd hT; decide}
    all_goals try decide

local notation "alpha_"l"("n")" => Nat.choose n (l + 1)

/-
If $nk-\alpha_{\lambda}(n) \leq \lambda v < (n+1)k-\alpha_{\lambda}(n+1)$, then $PDN_{\lambda}(k,v)=n$.
-/
@[category research open]
theorem arxiv.id421022607.conjecture6_2
    (hl : 0 < l) (htk : 2 ≤ k) (hkv : k ≤ v) (hln : l + 2 ≤ n)
    (h_lower : n * k ≤ l * v + (alpha_(l)(n)))
    (h_upper : l * v + alpha_(l)(n + 1) < (n + 1) * k) :
  PDN_(l)(k, v) = n := by sorry
