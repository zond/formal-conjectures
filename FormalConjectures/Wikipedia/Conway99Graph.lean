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

-- Wikipedia URL: https://en.wikipedia.org/wiki/Conway%27s_99-graph_problem
import FormalConjectures.Util.ProblemImports

/-
Conway's 99-graph problem
-/
--TODO(firsching): Consider using SimpleGraph.IsSRGWith to formulate the conjecture.
variable {V : Type} {G : SimpleGraph V}
@[category undergraduate]
lemma completeGraphIsClique (s : Finset V) : (⊤ : SimpleGraph V).IsClique s :=
  Pairwise.set_pairwise (fun _ _ a ↦ a) _

variable [Fintype V]

@[category undergraduate]
lemma completeGraph_cliqueSet :
    (⊤ : SimpleGraph V).cliqueSet (Fintype.card V) = {Set.univ.toFinset} := by
  simp only [SimpleGraph.cliqueSet, SimpleGraph.isNClique_iff ⊤, completeGraphIsClique, true_and,
    Set.toFinset_univ]
  exact (Set.Sized.univ_mem_iff fun ⦃x⦄ a ↦ a).mp rfl

variable [DecidableEq V]
/--
Each two non-adjacent vertices have exactly two common neighbors.
-/
def NonEdgesAreDiagonals (G : SimpleGraph V) : Prop :=
   Pairwise fun i j => ¬ G.Adj i j → (G.neighborSet i ∩ G.neighborSet j).ncard = 2

/--
Does there exist an undirected graph with 99 vertices, in which each two adjacent vertices have
exactly one common neighbor, and in which each two non-adjacent vertices have exactly two common
neighbors?
Equivalently, every edge should be part of a unique triangle and every non-adjacent pair should be
one of the two diagonals of a unique 4-cycle.
The first condition is equivalent to being locally linear.
-/
@[category research open]
theorem Conway99Graph : ∃ G : SimpleGraph (Fin 99), G.LocallyLinear ∧ NonEdgesAreDiagonals G :=
  sorry

/--
The triangle is an example with 3 vertices satisfying the condition.
-/
@[category test]
example : (completeGraph (Fin 3)).LocallyLinear ∧ NonEdgesAreDiagonals (completeGraph (Fin 3)) := by
  constructor
  · simp [SimpleGraph.LocallyLinear]
    constructor
    · simp only [SimpleGraph.EdgeDisjointTriangles, Set.Pairwise]
      intro x hx y hy hxy
      have := @completeGraph_cliqueSet (Fin 3) _
      rw [Fintype.card_fin] at this
      rw [this] at hx hy
      rw [hx, hy] at hxy
      tauto
    · intro x y hxy
      use {x, y, 2 * x + 2 * y}
      fin_cases x <;> fin_cases y <;> simp at hxy ⊢ <;> constructor <;> decide
  · tauto

/--
The box product of two triangles is an example with 9 vertices satisfying the condition.
(This graph is the complement of the one described in https://vimeo.com/109815595
and it is also isomorphic to it and to the Paley graph and the graph of the
3-3 duoprism)
-/
def Conway9 := (completeGraph (Fin 3)) □ (completeGraph (Fin 3))

@[category test]
example : NonEdgesAreDiagonals Conway9 := by
  simp only [NonEdgesAreDiagonals, Set.Pairwise]
  have : ∀ i, Fintype ↑(Conway9.neighborSet i) := by
    intro i
    exact Fintype.ofFinite ↑(Conway9.neighborSet i)
  have : ∀ i j, ((Conway9.neighborFinset i) ∩ Conway9.neighborFinset j).card =
    (Conway9.neighborSet i ∩ Conway9.neighborSet j).ncard := by
    simp only [SimpleGraph.neighborFinset]
    intros
    rw [← Set.toFinset_inter, Set.ncard_eq_toFinset_card']
  simp only [← this]
  intro x y
  have ⟨x1, x2⟩ := x
  have ⟨y1, y2⟩ := y
  simp only [Conway9, SimpleGraph.completeGraph_eq_top,
    SimpleGraph.boxProd_adj, SimpleGraph.top_adj, SimpleGraph.boxProd_neighborFinset]
  fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;> decide

lemma completeGraph_boxProd_completeGraph_cliqueSet :
  ((completeGraph V) □ (completeGraph V)).cliqueSet (Fintype.card V) =
  { ({(p,  σ p)| (p : V) } : Finset (V × V)) | σ : Equiv.Perm V } := by
  sorry

-- TODO(firsching): Make this proof faster
set_option maxHeartbeats 400000 in
@[category test]
example : Conway9.LocallyLinear := by
  dsimp [SimpleGraph.LocallyLinear]
  constructor
  · simp only [SimpleGraph.EdgeDisjointTriangles, Set.Pairwise]
    intro x hx y hy hxy
    have := @completeGraph_boxProd_completeGraph_cliqueSet (Fin 3) _ _
    simp only [SimpleGraph.completeGraph_eq_top, Fintype.card_fin,
      Finset.univ_filter_exists] at this
    simp only [Conway9, SimpleGraph.completeGraph_eq_top, this, Set.mem_setOf_eq, Finset.image,
      Fin.univ_val_map, List.ofFn_succ, Fin.isValue, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, List.ofFn_zero, List.toFinset_coe, List.toFinset_cons, List.toFinset_nil,
      insert_emptyc_eq] at hx hy
    have : ∀ (s : Finset (Fin 3 × Fin 3)),
        (∃ (σ : Equiv.Perm (Fin 3)), {(0, σ 0), (1, σ 1), (2, σ 2)} = s) ↔
        s ∈ Finset.image (fun (σ : Equiv.Perm (Fin 3)) =>
        {(0, σ 0), (1, σ 1), (2, σ 2)}) Finset.univ := by
      intro s
      simp only [Fin.isValue, Finset.mem_image, Finset.mem_univ, true_and]
    rw [this x] at hx
    rw [this y] at hy
    have : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
      {
        ⟨![0,1,2], ![0,1,2], by decide, by decide⟩,
        ⟨![0,2,1], ![0,2,1], by decide, by decide⟩,
        ⟨![1,0,2], ![1,0,2], by decide, by decide⟩,
        ⟨![1,2,0], ![2,0,1], by decide, by decide⟩,
        ⟨![2,0,1], ![1,2,0], by decide, by decide⟩,
        ⟨![2,1,0], ![2,1,0], by decide, by decide⟩
      } := by decide
    simp only [Fin.isValue, this, Finset.image_insert, Equiv.coe_fn_mk, Matrix.cons_val_zero,
      Prod.mk_zero_zero, Matrix.cons_val_one, Matrix.head_cons, Prod.mk_one_one,
      Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons,
      Finset.image_singleton, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with hx | hx | hx | hx | hx | hx <;>
    rcases hy with hy | hy | hy | hy | hy | hy <;> simp [hx, hy] at hxy ⊢ <;> decide
  · intro x y
    have ⟨x1, x2⟩ := x
    have ⟨y1, y2⟩ := y
    intro h
    use {(x1, x2), (y1, y2), (x1 + x1 + y1 + y1, x2 + x2 + y2 + y2)}
    simp only [Finset.mem_insert, Prod.mk.injEq, Finset.mem_singleton, true_or, self_eq_add_left,
      Fin.isValue, or_true, and_self, and_true]
    simp only [Conway9, SimpleGraph.completeGraph_eq_top, SimpleGraph.boxProd_adj,
      SimpleGraph.top_adj, ne_eq] at h ⊢
    constructor
    · dsimp [SimpleGraph.IsClique]
      fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;> simp at h ⊢
    · fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;> simp at h ⊢ <;> decide


