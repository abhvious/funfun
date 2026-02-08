import Mathlib

open Matrix
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph G_S with the same vertex set V, but only the edges between vertices in S. -/
def restrictEdges (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm _ _ h := ⟨G.symm h.1, h.2.2, h.2.1⟩
  loopless _ h := G.loopless _ h.1

/--
If S is an independent set, then L_S is the zero matrix,
and S is trivially ε-light for any ε ≥ 0.
-/
theorem independent_set_is_eps_light (G : SimpleGraph V) (S : Set V) (ε : ℝ)
    (h_indep : G.IsIndepSet S) (h_eps : 0 ≤ ε) :
    PosSemidef (ε • G.lapMatrix ℝ - (restrictEdges G S).lapMatrix ℝ) := by
  sorry

/-- A subset S is ε-light if the matrix εL - L_S is positive semidefinite. -/
noncomputable def IsEpsLight (G : SimpleGraph V) (S : Finset V) (ε : ℝ) : Prop :=
  PosSemidef (ε • G.lapMatrix ℝ - (restrictEdges G S).lapMatrix ℝ)

/--
If c is a universal constant such that for *every* finite graph and *every* ε ∈ (0, 1),
there exists an ε-light subset S of size at least c * ε * |V|, then c ≤ 1/2.
-/
theorem eps_light_constant_le_half (c : ℝ)
    (h_univ : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ε : ℝ),
      0 < ε → ε < 1 →
      ∃ S : Finset V, IsEpsLight G S ε ∧ c * ε * (Fintype.card V : ℝ) ≤ (S.card : ℝ)) :
    c ≤ 1 / 2 := by
  sorry
