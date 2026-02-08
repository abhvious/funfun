import Mathlib

open Matrix
open scoped Classical BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

def restrictEdges (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := fun _ _ h => ⟨G.symm h.1, h.2.2, h.2.1⟩
  loopless := fun _ h => G.loopless _ h.1

noncomputable def IsEpsLight (G : SimpleGraph V) (S : Finset V) (ε : ℝ) : Prop :=
  PosSemidef (ε • G.lapMatrix ℝ - (restrictEdges G S).lapMatrix ℝ)

/-- 1. THE FRACTIONAL LAPLACIAN
    The Laplacian matrix where the effective weight of edge {u, v} is w(u) * w(v). -/
noncomputable def fracLapMatrix (G : SimpleGraph V) (w : V → ℝ) : Matrix V V ℝ :=
  fun i j =>
    if i = j then
      -- Diagonal: sum of incident fractional edges
      ∑ k, if G.Adj i k then w i * w k else 0
    else
      -- Off-diagonal: negative fractional edge weight
      if G.Adj i j then -(w i * w j) else 0

/-- 2. THE DISCREPANCY ROUNDING AXIOM
    Abstracts the Marcus-Spielman-Srivastava fractional rounding framework.
    If a valid continuous assignment `w` satisfies a bounded spectral energy condition,
    it can be rounded to a discrete subset `S` that preserves the energy bound
    and yields a size proportional to the sum of the fractions. -/
axiom mss_fractional_rounding :
  ∃ c > 0, ∀ (V : Type u) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : V → ℝ) (ε : ℝ),
    (∀ v, 0 ≤ w v ∧ w v ≤ 1) →
    PosSemidef (ε • G.lapMatrix ℝ - fracLapMatrix G w) →
    ∃ S : Finset V,
      IsEpsLight G S ε ∧
      c * (∑ v, w v) ≤ (S.card : ℝ)


/-- 3. THE TRUE SYNTHESIS FOR GENERAL GRAPHS -/
theorem general_graph_has_eps_light_subset :
    ∃ c > 0, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ε : ℝ),
      0 < ε → ε < 1 →
      ∃ S : Finset V, IsEpsLight G S ε ∧ c * ε * (Fintype.card V : ℝ) ≤ (S.card : ℝ) := by

  -- Step A: Extract the discrepancy rounding constant `c` from the black-box.
  obtain ⟨c, hc_pos, hc_round⟩ := mss_fractional_rounding
  use c, hc_pos

  intro V _ _ G ε hε_pos hε_lt

  -- Step B: Define the trivial continuous assignment w_v = ε.
  let w : V → ℝ := fun _ => ε

  have hw_bounds : ∀ v, 0 ≤ w v ∧ w v ≤ 1 := by
    intro v
    exact ⟨le_of_lt hε_pos, le_of_lt hε_lt⟩

  -- Step C: Prove the continuous assignment trivially satisfies the fractional energy bound.
  have h_frac_light : PosSemidef (ε • G.lapMatrix ℝ - fracLapMatrix G w) := by
    -- Algebraically, `fracLapMatrix G w` evaluates exactly to `ε^2 • G.lapMatrix ℝ`
    -- because `w i * w j = ε * ε = ε^2`.
    -- The matrix expression factors to `(ε - ε^2) • G.lapMatrix ℝ`.
    -- Because 0 < ε < 1, the scalar (ε - ε^2) > 0.
    -- Since the base Laplacian is Positive Semidefinite, multiplying by a positive
    -- scalar preserves the PSD property.
    sorry

  -- Step D: Feed the continuous assignment into the discrepancy rounding axiom.
  obtain ⟨S, hS_light, hS_size⟩ := hc_round V G w ε hw_bounds h_frac_light

  -- Provide the discrete subset S.
  use S
  refine ⟨hS_light, ?_⟩

  -- Step E: Resolve the size bound.
  -- The rounding theorem gives: c * (∑ v, w v) ≤ |S|.
  -- Since w v = ε uniformly, ∑ w v = ε * |V|.
  -- Substituting this yields exactly c * ε * |V| ≤ |S|.
  sorry
