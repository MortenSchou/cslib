/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.Euler
public import Cslib.Computability.VAS.ProdGraphFinite
public import Cslib.Computability.VAS.Transformer

/-! # The production graph of a triple

For a triple `γ = (x, c, y)` the *production graph* `G_γ` (Leroux, Section 5.2) has as states the
configurations of `Q_γ` with the unbounded components zeroed out, and as transitions the factors
`q q'` of runs of `Ω_γ`, labelled by the action `q' - q`.

## Main results

* `VAS.Triple.proj_add_intraprod`: `π_γ(c + h)` is the special state `π_γ(c)` for every
  intraproduction `h`; in particular runs of `Ω_γ` start and end there (Corollary 5.9).
* `VAS.Triple.graph_stronglyConnected`: the graph `G_γ` is strongly connected.
* `VAS.Triple.graph_finite`: the graph `G_γ` is finite.
* `VAS.Triple.graph_states_incomparable`: the states of `G_γ` are pairwise incomparable.
* `VAS.Triple.path_of_reach`: runs between configurations of `Q_γ` give paths of `G_γ` with the
  same displacement.

## References

* [J. Leroux, *Vector Addition Systems Reachability Problem (A Simpler Solution)*][Leroux2012]
-/

@[expose] public section

namespace Cslib

variable {ι : Type*}

namespace VAS

namespace Triple

variable {V : VAS ι} (γ : Triple V)

open Classical in
/-- The projection `π_γ` forgetting (zeroing) the unbounded components. -/
noncomputable def proj (q : VASConfig ι) : VASConfig ι :=
  fun i => if i ∈ γ.bounded then q i else 0

/-- The projection keeps the bounded components. -/
theorem proj_apply_of_mem (q : VASConfig ι) {i : ι} (hi : i ∈ γ.bounded) : γ.proj q i = q i := by
  simp only [proj, hi, ↓reduceIte]

/-- The projection zeroes the unbounded components. -/
theorem proj_apply_of_not_mem (q : VASConfig ι) {i : ι} (hi : i ∉ γ.bounded) : γ.proj q i = 0 := by
  simp only [proj, hi, ↓reduceIte]

open Classical in
/-- The production graph `G_γ` of a triple. -/
noncomputable def graph : ProdGraph ι where
  states := γ.proj '' γ.Q
  trans := {t | ∃ π ∈ γ.runs, ∃ (L₁ L₂ : List (VASConfig ι)) (q q' : VASConfig ι),
    π.cfgs = L₁ ++ q :: q' :: L₂ ∧ t = (γ.proj q, q'.toInt - q.toInt, γ.proj q')}

/-- The special state `s_γ = π_γ(c)`. -/
noncomputable def special : VASConfig ι := γ.proj γ.c

/-- The transitions of `G_γ` are the pairs of consecutive configurations of runs of `Ω_γ`. -/
theorem mem_graph_trans {t : ProdGraph.Edge ι} :
    t ∈ γ.graph.trans ↔ ∃ q q' : VASConfig ι, t = (γ.proj q, q'.toInt - q.toInt, γ.proj q') ∧
      ∃ n : ℕ, V.Reach (γ.c + n • γ.x) q ∧ V.Move q q' ∧ V.Reach q' (γ.c + n • γ.y) := by
  constructor
  · rintro ⟨π, ⟨n, hs, ht⟩, L₁, L₂, q, q', hcfg, rfl⟩
    obtain ⟨hm, h1, h2⟩ := π.move_of_cfgs_eq hcfg
    exact ⟨q, q', rfl, n, hs ▸ h1, hm, ht ▸ h2⟩
  · rintro ⟨q, q', rfl, n, h1, hm, h2⟩
    obtain ⟨π, hs, ht, L₁, L₂, hcfg⟩ := Run.exists_run_pair h1 hm h2
    exact ⟨π, ⟨n, hs, ht⟩, L₁, L₂, q, q', hcfg, rfl⟩

/-- The special state is `π_γ(c + h)` for every intraproduction `h`. -/
theorem proj_add_intraprod {h : VASConfig ι} (hh : h ∈ γ.intraprod) :
    γ.proj (γ.c + h) = γ.special := by
  funext i
  by_cases hi : i ∈ γ.bounded
  · rw [proj_apply_of_mem γ _ hi, special, proj_apply_of_mem γ _ hi, Pi.add_apply,
      intraprod_apply_eq_zero γ hh hi, add_zero]
  · rw [proj_apply_of_not_mem γ _ hi, special, proj_apply_of_not_mem γ _ hi]

/-- Multiples of `x` are intraproductions once `n x ▷_c n y`. -/
theorem nsmul_x_mem_intraprod {n : ℕ} (h : V.Reach (γ.c + n • γ.x) (γ.c + n • γ.y)) :
    n • γ.x ∈ γ.intraprod := ⟨n, Reach.refl, h⟩

/-- Multiples of `y` are intraproductions once `n x ▷_c n y`. -/
theorem nsmul_y_mem_intraprod {n : ℕ} (h : V.Reach (γ.c + n • γ.x) (γ.c + n • γ.y)) :
    n • γ.y ∈ γ.intraprod := ⟨n, h, Reach.refl⟩

/-- The two ends of a factor of a run of `Ω_γ` lie in `Q_γ`. -/
theorem mem_Q_of_move {n : ℕ} {q q' : VASConfig ι} (h1 : V.Reach (γ.c + n • γ.x) q)
    (hm : V.Move q q') (h2 : V.Reach q' (γ.c + n • γ.y)) :
    q ∈ γ.Q ∧ q' ∈ γ.Q :=
  ⟨(mem_Q_iff γ).2 ⟨n, h1, LTS.CanReach.head hm h2⟩,
    (mem_Q_iff γ).2 ⟨n, h1.tail hm, h2⟩⟩

/-- The graph `G_γ` is well formed: transitions go between states. -/
theorem graph_wellFormed : γ.graph.WellFormed := by
  intro t ht
  obtain ⟨q, q', rfl, n, h1, hm, h2⟩ := (mem_graph_trans γ).1 ht
  obtain ⟨hq, hq'⟩ := mem_Q_of_move γ h1 hm h2
  exact ⟨⟨q, hq, rfl⟩, ⟨q', hq', rfl⟩⟩

/-- The action of a transition of `G_γ` is an action of the VAS. -/
theorem graph_act_mem (t : γ.graph.trans) : γ.graph.act t ∈ V.acts := by
  obtain ⟨⟨s, a, s'⟩, h⟩ := t
  obtain ⟨q, q', heq, n, h1, ⟨a', ha', hq'⟩, h2⟩ := (mem_graph_trans γ).1 h
  have : a = q'.toInt - q.toInt := (Prod.mk.inj (Prod.mk.inj heq).2).1
  change a ∈ V.acts
  rw [this, hq', add_sub_cancel_left]
  exact ha'

/-- The target of a transition of `G_γ` is determined by its source and its action: on bounded
components it adds the action, and the unbounded components are zero. -/
theorem graph_tgt_apply (t : γ.graph.trans) {i : ι} (hi : i ∈ γ.bounded) :
    (γ.graph.tgt t i : ℤ) = γ.graph.src t i + γ.graph.act t i := by
  obtain ⟨⟨s, a, s'⟩, h⟩ := t
  obtain ⟨q, q', heq, n, h1, hm, h2⟩ := (mem_graph_trans γ).1 h
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ heq
  simp only [ProdGraph.src, ProdGraph.tgt, ProdGraph.act, proj_apply_of_mem γ _ hi,
    Pi.sub_apply, VASConfig.toInt]
  ring

/-- The unbounded components of a target state are zero. -/
theorem graph_tgt_apply_of_not_mem (t : γ.graph.trans) {i : ι} (hi : i ∉ γ.bounded) :
    γ.graph.tgt t i = 0 := by
  obtain ⟨⟨s, a, s'⟩, h⟩ := t
  obtain ⟨q, q', heq, -⟩ := (mem_graph_trans γ).1 h
  obtain ⟨-, -, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ heq
  exact proj_apply_of_not_mem γ _ hi

/-- Runs between configurations of `Q_γ` give paths of `G_γ` with the same displacement. -/
theorem path_of_reach {n : ℕ} {p q : VASConfig ι} (h : V.Reach p q)
    (hp : V.Reach (γ.c + n • γ.x) p) (hq : V.Reach q (γ.c + n • γ.y)) :
    ∃ ρ : List γ.graph.trans, γ.graph.IsPath (γ.proj p) ρ (γ.proj q) ∧
      (ρ.map γ.graph.act).sum = q.toInt - p.toInt := by
  induction h using LTS.CanReach.induction_on with
  | refl => exact ⟨[], .nil _, by simp only [List.map_nil, List.sum_nil, sub_self]⟩
  | @tail b c hb hm ih =>
    obtain ⟨ρ, hρ, hsum⟩ := ih (hq := LTS.CanReach.head hm hq)
    have ht : (γ.proj b, c.toInt - b.toInt, γ.proj c) ∈ γ.graph.trans :=
      (mem_graph_trans γ).2 ⟨b, c, rfl, n, hp.trans hb, hm, hq⟩
    let t : γ.graph.trans := ⟨_, ht⟩
    refine ⟨ρ ++ [t], hρ.append (γ.graph.isPath_single t), ?_⟩
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero, hsum, ProdGraph.act, t]
    abel

/-- Every state of `G_γ` is reachable from the special state. -/
theorem exists_path_from_special {q : VASConfig ι} (hq : q ∈ γ.Q) :
    ∃ ρ, γ.graph.IsPath γ.special ρ (γ.proj q) := by
  obtain ⟨n, h1, h2⟩ := (mem_Q_iff γ).1 hq
  obtain ⟨ρ, hρ, -⟩ := path_of_reach γ h1 (Reach.refl) h2
  have hproj : γ.proj (γ.c + n • γ.x) = γ.special :=
    proj_add_intraprod γ (nsmul_x_mem_intraprod γ (h1.trans h2))
  exact ⟨ρ, hproj ▸ hρ⟩

/-- Every state of `G_γ` reaches the special state. -/
theorem exists_path_to_special {q : VASConfig ι} (hq : q ∈ γ.Q) :
    ∃ ρ, γ.graph.IsPath (γ.proj q) ρ γ.special := by
  obtain ⟨n, h1, h2⟩ := (mem_Q_iff γ).1 hq
  obtain ⟨ρ, hρ, -⟩ := path_of_reach γ h2 h1 (Reach.refl)
  have hproj : γ.proj (γ.c + n • γ.y) = γ.special :=
    proj_add_intraprod γ (nsmul_y_mem_intraprod γ (h1.trans h2))
  exact ⟨ρ, hproj ▸ hρ⟩

/-- **Corollary 5.10**: the graph `G_γ` is strongly connected. -/
theorem graph_stronglyConnected : γ.graph.StronglyConnected := by
  rintro _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩
  obtain ⟨ρ₁, h₁⟩ := exists_path_to_special γ hq
  obtain ⟨ρ₂, h₂⟩ := exists_path_from_special γ hq'
  exact ⟨ρ₁ ++ ρ₂, h₁.append h₂⟩

/-- The special state is a state of `G_γ`. -/
theorem special_mem_states : γ.special ∈ γ.graph.states := ⟨γ.c, c_mem_Q γ, rfl⟩

/-- The graph `G_γ` is finite. -/
theorem graph_finite [Finite ι] : γ.graph.states.Finite ∧ γ.graph.trans.Finite := by
  classical
  have hstates : γ.graph.states.Finite := by
    refine (Set.Finite.pi (t := fun i : ι =>
      if i ∈ γ.bounded then (fun q : VASConfig ι => q i) '' γ.Q else {0})
      (κ := fun _ => ℕ) (fun i => ?_)).subset ?_
    · by_cases hi : i ∈ γ.bounded
      · simp only [hi, ↓reduceIte]; exact hi
      · simp only [hi, ↓reduceIte]; exact Set.finite_singleton 0
    · rintro _ ⟨q, hq, rfl⟩ i -
      by_cases hi : i ∈ γ.bounded
      · simp only [hi, ↓reduceIte, proj_apply_of_mem γ _ hi]; exact ⟨q, hq, rfl⟩
      · simp only [hi, ↓reduceIte, proj_apply_of_not_mem γ _ hi, Set.mem_singleton_iff]
  refine ⟨hstates, (hstates.prod ((V.acts.finite_toSet).prod hstates)).subset ?_⟩
  intro t ht
  refine ⟨graph_wellFormed γ t ht |>.1, ?_, graph_wellFormed γ t ht |>.2⟩
  exact graph_act_mem γ ⟨t, ht⟩

/-- **Corollary 5.11**: the states of `G_γ` are pairwise incomparable. -/
theorem graph_states_incomparable [Finite ι] {s s' : VASConfig ι} (hs : s ∈ γ.graph.states)
    (hs' : s' ∈ γ.graph.states) (hle : s ≤ s') : s = s' := by
  have := Fintype.ofFinite ι
  obtain ⟨q, hq, rfl⟩ := hs
  obtain ⟨q', hq', rfl⟩ := hs'
  obtain ⟨h₀, hh₀, hb⟩ := exists_intraprod_support γ
  have hpos : ∀ i, i ∉ γ.bounded → 1 ≤ h₀ i := fun i hi => by
    have : h₀ i ≠ 0 := fun h => hi (hb ▸ h)
    omega
  have hzero : ∀ i, i ∈ γ.bounded → h₀ i = 0 := fun i hi => by
    have := hb ▸ hi
    exact this
  set k := ∑ j, q j with hk
  have hk' : k • h₀ ∈ γ.intraprod := (intraprod_periodic γ).nsmul_mem hh₀ k
  have hqle : q ≤ q' + k • h₀ := by
    intro i
    by_cases hi : i ∈ γ.bounded
    · have := hle i
      rw [proj_apply_of_mem γ _ hi, proj_apply_of_mem γ _ hi] at this
      simp only [Pi.add_apply, Pi.smul_apply, hzero i hi, smul_zero, add_zero]
      exact this
    · have h1 : q i ≤ k := Finset.single_le_sum (f := fun j => q j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
      have h2 := hpos i hi
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
  obtain ⟨h, hh, hge⟩ := exists_intraprod_ge γ hq (Q_add_intraprod γ hq' hk') hqle
  refine le_antisymm hle fun i => ?_
  by_cases hi : i ∈ γ.bounded
  · rw [proj_apply_of_mem γ _ hi, proj_apply_of_mem γ _ hi]
    have := hge i
    simp only [Pi.add_apply, Pi.smul_apply, hzero i hi, smul_zero, add_zero,
      intraprod_apply_eq_zero γ hh hi] at this
    exact this
  · rw [proj_apply_of_not_mem γ _ hi, proj_apply_of_not_mem γ _ hi]

end Triple

open Triple in
/-- **Corollary 5.12**: for a fixed capacity `c` there are only finitely many production graphs. -/
theorem finite_prodGraphs [Finite ι] (c : VASConfig ι) :
    {G : ProdGraph ι | ∃ γ : Triple V, γ.c = c ∧ G = γ.graph}.Finite := by
  classical
  have := Fintype.ofFinite ι
  have hsub : {G : ProdGraph ι | ∃ γ : Triple V, γ.c = c ∧ G = γ.graph} ⊆
      ⋃ I : Set ι,
        {G : ProdGraph ι | ∃ γ : Triple V, γ.c = c ∧ γ.bounded = I ∧ G = γ.graph} := by
    rintro G ⟨γ, hc, rfl⟩
    exact Set.mem_iUnion.2 ⟨γ.bounded, γ, hc, rfl, rfl⟩
  refine Set.Finite.subset (Set.finite_iUnion fun I => ?_) hsub
  let s₀ : VASConfig ι := fun i => if i ∈ I then c i else 0
  let step : VASConfig ι → (ι → ℤ) → VASConfig ι := fun s a i =>
    if i ∈ I then ((s i : ℤ) + a i).toNat else 0
  have hspec (γ : Triple V) (hc : γ.c = c) (hI : γ.bounded = I) : γ.special = s₀ := by
    funext i
    simp only [special, proj, s₀, hI, hc]
  refine ProdGraph.finite_of_incomparable (A := V.acts) (s₀ := s₀) (step := step) _
    ?_ ?_ ?_ ?_ ?_ ?_
  · rintro G ⟨γ, -, -, rfl⟩
    exact graph_wellFormed γ
  · rintro G ⟨γ, hc, hI, rfl⟩
    exact hspec γ hc hI ▸ special_mem_states γ
  · rintro G ⟨γ, hc, hI, rfl⟩ s ⟨q, hq, rfl⟩
    exact hspec γ hc hI ▸ exists_path_from_special γ hq
  · rintro G ⟨γ, -, -, rfl⟩ s hs s' hs' hle
    exact graph_states_incomparable γ hs hs' hle
  · rintro G ⟨γ, -, -, rfl⟩ t ht
    exact graph_act_mem γ ⟨t, ht⟩
  · rintro G ⟨γ, hc, hI, rfl⟩ ⟨s, a, s'⟩ ht
    funext i
    by_cases hi : i ∈ I
    · have : (s' i : ℤ) = s i + a i := graph_tgt_apply γ ⟨(s, a, s'), ht⟩ (hI ▸ hi)
      simp only [step, hi, ↓reduceIte]
      omega
    · have := graph_tgt_apply_of_not_mem γ ⟨(s, a, s'), ht⟩ (hI ▸ hi)
      simp only [step, hi, ↓reduceIte]
      exact this

end VAS

end Cslib
