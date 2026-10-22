/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.Euler
public import Mathlib.Order.WellQuasiOrder

/-! # Finiteness of classes of production graphs

A König-style finiteness argument (Leroux, Corollary 5.12): a class of deterministic graphs, all
rooted at the same state, with pairwise incomparable states and labels in a fixed finite set, has
only finitely many states and finitely many members. The argument uses Dickson's lemma on the
states and König's lemma on the tree of shortest words.

## Main results

* `ProdGraph.finite_states_of_incomparable`: the union of the states of the graphs in the class is
  finite.
* `ProdGraph.finite_of_incomparable`: the class itself is finite.
-/

@[expose] public section

namespace Cslib

variable {ι : Type*}

/-! ### König's lemma for prefix-closed sets of words -/

/-- **König's lemma** for prefix-closed sets of words over a finite alphabet: a prefix-closed set
of words that contains no arbitrarily long prefixes of an infinite word is finite. -/
theorem finite_of_prefixClosed {Λ : Type*} [Finite Λ] (T : Set (List Λ))
    (hT : ∀ u v, u ++ v ∈ T → u ∈ T)
    (hbr : ∀ f : ℕ → Λ, ∃ n, (List.range n).map f ∉ T) : T.Finite := by
  by_contra hinf
  -- `Inf ℓ`: infinitely many words of `T` extend `ℓ`
  let Inf : List Λ → Prop := fun ℓ => {t ∈ T | ℓ <+: t}.Infinite
  have h0 : Inf [] := by
    refine Set.Infinite.mono ?_ (Set.not_finite.1 hinf)
    intro t ht
    exact ⟨ht, List.nil_prefix⟩
  have hstep : ∀ ℓ, Inf ℓ → ∃ a : Λ, Inf (ℓ ++ [a]) := by
    intro ℓ hℓ
    by_contra hne
    push Not at hne
    have hfin : {t ∈ T | ℓ <+: t}.Finite := by
      have : {t ∈ T | ℓ <+: t} ⊆ {ℓ} ∪ ⋃ a : Λ, {t ∈ T | ℓ ++ [a] <+: t} := by
        rintro t ⟨htT, k, rfl⟩
        cases k with
        | nil => left; simp only [List.append_nil, Set.mem_singleton_iff]
        | cons a k =>
          right
          simp only [Set.mem_iUnion]
          exact ⟨a, htT, k, by simp only [List.append_assoc, List.singleton_append]⟩
      refine Set.Finite.subset (Set.finite_singleton ℓ |>.union (Set.finite_iUnion fun a => ?_))
        this
      exact Set.not_infinite.1 (hne a)
    exact hℓ hfin
  choose a ha using fun ℓ : {ℓ : List Λ // Inf ℓ} => hstep ℓ.1 ℓ.2
  let seq : ℕ → {ℓ : List Λ // Inf ℓ} := fun n =>
    Nat.rec ⟨[], h0⟩ (fun _ ℓ => ⟨ℓ.1 ++ [a ℓ], ha ℓ⟩) n
  have hseq : ∀ n, (seq (n + 1)).1 = (seq n).1 ++ [a (seq n)] := fun n => rfl
  have hrange : ∀ n, (List.range n).map (fun k => a (seq k)) = (seq n).1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.map_append, ih, hseq]; rfl
  obtain ⟨n, hn⟩ := hbr (fun k => a (seq k))
  apply hn
  rw [hrange]
  obtain ⟨t, ⟨htT, k, hk⟩⟩ := (seq n).2.nonempty
  exact hT _ k (hk ▸ htT)

namespace ProdGraph

section Finite

variable {A : Finset (ι → ℤ)} (s₀ : VASConfig ι)
  (step : VASConfig ι → (ι → ℤ) → VASConfig ι)

/-- `Walk G s w`: from `s`, the word `w` is read along transitions of `G`, the successor state
being given by `step`. -/
def Walk (G : ProdGraph ι) : VASConfig ι → List A → Prop
  | _, [] => True
  | s, a :: w => (s, a.1, step s a.1) ∈ G.trans ∧ Walk G (step s a.1) w

/-- The state reached from `s` after reading `w`. -/
def reached (s : VASConfig ι) (w : List A) : VASConfig ι := w.foldl (fun s a => step s a.1) s

variable {s₀ step}

/-- A walk along a concatenation splits into two walks. -/
theorem walk_append {G : ProdGraph ι} {s : VASConfig ι} {u v : List A} :
    Walk step G s (u ++ v) ↔ Walk step G s u ∧ Walk step G (reached step s u) v := by
  induction u generalizing s with
  | nil => simp only [List.nil_append, Walk, reached, List.foldl_nil, true_and]
  | cons a u ih =>
    simp only [List.cons_append, Walk, ih, reached, List.foldl_cons, and_assoc]

/-- The state reached along a concatenation. -/
theorem reached_append (s : VASConfig ι) (u v : List A) :
    reached step s (u ++ v) = reached step (reached step s u) v := by
  simp only [reached, List.foldl_append]

/-- Walks of a well-formed graph stay among its states. -/
theorem reached_mem {G : ProdGraph ι} (hwf : G.WellFormed) {s : VASConfig ι}
    (hs : s ∈ G.states) {w : List A} (hw : Walk step G s w) : reached step s w ∈ G.states := by
  induction w generalizing s with
  | nil => exact hs
  | cons a w ih =>
    exact ih (hwf _ hw.1).2 hw.2

/-- Paths of a deterministic graph are walks. -/
theorem exists_word_of_path {G : ProdGraph ι}
    (hacts : ∀ t ∈ G.trans, t.2.1 ∈ A) (hdet : ∀ t ∈ G.trans, t.2.2 = step t.1 t.2.1)
    {s₁ s₂ : VASConfig ι} {ρ : List G.trans} (hρ : G.IsPath s₁ ρ s₂) :
    ∃ w : List A, Walk step G s₁ w ∧ reached step s₁ w = s₂ := by
  induction hρ with
  | nil s => exact ⟨[], trivial, rfl⟩
  | cons t _ ih =>
    obtain ⟨w, hw, hr⟩ := ih
    have h : G.tgt t = step (G.src t) (G.act t) := hdet t.1 t.2
    rw [h] at hw hr
    exact ⟨⟨G.act t, hacts t.1 t.2⟩ :: w, ⟨by rw [← h]; exact t.2, hw⟩, hr⟩

/-- A word is *short* in `G` if it is a walk from `s₀` and no shorter walk reaches the same
state. -/
def Short (G : ProdGraph ι) (w : List A) : Prop :=
  Walk step G s₀ w ∧ ∀ w' : List A, Walk step G s₀ w' → reached step s₀ w' = reached step s₀ w →
    w.length ≤ w'.length

/-- The union of the states of a class of deterministic graphs rooted at `s₀`, whose states are
pairwise incomparable, is finite (Leroux, Corollary 5.12). -/
theorem finite_states_of_incomparable [Finite ι] (𝒢 : Set (ProdGraph ι))
    (hwf : ∀ G ∈ 𝒢, G.WellFormed) (h0 : ∀ G ∈ 𝒢, s₀ ∈ G.states)
    (hreach : ∀ G ∈ 𝒢, ∀ s ∈ G.states, ∃ p, G.IsPath s₀ p s)
    (hinc : ∀ G ∈ 𝒢, ∀ s ∈ G.states, ∀ s' ∈ G.states, s ≤ s' → s = s')
    (hacts : ∀ G ∈ 𝒢, ∀ t ∈ G.trans, t.2.1 ∈ A)
    (hdet : ∀ G ∈ 𝒢, ∀ t ∈ G.trans, t.2.2 = step t.1 t.2.1) :
    (⋃ G ∈ 𝒢, G.states).Finite := by
  have _ := Fintype.ofFinite ι
  let T : Set (List A) := {w | ∃ G ∈ 𝒢, Short (s₀ := s₀) (step := step) G w}
  have hTfin : T.Finite := by
    refine finite_of_prefixClosed T ?_ ?_
    · rintro u v ⟨G, hG, hwalk, hmin⟩
      refine ⟨G, hG, (walk_append.1 hwalk).1, fun w' hw' heq => ?_⟩
      have h1 : Walk step G s₀ (w' ++ v) := by
        refine walk_append.2 ⟨hw', ?_⟩
        rw [heq]
        exact (walk_append.1 hwalk).2
      have := hmin (w' ++ v) h1 (by rw [reached_append, heq, ← reached_append])
      simp only [List.length_append] at this ⊢
      omega
    · intro f
      by_contra hcon
      push Not at hcon
      choose G hG hshort using hcon
      obtain ⟨m, n, hmn, hle⟩ := wellQuasiOrdered_le
        (fun n => reached step s₀ ((List.range n).map f))
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hmn
      have hp : (List.range (m + k + 1)).map f =
          (List.range m).map f ++ (List.range (k + 1)).map (fun j => f (m + j)) := by
        rw [show m + k + 1 = m + (k + 1) by omega, List.range_add, List.map_append,
          List.map_map]
        rfl
      have hwalk := (hshort (m + k + 1)).1
      rw [hp] at hwalk
      have hwalk' := (walk_append.1 hwalk).1
      have hmem₁ : reached step s₀ ((List.range m).map f) ∈ (G (m + k + 1)).states :=
        reached_mem (hwf _ (hG _)) (h0 _ (hG _)) hwalk'
      have hmem₂ : reached step s₀ ((List.range (m + k + 1)).map f) ∈ (G (m + k + 1)).states :=
        reached_mem (hwf _ (hG _)) (h0 _ (hG _)) (hp ▸ hwalk)
      have heq := hinc _ (hG _) _ hmem₁ _ hmem₂ hle
      have := (hshort (m + k + 1)).2 _ hwalk' heq
      simp only [List.length_map, List.length_range] at this
      omega
  have hsub : (⋃ G ∈ 𝒢, G.states) ⊆ (reached step s₀) '' T := by
    classical
    intro s hs
    simp only [Set.mem_iUnion] at hs
    obtain ⟨G, hG, hsG⟩ := hs
    obtain ⟨ρ, hρ⟩ := hreach G hG s hsG
    obtain ⟨w, hw, hr⟩ := exists_word_of_path (hacts G hG) (hdet G hG) hρ
    have hex : ∃ n, ∃ w : List A, w.length = n ∧ Walk step G s₀ w ∧ reached step s₀ w = s :=
      ⟨_, w, rfl, hw, hr⟩
    obtain ⟨w₀, hlen, hw₀, hr₀⟩ := Nat.find_spec hex
    refine ⟨w₀, ⟨G, hG, hw₀, fun w' hw' heq => ?_⟩, hr₀⟩
    rw [hlen]
    exact Nat.find_min' hex ⟨w', rfl, hw', heq.trans hr₀⟩
  exact (hTfin.image _).subset hsub

/-- Under the hypotheses of `finite_states_of_incomparable`, the class of graphs is finite. -/
theorem finite_of_incomparable [Finite ι] (𝒢 : Set (ProdGraph ι))
    (hwf : ∀ G ∈ 𝒢, G.WellFormed) (h0 : ∀ G ∈ 𝒢, s₀ ∈ G.states)
    (hreach : ∀ G ∈ 𝒢, ∀ s ∈ G.states, ∃ p, G.IsPath s₀ p s)
    (hinc : ∀ G ∈ 𝒢, ∀ s ∈ G.states, ∀ s' ∈ G.states, s ≤ s' → s = s')
    (hacts : ∀ G ∈ 𝒢, ∀ t ∈ G.trans, t.2.1 ∈ A)
    (hdet : ∀ G ∈ 𝒢, ∀ t ∈ G.trans, t.2.2 = step t.1 t.2.1) : 𝒢.Finite := by
  have hU := finite_states_of_incomparable 𝒢 hwf h0 hreach hinc hacts hdet
  have hfin : ((Set.powerset (⋃ G ∈ 𝒢, G.states)) ×ˢ
      (Set.powerset ((⋃ G ∈ 𝒢, G.states) ×ˢ ((A : Set (ι → ℤ)) ×ˢ (⋃ G ∈ 𝒢, G.states))))).Finite :=
    hU.powerset.prod (hU.prod (A.finite_toSet.prod hU)).powerset
  refine (hfin.image fun p => (⟨p.1, p.2⟩ : ProdGraph ι)).subset fun G hG => ?_
  refine ⟨(G.states, G.trans), ⟨?_, ?_⟩, rfl⟩
  · intro s hs
    simp only [Set.mem_iUnion]
    exact ⟨G, hG, hs⟩
  · intro t ht
    exact ⟨Set.mem_iUnion₂.2 ⟨G, hG, (hwf G hG t ht).1⟩, hacts G hG t ht,
      Set.mem_iUnion₂.2 ⟨G, hG, (hwf G hG t ht).2⟩⟩

end Finite

end ProdGraph

end Cslib
