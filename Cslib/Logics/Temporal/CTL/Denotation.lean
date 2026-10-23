/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Logics.Temporal.CTL.Semantics

/-! # Denotational semantics of CTL

The set of states satisfying a CTL formula, by fixpoints: `E[φ U ψ]` is the least fixpoint of
`X ↦ ⟦ψ⟧ ∪ (⟦φ⟧ ∩ EX X)` and `EG φ` is the greatest fixpoint of `X ↦ ⟦φ⟧ ∩ (EX X ∪ deadlocks)`.
This agrees with the path semantics (`mem_denote_iff`), and is the basis of the labelling
algorithm for finite models.

## Main definitions

- `denote`: the set of states satisfying a formula.

## Main statements

- `mem_denote_iff`: a state is in the denotation of a formula iff it satisfies it.
-/

@[expose] public section

namespace Cslib.Logic.CTL

open scoped InferenceSystem Formula Cslib.Logic

variable {State : Type*} {Atom : Type*}

/-- The states with a successor in `S`. -/
def Model.pre (m : Model State Atom) (S : Set State) : Set State :=
  {s | ∃ t, m.tr s t ∧ t ∈ S}

theorem Model.pre_mono (m : Model State Atom) : Monotone m.pre :=
  fun _ _ h _ ⟨t, htr, ht⟩ => ⟨t, htr, h ht⟩

/-- The operator whose least fixpoint is `E[A U B]`. -/
def euOp (m : Model State Atom) (A B : Set State) : Set State →o Set State where
  toFun X := B ∪ (A ∩ m.pre X)
  monotone' _ _ h := Set.union_subset_union_right _ (Set.inter_subset_inter_right _ (m.pre_mono h))

/-- The operator whose greatest fixpoint is `EG A`: stay in `A`, and continue or stop at a
deadlock. -/
def egOp (m : Model State Atom) (A : Set State) : Set State →o Set State where
  toFun X := A ∩ (m.pre X ∪ {s | m.Dead s})
  monotone' _ _ h := Set.inter_subset_inter_right _ (Set.union_subset_union_left _ (m.pre_mono h))

/-- The set of states satisfying a formula, by fixpoints. -/
noncomputable def denote (m : Model State Atom) : Formula Atom → Set State
  | .atom p => {s | m.v s p}
  | .false => ∅
  | .not φ => (denote m φ)ᶜ
  | .or φ ψ => denote m φ ∪ denote m ψ
  | .ex φ => m.pre (denote m φ)
  | .eu φ ψ => OrderHom.lfp (euOp m (denote m φ) (denote m ψ))
  | .eg φ => OrderHom.gfp (egOp m (denote m φ))

section Fixpoints

variable {m : Model State Atom}

/-- The least fixpoint of `euOp` is the set of states with a maximal path through `A`-states to a
`B`-state. -/
theorem lfp_euOp_eq (A B : Set State) :
    OrderHom.lfp (euOp m A B) =
      {s | ∃ f, m.IsPath f ∧ f 0 = s ∧ ∃ n, f n ∈ B ∧ ∀ k < n, f k ∈ A} := by
  apply le_antisymm
  · refine OrderHom.lfp_le _ ?_
    rintro s (hB | ⟨hA, t, htr, f, hf, h0, n, hn, hk⟩)
    · obtain ⟨f, hf, h0⟩ := m.exists_path s
      exact ⟨f, hf, h0, 0, by rw [h0]; exact hB, by simp⟩
    · refine ⟨fun k => Nat.casesOn k s f, hf.cons (h0 ▸ htr), rfl, n + 1, hn, fun k hk' => ?_⟩
      cases k with
      | zero => exact hA
      | succ j => exact hk j (by omega)
  · rintro s ⟨f, hf, h0, n, hn, hk⟩
    induction n generalizing f s with
    | zero =>
      subst h0
      have : f 0 ∈ euOp m A B (OrderHom.lfp (euOp m A B)) := Or.inl hn
      rwa [OrderHom.map_lfp] at this
    | succ n ih =>
      subst h0
      rcases hf 0 with htr | ⟨hd, h1⟩
      · have h1 : f 1 ∈ OrderHom.lfp (euOp m A B) :=
          ih (f := fun k => f (k + 1)) (s := f 1) hf.tail rfl hn
            (fun k _ => hk (k + 1) (by omega))
        have : f 0 ∈ euOp m A B (OrderHom.lfp (euOp m A B)) :=
          Or.inr ⟨hk 0 (by omega), f 1, htr, h1⟩
        rwa [OrderHom.map_lfp] at this
      · have := hf.eq_of_dead hd (n + 1)
        have hB : f 0 ∈ B := this ▸ hn
        have : f 0 ∈ euOp m A B (OrderHom.lfp (euOp m A B)) := Or.inl hB
        rwa [OrderHom.map_lfp] at this

/-- The greatest fixpoint of `egOp` is the set of states with a maximal path through `A`-states. -/
theorem gfp_egOp_eq (A : Set State) :
    OrderHom.gfp (egOp m A) = {s | ∃ f, m.IsPath f ∧ f 0 = s ∧ ∀ n, f n ∈ A} := by
  classical
  apply le_antisymm
  · intro s hs
    have hG : OrderHom.gfp (egOp m A) = egOp m A (OrderHom.gfp (egOp m A)) :=
      (OrderHom.map_gfp _).symm
    set G := OrderHom.gfp (egOp m A) with hGdef
    have hmem : ∀ x ∈ G, x ∈ A ∧ ((∃ t, m.tr x t ∧ t ∈ G) ∨ m.Dead x) := fun x hx => by
      rw [hG] at hx
      exact hx
    let g : State → State := fun x => if h : ∃ t, m.tr x t ∧ t ∈ G then h.choose else x
    have hg : ∀ x ∈ G, g x ∈ G := fun x hx => by
      by_cases h : ∃ t, m.tr x t ∧ t ∈ G
      · have : g x = h.choose := by simp [g, h]
        rw [this]
        exact h.choose_spec.2
      · have : g x = x := by simp [g, h]
        rw [this]
        exact hx
    have hgn : ∀ n, g^[n] s ∈ G := fun n => by
      induction n with
      | zero => exact hs
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hg _ ih
    refine ⟨fun n => g^[n] s, fun n => ?_, rfl, fun n => (hmem _ (hgn n)).1⟩
    change m.tr (g^[n] s) (g^[n + 1] s) ∨ (m.Dead (g^[n] s) ∧ g^[n + 1] s = g^[n] s)
    rw [Function.iterate_succ_apply']
    by_cases h : ∃ t, m.tr (g^[n] s) t ∧ t ∈ G
    · left
      have : g (g^[n] s) = h.choose := by simp [g, h]
      rw [this]
      exact h.choose_spec.1
    · right
      refine ⟨?_, by simp [g, h]⟩
      rcases (hmem _ (hgn n)).2 with h' | h'
      · exact absurd h' h
      · exact h'
  · refine OrderHom.le_gfp _ ?_
    rintro s ⟨f, hf, h0, hall⟩
    refine ⟨h0 ▸ hall 0, ?_⟩
    rcases hf 0 with htr | ⟨hd, _⟩
    · exact Or.inl ⟨f 1, h0 ▸ htr, fun k => f (k + 1), hf.tail, rfl, fun n => hall (n + 1)⟩
    · exact Or.inr (h0 ▸ hd)

end Fixpoints

/-- **The fixpoint semantics agrees with the path semantics.** -/
theorem mem_denote_iff (m : Model State Atom) (φ : Formula Atom) (s : State) :
    s ∈ denote m φ ↔ ⇓CTL[m,s ⊨ φ] := by
  induction φ generalizing s with
  | atom p => rfl
  | false => simp [denote, Formula.false_def]
  | not φ ih => simp [denote, Formula.not_def, ih]
  | or φ ψ ihφ ihψ => simp [denote, Formula.or_def, ihφ, ihψ]
  | ex φ ih => simp [denote, Model.pre, ih]
  | eu φ ψ ihφ ihψ =>
    have hA : denote m φ = {s | ⇓CTL[m,s ⊨ φ]} := Set.ext ihφ
    have hB : denote m ψ = {s | ⇓CTL[m,s ⊨ ψ]} := Set.ext ihψ
    rw [denote, lfp_euOp_eq, Satisfies.eu_iff]
    simp [hA, hB]
  | eg φ ih =>
    have hA : denote m φ = {s | ⇓CTL[m,s ⊨ φ]} := Set.ext ih
    rw [denote, gfp_egOp_eq, Satisfies.eg_iff]
    simp [hA]

end Cslib.Logic.CTL
