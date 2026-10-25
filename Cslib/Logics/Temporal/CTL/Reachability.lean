/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Logics.Temporal.CTL.Semantics
public import Cslib.Foundations.Semantics.LTS.Relation
public import Mathlib.Logic.Relation

/-! # Reachability in CTL

`EF` and `AG` are reachability properties: `EF φ` holds at a state if some reachable state
satisfies `φ`, and `AG φ` if all reachable states do. Reachability is the reflexive transitive
closure of the transition relation.
-/

@[expose] public section

namespace Cslib.Logic.CTL

open scoped InferenceSystem Formula Cslib.Logic

variable {State : Type*} {Atom : Type*} {m : Model State Atom}

/-- Along a maximal path, later states are reachable from the first. -/
theorem Model.IsPath.reachable {f : ℕ → State} (h : m.IsPath f) (n : ℕ) :
    Relation.ReflTransGen m.tr (f 0) (f n) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    rcases h n with htr | ⟨_, heq⟩
    · exact ih.tail htr
    · rw [heq]; exact ih

/-- A reachable state lies on a maximal path from the start. -/
theorem Model.exists_path_through {s t : State} (h : Relation.ReflTransGen m.tr s t) :
    ∃ f, m.IsPath f ∧ f 0 = s ∧ ∃ n, f n = t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    obtain ⟨f, hf, h0⟩ := m.exists_path t
    exact ⟨f, hf, h0, 0, h0⟩
  | @head a b hab _ ih =>
    obtain ⟨f, hf, h0, n, hn⟩ := ih
    exact ⟨fun k => Nat.casesOn k a f, hf.cons (h0 ▸ hab), rfl, n + 1, hn⟩

/-- `EF φ` holds at the states from which a state satisfying `φ` is reachable. -/
theorem Satisfies.ef_iff_reachable {s : State} {φ : Formula Atom} :
    ⇓CTL[m,s ⊨ EF φ] ↔ ∃ t, Relation.ReflTransGen m.tr s t ∧ ⇓CTL[m,t ⊨ φ] := by
  rw [Satisfies.ef_iff]
  constructor
  · rintro ⟨f, hf, h0, n, hn⟩
    exact ⟨f n, h0 ▸ hf.reachable n, hn⟩
  · rintro ⟨t, hst, ht⟩
    obtain ⟨f, hf, h0, n, hn⟩ := Model.exists_path_through hst
    exact ⟨f, hf, h0, n, hn ▸ ht⟩

/-- `AG φ` holds at the states all of whose reachable states satisfy `φ`. -/
theorem Satisfies.ag_iff_reachable {s : State} {φ : Formula Atom} :
    ⇓CTL[m,s ⊨ AG φ] ↔ ∀ t, Relation.ReflTransGen m.tr s t → ⇓CTL[m,t ⊨ φ] := by
  rw [Satisfies.ag_iff]
  constructor
  · intro h t hst
    obtain ⟨f, hf, h0, n, hn⟩ := Model.exists_path_through hst
    exact hn ▸ h f hf h0 n
  · intro h f hf h0 n
    exact h _ (h0 ▸ hf.reachable n)

section LTS

variable {Label : Type*} {lts : LTS State Label} {v : State → Atom → Prop}

/-- In the model of an `LTS`, `EF φ` holds at the states that can reach a state satisfying `φ`. -/
theorem Satisfies.ef_ofLTS_iff {s : State} {φ : Formula Atom} :
    ⇓CTL[⟨lts, v⟩,s ⊨ EF φ] ↔
      ∃ t, lts.CanReach s t ∧ ⇓CTL[⟨lts, v⟩,t ⊨ φ] := by
  simp only [Satisfies.ef_iff_reachable, ← LTS.reflTransGen_unlabelledTr_iff]
  rfl

/-- In the model of an `LTS`, `AG φ` holds at the states all of whose reachable states satisfy
`φ`. -/
theorem Satisfies.ag_ofLTS_iff {s : State} {φ : Formula Atom} :
    ⇓CTL[⟨lts, v⟩,s ⊨ AG φ] ↔
      ∀ t, lts.CanReach s t → ⇓CTL[⟨lts, v⟩,t ⊨ φ] := by
  simp only [Satisfies.ag_iff_reachable, ← LTS.reflTransGen_unlabelledTr_iff]
  rfl

/-- In the model of an `LTS`, the deadlocks are the terminal states. -/
theorem Satisfies.deadlock_ofLTS_iff {s : State} :
    ⇓CTL[⟨lts, v⟩,s ⊨ Formula.deadlock] ↔ lts.IsTerminal s := by
  rw [Satisfies.deadlock_iff]
  simp only [Model.Dead, LTS.IsTerminal]
  exact ⟨fun h μ s' htr => h s' ⟨μ, htr⟩, fun h s' ⟨μ, htr⟩ => h μ s' htr⟩

end LTS

end Cslib.Logic.CTL
