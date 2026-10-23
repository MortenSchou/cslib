/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Logics.Temporal.CTL.Basic
public import Cslib.Foundations.Logic.InferenceSystem
public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Logics.Modal.Unimodal.Basic
public import Mathlib.Order.FixedPoints
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Data.Set.Basic

/-! # Semantics of CTL

A model is a model of basic modal logic (`Modal.Model` for the signature with one unary modality,
`PFunctor.y`): a transition relation together with a valuation of the atoms. The relation need
not be total: paths are *maximal*, so a path is either infinite or ends in a deadlock, a state
without successors. This is the natural reading for Petri nets, whose markings may deadlock. We
represent a maximal path as an infinite sequence that stutters forever at its deadlock.

The satisfaction relation is defined by the usual clauses over paths. We also give the denotational
semantics by fixpoints: `E[φ U ψ]` is the least fixpoint of `X ↦ ⟦ψ⟧ ∪ (⟦φ⟧ ∩ EX X)` and `EG φ`
is the greatest fixpoint of `X ↦ ⟦φ⟧ ∩ (EX X ∪ deadlocks)`, and prove that the two agree. The
fixpoint form is the basis of model checking algorithms.

## Main definitions

- `Model`: a transition relation with a valuation.
- `Model.IsPath`: maximal paths, as infinite sequences stuttering at deadlocks.
- `Satisfies`: the satisfaction relation, written `⇓CTL[m,s ⊨ φ]`.
- `denote`: the set of states satisfying a formula, by fixpoints.

## Main statements

- `mem_denote_iff`: the fixpoint semantics agrees with the path semantics.

## References

* [E. M. Clarke, E. A. Emerson, A. P. Sistla, *Automatic verification of finite-state concurrent
  systems using temporal logic specifications*][Clarke1986]
-/

@[expose] public section

namespace Cslib.Logic.CTL

universe u v

/-- A model is a model of basic modal logic: a transition relation and a valuation of atoms. -/
abbrev Model (State : Type u) (Atom : Type v) := Modal.Model State PFunctor.y.{0, 0} Atom

variable {State : Type*} {Atom : Type*}

/-- The transition relation of a model. -/
abbrev Model.tr (m : Model State Atom) : State → State → Prop := m.rel

/-- A model from a transition relation and a valuation of atoms. -/
def Model.ofRel (tr : State → State → Prop) (v : State → Atom → Prop) : Model State Atom :=
  ⟨Frame.ofRelation tr, v⟩

@[simp] theorem Model.tr_ofRel (tr : State → State → Prop) (v : State → Atom → Prop) :
    (Model.ofRel tr v).tr = tr := rfl

@[simp] theorem Model.v_ofRel (tr : State → State → Prop) (v : State → Atom → Prop) :
    (Model.ofRel tr v).v = v := rfl

/-- An `LTS` is read as a frame by forgetting the labels: the relation is the existence of a
transition. With this coercion, `⟨lts, v⟩` is the model of the LTS `lts` with the valuation `v`. -/
scoped instance {Label : Type*} : CoeOut (LTS State Label) (Frame State PFunctor.y.{0, 0}) :=
  ⟨fun lts => Frame.ofRelation lts.UnlabelledTr⟩

/-- A state without successors is a deadlock. -/
def Model.Dead (m : Model State Atom) (s : State) : Prop := ∀ t, ¬ m.tr s t

/-- A maximal path, as an infinite sequence of states. Each step is a transition, or the sequence
stutters at a deadlock. -/
def Model.IsPath (m : Model State Atom) (f : ℕ → State) : Prop :=
  ∀ n, m.tr (f n) (f (n + 1)) ∨ (m.Dead (f n) ∧ f (n + 1) = f n)

/-- Satisfaction relation. `Satisfies m s φ` means that, in the model `m`, the state `s` satisfies
the formula `φ`. -/
def Satisfies (m : Model State Atom) (s : State) : Formula Atom → Prop
  | .atom p => m.v s p
  | .false => False
  | .not φ => ¬ Satisfies m s φ
  | .or φ ψ => Satisfies m s φ ∨ Satisfies m s ψ
  | .ex φ => ∃ t, m.tr s t ∧ Satisfies m t φ
  | .eu φ ψ => ∃ f, m.IsPath f ∧ f 0 = s ∧ ∃ n, Satisfies m (f n) ψ ∧ ∀ k < n, Satisfies m (f k) φ
  | .eg φ => ∃ f, m.IsPath f ∧ f 0 = s ∧ ∀ n, Satisfies m (f n) φ

/-- Judgement, representing the conclusions one reaches in CTL. -/
structure Judgement (State : Type u) (Atom : Type v) where
  /-- Constructs a judgement. -/
  mk ::
  /-- Model. -/
  m : Model State Atom
  /-- The state satisfying the formula `φ`. -/
  s : State
  /-- The formula satisfied by the state `s`. -/
  φ : Formula Atom

@[inherit_doc] scoped notation "CTL[" m "," s " ⊨ " φ "]" => Judgement.mk m s φ

/-- Satisfaction for judgements. This just refers to the unbundled `Satisfies`. -/
def Satisfies.Bundled (j : Judgement State Atom) : Prop := Satisfies j.m j.s j.φ

instance : HasInferenceSystem (Judgement State Atom) := ⟨Satisfies.Bundled⟩

open scoped InferenceSystem Formula Cslib.Logic

theorem derivation_def {m : Model State Atom} {s : State} {φ : Formula Atom} :
    Satisfies m s φ = ⇓CTL[m,s ⊨ φ] := rfl

section Paths

variable {m : Model State Atom}

/-- Every state starts a maximal path. -/
theorem Model.exists_path (m : Model State Atom) (s : State) :
    ∃ f, m.IsPath f ∧ f 0 = s := by
  classical
  let g : State → State := fun x => if h : ∃ t, m.tr x t then h.choose else x
  refine ⟨fun n => g^[n] s, fun n => ?_, rfl⟩
  change m.tr (g^[n] s) (g^[n + 1] s) ∨ (m.Dead (g^[n] s) ∧ g^[n + 1] s = g^[n] s)
  rw [Function.iterate_succ_apply']
  by_cases h : ∃ t, m.tr (g^[n] s) t
  · left
    have : g (g^[n] s) = h.choose := by simp [g, h]
    rw [this]
    exact h.choose_spec
  · right
    refine ⟨fun t ht => h ⟨t, ht⟩, ?_⟩
    simp [g, h]

/-- The tail of a maximal path is a maximal path. -/
theorem Model.IsPath.tail {f : ℕ → State} (h : m.IsPath f) : m.IsPath fun n => f (n + 1) :=
  fun n => h (n + 1)

/-- Prepending a transition to a maximal path. -/
theorem Model.IsPath.cons {s : State} {f : ℕ → State} (h : m.IsPath f) (hs : m.tr s (f 0)) :
    m.IsPath fun n => Nat.casesOn n s f := by
  intro n
  cases n with
  | zero => exact Or.inl hs
  | succ k => exact h k

/-- A maximal path from a deadlock stays there. -/
theorem Model.IsPath.eq_of_dead {f : ℕ → State} (h : m.IsPath f) (hd : m.Dead (f 0)) (n : ℕ) :
    f n = f 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases h n with h1 | ⟨_, h2⟩
    · exact absurd h1 (by rw [ih]; exact hd _)
    · rw [h2, ih]

end Paths

section Characterisations

variable {m : Model State Atom} {s : State} {φ ψ : Formula Atom}

@[simp] theorem Satisfies.atom_iff {p : Atom} : ⇓CTL[m,s ⊨ .atom p] ↔ m.v s p := Iff.rfl

@[simp] theorem Satisfies.false_iff : ⇓CTL[m,s ⊨ ⊥] ↔ False := Iff.rfl

@[simp] theorem Satisfies.not_iff : ⇓CTL[m,s ⊨ ¬φ] ↔ ¬ ⇓CTL[m,s ⊨ φ] := Iff.rfl

@[simp] theorem Satisfies.or_iff : ⇓CTL[m,s ⊨ φ ∨ ψ] ↔ ⇓CTL[m,s ⊨ φ] ∨ ⇓CTL[m,s ⊨ ψ] := Iff.rfl

@[simp] theorem Satisfies.true_iff : ⇓CTL[m,s ⊨ ⊤] := by
  change ¬ False
  exact not_false

@[simp] theorem Satisfies.and_iff : ⇓CTL[m,s ⊨ φ ∧ ψ] ↔ ⇓CTL[m,s ⊨ φ] ∧ ⇓CTL[m,s ⊨ ψ] := by
  change ¬(¬ ⇓CTL[m,s ⊨ φ] ∨ ¬ ⇓CTL[m,s ⊨ ψ]) ↔ _
  tauto

@[simp] theorem Satisfies.imp_iff : ⇓CTL[m,s ⊨ φ → ψ] ↔ (⇓CTL[m,s ⊨ φ] → ⇓CTL[m,s ⊨ ψ]) := by
  change (¬ ⇓CTL[m,s ⊨ φ] ∨ ⇓CTL[m,s ⊨ ψ]) ↔ _
  tauto

@[simp] theorem Satisfies.ex_iff : ⇓CTL[m,s ⊨ EX φ] ↔ ∃ t, m.tr s t ∧ ⇓CTL[m,t ⊨ φ] := Iff.rfl

theorem Satisfies.eu_iff : ⇓CTL[m,s ⊨ E[φ U ψ]] ↔
    ∃ f, m.IsPath f ∧ f 0 = s ∧ ∃ n, ⇓CTL[m,f n ⊨ ψ] ∧ ∀ k < n, ⇓CTL[m,f k ⊨ φ] := Iff.rfl

theorem Satisfies.eg_iff : ⇓CTL[m,s ⊨ EG φ] ↔
    ∃ f, m.IsPath f ∧ f 0 = s ∧ ∀ n, ⇓CTL[m,f n ⊨ φ] := Iff.rfl

theorem Satisfies.ax_iff : ⇓CTL[m,s ⊨ AX φ] ↔ ∀ t, m.tr s t → ⇓CTL[m,t ⊨ φ] := by
  change ¬(∃ t, m.tr s t ∧ ¬ ⇓CTL[m,t ⊨ φ]) ↔ _
  push Not
  rfl

/-- `deadlock` characterises the states without successors. -/
theorem Satisfies.deadlock_iff : ⇓CTL[m,s ⊨ Formula.deadlock] ↔ m.Dead s := by
  change ¬(∃ t, m.tr s t ∧ ⇓CTL[m,t ⊨ ⊤]) ↔ _
  simp [Model.Dead]

theorem Satisfies.ef_iff : ⇓CTL[m,s ⊨ EF φ] ↔
    ∃ f, m.IsPath f ∧ f 0 = s ∧ ∃ n, ⇓CTL[m,f n ⊨ φ] := by
  rw [Formula.ef, Satisfies.eu_iff]
  simp only [Satisfies.true_iff, implies_true, and_true]

theorem Satisfies.af_iff : ⇓CTL[m,s ⊨ AF φ] ↔
    ∀ f, m.IsPath f → f 0 = s → ∃ n, ⇓CTL[m,f n ⊨ φ] := by
  change ¬ ⇓CTL[m,s ⊨ EG ¬φ] ↔ _
  rw [Satisfies.eg_iff]
  simp only [Satisfies.not_iff, not_exists, not_and, not_forall, not_not]

theorem Satisfies.ag_iff : ⇓CTL[m,s ⊨ AG φ] ↔
    ∀ f, m.IsPath f → f 0 = s → ∀ n, ⇓CTL[m,f n ⊨ φ] := by
  change ¬ ⇓CTL[m,s ⊨ EF ¬φ] ↔ _
  rw [Satisfies.ef_iff]
  simp only [Satisfies.not_iff, not_exists, not_and, not_not]

end Characterisations

end Cslib.Logic.CTL
