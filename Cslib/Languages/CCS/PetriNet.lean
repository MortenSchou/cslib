/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Labelled
public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Semantics.LTS.TraceEq
public import Cslib.Languages.CCS.Semantics
public import Mathlib.Tactic.Abel

/-! # CCS as a Petri net

A CCS process is a tree of parallel compositions whose leaves are the sequential components. The
marking of the net `CCS.net` holds one token per leaf. A step of a single component (including its
spawning of new parallel components) is a transition that consumes the component's token and
produces the leaves of its continuation. A communication consumes the tokens of two components and
produces the leaves of their continuations. Everything below the leaves, such as prefixing, choice,
restriction and constants, is handled by the CCS transition relation itself.

The net is infinite in general: its places are all processes. What the translation shows is that
the *interleaving semantics of CCS is the marking graph of a Petri net*, in which concurrency is
visible as independent transitions on disjoint tokens.

## Main definitions

- `CCS.leaves`: the sequential components of a process, as a multiset. This is the marking of
  the process in `CCS.net`.
- `CCS.net`: the Petri net of a CCS system, with `CCS.NetTransition` as transitions.
- `CCS.netLts`: the marking graph of `CCS.net`, labelled by actions.

## Main statements

- `CCS.bisimilar_leaves`: a process is bisimilar to its marking `leaves p` in the labelled
  marking graph of `CCS.net`.
- `CCS.traces_leaves`: a process and its marking have the same traces.

## References

* [R. Milner, *A Calculus of Communicating Systems*][Milner80]
-/

@[expose] public section

namespace Cslib.CCS

universe u v

open Process PetriNet
open scoped LTS

variable {Name : Type u} {Constant : Type v}
  {defs : Constant → Option (Process Name Constant)}

/-- The sequential components of a process: the leaves of its tree of parallel compositions.
As a marking of `CCS.net`, it holds one token on each sequential component. -/
def leaves : Process Name Constant → Multiset (Process Name Constant)
  | .nil => {.nil}
  | .pre μ p => {.pre μ p}
  | .par p q => leaves p + leaves q
  | .choice p q => {.choice p q}
  | .res a p => {.res a p}
  | .const c => {.const c}

@[simp] theorem leaves_par (p q : Process Name Constant) :
    leaves (par p q) = leaves p + leaves q := rfl

theorem leaves_of_not_par {r : Process Name Constant} (h : ∀ p q, r ≠ par p q) :
    leaves r = {r} := by
  cases r <;> simp_all [leaves]

set_option genSizeOfSpec false in
/-- The transitions of the Petri net of a CCS system: a step of one component, or a communication
between two components. -/
inductive NetTransition (defs : Constant → Option (Process Name Constant)) :
    Type (max u v) where
  /-- A single component `s` performs `μ` and continues as `s'`. -/
  | act (s : Process Name Constant) (μ : Act Name) (s' : Process Name Constant)
      (h : (lts (defs := defs)).Tr s μ s')
  /-- Two components perform complementary actions and continue as `s'` and `t'`. -/
  | comm (s t : Process Name Constant) (μ μ' : Act Name) (s' t' : Process Name Constant)
      (hco : μ.Co μ') (hs : (lts (defs := defs)).Tr s μ s') (ht : (lts (defs := defs)).Tr t μ' t')

/-- The observable label of a transition: the action, or `τ` for a communication. -/
def NetTransition.label : NetTransition defs → Act Name
  | .act _ μ _ _ => μ
  | .comm .. => Act.τ

/-- The Petri net of a CCS system. Its places are processes. -/
def net (defs : Constant → Option (Process Name Constant)) :
    PetriNet (Process Name Constant) (NetTransition defs) where
  pre
    | .act s .. => {s}
    | .comm s t .. => {s} + {t}
  post
    | .act _ _ s' _ => leaves s'
    | .comm _ _ _ _ s' t' .. => leaves s' + leaves t'

section Leaves

/-- A step of a process is either a step of one of its leaves, or a communication between two of
them. -/
theorem leaves_tr (p : Process Name Constant) {μ : Act Name} {p' : Process Name Constant}
    (h : (lts (defs := defs)).Tr p μ p') :
    (∃ s s' R, leaves p = {s} + R ∧ (lts (defs := defs)).Tr s μ s' ∧
      leaves p' = R + leaves s') ∨
    (∃ s t s' t' μ₁ μ₂ R, μ₁.Co μ₂ ∧ μ = Act.τ ∧ leaves p = {s} + {t} + R ∧
      (lts (defs := defs)).Tr s μ₁ s' ∧ (lts (defs := defs)).Tr t μ₂ t' ∧
      leaves p' = R + (leaves s' + leaves t')) := by
  induction p generalizing μ p' with
  | par a b iha ihb =>
    cases h with
    | parL h =>
      rcases iha h with ⟨s, s', R, h1, h2, h3⟩ | ⟨s, t, s', t', μ₁, μ₂, R, h0, h1, h2, h3, h4, h5⟩
      · refine .inl ⟨s, s', R + leaves b, ?_, h2, ?_⟩
        · rw [leaves_par, h1]; abel
        · rw [leaves_par, h3]; abel
      · refine .inr ⟨s, t, s', t', μ₁, μ₂, R + leaves b, h0, h1, ?_, h3, h4, ?_⟩
        · rw [leaves_par, h2]; abel
        · rw [leaves_par, h5]; abel
    | parR h =>
      rcases ihb h with ⟨s, s', R, h1, h2, h3⟩ | ⟨s, t, s', t', μ₁, μ₂, R, h0, h1, h2, h3, h4, h5⟩
      · refine .inl ⟨s, s', leaves a + R, ?_, h2, ?_⟩
        · rw [leaves_par, h1]; abel
        · rw [leaves_par, h3]; abel
      · refine .inr ⟨s, t, s', t', μ₁, μ₂, leaves a + R, h0, h1, ?_, h3, h4, ?_⟩
        · rw [leaves_par, h2]; abel
        · rw [leaves_par, h5]; abel
    | com hco h1 h2 =>
      have hv := Act.co_isVisible hco
      rcases iha h1 with ⟨s, s', R₁, e1, e2, e3⟩ | ⟨_, _, _, _, _, _, _, _, e, -⟩
      · rcases ihb h2 with ⟨t, t', R₂, f1, f2, f3⟩ | ⟨_, _, _, _, _, _, _, _, f, -⟩
        · refine .inr ⟨s, t, s', t', _, _, R₁ + R₂, hco, rfl, ?_, e2, f2, ?_⟩
          · rw [leaves_par, e1, f1]; abel
          · rw [leaves_par, e3, f3]; abel
        · exact absurd f (Act.isVisible_neq_τ hv.2)
      · exact absurd e (Act.isVisible_neq_τ hv.1)
  | _ =>
    refine .inl ⟨_, p', 0, ?_, h, ?_⟩ <;> simp [leaves]

theorem tr_of_leaves_atom {p s s' : Process Name Constant} {R : Multiset (Process Name Constant)}
    {μ : Act Name} (hp : ∀ a b, p ≠ par a b) (hl : leaves p = {s} + R)
    (h : (lts (defs := defs)).Tr s μ s') :
    ∃ p', (lts (defs := defs)).Tr p μ p' ∧ leaves p' = R + leaves s' := by
  rw [leaves_of_not_par hp] at hl
  have hs : s ∈ ({p} : Multiset _) := by rw [hl]; simp
  obtain rfl := Multiset.mem_singleton.1 hs
  have hR : R = 0 := by
    have := congrArg Multiset.card hl
    simpa using this
  subst hR
  exact ⟨s', h, by simp⟩

/-- A step of a leaf is a step of the whole process. -/
theorem tr_of_leaves (p : Process Name Constant) {s s' : Process Name Constant} {R : Multiset _}
    {μ : Act Name} (hl : leaves p = {s} + R) (h : (lts (defs := defs)).Tr s μ s') :
    ∃ p', (lts (defs := defs)).Tr p μ p' ∧ leaves p' = R + leaves s' := by
  induction p generalizing R with
  | par a b iha ihb =>
    have hs : s ∈ leaves a + leaves b := by rw [← leaves_par, hl]; simp
    rcases Multiset.mem_add.1 hs with hs | hs
    · obtain ⟨R₁, hR₁⟩ := Multiset.exists_cons_of_mem hs
      have hR : R = R₁ + leaves b := by
        rw [leaves_par, hR₁, ← Multiset.singleton_add] at hl
        exact (add_left_cancel (by rw [← hl]; abel)).symm
      obtain ⟨a', ha', hl'⟩ := iha (R := R₁) (by rw [hR₁, Multiset.singleton_add])
      exact ⟨par a' b, .parL ha', by rw [leaves_par, hl', hR]; abel⟩
    · obtain ⟨R₁, hR₁⟩ := Multiset.exists_cons_of_mem hs
      have hR : R = leaves a + R₁ := by
        rw [leaves_par, hR₁, ← Multiset.singleton_add] at hl
        exact (add_left_cancel (by rw [← hl]; abel)).symm
      obtain ⟨b', hb', hl'⟩ := ihb (R := R₁) (by rw [hR₁, Multiset.singleton_add])
      exact ⟨par a b', .parR hb', by rw [leaves_par, hl', hR]; abel⟩
  | _ => exact tr_of_leaves_atom (by simp) hl h

/-- Two distinguished elements of a sum of multisets lie in one summand or are split between
them. -/
theorem split_two {α : Type*} {A B R : Multiset α} {s t : α}
    (h : A + B = {s} + {t} + R) :
    (∃ A₁, A = {s} + {t} + A₁ ∧ R = A₁ + B) ∨ (∃ B₁, B = {s} + {t} + B₁ ∧ R = A + B₁) ∨
    (∃ A₁ B₁, A = {s} + A₁ ∧ B = {t} + B₁ ∧ R = A₁ + B₁) ∨
    (∃ A₁ B₁, A = {t} + A₁ ∧ B = {s} + B₁ ∧ R = A₁ + B₁) := by
  have hs : s ∈ A + B := by rw [h]; simp
  rcases Multiset.mem_add.1 hs with hs | hs
  · obtain ⟨A₁, rfl⟩ := Multiset.exists_cons_of_mem hs
    rw [← Multiset.singleton_add] at h
    have h' : A₁ + B = {t} + R := add_left_cancel (a := {s}) (by rw [← add_assoc, h]; abel)
    have ht : t ∈ A₁ + B := by rw [h']; simp
    rcases Multiset.mem_add.1 ht with ht | ht
    · obtain ⟨A₂, rfl⟩ := Multiset.exists_cons_of_mem ht
      rw [← Multiset.singleton_add] at h'
      refine .inl ⟨A₂, by rw [← Multiset.singleton_add, ← Multiset.singleton_add]; abel, ?_⟩
      exact (add_left_cancel (a := {t}) (by rw [← h']; abel)).symm
    · obtain ⟨B₁, rfl⟩ := Multiset.exists_cons_of_mem ht
      rw [← Multiset.singleton_add] at h'
      refine .inr (.inr (.inl ⟨A₁, B₁, by rw [Multiset.singleton_add],
        by rw [Multiset.singleton_add], ?_⟩))
      exact (add_left_cancel (a := {t}) (by rw [← h']; abel)).symm
  · obtain ⟨B₁, rfl⟩ := Multiset.exists_cons_of_mem hs
    rw [← Multiset.singleton_add] at h
    have h' : A + B₁ = {t} + R :=
      add_left_cancel (a := {s}) (by rw [← add_assoc ({s} : Multiset α) {t} R, ← h]; abel)
    have ht : t ∈ A + B₁ := by rw [h']; simp
    rcases Multiset.mem_add.1 ht with ht | ht
    · obtain ⟨A₁, rfl⟩ := Multiset.exists_cons_of_mem ht
      rw [← Multiset.singleton_add] at h'
      refine .inr (.inr (.inr ⟨A₁, B₁, by rw [Multiset.singleton_add],
        by rw [Multiset.singleton_add], ?_⟩))
      exact (add_left_cancel (a := {t}) (by rw [← h']; abel)).symm
    · obtain ⟨B₂, rfl⟩ := Multiset.exists_cons_of_mem ht
      rw [← Multiset.singleton_add] at h'
      refine .inr (.inl ⟨B₂, by rw [← Multiset.singleton_add, ← Multiset.singleton_add]; abel,
        ?_⟩)
      exact (add_left_cancel (a := {t}) (by rw [← h']; abel)).symm

/-- A communication between two leaves is a `τ`-step of the whole process. -/
theorem tr_com_of_leaves (p : Process Name Constant) {s t s' t' : Process Name Constant}
    {R : Multiset (Process Name Constant)} {μ₁ μ₂ : Act Name} (hco : μ₁.Co μ₂)
    (hl : leaves p = {s} + {t} + R) (hs : (lts (defs := defs)).Tr s μ₁ s')
    (ht : (lts (defs := defs)).Tr t μ₂ t') :
    ∃ p', (lts (defs := defs)).Tr p Act.τ p' ∧ leaves p' = R + (leaves s' + leaves t') := by
  induction p generalizing R with
  | par a b iha ihb =>
    rw [leaves_par] at hl
    rcases split_two hl with ⟨A₁, h1, h2⟩ | ⟨B₁, h1, h2⟩ | ⟨A₁, B₁, h1, h2, h3⟩ |
        ⟨A₁, B₁, h1, h2, h3⟩
    · obtain ⟨a', ha', hl'⟩ := iha h1
      exact ⟨par a' b, .parL ha', by rw [leaves_par, hl', h2]; abel⟩
    · obtain ⟨b', hb', hl'⟩ := ihb h1
      exact ⟨par a b', .parR hb', by rw [leaves_par, hl', h2]; abel⟩
    · obtain ⟨a', ha', hl₁⟩ := tr_of_leaves a h1 hs
      obtain ⟨b', hb', hl₂⟩ := tr_of_leaves b h2 ht
      exact ⟨par a' b', .com hco ha' hb', by rw [leaves_par, hl₁, hl₂, h3]; abel⟩
    · obtain ⟨a', ha', hl₁⟩ := tr_of_leaves a h1 ht
      obtain ⟨b', hb', hl₂⟩ := tr_of_leaves b h2 hs
      exact ⟨par a' b', .com hco.symm ha' hb', by rw [leaves_par, hl₁, hl₂, h3]; abel⟩
  | _ =>
    exfalso
    rw [leaves_of_not_par (by simp)] at hl
    have := congrArg Multiset.card hl
    simp at this

end Leaves

section Net

/-- The marking graph of the Petri net of a CCS system, labelled by actions. -/
def netLts (defs : Constant → Option (Process Name Constant)) :
    LTS (Marking (Process Name Constant)) (Act Name) :=
  (net defs).labelledLts NetTransition.label

/-- A process is related to its marking `leaves p`: the relation is a bisimulation. -/
theorem isBisimulation_leaves :
    LTS.IsBisimulation (lts (defs := defs)) (netLts defs) fun p M => M = leaves p := by
  intro p M hM a
  subst hM
  constructor
  · intro p' htr
    rcases leaves_tr p htr with ⟨s, s', R, h1, h2, h3⟩ |
        ⟨s, t, s', t', μ₁, μ₂, R, hco, rfl, h1, h2, h3, h4⟩
    · exact ⟨leaves p', ⟨.act s a s' h2, rfl, R, h1, h3⟩, rfl⟩
    · exact ⟨leaves p', ⟨.comm s t μ₁ μ₂ s' t' hco h2 h3, rfl, R, h1, h4⟩, rfl⟩
  · rintro M' ⟨t, rfl, R, h1, rfl⟩
    cases t with
    | act s μ s' h =>
      obtain ⟨p', hp', hl⟩ := tr_of_leaves p (R := R) h1 h
      exact ⟨p', hp', hl.symm⟩
    | comm s t μ μ' s' t' hco hs ht =>
      obtain ⟨p', hp', hl⟩ := tr_com_of_leaves p (R := R) hco h1 hs ht
      exact ⟨p', hp', hl.symm⟩

/-- A CCS process is bisimilar to its marking `leaves p` in the Petri net of the system. -/
theorem bisimilar_leaves (p : Process Name Constant) :
    p ~[lts (defs := defs), netLts defs] (leaves p) :=
  ⟨_, rfl, isBisimulation_leaves⟩

/-- A CCS process and its marking `leaves p` have the same traces. -/
theorem traces_leaves (p : Process Name Constant) :
    (lts (defs := defs)).traces p = (netLts defs).traces (leaves p) :=
  (bisimilar_leaves p).le_traceEq

end Net

end Cslib.CCS
