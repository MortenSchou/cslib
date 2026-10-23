/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Logic.Relation

/-! # Commuting labels and Mazurkiewicz equivalence

Given a relation `I` on the labels of an LTS, thought of as an independence relation, two label
sequences are related by `SwapStep` if they differ by swapping one adjacent pair of related labels.
Its equivalence closure `TraceEquiv` is the Mazurkiewicz equivalence. If the LTS can commute any
two adjacent steps with related labels, then equivalent sequences are executable from the same
states and lead to the same states.

## Main definitions

- `LTS.CommutesWith`: every pair of adjacent steps with `I`-related labels can be swapped.
- `LTS.SwapStep`: two label sequences differ by swapping one adjacent `I`-related pair.
- `LTS.TraceEquiv`: the Mazurkiewicz equivalence, the equivalence closure of `SwapStep`.

## Main statements

- `LTS.TraceEquiv.mTr_iff`: equivalent sequences are executable from the same states and lead to
  the same states.

## References

* [A. Mazurkiewicz, *Trace theory*][Mazurkiewicz1987]
-/

@[expose] public section

namespace Cslib.LTS

universe u v

variable {State : Type u} {Label : Type v}

/-- The independence relation `I` is commuted by `lts`: two adjacent steps with `I`-related labels
`μ ν` can be replaced by steps with the labels `ν μ`, between the same two states. -/
def CommutesWith (lts : LTS State Label) (I : Label → Label → Prop) : Prop :=
  ∀ s s₁ s₂ μ ν, I μ ν → lts.Tr s μ s₁ → lts.Tr s₁ ν s₂ → ∃ s₁', lts.Tr s ν s₁' ∧ lts.Tr s₁' μ s₂

/-- Two label sequences differ by one swap of adjacent `I`-related labels. -/
inductive SwapStep (I : Label → Label → Prop) : List Label → List Label → Prop
  /-- Swap the related labels `μ` and `ν` between the prefix `σ` and the suffix `τ`. -/
  | swap (σ τ : List Label) {μ ν : Label} (h : I μ ν) :
    SwapStep I (σ ++ μ :: ν :: τ) (σ ++ ν :: μ :: τ)

/-- Mazurkiewicz equivalence: label sequences related by swapping adjacent `I`-related labels. -/
def TraceEquiv (I : Label → Label → Prop) : List Label → List Label → Prop :=
  Relation.EqvGen (SwapStep I)

variable {lts : LTS State Label} {I : Label → Label → Prop}

/-- A swap step stays a swap step after adding a common first label. -/
theorem SwapStep.cons (x : Label) {σ τ : List Label} (h : SwapStep I σ τ) :
    SwapStep I (x :: σ) (x :: τ) := by
  obtain ⟨σ, τ, h⟩ := h
  exact SwapStep.swap (x :: σ) τ h

/-- Equivalent sequences stay equivalent after adding a common first label. -/
theorem TraceEquiv.cons (x : Label) {σ τ : List Label} (h : TraceEquiv I σ τ) :
    TraceEquiv I (x :: σ) (x :: τ) :=
  Relation.EqvGen.rec (fun _ _ h => .rel _ _ (SwapStep.cons x h)) (fun _ => .refl _)
    (fun _ _ _ ih => .symm _ _ ih) (fun _ _ _ _ _ ih₁ ih₂ => .trans _ _ _ ih₁ ih₂) h

/-- A label that is related to every label of `σ` can be moved from behind `σ` to the front. -/
theorem TraceEquiv.move_left (a : Label) (σ ρ : List Label) (h : ∀ u ∈ σ, I a u) :
    TraceEquiv I (σ ++ a :: ρ) (a :: (σ ++ ρ)) := by
  induction σ with
  | nil => exact .refl _
  | cons u σ ih =>
    have h1 := TraceEquiv.cons u (ih fun v hv => h v (List.mem_cons_of_mem _ hv))
    have h2 : TraceEquiv I (u :: a :: (σ ++ ρ)) (a :: u :: (σ ++ ρ)) :=
      .symm _ _ (.rel _ _ (SwapStep.swap [] (σ ++ ρ) (h u (List.mem_cons_self ..))))
    exact .trans _ _ _ h1 h2

/-- Adjacent related labels of an execution can be swapped. -/
theorem MTr.swap (hc : lts.CommutesWith I) {s s' : State} {μ ν : Label} {μs : List Label}
    (hI : I μ ν) (h : lts.MTr s (μ :: ν :: μs) s') : lts.MTr s (ν :: μ :: μs) s' := by
  obtain ⟨s₁, h₁, h⟩ := MTr.cons_iff.1 h
  obtain ⟨s₂, h₂, h⟩ := MTr.cons_iff.1 h
  obtain ⟨s₁', h₃, h₄⟩ := hc _ _ _ _ _ hI h₁ h₂
  exact .stepL h₃ (.stepL h₄ h)

/-- Sequences that differ by one swap are executable from the same states and lead to the same
states, if `lts` commutes the symmetric relation `I`. -/
theorem SwapStep.mTr_iff (hc : lts.CommutesWith I) (hs : ∀ {μ ν}, I μ ν → I ν μ)
    {σ τ : List Label} (h : SwapStep I σ τ) {s s' : State} : lts.MTr s σ s' ↔ lts.MTr s τ s' := by
  obtain ⟨σ, τ, hI⟩ := h
  simp only [MTr.append_iff]
  exact exists_congr fun _ => and_congr_right fun _ =>
    ⟨MTr.swap hc hI, MTr.swap hc (hs hI)⟩

/-- Equivalent sequences are executable from the same states and lead to the same states, if `lts`
commutes the symmetric relation `I`. -/
theorem TraceEquiv.mTr_iff (hc : lts.CommutesWith I) (hs : ∀ {μ ν}, I μ ν → I ν μ)
    {σ τ : List Label} (h : TraceEquiv I σ τ) {s s' : State} : lts.MTr s σ s' ↔ lts.MTr s τ s' :=
  Relation.EqvGen.rec (fun _ _ h => h.mTr_iff hc hs) (fun _ => Iff.rfl) (fun _ _ _ ih => ih.symm)
    (fun _ _ _ _ _ ih₁ ih₂ => ih₁.trans ih₂) h

/-- Equivalent sequences are simultaneously executable. -/
theorem TraceEquiv.exists_mTr_iff (hc : lts.CommutesWith I) (hs : ∀ {μ ν}, I μ ν → I ν μ)
    {σ τ : List Label} (h : TraceEquiv I σ τ) {s : State} :
    (∃ s', lts.MTr s σ s') ↔ ∃ s', lts.MTr s τ s' :=
  exists_congr fun _ => h.mTr_iff hc hs

end Cslib.LTS
