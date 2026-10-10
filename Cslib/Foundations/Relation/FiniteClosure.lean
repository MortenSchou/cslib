/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Foundations.Data.Search
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Relation

/-! # Deciding reachability in finite relations

On a finite type with a decidable relation `r`, the reflexive-transitive closure `ReflTransGen r` is
decidable: grow the set of elements reachable from a start element until it is stable, using
`searchIter`.

## Main definitions

- `Cslib.reachFrom`: the elements reachable from an element.

## Main statements

- `Cslib.mem_reachFrom_iff`: membership in `reachFrom` is `Relation.ReflTransGen`.
- `Cslib.instDecidableReflTransGen`: reachability in a finite relation is decidable.
-/

@[expose] public section

namespace Cslib

variable {α : Type*} [Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r]

/-- One step of the search: add the successors of the elements found so far. -/
def stepClosure (S : Finset α) : Finset α :=
  S ∪ Finset.univ.filter fun b => ∃ a ∈ S, r a b

theorem subset_stepClosure (S : Finset α) : S ⊆ stepClosure r S := Finset.subset_union_left

theorem mem_stepClosure {S : Finset α} {b : α} :
    b ∈ stepClosure r S ↔ b ∈ S ∨ ∃ a ∈ S, r a b := by
  simp [stepClosure]

/-- Iterating `stepClosure` from any set reaches a stable set, since the sets grow in a finite
type. -/
theorem exists_stable_stepClosure (a : α) :
    ∃ n, stepClosure r ((stepClosure r)^[n] {a}) = (stepClosure r)^[n] {a} := by
  by_contra hcon
  push Not at hcon
  have hcard : ∀ n, n + 1 ≤ ((stepClosure r)^[n] {a}).card := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hss : (stepClosure r)^[n] {a} ⊂ (stepClosure r)^[n + 1] {a} := by
        rw [Function.iterate_succ_apply']
        exact Finset.ssubset_iff_subset_ne.2 ⟨subset_stepClosure r _, (hcon n).symm⟩
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (Finset.card_lt_card hss))
  have := hcard (Fintype.card α)
  have := Finset.card_le_univ ((stepClosure r)^[Fintype.card α] {a})
  omega

/-- The elements reachable from `a` by the reflexive-transitive closure of `r`. -/
def reachFrom (a : α) : Finset α :=
  searchIter (stepClosure r) (fun S => stepClosure r S = S) {a} (exists_stable_stepClosure r a)

theorem reflTransGen_of_mem_iterate {a b : α} (n : ℕ) (hb : b ∈ (stepClosure r)^[n] {a}) :
    Relation.ReflTransGen r a b := by
  induction n generalizing b with
  | zero =>
    rw [Function.iterate_zero_apply, Finset.mem_singleton] at hb
    subst hb; exact .refl
  | succ n ih =>
    rw [Function.iterate_succ_apply', mem_stepClosure] at hb
    rcases hb with hb | ⟨c, hc, hcb⟩
    · exact ih hb
    · exact (ih hc).tail hcb

theorem mem_iterate_self {a : α} (n : ℕ) : a ∈ (stepClosure r)^[n] {a} := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact subset_stepClosure r _ ih

theorem mem_reachFrom_iff {a b : α} : b ∈ reachFrom r a ↔ Relation.ReflTransGen r a b := by
  obtain ⟨n, hn, hstable⟩ := searchIter_spec (stepClosure r) (fun S => stepClosure r S = S) {a}
    (exists_stable_stepClosure r a)
  change b ∈ searchIter (stepClosure r) (fun S => stepClosure r S = S) {a}
    (exists_stable_stepClosure r a) ↔ _
  rw [hn] at hstable ⊢
  constructor
  · exact reflTransGen_of_mem_iterate r n
  · intro h
    induction h with
    | refl => exact mem_iterate_self r n
    | tail _ hcd ih =>
      rw [← hstable, mem_stepClosure]
      exact Or.inr ⟨_, ih, hcd⟩

/-- Reachability in a finite relation is decidable. -/
instance instDecidableReflTransGen (a b : α) : Decidable (Relation.ReflTransGen r a b) :=
  decidable_of_iff _ (mem_reachFrom_iff r)

end Cslib
