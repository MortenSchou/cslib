/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.ExecutableReduction

/-! # Reductions of executable nets over `Fin`, with the indices renumbered

Deleting a place `p` from a net over `α` gives a net over `{q // q ≠ p}`. After `k` deletions the
places are a `k`-fold nested subtype, which makes instance synthesis expensive and makes the type of
the result depend on the whole history. For nets over `Fin n` places and `Fin m` transitions this
file renumbers the places and the transitions after each deletion, along the explicit bijection
`skipEquiv p : {q : Fin n // q ≠ p} ≃ Fin (n - 1)`, which closes the gap left by `p`. The
bijection is explicit (arithmetic on the values of `Fin` numerals, no choice), so the renamed net
and its marking are evaluated by the kernel, and `decide +kernel` can evaluate chains of
reductions.

Each step wraps the arc multisets of the net in one more `Multiset.map` and `dropMarking`, which the
kernel would unfold through all the earlier steps at every access. The search therefore stores the
arcs of each reduced net in tables (`ExecPetriNet.tabulate`, equal to the net by
`ExecPetriNet.tabulate_eq`), which cuts the time of the reduction of a ring of 80 places from 53 s
to 16 s.

## Main definitions

- `ExecPetriNet.skipEquiv`: the bijection between `{q // q ≠ p}` and `Fin (n - 1)`.
- `ExecPetriNet.removePlaceFin`, `ExecPetriNet.removeTransitionFin`, `ExecPetriNet.fuseFin`,
  `ExecPetriNet.dropFin`, `ExecPetriNet.collapseFin`: the reduced nets and markings, renumbered.
- `ExecPetriNet.tabulate`: the net with its arcs stored in tables.
- `ExecPetriNet.findFin`, `ExecPetriNet.findPair`: the first index, or pair of indices, that
  satisfies a decidable predicate. `ExecPetriNet.tryFin` and `ExecPetriNet.tryPair` build a result
  from the first one, with `ExecPetriNet.tryFin_eq_none_iff` and `ExecPetriNet.tryPair_eq_none_iff`
  characterising failure.
-/

@[expose] public section

namespace Cslib

namespace ExecPetriNet

open PetriNet
open scoped PetriNet

/-! ### Closing the gap left by a deleted index -/

/-- Deleting the index `p` of `Fin n` and renumbering the others: the indices below `p` stay, those
above are shifted down by one. -/
def skipEquiv {n : ℕ} (p : Fin n) : {q : Fin n // q ≠ p} ≃ Fin (n - 1) where
  toFun q := ⟨if q.1.val < p.val then q.1.val else q.1.val - 1, by
    have h₁ := q.1.isLt
    have h₂ : q.1.val ≠ p.val := fun h => q.2 (Fin.ext h)
    have h₃ := p.isLt
    split_ifs <;> omega⟩
  invFun k := ⟨⟨if k.val < p.val then k.val else k.val + 1, by
      have h₁ := k.isLt
      have h₃ := p.isLt
      split_ifs <;> omega⟩, fun h => by
    have h₁ := k.isLt
    have h₃ := p.isLt
    have := congrArg Fin.val h
    simp only at this
    split_ifs at this <;> omega⟩
  left_inv q := by
    have h₂ : q.1.val ≠ p.val := fun h => q.2 (Fin.ext h)
    apply Subtype.ext
    apply Fin.ext
    simp only
    split_ifs <;> omega
  right_inv k := by
    have h₁ := k.isLt
    have h₃ := p.isLt
    apply Fin.ext
    simp only
    split_ifs <;> omega

/-! ### Searching the indices -/

/-- The first index satisfying a decidable predicate. -/
def findFin {n : ℕ} (P : Fin n → Prop) [DecidablePred P] : Option (Fin n) :=
  (List.finRange n).find? fun i => decide (P i)

theorem findFin_spec {n : ℕ} {P : Fin n → Prop} [DecidablePred P] {i : Fin n}
    (h : findFin P = some i) : P i := by
  simpa using List.find?_some h

theorem findFin_eq_none_iff {n : ℕ} {P : Fin n → Prop} [DecidablePred P] :
    findFin P = none ↔ ∀ i, ¬ P i := by
  simp [findFin, List.find?_eq_none]

/-- The first pair of indices satisfying a decidable relation, in lexicographic order. -/
def findPair {n m : ℕ} (P : Fin n → Fin m → Prop) [∀ a b, Decidable (P a b)] :
    Option (Fin n × Fin m) :=
  (List.finRange n ×ˢ List.finRange m).find? fun x => decide (P x.1 x.2)

theorem findPair_spec {n m : ℕ} {P : Fin n → Fin m → Prop} [∀ a b, Decidable (P a b)]
    {x : Fin n × Fin m} (h : findPair P = some x) : P x.1 x.2 := by
  simpa using List.find?_some h

theorem findPair_eq_none_iff {n m : ℕ} {P : Fin n → Fin m → Prop} [∀ a b, Decidable (P a b)] :
    findPair P = none ↔ ∀ a b, ¬ P a b := by
  simp [findPair, List.find?_eq_none]

/-- Build a result from the first index satisfying `P`, if there is one. -/
def tryFin {n : ℕ} {α : Type*} (P : Fin n → Prop) [DecidablePred P] (mk : ∀ a, P a → α) :
    Option α :=
  (findFin P).attach.map fun x => mk x.1 (findFin_spec x.2)

/-- The search `tryFin` fails exactly when no index satisfies `P`. -/
theorem tryFin_eq_none_iff {n : ℕ} {α : Type*} {P : Fin n → Prop} [DecidablePred P]
    {mk : ∀ a, P a → α} : tryFin P mk = none ↔ ∀ a, ¬ P a := by
  rw [← findFin_eq_none_iff]
  simp [tryFin]

/-- Build a result from the first pair of indices satisfying `P`, if there is one. -/
def tryPair {n m : ℕ} {α : Type*} (P : Fin n → Fin m → Prop) [∀ a b, Decidable (P a b)]
    (mk : ∀ a b, P a b → α) : Option α :=
  (findPair P).attach.map fun x => mk x.1.1 x.1.2 (findPair_spec x.2)

/-- The search `tryPair` fails exactly when no pair of indices satisfies `P`. -/
theorem tryPair_eq_none_iff {n m : ℕ} {α : Type*} {P : Fin n → Fin m → Prop}
    [∀ a b, Decidable (P a b)] {mk : ∀ a b, P a b → α} :
    tryPair P mk = none ↔ ∀ a b, ¬ P a b := by
  rw [← findPair_eq_none_iff]
  simp [tryPair]

/-! ### Tabulating a net -/

/-- The net whose arc multisets are looked up in two tables. -/
def ofTables {n m : ℕ} (pre post : List (Multiset (Fin n))) : ExecPetriNet (Fin n) (Fin m) where
  pre t := pre.getD t.val 0
  post t := post.getD t.val 0

/-- The net with its arcs stored in tables, so that the multisets are computed once. -/
def tabulate {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) : ExecPetriNet (Fin n) (Fin m) :=
  ofTables (List.ofFn N.pre) (List.ofFn N.post)

theorem tabulate_eq {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) : tabulate N = N := by
  cases N with
  | mk pre post =>
    simp only [tabulate, ofTables]
    congr 1 <;> funext t <;> simp [List.getD_eq_getElem?_getD]

/-! ### The reduced nets over `Fin` -/

section Nets

variable {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m))

/-- A marking with the place `p` deleted, renumbered over `Fin (n - 1)`. -/
def dropFin (p : Fin n) (M : Multiset (Fin n)) : Multiset (Fin (n - 1)) :=
  (dropMarking p M).map (skipEquiv p)

/-- The net with the place `p` deleted, renumbered. -/
def removePlaceFin (p : Fin n) : ExecPetriNet (Fin (n - 1)) (Fin m) :=
  (N.removePlace p).renamePlaces (skipEquiv p)

/-- The net with the transition `t` deleted, renumbered. -/
def removeTransitionFin (t : Fin m) : ExecPetriNet (Fin n) (Fin (m - 1)) :=
  (N.removeTransition t).renameTransitions (skipEquiv t)

/-- The net with the transition `t` fused into the place `p` that it drains and `p` deleted,
renumbered. -/
def fuseFin (t : Fin m) (p : Fin n) : ExecPetriNet (Fin (n - 1)) (Fin (m - 1)) :=
  (N.fuseDelete t p).rename (skipEquiv p) (skipEquiv t)

/-- The marking collapsed through the fusion of `t` into `p`, renumbered. -/
def collapseFin (t : Fin m) (p : Fin n) (M : Multiset (Fin n)) : Multiset (Fin (n - 1)) :=
  (dropMarking p (N.collapseMarking t p M)).map (skipEquiv p)

end Nets

end ExecPetriNet

end Cslib
