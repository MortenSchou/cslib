/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Init
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Algebra.Order.Group.Multiset

/-! # Place/transition Petri nets

A place/transition (P/T) Petri net has a type of places and a type of transitions. Each transition
consumes tokens from its input places (its *preset*) and produces tokens in its output places
(its *postset*). Following the Petri net literature, presets, postsets and markings are multisets
of places: the multiplicity of a place is its arc weight, or its number of tokens.

Multisets are computable as soon as places have decidable equality, so the same nets serve both as
mathematical objects and as executable examples (`#eval`, `decide`).

## Main definitions

- `PetriNet`: a P/T net, with presets `pre` and postsets `post`.
- `PetriNet.Marking`: a distribution of tokens over places, as a multiset.
- `PetriNet.Enabled`: a transition is enabled at a marking if the marking contains its preset.
- `PetriNet.Fires`: firing a transition leads from one marking to another.
- `PetriNet.fire`, `PetriNet.fire?`, `PetriNet.run`: the computable firing rule.

## Notation

Scoped to `PetriNet` (use `open scoped PetriNet`), following the Petri net literature with the net
written in brackets at the end.

- `•[N] t` and `t •[N]` are the preset and the postset of the transition `t` in the net `N`,
  that is `N.pre t` and `N.post t`.
- `M [t⟩[N]` states that the transition `t` is enabled at the marking `M` in the net `N`.
  The marking before `[t⟩` has to be parenthesised if it is a function application, since
  `[t⟩` would otherwise read as a list argument.
- `M [t⟩[N] M'` states that firing `t` at `M` leads to `M'` in the net `N`.
- `M ⇝[N] M'` states that `M'` is reachable from `M` in the net `N`.

Markings are written as multiset literals: `{a, b, b}` has one token in `a` and two in `b`, and the
empty marking is `0`.

## References

* [T. Murata, *Petri nets: Properties, analysis and applications*][Murata1989]
* [N. Winskel and M. Nielsen, *Models for concurrency*][WinskelNielsen1995]
-/

@[expose] public section

/-- Multisets are canonically ordered: `s ≤ t` iff `t = s + u` for some `u`. This instance is
missing from Mathlib. -/
instance Multiset.instCanonicallyOrderedAdd {α : Type*} : CanonicallyOrderedAdd (Multiset α) where
  exists_add_of_le h := exists_add_of_le h
  le_add_self _ _ := Multiset.le_add_left _ _
  le_self_add _ _ := Multiset.le_add_right _ _

namespace Cslib

universe u v

/-- A place/transition Petri net. The multiplicity of a place in `pre t` (resp. `post t`) is the
weight of the arc from the place to `t` (resp. from `t` to the place). -/
structure PetriNet (Place : Type u) (Transition : Type v) where
  /-- Tokens consumed when a transition fires. -/
  pre : Transition → Multiset Place
  /-- Tokens produced when a transition fires. -/
  post : Transition → Multiset Place

namespace PetriNet

variable {Place : Type u} {Transition : Type v}

/-- The preset of a transition: `•[N] t` is `N.pre t`. -/
scoped notation:max "•[" N "] " t:max => PetriNet.pre N t

/-- The postset of a transition: `t •[N]` is `N.post t`. -/
scoped notation:max t:max " •[" N "]" => PetriNet.post N t

/-- A marking is a finite multiset of places: the number of tokens in `p` is `M.count p`. -/
abbrev Marking (Place : Type u) := Multiset Place

variable (N : PetriNet Place Transition)

/-- A transition is enabled at a marking if the marking contains its preset. -/
def Enabled (M : Marking Place) (t : Transition) : Prop :=
  •[N] t ≤ M

/-- Firing a transition from `M` to `M'`: the tokens of `M` not consumed by `t` are `R`. -/
def Fires (M : Marking Place) (t : Transition) (M' : Marking Place) : Prop :=
  ∃ R, M = •[N] t + R ∧ M' = R + t •[N]

/-- The marking obtained by firing `t` at `M`. It is only meaningful when `t` is enabled. -/
def fire [DecidableEq Place] (M : Marking Place) (t : Transition) : Marking Place :=
  M - •[N] t + t •[N]

/-- Fire `t` at `M`, if it is enabled. -/
def fire? [DecidableEq Place] (M : Marking Place) (t : Transition) : Option (Marking Place) :=
  if •[N] t ≤ M then some (N.fire M t) else none

/-- Run a firing sequence, if every transition in it is enabled in turn. -/
def run [DecidableEq Place] (M : Marking Place) : List Transition → Option (Marking Place)
  | [] => some M
  | t :: ts => (N.fire? M t).bind fun M' => run M' ts

/-- `M [t⟩[N]` says that `t` is enabled at `M` in the net `N`. -/
scoped syntax:50 term:51 " [" term "⟩[" term "]" : term

scoped macro_rules
  | `($M [$t⟩[$N]) => `(PetriNet.Enabled $N $M $t)

/-- Pretty-printer for the notation. -/
@[scoped app_unexpander PetriNet.Enabled]
meta def unexpandEnabled : Lean.PrettyPrinter.Unexpander
  | `($_ $N $M $t) => `($M [$t⟩[$N])
  | _ => throw ()

/-- `M [t⟩[N] M'` says that firing `t` leads from `M` to `M'` in the net `N`. -/
scoped syntax:50 term:51 " [" term "⟩[" term "] " term:51 : term

scoped macro_rules
  | `($M [$t⟩[$N] $M') => `(PetriNet.Fires $N $M $t $M')

/-- Pretty-printer for the notation. -/
@[scoped app_unexpander PetriNet.Fires]
meta def unexpandFires : Lean.PrettyPrinter.Unexpander
  | `($_ $N $M $t $M') => `($M [$t⟩[$N] $M')
  | _ => throw ()

instance [DecidableEq Place] (M : Marking Place) (t : Transition) : Decidable (M [t⟩[N]) :=
  inferInstanceAs (Decidable (_ ≤ _))

variable {N}

@[grind =]
theorem fires_iff [DecidableEq Place] {M M' : Marking Place} {t : Transition} :
    M [t⟩[N] M' ↔ M [t⟩[N] ∧ M' = N.fire M t := by
  constructor
  · rintro ⟨R, rfl, rfl⟩
    refine ⟨le_self_add, ?_⟩
    simp [fire, add_comm R]
  · rintro ⟨h, rfl⟩
    refine ⟨M - •[N] t, (add_tsub_cancel_of_le h).symm, rfl⟩

instance [DecidableEq Place] (M : Marking Place) (t : Transition) (M' : Marking Place) :
    Decidable (M [t⟩[N] M') :=
  decidable_of_iff _ fires_iff.symm

theorem fire?_eq_some_iff [DecidableEq Place] {M M' : Marking Place} {t : Transition} :
    N.fire? M t = some M' ↔ M [t⟩[N] M' := by
  rw [fires_iff, fire?]
  split_ifs with h
  · simp [Enabled, h, eq_comm]
  · simp [Enabled, h]

theorem run_append [DecidableEq Place] (M : Marking Place) (ts₁ ts₂ : List Transition) :
    N.run M (ts₁ ++ ts₂) = (N.run M ts₁).bind fun M' => N.run M' ts₂ := by
  induction ts₁ generalizing M with
  | nil => simp [run]
  | cons t ts ih =>
    simp only [List.cons_append, run]
    cases N.fire? M t <;> simp [ih]

/-- Firing is monotone: extra tokens never disable a transition. -/
theorem Fires.add {M M' : Marking Place} {t : Transition} (h : M [t⟩[N] M') (K : Marking Place) :
    (M + K) [t⟩[N] (M' + K) := by
  obtain ⟨R, rfl, rfl⟩ := h
  exact ⟨R + K, add_assoc .., add_right_comm ..⟩

/-- Firing conserves tokens up to the difference between the postset and preset sizes. -/
theorem Fires.card_add {M M' : Marking Place} {t : Transition} (h : M [t⟩[N] M') :
    M.card + (t •[N]).card = M'.card + (•[N] t).card := by
  obtain ⟨R, rfl, rfl⟩ := h
  simp only [Multiset.card_add]
  omega

end PetriNet

end Cslib
