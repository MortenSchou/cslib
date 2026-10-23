/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Elab
public meta import Lean.PrettyPrinter.Delaborator
public import Cslib.Init
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Weight

/-! # Place/transition Petri nets

A place/transition (P/T) Petri net has a type of places and a type of transitions. Each transition
consumes tokens from its input places (its *preset*) and produces tokens in its output places
(its *postset*), with arc weights given by natural numbers.

## Main definitions

- `PetriNet`: a P/T net, with arc weights `pre` and `post`.
- `PetriNet.Marking`: a distribution of tokens over places.
- `PetriNet.Enabled`: a transition is enabled at a marking if the marking covers its preset.
- `PetriNet.fire`: the marking reached by firing a transition.
- `PetriNet.Marking.size`: the total number of tokens in a marking.

## Notation

Scoped to `PetriNet` (use `open scoped PetriNet`), following the Petri net literature with the net
written in brackets at the end.

- `•[N] t` and `t •[N]` are the preset and the postset of the transition `t` in the net `N`,
  that is `N.pre t` and `N.post t`.
- `M [t⟩[N]` states that the transition `t` is enabled at the marking `M` in the net `N`. The net
  `N` may be anything with a `ToPetriNet` instance, such as an executable net.
  The marking before `[t⟩` has to be parenthesised if it is a function application, since
  `[t⟩` would otherwise read as a list argument.
- `M [t⟩[N] M'` states that firing `t` at `M` leads to `M'` in the net `N`.
- `M ⇝[N] M'` states that `M'` is reachable from `M` in the net `N`.
- `⦅a, b, c⦆` is the marking with one token in each of `a`, `b`, `c`, and more tokens for repeated
  places: it is `Multiset.toFinsupp {a, b, c}`. The empty marking is `⦅⦆`. Markings of this form
  are also pretty-printed this way.

## References

* [T. Murata, *Petri nets: Properties, analysis and applications*][Murata1989]
* [N. Winskel and M. Nielsen, *Models for concurrency*][WinskelNielsen1995]
-/

@[expose] public section

namespace Cslib

universe u v w

/-- A place/transition Petri net. -/
structure PetriNet (Place : Type u) (Transition : Type v) where
  /-- Tokens consumed from each place when a transition fires. -/
  pre : Transition → Place →₀ ℕ
  /-- Tokens produced in each place when a transition fires. -/
  post : Transition → Place →₀ ℕ

namespace PetriNet

variable {Place : Type u} {Transition : Type v}

/-- Types that can be read as a Petri net, such as executable nets. The notations
`M [t⟩[N] M'` and `M ⇝[N] M'` accept any such `N`. -/
class ToPetriNet (X : Sort w) (Place : outParam (Type u)) (Transition : outParam (Type v)) where
  /-- The Petri net denoted by an element of `X`. -/
  toPetriNet : X → PetriNet Place Transition

instance : ToPetriNet (PetriNet Place Transition) Place Transition := ⟨id⟩

/-- The preset of a transition: `•[N] t` is `N.pre t`. -/
scoped notation:max "•[" N "] " t:max => PetriNet.pre N t

/-- The postset of a transition: `t •[N]` is `N.post t`. -/
scoped notation:max t:max " •[" N "]" => PetriNet.post N t

/-- A marking assigns a finite number of tokens to each place. -/
abbrev Marking (Place : Type u) := Place →₀ ℕ

/-- A multiset literal, written as the nested `insert` and `singleton` that `{a, b, c}` stands
for. -/
scoped syntax "msetLit% " term,* : term

scoped macro_rules
  | `(msetLit% ) => `((0 : Multiset _))
  | `(msetLit% $x) => `(Singleton.singleton $x)
  | `(msetLit% $x, $xs,*) => `(Insert.insert $x (msetLit% $xs,*))

/-- The marking given by a multiset of places: `⦅a, b, b⦆` has one token in `a` and two in `b`. -/
scoped syntax "⦅" term,* "⦆" : term

scoped macro_rules
  | `(⦅$xs,*⦆) => `(Multiset.toFinsupp (msetLit% $xs,*))

open Lean PrettyPrinter Delaborator SubExpr in
/-- The places of a multiset literal `{a, b, c}`, as terms. -/
meta partial def markingElems : DelabM (Array Term) := do
  let e ← getExpr
  if e.isAppOfArity `Insert.insert 5 then
    let x ← withNaryArg 3 delab
    let rest ← withNaryArg 4 markingElems
    return #[x] ++ rest
  else if e.isAppOfArity `Singleton.singleton 4 then
    return #[← withNaryArg 3 delab]
  else if e.isAppOfArity `OfNat.ofNat 3 && (e.getArg! 1).rawNatLit? == some 0 then
    return #[]
  else failure

open Lean PrettyPrinter Delaborator SubExpr in
/-- Pretty-printer for markings given by a multiset literal: `Multiset.toFinsupp {a, b}` is shown
as `⦅a, b⦆`. -/
@[scoped delab app.DFunLike.coe]
meta def delabMarking : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity `DFunLike.coe 6
  guard <| (e.getArg! 4).isAppOf `Multiset.toFinsupp
  let xs ← withAppArg markingElems
  `(⦅$[$xs],*⦆)

/-- The total number of tokens in a marking. -/
def Marking.size (M : Marking Place) : ℕ := M.degree

@[simp] theorem Marking.size_zero : (0 : Marking Place).size = 0 := map_zero Finsupp.degree

@[simp, grind =] theorem Marking.size_add (M K : Marking Place) : (M + K).size = M.size + K.size :=
  map_add Finsupp.degree M K

@[simp] theorem Marking.size_single (p : Place) (n : ℕ) : Marking.size (Finsupp.single p n) = n :=
  Finsupp.degree_single p n

theorem Marking.le_size (M : Marking Place) (p : Place) : M p ≤ M.size :=
  Finsupp.le_degree p M

variable (N : PetriNet Place Transition)

/-- A transition is enabled at a marking if the marking has enough tokens in every input place. -/
def Enabled (M : Marking Place) (t : Transition) : Prop :=
  •[N] t ≤ M

/-- The marking obtained by firing `t` at `M`. It is only meaningful when `t` is enabled. -/
noncomputable def fire (M : Marking Place) (t : Transition) : Marking Place :=
  M - •[N] t + t •[N]

/-- Firing a transition from `M` to `M'`, stated without truncated subtraction: the tokens of `M`
not consumed by `t` are `R`. -/
def Fires (M : Marking Place) (t : Transition) (M' : Marking Place) : Prop :=
  ∃ R, M = •[N] t + R ∧ M' = R + t •[N]

/-- `M [t⟩[N]` says that `t` is enabled at `M` in the net `N`. -/
scoped syntax:50 term:51 " [" term "⟩[" term "]" : term

scoped macro_rules
  | `($M [$t⟩[$N]) => `(PetriNet.Enabled (net% $N) $M $t)

/-- Pretty-printer for the notation. -/
@[scoped app_unexpander PetriNet.Enabled]
meta def unexpandEnabled : Lean.PrettyPrinter.Unexpander
  | `($_ $N $M $t) => `($M [$t⟩[$N])
  | _ => throw ()

/-- `M [t⟩[N] M'` says that firing `t` leads from `M` to `M'` in the net `N`. -/
scoped syntax:50 term:51 " [" term "⟩[" term "] " term:51 : term

scoped macro_rules
  | `($M [$t⟩[$N] $M') => `(PetriNet.Fires (net% $N) $M $t $M')

/-- Pretty-printer for the notation. -/
@[scoped app_unexpander PetriNet.Fires]
meta def unexpandFires : Lean.PrettyPrinter.Unexpander
  | `($_ $N $M $t $M') => `($M [$t⟩[$N] $M')
  | _ => throw ()

variable {N}

@[grind =]
theorem fires_iff {M M' : Marking Place} {t : Transition} :
    M [t⟩[N] M' ↔ M [t⟩[N] ∧ M' = N.fire M t := by
  constructor
  · rintro ⟨R, rfl, rfl⟩
    refine ⟨le_self_add, ?_⟩
    simp [fire]
  · rintro ⟨h, rfl⟩
    refine ⟨M - •[N] t, ?_, rfl⟩
    exact (add_tsub_cancel_of_le h).symm

/-- Firing is monotone: extra tokens never disable a transition. -/
theorem Fires.add {M M' : Marking Place} {t : Transition} (h : M [t⟩[N] M') (K : Marking Place) :
    (M + K) [t⟩[N] (M' + K) := by
  obtain ⟨R, rfl, rfl⟩ := h
  exact ⟨R + K, add_assoc .., add_right_comm ..⟩

/-- Firing conserves tokens up to the difference between the postset and preset weights. -/
theorem Fires.size_add {M M' : Marking Place} {t : Transition} (h : M [t⟩[N] M') :
    M.size + Marking.size (t •[N]) = M'.size + Marking.size (•[N] t) := by
  obtain ⟨R, rfl, rfl⟩ := h
  simp only [Marking.size_add]
  omega

end PetriNet

end Cslib
