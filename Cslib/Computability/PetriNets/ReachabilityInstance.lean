/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.VASSimulation
public import Cslib.Computability.VAS.Effective
public import Cslib.Init
public import Mathlib.Computability.Primrec.List

/-! # Instances of the reachability problem

This file sets up the theorem that reachability of Petri nets is decidable
(see the README of this directory). The statement of that theorem has to be a computability
statement, since `Decidable P` is vacuous in classical logic. For that, the reachability problem
needs *instances*: finite objects that can be encoded as natural numbers.

An instance (`ReachInstance`) consists of a number `d` of places, a finite list of transitions
and an initial and a target marking. Vectors (arc weights and markings) are lists of natural
numbers that are read as vectors in `Fin d → ℕ` by `vecN`, and as markings of the places `Fin d`
by `toMarking`: missing entries are `0` and entries beyond the `d`-th are ignored. Hence every list
is a valid vector, which keeps the encoding free of well-formedness conditions. The net of an
instance is computed by `toPetriNet`, and every Petri net with places `Fin d` and transitions
`Fin n` and every pair of markings is represented (`ofNet`, `reachable_ofNet`).

## Main definitions

- `PetriNet.ReachInstance`: an instance of the reachability problem; it is `Primcodable`.
- `ReachInstance.toMarking`: the marking of the places `Fin d` given by a list.
- `ReachInstance.toPetriNet`: the net with places `Fin d` and one transition per list entry.
- `ReachInstance.Reachable`: the target marking is reachable from the initial one.
- `ReachInstance.stepL`, `ReachInstance.runL`: firing on lists, as total functions into `Option`;
  these are the functions whose primitive recursiveness is shown in `ReachabilityDecidable`.
- `ReachInstance.ofNet`: the instance of a net with a pair of markings.

## Main statements

- `ReachInstance.reachable_ofNet`: the instance of a net is reachable iff its target marking is.
- `ReachInstance.unlabelledTr_iff`: a step on lists is a firing of the net.
- `ReachInstance.reachable_iff_exists_accepts`: reachability is the existence of a list `σ` of
  transition indices that `runL` runs from the initial marking to the target.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

/-- An instance of the reachability problem for Petri nets: `d` places, transitions given by pairs
of a preset and a postset list, and an initial and a target marking. Lists are read as vectors by
`vecN`. -/
structure ReachInstance where
  /-- The number of places. -/
  d : ℕ
  /-- The transitions, as pairs of a preset and a postset. -/
  trans : List (List ℕ × List ℕ)
  /-- The initial marking. -/
  init : List ℕ
  /-- The target marking. -/
  target : List ℕ

namespace ReachInstance

/-- The tuple of the components of an instance, used to encode it. -/
def equivTuple : ReachInstance ≃ ℕ × List (List ℕ × List ℕ) × List ℕ × List ℕ where
  toFun I := (I.d, I.trans, I.init, I.target)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable ReachInstance := Primcodable.ofEquiv _ equivTuple

open Primrec in
/-- The number of places is a primitive recursive function of the instance. -/
theorem primrec_d : Primrec d := fst.comp (of_equiv (e := equivTuple))

open Primrec in
/-- The list of transitions is a primitive recursive function of the instance. -/
theorem primrec_trans : Primrec trans := fst.comp (snd.comp (of_equiv (e := equivTuple)))

open Primrec in
/-- The initial marking is a primitive recursive function of the instance. -/
theorem primrec_init : Primrec init :=
  fst.comp (snd.comp (snd.comp (of_equiv (e := equivTuple))))

open Primrec in
/-- The target marking is a primitive recursive function of the instance. -/
theorem primrec_target : Primrec target :=
  snd.comp (snd.comp (snd.comp (of_equiv (e := equivTuple))))

/-- The marking of the places `Fin d` given by a list: missing entries are `0`. -/
def toMarking (d : ℕ) (l : List ℕ) : Marking (Fin d) := Marking.ofFun (vecN d l)

@[simp] theorem count_toMarking (d : ℕ) (l : List ℕ) (i : Fin d) :
    (toMarking d l).count i = l.getD i 0 := by
  simp [toMarking, vecN]

variable (I : ReachInstance)

/-- The number of transitions. -/
abbrev n : ℕ := I.trans.length

/-- The net of an instance: the places are `Fin d`, and the transitions are the indices of
`I.trans`. -/
def toPetriNet : PetriNet (Fin I.d) (Fin I.n) where
  pre t := toMarking I.d (I.trans.get t).1
  post t := toMarking I.d (I.trans.get t).2

/-- The target marking of an instance is reachable from its initial marking. -/
def Reachable : Prop :=
  I.toPetriNet.Reachable (toMarking I.d I.init) (toMarking I.d I.target)

/-! ### Firing on lists -/

/-- One firing step on lists: the transition with index `k` is fired at `M`, if it exists and is
enabled. The result has exactly `d` entries. -/
def stepL (M : List ℕ) (k : ℕ) : Option (List ℕ) :=
  I.trans[k]?.bind fun t =>
    if ∀ i < I.d, t.1.getD i 0 ≤ M.getD i 0 then
      some ((List.range I.d).map fun i => M.getD i 0 - t.1.getD i 0 + t.2.getD i 0)
    else none

/-- Firing a list `σ` of transition indices from `M`. -/
def runL (M : List ℕ) (σ : List ℕ) : Option (List ℕ) :=
  σ.foldl (fun o k => o.bind fun M => I.stepL M k) (some M)

/-- Firing a non-empty list: fire the first index, then the rest. -/
theorem runL_cons (M : List ℕ) (k : ℕ) (σ : List ℕ) :
    I.runL M (k :: σ) = (I.stepL M k).bind fun M' => I.runL M' σ := by
  have h : ∀ σ : List ℕ, σ.foldl (fun o k => o.bind fun M => I.stepL M k) none = none := fun σ => by
    induction σ <;> simp_all
  rw [runL, List.foldl_cons, Option.bind_some]
  cases I.stepL M k <;> simp [h, runL]

variable {I}

/-- A step on lists succeeds iff the transition exists and is enabled; the result is then the
fired marking, listed in the first `d` coordinates. -/
theorem stepL_eq_some_iff {M M' : List ℕ} {k : ℕ} :
    I.stepL M k = some M' ↔ ∃ hk : k < I.n, (∀ i < I.d, (I.trans[k]).1.getD i 0 ≤ M.getD i 0) ∧
      M' = (List.range I.d).map fun i =>
        M.getD i 0 - (I.trans[k]).1.getD i 0 + (I.trans[k]).2.getD i 0 := by
  unfold stepL
  rcases hk : I.trans[k]? with _ | t
  · simp [List.getElem?_eq_none_iff.1 hk]
  · have hk' : k < I.n := (List.getElem?_eq_some_iff.1 hk).1
    obtain rfl : t = I.trans[k] := by simp [List.getElem?_eq_getElem hk'] at hk; exact hk.symm
    simp only [Option.bind_some]
    split_ifs with hle
    · exact ⟨fun h => ⟨hk', hle, (Option.some.inj h).symm⟩, fun ⟨_, _, h⟩ => congrArg some h.symm⟩
    · exact ⟨nofun, fun ⟨_, h, _⟩ => absurd h hle⟩

/-- A step on lists is a firing of the net. -/
theorem unlabelledTr_iff {M : List ℕ} {N : Marking (Fin I.d)} :
    I.toPetriNet.lts.UnlabelledTr (toMarking I.d M) N ↔
      ∃ k M', I.stepL M k = some M' ∧ N = toMarking I.d M' := by
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨hen, rfl⟩ := PetriNet.fires_iff.1 h
    refine ⟨t, _, stepL_eq_some_iff.2 ⟨t.2, fun i hi => ?_, rfl⟩, ?_⟩
    · simpa [toPetriNet] using Multiset.le_iff_count.1 hen ⟨i, hi⟩
    · ext i
      simp [fire, toPetriNet, i.2]
  · rintro ⟨k, M', h, rfl⟩
    obtain ⟨hk, hen, rfl⟩ := stepL_eq_some_iff.1 h
    refine ⟨⟨k, hk⟩, PetriNet.fires_iff.2
      ⟨Multiset.le_iff_count.2 fun i => by simpa [toPetriNet] using hen i i.2, ?_⟩⟩
    ext i
    simp [fire, toPetriNet, i.2]

/-- Reachability from the marking of a list is the existence of a list of transition indices that
`runL` runs from that list. -/
theorem reachable_toMarking_iff {M : List ℕ} {N : Marking (Fin I.d)} :
    I.toPetriNet.Reachable (toMarking I.d M) N ↔
      ∃ σ M', I.runL M σ = some M' ∧ N = toMarking I.d M' := by
  constructor
  · intro h
    generalize hs : toMarking I.d M = s at h
    induction h using LTS.CanReach.head_induction_on generalizing M with
    | refl => exact ⟨[], M, rfl, hs.symm⟩
    | head hab _ ih =>
      obtain ⟨k, M₁, hk, rfl⟩ := I.unlabelledTr_iff.1 (hs ▸ hab)
      obtain ⟨σ, M', hσ, hN⟩ := ih rfl
      exact ⟨k :: σ, M', by simp [runL_cons, hk, hσ], hN⟩
  · rintro ⟨σ, M', h, rfl⟩
    induction σ generalizing M with
    | nil =>
      obtain rfl : M = M' := by simpa [runL] using h
      exact LTS.CanReach.refl _ _
    | cons k σ ih =>
      obtain ⟨M₁, hk, hσ⟩ := Option.bind_eq_some_iff.1 (runL_cons .. ▸ h)
      exact (LTS.CanReach.of_unlabelledTr (I.unlabelledTr_iff.2 ⟨k, M₁, hk, rfl⟩)).trans (ih hσ)

/-- Two lists denote the same marking iff they agree in the first `d` coordinates. -/
theorem toMarking_eq_iff {a b : List ℕ} :
    toMarking I.d a = toMarking I.d b ↔ ∀ i < I.d, a.getD i 0 = b.getD i 0 := by
  simp [Multiset.ext, Fin.forall_iff]

/-- A list `σ` of transition indices is accepted if `runL` runs it from the initial marking to the
target. -/
def Accepts (σ : List ℕ) : Prop :=
  ∃ M', I.runL I.init σ = some M' ∧ ∀ i < I.d, M'.getD i 0 = I.target.getD i 0

/-- Reachability is the existence of an accepted list of transition indices. This is the form used
to show that reachability is recursively enumerable. -/
theorem reachable_iff_exists_accepts : I.Reachable ↔ ∃ σ, I.Accepts σ := by
  rw [Reachable, reachable_toMarking_iff]
  simp only [Accepts, toMarking_eq_iff, eq_comm (a := I.target.getD _ _)]

/-! ### Every net is represented -/

/-- The instance of a net with places `Fin d` and transitions `Fin n`, with an initial and a target
marking. -/
def ofNet {d n : ℕ} (N : PetriNet (Fin d) (Fin n)) (M M' : Marking (Fin d)) : ReachInstance where
  d := d
  trans := List.ofFn fun t => (List.ofFn (•[N] t).count, List.ofFn (t •[N]).count)
  init := List.ofFn M.count
  target := List.ofFn M'.count

/-- The list of the token counts of a marking denotes the marking. -/
@[simp] theorem toMarking_ofFn_count {d : ℕ} (M : Marking (Fin d)) :
    toMarking d (List.ofFn M.count) = M := by
  simp [toMarking]

/-- The instance of a net is reachable iff the target is reachable in the net. -/
theorem reachable_ofNet {d n : ℕ} (N : PetriNet (Fin d) (Fin n)) (M M' : Marking (Fin d)) :
    (ofNet N M M').Reachable ↔ M ⇝[N] M' := by
  have hn : (ofNet N M M').n = n := List.length_ofFn
  have hpre (t) : •[(ofNet N M M').toPetriNet] t = •[N] (Fin.cast hn t) := by
    simp [toPetriNet, ofNet]
    rfl
  have hpost (t) : t •[(ofNet N M M').toPetriNet] = (Fin.cast hn t) •[N] := by
    simp [toPetriNet, ofNet]
    rfl
  change (ofNet N M M').toPetriNet.Reachable (toMarking d (List.ofFn M.count))
    (toMarking d (List.ofFn M'.count)) ↔ _
  rw [toMarking_ofFn_count, toMarking_ofFn_count]
  refine LTS.CanReach.iff_of_equiv (lts' := N.lts) (Equiv.refl _) fun s s' => ?_
  constructor
  · rintro ⟨t, R, h1, h2⟩
    exact ⟨Fin.cast hn t, R, hpre t ▸ h1, hpost t ▸ h2⟩
  · rintro ⟨t, R, h1, h2⟩
    exact ⟨Fin.cast hn.symm t, R, by rw [hpre]; exact h1, by rw [hpost]; exact h2⟩

end ReachInstance

end PetriNet

end Cslib
