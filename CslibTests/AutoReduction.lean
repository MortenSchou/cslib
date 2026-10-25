/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.Decision.AutoReduction

/-! # Deciding properties of nets by automatic reduction

Nets over `Fin n` places and `Fin m` transitions are reduced by `PetriNet.reduce` (series
transitions, series places, parallel transitions and places, self-loop and isolated places), and
the existing decision procedures are run on the reduced net.

* `forkJoin 3 3` is a workflow net with a fork into three chains of three series transitions that
  are joined again: 14 places, 11 transitions. The automatic reduction leaves 5 places and 2
  transitions, and deciding soundness on the reduced net is fast. Most of the time of the examples
  is spent in deciding that the original net is a workflow net, which is required to transfer the
  answer.
* `ring 10` with three tokens in the ring and a lock has 220 reachable markings. The automatic
  reduction leaves one transition and a single reachable marking.
* Each rule of the search is exercised by an example, and some nets are irreducible, or reduce to
  nets whose answer is negative.
-/

namespace CslibTests.AutoReduction

open Cslib PetriNet
open scoped PetriNet

/-! ### A net from lists of arcs -/

/-- The net over `n + 1` places with the transition `t` consuming the places `(arcs t).1` and
producing into `(arcs t).2`, for `t < m`. Out-of-range indices wrap around, so each use is
accompanied by a check of `ListsOK`. -/
def ofLists (n m : ℕ) (arcs : List (List ℕ × List ℕ)) : PetriNet (Fin (n + 1)) (Fin m) where
  pre t := ((arcs.getD t.val ([], [])).1.map (Fin.ofNat (n + 1)) : List (Fin (n + 1)))
  post t := ((arcs.getD t.val ([], [])).2.map (Fin.ofNat (n + 1)) : List (Fin (n + 1)))

/-- The arcs describe `m` transitions over the places `0, …, n`. -/
abbrev ListsOK (n m : ℕ) (arcs : List (List ℕ × List ℕ)) : Prop :=
  arcs.length = m ∧ ∀ a ∈ arcs, ∀ x ∈ a.1 ++ a.2, x ≤ n

/-! ### A fork into chains of series transitions, and a join

Place `0` is the source and place `k * (len + 1) + 1` the sink. The `b`-th chain has the places
`1 + b * (len + 1) + j` for `j ≤ len`. -/

/-- A workflow net: `split` forks the token of the source into `k` chains of `len` series
transitions, and `join` waits for all of them. -/
def forkJoin (k len : ℕ) : PetriNet (Fin (k * (len + 1) + 1 + 1)) (Fin (k * len + 1 + 1)) where
  pre t :=
    if t.val = 0 then {Fin.ofNat _ 0}
    else if t.val = k * len + 1 then
      ((List.range k).map fun b => Fin.ofNat (k * (len + 1) + 1 + 1) (1 + b * (len + 1) + len) :
        List _)
    else
      {Fin.ofNat _ (1 + ((t.val - 1) / len) * (len + 1) + (t.val - 1) % len)}
  post t :=
    if t.val = 0 then
      ((List.range k).map fun b => Fin.ofNat (k * (len + 1) + 1 + 1) (1 + b * (len + 1)) : List _)
    else if t.val = k * len + 1 then {Fin.ofNat _ (k * (len + 1) + 1)}
    else
      {Fin.ofNat _ (1 + ((t.val - 1) / len) * (len + 1) + (t.val - 1) % len + 1)}

/-- Two chains of four series transitions. -/
abbrev W₂ : PetriNet (Fin 12) (Fin 10) := forkJoin 2 4

abbrev w₂i : Fin 12 := 0

abbrev w₂o : Fin 12 := 11

theorem W₂_isWFNet : W₂.IsWFNet w₂i w₂o := by decide +kernel

/-- Directly, the net has 27 reachable markings. -/
example : (W₂.reachSet {w₂i} 10).card = 27 := by decide +kernel

example : W₂.Closed {w₂i} 10 := by decide +kernel

/-- Eight series transitions are fused, and the search stops at a net with 4 places and 2
transitions. -/
example : (reduceWF W₂ w₂i w₂o).places = 4 ∧ (reduceWF W₂ w₂i w₂o).transitions = 2 := by
  decide +kernel

/-- The reduced net has three reachable markings, instead of 27. -/
example : ((reduceWF W₂ w₂i w₂o).net.reachSet {(reduceWF W₂ w₂i w₂o).source} 3).card = 3 := by
  decide +kernel

/-- The reduction has a certificate, with the source and the sink tracked. -/
example : W₂.ReducesWF w₂i w₂o (reduceWF W₂ w₂i w₂o).net (reduceWF W₂ w₂i w₂o).source
    (reduceWF W₂ w₂i w₂o).sink := (reduceWF W₂ w₂i w₂o).reduces

/-- The result of the reduction is a fixed point: no rule applies. -/
example : (reduceWF W₂ w₂i w₂o).net.stepWF (reduceWF W₂ w₂i w₂o).source
    (reduceWF W₂ w₂i w₂o).sink = none :=
  reduceWF_normal W₂ w₂i w₂o

/-- With the net known to be a workflow net, only soundness is decided on the reduced net. -/
example : W₂.Sound w₂i w₂o :=
  of_decide_eq_true (inst := decideSoundReduced W₂ w₂i w₂o W₂_isWFNet)
    (by decide +kernel)

/-- Three chains of three series transitions. The reduction leaves 5 places and 2 transitions;
soundness is decided automatically. -/
abbrev W : PetriNet (Fin 14) (Fin 11) := forkJoin 3 3

abbrev wi : Fin 14 := 0

abbrev wo : Fin 14 := 13

example : (reduceWF W wi wo).places = 5 ∧ (reduceWF W wi wo).transitions = 2 := by
  decide +kernel

/-- Soundness, decided on the reduced net. -/
example : W.IsWFNet wi wo ∧ W.Sound wi wo :=
  of_decide_eq_true (inst := decideWFNetAndSoundReduced W wi wo) (by decide +kernel)

/-! ### An unsound workflow net

The transition `skip` moves the token of `a1` to the sink, past the rest of the chain and past the
other chain: the sink can be marked while a token is left in the second chain. -/

/-- Places: `i = 0`, chain `a0 a1 a2 a3 = 1 2 3 4`, chain `b0 b1 b2 = 5 6 7`, sink `o = 8`. -/
def badArcs : List (List ℕ × List ℕ) :=
  [([0], [1, 5]), ([1], [2]), ([2], [3]), ([3], [4]), ([5], [6]), ([6], [7]), ([4, 7], [8]),
    ([2], [8])]

example : ListsOK 8 8 badArcs := by decide

def bad : PetriNet (Fin 9) (Fin 8) := ofLists 8 8 badArcs

example : bad.IsWFNet 0 8 := by decide +kernel

example : ¬ bad.Sound 0 8 := by decide +kernel

/-- The net is reduced, by fusing the series. -/
example : (reduceWF bad 0 8).places < 9 ∧ (reduceWF bad 0 8).transitions < 8 := by
  decide +kernel

/-- The unsound net is rejected after reduction. -/
example : ¬ (bad.IsWFNet 0 8 ∧ bad.Sound 0 8) :=
  of_decide_eq_false (inst := decideWFNetAndSoundReduced bad 0 8) (by decide +kernel)

/-! ### A workflow net with parallel transitions

The source `0` is split by two parallel transitions into the places `1` and `2`, which a join moves
to the sink `3`. No place is drained, so only the deletion of a parallel transition applies. -/

def parArcs : List (List ℕ × List ℕ) := [([0], [1, 2]), ([0], [1, 2]), ([1, 2], [3])]

example : ListsOK 3 3 parArcs := by decide

def par : PetriNet (Fin 4) (Fin 3) := ofLists 3 3 parArcs

theorem par_isWFNet : par.IsWFNet 0 3 := by decide +kernel

example : (tryFuseDrainWF par 0 3).isNone := by decide +kernel

example : (tryRemoveParallelTransitionWF par 0 3).isSome := by decide +kernel

example : (reduceWF par 0 3).places = 4 ∧ (reduceWF par 0 3).transitions = 2 := by
  decide +kernel

example : par.Sound 0 3 :=
  of_decide_eq_true (inst := decideSoundReduced par 0 3 par_isWFNet) (by decide +kernel)

/-! ### A ring with a lock

Three tokens circulate on a ring of ten places, and a lock `L` is read by the first and the last
transition. The lock is a self-loop place; the nine other transitions are series. -/

/-- The ring of `len` places `0, …, len - 1` and the lock `len`. -/
def ring (len : ℕ) : PetriNet (Fin (len + 1)) (Fin len) where
  pre t :=
    if t.val = 0 then {Fin.ofNat _ 0, Fin.ofNat _ len}
    else if t.val + 1 = len then {Fin.ofNat _ t.val, Fin.ofNat _ len}
    else {Fin.ofNat _ t.val}
  post t :=
    if t.val = 0 then {Fin.ofNat _ 1, Fin.ofNat _ len}
    else if t.val + 1 = len then {Fin.ofNat _ 0, Fin.ofNat _ len}
    else {Fin.ofNat _ (t.val + 1)}

/-- `k` tokens in the first place of the ring, and the lock. -/
def ring₀ (len k : ℕ) : Marking (Fin (len + 1)) :=
  Multiset.replicate k (Fin.ofNat _ 0) + {Fin.ofNat _ len}

abbrev R : PetriNet (Fin 11) (Fin 10) := ring 10

abbrev R₀ : Marking (Fin 11) := ring₀ 10 3

/-- A smaller ring of six places with two tokens, directly: 21 reachable markings. -/
example : ((ring 6).reachSet (ring₀ 6 2) 12).card = 21 := by decide +kernel

example : (ring 6).Closed (ring₀ 6 2) 12 := by decide +kernel

example : ((reduce (ring 6) (ring₀ 6 2)).net.reachSet (reduce (ring 6) (ring₀ 6 2)).init 1).card =
    1 := by decide +kernel

-- The ring of ten places with three tokens has 220 reachable markings (computed by `#eval`; the
-- direct evaluation by the kernel is slow).

/-- The reduced net has one transition and no places, and a single reachable marking. -/
example : (reduce R R₀).places = 0 ∧ (reduce R R₀).transitions = 1 := by decide +kernel

example : ((reduce R R₀).net.reachSet (reduce R R₀).init 1).card = 1 := by decide +kernel

example : (reduce R R₀).net.step (reduce R R₀).init = none := reduce_normal R R₀

/-- A longer ring: the reduction takes about three seconds. -/
abbrev R40 : PetriNet (Fin 41) (Fin 40) := ring 40

abbrev R40₀ : Marking (Fin 41) := ring₀ 40 3

example : (reduce R40 R40₀).places = 0 ∧ (reduce R40 R40₀).transitions = 1 := by
  decide +kernel

/-- Boundedness, decided on the reduced net. -/
example : R.Bounded R₀ :=
  of_decide_eq_true (inst := decideBoundedReduced R R₀) (by decide +kernel)

/-- Boundedness and liveness, decided on the reduced net. -/
example : R.Bounded R₀ ∧ R.Live R₀ :=
  of_decide_eq_true (inst := decideBoundedAndLiveReduced R R₀) (by decide +kernel)

/-- Boundedness and deadlock-freedom, decided on the reduced net. -/
example : R.Bounded R₀ ∧ ∀ M, R₀ ⇝[R] M → ¬ R.Dead M :=
  of_decide_eq_true (inst := decideBoundedAndDeadlockFreeReduced R R₀) (by decide +kernel)

/-! ### Two processes taking two locks in opposite orders -/

/-- Places: locks `l1 l2 = 0 1`, process `a0 a1 a2 = 2 3 4`, process `b0 b1 b2 = 5 6 7`. -/
def locksArcs : List (List ℕ × List ℕ) :=
  [([2, 0], [3]), ([3, 1], [4]), ([4], [2, 0, 1]), ([5, 1], [6]), ([6, 0], [7]),
    ([7], [5, 0, 1])]

example : ListsOK 7 6 locksArcs := by decide

def locks : PetriNet (Fin 8) (Fin 6) := ofLists 7 6 locksArcs

abbrev locks₀ : Marking (Fin 8) := {0, 1, 2, 5}

/-- Fusing the release of each process into its second acquisition. -/
example : (reduce locks locks₀).places = 6 ∧ (reduce locks locks₀).transitions = 4 := by
  decide +kernel

example : locks.Bounded locks₀ :=
  of_decide_eq_true (inst := decideBoundedReduced locks locks₀) (by decide +kernel)

/-- The deadlock, where each process holds one lock, is found. -/
example : ¬ (locks.Bounded locks₀ ∧
    ∀ M, locks₀ ⇝[locks] M → ¬ locks.Dead M) :=
  of_decide_eq_false (inst := decideBoundedAndDeadlockFreeReduced locks locks₀)
    (by decide +kernel)

/-! ### Each rule of the search

Nets on which a single rule applies. The nets are given by lists of arcs. -/

/-- The places `s0 s1 s2 p q z` are `0, …, 5`, and the transitions are `step`, `step'`, `mid`,
`back`. The transitions `step` and `step'` are parallel, and both read the parallel places `p` and
`q`. The place `z` is isolated. -/
def miscArcs : List (List ℕ × List ℕ) :=
  [([0, 3, 4], [1, 3, 4]), ([0, 3, 4], [1, 3, 4]), ([1], [2]), ([2], [0])]

example : ListsOK 5 4 miscArcs := by decide

def misc : PetriNet (Fin 6) (Fin 4) := ofLists 5 4 miscArcs

/-- The tokens of `s0`, two in `p`, one in `q` and one in `z`. -/
abbrev misc₀ : Marking (Fin 6) := {0, 3, 3, 4, 5}

example : (tryFuseDrain misc misc₀).isSome := by decide +kernel

example : (tryRemoveParallelTransition misc misc₀).isSome := by decide +kernel

example : (tryRemoveParallelPlace misc misc₀).isSome := by decide +kernel

example : (tryRemoveSelfLoopPlace misc misc₀).isSome := by decide +kernel

example : (tryRemoveIsolatedPlace misc misc₀).isSome := by decide +kernel

/-- No transition has a twin that is a self-loop transition. -/
example : (tryRemoveSelfLoopTransition misc misc₀).isNone := by decide +kernel

/-- The search deletes the parallel transition, the parallel place, the isolated place and fuses
the series. -/
example : (reduce misc misc₀).places = 0 ∧ (reduce misc misc₀).transitions = 1 := by
  decide +kernel

example : misc.Bounded misc₀ ∧ misc.Live misc₀ :=
  of_decide_eq_true (inst := decideBoundedAndLiveReduced misc misc₀) (by decide +kernel)

/-- The places `a b` are `0, 1`. The transition `loop` is a self-loop transition that reads `a`,
as does `go`, which has the same preset: `loop` is deleted. -/
def twinArcs : List (List ℕ × List ℕ) := [([0], [1]), ([1], [0]), ([0], [0])]

example : ListsOK 1 3 twinArcs := by decide

def twin : PetriNet (Fin 2) (Fin 3) := ofLists 1 3 twinArcs

abbrev twin₀ : Marking (Fin 2) := {0}

example : (tryRemoveSelfLoopTransition twin twin₀).isSome := by decide +kernel

/-- The certificate of the search for a net with a self-loop transition preserves liveness and
deadlocks. -/
example : twin.Bounded twin₀ ∧ twin.Live twin₀ :=
  of_decide_eq_true (inst := decideBoundedAndLiveReduced twin twin₀) (by decide +kernel)

example : twin.Bounded twin₀ ∧
    ∀ M, twin₀ ⇝[twin] M → ¬ twin.Dead M :=
  of_decide_eq_true (inst := decideBoundedAndDeadlockFreeReduced twin twin₀) (by decide +kernel)

/-- A self-loop transition without a twin is not deleted: from `{a}` it is the only enabled
transition, so the net is deadlock-free, whereas the net without it is not. -/
def loneArcs : List (List ℕ × List ℕ) := [([0], [0]), ([1], [2])]

example : ListsOK 2 2 loneArcs := by decide

def lone : PetriNet (Fin 3) (Fin 2) := ofLists 2 2 loneArcs

abbrev lone₀ : Marking (Fin 3) := {0}

example : (tryRemoveSelfLoopTransition lone lone₀).isNone := by decide +kernel

/-- For boundedness alone the transition is deleted all the same, and the reduction stops with one
transition. -/
example : (reduceBounded lone lone₀).transitions = 1 := by decide +kernel

example : (reduce lone lone₀).transitions = 2 := by decide +kernel

example : lone.Bounded lone₀ :=
  of_decide_eq_true (inst := decideBoundedReduced lone lone₀) (by decide +kernel)

/-! ### Irreducible nets, and rules that must not apply -/

/-- A synchronisation: every transition has two input places, no place is isolated, and no two
places or transitions are parallel. No rule applies. The net is unbounded: each round adds a token
to `b`. -/
def syncArcs : List (List ℕ × List ℕ) := [([0, 1], [2, 3, 3]), ([2, 3], [0, 1, 1])]

example : ListsOK 3 2 syncArcs := by decide

def sync : PetriNet (Fin 4) (Fin 2) := ofLists 3 2 syncArcs

abbrev sync₀ : Marking (Fin 4) := {0, 1}

example : (step sync sync₀).isNone := by decide +kernel

example : (reduce sync sync₀).places = 4 ∧ (reduce sync sync₀).transitions = 2 := by
  decide +kernel

/-- Boundedness is decided on the net itself, which is unbounded. -/
example : ¬ sync.Bounded sync₀ :=
  of_decide_eq_false (inst := decideBoundedReduced sync sync₀) (by decide +kernel)

/-- The place `0` is drained by `go`, but no transition produces into it: a fusion would make
the transition `go` forget that it needs a token there. The search leaves the net alone. -/
def sourceArcs : List (List ℕ × List ℕ) := [([0], [1])]

example : ListsOK 1 1 sourceArcs := by decide

def source : PetriNet (Fin 2) (Fin 1) := ofLists 1 1 sourceArcs

abbrev source₀ : Marking (Fin 2) := {0}

example : source.IsDrain 0 0 := by decide +kernel

example : (step source source₀).isNone := by decide +kernel

/-- A token that is multiplied: the places `0, 1`, with `up` producing two tokens in `1`. The
fusion of `0` into `up` leaves a single place with a transition that adds a token. The reduced net
is unbounded, hence so is the net. -/
def growArcs : List (List ℕ × List ℕ) := [([0], [1, 1]), ([1], [0])]

example : ListsOK 1 2 growArcs := by decide

def grow : PetriNet (Fin 2) (Fin 2) := ofLists 1 2 growArcs

abbrev grow₀ : Marking (Fin 2) := {0}

example : (reduce grow grow₀).places = 1 ∧ (reduce grow grow₀).transitions = 1 := by
  decide +kernel

example : ¬ grow.Bounded grow₀ :=
  of_decide_eq_false (inst := decideBoundedReduced grow grow₀) (by decide +kernel)

/-- A bounded net that is not live: the token walks from `0` to `2`, and stays there. -/
def walkArcs : List (List ℕ × List ℕ) := [([0], [1]), ([1], [2])]

example : ListsOK 2 2 walkArcs := by decide

def walk : PetriNet (Fin 3) (Fin 2) := ofLists 2 2 walkArcs

abbrev walk₀ : Marking (Fin 3) := {0}

example : (reduce walk walk₀).places = 2 ∧ (reduce walk walk₀).transitions = 1 := by
  decide +kernel

example : walk.Bounded walk₀ :=
  of_decide_eq_true (inst := decideBoundedReduced walk walk₀) (by decide +kernel)

/-- Not live, decided on the reduced net. -/
example : ¬ walk.Live walk₀ :=
  of_decide_eq_false
    (inst := decideLiveReduced walk walk₀
      (of_decide_eq_true (inst := decideBoundedReduced walk walk₀) (by decide +kernel)))
    (by decide +kernel)

/-- The net has a dead marking, `{2}`: it is not deadlock-free. -/
example : ¬ (walk.Bounded walk₀ ∧
    ∀ M, walk₀ ⇝[walk] M →
      ¬ walk.Dead M) :=
  of_decide_eq_false (inst := decideBoundedAndDeadlockFreeReduced walk walk₀) (by decide +kernel)

/-- A net with an isolated place is not a workflow net, and is rejected without looking at
soundness. -/
def notWFArcs : List (List ℕ × List ℕ) := [([0], [1])]

example : ListsOK 2 1 notWFArcs := by decide

def notWF : PetriNet (Fin 3) (Fin 1) := ofLists 2 1 notWFArcs

example : ¬ (notWF.IsWFNet 0 1 ∧ notWF.Sound 0 1) :=
  of_decide_eq_false (inst := decideWFNetAndSoundReduced notWF 0 1) (by decide +kernel)

/-! ### Nets over other finite types

A ring `x → a → b → c → x` with a lock `m`, over enumerated types of places and transitions. The
decision procedures with the suffix `Equiv` take bijections with `Fin` types, and rename the net. -/

inductive Cell | x | a | b | c | m
  deriving DecidableEq

inductive Move | enter | s1 | s2 | leave
  deriving DecidableEq

open Cell Move

/-- The cells, numbered. -/
def cellEquiv : Cell ≃ Fin 5 where
  toFun := fun | x => 0 | a => 1 | b => 2 | c => 3 | m => 4
  invFun := ![x, a, b, c, m]
  left_inv := fun y => by cases y <;> rfl
  right_inv := fun k => by fin_cases k <;> rfl

/-- The moves, numbered. -/
def moveEquiv : Move ≃ Fin 4 where
  toFun := fun | enter => 0 | s1 => 1 | s2 => 2 | leave => 3
  invFun := ![enter, s1, s2, leave]
  left_inv := fun y => by cases y <;> rfl
  right_inv := fun k => by fin_cases k <;> rfl

def cycle : PetriNet Cell Move where
  pre := fun | enter => {x, m} | s1 => {a} | s2 => {b} | leave => {c, m}
  post := fun | enter => {a, m} | s1 => {b} | s2 => {c} | leave => {x, m}

/-- Two tokens in `x`, and the lock. -/
abbrev cycle₀ : Marking Cell := {x, x, m}

example : cycle.Bounded cycle₀ ∧ cycle.Live cycle₀ :=
  of_decide_eq_true (inst := decideBoundedAndLiveReducedEquiv cycle cellEquiv moveEquiv cycle₀)
    (by decide +kernel)

example : cycle.Bounded cycle₀ ∧
    ∀ M, cycle₀ ⇝[cycle] M → ¬ cycle.Dead M :=
  of_decide_eq_true
    (inst := decideBoundedAndDeadlockFreeReducedEquiv cycle cellEquiv moveEquiv cycle₀)
    (by decide +kernel)

/-- With the lock alone no transition can ever fire: the net is bounded, and not live. -/
abbrev lockOnly : Marking Cell := {m}

example : ¬ cycle.Live lockOnly :=
  of_decide_eq_false
    (inst := decideLiveReducedEquiv cycle cellEquiv moveEquiv lockOnly
      (of_decide_eq_true (inst := decideBoundedReducedEquiv cycle cellEquiv moveEquiv lockOnly)
        (by decide +kernel)))
    (by decide +kernel)

end CslibTests.AutoReduction
