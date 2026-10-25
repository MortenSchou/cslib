/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.Decision.Reduced

/-! # Deciding properties of nets through reductions

A workflow net with two chains of series transitions, which run in parallel. Its reachable markings
are the pairs of positions in the two chains. Fusing the series gives a net with three reachable
markings, whose soundness `decide` checks quickly; the certificate of the reduction transfers the
answer to the original net. -/

namespace CslibTests.ReducedDecisions

open Cslib PetriNet
open scoped PetriNet

/-- Side conditions and memberships of subtypes are decided by the kernel. -/
local macro "dk" : term => `(by decide +kernel)

inductive Pl | i | a1 | a2 | a3 | a4 | b1 | b2 | b3 | o
  deriving DecidableEq

inductive Tr | split | u1 | u2 | u3 | v1 | v2 | join
  deriving DecidableEq

open Pl Tr

instance : Fintype Pl := ⟨{i, a1, a2, a3, a4, b1, b2, b3, o}, fun x => by cases x <;> simp⟩

instance : Fintype Tr := ⟨{split, u1, u2, u3, v1, v2, join}, fun x => by cases x <;> simp⟩

/-- `split` forks the token of `i` into two chains `a1 → a2 → a3 → a4` and `b1 → b2 → b3`, and
`join` waits for both. -/
def wf : PetriNet Pl Tr where
  pre
    | split => {i} | u1 => {a1} | u2 => {a2} | u3 => {a3} | v1 => {b1} | v2 => {b2}
    | join => {a4, b3}
  post
    | split => {a1, b1} | u1 => {a2} | u2 => {a3} | u3 => {a4} | v1 => {b2} | v2 => {b3}
    | join => {o}

/-! ### The original net, decided directly -/

example : wf.IsWFNet i o := by decide

/-- The original net has 14 reachable markings. -/
example : (wf.reachSet {i} 7).card = 14 := by decide +kernel

example : wf.Sound i o := by decide +kernel

/-! ### The certificate: five fusions of series transitions

Each step fuses a transition with the place it drains. The reduced nets are nets over subtypes of
the places and transitions; the side conditions of each step are decided on the net at hand. -/

abbrev wf1 := wf.fuseDelete u1 a1
abbrev wf2 := wf1.fuseDelete ⟨u2, dk⟩ ⟨a2, dk⟩
abbrev wf3 := wf2.fuseDelete ⟨⟨u3, dk⟩, dk⟩ ⟨⟨a3, dk⟩, dk⟩
abbrev wf4 := wf3.fuseDelete ⟨⟨⟨v1, dk⟩, dk⟩, dk⟩ ⟨⟨⟨b1, dk⟩, dk⟩, dk⟩
abbrev wf5 := wf4.fuseDelete ⟨⟨⟨⟨v2, dk⟩, dk⟩, dk⟩, dk⟩ ⟨⟨⟨⟨b2, dk⟩, dk⟩, dk⟩, dk⟩

/-- The type of places of a net. -/
abbrev PlaceOf {P T : Type} (_ : PetriNet P T) : Type := P

/-- The source and the sink of the reduced net. -/
abbrev i5 : PlaceOf wf5 := ⟨⟨⟨⟨⟨i, dk⟩, dk⟩, dk⟩, dk⟩, dk⟩

abbrev o5 : PlaceOf wf5 := ⟨⟨⟨⟨⟨o, dk⟩, dk⟩, dk⟩, dk⟩, dk⟩

/-- The certificate: five fusions of series transitions, with the source and the sink tracked. -/
theorem cert : ReducesWF wf i o wf5 i5 o5 :=
  (ReducesWF.fuseSeries (N := wf) (t₁ := split) (t₂ := u1) (p := a1) dk dk dk).trans <|
  (ReducesWF.fuseSeries (N := wf1) (t₁ := ⟨split, dk⟩) (t₂ := ⟨u2, dk⟩) (p := ⟨a2, dk⟩)
    dk dk dk).trans <|
  (ReducesWF.fuseSeries (N := wf2) (t₁ := ⟨⟨split, dk⟩, dk⟩) (t₂ := ⟨⟨u3, dk⟩, dk⟩)
    (p := ⟨⟨a3, dk⟩, dk⟩) dk dk dk).trans <|
  (ReducesWF.fuseSeries (N := wf3) (t₁ := ⟨⟨⟨split, dk⟩, dk⟩, dk⟩)
    (t₂ := ⟨⟨⟨v1, dk⟩, dk⟩, dk⟩) (p := ⟨⟨⟨b1, dk⟩, dk⟩, dk⟩) dk dk dk).trans <|
  (ReducesWF.fuseSeries (N := wf4) (t₁ := ⟨⟨⟨⟨split, dk⟩, dk⟩, dk⟩, dk⟩)
    (t₂ := ⟨⟨⟨⟨v2, dk⟩, dk⟩, dk⟩, dk⟩) (p := ⟨⟨⟨⟨b2, dk⟩, dk⟩, dk⟩, dk⟩) dk dk dk)

/-! ### The reduced net, and the answer transferred to the original net -/

section Reduced

-- Instance search for the nets over five nested subtypes needs a larger limit.
set_option synthInstance.maxSize 512

/-- The reduced net has the structure of a workflow net. -/
example : wf5.IsWFNet i5 o5 := by decide +kernel

/-- The reduced net has three reachable markings, instead of fourteen. -/
example : (wf5.reachSet {i5} 3).card = 3 := by decide +kernel

example : wf5.Sound i5 o5 := by decide +kernel

/-- Soundness of the original net, transferred from the reduced net: only `wf5` is evaluated. -/
example : wf.Sound i o :=
  (cert.isWFNet_and_sound dk).2.1 dk

/-- The same, as a decision procedure for the original net. -/
def soundViaCert : Decidable (wf.Sound i o) :=
  decidableSoundOfReducesWF cert dk

example : wf.Sound i o := of_decide_eq_true (inst := soundViaCert) dk

end Reduced

/-! ### Reductions of a cyclic net: bounded, live, deadlock-free

Two tokens circulate on the ring `x → a → b → c → x`, and a lock `m` is read by the first and the
last transition. Deleting the self-loop place `m` and fusing the series `a`, `b` leaves a ring with
two places. -/

inductive L | x | a | b | c | m
  deriving DecidableEq

inductive LT | enter | s1 | s2 | leave
  deriving DecidableEq

instance : Fintype L := ⟨{L.x, L.a, L.b, L.c, L.m}, fun y => by cases y <;> simp⟩

instance : Fintype LT := ⟨{LT.enter, LT.s1, LT.s2, LT.leave}, fun y => by cases y <;> simp⟩

def loop : PetriNet L LT where
  pre | .enter => {L.x, L.m} | .s1 => {L.a} | .s2 => {L.b} | .leave => {L.c, L.m}
  post | .enter => {L.a, L.m} | .s1 => {L.b} | .s2 => {L.c} | .leave => {L.x, L.m}

abbrev M₀ : Marking L := {L.x, L.x, L.m}

/-- Directly: the ring with two tokens has ten reachable markings, and it is bounded and live. -/
example : (loop.reachSet M₀ 6).card = 10 := by decide +kernel

example : loop.Bounded M₀ := by decide +kernel

instance : Fact (loop.Bounded M₀) := ⟨by decide +kernel⟩

example : loop.Live M₀ := by decide +kernel

abbrev loop1 := loop.removePlace L.m
abbrev loop2 := loop1.fuseDelete LT.s1 ⟨L.a, dk⟩
abbrev loop3 := loop2.fuseDelete ⟨LT.s2, dk⟩ ⟨⟨L.b, dk⟩, dk⟩

/-- The initial marking of the reduced net: two tokens in `x`. -/
abbrev M₃ : Marking (PlaceOf loop3) :=
  {⟨⟨⟨L.x, dk⟩, dk⟩, dk⟩, ⟨⟨⟨L.x, dk⟩, dk⟩, dk⟩}

/-- The certificate: delete the self-loop place, then fuse the series `a`, `b`. -/
theorem loopCert : ReducesTo loop M₀ loop3 M₃ :=
  (ReducesTo.selfLoopPlace (N := loop) (M₀ := M₀) L.m dk dk).trans <|
  (ReducesTo.fuseSeries (N := loop1) (t₁ := LT.enter) (t₂ := LT.s1) (p := ⟨L.a, dk⟩)
    dk dk).trans <|
  (ReducesTo.fuseSeries (N := loop2) (t₁ := ⟨LT.enter, dk⟩) (t₂ := ⟨LT.s2, dk⟩)
    (p := ⟨⟨L.b, dk⟩, dk⟩) dk dk)

/-- The reduced ring has three reachable markings, instead of ten. -/
example : (loop3.reachSet M₃ 2).card = 3 := by decide +kernel

/-- The reduced net is bounded, hence so is the original net. -/
example : loop.Bounded M₀ := loopCert.bounded_iff.1 dk

/-- Liveness of the original net, decided on the reduced net. -/
def liveViaCert : Decidable (loop.Live M₀) :=
  decidableLiveOfReducesTo loopCert dk

example : loop.Live M₀ := of_decide_eq_true (inst := liveViaCert) dk

/-- Deadlock-freedom of the original net, decided on the reduced net. -/
def deadlockFreeViaCert : Decidable (∀ M, M₀ ⇝[loop] M → ¬ loop.Dead M) :=
  decidableDeadlockFreeOfReducesTo loopCert dk

example : ∀ M, M₀ ⇝[loop] M → ¬ loop.Dead M :=
  of_decide_eq_true (inst := deadlockFreeViaCert) dk

/-- `k`-boundedness is transferred from the original net to the reduced net, not conversely. -/
example (h : loop.KBounded M₀ 2) : loop3.KBounded M₃ 2 := loopCert.kBounded h

/-- Renaming only the transitions keeps the initial marking. -/
example (f : LT ≃ LT) : ReducesTo loop M₀ (loop.rename (Equiv.refl _) f) M₀ := by
  simpa using ReducesTo.reindex (N := loop) (M₀ := M₀) (Equiv.refl _) f

/-! ### The remaining rules

A ring `s0 → s1 → s2 → s0` with two parallel transitions `step` and `step'` that also read the two
parallel places `p` and `q`, and an isolated place `z`. -/

inductive K | s0 | s1 | s2 | p | q | z
  deriving DecidableEq

inductive KT | step | step' | mid | back
  deriving DecidableEq

instance : Fintype K := ⟨{K.s0, K.s1, K.s2, K.p, K.q, K.z}, fun y => by cases y <;> simp⟩

instance : Fintype KT := ⟨{KT.step, KT.step', KT.mid, KT.back}, fun y => by cases y <;> simp⟩

def misc : PetriNet K KT where
  pre | .step => {K.s0, K.p, K.q} | .step' => {K.s0, K.p, K.q} | .mid => {K.s1} | .back => {K.s2}
  post | .step => {K.s1, K.p, K.q} | .step' => {K.s1, K.p, K.q} | .mid => {K.s2} | .back => {K.s0}

abbrev N₀ : Marking K := {K.s0, K.p, K.p, K.q, K.z}

abbrev misc1 := misc.removeTransition KT.step'
abbrev misc2 := misc1.removePlace K.p
abbrev misc3 := misc2.removePlace ⟨K.z, dk⟩
abbrev misc4 := misc3.fuseDelete ⟨KT.mid, dk⟩ ⟨⟨K.s1, dk⟩, dk⟩

/-- The initial marking of the reduced net: the tokens of `s0` and `q`. -/
abbrev N₄ : Marking (PlaceOf misc4) :=
  {⟨⟨⟨K.s0, dk⟩, dk⟩, dk⟩, ⟨⟨⟨K.q, dk⟩, dk⟩, dk⟩}

/-- The certificate: a parallel transition, a parallel place, an isolated place, a series of
places. -/
theorem miscCert : ReducesTo misc N₀ misc4 N₄ :=
  (ReducesTo.removeTransition (N := misc) (M₀ := N₀) (t₁ := KT.step) (t₂ := KT.step')
    dk).trans <|
  (ReducesTo.parallelPlace (N := misc1) (p := K.p) (q := K.q) dk dk).trans <|
  (ReducesTo.isolatedPlace (N := misc2) (p := ⟨K.z, dk⟩) dk).trans <|
  (ReducesTo.fuseSeriesPlace (N := misc3) (t := ⟨KT.mid, dk⟩) (p₁ := ⟨⟨K.s1, dk⟩, dk⟩)
    (p₂ := ⟨⟨K.s2, dk⟩, dk⟩) dk dk)

example : (misc.reachSet N₀ 4).card = 3 := by decide +kernel

example : (misc4.reachSet N₄ 4).card = 2 := by decide +kernel

example : misc.Bounded N₀ := miscCert.bounded_iff.1 dk

def miscLive : Decidable (misc.Live N₀) := decidableLiveOfReducesTo miscCert dk

example : misc.Live N₀ := of_decide_eq_true (inst := miscLive) dk

def miscDeadlock : Decidable (∃ M, N₀ ⇝[misc] M ∧ misc.Dead M) :=
  decidableDeadlockOfReducesTo miscCert dk

/-- No dead marking is reachable. -/
example : ¬ ∃ M, N₀ ⇝[misc] M ∧ misc.Dead M :=
  of_decide_eq_false (inst := miscDeadlock) dk

end CslibTests.ReducedDecisions
