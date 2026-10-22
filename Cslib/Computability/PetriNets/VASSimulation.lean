/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Semantics
public import Cslib.Computability.VAS.Basic

/-! # Vector addition systems and Petri nets

Reachability in a vector addition system (VAS) and reachability in a Petri net are interreducible.

A VAS is a Petri net whose transitions are the actions `a`, with preset the negative part of `a` and
postset its positive part (`VAS.toPetriNet`, `VAS.reach_iff_reachable`).

Conversely, a Petri net is not literally a VAS, because a transition that consumes and produces
tokens in the same place (`pre = post ≠ 0`) is not enabled at a marking with fewer tokens, whereas
its displacement `0` is always enabled in a VAS. The standard *lock* construction repairs this: each
transition `t` is split into two actions, `t⁻` that consumes `pre t`, takes a lock and marks a
private place of `t`, and `t⁺` that gives the lock back, unmarks the private place and produces
`post t`. The lock is initially free and the private places are empty. The invariant
`lock + ∑ private = 1` makes the actions alternate, so that runs between configurations with a free
lock are exactly the firing sequences of the net.

## Main definitions

- `VAS.toPetriNet`: the Petri net of a VAS.
- `PetriNet.toVAS`: the VAS with a lock that simulates a Petri net.
- `PetriNet.embed`: the configuration of the simulating VAS for a marking.

## Main statements

- `VAS.reach_iff_reachable`: reachability of a VAS is reachability of its Petri net.
- `PetriNet.reachable_iff_vas_reach`: reachability of a net is reachability of the simulating VAS.
-/

@[expose] public section

namespace Cslib

open scoped PetriNet

namespace VAS

variable {ι : Type*} [Finite ι] (V : VAS ι)

/-- The Petri net of a VAS: one transition per action, which consumes the negative part and
produces the positive part of the action. -/
noncomputable def toPetriNet : PetriNet ι V.acts where
  pre a := Finsupp.equivFunOnFinite.symm fun i => (-a.1 i).toNat
  post a := Finsupp.equivFunOnFinite.symm fun i => (a.1 i).toNat

/-- A firing of the Petri net of a VAS is a step of the VAS. -/
theorem fires_toPetriNet_iff {c c' : VASConfig ι} {a : V.acts} :
    (V.toPetriNet).Fires (Finsupp.equivFunOnFinite.symm c) a (Finsupp.equivFunOnFinite.symm c') ↔
      V.Step c a.1 c' := by
  simp only [PetriNet.Fires, VAS.Step, toPetriNet, a.2, true_and, VASConfig.toInt, funext_iff,
    Pi.add_apply, DFunLike.ext_iff, Finsupp.coe_add,
    Finsupp.equivFunOnFinite_symm_apply_apply]
  refine ⟨fun ⟨R, h1, h2⟩ x => ?_,
    fun h => ⟨Finsupp.equivFunOnFinite.symm fun i => c i - (-a.1 i).toNat,
      fun x => ?_, fun x => ?_⟩⟩
  · have := h1 x
    have := h2 x
    omega
  all_goals have := h x; simp only [Finsupp.equivFunOnFinite_symm_apply_apply]; omega

/-- Reachability in a VAS is reachability in its Petri net. -/
theorem reach_iff_reachable {c c' : VASConfig ι} :
    V.Reach c c' ↔
      (V.toPetriNet).Reachable (Finsupp.equivFunOnFinite.symm c) (Finsupp.equivFunOnFinite.symm c')
      :=
  LTS.CanReach.iff_of_equiv Finsupp.equivFunOnFinite.symm fun _ _ =>
    ⟨fun ⟨a, ha⟩ => ⟨⟨a, ha.1⟩, V.fires_toPetriNet_iff.2 ha⟩,
      fun ⟨a, ha⟩ => ⟨a, V.fires_toPetriNet_iff.1 ha⟩⟩

end VAS

namespace PetriNet

/-- The coordinates of the simulating VAS: the places, the lock (`none`) and one private place
`some t` for each transition `t`. -/
abbrev LockDim (Place Transition : Type*) := Place ⊕ Option Transition

variable [Finite Place] [Fintype Transition] [DecidableEq Transition]
  (N : PetriNet Place Transition)

/-- A configuration of the simulating VAS with `K` tokens in the places, `l` tokens in the lock
and `q t` tokens in the private place of `t`. -/
def lockCfg (K : Place → ℕ) (l : ℕ) (q : Transition → ℕ) : VASConfig (LockDim Place Transition) :=
  Sum.elim K fun o => o.elim l q

/-- The indicator of a transition, the contents of the private places while it fires. -/
def ind (t : Transition) : Transition → ℕ := fun s => if s = t then 1 else 0

omit [Fintype Transition] in
@[simp] theorem ind_self (t : Transition) : ind t t = 1 := by simp [ind]

omit [Fintype Transition] in
theorem ind_of_ne {s t : Transition} (h : s ≠ t) : ind t s = 0 := by simp [ind, h]

/-- The action `t⁻`: consume `pre t`, take the lock and mark the private place of `t`. -/
noncomputable def minusAct (t : Transition) : LockDim Place Transition → ℤ :=
  Sum.elim (fun p => -(N.pre t p : ℤ)) fun o => o.elim (-1) fun s => (ind t s : ℤ)

/-- The action `t⁺`: produce `post t`, release the lock and unmark the private place of `t`. -/
noncomputable def plusAct (t : Transition) : LockDim Place Transition → ℤ :=
  Sum.elim (fun p => (N.post t p : ℤ)) fun o => o.elim 1 fun s => -(ind t s : ℤ)

open Classical in
/-- The VAS with a lock that simulates the Petri net `N`. -/
noncomputable def toVAS : VAS (LockDim Place Transition) where
  acts := Finset.univ.image (minusAct N) ∪ Finset.univ.image (plusAct N)

/-- The configuration of the simulating VAS for a marking: lock free, private places empty. -/
def embed (M : Marking Place) : VASConfig (LockDim Place Transition) := lockCfg M 1 0

omit [Finite Place] in
theorem mem_acts_toVAS {a : LockDim Place Transition → ℤ} :
    a ∈ (toVAS N).acts ↔ ∃ t, a = minusAct N t ∨ a = plusAct N t := by
  simp only [toVAS, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, exists_or,
    eq_comm]

/-- From a configuration with a free lock, the simulating VAS can only start the firing of a
transition `t` that is enabled, moving to the configuration where `t` is being fired. -/
theorem move_embed_iff {M : Marking Place} {c' : VASConfig (LockDim Place Transition)} :
    (toVAS N).Move (embed M) c' ↔
      ∃ (t : Transition) (R : Marking Place), M = N.pre t + R ∧ c' = lockCfg R 0 (ind t) := by
  constructor
  · rintro ⟨a, ha, hx⟩
    obtain ⟨t, rfl | rfl⟩ := (mem_acts_toVAS N).1 ha
    · have hp (p) : (c' (.inl p) : ℤ) = M p + -(N.pre t p : ℤ) := congrFun hx (.inl p)
      have hl : (c' (.inr none) : ℤ) = 1 + -1 := congrFun hx (.inr none)
      have hs (s) : (c' (.inr (some s)) : ℤ) = 0 + (ind t s : ℤ) := congrFun hx (.inr (some s))
      refine ⟨t, Finsupp.equivFunOnFinite.symm fun p => c' (.inl p), ?_, funext fun x => ?_⟩
      · ext p
        have := hp p
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.equivFunOnFinite_symm_apply_apply]
        omega
      · rcases x with p | _ | s
        · rfl
        · change c' (.inr none) = 0
          omega
        · change c' (.inr (some s)) = ind t s
          have := hs s
          omega
    · have : (c' (.inr (some t)) : ℤ) = 0 + -(ind t t : ℤ) := congrFun hx (.inr (some t))
      have := ind_self t
      omega
  · rintro ⟨t, R, rfl, rfl⟩
    refine ⟨minusAct N t, (mem_acts_toVAS N).2 ⟨t, .inl rfl⟩, funext fun x => ?_⟩
    rcases x with p | _ | s
    · change (R p : ℤ) = ((N.pre t p + R p : ℕ) : ℤ) + -(N.pre t p : ℤ)
      omega
    · change ((0 : ℕ) : ℤ) = 1 + -1
      omega
    · change (ind t s : ℤ) = ((0 : ℕ) : ℤ) + (ind t s : ℤ)
      omega

omit [Finite Place] in
/-- While the transition `t` is being fired, the only move of the simulating VAS finishes the
firing: it produces `post t` and releases the lock. -/
theorem move_lockCfg_iff {R : Marking Place} {t : Transition}
    {c' : VASConfig (LockDim Place Transition)} :
    (toVAS N).Move (lockCfg R 0 (ind t)) c' ↔ c' = embed (R + N.post t) := by
  constructor
  · rintro ⟨a, ha, hx⟩
    obtain ⟨s, rfl | rfl⟩ := (mem_acts_toVAS N).1 ha
    · have : (c' (.inr none) : ℤ) = 0 + -1 := congrFun hx (.inr none)
      omega
    · have hs (u) : (c' (.inr (some u)) : ℤ) = (ind t u : ℤ) + -(ind s u : ℤ) :=
        congrFun hx (.inr (some u))
      obtain rfl : s = t := by
        by_contra hne
        have := hs s
        have := ind_of_ne hne
        have := ind_self s
        omega
      funext x
      rcases x with p | _ | u
      · have : (c' (.inl p) : ℤ) = R p + (N.post s p : ℕ) := congrFun hx (.inl p)
        change c' (.inl p) = R p + N.post s p
        omega
      · have : (c' (.inr none) : ℤ) = 0 + 1 := congrFun hx (.inr none)
        change c' (.inr none) = 1
        omega
      · have := hs u
        change c' (.inr (some u)) = 0
        omega
  · rintro rfl
    refine ⟨plusAct N t, (mem_acts_toVAS N).2 ⟨t, .inr rfl⟩, funext fun x => ?_⟩
    rcases x with p | _ | s
    · change ((R p + N.post t p : ℕ) : ℤ) = R p + (N.post t p : ℤ)
      omega
    · change ((1 : ℕ) : ℤ) = 0 + 1
      omega
    · change ((0 : ℕ) : ℤ) = (ind t s : ℤ) + -(ind t s : ℤ)
      omega

/-- The simulation is complete: a firing of the net is two moves of the VAS. -/
theorem reach_embed_of_fires {M M' : Marking Place} {t : Transition} (h : M [t⟩[N] M') :
    (toVAS N).Reach (embed M) (embed M') := by
  obtain ⟨R, rfl, rfl⟩ := h
  exact (VAS.Reach.single ((move_embed_iff N).2 ⟨t, R, rfl, rfl⟩)).tail
    ((move_lockCfg_iff N).2 rfl)

/-- **Simulation lemma**: a marking is reachable in the net iff the embedded marking is reachable in
the simulating VAS. -/
theorem reachable_iff_vas_reach {M M' : Marking Place} :
    N.Reachable M M' ↔ (toVAS N).Reach (embed M) (embed M') := by
  constructor
  · intro h
    induction h using LTS.CanReach.induction_on with
    | refl => exact .refl
    | tail _ ht ih =>
      obtain ⟨t, ht⟩ := ht
      exact ih.trans (reach_embed_of_fires N ht)
  · intro h
    -- the configurations reachable from `embed M`: free lock, or firing some transition
    let Q : VASConfig (LockDim Place Transition) → Prop := fun c =>
      (∃ K : Marking Place, c = embed K ∧ N.Reachable M K) ∨
        ∃ (t : Transition) (R : Marking Place),
          c = lockCfg R 0 (ind t) ∧ N.Reachable M (N.pre t + R)
    have hQ : Q (embed M') := by
      refine LTS.CanReach.induction_on (P := fun c _ => Q c) h (.inl ⟨M, rfl, .refl _ _⟩) ?_
      intro b c _ hm ih
      rcases ih with ⟨K, rfl, hK⟩ | ⟨t, R, rfl, hK⟩
      · obtain ⟨t, R, hKR, rfl⟩ := (move_embed_iff N).1 hm
        exact .inr ⟨t, R, rfl, hKR ▸ hK⟩
      · rw [(move_lockCfg_iff N).1 hm]
        exact .inl ⟨R + N.post t, rfl, hK.trans (Fires.reachable ⟨R, rfl, rfl⟩)⟩
    rcases hQ with ⟨K, hK, hr⟩ | ⟨t, R, hK, -⟩
    · have : K = M' := by
        ext p
        exact congrFun hK (.inl p) |>.symm
      exact this ▸ hr
    · have := congrFun hK (.inr none)
      simp [embed, lockCfg] at this

end PetriNet

end Cslib
