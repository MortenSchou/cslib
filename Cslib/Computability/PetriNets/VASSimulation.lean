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

The configurations of a VAS with coordinates `ι` are vectors `ι → ℕ`, and the markings of a net
with places `ι` are multisets of `ι`. For finite `ι` they correspond: a marking `M` is the vector
of its token counts `M.count`, and a vector `c` is the marking `Marking.ofFun c` with `c p` tokens
in each place `p`.

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

- `PetriNet.Marking.ofFun`: the marking of a vector of token counts.
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

namespace PetriNet.Marking

variable {Place : Type*} [Fintype Place]

/-- The marking with `c p` tokens in each place `p`. -/
def ofFun (c : Place → ℕ) : Marking Place := ∑ p, Multiset.replicate (c p) p

variable [DecidableEq Place]

@[simp] theorem count_ofFun (c : Place → ℕ) (p : Place) : (ofFun c).count p = c p := by
  simp [ofFun, Multiset.count_sum', Multiset.count_replicate]

@[simp] theorem ofFun_count (M : Marking Place) : ofFun (M.count ·) = M :=
  Multiset.ext.2 fun p => count_ofFun _ p

/-- Markings of finitely many places are the vectors of their token counts. -/
def equivFun : (Place → ℕ) ≃ Marking Place where
  toFun := ofFun
  invFun M p := M.count p
  left_inv c := funext (count_ofFun c)
  right_inv := ofFun_count

end PetriNet.Marking

namespace VAS

open PetriNet

variable {ι : Type*} [Fintype ι] (V : VAS ι)

/-- The Petri net of a VAS: one transition per action, which consumes the negative part and
produces the positive part of the action. -/
def toPetriNet : PetriNet ι V.acts where
  pre a := Marking.ofFun fun i => (-a.1 i).toNat
  post a := Marking.ofFun fun i => (a.1 i).toNat

/-- A firing of the Petri net of a VAS is a step of the VAS. -/
theorem fires_toPetriNet_iff {c c' : VASConfig ι} {a : V.acts} :
    (Marking.ofFun c) [a⟩[V.toPetriNet] (Marking.ofFun c') ↔ V.Step c a.1 c' := by
  classical
  simp only [fires_iff, Enabled, fire, Multiset.le_iff_count, Multiset.ext (s := Marking.ofFun c'),
    Multiset.count_add, Multiset.count_sub, toPetriNet, Marking.count_ofFun, VAS.Step, a.2,
    true_and, VASConfig.toInt, funext_iff, Pi.add_apply, ← forall_and]
  exact forall_congr' fun i => by omega

/-- Reachability in a VAS is reachability in its Petri net. -/
theorem reach_iff_reachable {c c' : VASConfig ι} :
    V.Reach c c' ↔ V.toPetriNet.Reachable (Marking.ofFun c) (Marking.ofFun c') := by
  classical
  exact LTS.CanReach.iff_of_equiv Marking.equivFun fun _ _ =>
      ⟨fun ⟨a, ha⟩ => ⟨⟨a, ha.1⟩, V.fires_toPetriNet_iff.2 ha⟩,
        fun ⟨a, ha⟩ => ⟨a, V.fires_toPetriNet_iff.1 ha⟩⟩

end VAS

namespace PetriNet

/-- The coordinates of the simulating VAS: the places, the lock (`none`) and one private place
`some t` for each transition `t`. -/
abbrev LockDim (Place Transition : Type*) := Place ⊕ Option Transition

variable {Place Transition : Type*} [DecidableEq Place] [DecidableEq Transition]
  (N : PetriNet Place Transition)

/-- A configuration of the simulating VAS with the tokens of `K` in the places, `l` tokens in the
lock and `q t` tokens in the private place of `t`. -/
def lockCfg (K : Marking Place) (l : ℕ) (q : Transition → ℕ) :
    VASConfig (LockDim Place Transition) :=
  Sum.elim K.count fun o => o.elim l q

/-- The indicator of a transition, the contents of the private places while it fires. -/
def ind (t : Transition) : Transition → ℕ := fun s => if s = t then 1 else 0

@[simp] theorem ind_self (t : Transition) : ind t t = 1 := by simp [ind]

theorem ind_of_ne {s t : Transition} (h : s ≠ t) : ind t s = 0 := by simp [ind, h]

/-- The action `t⁻`: consume `pre t`, take the lock and mark the private place of `t`. -/
def minusAct (t : Transition) : LockDim Place Transition → ℤ :=
  Sum.elim (fun p => -((•[N] t).count p : ℤ)) fun o => o.elim (-1) fun s => (ind t s : ℤ)

/-- The action `t⁺`: produce `post t`, release the lock and unmark the private place of `t`. -/
def plusAct (t : Transition) : LockDim Place Transition → ℤ :=
  Sum.elim (fun p => ((t •[N]).count p : ℤ)) fun o => o.elim 1 fun s => -(ind t s : ℤ)

/-- The configuration of the simulating VAS for a marking: lock free, private places empty. -/
def embed (M : Marking Place) : VASConfig (LockDim Place Transition) := lockCfg M 1 0

variable [Fintype Place] [Fintype Transition]

/-- The VAS with a lock that simulates the Petri net `N`. -/
def toVAS : VAS (LockDim Place Transition) where
  acts := Finset.univ.image (minusAct N) ∪ Finset.univ.image (plusAct N)

theorem mem_acts_toVAS {a : LockDim Place Transition → ℤ} :
    a ∈ (toVAS N).acts ↔ ∃ t, a = minusAct N t ∨ a = plusAct N t := by
  simp only [toVAS, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, exists_or,
    eq_comm]

/-- From a configuration with a free lock, the simulating VAS can only start the firing of a
transition `t` that is enabled, moving to the configuration where `t` is being fired. -/
theorem move_embed_iff {M : Marking Place} {c' : VASConfig (LockDim Place Transition)} :
    (toVAS N).Move (embed M) c' ↔
      ∃ (t : Transition) (R : Marking Place), M = •[N] t + R ∧ c' = lockCfg R 0 (ind t) := by
  constructor
  · rintro ⟨a, ha, hx⟩
    obtain ⟨t, rfl | rfl⟩ := (mem_acts_toVAS N).1 ha
    · have hp (p) : (c' (.inl p) : ℤ) = M.count p + -((•[N] t).count p : ℤ) :=
        congrFun hx (.inl p)
      have hl : (c' (.inr none) : ℤ) = 1 + -1 := congrFun hx (.inr none)
      have hs (s) : (c' (.inr (some s)) : ℤ) = 0 + (ind t s : ℤ) := congrFun hx (.inr (some s))
      have hle : •[N] t ≤ M := Multiset.le_iff_count.2 fun p => by have := hp p; omega
      refine ⟨t, M - •[N] t, (add_tsub_cancel_of_le hle).symm, funext fun x => ?_⟩
      rcases x with p | _ | s
      · have := hp p
        simp only [lockCfg, Sum.elim_inl, Multiset.count_sub]
        omega
      · simp only [lockCfg, Sum.elim_inr, Option.elim_none]
        omega
      · have := hs s
        simp only [lockCfg, Sum.elim_inr, Option.elim_some]
        omega
    · have : (c' (.inr (some t)) : ℤ) = 0 + -(ind t t : ℤ) := congrFun hx (.inr (some t))
      have := ind_self t
      omega
  · rintro ⟨t, R, rfl, rfl⟩
    refine ⟨minusAct N t, (mem_acts_toVAS N).2 ⟨t, .inl rfl⟩, funext fun x => ?_⟩
    rcases x with p | _ | s <;>
      simp [VASConfig.toInt, embed, lockCfg, minusAct, Multiset.count_add]

/-- While the transition `t` is being fired, the only move of the simulating VAS finishes the
firing: it produces `post t` and releases the lock. -/
theorem move_lockCfg_iff {R : Marking Place} {t : Transition}
    {c' : VASConfig (LockDim Place Transition)} :
    (toVAS N).Move (lockCfg R 0 (ind t)) c' ↔ c' = embed (R + t •[N]) := by
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
      · have : (c' (.inl p) : ℤ) = R.count p + ((s •[N]).count p : ℤ) := congrFun hx (.inl p)
        simp only [embed, lockCfg, Sum.elim_inl, Multiset.count_add]
        omega
      · have : (c' (.inr none) : ℤ) = 0 + 1 := congrFun hx (.inr none)
        simp only [embed, lockCfg, Sum.elim_inr, Option.elim_none]
        omega
      · have := hs u
        simp only [embed, lockCfg, Sum.elim_inr, Option.elim_some, Pi.zero_apply]
        omega
  · rintro rfl
    refine ⟨plusAct N t, (mem_acts_toVAS N).2 ⟨t, .inr rfl⟩, funext fun x => ?_⟩
    rcases x with p | _ | s <;>
      simp [VASConfig.toInt, embed, lockCfg, plusAct, Multiset.count_add]

/-- The simulation is complete: a firing of the net is two moves of the VAS. -/
theorem reach_embed_of_fires {M M' : Marking Place} {t : Transition} (h : M [t⟩[N] M') :
    (toVAS N).Reach (embed M) (embed M') := by
  obtain ⟨R, rfl, rfl⟩ := h
  exact (VAS.Reach.single ((move_embed_iff N).2 ⟨t, R, rfl, rfl⟩)).tail
    ((move_lockCfg_iff N).2 rfl)

/-- **Simulation lemma**: a marking is reachable in the net iff the embedded marking is reachable in
the simulating VAS. -/
theorem reachable_iff_vas_reach {M M' : Marking Place} :
    M ⇝[N] M' ↔ (toVAS N).Reach (embed M) (embed M') := by
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
      (∃ K : Marking Place, c = embed K ∧ M ⇝[N] K) ∨
        ∃ (t : Transition) (R : Marking Place), c = lockCfg R 0 (ind t) ∧ M ⇝[N] (•[N] t + R)
    have hQ : Q (embed M') := by
      refine LTS.CanReach.induction_on (P := fun c _ => Q c) h (.inl ⟨M, rfl, .refl _ _⟩) ?_
      intro b c _ hm ih
      rcases ih with ⟨K, rfl, hK⟩ | ⟨t, R, rfl, hK⟩
      · obtain ⟨t, R, hKR, rfl⟩ := (move_embed_iff N).1 hm
        exact .inr ⟨t, R, rfl, hKR ▸ hK⟩
      · rw [(move_lockCfg_iff N).1 hm]
        exact .inl ⟨R + t •[N], rfl, hK.trans (Fires.reachable ⟨R, rfl, rfl⟩)⟩
    rcases hQ with ⟨K, hK, hr⟩ | ⟨t, R, hK, -⟩
    · obtain rfl : K = M' := Multiset.ext.2 fun p => (congrFun hK (.inl p)).symm
      exact hr
    · have := congrFun hK (.inr none)
      simp [embed, lockCfg] at this

end PetriNet

end Cslib
