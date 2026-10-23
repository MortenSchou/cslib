/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.ExecutableForward
public import Cslib.Computability.PetriNets.ExecutableSoundnessNotions
public import Cslib.Logics.Temporal.CTL.Bisimulation
public import Cslib.Logics.Temporal.CTL.ModelChecking
public import Cslib.Logics.Temporal.CTL.Reachability

/-! # Petri nets and CTL

The marking graph of a Petri net is a model of CTL, with atoms saying that the marking is a given
marking, or that a transition is enabled. Properties of nets become CTL formulas: reachability is
`EF`, deadlocks are `deadlock`, and easy and `k`-soundness (hence weak soundness) and liveness are
`EF` and `AG EF` formulas.

For a bounded executable net, the reachable markings form a finite model, bisimilar to the marking
graph, in which CTL satisfaction is decided by the labelling algorithm.

## Main definitions

- `PetriNet.Atom`: the atomic propositions about markings.
- `PetriNet.model`: the marking graph as a CTL model.
- `ExecPetriNet.finiteModel`: the finite model of the markings reachable within `n` steps.

## Main statements

- `PetriNet.easySound_iff`, `PetriNet.kSound_iff`, `PetriNet.liveAt_iff`,
  `PetriNet.deadlockFree_iff`: properties of nets as CTL formulas.
- `ExecPetriNet.satisfies_iff_finiteModel`: satisfaction in the marking graph is satisfaction in
  the finite model, when the latter is closed under transitions.
- `ExecPetriNet.decidableSatisfies`: CTL satisfaction is decidable for bounded executable nets.
-/

@[expose] public section

namespace Cslib

open Cslib.Logic Cslib.Logic.CTL
open scoped Cslib.Logic.InferenceSystem Cslib.Logic.CTL.Formula

namespace PetriNet

variable {Place : Type*} {Transition : Type*}

/-- The atomic propositions about the marking of a net. -/
inductive Atom (Place : Type*) (Transition : Type*) where
  /-- The marking is exactly `M`. -/
  | marking (M : Marking Place)
  /-- The transition `t` is enabled. -/
  | enabled (t : Transition)
deriving DecidableEq

/-- The marking graph of a net as a CTL model. -/
def model (N : PetriNet Place Transition) : CTL.Model (Marking Place) (Atom Place Transition) :=
  ⟨N.lts, fun M a => match a with
    | .marking M' => M = M'
    | .enabled t => M [t⟩[N]⟩

/-- The formula saying that the marking is exactly `M`. -/
abbrev marked (M : Marking Place) : Formula (Atom Place Transition) := .atom (.marking M)

variable {N : PetriNet Place Transition}

theorem satisfies_marked {M M' : Marking Place} :
    ⇓CTL[N.model,M ⊨ marked M'] ↔ M = M' := Iff.rfl

theorem satisfies_enabled {M : Marking Place} {t : Transition} :
    ⇓CTL[N.model,M ⊨ .atom (.enabled t)] ↔ M [t⟩[N] := Iff.rfl

/-- The deadlocks of the model are the dead markings. -/
theorem satisfies_deadlock {M : Marking Place} :
    ⇓CTL[N.model,M ⊨ Formula.deadlock] ↔ N.Dead M :=
  Satisfies.deadlock_ofLTS_iff

/-- `EF` of a marking is reachability. -/
theorem satisfies_ef_marked {M M' : Marking Place} :
    ⇓CTL[N.model,M ⊨ EF (marked M')] ↔ M ⇝[N] M' := by
  rw [model, Satisfies.ef_ofLTS_iff]
  simp only [Satisfies.atom_iff]
  constructor
  · rintro ⟨t, hr, rfl⟩
    exact hr
  · intro h
    exact ⟨M', h, rfl⟩

/-- Easy soundness: the final marking can be reached. -/
theorem easySound_iff {i o : Place} :
    N.EasySound i o ↔ ⇓CTL[N.model,token i ⊨ EF (marked (token o))] :=
  satisfies_ef_marked.symm

/-- `k`-soundness: from every marking reachable from `k` tokens in the source, the final marking
with `k` tokens in the sink can be reached. -/
theorem kSound_iff {i o : Place} {k : ℕ} :
    N.KSound i o k ↔
      ⇓CTL[N.model,k • token i ⊨ AG (EF (marked (k • token o)))] := by
  rw [model, Satisfies.ag_ofLTS_iff]
  refine forall_congr' fun M => imp_congr_right fun _ => ?_
  exact satisfies_ef_marked.symm

/-- A transition is live iff `AG EF` of its enabledness. -/
theorem liveAt_iff {M₀ : Marking Place} {t : Transition} :
    N.LiveAt M₀ t ↔ ⇓CTL[N.model,M₀ ⊨ AG (EF (.atom (.enabled t)))] := by
  rw [model, Satisfies.ag_ofLTS_iff]
  refine forall_congr' fun M => imp_congr_right fun _ => ?_
  rw [Satisfies.ef_ofLTS_iff]
  rfl

/-- No reachable marking is dead iff `AG ¬deadlock`. -/
theorem deadlockFree_iff {M₀ : Marking Place} :
    (∀ M, M₀ ⇝[N] M → ¬ N.Dead M) ↔
      ⇓CTL[N.model,M₀ ⊨ AG (¬Formula.deadlock)] := by
  rw [model, Satisfies.ag_ofLTS_iff]
  refine forall_congr' fun M => imp_congr_right fun _ => ?_
  rw [Satisfies.not_iff, Satisfies.deadlock_ofLTS_iff]
  rfl

end PetriNet

namespace ExecPetriNet

open PetriNet
open scoped PetriNet

variable {Place Transition : Type*} [DecidableEq Place] [Fintype Transition]
  (N : ExecPetriNet Place Transition)

/-- The marking graph of an executable net as a CTL model. -/
abbrev model : CTL.Model (Marking Place) (Atom Place Transition) := N.toPetriNet.model

/-- The finite LTS of the markings reachable within `n` steps. -/
def finiteLts (M₀ : Multiset Place) (n : ℕ) : LTS (N.reachSet M₀ n) Transition :=
  ⟨fun a t b => N.fire a.1 t = some b.1⟩

/-- The atoms that hold at the markings reachable within `n` steps. -/
def finiteVal (M₀ : Multiset Place) (n : ℕ) :
    N.reachSet M₀ n → Atom Place Transition → Prop
  | a, .marking M' => Multiset.toFinsupp a.1 = M'
  | a, .enabled t => N.pre t ≤ a.1

/-- The finite model of the markings reachable within `n` steps. -/
def finiteModel (M₀ : Multiset Place) (n : ℕ) :
    CTL.Model (N.reachSet M₀ n) (Atom Place Transition) :=
  ⟨N.finiteLts M₀ n, N.finiteVal M₀ n⟩

variable {N}

instance (M₀ : Multiset Place) (n : ℕ) : DecidableRel (N.finiteModel M₀ n).tr := fun a b =>
  inferInstanceAs (Decidable (∃ t, N.fire a.1 t = some b.1))

instance (M₀ : Multiset Place) (n : ℕ) (a : N.reachSet M₀ n) (p : Atom Place Transition) :
    Decidable ((N.finiteModel M₀ n).v a p) :=
  match p with
  | .marking M' => inferInstanceAs (Decidable (Multiset.toFinsupp a.1 = M'))
  | .enabled t => inferInstanceAs (Decidable (N.pre t ≤ a.1))

theorem mem_reachSet_self (M₀ : Multiset Place) (n : ℕ) : M₀ ∈ N.reachSet M₀ n :=
  (mem_reachSet_iff N).2 ⟨[], Nat.zero_le _, rfl⟩

/-- The finite LTS of a closed level is bisimilar to the marking graph. -/
theorem finiteLts_isBisimulation {M₀ : Multiset Place} {n : ℕ} (hc : N.Closed M₀ n) :
    LTS.IsBisimulation (N.finiteLts M₀ n) N.lts
      (fun a M => Multiset.toFinsupp a.1 = M) := by
  rintro a _ rfl t
  refine ⟨fun b hb => ⟨Multiset.toFinsupp b.1, fires_iff.2 hb, rfl⟩, fun M' hM' => ?_⟩
  obtain ⟨m', rfl, hf⟩ := (fires_toFinsupp_iff N).1 hM'
  have hmem : m' ∈ N.reachSet M₀ n := hc (by
    simp only [stepSet, Finset.mem_biUnion, Finset.mem_univ, true_and, Option.mem_toFinset]
    exact ⟨a.1, a.2, t, hf⟩)
  exact ⟨⟨m', hmem⟩, hf, rfl⟩

/-- The atoms of the finite LTS agree with those of the marking graph. -/
theorem finiteVal_iff (M₀ : Multiset Place) (n : ℕ) (a : N.reachSet M₀ n) (M : Marking Place)
    (h : Multiset.toFinsupp a.1 = M) (p : Atom Place Transition) :
    N.finiteVal M₀ n a p ↔ N.model.v M p := by
  subst h
  cases p with
  | marking M' => exact Iff.rfl
  | enabled t => exact enabled_toPetriNet_iff.symm

/-- Satisfaction in the marking graph is satisfaction in the finite model, when the model is closed
under transitions. -/
theorem satisfies_iff_finiteModel {M₀ : Multiset Place} {n : ℕ} (hc : N.Closed M₀ n)
    (φ : Formula (Atom Place Transition)) :
    ⇓CTL[N.model,M₀ ⊨ φ] ↔
      ⇓CTL[N.finiteModel M₀ n,⟨M₀, mem_reachSet_self M₀ n⟩ ⊨ φ] :=
  (Satisfies.of_isBisimulation (finiteLts_isBisimulation hc)
    (fun a M h p => finiteVal_iff M₀ n a M h p) φ (s := ⟨M₀, mem_reachSet_self M₀ n⟩) rfl).symm

variable [Fintype Place]

/-- CTL satisfaction at the initial marking is decidable for bounded executable nets: look it up in
the finite model of a closed level. -/
def decidableSatisfies (M₀ : Multiset Place) (hb : N.Bounded M₀)
    (φ : Formula (Atom Place Transition)) :
    Decidable (⇓CTL[N.model,M₀ ⊨ φ]) :=
  decidable_of_iff _ (satisfies_iff_finiteModel (closed_closedLevel hb) φ).symm

instance (M₀ : Multiset Place) [h : Fact (N.Bounded M₀)]
    (φ : Formula (Atom Place Transition)) :
    Decidable (⇓CTL[N.model,M₀ ⊨ φ]) :=
  decidableSatisfies M₀ h.out φ

end ExecPetriNet

end Cslib
