/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.CTL
public import Cslib.Logics.Temporal.LTL.Bisimulation
public import Cslib.Logics.Temporal.LTL.ModelChecking

/-! # Petri nets and LTL

LTL formulas over the atoms of `Cslib.Computability.PetriNets.CTL` are evaluated on the maximal
firing sequences of a net, which are infinite or end in a dead marking. For a bounded
net, LTL model checking is decidable, through the finite model bisimilar to the marking graph.

## Main statements

- `PetriNet.allPaths_iff_finiteModel`: LTL satisfaction in the marking graph is satisfaction in
  the finite model.
- `PetriNet.decidableAllPaths`, `PetriNet.decidableSomePath`: LTL model checking is
  decidable for bounded nets.
-/

@[expose] public section

namespace Cslib

open Cslib.Logic Cslib.Logic.LTL
open scoped Cslib.Logic.InferenceSystem

namespace PetriNet

open scoped PetriNet

variable {Place Transition : Type*} [DecidableEq Place] [Fintype Transition]
  {N : PetriNet Place Transition}

/-- Some maximal firing sequence satisfies the formula iff it does in the finite model. -/
theorem somePath_iff_finiteModel {M₀ : Marking Place} {n : ℕ} (hc : N.Closed M₀ n)
    (φ : Formula (Atom Place Transition)) :
    ⇓LTL[N.model,M₀ ⊨∃ φ] ↔
      ⇓LTL[N.finiteModel M₀ n,⟨M₀, mem_reachSet_self M₀ n⟩ ⊨∃ φ] :=
  (somePath_iff_of_isBisimulation (finiteLts_isBisimulation hc)
    (fun a M h p => by subst h; exact Iff.rfl) (s := ⟨M₀, mem_reachSet_self M₀ n⟩) rfl φ).symm

/-- All maximal firing sequences satisfy the formula iff they do in the finite model. -/
theorem allPaths_iff_finiteModel {M₀ : Marking Place} {n : ℕ} (hc : N.Closed M₀ n)
    (φ : Formula (Atom Place Transition)) :
    ⇓LTL[N.model,M₀ ⊨∀ φ] ↔
      ⇓LTL[N.finiteModel M₀ n,⟨M₀, mem_reachSet_self M₀ n⟩ ⊨∀ φ] :=
  (allPaths_iff_of_isBisimulation (finiteLts_isBisimulation hc)
    (fun a M h p => by subst h; exact Iff.rfl) (s := ⟨M₀, mem_reachSet_self M₀ n⟩) rfl φ).symm

variable [DecidableEq Transition] [Fintype Place]

/-- Whether some maximal firing sequence satisfies a formula is decidable for bounded
nets. -/
def decidableSomePath (M₀ : Marking Place) (hb : N.Bounded M₀)
    (φ : Formula (Atom Place Transition)) :
    Decidable (⇓LTL[N.model,M₀ ⊨∃ φ]) :=
  decidable_of_iff _ (somePath_iff_finiteModel (closed_closedLevel hb) φ).symm

instance (M₀ : Marking Place) [h : Fact (N.Bounded M₀)]
    (φ : Formula (Atom Place Transition)) :
    Decidable (⇓LTL[N.model,M₀ ⊨∃ φ]) :=
  decidableSomePath M₀ h.out φ

/-- LTL model checking at the initial marking is decidable for bounded nets. -/
def decidableAllPaths (M₀ : Marking Place) (hb : N.Bounded M₀)
    (φ : Formula (Atom Place Transition)) :
    Decidable (⇓LTL[N.model,M₀ ⊨∀ φ]) :=
  decidable_of_iff _ (allPaths_iff_finiteModel (closed_closedLevel hb) φ).symm

instance (M₀ : Marking Place) [h : Fact (N.Bounded M₀)]
    (φ : Formula (Atom Place Transition)) :
    Decidable (⇓LTL[N.model,M₀ ⊨∀ φ]) :=
  decidableAllPaths M₀ h.out φ

end PetriNet

end Cslib
