/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Automaton
public import Cslib.Computability.PetriNets.Executable
public import Cslib.Computability.PetriNets.FreeChoice
public import Cslib.Computability.PetriNets.PlaceInvariants
public import Cslib.Computability.PetriNets.SoundnessNotions

/-! # Dot notation for executable nets

Executable nets are translated to weighted nets by `ExecPetriNet.toPetriNet`, and the properties of
a net are defined for weighted nets. Lean does not coerce the receiver of a dot notation, nor the
net argument of a predicate whose types are determined by that net. This file therefore forwards
the properties of weighted nets to executable nets as reducible abbreviations, so that
`N.Bounded M₀` can be written for `N.toPetriNet.Bounded M₀`.

After `open scoped PetriNet`, markings can also be given as multisets.
-/

@[expose] public section

namespace Cslib.ExecPetriNet

open PetriNet

variable {Place Transition : Type*} [DecidableEq Place] (N : ExecPetriNet Place Transition)

/-- The marking graph of an executable net. -/
abbrev lts : LTS (Marking Place) Transition := N.toPetriNet.lts

/-- `N.Enabled M t` says that `t` is enabled at `M`. -/
abbrev Enabled (M : Marking Place) (t : Transition) : Prop := N.toPetriNet.Enabled M t

/-- `N.Fires M t M'` says that firing `t` at `M` leads to `M'`. -/
abbrev Fires (M : Marking Place) (t : Transition) (M' : Marking Place) : Prop :=
  N.toPetriNet.Fires M t M'

/-- `N.Reachable M M'` says that `M'` is reachable from `M`. -/
abbrev Reachable (M M' : Marking Place) : Prop := N.toPetriNet.Reachable M M'

/-- `N.KBounded M₀ k` says that the net is `k`-bounded at `M₀`. -/
abbrev KBounded (M₀ : Marking Place) (k : ℕ) : Prop := N.toPetriNet.KBounded M₀ k

/-- `N.Bounded M₀` says that the net is bounded at `M₀`. -/
abbrev Bounded (M₀ : Marking Place) : Prop := N.toPetriNet.Bounded M₀

/-- `N.Safe M₀` says that the net is safe at `M₀`. -/
abbrev Safe (M₀ : Marking Place) : Prop := N.toPetriNet.Safe M₀

/-- `N.Conservative` says that every transition conserves the number of tokens. -/
abbrev Conservative : Prop := N.toPetriNet.Conservative

/-- `N.Dead M` says that no transition is enabled at `M`. -/
abbrev Dead (M : Marking Place) : Prop := N.toPetriNet.Dead M

/-- `N.LiveAt M₀ t` says that `t` is live at `M₀`. -/
abbrev LiveAt (M₀ : Marking Place) (t : Transition) : Prop := N.toPetriNet.LiveAt M₀ t

/-- `N.Live M₀` says that the net is live at `M₀`. -/
abbrev Live (M₀ : Marking Place) : Prop := N.toPetriNet.Live M₀

/-- `N.Coverable M₀ M` says that `M` is coverable from `M₀`. -/
abbrev Coverable (M₀ M : Marking Place) : Prop := N.toPetriNet.Coverable M₀ M

/-- `N.IsSiphon S` says that `S` is a siphon. -/
abbrev IsSiphon (S : Set Place) : Prop := N.toPetriNet.IsSiphon S

/-- `N.IsTrap T` says that `T` is a trap. -/
abbrev IsTrap (T : Set Place) : Prop := N.toPetriNet.IsTrap T

/-- `N.SiphonTrap M₀` is the siphon-trap property at `M₀`. -/
abbrev SiphonTrap (M₀ : Marking Place) : Prop := N.toPetriNet.SiphonTrap M₀

/-- `N.Ordinary` says that all arc weights are at most `1`. -/
abbrev Ordinary : Prop := N.toPetriNet.Ordinary

/-- `N.IsFreeChoice` says that the net is free-choice. -/
abbrev IsFreeChoice : Prop := N.toPetriNet.IsFreeChoice

/-- `N.IsInvariant w` says that `w` is a place invariant. -/
abbrev IsInvariant (w : Place → ℕ) : Prop := N.toPetriNet.IsInvariant w

/-- `N.Sound i o` is classical soundness for the source `i` and sink `o`. -/
abbrev Sound (i o : Place) : Prop := N.toPetriNet.Sound i o

/-- `N.KSound i o k` is `k`-soundness. -/
abbrev KSound (i o : Place) (k : ℕ) : Prop := N.toPetriNet.KSound i o k

/-- `N.UpToKSound i o k` is up-to-`k` soundness. -/
abbrev UpToKSound (i o : Place) (k : ℕ) : Prop := N.toPetriNet.UpToKSound i o k

/-- `N.GeneralizedSound i o` is generalized soundness. -/
abbrev GeneralizedSound (i o : Place) : Prop := N.toPetriNet.GeneralizedSound i o

/-- `N.WeakSound i o` is weak soundness. -/
abbrev WeakSound (i o : Place) : Prop := N.toPetriNet.WeakSound i o

/-- `N.RelaxedSound i o` is relaxed soundness. -/
abbrev RelaxedSound (i o : Place) : Prop := N.toPetriNet.RelaxedSound i o

/-- `N.LazySound i o` is lazy soundness. -/
abbrev LazySound (i o : Place) : Prop := N.toPetriNet.LazySound i o

/-- `N.EasySound i o` is easy soundness. -/
abbrev EasySound (i o : Place) : Prop := N.toPetriNet.EasySound i o

/-- `N.IsWFNet i o` says that the net is a workflow net with source `i` and sink `o`. -/
abbrev IsWFNet (i o : Place) : Prop := N.toPetriNet.IsWFNet i o

end Cslib.ExecPetriNet

namespace Cslib.ExecPetriNet

open PetriNet

variable {Place Transition : Type} [DecidableEq Place] (N : ExecPetriNet Place Transition)

/-- `N.firingLanguage M₀ F` is the firing language of the net. -/
abbrev firingLanguage (M₀ : Marking Place) (F : Set (Marking Place)) : Language Transition :=
  N.toPetriNet.firingLanguage M₀ F

end Cslib.ExecPetriNet
