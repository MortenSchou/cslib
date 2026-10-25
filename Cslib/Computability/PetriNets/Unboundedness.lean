/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Coverability
public import Cslib.Computability.WSTS.Unboundedness

/-! # Characterisation of unbounded nets

A net with finitely many places and transitions is unbounded at `M₀` exactly when some marking
reachable from `M₀` can reach a strictly larger marking. The easy direction is
`not_bounded_of_pump`. The converse is König's lemma with Dickson's lemma, which holds for any
finitely branching transition system on a well-quasi-ordered partial order and is proved in
`Cslib.WSTS.exists_pump_of_infinite_reachable`; a net is unbounded iff it has infinitely many
reachable markings (`bounded_iff_finite_reachable`).

## Main statements

- `PetriNet.exists_pump_of_not_bounded`: an unbounded net has a pumping pair.
- `PetriNet.bounded_iff_no_pump`: the characterisation.

## References

* [R. M. Karp, R. E. Miller, *Parallel Program Schemata*][KarpMiller1969]
* [T. Murata, *Petri nets: Properties, analysis and applications*][Murata1989]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*} {N : PetriNet Place Transition}

/-- An unbounded net over finitely many places and transitions has a pumping pair. This is the
generic `Cslib.WSTS.exists_pump_of_infinite_reachable` for the marking graph. -/
theorem exists_pump_of_not_bounded [Finite Place] [Finite Transition] {M₀ : Marking Place}
    (h : ¬ N.Bounded M₀) :
    ∃ M₁ M₂, M₀ ⇝[N] M₁ ∧ M₁ ⇝[N] M₂ ∧ M₁ < M₂ :=
  WSTS.exists_pump_of_infinite_reachable (lts := N.lts)
    fun hfin => h (bounded_of_finite_reachable hfin)

/-- A net over finitely many places and transitions is bounded exactly when no reachable marking
can reach a strictly larger one. -/
theorem bounded_iff_no_pump [Finite Place] [Finite Transition]
    {M₀ : Marking Place} :
    N.Bounded M₀ ↔ ¬ ∃ M₁ M₂, M₀ ⇝[N] M₁ ∧ M₁ ⇝[N] M₂ ∧ M₁ < M₂ :=
  ⟨fun hb ⟨_, _, h1, h2, hlt⟩ => not_bounded_of_pump h1 h2 hlt hb,
    fun hno => by_contra fun hb => hno (exists_pump_of_not_bounded hb)⟩

end PetriNet

end Cslib
