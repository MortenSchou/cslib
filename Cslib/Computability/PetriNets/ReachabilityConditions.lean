/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.StateEquation
import Mathlib.Tactic.FinCases

/-! # Conditions for reachability

Reachability in general nets is decidable (Mayr, Kosaraju), but the proof is far beyond this
file. Here we collect what the state equation says about reachability.

A *firing count vector* `σ : Transition →₀ ℕ` records how often each transition fires. The state
equation `M = M₀ + C σ` is necessary for reachability (`PetriNet.Reachable.exists_vectorEffect`),
but not sufficient in general (`PetriNet.Example.not_reachable`). It becomes sufficient for
nets whose flow relation is acyclic (`PetriNet.reachable_of_vectorEffect`), a theorem of Murata.

## Main definitions

- `PetriNet.Feeds`: a transition `u` feeds `t` if `u` produces tokens in an input place of `t`.
- `PetriNet.FlowAcyclic`: the relation `Feeds` is well-founded.

## Main statements

- `PetriNet.reachable_of_vectorEffect`: in a flow-acyclic net, every nonnegative solution `σ` of
  the state equation is realised by a firing sequence whose firing count vector is `σ`.
- `PetriNet.FlowAcyclic.reachable_iff`: reachability coincides with solvability of the state
  equation in flow-acyclic nets.
- `PetriNet.flowAcyclic_iff_irrefl_transGen`: for finitely many transitions, flow-acyclicity means
  that the transitive closure of `Feeds` is irreflexive.
- `PetriNet.FlowAcyclic.exists_bound`: in a flow-acyclic net where every transition has an input
  place, the firing counts of nonnegative solutions of the state equation are bounded, uniformly in
  the target marking.
- `PetriNet.FlowAcyclic.exists_finite_search`: hence reachability from `M₀` is solvability of the
  state equation by one of finitely many vectors, a finite search.

A decision procedure in the Lean sense (a `Decidable` instance) would be vacuous here, since
`Marking.toInt` and the `Finsupp` operations are noncomputable; the finite search is the content.
The executable nets of `Executable*` are the setting for computable procedures.

The hypothesis that every transition has an input place cannot simply be dropped from the bound:
a transition without input places that feeds a transition without output places has solutions of
the state equation with arbitrarily large firing counts. For such nets, the existence of a
solution is still decided by a bound on *minimal* solutions, which needs a lattice argument
(Pottier-style bounds) that is not formalised here.

## References

* [T. Murata, *Petri nets: Properties, analysis and applications*][Murata1989]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*}

section Acyclic

variable (N : PetriNet Place Transition)

/-- A transition `u` feeds `t` if `u` produces tokens in an input place of `t`. -/
def Feeds (u t : Transition) : Prop :=
  ∃ p, 0 < (u •[N]) p ∧ 0 < (•[N] t) p

/-- A net is flow-acyclic if `Feeds` is well-founded, that is, there is no infinite sequence
`t₀, t₁, …` with `Feeds t_{n+1} t_n` for all `n`. For finitely many transitions this says that the
transitive closure of `Feeds` has no cycle (`flowAcyclic_iff_irrefl_transGen`). In particular nets
with a transition that feeds itself, such as those with self-loops or read arcs, are not
flow-acyclic. -/
def FlowAcyclic : Prop :=
  WellFounded N.Feeds

variable {N}

/-- For finitely many transitions, a net is flow-acyclic exactly when the transitive closure of
`Feeds` is irreflexive. -/
theorem flowAcyclic_iff_irrefl_transGen [Finite Transition] :
    N.FlowAcyclic ↔ ∀ t, ¬ Relation.TransGen N.Feeds t t := by
  refine ⟨fun h t ht => h.transGen.irrefl.irrefl t ht, fun h => ?_⟩
  have : Std.Irrefl (Relation.TransGen N.Feeds) := ⟨h⟩
  exact Subrelation.wf Relation.TransGen.single
    (Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen N.Feeds))

/-- Firing a transition that no other transition in the support of `σ` feeds, and that belongs to
the support, is possible at any `M₀` satisfying the state equation with solution `σ`. -/
theorem enabled_of_vectorEffect {M₀ M : Marking Place} {σ : Transition →₀ ℕ} {t : Transition}
    (ht : t ∈ σ.support) (hmin : ∀ u ∈ σ.support, ¬ N.Feeds u t)
    (heq : Marking.toInt M = Marking.toInt M₀ + N.vectorEffect σ) : M₀ [t⟩[N] := by
  intro p
  have h := toInt_eq_add_vectorEffect_iff.1 heq p
  by_cases hp : (•[N] t) p = 0
  · simp [hp]
  have hprod : N.produced σ p = 0 := by
    rw [produced_apply]
    refine Finset.sum_eq_zero fun u hu => ?_
    have : (u •[N]) p = 0 := Nat.eq_zero_of_not_pos fun h => hmin u hu ⟨p, h, Nat.pos_of_ne_zero hp⟩
    simp [this]
  have h1 := mul_pre_le_consumed (N := N) σ t p
  have h2 : (•[N] t) p ≤ σ t * (•[N] t) p :=
    Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 ht))
  omega

/-- Murata's sufficiency theorem for flow-acyclic nets: a nonnegative solution `σ` of the state
equation is realised by a firing sequence with firing count vector `σ`. The proof fires a
transition of the support that no other transition of the support feeds, and recurses on the rest
of the solution. -/
theorem reachable_of_vectorEffect (hN : N.FlowAcyclic) {M₀ M : Marking Place}
    {σ : Transition →₀ ℕ} (heq : Marking.toInt M = Marking.toInt M₀ + N.vectorEffect σ) :
    ∃ ts, N.lts.MTr M₀ ts M ∧ parikh ts = σ := by
  induction h : σ.degree generalizing σ M₀ with
  | zero =>
    have : σ = 0 := by
      rwa [Finsupp.degree_eq_zero_iff] at h
    subst this
    simp only [vectorEffect_zero, add_zero] at heq
    rw [Marking.toInt_injective heq]
    exact ⟨[], .refl, rfl⟩
  | succ n ih =>
    have hne : σ.support.Nonempty := by
      rw [Finsupp.support_nonempty_iff]
      rintro rfl
      simp at h
    obtain ⟨t, ht, hmin⟩ := hN.has_min (σ.support : Set Transition) hne
    have hen : M₀ [t⟩[N] := enabled_of_vectorEffect ht hmin heq
    have hσt : σ t ≠ 0 := Finsupp.mem_support_iff.1 ht
    have hσ : σ - Finsupp.single t 1 + Finsupp.single t 1 = σ :=
      Finsupp.sub_add_single_one_cancel hσt
    have hfire : M₀ [t⟩[N] N.fire M₀ t := fires_iff.2 ⟨hen, rfl⟩
    obtain ⟨ts, hts, hp⟩ := ih (M₀ := N.fire M₀ t) (σ := σ - Finsupp.single t 1) (by
      rw [hfire.toInt]
      rw [← hσ, vectorEffect_add, vectorEffect_single, one_smul] at heq
      rw [heq]
      abel) (by have := degree_tsub_single_add_one hσt; omega)
    exact ⟨t :: ts, .stepL hfire hts, by rw [parikh_cons, hp, add_comm, hσ]⟩

/-- In a flow-acyclic net, a marking is reachable exactly when the state equation has a
nonnegative solution. -/
theorem FlowAcyclic.reachable_iff (hN : N.FlowAcyclic) {M₀ M : Marking Place} :
    M₀ ⇝[N] M ↔ ∃ σ : Transition →₀ ℕ, Marking.toInt M = Marking.toInt M₀ + N.vectorEffect σ :=
  ⟨Reachable.exists_vectorEffect, fun ⟨_, h⟩ =>
    let ⟨ts, hts, _⟩ := reachable_of_vectorEffect hN h
    ⟨ts, hts⟩⟩

section Bound

variable {N : PetriNet Place Transition}

/-- **A priori bound for acyclic nets.** In a flow-acyclic net with finitely many transitions, each
of which has an input place, the firing counts of nonnegative solutions of the state equation from
`M₀` are bounded, whatever the target marking. The bound for `t` comes from the tokens that can
ever reach one of its input places: those in `M₀` and those produced by the transitions that feed
`t`, which are bounded by induction along `Feeds`. -/
theorem FlowAcyclic.exists_bound [Finite Transition] (hN : N.FlowAcyclic)
    (hsrc : ∀ t, ∃ p, 0 < (•[N] t) p) (M₀ : Marking Place) :
    ∃ B : Transition → ℕ, ∀ {M : Marking Place} {σ : Transition →₀ ℕ},
      Marking.toInt M = Marking.toInt M₀ + N.vectorEffect σ → ∀ t, σ t ≤ B t := by
  have := Fintype.ofFinite Transition
  suffices key : ∀ t, ∃ b, ∀ {M : Marking Place} {σ : Transition →₀ ℕ},
      Marking.toInt M = Marking.toInt M₀ + N.vectorEffect σ → σ t ≤ b by
    choose B hB using key
    exact ⟨B, fun h t => hB t h⟩
  intro t
  induction t using hN.induction with
  | _ t ih =>
  obtain ⟨p, hp⟩ := hsrc t
  have ih' : ∀ u, ∃ b, N.Feeds u t → ∀ {M : Marking Place} {σ : Transition →₀ ℕ},
      Marking.toInt M = Marking.toInt M₀ + N.vectorEffect σ → σ u ≤ b := by
    intro u
    by_cases hu : N.Feeds u t
    · obtain ⟨b, hb⟩ := ih u hu
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hu⟩
  choose b hb using ih'
  refine ⟨M₀ p + ∑ u, b u * (u •[N]) p, fun {M σ} heq => ?_⟩
  have h := toInt_eq_add_vectorEffect_iff.1 heq p
  have h1 := mul_pre_le_consumed (N := N) σ t p
  have h2 : σ t ≤ σ t * (•[N] t) p := Nat.le_mul_of_pos_right _ hp
  have h3 : N.produced σ p ≤ ∑ u, b u * (u •[N]) p := by
    rw [produced_apply, Finsupp.sum_fintype _ _ (by simp)]
    refine Finset.sum_le_sum fun u _ => ?_
    by_cases hu : N.Feeds u t
    · exact Nat.mul_le_mul_right _ (hb u hu heq)
    · have : (u •[N]) p = 0 := Nat.eq_zero_of_not_pos fun h => hu ⟨p, h, hp⟩
      simp [this]
  omega

/-- **Reachability in flow-acyclic nets is a finite search.** In a flow-acyclic net with finitely
many transitions, each of which has an input place, a marking is reachable from `M₀` exactly when
the state equation has a solution in some fixed finite set of vectors. -/
theorem FlowAcyclic.exists_finite_search [Finite Transition] (hN : N.FlowAcyclic)
    (hsrc : ∀ t, ∃ p, 0 < (•[N] t) p) (M₀ : Marking Place) :
    ∃ S : Set (Transition →₀ ℕ), S.Finite ∧ ∀ M : Marking Place,
      M₀ ⇝[N] M ↔ ∃ σ ∈ S, Marking.toInt M = Marking.toInt M₀ + N.vectorEffect σ := by
  have := Fintype.ofFinite Transition
  obtain ⟨B, hB⟩ := hN.exists_bound hsrc M₀
  refine ⟨Finsupp.equivFunOnFinite.symm '' Set.pi Set.univ (fun t => {n | n ≤ B t}),
    (Set.Finite.pi fun t => Set.finite_le_nat _).image _, fun M => ?_⟩
  rw [hN.reachable_iff]
  refine ⟨?_, fun ⟨σ, _, h⟩ => ⟨σ, h⟩⟩
  rintro ⟨σ, h⟩
  exact ⟨σ, ⟨⇑σ, fun t _ => hB h t, by ext; simp⟩, h⟩

end Bound

end Acyclic

namespace Example

/-- A net with places `0, 1, 2` and two transitions: `false` moves a token from place `0` to
place `1`, and `true` moves a token from `1` to `0` and also puts one in `2`. -/
noncomputable def cycleNet : PetriNet (Fin 3) Bool where
  pre b := if b then Finsupp.single 1 1 else Finsupp.single 0 1
  post b := if b then Finsupp.single 0 1 + Finsupp.single 2 1 else Finsupp.single 1 1

/-- The state equation has a nonnegative solution from the empty marking to a token in place `2`:
fire each transition once. -/
theorem cycleNet_stateEquation :
    Marking.toInt (Finsupp.single 2 1 : Marking (Fin 3)) =
      Marking.toInt (0 : Marking (Fin 3)) +
        cycleNet.vectorEffect (Finsupp.single true 1 + Finsupp.single false 1) := by
  ext p
  fin_cases p <;> simp [vectorEffect_add, cycleNet, incidence]

/-- No transition of `cycleNet` is enabled at the empty marking. -/
theorem cycleNet_not_enabled (b : Bool) : ¬ (0 : Marking (Fin 3)) [b⟩[cycleNet] := by
  intro h
  cases b
  · simpa [cycleNet] using h 0
  · simpa [cycleNet] using h 1

/-- The state equation is not sufficient for reachability: the marking with one token in place `2`
solves it, but is not reachable from the empty marking, since nothing can fire there. -/
theorem not_reachable :
    ¬ (0 : Marking (Fin 3)) ⇝[cycleNet] Finsupp.single 2 1 := by
  intro h
  have := Reachable.invariant (P := fun M => M = 0)
    (fun hf hM => absurd (hM ▸ (fires_iff.1 hf).1) (cycleNet_not_enabled _)) h rfl
  simpa using congrArg (· 2) this

end Example

end PetriNet

end Cslib
