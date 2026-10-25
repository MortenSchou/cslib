/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.StateEquation

/-! # Conditions for reachability

Reachability in general nets is decidable (Mayr, Kosaraju), but the proof is far beyond this
file. Here we collect what the state equation says about reachability.

A *firing count vector* `σ : Multiset Transition` records how often each transition fires. The
state equation `M + Σ_{t ∈ σ} pre t = M₀ + Σ_{t ∈ σ} post t` is necessary for reachability
(`PetriNet.Reachable.exists_add_sum_pre`), but not sufficient in general
(`PetriNet.Example.not_reachable`). It becomes sufficient for nets whose flow relation is acyclic
(`PetriNet.reachable_of_add_sum_pre`), a theorem of Murata.

## Main definitions

- `PetriNet.Feeds`: a transition `u` feeds `t` if `u` produces tokens in an input place of `t`.
- `PetriNet.FlowAcyclic`: the relation `Feeds` is well-founded.

## Main statements

- `PetriNet.reachable_of_add_sum_pre`: in a flow-acyclic net, every solution `σ` of the state
  equation is realised by a firing sequence whose firing count vector is `σ`.
- `PetriNet.FlowAcyclic.reachable_iff`: reachability coincides with solvability of the state
  equation in flow-acyclic nets.
- `PetriNet.flowAcyclic_iff_irrefl_transGen`: for finitely many transitions, flow-acyclicity means
  that the transitive closure of `Feeds` is irreflexive.
- `PetriNet.FlowAcyclic.exists_bound`: in a flow-acyclic net where every transition has an input
  place, the solutions of the state equation are bounded, uniformly in the target marking.
- `PetriNet.FlowAcyclic.exists_finite_search`: hence reachability from `M₀` is solvability of the
  state equation by a sub-multiset of a fixed firing count vector, a finite search.

The bound is obtained by well-founded induction along `Feeds` and is not computed here, so the
finite search is not packaged as a `Decidable` instance.

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
  ∃ p, p ∈ u •[N] ∧ p ∈ •[N] t

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

/-- A transition of a solution `σ` of the state equation that no transition of `σ` feeds is
enabled at the initial marking. -/
theorem enabled_of_add_sum_pre {M₀ M : Marking Place} {σ : Multiset Transition} {t : Transition}
    (ht : t ∈ σ) (hmin : ∀ u ∈ σ, ¬ N.Feeds u t)
    (heq : M + (σ.map N.pre).sum = M₀ + (σ.map N.post).sum) : M₀ [t⟩[N] := by
  classical
  refine Multiset.le_iff_count.2 fun p => ?_
  by_cases hp : p ∈ •[N] t
  · have hprod : p ∉ (σ.map N.post).sum := fun hmem => by
      obtain ⟨_, hm, hpm⟩ := Multiset.mem_join.1 hmem
      obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.1 hm
      exact hmin u hu ⟨p, hpm, hp⟩
    have h := congrArg (Multiset.count p) heq
    have hle := Multiset.count_le_of_le p
      (Multiset.le_sum_of_mem (Multiset.mem_map_of_mem N.pre ht))
    simp only [Multiset.count_add, Multiset.count_eq_zero.2 hprod] at h
    omega
  · simp [Multiset.count_eq_zero.2 hp]

/-- Murata's sufficiency theorem for flow-acyclic nets: a solution `σ` of the state equation is
realised by a firing sequence with firing count vector `σ`. The proof fires a transition of `σ`
that no other transition of `σ` feeds, and recurses on the rest of the solution. -/
theorem reachable_of_add_sum_pre (hN : N.FlowAcyclic) {M₀ M : Marking Place}
    {σ : Multiset Transition} (heq : M + (σ.map N.pre).sum = M₀ + (σ.map N.post).sum) :
    ∃ ts, N.lts.MTr M₀ ts M ∧ (ts : Multiset Transition) = σ := by
  induction σ using Multiset.strongInductionOn generalizing M₀ with
  | ih σ ih =>
  rcases Multiset.empty_or_exists_mem σ with rfl | ⟨t₁, ht₁⟩
  · simp only [Multiset.map_zero, Multiset.sum_zero, add_zero] at heq
    exact ⟨[], heq ▸ .refl, rfl⟩
  obtain ⟨t, ht, hmin⟩ := hN.has_min {t | t ∈ σ} ⟨t₁, ht₁⟩
  obtain ⟨R, hR⟩ := exists_add_of_le (enabled_of_add_sum_pre ht hmin heq)
  have hfire : M₀ [t⟩[N] R + t •[N] := ⟨R, hR, rfl⟩
  classical
  obtain ⟨ts, hts, hp⟩ := ih (σ.erase t) (Multiset.erase_lt.2 ht) (M₀ := R + t •[N]) (by
    rw [← Multiset.cons_erase ht, Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.sum_cons, hR] at heq
    apply add_left_cancel (a := •[N] t)
    rw [add_left_comm, heq]
    abel)
  exact ⟨t :: ts, .stepL hfire hts, by rw [← Multiset.cons_coe, hp, Multiset.cons_erase ht]⟩

/-- In a flow-acyclic net, a marking is reachable exactly when the state equation has a
solution. -/
theorem FlowAcyclic.reachable_iff (hN : N.FlowAcyclic) {M₀ M : Marking Place} :
    M₀ ⇝[N] M ↔
      ∃ σ : Multiset Transition, M + (σ.map N.pre).sum = M₀ + (σ.map N.post).sum :=
  ⟨Reachable.exists_add_sum_pre, fun ⟨_, h⟩ =>
    let ⟨ts, hts, _⟩ := reachable_of_add_sum_pre hN h
    ⟨ts, hts⟩⟩

section Bound

variable {N : PetriNet Place Transition}

/-- **A priori bound for acyclic nets.** In a flow-acyclic net with finitely many transitions, each
of which has an input place, the solutions of the state equation from `M₀` are bounded, whatever
the target marking. The bound for `t` comes from the tokens that can ever reach one of its input
places: those in `M₀` and those produced by the transitions that feed `t`, which are bounded by
induction along `Feeds`. -/
theorem FlowAcyclic.exists_bound [Finite Transition] (hN : N.FlowAcyclic)
    (hsrc : ∀ t, ∃ p, p ∈ •[N] t) (M₀ : Marking Place) :
    ∃ B : Multiset Transition, ∀ {M : Marking Place} {σ : Multiset Transition},
      M + (σ.map N.pre).sum = M₀ + (σ.map N.post).sum → σ ≤ B := by
  classical
  have := Fintype.ofFinite Transition
  suffices key : ∀ t, ∃ b, ∀ {M : Marking Place} {σ : Multiset Transition},
      M + (σ.map N.pre).sum = M₀ + (σ.map N.post).sum → σ.count t ≤ b by
    choose b hb using key
    refine ⟨∑ t, Multiset.replicate (b t) t, fun h => Multiset.le_iff_count.2 fun t => ?_⟩
    simpa [Multiset.count_sum', Multiset.count_replicate] using hb t h
  intro t
  induction t using hN.induction with
  | _ t ih =>
  obtain ⟨p, hp⟩ := hsrc t
  have ih' : ∀ u, ∃ b, N.Feeds u t → ∀ {M : Marking Place} {σ : Multiset Transition},
      M + (σ.map N.pre).sum = M₀ + (σ.map N.post).sum → σ.count u ≤ b := by
    intro u
    by_cases hu : N.Feeds u t
    · obtain ⟨b, hb⟩ := ih u hu
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hu⟩
  choose b hb using ih'
  refine ⟨M₀.count p + ∑ u, b u * (u •[N]).count p, fun {M σ} heq => ?_⟩
  have h := congrArg (Multiset.count p) heq
  have h1 := count_le_count_sum_map hp σ
  rw [Multiset.count_add, Multiset.count_add, Multiset.count_sum (m := σ) (f := N.post)] at h
  have h2 : (σ.map fun u => (u •[N]).count p).sum ≤ ∑ u, b u * (u •[N]).count p := by
    rw [Finset.sum_multiset_map_count,
      Finset.sum_subset (Finset.subset_univ _) fun u _ hu => by
        rw [Multiset.count_eq_zero.2 (by simpa using hu), zero_smul]]
    refine Finset.sum_le_sum fun u _ => ?_
    by_cases hu : N.Feeds u t
    · rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ (hb u hu heq)
    · have : p ∉ u •[N] := fun h => hu ⟨p, h, hp⟩
      simp [Multiset.count_eq_zero.2 this]
  omega

/-- **Reachability in flow-acyclic nets is a finite search.** In a flow-acyclic net with finitely
many transitions, each of which has an input place, there is a firing count vector `B` such that
a marking is reachable from `M₀` exactly when the state equation has a solution among the
finitely many sub-multisets of `B`. -/
theorem FlowAcyclic.exists_finite_search [Finite Transition] (hN : N.FlowAcyclic)
    (hsrc : ∀ t, ∃ p, p ∈ •[N] t) (M₀ : Marking Place) :
    ∃ B : Multiset Transition, ∀ M : Marking Place,
      M₀ ⇝[N] M ↔ ∃ σ ∈ B.powerset, M + (σ.map N.pre).sum = M₀ + (σ.map N.post).sum := by
  obtain ⟨B, hB⟩ := hN.exists_bound hsrc M₀
  refine ⟨B, fun M => ?_⟩
  rw [hN.reachable_iff]
  exact ⟨fun ⟨σ, h⟩ => ⟨σ, Multiset.mem_powerset.2 (hB h), h⟩, fun ⟨σ, _, h⟩ => ⟨σ, h⟩⟩

end Bound

end Acyclic

namespace Example

/-- A net with places `0, 1, 2` and two transitions: `false` moves a token from place `0` to
place `1`, and `true` moves a token from `1` to `0` and also puts one in `2`. -/
def cycleNet : PetriNet (Fin 3) Bool where
  pre b := if b then {1} else {0}
  post b := if b then {0, 2} else {1}

/-- The state equation has a solution from the empty marking to a token in place `2`: fire each
transition once. -/
theorem cycleNet_stateEquation :
    ({2} : Marking (Fin 3)) + (({true, false} : Multiset Bool).map cycleNet.pre).sum =
      0 + (({true, false} : Multiset Bool).map cycleNet.post).sum := by
  decide

/-- No transition of `cycleNet` is enabled at the empty marking. -/
theorem cycleNet_not_enabled (b : Bool) : ¬ (0 : Marking (Fin 3)) [b⟩[cycleNet] := by
  cases b <;> decide

/-- The state equation is not sufficient for reachability: the marking with one token in place `2`
solves it, but is not reachable from the empty marking, since nothing can fire there. -/
theorem not_reachable : ¬ (0 : Marking (Fin 3)) ⇝[cycleNet] {2} := by
  intro h
  have := Reachable.invariant (P := fun M => M = 0)
    (fun hf hM => absurd (hM ▸ (enabled_iff_exists_fires.2 ⟨_, hf⟩)) (cycleNet_not_enabled _)) h rfl
  exact Multiset.singleton_ne_zero _ this

end Example

end PetriNet

end Cslib
