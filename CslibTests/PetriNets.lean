/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.Automaton
import Cslib.Computability.PetriNets.BackwardCoverability
import Cslib.Computability.PetriNets.Basic
import Cslib.Computability.PetriNets.CTL
import Cslib.Computability.PetriNets.Coverability
import Cslib.Computability.PetriNets.CoverabilityBasis
import Cslib.Computability.PetriNets.Decision.Boundedness
import Cslib.Computability.PetriNets.Decision.Coverability
import Cslib.Computability.PetriNets.Decision.Language
import Cslib.Computability.PetriNets.Decision.Reachability
import Cslib.Computability.PetriNets.Decision.Soundness
import Cslib.Computability.PetriNets.Decision.SoundnessNotions
import Cslib.Computability.PetriNets.Decision.Structure
import Cslib.Computability.PetriNets.Equivalence
import Cslib.Computability.PetriNets.FreeChoice
import Cslib.Computability.PetriNets.LTL
import Cslib.Computability.PetriNets.Monotonicity
import Cslib.Computability.PetriNets.PlaceInvariants
import Cslib.Computability.PetriNets.Semantics
import Cslib.Computability.PetriNets.Soundness
import Cslib.Computability.PetriNets.SoundnessNotions
import Cslib.Computability.PetriNets.StateEquation
import Cslib.Computability.PetriNets.Structure
import Cslib.Computability.PetriNets.Unboundedness

namespace CslibTests

open Cslib PetriNet
open scoped PetriNet

/-! A producer/consumer net: `producing --produce--> buffer --consume--> consuming`. -/

inductive Pl | producing | buffer | consuming
  deriving DecidableEq

inductive Tr | produce | consume
  deriving DecidableEq

open Pl Tr

instance : Fintype Pl := ⟨{producing, buffer, consuming}, fun x => by cases x <;> simp⟩

/-- `produce` turns a `producing` token into a `buffer` token; `consume` moves it to `consuming`. -/
def prodCons : PetriNet Pl Tr where
  pre | produce => {producing} | consume => {buffer}
  post | produce => {buffer} | consume => {consuming}

/-! ### Notation -/

-- Markings are multiset literals; the enabling, firing and reachability notation is
-- pretty-printed with the notation.

/-- info: {producing, buffer} : Marking Pl -/
#guard_msgs in
#check ({producing, buffer} : Marking Pl)

/-- info: 0 : Marking Pl -/
#guard_msgs in
#check (0 : Marking Pl)

/-- info: {producing} [produce⟩[prodCons] {buffer} : Prop -/
#guard_msgs in
#check ({producing} : Marking Pl) [produce⟩[prodCons] {buffer}

/-- info: {producing} ⇝[prodCons] {consuming} : Prop -/
#guard_msgs in
#check ({producing} : Marking Pl) ⇝[prodCons] {consuming}

/-- The preset and postset of `produce`. -/
example : •[prodCons] produce = {producing} := rfl

example : produce •[prodCons] = {buffer} := rfl

/-! ### Enabling and firing -/

example : ({producing} : Marking Pl) [produce⟩[prodCons] := le_rfl

example : ¬ ({producing} : Marking Pl) [consume⟩[prodCons] := by decide

/-- Firing moves the token; the tokens not consumed (here the extra `consuming` token) stay. -/
theorem fires_produce_consuming :
    ({producing, consuming} : Marking Pl) [produce⟩[prodCons] {buffer, consuming} :=
  ⟨{consuming}, rfl, Multiset.cons_swap ..⟩

/-- Firing is the explicit rule `M - pre + post`. -/
example : prodCons.fire {producing, consuming} produce = {buffer, consuming} :=
  (fires_iff.1 fires_produce_consuming).2.symm

/-! ### Reachability and boundedness -/

example : ({producing} : Marking Pl) ⇝[prodCons] {consuming} := by
  have h₁ : ({producing} : Marking Pl) [produce⟩[prodCons] {buffer} := by decide
  have h₂ : ({buffer} : Marking Pl) [consume⟩[prodCons] {consuming} := by decide
  exact h₁.reachable.trans h₂.reachable

/-- Both transitions consume and produce one token, so the net is conservative. -/
theorem prodCons_conservative : prodCons.Conservative := by
  intro t
  cases t <;> rfl

/-- A conservative net is bounded, and with finitely many places it has finitely many reachable
markings. -/
example (M₀ : Marking Pl) : {M | M₀ ⇝[prodCons] M}.Finite :=
  (prodCons_conservative.kBounded M₀).finite_reachable

/-- The marking graph of any net is deterministic. -/
example : prodCons.lts.Deterministic := inferInstance

/-- With finitely many transitions it is finitely branching. -/
instance : Fintype Tr := ⟨{produce, consume}, fun x => by cases x <;> simp⟩

example : prodCons.lts.FinitelyBranching := inferInstance

/-- A marking with no enabled transition is dead. -/
example : prodCons.Dead {consuming} := by
  rw [dead_iff]
  decide

/-! ### The computable firing rule -/

example : prodCons.fire? {producing} consume = none := by decide

example : prodCons.run {producing} [produce, consume] = some {consuming} := by decide

/-- A run of the computable rule is a firing sequence of the marking graph. -/
example : prodCons.lts.MTr {producing} [produce, consume] {consuming} :=
  run_eq_some_iff.1 (by decide)

/-! ### Monotonicity -/

theorem fires_produce : ({producing} : Marking Pl) [produce⟩[prodCons] {buffer} :=
  ⟨0, rfl, rfl⟩

theorem fires_consume : ({buffer} : Marking Pl) [consume⟩[prodCons] {consuming} :=
  ⟨0, rfl, rfl⟩

/-- Extra tokens never disable a transition. -/
example : ({producing, consuming} : Marking Pl) [produce⟩[prodCons] :=
  (show ({producing} : Marking Pl) [produce⟩[prodCons] from le_rfl).mono (by decide)

/-- A firing sequence can be replayed from a larger marking, reaching a larger marking. -/
example : ∃ M', prodCons.lts.MTr {producing, consuming} [produce] M' ∧ {buffer} ≤ M' :=
  mTr_mono (.single _ fires_produce) (by decide)

/-- The net is bounded at every marking, hence at the smaller marking `{producing}`. -/
example : prodCons.Bounded {producing} :=
  (prodCons_conservative.kBounded _).bounded

/-! ### Coverability and unboundedness -/

/-- A source transition that creates a token from nothing. -/
def source : PetriNet Unit Unit where
  pre _ := 0
  post _ := {()}

theorem source_fires (M : Marking Unit) : M [()⟩[source] (M + {()}) :=
  ⟨M, (zero_add M).symm, rfl⟩

/-- The source net is unbounded, by pumping from the empty marking. -/
theorem source_unbounded : ¬ source.Bounded 0 :=
  not_bounded_of_pump (.refl _ _) (source_fires 0).reachable (Multiset.lt_cons_self 0 ())

/-- By the characterisation of unbounded nets, the source net has a pumping pair. -/
example : ∃ M₁ M₂, 0 ⇝[source] M₁ ∧ M₁ ⇝[source] M₂ ∧ M₁ < M₂ :=
  exists_pump_of_not_bounded source_unbounded

/-- The producer/consumer net is bounded, so no reachable marking can be pumped. -/
example (M₀ : Marking Pl) : ¬ ∃ M₁ M₂, M₀ ⇝[prodCons] M₁ ∧ M₁ ⇝[prodCons] M₂ ∧ M₁ < M₂ :=
  bounded_iff_no_pump.1 (prodCons_conservative.kBounded _).bounded

/-- Every marking is coverable from every marking in the source net. -/
theorem source_coverable (M₀ M : Marking Unit) : source.Coverable M₀ M := by
  have hreach : ∀ n : ℕ, M₀ ⇝[source] (M₀ + n • {()}) := by
    intro n
    induction n with
    | zero => simpa using Reachable.refl source M₀
    | succ n ih =>
      refine ih.trans (Fires.reachable (t := ()) ?_)
      have := source_fires (M₀ + n • {()})
      rwa [succ_nsmul, ← add_assoc]
  refine ⟨_, hreach M.card, ?_⟩
  rw [Multiset.nsmul_singleton, ← Multiset.eq_replicate_card.2 fun _ _ => rfl]
  exact Multiset.le_add_left _ _

/-- Hence every finite basis for coverability on the source net contains the empty marking. -/
example (M : Marking Unit) : ∃ B : Set (Marking Unit), B.Finite ∧ (0 : Marking Unit) ∈ B ∧
    ∀ M₀, source.Coverable M₀ M ↔ ∃ b ∈ B, b ≤ M₀ := by
  obtain ⟨B, hB, hiff⟩ := exists_finite_basis_coverable (N := source) M
  obtain ⟨b, hb, hb0⟩ := (hiff 0).1 (source_coverable 0 M)
  have hb' : b = 0 := Multiset.le_zero.1 hb0
  exact ⟨B, hB, hb' ▸ hb, hiff⟩

/-- Backward coverability on the producer/consumer net: `{buffer}` is a predecessor of the target
`{consuming}` after one step, and `{producing}` after two. -/
theorem producing_mem_backSeq : {producing} ∈ prodCons.backSeq {consuming} 2 := by
  have h1 : {buffer} ∈ prodCons.backSeq {consuming} 1 := by
    rw [backSeq_succ]
    exact Or.inr ⟨consume, _, fires_consume, show _ ∈ Set.Ici _ from Set.mem_Ici.2 le_rfl⟩
  rw [backSeq_succ]
  exact Or.inr ⟨produce, _, fires_produce, h1⟩

example : prodCons.Coverable {producing} {consuming} :=
  coverable_of_mem_backSeq producing_mem_backSeq

/-- The backward iteration reaches a fixpoint that is exactly the coverable markings. -/
example : ∃ n, prodCons.backStep (prodCons.backSeq {consuming} n) = prodCons.backSeq {consuming} n ∧
    ∀ M₀, prodCons.Coverable M₀ {consuming} ↔ M₀ ∈ prodCons.backSeq {consuming} n :=
  exists_backSeq_fixpoint _

/-! ### Computable firing

Markings are multisets, so firing is computable and the properties of the net can be decided. -/

/-- The computable firing function agrees with the firing relation. -/
example : prodCons.fire? {producing} produce = some {buffer} :=
  fire?_eq_some_iff.2 fires_produce

/-- Two items in the system. -/
def M₀ : Marking Pl := {producing, producing}

example : M₀ [produce⟩[prodCons] := by decide
example : ¬ M₀ [consume⟩[prodCons] := by decide

example : (prodCons.run M₀ [produce, consume]).isSome = true := by decide
example : (prodCons.run M₀ [consume]).isNone = true := by decide
example : prodCons.run M₀ [produce, produce, consume] = some {buffer, consuming} := by
  decide

/-- The computable firing function witnesses the firing relation. -/
example : M₀ [produce⟩[prodCons] {producing, buffer} :=
  fire?_eq_some_iff.1 (by decide)

/-- Enabledness and firing are decided directly. -/
example : ({producing} : Marking Pl) [produce⟩[prodCons] := by decide

example : M₀ [produce⟩[prodCons] {producing, buffer} := by decide

/-- Reachability is witnessed by a computed run. -/
example : ({producing} : Marking Pl) ⇝[prodCons] {consuming} :=
  ⟨[produce, consume], run_eq_some_iff.1 (by decide)⟩

/-! ### Decidable coverability -/

/-- The backward iteration from `{consuming}` has stabilised after two steps. -/
example : WSTS.Stable prodCons.predBasis
    (WSTS.basisSeq prodCons.predBasis ({consuming} : Marking Pl) 2) := by decide

/-- `{producing}` can cover `{consuming}`. -/
example : prodCons.Coverable {producing} {consuming} := by decide

/-- The empty marking cannot cover `{consuming}`. -/
example : ¬ prodCons.Coverable 0 {consuming} := by decide

/-! ### Decidable boundedness -/

/-- The reachable markings of the producer/consumer net from `M₀` stop growing after four steps. -/
example : prodCons.Closed M₀ 4 := by decide

/-- The source net has a pumping pair already within one step. -/
example : source.PumpWithin 0 1 := by decide

/-- Boundedness is decided outright, in both directions. -/
example : prodCons.Bounded M₀ := by decide

example : ¬ source.Bounded 0 := by decide

/-! ### The state equation -/

/-- Firing never produces tokens in `producing`. -/
theorem prodCons_incidence_producing (t : Tr) : prodCons.incidence t producing ≤ 0 := by
  cases t <;> decide

theorem prodCons_effect_producing (ts : List Tr) : prodCons.effect ts producing ≤ 0 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [effect_cons, Pi.add_apply]
    have := prodCons_incidence_producing t
    omega

/-- By the state equation, no marking with more `producing` tokens than `M₀` is reachable. -/
example (M : Marking Pl) (h : 2 < M.count producing) : ¬ M₀ ⇝[prodCons] M := by
  intro hr
  obtain ⟨ts, hts⟩ := hr.exists_toInt_eq
  have h1 := congrFun hts producing
  have h2 := prodCons_effect_producing ts
  simp only [Pi.add_apply, Marking.toInt_apply] at h1
  have h3 : M₀.count producing = 2 := rfl
  omega

/-! ### Place invariants -/

/-- Two `a` tokens are merged into one `b` token, so `a` has weight `1` and `b` has weight `2`. -/
inductive Pl2 | a | b
  deriving DecidableEq

instance : Fintype Pl2 := ⟨{.a, .b}, fun x => by cases x <;> simp⟩

def merge : PetriNet Pl2 Unit where
  pre _ := {.a, .a}
  post _ := {.b}

def mergeWeight : Pl2 → ℕ | .a => 1 | .b => 2

theorem merge_invariant : merge.IsInvariant mergeWeight := by
  intro t
  rw [Marking.weight_apply, Marking.weight_apply]
  rfl

/-- A positive invariant bounds the net at every marking. -/
example (M₀ : Marking Pl2) : merge.Bounded M₀ :=
  merge_invariant.bounded (by intro p; cases p <;> simp [mergeWeight]) M₀

/-- The merge net is not conservative, although it has an invariant. -/
example : ¬ merge.Conservative := by
  rw [conservative_iff_isInvariant]
  intro h
  exact absurd (h ()) (by decide)

/-! ### Siphons and traps -/

/-- In the producer/consumer net, `producing` is a siphon (nothing produces into it) and
`consuming` is a trap (nothing consumes from it). -/
theorem prodCons_siphon : prodCons.IsSiphon {producing} := by
  rintro t ⟨p, rfl, hp⟩
  cases t <;> simp [prodCons] at hp

theorem prodCons_trap : prodCons.IsTrap {consuming} := by
  rintro t ⟨p, rfl, hp⟩
  cases t <;> simp [prodCons] at hp

/-- With no `producing` token, none can ever appear. -/
example (M M' : Marking Pl) (h : M ⇝[prodCons] M') (hM : producing ∉ M) :
    producing ∉ M' := fun hp =>
  prodCons_siphon.unmarked_of_reachable h (fun ⟨_, rfl, hpM⟩ => hM hpM) ⟨producing, rfl, hp⟩

/-- A two-place cycle: `false` moves a token from place `false` to place `true`, and `true`
moves it back. -/
def cycleNet : PetriNet Bool Bool where
  pre t := {t}
  post t := {!t}

theorem cycleNet_ordinary : cycleNet.Ordinary :=
  fun t => ⟨Multiset.nodup_singleton t, Multiset.nodup_singleton !t⟩

/-- The firing sequence `[false, true]` of the cycle net has total effect zero, so it returns to
its starting marking from every marking where it can fire. -/
example (M M' : Marking Bool) (h : cycleNet.lts.MTr M [false, true] M') : M' = M :=
  (mTr_eq_iff_effect_eq_zero h).2 (by decide)

/-- The same, by the multiset form of the state equation: the sequence consumes exactly the
tokens it produces. -/
example (M M' : Marking Bool) (h : cycleNet.lts.MTr M [false, true] M') : M' = M :=
  (mTr_eq_iff_sum_pre_eq h).2 (by decide)

/-! ### Structure

The structural properties of nets are decidable. -/

/-- The producer/consumer net is ordinary, free-choice and conservative. -/
example : prodCons.Ordinary := by decide

example : prodCons.IsFreeChoice := by decide

example : prodCons.Conservative := by decide

/-! ### Free-choice nets and Commoner's theorem -/

inductive Tr3 | a | b | c
  deriving DecidableEq

instance : Fintype Tr3 := ⟨{Tr3.a, Tr3.b, Tr3.c}, fun x => by cases x <;> simp⟩

/-- The producer/consumer net closed into a ring by a transition returning the token. -/
def ring : PetriNet Pl Tr3 where
  pre | .a => {producing} | .b => {buffer} | .c => {consuming}
  post | .a => {buffer} | .b => {consuming} | .c => {producing}

/-- The hypotheses of Commoner's criterion are all decided: the ring is ordinary and free-choice,
and every nonempty siphon contains a trap marked at the initial marking. Hence the ring is live. -/
example : ring.Ordinary := by decide

example : ring.IsFreeChoice := by decide

example : ring.SiphonTrap {producing} := by decide

example : ring.Live {producing} :=
  live_of_siphons_contain_marked_trap (by decide) (by decide) (by decide)

/-- Commoner's theorem for the ring: it is live exactly when it has the siphon-trap property. -/
example : ring.Live {producing} :=
  (live_iff_siphonTrap (by decide) (by decide) (by decide)).2 (by decide)

inductive Pl4 | i | p | q | o
  deriving DecidableEq

instance : Fintype Pl4 := ⟨{.i, .p, .q, .o}, fun x => by cases x <;> simp⟩

inductive Tr5 | a | b | c | d | e
  deriving DecidableEq

instance : Fintype Tr5 := ⟨{.a, .b, .c, .d, .e}, fun x => by cases x <;> simp⟩

/-- A free-choice net in which the token on the cycle `i → p → q → i` may escape through `d` to a
place `o` that only loops. -/
def escapeNet : PetriNet Pl4 Tr5 where
  pre | .a => {.i} | .b => {.p} | .c => {.q} | .d => {.p} | .e => {.o}
  post | .a => {.p} | .b => {.q} | .c => {.i} | .d => {.o} | .e => {.o}

/-- The escape net is not live. Reachability alone would not show this easily, but the converse of
Commoner's theorem reduces it to a finite check: the siphon `{i, p, q}` contains no trap. -/
example : ¬ escapeNet.Live {Pl4.i} := fun hl =>
  (by decide : ¬ escapeNet.SiphonTrap {Pl4.i})
    (siphonTrap_of_live (by decide) (by decide) hl (by decide))

/-- Without a token, the siphon-trap property fails: the empty marking marks no trap. -/
example : ¬ ring.SiphonTrap 0 := by decide

/-- Two transitions sharing `producing` but with different presets break free choice. -/
def confusion : PetriNet Pl Tr where
  pre | produce => {producing} | consume => {producing, buffer}
  post | produce => {buffer} | consume => {consuming}

example : ¬ confusion.IsFreeChoice := by decide

/-! ### Soundness of workflow nets

The smallest workflow: a single transition moves the token from the source `false` to the sink
`true`. -/

/-- A workflow net with one transition from the source `false` to the sink `true`. -/
def step : PetriNet Bool Unit where
  pre _ := {false}
  post _ := {true}

theorem step_fires : (token false) [()⟩[step] token true :=
  ⟨0, rfl, rfl⟩

/-- From the source, only the markings with a single token in the source or in the sink are
reachable. -/
theorem step_reachable (M : Marking Bool) (h : token false ⇝[step] M) :
    M = token false ∨ M = token true := by
  refine h.invariant (P := fun K => K = token false ∨ K = token true) ?_ (Or.inl rfl)
  rintro K u K' ⟨R, rfl, rfl⟩ hK
  rcases hK with hK | hK
  · have hR : R = 0 := add_eq_left.1 hK
    subst hR
    simp [token, step]
  · have := congrArg (false ∈ ·) hK
    simp [token, step] at this

theorem step_sound : step.Sound false true where
  completion M h := by
    rcases step_reachable M h with rfl | rfl
    · exact step_fires.reachable
    · exact Reachable.refl _ _
  proper M h hle := by
    rcases step_reachable M h with rfl | rfl
    · exact absurd hle (by decide)
    · rfl
  noDead _ := ⟨token false, Reachable.refl _ _, le_rfl⟩

/-- The net is a workflow net: every node lies on a path from the source to the sink. -/
theorem step_wf : step.IsWFNet false true where
  no_input_source _ := by simp [step]
  no_output_sink _ := by simp [step]
  reach_from_source n := by
    have a₁ : step.Arc (.inl false) (.inr ()) := by simp [Arc, step]
    have a₂ : step.Arc (.inr ()) (.inl true) := by simp [Arc, step]
    rcases n with (_ | _) | _
    · exact .refl
    · exact .head a₁ (.single a₂)
    · exact .single a₁
  reach_to_sink n := by
    have a₁ : step.Arc (.inl false) (.inr ()) := by simp [Arc, step]
    have a₂ : step.Arc (.inr ()) (.inl true) := by simp [Arc, step]
    rcases n with (_ | _) | _
    · exact .head a₁ (.single a₂)
    · exact .refl
    · exact .single a₂

/-- Soundness implies the weaker notions. -/
example : step.WeakSound false true := step_sound.weak

example : step.RelaxedSound false true := step_sound.relaxed

example : step.EasySound false true := step_sound.weak.easy

example : step.LazySound false true := .of_weak (fun _ => by simp [step]) step_sound.weak

/-- In a workflow net, soundness is weak soundness without dead transitions. -/
example : step.Sound false true ↔ step.WeakSound false true ∧
    ∀ t, ∃ M, token false ⇝[step] M ∧ M [t⟩[step] :=
  step_wf.sound_iff

/-- Van der Aalst's theorem: the short-circuited net is live and bounded. -/
example : (step.shortCircuit false true).Live (token false) ∧
    (step.shortCircuit false true).Bounded (token false) :=
  sound_iff_live_and_bounded.1 step_sound

/-- A sound net over finitely many places and transitions is bounded. -/
example : step.Bounded (token false) := step_sound.bounded_net

/-- Generalized soundness is refuted by a failure of `k`-soundness for some `k`. -/
example (h : ¬ step.KSound false true 3) : ¬ step.GeneralizedSound false true :=
  not_generalizedSound_of_not_kSound h

/-! ### Firing languages as automata -/

/-- Every firing language of the (bounded) producer/consumer net is regular. -/
example (F : Set (Marking Pl)) : (prodCons.firingLanguage M₀ F).IsRegular :=
  isRegular_firingLanguage (prodCons_conservative.kBounded _).bounded F

/-- The sequence `produce, produce, consume` leads from `M₀` to `{buffer, consuming}`. -/
example : [produce, produce, consume] ∈ prodCons.firingLanguage M₀ {{buffer, consuming}} := by
  have h₁ : M₀ [produce⟩[prodCons] {producing, buffer} := by decide
  have h₂ : ({producing, buffer} : Marking Pl) [produce⟩[prodCons] {buffer, buffer} := by decide
  have h₃ : ({buffer, buffer} : Marking Pl) [consume⟩[prodCons] {buffer, consuming} := by decide
  exact ⟨_, rfl, .stepL h₁ (.stepL h₂ (.single _ h₃))⟩

/-- The sequence `[consume]` is not even firable from `M₀`. -/
example : [consume] ∉ prodCons.firingLanguage M₀ {{buffer, consuming}} := by
  rintro ⟨M, -, h⟩
  cases h with
  | stepL htr _ => exact absurd (fires_iff.1 htr).1 (by decide)

/-! ### Behavioural equivalence -/

/-- A marking with no `producing` and no `buffer` token is dead. -/
theorem prodCons_dead (M : Marking Pl) (h₁ : producing ∉ M) (h₂ : buffer ∉ M) :
    prodCons.Dead M := by
  rw [dead_iff]
  intro t h
  cases t
  · exact h₁ (Multiset.mem_of_le h (Multiset.mem_singleton_self _))
  · exact h₂ (Multiset.mem_of_le h (Multiset.mem_singleton_self _))

theorem dead_one : prodCons.Dead {consuming} :=
  prodCons_dead _ (by simp) (by simp)

theorem dead_two : prodCons.Dead {consuming, consuming} :=
  prodCons_dead _ (by simp) (by simp)

open LTS in
/-- The markings with one and with two `consuming` tokens are different but bisimilar. -/
example : ∃ M₁ M₂ : Marking Pl, M₁ ≠ M₂ ∧ (M₁ ~[prodCons.lts] M₂) :=
  ⟨{consuming}, {consuming, consuming}, by decide, bisimilar_of_dead _ dead_one dead_two⟩

/-- Bisimilar markings have the same traces. -/
example : prodCons.lts.traces {consuming} = prodCons.lts.traces {consuming, consuming} :=
  (bisimilar_iff_traces_eq _ _ _).1 (bisimilar_of_dead _ dead_one dead_two)

open Logic.Modal in
/-- Bisimilar dead markings satisfy the same Hennessy-Milner formulas. -/
example : TheoryEq (HML.Model.mk prodCons.lts (fun _ (_ : Unit) => True)).toModal
    {consuming} {consuming, consuming} :=
  (theoryEq_iff_bisimilar prodCons _ (fun _ _ => Iff.rfl) _ _).2
    (bisimilar_of_dead _ dead_one dead_two)

/-! ### Firing languages, decided -/

/-- Membership in a firing language is decided by running the net. -/
example : [produce, produce, consume] ∈ prodCons.firingLanguage M₀ {{buffer, consuming}} := by
  decide

example : [consume] ∉ prodCons.firingLanguage M₀ {{buffer, consuming}} := by decide

example : [produce] ∉ prodCons.firingLanguage M₀ {{buffer, consuming}} := by decide

/-! ### Reachability and deadlocks of bounded nets -/

/-- The ring reaches all its markings within two steps. -/
example : ring.Closed {producing} 2 := by decide

/-- For bounded nets, reachability and deadlock reachability are decided once boundedness is
available as a `Fact`. -/
instance : Fact (ring.Bounded {producing}) := ⟨by decide⟩

instance : Fact (prodCons.Bounded M₀) := ⟨by decide⟩

example : ({producing} : Marking Pl) ⇝[ring] {consuming} := by decide

/-- A second token cannot appear in the ring. -/
example : ¬ ({producing} : Marking Pl) ⇝[ring] {producing, producing} := by decide

/-- The ring never reaches a dead marking, as Commoner's criterion also shows. -/
example : ¬ ∃ M, {producing} ⇝[ring] M ∧ ring.Dead M := by decide

/-- The producer/consumer net with two producers reaches a dead marking. -/
example : ∃ M, M₀ ⇝[prodCons] M ∧ prodCons.Dead M := by decide

/-! ### Decidable soundness -/

/-- A workflow in which `produce` leaves a token in `buffer` besides finishing the case. -/
def leaky : PetriNet Pl Tr where
  pre | produce => {producing} | consume => {buffer}
  post | produce => {buffer, consuming} | consume => {consuming}

/-- Soundness is decided outright, in both directions. The leaky workflow is unsound: after
`produce`, the sink is marked but so is `buffer`. -/
example : prodCons.Sound producing consuming := by decide

example : ¬ leaky.Sound producing consuming := by decide

/-- An unbounded net is never sound; the decision finds the pumping pair. -/
example : ¬ source.Sound () () := by decide

/-- A single token circulating in the ring can always be moved to any place, so the ring is sound
for every choice of source and sink. -/
example : ring.Sound producing buffer := by decide

/-- By van der Aalst's theorem, the short circuit of the sound workflow is live and bounded. -/
example : (prodCons.shortCircuit producing consuming).Live (token producing) ∧
    (prodCons.shortCircuit producing consuming).Bounded (token producing) :=
  sound_iff_live_and_bounded.1 (by decide)

/-! ### Notions of soundness -/

open Pl4 Tr5 in
/-- A net with a bad branch: `a` splits the case into `p` and `q`, after which `b` completes
without `q`, leaving a token behind, while `e` completes properly. The other route `c; b` is
fine. -/
def choiceNet : PetriNet Pl4 Tr5 where
  pre | .a => {.i} | .b => {.p} | .c => {.i} | .d => {.q} | .e => {.p, .q}
  post | .a => {.p, .q} | .b => {.o} | .c => {.p} | .d => {.q} | .e => {.o}

open Pl4 Tr5 in
/-- A net that is sound for one token in `i` apart from the dead transition `e`, and that is not
sound for two tokens: `e` merges the two branches into a single token. -/
def joinNet : PetriNet Pl4 Tr5 where
  pre | .a => {.i} | .b => {.p} | .c => {.i} | .d => {.q} | .e => {.p, .q}
  post | .a => {.p} | .b => {.o} | .c => {.q} | .d => {.o} | .e => {.o}

instance : Fact (choiceNet.Bounded (token Pl4.i)) := ⟨by decide⟩

instance : Fact (joinNet.Bounded (token Pl4.i)) := ⟨by decide⟩

instance : Fact (joinNet.Bounded (2 • token Pl4.i)) := ⟨by decide⟩

instance : Fact (prodCons.Bounded (token producing)) := ⟨by decide⟩

instance : Fact (prodCons.Bounded (2 • token producing)) := ⟨by decide⟩

/-- The choice net is relaxed sound, lazy sound and easy sound, but neither weakly nor classically
sound. -/
example : choiceNet.RelaxedSound Pl4.i Pl4.o := by decide

example : choiceNet.LazySound Pl4.i Pl4.o := by decide

example : choiceNet.EasySound Pl4.i Pl4.o := by decide

example : ¬ choiceNet.WeakSound Pl4.i Pl4.o := by decide

example : ¬ choiceNet.Sound Pl4.i Pl4.o := by decide

/-- The join net is weakly sound but has a dead transition, and is not `2`-sound. -/
example : joinNet.WeakSound Pl4.i Pl4.o := by decide

example : ¬ joinNet.Sound Pl4.i Pl4.o := by decide

example : ¬ joinNet.RelaxedSound Pl4.i Pl4.o := by decide

example : ¬ joinNet.KSound Pl4.i Pl4.o 2 := by decide

example : ¬ joinNet.UpToKSound Pl4.i Pl4.o 2 := by decide

/-- Generalized soundness is refuted by a `k` for which the net is not `k`-sound: the join net is
not generalized sound since it is not `2`-sound, and the choice net since it is not weakly
sound. -/
example : ¬ joinNet.GeneralizedSound Pl4.i Pl4.o :=
  not_generalizedSound_of_not_upToKSound (k := 2) (by decide)

example : ¬ choiceNet.GeneralizedSound Pl4.i Pl4.o := fun h => absurd h.weak (by decide)

/-- The producer/consumer net is sound, and `1`- and `2`-sound. -/
example : prodCons.KSound producing consuming 2 := by decide

example : prodCons.UpToKSound producing consuming 2 := by decide

example : prodCons.LazySound producing consuming := by decide

/-- A weakly sound net is lazy sound, as the sink has no output transition, and a sound net is
weakly and relaxed sound. -/
example : prodCons.LazySound producing consuming :=
  LazySound.of_weak (fun t => by cases t <;> decide) (by decide)

example : prodCons.RelaxedSound producing consuming :=
  Sound.relaxed (by decide)

/-- The producer/consumer net is a workflow net, which `decide` checks by computing reachability in
its flow graph. -/
theorem prodCons_wf : prodCons.IsWFNet producing consuming := by decide

/-- The producer/consumer net with the sink and source swapped is not a workflow net. -/
example : ¬ prodCons.IsWFNet consuming producing := by decide

/-- The nets of the previous examples are workflow nets too. -/
example : choiceNet.IsWFNet Pl4.i Pl4.o := by decide

example : joinNet.IsWFNet Pl4.i Pl4.o := by decide

/-- Hence proper completion follows from the option to complete, which `decide` establishes. -/
example : ∀ M, prodCons.Reachable (token producing) M → token consuming ≤ M →
    M = token consuming :=
  prodCons_wf.proper_of_completion (weakSound_iff.1 (by decide))

/-! ### Temporal logics -/

section CTL

open Cslib.Logic Cslib.Logic.CTL
open scoped Cslib.Logic.InferenceSystem Cslib.Logic.CTL.Formula

instance : Fact (ring.Bounded {buffer}) := ⟨by decide⟩

/-- Reachability is `EF`: the token of the ring can be moved to the buffer. -/
example : ⇓CTL[ring.model,{producing} ⊨ EF (marked {buffer})] := by decide

example : ¬ ⇓CTL[ring.model,{producing} ⊨ EF (marked {producing, producing})] := by
  decide

/-- The ring is deadlock-free, and every transition stays reachable: the ring is live. Both are
`AG` formulas, decided on the finite model. -/
example : ⇓CTL[ring.model,{producing} ⊨ AG (¬Formula.deadlock)] := by decide

example : ∀ t : Tr3,
    ⇓CTL[ring.model,{producing} ⊨ AG (EF (.atom (Atom.enabled t)))] := by decide

/-- By the translation of liveness to CTL, the ring is live. -/
example : ring.Live {producing} := fun t =>
  liveAt_iff.2 (by revert t; decide)

/-- The same holds of the deadlock-freeness. -/
example : ∀ M, {producing} ⇝[ring] M → ¬ ring.Dead M :=
  deadlockFree_iff_ag.2 (by decide)

/-- The producer/consumer net with two producers reaches a deadlock, so it is not deadlock-free,
and it is not live since its transitions cannot be re-enabled. -/
example : ⇓CTL[prodCons.model,M₀ ⊨ EF Formula.deadlock] := by decide

example : ¬ ∀ M, M₀ ⇝[prodCons] M → ¬ prodCons.Dead M :=
  fun h => absurd (deadlockFree_iff_ag.1 h) (by decide)

example : ¬ prodCons.LiveAt M₀ produce :=
  fun h => absurd (liveAt_iff.1 h) (by decide)

/-- Soundness is `AG EF`: the join net is weakly sound, and the choice net is not. -/
example : joinNet.WeakSound Pl4.i Pl4.o := by
  rw [WeakSound, kSound_iff, one_smul, one_smul]
  decide

example : ¬ choiceNet.WeakSound Pl4.i Pl4.o := by
  rw [WeakSound, kSound_iff, one_smul, one_smul]
  decide

end CTL

section LTL

open Cslib.Logic.LTL
open scoped Cslib.Logic.InferenceSystem Cslib.Logic.LTL.Formula

/-- The formula saying that the marking is exactly `M`. -/
abbrev here {Pl Tr : Type} (M : Marking Pl) : Formula (Atom Pl Tr) := .atom (.marking M)

/-- The token of the ring visits the buffer infinitely often. This is `G F`, which CTL cannot
express without fairness, but there is a single path here. -/
example : ⇓LTL[ring.model,{producing} ⊨∀
    G F (here (Tr := Tr3) {buffer})] := by decide

example : ¬ ⇓LTL[ring.model,{producing} ⊨∀
    F G (here (Tr := Tr3) {buffer})] := by decide

/-- Every maximal run of the producer/consumer net with two items ends in the dead marking where
both are consumed, and stays there. -/
example : ⇓LTL[prodCons.model,M₀ ⊨∀
    F G (here (Tr := Tr) {consuming, consuming})] := by decide

/-- The nets are not deadlock-free, and the first transition fires first on some run. -/
example : ⇓LTL[prodCons.model,M₀ ⊨∃
    X (here (Tr := Tr) {producing, buffer})] := by decide

example : ¬ ⇓LTL[prodCons.model,M₀ ⊨∃
    X (here (Tr := Tr) {buffer, buffer, buffer})] := by decide

end LTL

end CslibTests
