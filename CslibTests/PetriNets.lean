/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.Automaton
import Cslib.Computability.PetriNets.BackwardCoverability
import Cslib.Computability.PetriNets.Basic
import Cslib.Computability.PetriNets.Coverability
import Cslib.Computability.PetriNets.CoverabilityBasis
import Cslib.Computability.PetriNets.Equivalence
import Cslib.Computability.PetriNets.Executable
import Cslib.Computability.PetriNets.ExecutableBoundedness
import Cslib.Computability.PetriNets.ExecutableCoverability
import Cslib.Computability.PetriNets.ExecutableForward
import Cslib.Computability.PetriNets.ExecutableLanguage
import Cslib.Computability.PetriNets.ExecutableReachability
import Cslib.Computability.PetriNets.ExecutableSoundness
import Cslib.Computability.PetriNets.ExecutableSoundnessNotions
import Cslib.Computability.PetriNets.ExecutableStructure
import Cslib.Computability.PetriNets.FreeChoice
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
  pre | produce => ⦅producing⦆ | consume => ⦅buffer⦆
  post | produce => ⦅buffer⦆ | consume => ⦅consuming⦆

/-! ### Notation -/

-- Markings given by multiset literals, and the enabling, firing and reachability notation, are
-- pretty-printed with the notation.

/-- info: ⦅producing, buffer⦆ : Pl →₀ ℕ -/
#guard_msgs in
#check (⦅producing, buffer⦆ : Marking Pl)

/-- info: ⦅⦆ : Pl →₀ ℕ -/
#guard_msgs in
#check (⦅⦆ : Marking Pl)

/-- info: ⦅producing⦆ [produce⟩[prodCons] ⦅buffer⦆ : Prop -/
#guard_msgs in
#check ⦅producing⦆ [produce⟩[prodCons] ⦅buffer⦆

/-- info: ⦅producing⦆ ⇝[prodCons] ⦅consuming⦆ : Prop -/
#guard_msgs in
#check ⦅producing⦆ ⇝[prodCons] ⦅consuming⦆

/-- The preset and postset of `produce`. -/
example : •[prodCons] produce = ⦅producing⦆ := rfl

example : produce •[prodCons] = ⦅buffer⦆ := rfl

/-! ### Enabling and firing -/

example : ⦅producing⦆ [produce⟩[prodCons] := le_rfl

example : ¬ ⦅producing⦆ [consume⟩[prodCons] := by
  intro h
  have := h buffer
  simp [prodCons] at this

/-- Firing moves the token; the tokens not consumed (here the extra `consuming` token) stay. -/
example : ⦅producing, consuming⦆ [produce⟩[prodCons] ⦅buffer, consuming⦆ :=
  ⟨⦅consuming⦆, by ext p; cases p <;> simp [prodCons, Multiset.toFinsupp_apply],
    by ext p; cases p <;> simp [prodCons, Multiset.toFinsupp_apply]⟩

/-- Firing is the explicit rule `M - pre + post`. -/
example : prodCons.fire ⦅producing, consuming⦆ produce = ⦅buffer, consuming⦆ := by
  have h : ⦅producing, consuming⦆ [produce⟩[prodCons] ⦅buffer, consuming⦆ :=
    ⟨⦅consuming⦆, by ext p; cases p <;> simp [prodCons, Multiset.toFinsupp_apply],
    by ext p; cases p <;> simp [prodCons, Multiset.toFinsupp_apply]⟩
  exact (fires_iff.1 h).2.symm

/-! ### Reachability and boundedness -/

example : ⦅producing⦆ ⇝[prodCons] ⦅consuming⦆ := by
  have h₁ : ⦅producing⦆ [produce⟩[prodCons] ⦅buffer⦆ := ⟨0, by simp [prodCons], by simp [prodCons]⟩
  have h₂ : ⦅buffer⦆ [consume⟩[prodCons] ⦅consuming⦆ := ⟨0, by simp [prodCons], by simp [prodCons]⟩
  exact h₁.reachable.trans h₂.reachable

/-- Both transitions consume and produce one token, so the net is conservative. -/
theorem prodCons_conservative : prodCons.Conservative := by
  intro t
  cases t <;> simp [prodCons, Marking.size]

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
example : prodCons.Dead ⦅consuming⦆ := by
  rw [dead_iff]
  intro t h
  cases t
  · simpa [prodCons] using h producing
  · simpa [prodCons] using h buffer

/-! ### Monotonicity -/

theorem fires_produce : ⦅producing⦆ [produce⟩[prodCons] ⦅buffer⦆ :=
  ⟨0, by simp [prodCons], by simp [prodCons]⟩

theorem fires_consume : ⦅buffer⦆ [consume⟩[prodCons] ⦅consuming⦆ :=
  ⟨0, by simp [prodCons], by simp [prodCons]⟩

/-- Extra tokens never disable a transition. -/
example : ⦅producing, consuming⦆ [produce⟩[prodCons] :=
  (show ⦅producing⦆ [produce⟩[prodCons] from le_rfl).mono (by
    intro p; cases p <;> simp [Multiset.toFinsupp_apply])

/-- A firing sequence can be replayed from a larger marking, reaching a larger marking. -/
example : ∃ M', prodCons.lts.MTr ⦅producing, consuming⦆ [produce] M' ∧ ⦅buffer⦆ ≤ M' :=
  mTr_mono (.single _ fires_produce) (by
    intro p; cases p <;> simp [Multiset.toFinsupp_apply])

/-- The net is bounded at every marking, hence at the smaller marking `⦅producing⦆`. -/
example : prodCons.Bounded ⦅producing⦆ :=
  (prodCons_conservative.kBounded _).bounded

/-! ### Coverability and unboundedness -/

/-- A source transition that creates a token from nothing. -/
noncomputable def source : PetriNet Unit Unit where
  pre _ := 0
  post _ := Finsupp.single () 1

theorem source_fires (M : Marking Unit) : M [()⟩[source] (M + Finsupp.single () 1) :=
  ⟨M, by simp [source], by simp [source]⟩

/-- The source net is unbounded, by pumping from the empty marking. -/
theorem source_unbounded : ¬ source.Bounded 0 :=
  not_bounded_of_pump (.refl _ _) (source_fires 0).reachable (by
    simp only [zero_add]
    exact lt_of_le_of_ne bot_le (fun h => by simpa using DFunLike.congr_fun h ()))

/-- By the characterisation of unbounded nets, the source net has a pumping pair. -/
example : ∃ M₁ M₂, 0 ⇝[source] M₁ ∧ M₁ ⇝[source] M₂ ∧ M₁ < M₂ :=
  exists_pump_of_not_bounded source_unbounded

/-- The producer/consumer net is bounded, so no reachable marking can be pumped. -/
example (M₀ : Marking Pl) : ¬ ∃ M₁ M₂, M₀ ⇝[prodCons] M₁ ∧ M₁ ⇝[prodCons] M₂ ∧ M₁ < M₂ :=
  bounded_iff_no_pump.1 (prodCons_conservative.kBounded _).bounded

/-- Every marking is coverable from every marking in the source net. -/
theorem source_coverable (M₀ M : Marking Unit) : source.Coverable M₀ M := by
  have hreach : ∀ n : ℕ, M₀ ⇝[source] (M₀ + n • Finsupp.single () 1) := by
    intro n
    induction n with
    | zero => simpa using Reachable.refl source M₀
    | succ n ih =>
      refine ih.trans (Fires.reachable (t := ()) ?_)
      have := source_fires (M₀ + n • Finsupp.single () 1)
      rwa [succ_nsmul, ← add_assoc]
  exact ⟨_, hreach (M ()), fun u => by simp⟩

/-- Hence every finite basis for coverability on the source net contains the empty marking. -/
example (M : Marking Unit) : ∃ B : Set (Marking Unit), B.Finite ∧ (0 : Marking Unit) ∈ B ∧
    ∀ M₀, source.Coverable M₀ M ↔ ∃ b ∈ B, b ≤ M₀ := by
  obtain ⟨B, hB, hiff⟩ := exists_finite_basis_coverable (N := source) M
  obtain ⟨b, hb, hb0⟩ := (hiff 0).1 (source_coverable 0 M)
  have hb' : b = 0 := le_antisymm hb0 bot_le
  exact ⟨B, hB, hb' ▸ hb, hiff⟩

/-- Backward coverability on the producer/consumer net: `⦅buffer⦆` is a predecessor of the target
`⦅consuming⦆` after one step, and `⦅producing⦆` after two. -/
theorem producing_mem_backSeq : ⦅producing⦆ ∈ prodCons.backSeq ⦅consuming⦆ 2 := by
  have h1 : ⦅buffer⦆ ∈ prodCons.backSeq ⦅consuming⦆ 1 := by
    rw [backSeq_succ]
    exact Or.inr ⟨consume, _, fires_consume, show _ ∈ Set.Ici _ from Set.mem_Ici.2 le_rfl⟩
  rw [backSeq_succ]
  exact Or.inr ⟨produce, _, fires_produce, h1⟩

example : prodCons.Coverable ⦅producing⦆ ⦅consuming⦆ :=
  coverable_of_mem_backSeq producing_mem_backSeq

/-- The backward iteration reaches a fixpoint that is exactly the coverable markings. -/
example : ∃ n, prodCons.backStep (prodCons.backSeq ⦅consuming⦆ n) = prodCons.backSeq ⦅consuming⦆ n ∧
    ∀ M₀, prodCons.Coverable M₀ ⦅consuming⦆ ↔ M₀ ∈ prodCons.backSeq ⦅consuming⦆ n :=
  exists_backSeq_fixpoint _

/-! ### Executable nets

An `ExecPetriNet` has multisets as arc weights, so firing is computable and the properties of the
net can be decided. -/

/-- The producer/consumer net with multisets as arc weights. -/
def prodConsExec : ExecPetriNet Pl Tr where
  pre | produce => {producing} | consume => {buffer}
  post | produce => {buffer} | consume => {consuming}

/-- It is the same net as `prodCons`. -/
example : prodConsExec.toPetriNet = prodCons := by
  have h : ∀ t, prodConsExec.toPetriNet.pre t = prodCons.pre t ∧
      prodConsExec.toPetriNet.post t = prodCons.post t := by
    intro t; cases t <;> exact ⟨rfl, rfl⟩
  cases h₁ : prodConsExec.toPetriNet
  cases h₂ : prodCons
  simp only [PetriNet.mk.injEq]
  constructor <;> funext t <;> [have := (h t).1; have := (h t).2] <;> simp_all

/-- Two items in the system, as a multiset. -/
def Mx : Multiset Pl := {producing, producing}

example : prodConsExec.enabled Mx produce = true := by decide
example : prodConsExec.enabled Mx consume = false := by decide

example : (prodConsExec.run Mx [produce, consume]).isSome = true := by decide
example : (prodConsExec.run Mx [consume]).isNone = true := by decide
example :
    prodConsExec.run Mx [produce, produce, consume] = some ({buffer, consuming} : Multiset Pl) := by
  decide

/-- The computable run is witnessed in the weighted semantics, with the net given to the notation as
an executable net. -/
example : Mx [produce⟩[prodConsExec] ⦅producing, buffer⦆ :=
  ExecPetriNet.fires_iff.2 (by decide)

/-- Enabledness of a transition at a marking given by a multiset. -/
example : ⦅producing⦆ [produce⟩[prodConsExec] :=
  ExecPetriNet.enabled_toPetriNet_iff.2 (by decide)

/-- Reachability and its notation, for an executable net. -/
example : ⦅producing⦆ ⇝[prodConsExec] ⦅consuming⦆ := by
  have h₁ : ⦅producing⦆ [produce⟩[prodConsExec] ⦅buffer⦆ := ExecPetriNet.fires_iff.2 (by decide)
  have h₂ : ⦅buffer⦆ [consume⟩[prodConsExec] ⦅consuming⦆ := ExecPetriNet.fires_iff.2 (by decide)
  exact h₁.reachable.trans h₂.reachable

/-! ### Decidable coverability -/

/-- The backward iteration from `{consuming}` has stabilised after two steps. -/
example : prodConsExec.Stable (prodConsExec.basisSeq {consuming} 2) := by decide

/-- `{producing}` can cover `{consuming}`. -/
example : prodConsExec.toPetriNet.Coverable ⦅producing⦆ ⦅consuming⦆ := by decide

/-- The empty marking cannot cover `{consuming}`. -/
example : ¬ prodConsExec.toPetriNet.Coverable ⦅⦆ ⦅consuming⦆ := by decide

/-! ### Decidable boundedness -/

/-- The reachable markings of the producer/consumer net from `Mx` stop growing after four steps. -/
example : prodConsExec.Closed Mx 4 := by decide

/-- A source transition that creates a token from nothing, as an executable net. -/
def sourceExec : ExecPetriNet Unit Unit where
  pre _ := 0
  post _ := {()}

/-- The source net has a pumping pair already within one step. -/
example : sourceExec.PumpWithin 0 1 := by decide

/-- Boundedness is decided outright, in both directions. -/
example : prodConsExec.toPetriNet.Bounded Mx := by decide

example : ¬ sourceExec.toPetriNet.Bounded ⦅⦆ := by decide
/-! ### The state equation -/
/-! ### Firing languages as automata -/

/-- Two items in the system. -/
def M₀ : Marking Pl := ⦅producing, producing⦆

/-- Firing never produces tokens in `producing`. -/
theorem prodCons_incidence_producing (t : Tr) : prodCons.incidence t producing ≤ 0 := by
  cases t <;> simp [incidence, Marking.toInt, prodCons]

theorem prodCons_effect_producing (ts : List Tr) : prodCons.effect ts producing ≤ 0 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [effect_cons, Finsupp.add_apply]
    have := prodCons_incidence_producing t
    omega

/-- By the state equation, no marking with more `producing` tokens than `M₀` is reachable. -/
example (M : Marking Pl) (h : 2 < M producing) : ¬ M₀ ⇝[prodCons] M := by
  intro hr
  obtain ⟨ts, hts⟩ := hr.exists_toInt_eq
  have h1 := congrArg (fun f => f producing) hts
  have h2 := prodCons_effect_producing ts
  simp [Marking.toInt, M₀, Multiset.toFinsupp_apply] at h1
  omega

/-! ### Place invariants -/

/-- Two `a` tokens are merged into one `b` token, so `a` has weight `1` and `b` has weight `2`. -/
inductive Pl2 | a | b
  deriving DecidableEq

instance : Fintype Pl2 := ⟨{.a, .b}, fun x => by cases x <;> simp⟩

def merge : PetriNet Pl2 Unit where
  pre _ := ⦅.a, .a⦆
  post _ := ⦅.b⦆

def mergeWeight : Pl2 → ℕ | .a => 1 | .b => 2

theorem merge_invariant : merge.IsInvariant mergeWeight := by
  intro t
  change Marking.weight mergeWeight ⦅.a, .a⦆ = Marking.weight mergeWeight ⦅.b⦆
  rw [Marking.weight_toFinsupp, Marking.weight_toFinsupp]
  simp [mergeWeight]

/-- A positive invariant bounds the net at every marking. -/
example (M₀ : Marking Pl2) : merge.Bounded M₀ :=
  merge_invariant.bounded (by intro p; cases p <;> simp [mergeWeight]) M₀

/-- The merge net is not conservative, although it has an invariant. -/
example : ¬ merge.Conservative := by
  rw [conservative_iff_isInvariant]
  intro h
  have := h ()
  change Marking.weight (fun _ => 1) ⦅Pl2.a, Pl2.a⦆ = Marking.weight (fun _ => 1) ⦅Pl2.b⦆ at this
  rw [Marking.weight_toFinsupp, Marking.weight_toFinsupp] at this
  simp at this

/-! ### Siphons and traps -/

/-- In the producer/consumer net, `producing` is a siphon (nothing produces into it) and
`consuming` is a trap (nothing consumes from it). -/
theorem prodCons_siphon : prodCons.IsSiphon {producing} := by
  rintro t ⟨p, rfl, hpos⟩
  cases t <;> simp [prodCons] at hpos

theorem prodCons_trap : prodCons.IsTrap {consuming} := by
  rintro t ⟨p, rfl, hpos⟩
  cases t <;> simp [prodCons] at hpos

/-- With no `producing` token, none can ever appear. -/
example (M M' : Marking Pl) (h : M ⇝[prodCons] M') (hM : M producing = 0) :
    M' producing = 0 := by
  have := prodCons_siphon.unmarked_of_reachable h (fun ⟨p, hp, hpos⟩ => by
    simp only [Set.mem_singleton_iff] at hp; subst hp; omega)
  by_contra hne
  exact this ⟨producing, rfl, Nat.pos_of_ne_zero hne⟩

/-- A two-place cycle: `false` moves a token from place `false` to place `true`, and `true`
moves it back. -/
def cycleNet : PetriNet Bool Bool where
  pre t := ⦅t⦆
  post t := ⦅!t⦆

theorem cycleNet_ordinary : cycleNet.Ordinary := by
  intro t p
  cases t <;> cases p <;> simp [cycleNet]

/-- The firing sequence `[false, true]` of the cycle net has total effect zero, so it returns to
its starting marking from every marking where it can fire. -/
example (M M' : Marking Bool) (h : cycleNet.lts.MTr M [false, true] M') : M' = M := by
  refine (mTr_eq_iff_effect_eq_zero h).2 ?_
  ext p
  cases p <;> simp [effect, incidence, Marking.toInt, cycleNet]

/-! ### Structure of executable nets

The structural properties of executable nets are decidable. -/

/-- The producer/consumer net is ordinary, free-choice and conservative. -/
example : prodConsExec.toPetriNet.Ordinary := by decide

example : prodConsExec.toPetriNet.IsFreeChoice := by decide

example : prodConsExec.toPetriNet.Conservative := by decide

/-! ### Free-choice nets and Commoner's theorem -/

inductive Tr3 | a | b | c
  deriving DecidableEq

instance : Fintype Tr3 := ⟨{Tr3.a, Tr3.b, Tr3.c}, fun x => by cases x <;> simp⟩

/-- The producer/consumer net closed into a ring by a transition returning the token. -/
def ring : ExecPetriNet Pl Tr3 where
  pre | .a => {producing} | .b => {buffer} | .c => {consuming}
  post | .a => {buffer} | .b => {consuming} | .c => {producing}

/-- The hypotheses of Commoner's criterion are all decided: the ring is ordinary and free-choice,
and every nonempty siphon contains a trap marked at the initial marking. Hence the ring is live. -/
example : ring.toPetriNet.Ordinary := by decide

example : ring.toPetriNet.IsFreeChoice := by decide

example : ring.toPetriNet.SiphonTrap ⦅producing⦆ := by decide

example : ring.toPetriNet.Live ⦅producing⦆ :=
  live_of_siphons_contain_marked_trap (by decide) (by decide) (by decide)

/-- Commoner's theorem for the ring: it is live exactly when it has the siphon-trap property. -/
example : ring.toPetriNet.Live ⦅producing⦆ :=
  (live_iff_siphonTrap (by decide) (by decide) (by decide)).2 (by decide)

inductive Pl4 | i | p | q | o
  deriving DecidableEq

instance : Fintype Pl4 := ⟨{.i, .p, .q, .o}, fun x => by cases x <;> simp⟩

inductive Tr5 | a | b | c | d | e
  deriving DecidableEq

instance : Fintype Tr5 := ⟨{.a, .b, .c, .d, .e}, fun x => by cases x <;> simp⟩

/-- A free-choice net in which the token on the cycle `i → p → q → i` may escape through `d` to a
place `o` that only loops. -/
def escapeNet : ExecPetriNet Pl4 Tr5 where
  pre | .a => {.i} | .b => {.p} | .c => {.q} | .d => {.p} | .e => {.o}
  post | .a => {.p} | .b => {.q} | .c => {.i} | .d => {.o} | .e => {.o}

/-- The escape net is not live. Reachability alone would not show this easily, but the converse of
Commoner's theorem reduces it to a finite check: the siphon `{i, p, q}` contains no trap. -/
example : ¬ escapeNet.toPetriNet.Live ⦅Pl4.i⦆ := fun hl =>
  (by decide : ¬ escapeNet.toPetriNet.SiphonTrap ⦅Pl4.i⦆)
    (siphonTrap_of_live (by decide) (by decide) hl (by decide))

/-- Without a token, the siphon-trap property fails: the empty marking marks no trap. -/
example : ¬ ring.toPetriNet.SiphonTrap ⦅⦆ := by decide

/-- Two transitions sharing `producing` but with different presets break free choice. -/
def confusion : ExecPetriNet Pl Tr where
  pre | produce => {producing} | consume => {producing, buffer}
  post | produce => {buffer} | consume => {consuming}

example : ¬ confusion.toPetriNet.IsFreeChoice := by decide
/-! ### Soundness of workflow nets

The smallest workflow: a single transition moves the token from the source `false` to the sink
`true`. -/

/-- A workflow net with one transition from the source `false` to the sink `true`. -/
noncomputable def step : PetriNet Bool Unit where
  pre _ := Finsupp.single false 1
  post _ := Finsupp.single true 1

theorem step_fires : (token false) [()⟩[step] token true :=
  ⟨0, by simp [token, step], by simp [token, step]⟩

/-- From the source, only the markings with a single token in the source or in the sink are
reachable. -/
theorem step_reachable (M : Marking Bool) (h : token false ⇝[step] M) :
    M = token false ∨ M = token true := by
  refine h.invariant (P := fun K => K = token false ∨ K = token true) ?_ (Or.inl rfl)
  rintro K u K' ⟨R, rfl, rfl⟩ hK
  rcases hK with hK | hK
  · have hR : R = 0 := by simpa [token, step] using hK
    subst hR
    simp [token, step]
  · have := DFunLike.congr_fun hK false
    simp [token, step] at this

theorem step_sound : step.Sound false true where
  completion M h := by
    rcases step_reachable M h with rfl | rfl
    · exact step_fires.reachable
    · exact Reachable.refl _ _
  proper M h hle := by
    rcases step_reachable M h with rfl | rfl
    · have := hle true
      simp [token] at this
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
/-- Every firing language of the (bounded) producer/consumer net is regular. -/
example (F : Set (Marking Pl)) : (prodCons.firingLanguage M₀ F).IsRegular :=
  isRegular_firingLanguage (prodCons_conservative.kBounded _).bounded F

/-- The sequence `produce, produce, consume` leads from `M₀` to `⦅buffer, consuming⦆`. -/
example : [produce, produce, consume] ∈ prodCons.firingLanguage M₀ {⦅buffer, consuming⦆} := by
  refine ⟨⦅buffer, consuming⦆, rfl, ?_⟩
  refine .stepL (μ := produce) (s2 := ⦅producing, buffer⦆) ⟨⦅producing⦆, ?_, ?_⟩
    (.stepL (μ := produce) (s2 := ⦅buffer, buffer⦆) ⟨⦅buffer⦆, ?_, ?_⟩
      (.single _ (show ⦅buffer, buffer⦆ [consume⟩[prodCons] ⦅buffer, consuming⦆ from
        ⟨⦅buffer⦆, ?_, ?_⟩)))
  all_goals ext p; cases p <;> simp [M₀, prodCons, Multiset.toFinsupp_apply]

/-- The sequence `[consume]` is not even firable from `M₀`. -/
example : [consume] ∉ prodCons.firingLanguage M₀ {⦅buffer, consuming⦆} := by
  rintro ⟨M, -, h⟩
  cases h with
  | stepL htr _ =>
    have := (fires_iff.1 htr).1 buffer
    simp [M₀, prodCons, Multiset.toFinsupp_apply] at this

/-! ### Behavioural equivalence -/

/-- A marking with no `producing` and no `buffer` token is dead. -/
theorem prodCons_dead (M : Marking Pl) (h₁ : M producing = 0) (h₂ : M buffer = 0) :
    prodCons.Dead M := by
  rw [dead_iff]
  intro t h
  cases t
  · simpa [prodCons, Multiset.toFinsupp_apply, h₁] using h producing
  · simpa [prodCons, Multiset.toFinsupp_apply, h₂] using h buffer

theorem dead_one : prodCons.Dead ⦅consuming⦆ :=
  prodCons_dead _ (by simp) (by simp)

theorem dead_two : prodCons.Dead ⦅consuming, consuming⦆ :=
  prodCons_dead _ (by simp) (by simp)

open LTS in
/-- The markings with one and with two `consuming` tokens are different but bisimilar. -/
example : ∃ M₁ M₂ : Marking Pl, M₁ ≠ M₂ ∧ (M₁ ~[prodCons.lts] M₂) := by
  refine ⟨⦅consuming⦆, ⦅consuming, consuming⦆, fun h => ?_, bisimilar_of_dead _ dead_one dead_two⟩
  simpa [Multiset.toFinsupp_apply] using DFunLike.congr_fun h consuming

/-- Bisimilar markings have the same traces. -/
example : prodCons.lts.traces ⦅consuming⦆ = prodCons.lts.traces ⦅consuming, consuming⦆ :=
  (bisimilar_iff_traces_eq _ _ _).1 (bisimilar_of_dead _ dead_one dead_two)

open Logic.Modal in
/-- Bisimilar dead markings satisfy the same Hennessy-Milner formulas. -/
example : TheoryEq (HML.Model.mk prodCons.lts (fun _ (_ : Unit) => True)).toModal
    ⦅consuming⦆ ⦅consuming, consuming⦆ :=
  (theoryEq_iff_bisimilar prodCons _ (fun _ _ => Iff.rfl) _ _).2
    (bisimilar_of_dead _ dead_one dead_two)

/-! ### Dot notation for executable nets

The properties of weighted nets are forwarded to executable nets, so that `N.Bounded M₀` can be
written for `N.toPetriNet.Bounded M₀`. -/

example : prodConsExec.Bounded Mx := by decide

example : prodConsExec.Conservative := by decide

example : ring.IsFreeChoice := by decide

example : ring.SiphonTrap ⦅producing⦆ := by decide

example : ring.Live ⦅producing⦆ :=
  live_of_siphons_contain_marked_trap (by decide) (by decide) (by decide)

/-! ### Firing languages of executable nets -/

/-- Membership in a firing language is decided by running the net. -/
example : [produce, produce, consume] ∈ prodConsExec.firingLanguage Mx {⦅buffer, consuming⦆} := by
  decide

example : [consume] ∉ prodConsExec.firingLanguage Mx {⦅buffer, consuming⦆} := by decide

example : [produce] ∉ prodConsExec.firingLanguage Mx {⦅buffer, consuming⦆} := by decide

/-! ### Reachability and deadlocks of bounded executable nets -/

/-- The ring reaches all its markings within two steps. -/
example : ring.Closed {producing} 2 := by decide

/-- For bounded nets, reachability and deadlock reachability are decided once boundedness is
available as a `Fact`. -/
instance : Fact (ring.Bounded ⦅producing⦆) := ⟨by decide⟩

instance : Fact (prodConsExec.Bounded Mx) := ⟨by decide⟩

example : ⦅producing⦆ ⇝[ring] ⦅consuming⦆ := by decide

/-- A second token cannot appear in the ring. -/
example : ¬ ⦅producing⦆ ⇝[ring] ⦅producing, producing⦆ := by decide

/-- The ring never reaches a dead marking, as Commoner's criterion also shows. -/
example : ¬ ∃ M, ⦅producing⦆ ⇝[ring] M ∧ ring.Dead M := by decide

/-- The producer/consumer net with two producers reaches a dead marking. -/
example : ∃ M, Mx ⇝[prodConsExec] M ∧ prodConsExec.Dead M := by decide

/-! ### Soundness of executable nets -/

/-- A workflow in which `produce` leaves a token in `buffer` besides finishing the case. -/
def leaky : ExecPetriNet Pl Tr where
  pre | produce => {producing} | consume => {buffer}
  post | produce => {buffer, consuming} | consume => {consuming}

/-- Soundness is decided outright, in both directions. The leaky workflow is unsound: after
`produce`, the sink is marked but so is `buffer`. -/
example : prodConsExec.Sound producing consuming := by decide

example : ¬ leaky.Sound producing consuming := by decide

/-- An unbounded net is never sound; the decision finds the pumping pair. -/
example : ¬ sourceExec.Sound () () := by decide

/-- A single token circulating in the ring can always be moved to any place, so the ring is sound
for every choice of source and sink. -/
example : ring.Sound producing buffer := by decide

/-- By van der Aalst's theorem, the short circuit of the sound workflow is live and bounded. -/
example : (prodConsExec.toPetriNet.shortCircuit producing consuming).Live
      (token producing) ∧
    (prodConsExec.toPetriNet.shortCircuit producing consuming).Bounded (token producing) :=
  sound_iff_live_and_bounded.1 (by decide)

/-! ### Notions of soundness -/

open Pl4 Tr5 in
/-- A net with a bad branch: `a` splits the case into `p` and `q`, after which `b` completes
without `q`, leaving a token behind, while `e` completes properly. The other route `c; b` is
fine. -/
def choiceNet : ExecPetriNet Pl4 Tr5 where
  pre | .a => {.i} | .b => {.p} | .c => {.i} | .d => {.q} | .e => {.p, .q}
  post | .a => {.p, .q} | .b => {.o} | .c => {.p} | .d => {.q} | .e => {.o}

open Pl4 Tr5 in
/-- A net that is sound for one token in `i` apart from the dead transition `e`, and that is not
sound for two tokens: `e` merges the two branches into a single token. -/
def joinNet : ExecPetriNet Pl4 Tr5 where
  pre | .a => {.i} | .b => {.p} | .c => {.i} | .d => {.q} | .e => {.p, .q}
  post | .a => {.p} | .b => {.o} | .c => {.q} | .d => {.o} | .e => {.o}

instance : Fact (choiceNet.Bounded ⦅Pl4.i⦆) := ⟨by decide⟩

instance : Fact (joinNet.Bounded ⦅Pl4.i⦆) := ⟨by decide⟩

instance : Fact (joinNet.Bounded (Multiset.replicate 2 Pl4.i)) := ⟨by decide⟩

instance : Fact (prodConsExec.Bounded ⦅producing⦆) := ⟨by decide⟩

instance : Fact (prodConsExec.Bounded (Multiset.replicate 2 producing)) := ⟨by decide⟩

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
example : prodConsExec.KSound producing consuming 2 := by decide

example : prodConsExec.UpToKSound producing consuming 2 := by decide

example : prodConsExec.LazySound producing consuming := by decide

/-- A weakly sound net is lazy sound, as the sink has no output transition, and a sound net is
weakly and relaxed sound. -/
example : prodConsExec.LazySound producing consuming :=
  LazySound.of_weak (fun t => by cases t <;> simp [ExecPetriNet.toPetriNet, prodConsExec])
    (by decide)

example : prodConsExec.RelaxedSound producing consuming :=
  Sound.relaxed (by decide)

/-- The producer/consumer net is a workflow net, which `decide` checks by computing reachability in
its flow graph. -/
theorem prodCons_wf : prodConsExec.IsWFNet producing consuming := by decide

/-- The producer/consumer net with the sink and source swapped is not a workflow net. -/
example : ¬ prodConsExec.IsWFNet consuming producing := by decide

/-- The nets of the previous examples are workflow nets too. -/
example : choiceNet.IsWFNet Pl4.i Pl4.o := by decide

example : joinNet.IsWFNet Pl4.i Pl4.o := by decide

/-- Hence proper completion follows from the option to complete, which `decide` establishes. -/
example : ∀ M, prodConsExec.Reachable (token producing) M → token consuming ≤ M →
    M = token consuming :=
  prodCons_wf.proper_of_completion (weakSound_iff.1 (by decide))

end CslibTests
