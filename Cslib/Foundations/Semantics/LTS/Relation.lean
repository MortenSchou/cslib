/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Conversions between `LTS` and `Relation`.

## Main statements

- `LTS.reflTransGen_unlabelledTr_iff`: reachability (`LTS.CanReach`) is the reflexive-transitive
closure of the underlying unlabelled transition relation.
- `LTS.CanReach.induction_on` and `LTS.CanReach.head_induction_on`: induction principles for
reachability, mirroring `Relation.ReflTransGen.rec` and `Relation.ReflTransGen.head_induction_on`
(usable with `induction h using ...`).
- `LTS.CanReach.lift`: a map on states that preserves unlabelled transitions preserves
reachability, mirroring `Relation.ReflTransGen.lift`.
- `Trans` instances, so that `calc` can chain reachability with unlabelled transitions.

The basic reachability API (`CanReach.refl`, `single`, `trans`, `head`, `tail`) is in
`Cslib.Foundations.Semantics.LTS.Basic`.
-/

@[expose] public section

namespace Cslib.LTS

variable {State Label : Type*}

/-- Returns the relation that relates all states `s1` and `s2` via a fixed transition label `μ`. -/
def Tr.toRelation (lts : LTS State Label) (μ : Label) : State → State → Prop :=
  fun s1 s2 => lts.Tr s1 μ s2

/-- Any homogeneous relation can be seen as an LTS where all transitions have the same label. -/
def Relation.toLTS [DecidableEq Label] (r : State → State → Prop) (μ : Label) :
  LTS State Label where
  Tr := fun s1 μ' s2 => if μ' = μ then r s1 s2 else False

/-- Returns the relation that relates all states `s1` and `s2` via a fixed list of transition
labels `μs`. -/
def MTr.toRelation (lts : LTS State Label) (μs : List Label) : State → State → Prop :=
  fun s1 s2 => lts.MTr s1 μs s2

section UnlabelledPaths

variable (lts : LTS State Label)

/-- A multistep transition induces a reflexive-transitive path in the underlying unlabelled
transition relation. -/
theorem MTr.toReflTransGen (h : lts.MTr s1 μs s2) :
    Relation.ReflTransGen lts.UnlabelledTr s1 s2 := by
  induction h with
  | refl => exact .refl
  | stepL htr _ ih => exact ih.head ⟨_, htr⟩

/-- A nonempty multistep transition induces a nonempty path in the underlying unlabelled
transition relation. -/
theorem MTr.toTransGen (h : lts.MTr s1 μs s2) (hne : μs ≠ []) :
    Relation.TransGen lts.UnlabelledTr s1 s2 := by
  cases h with
  | refl => contradiction
  | stepL htr hmtr => exact Relation.TransGen.head' ⟨_, htr⟩ (hmtr.toReflTransGen lts)

/-- The reflexive-transitive closure of the underlying unlabelled transition relation is exactly
reachability in the LTS. -/
theorem reflTransGen_unlabelledTr_iff :
    Relation.ReflTransGen lts.UnlabelledTr s1 s2 ↔ lts.CanReach s1 s2 := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], .refl⟩
    | tail _ htr ih =>
        obtain ⟨μs, hmtr⟩ := ih
        obtain ⟨μ, htr⟩ := htr
        exact ⟨μs ++ [μ], hmtr.stepR lts htr⟩
  · rintro ⟨μs, hmtr⟩
    exact hmtr.toReflTransGen lts

/-- The transitive closure of the underlying unlabelled transition relation is exactly the
nonempty multistep transitions of the LTS. -/
theorem transGen_unlabelledTr_iff :
    Relation.TransGen lts.UnlabelledTr s1 s2 ↔
      ∃ μs, μs ≠ [] ∧ lts.MTr s1 μs s2 := by
  constructor
  · intro h
    induction h with
    | single htr =>
        obtain ⟨μ, htr⟩ := htr
        exact ⟨[μ], by simp, MTr.single lts htr⟩
    | tail _ htr ih =>
        obtain ⟨μs, hne, hmtr⟩ := ih
        obtain ⟨μ, htr⟩ := htr
        exact ⟨μs ++ [μ], by simp, hmtr.stepR lts htr⟩
  · rintro ⟨μs, hne, hmtr⟩
    exact hmtr.toTransGen lts hne

end UnlabelledPaths

section Reachability

variable {lts : LTS State Label}

/-- Induction on reachability, peeling off the last unlabelled transition. This is the analogue
of `Relation.ReflTransGen.rec`, and can be used with `induction h using CanReach.induction_on`. -/
@[elab_as_elim]
theorem CanReach.induction_on {s : State} {P : ∀ t, lts.CanReach s t → Prop} {t : State}
    (h : lts.CanReach s t) (refl : P s (CanReach.refl lts s))
    (tail : ∀ {a b} (hsa : lts.CanReach s a) (hab : lts.UnlabelledTr a b),
      P a hsa → P b (hsa.tail hab)) : P t h :=
  -- `P t h` and `P t ((reflTransGen_unlabelledTr_iff lts).1 _)` agree by proof irrelevance.
  Relation.ReflTransGen.rec (motive := fun t h' => P t ((reflTransGen_unlabelledTr_iff lts).1 h'))
    refl (fun _ hbc ih => tail _ hbc ih) ((reflTransGen_unlabelledTr_iff lts).2 h)

/-- Induction on reachability, peeling off the first unlabelled transition. This is the analogue
of `Relation.ReflTransGen.head_induction_on`, and can be used with
`induction h using CanReach.head_induction_on`. -/
@[elab_as_elim]
theorem CanReach.head_induction_on {t : State} {P : ∀ s, lts.CanReach s t → Prop} {s : State}
    (h : lts.CanReach s t) (refl : P t (CanReach.refl lts t))
    (head : ∀ {a b} (hab : lts.UnlabelledTr a b) (hbt : lts.CanReach b t),
      P b hbt → P a (hbt.head hab)) : P s h :=
  -- `P s h` and `P s ((reflTransGen_unlabelledTr_iff lts).1 _)` agree by proof irrelevance.
  Relation.ReflTransGen.head_induction_on (motive := fun s h' =>
      P s ((reflTransGen_unlabelledTr_iff lts).1 h'))
    ((reflTransGen_unlabelledTr_iff lts).2 h) refl fun hab _ ih => head hab _ ih

/-- A map on states that sends unlabelled transitions to unlabelled transitions sends reachability
to reachability. This is the analogue of `Relation.ReflTransGen.lift`. -/
theorem CanReach.lift {State' Label' : Type*} {lts' : LTS State' Label'} (f : State → State')
    (hf : ∀ s s', lts.UnlabelledTr s s' → lts'.UnlabelledTr (f s) (f s')) {s s' : State}
    (h : lts.CanReach s s') : lts'.CanReach (f s) (f s') :=
  (reflTransGen_unlabelledTr_iff lts').1 (((reflTransGen_unlabelledTr_iff lts).2 h).lift f hf)

/-- Reachability is invariant under an equivalence of the states that preserves and reflects
unlabelled transitions. -/
theorem CanReach.iff_of_equiv {State' Label' : Type*} {lts' : LTS State' Label'}
    (e : State ≃ State') (h : ∀ s s', lts.UnlabelledTr s s' ↔ lts'.UnlabelledTr (e s) (e s'))
    {s s' : State} : lts.CanReach s s' ↔ lts'.CanReach (e s) (e s') :=
  ⟨CanReach.lift e fun _ _ => (h _ _).1, fun hr => by
    simpa using CanReach.lift (lts := lts') (lts' := lts) e.symm
      (fun a b hab => (h _ _).2 (by simpa using hab)) hr⟩

end Reachability

/-! ### Calc tactic support for MTr -/

/-- Transitions can be chained. -/
instance (lts : LTS State Label) :
  Trans
    (Tr.toRelation lts μ1)
    (Tr.toRelation lts μ2)
    (MTr.toRelation lts [μ1, μ2]) where
  trans := by
    intro s1 s2 s3 htr1 htr2
    apply MTr.single at htr1
    apply MTr.single at htr2
    apply MTr.comp lts htr1 htr2

/-- Transitions can be chained with multi-step transitions. -/
instance (lts : LTS State Label) :
  Trans
    (Tr.toRelation lts μ)
    (MTr.toRelation lts μs)
    (MTr.toRelation lts (μ :: μs)) where
  trans := by
    intro s1 s2 s3 htr1 hmtr2
    apply MTr.single at htr1
    apply MTr.comp lts htr1 hmtr2

/-- Multi-step transitions can be chained with transitions. -/
instance (lts : LTS State Label) :
  Trans
    (MTr.toRelation lts μs)
    (Tr.toRelation lts μ)
    (MTr.toRelation lts (μs ++ [μ])) where
  trans := by
    intro s1 s2 s3 hmtr1 htr2
    apply MTr.single at htr2
    apply MTr.comp lts hmtr1 htr2

/-- Multi-step transitions can be chained. -/
instance (lts : LTS State Label) :
  Trans
    (MTr.toRelation lts μs1)
    (MTr.toRelation lts μs2)
    (MTr.toRelation lts (μs1 ++ μs2)) where
  trans := by
    intro s1 s2 s3 hmtr1 hmtr2
    apply MTr.comp lts hmtr1 hmtr2

/-! ### Calc tactic support for reachability -/

/-- Reachability can be chained. -/
instance {lts : LTS State Label} : Trans lts.CanReach lts.CanReach lts.CanReach := ⟨CanReach.trans⟩

/-- An unlabelled transition can be chained with reachability. -/
instance {lts : LTS State Label} : Trans lts.UnlabelledTr lts.CanReach lts.CanReach :=
  ⟨CanReach.head⟩

/-- Reachability can be chained with an unlabelled transition. -/
instance {lts : LTS State Label} : Trans lts.CanReach lts.UnlabelledTr lts.CanReach :=
  ⟨CanReach.tail⟩

/-- Unlabelled transitions can be chained into reachability. -/
instance {lts : LTS State Label} : Trans lts.UnlabelledTr lts.UnlabelledTr lts.CanReach :=
  ⟨fun h₁ h₂ => (CanReach.of_unlabelledTr h₁).tail h₂⟩

end Cslib.LTS
