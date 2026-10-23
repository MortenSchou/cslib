/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Foundations.Data.OmegaSequence.Stuttering
public import Cslib.Foundations.Semantics.LTS.AmpleStep
public import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-! # Ample sets and infinite executions

`Cslib.Foundations.Semantics.LTS.AmpleSets` shows that the reduction of an LTS by an ample selector
preserves finite executions up to invisible labels. Here we treat *infinite* executions. We show
that every infinite execution of an LTS has an infinite execution in the reduced LTS with the same
start state and a stuttering equivalent sequence of observations, where an
observation is a function `ℓ` of the state that the invisible labels do not change. By the stutter
invariance of LTL without next-time this gives preservation of LTL without next-time; see
`Cslib.Logics.Temporal.LTL.AmpleSets`.

## Main statements

- `LTS.IsAmpleStep.exists_reduced_omegaExecution`: for an ample selector with the stepwise
  stubbornness (`LTS.IsAmpleStep`) and the cycle proviso, and an infinite execution, the reduced LTS
  has an infinite execution from the same state whose observations are stuttering equivalent. The
  LTS need not be deterministic.
- `LTS.exists_reduced_omegaExecution`: the same for a deterministic LTS and `LTS.IsAmple`, which
  is `LTS.IsAmpleStep` there.

## Proof idea

We build the infinite reduced execution one step at a time, maintaining a *remaining* infinite
execution `ss` from the current state, whose observations are those of the original execution with
some letters (which equal their successors) removed; this is recorded by a strictly monotone map
`h`. At the current state, if some label of the ample set occurs in the remaining execution, the
first such label is taken, and moved to the front of the remaining execution; this uses the
stepwise stubbornness along the execution (`OmegaExecution.exists_push`). If none occurs, an
enabled ample label is taken and added to every state of the remaining execution. At a state that
is fully expanded, the first label of the remaining execution is taken, so the remaining execution
is shortened. The cycle
proviso shows that fully expanded states occur infinitely often, so the position in the original
execution grows without bound. This is what makes the observations stuttering equivalent, and not
only equal on every finite prefix.

## What is and is not covered

The LTS need not be deterministic, but `IsStubborn` is not enough without determinism: it gives
the existence of the commuted executions, and nothing that identifies the intermediate states of two
such executions. `IsStubbornStep` asks for the diamond one step at a time, which is what builds the
moved execution, and for the members of the ample set to be deterministic at the states reached
without them; the latter makes the moved execution rejoin the remaining one after the moved label.
In a deterministic LTS the two notions agree (`IsStubborn.isStubbornStep`), so deterministic
concrete models, such as a marking graph, are covered. The observations are functions of the
state, so they are compared pointwise. The cycle proviso `LTS.CycleProviso A (ss 0)` is
only required of the states that the reduced LTS reaches from the start state; the construction
visits only such states. If these are finitely many, it says that every cycle of the reduced graph
contains a fully expanded state. No fairness assumptions are made, and the selector is not required
to be small.

## References

* [D. Peled, *All from one, one for all: on model checking using representatives*][Peled1993]
-/

@[expose] public section

namespace Cslib.LTS

open Cslib Cslib.ωSequence

universe u v w

variable {State : Type u} {Label : Type v} {lts : LTS State Label}

section Prefix

/-- The labels at the positions before `n` of an infinite execution form a multistep transition. -/
theorem OmegaExecution.mTr_take {ss : ωSequence State} {μs : ωSequence Label}
    (h : lts.OmegaExecution ss μs) (n : ℕ) : lts.MTr (ss 0) (μs.take n) (ss n) :=
  extract_eq_take ▸ h.extract_mTr n.zero_le

end Prefix

section Commute

variable {ss : ωSequence State} {μs : ωSequence Label} {T : Set Label} {b : Label}

/-- The states of an infinite execution before its first label of `T` are reached from the start
by executions that avoid `T`. -/
theorem OmegaExecution.avoidReach (h : lts.OmegaExecution ss μs) {n : ℕ}
    (hav : ∀ k < n, μs k ∉ T) : lts.AvoidReach T (ss 0) (ss n) :=
  ⟨μs.take n, h.mTr_take n, fun u hu => by
    obtain ⟨k, hk, rfl⟩ := mem_take_iff.1 hu
    exact hav k hk⟩

/-- A member `b` of a stepwise stubborn set `T` that is enabled at the start of an infinite
execution can be moved past the labels of the execution up to the first label of `T`: there are
states `w n`, reached from the `n`th state by `b`, with steps by the `n`th label between them. -/
theorem OmegaExecution.exists_push (h : lts.OmegaExecution ss μs)
    (hT : lts.IsStubbornStep (ss 0) T) (hb : b ∈ T) {u : State} (hu : lts.Tr (ss 0) b u) :
    ∃ w : ℕ → State, (∀ n, (∀ k < n, μs k ∉ T) → lts.Tr (ss n) b (w n)) ∧
      ∀ n, (∀ k ≤ n, μs k ∉ T) → lts.Tr (w n) (μs n) (w (n + 1)) := by
  have step : ∀ n w, (∀ k ≤ n, μs k ∉ T) → lts.Tr (ss n) b w →
      ∃ w', lts.Tr w (μs n) w' ∧ lts.Tr (ss (n + 1)) b w' := fun n w hav hw =>
    (((hT _ (h.avoidReach fun k hk => hav k hk.le) b hb).2 (μs n) (hav n le_rfl) _ (h n)).2 w hw)
  have : Nonempty State := ⟨u⟩
  choose! g hg using step
  let w : ℕ → State := fun n => Nat.rec u (fun i wi => g i wi) n
  have ha : ∀ n, (∀ k < n, μs k ∉ T) → lts.Tr (ss n) b (w n) := by
    intro n
    induction n with
    | zero => exact fun _ => hu
    | succ n ih =>
      intro hav
      exact (hg n (w n) (fun k hk => hav k (by omega)) (ih fun k hk => hav k (by omega))).2
  exact ⟨w, ha, fun n hav => (hg n (w n) hav (ha n fun k hk => hav k (by omega))).1⟩

end Commute

section Stage

variable {α : Type w} (ℓ : State → α)

/-- The data of the construction of the reduced execution, for an original sequence of observations
`x`: a remaining infinite execution `ss`, `μs`, and an embedding `h` of its positions into those of
`x`, such that the observations of the remaining execution are those of `x` at the image positions,
and the positions of `x` outside the image have the observation of the next position in the
image. -/
structure Stage (lts : LTS State Label) (x : ωSequence α) where
  /-- The states of the remaining execution. -/
  ss : ωSequence State
  /-- The labels of the remaining execution. -/
  μs : ωSequence Label
  /-- The position in the original sequence of observations of each state. -/
  h : ℕ → ℕ
  /-- The remaining execution is an execution. -/
  exec : lts.OmegaExecution ss μs
  /-- The positions of the original sequence are visited in order. -/
  strictMono : StrictMono h
  /-- The observations agree with the original ones. -/
  eq : ∀ i, ℓ (ss i) = x (h i)
  /-- The positions of the original sequence that are skipped have the observation of the next
  position that is visited. -/
  gap : ∀ i j, h i < j → j < h (i + 1) → x j = x (h (i + 1))

variable {ℓ} {A : State → Set Label} {Inv : Label → Prop} {x : ωSequence α}

/-- One step of the construction: a label of the ample set leads from the current state to the
state of a new stage. The position `h 0` of the new stage is that of the old stage, or the next
one, and the latter is the case when the current state is fully expanded. -/
theorem Stage.exists_step (hA : lts.IsAmpleStep A Inv)
    (hℓ : ∀ s μ s', lts.Tr s μ s' → Inv μ → ℓ s = ℓ s') (S : Stage ℓ lts x) :
    ∃ (S' : Stage ℓ lts x) (a : Label), a ∈ A (S.ss 0) ∧ lts.Tr (S.ss 0) a (S'.ss 0) ∧
      (S'.h 0 = S.h 0 ∨ S'.h 0 = S.h 1) ∧ (lts.IsExpanded A (S.ss 0) → S'.h 0 = S.h 1) := by
  classical
  have hne0 : lts.Enabled (S.ss 0) (S.μs 0) := ⟨_, S.exec 0⟩
  by_cases hocc : ∃ k, S.μs k ∈ A (S.ss 0)
  · -- Some label of the ample set occurs: the first one is moved to the front.
    obtain ⟨hk, hav⟩ : S.μs (Nat.find hocc) ∈ A (S.ss 0) ∧
        ∀ j < Nat.find hocc, S.μs j ∉ A (S.ss 0) := ⟨Nat.find_spec hocc, fun j => Nat.find_min hocc⟩
    generalize Nat.find hocc = k at hk hav
    have hen : lts.Enabled (S.ss 0) (S.μs k) := by
      by_contra hna
      exact ((hA.stubborn _).isStubborn _ _ (S.exec.mTr_take k) (fun u hu => by
        obtain ⟨j, hj, rfl⟩ := mem_take_iff.1 hu
        exact hav j hj) _ hk).2 hna ⟨_, S.exec k⟩
    obtain ⟨ub, hub⟩ := hen
    have hinv : 0 < k → Inv (S.μs k) := fun hk0 =>
      hA.invisible _ (fun he => hav 0 hk0 (he _ hne0)) _ hk ⟨_, hub⟩
    obtain ⟨w, hwa, hwb⟩ := S.exec.exists_push (hA.stubborn _) hk hub
    have hw : ∀ i ≤ k, lts.Tr (S.ss i) (S.μs k) (w i) := fun i hi =>
      hwa i fun j hj => hav j (by omega)
    have hwk : w k = S.ss (k + 1) :=
      ((hA.stubborn _) _ (S.exec.avoidReach hav) _ hk).1 _ _ (hw k le_rfl) (S.exec k)
    obtain ⟨ss', hss'⟩ : ∃ ss' : ℕ → State, ∀ i, ss' i = if i < k then w i else
        S.ss (i + 1) := ⟨_, fun _ => rfl⟩
    obtain ⟨μs', hμs'⟩ : ∃ μs' : ℕ → Label, ∀ i, μs' i = if i < k then S.μs i else
        S.μs (i + 1) := ⟨_, fun _ => rfl⟩
    obtain ⟨h', hh'⟩ : ∃ h' : ℕ → ℕ, ∀ i, h' i = if i < k then S.h i else S.h (i + 1) :=
      ⟨_, fun _ => rfl⟩
    have hexec : lts.OmegaExecution (⟨ss'⟩ : ωSequence State) (⟨μs'⟩ : ωSequence Label) := by
      intro i
      change lts.Tr (ss' i) (μs' i) (ss' (i + 1))
      by_cases hi : i < k
      · have h1 := hwb i fun j hj => hav j (by omega)
        by_cases hi1 : i + 1 < k
        · simp only [hss', hμs', hi, hi1, ↓reduceIte]
          exact h1
        · have hik : i + 1 = k := by omega
          simp only [hss', hμs', hi, hi1, ↓reduceIte]
          rw [← hik] at hwk
          rw [← hwk]
          exact h1
      · have hi1 : ¬ i + 1 < k := by omega
        simp only [hss', hμs', hi, hi1, ↓reduceIte]
        exact S.exec (i + 1)
    have hmono : StrictMono h' := by
      intro i j hij
      rw [hh', hh']
      split_ifs with h1 h2 h2
      · exact S.strictMono hij
      · exact S.strictMono (by omega)
      · omega
      · exact S.strictMono (by omega)
    have heq : ∀ i, ℓ (ss' i) = x (h' i) := by
      intro i
      rw [hss', hh']
      split_ifs with hi
      · exact (hℓ _ _ _ (hw i hi.le) (hinv (by omega))).symm.trans (S.eq i)
      · exact S.eq (i + 1)
    have hgap : ∀ i j, h' i < j → j < h' (i + 1) → x j = x (h' (i + 1)) := by
      intro i j hj1 hj2
      rw [hh'] at hj1 hj2 ⊢
      by_cases hi : i < k
      · by_cases hi1 : i + 1 < k
        · simp only [hi, hi1, ↓reduceIte] at hj1 hj2 ⊢
          exact S.gap i j hj1 hj2
        · have hik : i + 1 = k := by omega
          simp only [hi, hi1, ↓reduceIte] at hj1 hj2 ⊢
          have hxx : x (S.h (i + 1)) = x (S.h (i + 1 + 1)) := by
            rw [← S.eq, ← S.eq]
            refine hℓ _ (S.μs (i + 1)) _ (S.exec (i + 1)) ?_
            rw [hik]
            exact hinv (by omega)
          rcases lt_trichotomy j (S.h (i + 1)) with hlt | heq | hgt
          · exact (S.gap i j hj1 hlt).trans hxx
          · rw [heq]
            exact hxx
          · exact S.gap (i + 1) j hgt hj2
      · have hi1 : ¬ i + 1 < k := by omega
        simp only [hi, hi1, ↓reduceIte] at hj1 hj2 ⊢
        exact S.gap (i + 1) j hj1 hj2
    refine ⟨⟨⟨ss'⟩, ⟨μs'⟩, h', hexec, hmono, heq, hgap⟩, S.μs k, hk, ?_, ?_, ?_⟩
    · change lts.Tr (S.ss 0) (S.μs k) (ss' 0)
      rw [hss']
      by_cases h0 : 0 < k
      · simp only [h0, ↓reduceIte]
        exact hw 0 h0.le
      · simp only [h0, ↓reduceIte]
        obtain rfl : k = 0 := by omega
        exact S.exec 0
    · change h' 0 = S.h 0 ∨ h' 0 = S.h 1
      rw [hh']
      by_cases h0 : 0 < k
      · exact Or.inl (by simp only [h0, ↓reduceIte])
      · exact Or.inr (by simp only [h0, ↓reduceIte])
    · intro hexp
      change h' 0 = S.h 1
      have h0 : ¬ 0 < k := fun h0 => hav 0 h0 (hexp _ hne0)
      simp only [hh', h0, ↓reduceIte]
  · -- No label of the ample set occurs: an enabled ample label is added to every state.
    have hocc' : ∀ k, S.μs k ∉ A (S.ss 0) := fun k hk => hocc ⟨k, hk⟩
    have hnexp : ¬ lts.IsExpanded A (S.ss 0) := fun he => hocc' 0 (he _ hne0)
    obtain ⟨a, haA, hen⟩ := hA.nonempty _ fun ht => ht _ _ (S.exec 0)
    have hinv := hA.invisible _ hnexp a haA hen
    obtain ⟨ua, hua⟩ := hen
    obtain ⟨w, hwa, hwb⟩ := S.exec.exists_push (hA.stubborn _) haA hua
    have hw : ∀ i, lts.Tr (S.ss i) a (w i) := fun i => hwa i fun j _ => hocc' j
    have hexec : lts.OmegaExecution (⟨w⟩ : ωSequence State) S.μs :=
      fun i => hwb i fun j _ => hocc' j
    refine ⟨⟨⟨w⟩, S.μs, S.h, hexec, S.strictMono,
      fun i => (hℓ _ _ _ (hw i) hinv).symm.trans (S.eq i), S.gap⟩, a, haA, hw 0,
      Or.inl rfl, fun he => absurd he hnexp⟩

end Stage

section Main

/-- An accessible state starts no infinite descending chain. -/
private theorem exists_not_rel_apply_succ_of_acc {α : Type*} {r : α → α → Prop} {a : α}
    (h : Acc r a) (f : ℕ → α) (h0 : f 0 = a) : ∃ n, ¬ r (f (n + 1)) (f n) := by
  induction h generalizing f with
  | intro a _ ih =>
    by_cases hr : r (f 1) (f 0)
    · obtain ⟨n, hn⟩ := ih (f 1) (h0 ▸ hr) (fun k => f (k + 1)) rfl
      exact ⟨n + 1, hn⟩
    · exact ⟨0, hr⟩

variable {α : Type w} {ℓ : State → α} {A : State → Set Label} {Inv : Label → Prop}

/-- Every infinite execution of an LTS has an infinite execution in the reduction by an ample
selector with the stepwise stubbornness and the cycle proviso, from the same state and with
stuttering equivalent observations `ℓ`, where `ℓ` is not changed by the invisible labels. The LTS
need not be deterministic.

For LTL without next-time and the maximal paths of a model, see
`Cslib.Logics.Temporal.LTL.AmpleSets`. -/
theorem IsAmpleStep.exists_reduced_omegaExecution {ss : ωSequence State}
    {μs : ωSequence Label} (hA : lts.IsAmpleStep A Inv) (h3 : lts.CycleProviso A (ss 0))
    (hℓ : ∀ s μ s', lts.Tr s μ s' → Inv μ → ℓ s = ℓ s') (h : lts.OmegaExecution ss μs) :
    ∃ (gs : ωSequence State) (νs : ωSequence Label), (lts.reduced A).OmegaExecution gs νs ∧
      gs 0 = ss 0 ∧ StutterEq (ss.map ℓ) (gs.map ℓ) := by
  classical
  let x : ωSequence α := ss.map ℓ
  let S₀ : Stage ℓ lts x := ⟨ss, μs, id, h, strictMono_id, fun _ => rfl, fun i j h1 h2 => by
    simp only [id_eq] at h1 h2
    omega⟩
  choose next a hnext using fun S : Stage ℓ lts x => Stage.exists_step hA hℓ S
  let seq : ℕ → Stage ℓ lts x := fun n => Nat.rec S₀ (fun _ S => next S) n
  let e : ℕ → ℕ := fun n => (seq n).h 0
  have hgs : ∀ n, a (seq n) ∈ A ((seq n).ss 0) ∧
      lts.Tr ((seq n).ss 0) (a (seq n)) ((seq (n + 1)).ss 0) := fun n =>
    ⟨(hnext (seq n)).1, (hnext (seq n)).2.1⟩
  have he : ∀ n, e (n + 1) = (next (seq n)).h 0 := fun _ => rfl
  have hmono : Monotone e := monotone_nat_of_le_succ fun n => by
    have h0 : (seq n).h 0 ≤ (seq n).h 1 := (seq n).strictMono.monotone (Nat.zero_le 1)
    have h1 : e n = (seq n).h 0 := rfl
    rcases (hnext (seq n)).2.2.1 with h | h <;> rw [he] <;> omega
  have hreach : ∀ n, (lts.reduced A).CanReach (ss 0) ((seq n).ss 0) := by
    intro n
    induction n with
    | zero => exact .refl _ _
    | succ n ih => exact canReach_reduced_of_tr ih (hgs n).1 (hgs n).2
  have hexp : ∀ n, ∃ m, n ≤ m ∧ lts.IsExpanded A ((seq m).ss 0) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨n, hn⟩ := hcon
    obtain ⟨k, hk⟩ := exists_not_rel_apply_succ_of_acc (h3 _ (hreach n))
      (fun k => (seq (n + k)).ss 0) rfl
    exact hk ⟨hn _ (Nat.le_add_right n k), _, (hgs (n + k)).1, (hgs (n + k)).2⟩
  have hu : ∀ N, ∃ n, N ≤ e n := by
    intro N
    induction N with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ N ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hnm, hm⟩ := hexp n
      have h1 : e (m + 1) = (seq m).h 1 := (hnext (seq m)).2.2.2 hm
      have h2 : (seq m).h 0 < (seq m).h 1 := (seq m).strictMono Nat.zero_lt_one
      have h3 : e n ≤ e m := hmono hnm
      have h4 : e m = (seq m).h 0 := rfl
      exact ⟨m + 1, by omega⟩
  refine ⟨⟨fun n => (seq n).ss 0⟩, ⟨fun n => a (seq n)⟩, fun n => hgs n, rfl, ?_⟩
  refine StutterEq.of_gapMap (e := e) hmono rfl hu (fun n => (seq n).eq 0) ?_
  intro n j hj1 hj2
  have h1 : e n = (seq n).h 0 := rfl
  rcases (hnext (seq n)).2.2.1 with h | h
  · rw [he, h, ← h1] at hj2
    omega
  · rw [he, h] at hj2 ⊢
    exact (seq n).gap 0 j hj1 hj2

/-- Every infinite execution of a deterministic LTS has an infinite execution in the reduction by
an ample selector with the cycle proviso, from the same state and with stuttering equivalent
observations `ℓ`, where `ℓ` is not changed by the invisible labels. -/
theorem exists_reduced_omegaExecution [lts.Deterministic] {ss : ωSequence State}
    {μs : ωSequence Label} (hA : lts.IsAmple A Inv) (h3 : lts.CycleProviso A (ss 0))
    (hℓ : ∀ s μ s', lts.Tr s μ s' → Inv μ → ℓ s = ℓ s') (h : lts.OmegaExecution ss μs) :
    ∃ (gs : ωSequence State) (νs : ωSequence Label), (lts.reduced A).OmegaExecution gs νs ∧
      gs 0 = ss 0 ∧ StutterEq (ss.map ℓ) (gs.map ℓ) :=
  hA.toIsAmpleStep.exists_reduced_omegaExecution h3 hℓ h

end Main

end Cslib.LTS
