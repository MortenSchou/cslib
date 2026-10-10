/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.ExecutableSoundness
public import Cslib.Foundations.Relation.FiniteClosure
public import Cslib.Computability.PetriNets.SoundnessNotions

/-! # Deciding the notions of soundness for executable nets

For executable nets with finitely many places and transitions, the notions of soundness defined in
`Cslib.Computability.PetriNets.SoundnessNotions` are decidable whenever the relevant initial marking
is bounded. Boundedness is supplied as a `Fact`, which `decide` can establish with
`ExecPetriNet.instDecidableBounded`.

The decision procedures reduce each notion to finite checks over the finite set of markings
reachable from the initial marking, using `ExecPetriNet.decidableForallReachable`,
`ExecPetriNet.decidableExistsReachable` and `ExecPetriNet.decidableReachable`.

Generalized soundness is not decided here.
-/

@[expose] public section

namespace Cslib

namespace ExecPetriNet

open PetriNet

variable {Place Transition : Type*} [DecidableEq Place] [Fintype Place] [Fintype Transition]
  {N : ExecPetriNet Place Transition}

omit [Fintype Place] [Fintype Transition] in
theorem nsmul_token (k : ℕ) (p : Place) :
    k • PetriNet.token p = Multiset.toFinsupp (Multiset.replicate k p) := by
  rw [token_eq_toFinsupp, ← Multiset.nsmul_singleton, map_nsmul]

/-- Easy soundness is decidable for bounded executable nets. -/
instance (i o : Place) [h : Fact (N.toPetriNet.Bounded (Multiset.toFinsupp {i}))] :
    Decidable (N.toPetriNet.EasySound i o) :=
  decidable_of_iff (Multiset.toFinsupp {i} ⇝[N] Multiset.toFinsupp {o})
    (by simp [EasySound, token_eq_toFinsupp])

/-- `k`-soundness is decidable for executable nets, if `k` tokens in the source give a bounded
marking. -/
def decidableKSound (i o : Place) (k : ℕ)
    (hb : N.toPetriNet.Bounded (Multiset.replicate k i)) :
    Decidable (N.toPetriNet.KSound i o k) :=
  @decidable_of_iff _ (∀ m : Multiset Place, Multiset.replicate k i ⇝[N] m →
      m ⇝[N] Multiset.replicate k o)
    (by
      simp only [KSound, nsmul_token]
      refine ⟨fun h M hM => ?_, fun h m hm => h _ hm⟩
      obtain ⟨m, rfl⟩ := Multiset.toFinsupp.surjective M
      exact h m hM)
    (decidableForallReachable _ hb _ fun m hm =>
      decidableReachable m (Multiset.replicate k o) (hb.of_reachable hm))

instance (i o : Place) (k : ℕ) [h : Fact (N.toPetriNet.Bounded (Multiset.replicate k i))] :
    Decidable (N.toPetriNet.KSound i o k) :=
  decidableKSound i o k h.out

/-- Up-to-`k` soundness is decidable for executable nets, if `k` tokens in the source give a bounded
marking. -/
instance (i o : Place) (k : ℕ) [h : Fact (N.toPetriNet.Bounded (Multiset.replicate k i))] :
    Decidable (N.toPetriNet.UpToKSound i o k) :=
  have : ∀ l, l ≤ k → Decidable (N.toPetriNet.KSound i o l) := fun l hl =>
    decidableKSound i o l (h.out.mono_marking (toFinsupp_le_iff.2
      (Multiset.replicate_le_replicate i |>.2 hl)))
  @Nat.decidableBallLE k (fun l _ => N.toPetriNet.KSound i o l) this

/-- Weak soundness is decidable for bounded executable nets. -/
instance (i o : Place) [h : Fact (N.toPetriNet.Bounded (Multiset.toFinsupp {i}))] :
    Decidable (N.toPetriNet.WeakSound i o) :=
  decidableKSound i o 1 (by simpa using h.out)

omit [Fintype Place] [Fintype Transition] in
/-- Relaxed soundness, stated for markings given by multisets. -/
theorem relaxedSound_iff {i o : Place} : N.toPetriNet.RelaxedSound i o ↔ ∀ t, ∃ m : Multiset Place,
    Multiset.toFinsupp {i} ⇝[N] m ∧
      N.pre t ≤ m ∧ Multiset.toFinsupp (m - N.pre t + N.post t) ⇝[N]
        Multiset.toFinsupp {o} := by
  simp only [RelaxedSound, token_eq_toFinsupp]
  refine forall_congr' fun t => ⟨fun ⟨M, M', hM, hf, hc⟩ => ?_, fun ⟨m, hm, hle, hc⟩ => ?_⟩
  · obtain ⟨m, rfl⟩ := Multiset.toFinsupp.surjective M
    obtain ⟨m', rfl⟩ := Multiset.toFinsupp.surjective M'
    have hf' := fires_iff.1 hf
    have hle : N.pre t ≤ m := by
      by_contra h; simp [fire, h] at hf'
    simp only [fire, hle, ite_true, Option.some.injEq] at hf'
    exact ⟨m, hM, hle, hf' ▸ hc⟩
  · exact ⟨Multiset.toFinsupp m, _, hm, fires_iff.2 (by simp [fire, hle]), hc⟩

/-- Relaxed soundness is decidable for bounded executable nets. -/
instance (i o : Place) [h : Fact (N.toPetriNet.Bounded (Multiset.toFinsupp {i}))] :
    Decidable (N.toPetriNet.RelaxedSound i o) :=
  have hb := h.out
  have inst : ∀ t, Decidable (∃ m : Multiset Place,
      Multiset.toFinsupp {i} ⇝[N] m ∧
        N.pre t ≤ m ∧ Multiset.toFinsupp (m - N.pre t + N.post t) ⇝[N]
          Multiset.toFinsupp {o}) := fun t =>
    decidableExistsReachable {i} hb _ fun m hm =>
      if hle : N.pre t ≤ m then
        have hf : m [t⟩[N]
            Multiset.toFinsupp (m - N.pre t + N.post t) :=
          fires_iff.2 (by simp [fire, hle])
        @decidable_of_iff _ (Multiset.toFinsupp (m - N.pre t + N.post t) ⇝[N]
            Multiset.toFinsupp {o})
          ⟨fun h => ⟨hle, h⟩, fun h => h.2⟩
          (decidableReachable _ {o} (hb.of_reachable (hm.trans hf.reachable)))
      else isFalse fun h => hle h.1
  @decidable_of_iff _ _ relaxedSound_iff.symm (@Fintype.decidableForallFintype _ _ inst _)

omit [Fintype Place] [Fintype Transition] in
/-- Lazy soundness, stated for markings given by multisets. -/
theorem lazySound_iff {i o : Place} : N.toPetriNet.LazySound i o ↔
    (∀ m : Multiset Place, Multiset.toFinsupp {i} ⇝[N] m →
      ∃ m' : Multiset Place, m ⇝[N] m' ∧
        m'.count o = 1) ∧
    ∀ m : Multiset Place, Multiset.toFinsupp {i} ⇝[N] m →
      m.count o ≤ 1 := by
  simp only [LazySound, token_eq_toFinsupp]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · obtain ⟨M', hr, hM'⟩ := h1 _ hm
      obtain ⟨m', rfl⟩ := Multiset.toFinsupp.surjective M'
      exact ⟨m', hr, by simpa [Multiset.toFinsupp_apply] using hM'⟩
    · simpa [Multiset.toFinsupp_apply] using h2 _ hm
  · rintro ⟨h1, h2⟩
    refine ⟨fun M hM => ?_, fun M hM => ?_⟩
    · obtain ⟨m, rfl⟩ := Multiset.toFinsupp.surjective M
      obtain ⟨m', hr, hm'⟩ := h1 m hM
      exact ⟨_, hr, by simpa [Multiset.toFinsupp_apply] using hm'⟩
    · obtain ⟨m, rfl⟩ := Multiset.toFinsupp.surjective M
      simpa [Multiset.toFinsupp_apply] using h2 m hM

/-- Lazy soundness is decidable for bounded executable nets. -/
instance (i o : Place) [h : Fact (N.toPetriNet.Bounded (Multiset.toFinsupp {i}))] :
    Decidable (N.toPetriNet.LazySound i o) :=
  have hb := h.out
  @decidable_of_iff _ _ lazySound_iff.symm
    (@instDecidableAnd _ _
      (decidableForallReachable {i} hb _ fun m hm =>
        decidableExistsReachable m (hb.of_reachable hm) _ fun _ _ => inferInstance)
      (decidableForallReachable {i} hb _ fun _ _ => inferInstance))

/-- The flow relation of an executable net, on its places and transitions. -/
def arc : Place ⊕ Transition → Place ⊕ Transition → Prop
  | .inl p, .inr t => p ∈ N.pre t
  | .inr t, .inl p => p ∈ N.post t
  | _, _ => False

instance : DecidableRel N.arc := fun a b =>
  match a, b with
  | .inl p, .inr t => inferInstanceAs (Decidable (p ∈ N.pre t))
  | .inr t, .inl p => inferInstanceAs (Decidable (p ∈ N.post t))
  | .inl _, .inl _ => isFalse nofun
  | .inr _, .inr _ => isFalse nofun

omit [Fintype Place] [Fintype Transition] in
theorem arc_toPetriNet : N.toPetriNet.Arc = N.arc := by
  ext a b
  rcases a with p | t <;> rcases b with q | u <;>
    simp [PetriNet.Arc, arc, toPetriNet, Multiset.toFinsupp_apply, Multiset.count_pos]

omit [Fintype Place] [Fintype Transition] in
/-- Being a workflow net, stated for the flow relation of an executable net. -/
theorem isWFNet_iff {i o : Place} : N.toPetriNet.IsWFNet i o ↔ (∀ t, i ∉ N.post t) ∧
    (∀ t, o ∉ N.pre t) ∧ (∀ n, Relation.ReflTransGen N.arc (.inl i) n) ∧
      ∀ n, Relation.ReflTransGen N.arc n (.inl o) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rw [arc_toPetriNet] at h3 h4
    exact ⟨fun t => by simpa [toPetriNet, Multiset.toFinsupp_apply] using h1 t,
      fun t => by simpa [toPetriNet, Multiset.toFinsupp_apply] using h2 t, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    rw [← arc_toPetriNet] at h3 h4
    exact ⟨fun t => by simpa [toPetriNet, Multiset.toFinsupp_apply] using h1 t,
      fun t => by simpa [toPetriNet, Multiset.toFinsupp_apply] using h2 t, h3, h4⟩

/-- Being a workflow net is decidable for executable nets. -/
instance [DecidableEq Transition] (i o : Place) : Decidable (N.toPetriNet.IsWFNet i o) :=
  decidable_of_iff _ isWFNet_iff.symm

end ExecPetriNet

end Cslib
