/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Decision.Soundness
public import Cslib.Foundations.Relation.FiniteClosure
public import Cslib.Computability.PetriNets.SoundnessNotions

/-! # Deciding the notions of soundness

For nets with finitely many places and transitions, the notions of soundness defined in
`Cslib.Computability.PetriNets.SoundnessNotions` are decidable whenever the relevant initial marking
is bounded. Boundedness is supplied as a `Fact`, which `decide` can establish with
`PetriNet.instDecidableBounded`.

The decision procedures reduce each notion to finite checks over the finite set of markings
reachable from the initial marking, using `PetriNet.decidableForallReachable`,
`PetriNet.decidableExistsReachable` and `PetriNet.decidableReachable`.

Generalized soundness is not decided here.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place Transition : Type*} [DecidableEq Place] [Fintype Place] [Fintype Transition]
  {N : PetriNet Place Transition}

/-- Easy soundness is decidable for bounded nets. -/
instance (i o : Place) [h : Fact (N.Bounded (token i))] : Decidable (N.EasySound i o) :=
  decidableReachable _ _ h.out

/-- `k`-soundness is decidable, if `k` tokens in the source give a bounded marking. -/
def decidableKSound (i o : Place) (k : ℕ) (hb : N.Bounded (k • token i)) :
    Decidable (N.KSound i o k) :=
  decidableForallReachable _ hb _ fun M hM => decidableReachable M _ (hb.of_reachable hM)

instance (i o : Place) (k : ℕ) [h : Fact (N.Bounded (k • token i))] :
    Decidable (N.KSound i o k) :=
  decidableKSound i o k h.out

/-- Up-to-`k` soundness is decidable, if `k` tokens in the source give a bounded marking. -/
instance (i o : Place) (k : ℕ) [h : Fact (N.Bounded (k • token i))] :
    Decidable (N.UpToKSound i o k) :=
  @Nat.decidableBallLE k (fun l _ => N.KSound i o l) fun l hl =>
    decidableKSound i o l (h.out.mono_marking (nsmul_le_nsmul_left zero_le hl))

/-- Weak soundness is decidable for bounded nets. -/
instance (i o : Place) [h : Fact (N.Bounded (token i))] : Decidable (N.WeakSound i o) :=
  decidableKSound i o 1 (by simpa using h.out)

omit [Fintype Place] [Fintype Transition] in
/-- Relaxed soundness, stated with the computable firing rule. -/
theorem relaxedSound_iff {i o : Place} : N.RelaxedSound i o ↔
    ∀ t, ∃ M, token i ⇝[N] M ∧ M [t⟩[N] ∧ N.fire M t ⇝[N] token o := by
  simp only [RelaxedSound, fires_iff]
  refine forall_congr' fun t => ⟨fun ⟨M, _, hM, ⟨hen, rfl⟩, hc⟩ => ⟨M, hM, hen, hc⟩,
    fun ⟨M, hM, hen, hc⟩ => ⟨M, _, hM, ⟨hen, rfl⟩, hc⟩⟩

/-- Relaxed soundness is decidable for bounded nets. -/
instance (i o : Place) [h : Fact (N.Bounded (token i))] : Decidable (N.RelaxedSound i o) :=
  have inst : ∀ t, Decidable (∃ M, token i ⇝[N] M ∧ M [t⟩[N] ∧ N.fire M t ⇝[N] token o) :=
    fun t => decidableExistsReachable _ h.out _ fun M hM =>
      if hen : M [t⟩[N] then
        have hf : M [t⟩[N] N.fire M t := fires_iff.2 ⟨hen, rfl⟩
        @decidable_of_iff _ _ ⟨fun h => ⟨hen, h⟩, fun h => h.2⟩
          (decidableReachable _ _ (h.out.of_reachable (hM.trans hf.reachable)))
      else isFalse fun h => hen h.1
  @decidable_of_iff _ _ relaxedSound_iff.symm (@Fintype.decidableForallFintype _ _ inst _)

/-- Lazy soundness is decidable for bounded nets. -/
instance (i o : Place) [h : Fact (N.Bounded (token i))] : Decidable (N.LazySound i o) :=
  @instDecidableAnd _ _
    (decidableForallReachable _ h.out _ fun M hM =>
      decidableExistsReachable M (h.out.of_reachable hM) _ fun _ _ => inferInstance)
    (decidableForallReachable _ h.out _ fun _ _ => inferInstance)

instance : DecidableRel N.Arc := fun a b =>
  match a, b with
  | .inl p, .inr t => inferInstanceAs (Decidable (p ∈ N.pre t))
  | .inr t, .inl p => inferInstanceAs (Decidable (p ∈ N.post t))
  | .inl _, .inl _ => isFalse nofun
  | .inr _, .inr _ => isFalse nofun

/-- Being a workflow net is decidable. -/
instance [DecidableEq Transition] (i o : Place) : Decidable (N.IsWFNet i o) :=
  decidable_of_iff ((∀ t, i ∉ N.post t) ∧ (∀ t, o ∉ N.pre t) ∧
      (∀ n, Relation.ReflTransGen N.Arc (.inl i) n) ∧ ∀ n, Relation.ReflTransGen N.Arc n (.inl o))
    ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩⟩

end PetriNet

end Cslib
