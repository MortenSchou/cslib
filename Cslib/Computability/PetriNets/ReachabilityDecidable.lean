/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.ReachabilityLock
public import Cslib.Computability.VAS.Decidable
public import Cslib.Init
public import Mathlib.Computability.RE
public import Mathlib.Computability.Partrec

/-! # Decidability of reachability of Petri nets

This file states and proves the theorem that reachability of Petri nets (equivalently, of vector
addition systems with states) is decidable; see the README of this directory.

In classical logic `Decidable P` is vacuous, so the theorem is stated as a computability
statement about the encoded instances of `ReachabilityInstance`:
`ReachabilityDecidable` says that the predicate `ReachInstance.Reachable` on instances is
`ComputablePred` in the sense of Mathlib (its indicator is a computable function).
By `reachabilityDecidable_iff` this is the conjunction of two semi-decidability statements:

- `reachable_rePred`: `REPred Reachable`. A semi-decision procedure enumerates all
  finite sequences of transition indices and runs each of them (`runL`), which is primitive
  recursive; this is the easy half.
- `REPred (¬ Reachable)`: the hard half, and the content of the theorem of Mayr, Kosaraju,
  Lambert and Leroux. A net is simulated by a coded VAS with a lock (`ReachabilityLock`), and
  non-reachability of that VAS is recursively enumerable by Leroux's Presburger inductive
  invariants (`Cslib.Computability.VAS.Decidable`).

## Main definitions

- `PetriNet.ReachabilityDecidable`: the statement of the theorem.

## Main statements

- `PetriNet.reachabilityDecidable_iff`: decidability is semi-decidability of reachability and of
  non-reachability.
- `PetriNet.reachable_rePred`: reachability is recursively enumerable.
- `PetriNet.reachabilityDecidable`: **reachability in Petri nets is decidable**.

## References

* [J. Leroux, *Vector Addition Systems Reachability Problem (A Simpler Solution)*][Leroux2012]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

namespace ReachInstance

open Primrec

/-- Firing a step on lists is primitive recursive. -/
theorem primrec_stepL : Primrec fun p : ReachInstance × List ℕ × ℕ => p.1.stepL p.2.1 p.2.2 := by
  have hd : Primrec fun p : ReachInstance × List ℕ × ℕ => p.1.d := primrec_d.comp fst
  have ht : Primrec fun p : ReachInstance × List ℕ × ℕ => p.1.trans := primrec_trans.comp fst
  have hM : Primrec fun p : ReachInstance × List ℕ × ℕ => p.2.1 := fst.comp snd
  have hk : Primrec fun p : ReachInstance × List ℕ × ℕ => p.2.2 := snd.comp snd
  have hR : PrimrecRel fun (i : ℕ) (b : (List ℕ × List ℕ) × List ℕ) =>
      b.1.1.getD i 0 ≤ b.2.getD i 0 :=
    nat_le.comp ((list_getD 0).comp (fst.comp (fst.comp snd)) fst)
      ((list_getD 0).comp (snd.comp snd) fst)
  refine option_bind (list_getElem?.comp ht hk) <| Primrec.ite
    (c := fun q : (ReachInstance × List ℕ × ℕ) × (List ℕ × List ℕ) =>
      ∀ i < q.1.1.d, q.2.1.getD i 0 ≤ q.1.2.1.getD i 0) ?_ ?_ (const none)
  · exact ((PrimrecRel.forall_mem_list hR).comp (list_range.comp (hd.comp fst))
      (snd.pair (hM.comp fst))).of_eq fun _ => by simp
  · refine option_some.comp (list_map (list_range.comp (hd.comp fst)) ?_)
    refine nat_add.comp (nat_sub.comp ?_ ?_) ?_
    · exact (list_getD 0).comp (hM.comp (fst.comp fst)) snd
    · exact (list_getD 0).comp (fst.comp (snd.comp fst)) snd
    · exact (list_getD 0).comp (snd.comp (snd.comp fst)) snd

/-- Firing a list of transition indices is primitive recursive. -/
theorem primrec_runL :
    Primrec fun p : ReachInstance × List ℕ × List ℕ => p.1.runL p.2.1 p.2.2 := by
  unfold runL
  refine list_foldl (h := fun (p : ReachInstance × List ℕ × List ℕ) (q : Option (List ℕ) × ℕ) =>
      q.1.bind fun M => p.1.stepL M q.2) (snd.comp snd) (option_some.comp (fst.comp snd)) ?_
  exact option_bind (fst.comp snd) (primrec_stepL.comp
    (fst.comp (fst.comp fst) |>.pair (snd.pair (snd.comp (snd.comp fst))))).to₂

/-- Whether a list is accepted is a primitive recursive predicate. -/
theorem primrec_accepts : PrimrecPred fun p : ReachInstance × List ℕ => p.1.Accepts p.2 := by
  classical
  have hr : Primrec fun p : ReachInstance × List ℕ => p.1.runL p.1.init p.2 :=
    primrec_runL.comp (fst.pair ((primrec_init.comp fst).pair snd))
  have hR : PrimrecRel fun (i : ℕ) (q : (ReachInstance × List ℕ) × List ℕ) =>
      q.2.getD i 0 = q.1.1.target.getD i 0 :=
    Primrec.eq.comp ((list_getD 0).comp (snd.comp snd) fst)
      ((list_getD 0).comp (primrec_target.comp (fst.comp (fst.comp snd))) fst)
  have hP : PrimrecPred fun q : (ReachInstance × List ℕ) × List ℕ =>
      ∀ i < q.1.1.d, q.2.getD i 0 = q.1.1.target.getD i 0 :=
    ((PrimrecRel.forall_mem_list hR).comp (list_range.comp (primrec_d.comp (fst.comp fst)))
      Primrec.id).of_eq fun _ => by simp
  refine ⟨inferInstance, (option_casesOn hr (const false) hP.decide.to₂).of_eq fun p => ?_⟩
  rcases h : p.1.runL p.1.init p.2 with _ | M' <;> simp [Accepts, h]

end ReachInstance

/-- The statement of the theorem that reachability is decidable: the predicate `Reachable` on
encoded instances has a computable indicator function. -/
def ReachabilityDecidable : Prop := ComputablePred ReachInstance.Reachable

/-- Reachability is recursively enumerable: this is the easy half of the decidability of
reachability. -/
theorem reachable_rePred : REPred ReachInstance.Reachable :=
  (rePred_exists_of_computablePred (R := fun (I : ReachInstance) (σ : List ℕ) => I.Accepts σ)
    ReachInstance.primrec_accepts.computablePred).of_eq fun _ =>
      ReachInstance.reachable_iff_exists_accepts.symm

/-- Reachability is decidable iff both reachability and non-reachability are recursively
enumerable. By `reachable_rePred` the remaining part of the theorem is `REPred (¬ Reachable)`. -/
theorem reachabilityDecidable_iff : ReachabilityDecidable ↔
    REPred ReachInstance.Reachable ∧ REPred fun I : ReachInstance => ¬ I.Reachable :=
  ComputablePred.computable_iff_re_compl_re'

/-- **Reachability in Petri nets is decidable**: the predicate that holds of a coded net with an
initial and a target marking when the target is reachable from the initial marking is computable.
Non-reachability of an instance is semi-decided by translating it to a coded VAS with a lock
(`ReachInstance.lockInput`) and searching for a Presburger inductive invariant as a certificate. -/
theorem reachabilityDecidable : ReachabilityDecidable := by
  refine reachabilityDecidable_iff.2 ⟨reachable_rePred, ?_⟩
  have h1 : REPred fun I : ReachInstance => ¬ (ReachInstance.lockInput I).Reaches :=
    VAS.not_reaches_rePred.comp ReachInstance.primrec_lockInput.to_comp
  exact h1.of_eq fun I => not_congr ReachInstance.reachable_iff_reaches_lockInput.symm

end PetriNet

end Cslib
