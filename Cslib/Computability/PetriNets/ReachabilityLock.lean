/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.EffectiveSearch
public import Cslib.Computability.PetriNets.ReachabilityInstance
public import Cslib.Computability.PetriNets.VASSimulation
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Coded VAS for reachability instances of Petri nets

The lock construction of `VASSimulation` simulates a Petri net by a VAS whose coordinates are
`Place ⊕ Option Transition`. This file writes the same VAS as a *code* (`VASCode`), by a function
on lists, so that the translation from `ReachInstance` to `ReachInput` is computable.

The coordinates of the coded VAS are numbered as follows: the places `0, …, d - 1`, the lock `d`,
and the private place of the transition `k` is `d + 1 + k`. The correspondence with the coordinates
of the abstract construction is the equivalence `lockEquiv`, and `VAS.map` transports a VAS along
an equivalence of the coordinates.

## Main definitions

- `VAS.map`: renaming of the coordinates of a VAS.
- `ReachInstance.lockInput`: the coded VAS, source and target of an instance.

## Main statements

- `VAS.reach_map_iff`: reachability is invariant under renaming of the coordinates.
- `ReachInstance.primrec_lockInput`: the translation is primitive recursive.
- `ReachInstance.reachable_iff_reaches_lockInput`: an instance is reachable iff its coded VAS
  reaches the coded target from the coded source.
-/

@[expose] public section

namespace Cslib

namespace VAS

variable {ι κ : Type*}

/-- The VAS obtained by renaming the coordinates along an equivalence. -/
def map (e : ι ≃ κ) (V : VAS ι) : VAS κ :=
  ⟨V.acts.map (e.arrowCongr (Equiv.refl ℤ)).toEmbedding⟩

/-- The actions of the renamed VAS. -/
theorem mem_map_acts {e : ι ≃ κ} {V : VAS ι} {a' : κ → ℤ} :
    a' ∈ (V.map e).acts ↔ ∃ a ∈ V.acts, a' = a ∘ e.symm := by
  simp only [map, Finset.mem_map, Equiv.coe_toEmbedding]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h.symm ▸ rfl⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h ▸ rfl⟩⟩

/-- A move of the renamed VAS is a move of the original one. -/
theorem move_map_iff {e : ι ≃ κ} {V : VAS ι} {x y : VASConfig κ} :
    (V.map e).Move x y ↔ V.Move (x ∘ e) (y ∘ e) := by
  constructor
  · rintro ⟨a', ha', hy⟩
    obtain ⟨a, ha, rfl⟩ := mem_map_acts.1 ha'
    exact ⟨a, ha, funext fun i => by simpa [VASConfig.toInt] using congrFun hy (e i)⟩
  · rintro ⟨a, ha, hy⟩
    exact ⟨a ∘ e.symm, mem_map_acts.2 ⟨a, ha, rfl⟩,
      funext fun j => by simpa [VASConfig.toInt] using congrFun hy (e.symm j)⟩

/-- Reachability is invariant under renaming of the coordinates. -/
theorem reach_map_iff {e : ι ≃ κ} {V : VAS ι} {x y : VASConfig κ} :
    (V.map e).Reach x y ↔ V.Reach (x ∘ e) (y ∘ e) :=
  LTS.CanReach.iff_of_equiv (lts := (V.map e).lts) (lts' := V.lts)
    (e.symm.arrowCongr (Equiv.refl ℕ)) fun x y => move_map_iff (V := V) (x := x) (y := y)

end VAS

namespace PetriNet

namespace ReachInstance

/-- The list `f 0, …, f (d - 1), a, g 0, …, g (n - 1)`: the layout of the coordinates of the
coded VAS with a lock, `d` places, the lock and `n` private places. -/
def layout {α : Type*} (f g : ℕ → α) (a : α) (d n : ℕ) : List α :=
  (List.range d).map f ++ a :: (List.range n).map g

/-- The action `t⁻` of the transition number `k`, as a list: consume the preset, take the lock, mark
the private place of `k`. -/
def minusL (I : ReachInstance) (k : ℕ) : List ℤ :=
  layout (fun i => -((I.trans.getD k ([], [])).1.getD i 0 : ℤ))
    (fun s => if s = k then 1 else 0) (-1) I.d I.n

/-- The action `t⁺` of the transition number `k`, as a list: produce the postset, release the lock,
unmark the private place of `k`. -/
def plusL (I : ReachInstance) (k : ℕ) : List ℤ :=
  layout (fun i => ((I.trans.getD k ([], [])).2.getD i 0 : ℤ))
    (fun s => if s = k then -1 else 0) 1 I.d I.n

/-- The actions of the coded VAS with a lock of the net of an instance. -/
def lockActs (I : ReachInstance) : List (List ℤ) :=
  (List.range I.n).flatMap fun k => [I.minusL k, I.plusL k]

/-- The coded configuration of the VAS with a lock for the marking `M`: the marking, a free lock
and empty private places. -/
def lockMarking (I : ReachInstance) (M : List ℕ) : List ℕ :=
  layout (fun i => M.getD i 0) (fun _ => 0) 1 I.d I.n

/-- The coded VAS with a lock that simulates the net of an instance. -/
def lockCode (I : ReachInstance) : VASCode := (I.d + (I.n + 1), I.lockActs)

/-- The instance of reachability for coded VAS that simulates an instance of reachability for
Petri nets. -/
def lockInput (I : ReachInstance) : ReachInput :=
  (I.lockCode, I.lockMarking I.init, I.lockMarking I.target)

/-- The equivalence between the coordinates of `PetriNet.toVAS` and the numbering of the coded
VAS: the places `0, …, d - 1`, the lock `d`, and the private place of the transition `k`, which is
`d + 1 + k`. -/
def lockEquiv (d n : ℕ) : LockDim (Fin d) (Fin n) ≃ Fin (d + (n + 1)) :=
  (Equiv.sumCongr (Equiv.refl _) (finSuccEquiv n).symm).trans finSumFinEquiv

/-- Reading the layout at the coordinate `lockEquiv x`. -/
theorem getD_layout_lockEquiv {α : Type*} (f g : ℕ → α) (a z : α) {d n : ℕ}
    (x : LockDim (Fin d) (Fin n)) :
    (layout f g a d n).getD (lockEquiv d n x) z = Sum.elim (fun p : Fin d => f p)
      (fun o : Option (Fin n) => o.elim a fun s => g s) x := by
  rcases x with p | _ | s <;>
    simp [layout, lockEquiv, List.getD_eq_getElem?_getD, List.getElem?_append_left]

/-- The vector of a layout of integers, with renamed coordinates. -/
theorem vecZ_layout {d n : ℕ} (f g : ℕ → ℤ) (a : ℤ) :
    vecZ (d + (n + 1)) (layout f g a d n) = Sum.elim (fun p : Fin d => f p)
      (fun o : Option (Fin n) => o.elim a fun s => g s) ∘ (lockEquiv d n).symm := by
  funext j
  obtain ⟨x, rfl⟩ := (lockEquiv d n).surjective j
  simpa [vecZ] using getD_layout_lockEquiv f g a 0 x

/-- The vector of a layout of natural numbers, with renamed coordinates. -/
theorem vecN_layout {d n : ℕ} (f g : ℕ → ℕ) (a : ℕ) :
    vecN (d + (n + 1)) (layout f g a d n) = Sum.elim (fun p : Fin d => f p)
      (fun o : Option (Fin n) => o.elim a fun s => g s) ∘ (lockEquiv d n).symm := by
  funext j
  obtain ⟨x, rfl⟩ := (lockEquiv d n).surjective j
  simpa [vecN] using getD_layout_lockEquiv f g a 0 x

variable {I : ReachInstance}

/-- The coded action `t⁻` is the abstract one, with renamed coordinates. -/
theorem vecZ_minusL (k : Fin I.n) :
    vecZ (I.d + (I.n + 1)) (I.minusL k) =
      minusAct I.toPetriNet k ∘ (lockEquiv I.d I.n).symm := by
  rw [minusL, vecZ_layout]
  congr 1
  funext x
  rcases x with p | _ | s <;> simp [minusAct, ind, toPetriNet, Fin.ext_iff]

/-- The coded action `t⁺` is the abstract one, with renamed coordinates. -/
theorem vecZ_plusL (k : Fin I.n) :
    vecZ (I.d + (I.n + 1)) (I.plusL k) =
      plusAct I.toPetriNet k ∘ (lockEquiv I.d I.n).symm := by
  rw [plusL, vecZ_layout]
  congr 1
  funext x
  rcases x with p | _ | s <;> simp [plusAct, ind, toPetriNet, Fin.ext_iff, neg_ite]

/-- The coded VAS with a lock is the VAS with a lock of the net, with renamed coordinates. -/
theorem lockCode_toVAS :
    I.lockCode.toVAS = (toVAS I.toPetriNet).map (lockEquiv I.d I.n) := by
  refine congrArg VAS.mk (Finset.ext fun a' => ?_)
  refine (VASCode.mem_acts (c := lockCode I)).trans (Iff.trans ?_ VAS.mem_map_acts.symm)
  simp only [lockCode, lockActs, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, mem_acts_toVAS]
  constructor
  · rintro ⟨l, ⟨k, hk, rfl | rfl⟩, rfl⟩
    · exact ⟨_, ⟨_, Or.inl rfl⟩, vecZ_minusL (I := I) ⟨k, hk⟩⟩
    · exact ⟨_, ⟨_, Or.inr rfl⟩, vecZ_plusL (I := I) ⟨k, hk⟩⟩
  · rintro ⟨_, ⟨t, rfl | rfl⟩, rfl⟩
    · exact ⟨_, ⟨t.1, t.2, Or.inl rfl⟩, vecZ_minusL t⟩
    · exact ⟨_, ⟨t.1, t.2, Or.inr rfl⟩, vecZ_plusL t⟩

/-- The embedding of the marking of a list, as a function of the coordinates. -/
theorem embed_toMarking (l : List ℕ) :
    (embed (toMarking I.d l) : VASConfig (LockDim (Fin I.d) (Fin I.n))) =
      Sum.elim (fun p : Fin I.d => l.getD p 0) fun o => o.elim 1 fun _ => 0 := by
  funext x
  rcases x with p | _ | s <;> simp [embed, lockCfg]

/-- **Correctness of the computable lock construction**: an instance of reachability for Petri nets
is reachable iff the coded VAS with a lock reaches the coded target from the coded source. -/
theorem reachable_iff_reaches_lockInput : I.Reachable ↔ I.lockInput.Reaches := by
  have h (x y : List ℕ) : I.lockCode.toVAS.Reach (vecN (I.d + (I.n + 1)) x)
      (vecN (I.d + (I.n + 1)) y) ↔ ((toVAS I.toPetriNet).map (lockEquiv I.d I.n)).Reach
        (vecN (I.d + (I.n + 1)) x) (vecN (I.d + (I.n + 1)) y) := by
    rw [lockCode_toVAS]
    exact Iff.rfl
  rw [Reachable, reachable_iff_vas_reach, ReachInput.Reaches]
  refine Iff.trans ?_ (h (I.lockMarking I.init) (I.lockMarking I.target)).symm
  rw [VAS.reach_map_iff, lockMarking, lockMarking, vecN_layout, vecN_layout]
  simp only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  rw [embed_toMarking, embed_toMarking]

/-! ### The construction is primitive recursive -/

open Primrec

/-- Layouts are primitive recursive. -/
theorem primrec_layout {α σ : Type*} [Primcodable α] [Primcodable σ] {f g : α → ℕ → σ}
    {a : α → σ} {d n : α → ℕ} (hf : Primrec₂ f) (hg : Primrec₂ g) (ha : Primrec a)
    (hd : Primrec d) (hn : Primrec n) :
    Primrec fun x => layout (f x) (g x) (a x) (d x) (n x) :=
  list_append.comp (list_map (list_range.comp hd) hf)
    (list_cons.comp ha (list_map (list_range.comp hn) hg))

/-- The coded action `t⁻` is primitive recursive. -/
theorem primrec_minusL : Primrec fun p : ReachInstance × ℕ => p.1.minusL p.2 := by
  have ht : Primrec fun p : ReachInstance × ℕ => p.1.trans.getD p.2 ([], []) :=
    (list_getD _).comp (primrec_trans.comp fst) snd
  exact primrec_layout
    (Presburger.PrimrecArith.primrec_neg.comp (Presburger.PrimrecArith.primrec_natCast.comp
      ((list_getD 0).comp (fst.comp (ht.comp fst)) snd))).to₂
    (Primrec.ite (Primrec.eq.comp snd (snd.comp fst)) (const 1) (const 0)).to₂
    (const _) (primrec_d.comp fst) (list_length.comp (primrec_trans.comp fst))

/-- The coded action `t⁺` is primitive recursive. -/
theorem primrec_plusL : Primrec fun p : ReachInstance × ℕ => p.1.plusL p.2 := by
  have ht : Primrec fun p : ReachInstance × ℕ => p.1.trans.getD p.2 ([], []) :=
    (list_getD _).comp (primrec_trans.comp fst) snd
  exact primrec_layout
    (Presburger.PrimrecArith.primrec_natCast.comp
      ((list_getD 0).comp (snd.comp (ht.comp fst)) snd)).to₂
    (Primrec.ite (Primrec.eq.comp snd (snd.comp fst)) (const (-1)) (const 0)).to₂
    (const _) (primrec_d.comp fst) (list_length.comp (primrec_trans.comp fst))

/-- The actions of the coded VAS with a lock are primitive recursive. -/
theorem primrec_lockActs : Primrec lockActs :=
  list_flatMap (list_range.comp (list_length.comp primrec_trans))
    (list_cons.comp (primrec_minusL.comp (fst.pair snd))
      (list_cons.comp (primrec_plusL.comp (fst.pair snd)) (const []))).to₂

/-- The coded configurations of the VAS with a lock are primitive recursive. -/
theorem primrec_lockMarking : Primrec fun p : ReachInstance × List ℕ => p.1.lockMarking p.2 :=
  primrec_layout ((list_getD 0).comp (snd.comp fst) snd).to₂ (const 0).to₂ (const _)
    (primrec_d.comp fst) (list_length.comp (primrec_trans.comp fst))

/-- **The translation from instances of Petri net reachability to coded VAS reachability is
primitive recursive.** -/
theorem primrec_lockInput : Primrec lockInput :=
  ((nat_add.comp primrec_d (Primrec.succ.comp (list_length.comp primrec_trans))).pair
    primrec_lockActs).pair
    ((primrec_lockMarking.comp (Primrec.id.pair primrec_init)).pair
      (primrec_lockMarking.comp (Primrec.id.pair primrec_target)))

end ReachInstance

end PetriNet

end Cslib
