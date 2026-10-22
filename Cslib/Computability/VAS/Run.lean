/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.Basic
public import Cslib.Foundations.Data.List.IsChainFromTo

/-! # Runs of a VAS

* `VAS.Run`: a non-empty chain of configurations, with `src`, `tgt`, `dir`, `single`, `cons`.
  Its configurations form a `List.IsChainFromTo` of moves (`VAS.Run.isChainFromTo`), and
  `VAS.Run.ofChain` turns any such chain into a run.
* `VAS.Run.exists_run_iff_reach`: reachability is the existence of a run.
* `VAS.Run.exists_run_through`, `VAS.Run.exists_run_pair`: runs through a given configuration or
  a given pair of consecutive configurations.
* `Cslib.relVec`: the encoding of a pair of configurations in `ℤ^(ι ⊕ ι)`.
-/

@[expose] public section

namespace Cslib

variable {ι : Type*}

/-- The encoding of a pair of configurations as a vector of `ℤ^(ι ⊕ ι)`. -/
def relVec (x y : VASConfig ι) : ι ⊕ ι → ℤ := Sum.elim x.toInt y.toInt

namespace VAS

/-- A run of the VAS: a non-empty word of configurations, consecutive ones related by a move. The
action `a_j = c_j - c_{j-1}` is determined by the word. -/
structure Run (V : VAS ι) where
  /-- The word of configurations `c_0 ... c_k`. -/
  cfgs : List (VASConfig ι)
  /-- A run is non-empty. -/
  ne : cfgs ≠ []
  /-- Consecutive configurations are related by a move. -/
  chain : cfgs.IsChain V.Move

namespace Run

variable {V : VAS ι}

/-- The source configuration of a run. -/
def src (π : V.Run) : VASConfig ι := π.cfgs.head π.ne

/-- The target configuration of a run. -/
def tgt (π : V.Run) : VASConfig ι := π.cfgs.getLast π.ne

/-- The direction `(src π, tgt π)` of a run. -/
def dir (π : V.Run) : VASConfig ι × VASConfig ι := (π.src, π.tgt)

/-- The configurations of a run form a chain of moves from its source to its target. -/
theorem isChainFromTo (π : V.Run) : π.cfgs.IsChainFromTo V.Move π.src π.tgt :=
  ⟨π.chain, π.ne, rfl, rfl⟩

/-- A chain of moves from `a` to `b` is a run. -/
def ofChain {l : List (VASConfig ι)} {a b : VASConfig ι} (h : l.IsChainFromTo V.Move a b) :
    Run V :=
  ⟨l, h.ne_nil, h.isChain⟩

@[simp] theorem ofChain_cfgs {l : List (VASConfig ι)} {a b : VASConfig ι}
    (h : l.IsChainFromTo V.Move a b) : (ofChain h).cfgs = l := rfl

theorem src_ofChain {l : List (VASConfig ι)} {a b : VASConfig ι}
    (h : l.IsChainFromTo V.Move a b) : (ofChain h).src = a := h.head_eq

theorem tgt_ofChain {l : List (VASConfig ι)} {a b : VASConfig ι}
    (h : l.IsChainFromTo V.Move a b) : (ofChain h).tgt = b := h.getLast_eq

/-- The run of a single configuration. -/
def single (V : VAS ι) (c : VASConfig ι) : Run V := ⟨[c], by simp, .singleton c⟩

/-- Prepending a configuration to a run, given a move to its source. -/
def cons (c : VASConfig ι) (π : V.Run) (h : V.Move c π.src) : Run V :=
  ⟨c :: π.cfgs, List.cons_ne_nil _ _, π.chain.cons_of_ne_nil π.ne h⟩

@[simp] theorem cons_cfgs (c : VASConfig ι) (π : V.Run) (h : V.Move c π.src) :
    (cons c π h).cfgs = c :: π.cfgs := rfl

@[simp] theorem single_cfgs (c : VASConfig ι) : (single V c).cfgs = [c] := rfl

@[simp] theorem src_single (c : VASConfig ι) : (single V c).src = c := rfl

@[simp] theorem tgt_single (c : VASConfig ι) : (single V c).tgt = c := rfl

@[simp] theorem src_cons (c : VASConfig ι) (π : V.Run) (h : V.Move c π.src) :
    (cons c π h).src = c := rfl

@[simp] theorem tgt_cons (c : VASConfig ι) (π : V.Run) (h : V.Move c π.src) :
    (cons c π h).tgt = π.tgt := by
  simp only [tgt, cons_cfgs, List.getLast_cons π.ne]

/-- A run reaches its target from its source. -/
theorem reach (π : V.Run) : V.Reach π.src π.tgt :=
  V.reach_iff_reflTransGen.2 π.isChainFromTo.reflTransGen

/-- Existence of a run is reachability. -/
theorem exists_run_iff_reach {x y : VASConfig ι} :
    (∃ π : Run V, π.src = x ∧ π.tgt = y) ↔ V.Reach x y := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨π, rfl, rfl⟩
    exact π.reach
  · obtain ⟨l, hl, hne, hx, hy⟩ :=
      List.exists_isChain_ne_nil_of_relationReflTransGen (V.reach_iff_reflTransGen.1 h)
    exact ⟨⟨l, hl, hne⟩, hx, hy⟩

/-- The first configuration of a run is its source. -/
theorem head?_cfgs (π : V.Run) : π.cfgs.head? = some π.src :=
  List.head?_eq_some_head π.ne

/-- The last configuration of a run is its target. -/
theorem getLast?_cfgs (π : V.Run) : π.cfgs.getLast? = some π.tgt :=
  List.getLast?_eq_some_getLast π.ne

/-- Every configuration of a run is reachable from the source and reaches the target. -/
theorem mem_reach (π : V.Run) {q : VASConfig ι} (hq : q ∈ π.cfgs) :
    V.Reach π.src q ∧ V.Reach q π.tgt :=
  ⟨V.reach_iff_reflTransGen.2 (π.isChainFromTo.reflTransGen_of_mem hq),
    V.reach_iff_reflTransGen.2 (π.isChainFromTo.reflTransGen_of_mem' hq)⟩

/-- Two consecutive configurations of a run are related by a move, and sit between the source
and the target. -/
theorem move_of_cfgs_eq (π : V.Run) {L₁ L₂ : List (VASConfig ι)} {q q' : VASConfig ι}
    (h : π.cfgs = L₁ ++ q :: q' :: L₂) :
    V.Move q q' ∧ V.Reach π.src q ∧ V.Reach q' π.tgt := by
  refine ⟨?_, (π.mem_reach (q := q) (by simp [h])).1, (π.mem_reach (q := q') (by simp [h])).2⟩
  have := π.chain
  rw [h] at this
  exact (List.isChain_append_cons_cons.1 this).2.1

/-- A run through a given configuration between two given configurations. -/
theorem exists_run_through {x q y : VASConfig ι} (h₁ : V.Reach x q) (h₂ : V.Reach q y) :
    ∃ π : V.Run, π.src = x ∧ π.tgt = y ∧ q ∈ π.cfgs := by
  obtain ⟨π₁, rfl, rfl⟩ := exists_run_iff_reach.2 h₁
  obtain ⟨π₂, hq, rfl⟩ := exists_run_iff_reach.2 h₂
  have hc := π₁.isChainFromTo.append_dropLast (hq ▸ π₂.isChainFromTo)
  refine ⟨ofChain hc, src_ofChain hc, tgt_ofChain hc, ?_⟩
  simpa using Or.inr (hq ▸ List.head_mem π₂.ne)

/-- A run with a given pair of consecutive configurations. -/
theorem exists_run_pair {x q q' y : VASConfig ι} (h₁ : V.Reach x q) (hm : V.Move q q')
    (h₂ : V.Reach q' y) :
    ∃ π : V.Run, π.src = x ∧ π.tgt = y ∧ ∃ L₁ L₂, π.cfgs = L₁ ++ q :: q' :: L₂ := by
  obtain ⟨π₁, rfl, rfl⟩ := exists_run_iff_reach.2 h₁
  obtain ⟨π₂, rfl, rfl⟩ := exists_run_iff_reach.2 h₂
  have hc := π₁.isChainFromTo.append_dropLast (π₂.isChainFromTo.cons hm)
  refine ⟨ofChain hc, src_ofChain hc, tgt_ofChain hc, π₁.cfgs.dropLast, π₂.cfgs.tail, ?_⟩
  exact congrArg (fun l => π₁.cfgs.dropLast ++ π₁.tgt :: l) (List.cons_head_tail π₂.ne).symm

end Run

end VAS

end Cslib
