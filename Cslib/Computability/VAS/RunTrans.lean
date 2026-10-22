/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.TransformerAsymp
public import Cslib.Computability.VAS.AsympDefinable

/-! # The transformer relation along a run

For a run `π = c_0 … c_k`, the relation `π▷` holds between `u` and `v` iff there are
`v_0 = u, …, v_{k+1} = v` with `v_j ▷_{c_j} v_{j+1}` (Leroux, Section 6). It is a composition of
transformer relations, hence periodic and asymptotically definable.

## Main definitions

* `VAS.runTransList`, `VAS.runTrans`: the relation along a list of configurations, along a run.
* `Cslib.relVecSet`: the encoding of a set of pairs of configurations in `ℤ^(ι ⊕ ι)`.

## Main results

* `VAS.reach_of_runTransList`: `(u, v) ∈ π▷` gives a run from `src π + u` to `tgt π + v`.
* `VAS.runTrans_asympDefinable`: `π▷` is periodic and asymptotically definable.

## References

* [J. Leroux, *Vector Addition Systems Reachability Problem (A Simpler Solution)*][Leroux2012]
-/

@[expose] public section

namespace Cslib

variable {ι : Type*}

/-- The integer view of configurations is injective. -/
theorem VASConfig.toInt_injective : Function.Injective (VASConfig.toInt : VASConfig ι → ι → ℤ) := by
  intro c d h
  funext i
  have h' : ((c i : ℕ) : ℤ) = (d i : ℤ) := congrFun h i
  exact_mod_cast h'

/-- The encoding in `ℤ^(ι ⊕ ι)` of a set of pairs of configurations. -/
def relVecSet (S : Set (VASConfig ι × VASConfig ι)) : Set (ι ⊕ ι → ℤ) := VAS.relVecHom '' S

namespace VAS

variable (V : VAS ι)

/-- The transformer relation along a list of configurations `c_0 … c_k`: `(u, v)` is related iff
there are `v_0 = u, …, v_{k+1} = v` with `c_j + v_j →* c_j + v_{j+1}`. -/
def runTransList (l : List (VASConfig ι)) : Set (VASConfig ι × VASConfig ι) :=
  {p | ∃ vs : ℕ → VASConfig ι, vs 0 = p.1 ∧ vs l.length = p.2 ∧
    ∀ (j : ℕ) (h : j < l.length), V.Reach (l[j] + vs j) (l[j] + vs (j + 1))}

variable {V}

/-- The transformer relation `π▷` along a run. -/
def Run.trans (π : V.Run) : Set (VASConfig ι × VASConfig ι) := runTransList V π.cfgs

/-- The relation along a one-element list is the transformer relation. -/
theorem runTransList_singleton (c : VASConfig ι) :
    runTransList V [c] = {p | V.Reach (c + p.1) (c + p.2)} := by
  ext ⟨u, w⟩
  refine ⟨fun ⟨vs, h0, h1, h⟩ => ?_, fun h => ⟨fun j => if j = 0 then u else w, by simp, by simp,
    fun j hj => ?_⟩⟩
  · rw [List.length_singleton] at h1
    simpa [h0, h1] using h 0 (by simp)
  · obtain rfl : j = 0 := by simpa using hj
    simpa using h

/-- Peeling the first configuration off a list. -/
theorem runTransList_cons (c : VASConfig ι) (l : List (VASConfig ι)) :
    runTransList V (c :: l) =
      {p | ∃ z, V.Reach (c + p.1) (c + z) ∧ (z, p.2) ∈ runTransList V l} := by
  ext ⟨u, w⟩
  constructor
  · rintro ⟨vs, h0, h1, h⟩
    refine ⟨vs 1, ?_, fun j => vs (j + 1), rfl, ?_, ?_⟩
    · have := h 0 (by simp)
      simpa only [List.getElem_cons_zero, h0, zero_add] using this
    · simpa using h1
    · intro j hj
      have := h (j + 1) (by simpa using hj)
      simpa using this
  · rintro ⟨z, hz, vs', h0, h1, h⟩
    refine ⟨fun j => match j with | 0 => u | j + 1 => vs' j, rfl, ?_, ?_⟩
    · simpa using h1
    · intro j hj
      cases j with
      | zero => simpa [h0] using hz
      | succ j => simpa using h j (by simpa using hj)

/-- A run of the form `l` (a chain of moves) and `(u, v) ∈ l▷` give a run from `head l + u` to
`last l + v`. -/
theorem reach_of_runTransList {l : List (VASConfig ι)} (hl : l.IsChain V.Move) :
    ∀ {x y u v : VASConfig ι}, l.head? = some x → l.getLast? = some y →
      (u, v) ∈ runTransList V l → V.Reach (x + u) (y + v) := by
  induction l with
  | nil => intro x y u v hx; simp at hx
  | cons c l ih =>
    intro x y u v hx hy huv
    simp only [List.head?_cons, Option.some.injEq] at hx
    subst hx
    cases l with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hy
      subst hy
      rw [runTransList_singleton] at huv
      exact huv
    | cons d l =>
      rw [runTransList_cons] at huv
      obtain ⟨z, hz, hzv⟩ := huv
      have hcd : V.Move c d := (List.isChain_cons_cons.1 hl).1
      have hy' : (d :: l).getLast? = some y := by
        simpa only [List.getLast?_cons_cons] using hy
      have := ih (List.isChain_cons_cons.1 hl).2 rfl hy' hzv
      refine hz.trans ((?_ : V.Reach (c + z) (d + z)).trans this)
      exact Reach.single (by simpa only [add_comm] using hcd.add_left z)

/-- A run is reachability from its source plus `u` to its target plus `v`. -/
theorem Run.reach_of_trans (π : V.Run) {u v : VASConfig ι} (h : (u, v) ∈ π.trans) :
    V.Reach (π.src + u) (π.tgt + v) :=
  reach_of_runTransList π.chain π.head?_cfgs π.getLast?_cfgs h

/-- The encoding of the relation along a list is the composition of the transformer relations. -/
theorem relVecSet_cons (c : VASConfig ι) (S : Set (VASConfig ι × VASConfig ι)) :
    relVecSet {p | ∃ z, V.Reach (c + p.1) (c + z) ∧ (z, p.2) ∈ S} =
      relComp (V.transSet c) (relVecSet S) := by
  ext w
  constructor
  · rintro ⟨⟨u, v⟩, ⟨z, hz, hzv⟩, rfl⟩
    refine ⟨z.toInt, ⟨u, z, rfl, hz⟩, ⟨(z, v), hzv, rfl⟩⟩
  · rintro ⟨z', ⟨x, y, h1, hxy⟩, ⟨⟨a, b⟩, hab, h2⟩⟩
    have hx : ∀ i, x.toInt i = w (Sum.inl i) := fun i => congrFun h1 (Sum.inl i)
    have hy : ∀ i, y.toInt i = z' i := fun i => congrFun h1 (Sum.inr i)
    have ha : ∀ i, a.toInt i = z' i := fun i => congrFun h2 (Sum.inl i)
    have hb : ∀ i, b.toInt i = w (Sum.inr i) := fun i => congrFun h2 (Sum.inr i)
    have hya : y = a := VASConfig.toInt_injective (funext fun i => (hy i).trans (ha i).symm)
    subst hya
    refine ⟨(x, b), ⟨y, hxy, hab⟩, ?_⟩
    funext j
    cases j with
    | inl i => exact hx i
    | inr i => exact hb i

/-- The relation along a non-empty list of configurations is periodic and asymptotically
definable. -/
theorem runTransList_asympDefinable [Fintype ι] :
    ∀ l : List (VASConfig ι), l ≠ [] →
      IsPeriodic (relVecSet (runTransList V l)) ∧ AsympDefinable (relVecSet (runTransList V l))
  | [], h => absurd rfl h
  | [c], _ => by
    have : relVecSet (runTransList V [c]) = V.transSet c := by
      rw [runTransList_singleton]
      ext w
      constructor
      · rintro ⟨⟨u, v⟩, h, rfl⟩
        exact ⟨u, v, rfl, h⟩
      · rintro ⟨u, v, rfl, h⟩
        exact ⟨(u, v), h, rfl⟩
    rw [this]
    exact ⟨transSet_periodic V c, ratDefinable_ratCone_transSet V c⟩
  | c :: d :: l, _ => by
    rw [runTransList_cons, relVecSet_cons]
    have ih : IsPeriodic (relVecSet (runTransList V (d :: l))) ∧
        AsympDefinable (relVecSet (runTransList V (d :: l))) :=
      runTransList_asympDefinable (d :: l) (List.cons_ne_nil _ _)
    exact AsympDefinable.relComp (transSet_periodic V c) ih.1 (ratDefinable_ratCone_transSet V c)
      ih.2

/-- `π▷` is periodic and asymptotically definable: it is a composition of the `▷_{c_j}`
(Leroux, Section 6, after Lemma 5.1). -/
theorem runTrans_asympDefinable [Fintype ι] (π : V.Run) :
    IsPeriodic (relVecSet π.trans) ∧ AsympDefinable (relVecSet π.trans) :=
  runTransList_asympDefinable π.cfgs π.ne

end VAS

end Cslib
