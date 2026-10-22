/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.RunTrans
public import Cslib.Computability.VAS.WellOrder

/-! # The reachability relation intersected with a linear relation

**Lemma 6.1** (Leroux): for a linear relation `R = r + P` (`P` finitely generated periodic) there
is a finite set `Min` of runs with direction in `R` such that
`(→* ∩ R) = ⋃_{π ∈ Min} dir π + (π▷ ∩ P)`.

## Main results

* `Set.PartiallyWellOrderedOn.exists_finite_basis`: a partially well-ordered set has a finite
  basis.
* `VAS.Run.Embeds.exists_trans`: an embedding of runs yields a pair in `π▷`.
* `VAS.reach_inter_linear`: Lemma 6.1.

## References

* [J. Leroux, *Vector Addition Systems Reachability Problem (A Simpler Solution)*][Leroux2012]
-/

@[expose] public section

open scoped Pointwise

namespace Set.PartiallyWellOrderedOn

/-- A partially well-ordered set has a finite basis: a finite subset such that every element is
above an element of it. -/
theorem exists_finite_basis {α : Type*} {r : α → α → Prop} {s : Set α}
    (h : s.PartiallyWellOrderedOn r) : ∃ t ⊆ s, t.Finite ∧ ∀ x ∈ s, ∃ y ∈ t, r y x := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, -, -⟩ := hcon ∅ (Set.empty_subset _) Set.finite_empty
  have : Nonempty α := ⟨x₀⟩
  -- a new element of `s` which is above none of the elements chosen so far
  choose! nxt hnxt using fun F : Finset α => fun hF : (F : Set α) ⊆ s =>
    hcon F hF F.finite_toSet
  let S : ℕ → Finset α := fun n => Nat.rec ∅ (fun _ F => insert (nxt F) F) n
  have hS : ∀ n, ∀ x ∈ S n, x ∈ s := by
    intro n
    induction n with
    | zero => simp [S]
    | succ n ih =>
      simp only [S, Finset.mem_insert, forall_eq_or_imp]
      exact ⟨(hnxt _ ih).1, ih⟩
  have hmono : Monotone S := monotone_nat_of_le_succ fun n => Finset.subset_insert _ _
  obtain ⟨m, n, hmn, hr⟩ := h.exists_lt (f := fun n => nxt (S n)) fun n => (hnxt _ (hS n)).1
  exact (hnxt _ (hS n)).2 _ (hmono hmn (Finset.mem_insert_self _ _)) hr

end Set.PartiallyWellOrderedOn

namespace Cslib

variable {ι : Type*}

namespace VAS

variable {V : VAS ι}

/-- The first configuration of a concatenation of runs is the source of the first run. -/
theorem head?_flatten_map_cfgs {ρs : List V.Run} (h : ρs ≠ []) :
    ((ρs.map Run.cfgs).flatten).head? = some (ρs.head h).src := by
  cases ρs with
  | nil => exact absurd rfl h
  | cons ρ ρs => simp [Run.head?_cfgs]

/-- The last configuration of a concatenation of runs is the target of the last run. -/
theorem getLast?_flatten_map_cfgs {ρs : List V.Run} (h : ρs ≠ []) :
    ((ρs.map Run.cfgs).flatten).getLast? = some (ρs.getLast h).tgt := by
  induction ρs using List.reverseRecOn with
  | nil => exact absurd rfl h
  | append_singleton L b _ => simp [Run.getLast?_cfgs]

/-- If `π ≼ π'`, then `π'` goes from `src π + u` to `tgt π + v` for a pair `(u, v) ∈ π▷`. -/
theorem Run.Embeds.exists_trans {π π' : V.Run} (h : Run.Embeds π π') :
    ∃ p ∈ π.trans, π'.dir = π.dir + p := by
  obtain ⟨v, ρs, hlen, hρ, hcfgs⟩ := h
  have hn : 0 < π.cfgs.length := List.length_pos_iff.2 π.ne
  have hne : ρs ≠ [] := List.ne_nil_of_length_pos (hlen ▸ hn)
  refine ⟨(v 0, v π.cfgs.length), ⟨v, rfl, rfl, fun j hj => ?_⟩, Prod.ext ?_ ?_⟩
  · have := hρ j hj (by omega)
    rw [← this.1, ← this.2]
    exact ρs[j].reach
  · have h1 := π'.head?_cfgs
    rw [hcfgs, head?_flatten_map_cfgs hne, Option.some_inj, List.head_eq_getElem] at h1
    change π'.src = π.src + v 0
    rw [← h1, (hρ 0 hn (by omega)).1, Run.src, List.head_eq_getElem π.ne]
  · have h1 := π'.getLast?_cfgs
    rw [hcfgs, getLast?_flatten_map_cfgs hne, Option.some_inj, List.getLast_eq_getElem] at h1
    simp only [hlen] at h1
    have h4 := (hρ (π.cfgs.length - 1) (by omega) (by omega)).2
    rw [Nat.sub_add_cancel hn] at h4
    change π'.tgt = π.tgt + v π.cfgs.length
    rw [← h1, h4, Run.tgt, List.getLast_eq_getElem π.ne]

variable (V) in
/-- **Lemma 6.1** (Leroux): for a linear relation `R = r + P`, with `P` a finitely generated
periodic set, there is a finite set `Min` of runs with direction in `R` such that
`(→* ∩ R) = ⋃_{π ∈ Min} dir π + (π▷ ∩ P)`. -/
theorem reach_inter_linear [Finite ι] (r : VASConfig ι × VASConfig ι)
    (gens : Finset (VASConfig ι × VASConfig ι)) :
    ∃ Min : Set V.Run, Min.Finite ∧ (∀ π ∈ Min, π.dir ∈ r +ᵥ
        (AddSubmonoid.closure (gens : Set (VASConfig ι × VASConfig ι)) :
          Set (VASConfig ι × VASConfig ι))) ∧
      {p : VASConfig ι × VASConfig ι | V.Reach p.1 p.2} ∩
          (r +ᵥ (AddSubmonoid.closure (gens : Set (VASConfig ι × VASConfig ι)) :
            Set (VASConfig ι × VASConfig ι))) =
        ⋃ π ∈ Min, π.dir +ᵥ (π.trans ∩
          (AddSubmonoid.closure (gens : Set (VASConfig ι × VASConfig ι)) :
            Set (VASConfig ι × VASConfig ι))) := by
  set P : Set (VASConfig ι × VASConfig ι) := (AddSubmonoid.closure
    (gens : Set (VASConfig ι × VASConfig ι)) : Set (VASConfig ι × VASConfig ι)) with hP
  let Ω : Set V.Run := {π | π.dir ∈ r +ᵥ P}
  have hpwo : Ω.PartiallyWellOrderedOn (Run.RunLE (V := V) P) :=
    Run.partiallyWellOrderedOn_runLE r gens fun π hπ => hπ
  obtain ⟨Min, hMinΩ, hfin, hbasis⟩ := hpwo.exists_finite_basis
  refine ⟨Min, hfin, hMinΩ, ?_⟩
  ext p
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hreach, hp⟩
    obtain ⟨π', hsrc, htgt⟩ := Run.exists_run_iff_reach.2 hreach
    have hπ' : π' ∈ Ω := by
      have : π'.dir = p := Prod.ext hsrc htgt
      simpa only [Ω, Set.mem_ofPred_eq, this] using hp
    obtain ⟨π, hπ, hle⟩ := hbasis π' hπ'
    obtain ⟨q, hq, hdir⟩ := hle.2.exists_trans
    obtain ⟨y, hy, hy'⟩ := Set.mem_vadd_set.1 hle.1
    have hyq : y = q := by
      rw [vadd_eq_add, hdir] at hy'
      exact add_left_cancel hy'
    refine ⟨π, hπ, ?_⟩
    rw [Set.mem_vadd_set]
    refine ⟨q, ⟨hq, hyq ▸ hy⟩, ?_⟩
    rw [vadd_eq_add, ← hdir]
    exact Prod.ext hsrc htgt
  · rintro ⟨π, hπ, hp⟩
    obtain ⟨q, ⟨hq, hqP⟩, rfl⟩ := Set.mem_vadd_set.1 hp
    refine ⟨?_, ?_⟩
    · exact π.reach_of_trans hq
    · obtain ⟨y, hy, hy'⟩ := Set.mem_vadd_set.1 (hMinΩ hπ)
      refine Set.mem_vadd_set.2 ⟨y + q, ?_, ?_⟩
      · exact AddSubmonoid.add_mem _ hy hqP
      · rw [vadd_eq_add, ← add_assoc]
        rw [vadd_eq_add] at hy'
        rw [hy']
        rfl

end VAS

end Cslib
