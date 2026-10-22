/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.Run
public import Mathlib.Order.WellFoundedSet
public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Data.Finsupp.PWO
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Data.List.Chain

/-! # Runs of a VAS and the well-quasi-order on runs

A run of a VAS is a non-empty word of configurations, consecutive ones being related by a move.
Following the second presentation of Leroux (POPL 2011), the order on runs is defined through
Higman's embedding order on the words of letters `(a, c)` (an action and the configuration it leads
to). We show that this order is a well-quasi-order (Dickson and Higman) and that it implies the
decomposition order `Run.Embeds`, which is thereby a well-quasi-order as well.

## Main definitions

- `VAS.Run`: runs of a VAS.
- `VAS.Run.Embeds`: the decomposition order on runs.
- `VAS.Run.word`, `VAS.Run.WordLE`: the word of a run and the Higman order on runs.

## Main statements

- `VAS.Run.exists_run_iff_reach`: reachability is the existence of a run.
- `VAS.Run.wellQuasiOrdered_wordLE`: the Higman order on runs is a well-quasi-order.
- `VAS.Run.wordLE_embeds`: the Higman order implies the decomposition order.
- `VAS.Run.wellQuasiOrdered_embeds`: the decomposition order is a well-quasi-order.

## References

* [J. Leroux, *Vector Addition Systems Reachability Problem (A Simpler Solution)*][Leroux2012],
  Lemma 4.1.
* J. Leroux, *Vector addition system reachability problem: a short self-contained proof*, POPL
  2011, Lemmas 7.5 and 7.6.
-/

@[expose] public section

namespace Cslib

namespace VAS

variable {ι : Type*}

namespace Run

variable {V : VAS ι}

/-- The letters `(a_j, c_j)` of a word of configurations `c_0 ... c_k`, where `a_j = c_j - c_{j-1}`
is the displacement of the `j`-th step. -/
def wordOf (l : List (VASConfig ι)) : List ((ι → ℤ) × VASConfig ι) :=
  (l.zip l.tail).map fun p => (p.2.toInt - p.1.toInt, p.2)

@[simp] theorem wordOf_nil : wordOf ([] : List (VASConfig ι)) = [] := rfl

@[simp] theorem wordOf_singleton (c : VASConfig ι) : wordOf [c] = [] := rfl

@[simp] theorem wordOf_cons_cons (c d : VASConfig ι) (l : List (VASConfig ι)) :
    wordOf (c :: d :: l) = (d.toInt - c.toInt, d) :: wordOf (d :: l) := rfl

/-- The word `(a_1,c_1)...(a_k,c_k)` of a run `c_0 ... c_k` over `ℤ^ι × ℕ^ι`, with
`a_j = c_j - c_{j-1}`. -/
def word (π : Run V) : List ((ι → ℤ) × VASConfig ι) := wordOf π.cfgs

/-- The actions of the letters of a chain of moves belong to the VAS. -/
theorem fst_mem_acts_of_mem_wordOf {l : List (VASConfig ι)} (h : l.IsChain V.Move)
    {x : (ι → ℤ) × VASConfig ι} (hx : x ∈ wordOf l) : x.1 ∈ V.acts := by
  induction l with
  | nil => simp at hx
  | cons c l ih =>
    rcases l with _ | ⟨d, l⟩
    · simp at hx
    · obtain ⟨⟨a, ha, hd⟩, h⟩ := List.isChain_cons_cons.1 h
      rw [wordOf_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa [hd] using ha
      · exact ih h hx

/-- The actions of the letters of the word of a run belong to the VAS. -/
theorem fst_mem_acts_of_mem_word (π : Run V) {x : (ι → ℤ) × VASConfig ι} (hx : x ∈ π.word) :
    x.1 ∈ V.acts :=
  fst_mem_acts_of_mem_wordOf π.chain hx

/-- The order on the letters of runs: equal actions and componentwise smaller configurations. -/
def LetterLE (a b : (ι → ℤ) × VASConfig ι) : Prop := a.1 = b.1 ∧ a.2 ≤ b.2

instance : IsPreorder ((ι → ℤ) × VASConfig ι) LetterLE where
  refl _ := ⟨rfl, le_rfl⟩
  trans _ _ _ h h' := ⟨h.1.trans h'.1, h.2.trans h'.2⟩

/-- The Higman order on runs: the words embed (Higman's order over the alphabet `A × ℕ^ι`, where
`(a,c) ⊑ (a',c')` iff `a = a'` and `c ≤ c'`), and `src ≤ src'`, `tgt ≤ tgt'`. -/
def WordLE (π π' : Run V) : Prop :=
  π.src ≤ π'.src ∧ π.tgt ≤ π'.tgt ∧ List.SublistForall₂ LetterLE π.word π'.word

/-- The letters over a finite set of actions are well-quasi-ordered by `LetterLE`. -/
theorem partiallyWellOrderedOn_letterLE [Finite ι] (acts : Finset (ι → ℤ)) :
    {a : (ι → ℤ) × VASConfig ι | a.1 ∈ acts}.PartiallyWellOrderedOn LetterLE := by
  rw [Set.partiallyWellOrderedOn_iff_exists_lt]
  intro f hf
  let g : ℕ → acts × VASConfig ι := fun n => (⟨(f n).1, hf n⟩, (f n).2)
  have hw : WellQuasiOrdered fun a b : acts × VASConfig ι => a.1 = b.1 ∧ a.2 ≤ b.2 :=
    WellQuasiOrdered.prod (Finite.wellQuasiOrdered _) wellQuasiOrdered_le
  obtain ⟨m, n, hmn, h1, h2⟩ := hw g
  exact ⟨m, n, hmn, congrArg Subtype.val h1, h2⟩

/-- `WordLE` is a well-quasi-order (Dickson and Higman). -/
theorem wellQuasiOrdered_wordLE [Finite ι] : WellQuasiOrdered (WordLE (V := V)) := by
  intro f
  have hw : WellQuasiOrdered fun a b : VASConfig ι × VASConfig ι => a ≤ b := wellQuasiOrdered_le
  obtain ⟨g, hg⟩ := hw.exists_monotone_subseq fun n => ((f n).src, (f n).tgt)
  have hH := Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ LetterLE
    (partiallyWellOrderedOn_letterLE V.acts)
  obtain ⟨m, n, hmn, h⟩ := hH.exists_lt (f := fun n => (f (g n)).word)
    fun n x hx => fst_mem_acts_of_mem_word _ hx
  have := hg m n hmn.le
  exact ⟨g m, g n, g.strictMono hmn, this.1, this.2, h⟩

/-- The order `π ≼ π'` on runs: `π = c_0 ... c_k` and `π' = π'_0 ... π'_k` (concatenation of
configuration words) where `π'_j` is a run from `c_j + v_j` to `c_j + v_{j+1}` for some vectors
`v_0, ..., v_{k+1}` of `ℕ^ι`. -/
def Embeds (π π' : Run V) : Prop :=
  ∃ (v : ℕ → VASConfig ι) (ρs : List (Run V)),
    ρs.length = π.cfgs.length ∧
    (∀ (j : ℕ) (h : j < π.cfgs.length) (h' : j < ρs.length),
      ρs[j].src = π.cfgs[j] + v j ∧ ρs[j].tgt = π.cfgs[j] + v (j + 1)) ∧
    π'.cfgs = (ρs.map Run.cfgs).flatten

theorem add_sub_of_le' {c d : VASConfig ι} (h : c ≤ d) : c + (d - c) = d :=
  funext fun i => Nat.add_sub_cancel' (h i)

/-- The decomposition lemma behind `wordLE_embeds`, by induction on the embedding of the words:
the first factor of the decomposition has an unconstrained source. -/
theorem exists_decomp_of_sublistForall₂ {ws ws' : List ((ι → ℤ) × VASConfig ι)}
    (h : List.SublistForall₂ LetterLE ws ws') :
    ∀ {c : VASConfig ι} {cs : List (VASConfig ι)} {d : VASConfig ι} {ds : List (VASConfig ι)},
      ws = wordOf (c :: cs) → ws' = wordOf (d :: ds) → (d :: ds).IsChain V.Move →
      (c :: cs).getLast (List.cons_ne_nil _ _) ≤ (d :: ds).getLast (List.cons_ne_nil _ _) →
      ∃ (v : ℕ → VASConfig ι) (ρ : Run V) (ρs : List (Run V)),
        ρs.length = cs.length ∧ ρ.src = d ∧ ρ.tgt = c + v 1 ∧
        (∀ (j : ℕ) (hj : j < ρs.length) (hj' : j < cs.length),
          ρs[j].src = cs[j] + v (j + 1) ∧ ρs[j].tgt = cs[j] + v (j + 2)) ∧
        d :: ds = ((ρ :: ρs).map Run.cfgs).flatten := by
  induction h with
  | nil =>
    intro c cs d ds hw _ hch hle
    cases cs with
    | cons c' cs' => simp [wordOf_cons_cons] at hw
    | nil =>
      refine ⟨fun _ => (⟨d :: ds, by simp, hch⟩ : Run V).tgt - c, ⟨d :: ds, by simp, hch⟩, [],
        rfl, rfl, ?_, by simp, by simp⟩
      refine (add_sub_of_le' ?_).symm
      simpa [Run.tgt] using hle
  | @cons a b l1 l2 hab _ ih =>
    intro c cs d ds hw hw' hch hle
    rcases cs with _ | ⟨c', cs'⟩
    · simp at hw
    rcases ds with _ | ⟨d', ds'⟩
    · simp at hw'
    rw [wordOf_cons_cons] at hw hw'
    obtain ⟨rfl, hl1⟩ := List.cons.inj hw
    obtain ⟨rfl, hl2⟩ := List.cons.inj hw'
    obtain ⟨h1, h2⟩ := hab
    dsimp only at h1 h2
    have key (i : ι) : c i ≤ d i ∧ d' i = c' i + (d i - c i) := by
      have h3 := congrFun h1 i
      have h4 : c' i ≤ d' i := h2 i
      simp only [VASConfig.toInt, Pi.sub_apply] at h3
      omega
    have hcd : c ≤ d := fun i => (key i).1
    have hdd : d' = c' + (d - c) := funext fun i => (key i).2
    obtain ⟨v, ρ, ρs, hlen, hsrc, htgt, hρs, hfl⟩ :=
      ih hl1 hl2 (List.isChain_cons.1 hch).2 (by simpa using hle)
    refine ⟨fun k => if k = 0 then 0 else if k = 1 then d - c else v (k - 1), single V d,
      ρ :: ρs, by simp [hlen], rfl, by simp [add_sub_of_le' hcd], ?_, ?_⟩
    · intro j hj hj'
      cases j with
      | zero => simp [hsrc, hdd, htgt]
      | succ j =>
        simpa using hρs j (by simpa using hj) (by simpa using hj')
    · change d :: d' :: ds' = [d] ++ (List.map cfgs (ρ :: ρs)).flatten
      rw [← hfl]
      rfl
  | @cons_right a l1 l2 _ ih =>
    intro c cs d ds hw hw' hch hle
    rcases ds with _ | ⟨d', ds'⟩
    · simp at hw'
    rw [wordOf_cons_cons] at hw'
    obtain ⟨-, hl2⟩ := List.cons.inj hw'
    obtain ⟨v, ρ, ρs, hlen, hsrc, htgt, hρs, hfl⟩ :=
      ih hw hl2 (List.isChain_cons.1 hch).2 (by simpa using hle)
    have hm : V.Move d ρ.src := hsrc ▸ (List.isChain_cons_cons.1 hch).1
    refine ⟨v, Run.cons d ρ hm, ρs, hlen, by simp, by simpa using htgt, hρs, ?_⟩
    simp only [List.map_cons, List.flatten_cons, cons_cfgs, List.cons_append] at hfl ⊢
    rw [← hfl]

/-- The Higman order implies the decomposition order. -/
theorem wordLE_embeds {π π' : Run V} (h : WordLE π π') : Embeds π π' := by
  obtain ⟨hs, ht, hw⟩ := h
  obtain ⟨_ | ⟨c, cs⟩, hne, hch⟩ := π
  · exact absurd rfl hne
  obtain ⟨_ | ⟨d, ds⟩, hne', hch'⟩ := π'
  · exact absurd rfl hne'
  have hs' : c ≤ d := hs
  have ht' : (c :: cs).getLast hne ≤ (d :: ds).getLast hne' := ht
  obtain ⟨v, ρ, ρs, hlen, hsrc, htgt, hρs, hfl⟩ :=
    exists_decomp_of_sublistForall₂ hw rfl rfl hch' ht'
  refine ⟨fun j => if j = 0 then d - c else v j, ρ :: ρs, by simp [hlen], ?_, hfl⟩
  intro j hj hj'
  cases j with
  | zero =>
    simp only [List.getElem_cons_zero, ite_true, add_sub_of_le' hs', List.getElem_cons_zero]
    exact ⟨hsrc, by simpa using htgt⟩
  | succ j =>
    simpa using hρs j (by simpa using hj') (by simpa using hj)

/-- The decomposition order is a well-quasi-order (Lemma 4.1 of Leroux). -/
theorem wellQuasiOrdered_embeds [Finite ι] : WellQuasiOrdered (Embeds (V := V)) := by
  intro f
  obtain ⟨m, n, hmn, h⟩ := wellQuasiOrdered_wordLE f
  exact ⟨m, n, hmn, wordLE_embeds h⟩

open scoped Pointwise in
/-- The order `π ⊑ π'` on the runs with direction in a translate of a periodic set `P`:
`π ≼ π'` and `dir π' ∈ dir π + P`. -/
def RunLE (P : Set (VASConfig ι × VASConfig ι)) (π π' : Run V) : Prop :=
  π'.dir ∈ π.dir +ᵥ P ∧ Embeds π π'

open scoped Pointwise in
/-- The order `⊑` is a well-quasi-order on every set of runs whose directions lie in a translate
`r + P` of a finitely generated periodic set `P` (Dickson's lemma on the coefficients of the
generators, and `wellQuasiOrdered_embeds`). The restriction on directions is necessary: the
statement for all runs is false. -/
theorem partiallyWellOrderedOn_runLE [Finite ι] (r : VASConfig ι × VASConfig ι)
    (gens : Finset (VASConfig ι × VASConfig ι)) {Ω : Set (Run V)}
    (hΩ : ∀ π ∈ Ω, π.dir ∈ r +ᵥ (AddSubmonoid.closure (gens : Set (VASConfig ι × VASConfig ι)) :
      Set (VASConfig ι × VASConfig ι))) :
    Ω.PartiallyWellOrderedOn
      (RunLE (V := V) (AddSubmonoid.closure (gens : Set (VASConfig ι × VASConfig ι)) :
        Set (VASConfig ι × VASConfig ι))) := by
  rw [Set.partiallyWellOrderedOn_iff_exists_lt]
  intro f hf
  have hc : ∀ n, ∃ a : gens → ℕ, (f n).dir = r + ∑ i, a i • i.1 := by
    intro n
    obtain ⟨y, hy, hdir⟩ := Set.mem_vadd_set.1 (hΩ _ (hf n))
    obtain ⟨a, ha⟩ := AddSubmonoid.mem_closure_finset'.1 hy
    exact ⟨a, by rw [← hdir, ha]; rfl⟩
  choose a ha using hc
  have hw : WellQuasiOrdered fun x y : gens → ℕ => x ≤ y := wellQuasiOrdered_le
  obtain ⟨g, hg⟩ := hw.exists_monotone_subseq a
  obtain ⟨m, n, hmn, h⟩ := wellQuasiOrdered_embeds (V := V) (f ∘ g)
  refine ⟨g m, g n, g.strictMono hmn, ?_, h⟩
  refine Set.mem_vadd_set.2 ⟨∑ i, (a (g n) i - a (g m) i) • i.1, ?_, ?_⟩
  · exact AddSubmonoid.sum_mem _ fun i _ =>
      AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure i.2) _
  · have hle := hg m n hmn.le
    rw [vadd_eq_add, ha (g m), ha (g n), add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_nsmul, Nat.add_sub_cancel' (hle i)]

end Run

end VAS

end Cslib
