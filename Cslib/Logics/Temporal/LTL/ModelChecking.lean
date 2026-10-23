/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Logics.Temporal.LTL.FairPath
public import Cslib.Logics.Temporal.LTL.Model
public import Cslib.Logics.Temporal.CTL.ModelChecking
public import Mathlib.Data.Fintype.Powerset

/-! # Model checking LTL on finite models

LTL model checking is decidable for models with finitely many states. The existence of a maximal
path satisfying a formula `φ` is reduced to the existence of a *fair* path in a finite product graph
(the tableau construction, see [Vardi1986]).

A vertex of the product is a state together with a *type*: the set of `X`- and `U`-subformulas of
`φ` that hold at the current position. The other subformulas are determined from the type and the
state (`Formula.eval`). An edge respects the transition relation of the model and the local laws of
`X` (`X ψ` holds iff `ψ` holds next) and `U` (`ψ₁ U ψ₂` holds iff `ψ₂` holds, or `ψ₁` holds and
`ψ₁ U ψ₂` holds next). The laws of `U` do not force `ψ₂` to ever hold, which is why the path must
also be fair: for each `ψ₁ U ψ₂`, either `ψ₁ U ψ₂` fails or `ψ₂` holds, infinitely often. In a
finite graph, a fair path exists iff a reachable cycle visits all the fairness sets (`FairPath`).

## Main definitions

- `Formula.elem`: the `X`- and `U`-subformulas of a formula.
- `Formula.eval`: the truth of a formula from a type and a state.
- `prodRel`: the edges of the product graph.

## Main statements

- `somePath_iff_fairPath`: some path of the model satisfies `φ` iff the product has a fair path
  from a vertex that makes `φ` true.
- `instDecidableSomePath`, `instDecidableAllPaths`: LTL model checking is decidable.

## References

* [M. Y. Vardi, P. Wolper, *An automata-theoretic approach to automatic program
  verification*][Vardi1986]
-/

@[expose] public section

namespace Cslib.Logic.LTL

open Cslib Cslib.ωSequence
open scoped InferenceSystem Formula Cslib.Logic

variable {Atom : Type*} [DecidableEq Atom]

namespace Formula

/-- The elementary subformulas of a formula: those of the form `X ψ` and `ψ₁ U ψ₂`. -/
def elem : Formula Atom → Finset (Formula Atom)
  | .atom _ => ∅
  | .false => ∅
  | .not a => elem a
  | .or a b => elem a ∪ elem b
  | .next a => insert (X a) (elem a)
  | .until a b => insert (a U b) (elem a ∪ elem b)

/-- The `U`-subformulas of a formula, as a list. -/
def untils : Formula Atom → List (Formula Atom)
  | .atom _ => []
  | .false => []
  | .not a => untils a
  | .or a b => untils a ++ untils b
  | .next a => untils a
  | .until a b => (a U b) :: (untils a ++ untils b)

theorem elem_subset_of_mem : ∀ {φ ψ : Formula Atom}, ψ ∈ elem φ → elem ψ ⊆ elem φ
  | .atom _, ψ, h => by simp [elem] at h
  | .false, ψ, h => by simp [elem] at h
  | .not a, ψ, h => elem_subset_of_mem (φ := a) h
  | .or a b, ψ, h => by
    rcases Finset.mem_union.1 h with h | h
    · exact (elem_subset_of_mem h).trans Finset.subset_union_left
    · exact (elem_subset_of_mem h).trans Finset.subset_union_right
  | .next a, ψ, h => by
    rcases Finset.mem_insert.1 h with rfl | h
    · exact subset_rfl
    · exact (elem_subset_of_mem h).trans (Finset.subset_insert _ _)
  | .until a b, ψ, h => by
    rcases Finset.mem_insert.1 h with rfl | h
    · exact subset_rfl
    · refine Finset.Subset.trans ?_ (Finset.subset_insert _ _)
      rcases Finset.mem_union.1 h with h | h
      · exact (elem_subset_of_mem h).trans Finset.subset_union_left
      · exact (elem_subset_of_mem h).trans Finset.subset_union_right

theorem mem_untils_of_mem_elem : ∀ {φ : Formula Atom} {a b : Formula Atom},
    (a U b) ∈ elem φ → (a U b) ∈ untils φ
  | .atom _, _, _, h => by simp [elem] at h
  | .false, _, _, h => by simp [elem] at h
  | .not c, _, _, h => mem_untils_of_mem_elem (φ := c) h
  | .or c d, _, _, h => by
    rcases Finset.mem_union.1 h with h | h
    · exact List.mem_append_left _ (mem_untils_of_mem_elem h)
    · exact List.mem_append_right _ (mem_untils_of_mem_elem h)
  | .next c, _, _, h => by
    rcases Finset.mem_insert.1 h with h | h
    · cases h
    · exact mem_untils_of_mem_elem (φ := c) h
  | .until c d, a, b, h => by
    rcases Finset.mem_insert.1 h with h | h
    · rw [h]; exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ ?_
      rcases Finset.mem_union.1 h with h | h
      · exact List.mem_append_left _ (mem_untils_of_mem_elem h)
      · exact List.mem_append_right _ (mem_untils_of_mem_elem h)

/-- The truth of a formula at a state with valuation `L`, when the elementary subformulas that hold
are those of `τ`. -/
def eval (L : Atom → Prop) (τ : Finset (Formula Atom)) : Formula Atom → Prop
  | .atom p => L p
  | .false => False
  | .not a => ¬ eval L τ a
  | .or a b => eval L τ a ∨ eval L τ b
  | .next a => (X a) ∈ τ
  | .until a b => (a U b) ∈ τ

instance decidableEval (L : Atom → Prop) [DecidablePred L] (τ : Finset (Formula Atom)) :
    DecidablePred (eval L τ)
  | .atom p => inferInstanceAs (Decidable (L p))
  | .false => isFalse id
  | .not a =>
    have := decidableEval L τ a
    inferInstanceAs (Decidable (¬ eval L τ a))
  | .or a b =>
    have := decidableEval L τ a
    have := decidableEval L τ b
    inferInstanceAs (Decidable (eval L τ a ∨ eval L τ b))
  | .next a => inferInstanceAs (Decidable ((X a) ∈ τ))
  | .until a b => inferInstanceAs (Decidable ((a U b) ∈ τ))

/-- The local laws of `X` and `U` between consecutive positions with types `τ` and `τ'` and
valuations `L` and `L'`. -/
def edge (L L' : Atom → Prop) (τ τ' : Finset (Formula Atom)) : Formula Atom → Prop
  | .next a => ((X a) ∈ τ ↔ eval L' τ' a)
  | .until a b =>
    ((a U b) ∈ τ ↔ eval L τ b ∨ (eval L τ a ∧ (a U b) ∈ τ'))
  | _ => True

instance decidableEdge (L L' : Atom → Prop) [DecidablePred L] [DecidablePred L']
    (τ τ' : Finset (Formula Atom)) : DecidablePred (edge L L' τ τ')
  | .atom _ => isTrue trivial
  | .false => isTrue trivial
  | .not _ => isTrue trivial
  | .or _ _ => isTrue trivial
  | .next a => inferInstanceAs (Decidable ((X a) ∈ τ ↔ eval L' τ' a))
  | .until a b => inferInstanceAs (Decidable
      ((a U b) ∈ τ ↔ eval L τ b ∨ (eval L τ a ∧ (a U b) ∈ τ')))

end Formula

section Product

variable {State : Type*} (m : CTL.Model State Atom) (φ : Formula Atom)

/-- The types of a formula: the sets of its elementary subformulas. -/
abbrev Ty : Type _ := ↥(Formula.elem φ).powerset

/-- The edges of the product graph: a step of the model (or a stutter at a deadlock) that respects
the local laws of `X` and `U`. -/
def prodRel (a b : State × Ty φ) : Prop :=
  (m.tr a.1 b.1 ∨ (m.Dead a.1 ∧ b.1 = a.1)) ∧
    ∀ ψ ∈ Formula.elem φ, Formula.edge (m.v a.1) (m.v b.1) a.2.1 b.2.1 ψ

/-- The fairness set of an `U`-formula `ψ₁ U ψ₂`: either it fails, or `ψ₂` holds. -/
def fairPred : Formula Atom → State × Ty φ → Prop
  | .until a b, v => (a U b) ∉ v.2.1 ∨ Formula.eval (m.v v.1) v.2.1 b
  | _, _ => True

end Product

section Correctness

open scoped Classical in
/-- The type at position `i` of a word: the elementary subformulas in `E` that hold there. -/
noncomputable def typeAt (E : Finset (Formula Atom)) (w : ωSequence (Set Atom)) (i : ℕ) :
    Finset (Formula Atom) :=
  E.filter fun ψ => ⇓LTL[w.drop i ⊨ ψ]

omit [DecidableEq Atom] in
theorem typeAt_subset (E : Finset (Formula Atom)) (w : ωSequence (Set Atom)) (i : ℕ) :
    typeAt E w i ⊆ E := by
  classical
  exact Finset.filter_subset _ _

omit [DecidableEq Atom] in
open scoped Classical in
theorem mem_typeAt {E : Finset (Formula Atom)} {w : ωSequence (Set Atom)} {i : ℕ}
    {ψ : Formula Atom} (h : ψ ∈ E) : ψ ∈ typeAt E w i ↔ ⇓LTL[w.drop i ⊨ ψ] := by
  simp [typeAt, h]

omit [DecidableEq Atom] in
theorem satisfies_atom_drop_zero {w : ωSequence (Set Atom)} {i : ℕ} {p : Atom} :
    ⇓LTL[w.drop i ⊨ .atom p] ↔ p ∈ w i := by
  rw [Satisfies.atom_iff]
  change p ∈ w (0 + i) ↔ _
  rw [Nat.zero_add]

/-- From the type of a word at a position, the truth of every formula is determined. -/
theorem eval_typeAt {E : Finset (Formula Atom)} {w : ωSequence (Set Atom)} {i : ℕ}
    {L : Atom → Prop} (hL : ∀ p, L p ↔ p ∈ w i) :
    ∀ {ψ : Formula Atom}, Formula.elem ψ ⊆ E →
      (Formula.eval L (typeAt E w i) ψ ↔ ⇓LTL[w.drop i ⊨ ψ])
  | .atom p, _ => by rw [satisfies_atom_drop_zero]; exact hL p
  | .false, _ => Iff.rfl
  | .not a, h => not_congr (eval_typeAt hL (ψ := a) h)
  | .or a b, h => or_congr
    (eval_typeAt hL (ψ := a) (Finset.subset_union_left.trans h))
    (eval_typeAt hL (ψ := b) (Finset.subset_union_right.trans h))
  | .next a, h => mem_typeAt (h (Finset.mem_insert_self _ _))
  | .until a b, h => mem_typeAt (h (Finset.mem_insert_self _ _))

theorem untils_spec : ∀ {φ u : Formula Atom}, u ∈ Formula.untils φ →
    ∃ a b, u = (a U b) ∧ (a U b) ∈ Formula.elem φ
  | .atom _, _, h => by simp [Formula.untils] at h
  | .false, _, h => by simp [Formula.untils] at h
  | .not c, _, h => untils_spec (φ := c) h |>.imp fun a => Exists.imp fun b ⟨h1, h2⟩ => ⟨h1, h2⟩
  | .or c d, _, h => by
    rcases List.mem_append.1 h with h | h
    · obtain ⟨a, b, h1, h2⟩ := untils_spec h
      exact ⟨a, b, h1, Finset.mem_union_left _ h2⟩
    · obtain ⟨a, b, h1, h2⟩ := untils_spec h
      exact ⟨a, b, h1, Finset.mem_union_right _ h2⟩
  | .next c, _, h => by
    obtain ⟨a, b, h1, h2⟩ := untils_spec (φ := c) h
    exact ⟨a, b, h1, Finset.mem_insert_of_mem h2⟩
  | .until c d, _, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨c, d, rfl, Finset.mem_insert_self _ _⟩
    · rcases List.mem_append.1 h with h | h
      · obtain ⟨a, b, h1, h2⟩ := untils_spec h
        exact ⟨a, b, h1, Finset.mem_insert_of_mem (Finset.mem_union_left _ h2)⟩
      · obtain ⟨a, b, h1, h2⟩ := untils_spec h
        exact ⟨a, b, h1, Finset.mem_insert_of_mem (Finset.mem_union_right _ h2)⟩

variable {State : Type*} (m : CTL.Model State Atom) (φ : Formula Atom)

/-- A maximal path of the model has a run in the product graph, with the types of its
positions: the first components are the states of the path, the edges are respected and the
fairness sets are visited infinitely often. -/
theorem exists_fairRun {f : ℕ → State} (hf : m.IsPath f) :
    ∃ g : ℕ → State × Ty φ, (∀ n, (g n).1 = f n) ∧ (∀ n, prodRel m φ (g n) (g (n + 1))) ∧
      ∀ u ∈ Formula.untils φ, ∀ n, ∃ k ≥ n, fairPred m φ u (g k) := by
  let w := m.trace f
  have hL : ∀ i p, m.v (f i) p ↔ p ∈ w i := fun i p => Iff.rfl
  have hT : ∀ i, typeAt (Formula.elem φ) w i ∈ (Formula.elem φ).powerset := fun i =>
    Finset.mem_powerset.2 (typeAt_subset _ _ _)
  refine ⟨fun n => (f n, ⟨typeAt (Formula.elem φ) w n, hT n⟩), fun n => rfl,
    fun n => ⟨hf n, fun ψ hψ => ?_⟩, fun u hu n => ?_⟩
  · cases ψ with
    | next a =>
      have hsub : Formula.elem a ⊆ Formula.elem φ :=
        (Finset.subset_insert _ _).trans (Formula.elem_subset_of_mem hψ)
      change ((X a) ∈ typeAt _ w n ↔ Formula.eval (m.v (f (n + 1))) (typeAt _ w (n + 1)) a)
      rw [mem_typeAt hψ, eval_typeAt (hL (n + 1)) hsub, Satisfies.next_iff, tail_drop]
    | «until» a b =>
      have hsa : Formula.elem a ⊆ Formula.elem φ :=
        (Finset.subset_union_left.trans (Finset.subset_insert _ _)).trans
          (Formula.elem_subset_of_mem hψ)
      have hsb : Formula.elem b ⊆ Formula.elem φ :=
        (Finset.subset_union_right.trans (Finset.subset_insert _ _)).trans
          (Formula.elem_subset_of_mem hψ)
      change ((a U b) ∈ typeAt _ w n ↔ Formula.eval (m.v (f n)) (typeAt _ w n) b ∨
        (Formula.eval (m.v (f n)) (typeAt _ w n) a ∧
          (a U b) ∈ typeAt _ w (n + 1)))
      rw [mem_typeAt hψ, mem_typeAt hψ, eval_typeAt (hL n) hsa, eval_typeAt (hL n) hsb,
        Satisfies.until_unfold, tail_drop]
    | atom p => trivial
    | false => trivial
    | not a => trivial
    | or a b => trivial
  · obtain ⟨a, b, rfl, hmem⟩ := untils_spec hu
    have hsb : Formula.elem b ⊆ Formula.elem φ :=
      (Finset.subset_union_right.trans (Finset.subset_insert _ _)).trans
        (Formula.elem_subset_of_mem hmem)
    by_cases hin : (a U b) ∈ typeAt (Formula.elem φ) w n
    · obtain ⟨j, hj, -⟩ := (mem_typeAt hmem).1 hin
      refine ⟨n + j, by omega, Or.inr ?_⟩
      refine (eval_typeAt (hL (n + j)) hsb).2 ?_
      rw [drop_drop] at hj
      rwa [Nat.add_comm]
    · exact ⟨n, le_rfl, Or.inl hin⟩

/-- The trace of the first components of a path in the product graph. -/
abbrev prodTrace (g : ℕ → State × Ty φ) : ωSequence (Set Atom) := m.trace fun n => (g n).1

/-- On a fair path of the product graph, the truth value computed from the types is the
semantic truth value. -/
theorem key_eval (g : ℕ → State × Ty φ) (hs : ∀ n, prodRel m φ (g n) (g (n + 1)))
    (hfair : ∀ u ∈ Formula.untils φ, ∀ n, ∃ k ≥ n, fairPred m φ u (g k)) :
    ∀ {ψ : Formula Atom}, Formula.elem ψ ⊆ Formula.elem φ → ∀ i,
      (Formula.eval (m.v (g i).1) (g i).2.1 ψ ↔ ⇓LTL[(prodTrace m φ g).drop i ⊨ ψ])
  | .atom p, _, i => by
    rw [satisfies_atom_drop_zero]
    exact Iff.rfl
  | .false, _, _ => Iff.rfl
  | .not a, h, i => not_congr (key_eval g hs hfair (ψ := a) h i)
  | .or a b, h, i => or_congr
    (key_eval g hs hfair (ψ := a) (Finset.subset_union_left.trans h) i)
    (key_eval g hs hfair (ψ := b) (Finset.subset_union_right.trans h) i)
  | .next a, h, i => by
    have hmem : (X a) ∈ Formula.elem φ := h (Finset.mem_insert_self _ _)
    have hsub : Formula.elem a ⊆ Formula.elem φ := (Finset.subset_insert _ _).trans h
    have e : ((X a) ∈ (g i).2.1 ↔ Formula.eval (m.v (g (i + 1)).1) (g (i + 1)).2.1 a) :=
      (hs i).2 _ hmem
    change (X a) ∈ (g i).2.1 ↔ _
    rw [e, key_eval g hs hfair hsub (i + 1), Satisfies.next_iff, tail_drop]
  | .until a b, h, i => by
    have hmem : (a U b) ∈ Formula.elem φ := h (Finset.mem_insert_self _ _)
    have hsa : Formula.elem a ⊆ Formula.elem φ :=
      (Finset.subset_union_left.trans (Finset.subset_insert _ _)).trans h
    have hsb : Formula.elem b ⊆ Formula.elem φ :=
      (Finset.subset_union_right.trans (Finset.subset_insert _ _)).trans h
    have ha := key_eval g hs hfair hsa
    have hb := key_eval g hs hfair hsb
    set w := prodTrace m φ g with hw
    have e : ∀ k, ((a U b) ∈ (g k).2.1 ↔
        Formula.eval (m.v (g k).1) (g k).2.1 b ∨
          (Formula.eval (m.v (g k).1) (g k).2.1 a ∧ (a U b) ∈ (g (k + 1)).2.1)) :=
      fun k => (hs k).2 _ hmem
    change (a U b) ∈ (g i).2.1 ↔ _
    constructor
    · intro hu
      classical
      have hex : ∃ j, i ≤ j ∧ ((a U b) ∉ (g j).2.1 ∨
          Formula.eval (m.v (g j).1) (g j).2.1 b) := by
        obtain ⟨k, hk, hfk⟩ := hfair _ (Formula.mem_untils_of_mem_elem hmem) i
        exact ⟨k, hk, hfk⟩
      have hj := Nat.find_spec hex
      have hmin : ∀ k < Nat.find hex, ¬ (i ≤ k ∧ ((a U b) ∉ (g k).2.1 ∨
          Formula.eval (m.v (g k).1) (g k).2.1 b)) := fun k hk => Nat.find_min hex hk
      set j := Nat.find hex with hjdef
      have hstep : ∀ k, i ≤ k → k < j → (a U b) ∈ (g k).2.1 ∧
          ¬ Formula.eval (m.v (g k).1) (g k).2.1 b := fun k hik hkj => by
        have := hmin k hkj
        push Not at this
        exact this hik
      have hA : ∀ k, i ≤ k → k ≤ j → (a U b) ∈ (g k).2.1 := by
        intro k hik hkj
        induction k, hik using Nat.le_induction with
        | base => exact hu
        | succ k hik ih =>
          obtain ⟨huk, hnb⟩ := hstep k hik (by omega)
          rcases (e k).1 huk with hb' | ⟨_, hnext⟩
          · exact absurd hb' hnb
          · exact hnext
      have hbj : Formula.eval (m.v (g j).1) (g j).2.1 b := by
        rcases hj.2 with hnu | hbj
        · exact absurd (hA j hj.1 le_rfl) hnu
        · exact hbj
      refine ⟨j - i, ?_, fun k hk => ?_⟩
      · rw [drop_drop, show j - i + i = j by omega]
        exact (hb j).1 hbj
      · rw [drop_drop]
        obtain ⟨huk, hnb⟩ := hstep (k + i) (by omega) (by omega)
        rcases (e (k + i)).1 huk with hb' | ⟨hak, _⟩
        · exact absurd hb' hnb
        · exact (ha (k + i)).1 hak
    · rintro ⟨n, hn, hk⟩
      have back : ∀ n i, ⇓LTL[(w.drop i).drop n ⊨ b] →
          (∀ k < n, ⇓LTL[(w.drop i).drop k ⊨ a]) → (a U b) ∈ (g i).2.1 := by
        intro n
        induction n with
        | zero =>
          intro i hbn _
          exact (e i).2 (Or.inl ((hb i).2 hbn))
        | succ n ih =>
          intro i hbn hkn
          have hai : ⇓LTL[w.drop i ⊨ a] := hkn 0 (Nat.succ_pos n)
          have hnext : (a U b) ∈ (g (i + 1)).2.1 := by
            refine ih (i + 1) ?_ fun k hk' => ?_
            · rw [drop_drop] at hbn ⊢
              rwa [show n + (i + 1) = n + 1 + i by omega]
            · have := hkn (k + 1) (by omega)
              rw [drop_drop] at this ⊢
              rwa [show k + (i + 1) = k + 1 + i by omega]
          exact (e i).2 (Or.inr ⟨(ha i).2 hai, hnext⟩)
      exact back n i hn hk

/-- A path of the model satisfying `φ` gives a fair path of the product graph from a vertex that
makes `φ` true. -/
theorem fairPath_of_somePath {s : State} (h : ⇓LTL[m,s ⊨∃ φ]) :
    ∃ τ : Ty φ, Formula.eval (m.v s) τ.1 φ ∧
      FairPath (prodRel m φ) (fairPred m φ) (Formula.untils φ) (s, τ) := by
  obtain ⟨f, hf, h0, hsat⟩ := h
  obtain ⟨g, hgf, hs, hfair⟩ := exists_fairRun m φ hf
  have hs0 : (g 0).1 = s := by rw [hgf, h0]
  refine ⟨(g 0).2, ?_, g, Prod.ext hs0 rfl, hs, hfair⟩
  have htrace : prodTrace m φ g = m.trace f := congrArg m.trace (funext hgf)
  have := (key_eval m φ g hs hfair subset_rfl 0).2 (by rw [htrace]; exact hsat)
  rw [← hs0]
  exact this

/-- A fair path of the product graph from a vertex making `φ` true gives a path of the model
satisfying `φ`. -/
theorem somePath_of_fairPath {s : State} {τ : Ty φ} (hev : Formula.eval (m.v s) τ.1 φ)
    (hfp : FairPath (prodRel m φ) (fairPred m φ) (Formula.untils φ) (s, τ)) :
    ⇓LTL[m,s ⊨∃ φ] := by
  obtain ⟨g, h0, hs, hfair⟩ := hfp
  refine ⟨fun n => (g n).1, fun n => (hs n).1, by simp [h0], ?_⟩
  refine (key_eval m φ g hs hfair subset_rfl 0).1 ?_
  rw [h0]
  exact hev

/-- **Tableau construction.** Some maximal path of the model satisfies `φ` iff the product graph
has a fair path from a vertex that makes `φ` true. -/
theorem somePath_iff_fairPath {s : State} :
    ⇓LTL[m,s ⊨∃ φ] ↔ ∃ τ : Ty φ, Formula.eval (m.v s) τ.1 φ ∧
      FairPath (prodRel m φ) (fairPred m φ) (Formula.untils φ) (s, τ) :=
  ⟨fairPath_of_somePath m φ, fun ⟨_, hev, hfp⟩ => somePath_of_fairPath m φ hev hfp⟩

end Correctness

section Decidable

variable {State : Type*} [Fintype State] [DecidableEq State] (m : CTL.Model State Atom)
  [DecidableRel m.tr] [∀ s p, Decidable (m.v s p)] (φ : Formula Atom)

instance : DecidableRel (prodRel m φ) := fun a b =>
  inferInstanceAs (Decidable ((m.tr a.1 b.1 ∨ (m.Dead a.1 ∧ b.1 = a.1)) ∧
    ∀ ψ ∈ Formula.elem φ, Formula.edge (m.v a.1) (m.v b.1) a.2.1 b.2.1 ψ))

instance : ∀ (ψ : Formula Atom) (v : State × Ty φ), Decidable (fairPred m φ ψ v)
  | .atom _, _ => isTrue trivial
  | .false, _ => isTrue trivial
  | .not _, _ => isTrue trivial
  | .or _ _, _ => isTrue trivial
  | .next _, _ => isTrue trivial
  | .until a b, v => inferInstanceAs (Decidable
      ((a U b) ∉ v.2.1 ∨ Formula.eval (m.v v.1) v.2.1 b))

/-- LTL model checking is decidable for finite models: whether some maximal path from a state
satisfies a formula. -/
instance instDecidableSomePath (s : State) : Decidable (⇓LTL[m,s ⊨∃ φ]) :=
  decidable_of_iff _ (somePath_iff_fairPath m φ).symm

/-- LTL model checking is decidable for finite models: whether all maximal paths from a state
satisfy a formula. -/
instance instDecidableAllPaths (s : State) : Decidable (⇓LTL[m,s ⊨∀ φ]) :=
  decidable_of_iff _ allPaths_iff_not_somePath.symm

end Decidable

end Cslib.Logic.LTL
