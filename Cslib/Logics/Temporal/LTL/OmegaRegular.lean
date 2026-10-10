/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Logics.Temporal.LTL.ModelChecking
public import Cslib.Computability.Languages.OmegaRegularLanguage
public import Cslib.Computability.Automata.NA.Degeneralize

/-! # LTL languages are ω-regular

The ω-language of an LTL formula is ω-regular: it is accepted by a finite-state nondeterministic
Büchi automaton. The alphabet, the sets of atoms, may be infinite: the automaton only depends on the
finitely many atoms that occur in the formula.

The automaton is the tableau of the formula, the product graph used for model checking, for the
model whose states are the letters (sets of atoms) and in which every letter can follow every
letter. A state is the restriction of a letter to the atoms of the formula together with the type
of the current position, the transitions read a letter with that restriction, and a run is
accepting if it visits the fairness sets infinitely often. The generalised Büchi acceptance becomes
Büchi acceptance with a counter (`NA.degeneralize`).

## Main definitions

- `Formula.tableau`: the nondeterministic automaton of a formula.

## Main statements

- `Satisfies.restrict_iff`: a formula only depends on its atoms.
- `Formula.language_eq_tableau`: the language of a formula is the sequences with a run of the
  tableau visiting each fairness set infinitely often.
- `Formula.isRegular_language`: the ω-language of an LTL formula is ω-regular.
-/

@[expose] public section

namespace Cslib.Logic.LTL

open Cslib Cslib.Automata Cslib.ωSequence Filter
open scoped InferenceSystem Formula Cslib.Logic

variable {Atom : Type*} [DecidableEq Atom]

/-- The model whose states are the letters, sets of atoms: any letter can follow any letter, and
the atoms that hold at a letter are those it contains. -/
def letterModel (Atom : Type*) : CTL.Model (Set Atom) Atom :=
  .ofRel (fun _ _ => True) fun a p => p ∈ a

omit [DecidableEq Atom] in
theorem letterModel_trace (f : ℕ → Set Atom) : (letterModel Atom).trace f = ⟨f⟩ := rfl

omit [DecidableEq Atom] in
theorem letterModel_isPath (f : ℕ → Set Atom) : (letterModel Atom).IsPath f :=
  fun _ => Or.inl trivial

namespace Formula

/-- The atoms occurring in a formula. -/
def atoms : Formula Atom → Finset Atom
  | .atom p => {p}
  | .false => ∅
  | .not a => atoms a
  | .or a b => atoms a ∪ atoms b
  | .next a => atoms a
  | .until a b => atoms a ∪ atoms b

end Formula

/-- The sequence with every letter restricted to the atoms in `A`. -/
def restrictWord (A : Set Atom) (w : ωSequence (Set Atom)) : ωSequence (Set Atom) :=
  ⟨fun n => w n ∩ A⟩

/-- Whether a sequence satisfies a formula only depends on the atoms of the formula. -/
theorem Satisfies.restrict_iff {A : Set Atom} :
    ∀ {φ : Formula Atom}, (↑φ.atoms ⊆ A) → ∀ w : ωSequence (Set Atom),
      (⇓LTL[restrictWord A w ⊨ φ] ↔ ⇓LTL[w ⊨ φ])
  | .atom p, h, w => by
    have hp : p ∈ A := h (by simp [Formula.atoms])
    rw [Satisfies.atom_iff, Satisfies.atom_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, hp⟩⟩
  | .false, _, _ => Iff.rfl
  | .not a, h, w => not_congr (Satisfies.restrict_iff (φ := a) h w)
  | .or a b, h, w => or_congr
    (Satisfies.restrict_iff (φ := a) ((Finset.coe_subset.2 Finset.subset_union_left).trans h) w)
    (Satisfies.restrict_iff (φ := b) ((Finset.coe_subset.2 Finset.subset_union_right).trans h) w)
  | .next a, h, w => Satisfies.restrict_iff (φ := a) h w.tail
  | .until a b, h, w => exists_congr fun n => and_congr
    (Satisfies.restrict_iff (φ := b) ((Finset.coe_subset.2 Finset.subset_union_right).trans h)
      (w.drop n))
    (forall_congr' fun k => imp_congr_right fun _ =>
      Satisfies.restrict_iff (φ := a) ((Finset.coe_subset.2 Finset.subset_union_left).trans h)
        (w.drop k))

variable (φ : Formula Atom)

/-- The letters of a formula: the sets of its atoms. -/
abbrev Formula.Letter : Type _ := ↥φ.atoms.powerset

/-- The vertex of the product graph of a state of the tableau. -/
def Formula.vertex (q : φ.Letter × Ty φ) : Set Atom × Ty φ := (↑q.1.1, q.2)

/-- The tableau of a formula as a nondeterministic automaton. A state is a set of atoms of the
formula, standing for a letter, and a type. A transition reads a letter with that restriction to the
atoms of the formula, and respects the local laws of `X` and `U`. The initial states are those that
make the formula true. -/
def Formula.tableau : NA (φ.Letter × Ty φ) (Set Atom) where
  Tr q x q' := (↑q.1.1 : Set Atom) = x ∩ ↑φ.atoms ∧
    prodRel (letterModel Atom) φ (φ.vertex q) (φ.vertex q')
  start := {q | Formula.eval (fun p => p ∈ q.1.1) q.2.1 φ}

/-- The fairness set of the `i`-th `U`-subformula. -/
def Formula.tableauFair (i : ℕ) : Set (φ.Letter × Ty φ) :=
  {q | fairPred (letterModel Atom) φ ((Formula.untils φ).getD i ⊥) (φ.vertex q)}

theorem Formula.tableau_run_iff (w : ωSequence (Set Atom)) (ss : ωSequence (φ.Letter × Ty φ)) :
    φ.tableau.Run w ss ↔ ss 0 ∈ φ.tableau.start ∧ ∀ n, (↑(ss n).1.1 : Set Atom) = w n ∩ ↑φ.atoms ∧
      prodRel (letterModel Atom) φ (φ.vertex (ss n)) (φ.vertex (ss (n + 1))) :=
  ⟨fun ⟨h0, h⟩ => ⟨h0, h⟩, fun ⟨h0, h⟩ => ⟨h0, h⟩⟩

/-- The language of a formula is the set of sequences with a run of the tableau that visits each
fairness set infinitely often. -/
theorem Formula.language_eq_tableau (w : ωSequence (Set Atom)) :
    w ∈ φ.language ↔ ∃ ss, φ.tableau.Run w ss ∧
      ∀ i < (Formula.untils φ).length, ∃ᶠ n in atTop, ss n ∈ φ.tableauFair i := by
  classical
  have hmem : ∀ u ∈ Formula.untils φ, ∃ i, ∃ h : i < (Formula.untils φ).length,
      (Formula.untils φ)[i] = u := fun u hu => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hu
    exact ⟨i, hi, rfl⟩
  constructor
  · intro hw
    let ℓ : ℕ → Finset Atom := fun n => φ.atoms.filter fun p => p ∈ w n
    have hℓ : ∀ n, (↑(ℓ n) : Set Atom) = w n ∩ ↑φ.atoms := fun n => by
      ext p
      simp [ℓ, and_comm]
    have hℓmem : ∀ n, ℓ n ∈ φ.atoms.powerset := fun n =>
      Finset.mem_powerset.2 (Finset.filter_subset _ _)
    obtain ⟨g, hgf, hs, hfair⟩ := exists_fairRun (letterModel Atom) φ
      (letterModel_isPath fun n => (↑(ℓ n) : Set Atom))
    let ss : ωSequence (φ.Letter × Ty φ) := ⟨fun n => (⟨ℓ n, hℓmem n⟩, (g n).2)⟩
    have hv : ∀ n, φ.vertex (ss n) = g n := fun n => Prod.ext (hgf n).symm rfl
    have htrace : prodTrace (letterModel Atom) φ g = restrictWord ↑φ.atoms w := by
      rw [prodTrace, show (fun n => (g n).1) = fun n => (↑(ℓ n) : Set Atom) from funext hgf,
        letterModel_trace]
      exact congrArg ωSequence.mk (funext hℓ)
    refine ⟨ss, (Formula.tableau_run_iff φ w ss).2 ⟨?_, fun n => ⟨hℓ n, ?_⟩⟩, fun i hi => ?_⟩
    · have h0 := (key_eval (letterModel Atom) φ g hs hfair subset_rfl 0).2 (by
        rw [htrace]
        exact (Satisfies.restrict_iff subset_rfl w).2 hw)
      change Formula.eval (fun p => p ∈ (g 0).1) (g 0).2.1 φ at h0
      rw [hgf 0] at h0
      exact h0
    · rw [hv, hv]
      exact hs n
    · rw [frequently_atTop]
      intro N
      obtain ⟨k, hk, hfk⟩ := hfair _ (List.getElem_mem hi) N
      refine ⟨k, hk, ?_⟩
      simpa [Formula.tableauFair, List.getElem?_eq_getElem hi, hv] using hfk
  · rintro ⟨ss, hrun, hfair⟩
    obtain ⟨h0, h⟩ := (Formula.tableau_run_iff φ w ss).1 hrun
    have hs : ∀ n, prodRel (letterModel Atom) φ (φ.vertex (ss n)) (φ.vertex (ss (n + 1))) :=
      fun n => (h n).2
    have hfair' : ∀ u ∈ Formula.untils φ, ∀ n, ∃ k ≥ n,
        fairPred (letterModel Atom) φ u (φ.vertex (ss k)) := by
      intro u hu N
      obtain ⟨i, hi, rfl⟩ := hmem u hu
      obtain ⟨k, hk, hfk⟩ := frequently_atTop.1 (hfair i hi) N
      refine ⟨k, hk, ?_⟩
      simpa [Formula.tableauFair, List.getElem?_eq_getElem hi] using hfk
    have htrace : prodTrace (letterModel Atom) φ (fun n => φ.vertex (ss n)) =
        restrictWord ↑φ.atoms w := by
      rw [prodTrace, letterModel_trace]
      exact congrArg ωSequence.mk (funext fun n => (h n).1)
    have := (key_eval (letterModel Atom) φ (fun n => φ.vertex (ss n)) hs hfair' subset_rfl 0).1 h0
    rw [htrace] at this
    exact (Satisfies.restrict_iff subset_rfl w).1 this

omit [DecidableEq Atom] in
/-- **The ω-language of an LTL formula is ω-regular.** -/
theorem Formula.isRegular_language : φ.language.IsRegular := by
  classical
  rw [ωLanguage.isRegular_iff]
  refine ⟨(φ.Letter × Ty φ) × Fin ((Formula.untils φ).length + 1), inferInstance,
    NA.degeneralize φ.tableau φ.tableauFair (Formula.untils φ).length, ?_⟩
  refine ωLanguage.mem_ext fun w => ?_
  rw [ωAcceptor.mem_language, NA.degeneralize_accepts_iff]
  exact (Formula.language_eq_tableau φ w).symm

end Cslib.Logic.LTL
