/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Foundations.Data.OmegaSequence.Stuttering
public import Cslib.Logics.Temporal.LTL.Basic

/-! # LTL without next-time is invariant under stuttering

An LTL formula without the next-time operator `X` cannot count how many times a letter is repeated,
so it cannot distinguish stuttering equivalent ω-sequences
(`Cslib.Foundations.Data.OmegaSequence.Stuttering`). This is the reason why partial-order reduction
preserves LTL without next-time.

## Main definitions

- `Formula.NextFree`: the formula does not contain `X`.
- `Formula.atomSet`: the set of atoms of a formula (`Formula.atoms` in `OmegaRegular` is the
  `Finset`, which needs decidable equality).

## Main statements

- `Satisfies.iff_of_stutterEq`: a next-free formula has the same truth value on stuttering
  equivalent sequences.
- `Satisfies.iff_of_stutterEq_inter`: the same, if the sequences are only equivalent after
  restricting the letters to a set of atoms that contains those of the formula.
-/

@[expose] public section

namespace Cslib.Logic.LTL

open Cslib Cslib.ωSequence

variable {Atom : Type*}

namespace Formula

/-- The formula does not contain the next-time operator. -/
def NextFree : Formula Atom → Prop
  | .atom _ => True
  | .false => True
  | .not φ => NextFree φ
  | .or φ ψ => NextFree φ ∧ NextFree ψ
  | .next _ => False
  | .until φ ψ => NextFree φ ∧ NextFree ψ

/-- The atoms that occur in the formula. -/
def atomSet : Formula Atom → Set Atom
  | .atom p => {p}
  | .false => ∅
  | .not φ => atomSet φ
  | .or φ ψ => atomSet φ ∪ atomSet ψ
  | .next φ => atomSet φ
  | .until φ ψ => atomSet φ ∪ atomSet ψ

open scoped Cslib.Logic

/-- `⊤` does not contain the next-time operator. -/
theorem NextFree.top : (⊤ : Formula Atom).NextFree := trivial

/-- A conjunction of formulas without next-time has no next-time. -/
theorem NextFree.and {φ ψ : Formula Atom} (hφ : φ.NextFree) (hψ : ψ.NextFree) :
    (φ ∧ ψ).NextFree := ⟨hφ, hψ⟩

/-- An implication between formulas without next-time has no next-time. -/
theorem NextFree.imp {φ ψ : Formula Atom} (hφ : φ.NextFree) (hψ : ψ.NextFree) :
    (φ → ψ).NextFree := ⟨hφ, hψ⟩

/-- `F φ` has no next-time if `φ` has none. -/
theorem NextFree.eventually {φ : Formula Atom} (hφ : φ.NextFree) : (F φ).NextFree :=
  ⟨NextFree.top, hφ⟩

/-- `G φ` has no next-time if `φ` has none. -/
theorem NextFree.always {φ : Formula Atom} (hφ : φ.NextFree) : (G φ).NextFree :=
  NextFree.eventually hφ

/-- `φ W ψ` has no next-time if `φ` and `ψ` have none. -/
theorem NextFree.weakUntil {φ ψ : Formula Atom} (hφ : φ.NextFree) (hψ : ψ.NextFree) :
    (φ W ψ).NextFree := ⟨⟨hφ, hψ⟩, NextFree.always hφ⟩

/-- `φ R ψ` has no next-time if `φ` and `ψ` have none. -/
theorem NextFree.release {φ ψ : Formula Atom} (hφ : φ.NextFree) (hψ : ψ.NextFree) :
    (φ R ψ).NextFree := ⟨hφ, hψ⟩

end Formula

/-- The truth of a formula only depends on the letters restricted to the atoms of the formula. -/
theorem Satisfies.iff_map_inter {S : Set Atom} {φ : Formula Atom} (hφ : φ.atomSet ⊆ S) :
    ∀ {w : ωSequence (Set Atom)}, Satisfies w φ ↔ Satisfies (w.map (· ∩ S)) φ := by
  induction φ with
  | atom p =>
    intro w
    exact ⟨fun h => ⟨h, hφ rfl⟩, fun h => h.1⟩
  | false => exact Iff.rfl
  | not φ ih => exact fun {w} => not_congr (ih hφ)
  | or φ ψ ihφ ihψ =>
    exact fun {w} => or_congr (ihφ (hφ.trans' Set.subset_union_left))
      (ihψ (hφ.trans' Set.subset_union_right))
  | next φ ih =>
    exact fun {w} => ih hφ
  | «until» φ ψ ihφ ihψ =>
    exact fun {w} => exists_congr fun n => and_congr
      (by rw [drop_map]; exact ihψ (hφ.trans' Set.subset_union_right))
      (forall_congr' fun k => imp_congr_right fun _ => by
        rw [drop_map]; exact ihφ (hφ.trans' Set.subset_union_left))

/-- The core of the until case: stuttering equivalence transfers the witness of an until. -/
private theorem until_of_stutterEq {φ ψ : Formula Atom}
    (ihφ : ∀ {x y : ωSequence (Set Atom)}, StutterEq x y → (Satisfies x φ ↔ Satisfies y φ))
    (ihψ : ∀ {x y : ωSequence (Set Atom)}, StutterEq x y → (Satisfies x ψ ↔ Satisfies y ψ))
    {x y : ωSequence (Set Atom)} (h : StutterEq x y) (hx : Satisfies x (.until φ ψ)) :
    Satisfies y (.until φ ψ) := by
  classical
  obtain ⟨p, q, hp, hq, hps, hqs, hpq⟩ := h
  obtain ⟨i, hψ, hk⟩ := hx
  have hex : ∃ n, p n = i := hps i
  have hspec : p (Nat.find hex) = i := Nat.find_spec hex
  refine ⟨q (Nat.find hex), ?_, fun k hk' => ?_⟩
  · rw [← ihψ (StutterEq.drop_aligned hp hq hps hqs hpq (Nat.find hex)), hspec]
    exact hψ
  · obtain ⟨m, rfl⟩ := hqs k
    have hmn : m < Nat.find hex := by
      by_contra hcon
      exact absurd (hq (not_lt.1 hcon)) (not_le.2 hk')
    have hlt : p m < i := by
      have hle : p m ≤ i := hspec ▸ hp hmn.le
      exact lt_of_le_of_ne hle fun heq => Nat.find_min hex hmn heq
    rw [← ihφ (StutterEq.drop_aligned hp hq hps hqs hpq m)]
    exact hk _ hlt

/-- A formula without next-time has the same truth value on stuttering equivalent sequences. -/
theorem Satisfies.iff_of_stutterEq {φ : Formula Atom} (hφ : φ.NextFree) :
    ∀ {x y : ωSequence (Set Atom)}, StutterEq x y → (Satisfies x φ ↔ Satisfies y φ) := by
  induction φ with
  | atom p =>
    intro x y h
    change p ∈ x 0 ↔ p ∈ y 0
    rw [h.head_eq]
  | false => exact fun _ => Iff.rfl
  | not φ ih => exact fun h => not_congr (ih hφ h)
  | or φ ψ ihφ ihψ => exact fun h => or_congr (ihφ hφ.1 h) (ihψ hφ.2 h)
  | next φ ih => exact hφ.elim
  | «until» φ ψ ihφ ihψ =>
    exact fun h => ⟨until_of_stutterEq (ihφ hφ.1) (ihψ hφ.2) h,
      until_of_stutterEq (ihφ hφ.1) (ihψ hφ.2) h.symm⟩

/-- A formula without next-time cannot distinguish sequences that are stuttering equivalent after
restricting the letters to a set of atoms that contains the atoms of the formula. -/
theorem Satisfies.iff_of_stutterEq_inter {S : Set Atom} {φ : Formula Atom} (hφ : φ.NextFree)
    (hS : φ.atomSet ⊆ S) {x y : ωSequence (Set Atom)}
    (h : StutterEq (x.map (· ∩ S)) (y.map (· ∩ S))) : Satisfies x φ ↔ Satisfies y φ :=
  (Satisfies.iff_map_inter hS).trans
    ((Satisfies.iff_of_stutterEq hφ h).trans (Satisfies.iff_map_inter hS).symm)

end Cslib.Logic.LTL
