/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Foundations.Semantics.LTS.Relation

/-! # Tests for the reachability API of `LTS.CanReach` -/

namespace CslibTests

open Cslib LTS

/-- A counter that counts up by one in each step. -/
def succLTS : LTS ℕ Unit where
  Tr n _ m := m = n + 1

/-- A counter that counts up by two in each step. -/
def succ2LTS : LTS ℕ Unit where
  Tr n _ m := m = n + 2

theorem succLTS_unlabelledTr (n : ℕ) : succLTS.UnlabelledTr n (n + 1) := ⟨(), rfl⟩

example (n : ℕ) : succLTS.CanReach n (n + 1) := .single (μ := ()) rfl

example (n : ℕ) : succLTS.CanReach n (n + 1) := .of_unlabelledTr (succLTS_unlabelledTr n)

example (n : ℕ) : succLTS.CanReach n (n + 2) :=
  (CanReach.of_unlabelledTr (succLTS_unlabelledTr n)).trans
    (.of_unlabelledTr (succLTS_unlabelledTr (n + 1)))

example (n : ℕ) : succLTS.CanReach n n := .refl _ _

example (n : ℕ) : succLTS.CanReach n (n + 2) := by
  trans n + 1 <;> exact .of_unlabelledTr (succLTS_unlabelledTr _)

/-- `calc` can chain reachability with unlabelled transitions in any combination. -/
example (n : ℕ) : succLTS.CanReach n (n + 5) :=
  calc
    succLTS.UnlabelledTr n (n + 1) := succLTS_unlabelledTr n
    succLTS.UnlabelledTr _ (n + 2) := succLTS_unlabelledTr (n + 1)
    succLTS.CanReach _ (n + 3) := .of_unlabelledTr (succLTS_unlabelledTr (n + 2))
    succLTS.UnlabelledTr _ (n + 4) := succLTS_unlabelledTr (n + 3)
    succLTS.CanReach _ (n + 5) := .of_unlabelledTr (succLTS_unlabelledTr (n + 4))

example (n : ℕ) : succLTS.CanReach n (n + 3) :=
  calc
    succLTS.UnlabelledTr n (n + 1) := succLTS_unlabelledTr n
    succLTS.UnlabelledTr _ (n + 2) := succLTS_unlabelledTr (n + 1)
    succLTS.UnlabelledTr _ (n + 3) := succLTS_unlabelledTr (n + 2)

/-- `head` and `tail` add one unlabelled transition at either end. -/
example (n m : ℕ) (h : succLTS.CanReach (n + 1) m) : succLTS.CanReach n m :=
  h.head (succLTS_unlabelledTr n)

example (n m : ℕ) (h : succLTS.CanReach n m) : succLTS.CanReach n (m + 1) :=
  h.tail (succLTS_unlabelledTr m)

/-- Reachability in `succLTS` is `≤`, by induction on the last transition. -/
example (n m : ℕ) (h : succLTS.CanReach n m) : n ≤ m := by
  induction h using CanReach.induction_on with
  | refl => exact le_rfl
  | tail _ hab ih =>
    obtain ⟨_, rfl⟩ := hab
    omega

/-- Reachability in `succLTS` is `≤`, by induction on the first transition. -/
example (n m : ℕ) (h : succLTS.CanReach n m) : n ≤ m := by
  induction h using CanReach.head_induction_on with
  | refl => exact le_rfl
  | head hab _ ih =>
    obtain ⟨_, rfl⟩ := hab
    omega

/-- Both principles are also usable by `refine`, with a motive that ignores the proof. -/
example (n m : ℕ) (h : succLTS.CanReach n m) : n ≤ m :=
  CanReach.induction_on (P := fun t _ => n ≤ t) h le_rfl fun _ hab ih => by
    obtain ⟨_, rfl⟩ := hab
    omega

/-- A state map sending unlabelled transitions to unlabelled transitions preserves reachability. -/
example (n m : ℕ) (h : succLTS.CanReach n m) : succ2LTS.CanReach (2 * n) (2 * m) :=
  h.lift (lts' := succ2LTS) (2 * ·) fun a _ ⟨_, hab⟩ => ⟨(), by simp_all [succLTS, succ2LTS]; omega⟩

end CslibTests
