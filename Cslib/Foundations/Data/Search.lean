/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Init
public import Mathlib.Data.Nat.Find
public import Mathlib.Logic.Function.Iterate

/-! # Terminating searches that `decide` can evaluate

The decision procedures for executable Petri nets search for the first iterate of a function that
satisfies a decidable predicate, such as the first closed level of reachable markings. That such an
iterate exists is proved with Dickson's lemma or similar non-constructive arguments, so a search by
`Nat.find` is computable but cannot be evaluated by `decide`.

`searchIter` therefore first runs the search for a fixed number of steps by structural recursion on
a fuel parameter, which `decide` evaluates, and only then falls back to `Nat.find`. The result is
the same either way.

## Main definitions

- `iterFind`: the first iterate within a number of steps that satisfies a predicate.
- `searchIter`: the first iterate satisfying a predicate, given that one exists.
- `searchNat`: the least natural number satisfying a predicate, given that one exists.
-/

@[expose] public section

namespace Cslib

variable {α : Type*}

/-- Apply `f` to `x` at most `fuel` times, and return the first iterate satisfying `p`. -/
def iterFind (f : α → α) (p : α → Prop) [DecidablePred p] : ℕ → α → Option α
  | 0, _ => none
  | fuel + 1, x => if p x then some x else iterFind f p fuel (f x)

theorem iterFind_spec {f : α → α} {p : α → Prop} [DecidablePred p] {fuel : ℕ} {x y : α}
    (h : iterFind f p fuel x = some y) : ∃ n, y = f^[n] x ∧ p y := by
  induction fuel generalizing x with
  | zero => simp [iterFind] at h
  | succ fuel ih =>
    unfold iterFind at h
    split_ifs at h with hp
    · obtain rfl := Option.some.inj h
      exact ⟨0, rfl, hp⟩
    · obtain ⟨n, rfl, hy⟩ := ih h
      exact ⟨n + 1, by rw [Function.iterate_succ_apply], hy⟩

/-- The number of steps tried by structural recursion before `searchIter` falls back to
`Nat.find`. -/
def searchFuel : ℕ := 256

/-- The first iterate of `f` from `x` that satisfies `p`, given that one exists. -/
def searchIter (f : α → α) (p : α → Prop) [DecidablePred p] (x : α)
    (hex : ∃ n, p (f^[n] x)) : α :=
  match iterFind f p searchFuel x with
  | some y => y
  | none => f^[Nat.find hex] x

theorem searchIter_spec (f : α → α) (p : α → Prop) [DecidablePred p] (x : α)
    (hex : ∃ n, p (f^[n] x)) : ∃ n, searchIter f p x hex = f^[n] x ∧ p (searchIter f p x hex) := by
  unfold searchIter
  split
  · rename_i y h
    exact iterFind_spec h
  · exact ⟨_, rfl, Nat.find_spec hex⟩

/-- Counting up from `0` for `n` steps gives `n`. -/
private theorem iterate_succ_zero (n : ℕ) : (fun x : ℕ => x + 1)^[n] 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]

/-- The first natural number satisfying `p`, found by counting up from `0`, given that one
exists. -/
def searchNat (p : ℕ → Prop) [DecidablePred p] (hex : ∃ n, p n) : ℕ :=
  searchIter (· + 1) p 0 (hex.imp fun n h => by rwa [iterate_succ_zero])

theorem searchNat_spec (p : ℕ → Prop) [DecidablePred p] (hex : ∃ n, p n) :
    p (searchNat p hex) := by
  obtain ⟨-, -, h⟩ := searchIter_spec (· + 1) p 0 (hex.imp fun n h => by rwa [iterate_succ_zero])
  exact h

end Cslib
