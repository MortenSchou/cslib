/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Foundations.Data.RatDefinable.FourierMotzkin

@[expose] public section

namespace CslibTests.FourierMotzkin

open Cslib Function

/-- The constraint `a * y + b * x ≥ 0` (or `> 0`) on the variables `y = 0` and `x = 1`. -/
def mk (a b : ℤ) (σ : Bool) : LinCons (Fin 2) := ⟨![a, b], σ⟩

/-- The triangle-like system `x ≥ 0`, `y ≥ 0`, `x - y ≥ 0`. -/
def triangle : List (LinCons (Fin 2)) := [mk 0 1 false, mk 1 0 false, mk (-1) 1 false]

/-- Eliminating `y` from the triangle yields `x ≥ 0` (twice, once from the combination). -/
example : (elimSystem 0 triangle).map (fun g => (g.coeff 0, g.coeff 1, g.strict)) =
    [(0, 1, false), (0, 1, false)] := by decide +kernel

/-- `y > 0` and `-y ≥ 0` is unsatisfiable, and the eliminated system detects it. -/
def contradictory : List (LinCons (Fin 2)) := [mk 1 0 true, mk (-1) 0 false]

example : (elimSystem 0 contradictory).map (fun g => (g.coeff 0, g.coeff 1, g.strict)) =
    [(0, 0, true)] := by decide +kernel

lemma elimSystem_contradictory :
    elimSystem 0 contradictory = [LinCons.comb 0 (mk 1 0 true) (mk (-1) 0 false)] := rfl

example (v : Fin 2 → ℚ) : ¬ ∃ y : ℚ, ∀ g ∈ contradictory, g.Holds (update v 0 y) := by
  rw [exists_holds_iff_elimSystem]
  intro h
  have h0 := h (LinCons.comb 0 (mk 1 0 true) (mk (-1) 0 false))
    (by rw [elimSystem_contradictory]; exact List.mem_singleton_self _)
  simp [LinCons.Holds, LinCons.eval, StrictRel, LinCons.comb, mk, Fin.sum_univ_two] at h0

/-! ### Projection of a definable set -/

/-- The triangle `x ≥ 0`, `y ≥ 0`, `x - y ≥ 0` in coordinates `Unit ⊕ Unit`. -/
def triangleSet : Set (Unit ⊕ Unit → ℚ) :=
  {w | 0 ≤ w (.inl ()) ∧ 0 ≤ w (.inr ()) ∧ w (.inr ()) ≤ w (.inl ())}

lemma triangleSet_definable : RatDefinable triangleSet := by
  refine ⟨[[⟨Sum.elim (fun _ => 1) (fun _ => 0), false⟩,
    ⟨Sum.elim (fun _ => 0) (fun _ => 1), false⟩,
    ⟨Sum.elim (fun _ => 1) (fun _ => -1), false⟩]], Set.ext fun w => ?_⟩
  simp [triangleSet, LinCons.Holds, LinCons.eval, StrictRel]

/-- Existential quantification over `y` of the triangle is definable. -/
example : RatDefinable {v : Unit → ℚ | ∃ w : Unit → ℚ, Sum.elim v w ∈ triangleSet} :=
  triangleSet_definable.proj

end CslibTests.FourierMotzkin
