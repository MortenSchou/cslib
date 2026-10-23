/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Logics.Temporal.LTL.Basic
public import Cslib.Computability.Languages.SafetyLiveness

/-! # Safety and liveness of LTL formulas

`G φ`, for a state formula `φ`, defines a safety property (a closed set of ω-sequences): a violation
is witnessed by a finite prefix. `F φ`, for a satisfiable `φ`, defines a liveness property (a dense
set): every finite prefix extends to a sequence satisfying it. These are the two classes of
[AlpernSchneider1985].
-/

@[expose] public section

namespace Cslib.Logic.LTL

open Cslib Cslib.ωSequence Cslib.ωLanguage
open scoped InferenceSystem Formula Cslib.Logic

variable {Atom : Type*} {φ : Formula Atom}

/-- A state formula only depends on the first position. -/
theorem Satisfies.of_isState {w w' : ωSequence (Set Atom)} (h : φ.IsState) (h0 : w 0 = w' 0) :
    ⇓LTL[w ⊨ φ] ↔ ⇓LTL[w' ⊨ φ] := by
  induction φ with
  | atom p => simp [h0]
  | false => exact Iff.rfl
  | not φ ih => exact not_congr (ih h)
  | or φ ψ ihφ ihψ => exact or_congr (ihφ h.1) (ihψ h.2)
  | next φ => exact h.elim
  | «until» φ ψ => exact h.elim

/-- Eventually a satisfiable formula is a liveness property: every finite prefix extends to a
sequence satisfying it. -/
theorem isLiveness_language_F (h : ∃ w, ⇓LTL[w ⊨ φ]) : (F φ).language.IsLiveness := by
  obtain ⟨w, hw⟩ := h
  rw [isLiveness_iff]
  intro xs n
  refine ⟨w, Satisfies.eventually_iff.2 ⟨n, ?_⟩⟩
  have : ((xs.take n) ++ω w).drop n = w := by
    refine DFunLike.ext _ _ fun i => ?_
    change ((xs.take n) ++ω w) (i + n) = w i
    rw [Nat.add_comm]
    simpa [length_take] using get_append_right (x := xs.take n) (a := w) (n := i)
  rw [this]
  exact hw

/-- Always a state formula is a safety property: a violation is witnessed by a finite prefix. -/
theorem isSafety_language_G (h : φ.IsState) : (G φ).language.IsSafety := by
  rw [isSafety_iff]
  intro xs hxs
  have : ¬ ⇓LTL[xs ⊨ G φ] := hxs
  rw [Satisfies.always_iff] at this
  push Not at this
  obtain ⟨k, hk⟩ := this
  refine ⟨k + 1, fun ys hys => ?_⟩
  refine hk ?_
  have hys' : ⇓LTL[xs.take (k + 1) ++ω ys ⊨ G φ] := hys
  rw [Satisfies.always_iff] at hys'
  have := hys' k
  rw [Satisfies.of_isState h (w' := xs.drop k)] at this
  · exact this
  · have hlt : k < (xs.take (k + 1)).length := by simp [length_take]
    have h2 := getElem?_take (s := xs) (k := k) (n := k + 1) (Nat.lt_succ_self k)
    rw [List.getElem?_eq_getElem hlt] at h2
    change (xs.take (k + 1) ++ω ys) (0 + k) = xs (0 + k)
    rw [Nat.zero_add]
    exact (get_append_left (x := xs.take (k + 1)) (a := ys) (n := k) hlt).trans
      (Option.some.inj h2)

end Cslib.Logic.LTL
