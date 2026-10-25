/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Logics.Temporal.CTL.Semantics

/-! # CTL as an extension of basic modal logic

A CTL model is a modal model for the signature with one unary modality, `PFunctor.y`. The
`EX`-fragment of CTL is basic modal logic: `Formula.ofModal` embeds modal propositions, and
`Satisfies.ofModal_iff` shows that satisfaction is the modal satisfaction.

CTL formulas are not defined by wrapping `Modal.Proposition`, since `EX` must be able to contain
`E[· U ·]` and `EG`, and a modal proposition cannot contain them.
-/

@[expose] public section

namespace Cslib.Logic.CTL

open scoped InferenceSystem Formula Cslib.Logic Modal

variable {State : Type*} {Atom : Type*}

/-- The embedding of basic modal propositions into CTL: `◇` becomes `EX`. -/
def Formula.ofModal : Modal.Proposition PFunctor.y.{0, 0} Atom → Formula Atom
  | .atom p => .atom p
  | .false => .false
  | .not φ => .not (ofModal φ)
  | .or φ ψ => .or (ofModal φ) (ofModal ψ)
  | .triangle _ φs => .ex (ofModal (φs PUnit.unit))

/-- On the modal fragment, CTL satisfaction is modal satisfaction. -/
theorem Satisfies.ofModal_iff (m : Model State Atom) (s : State)
    (φ : Modal.Proposition PFunctor.y.{0, 0} Atom) :
    ⇓CTL[m,s ⊨ Formula.ofModal φ] ↔ ⇓Modal[m,s ⊨ φ] := by
  induction φ generalizing s with
  | atom p => exact Iff.rfl
  | false => exact Iff.rfl
  | not φ ih =>
    change ⇓CTL[m,s ⊨ ¬Formula.ofModal φ] ↔ ⇓Modal[m,s ⊨ ¬φ]
    rw [Satisfies.not_iff, Modal.Satisfies.not_iff_not, ih]
  | or φ ψ ihφ ihψ =>
    change ⇓CTL[m,s ⊨ Formula.ofModal φ ∨ Formula.ofModal ψ] ↔ ⇓Modal[m,s ⊨ φ ∨ ψ]
    rw [Satisfies.or_iff, Modal.Satisfies.or_iff_or, ihφ, ihψ]
  | triangle op φs ih =>
    change ⇓CTL[m,s ⊨ EX (Formula.ofModal (φs PUnit.unit))] ↔ _
    rw [Satisfies.ex_iff]
    simp only [ih]
    constructor
    · rintro ⟨t, htr, ht⟩
      exact ⟨fun _ => t, htr, fun _ => ht⟩
    · rintro ⟨ws, hr, hws⟩
      exact ⟨ws PUnit.unit, Frame.diagonal_of_r hr, hws PUnit.unit⟩

end Cslib.Logic.CTL
