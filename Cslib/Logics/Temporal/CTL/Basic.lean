/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Foundations.Logic.Operators

/-! # Computation Tree Logic (CTL)

CTL is a branching-time temporal logic for specifying the behaviour of transition systems: it
combines path quantifiers (`E`, there is a path, and `A`, on all paths) with the temporal operators
next (`X`), until (`U`), eventually (`F`) and always (`G`).

## Implementation notes

We follow the minimal basis `{⊥, ¬, ∨, EX, E[· U ·], EG}`, recovering the other connectives and
temporal operators as derived constructs (see [Clarke1986]). Atomic propositions are arbitrary.

## Main definitions

- `Formula`: CTL formulas.
- `Formula.ax`, `Formula.ef`, `Formula.af`, `Formula.ag`, `Formula.au`: the derived operators.

## References

* [E. M. Clarke, E. A. Emerson, A. P. Sistla, *Automatic verification of finite-state concurrent
  systems using temporal logic specifications*][Clarke1986]
-/

@[expose] public section

namespace Cslib.Logic.CTL

/-- A CTL formula over the atoms `Atom`. -/
inductive Formula (Atom : Type u) where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Falsehood. -/
  | false
  /-- Negation. -/
  | not (φ : Formula Atom)
  /-- Disjunction. -/
  | or (φ₁ φ₂ : Formula Atom)
  /-- `EX φ`: some successor satisfies `φ`. -/
  | ex (φ : Formula Atom)
  /-- `E[φ₁ U φ₂]`: some maximal path satisfies `φ₂` at some point, and `φ₁` before. -/
  | eu (φ₁ φ₂ : Formula Atom)
  /-- `EG φ`: some maximal path satisfies `φ` everywhere. -/
  | eg (φ : Formula Atom)

namespace Formula

variable {Atom : Type*}

instance : Bot (Formula Atom) := ⟨.false⟩
instance : HasNot (Formula Atom) := ⟨.not⟩
instance : HasOr (Formula Atom) := ⟨.or⟩

instance : Coe Atom (Formula Atom) := ⟨.atom⟩

theorem false_def : (Formula.false : Formula Atom) = ⊥ := rfl

theorem not_def (φ : Formula Atom) : φ.not = ¬φ := rfl

theorem or_def (φ ψ : Formula Atom) : φ.or ψ = (φ ∨ ψ) := rfl

open scoped Cslib.Logic in
/-- Truth. -/
instance : Top (Formula Atom) := ⟨¬⊥⟩

open scoped Cslib.Logic in
/-- Conjunction, defined by De Morgan's law. -/
instance : HasAnd (Formula Atom) := ⟨fun φ ψ => ¬(¬φ ∨ ¬ψ)⟩

open scoped Cslib.Logic in
/-- Implication. -/
instance : HasImp (Formula Atom) := ⟨fun φ ψ => ¬φ ∨ ψ⟩

open scoped Cslib.Logic in
/-- Bi-implication. -/
instance : HasIff (Formula Atom) := ⟨fun φ ψ => (φ → ψ) ∧ (ψ → φ)⟩

open scoped Cslib.Logic in
/-- `AX φ`: all successors satisfy `φ`. It holds vacuously at states without successors. -/
def ax (φ : Formula Atom) : Formula Atom := ¬(Formula.ex (¬φ))

open scoped Cslib.Logic in
/-- `EF φ`: some path eventually reaches `φ`. -/
def ef (φ : Formula Atom) : Formula Atom := Formula.eu ⊤ φ

open scoped Cslib.Logic in
/-- `AF φ`: all maximal paths eventually reach `φ`. -/
def af (φ : Formula Atom) : Formula Atom := ¬(Formula.eg (¬φ))

open scoped Cslib.Logic in
/-- `AG φ`: `φ` holds everywhere on all reachable states. -/
def ag (φ : Formula Atom) : Formula Atom := ¬(ef (¬φ))

open scoped Cslib.Logic in
/-- `A[φ₁ U φ₂]`: on all maximal paths, `φ₂` eventually holds, and `φ₁` before. -/
def au (φ₁ φ₂ : Formula Atom) : Formula Atom :=
  ¬((Formula.eu (¬φ₂) ((¬φ₁) ∧ (¬φ₂))) ∨ (Formula.eg (¬φ₂)))

open scoped Cslib.Logic in
/-- The states without successors, definable in CTL as `¬EX ⊤`. -/
def deadlock : Formula Atom := ¬(Formula.ex ⊤)

@[inherit_doc] scoped notation:max "EX " φ:max => Formula.ex φ
@[inherit_doc] scoped notation:max "EG " φ:max => Formula.eg φ
@[inherit_doc] scoped notation:max "EF " φ:max => Formula.ef φ
@[inherit_doc] scoped notation:max "AX " φ:max => Formula.ax φ
@[inherit_doc] scoped notation:max "AF " φ:max => Formula.af φ
@[inherit_doc] scoped notation:max "AG " φ:max => Formula.ag φ
/-- `E[φ₁ U φ₂]`. The first argument has precedence above that of the infix `U` of LTL, so that
the notations can be used together; a conjunction in it needs parentheses. -/
scoped notation "E[" φ₁:51 " U " φ₂ "]" => Formula.eu φ₁ φ₂

/-- `A[φ₁ U φ₂]`, with the same remark on precedence as for `E[φ₁ U φ₂]`. -/
scoped notation "A[" φ₁:51 " U " φ₂ "]" => Formula.au φ₁ φ₂

end Formula

end Cslib.Logic.CTL
