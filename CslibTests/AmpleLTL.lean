/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Logics.Temporal.LTL.AmpleSets
import Cslib.Logics.Temporal.LTL.Stuttering

open Cslib
open Cslib.Logic Cslib.Logic.LTL
open scoped InferenceSystem CTL

namespace CslibTests

namespace AmpleLTL

/-- The formula `G F p` has no next-time operator. -/
example : (Cslib.Logic.LTL.Formula.always (.eventually (.atom 0 :
    Cslib.Logic.LTL.Formula ℕ))).NextFree :=
  .always (.eventually trivial)

/-- A formula with next-time is not next-free. -/
example : ¬ (Cslib.Logic.LTL.Formula.next (.atom 0 : Cslib.Logic.LTL.Formula ℕ)).NextFree :=
  fun h => h

/-- Repeating a letter gives a stuttering equivalent sequence. -/
example (x : ωSequence ℕ) : x.StutterEq (ωSequence.cons (x 0) x) :=
  ωSequence.StutterEq.cons_head_stutterEq x

/-- Stuttering must stop: `0 1 1 1 ...` and `0 0 0 ...` are not stuttering equivalent. -/
example : ¬ (⟨fun n => if n = 0 then 0 else 1⟩ : ωSequence ℕ).StutterEq (ωSequence.const 0) := by
  rintro ⟨p, q, -, -, hps, -, h⟩
  obtain ⟨n, hn⟩ := hps 1
  have := h n
  simp [hn] at this

/-- Partial-order reduction with the stepwise stubbornness preserves next-free LTL on all paths,
without determinism of the LTS. -/
example {State Label Atom : Type} (lts : LTS State Label) (v : State → Atom → Prop)
    (A : State → Set Label) (Inv : Label → Prop) (hA : lts.IsAmpleStep A Inv) {s : State}
    (h3 : lts.CycleProviso A s) {S : Set Atom}
    (hS : ∀ s μ s' p, p ∈ S → lts.Tr s μ s' → Inv μ → (v s p ↔ v s' p))
    {φ : Cslib.Logic.LTL.Formula Atom} (hφ : φ.NextFree) (hφS : φ.atomSet ⊆ S) :
    ⇓LTL[(⟨lts, v⟩ : CTL.Model State Atom),s ⊨∀ φ] ↔
      ⇓LTL[(⟨lts.reduced A, v⟩ : CTL.Model State Atom),s ⊨∀ φ] :=
  Cslib.Logic.LTL.allPaths_reduced_iff_of_isAmpleStep hA h3 hS hφ hφS

/-- A stubborn selector of a deterministic LTS is a stepwise stubborn one. -/
example {State Label : Type} (lts : LTS State Label) [lts.Deterministic] (A : State → Set Label)
    (Inv : Label → Prop) (hA : lts.IsAmple A Inv) : lts.IsAmpleStep A Inv :=
  hA.toIsAmpleStep

end AmpleLTL

end CslibTests
