/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.WSTS.Coverability
public import Mathlib.Data.Nat.Nth
public import Mathlib.Order.Interval.Set.Infinite

/-! # Vector addition systems with states

A *vector addition system with states* (VASS) has a control state and a vector of natural-number
counters. A rule moves between control states and adds an integer vector to the counters, which
must stay non-negative. VASS are the standard example of a WSTS beyond Petri nets: configurations
are ordered by comparing the counters while requiring *equal* control states, which is a
well-quasi-order when there are finitely many control states and counters.

## Main definitions

- `Cslib.VASS`: a VASS, given by a set of rules.
- `Cslib.VASS.Config`: control state and counter values, ordered by equality of control states and
  the pointwise order of the counters.
- `Cslib.VASS.lts`: the transition system of configurations, labelled by the rules.

## Main statements

- `Cslib.VASS.instWSTS`: over finitely many control states and counters, the transition system of
  a VASS is a WSTS. Hence the generic results of `Cslib.WSTS` apply, e.g.
  `Cslib.WSTS.exists_backSeq_fixpoint` (termination of backward coverability) and
  `Cslib.WSTS.exists_run_iff`.
-/

@[expose] public section

namespace Cslib

/-- A vector addition system with states over control states `Q` and counters `ι`. A rule
`(q, δ, q')` moves from `q` to `q'` and adds `δ` to the counters. -/
structure VASS (Q : Type*) (ι : Type*) where
  /-- The rules of the system. -/
  rules : Set (Q × (ι → ℤ) × Q)

namespace VASS

variable {Q : Type*} {ι : Type*}

/-- A configuration: a control state together with the values of the counters. -/
@[ext]
structure Config (Q : Type*) (ι : Type*) where
  /-- The control state. -/
  ctrl : Q
  /-- The counter values. -/
  val : ι → ℕ

instance : Preorder (Config Q ι) where
  le c d := c.ctrl = d.ctrl ∧ c.val ≤ d.val
  le_refl _ := ⟨rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem Config.le_def {c d : Config Q ι} : c ≤ d ↔ c.ctrl = d.ctrl ∧ c.val ≤ d.val := Iff.rfl

/-- The transition system of a VASS: a rule `(q, δ, q')` takes `(q, v)` to `(q', v + δ)`, provided
that `v + δ` is non-negative. The labels are the rules. -/
def lts (V : VASS Q ι) : LTS (Config Q ι) (Q × (ι → ℤ) × Q) where
  Tr c r c' :=
    r ∈ V.rules ∧ c.ctrl = r.1 ∧ c'.ctrl = r.2.2 ∧ ∀ i, (c.val i : ℤ) + r.2.1 i = c'.val i

/-- Over finitely many control states and counters, configurations are well-quasi-ordered. -/
instance [Finite Q] [Finite ι] : WellQuasiOrderedLE (Config Q ι) where
  wqo f := by
    -- some control state occurs infinitely often
    obtain ⟨q, hinf⟩ : ∃ q, {n | (f n).ctrl = q}.Infinite := by
      by_contra hcon
      simp only [not_exists, Set.not_infinite] at hcon
      refine Set.infinite_univ (α := ℕ) ((Set.finite_iUnion hcon).subset fun n _ => ?_)
      exact Set.mem_iUnion.2 ⟨(f n).ctrl, rfl⟩
    obtain ⟨a, b, hab, hle⟩ := wellQuasiOrdered_le fun k => (f (Nat.nth _ k)).val
    refine ⟨Nat.nth _ a, Nat.nth _ b, Nat.nth_strictMono hinf hab, ?_, hle⟩
    exact (Nat.nth_mem_of_infinite hinf a).trans (Nat.nth_mem_of_infinite hinf b).symm

/-- A VASS is a well-structured transition system: adding to the counters of a configuration
(without changing its control state) preserves every step. -/
instance instWSTS [Finite Q] [Finite ι] (V : VASS Q ι) : WSTS V.lts where
  mono {c d c'} {r} hle := by
    rintro ⟨hr, hc, hc', hv⟩
    refine ⟨⟨c'.ctrl, fun i => c'.val i + (d.val i - c.val i)⟩, ⟨hr, ?_, hc', fun i => ?_⟩, ?_⟩
    · rw [← hle.1]; exact hc
    · have h1 := hv i
      have h2 : c.val i ≤ d.val i := hle.2 i
      simp only
      omega
    · exact ⟨rfl, fun i => Nat.le_add_right _ _⟩

end VASS

end Cslib
