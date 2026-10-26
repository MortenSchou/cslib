/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.WSTS.Decidability
public import Cslib.Computability.WSTS.Examples.VASS
public import Mathlib.Data.Fintype.Pi

/-! # Decidable coverability for vector addition systems with states

The abstract decidability theorem `Cslib.WSTS.decidableCoverable` needs an effective pred-basis.
For a VASS with finitely many rules this is the classical one: the minimal configurations that
reach `↑b` by a rule `(q, δ, q')` have control state `q` and counters `max 0 (b - δ)`.

## Main definitions

- `Cslib.VASS.predBasis`: the pred-basis of a VASS given by a finite list of rules.
- `Cslib.VASS.decidableCoverable`: coverability in a VASS with finitely many control states,
  counters, and rules is decidable.

## Main statements

- `Cslib.VASS.isPredBasis`: `predBasis` is a correct pred-basis.
-/

@[expose] public section

namespace Cslib

namespace VASS

variable {Q : Type*} {ι : Type*}

instance [DecidableEq Q] [Fintype ι] : DecidableEq (Config Q ι) := fun c d =>
  decidable_of_iff (c.ctrl = d.ctrl ∧ c.val = d.val) (by
    cases c; cases d; simp only [Config.mk.injEq])

instance [DecidableEq Q] [Fintype ι] : DecidableRel (α := Config Q ι) (· ≤ ·) :=
  fun c d => inferInstanceAs (Decidable (c.ctrl = d.ctrl ∧ c.val ≤ d.val))

variable [DecidableEq Q] [Fintype ι]

/-- The predecessor basis of the upward closure of `B` for a finite set of rules `R`: for each rule
`(q, δ, q')` and each `b ∈ B` with control state `q'`, the configuration `(q, max 0 (b - δ))`. -/
def predBasis (R : Finset (Q × (ι → ℤ) × Q)) (B : Finset (Config Q ι)) : Finset (Config Q ι) :=
  ((R ×ˢ B).filter fun p => p.2.ctrl = p.1.2.2).image fun p =>
    ⟨p.1.1, fun i => ((p.2.val i : ℤ) - p.1.2.1 i).toNat⟩

/-- `predBasis` is an effective pred-basis for a VASS whose rules are `R`. -/
theorem isPredBasis (V : VASS Q ι) (R : Finset (Q × (ι → ℤ) × Q)) (hR : (R : Set _) = V.rules) :
    WSTS.IsPredBasis V.lts (predBasis R) := by
  intro B
  ext s
  constructor
  · rintro ⟨p, hp, hps⟩
    simp only [predBasis, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨r, b⟩, ⟨⟨hrR, hbB⟩, hbr⟩, rfl⟩ := hp
    obtain ⟨hctrl, hval⟩ := hps
    refine ⟨r, ⟨r.2.2, fun i => ((s.val i : ℤ) + r.2.1 i).toNat⟩,
      ⟨?_, hctrl.symm, rfl, fun i => ?_⟩, b, hbB, ?_, fun i => ?_⟩
    · exact hR ▸ hrR
    · have h : (((b.val i : ℤ) - r.2.1 i).toNat : ℤ) ≤ s.val i := by exact_mod_cast hval i
      simp only
      omega
    · exact hbr
    · have h : (((b.val i : ℤ) - r.2.1 i).toNat : ℤ) ≤ s.val i := by exact_mod_cast hval i
      simp only
      omega
  · rintro ⟨r, s', ⟨hr, hc, hc', hv⟩, b, hbB, hbs', hbv⟩
    refine ⟨⟨r.1, fun i => ((b.val i : ℤ) - r.2.1 i).toNat⟩, ?_, hc.symm, fun i => ?_⟩
    · simp only [predBasis, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
      exact ⟨(r, b), ⟨⟨(hR ▸ hr : r ∈ (R : Set _)), hbB⟩, hbs'.trans hc'⟩, rfl⟩
    · have h1 := hv i
      have h2 : b.val i ≤ s'.val i := hbv i
      simp only
      omega

/-- Coverability in a VASS with finitely many control states, counters, and rules is decidable. -/
def decidableCoverable [Finite Q] [Finite ι] (V : VASS Q ι) (R : Finset (Q × (ι → ℤ) × Q))
    (hR : (R : Set _) = V.rules) (s t : Config Q ι) : Decidable (WSTS.Coverable V.lts s t) :=
  WSTS.decidableCoverable (isPredBasis V R hR) s t

end VASS

end Cslib
