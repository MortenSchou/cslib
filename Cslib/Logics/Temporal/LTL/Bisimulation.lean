/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Logics.Temporal.LTL.Model
public import Cslib.Logics.Temporal.CTL.Bisimulation

/-! # Bisimulation invariance of LTL

States related by a bisimulation of labelled transition systems satisfy the same LTL formulas on
their maximal paths: a path from one state lifts to a path from the other with the same trace, if
related states satisfy the same atoms. This uses the bisimulations of
`Cslib.Foundations.Semantics.LTS.Bisimulation`.
-/

@[expose] public section

namespace Cslib.Logic.LTL

open Cslib
open scoped InferenceSystem Formula Cslib.Logic CTL

variable {S₁ S₂ : Type*} {Label : Type*} {Atom : Type*} {lts₁ : LTS S₁ Label}
  {lts₂ : LTS S₂ Label} {v₁ : S₁ → Atom → Prop} {v₂ : S₂ → Atom → Prop} {r : S₁ → S₂ → Prop}

/-- Some maximal path from related states satisfies the same formulas. -/
theorem somePath_iff_of_isBisimulation (hr : LTS.IsBisimulation lts₁ lts₂ r)
    (hv : CTL.RespectsAtoms r v₁ v₂) {s t} (hst : r s t) (φ : Formula Atom) :
    ⇓LTL[⟨lts₁, v₁⟩,s ⊨∃ φ] ↔ ⇓LTL[⟨lts₂, v₂⟩,t ⊨∃ φ] := by
  have trace_eq : ∀ (hv : CTL.RespectsAtoms r v₁ v₂) {f : ℕ → S₁} {g : ℕ → S₂},
      (∀ n, r (f n) (g n)) →
        CTL.Model.trace ⟨lts₁, v₁⟩ f = CTL.Model.trace ⟨lts₂, v₂⟩ g :=
    fun hv f g hZ => DFunLike.ext _ _ fun n => Set.ext fun p => hv _ _ (hZ n) p
  constructor
  · rintro ⟨f, hf, h0, hsat⟩
    obtain ⟨g, hg, hg0, hZg⟩ := CTL.lift_path (v₂ := v₂) hr hf (t := t) (by rw [h0]; exact hst)
    exact ⟨g, hg, hg0, trace_eq hv hZg ▸ hsat⟩
  · rintro ⟨g, hg, hg0, hsat⟩
    obtain ⟨f, hf, hf0, hZf⟩ :=
      CTL.lift_path (v₂ := v₁) hr.inv hg (t := s) (by rw [hg0]; exact hst)
    exact ⟨f, hf, hf0, (trace_eq hv hZf).symm ▸ hsat⟩

/-- All maximal paths from related states satisfy the same formulas. -/
theorem allPaths_iff_of_isBisimulation (hr : LTS.IsBisimulation lts₁ lts₂ r)
    (hv : CTL.RespectsAtoms r v₁ v₂) {s t} (hst : r s t) (φ : Formula Atom) :
    ⇓LTL[⟨lts₁, v₁⟩,s ⊨∀ φ] ↔ ⇓LTL[⟨lts₂, v₂⟩,t ⊨∀ φ] := by
  rw [allPaths_iff_not_somePath, allPaths_iff_not_somePath,
    somePath_iff_of_isBisimulation hr hv hst]

open LTS in
/-- Bisimilar states of LTSs satisfy the same LTL formulas on all their maximal paths, if the atoms
hold in bisimilar states alike. -/
theorem allPaths_iff_of_bisimilar
    (hv : CTL.RespectsAtoms (Bisimilarity lts₁ lts₂) v₁ v₂)
    {s : S₁} {t : S₂} (hst : Bisimilarity lts₁ lts₂ s t) (φ : Formula Atom) :
    ⇓LTL[⟨lts₁, v₁⟩,s ⊨∀ φ] ↔ ⇓LTL[⟨lts₂, v₂⟩,t ⊨∀ φ] :=
  allPaths_iff_of_isBisimulation (Bisimilarity.isBisimulation lts₁ lts₂) hv hst φ

end Cslib.Logic.LTL
