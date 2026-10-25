/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Semantics
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Abel

/-! # The state equation

Firing a transition `t` at `M` leads to `M'` with `M' + pre t = M + post t`. Hence the marking `M'`
reached by a firing sequence `ts` satisfies `M' + Σ pre = M + Σ post`, the sums ranging over the
fired transitions. Viewing markings as integer vectors, this says that `M'` is `M` plus the sum
of the *incidences* `post t - pre t` of the fired transitions. This gives a necessary (but not
sufficient) condition for reachability.

The multiset form needs no decidable equality on places; the integer form does, to count tokens.

A *firing count vector* records how often each transition fires; it is a multiset of transitions.
The firing count vector (Parikh vector) of a firing sequence `ts` is `(ts : Multiset Transition)`.

## Main definitions

- `PetriNet.Marking.toInt`: view a marking as an integer vector.
- `PetriNet.incidence`: the effect `post t - pre t` of a transition.
- `PetriNet.effect`: the total effect of a firing sequence.

## Main statements

- `PetriNet.mTr_add_sum_pre`: the state equation for firing sequences, on multisets.
- `PetriNet.Reachable.exists_add_sum_pre`: the state equation has a solution, a firing count
  vector, at every reachable marking.
- `PetriNet.mTr_toInt`: the state equation for firing sequences, on integer vectors.
- `PetriNet.Reachable.exists_toInt_eq`: the state equation for reachable markings.
- `PetriNet.mTr_eq_iff_effect_eq_zero`: a firing sequence returns to its start iff its effect is
  zero.
- `PetriNet.mTr_replicate`: a cyclic firing sequence can be repeated.

## References

* [T. Murata, *Petri nets: Properties, analysis and applications*][Murata1989]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*} {N : PetriNet Place Transition}

/-- Firing `t` adds the postset and removes the preset. -/
theorem Fires.add_pre {M M' : Marking Place} {t : Transition} (h : M [t⟩[N] M') :
    M' + •[N] t = M + t •[N] := by
  obtain ⟨R, rfl, rfl⟩ := h
  abel

/-- The state equation on multisets: a firing sequence adds the postsets and removes the presets of
the fired transitions. -/
theorem mTr_add_sum_pre {M M' : Marking Place} {ts : List Transition} (h : N.lts.MTr M ts M') :
    M' + (ts.map N.pre).sum = M + (ts.map N.post).sum := by
  induction h with
  | refl => simp
  | @stepL M t M₁ ts M' htr _ ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, add_left_comm, ih,
      add_left_comm, ← add_assoc, htr.add_pre, add_assoc]

/-- A firing sequence returns to its starting marking exactly when the fired transitions consume
as many tokens as they produce, in every place. -/
theorem mTr_eq_iff_sum_pre_eq {M M' : Marking Place} {ts : List Transition}
    (h : N.lts.MTr M ts M') : M' = M ↔ (ts.map N.pre).sum = (ts.map N.post).sum := by
  have heq := mTr_add_sum_pre h
  constructor
  · rintro rfl
    exact add_left_cancel heq
  · intro h0
    rw [h0] at heq
    exact add_right_cancel heq

/-- The state equation for reachable markings, on multisets: if `M'` is reachable from `M`, some
firing count vector `σ` (the firing count vector of a firing sequence) satisfies
`M' + Σ pre = M + Σ post`. -/
theorem Reachable.exists_add_sum_pre {M M' : Marking Place} (h : M ⇝[N] M') :
    ∃ σ : Multiset Transition, M' + (σ.map N.pre).sum = M + (σ.map N.post).sum :=
  let ⟨ts, hts⟩ := h
  ⟨ts, mTr_add_sum_pre hts⟩

/-- A larger firing count vector consumes (or produces) more tokens. -/
theorem sum_map_le_of_le {σ τ : Multiset Transition} (h : σ ≤ τ) (f : Transition → Marking Place) :
    (σ.map f).sum ≤ (τ.map f).sum := by
  obtain ⟨ρ, rfl⟩ := exists_add_of_le h
  rw [Multiset.map_add, Multiset.sum_add]
  exact le_self_add

section Count

variable [DecidableEq Place] [DecidableEq Transition] {f : Transition → Marking Place}
  {u v : Transition} {p : Place}

/-- If every occurrence of `u` puts a token in `p`, then `σ` puts at least `σ.count u` tokens in
`p`. -/
theorem count_le_count_sum_map (hu : p ∈ f u) (σ : Multiset Transition) :
    σ.count u ≤ ((σ.map f).sum).count p := by
  have := Multiset.count_le_of_le p
    (sum_map_le_of_le (Multiset.le_count_iff_replicate_le.1 (le_refl (σ.count u))) f)
  rw [Multiset.map_replicate, Multiset.sum_replicate, Multiset.count_nsmul] at this
  exact (Nat.le_mul_of_pos_right _ (Multiset.count_pos.2 hu)).trans this

/-- Two distinct transitions that both put a token in `p` contribute their counts separately. -/
theorem count_add_count_le_count_sum_map (hu : p ∈ f u) (hv : p ∈ f v) (huv : u ≠ v)
    (σ : Multiset Transition) : σ.count u + σ.count v ≤ ((σ.map f).sum).count p := by
  have hle : Multiset.replicate (σ.count u) u + Multiset.replicate (σ.count v) v ≤ σ :=
    Multiset.le_iff_count.2 fun x => by
      simp only [Multiset.count_add, Multiset.count_replicate]
      split_ifs <;> subst_vars <;> simp_all
  have := Multiset.count_le_of_le p (sum_map_le_of_le hle f)
  simp only [Multiset.map_add, Multiset.map_replicate, Multiset.sum_add, Multiset.sum_replicate,
    Multiset.count_add, Multiset.count_nsmul] at this
  have h₁ := Nat.le_mul_of_pos_right (σ.count u) (Multiset.count_pos.2 hu)
  have h₂ := Nat.le_mul_of_pos_right (σ.count v) (Multiset.count_pos.2 hv)
  omega

end Count

section Int

variable [DecidableEq Place]

/-- View a marking as an integer vector. -/
def Marking.toInt : Marking Place →+ (Place → ℤ) :=
  AddMonoidHom.pi fun p => (Nat.castAddMonoidHom ℤ).comp (Multiset.countAddMonoidHom p)

@[simp] theorem Marking.toInt_apply (M : Marking Place) (p : Place) :
    Marking.toInt M p = M.count p :=
  rfl

theorem Marking.toInt_injective : Function.Injective (Marking.toInt (Place := Place)) :=
  fun _ _ h => Multiset.ext.2 fun p => by simpa using congrFun h p

variable (N) in
/-- The effect of firing `t`: tokens produced minus tokens consumed. -/
def incidence (t : Transition) : Place → ℤ :=
  Marking.toInt (t •[N]) - Marking.toInt (•[N] t)

variable (N) in
/-- The total effect of a firing sequence. -/
def effect (ts : List Transition) : Place → ℤ :=
  (ts.map N.incidence).sum

@[simp] theorem effect_nil : N.effect [] = 0 := rfl

@[simp] theorem effect_cons (t : Transition) (ts : List Transition) :
    N.effect (t :: ts) = N.incidence t + N.effect ts := by
  simp [effect]

theorem effect_append (ts₁ ts₂ : List Transition) :
    N.effect (ts₁ ++ ts₂) = N.effect ts₁ + N.effect ts₂ := by
  simp [effect]

theorem Fires.toInt {M M' : Marking Place} {t : Transition} (h : M [t⟩[N] M') :
    Marking.toInt M' = Marking.toInt M + N.incidence t := by
  obtain ⟨R, rfl, rfl⟩ := h
  simp only [incidence, map_add]
  abel

/-- The state equation: a firing sequence changes the marking by its total effect. -/
theorem mTr_toInt {M M' : Marking Place} {ts : List Transition} (h : N.lts.MTr M ts M') :
    Marking.toInt M' = Marking.toInt M + N.effect ts := by
  induction h with
  | refl => simp
  | stepL htr _ ih => rw [ih, htr.toInt, effect_cons]; abel

/-- Every reachable marking satisfies the state equation for some firing sequence. -/
theorem Reachable.exists_toInt_eq {M M' : Marking Place} (h : M ⇝[N] M') :
    ∃ ts, Marking.toInt M' = Marking.toInt M + N.effect ts :=
  let ⟨ts, hts⟩ := h
  ⟨ts, mTr_toInt hts⟩

/-- A firing sequence returns to its starting marking exactly when its total effect is zero.
Such a sequence is called a *T-invariant*. -/
theorem mTr_eq_iff_effect_eq_zero {M M' : Marking Place} {ts : List Transition}
    (h : N.lts.MTr M ts M') : M' = M ↔ N.effect ts = 0 := by
  have heq := mTr_toInt h
  constructor
  · rintro rfl
    simpa using heq
  · intro h0
    exact Marking.toInt_injective (by rw [heq, h0, add_zero])

end Int

/-- A cyclic firing sequence can be repeated any number of times. -/
theorem mTr_replicate {M : Marking Place} {ts : List Transition} (h : N.lts.MTr M ts M) (n : ℕ) :
    N.lts.MTr M (List.replicate n ts).flatten M := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons]
    exact LTS.MTr.comp _ h ih

end PetriNet

end Cslib
