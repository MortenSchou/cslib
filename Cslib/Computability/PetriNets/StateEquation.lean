/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Semantics
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic.Abel

/-! # The state equation

Firing a transition `t` changes a marking by the integer vector `post t - pre t`, its
*incidence*. Hence the marking reached by a firing sequence is the initial marking plus the sum of
the incidences of the fired transitions. This gives a necessary (but not sufficient) condition for
reachability.

## Main definitions

- `PetriNet.Marking.toInt`: view a marking as an integer vector.
- `PetriNet.incidence`: the effect `post t - pre t` of a transition.
- `PetriNet.effect`: the total effect of a firing sequence.
- `PetriNet.parikh`: the firing count vector (Parikh vector) of a firing sequence.
- `PetriNet.vectorEffect`: the effect `C σ` of a firing count vector `σ : Transition →₀ ℕ`.
- `PetriNet.produced`, `PetriNet.consumed`: the tokens a firing count vector puts into, and takes
  from, each place; `vectorEffect σ = produced σ - consumed σ`.

## Main statements

- `PetriNet.mTr_toInt`: the state equation for firing sequences.
- `PetriNet.Reachable.exists_toInt_eq`: the state equation for reachable markings.
- `PetriNet.Reachable.exists_vectorEffect`: the state equation has a nonnegative solution at
  every reachable marking.
- `PetriNet.mTr_eq_iff_effect_eq_zero`: a firing sequence returns to its start iff its effect is
  zero.
- `PetriNet.mTr_replicate`: a cyclic firing sequence can be repeated.

## References

* [T. Murata, *Petri nets: Properties, analysis and applications*][Murata1989]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*}

/-- View a marking as an integer vector. -/
noncomputable def Marking.toInt : Marking Place →+ (Place →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

@[simp] theorem Marking.toInt_apply (M : Marking Place) (p : Place) :
    Marking.toInt M p = (M p : ℤ) := by
  simp [Marking.toInt]

variable (N : PetriNet Place Transition)

/-- The effect of firing `t`: tokens produced minus tokens consumed. -/
noncomputable def incidence (t : Transition) : Place →₀ ℤ :=
  Marking.toInt (t •[N]) - Marking.toInt (•[N] t)

/-- The total effect of a firing sequence. -/
noncomputable def effect (ts : List Transition) : Place →₀ ℤ :=
  (ts.map N.incidence).sum

/-- The firing count vector (Parikh vector) of a firing sequence. -/
noncomputable def parikh (ts : List Transition) : Transition →₀ ℕ :=
  (ts.map fun t => Finsupp.single t 1).sum

/-- The effect `C σ` of a firing count vector: each transition `t` contributes `σ t` times its
incidence. -/
noncomputable def vectorEffect (σ : Transition →₀ ℕ) : Place →₀ ℤ :=
  Finsupp.linearCombination ℕ N.incidence σ

/-- The tokens that a firing count vector `σ` puts into each place. -/
noncomputable def produced (σ : Transition →₀ ℕ) : Place →₀ ℕ :=
  Finsupp.linearCombination ℕ N.post σ

/-- The tokens that a firing count vector `σ` takes from each place. -/
noncomputable def consumed (σ : Transition →₀ ℕ) : Place →₀ ℕ :=
  Finsupp.linearCombination ℕ N.pre σ

variable {N}

@[simp] theorem parikh_nil : parikh ([] : List Transition) = 0 := rfl

@[simp] theorem parikh_cons (t : Transition) (ts : List Transition) :
    parikh (t :: ts) = Finsupp.single t 1 + parikh ts := by
  simp [parikh]

@[simp] theorem parikh_apply [DecidableEq Transition] (ts : List Transition) (t : Transition) :
    parikh ts t = ts.count t := by
  induction ts with
  | nil => simp
  | cons u ts ih => by_cases h : u = t <;> simp [ih, h, add_comm]

theorem parikh_pos_iff {ts : List Transition} {t : Transition} : 0 < parikh ts t ↔ t ∈ ts := by
  classical
  simp [List.count_pos_iff]

theorem parikh_append (ts₁ ts₂ : List Transition) :
    parikh (ts₁ ++ ts₂) = parikh ts₁ + parikh ts₂ := by
  simp [parikh]

/-- Removing one occurrence of a transition lowers the total count by one. -/
theorem degree_tsub_single_add_one {σ : Transition →₀ ℕ} {t : Transition} (h : σ t ≠ 0) :
    (σ - Finsupp.single t 1).degree + 1 = σ.degree := by
  have := congrArg Finsupp.degree (Finsupp.sub_add_single_one_cancel h)
  simpa using this

@[simp] theorem vectorEffect_zero : N.vectorEffect 0 = 0 := by simp [vectorEffect]

theorem vectorEffect_add (σ τ : Transition →₀ ℕ) :
    N.vectorEffect (σ + τ) = N.vectorEffect σ + N.vectorEffect τ := by
  simp [vectorEffect]

@[simp] theorem vectorEffect_single (t : Transition) (n : ℕ) :
    N.vectorEffect (Finsupp.single t n) = n • N.incidence t := by
  simp [vectorEffect]

theorem produced_apply (σ : Transition →₀ ℕ) (p : Place) :
    N.produced σ p = σ.sum fun t n => n * (t •[N]) p := by
  simp [produced, Finsupp.linearCombination_apply, Finsupp.sum_apply]

theorem consumed_apply (σ : Transition →₀ ℕ) (p : Place) :
    N.consumed σ p = σ.sum fun t n => n * (•[N] t) p := by
  simp [consumed, Finsupp.linearCombination_apply, Finsupp.sum_apply]

theorem produced_add (σ τ : Transition →₀ ℕ) : N.produced (σ + τ) = N.produced σ + N.produced τ :=
  map_add ..

theorem consumed_add (σ τ : Transition →₀ ℕ) : N.consumed (σ + τ) = N.consumed σ + N.consumed τ :=
  map_add ..

/-- A single transition's contribution to the tokens produced is at most the total. -/
theorem mul_post_le_produced (σ : Transition →₀ ℕ) (t : Transition) (p : Place) :
    σ t * (t •[N]) p ≤ N.produced σ p := by
  rw [produced_apply]
  simpa using Finsupp.single_le_sum σ (g := fun t n => n * (t •[N]) p) (fun _ _ => Nat.zero_le _) t

theorem mul_pre_le_consumed (σ : Transition →₀ ℕ) (t : Transition) (p : Place) :
    σ t * (•[N] t) p ≤ N.consumed σ p := by
  rw [consumed_apply]
  simpa using Finsupp.single_le_sum σ (g := fun t n => n * (•[N] t) p) (fun _ _ => Nat.zero_le _) t

theorem vectorEffect_apply (σ : Transition →₀ ℕ) (p : Place) :
    N.vectorEffect σ p = σ.sum fun t n => (n : ℤ) * ((t •[N]) p - (•[N] t) p) := by
  simp [vectorEffect, Finsupp.linearCombination_apply, Finsupp.sum_apply, incidence]

theorem vectorEffect_apply_eq_sub (σ : Transition →₀ ℕ) (p : Place) :
    N.vectorEffect σ p = N.produced σ p - N.consumed σ p := by
  simp [vectorEffect_apply, produced_apply, consumed_apply, Finsupp.sum, mul_sub,
    Finset.sum_sub_distrib]

/-- The state equation without subtraction: `M = M₀ + C σ` iff `M + consumed σ = M₀ + produced σ`
at every place. -/
theorem toInt_eq_add_vectorEffect_iff {M₀ M : Marking Place} {σ : Transition →₀ ℕ} :
    Marking.toInt M = Marking.toInt M₀ + N.vectorEffect σ ↔
      ∀ p, M p + N.consumed σ p = M₀ p + N.produced σ p := by
  rw [Finsupp.ext_iff]
  refine forall_congr' fun p => ?_
  simp only [Finsupp.add_apply, Marking.toInt_apply, vectorEffect_apply_eq_sub]
  omega

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

/-- The effect of a firing sequence is the effect of its firing count vector. -/
theorem effect_eq_vectorEffect (ts : List Transition) :
    N.effect ts = N.vectorEffect (parikh ts) := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih, vectorEffect_add]

/-- Every reachable marking satisfies the state equation for some firing sequence. -/
theorem Reachable.exists_toInt_eq {M M' : Marking Place} (h : M ⇝[N] M') :
    ∃ ts, Marking.toInt M' = Marking.toInt M + N.effect ts :=
  let ⟨ts, hts⟩ := h
  ⟨ts, mTr_toInt hts⟩

/-- The state equation with a nonnegative solution: every reachable marking is the initial
marking plus the effect of the firing count vector of some firing sequence. -/
theorem Reachable.exists_vectorEffect {M M' : Marking Place} (h : M ⇝[N] M') :
    ∃ σ : Transition →₀ ℕ, Marking.toInt M' = Marking.toInt M + N.vectorEffect σ :=
  let ⟨ts, hts⟩ := h.exists_toInt_eq
  ⟨parikh ts, by rwa [← effect_eq_vectorEffect]⟩

theorem Marking.toInt_injective : Function.Injective (Marking.toInt (Place := Place)) :=
  fun _ _ h => Finsupp.mapRange_injective (Nat.cast : ℕ → ℤ) (by simp) Nat.cast_injective h

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
