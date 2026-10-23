/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Foundations.Data.OmegaSequence.Init

/-! # Stuttering equivalence of ω-sequences

Two ω-sequences are *stuttering equivalent* if they are equal after collapsing finite repetitions
of letters. This is the notion of equivalence for traces that temporal logics without a next-time
operator cannot distinguish; see `Cslib.Logics.Temporal.LTL.Stuttering`.

We define it by an alignment: two monotone surjections `p` and `q` of the positions that match the
letters of the two sequences. Surjectivity is what forbids stuttering forever on one side, so that
`a b b b ...` and `a a a ...` are not equivalent.

## Main definitions

- `ωSequence.StutterEq`: stuttering equivalence.

## Main statements

- `StutterEq.refl`, `StutterEq.symm`, `StutterEq.trans`: stuttering equivalence is an equivalence
  relation (`ωSequence.stutterSetoid`).
- `StutterEq.drop_aligned`: aligned suffixes of stuttering equivalent sequences are stuttering
  equivalent.
- `StutterEq.of_gapMap`: a criterion for stuttering equivalence by a monotone map `e` from the
  positions of `y` into those of `x`, skipping only letters that equal their successor. This is the
  form in which the partial-order reduction argument produces equivalences.
-/

@[expose] public section

namespace Cslib.ωSequence

variable {α : Type*}

/-- Stuttering equivalence: there are monotone surjections `p` and `q` of the positions such that
`x (p n) = y (q n)` for all `n`. The pairs `(p n, q n)` form a path through the grid of positions
that moves forwards in one or both coordinates and does not stay forever in one of the two. -/
def StutterEq (x y : ωSequence α) : Prop :=
  ∃ p q : ℕ → ℕ, Monotone p ∧ Monotone q ∧ Function.Surjective p ∧ Function.Surjective q ∧
    ∀ n, x (p n) = y (q n)

namespace StutterEq

/-- A monotone surjection of the natural numbers starts at `0`. -/
private theorem zero_of_surjective {p : ℕ → ℕ} (hm : Monotone p) (hs : Function.Surjective p) :
    p 0 = 0 := by
  obtain ⟨k, hk⟩ := hs 0
  have := hm (Nat.zero_le k)
  omega

/-- A monotone surjection of the natural numbers advances by at most one. -/
private theorem succ_le_of_surjective {p : ℕ → ℕ} (hm : Monotone p) (hs : Function.Surjective p)
    (n : ℕ) : p (n + 1) ≤ p n + 1 := by
  obtain ⟨k, hk⟩ := hs (p n + 1)
  by_cases hkn : k ≤ n
  · have := hm hkn
    omega
  · have := hm (show n + 1 ≤ k by omega)
    omega

/-- A monotone map that starts at `0`, advances by at most one and is unbounded is surjective. -/
private theorem surjective_of_step {p : ℕ → ℕ} (h0 : p 0 = 0)
    (hs : ∀ n, p (n + 1) ≤ p n + 1) (hu : ∀ N, ∃ n, N ≤ p n) : Function.Surjective p := by
  classical
  intro v
  have hspec := Nat.find_spec (hu v)
  refine ⟨Nat.find (hu v), ?_⟩
  rcases h : Nat.find (hu v) with _ | t
  · rw [h] at hspec
    omega
  · have hmin := Nat.find_min (hu v) (show t < Nat.find (hu v) by omega)
    rw [h] at hspec
    have := hs t
    omega

/-- Stuttering equivalence is reflexive. -/
@[refl] protected theorem refl (x : ωSequence α) : StutterEq x x :=
  ⟨id, id, monotone_id, monotone_id, Function.surjective_id, Function.surjective_id,
    fun _ => rfl⟩

/-- Stuttering equivalence is symmetric. -/
@[symm] protected theorem symm {x y : ωSequence α} (h : StutterEq x y) : StutterEq y x :=
  let ⟨p, q, hp, hq, hps, hqs, h⟩ := h
  ⟨q, p, hq, hp, hqs, hps, fun n => (h n).symm⟩

/-- Stuttering equivalent sequences start with the same letter. -/
theorem head_eq {x y : ωSequence α} (h : StutterEq x y) : x 0 = y 0 := by
  obtain ⟨p, q, hp, hq, hps, hqs, h⟩ := h
  have := h 0
  rwa [zero_of_surjective hp hps, zero_of_surjective hq hqs] at this

/-- Aligned suffixes of stuttering equivalent sequences are stuttering equivalent. -/
theorem drop_aligned {x y : ωSequence α} {p q : ℕ → ℕ} (hp : Monotone p) (hq : Monotone q)
    (hps : Function.Surjective p) (hqs : Function.Surjective q) (h : ∀ n, x (p n) = y (q n))
    (n : ℕ) : StutterEq (x.drop (p n)) (y.drop (q n)) := by
  have key {r : ℕ → ℕ} (hr : Monotone r) (hrs : Function.Surjective r) :
      Monotone (fun m => r (n + m) - r n) ∧ Function.Surjective (fun m => r (n + m) - r n) := by
    refine ⟨fun a b hab => Nat.sub_le_sub_right (hr (by omega)) _, fun v => ?_⟩
    obtain ⟨m, hm⟩ := hrs (r n + v)
    by_cases hnm : n ≤ m
    · exact ⟨m - n, by simp only [Nat.add_sub_cancel' hnm, hm]; omega⟩
    · have := hr (show m ≤ n by omega)
      exact ⟨0, by simp only [Nat.add_zero]; omega⟩
  obtain ⟨hp', hps'⟩ := key hp hps
  obtain ⟨hq', hqs'⟩ := key hq hqs
  refine ⟨_, _, hp', hq', hps', hqs', fun m => ?_⟩
  rw [get_drop, get_drop, Nat.add_sub_cancel' (hp (Nat.le_add_right n m)),
    Nat.add_sub_cancel' (hq (Nat.le_add_right n m))]
  exact h _

section Merge

variable (f g : ℕ → ℕ)

/-- One step of the path that merges two alignments: the pairs `(n, m)` with `f n = g m`. -/
private def mergeStep (z : ℕ × ℕ) : ℕ × ℕ :=
  if f (z.1 + 1) = f z.1 then (z.1 + 1, z.2)
  else if g (z.2 + 1) = g z.2 then (z.1, z.2 + 1)
  else (z.1 + 1, z.2 + 1)

private def mergePath (t : ℕ) : ℕ × ℕ := (mergeStep f g)^[t] (0, 0)

private theorem mergePath_succ (t : ℕ) :
    mergePath f g (t + 1) = mergeStep f g (mergePath f g t) :=
  Function.iterate_succ_apply' _ _ _

variable {f g}

private theorem mergePath_eq (hf : Monotone f) (hfs : Function.Surjective f) (hg : Monotone g)
    (hgs : Function.Surjective g) (t : ℕ) :
    f (mergePath f g t).1 = g (mergePath f g t).2 := by
  induction t with
  | zero => simp only [mergePath, Function.iterate_zero, id, zero_of_surjective hf hfs,
      zero_of_surjective hg hgs]
  | succ t ih =>
    rw [mergePath_succ]
    unfold mergeStep
    split_ifs with h1 h2
    · simpa only [h1] using ih
    · simpa only [h2] using ih
    · have h3 := succ_le_of_surjective hf hfs (mergePath f g t).1
      have h4 := succ_le_of_surjective hg hgs (mergePath f g t).2
      have h5 := hf (Nat.le_add_right (mergePath f g t).1 1)
      have h6 := hg (Nat.le_add_right (mergePath f g t).2 1)
      simp only
      omega

private theorem mergePath_succ_fst (t : ℕ) :
    (mergePath f g t).1 ≤ (mergePath f g (t + 1)).1 ∧
      (mergePath f g (t + 1)).1 ≤ (mergePath f g t).1 + 1 := by
  rw [mergePath_succ]
  unfold mergeStep
  split_ifs <;> simp only <;> omega

private theorem mergePath_succ_snd (t : ℕ) :
    (mergePath f g t).2 ≤ (mergePath f g (t + 1)).2 ∧
      (mergePath f g (t + 1)).2 ≤ (mergePath f g t).2 + 1 := by
  rw [mergePath_succ]
  unfold mergeStep
  split_ifs <;> simp only <;> omega

/-- The path advances in at least one coordinate at each step. -/
private theorem mergePath_sum (t : ℕ) : t ≤ (mergePath f g t).1 + (mergePath f g t).2 := by
  induction t with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    rw [mergePath_succ]
    unfold mergeStep
    split_ifs <;> simp only <;> omega

/-- If a path `(a t, b t)` advances in at least one coordinate at each step, and `f (a t) = g (b t)`
for monotone maps `f` and `g` with `g` unbounded, then `a` is unbounded. -/
private theorem unbounded_of_sum {f g a b : ℕ → ℕ} (hf : Monotone f) (hg : Monotone g)
    (hgu : ∀ N, ∃ m, N ≤ g m) (hsum : ∀ t, t ≤ a t + b t) (heq : ∀ t, f (a t) = g (b t)) :
    ∀ N, ∃ t, N ≤ a t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨N, hN⟩ := hcon
  obtain ⟨m, hm⟩ := hgu (f N + 1)
  have h1 := hf (hN (m + N)).le
  have h2 := hsum (m + N)
  have h3 := hN (m + N)
  have h4 := hg (show m ≤ b (m + N) by omega)
  have h5 := heq (m + N)
  omega

/-- Both coordinates of the merging path are unbounded. -/
private theorem mergePath_unbounded (hf : Monotone f) (hfs : Function.Surjective f)
    (hg : Monotone g) (hgs : Function.Surjective g) :
    (∀ N, ∃ t, N ≤ (mergePath f g t).1) ∧ ∀ N, ∃ t, N ≤ (mergePath f g t).2 :=
  ⟨unbounded_of_sum hf hg (fun N => let ⟨m, hm⟩ := hgs N; ⟨m, hm.ge⟩) mergePath_sum
      (mergePath_eq hf hfs hg hgs),
    unbounded_of_sum hg hf (fun N => let ⟨m, hm⟩ := hfs N; ⟨m, hm.ge⟩)
      (fun t => by rw [Nat.add_comm]; exact mergePath_sum t)
      (fun t => (mergePath_eq hf hfs hg hgs t).symm)⟩

/-- Two monotone surjections can be merged: there is a common time parameter along which both are
advanced, in such a way that they take the same value. -/
private theorem exists_merge (hf : Monotone f) (hfs : Function.Surjective f) (hg : Monotone g)
    (hgs : Function.Surjective g) :
    ∃ a b : ℕ → ℕ, Monotone a ∧ Monotone b ∧ Function.Surjective a ∧ Function.Surjective b ∧
      ∀ t, f (a t) = g (b t) := by
  obtain ⟨h1, h2⟩ := mergePath_unbounded hf hfs hg hgs
  refine ⟨fun t => (mergePath f g t).1, fun t => (mergePath f g t).2,
    monotone_nat_of_le_succ fun t => (mergePath_succ_fst t).1,
    monotone_nat_of_le_succ fun t => (mergePath_succ_snd t).1,
    surjective_of_step rfl (fun t => (mergePath_succ_fst t).2) h1,
    surjective_of_step rfl (fun t => (mergePath_succ_snd t).2) h2,
    mergePath_eq hf hfs hg hgs⟩

end Merge

/-- Stuttering equivalence is transitive. -/
@[trans] protected theorem trans {x y z : ωSequence α} (h₁ : StutterEq x y)
    (h₂ : StutterEq y z) : StutterEq x z := by
  obtain ⟨p, q, hp, hq, hps, hqs, h⟩ := h₁
  obtain ⟨p', q', hp', hq', hps', hqs', h'⟩ := h₂
  obtain ⟨a, b, ha, hb, has, hbs, hab⟩ := exists_merge hq hqs hp' hps'
  refine ⟨p ∘ a, q' ∘ b, hp.comp ha, hq'.comp hb, hps.comp has, hqs'.comp hbs, fun t => ?_⟩
  exact (h (a t)).trans ((congrArg y (hab t)).trans (h' (b t)))

section GapMap

variable (e : ℕ → ℕ)

/-- One step of the path through the grid of pairs `(j, n)` of a position `j` of `x` and a
position `n` of `y`, for a map `e` from the positions of `y` to those of `x`. The position of `x`
advances up to `e n`, and then both advance. -/
private def gapStep (z : ℕ × ℕ) : ℕ × ℕ :=
  if z.1 < e z.2 then (z.1 + 1, z.2)
  else if e z.2 < e (z.2 + 1) then (z.1 + 1, z.2 + 1)
  else (z.1, z.2 + 1)

private def gapPath (t : ℕ) : ℕ × ℕ := (gapStep e)^[t] (0, 0)

private theorem gapPath_succ (t : ℕ) : gapPath e (t + 1) = gapStep e (gapPath e t) :=
  Function.iterate_succ_apply' _ _ _

/-- The pairs on the path: `j` is at most `e n`, and it is `e n` or it lies strictly after
`e (n - 1)`. -/
private def GapInv (z : ℕ × ℕ) : Prop :=
  z.1 ≤ e z.2 ∧ (z.1 = e z.2 ∨ ∃ n, z.2 = n + 1 ∧ e n < z.1)

variable {e}

private theorem gapPath_inv (hm : Monotone e) (h0 : e 0 = 0) (t : ℕ) :
    GapInv e (gapPath e t) := by
  induction t with
  | zero => simp only [gapPath, Function.iterate_zero, id, GapInv, h0, le_refl, true_or, and_self]
  | succ t ih =>
    rw [gapPath_succ]
    rcases hz : gapPath e t with ⟨j, n⟩
    rw [hz] at ih
    obtain ⟨hle, hcase⟩ := ih
    simp only at hle hcase
    have hmn := hm (Nat.le_add_right n 1)
    unfold gapStep GapInv
    dsimp only
    split_ifs with h1 h2
    · refine ⟨by simp only; omega, Or.inr ?_⟩
      obtain h | ⟨n', hn', hlt⟩ := hcase
      · omega
      · exact ⟨n', hn', by simp only; omega⟩
    · exact ⟨by simp only; omega, Or.inr ⟨n, rfl, by simp only; omega⟩⟩
    · exact ⟨by simp only; omega, Or.inl (by simp only; omega)⟩

private theorem gapPath_succ_fst (t : ℕ) :
    (gapPath e t).1 ≤ (gapPath e (t + 1)).1 ∧ (gapPath e (t + 1)).1 ≤ (gapPath e t).1 + 1 := by
  rw [gapPath_succ]
  unfold gapStep
  split_ifs <;> simp only <;> omega

private theorem gapPath_succ_snd (t : ℕ) :
    (gapPath e t).2 ≤ (gapPath e (t + 1)).2 ∧ (gapPath e (t + 1)).2 ≤ (gapPath e t).2 + 1 := by
  rw [gapPath_succ]
  unfold gapStep
  split_ifs <;> simp only <;> omega

private theorem gapPath_sum (t : ℕ) : t ≤ (gapPath e t).1 + (gapPath e t).2 := by
  induction t with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    rw [gapPath_succ]
    unfold gapStep
    split_ifs <;> simp only <;> omega

/-- The second coordinate of the path is unbounded. -/
private theorem gapPath_snd_unbounded (hm : Monotone e) (h0 : e 0 = 0) :
    ∀ N, ∃ t, N ≤ (gapPath e t).2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨B, hB⟩ := hcon
  have h1 := hm (hB (e B + B)).le
  have h2 := gapPath_sum (e := e) (e B + B)
  have h3 := (gapPath_inv hm h0 (e B + B)).1
  have h4 := hB (e B + B)
  omega

/-- The first coordinate of the path is unbounded, if `e` is. -/
private theorem gapPath_fst_unbounded (hm : Monotone e) (h0 : e 0 = 0)
    (hu : ∀ N, ∃ n, N ≤ e n) : ∀ N, ∃ t, N ≤ (gapPath e t).1 := by
  intro N
  obtain ⟨n, hn⟩ := hu N
  obtain ⟨t, ht⟩ := gapPath_snd_unbounded hm h0 (n + 1)
  refine ⟨t, ?_⟩
  obtain ⟨-, h | ⟨n', hn', hlt⟩⟩ := gapPath_inv hm h0 t
  · have := hm (show n ≤ (gapPath e t).2 by omega)
    omega
  · have := hm (show n ≤ n' by omega)
    omega

/-- Stuttering equivalence from a monotone map `e` from the positions of `y` to those of `x`: it
starts at `0`, is unbounded, `y n = x (e n)`, and the positions of `x` that `e` skips hold the
same letter as the next position that `e` hits. Then `y` is `x` with some repetitions removed and
others added. -/
theorem of_gapMap {x y : ωSequence α} {e : ℕ → ℕ} (hm : Monotone e) (h0 : e 0 = 0)
    (hu : ∀ N, ∃ n, N ≤ e n) (hy : ∀ n, y n = x (e n))
    (hgap : ∀ n j, e n < j → j < e (n + 1) → x j = x (e (n + 1))) : StutterEq x y := by
  have hfst : ∀ t, x (gapPath e t).1 = y (gapPath e t).2 := by
    intro t
    obtain ⟨hle, hcase⟩ := gapPath_inv hm h0 t
    rcases hz : gapPath e t with ⟨j, n⟩
    rw [hz] at hle hcase
    simp only at hle hcase ⊢
    obtain h | ⟨n', hn', hlt⟩ := hcase
    · rw [hy, h]
    · subst hn'
      by_cases hj : j = e (n' + 1)
      · rw [hy, hj]
      · rw [hy, hgap n' j hlt (by omega)]
  exact ⟨fun t => (gapPath e t).1, fun t => (gapPath e t).2,
    monotone_nat_of_le_succ fun t => (gapPath_succ_fst t).1,
    monotone_nat_of_le_succ fun t => (gapPath_succ_snd t).1,
    surjective_of_step (by simp only [gapPath, Function.iterate_zero, id])
      (fun t => (gapPath_succ_fst t).2) (gapPath_fst_unbounded hm h0 hu),
    surjective_of_step (by simp only [gapPath, Function.iterate_zero, id])
      (fun t => (gapPath_succ_snd t).2) (gapPath_snd_unbounded hm h0), hfst⟩

end GapMap

/-- Repeating the first letter gives a stuttering equivalent sequence. -/
theorem cons_head_stutterEq (x : ωSequence α) : StutterEq x (x 0 ::ω x) := by
  refine ⟨fun n => n - 1, id, fun a b hab => Nat.sub_le_sub_right hab 1, monotone_id, ?_,
    Function.surjective_id, fun n => ?_⟩
  · exact fun v => ⟨v + 1, by simp only [Nat.add_sub_cancel]⟩
  · cases n with
    | zero => rfl
    | succ n => simp only [id, Nat.add_sub_cancel, get_succ_cons]

end StutterEq

/-- Stuttering equivalence as a setoid on ω-sequences. -/
def stutterSetoid (α : Type*) : Setoid (ωSequence α) :=
  ⟨StutterEq, ⟨StutterEq.refl, StutterEq.symm, StutterEq.trans⟩⟩

end Cslib.ωSequence
