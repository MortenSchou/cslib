/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.Automata.NA.Basic

/-! # Generalised Büchi acceptance

A run of a nondeterministic automaton is accepting in the *generalised* Büchi sense if it visits
each of finitely many sets of states infinitely often. A nondeterministic Büchi automaton, with one
accepting set, recognises the same ω-language: it keeps a counter that advances when the run visits
the set the counter points to, and accepts when the counter has gone through all the sets.

## Main definitions

- `NA.degeneralize`: the Büchi automaton with the counter.

## Main statements

- `NA.degeneralize_accepts_iff`: it accepts the sequences with a run visiting each set infinitely
  often.
-/

@[expose] public section

open Filter

namespace Cslib.Automata.NA

variable {Q Symbol : Type*}

/-- The counter of `degeneralize` after a run visits state `q` with counter `c`: it advances if
`q` is in the set `F c`, and starts over from `0` once it reached `k`. -/
noncomputable def degenNext (F : ℕ → Set Q) (k : ℕ) (q : Q) (c : Fin (k + 1)) : Fin (k + 1) :=
  open scoped Classical in
  if h : c.val < k then (if q ∈ F c.val then ⟨c.val + 1, by omega⟩ else c) else 0

open scoped Classical in
theorem degenNext_val_of_lt {F : ℕ → Set Q} {k : ℕ} {q : Q} {c : Fin (k + 1)} (h : c.val < k) :
    (degenNext F k q c).val = if q ∈ F c.val then c.val + 1 else c.val := by
  classical
  simp only [degenNext, h, dite_true]
  split_ifs <;> rfl

theorem degenNext_of_not_lt {F : ℕ → Set Q} {k : ℕ} {q : Q} {c : Fin (k + 1)}
    (h : ¬ c.val < k) : degenNext F k q c = 0 := by
  simp [degenNext, h]

/-- The Büchi automaton with a counter that goes through the sets `F 0, …, F (k - 1)`. -/
noncomputable def degeneralize (na : NA Q Symbol) (F : ℕ → Set Q) (k : ℕ) :
    Buchi (Q × Fin (k + 1)) Symbol where
  Tr p a p' := na.Tr p.1 a p'.1 ∧ p'.2 = degenNext F k p.1 p.2
  start := {p | p.1 ∈ na.start ∧ p.2 = 0}
  accept := {p | p.2.val = k}

theorem degeneralize_accepts_iff (na : NA Q Symbol) (F : ℕ → Set Q) (k : ℕ)
    (xs : ωSequence Symbol) :
    ωAcceptor.Accepts (degeneralize na F k) xs ↔
      ∃ ss, na.Run xs ss ∧ ∀ i < k, ∃ᶠ n in atTop, ss n ∈ F i := by
  constructor
  · rintro ⟨ts, ⟨hstart, htr⟩, hacc⟩
    refine ⟨⟨fun n => (ts n).1⟩, ⟨(hstart).1, fun n => (htr n).1⟩, fun i hi => ?_⟩
    rw [frequently_atTop] at hacc ⊢
    intro N
    obtain ⟨n₁, hn₁, hn₁k⟩ := hacc N
    have hn₁k' : (ts n₁).2.val = k := hn₁k
    have h0 : (ts (n₁ + 1)).2.val = 0 := by
      rw [(htr n₁).2, degenNext_of_not_lt (by omega)]
      rfl
    obtain ⟨n₂, hn₂, hn₂k⟩ := hacc (n₁ + 1)
    have hn₂k' : (ts n₂).2.val = k := hn₂k
    have hex : ∃ t, n₁ + 1 ≤ t ∧ i < (ts t).2.val := ⟨n₂, hn₂, by omega⟩
    classical
    obtain ⟨t, ⟨ht1, ht2⟩, hmin⟩ : ∃ t, (n₁ + 1 ≤ t ∧ i < (ts t).2.val) ∧
        ∀ s, s < t → ¬ (n₁ + 1 ≤ s ∧ i < (ts s).2.val) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun s hs => Nat.find_min hex hs⟩
    have htpos : n₁ + 1 < t := by
      rcases Nat.lt_or_ge (n₁ + 1) t with h | h
      · exact h
      · have : t = n₁ + 1 := le_antisymm h ht1
        rw [this] at ht2
        omega
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have hle : (ts t').2.val ≤ i := by
      by_contra hcon
      exact hmin t' (by omega) ⟨by omega, by omega⟩
    have hlt : (ts t').2.val < k := by omega
    have hstep := (htr t').2
    have hval : (ts (t' + 1)).2.val = if (ts t').1 ∈ F (ts t').2.val then (ts t').2.val + 1
        else (ts t').2.val := by
      rw [hstep, degenNext_val_of_lt hlt]
    have hin : (ts t').1 ∈ F (ts t').2.val := by
      by_contra hn
      simp only [hn, ite_false] at hval
      omega
    have hi' : (ts t').2.val = i := by
      simp only [hin, ite_true] at hval
      omega
    exact ⟨t', by omega, by rw [← hi']; exact hin⟩
  · rintro ⟨ss, ⟨hstart, htr⟩, hfair⟩
    classical
    let c : ℕ → Fin (k + 1) := fun n => Nat.rec 0 (fun n cn => degenNext F k (ss n) cn) n
    have hc0 : c 0 = 0 := rfl
    have hcs : ∀ n, c (n + 1) = degenNext F k (ss n) (c n) := fun n => rfl
    refine ⟨⟨fun n => (ss n, c n)⟩, ⟨⟨hstart, hc0⟩, fun n => ⟨htr n, hcs n⟩⟩, ?_⟩
    have mono : ∀ n, (c n).val < k → (c n).val ≤ (c (n + 1)).val := fun n hn => by
      rw [hcs, degenNext_val_of_lt hn]
      split_ifs <;> omega
    have key : ∀ d N, k - (c N).val ≤ d → ∃ n ≥ N, (c n).val = k := by
      intro d
      induction d with
      | zero => exact fun N hN => ⟨N, le_rfl, by have := (c N).isLt; omega⟩
      | succ d ih =>
        intro N hN
        by_cases hk : (c N).val < k
        swap
        · exact ⟨N, le_rfl, by have := (c N).isLt; omega⟩
        set j := (c N).val with hj
        obtain ⟨m, hm, hFm⟩ := frequently_atTop.1 (hfair j hk) N
        by_cases hlast : ∃ n, N ≤ n ∧ n ≤ m ∧ (c n).val = k
        · obtain ⟨n, hn, -, hnk⟩ := hlast
          exact ⟨n, hn, hnk⟩
        push Not at hlast
        have hge : ∀ n, N ≤ n → n ≤ m → j ≤ (c n).val := by
          intro n hn
          induction n, hn using Nat.le_induction with
          | base => exact fun _ => le_rfl
          | succ n hn ih =>
            intro hnm
            have hlt : (c n).val < k := lt_of_le_of_ne (by have := (c n).isLt; omega)
              (hlast n hn (by omega))
            exact (ih (by omega)).trans (mono n hlt)
        have hcm := hge m hm le_rfl
        have hcmk : (c m).val < k := lt_of_le_of_ne (by have := (c m).isLt; omega)
          (hlast m hm le_rfl)
        have : ∃ m', N ≤ m' ∧ j + 1 ≤ (c m').val := by
          by_cases hgt : j < (c m).val
          · exact ⟨m, hm, hgt⟩
          · have hjm : (c m).val = j := by omega
            refine ⟨m + 1, by omega, ?_⟩
            rw [hcs, degenNext_val_of_lt hcmk, hjm]
            simp only [hFm, ite_true, le_refl]
        obtain ⟨m', hm', hcm'⟩ := this
        obtain ⟨n, hn, hnk⟩ := ih m' (by omega)
        exact ⟨n, hm'.trans hn, hnk⟩
    rw [frequently_atTop]
    intro N
    obtain ⟨n, hn, hnk⟩ := key k N (by omega)
    exact ⟨n, hn, hnk⟩

end Cslib.Automata.NA
