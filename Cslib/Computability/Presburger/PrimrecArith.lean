/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Init
public import Mathlib.Computability.Primrec.List
public import Mathlib.Basic.Denumerable
public import Mathlib.Tactic.Ring

/-! # Primitive recursive arithmetic on `ℤ` and `ℕ`

Mathlib has `Primcodable ℤ` but no primitive-recursiveness lemmas about integer arithmetic, and
none about `Nat.gcd`. We prove what is needed for the Presburger decision procedure: the integers
are decomposed into their positive and negative parts (`Int.toNat z` and `(-z).toNat`), which are
primitive recursive from the encoding of `ℤ`, and `ℕ × ℕ → ℤ`, `(p, q) ↦ p - q` is primitive
recursive as well. Addition, multiplication, negation, `natAbs` and `sign` follow.

## Main statements

- `Presburger.PrimrecArith.primrec_add`, `primrec_mul`, `primrec_neg`, `primrec_natAbs`,
  `primrec_sign`: integer arithmetic.
- `Presburger.PrimrecArith.primrecPred_le_zero` and friends: sign tests.
- `Presburger.PrimrecArith.primrec_gcd`, `primrec_lcm`: `Nat.gcd` and `Nat.lcm`.
-/

@[expose] public section

namespace Cslib.Presburger.PrimrecArith

open Primrec Encodable

theorem encode_int (z : ℤ) :
    encode z = if 0 ≤ z then 2 * z.toNat else 2 * (-(z + 1)).toNat + 1 := by
  rcases z with n | n
  · have : 0 ≤ Int.ofNat n := Int.natCast_nonneg n
    simp only [this, ↓reduceIte]
    rfl
  · have : ¬ 0 ≤ Int.negSucc n := by omega
    simp only [this, ↓reduceIte]
    change 2 * n + 1 = _
    omega

/-- The positive part. -/
theorem primrec_toNat : Primrec Int.toNat := by
  have : Primrec (fun z : ℤ => if encode z % 2 = 0 then encode z / 2 else 0) :=
    Primrec.ite (Primrec.eq.comp (nat_mod.comp Primrec.encode (Primrec.const 2)) (Primrec.const 0))
      (nat_div.comp Primrec.encode (Primrec.const 2)) (Primrec.const 0)
  refine this.of_eq fun z => ?_
  rw [encode_int z]
  split_ifs <;> omega

theorem primrec_negPart : Primrec (fun z : ℤ => (-z).toNat) := by
  have : Primrec (fun z : ℤ => if encode z % 2 = 0 then 0 else encode z / 2 + 1) :=
    Primrec.ite (Primrec.eq.comp (nat_mod.comp Primrec.encode (Primrec.const 2)) (Primrec.const 0))
      (Primrec.const 0) (Primrec.succ.comp (nat_div.comp Primrec.encode (Primrec.const 2)))
  refine this.of_eq fun z => ?_
  rw [encode_int z]
  split_ifs <;> omega

theorem primrec_sub : Primrec (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2) := by
  have : Primrec (fun p : ℕ × ℕ => (Denumerable.ofNat ℤ
      (if p.2 ≤ p.1 then 2 * (p.1 - p.2) else 2 * (p.2 - p.1 - 1) + 1))) :=
    (Primrec.ofNat ℤ).comp <| Primrec.ite (Primrec.nat_le.comp snd fst)
      (nat_double.comp (nat_sub.comp fst snd))
      (nat_double_succ.comp (nat_sub.comp (nat_sub.comp snd fst) (Primrec.const 1)))
  refine this.of_eq fun p => ?_
  refine encode_injective ?_
  rw [Denumerable.encode_ofNat, encode_int]
  split_ifs <;> omega

theorem primrec_add : Primrec₂ (· + · : ℤ → ℤ → ℤ) := by
  have h := primrec_sub.comp
    ((nat_add.comp (primrec_toNat.comp fst) (primrec_toNat.comp snd)).pair
      (nat_add.comp (primrec_negPart.comp fst) (primrec_negPart.comp snd)))
  refine h.of_eq fun p => ?_
  dsimp only
  omega

theorem primrec_neg : Primrec (fun z : ℤ => -z) := by
  have h := primrec_sub.comp (primrec_negPart.pair primrec_toNat)
  refine h.of_eq fun z => ?_
  omega

theorem primrec_mul : Primrec₂ (· * · : ℤ → ℤ → ℤ) := by
  have h := primrec_sub.comp
    ((nat_add.comp
        (nat_mul.comp (primrec_toNat.comp fst) (primrec_toNat.comp snd))
        (nat_mul.comp (primrec_negPart.comp fst) (primrec_negPart.comp snd))).pair
      (nat_add.comp
        (nat_mul.comp (primrec_toNat.comp fst) (primrec_negPart.comp snd))
        (nat_mul.comp (primrec_negPart.comp fst) (primrec_toNat.comp snd))))
  refine h.of_eq fun p => ?_
  obtain ⟨a, b⟩ := p
  dsimp only
  have ha := Int.toNat_sub_toNat_neg a
  have hb := Int.toNat_sub_toNat_neg b
  have e : ((a.toNat * b.toNat + (-a).toNat * (-b).toNat : ℕ) : ℤ) -
      ((a.toNat * (-b).toNat + (-a).toNat * b.toNat : ℕ) : ℤ) =
      ((a.toNat : ℤ) - (-a).toNat) * ((b.toNat : ℤ) - (-b).toNat) := by
    push_cast; ring
  rw [ha, hb] at e
  exact e

theorem primrec_natCast : Primrec (fun n : ℕ => (n : ℤ)) := by
  have h := primrec_sub.comp (Primrec.id.pair (Primrec.const 0))
  refine h.of_eq fun n => ?_
  simp only [id_eq]
  omega

theorem primrec_natAbs : Primrec Int.natAbs := by
  have h := nat_add.comp primrec_toNat primrec_negPart
  refine h.of_eq fun z => ?_
  omega

theorem primrec_sign : Primrec Int.sign := by
  have : Primrec (fun z : ℤ =>
      if z.toNat = 0 then (if (-z).toNat = 0 then (0 : ℤ) else -1) else 1) :=
    Primrec.ite (Primrec.eq.comp primrec_toNat (const 0))
      (Primrec.ite (Primrec.eq.comp primrec_negPart (const 0)) (const 0) (const (-1))) (const 1)
  refine this.of_eq fun z => ?_
  rcases lt_trichotomy z 0 with h | h | h
  · rw [Int.sign_eq_neg_one_of_neg h]; split_ifs <;> omega
  · rw [h]; simp
  · rw [Int.sign_eq_one_of_pos h]; split_ifs <;> omega

theorem primrecPred_le_zero : PrimrecPred (fun z : ℤ => z ≤ 0) :=
  (Primrec.eq.comp primrec_toNat (const 0)).of_eq fun z => by omega

theorem primrecPred_zero_lt : PrimrecPred (fun z : ℤ => 0 < z) :=
  PrimrecPred.not primrecPred_le_zero |>.of_eq fun z => by omega

theorem primrecPred_lt_zero : PrimrecPred (fun z : ℤ => z < 0) :=
  (Primrec.eq.comp primrec_negPart (const 0)).not.of_eq fun z => by omega

theorem primrec_gcd : Primrec₂ Nat.gcd := by
  have hd : PrimrecRel fun (p : ℕ × ℕ) d => d ∣ p.1 ∧ d ∣ p.2 :=
    PrimrecPred.and
      ((Primrec.eq.comp (nat_mod.comp (fst.comp fst) snd) (const 0)).of_eq fun _ => by
        simp only [Nat.dvd_iff_mod_eq_zero])
      ((Primrec.eq.comp (nat_mod.comp (snd.comp fst) snd) (const 0)).of_eq fun _ => by
        simp only [Nat.dvd_iff_mod_eq_zero])
  refine (nat_findGreatest (nat_add.comp fst snd) hd).of_eq fun ⟨a, b⟩ => ?_
  dsimp only
  rw [Nat.findGreatest_eq_iff]
  refine ⟨?_, fun _ => ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩, ?_⟩
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · exact (Nat.gcd_le_left b ha).trans (Nat.le_add_right a b)
  · rintro n hn hle ⟨h1, h2⟩
    have h := Nat.dvd_gcd h1 h2
    rcases Nat.eq_zero_or_pos (Nat.gcd a b) with h0 | h0
    · have := Nat.gcd_eq_zero_iff.1 h0
      omega
    · exact absurd (Nat.le_of_dvd h0 h) (by omega)

theorem primrec_lcm : Primrec₂ Nat.lcm :=
  (nat_div.comp (nat_mul.comp fst snd) primrec_gcd).to₂.of_eq fun _ _ => rfl

end Cslib.Presburger.PrimrecArith
