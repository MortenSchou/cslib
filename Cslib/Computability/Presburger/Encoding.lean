/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.Presburger.Syntax
public import Mathlib.Computability.Primrec.List
public import Mathlib.Basic.Denumerable

/-! # Gödel numbering of Presburger formulas

`Term`, `QF` and `PForm` are `Denumerable`, hence `Primcodable`. The numbering is the usual one:
the low bits of the code are a constructor tag and the high bits are the codes of the arguments
(`Nat.pair` for several arguments), so the codes of the immediate subformulas are smaller than the
code of a formula.

The constructors are primitive recursive, and so is every function defined by structural recursion
on `QF` or `PForm` from primitive recursive step functions (`QF.primrec_rec`, `PForm.primrec_rec`,
and the versions `QF.primrec_rec₀`, `PForm.primrec_rec₀` without parameter). The equations of the
function are hypotheses of these lemmas, so that no fold combinator is needed and, for a function
defined by pattern matching, they hold by `rfl`. Primitive recursiveness of the syntactic
operations (see `Cslib.Computability.Presburger.Computable`) is derived from these lemmas.

## Main definitions

- `Presburger.Term.equiv`: the isomorphism `Term ≃ ℤ × List ℤ` that gives `Denumerable Term`.
- `Presburger.QF.code`, `Presburger.PForm.code`: the Gödel numberings.

## Main statements

- `Presburger.QF.primrec_rec`, `Presburger.PForm.primrec_rec`: primitive recursion on formulas.
-/

@[expose] public section

namespace Cslib.Presburger

open Encodable

namespace Term

/-- A term is a constant together with a list of coefficients. -/
def equiv : Term ≃ ℤ × List ℤ where
  toFun t := (t.const, t.coeffs)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Denumerable Term := Denumerable.ofEquiv _ equiv

theorem primrec_equiv : Primrec equiv :=
  Primrec.encode_iff.1 (Primrec.encode.of_eq fun _ => rfl)

theorem primrec_mk : Primrec₂ Term.mk :=
  Primrec.encode_iff.1 ((Primrec.encode.comp (Primrec.fst.pair Primrec.snd)).of_eq fun _ => rfl)

theorem primrec_const : Primrec Term.const := Primrec.fst.comp primrec_equiv

theorem primrec_coeffs : Primrec Term.coeffs := Primrec.snd.comp primrec_equiv

end Term

namespace QF

/-- The code of a formula. -/
def code : QF → ℕ
  | le t => 4 * encode t
  | dvd m t => 4 * Nat.pair m (encode t) + 1
  | and φ ψ => 4 * Nat.pair φ.code ψ.code + 2
  | or φ ψ => 4 * Nat.pair φ.code ψ.code + 3

/-- Decoding. -/
def ofCode (n : ℕ) : QF :=
  if h : n % 4 < 2 then
    if n % 4 = 0 then le (Denumerable.ofNat Term (n / 4))
    else dvd (n / 4).unpair.1 (Denumerable.ofNat Term (n / 4).unpair.2)
  else
    have h1 : (n / 4).unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le _) (by omega)
    have h2 : (n / 4).unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le _) (by omega)
    if n % 4 = 2 then and (ofCode (n / 4).unpair.1) (ofCode (n / 4).unpair.2)
    else or (ofCode (n / 4).unpair.1) (ofCode (n / 4).unpair.2)
termination_by n

theorem ofCode_mod0 {n : ℕ} (h : n % 4 = 0) : ofCode n = le (Denumerable.ofNat Term (n / 4)) := by
  rw [ofCode]; simp only [h]; simp

theorem ofCode_mod1 {n : ℕ} (h : n % 4 = 1) :
    ofCode n = dvd (n / 4).unpair.1 (Denumerable.ofNat Term (n / 4).unpair.2) := by
  rw [ofCode]; simp [h]

theorem ofCode_mod2 {n : ℕ} (h : n % 4 = 2) :
    ofCode n = and (ofCode (n / 4).unpair.1) (ofCode (n / 4).unpair.2) := by
  rw [ofCode]; simp [h]

theorem ofCode_mod3 {n : ℕ} (h : n % 4 = 3) :
    ofCode n = or (ofCode (n / 4).unpair.1) (ofCode (n / 4).unpair.2) := by
  rw [ofCode]; simp [h]

theorem ofCode_code (φ : QF) : ofCode (code φ) = φ := by
  induction φ with
  | le t =>
    rw [code, ofCode_mod0 (by omega), show 4 * encode t / 4 = encode t by omega,
      Denumerable.ofNat_encode]
  | dvd m t =>
    rw [code, ofCode_mod1 (by omega), show (4 * Nat.pair m (encode t) + 1) / 4 =
      Nat.pair m (encode t) by omega, Nat.unpair_pair, Denumerable.ofNat_encode]
  | and φ ψ ihφ ihψ =>
    rw [code, ofCode_mod2 (by omega), show (4 * Nat.pair φ.code ψ.code + 2) / 4 =
      Nat.pair φ.code ψ.code by omega, Nat.unpair_pair, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    rw [code, ofCode_mod3 (by omega), show (4 * Nat.pair φ.code ψ.code + 3) / 4 =
      Nat.pair φ.code ψ.code by omega, Nat.unpair_pair, ihφ, ihψ]

theorem code_ofCode (n : ℕ) : code (ofCode n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · rw [ofCode_mod0 h, code, Denumerable.encode_ofNat]; omega
    · rw [ofCode_mod1 h, code, Denumerable.encode_ofNat, Nat.pair_unpair]; omega
    · rw [ofCode_mod2 h, code, ih _ (lt_of_le_of_lt (Nat.unpair_left_le _) (by omega)),
        ih _ (lt_of_le_of_lt (Nat.unpair_right_le _) (by omega)), Nat.pair_unpair]
      omega
    · rw [ofCode_mod3 h, code, ih _ (lt_of_le_of_lt (Nat.unpair_left_le _) (by omega)),
        ih _ (lt_of_le_of_lt (Nat.unpair_right_le _) (by omega)), Nat.pair_unpair]
      omega

instance : Denumerable QF :=
  Denumerable.mk' ⟨code, ofCode, ofCode_code, code_ofCode⟩

open Primrec in
/-- **Primitive recursion on quantifier-free formulas.** A function defined by structural
recursion, with a parameter in `α`, is primitive recursive if its step functions are. -/
theorem primrec_rec {α σ : Type} [Primcodable α] [Primcodable σ] {f : α → QF → σ}
    {fle : α → Term → σ} {fdvd : α → ℕ → Term → σ} {fand for_ : α → σ → σ → σ}
    (hle : Primrec₂ fle) (hdvd : Primrec fun p : α × ℕ × Term => fdvd p.1 p.2.1 p.2.2)
    (hand : Primrec fun p : α × σ × σ => fand p.1 p.2.1 p.2.2)
    (hor : Primrec fun p : α × σ × σ => for_ p.1 p.2.1 p.2.2)
    (e_le : ∀ a t, f a (le t) = fle a t) (e_dvd : ∀ a m t, f a (dvd m t) = fdvd a m t)
    (e_and : ∀ a φ ψ, f a (and φ ψ) = fand a (f a φ) (f a ψ))
    (e_or : ∀ a φ ψ, f a (or φ ψ) = for_ a (f a φ) (f a ψ)) : Primrec₂ f := by
  let F : α → ℕ → σ := fun a n => f a (ofCode n)
  let d : α → σ := fun a => fle a (Denumerable.ofNat Term 0)
  let G : α → List σ → σ := fun a IH =>
    if IH.length % 4 = 0 then fle a (Denumerable.ofNat Term (IH.length / 4))
    else if IH.length % 4 = 1 then
      fdvd a (IH.length / 4).unpair.1 (Denumerable.ofNat Term (IH.length / 4).unpair.2)
    else if IH.length % 4 = 2 then
      fand a ((IH[(IH.length / 4).unpair.1]?).getD (d a))
        ((IH[(IH.length / 4).unpair.2]?).getD (d a))
    else
      for_ a ((IH[(IH.length / 4).unpair.1]?).getD (d a))
        ((IH[(IH.length / 4).unpair.2]?).getD (d a))
  have hn : Primrec fun p : α × List σ => p.2.length := list_length.comp snd
  have hm : Primrec fun p : α × List σ => p.2.length / 4 := nat_div.comp hn (const 4)
  have hr : Primrec fun p : α × List σ => p.2.length % 4 := nat_mod.comp hn (const 4)
  have hu1 : Primrec fun p : α × List σ => (p.2.length / 4).unpair.1 :=
    fst.comp (Primrec.unpair.comp hm)
  have hu2 : Primrec fun p : α × List σ => (p.2.length / 4).unpair.2 :=
    snd.comp (Primrec.unpair.comp hm)
  have hd : Primrec d := hle.comp Primrec.id (const _)
  have hg1 : Primrec fun p : α × List σ => (p.2[(p.2.length / 4).unpair.1]?).getD (d p.1) :=
    option_getD.comp (list_getElem?.comp snd hu1) (hd.comp fst)
  have hg2 : Primrec fun p : α × List σ => (p.2[(p.2.length / 4).unpair.2]?).getD (d p.1) :=
    option_getD.comp (list_getElem?.comp snd hu2) (hd.comp fst)
  have hG : Primrec₂ G := by
    refine Primrec.ite (Primrec.eq.comp hr (const 0))
      (hle.comp fst ((Primrec.ofNat Term).comp hm)) ?_
    refine Primrec.ite (Primrec.eq.comp hr (const 1))
      (hdvd.comp (fst.pair (hu1.pair ((Primrec.ofNat Term).comp hu2)))) ?_
    exact Primrec.ite (Primrec.eq.comp hr (const 2))
      (hand.comp (fst.pair (hg1.pair hg2))) (hor.comp (fst.pair (hg1.pair hg2)))
  have hF : Primrec₂ F := by
    refine nat_strong_rec F (g := fun a IH => some (G a IH)) (Primrec.option_some.comp hG)
      fun a n => ?_
    have hget : ∀ i, i < n → ((List.range n).map (F a))[i]? = some (F a i) := by
      intro i hi
      simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]
    have lt1 : n % 4 ≥ 2 → (n / 4).unpair.1 < n :=
      fun h => lt_of_le_of_lt (Nat.unpair_left_le _) (by omega)
    have lt2 : n % 4 ≥ 2 → (n / 4).unpair.2 < n :=
      fun h => lt_of_le_of_lt (Nat.unpair_right_le _) (by omega)
    change some (G a ((List.range n).map (F a))) = some (F a n)
    congr 1
    simp only [G, List.length_map, List.length_range]
    have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · simp only [h, ↓reduceIte, F, ofCode_mod0 h, e_le]
    · simp only [h, Nat.reduceEqDiff, ↓reduceIte, F, ofCode_mod1 h, e_dvd]
    · simp only [h, Nat.reduceEqDiff, ↓reduceIte, hget _ (lt1 (by omega)),
        hget _ (lt2 (by omega)), Option.getD_some, F, ofCode_mod2 h, e_and]
    · simp only [h, Nat.reduceEqDiff, ↓reduceIte, hget _ (lt1 (by omega)),
        hget _ (lt2 (by omega)), Option.getD_some, F, ofCode_mod3 h, e_or]
  exact (hF.comp fst (Primrec.encode.comp snd)).of_eq fun p =>
    congrArg (f p.1) (ofCode_code p.2)

open Primrec in
/-- **Primitive recursion on quantifier-free formulas**, without parameter. -/
theorem primrec_rec₀ {σ : Type} [Primcodable σ] {f : QF → σ} {fle : Term → σ}
    {fdvd : ℕ → Term → σ} {fand for_ : σ → σ → σ}
    (hle : Primrec fle) (hdvd : Primrec₂ fdvd) (hand : Primrec₂ fand) (hor : Primrec₂ for_)
    (e_le : ∀ t, f (le t) = fle t) (e_dvd : ∀ m t, f (dvd m t) = fdvd m t)
    (e_and : ∀ φ ψ, f (and φ ψ) = fand (f φ) (f ψ))
    (e_or : ∀ φ ψ, f (or φ ψ) = for_ (f φ) (f ψ)) : Primrec f :=
  (primrec_rec (α := Unit) (f := fun _ => f) (fle := fun _ => fle) (fdvd := fun _ => fdvd)
    (fand := fun _ => fand) (for_ := fun _ => for_) (hle.comp snd).to₂
    (hdvd.comp (fst.comp snd) (snd.comp snd)) (hand.comp (fst.comp snd) (snd.comp snd))
    (hor.comp (fst.comp snd) (snd.comp snd)) (fun _ => e_le) (fun _ => e_dvd)
    (fun _ => e_and) (fun _ => e_or)).comp (const ()) Primrec.id


section Constructors

open Primrec

private theorem primrec_tag {α : Type} [Primcodable α] {f : α → ℕ} (hf : Primrec f) (j : ℕ) :
    Primrec fun a => 4 * f a + j :=
  nat_add.comp (nat_mul.comp (const 4) hf) (const j)

theorem primrec_le : Primrec QF.le :=
  Primrec.encode_iff.1 ((primrec_tag Primrec.encode 0).of_eq fun _ => rfl)

theorem primrec_dvd : Primrec₂ QF.dvd :=
  Primrec.encode_iff.1
    ((primrec_tag (Primrec₂.natPair.comp fst (Primrec.encode.comp snd)) 1).of_eq fun _ => rfl)

theorem primrec_and : Primrec₂ QF.and :=
  Primrec.encode_iff.1 ((primrec_tag (Primrec₂.natPair.comp (Primrec.encode.comp fst)
    (Primrec.encode.comp snd)) 2).of_eq fun _ => rfl)

theorem primrec_or : Primrec₂ QF.or :=
  Primrec.encode_iff.1 ((primrec_tag (Primrec₂.natPair.comp (Primrec.encode.comp fst)
    (Primrec.encode.comp snd)) 3).of_eq fun _ => rfl)

end Constructors

end QF

namespace PForm

/-- The code of a formula. -/
def code : PForm → ℕ
  | le t => 8 * encode t
  | eq t => 8 * encode t + 1
  | dvd k t => 8 * Nat.pair k (encode t) + 2
  | not φ => 8 * φ.code + 3
  | and φ ψ => 8 * Nat.pair φ.code ψ.code + 4
  | or φ ψ => 8 * Nat.pair φ.code ψ.code + 5
  | ex φ => 8 * φ.code + 6
  | all φ => 8 * φ.code + 7

/-- Decoding. -/
def ofCode (n : ℕ) : PForm :=
  if h : n % 8 < 3 then
    if n % 8 = 0 then le (Denumerable.ofNat Term (n / 8))
    else if n % 8 = 1 then eq (Denumerable.ofNat Term (n / 8))
    else dvd (n / 8).unpair.1 (Denumerable.ofNat Term (n / 8).unpair.2)
  else
    have h0 : n / 8 < n := by omega
    have h1 : (n / 8).unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le _) h0
    have h2 : (n / 8).unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le _) h0
    if n % 8 = 3 then not (ofCode (n / 8))
    else if n % 8 = 4 then and (ofCode (n / 8).unpair.1) (ofCode (n / 8).unpair.2)
    else if n % 8 = 5 then or (ofCode (n / 8).unpair.1) (ofCode (n / 8).unpair.2)
    else if n % 8 = 6 then ex (ofCode (n / 8))
    else all (ofCode (n / 8))
termination_by n

theorem ofCode_mod0 {n : ℕ} (h : n % 8 = 0) : ofCode n = le (Denumerable.ofNat Term (n / 8)) := by
  rw [ofCode]; simp [h]

theorem ofCode_mod1 {n : ℕ} (h : n % 8 = 1) : ofCode n = eq (Denumerable.ofNat Term (n / 8)) := by
  rw [ofCode]; simp [h]

theorem ofCode_mod2 {n : ℕ} (h : n % 8 = 2) :
    ofCode n = dvd (n / 8).unpair.1 (Denumerable.ofNat Term (n / 8).unpair.2) := by
  rw [ofCode]; simp [h]

theorem ofCode_mod3 {n : ℕ} (h : n % 8 = 3) : ofCode n = not (ofCode (n / 8)) := by
  rw [ofCode]; simp [h]

theorem ofCode_mod4 {n : ℕ} (h : n % 8 = 4) :
    ofCode n = and (ofCode (n / 8).unpair.1) (ofCode (n / 8).unpair.2) := by
  rw [ofCode]; simp [h]

theorem ofCode_mod5 {n : ℕ} (h : n % 8 = 5) :
    ofCode n = or (ofCode (n / 8).unpair.1) (ofCode (n / 8).unpair.2) := by
  rw [ofCode]; simp [h]

theorem ofCode_mod6 {n : ℕ} (h : n % 8 = 6) : ofCode n = ex (ofCode (n / 8)) := by
  rw [ofCode]; simp [h]

theorem ofCode_mod7 {n : ℕ} (h : n % 8 = 7) : ofCode n = all (ofCode (n / 8)) := by
  rw [ofCode]; simp [h]

theorem ofCode_code (φ : PForm) : ofCode (code φ) = φ := by
  induction φ with
  | le t =>
    rw [code, ofCode_mod0 (by omega), show 8 * encode t / 8 = encode t by omega,
      Denumerable.ofNat_encode]
  | eq t =>
    rw [code, ofCode_mod1 (by omega), show (8 * encode t + 1) / 8 = encode t by omega,
      Denumerable.ofNat_encode]
  | dvd k t =>
    rw [code, ofCode_mod2 (by omega), show (8 * Nat.pair k (encode t) + 2) / 8 =
      Nat.pair k (encode t) by omega, Nat.unpair_pair, Denumerable.ofNat_encode]
  | not φ ih =>
    rw [code, ofCode_mod3 (by omega), show (8 * φ.code + 3) / 8 = φ.code by omega, ih]
  | and φ ψ ihφ ihψ =>
    rw [code, ofCode_mod4 (by omega), show (8 * Nat.pair φ.code ψ.code + 4) / 8 =
      Nat.pair φ.code ψ.code by omega, Nat.unpair_pair, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    rw [code, ofCode_mod5 (by omega), show (8 * Nat.pair φ.code ψ.code + 5) / 8 =
      Nat.pair φ.code ψ.code by omega, Nat.unpair_pair, ihφ, ihψ]
  | ex φ ih =>
    rw [code, ofCode_mod6 (by omega), show (8 * φ.code + 6) / 8 = φ.code by omega, ih]
  | all φ ih =>
    rw [code, ofCode_mod7 (by omega), show (8 * φ.code + 7) / 8 = φ.code by omega, ih]

theorem code_ofCode (n : ℕ) : code (ofCode n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h8 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨
        n % 8 = 6 ∨ n % 8 = 7 := by omega
    rcases h8 with h | h | h | h | h | h | h | h
    · rw [ofCode_mod0 h, code, Denumerable.encode_ofNat]; omega
    · rw [ofCode_mod1 h, code, Denumerable.encode_ofNat]; omega
    · rw [ofCode_mod2 h, code, Denumerable.encode_ofNat, Nat.pair_unpair]; omega
    · rw [ofCode_mod3 h, code, ih _ (by omega)]; omega
    · rw [ofCode_mod4 h, code, ih _ (lt_of_le_of_lt (Nat.unpair_left_le _) (by omega)),
        ih _ (lt_of_le_of_lt (Nat.unpair_right_le _) (by omega)), Nat.pair_unpair]
      omega
    · rw [ofCode_mod5 h, code, ih _ (lt_of_le_of_lt (Nat.unpair_left_le _) (by omega)),
        ih _ (lt_of_le_of_lt (Nat.unpair_right_le _) (by omega)), Nat.pair_unpair]
      omega
    · rw [ofCode_mod6 h, code, ih _ (by omega)]; omega
    · rw [ofCode_mod7 h, code, ih _ (by omega)]; omega

instance : Denumerable PForm :=
  Denumerable.mk' ⟨code, ofCode, ofCode_code, code_ofCode⟩

open Primrec in
/-- **Primitive recursion on formulas.** A function defined by structural recursion, with a
parameter in `α`, is primitive recursive if its step functions are. -/
theorem primrec_rec {α σ : Type} [Primcodable α] [Primcodable σ] {f : α → PForm → σ}
    {fle feq : α → Term → σ} {fdvd : α → ℕ → Term → σ} {fnot : α → σ → σ}
    {fand for_ : α → σ → σ → σ} {fex fall : α → σ → σ}
    (hle : Primrec₂ fle) (heq : Primrec₂ feq)
    (hdvd : Primrec fun p : α × ℕ × Term => fdvd p.1 p.2.1 p.2.2)
    (hnot : Primrec₂ fnot)
    (hand : Primrec fun p : α × σ × σ => fand p.1 p.2.1 p.2.2)
    (hor : Primrec fun p : α × σ × σ => for_ p.1 p.2.1 p.2.2)
    (hex : Primrec₂ fex) (hall : Primrec₂ fall)
    (e_le : ∀ a t, f a (le t) = fle a t) (e_eq : ∀ a t, f a (eq t) = feq a t)
    (e_dvd : ∀ a k t, f a (dvd k t) = fdvd a k t)
    (e_not : ∀ a φ, f a (not φ) = fnot a (f a φ))
    (e_and : ∀ a φ ψ, f a (and φ ψ) = fand a (f a φ) (f a ψ))
    (e_or : ∀ a φ ψ, f a (or φ ψ) = for_ a (f a φ) (f a ψ))
    (e_ex : ∀ a φ, f a (ex φ) = fex a (f a φ))
    (e_all : ∀ a φ, f a (all φ) = fall a (f a φ)) : Primrec₂ f := by
  let F : α → ℕ → σ := fun a n => f a (ofCode n)
  let d : α → σ := fun a => fle a (Denumerable.ofNat Term 0)
  let G : α → List σ → σ := fun a IH =>
    if IH.length % 8 = 0 then fle a (Denumerable.ofNat Term (IH.length / 8))
    else if IH.length % 8 = 1 then feq a (Denumerable.ofNat Term (IH.length / 8))
    else if IH.length % 8 = 2 then
      fdvd a (IH.length / 8).unpair.1 (Denumerable.ofNat Term (IH.length / 8).unpair.2)
    else if IH.length % 8 = 3 then fnot a ((IH[IH.length / 8]?).getD (d a))
    else if IH.length % 8 = 4 then
      fand a ((IH[(IH.length / 8).unpair.1]?).getD (d a))
        ((IH[(IH.length / 8).unpair.2]?).getD (d a))
    else if IH.length % 8 = 5 then
      for_ a ((IH[(IH.length / 8).unpair.1]?).getD (d a))
        ((IH[(IH.length / 8).unpair.2]?).getD (d a))
    else if IH.length % 8 = 6 then fex a ((IH[IH.length / 8]?).getD (d a))
    else fall a ((IH[IH.length / 8]?).getD (d a))
  have hn : Primrec fun p : α × List σ => p.2.length := list_length.comp snd
  have hm : Primrec fun p : α × List σ => p.2.length / 8 := nat_div.comp hn (const 8)
  have hr : Primrec fun p : α × List σ => p.2.length % 8 := nat_mod.comp hn (const 8)
  have hu1 : Primrec fun p : α × List σ => (p.2.length / 8).unpair.1 :=
    fst.comp (Primrec.unpair.comp hm)
  have hu2 : Primrec fun p : α × List σ => (p.2.length / 8).unpair.2 :=
    snd.comp (Primrec.unpair.comp hm)
  have hd : Primrec d := hle.comp Primrec.id (const _)
  have hg0 : Primrec fun p : α × List σ => (p.2[p.2.length / 8]?).getD (d p.1) :=
    option_getD.comp (list_getElem?.comp snd hm) (hd.comp fst)
  have hg1 : Primrec fun p : α × List σ => (p.2[(p.2.length / 8).unpair.1]?).getD (d p.1) :=
    option_getD.comp (list_getElem?.comp snd hu1) (hd.comp fst)
  have hg2 : Primrec fun p : α × List σ => (p.2[(p.2.length / 8).unpair.2]?).getD (d p.1) :=
    option_getD.comp (list_getElem?.comp snd hu2) (hd.comp fst)
  have hG : Primrec₂ G := by
    refine Primrec.ite (Primrec.eq.comp hr (const 0))
      (hle.comp fst ((Primrec.ofNat Term).comp hm)) ?_
    refine Primrec.ite (Primrec.eq.comp hr (const 1))
      (heq.comp fst ((Primrec.ofNat Term).comp hm)) ?_
    refine Primrec.ite (Primrec.eq.comp hr (const 2))
      (hdvd.comp (fst.pair (hu1.pair ((Primrec.ofNat Term).comp hu2)))) ?_
    refine Primrec.ite (Primrec.eq.comp hr (const 3)) (hnot.comp fst hg0) ?_
    refine Primrec.ite (Primrec.eq.comp hr (const 4)) (hand.comp (fst.pair (hg1.pair hg2))) ?_
    refine Primrec.ite (Primrec.eq.comp hr (const 5)) (hor.comp (fst.pair (hg1.pair hg2))) ?_
    exact Primrec.ite (Primrec.eq.comp hr (const 6)) (hex.comp fst hg0) (hall.comp fst hg0)
  have hF : Primrec₂ F := by
    refine nat_strong_rec F (g := fun a IH => some (G a IH)) (Primrec.option_some.comp hG)
      fun a n => ?_
    have hget : ∀ i, i < n → ((List.range n).map (F a))[i]? = some (F a i) := by
      intro i hi
      simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]
    have lt0 : n % 8 ≥ 3 → n / 8 < n := fun h => by omega
    have lt1 : n % 8 ≥ 3 → (n / 8).unpair.1 < n :=
      fun h => lt_of_le_of_lt (Nat.unpair_left_le _) (by omega)
    have lt2 : n % 8 ≥ 3 → (n / 8).unpair.2 < n :=
      fun h => lt_of_le_of_lt (Nat.unpair_right_le _) (by omega)
    change some (G a ((List.range n).map (F a))) = some (F a n)
    congr 1
    simp only [G, List.length_map, List.length_range]
    have h8 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨
        n % 8 = 6 ∨ n % 8 = 7 := by omega
    rcases h8 with h | h | h | h | h | h | h | h
    · simp only [h, ↓reduceIte, F, ofCode_mod0 h, e_le]
    · simp only [h, Nat.reduceEqDiff, ↓reduceIte, F, ofCode_mod1 h, e_eq]
    · simp only [h, Nat.reduceEqDiff, ↓reduceIte, F, ofCode_mod2 h, e_dvd]
    · simp only [h, Nat.reduceEqDiff, ↓reduceIte, hget _ (lt0 (by omega)), Option.getD_some, F,
        ofCode_mod3 h, e_not]
    · simp only [h, Nat.reduceEqDiff, ↓reduceIte, hget _ (lt1 (by omega)),
        hget _ (lt2 (by omega)), Option.getD_some, F, ofCode_mod4 h, e_and]
    · simp only [h, Nat.reduceEqDiff, ↓reduceIte, hget _ (lt1 (by omega)),
        hget _ (lt2 (by omega)), Option.getD_some, F, ofCode_mod5 h, e_or]
    · simp only [h, Nat.reduceEqDiff, ↓reduceIte, hget _ (lt0 (by omega)), Option.getD_some, F,
        ofCode_mod6 h, e_ex]
    · simp only [h, Nat.reduceEqDiff, ↓reduceIte, hget _ (lt0 (by omega)), Option.getD_some, F,
        ofCode_mod7 h, e_all]
  exact (hF.comp fst (Primrec.encode.comp snd)).of_eq fun p =>
    congrArg (f p.1) (ofCode_code p.2)

open Primrec in
/-- **Primitive recursion on formulas**, without parameter. -/
theorem primrec_rec₀ {σ : Type} [Primcodable σ] {f : PForm → σ} {fle feq : Term → σ}
    {fdvd : ℕ → Term → σ} {fnot fex fall : σ → σ} {fand for_ : σ → σ → σ}
    (hle : Primrec fle) (heq : Primrec feq) (hdvd : Primrec₂ fdvd) (hnot : Primrec fnot)
    (hand : Primrec₂ fand) (hor : Primrec₂ for_) (hex : Primrec fex) (hall : Primrec fall)
    (e_le : ∀ t, f (le t) = fle t) (e_eq : ∀ t, f (eq t) = feq t)
    (e_dvd : ∀ k t, f (dvd k t) = fdvd k t) (e_not : ∀ φ, f (not φ) = fnot (f φ))
    (e_and : ∀ φ ψ, f (and φ ψ) = fand (f φ) (f ψ))
    (e_or : ∀ φ ψ, f (or φ ψ) = for_ (f φ) (f ψ))
    (e_ex : ∀ φ, f (ex φ) = fex (f φ)) (e_all : ∀ φ, f (all φ) = fall (f φ)) : Primrec f :=
  (primrec_rec (α := Unit) (f := fun _ => f) (fle := fun _ => fle) (feq := fun _ => feq)
    (fdvd := fun _ => fdvd) (fnot := fun _ => fnot) (fand := fun _ => fand)
    (for_ := fun _ => for_) (fex := fun _ => fex) (fall := fun _ => fall)
    (hle.comp snd).to₂ (heq.comp snd).to₂ (hdvd.comp (fst.comp snd) (snd.comp snd))
    (hnot.comp snd).to₂ (hand.comp (fst.comp snd) (snd.comp snd))
    (hor.comp (fst.comp snd) (snd.comp snd)) (hex.comp snd).to₂ (hall.comp snd).to₂
    (fun _ => e_le) (fun _ => e_eq) (fun _ => e_dvd) (fun _ => e_not) (fun _ => e_and)
    (fun _ => e_or) (fun _ => e_ex) (fun _ => e_all)).comp (const ()) Primrec.id

section Constructors

open Primrec

private theorem primrec_tag {α : Type} [Primcodable α] {f : α → ℕ} (hf : Primrec f) (j : ℕ) :
    Primrec fun a => 8 * f a + j :=
  nat_add.comp (nat_mul.comp (const 8) hf) (const j)

theorem primrec_le : Primrec PForm.le :=
  Primrec.encode_iff.1 ((primrec_tag Primrec.encode 0).of_eq fun _ => rfl)

theorem primrec_eq : Primrec PForm.eq :=
  Primrec.encode_iff.1 ((primrec_tag Primrec.encode 1).of_eq fun _ => rfl)

theorem primrec_dvd : Primrec₂ PForm.dvd :=
  Primrec.encode_iff.1
    ((primrec_tag (Primrec₂.natPair.comp fst (Primrec.encode.comp snd)) 2).of_eq fun _ => rfl)

theorem primrec_not : Primrec PForm.not :=
  Primrec.encode_iff.1 ((primrec_tag Primrec.encode 3).of_eq fun _ => rfl)

theorem primrec_and : Primrec₂ PForm.and :=
  Primrec.encode_iff.1 ((primrec_tag (Primrec₂.natPair.comp (Primrec.encode.comp fst)
    (Primrec.encode.comp snd)) 4).of_eq fun _ => rfl)

theorem primrec_or : Primrec₂ PForm.or :=
  Primrec.encode_iff.1 ((primrec_tag (Primrec₂.natPair.comp (Primrec.encode.comp fst)
    (Primrec.encode.comp snd)) 5).of_eq fun _ => rfl)

theorem primrec_ex : Primrec PForm.ex :=
  Primrec.encode_iff.1 ((primrec_tag Primrec.encode 6).of_eq fun _ => rfl)

theorem primrec_all : Primrec PForm.all :=
  Primrec.encode_iff.1 ((primrec_tag Primrec.encode 7).of_eq fun _ => rfl)

end Constructors

end PForm

end Cslib.Presburger
