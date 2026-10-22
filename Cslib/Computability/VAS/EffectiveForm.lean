/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.Effective
public import Cslib.Computability.Presburger.Decide

/-! # Presburger formulas for coded semilinear sets

A code of a semilinear set (`SLCode`) is translated into a Presburger formula, and the
inductiveness of a coded set for a coded VAS is expressed by a Presburger sentence. The translation
is the textbook one: the linear set with base `b` and periods `p₁, …, p_k` is
`∃ n₁ … n_k ≥ 0, x = b + ∑ nᵢ pᵢ`, and a semilinear set is the disjunction of its linear sets.

The formula `setForm d r` speaks about the vector of the `d` innermost variables `x₀, …, x_{d-1}`.
A block of `d` natural-number quantifiers (`allsNat d`) binds such a vector, and a second block
nested inside the first one refers to the outer vector through the shifted variables `x_{d+j}`.
Natural quantifiers are expressed by relativising integer quantifiers (`exNat`, `allNat`).

## Main definitions

- `Presburger.PForm.setForm`: the formula of a coded semilinear set at the innermost variables.
- `Presburger.PForm.inductiveForm`: the sentence "the coded set is inductive for the coded VAS".
- `Presburger.PForm.certForm`: the sentence "`X` is inductive, contains `x` and omits `y`".

## Main statements

- `Presburger.PForm.eval_setForm`: correctness of the translation.
- `Presburger.PForm.eval_inductiveForm`: correctness of the inductiveness sentence.
- `Presburger.PForm.valid_certForm_iff`: correctness of the certificate sentence.
-/

@[expose] public section

namespace Cslib

theorem VASCode.isInductive_iff {c : VASCode} {X : Set (Fin c.1 → ℕ)} :
    c.toVAS.IsInductive X ↔ ∀ x : Fin c.1 → ℕ, ∀ l ∈ c.2, x ∈ X →
      ∀ x' : Fin c.1 → ℕ, (∀ j, (x' j : ℤ) = x j + l.getD j 0) → x' ∈ X := by
  constructor
  · exact fun h x l hl hx x' hx' =>
      h x hx x' ⟨vecZ c.1 l, VASCode.mem_acts.2 ⟨l, hl, rfl⟩, funext hx'⟩
  · rintro h x hx x' ⟨a, ha, hxx⟩
    obtain ⟨l, hl, rfl⟩ := VASCode.mem_acts.1 ha
    exact h x l hl hx x' fun j => congrFun hxx j

namespace Presburger

/-! ### Environments -/

/-- The assignment that extends `v` by the natural numbers `ns`, the head being the variable `0`. -/
def envN : List ℕ → (ℕ → ℤ) → ℕ → ℤ
  | [], v => v
  | n :: ns, v => cons n (envN ns v)

theorem envN_getElem (ns : List ℕ) (v : ℕ → ℤ) (j : ℕ) (hj : j < ns.length) :
    envN ns v j = ns[j] := by
  induction ns generalizing j with
  | nil => simp at hj
  | cons n ns ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j (by simpa using hj)

@[simp] theorem envN_ofFn_apply {d : ℕ} (x : Fin d → ℕ) (v : ℕ → ℤ) (j : Fin d) :
    envN (List.ofFn x) v j = x j := by
  simp [envN_getElem]

theorem envN_add (ns : List ℕ) (v : ℕ → ℤ) (j : ℕ) : envN ns v (ns.length + j) = v j := by
  induction ns with
  | nil => simp [envN]
  | cons n ns ih => simpa [envN, Nat.add_right_comm] using ih

@[simp] theorem envN_ofFn_add {d : ℕ} (x : Fin d → ℕ) (v : ℕ → ℤ) (j : ℕ) :
    envN (List.ofFn x) v (d + j) = v j := by
  simpa using envN_add (List.ofFn x) v j

namespace PForm

/-! ### Bounded quantifiers and big connectives -/

/-- The nonnegativity of the variable `0`. -/
def nonneg : PForm := le (-Term.var 0)

/-- The natural-number quantifier `∃ x ≥ 0`. -/
def exNat (φ : PForm) : PForm := ex (and nonneg φ)

/-- The natural-number quantifier `∀ x ≥ 0`. -/
def allNat (φ : PForm) : PForm := all (imp nonneg φ)

/-- `k` natural-number existential quantifiers. -/
def exsNat (k : ℕ) (φ : PForm) : PForm := exNat^[k] φ

/-- `k` natural-number universal quantifiers. -/
def allsNat (k : ℕ) (φ : PForm) : PForm := allNat^[k] φ

/-- The disjunction of a list of formulas. -/
def bigOr (l : List PForm) : PForm := l.foldr or ff

/-- The conjunction of a list of formulas. -/
def bigAnd (l : List PForm) : PForm := l.foldr and tt

/-- The conjunction of `φ₀, …, φ_{d-1}`, where `φⱼ = f j`. -/
def andRange (d : ℕ) (f : ℕ → PForm) : PForm := bigAnd ((List.range d).map f)

@[simp] theorem eval_bigOr (v : ℕ → ℤ) (l : List PForm) :
    (bigOr l).eval v ↔ ∃ φ ∈ l, φ.eval v := by
  induction l with
  | nil => simp [bigOr]
  | cons φ l ih => simp_all [bigOr, eval]

@[simp] theorem eval_bigAnd (v : ℕ → ℤ) (l : List PForm) :
    (bigAnd l).eval v ↔ ∀ φ ∈ l, φ.eval v := by
  induction l with
  | nil => simp [bigAnd]
  | cons φ l ih => simp_all [bigAnd, eval]

@[simp] theorem eval_andRange (d : ℕ) (f : ℕ → PForm) (v : ℕ → ℤ) :
    (andRange d f).eval v ↔ ∀ j : Fin d, (f j).eval v := by
  simp [andRange, Fin.forall_iff]

@[simp] theorem eval_exNat (φ : PForm) (v : ℕ → ℤ) :
    (exNat φ).eval v ↔ ∃ n : ℕ, φ.eval (cons n v) := by
  simp only [exNat, nonneg, eval, Term.eval_neg, Term.eval_var, cons_zero]
  refine ⟨fun ⟨x, hx, h⟩ => ⟨x.toNat, ?_⟩, fun ⟨n, h⟩ => ⟨n, by omega, h⟩⟩
  rwa [Int.toNat_of_nonneg (by omega)]

@[simp] theorem eval_allNat (φ : PForm) (v : ℕ → ℤ) :
    (allNat φ).eval v ↔ ∀ n : ℕ, φ.eval (cons n v) := by
  simp only [allNat, nonneg, eval, eval_imp, Term.eval_neg, Term.eval_var, cons_zero]
  refine ⟨fun h n => h n (by omega), fun h x hx => ?_⟩
  simpa [Int.toNat_of_nonneg (by omega : 0 ≤ x)] using h x.toNat

theorem eval_exsNat (k : ℕ) (φ : PForm) (v : ℕ → ℤ) :
    (exsNat k φ).eval v ↔ ∃ ns : List ℕ, ns.length = k ∧ φ.eval (envN ns v) := by
  induction k generalizing φ with
  | zero => simp [exsNat, envN]
  | succ k ih =>
    rw [exsNat, Function.iterate_succ_apply, ← exsNat, ih]
    simp only [eval_exNat]
    refine ⟨fun ⟨ns, hns, n, h⟩ => ⟨n :: ns, by simp [hns], h⟩, ?_⟩
    rintro ⟨_ | ⟨n, ns⟩, hns, h⟩
    · simp at hns
    · exact ⟨ns, by simpa using hns, n, h⟩

theorem eval_allsNat (k : ℕ) (φ : PForm) (v : ℕ → ℤ) :
    (allsNat k φ).eval v ↔ ∀ ns : List ℕ, ns.length = k → φ.eval (envN ns v) := by
  induction k generalizing φ with
  | zero => simp [allsNat, envN]
  | succ k ih =>
    rw [allsNat, Function.iterate_succ_apply, ← allsNat, ih]
    simp only [eval_allNat]
    refine ⟨fun h => ?_, fun h ns hns n => h (n :: ns) (by simp [hns])⟩
    rintro (_ | ⟨n, ns⟩) hns
    · simp at hns
    · exact h ns (by simpa using hns) n

/-- A block of `d` natural-number quantifiers binds a vector `x : Fin d → ℕ`. -/
@[simp] theorem eval_allsNat_fin (d : ℕ) (φ : PForm) (v : ℕ → ℤ) :
    (allsNat d φ).eval v ↔ ∀ x : Fin d → ℕ, φ.eval (envN (List.ofFn x) v) := by
  rw [eval_allsNat]
  refine ⟨fun h x => h _ (by simp), fun h ns hns => ?_⟩
  subst hns
  simpa using h (fun j => ns[j])

/-! ### Coded semilinear sets -/

/-- The term `x_{k+j} - b_j - ∑ᵢ nᵢ pᵢ_j` for the linear set `l = (b, [p₁, …, p_k])`, where the
variable `i` stands for `nᵢ`. -/
def linTerm (l : List ℕ × List (List ℕ)) (j : ℕ) : Term :=
  ⟨-(l.1.getD j 0 : ℤ), l.2.map fun p => -(p.getD j 0 : ℤ)⟩ + Term.var (l.2.length + j)

/-- The formula that the vector of the innermost variables belongs to the linear set `l`. -/
def linForm (d : ℕ) (l : List ℕ × List (List ℕ)) : PForm :=
  exsNat l.2.length (andRange d fun j => eq (linTerm l j))

/-- The formula that the vector of the innermost variables belongs to the semilinear set coded
by `r`. -/
def setForm (d : ℕ) (r : SLCode) : PForm := bigOr (r.map (linForm d))

theorem evalCoeffs_negCol {d : ℕ} (ps : List (List ℕ)) (j : Fin d) (ns : List ℕ) (w : ℕ → ℤ)
    (h : ns.length = ps.length) :
    evalCoeffs (ps.map fun p => -(p.getD j 0 : ℤ)) (envN ns w) =
      -((List.zipWith (fun n p => n • vecN d p) ns ps).sum j : ℕ) := by
  induction ps generalizing ns with
  | nil => simp [evalCoeffs]
  | cons p ps ih =>
    obtain _ | ⟨n, ns⟩ := ns
    · simp at h
    · have := ih ns (by simpa using h)
      simp only [List.map_cons, evalCoeffs, envN, cons_zero, List.zipWith_cons_cons,
        List.sum_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_mul]
      change _ * _ + evalCoeffs _ (envN ns w) = _
      rw [this]
      simp [vecN]
      ring

@[simp] theorem eval_linForm {d : ℕ} (l : List ℕ × List (List ℕ)) (x : Fin d → ℕ) (v : ℕ → ℤ) :
    (linForm d l).eval (envN (List.ofFn x) v) ↔ x ∈ linSet d l := by
  rw [linForm, eval_exsNat, mem_linSet]
  refine exists_congr fun ns => and_congr_right fun hns => ?_
  rw [eval_andRange, funext_iff]
  refine forall_congr' fun j => ?_
  simp only [PForm.eval, linTerm, Term.eval_add, Term.eval_var]
  rw [← hns, envN_add, envN_ofFn_apply]
  simp only [Term.eval, evalCoeffs_negCol l.2 j ns _ hns, Pi.add_apply, vecN]
  omega

/-- **Correctness of the translation of a code to a formula.** -/
@[simp] theorem eval_setForm {d : ℕ} (r : SLCode) (x : Fin d → ℕ) (v : ℕ → ℤ) :
    (setForm d r).eval (envN (List.ofFn x) v) ↔ x ∈ r.set d := by
  simp [setForm, SLCode.set]

/-! ### Inductiveness and certificates -/

/-- The equations `x'ⱼ = xⱼ + aⱼ` between the innermost vector `x'` and the vector `x` just
outside of it. -/
def stepEq (d : ℕ) (a : List ℤ) : PForm :=
  andRange d fun j => eq' (Term.var j) (Term.var (d + j) + Term.ofInt (a.getD j 0))

/-- The closure of the coded set under the action `a`, for the innermost vector. -/
def stepForm (d : ℕ) (r : SLCode) (a : List ℤ) : PForm :=
  imp (setForm d r) (allsNat d (imp (stepEq d a) (setForm d r)))

/-- The sentence that the set coded by `r` is inductive for the VAS coded by `c`. -/
def inductiveForm (c : VASCode) (r : SLCode) : PForm :=
  allsNat c.1 (bigAnd (c.2.map (stepForm c.1 r)))

/-- The equations `xⱼ = aⱼ` between the innermost vector and the constant vector `a`. -/
def eqConst (d : ℕ) (a : List ℕ) : PForm :=
  andRange d fun j => eq' (Term.var j) (Term.ofInt (a.getD j 0 : ℕ))

/-- The sentence that the set coded by `r` is inductive, contains `x` and omits `y`. -/
def certForm (c : VASCode) (x y : List ℕ) (r : SLCode) : PForm :=
  and (inductiveForm c r)
    (allsNat c.1 (and (imp (eqConst c.1 x) (setForm c.1 r))
      (imp (eqConst c.1 y) (not (setForm c.1 r)))))

@[simp] theorem eval_stepEq {d : ℕ} (a : List ℤ) (x x' : Fin d → ℕ) (v : ℕ → ℤ) :
    (stepEq d a).eval (envN (List.ofFn x') (envN (List.ofFn x) v)) ↔
      ∀ j, (x' j : ℤ) = x j + a.getD j 0 := by
  simp [stepEq]

@[simp] theorem eval_stepForm {d : ℕ} (r : SLCode) (a : List ℤ) (x : Fin d → ℕ) (v : ℕ → ℤ) :
    (stepForm d r a).eval (envN (List.ofFn x) v) ↔
      (x ∈ r.set d → ∀ x' : Fin d → ℕ, (∀ j, (x' j : ℤ) = x j + a.getD j 0) → x' ∈ r.set d) := by
  simp [stepForm]

/-- **Correctness of the inductiveness sentence.** -/
@[simp] theorem eval_inductiveForm (c : VASCode) (r : SLCode) (v : ℕ → ℤ) :
    (inductiveForm c r).eval v ↔ c.toVAS.IsInductive (r.set c.1) := by
  simp [inductiveForm, VASCode.isInductive_iff]

@[simp] theorem eval_eqConst {d : ℕ} (a : List ℕ) (x : Fin d → ℕ) (v : ℕ → ℤ) :
    (eqConst d a).eval (envN (List.ofFn x) v) ↔ x = vecN d a := by
  simp [eqConst, funext_iff, vecN]

@[simp] theorem eval_certForm (c : VASCode) (x y : List ℕ) (r : SLCode) (v : ℕ → ℤ) :
    (certForm c x y r).eval v ↔ c.Certificate x y r := by
  simp [certForm, VASCode.Certificate, eval, forall_and]

/-- **Correctness of the certificate sentence**: it is valid iff `r` is a certificate. -/
theorem valid_certForm_iff (c : VASCode) (x y : List ℕ) (r : SLCode) :
    (certForm c x y r).valid = true ↔ c.Certificate x y r := by
  rw [valid_iff]
  exact ⟨fun h => (eval_certForm c x y r _).1 (h fun _ => 0),
    fun h v => (eval_certForm c x y r v).2 h⟩

end PForm

end Presburger

end Cslib
