/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.Presburger.Decide
public import Cslib.Computability.Presburger.Encoding
public import Cslib.Computability.Presburger.PrimrecArith
public import Mathlib.Computability.Halting

/-! # Computability of the Presburger decision procedure

Every operation of the decision procedure is primitive recursive for the Gödel numbering of
`Cslib.Computability.Presburger.Encoding`: first the operations on terms, then those on
quantifier-free formulas (each by `QF.primrec_rec`), then `PForm.qe` and finally `PForm.valid`.

## Main statements

- `Presburger.PForm.primrec_valid`: `PForm.valid` is primitive recursive.
- `Presburger.PForm.computable_valid`: `PForm.valid` is computable.
- `Presburger.PForm.computablePred_valid`: truth in all assignments is a computable predicate.
-/

@[expose] public section

namespace Cslib.Presburger

open Primrec
namespace Term

theorem length_addCoeffs (as bs : List ℤ) :
    (addCoeffs as bs).length = max as.length bs.length := by
  induction as generalizing bs <;> cases bs <;> simp_all [addCoeffs]

theorem getD_addCoeffs (as bs : List ℤ) (i : ℕ) :
    (addCoeffs as bs).getD i 0 = as.getD i 0 + bs.getD i 0 := by
  induction as generalizing bs i <;> cases bs <;> cases i <;> simp_all [addCoeffs]

theorem addCoeffs_eq (as bs : List ℤ) :
    addCoeffs as bs = (List.range (max as.length bs.length)).map
      fun i => as.getD i 0 + bs.getD i 0 :=
  List.ext_getElem (by simp [length_addCoeffs]) fun i h _ => by
    rw [List.getElem_map, List.getElem_range, ← getD_addCoeffs, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h]
    rfl

theorem primrec_addCoeffs : Primrec₂ addCoeffs := by
  have h := list_map
    (list_range.comp (nat_max.comp (list_length.comp fst) (list_length.comp snd)))
    (PrimrecArith.primrec_add.comp (((list_getD 0).comp (fst.comp fst) snd))
      ((list_getD 0).comp (snd.comp fst) snd)).to₂
  exact h.to₂.of_eq fun as bs => (addCoeffs_eq as bs).symm

theorem primrec_ofInt : Primrec Term.ofInt :=
  primrec_mk.comp Primrec.id (Primrec.const [])

theorem primrec_smul : Primrec₂ Term.smul :=
  primrec_mk.comp (PrimrecArith.primrec_mul.comp fst (primrec_const.comp snd))
    (list_map (primrec_coeffs.comp snd) (PrimrecArith.primrec_mul.comp (fst.comp fst) snd).to₂)

theorem primrec_add : Primrec₂ (· + · : Term → Term → Term) :=
  (primrec_mk.comp (PrimrecArith.primrec_add.comp (primrec_const.comp fst)
    (primrec_const.comp snd)) (primrec_addCoeffs.comp (primrec_coeffs.comp fst)
    (primrec_coeffs.comp snd))).to₂.of_eq fun _ _ => rfl

theorem primrec_neg : Primrec (fun t : Term => -t) :=
  primrec_smul.comp (Primrec.const (-1)) Primrec.id

theorem primrec_sub : Primrec₂ (· - · : Term → Term → Term) :=
  (primrec_add.comp fst (primrec_neg.comp snd)).to₂.of_eq fun _ _ => rfl

theorem primrec_coef0 : Primrec Term.coef0 :=
  (option_getD.comp (list_head?.comp primrec_coeffs) (Primrec.const 0)).of_eq fun t => by
    cases h : t.coeffs <;> simp [Term.coef0, h]

theorem primrec_rest : Primrec Term.rest :=
  primrec_mk.comp primrec_const (list_tail.comp primrec_coeffs)

theorem primrec_subst0 : Primrec₂ Term.subst0 :=
  (primrec_add.comp (primrec_rest.comp fst)
    (primrec_smul.comp (primrec_coef0.comp fst) snd)).to₂.of_eq fun _ _ => rfl

theorem primrec_absCoef : Primrec Term.absCoef :=
  (nat_max.comp (Primrec.const 1)
    (PrimrecArith.primrec_natAbs.comp primrec_coef0)).of_eq fun _ => rfl

theorem primrec_mult : Primrec₂ Term.mult :=
  (nat_div.comp fst (primrec_absCoef.comp snd)).to₂.of_eq fun _ _ => rfl

theorem primrec_scale : Primrec₂ Term.scale := by
  have hm : Primrec fun p : ℕ × Term => ((Term.mult p.1 p.2 : ℕ) : ℤ) :=
    PrimrecArith.primrec_natCast.comp (primrec_mult.comp fst snd)
  exact (primrec_mk.comp (PrimrecArith.primrec_mul.comp hm (primrec_const.comp snd))
    (list_cons.comp (PrimrecArith.primrec_sign.comp (primrec_coef0.comp snd))
      (list_map (primrec_coeffs.comp (primrec_rest.comp snd))
        (PrimrecArith.primrec_mul.comp (hm.comp fst) snd).to₂))).to₂.of_eq fun _ _ => rfl

end Term
namespace QF

theorem primrec_bigOr : Primrec bigOr :=
  list_foldr Primrec.id (Primrec.const ff) (primrec_or.comp (fst.comp snd) (snd.comp snd)).to₂

theorem primrec_negDvd : Primrec₂ negDvd := by
  have hr : Primrec fun p : (ℕ × Term) × ℕ => -(((p.2 : ℕ) : ℤ) + 1) :=
    PrimrecArith.primrec_neg.comp (PrimrecArith.primrec_add.comp
      (PrimrecArith.primrec_natCast.comp snd) (Primrec.const 1))
  exact (primrec_bigOr.comp (list_map (list_range.comp fst)
    (primrec_dvd.comp (fst.comp fst) (Term.primrec_add.comp (snd.comp fst)
      (Term.primrec_ofInt.comp hr))).to₂)).to₂.of_eq fun _ _ => rfl

theorem primrec_neg : Primrec QF.neg :=
  primrec_rec₀ (primrec_le.comp (Term.primrec_sub.comp (Primrec.const _) Primrec.id))
    primrec_negDvd primrec_or primrec_and (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)

theorem primrec_holds0 : Primrec holds0 :=
  primrec_rec₀ (PrimrecArith.primrecPred_le_zero.decide.comp Term.primrec_const)
    (Primrec.eq.decide.comp (nat_mod.comp (PrimrecArith.primrec_natAbs.comp
      (Term.primrec_const.comp snd)) (succ.comp fst)) (Primrec.const 0)).to₂
    Primrec.and Primrec.or (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem primrec_subst : Primrec₂ QF.subst :=
  primrec_rec (primrec_le.comp (Term.primrec_subst0.comp snd fst)).to₂
    (primrec_dvd.comp (fst.comp snd) (Term.primrec_subst0.comp (snd.comp snd) fst))
    (primrec_and.comp (fst.comp snd) (snd.comp snd))
    (primrec_or.comp (fst.comp snd) (snd.comp snd))
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

theorem primrec_lcmCoef : Primrec lcmCoef :=
  primrec_rec₀ Term.primrec_absCoef (Term.primrec_absCoef.comp snd).to₂
    PrimrecArith.primrec_lcm PrimrecArith.primrec_lcm (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem primrec_lcmMod : Primrec lcmMod :=
  primrec_rec₀ (Primrec.const 1) (succ.comp fst).to₂ PrimrecArith.primrec_lcm
    PrimrecArith.primrec_lcm (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem primrec_norm : Primrec₂ QF.norm :=
  primrec_rec (primrec_le.comp (Term.primrec_scale.comp fst snd)).to₂
    (primrec_dvd.comp
      (nat_sub.comp (nat_mul.comp (Term.primrec_mult.comp fst (snd.comp snd))
        (succ.comp (fst.comp snd))) (Primrec.const 1))
      (Term.primrec_scale.comp fst (snd.comp snd)))
    (primrec_and.comp (fst.comp snd) (snd.comp snd))
    (primrec_or.comp (fst.comp snd) (snd.comp snd))
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

theorem primrec_minf : Primrec minf :=
  primrec_rec₀
    (Primrec.ite (PrimrecArith.primrecPred_zero_lt.comp Term.primrec_coef0) (Primrec.const tt)
      (Primrec.ite (PrimrecArith.primrecPred_lt_zero.comp Term.primrec_coef0)
        (Primrec.const ff) primrec_le))
    primrec_dvd primrec_and primrec_or (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)

theorem primrec_bset : Primrec bset :=
  primrec_rec₀
    (Primrec.ite (Primrec.eq.comp Term.primrec_coef0 (Primrec.const (-1)))
      (list_cons.comp Term.primrec_rest (Primrec.const [])) (Primrec.const []))
    (Primrec.const []).to₂ list_append list_append (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem primrec_cooper : Primrec cooper := by
  have hj : Primrec fun p : QF × ℕ => (((p.2 : ℕ) : ℤ)) :=
    PrimrecArith.primrec_natCast.comp snd
  have hleft : Primrec fun φ : QF => bigOr ((List.range φ.lcmMod).map fun j : ℕ =>
      φ.minf.subst (Term.ofInt ((j : ℤ) + 1))) :=
    primrec_bigOr.comp (list_map (list_range.comp primrec_lcmMod)
      (primrec_subst.comp (Term.primrec_ofInt.comp (PrimrecArith.primrec_add.comp hj
        (Primrec.const 1))) (primrec_minf.comp fst)).to₂)
  have hright : Primrec fun φ : QF => bigOr (φ.bset.flatMap fun b =>
      (List.range φ.lcmMod).map fun j : ℕ => φ.subst (b + Term.ofInt (j : ℤ))) :=
    primrec_bigOr.comp (list_flatMap primrec_bset
      (list_map (list_range.comp (primrec_lcmMod.comp fst))
        (primrec_subst.comp (Term.primrec_add.comp (snd.comp fst)
          (Term.primrec_ofInt.comp (PrimrecArith.primrec_natCast.comp snd)))
          (fst.comp fst)).to₂).to₂)
  exact (primrec_or.comp hleft hright).of_eq fun _ => rfl

theorem primrec_elim : Primrec elim := by
  have hL : Primrec fun φ : QF => φ.lcmCoef := primrec_lcmCoef
  exact (primrec_cooper.comp (primrec_and.comp (primrec_norm.comp hL Primrec.id)
    (primrec_dvd.comp (nat_sub.comp hL (Primrec.const 1))
      (Primrec.const (Term.var 0))))).of_eq fun _ => rfl

end QF

namespace PForm

theorem primrec_qe : Primrec qe :=
  primrec_rec₀ (QF.primrec_le) (QF.primrec_and.comp QF.primrec_le
    (QF.primrec_le.comp Term.primrec_neg))
    (Primrec.ite (Primrec.eq.comp fst (Primrec.const 0))
      (QF.primrec_and.comp (QF.primrec_le.comp snd)
        (QF.primrec_le.comp (Term.primrec_neg.comp snd)))
      (QF.primrec_dvd.comp (nat_sub.comp fst (Primrec.const 1)) snd)).to₂
    QF.primrec_neg QF.primrec_and QF.primrec_or QF.primrec_elim
    (QF.primrec_neg.comp (QF.primrec_elim.comp QF.primrec_neg))
    (fun _ => rfl) (fun _ => rfl) (fun k t => by cases k <;> rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem primrec_bound : Primrec bound :=
  have hl : Primrec fun t : Term => t.coeffs.length := list_length.comp Term.primrec_coeffs
  primrec_rec₀ hl hl (hl.comp snd).to₂ Primrec.id nat_max nat_max
    (nat_sub.comp Primrec.id (Primrec.const 1)) (nat_sub.comp Primrec.id (Primrec.const 1))
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem primrec_allN : Primrec₂ allN :=
  (nat_iterate fst snd (primrec_all.comp snd).to₂).to₂

theorem primrec_valid : Primrec valid :=
  QF.primrec_holds0.comp (primrec_qe.comp (primrec_allN.comp primrec_bound Primrec.id))

theorem primrec_sat : Primrec sat :=
  Primrec.not.comp (primrec_valid.comp primrec_not)

/-- **The decision procedure is computable.** -/
theorem computable_valid : Computable valid := primrec_valid.to_comp

theorem computable_sat : Computable sat := primrec_sat.to_comp

/-- **Validity in Presburger arithmetic is a computable predicate**: whether a formula is true
under every assignment of its free variables. -/
theorem computablePred_valid : ComputablePred (fun φ : PForm => ∀ v : ℕ → ℤ, φ.eval v) := by
  classical
  refine ⟨inferInstance, computable_valid.of_eq fun φ => ?_⟩
  rw [Bool.eq_iff_iff, valid_iff, decide_eq_true_iff]

/-- **Truth of Presburger sentences is a computable predicate**. -/
theorem computablePred_sentence :
    ComputablePred (fun φ : PForm => φ.bound = 0 ∧ φ.eval (fun _ => 0)) := by
  classical
  refine ⟨inferInstance, ?_⟩
  have h := (Primrec.and.comp (Primrec.eq.decide.comp primrec_bound (Primrec.const 0))
    primrec_valid).to_comp
  refine h.of_eq fun φ => ?_
  rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, valid_iff, decide_eq_true_iff]
  refine and_congr_right fun h0 => ⟨fun h => h _, fun h w => ?_⟩
  exact (eval_congr φ (fun i hi => by omega)).1 h

end PForm

end Cslib.Presburger
