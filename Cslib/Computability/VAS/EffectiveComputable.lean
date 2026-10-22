/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.EffectiveForm
public import Cslib.Computability.Presburger.Computable
public import Mathlib.Computability.Primrec.List

/-! # Computability of the certificate check

The translation of a code to a formula (`EffectiveForm`) is primitive recursive, hence so is the
certificate sentence `certForm`. With the decision procedure for Presburger arithmetic this shows
that the certificate check is a computable predicate.

## Main statements

- `Presburger.PForm.primrec_certForm`: the certificate sentence is a primitive recursive function
  of the instance and the code.
- `computablePred_certificate`: being a certificate is a computable predicate.
-/

@[expose] public section

namespace Cslib

namespace Presburger

open Primrec

theorem Term.primrec_var : Primrec Term.var :=
  (Term.primrec_mk.comp (Primrec.const 0) (list_append.comp
    (list_map list_range (Primrec.const 0).to₂) (Primrec.const [1]))).of_eq fun j => by
  simp [Term.var, List.map_const', List.length_range]

namespace PForm

theorem primrec_imp : Primrec₂ imp :=
  (primrec_or.comp (primrec_not.comp fst) snd).to₂

theorem primrec_eq' : Primrec₂ eq' :=
  (primrec_eq.comp (Term.primrec_sub.comp fst snd)).to₂

theorem primrec_exNat : Primrec exNat :=
  primrec_ex.comp (primrec_and.comp (Primrec.const nonneg) Primrec.id)

theorem primrec_allNat : Primrec allNat :=
  primrec_all.comp (primrec_imp.comp (Primrec.const nonneg) Primrec.id)

theorem primrec_exsNat : Primrec₂ exsNat :=
  (nat_iterate fst snd (primrec_exNat.comp snd).to₂).to₂

theorem primrec_allsNat : Primrec₂ allsNat :=
  (nat_iterate fst snd (primrec_allNat.comp snd).to₂).to₂

theorem primrec_bigOr : Primrec bigOr :=
  list_foldr Primrec.id (Primrec.const ff)
    (primrec_or.comp (fst.comp snd) (snd.comp snd)).to₂

theorem primrec_bigAnd : Primrec bigAnd :=
  list_foldr Primrec.id (Primrec.const tt)
    (primrec_and.comp (fst.comp snd) (snd.comp snd)).to₂

theorem primrec_andRange {α : Type*} [Primcodable α] {d : α → ℕ} {f : α → ℕ → PForm}
    (hd : Primrec d) (hf : Primrec₂ f) : Primrec fun a => andRange (d a) (f a) :=
  primrec_bigAnd.comp (list_map (list_range.comp hd) hf)

theorem primrec_linTerm : Primrec₂ linTerm := by
  have hneg : Primrec fun n : ℕ => -(n : ℤ) :=
    PrimrecArith.primrec_neg.comp PrimrecArith.primrec_natCast
  have hps : Primrec fun p : (List ℕ × List (List ℕ)) × ℕ => p.1.2 := snd.comp fst
  exact Term.primrec_add.comp
    (Term.primrec_mk.comp (hneg.comp ((list_getD 0).comp (fst.comp fst) snd))
      (list_map hps (hneg.comp ((list_getD 0).comp snd (snd.comp fst))).to₂))
    (Term.primrec_var.comp (nat_add.comp (list_length.comp hps) snd))

theorem primrec_linForm : Primrec₂ linForm :=
  primrec_exsNat.comp (list_length.comp (snd.comp snd))
    (primrec_andRange fst (primrec_eq.comp (primrec_linTerm.comp (snd.comp fst) snd)).to₂)

theorem primrec_setForm : Primrec₂ setForm :=
  primrec_bigOr.comp (list_map snd (primrec_linForm.comp (fst.comp fst) snd).to₂)

theorem primrec_stepEq : Primrec₂ stepEq :=
  primrec_andRange fst (primrec_eq'.comp (Term.primrec_var.comp snd)
    (Term.primrec_add.comp (Term.primrec_var.comp (nat_add.comp (fst.comp fst) snd))
      (Term.primrec_ofInt.comp ((list_getD 0).comp (snd.comp fst) snd)))).to₂

theorem primrec_stepForm : Primrec fun p : (ℕ × SLCode) × List ℤ => stepForm p.1.1 p.1.2 p.2 := by
  have hd : Primrec fun p : (ℕ × SLCode) × List ℤ => p.1.1 := fst.comp fst
  have hr : Primrec fun p : (ℕ × SLCode) × List ℤ => p.1.2 := snd.comp fst
  have h := primrec_setForm.comp hd hr
  exact primrec_imp.comp h (primrec_allsNat.comp hd
    (primrec_imp.comp (primrec_stepEq.comp hd snd) h))

theorem primrec_inductiveForm : Primrec₂ inductiveForm :=
  primrec_allsNat.comp (fst.comp fst) (primrec_bigAnd.comp (list_map (snd.comp fst)
    (primrec_stepForm.comp (Primrec.pair (Primrec.pair (fst.comp (fst.comp fst)) (snd.comp fst))
      snd)).to₂))

theorem primrec_eqConst : Primrec₂ eqConst :=
  primrec_andRange fst (primrec_eq'.comp (Term.primrec_var.comp snd)
    (Term.primrec_ofInt.comp (PrimrecArith.primrec_natCast.comp
      ((list_getD 0).comp (snd.comp fst) snd)))).to₂

theorem primrec_certForm : Primrec fun p : (VASCode × List ℕ × List ℕ) × SLCode =>
    certForm p.1.1 p.1.2.1 p.1.2.2 p.2 := by
  have hc : Primrec fun p : (VASCode × List ℕ × List ℕ) × SLCode => p.1.1 := fst.comp fst
  have hd : Primrec fun p : (VASCode × List ℕ × List ℕ) × SLCode => p.1.1.1 := fst.comp hc
  have hx : Primrec fun p : (VASCode × List ℕ × List ℕ) × SLCode => p.1.2.1 :=
    fst.comp (snd.comp fst)
  have hy : Primrec fun p : (VASCode × List ℕ × List ℕ) × SLCode => p.1.2.2 :=
    snd.comp (snd.comp fst)
  have h := primrec_setForm.comp hd snd
  exact primrec_and.comp (primrec_inductiveForm.comp hc snd) (primrec_allsNat.comp hd
    (primrec_and.comp (primrec_imp.comp (primrec_eqConst.comp hd hx) h)
      (primrec_imp.comp (primrec_eqConst.comp hd hy) (primrec_not.comp h))))

end PForm

end Presburger

open Presburger in
/-- **The certificate check is computable.** Whether a list of codes of linear sets is a
certificate that `y` is not reachable from `x` in the coded VAS is a computable predicate. -/
theorem computablePred_certificate :
    ComputablePred fun p : (VASCode × List ℕ × List ℕ) × SLCode =>
      p.1.1.Certificate p.1.2.1 p.1.2.2 p.2 := by
  classical
  refine ⟨inferInstance, ?_⟩
  refine (PForm.primrec_valid.comp PForm.primrec_certForm).to_comp.of_eq fun p => ?_
  rw [Bool.eq_iff_iff, PForm.valid_certForm_iff, decide_eq_true_iff]

end Cslib
