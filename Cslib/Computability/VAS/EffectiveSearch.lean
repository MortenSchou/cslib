/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.EffectiveComputable
public import Mathlib.Computability.RE
public import Mathlib.Computability.Partrec

/-! # The search for certificates of non-reachability

Whether a list of codes is a certificate that a target is not reachable in a coded VAS is
computable (`computablePred_certificate`), so the existence of a certificate is recursively
enumerable: enumerate the codes and check each of them. Leroux's theorem, that a certificate exists
whenever the target is not reachable, is combined with this in `Cslib.Computability.VAS.Decidable`.

## Main definitions

- `ReachInput`, `ReachInput.Reaches`: an instance of reachability for coded VAS.

## Main statements

- `rePred_exists_of_computablePred`: the existential projection of a computable predicate is r.e.
- `rePred_exists_certificate`: the existence of a certificate of non-reachability is r.e.
-/

@[expose] public section

namespace Cslib

/-- The existential projection of a computable predicate over a `Primcodable` type is
recursively enumerable: search through the values in the order of their codes. -/
theorem rePred_exists_of_computablePred {α β : Type*} [Primcodable α] [Primcodable β]
    {R : α → β → Prop} (hR : ComputablePred fun p : α × β => R p.1 p.2) :
    REPred fun a => ∃ b, R a b := by
  classical
  have hf : Computable₂ fun (a : α) (n : ℕ) => (Encodable.decode (α := β) n).bind
      fun b => bif decide (R a b) then some () else none :=
    Computable.option_bind (Computable.decode.comp Computable.snd)
      (Computable.cond (hR.decide.comp (Computable.pair (Computable.fst.comp Computable.fst)
        Computable.snd)) (Computable.const (some ())) (Computable.const none)).to₂
  refine (Partrec.rfindOpt hf).dom_re.of_eq fun a => ?_
  rw [Nat.rfindOpt_dom]
  constructor
  · rintro ⟨n, u, h⟩
    cases hn : Encodable.decode (α := β) n <;> grind
  · rintro ⟨b, hb⟩
    exact ⟨Encodable.encode b, (), by simp [hb]⟩

/-- An instance of reachability for coded VAS: a code of a VAS, a source and a target. -/
abbrev ReachInput := VASCode × List ℕ × List ℕ

/-- The target is reachable from the source in the coded VAS. -/
def ReachInput.Reaches (p : ReachInput) : Prop :=
  p.1.toVAS.Reach (vecN p.1.1 p.2.1) (vecN p.1.1 p.2.2)

/-- The existence of a coded certificate of non-reachability is recursively enumerable. -/
theorem rePred_exists_certificate :
    REPred fun p : ReachInput => ∃ r : SLCode, p.1.Certificate p.2.1 p.2.2 r :=
  rePred_exists_of_computablePred (R := fun (p : ReachInput) (r : SLCode) =>
    p.1.Certificate p.2.1 p.2.2 r) computablePred_certificate

end Cslib
