/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Init
public meta import Lean.Elab.Term

/-! # Elaborating the net in Petri net notation

Lean can insert a coercion only if the target type is fully known. The type `PetriNet Place
Transition` of the net slot in the notations `M [t⟩[N] M'` and `M ⇝[N] M'` is not known before the
net is elaborated, so no coercion from another kind of net, such as `ExecPetriNet`, can be inserted.

The elaborator `net% N` instead elaborates `N`, leaves it unchanged if it is a `PetriNet`, and
otherwise applies the instance of the class `PetriNet.ToPetriNet`, whose type arguments are
`outParam`s and hence found by instance search. The result is unfolded to the underlying function,
so that `net% N` is `N.toPetriNet` when `N` is an executable net.
-/

public meta section

namespace Cslib.PetriNet

open Lean Elab Term Meta

/-- `net% N` elaborates `N` as a Petri net, applying `ToPetriNet.toPetriNet` if `N` is not
one. -/
scoped elab "net% " t:term : term => do
  let e ← elabTerm t none
  let ty ← instantiateMVars (← inferType e)
  tryPostponeIfMVar ty
  let ty ← whnfR ty
  if ty.isAppOf `Cslib.PetriNet then
    return e
  else
    let r ← mkAppM `Cslib.PetriNet.ToPetriNet.toPetriNet #[e]
    withTransparency .instances (whnf r)

end Cslib.PetriNet
