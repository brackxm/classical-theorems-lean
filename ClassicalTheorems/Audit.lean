/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import Lean.Elab.Command
import Lean.Meta.InferType
import Lean.Util.CollectAxioms

/-! Check an upstream declaration and reject unfinished proofs or extra axioms. -/

open Lean Elab Command in
elab "#check_upstream " declaration:ident : command => do
  let name ← resolveGlobalConstNoOverload declaration
  let axioms ← collectAxioms name
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let unexpected := axioms.filter fun dependency => !allowed.contains dependency
  unless unexpected.isEmpty do
    throwError "{name} uses unapproved axioms: {unexpected}"
  logInfo m!"Checked {name}; axioms: {axioms}"

/-! An indexed proof must prove a proposition, not merely name a definition. -/

open Lean Elab Command in
elab "#check_indexed " declaration:ident : command => do
  let name ← resolveGlobalConstNoOverload declaration
  liftTermElabM do
    let info ← getConstInfo name
    unless ← Meta.isProp info.type do
      throwError "{name} is not a proof of a proposition"
  elabCommand (← `(#check_upstream $declaration))
