/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Util.AssertNoSorry

/-!
# Kernel-level project axiom audit

This module defines the command used at the end of `YangMills.lean`. It asks Lean for the transitive
axioms of every declaration in the `YangMills` namespace and rejects `sorryAx` or any axiom declared
inside that namespace. This complements, but does not replace, the fast source scan.
-/

public meta section

open Lean Elab Command

namespace YangMills.Audit

/-- Audit every loaded declaration in the `YangMills` namespace for proof placeholders and project
axioms. Invoke this only after importing all production modules. -/
elab "audit_yang_mills_axioms" : command => do
  let declarations := (← getEnv).constants.toList.filter fun (name, _) =>
    (`YangMills).isPrefixOf name
  if declarations.isEmpty then
    throwError "the YangMills namespace contains no declarations to audit"
  let mut audited := 0
  for (name, _) in declarations do
    let axioms ← Lean.collectAxioms name
    if axioms.contains ``sorryAx then
      throwError "{name} transitively depends on sorryAx"
    let projectAxioms := axioms.toList.filter fun axiomName =>
      (`YangMills).isPrefixOf axiomName
    unless projectAxioms.isEmpty do
      throwError "{name} transitively depends on project axiom(s): {projectAxioms}"
    audited := audited + 1
  logInfo m!"PASS kernel-audited {audited} YangMills declaration(s)"

end YangMills.Audit
