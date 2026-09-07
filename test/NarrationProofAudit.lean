-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
import Gnpl.Core
import Lean

-- Lean itself audits the transitive assumptions. Any additional axiom changes
-- the diagnostic and fails the build. propext is Lean's propositional extensionality.
/-- info: 'Gnpl.narrate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Gnpl.narrate

/-- info: 'Gnpl.withdrawn_cannot_support' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Gnpl.withdrawn_cannot_support

/-- info: 'Gnpl.narration_preserves_projection' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Gnpl.narration_preserves_projection
