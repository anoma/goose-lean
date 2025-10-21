import Prelude
import Lean

open Lean Elab Command

/-! # Tests for `#see` and `seeThis` debugging utilities

Enhanced with position tracking: each output includes `filename:line:column:` by default.
Use `set_option see.showPosition false` to hide positions and get clean output.
-/

/-! ## Basic `#see` command tests (with position tracking) -/

#see "Hello, world!"
#see 1 + 1
#see [1, 2, 3, 4, 5]

/-! ## Output mode: scoped dbg_trace -/

set_option see.useDbgTrace true in
#see "Scoped dbg_trace output"

#see "Back to default logInfo"

/-! ## Output mode: global dbg_trace -/

set_option see.useDbgTrace true

#see "Now using dbg_trace globally"
#see 42 * 37
#see ("tuple", 123)

set_option see.useDbgTrace false

#see "Back to logInfo for IDE"
#see true && false

/-! ## `seeThis` in monadic code -/

def exampleFunction1 : CommandElabM Unit := do
  seeThis f!"Starting example function 1"
  seeThis f!"Processing step 1"
  seeThis f!"Processing step 2"
  seeThis f!"Completed"

#eval exampleFunction1

def processItems (items : List String) : CommandElabM Unit := do
  seeThis f!"Processing {items.length} items"
  for item in items do
    seeThis f!"  - Processing item: {item}"
  seeThis f!"All items processed"

#eval processItems ["foo", "bar", "baz"]

/-! ## Option-controlled output -/

def testDefault : CommandElabM Unit := do
  seeThis f!"This uses logInfo by default"

#eval testDefault

def testWithTrace : CommandElabM Unit := do
  seeThis f!"This uses dbg_trace when option is set"

set_option see.useDbgTrace true in
#eval testWithTrace

/-! ## Simulated elaborator workflow -/

def mockElaborator (className : String) (methodCount : Nat) : CommandElabM Unit := do
  seeThis f!"[Elab] Starting elaboration of class {className}"
  seeThis f!"[Elab] Found {methodCount} methods"
  for i in [0:methodCount] do
    seeThis f!"[Elab]   - Elaborating method #{i + 1}"
  seeThis f!"[Elab] Successfully elaborated {className}"

#eval mockElaborator "MyClass" 3

/-! ## Multi-line message tests -/

def testMultiLine : CommandElabM Unit := do
  seeThis f!"Line 1
Line 2
Line 3"
  seeThis f!"Step 1: Starting process
  Step 2: Processing data
  Step 3: Finalizing"

#eval testMultiLine

/-! ## Position display control -/

-- Default: position shown
#see "With position (default)"

-- Hide position for clean output
set_option see.showPosition false in
#see "Without position - clean!"

-- Scoped hide for function
set_option see.showPosition false
def cleanOutput : CommandElabM Unit := do
  seeThis f!"Clean message 1"
  seeThis f!"Clean message 2"

#eval cleanOutput

-- Position shown again (option was scoped)
#see "Position is back"
