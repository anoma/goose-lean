import Lean

open Lean Elab Command Meta Term

/-- Option to control whether see commands use `dbg_trace` (true) or `logInfo` (false) -/
register_option see.useDbgTrace : Bool := {
  defValue := true
  group := "debug"
  descr := "When true, see commands use dbg_trace
  (console output). When false (default),
  uses logInfo (IDE output)."
}

/-- Option to control whether see commands show file paths and positions -/
register_option see.showPosition : Bool := {
  defValue := false
  group := "debug"
  descr := "When true (default), see commands show
  file path and position (filename:line:column).
  When false, only shows the message."
}

/-- Option to filter messages by prefix patterns (comma-separated list) -/
register_option see.filterPrefixes : String := {
  defValue := ""
  group := "debug"
  descr := "Comma-separated list of message prefixes to allow.
  Empty string (default) means show all messages.
  Example: '[Parser],[Elab]' shows only Parser and Elab messages."
}

/-- Option to exclude messages by prefix patterns (comma-separated list) -/
register_option see.excludePrefixes : String := {
  defValue := ""
  group := "debug"
  descr := "Comma-separated list of message prefixes to exclude.
  Empty string (default) means exclude nothing.
  Example: '[Parser]' hides all Parser messages."
}

/-- Check if a string contains a substring -/
def stringContains (s : String) (substr : String) : Bool :=
  (s.splitOn substr).length > 1

/-- Check if a message should be shown based on filter/exclude prefix options -/
def shouldShowMessage (msgStr : String) (filterPrefixes excludePrefixes : String) : Bool :=
  -- Parse comma-separated lists
  let filters := if filterPrefixes.isEmpty then [] else filterPrefixes.splitOn ","
  let excludes := if excludePrefixes.isEmpty then [] else excludePrefixes.splitOn ","

  -- If there are exclude patterns, check if message matches any of them
  let isExcluded := excludes.any (fun pfx => stringContains msgStr pfx.trim)
  if isExcluded then false
  else
    -- If there are filter patterns, only show if message matches at least one
    if filters.isEmpty then
      true  -- No filters means show everything (that's not excluded)
    else
      filters.any (fun pfx => stringContains msgStr pfx.trim)

/--
Internal helper function for conditional output with position tracking.
This is called by the `seeThis` macro with the call site syntax.
Outputs format:
`filename:line:column: message` (when see.showPosition is true)
-/
def seeThisImpl
  [Monad m]
  [MonadOptions m]
  [MonadLog m]
  [AddMessageContext m]
  [MonadFileMap m]
  [MonadEnv m]
  (msg : Format)
  (posNum : Nat)
  : m Unit := do
  let opts ← getOptions
  let useDbgTrace := see.useDbgTrace.get opts
  let showPosition := see.showPosition.get opts
  let filterPrefixes := see.filterPrefixes.get opts
  let excludePrefixes := see.excludePrefixes.get opts

  -- Filter based on message prefix patterns
  let msgStr := msg.pretty
  if !shouldShowMessage msgStr filterPrefixes excludePrefixes then
    return ()

  -- Conditionally add position information in VSCode-compatible format
  let fullMsg ← if showPosition then do
    let fileMap ← getFileMap
    let pos : String.Pos := ⟨posNum⟩
    let position := fileMap.toPosition pos
    let env ← getEnv
    let fileName := env.mainModule.toString.replace "." "/"
    let posInfo := s!"{fileName}.lean:{position.line}:{position.column}: "
    pure f!"{posInfo}{msg}"
  else
    pure msg

  if useDbgTrace then
    dbg_trace fullMsg
  else
    logInfo (MessageData.ofFormat fullMsg)

/--
Macro that captures the call site position and outputs a message.
Uses `logInfo` by default (IDE output), or `dbg_trace` if `see.useDbgTrace` is set to true.

Works in CommandElabM, MetaM, TermElabM, and other monads with the required type classes.
This is the function-level equivalent of the `#see` command.

The position shown will be exactly where `seeThis` is called in your code.
-/
macro "seeThis" msg:term : doElem =>
  let pos := msg.raw.getPos?.getD 0
  `(doElem| seeThisImpl $msg $(quote pos.byteIdx))

/-- The `#see` command: conditional output based on `see.useDbgTrace` option.
    Includes source position information (when see.showPosition is true).
    Uses the same implementation as `seeThis` for consistency. -/
elab "#see" e:term : command => do
  -- Get position of the #see command
  let stx ← getRef
  let pos := stx.getPos?.getD 0

  -- Elaborate the term to get its value
  let e ← liftTermElabM do
    let e ← elabTerm e none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e

  -- Use the same implementation as seeThis
  seeThisImpl (format e) pos.byteIdx
