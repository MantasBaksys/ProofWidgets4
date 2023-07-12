import Lean.Elab.Calc
import Lean.Elab.Tactic.ElabTerm
import Lean.Meta.ExprLens

import Std.Lean.Position
import Std.CodeAction

import ProofWidgets.Compat
import ProofWidgets.Component.Panel

open ProofWidgets
open Lean Meta

@[widget_module]
def CalcPanel : Component PanelWidgetProps where
  javascript := include_str "build" / "js" / "calcPanel.js"


structure CalcPanelProps where
  help : String
  callback : String
  /-- The range to be replaced. -/
  replaceRange : Lsp.Range
  /-- If this the first calc step? -/
  isFirst : Bool
  deriving FromJson, ToJson

open Lean Server in
/-- Parameter for a widget callback that will insert a tactic call after selecting things in
the tactic state. -/
structure CalcParams where
  /-- The current cursor position. -/
  cursorPos : Lsp.Position
  /-- The current context information. -/
  ctx : WithRpcRef Elab.ContextInfo
  /-- The locations selected in the tactic state. -/
  selectedLocations : Array SubExpr.GoalsLocation
  /-- The range in the source document where the result will be inserted. -/
  replaceRange : Lsp.Range
  /-- If this the first calc step? -/
  isFirst : Bool
  deriving RpcEncodable

/-- Response for a widget callback that will insert a tactic call after selecting things in
the tactic state. -/
structure CalcResponse where
  /-- The tactic call to be displayed in the panel. -/
  content : String
  /-- The edit to perform on the file. -/
  edit : Lsp.WorkspaceEdit
  /-- Where to place the cursor after the edit. It is always in the same file. -/
  newCursorPos : Lsp.Position
  deriving FromJson, ToJson

def Lean.SubExpr.GoalLocation.target! : Lean.SubExpr.GoalLocation → SubExpr.Pos
| .target pos => pos
| _ => panic! "You must select part of the goal."

open Lean Meta

def insertMetaVar (e : Expr) (pos  : SubExpr.Pos) : MetaM Expr :=
replaceSubexpr (fun _ ↦  do mkFreshExprMVar none .synthetic) pos e

def String.renameMetaVar (s : String) : String :=
  match s.splitOn "?m." with
  | [] => ""
  | [s] => s
  | head::tail => head ++ "?_" ++ "?_".intercalate (tail.map fun s ↦ s.dropWhile Char.isDigit)

def Lean.Expr.relStr : Expr → String
| .const ``Eq _ => "="
| .const ``LE.le _ => "≤"
| .const ``LT.lt _ => "<"
| .const ``GE.ge _ => "≥"
| .const ``GT.gt _ => ">"
| _ => "Unknow relation"

/-- Return the button text and inserted text above and below.-/
def mkCalcStr (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr) (isFirst : Bool) :
    MetaM (String × String) := do
  let subexprPos := pos.map (·.loc.target!)
  let goalType := goalType.consumeMData
  let some (rel, lhs, rhs) ← Lean.Elab.Term.getCalcRelation? goalType |
      throwError "invalid 'calc' step, relation expected{indentExpr goalType}"
  let relStr := rel.getAppFn.relStr
  let selectedLeft := subexprPos.filter (fun L ↦ #[0, 1].isPrefixOf L.toArray)
  let selectedRight := subexprPos.filter (fun L ↦ #[1].isPrefixOf L.toArray)

  let mut goalTypeWithMetaVarsLeft := goalType
  for pos in selectedLeft do
    goalTypeWithMetaVarsLeft ← insertMetaVar goalTypeWithMetaVarsLeft pos
  let some (_, newLhs, _) ← Lean.Elab.Term.getCalcRelation? goalTypeWithMetaVarsLeft | unreachable!
  let mut goalTypeWithMetaVarsRight := goalType
  for pos in selectedRight do
    goalTypeWithMetaVarsRight ← insertMetaVar goalTypeWithMetaVarsRight pos
  let some (_, _, newRhs) ← Lean.Elab.Term.getCalcRelation? goalTypeWithMetaVarsRight | unreachable!

  let lhsStr := (toString <| ← Meta.ppExpr lhs).renameMetaVar
  let newLhsStr := (toString <| ← Meta.ppExpr newLhs).renameMetaVar
  let rhsStr := (toString <| ← Meta.ppExpr rhs).renameMetaVar
  let newRhsStr := (toString <| ← Meta.ppExpr newRhs).renameMetaVar

  let insertedCode := match selectedLeft.isEmpty, selectedRight.isEmpty with
  | false, false =>
    if isFirst then
      s!"{lhsStr} {relStr} {newLhsStr} := by sorry\n_ {relStr} {newRhsStr} := by sorry\n_ {relStr} {rhsStr} := by sorry"
    else
      s!"_ {relStr} {newLhsStr} := by sorry\n_ {relStr} {newRhsStr} := by sorry\n_ {relStr} {rhsStr} := by sorry"
  | true, false  =>
  if isFirst then
      s!"{lhsStr} {relStr} {newRhsStr} := by sorry\n_ {relStr} {rhsStr} := by sorry"
    else
      s!"_ {relStr} {newRhsStr} := by sorry\n_ {relStr} {rhsStr} := by sorry"
  | false, true =>
    if isFirst then
      s!"{lhsStr} {relStr} {newLhsStr} := by sorry\n_ {relStr} {rhsStr} := by sorry"
    else
      s!"_ {relStr} {newLhsStr} := by sorry\n_ {relStr} {rhsStr} := by sorry"
  | true, true => "This should not happen"

  let stepInfo := match selectedLeft.isEmpty, selectedRight.isEmpty with
  | false, false => "Create two new steps"
  | true, false  => "Create a new step"
  | false, true => "Create a new step"
  | true, true => "This should not happen"
  return (stepInfo, toString insertedCode)

open Lean Server in
@[server_rpc_method]
def calcCommand : CalcParams → RequestM (RequestTask (Option CalcResponse))
| ⟨cursorPos, ⟨ctx⟩, selectedLocations, replaceRange, isFirst⟩ =>
    RequestM.withWaitFindSnapAtPos cursorPos fun _ => do
      let some firstLoc := selectedLocations[0]? | return none
      let doc ← RequestM.readDoc
      ctx.runMetaM {} do
        let md ← firstLoc.mvarId.getDecl
        let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
        Meta.withLCtx lctx md.localInstances do
          let (buttonText, insertedCode) ← mkCalcStr selectedLocations md.type isFirst
          let textDocumentEdit : Lsp.TextDocumentEdit := {
            textDocument := { uri := doc.meta.uri, version? := doc.meta.version },
            edits        := #[{range := replaceRange, newText := insertedCode }] }
          return some { content := buttonText,
                        edit := Lsp.WorkspaceEdit.ofTextDocumentEdit textDocumentEdit,
                        /- CHECKME: the new cursor position computation below looks very naive.
                           Will it work with non-ascii insertedCode? -/
                        newCursorPos := {line := replaceRange.start.line,
                                         character := replaceRange.start.character + insertedCode.length } }

section code_action
open Std CodeAction
open Lean Server RequestM

@[tactic_code_action calcTactic]
def createCalc : TacticCodeAction := fun params _snap ctx _stack node => do
  let .node (.ofTacticInfo info) _ := node | return #[]
  if info.goalsBefore.isEmpty then return #[]
  let eager := {
    title := s!"Generate a calc block."
    kind? := "quickfix"
  }
  let doc ← readDoc
  return #[{
    eager
    lazy? := some do
      let tacPos := doc.meta.text.utf8PosToLspPos info.stx.getPos?.get!
      let endPos := doc.meta.text.utf8PosToLspPos info.stx.getTailPos?.get!
      let goal := info.goalsBefore[0]!
      let goalFmt ← ctx.runMetaM {} <| goal.withContext do Meta.ppExpr (← goal.getType)
      return { eager with
        edit? := some <|.ofTextEdit params.textDocument.uri
          { range := ⟨tacPos, endPos⟩, newText := s!"calc {goalFmt} := by sorry" }
      }
  }]
end code_action

namespace Lean.Elab.Term
open Meta

def getCalcFirstStep' (step0 : TSyntax ``calcFirstStep) : TermElabM (TSyntax ``calcStep) :=
  withRef step0 do
  match step0  with
  | `(calcFirstStep| $term:term) =>
    `(calcStep| $term = _ := rfl)
  | `(calcFirstStep| $term := $proof) =>
    `(calcStep| $term := $proof)
  | _ => throwUnsupportedSyntax

def getCalcSteps' (steps : TSyntax ``calcSteps) : TermElabM (Array (TSyntax ``calcStep)) :=
  match steps with
  | `(calcSteps| $step0:calcFirstStep $rest*) => do
    let step0 ← getCalcFirstStep' step0
    pure (#[step0] ++ rest)
  | _ => unreachable!

def myElabCalcSteps (steps : TSyntax ``calcSteps) : TermElabM Expr := do
  let mut result? := none
  let mut prevRhs? := none
  let mut isFirst := true
  for step in ← getCalcSteps' steps do

    let `(calcStep| $pred := $proofTerm) := step | unreachable!
    let type ← elabType <| ← do
      if let some prevRhs := prevRhs? then
        annotateFirstHoleWithType pred (← inferType prevRhs)
      else
        pure pred
    let some (_, lhs, rhs) ← getCalcRelation? type |
      throwErrorAt pred "invalid 'calc' step, relation expected{indentExpr type}"

    let some replaceRange := (← getFileMap).rangeOfStx? step | unreachable!
    let props : CalcPanelProps := ⟨"Please select part of the goal", "calcCommand", replaceRange, isFirst⟩

    ProofWidgets.savePanelWidgetInfo proofTerm `CalcPanel (pure <| toJson props)
    isFirst := false

    if let some prevRhs := prevRhs? then
      unless (← isDefEqGuarded lhs prevRhs) do
        throwErrorAt pred "invalid 'calc' step, left-hand-side is{indentD m!"{lhs} : {← inferType lhs}"}\nprevious right-hand-side is{indentD m!"{prevRhs} : {← inferType prevRhs}"}" -- "
    let proof ← withFreshMacroScope do elabTermEnsuringType proofTerm type
    result? := some <| ← do
      if let some (result, resultType) := result? then
        synthesizeSyntheticMVarsUsingDefault
        withRef pred do mkCalcTrans result resultType proof type
      else
        pure (proof, type)
    prevRhs? := rhs
  return result?.get!.1
end Lean.Elab.Term


namespace Lean.Elab.Tactic
open Meta

/-- Elaborator for the `calc` tactic mode variant. -/
elab_rules : tactic
| `(tactic|calc $stx) => withMainContext do
  let steps : TSyntax ``calcSteps := ⟨stx⟩
  let (val, mvarIds) ← withCollectingNewGoalsFrom (tagSuffix := `calc) do
    let target ← getMainTarget
    let tag ← getMainTag
    runTermElab do
    let mut val ← Term.myElabCalcSteps steps
    let mut valType ← inferType val
    unless (← isDefEq valType target) do
      let rec throwFailed :=
        throwError "'calc' tactic failed, has type{indentExpr valType}\nbut it is expected to have type{indentExpr target}"
      let some (_, _, rhs) ← Term.getCalcRelation? valType | throwFailed
      let some (r, _, rhs') ← Term.getCalcRelation? target | throwFailed
      let lastStep := mkApp2 r rhs rhs'
      let lastStepGoal ← mkFreshExprSyntheticOpaqueMVar lastStep (tag := tag ++ `calc.step)
      (val, valType) ← Term.mkCalcTrans val valType lastStepGoal lastStep
      unless (← isDefEq valType target) do throwFailed
    return val
  (← getMainGoal).assign val
  replaceMainGoal mvarIds


example {a b : Nat} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 := by
sorry


example (a b c d e : Nat) (h₁ : a = b) (h₂ : b = c) (h₃ : c = d) (h₄ : d = e): a + d = e + d := by
calc a + d = e + d := by sorry

/-
calc a + d
  = b + d := by rw [h₁]
_ = c + d := by rw [h₂]
_ = d + d  := by rw [h₃]
_ = e + d := by rw [h₄]
-/
