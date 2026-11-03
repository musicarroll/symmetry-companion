import SymmetryMonograph
import Lean.Util.CollectAxioms

open Lean Elab Command
open SymmetryMonograph.BookIndex

/- Resolve the ledger against the elaborated environment. Audit every theorem
in the project's namespace, including theorems not named in the ledger. -/
run_cmd do
  let env ← getEnv
  for s in statements do
    if s.status == .complete && s.leanNames.isEmpty then
      throwError "Complete entry has no declarations: {s.labelOrTitle}"
    for str in s.leanNames do
      unless env.contains str.toName do
        throwError "Unknown ledger declaration: {str}"
  for (name, info) in env.constants.toList do
    if (`SymmetryMonograph).isPrefixOf name then
      if let .thmInfo _ := info then
        for ax in ← collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Unapproved axiom {ax} in {name}"

def statusName : FormalizationStatus → String
  | .complete => "complete"
  | .partiallyComplete => "partiallyComplete"
  | .formalizableNow => "formalizableNow"
  | .needsDefinitions => "needsDefinitions"
  | .analyticHeavy => "analyticHeavy"
  | .computationalOnly => "computationalOnly"
  | .externallyCited => "externallyCited"
  | .compatibilityCondition => "compatibilityCondition"
  | .researchProgram => "researchProgram"

def statementJson (s : BookStatement) : Json := Json.mkObj [
  ("kind", toJson s.kind), ("source", toJson s.source),
  ("title", toJson s.labelOrTitle), ("label", toJson s.bookLabel),
  ("category", toJson s.category), ("scope", toJson s.scope),
  ("leanNames", toJson s.leanNames), ("status", toJson (statusName s.status))]

#eval IO.println ((toJson (statements.map statementJson)).compress)
