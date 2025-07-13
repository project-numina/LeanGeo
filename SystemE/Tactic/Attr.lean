import Lean
import Smt.Translate
import Smt.Real
import Smt.Translate.Commands
import SystemE.Tactic.EQuery
-- import SystemE.Tactic.Translate
import Smt

open Lean Meta Elab Command

open Smt.Translate.Query

initialize diagExtension : LabelExtension ← registerLabelAttr `diag "System E diagrammatic inference axiom"
initialize metricExtension : LabelExtension ← registerLabelAttr `metric "System E metric inference axiom"
initialize superExtension : LabelExtension ← registerLabelAttr `super "System E superposition inference axiom"
initialize transferExtension : LabelExtension ← registerLabelAttr `transfer "System E transfer inference axiom"

abbrev EuclidExtension := SimpleScopedEnvExtension (QueryBuilderM.State × List Expr × List Smt.Translate.Command) (QueryBuilderM.State × List Expr × List Smt.Translate.Command)

instance : Inhabited Smt.Translate.Command :=
  ⟨Smt.Translate.Command.exit⟩

#check ConstantInfo.levelParams
#check getConstInfo
#check ConstantInfo.type
#check Smt.Translator.applyTranslators!
#check IO.processCommands
#check registerSimpAttr

instance : Inhabited QueryBuilderM.State :=
  ⟨{ : QueryBuilderM.State }⟩

def Smt.Term.beq : Smt.Term → Smt.Term → Bool
| .literalT s₁, .literalT s₂ => s₁ == s₂
| .symbolT s₁, .symbolT s₂ => s₁ == s₂
| .arrowT a₁ b₁, .arrowT a₂ b₂ => beq a₁ a₂ && beq b₁ b₂
| .appT f₁ x₁, .appT f₂ x₂ => beq f₁ f₂ && beq x₁ x₂
| .forallT n₁ t₁ b₁, .forallT n₂ t₂ b₂ => n₁ == n₂ && beq t₁ t₂ && beq b₁ b₂
| .existsT n₁ t₁ b₁, .existsT n₂ t₂ b₂ => n₁ == n₂ && beq t₁ t₂ && beq b₁ b₂
| .letT n₁ v₁ b₁, .letT n₂ v₂ b₂ => n₁ == n₂ && beq v₁ v₂ && beq b₁ b₂
| _, _ => false

instance : BEq Smt.Term :=
  ⟨Smt.Term.beq⟩


instance : BEq Smt.Translate.Command where
  beq
    | .setLogic l₁, .setLogic l₂ => l₁ == l₂
    | .setOption k₁ v₁, .setOption k₂ v₂ => k₁ == k₂ && v₁ == v₂
    | .declareSort nm₁ ar₁, .declareSort nm₂ ar₂ => nm₁ == nm₂ && ar₁ == ar₂
    | .defineSort nm₁ ps₁ tm₁, .defineSort nm₂ ps₂ tm₂ => nm₁ == nm₂ && ps₁ == ps₂ && tm₁ == tm₂
    | .declare nm₁ st₁, .declare nm₂ st₂ => nm₁ == nm₂ && st₁ == st₂
    | .defineFun nm₁ ps₁ cod₁ tm₁ rec₁, .defineFun nm₂ ps₂ cod₂ tm₂ rec₂ =>
        nm₁ == nm₂ && ps₁ == ps₂ && cod₁ == cod₂ && tm₁ == tm₂ && rec₁ == rec₂
    | .assert tm₁, .assert tm₂ => tm₁ == tm₂
    | .checkSat, .checkSat => true
    | .getModel, .getModel => true
    | .getProof, .getProof => true
    | .exit, .exit => true
    | _, _ => false



def registerEuclidAttr (attrName : Name) (attrDescr : String)
  (ref : Name := by exact decl_name%) : IO EuclidExtension := do
  let ext : EuclidExtension ← registerSimpleScopedEnvExtension {
    name     := ref
    initial  := ⟨{ : QueryBuilderM.State }, [], []⟩
    addEntry := fun d e => e
  }
  registerBuiltinAttribute {
    ref   := ref
    name  := attrName
    descr := attrDescr
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName stx attrKind => do
      let go : MetaM Unit := do
        -- let info ← getConstInfo declName
        -- let reducedType ← reduce info.type
        let ⟨oldSt, oldExprs, _⟩ := (ext.getState (← getEnv))
        ext.add <| ← addCommandForConstant oldExprs declName oldSt
      discard <| go.run {} {}
    erase := fun declName => do
      pure ()
  }
  return ext

initialize euclidExtension : EuclidExtension ← registerEuclidAttr `euclid "euclidean geometry inference rules"

-- def getEuclidTheorems : CoreM (Array Smt.Translate.Command × ) := do
--   pure <| (euclidExtension.getState (← getEnv)).map (·.2)

elab "#euclid_post" : command => do
  liftTermElabM do
    let ⟨st, oldExprs, cmds⟩ := euclidExtension.getState (← getEnv)
    for cmd in cmds.reverse do
      IO.println cmd
    IO.println oldExprs.length
