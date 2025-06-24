
import Goose.Class
import Goose.Object.Translation

namespace Goose

def Class.logic (cls : Class) (args : Anoma.Logic.Args Class.AppData) : Bool :=
  let selfObj := @Object.fromResource _ args.data.objectAppData.rawPublicData args.data.objectAppData.publicData args.self
  let actionLogicArgs := { args with data := args.data.objectAppData }
  let extraLogicArgs := { args with data := { args.data.objectAppData with args := () } }
  -- In a real implementation, there is a fixed finite number of action logics
  -- (constructor and method logics). The action logics are identified by enum
  -- values and we make a big case switch here instead of the first conjunct to
  -- choose an appropriate action logic. In Lean, it is clearer and more
  -- convenient to store the action logic function directly in appData, instead
  -- of storing its identifying enum value.
  args.data.actionLogic actionLogicArgs
    && cls.extraLogic selfObj extraLogicArgs

end Goose
