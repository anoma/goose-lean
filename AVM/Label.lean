import AVM.Class.Label
import AVM.Message

namespace AVM

structure Object.Resource.Label where
  /-- The label of the class -/
  classLabel : Class.Label
  /-- The dynamic label is used to put dynamic data into the Resource label -/
  dynamicLabel : classLabel.DynamicLabel.Label.type

instance : TypeRep Object.Resource.Label where
  rep := Rep.atomic "Object.Resource.Label"

instance : BEq Object.Resource.Label where
  beq o1 o2 := o1.classLabel == o2.classLabel && o1.dynamicLabel === o2.dynamicLabel

inductive Resource.Label where
  | object : Object.Resource.Label → Label
  | message : SomeMessage → Label
  | intent : Label

instance : TypeRep Resource.Label where
  rep := Rep.atomic "AVM.Resource.Label"

instance : BEq Resource.Label where
  beq
    | .object l1, .object l2 => l1 == l2
    | .message m1, .message m2 => m1 == m2
    | .intent, .intent => true
    | _, _ => false
