inductive ConsumedCreated where
 | Created : ConsumedCreated
 | Consumed : ConsumedCreated

export ConsumedCreated (Created Consumed)

def ConsumedCreated.isCreated (c : ConsumedCreated) : Bool :=
  match c with
  | Created => true
  | _ => false

def ConsumedCreated.isConsumed (c : ConsumedCreated) : Bool :=
  match c with
  | Consumed => true
  | _ => false
