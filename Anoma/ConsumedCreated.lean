inductive ConsumedCreated where
 | Created : ConsumedCreated
 | Consumed : ConsumedCreated

export ConsumedCreated (Created Consumed)

def ConsumedCreated.isCreated (c : ConsumedCreated) : Bool :=
  match c with
   | Created => True
   | _ => False

def ConsumedCreated.isConsumed (c : ConsumedCreated) : Bool :=
  match c with
   | Consumed => True
   | _ => False
