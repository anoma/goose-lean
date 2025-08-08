import AVM.Class.Label

namespace AVM

structure Message (lab : Class.Label) where
  /-- The message ID. -/
  id : Class.Label.MemberId lab
  /-- The arguments of the message. -/
  args : (Class.Label.MemberId.Args id).type
  /-- The sender of the message. -/
  sender : Anoma.ObjectId
  /-- The recipient of the message. -/
  recipient : Anoma.ObjectId
