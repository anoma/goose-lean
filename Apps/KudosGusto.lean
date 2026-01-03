-- Gusto DSL version of Kudos.lean
-- This demonstrates the Gusto syntax for a simple token class

import Applib.Gusto

gusto KudosModule
  class Kudos:
    originator: PublicKey
    owner: PublicKey

    @constructor
    @signature(originator)
    def Mint(self, originator: PublicKey, quantity: Nat):
        self.quantity = quantity
        self.owner = originator
        self.originator = originator

    @method
    @signature(owner)
    def Transfer(self, newOwner: PublicKey):
        self.owner = newOwner

    @destructor
    @signature(owner)
    def Burn(self):
        pass
end KudosModule
