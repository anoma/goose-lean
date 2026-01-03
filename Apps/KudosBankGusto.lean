-- Gusto DSL version of KudosBank.lean
-- This demonstrates context syntax with multiple classes and multi-methods

import Applib.Gusto

-- Note: Helper types (Denomination, Account, Balances) remain in regular Lean
-- as they are reusable domain types, not AVM-specific boilerplate

gusto KudosBank
    /-
    ============================================
    CLASS 1: KudosBank (Main banking contract)
    ============================================
    -/
    class KudosBank:
        owner: PublicKey
        balances: Balances

        @constructor
        def Open(self, owner: PublicKey):
            self.owner = owner
            self.balances = Balances.empty

        @method
        @signature(owner)
        def Mint(self, denom: Denomination, quantity: Nat):
            self.balances = self.balances.addTokens(
                denom.originator, denom, quantity)

        @method
        @signature(owner)
        def Transfer(self, oldOwner: PublicKey, newOwner: PublicKey,
                     denom: Denomination, quantity: Nat):
            self.balances = (self.balances
                .addTokens(newOwner, denom, quantity)
                .subTokens(oldOwner, denom, quantity))

        @method
        @signature(owner, originator)
        def Burn(self, denom: Denomination, owner: PublicKey, quantity: Nat):
            self.balances = self.balances.subTokens(
                denom.originator, denom, quantity)

        @destructor
        @signature(owner)
        def Close(self):
            pass

    /-
    ============================================
    CLASS 2: Check (Transferable token voucher)
    ============================================
    -/
    class Check:
        denomination: Denomination
        owner: PublicKey
        quantity: Nat

        @method
        def Transfer(self, newOwner: PublicKey):
            self.owner = newOwner

    /-
    ============================================
    CLASS 3: Auction (Auction state)
    ============================================
    -/
    class Auction:
        owner: PublicKey
        auctionedDenomination: Denomination
        auctionedQuantity: Nat
        biddingDenomination: Denomination
        highestBid: Nat
        highestBidder: PublicKey

    /-
    ============================================
    MULTI-METHODS (Cross-object transactions)
    ============================================
    -/

    @signature(owner)
    def IssueCheck(bank: KudosBank, denomination: Denomination,
                   owner: PublicKey, quantity: Nat) -> Check:
        bank.balances = bank.balances.subTokens(owner, denomination, quantity)
        return Check(denomination, owner, quantity)

    @signature(owner)
    def DepositCheck(bank: KudosBank, check: Check):
        bank.balances = bank.balances.addTokens(
            check.owner, check.denomination, check.quantity)
        destroy check

    @signature(owner)
    def NewAuction(check: Check, biddingDenomination: Denomination) -> Auction:
        return Auction(
            owner=check.owner,
            auctionedDenomination=check.denomination,
            auctionedQuantity=check.quantity,
            biddingDenomination=biddingDenomination,
            highestBid=0,
            highestBidder=check.owner)
        destroy check

    @signature(owner)
    def Bid(check: Check, auction: Auction) -> Check:
        old_winner_check = Check(
            auction.biddingDenomination,
            auction.highestBidder,
            auction.highestBid)

        auction.highestBid = check.quantity
        auction.highestBidder = check.owner

        destroy check
        return old_winner_check

    @signature(owner)
    def EndAuction(auction: Auction) -> (Check, Check):
        winner_check = Check(
            auction.auctionedDenomination,
            auction.highestBidder,
            auction.auctionedQuantity)

        owner_check = Check(
            auction.biddingDenomination,
            auction.owner,
            auction.highestBid)

        destroy auction
        return (winner_check, owner_check)
end KudosBank
