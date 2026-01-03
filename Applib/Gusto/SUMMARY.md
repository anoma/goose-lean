Write-up on Gusto DSL.

## What is Gusto?

It's a domain-specific language for writing applications that compiles
to Goose IR, which ultimately compiles to RM applications. The word
*Gusto* is the Spanish translation of the English word *taste*.
The name is thanks to Jan, and agreed by the team.

Gusto syntax is a subset of Python syntax. We borrow constructs from the official Python PEG grammar:
https://docs.python.org/3/reference/grammar.html. See `Applib/Gusto/Syntax.lean` for the details.

## How to Write Gusto

Gusto uses Python-like syntax to define AVM classes with special syntax
including constructors, destructors decorators, and signatures. Here's what you need to know

*Basic Structure*

```python
import Applib.Gusto

gusto ModuleName
  class ClassName:
    field1: Type1
    field2: Type2

    @constructor
    @signature(field1)
    def ConstructorName(self, param: Type, quantity: Nat):
        self.field1 = param
        self.field2 = value
        self.quantity = quantity

    @method
    @signature(field1)
    def MethodName(self, param: Type):
        self.field1 = param

    @destructor
    @signature(field1)
    def DestructorName(self):
        pass
end ModuleName
```

Key Features:
- Modules: Wrap classes with `gusto ModuleName` ... `end ModuleName`. Although not required. A module compiles to an *ecosystem* in Goose lingo.
- Classes: Define resource types with `class Name:` (indented under module)
- Fields: Type-annotated properties (e.g., `balance: Nat`)
- Decorators: Mark members with `@constructor`, `@method`, or `@destructor`
 `@signature(field1, field2)` is a special decorator that adds cryptographic validation to the constructor.

Simple Example (Single Class):

```python
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

    @signature(owner)
    def Transfer(self, newOwner: PublicKey):
        self.owner = newOwner

    @destructor
    @signature(owner)
    def Burn(self):
        pass
end KudosModule
```

Advanced Example (Goose Ecosystem with Multiple Classes + Multi-methods):

```python
gusto KudosBank
    class KudosBank:
        owner: PublicKey
        balances: Balances

        @constructor
        def Open(self, owner: PublicKey):
            self.owner = owner
            self.balances = Balances.empty

    class Check:
        denomination: Denomination
        owner: PublicKey
        quantity: Nat

        def Transfer(self, newOwner: PublicKey):
            self.owner = newOwner

    -- Multi-methods operate on multiple objects, as Goose ecosystems
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
end KudosBank
```

The Gusto compiler internally transforms this into complete Lean4 definitions
with all necessary boilerplate, type-safe structures, and AVM program
implementations.

With a complete implementation, we'll have even IDE support for Gusto,
like auto-completion, type checking, and error highlighting.

## Why Gusto?

Were you able to read the Gusto snippet above? I'm sure you can.
That's the point! Easy. Gusto is a DSL for Goose. 

Writing Goose applications involves a lot of boilerplate definitions—
defining structs, inductive types, and functions that only
after a while on the job can handle, while most of us cannot. See https://github.com/anoma/goose-lean/tree/main/Apps for examples.


## Why do we branch off the syntax from Python?

The choice to use Python-like syntax is pragmatic rather than ideological. Python is currently the [most popular programming language](https://trends.google.com/trends/explore?date=now%201-d&q=%2Fm%2F05z1_,rust,%2Fm%2F0jgqg,%2Fm%2F04kyw,%2Fm%2F01tlw&hl=en), which means any developer can read and write it with little effort, and AI tools handle it effortlessly. This popularity is a fact independent of debates about whether Python's design is ergonomic, well-designed, or brilliant.

Importantly, using Python-like syntax does not mean adopting Python's features or limitations. Gusto is a DSL that desugars into a typed intermediate representation. Users can omit types for brevity or add type annotations for clarity. Because we desugar to an IR with complete type information, we leverage the full power of Lean4's elaborator: type checking, type inference, dependent types, and more.

The syntax is fully extensible. Want a different keyword instead of "class"?
Need embedded logic or specialized fetch operations? All can be implemented. We
can go as far as the elaborator allows us. See [metaprogramming in
Lean4](https://leanprover-community.github.io/lean4-metaprogramming-book/) or
the [Lean4
reference](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/#The-Lean-Language-Reference--Elaboration-and-Compilation)
for details on what's possible. So far I only have compliments for the syntax facilities of Lean4.

## Current Status

Gusto is in early development with the core infrastructure in place. The compilation pipeline consists of three main components:

1. Syntax: BNF-style grammar definitions for parsing Gusto source code
2. Parsing: Syntax-to-IR conversion producing typed intermediate representations
3. Elaboration: IR-to-AVM code generation emitting complete Lean4 definitions

The basic syntax is functional and supports single-class definitions with
constructors, methods, and destructors. Gusto provides a higher-layer,
user-friendly interface for AVM programs as defined in Goose v0.3. See the
Goose's summary.

## Future Extensibility

The approach of implementing Gusto as a Lean4 DSL provides inherent advantages. Out-of-the-box compatibility with Goose's existing infrastructure means we build on a solid foundation rather than starting from scratch. The syntax and compilation process remain fully modifiable—Lean4's metaprogramming facilities allow us to extend the language arbitrarily, just as Lean4's own elaborator is written in Lean4.

This design allows continuous refinement without architectural constraints.

## Why not use Python directly?

An alternative would be writing a Python library using `import ast` to compile
actual Python code into Lean4 definitions. However, this approach introduces
fragility: the compilation pipeline becomes error-prone for sure and risks
diverging from the Goose repository over time. 

With Gusto as a Lean4 DSL, we ensure tight integration with the existing
codebase, making the system more maintainable and the compilation process more
transparent, plus the possibility to add formal verification and other features
to the language at any time.







