import Applib.Gusto.Syntax

/-!
# Gusto Syntax Test Cases

Verifies that our syntax correctly parses according to the PEG grammar specification.
Uses #check_failure to ensure syntax parsing works without requiring elaboration
functions (which will be implemented later).
-/

namespace Gusto.Tests

/-!
## Atom Tests
-/

#check_failure gusto(42)                    -- NUMBER
#check_failure gusto(foo)                   -- NAME
#check_failure gusto("hello")               -- STRING
#check_failure gusto(True)                  -- True literal
#check_failure gusto(False)                 -- False literal
#check_failure gusto(None)                  -- None literal
#check_failure gusto((1 + 2))               -- grouped expression

/-!
## Primary Tests (attribute access and calls)
-/

#check_failure gusto(foo.bar)               -- attribute access
#check_failure gusto(foo.bar.baz)           -- chained attribute access
#check_failure gusto(foo())                 -- function call, no args
#check_failure gusto(foo(1))                -- function call, one arg
#check_failure gusto(foo(1, 2, 3))          -- function call, multiple args
#check_failure gusto(foo.bar())             -- method call
#check_failure gusto(foo.bar(1, 2))         -- method call with args

/-!
## Expression Tests (operators with correct precedence)
-/

-- Power operator (highest precedence)
#check_failure gusto(2 ** 3)                -- exponentiation
#check_failure gusto(x ** y ** z)           -- right associative

-- Unary operators
#check_failure gusto(+x)                    -- unary plus
#check_failure gusto(-x)                    -- unary minus
#check_failure gusto(- -x)                  -- double negation

-- Multiplicative operators
#check_failure gusto(a * b)                 -- multiplication
#check_failure gusto(a / b)                 -- division
#check_failure gusto(a // b)                -- floor division
#check_failure gusto(a % b)                 -- modulo
#check_failure gusto(a * b / c)             -- left associative

-- Additive operators
#check_failure gusto(a + b)                 -- addition
#check_failure gusto(a - b)                 -- subtraction
#check_failure gusto(a + b - c)             -- left associative

-- Comparison operators
#check_failure gusto(a == b)                -- equality
#check_failure gusto(a != b)                -- inequality
#check_failure gusto(a < b)                 -- less than
#check_failure gusto(a > b)                 -- greater than
#check_failure gusto(a <= b)                -- less or equal
#check_failure gusto(a >= b)                -- greater or equal
#check_failure gusto(a < b < c)             -- chained comparisons

-- Complex expressions testing precedence
#check_failure gusto(a + b * c)             -- * binds tighter than +
#check_failure gusto(a * b + c * d)         -- multiple operators
#check_failure gusto(2 + 3 * 4 ** 5)        -- all levels
#check_failure gusto(-a ** 2)               -- unary vs power
#check_failure gusto(a.b + c.d(1, 2))       -- calls and operators

/-!
## Simple Statement Tests
-/

-- Expression statements
#check_failure gusto_block(42)              -- literal expression
#check_failure gusto_block(foo())           -- function call

-- Assignment statements
#check_failure gusto_block(x = 42)          -- simple assignment
#check_failure gusto_block(x.y = 42)        -- attribute assignment
#check_failure gusto_block((x) = 42)        -- parenthesized target

-- Return statements
#check_failure gusto_block(return)          -- return without value
#check_failure gusto_block(return 42)       -- return with value
#check_failure gusto_block(return x + y)    -- return expression

-- Pass statement
#check_failure gusto_block(pass)            -- pass statement

-- Semicolon-separated statements
#check_failure gusto_block(x = 1; y = 2)    -- two assignments

/-!
## Compound Statement Tests

Function definitions, class definitions, and if statements.
These will show "elaboration not implemented" - that's expected.
The absence of parse errors confirms syntax is correct.
-/

-- Nested function calls with operators
#check_failure gusto(foo(a + b, c * d))

-- Chained method calls
#check_failure gusto(obj.method1().method2(x).method3())

/-!
## Commented out tests (require elaboration)

These are commented out because they require elaboration to be implemented.
Uncomment when elaborators are ready.

```lean
-- Function definitions
langy
  def foo():
    pass

langy
  def add(x, y):
    return x + y

langy
  def greet(name = "World"):
    return "Hello"

langy
  def identity(x) -> x:
    return x

-- Class definitions
langy
  class Foo:
    pass

langy
  class Bar():
    x = 42

langy
  class Baz(Base):
    def method():
      return 1

-- If statements
langy
  if x > 0:
    y = 1

langy
  if x > 0:
    y = 1
  else:
    y = -1

langy
  if cond:
    foo()
  else:
    bar()

-- Complex class with methods
langy
  class Counter:
    def increment(self, n = 1):
      self.value = self.value + n
      return self.value

-- Function with multiple statements
langy
  def compute(x, y):
    result = x * 2 + y
    result = result ** 2
    return result

-- Nested if statements
langy
  if a > 0:
    if b > 0:
      return a + b
    else:
      return a
  else:
    return 0
```
-/

end Gusto.Tests
