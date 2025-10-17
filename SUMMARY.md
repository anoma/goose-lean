# GOOSE v0.3.1 Summary
A high-level summary description of GOOSE v0.3.1. The description intentionally simplifies some data structures in comparison to the actual Lean implementation. The aim is to provide a high-level overview of the essential features of the model and its translation to the Anoma Resource Machine.

- [GOOSE v0.3.1 Summary](#goose-v031-summary)
	- [Overview](#overview)
	- [Anoma Programs](#anoma-programs)
	- [AVM Programs](#avm-programs)
	- [Translation overview](#translation-overview)
	- [AVM data structures](#avm-data-structures)
		- [Class.Label](#classlabel)
		- [Ecosystem.Label](#ecosystemlabel)
		- [Object](#object)
		- [ObjectData](#objectdata)
		- [MessageId](#messageid)
		- [Message](#message)
		- [Constructor](#constructor)
		- [Destructor](#destructor)
		- [Method](#method)
		- [MultiMethod](#multimethod)
		- [Class](#class)
		- [Ecosystem](#ecosystem)
		- [Authorization](#authorization)
	- [AVM -\> RM translation](#avm---rm-translation)
		- [Object](#object-1)
			- [Resource data check](#resource-data-check)
		- [Message](#message-1)
		- [Task](#task)
			- [Task composition](#task-composition)
		- [Member calls - message sending](#member-calls---message-sending)
			- [Message logics](#message-logics)
			- [Example](#example)
			- [Technical details](#technical-details)
				- [Compliance Units](#compliance-units)
				- [Dummy Resource](#dummy-resource)
				- [Action partitioning](#action-partitioning)
		- [Constructor](#constructor-1)
			- [Constructor call](#constructor-call)
			- [Constructor message logic](#constructor-message-logic)
		- [Destructor](#destructor-1)
			- [Destructor call](#destructor-call)
			- [Destructor message logic](#destructor-message-logic)
		- [Method](#method-1)
			- [Method call](#method-call)
			- [Method message logic](#method-message-logic)
		- [Upgrade](#upgrade)
			- [Upgrade call](#upgrade-call)
			- [Upgrade message logic](#upgrade-message-logic)
		- [Multi-method](#multi-method)
			- [Multi-method call](#multi-method-call)
			- [Multi-method message logic](#multi-method-message-logic)
		- [Function invocation](#function-invocation)
		- [Class logic](#class-logic)
	- [Translation issues and limitations](#translation-issues-and-limitations)
	- [Implemented example apps](#implemented-example-apps)

## Overview

The Anoma Virtual Machine (AVM) data structures provide an object-oriented abstraction over the Anoma Resource Machine (RM). Ecosystems encapsulate collections of related classes and functions. Each class within an ecosystem uniquely defines its structure through private fields and member operations — constructors, destructors, and methods. Multi-methods in an ecosystem operate over sets of objects from these classes. Every class belongs to a single ecosystem, and the relationships between classes, their operations, and multi-methods must be fully specified ahead of time — there is no dynamic addition of members or runtime reflection.

The translation from AVM to the Resource Machine (RM) relies on the static nature of AVM programs. Each object is compiled to a single resource, tagged with its class and ecosystem metadata. Constructor, destructor, method and multi-method calls are translated into message sends. Each message is implemented with a single message resource. The transactions generated for each call consist of a number of actions, one per object. The messages received by the object are consumed in the action, the messages sent by it are created. The Resource Logics (RLs) of the message resources implement the checks corresponding to the code of the class member operations and multi-methods.

Because all class member operations and multi-methods are known statically, appropriate RLs for the message resources can be automatically generated from the code. In addition to RLs for messages, a Resource Logic is generated for each class (the class logic) and associated with each object of the class - it checks if the messages sent to the object correspond to statically known member operations or multi-methods.

## Anoma Programs

Anoma programs are an abstraction that reifies the local domain, solver and controller (see [related forum post](https://forum.anoma.net/t/reifying-the-local-domain-solver-and-controller-in-the-avm)). Anoma programs deal with Resource Machine data structures (resources, transactions, etc.). Anoma programs are a low-level compilation target for the AVM programs which deal with higher-level AVM data structures - objects, methods, classes, etc.

An Anoma program consists of a list of statements of the following form.
- `submitTransaction : Transaction -> Unit`. Submit an Anoma transaction to the Anoma Resource Machine.
- `queryResource : ObjectId -> Resource`. Queries a resource by ID from the Anoma Resource Machine. This is an abstraction over the Resource Machine - we elide how / where resources are stored exactly.
- `genRand : Unit -> Nat`. Generate a random number.

Relevant file: `Anoma/Program.lean`.

## AVM Programs

AVM programs provide an object-oriented abstraction over Anoma programs to which they are translated. An AVM program `Program A` is parameterized by the return type `A`. An AVM program consists of a list of statements of the following form.
- `objId := create Class.Contructor args`. Call a constructor to create a new object.
- `destroy Destructor objId args`. Call a destructor on an object with a given ID.
- `call Method objId args`. Call a method of an object with a given ID.
- `multiCall MultiMethod objIds args`. Call a multi-method on objects with given IDs.
- `upgrade objId to obj`. Upgrade an object with a given ID `objId` to an object `obj`. An upgrade is permitted only to an object of the same class with a newer version. The new object `obj` replaces the upgraded one. The ID of the object is preserved.
- `obj := fetch objId`. Fetch an object with a given ID.
- `invoke fn args`. Invoke a function, i.e., a sub-program.
- `return a`. Return a given value `a : A`.

AVM Programs can also contain conditionals, matches and other Lean control structures - they are implemented as a DSL embedded in Lean.

Relevant files: `Applib/Surface/Program.lean`, `AVM/Program.lean`.

Example - mutual increment program:
```
def mutualIncrement (rc1 rc2 : Reference Counter) (n : Nat) : Program Unit := ⟪
  c1 := fetch rc1
  c2 := fetch rc2
  call Counter.Incr rc1 (c1.count * n + c2.count)
  call Counter.Incr rc2 (c2.count * n + c1.count)
  return ()
⟫
```
`Reference` is a typed wrapper over `ObjectId`.

## Translation overview

The translation from AVM programs to Anoma programs can be summarized by the following phases.
1. Move all object fetches and object id generation to the beginning of the program.
2. For each class member or multi-method call create an action implementing the manipulations on `self` objects in the body. For example, a method `Counter.Incr` defined by
```
method Counter.Incr (self : Counter) (n : Nat) : Program Counter := ⟪
  return {self with count := self.count + n}
⟫
```
would result in an action with:
  - one consumed object resource corresponding to `self`,
  - one created object resource corresponding to `self` with the `count` field increased by `n`,
  - one consumed message resource for `Counter.Incr` containing the `n` argument,
  - created message resources for all nested calls (none in this case),
  - one consumed and one created object resource for each object fetched in the body (none in this case).
3. The previous points are applied recursively, resulting in a set of actions dependent on parameter values (fetched objects and generated object ids).
4. The fetches and id generation at the beginning of the program are translated to `queryResource` and `genRand` Anoma program commands.
5. The actions are grouped into a single transaction, together with an action that sends the messages corresponding to the calls in the program. The `submitTransaction` command submits this transaction in the resulting Anoma program.

The message RLs check that the created object resources correspond to modifications of consumed object resources specified by the bodies of corresponding class members or multi-methods, e.g., for methods the consumed object resource `self` is correctly updated into the created object resource.

For example, the AVM program `mutualIncrement` from the previous section is translated to the Anoma program performing the following.
1. `c1 := queryResource rc1.id`
2. `c2 := queryResource rc2.id`
3. `submitTransaction tx` where `tx` consists of two actions corresponding to the two calls and an action sending the call messages.

Action for the first call:
- Consumed resources:
  - object resource for `c1`,
  - message resource for `Counter.Incr` with recipient `c1.id` and argument `c1.count * n + c2.count`.
- Created resources:
  - object resource for `{c1 with count := c1.count + c1.count * n + c2.count}`.

Action for the second call:
- Consumed resources:
  - object resource for `c2`,
  - message resource for `Counter.Incr` with recipient `c2.id` and argument `c2.count * n + c1.count`.
- Created resources:
  - object resource for `{c2 with count := c2.count + c2.count * n + c1.count}`.

Action sending the call messages:
- Consumed resources: none.
- Created resources:
  - message resource for `Counter.Incr` with recipient `c1.id` and argument `c1.count * n + c2.count`.
  - message resource for `Counter.Incr` with recipient `c2.id` and argument `c2.count * n + c1.count`.

## AVM data structures

### Class.Label
- `Class.Label` in `AVM/Class/Label.lean`
- Uniquely identifies and specifies a class.
- Consists of:
	- `name : String`. A unique class name.
	- `version : Nat`. A version of the class. An object can be upgraded to an object of a class with the same name and strictly higher version.
	- `PrivateFields : Type`. Type of private fields for objects of the class described by the label.
	- `DynamicResourceLabel : PrivateFields -> Type`. Describes dynamic data stored in Resource's `label` field. The dynamic resource label data is determined by the actual values of the object's fields.
	- `ConstructorId : Type`. Enumeration type of identifiers for constructors of the described class.
	- `ConstructorArgs : ConstructorId -> Type`. Type of arguments for a given constructor.
	- `DestructorId : Type`. Enumeration type of identifiers for destructors of the described class.
	- `DestructorArgs : DestructorId -> Type`. Type of arguments for a given destructor.
	- `MethodId : Type`. Enumeration type of identifiers for methods of the described class.
	- `MethodArgs : MethodId -> Type`. Type of arguments for a given method.

### Ecosystem.Label
- `Ecosystem.Label` in `AVM/Ecosystem/Label/Base.lean`
- Uniquely identifies and specifies an ecosystem.
- An ecosystem is a collection of classes and functions on objects of these classes. A class belongs to exactly one ecosystem. The functions can have multiple designated `self` arguments (_selves_), all of which are consumed (destroyed or modified) by function invocation.
- Consists of:
	- `classLabels : Set Class.Label`. Classes in the ecosystem. A class can be in only one ecosystem.
	- `MultiMethodId : Type`. Enumeration type for multi-methods in the described ecosystem.
	- `MultiMethodArgs : MultiMethodId -> Type`. Type of multi-method arguments excluding selves.
	- `MultiMethodSelves : MultiMethodId -> List Class.Label`. Class identifiers for selves. Every class label of a `self` argument must be in the `classLabels` set.

### Object
- `Object` in `AVM/Object.lean`
- Concrete object representation.
- Consists of:
	- `label : Class.Label` determines the object's class,
	- `id : ObjectId` is the unique object ID,
	- `quantity : Nat`,
	- private fields,
    - nonce – ensures the uniqueness of resource commitment and nullifier.

### ObjectData
- `ObjectData` in `AVM/Object.lean`
- Consists of `label`, `quantity` and private fields of the object.

### MessageId
- Implemented with `MemberId` in `AVM/Ecosystem/Label/Base.lean` and `Label.MemberId` in `AVM/Class/Label.lean`.
- A unique message identifier which also specifies the type of the message (the high-level AVM concept the message implements):
  - `constructorId : (label : Class.Label) -> label.ConstructorId -> MessageId`,
  - `destructorId : (label : Class.Label) -> label.DestructorId -> MessageId`,
  - `methodId : (label : Class.Label) -> label.MethodId -> MessageId`,
  - `upgradeId : (label : Class.Label) -> MessageId`,
  - `multiMethodId : (label : Ecosystem.Label) -> label.MultiMethodId -> MessageId`.

### Message
- `Message` in `AVM/Message/Base.lean`
- A message is a communication sent from one object to another in the AVM. Messages are created for constructor, destructor, method and multi-method calls. The end-user never directly manipulates messages - only through calls to class members and multi-methods.
- Consists of:
  - `label : Ecosystem.Label`. The label of the ecosystem of the message.
  - `vals : Vals`. Message parameter values. The message parameters are object resources and generated random values that are used in the body of the call associated with the message. These need to be provided in the message, because the associated Resource Logic cannot fetch object resources from the Anoma system or generate new object identifiers.
  - `id : MessageId`. The message ID.
  - `args : id.Args`. The arguments of the message, where `id.Args` is the type of arguments based on the message id. The message arguments are the non-self arguments of the corresponding member or multi-method call.
  - `recipients : List ObjectId`. The recipients of the message.
  - `signatures : List Signature`. Authorization signatures for the message. Each signature consists of:
    - public identifier of the signer,
    - signature data: the message `id` and `args` cryptographically signed with signer's private key.

### Constructor
- `Class.Constructor` in `AVM/Class/Member.lean`
- Represents a constructor of an object in a given class.
- Consists of:
	- `label : Class.Label` determines the constructor's class.
	- `id : label.ConstructorId` determines the unique id of the constructor.
	- `Args := label.ConstructorArgs id` is the type of constructor arguments.
	- `body : Args -> Program ObjectData`. Constructor body, returning the object data for the object created by the constructor call.
	- `invariant : Message -> Args -> Bool`. Extra constructor logic. The constructor message logic is a conjunction of auto-generated constructor logic and the extra constructor logic.

### Destructor
- `Class.Destructor` in `AVM/Class/Member.lean`
- Represents a destructor of an object in a given class. Allows to "burn" objects of this class.
- Consists of:
	- `label : Class.Label` determines the destructor's class.
	- `id : label.DestructorId` determines the unique id of the destructor.
	- `Args := label.DestructorArgs id` is the type of destructor arguments excluding `self`.
	- `body : (self : Object) -> Args -> Program Unit`. Destructor body program.
	- `invariant : Message -> (self : Object) -> Args -> Bool`. Extra destructor logic. The destructor message logic is a conjunction of auto-generated destructor logic and the extra destructor logic.

### Method
- `Class.Method` in `AVM/Class/Member.lean`
- Represents a method of an object in a given class.
- Consists of:
	- `label : Class.Label` determines the method's class.
	- `id : label.MethodId` determines the unique id of the method.
	- `Args := label.MethodArgs id` is the type of method arguments excluding `self`.
	- `body : (self : Object) -> Args -> Program Object`. Method body program. The return value is the updated `self`.
	- `invariant : Message -> (self : Object) -> Args -> Bool`. Extra method logic. The method message logic is a conjunction of auto-generated method logic and the extra method logic.

### MultiMethod
- `MultiMethod` in `AVM/Ecosystem/Member.lean`
- Represents a multi-method in an ecosystem. A multi-method operates on multiple `self` arguments – objects of classes in the ecosystem. The `self` arguments are consumed by the multi-method. There may be other arguments provided beside the `self` arguments.
- A multi-method can modify / re-assemble selves (disassemble and then assemble) or destroy them, and also construct new objects.
- Consists of:
	- `label : Ecosystem.Label` determines the multi-method's ecosystem.
	- `id : label.MultiMethodId` determines the unique id of the funtion.
	- `Args := label.MultiMethodArgs id` is the type of multi-method arguments excluding selves.
	- `body : (selves : List Object) -> Args -> Program MultiMethodResult`. The body of the multi-method. `MultiMethodResult` is a record which consists of:
		- `disassembled : List Object`. List of disassembles selves. Disassembled object resources are balanced with the newly assembled objects (see `assembled` below). The `disassembled` list must be a sublist of `selves`.
		- `destroyed : List Object`. List of destroyed selves. Destroyed object resources are balanced with automatically generated created ephemeral resources. The `destroyed` list must be a sublist of `selves`.
		- `assembled : List Object`. List of assembled objects into which disassembled objects are transformed as a result of the multi-method call. It is the responsibility of the user to ensure that assembled object resources balance with the disassembled selves.
		- `constructed : List Object`. List of constructed objects. Constructed object resources are balanced with automatically generated consumed ephemeral resources.
	- `invariant : Message -> (selves : List Object) -> Args -> Bool`. Extra multi-method logic. The multi-method message logic is a conjunction of the auto-generated multi-method logic and the extra multi-method logic.
- `selves : List Object` in `body` and `invariant` above is a list of `self` arguments - objects whose classes are described by `label.MultiMethodSelves id`.
- `selves = disassembled ++ destroyed`.

### Class
- `Class` in `AVM/Class.lean`
- Represents a class of objects.
- Consists of:
	- `label : Class.Label`. Unique class label.
	- `constructors : Set Class.Constructor`. Set of constructors. There is one constructor for each element of `label.ConstructorId`.
	- `destructors : Set Class.Destructor`. Set of destructors. There is one destructor for each element of `label.DestructorId`.
	- `methods : Set Class.Method`. Set of methods. There is one method for each element of `label.MethodId`.
	- `invariant : (self : Object) -> Logic.Args -> Bool`. Extra class-specific logic. The class logic is the conjunction of the extra class logic and the member logics. `Logic.Args` is the type of Resource Logic arguments in the Anoma Resource Machine.

### Ecosystem
- `Ecosystem` in `AVM/Ecosystem.lean`
- Represents an ecosystem of mutually dependent classes and functions.
- Consists of:
	- `label : Ecosystem.Label`. Unique ecosystem label.
	- `classes : Set Class`. Classes in the ecosystem. A class is in exactly one ecosystem.
	- `multiMethods : Set MultiMethod`. Multi-methods in the ecosystem. A multi-method is in exactly one ecosystem.

### Authorization
The GOOSE framework provides a function `checkSignature : Message -> PublicKey -> Bool` which checks that a given message was signed with the private key corresponding to a given public key. In other words, `checkSignature(msg, pubKey)` checks that decrypting `msg.signature` with `pubKey` yields (a digest of) `msg`.

The `checkSignature` function can be used in invariants to perform authorization of the received messages.

## AVM -> RM translation

### Object

Objects are translated to Resources. Every object is translated to a single resource, but it may contain references to sub-objects which are translated to separate resources.

- `label` (the class label) is stored in the `label` field.
- `quantity` is stored in the `quantity` field.
- Private fields are stored in the `value` field.
- The Resource Logic (RL) of the resource corresponding to the object is determined by the object's class. This way the resource kind (label + logic) determines the object class. The RL check if the messages sent to the object are correspond to class member or known multi-methods.
- The ephemerality of the resource is _not_ determined by the object. An object can map to either an ephemeral or a persistent resource depending on how it is used in the action.
- The `nullifierKeyCommitment` field is computed using the universal nullifier key.

#### Resource data check
Resource data check `checkDataEq(res,objData)` compares a resource `res` against  object data `objData`.

- `Class.Member.Logic.checkResourceData` in `AVM/Class/Member/Logic.lean`.
- Check `res.label == objData.label`.
- Check `res.logicHash` is equal to the hash of the [class logic](#class-logic) for the class of `objData`.
- Check `res.quantity == objData.quantity`.
- Check `res.value` encodes the private fields of `objData`.

### Message

Messages are translated to ephemeral consumed resources (received messages) or ephemeral created resources (sent messages). All message data is stored in the resource label - this ensures that sent and received messages match, due to the balance check in the Anoma Resource Machine.

### Task

- `Task` in `AVM/Task.lean`
- A Task is an intermediate data structure into which class member and multi-method calls are translated.
- Consists of:
  - `Params : Type`. Type of Task parameters - objects to fetch from the Anoma system and new object ids to generate.
  - `message : Message`. The message to send.
  - `actions : Params → List Action`. Task actions - Resource Machine actions to perform parameterised by fetched objects and new object ids.
- A Task is translated into an Anoma Program which:
  1. Fetches the objects and generates object ids specified by `Params`.
  2. Submits a transaction with actions:
  	- an action with one created resource corresponding to `message`,
  	- `actions` of the Task.

#### Task composition

Tasks `<Params1, message1, actions1>, .., <ParamsN, messageN, actionsN>` can be composed with a new message `msg` and action `act` to create a task `<Params, message, actions>` such that:
- `Params := Params1 ++ .. ++ ParamsN`,
- `message := msg`,
- `actions params1 .. paramsN := act :: actions1 params1 ++ .. ++ actionsN paramsN`.
Typically, `act` has among created resources the message resources for `message1, .., messageN`.

### Member calls - message sending

Calls to class members (constructor, destructor or method calls) and multi-methods are first translated into Tasks - one Task per call. The Task is composed from sub-tasks generated for the nested calls in the body program of the class member / multi-method, a message corresponding to the called member, and an action sending the sub-task messages and implementing the changes to selves and creation of objects specified by the member body.

#### Message logics
A message logic is a logic for a specific message (corresponding to a member call):

- constructor,
- destructor,
- method,
- multi-method,
- upgrade.

The message logics check the constraints for the corresponding member call, i.e., that the object resource in the action was modified correctly according to the member's code.

#### Example

Consider the following `Counter` and `TwoCounter` classes with the methods `Counter.Incr` and `TwoCounter.MutualIncrement`.
```
class Counter {
  count : Nat
}

method Counter.Incr (self : Counter) (n : Nat) : Program Counter := ⟪
  return {self with count := count + n}
⟫

class TwoCounter {
	cnt1 : Reference Counter
	cnt2 : Reference Counter
}

method TwoCounter.MutualIncrement (self : TwoCounter) (n : Nat) : Program TwoCounter := ⟪
  c1 := fetch self.cnt1
  c2 := fetch self.cnt2
  call Counter.Incr self.cnt1 (c1.count * n + c2.count)
  call Counter.Incr self.cnt2 (c2.count * n + c1.count)
  return self
⟫
```

The Task generated for `Counter.Incr` is:
- parameters: `self : Counter`
- message: `Counter.Incr(self.id, n)`
- action:
  - consumed resources:
    - object resource for `self`,
    - message resource for `Counter.Incr(self.id, n)`
  - created resources:
    - object resource for `{self with count := self.count + n}`.

The message logic for `Counter.Incr` checks if there is exactly one consumed object resource `self`, and exactly one created object resource `self'` with `self' = {self with count := self.count + n}`. The argument `n` is stored in the message resource.

The Task generated for `TwoCounter.MutualIncrement` composes the Tasks for the two calls to `Counter.Incr` with an action that sends the messages (has them as created resources) to the sub-objects and checks the constraints on the `self : TwoCounter` object.
- parameters: `self : TwoCounter, c1 : Counter, c2 : Counter`
- message: `TwoCounter.MutualIncrement(self.id, n)`
- actions:
  1. action for the call to `Counter.Incr` on `self.cnt1`:
	- consumed resources:
    	- object resource for `c1`
    	- message resource for `Counter.Incr(c1.id, c1.count * n + c2.count)`
    - created resources:
    	- object resource for `{c1 with count := c1.count + c1.count * n + c2.count}`
  2. action for the call to `Counter.Incr` on `self.cnt2`:
	- consumed resources:
    	- object resource for `c2`
    	- message resource for `Counter.Incr(c2.id, c2.count * n + c1.count)`
    - created resources:
    	- object resource for `{c2 with count := c2.count + c2.count * n + c1.count}`
  3. action for `TwoCounter.MutualIncrement`:
	- consumed resources:
    	- object resource for `self`
    	- message resource for `TwoCounter.MutualIncrement(n)`
		- object resources for `c1` and `c2`
	- created resources:
    	- object resource for `self`
    	- message resources for `Counter.Incr(c1.id, c1.count * n + c2.count)` and `Counter.Incr(c2.id, c2.count * n + c1.count)`
		- object resources for `c1` and `c2`

In order to ensure the consistency of sub-objects, we include the object resources for `c1` and `c2` in the consumed and created resources of the action for `TwoCounter.MutualIncrement`. See https://github.com/anoma/goose-lean/issues/103.

The message logic for `TwoCounter.MutualIncrement` checks if there is exactly one consumed object resource `self`, and exactly one created object resource `self'` with `self' = self`.

#### Technical details
In the description above, we elided some technical details not essential to the idea of translation, but necessary to implement it correctly for the Anoma Resource Machine.

##### Compliance Units
The generated actions consist of lists of Compliance Units. A Compliance Unit has exactly one consumed and one created resource. To ensure matching numbers of consumed and created resources, dummy ephemeral resources with quantity 0 are put in as placeholders in compliance units.

##### Dummy Resource
Dummy Resource has the unique dummy label and the always-true resource logic.

- `dummyResource` in `AVM/Action/DummyResource.lean`.
- Ephemeral with quantity 0.
- Used as a placeholder in compliance units to ensure that the numbers of consumed and created resource match.
- The nonce is set on creation according to the general rules for assigning nonces to ephemeral resources:
	- consumed dummy resources – random,
	- created dummy resources – nullifier of the consumed resource in the same compliance unit.
- Resource Logic of the Dummy Resource is always true.
- Dummy Resource uses the universal key commitment.

##### Action partitioning
An Action can be considered to contain lists of consumed and created non-dummy resources. We partition Actions into Compliance Units as follows.

- We put every non-dummy consumed resource in a separate compliance unit with a created Dummy Resource.
- We put every non-dummy created resource in a separate compliance unit with a consumed Dummy Resource.
- See: `AVM/Action.lean`.
In what follows, when referring to consumed and created resources of an Action, we implicitly ignore Dummy Resources.

### Constructor

#### Constructor call
Constructor calls are translated to Tasks. The task for a call to a constructor `constr` with arguments `args : constr.Args` is the composition of the tasks for nested calls in constructor body with the constructor action specified by the following.

- `Class.Constructor.task'` in `AVM/Class/Translation/Tasks.lean`.
- Consumed resources:
	- one ephemeral object resource corresponding to the created object `(constr.body args).result`,
	- one ephemeral message resource for the received constructor message, with message arguments set to `args`,
	- persistent object resources corresponding to the objects fetched in the constructor body.
- Created resources:
	- one persistent object resource corresponding to the created object `(constr.body args).result`,
	- ephemeral message resources for all messages sent in the constructor body (corresponding to nested calls),
	- persistent object resources corresponding to the objects fetched in the constructor body.

The IDs of created objects are ensured to be unique by making them equal to the nonce of the consumed ephemeral object resource.

#### Constructor message logic
Constructor message logic is the logic associated with the constructor message. Constructor message logic is implemented in `Class.Constructor.logic` in `AVM/Class/Translation/Logics.lean`.

Constructor message logic has access to RL arguments which contain the following.

- `msgRes : Resource`. The resource of the constructor message. Let `msg := Message.fromResource msgRes`.
- `consumed : List Resource`. List of resources consumed in the action.
- `created : List Resource`. List of resources created in the action.

Constructor message logic for a constructor `constr` performs the following checks.

- `consumed` contains:
	- one ephemeral object resource `res` such that `checkDataEq(res, (constr.body msg.args).result)` holds,
	- persistent object resources corresponding to the objects fetched in the constructor body.
- `created` contains:
	- one persistent object resource `res'` such that `checkDataEq(res', (constr.body msg.args).result)` holds,
	- ephemeral message resources for all messages sent in the constructor body, with arguments matching the arguments to the nested calls.
	- persistent object resources corresponding to the objects fetched in the constructor body.
- `consumed` and `created` may contain more message resources, but not any object resources other than the ones specified above.
- `constr.invariant msg.args` holds.

### Destructor

#### Destructor call
Destructor calls are translated to Tasks. The task for a call to a destructor `destr` on `self : Object` with arguments `args : destr.Args` is the composition of the tasks for nested calls in destructor body with the destructor action specified by the following.

- `Class.Destructor.task'` in `AVM/Class/Translation/Tasks.lean`.
- Consumed resources:
	- one persistent object resource corresponding to `self`,
	- one ephemeral message resource for the received destructor message, with message arguments set to `args`,
	- persistent object resources corresponding to the objects fetched in the destructor body.
- Created resources:
	- one ephemeral object resource corresponding to `self`,
	- ephemeral message resources for all messages sent in the destructor body (corresponding to nested calls),
	- persistent object resources corresponding to the objects fetched in the destructor body.

#### Destructor message logic
Destructor message logic is the logic associated with the destructor message. Destructor message logic is implemented in `Class.Destructor.logic` in `AVM/Class/Translation/Logics.lean`.

Destructor message logic has access to RL arguments which contain the following.

- `msgRes : Resource`. The resource of the destructor message. Let `msg := Message.fromResource msgRes`.
- `consumed : List Resource`. List of resources consumed in the action.
- `created : List Resource`. List of resources created in the action.

Destructor message logic for a destructor `destr` performs the following checks.

- `consumed` contains:
	- one persistent object resource `selfRes` corresponding to the `self` object,
	- persistent object resources corresponding to the objects fetched in the destructor body.
- `created` contains:
	- one emphemeral object resource `selfRes'` and `checkDataEq(selfRes', self.data)` holds,
	- ephemeral message resources for all messages sent in the destructor body, with arguments matching the arguments to the nested calls,
	- persistent object resources corresponding to the objects fetched in the destructor body.
- `consumed` and `created` may contain more message resources, but not any object resources other than the ones specified above.
- `destr.invariant self args` holds.

### Method

#### Method call
Method calls are translated to Tasks. The task for a call to a method `method` on `self : Object` with arguments `args : method.Args` is the composition of the tasks for nested calls in method body with the method action specified by the following.

- `Class.Method.task'` in `AVM/Class/Translation.lean`
- Consumed resources:
	- one persistent object resource corresponding to `self`,
	- one ephemeral message resource for the received method message, with message arguments set to `args`,
	- persistent object resources corresponding to the objects fetched in the method body.
- Created resources:
	- one persistent object resource corresponding to `(method.body self args).result`,
	- ephemeral message resources for all messages sent in the method body (corresponding to nested calls),
	- persistent object resources corresponding to the objects fetched in the method body.

#### Method message logic
Method message logic is the logic associated with the method message. Method message logic is implemented in `Class.Method.logic` in `AVM/Class/Translation/Logics.lean`.

Method message logic has access to RL arguments which contain the following.

- `msgRes : Resource`. The resource of the method message. Let `msg := Message.fromResource msgRes`.
- `consumed : List Resource`. List of resources consumed in the action.
- `created : List Resource`. List of resources created in the action.

Method message logic for a method `method` performs the following checks.

- `consumed` contains:
	- one persistent object resource `selfRes` corresponding to the `self` object,
	- persistent object resources corresponding to the objects fetched in the method body.
- `created` contains:
	- one persistent object resource `selfRes'` and `checkDataEq(selfRes', (method.body self args).result.data)` holds,
	- ephemeral message resources for all messages sent in the method body, with arguments matching the arguments to the nested calls,
	- persistent object resources corresponding to the objects fetched in the method body.
- `consumed` and `created` may contain more message resources, but not any object resources other than the ones specified above.
- `method.invariant self args` holds.

### Upgrade

#### Upgrade call
Upgrade calls are translated to Tasks. The task for an upgrade of `self : Object` to `obj : Object` consists of a single action specified by the following.

- `Class.Upgrade.task'` in `AVM/Class/Translation.lean`
- Consumed resources:
	- one persistent object resource corresponding to `self`,
	- one ephemeral message resource for the received upgrade message, with no arguments.
- Created resources:
	- one persistent object resource corresponding to `obj`.

#### Upgrade message logic
Upgrade message logic is the logic associated with the upgrade message. Upgrade message logic is implemented in `Class.Upgrade.logic` in `AVM/Class/Translation/Logics.lean`.

Upgrade message logic has access to RL arguments which contain the following.

- `consumed : List Resource`. List of resources consumed in the action.
- `created : List Resource`. List of resources created in the action.

Upgrade message logic performs the following checks.

- `consumed` contains exactly one persistent object resource `selfRes` corresponding to the `self` object.
- `created` contains exactly one persistent object resource `objRes` corresponding to the `obj` upgraded object.
- `obj.id = self.id` and the class of `obj` is the same as the class of `self` but with higher version.
- `consumed` and `created` may contain more message resources, but not any object resources other than the ones specified above.

### Multi-method

#### Multi-method call
Multi-method calls are translated to Tasks. The task for a call to a multi-method `multiMethod` on `selves : List Object` with arguments `args : multiMethod.Args` is the composition of the tasks for nested calls in multi-method body with the multi-method action specified by the following.

- `Ecosystem.MultiMethod.task'` in `AVM/Ecosystem/Translation/Tasks.lean`
- Consumed resources:
	- persistent object resources corresponding to `selves` (these consist of disassmbled and destroyed object resources),
	- ephemeral object resources corresponding to the constructed objects `(multiMethod.body selves args).result.constructed`.
	- one ephemeral message resource for the received multi-method message, with message arguments set to `args`,
	- persistent object resources corresponding to the objects fetched in the multi-method body.
- Created resources:
	- persistent object resources corresponding to the assembled objects `(multiMethod.body selves args).result.assembled`,
	- ephemeral object resources corresponding to the destroyed objects `(multiMethod.body selves args).result.destroyed`,
	- persistent object resources corresponding to the constructed objects `(multiMethod.body selves args).result.constructed`,
	- ephemeral message resources for all messages sent in the multi-method body (corresponding to nested calls),
	- persistent object resources corresponding to the objects fetched in the multi-method body.

#### Multi-method message logic
Multi-method message logic is the logic associated with the multi-method message. Multi-method message logic is implemented in `Ecosystem.MultiMethod.logic` in `AVM/Class/Translation/Logics.lean`.

Multi-method message logic has access to RL arguments which contain the following.

- `consumed : List Resource`. List of resources consumed in the transaction.
- `created : List Resource`. List of resources created in the transaction.
- `msgRes : Resource`. The resource of the method message `msg`, which contains the method call arguments `args` and parameter values `vals`.

For a given multi-method, the number `n` of `selves` is specified in the
multi-method definition. We re-create the `selves` objects from the first `n`
object resources in `consumed`.

With `selves`, `args` and `vals`, we compute the result of of the multi-method. In this way, we obtain the numbers of:
  - disassembled selves,
  - destroyed selves,
  - constructed objects.

We use the above numbers to partition the object resources in `consumed` into:

- `disassembledSelves` list of persistent object resources corresponding to disassembled selves,
- `destroyedSelves` list of persistent object resources corresponding to destroyed selves,
- `constructedEph` list of ephemeral object resources corresponding to constructed objects,
- `fetchedConsumed` list of persistent object resources corresponding to the objects fetched in the multi-method body.

We re-create the `selves` objects from `disassembledSelves` and `destroyedSelves`.

Similarly, the `created` list is partitioned into:

- `assembled` list of persistent object resources corresponding to the selves reassembled in the function body,
- `destroyedEph` list of ephemeral object resources corresponding to the selves destroyed by the function,
- `constructed` list of persistent object resources corresponding to the objects constructed in the function body,
- `fetchedCreated` list of persistent object resources corresponding to the objects fetched in the multi-method body.

Multi-method message logic for a multi-method `multiMethod` performs the following checks.

- `checkDataEq(res, obj)` holds pairwise for `(res, obj)` in `zip assembled (multiMethod.body selves msg.args).result.assembled`.
- `checkDataEq(res, obj)` holds pairwise for `(res, obj)` in `zip destroyedEph (multiMethod.body selves msg.args).result.destroyed`.
- `checkDataEq(res, obj)` holds pairwise for `(res, obj)` in `zip constructed (multiMethod.body selves msg.args).result.constructed`.
- `checkDataEq(res, obj)` holds pairwise for `(res, obj)` in `zip constructedEph (multiMethod.body selves msg.args).result.constructed`.
- `checkDataEq(res, obj)` holds pairwise for `(res, obj)` in `zip destroyed (multiMethod.body selves args).result.destroyed`.
- `checkDataEq(res, obj)` holds pairwise for `(res, obj)` in `zip destroyedEph (multiMethod.body selves args).result.destroyed`.
- resources in `fetchedConsumed` correspond to the objects fetched in the multi-method body.
- resources in `fetchedCreated` correspond to the objects fetched in the multi-method body.
- resources in `assembledSelves` are persistent.
- resources in `destroyedSelves` are persistent.
- resources in `constructedEph` are ephemeral.
- resources in `destroyed` are persistent.
- resources in `assembled` are persistent.
- resources in `destroyedEph` are ephemeral.
- resources in `constructed` are persistent.
- resources in `fetchedConsumed` are persistent.
- resources in `fetchedCreated` are persistent.
- `multiMethod.invariant selves msg.args` holds.

### Function invocation

Invoking functions (sub-programs) is handled by simply recursively processing the invoked sub-program, i.e., by program composition.
- `AVM.Program.invoke` in `AVM/Program.lean`.
- Thanks to the use of continuations to represent program sequencing, compilation is interleaved with object fetching and object id generation. At the point of compiling a function invocation, all arguments to the invocation are known and we can process the function body program recursively. The arguments to the invocation may depend on the fetched objects and ids generated, but these have been already resolved.

### Class logic
Class logic is the logic associated with a class. Class logic is implemented in `Class.logic` in `AVM/Class/Translation/Logics.lean`.

Class logic has access to RL arguments `logicArgs : Logic.Args` which contain the following.

- `selfRes` consumed resource corresponding to the `self` object of this class.
- `consumed : List Resource`. List of resources consumed in the action.
- `created : List Resource`. List of resources created in the action.

The `self` object is re-created from `selfRes`.

Class logic for a class `cls` performs the following checks.

- `consumed` contains exactly one message resource corresponding to a message `msg` in the ecosystem of the class.
- `self.id` is in `msg.recipients`.
- `msg.recipients.length` is equal to the number of object resources in `consumed`.
- `cls.invariant self logicArgs` holds.

## Translation issues and limitations

- Objects can be upgraded by anyone and no data preservation is checked on upgrade, except that the class version increases and the id is preserved. Hence, someone could upgrade an object to one with different essential fields, e.g., owner. We need some form of access control to limit object upgrade to the object owner or other authorized principals.

## Implemented example apps

- Counter: `Apps/UniversalCounter.lean`.
	- A universal counter which can be created with zero count and incremented by anyone.
	- Demonstrates the use of multi-methods:
		- merging two counters to create a new one.
- Owned counter: `Apps/OwnerCounter.lean`.
	- Counter with ownership.
	- Constructor: create with count zero.
	- Destructor: destroy when count $\ge 10$.
	- Methods: increment, transfer ownership.
- TwoCounter: `Apps/TwoCounter.lean`
    - TwoCounter is an object with two Counter sub-objects.
    - Demonstrates the use of sub-objects and nested calls:
        - incrementing both sub-object Counters in a TwoCounter.
- Kudos: `Apps/Kudos.lean`.
	- Kudos with ownership.
	- Kudos token has: quantity, originator, owner.
	- Operations: mint, burn, transfer.
	- Multi-methods: split, merge.
- Kudos bank: `Apps/KudosBank.lean`.
	- Kudos app implemented with a single object KudosBank which tracks all kudo balances.
	- Operations: open, close, mint, burn, transfer.
	- Multi-methods:
    	- cheques: issue, deposit.
        - auctions: new, bid, end.
