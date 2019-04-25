# Note on sf1-lf

## Basics.v

### Keywords
- `Inductive`: define a type of type `Type`
- `Definition`: define functions
- `Compute`: evaluate expressions
- `Example`: example with a name and an assertion 
- `Proof. Qed.`: proof
- `Check`: print the type info
- `Module X.` `End X.`
- `Fixpoint`: define recursive functions

### Proof
- `simpl`
- `reflexivity`

### List of Types, Definitions, Notations, (Useful) Examples
- `Inductive day : Type`
- `Defintion next_weekday (d: day) : day`
-
- `Inductive bool : Type`
- `Defintion negb (b: bool) : bool`
- `Definition andb (b: bool) : bool`
- `Definition orb (b: bool) : bool`
- `Notation "x && y"`
- `Notation "x || y"`
- `Definition andb3`
- 
- `Inductive rgb : Type`
- `Inductive color : Type`
- `Definition monochrome (c: color) : bool`
- `Definition isred (c: color) : bool`
- 
- `Inductive bit : Type`
- `Inductive nybble : Type`
- `Definition all_zero (nb : nybble) : bool`
-  
- `Module NatPlayground.`
- `Inductive nat : Type`
- `Definition pred (n : nat) : nat`
- `End NatPlayground.`
- 
- `Definition minustwo (n : nat) : nat` 
- `Fixpoint evenb (n : nat) : bool`
- `Definition oddb (n : nat) : bool`
-  
- `Module NatPlayground2.`
- `Fixpoint plus (n : nat) (m : nat) : nat`
- `Fixpoint Mult (n m : nat) : nat`
- `Fixpoint minus (n m : nat) : nat`
- `End NatPlayground2.`
-  
- `Fixpoint exp (base power : nat) : nat`
- `Fixpoint factorial (n : nat) : nat`
