# Logic in Coq (Logic.v)

## Keywords
- `Prop`: `Type` for propositions
- 
## Tactics
- `split`: to prove a conjunction
- `destruct (A /\ B) as [HA HB].`: remove `A /\ B` from the context and add two new hypotheses `HA`, stating that `A` is true, and `HB`, stating that `B` is true
- `intros [HA HB].`
- `intros [HP [HQ HR]].`


## Defintions and Theorems
### `Prop`
- `Definition injective {A B : Type} (f : A -> B) := forall x y : A, f x = f y -> x = y.`
- `Lemma succ_inj : injective S.`

### Logical Connectives
#### Conjunction
- `Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.`
- `Example and_exercise : forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.`
- `Lemma proj1 : forall P Q : Prop, P /\ Q -> P.`
- `Lemma proj2 : forall P Q : Prop, P /\ Q -> Q.`
- `Theorem and_commut : forall P Q : Prop, P /\ Q -> Q /\ P.`
- `Theorem and_assoc : forall P Q : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.`
#### Disjunction

## Problems

> Written with [StackEdit](https://stackedit.io/).
