import Mathlib.Data.Nat.Notation
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.Finmap
import Aesop

/-!
Vertex are numbers & the special one ω. We use Option as the underlying type for convenience.
-/
abbrev Vertex := Option ℕ
instance : DecidableEq Vertex := by unfold Vertex; infer_instance
abbrev ω : Vertex := none
instance (n : ℕ) : OfNat Vertex n where
  ofNat := some n

/-!
An edge is either simple or with a lock. A lock is also represented by a number.
-/
abbrev Edge := Option ℕ
instance : DecidableEq Edge := by unfold Edge; infer_instance

/-!
A chain is a list of vertices and edges interleaved together.
To avoid reinventing new types, we use two separate lists with
a hypothesis to ensure the lengths are correct.

Note that we only call it "pre"-chain here, because it is not the real type
we want to sotre in the map. A real chain has an equivalent relation with its
inverse, so we need to create a quotient type later, which we will call `Chain`.
`PreChain` is used for all axiom inputs.
-/
structure PreChain where
  vertices : List Vertex
  edges : List Edge
  hlength : vertices.length = edges.length + 1
deriving DecidableEq

/-!
Some utility lemmas and methods for chains
-/
lemma PreChain.nodeAtLeast1 (chain : PreChain) : 0 < chain.vertices.length := by
  rw [chain.hlength]
  simp

def PreChain.reverse (chain : PreChain) : PreChain where
  vertices := chain.vertices.reverse
  edges := chain.edges.reverse
  hlength := by simpa using chain.hlength

def PreChain.first (chain : PreChain) : Vertex :=
  have : 0 < chain.vertices.length := chain.nodeAtLeast1
  chain.vertices[0]

def PreChain.last (chain : PreChain) : Vertex :=
  chain.vertices.getLast (by
    obtain atLeast1 := chain.nodeAtLeast1
    contrapose! atLeast1 with empty
    rw [empty]
    simp
  )

def PreChain.lockless (chain : PreChain) : Prop :=
  chain.edges.all (fun edge ↦ edge = none)

instance (chain : PreChain) : Decidable chain.lockless := by
  unfold PreChain.lockless
  infer_instance

/-!
Some axioms concerns about subchains, which we define here.
Note the final version `isSubChain` also allows inverse order,
which provides convinience for axioms without consulting the quotient type.
-/
def PreChain.isSubChainAt (small large : PreChain) (bNodeIndex : ℕ) : Prop :=
  (List.range small.edges.length).attach.Forall (fun i ↦ by
    have : i.val < small.edges.length := by aesop
    exact some small.edges[i.val] = large.edges[bNodeIndex + i.val]?
  ) ∧ (List.range small.vertices.length).attach.Forall (fun i ↦ by
    have : i.val < small.vertices.length := by aesop
    exact some small.vertices[i.val] = large.vertices[bNodeIndex + i.val]?
  )

instance (small large : PreChain) (bNodeIndex : ℕ)
    : Decidable <| PreChain.isSubChainAt small large bNodeIndex := by
  unfold PreChain.isSubChainAt;
  infer_instance

def PreChain.isSubChain (small large : PreChain) : Prop :=
  (¬ (List.range large.vertices.length).Forall (fun i ↦ ¬ PreChain.isSubChainAt small large i)) ∨
  (¬ (List.range large.vertices.length).Forall (fun i ↦ ¬ PreChain.isSubChainAt small.reverse large i))

instance (small large : PreChain)
    : Decidable <| PreChain.isSubChain small large := by
  unfold PreChain.isSubChain
  infer_instance

/-!
We create methods to construct and update chains, as well as custom notation for them.
-/
def PreChain.singleton (vertex : Vertex) : PreChain where
  vertices := [vertex]
  edges := []
  hlength := by simp

def PreChain.append (chain : PreChain) (edge : Edge) (vertex : Vertex) :
    PreChain where
  vertices := chain.vertices ++ [vertex]
  edges := chain.edges ++ [edge]
  hlength := by simpa using chain.hlength

def PreChain.concat (a b : PreChain) (_ : a.last = b.first) : PreChain where
  vertices := a.vertices ++ b.vertices.eraseIdx 0
  edges := a.edges ++ b.edges
  hlength := by
    simp only [List.eraseIdx_zero, List.length_append, List.length_tail]
    rw [a.hlength, b.hlength]
    simpa using Nat.add_right_comm _ _ _

def PreChain.setEdge (chain : PreChain) (edgeIndex : ℕ) (edge : Edge) :
    PreChain where
  vertices := chain.vertices
  edges := chain.edges.set edgeIndex edge
  hlength := by simpa using chain.hlength

notation:50 "$" u:60 => PreChain.singleton u
notation:50 u " ~L(" l:50 ")~ " v:60 => PreChain.append u (some l) v
notation:50 u " ~~ " v:60 => PreChain.append u none v

example : ($3 ~~ 1 ~L(4)~ ω).reverse = ($ ω ~L(4)~ 1 ~~ 3) := by decide
example : ($3 ~~ 1 ~L(4)~ ω).first = 3 := by decide
example : ($3 ~~ 1 ~L(4)~ ω).last = ω := by decide
example : ($2 ~L(5)~ 3 ~L(7)~ 4).isSubChain ($2 ~L(5)~ 3 ~L(7)~ 4 ~~ 5) := by decide
example : ($2 ~L(5)~ 3 ~L(7)~ 4 ~~ 5).isSubChain ($2 ~L(5)~ 3 ~L(7)~ 4 ~~ 5) := by decide
example : ($4 ~~ 5).isSubChain ($2 ~L(5)~ 3 ~L(7)~ 4 ~~ 5) := by decide
example : ($4).isSubChain ($2 ~L(5)~ 3 ~L(7)~ 4 ~~ 5) := by decide
example : ($3 ~L(7)~ 4).isSubChain ($2 ~L(5)~ 3 ~L(7)~ 4 ~~ 5) := by decide
example : ¬ ($3 ~L(7)~ 4).isSubChain ($2 ~L(5)~ 3 ~~ 4 ~~ 5) := by decide
example : ¬ ($4 ~~ 5 ~~ 6).isSubChain ($2 ~L(5)~ 3 ~~ 4 ~~ 5) := by decide
example : ($1 ~L(3)~ ω ~~ 7).concat ($7 ~~ 5 ~L(0)~ 1) (by decide) = ($1 ~L(3)~ ω ~~ 7 ~~ 5 ~L(0)~ 1) := by decide
example : ($4 ~~ 5 ~~ 6).setEdge 1 (some 3) = ($4 ~~ 5 ~L(3)~ 6) := by decide

/-!
We create the real chain type as a quotient.
-/
instance PreChainSetoid : Setoid PreChain where
  r := fun a b ↦ a = b ∨ a = b.reverse
  iseqv := {
    refl := by unfold PreChain.reverse; aesop
    symm := by unfold PreChain.reverse; aesop
    trans := by unfold PreChain.reverse; aesop
  }

instance (a b : PreChain) : Decidable (a ≈ b) := by
  unfold HasEquiv.Equiv instHasEquivOfSetoid PreChainSetoid
  simp
  infer_instance

abbrev Chain := Quotient PreChainSetoid

instance : DecidableEq Chain := by
  intro _ _
  infer_instance

instance : Coe PreChain Chain where
  coe := Quotient.mk'

example : ($3 ~~ 1 ~L(4)~ ω: Chain) = ($ ω ~L(4)~ 1 ~~ 3: Chain) := by decide

/-!
An item is a key for multiple times or a key for once.
-/
inductive Item
| Key (lock : ℕ) : Item
| KeyOnce (lock : ℕ) : Item
deriving DecidableEq

/-!
An `ItemMap` assigns keys to vertices. To maintain a normal form,
we require that the keys are not empty for each entry.
-/
abbrev ItemSet := { x : Multiset Item // x ≠ ∅ }

def ItemMap := Finmap (fun (_ : Vertex) ↦ ItemSet)
deriving DecidableEq

instance : EmptyCollection ItemMap where
  emptyCollection := Finmap.instEmptyCollection.emptyCollection

instance : GetElem ItemMap Vertex (Multiset Item) (fun _ _ ↦ True) where
  getElem map i _ := ((map.lookup i).map (·.val)).getD ∅

def ItemMap.set (itemMap : ItemMap) (vertex : Vertex) (items : Multiset Item) : ItemMap :=
  if h : items ≠ ∅ then
    itemMap.insert vertex ⟨items, h⟩
  else
    itemMap.erase vertex

def ItemMap.update (itemMap : ItemMap) (vertex : Vertex) (updater : Multiset Item → Multiset Item) : ItemMap :=
  itemMap.set vertex <| updater <| itemMap[vertex]

abbrev im (itemMap : List (Vertex × (List Item))) : ItemMap :=
  (itemMap.map (fun entry ↦ (entry.1, (entry.2 : Multiset Item)))).foldl
    (fun itemMap e ↦ itemMap.set e.1 e.2) ∅

/-!
Also some custom notation for items
-/
notation:50 " K(" k:50 ") " => Item.Key k
notation:50 " K*(" k:50 ") " => Item.KeyOnce k
example : Multiset Item := [K(2), K*(3), K(2)]

example : ((im [(4, [K(2), K*(3), K(2)]), (3, [K*(9)])]).set 7 [K(8)]).set 3 ∅ =
    im [(7, [K(8)]), (5, []), (4, [K(2), K(2), K*(3)])] := by
  decide +native

/-!
A level is a collection of chains and an item map.
-/
structure Level where
  chains : Multiset Chain
  itemMap : ItemMap
deriving DecidableEq

abbrev lv (chains : List PreChain) (itemMap : ItemMap) : Level where
  chains := (chains : List Chain)
  itemMap := itemMap

/-!
The proposition of "you can win".
-/
opaque beatable (level: Level) : Prop
