import Mathlib.Order.TypeTags
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.Finmap
import Aesop

abbrev Node := WithTop ℕ
abbrev ω : Node := ⊤
instance (n : ℕ) : OfNat Node n where
  ofNat := some n

abbrev Edge := Option ℕ

instance : DecidableEq Node := by unfold Node WithTop; infer_instance
instance : DecidableEq Edge := by unfold Edge; infer_instance

structure PreChain where
  nodes : List Node
  edges : List Edge
  hlength : nodes.length = edges.length + 1
deriving DecidableEq

lemma PreChain.nodeAtLeast1 (chain : PreChain) : 0 < chain.nodes.length := by
  rw [chain.hlength]
  simp

def PreChain.reverse (chain : PreChain) : PreChain where
  nodes := chain.nodes.reverse
  edges := chain.edges.reverse
  hlength := by simpa using chain.hlength

def PreChain.first (chain : PreChain) : Node :=
  have : 0 < chain.nodes.length := chain.nodeAtLeast1
  chain.nodes[0]

def PreChain.last (chain : PreChain) : Node :=
  chain.nodes.getLast (by
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

def PreChain.isSubChainAt (small large : PreChain) (bNodeIndex : ℕ) : Prop :=
  (List.range small.edges.length).attach.Forall (fun i ↦ by
    have : i.val < small.edges.length := by aesop
    exact some small.edges[i.val] = large.edges[bNodeIndex + i.val]?
  ) ∧ (List.range small.nodes.length).attach.Forall (fun i ↦ by
    have : i.val < small.nodes.length := by aesop
    exact some small.nodes[i.val] = large.nodes[bNodeIndex + i.val]?
  )

instance (small large : PreChain) (bNodeIndex : ℕ)
    : Decidable <| PreChain.isSubChainAt small large bNodeIndex := by
  unfold PreChain.isSubChainAt;
  infer_instance

def PreChain.isSubChain (small large : PreChain) : Prop :=
  (¬ (List.range large.nodes.length).Forall (fun i ↦ ¬ PreChain.isSubChainAt small large i)) ∨
  (¬ (List.range large.nodes.length).Forall (fun i ↦ ¬ PreChain.isSubChainAt small.reverse large i))

instance (small large : PreChain)
    : Decidable <| PreChain.isSubChain small large := by
  unfold PreChain.isSubChain
  infer_instance

def PreChain.singleton (node : Node) : PreChain where
  nodes := [node]
  edges := []
  hlength := by simp

def PreChain.append (chain : PreChain) (edge : Edge) (node : Node) :
    PreChain where
  nodes := chain.nodes ++ [node]
  edges := chain.edges ++ [edge]
  hlength := by simpa using chain.hlength

def PreChain.concat (a b : PreChain) (_ : a.last = b.first) : PreChain where
  nodes := a.nodes ++ b.nodes.eraseIdx 0
  edges := a.edges ++ b.edges
  hlength := by
    simp only [List.eraseIdx_zero, List.length_append, List.length_tail]
    rw [a.hlength, b.hlength]
    simpa using Nat.add_right_comm _ _ _

def PreChain.setEdge (chain : PreChain) (edgeIndex : ℕ) (edge : Edge) :
    PreChain where
  nodes := chain.nodes
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

inductive Item
| Key (lock : ℕ) : Item
| KeyOnce (lock : ℕ) : Item
deriving DecidableEq

abbrev ItemSet := { x : Multiset Item // x ≠ ∅ }

def ItemMap := Finmap (fun (_ : Node) ↦ ItemSet)
deriving DecidableEq

instance : EmptyCollection ItemMap where
  emptyCollection := Finmap.instEmptyCollection.emptyCollection

instance : GetElem ItemMap Node (Multiset Item) (fun _ _ ↦ True) where
  getElem map i _ := ((map.lookup i).map (·.val)).getD ∅

def ItemMap.set (itemMap : ItemMap) (node : Node) (items : Multiset Item) : ItemMap :=
  if h : items ≠ ∅ then
    itemMap.insert node ⟨items, h⟩
  else
    itemMap.erase node

def ItemMap.update (itemMap : ItemMap) (node : Node) (updater : Multiset Item → Multiset Item) : ItemMap :=
  itemMap.set node <| updater <| itemMap[node]

abbrev im (itemMap : List (Node × (List Item))) : ItemMap :=
  (itemMap.map (fun entry ↦ (entry.1, (entry.2 : Multiset Item)))).foldl
    (fun itemMap e ↦ itemMap.set e.1 e.2) ∅

notation:50 " K(" k:50 ") " => Item.Key k
notation:50 " K*(" k:50 ") " => Item.KeyOnce k
example : Multiset Item := [K(2), K*(3), K(2)]

example : ((im [(4, [K(2), K*(3), K(2)]), (3, [K*(9)])]).set 7 [K(8)]).set 3 ∅ =
    im [(7, [K(8)]), (5, []), (4, [K(2), K(2), K*(3)])] := by
  decide +native

structure Level where
  chains : Multiset Chain
  itemMap : ItemMap
deriving DecidableEq

abbrev lv (chains : List PreChain) (itemMap : ItemMap) : Level where
  chains := (chains : List Chain)
  itemMap := itemMap

opaque beatable (level: Level) : Prop
