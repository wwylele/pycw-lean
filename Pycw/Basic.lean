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

axiom Axiom1 (chain : PreChain) (itemMap : ItemMap)
  (h0 : chain.first = 0) (hω : chain.last = ω) (hlock : chain.lockless) :
  beatable (lv [chain] itemMap)

axiom Rule1_1 (level : Level) (h : beatable level) (chain : PreChain) :
  beatable {
    chains := chain ::ₘ level.chains,
    itemMap := level.itemMap
  }

axiom Rule1_2 (level : Level) (h : beatable level) (a b : PreChain)
  (hab : a.isSubChain b) (hmem : ([(a : Chain), (b : Chain)] : Multiset Chain) ≤ level.chains) :
  beatable {
    chains := level.chains.erase a,
    itemMap := level.itemMap
  }

axiom Rule1_3 (level : Level) (h : beatable level) (a b : PreChain) (hab : a.last = b.first)
  (hmem : ⟦a.concat b hab⟧ ∈ level.chains) :
  beatable {
    chains := a ::ₘ b ::ₘ (level.chains.erase ⟦(a.concat b hab)⟧),
    itemMap := level.itemMap
  }


lemma Lemma1 (level : Level) (chain : PreChain) (h0 : chain.first = 0) (hω : chain.last = ω)
    (hlock : chain.lockless) (hmem : ⟦chain⟧ ∈ level.chains) : beatable level := by
  if h : level.chains == [ (chain : Chain) ] then
    convert Axiom1 chain level.itemMap h0 hω hlock
    simp only [Multiset.coe_singleton, beq_iff_eq] at h
    unfold lv
    simp [← h]
  else
    let rest_chains := level.chains.erase ⟦chain⟧
    have rest_nonempty : rest_chains ≠ ∅ := by
      unfold rest_chains
      contrapose! h with hempty
      simp only [Multiset.coe_singleton, beq_iff_eq]
      obtain hmem' := Multiset.cons_erase hmem
      rw [hempty] at hmem'
      rw [← hmem']
      simp only [Multiset.empty_eq_zero, Multiset.cons_zero, Multiset.singleton_inj]
      rfl
    obtain ⟨another, ha⟩ := Multiset.exists_mem_of_ne_zero rest_nonempty
    obtain hrec := Lemma1 {
      chains := level.chains.erase another
      itemMap := level.itemMap
    } chain h0 hω hlock (by
      simp only
      by_cases heq : chain = another
      · rw [← heq] at ⊢ ha
        unfold rest_chains at ha
        exact ha
      · exact (Multiset.mem_erase_of_ne heq).mpr hmem
    )
    convert Rule1_1 _ hrec another.out
    simp
    symm
    have anotherrw : Quotient.mk' (Quotient.out another) = another := by
      exact Quotient.out_eq another
    rw [anotherrw]
    apply Multiset.cons_erase
    exact Multiset.mem_of_mem_erase ha
termination_by level.chains.card
decreasing_by
  apply Multiset.card_erase_lt_of_mem
  exact Multiset.mem_of_mem_erase ha

theorem Prop1_1 : beatable (lv [($0 ~~ 1 ~~ 2 ~~ ω)] ∅) := by
  apply Lemma1 _ ($0 ~~ 1 ~~ 2 ~~ ω)
  all_goals decide

theorem Prop1_2 : beatable (lv [($2 ~~ 1 ~~ 0 ~~ ω ~~ 3)] ∅) := by
  have h : beatable (lv [($2 ~~ 1 ~~ 0 ~~ ω ~~ 3), ($0 ~~ ω)] ∅) := by
    apply Lemma1 _ ($0 ~~ ω)
    all_goals decide
  convert Rule1_2 _ h ($0 ~~ ω) ($2 ~~ 1 ~~ 0 ~~ ω ~~ 3) (by decide) (by decide)

theorem Prop1_3 : beatable (lv [($0 ~~ 1 ~~ 2), ($1 ~~ 2 ~~ ω)] ∅) := by
  have h : beatable (lv [($0 ~~ 1 ~~ 2), ($0 ~~ 1 ~~ 2 ~~ ω)] ∅) := by
    convert Rule1_1 _ Prop1_1 ($0 ~~ 1 ~~ 2)
  have h2 : beatable (lv [($0 ~~ 1 ~~ 2), ($0 ~~ 1), ($1 ~~ 2 ~~ ω)] ∅) := by
    convert Rule1_3 _ h ($0 ~~ 1) ($1 ~~ 2 ~~ ω) (by decide) (by decide)
    decide
  convert Rule1_2 _ h2 ($0 ~~ 1) ($0 ~~ 1 ~~ 2) (by decide) (by decide)

theorem Prop1_4 : beatable (lv [($2 ~~ 6 ~~ 2), ($0 ~~ 1 ~~ 2 ~~ 3), ($4 ~~ 5 ~~ 6 ~~ 7 ~~ ω)] ∅) := by
  suffices beatable (lv [($2 ~~ 6), ($0 ~~ 1 ~~ 2 ~~ 3), ($4 ~~ 5 ~~ 6 ~~ 7 ~~ ω)] ∅) by
    obtain h := Rule1_1 _ this ($2 ~~ 6 ~~ 2)
    convert Rule1_2 _ h ($2 ~~ 6) ($2 ~~ 6 ~~ 2) (by decide) (by decide)
  suffices beatable (lv [($2 ~~ 6), ($0 ~~ 1 ~~ 2), ($4 ~~ 5 ~~ 6 ~~ 7 ~~ ω)] ∅) by
    obtain h := Rule1_1 _ this ($0 ~~ 1 ~~ 2 ~~ 3)
    convert Rule1_2 _ h ($0 ~~ 1 ~~ 2) ($0 ~~ 1 ~~ 2 ~~ 3) (by decide) (by decide)
    decide
  suffices beatable (lv [($2 ~~ 6), ($0 ~~ 1 ~~ 2), ($6 ~~ 7 ~~ ω)] ∅) by
    obtain h := Rule1_1 _ this ($4 ~~ 5 ~~ 6 ~~ 7 ~~ ω)
    convert Rule1_2 _ h ($6 ~~ 7 ~~ ω) ($4 ~~ 5 ~~ 6 ~~ 7 ~~ ω) (by decide) (by decide)
    decide
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~~ 6), ($6 ~~ 7 ~~ ω)] ∅) by
    convert Rule1_3 _ this ($0 ~~ 1 ~~ 2) ($2 ~~ 6) (by decide) (by decide)
    decide
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~~ 6 ~~ 7 ~~ ω)] ∅) by
    convert Rule1_3 _ this ($0 ~~ 1 ~~ 2 ~~ 6) ($6 ~~ 7 ~~ ω) (by decide) (by decide)
  apply Lemma1 _ ($0 ~~ 1 ~~ 2 ~~ 6 ~~ 7 ~~ ω)
  all_goals decide


axiom Rule2_1 (level : Level) (h : beatable level) (a b : PreChain) (lock : ℕ) (bEdgeIndex : ℕ)
  (ha : a.first = 0) (hkey : Item.Key lock ∈ level.itemMap[a.last])
  (hmem : ([(a : Chain), (b : Chain)] : Multiset Chain) ≤ level.chains)
  (hindex : bEdgeIndex < b.edges.length)
  (hlock : b.edges[bEdgeIndex] = none) :
  beatable {
    chains := (b.setEdge bEdgeIndex (some lock)) ::ₘ (level.chains.erase ⟦b⟧),
    itemMap := level.itemMap
  }

axiom Rule2_2 (level : Level) (h : beatable level) (chain : PreChain) (key : ℕ)
  (hkey : Item.KeyOnce key ∈ level.itemMap[chain.first])
  (hmem : ⟦chain⟧ ∈ level.chains)
  (hlock : chain.lockless) :
  beatable {
    chains := level.chains,
    itemMap := level.itemMap.update
      chain.first (·.erase (Item.KeyOnce key)) |>.update
      chain.last ((Item.KeyOnce key) ::ₘ ·)
  }

axiom Rule2_3 (level : Level) (h : beatable level) (a b : PreChain) (lock : ℕ)
  (ha : a.first = 0) (hab : a.last = b.first) (hb : b.edges.length = 1)
  (hmem : ([(a : Chain), (b : Chain)] : Multiset Chain) ≤ level.chains) :
  beatable {
    chains := (b.setEdge 0 (some lock)) ::ₘ (level.chains.erase b),
    itemMap := level.itemMap.update a.last ((Item.KeyOnce lock) ::ₘ ·)
  }

theorem Prop2_1 : beatable (lv [($1 ~~ 2), ($0 ~~ 1 ~L(0)~2 ~~ ω)] ∅) := by
  suffices beatable (lv [($1 ~~ 2), ($0 ~~ 1 ~L(0)~ 2 ~~ ω), ($0 ~~ 1)] ∅) by
    convert Rule1_2 _ this ($0 ~~ 1) ($0 ~~ 1 ~L(0)~ 2 ~~ ω) (by decide) (by decide)
  suffices beatable (lv [($1 ~~ 2), ($0 ~~ 1 ~L(0)~ 2 ~~ ω), ($0 ~~ 1), ($2 ~~ ω)] ∅) by
    convert Rule1_2 _ this ($2 ~~ ω) ($0 ~~ 1 ~L(0)~ 2 ~~ ω) (by decide) (by decide)
  suffices beatable (lv [($0 ~~ 1 ~~ 2), ($0 ~~ 1 ~L(0)~ 2 ~~ ω), ($2 ~~ ω)] ∅) by
    convert Rule1_3 _ this ($0 ~~ 1) ($1 ~~ 2) (by decide) (by decide)
    decide
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~~ ω), ($0 ~~ 1 ~L(0)~ 2 ~~ ω)] ∅) by
    convert Rule1_3 _ this ($0 ~~ 1 ~~ 2) ($2 ~~ ω) (by decide) (by decide)
    decide
  apply Lemma1 _ ($0 ~~ 1 ~~ 2 ~~ ω)
  all_goals decide

theorem Prop2_2 : beatable (lv [($0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω)] <| im [(2, [K(0)])]) := by
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω), ($0 ~~ 1 ~~ 2)] <| im [(2, [K(0)])]) by
    convert Rule1_2 _ this ($0 ~~ 1 ~~ 2) ($0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω) (by decide) (by decide)
  have h : beatable (lv [($0 ~~ 1 ~~ 2 ~~ 3 ~~ ω), ($0 ~~ 1 ~~ 2)] <| im [(2, [K(0)])]) := by
    apply Lemma1 _ ($0 ~~ 1 ~~ 2 ~~ 3 ~~ ω)
    all_goals decide
  convert Rule2_1 _ h ($0 ~~ 1 ~~ 2) ($0 ~~ 1 ~~ 2 ~~ 3 ~~ ω) 0 3 (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem Prop2_3 : beatable (lv [($2 ~~ 4), ($0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω)] <| im [(4, [K(0)])]) := by
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~~ 4), ($0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω)] <| im [(4, [K(0)])]) by
    obtain h := Rule1_3 _ this ($0 ~~ 1 ~~ 2) ($2 ~~ 4) (by decide) (by decide)
    convert Rule1_2 _ h ($0 ~~ 1 ~~ 2) ($0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω) (by decide) (by decide)
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~~ 4), ($0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω)] <| im [(4, [K(0)])]) by
    convert Rule2_1 _ this ($0 ~~ 1 ~~ 2 ~~ 4) ($0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω) 0 2
      (by decide) (by decide) (by decide) (by decide) (by decide)
    decide
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~~ 4), ($0 ~~ 1 ~~ 2 ~~ 3 ~~ ω)] <| im [(4, [K(0)])]) by
    convert Rule2_1 _ this ($0 ~~ 1 ~~ 2 ~~ 4) ($0 ~~ 1 ~~ 2 ~~ 3 ~~ ω) 0 3
      (by decide) (by decide) (by decide) (by decide) (by decide)
    decide
  apply Lemma1 _ ($0 ~~ 1 ~~ 2 ~~ 3 ~~ ω)
  all_goals decide

theorem Prop2_4 :
    beatable (lv [($2 ~~ 4 ~L(1)~ 5), ($0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω)] <| im [(3, [K(1)]), (5, [K(0)])]) := by

  suffices beatable (lv [($2 ~~ 4 ~L(1)~ 5), ($0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω), ($0 ~~ 1 ~~ 2 ~~ 3)]
      <| im [(3, [K(1)]), (5, [K(0)])]) by
    convert Rule1_2 _ this ($0 ~~ 1 ~~ 2 ~~ 3) ($0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω) (by decide) (by decide)
  suffices beatable (lv [($2 ~~ 4 ~~ 5), ($0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω), ($0 ~~ 1 ~~ 2 ~~ 3)]
      <| im [(3, [K(1)]), (5, [K(0)])]) by
    convert Rule2_1 _ this ($0 ~~ 1 ~~ 2 ~~ 3) ($2 ~~ 4 ~~ 5) 1 1
      (by decide) (by decide) (by decide) (by decide) (by decide)
  suffices beatable (lv [($2 ~~ 4 ~~ 5), ($0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω), ($0 ~~ 1 ~~ 2 ~~ 3), ($0 ~~ 1 ~~ 2)]
      <| im [(3, [K(1)]), (5, [K(0)])]) by
    convert Rule1_2 _ this ($0 ~~ 1 ~~ 2) ($0 ~~ 1 ~~ 2 ~~ 3) (by decide) (by decide)
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω), ($0 ~~ 1 ~~ 2 ~~ 3), ($0 ~~ 1 ~~ 2 ~~ 4 ~~ 5)]
      <| im [(3, [K(1)]), (5, [K(0)])]) by
    convert Rule1_3 _ this ($0 ~~ 1 ~~ 2) ($2 ~~ 4 ~~ 5) (by decide) (by decide)
    decide
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~~ 3 ~~ ω), ($0 ~~ 1 ~~ 2 ~~ 3), ($0 ~~ 1 ~~ 2 ~~ 4 ~~ 5)]
      <| im [(3, [K(1)]), (5, [K(0)])]) by
    convert Rule2_1 _ this ($0 ~~ 1 ~~ 2 ~~ 4 ~~ 5) ($0 ~~ 1 ~~ 2 ~~ 3 ~~ ω) 0 3
      (by decide) (by decide) (by decide) (by decide) (by decide)
  apply Lemma1 _ ($0 ~~ 1 ~~ 2 ~~ 3 ~~ ω)
  all_goals decide

theorem Prop2_5 :
    beatable (lv [($0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω)] <| im [(2, [K*(0), K*(0)])]) := by

  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω), ($0 ~~ 1 ~~ 2)]
      <| im [(2, [K*(0), K*(0)])]) by
    convert Rule1_2 _ this ($0 ~~ 1 ~~ 2) ($0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω) (by decide) (by decide)
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω), ($0 ~~ 1 ~~ 2), ($2 ~L(0)~ 3)]
      <| im [(2, [K*(0), K*(0)])]) by
    convert Rule1_2 _ this ($2 ~L(0)~ 3) ($0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω) (by decide) (by decide)
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω), ($0 ~~ 1 ~~ 2), ($2 ~L(0)~ 3), ($3 ~L(0)~ ω)]
      <| im [(2, [K*(0), K*(0)])]) by
    convert Rule1_2 _ this ($3 ~L(0)~ ω) ($0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω) (by decide) (by decide)
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω), ($0 ~~ 1 ~~ 2), ($2 ~~ 3), ($3 ~L(0)~ ω)]
      <| im [(2, [K*(0)])]) by
    convert Rule2_3 _ this ($0 ~~ 1 ~~ 2) ($2 ~~ 3) 0 (by decide) (by decide) (by decide) (by decide)
    decide
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω), ($0 ~~ 1 ~~ 2), ($2 ~~ 3), ($3 ~L(0)~ ω)]
      <| im [(3, [K*(0)])]) by
    convert Rule2_2 _ this ($3 ~~ 2) 0 (by decide) (by decide) (by decide)
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω), ($0 ~~ 1 ~~ 2 ~~ 3), ($3 ~L(0)~ ω)]
      <| im [(3, [K*(0)])]) by
    convert Rule1_3 _ this ($0 ~~ 1 ~~ 2) ($2 ~~ 3) (by decide) (by decide)
    decide
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω), ($0 ~~ 1 ~~ 2 ~~ 3), ($3 ~~ ω)] ∅) by
    convert Rule2_3 _ this ($0 ~~ 1 ~~ 2 ~~ 3) ($3 ~~ ω) 0 (by decide) (by decide) (by decide) (by decide)
    decide
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω), ($0 ~~ 1 ~~ 2 ~~ 3 ~~ ω)] ∅) by
    convert Rule1_3 _ this ($0 ~~ 1 ~~ 2 ~~ 3) ($3 ~~ ω) (by decide) (by decide)
    decide
  apply Lemma1 _ ($0 ~~ 1 ~~ 2 ~~ 3 ~~ ω)
  all_goals decide

theorem Prop2_6 :
    beatable (lv [($2 ~~ 4), ($0 ~~ 1 ~~ 2 ~L(0)~ ω)] <| im [(4, [K*(0)])]) := by
  suffices beatable (lv [($2 ~~ 4), ($0 ~~ 1 ~~ 2 ~L(0)~ ω), ($0 ~~ 1 ~~ 2)] <| im [(4, [K*(0)])]) by
    convert Rule1_2 _ this ($0 ~~ 1 ~~ 2) ($0 ~~ 1 ~~ 2 ~L(0)~ ω) (by decide) (by decide)
  suffices beatable (lv [($2 ~~ 4), ($0 ~~ 1 ~~ 2 ~L(0)~ ω), ($0 ~~ 1 ~~ 2), ($2 ~L(0)~ ω)] <| im [(4, [K*(0)])]) by
    convert Rule1_2 _ this ($2 ~L(0)~ ω) ($0 ~~ 1 ~~ 2 ~L(0)~ ω) (by decide) (by decide)
  suffices beatable (lv [($2 ~~ 4), ($0 ~~ 1 ~~ 2 ~L(0)~ ω), ($0 ~~ 1 ~~ 2), ($2 ~L(0)~ ω), ($0 ~~ 1 ~~ 2)]
      <| im [(4, [K*(0)])]) by
    convert Rule1_2 _ this ($0 ~~ 1 ~~ 2) ($0 ~~ 1 ~~ 2) (by decide) (by decide)
    decide
  suffices beatable (lv [($2 ~~ 4), ($0 ~~ 1 ~~ 2 ~L(0)~ ω), ($0 ~~ 1 ~~ 2), ($2 ~L(0)~ ω), ($0 ~~ 1 ~~ 2)]
      <| im [(2, [K*(0)])]) by
    convert Rule2_2 _ this ($2 ~~ 4) 0 (by decide) (by decide) (by decide)
  suffices beatable (lv [($2 ~~ 4), ($0 ~~ 1 ~~ 2 ~L(0)~ ω), ($0 ~~ 1 ~~ 2), ($2 ~~ ω), ($0 ~~ 1 ~~ 2)] ∅) by
    convert Rule2_3 _ this ($0 ~~ 1 ~~ 2) ($2 ~~ ω) 0 (by decide) (by decide) (by decide) (by decide)
    decide
  suffices beatable (lv [($2 ~~ 4), ($0 ~~ 1 ~~ 2 ~L(0)~ ω), ($0 ~~ 1 ~~ 2 ~~ ω), ($0 ~~ 1 ~~ 2)] ∅) by
    convert Rule1_3 _ this ($0 ~~ 1 ~~ 2) ($2 ~~ ω) (by decide) (by decide)
    decide
  apply Lemma1 _ ($0 ~~ 1 ~~ 2 ~~ ω)
  all_goals decide

theorem Prop2_7 :
    beatable (lv [($2 ~L(1)~ 4), ($0 ~~ 1 ~~ 2 ~L(0)~ ω)] <| im [(1, [K*(1)]), (4, [K*(0)])]) := by
  suffices beatable (lv [($2 ~L(1)~ 4), ($0 ~~ 1 ~~ 2 ~L(0)~ ω), ($1 ~~ 2)]
      <| im [(1, [K*(1)]), (4, [K*(0)])]) by
    convert Rule1_2 _ this ($1 ~~ 2) ($0 ~~ 1 ~~ 2 ~L(0)~ ω) (by decide) (by decide)
  suffices beatable (lv [($2 ~L(1)~ 4), ($0 ~~ 1 ~~ 2 ~L(0)~ ω), ($1 ~~ 2)]
      <| im [(2, [K*(1)]), (4, [K*(0)])]) by
    convert Rule2_2 _ this ($2 ~~ 1) 1 (by decide) (by decide) (by decide)
    decide
  suffices beatable (lv [($2 ~L(1)~ 4), ($0 ~~ 1 ~~ 2 ~L(0)~ ω), ($1 ~~ 2), ($0 ~~ 1 ~~ 2)]
      <| im [(2, [K*(1)]), (4, [K*(0)])]) by
    convert Rule1_2 _ this ($0 ~~ 1 ~~ 2) ($0 ~~ 1 ~~ 2 ~L(0)~ ω) (by decide) (by decide)
  suffices beatable (lv [($2 ~~ 4), ($0 ~~ 1 ~~ 2 ~L(0)~ ω), ($1 ~~ 2), ($0 ~~ 1 ~~ 2)]
      <| im [(4, [K*(0)])]) by
    convert Rule2_3 _ this ($0 ~~ 1 ~~ 2) ($2 ~~ 4) 1 (by decide) (by decide) (by decide) (by decide)
    decide
  suffices beatable (lv [($2 ~~ 4), ($0 ~~ 1 ~~ 2 ~L(0)~ ω), ($1 ~~ 2)]
      <| im [(4, [K*(0)])]) by
    convert Rule1_1 _ this ($0 ~~ 1 ~~ 2)
    decide
  suffices beatable (lv [($2 ~~ 4), ($0 ~~ 1 ~~ 2 ~L(0)~ ω)]
      <| im [(4, [K*(0)])]) by
    convert Rule1_1 _ this ($1 ~~ 2)
    decide
  exact Prop2_6

theorem Prop2_8 :  -- second prop
    beatable (lv [($1 ~L(0)~ 4), ($0 ~~ 1 ~L(0)~ 2 ~L(0)~ ω)] <| im [(1, [K*(0)]), (4, [K(0)])]) := by
  suffices beatable (lv [($1 ~L(0)~ 4), ($0 ~~ 1 ~L(0)~ 2 ~L(0)~ ω), ($0 ~~ 1)] <| im [(1, [K*(0)]), (4, [K(0)])]) by
    convert Rule1_2 _ this ($0 ~~ 1) ($0 ~~ 1 ~L(0)~ 2 ~L(0)~ ω) (by decide) (by decide)
  suffices beatable (lv [($1 ~~ 4), ($0 ~~ 1 ~L(0)~ 2 ~L(0)~ ω), ($0 ~~ 1)] <| im [(4, [K(0)])]) by
    convert Rule2_3 _ this ($0 ~~ 1) ($1 ~~ 4) 0 (by decide) (by decide) (by decide) (by decide)
    decide
  suffices beatable (lv [($0 ~~ 1 ~L(0)~ 2 ~L(0)~ ω), ($0 ~~ 1 ~~ 4)] <| im [(4, [K(0)])]) by
    convert Rule1_3 _ this ($0 ~~ 1) ($1 ~~ 4) (by decide) (by decide)
    decide
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~L(0)~ ω), ($0 ~~ 1 ~~ 4)] <| im [(4, [K(0)])]) by
    convert Rule2_1 _ this ($0 ~~ 1 ~~ 4) ($0 ~~ 1 ~~ 2 ~L(0)~ ω) 0 1
      (by decide) (by decide) (by decide) (by decide) (by decide)
  suffices beatable (lv [($0 ~~ 1 ~~ 2 ~~ ω), ($0 ~~ 1 ~~ 4)] <| im [(4, [K(0)])]) by
    convert Rule2_1 _ this ($0 ~~ 1 ~~ 4) ($0 ~~ 1 ~~ 2 ~~ ω) 0 2
      (by decide) (by decide) (by decide) (by decide) (by decide)
  apply Lemma1 _ ($0 ~~ 1 ~~ 2 ~~ ω)
  all_goals decide

axiom Axiom2 (a b : PreChain) (itemMap : ItemMap) (hab : a.nodes.inter b.nodes = [])
  (ha : 0 ∉ a.nodes ∨ ω ∉ a.nodes) (ha : 0 ∉ b.nodes ∨ ω ∉ b.nodes) :
  ¬ beatable (lv [a, b] itemMap)

theorem Prop3_1 : ¬ beatable (lv [($1 ~~ 2), ($3 ~~ 4)] ∅) := by
  apply Axiom2 ($1 ~~ 2) ($3 ~~ 4) _
  all_goals decide

theorem Prop3_2 : ¬ beatable (lv [($0 ~~ 1 ~~ 2), ($3 ~~ 4 ~L(0)~ ω)] <| im [(2, [K(0)])]) := by
  apply Axiom2 ($0 ~~ 1 ~~ 2) ($3 ~~ 4 ~L(0)~ ω) _
  all_goals decide

theorem Prop3_3 : ¬ beatable (lv [] ∅) := by
  obtain h := Axiom2 ($100) ($12345) ∅ (by decide) (by decide) (by decide)
  contrapose! h with h1
  obtain h2 := Rule1_1 _ h1 ($100)
  convert Rule1_1 _ h2 ($12345)
  decide

theorem Prop3_4 : ¬ beatable (lv [($4 ~~ ω), ($6 ~~ 5 ~~ 7), ($0 ~~ 1 ~~ 2 ~~ 3)] ∅) := by
  by_contra! h1
  have h2 : beatable (lv [($4 ~~ ω), ($6 ~~ 5 ~~ 7), ($0 ~~ 1 ~~ 2 ~~ 3), ($0 ~~ 1 ~~ 2 ~~ 3 ~~ 6 ~~ 5 ~~ 7)] ∅) := by
    convert Rule1_1 _ h1 ($0 ~~ 1 ~~ 2 ~~ 3 ~~ 6 ~~ 5 ~~ 7)
    decide
  have h3 : beatable (lv [($4 ~~ ω), ($0 ~~ 1 ~~ 2 ~~ 3), ($0 ~~ 1 ~~ 2 ~~ 3 ~~ 6 ~~ 5 ~~ 7)] ∅) := by
    convert Rule1_2 _ h2 ($6 ~~ 5 ~~ 7) ($0 ~~ 1 ~~ 2 ~~ 3 ~~ 6 ~~ 5 ~~ 7) (by decide) (by decide)
  have h4 : beatable (lv [($4 ~~ ω), ($0 ~~ 1 ~~ 2 ~~ 3 ~~ 6 ~~ 5 ~~ 7)] ∅) := by
    convert Rule1_2 _ h3 ($0 ~~ 1 ~~ 2 ~~ 3) ($0 ~~ 1 ~~ 2 ~~ 3 ~~ 6 ~~ 5 ~~ 7) (by decide) (by decide)
  have h : ¬ beatable (lv [($4 ~~ ω), ($0 ~~ 1 ~~ 2 ~~ 3 ~~ 6 ~~ 5 ~~ 7)] ∅) :=
    Axiom2 _ _ _ (by decide) (by decide) (by decide)
  contradiction

theorem Prop3_5 : ¬ beatable (lv [($5 ~~ 6), ($7 ~~ ω), ($0 ~~ 2 ~~ 3), ($1 ~~ 2 ~~ 4)] ∅) := by
  obtain h := Axiom2 ($5 ~~ 6 ~~ 7 ~~ ω) ($0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4) ∅ (by decide) (by decide) (by decide)
  contrapose! h with h1
  suffices beatable (lv [($5 ~~ 6 ~~ 7 ~~ ω), ($0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4), ($5 ~~ 6)] ∅) by
    convert Rule1_2 _ this ($5 ~~ 6) ($5 ~~ 6 ~~ 7 ~~ ω) (by decide) (by decide)
  suffices beatable (lv [($5 ~~ 6 ~~ 7 ~~ ω), ($0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4), ($5 ~~ 6), ($7 ~~ ω)] ∅) by
    convert Rule1_2 _ this ($7 ~~ ω) ($5 ~~ 6 ~~ 7 ~~ ω) (by decide) (by decide)
  suffices beatable (lv [($0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4), ($5 ~~ 6), ($7 ~~ ω)] ∅) by
    convert Rule1_1 _ this ($5 ~~ 6 ~~ 7 ~~ ω)
  suffices beatable (lv [($0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4), ($5 ~~ 6), ($7 ~~ ω), ($0 ~~ 2 ~~ 3)] ∅) by
    convert Rule1_2 _ this ($0 ~~ 2 ~~ 3) ($0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4) (by decide) (by decide)
  suffices beatable (lv [($0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4), ($5 ~~ 6), ($7 ~~ ω), ($0 ~~ 2 ~~ 3), ($1 ~~ 2 ~~ 4)] ∅) by
    convert Rule1_2 _ this ($1 ~~ 2 ~~ 4) ($0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4) (by decide) (by decide)
  suffices beatable (lv [($5 ~~ 6), ($7 ~~ ω), ($0 ~~ 2 ~~ 3), ($1 ~~ 2 ~~ 4)] ∅) by
    convert Rule1_1 _ this ($0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4)
  exact h1
