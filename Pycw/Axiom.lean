import Pycw.Basic

axiom Axiom1 (chain : PreChain) (itemMap : ItemMap)
  (h0 : chain.first = 0) (hω : chain.last = ω) (hlock : chain.lockless) :
  beatable (lv [chain] itemMap)

axiom Axiom2 (a b : PreChain) (itemMap : ItemMap) (hab : a.nodes.inter b.nodes = [])
  (ha : 0 ∉ a.nodes ∨ ω ∉ a.nodes) (ha : 0 ∉ b.nodes ∨ ω ∉ b.nodes) :
  ¬ beatable (lv [a, b] itemMap)

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
axiom Rule3_2 (level : Level) (h : ¬ beatable level) (lock : ℕ) (a b : Node)
  (hlock : level.itemMap.all (fun _ items ↦ (Item.Key lock) ∉ items.val ∧ (Item.KeyOnce lock) ∉ items.val)) :
  ¬ beatable {
    chains := ($ a ~L(lock)~ b) ::ₘ level.chains
    itemMap := level.itemMap
  }

axiom Rule3_3 (level : Level) (h : ¬ beatable level) (chain : PreChain) (item : Item)
  (hω : chain.last = ω) :
  ¬ beatable {
    chains := level.chains
    itemMap := level.itemMap.update chain.first (item ::ₘ ·)
  }
