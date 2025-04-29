import Pycw.Basic

/-!
Base axioms for beatable and unbeatable levels.
-/
/-- A level with a single lockless chain from 0 to ω is beatable. -/
axiom Axiom1 (chain : PreChain) (itemMap : ItemMap)
  (h0 : chain.first = 0) (hω : chain.last = ω) (hlock : chain.lockless) :
  beatable (lv [chain] itemMap)

/-- A level with two disjoint chains with 0 and ω not in the same chain is unbeatable. -/
axiom Axiom2 (a b : PreChain) (itemMap : ItemMap) (hab : a.vertices.inter b.vertices = [])
  (ha : 0 ∉ a.vertices ∨ ω ∉ a.vertices) (ha : 0 ∉ b.vertices ∨ ω ∉ b.vertices) :
  ¬ beatable (lv [a, b] itemMap)

/-!
Rules introduced in chapter one
-/
/-- If a level is beatable, one can add an arbitrary chain and it is still beatable. -/
axiom Rule1_1 (level : Level) (h : beatable level) (chain : PreChain) :
  beatable {
    chains := chain ::ₘ level.chains,
    itemMap := level.itemMap
  }

/-- If a level is beatable, one can remove a subchain and it is still beatable. -/
axiom Rule1_2 (level : Level) (h : beatable level) (a b : PreChain)
  (hab : a.isSubChain b) (hmem : ([(a : Chain), (b : Chain)] : Multiset Chain) ≤ level.chains) :
  beatable {
    chains := level.chains.erase a,
    itemMap := level.itemMap
  }

/-- If a level is beatable, one can split a chain and it is still beatable. -/
axiom Rule1_3 (level : Level) (h : beatable level) (a b : PreChain) (hab : a.last = b.first)
  (hmem : ⟦a.concat b hab⟧ ∈ level.chains) :
  beatable {
    chains := a ::ₘ b ::ₘ (level.chains.erase ⟦(a.concat b hab)⟧),
    itemMap := level.itemMap
  }

/-!
Rules introduced in chapter two
-/
/--
If a level is beatable, one can add lock to an edge
so long there is a corresponding multi-use key reachable from 0 via another chain,
and the level is still beatable.
-/
axiom Rule2_1 (level : Level) (h : beatable level) (a b : PreChain) (lock : ℕ) (bEdgeIndex : ℕ)
  (ha : a.first = 0) (hkey : Item.Key lock ∈ level.itemMap[a.last])
  (hmem : ([(a : Chain), (b : Chain)] : Multiset Chain) ≤ level.chains)
  (hindex : bEdgeIndex < b.edges.length)
  (hlock : b.edges[bEdgeIndex] = none) :
  beatable {
    chains := (b.setEdge bEdgeIndex (some lock)) ::ₘ (level.chains.erase ⟦b⟧),
    itemMap := level.itemMap
  }

/--
If a level is beatable, one can move a single-use key along a lockless chain,
and the level is still beatable.
-/
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

/--
If a level is beatable, one can lock a chain and place a reachable single-use key,
and the level is still beatable.
-/
axiom Rule2_3 (level : Level) (h : beatable level) (a b : PreChain) (lock : ℕ)
  (ha : a.first = 0) (hab : a.last = b.first) (hb : b.edges.length = 1)
  (hmem : ([(a : Chain), (b : Chain)] : Multiset Chain) ≤ level.chains) :
  beatable {
    chains := (b.setEdge 0 (some lock)) ::ₘ (level.chains.erase b),
    itemMap := level.itemMap.update a.last ((Item.KeyOnce lock) ::ₘ ·)
  }

/-!
Rules introduced in chapter three.
There is no Rule3_1 here because we use Lean's built-in logic for proof by contradiction
-/
/--
If a level is unbeatable, one can lock an edge without a key and it is still unbeatable.
-/
axiom Rule3_2 (level : Level) (h : ¬ beatable level) (lock : ℕ) (a b : Vertex)
  (hlock : level.itemMap.all (fun _ items ↦ (Item.Key lock) ∉ items.val ∧ (Item.KeyOnce lock) ∉ items.val)) :
  ¬ beatable {
    chains := ($ a ~L(lock)~ b) ::ₘ level.chains
    itemMap := level.itemMap
  }

/--
If a level is unbeatable, one can add a useless key reachable from ω, and it is still unbeatable.
-/
axiom Rule3_3 (level : Level) (h : ¬ beatable level) (chain : PreChain) (item : Item)
  (hω : chain.last = ω) :
  ¬ beatable {
    chains := level.chains
    itemMap := level.itemMap.update chain.first (item ::ₘ ·)
  }
