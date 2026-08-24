import Nullivance.QuantifiedEqualityHashMemo

/-!
# Verified source-level hash-operation cost model

This module instruments the pinned Lean 4.32.1 `Std.HashMap` execution used by
the quantified-equality orbit engine.  The model follows the separate-chaining
source implementation: one primary hash and one bucket access per `get?` or
`insert`, sequential key comparisons inside the selected bucket, and one
additional hash per stored entry when an insertion triggers table expansion.

The counts are source-level operation counts, not wall-clock time and not an
average-case `O(1)` assumption.  Hash-function internals, allocation, array
indexing, cache behavior, and compiler/runtime constants remain outside scope.
-/

namespace Nullivance.InfiniteFO

open Nullivance.FiniteFO (Var QFormula)
open Nullivance.Semantics

noncomputable section

namespace HashCost

open Std.DHashMap.Internal

structure AssocProbeResult (β : Type) where
  value : Option β
  comparisons : Nat

/-- Instrumented mirror of `AssocList.get?`: one comparison per visited
bucket entry, stopping at the first matching key. -/
def probeAssocList {α β : Type} [BEq α] (query : α) :
    AssocList α (fun _ => β) → AssocProbeResult β
  | .nil => ⟨none, 0⟩
  | .cons key value rest =>
      if key == query then ⟨some value, 1⟩
      else
        let tail := probeAssocList query rest
        ⟨tail.value, tail.comparisons + 1⟩

/-- Structural bucket length, kept local so the comparison proof does not
depend on opaque array-fold implementation details. -/
def assocEntryCount {α : Type} {β : α → Type} : AssocList α β → Nat
  | .nil => 0
  | .cons _ _ rest => assocEntryCount rest + 1

theorem assocEntryCount_eq_toList_length
    {α : Type} {β : α → Type} (bucket : AssocList α β) :
    assocEntryCount bucket = bucket.toList.length := by
  induction bucket with
  | nil => rfl
  | cons key value rest ih => simp [assocEntryCount, AssocList.toList, ih]

theorem probeAssocList_value_eq_get?
    {α β : Type} [BEq α] (query : α)
    (bucket : AssocList α (fun _ => β)) :
    (probeAssocList query bucket).value = bucket.get? query := by
  induction bucket with
  | nil => rfl
  | cons key value rest ih =>
      simp only [probeAssocList, AssocList.get?]
      by_cases h : key == query
      · simp [h]
      · simp [h, ih]

theorem probeAssocList_comparisons_le_entries
    {α β : Type} [BEq α] (query : α)
    (bucket : AssocList α (fun _ => β)) :
    (probeAssocList query bucket).comparisons ≤ assocEntryCount bucket := by
  induction bucket with
  | nil => simp [probeAssocList, assocEntryCount]
  | cons key value rest ih =>
      simp only [probeAssocList, assocEntryCount]
      split
      · dsimp only
        omega
      · dsimp only
        omega

/-- The physical bucket selected by the pinned `Std.HashMap` implementation. -/
def hashedMemoBucket (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) :
    AssocList RecursiveEqualityOrbitMemoKey (fun _ => EqBoolFormula) :=
  let buckets := table.inner.inner.buckets
  let index := mkIdx buckets.size table.inner.wf.size_buckets_pos (hash key)
  buckets[index.1]

def hashedMemoBucketCount (table : HashedEqualityOrbitMemoTable) : Nat :=
  table.inner.inner.buckets.size

/-- A selected chain is a sublist of the table model, so even a maximally bad
collision cannot make a bucket longer than the number of stored keys. -/
theorem hashedMemoBucket_entryCount_le_size
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) :
    assocEntryCount (hashedMemoBucket table key) ≤ table.size := by
  let buckets := table.inner.inner.buckets
  let hpos := table.inner.wf.size_buckets_pos
  obtain ⟨rest, hperm, hkeys⟩ := exists_bucket buckets hpos key
  have hlength := hperm.length_eq
  have hwf := (Raw.WF.out table.inner.wf).size_eq
  rw [assocEntryCount_eq_toList_length]
  change (bucket buckets hpos key).toList.length ≤ table.inner.inner.size
  change table.inner.inner.size = (toListModel buckets).length at hwf
  rw [hwf, hlength]
  simp

def probeHashedMemo (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) : AssocProbeResult EqBoolFormula :=
  probeAssocList key (hashedMemoBucket table key)

/-- The instrumented lookup returns exactly the production `HashMap.get?`
value; only the comparison counter is additional. -/
theorem probeHashedMemo_value_eq_get?
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) :
    (probeHashedMemo table key).value = table.get? key := by
  rw [probeHashedMemo, probeAssocList_value_eq_get?]
  rfl

structure OperationCost where
  lookups : Nat := 0
  inserts : Nat := 0
  primaryHashes : Nat := 0
  rehashHashes : Nat := 0
  /-- Sum of the post-insertion table sizes.  Every resize hashes at most this
  many entries, so this is a deterministic, collision-independent envelope. -/
  rehashEnvelope : Nat := 0
  bucketAccesses : Nat := 0
  keyComparisons : Nat := 0
  comparisonEnvelope : Nat := 0
deriving DecidableEq, Repr

def OperationCost.add (left right : OperationCost) : OperationCost where
  lookups := left.lookups + right.lookups
  inserts := left.inserts + right.inserts
  primaryHashes := left.primaryHashes + right.primaryHashes
  rehashHashes := left.rehashHashes + right.rehashHashes
  rehashEnvelope := left.rehashEnvelope + right.rehashEnvelope
  bucketAccesses := left.bucketAccesses + right.bucketAccesses
  keyComparisons := left.keyComparisons + right.keyComparisons
  comparisonEnvelope := left.comparisonEnvelope + right.comparisonEnvelope

def OperationCost.totalHashes (cost : OperationCost) : Nat :=
  cost.primaryHashes + cost.rehashHashes

def OperationCost.Valid (cost : OperationCost) : Prop :=
  cost.keyComparisons ≤ cost.comparisonEnvelope ∧
    cost.rehashHashes ≤ cost.rehashEnvelope ∧
      cost.primaryHashes = cost.lookups + cost.inserts ∧
      cost.bucketAccesses = cost.lookups + cost.inserts

def OperationCost.withStats (cost : OperationCost)
    (stats : EqualityOrbitMemoStats) : OperationCost :=
  { cost with
    lookups := stats.requests
    inserts := stats.misses
    primaryHashes := stats.requests + stats.misses
    bucketAccesses := stats.requests + stats.misses }

theorem OperationCost.Valid.zero : ({} : OperationCost).Valid := by
  simp [OperationCost.Valid]

theorem OperationCost.Valid.add {left right : OperationCost}
    (hleft : left.Valid) (hright : right.Valid) : (left.add right).Valid := by
  rcases hleft with ⟨hleftCmp, hleftRehash, hleftHash, hleftBucket⟩
  rcases hright with ⟨hrightCmp, hrightRehash, hrightHash, hrightBucket⟩
  constructor
  · simp [OperationCost.add]
    omega
  constructor
  · simp [OperationCost.add]
    omega
  constructor <;> simp [OperationCost.add, *] <;> omega

theorem OperationCost.Valid.withStats {cost : OperationCost}
    (hcost : cost.Valid) (stats : EqualityOrbitMemoStats) :
    (cost.withStats stats).Valid := by
  rcases hcost with ⟨hcmp, hrehash, hhash, hbucket⟩
  exact ⟨hcmp, hrehash, rfl, rfl⟩

theorem OperationCost.Valid.totalHashes_le {cost : OperationCost}
    (hcost : cost.Valid) :
    cost.totalHashes ≤ cost.lookups + cost.inserts + cost.rehashEnvelope := by
  rcases hcost with ⟨hcmp, hrehash, hprimary, hbucket⟩
  simp only [OperationCost.totalHashes, hprimary]
  omega

/-- Collision-independent budget indexed by logical requests, insertions, and
the largest table size visible to the operation sequence. -/
def OperationCost.BudgetBound (cost : OperationCost)
    (requests misses finalSize : Nat) : Prop :=
  cost.rehashEnvelope ≤ misses * finalSize ∧
    cost.comparisonEnvelope ≤ (requests + misses) * finalSize

theorem OperationCost.BudgetBound.zero (finalSize : Nat) :
    ({} : OperationCost).BudgetBound 0 0 finalSize := by
  simp [OperationCost.BudgetBound]

theorem OperationCost.BudgetBound.mono_final
    {cost : OperationCost} {requests misses smaller larger : Nat}
    (hbound : cost.BudgetBound requests misses smaller)
    (hsize : smaller ≤ larger) :
    cost.BudgetBound requests misses larger := by
  rcases hbound with ⟨hrehash, hcompare⟩
  exact ⟨hrehash.trans (Nat.mul_le_mul_left misses hsize),
    hcompare.trans (Nat.mul_le_mul_left (requests + misses) hsize)⟩

theorem OperationCost.BudgetBound.add
    {left right : OperationCost}
    {leftRequests leftMisses rightRequests rightMisses finalSize : Nat}
    (hleft : left.BudgetBound leftRequests leftMisses finalSize)
    (hright : right.BudgetBound rightRequests rightMisses finalSize) :
    (left.add right).BudgetBound
      (leftRequests + rightRequests) (leftMisses + rightMisses) finalSize := by
  rcases hleft with ⟨hleftRehash, hleftCompare⟩
  rcases hright with ⟨hrightRehash, hrightCompare⟩
  constructor
  · simp only [OperationCost.add, Nat.add_mul]
    omega
  · simp only [OperationCost.add]
    rw [show (leftRequests + rightRequests + (leftMisses + rightMisses)) * finalSize =
      (leftRequests + leftMisses) * finalSize +
        (rightRequests + rightMisses) * finalSize by ring]
    omega

theorem OperationCost.BudgetBound.withStats
    {cost : OperationCost} {requests misses finalSize : Nat}
    (hbound : cost.BudgetBound requests misses finalSize)
    (stats : EqualityOrbitMemoStats) :
    (cost.withStats stats).BudgetBound requests misses finalSize := by
  exact hbound

def lookupCost (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) : OperationCost :=
  let probe := probeHashedMemo table key
  { lookups := 1
    primaryHashes := 1
    bucketAccesses := 1
    keyComparisons := probe.comparisons
    comparisonEnvelope := assocEntryCount (hashedMemoBucket table key) }

/-- Cost of an insertion known to be for a missing key.  The orbit engine's
parent-key freshness theorem supplies that precondition at every insertion.
If the physical bucket array grows, the pinned implementation hashes every
entry of the resulting table once during rehashing. -/
def insertMissCost (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) (value : EqBoolFormula) : OperationCost :=
  let probe := probeHashedMemo table key
  let inserted := table.insert key value
  let rehashed := if hashedMemoBucketCount table < hashedMemoBucketCount inserted
    then inserted.size else 0
  { inserts := 1
    primaryHashes := 1
    rehashHashes := rehashed
    rehashEnvelope := inserted.size
    bucketAccesses := 1
    keyComparisons := probe.comparisons
    comparisonEnvelope := assocEntryCount (hashedMemoBucket table key) }

theorem lookupCost_valid (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) : (lookupCost table key).Valid := by
  constructor
  · exact probeAssocList_comparisons_le_entries key (hashedMemoBucket table key)
  constructor
  · rfl
  constructor <;> rfl

theorem lookupCost_budget (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) {finalSize : Nat}
    (hsize : table.size ≤ finalSize) :
    (lookupCost table key).BudgetBound 1 0 finalSize := by
  constructor
  · simp [lookupCost]
  · simpa [OperationCost.BudgetBound, lookupCost] using
      (hashedMemoBucket_entryCount_le_size table key).trans hsize

theorem insertMissCost_valid (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) (value : EqBoolFormula) :
    (insertMissCost table key value).Valid := by
  constructor
  · exact probeAssocList_comparisons_le_entries key (hashedMemoBucket table key)
  constructor
  · simp [insertMissCost]
    split <;> simp_all
  constructor <;> rfl

theorem insertMissCost_rehashHashes_le_inserted_size
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) (value : EqBoolFormula) :
    (insertMissCost table key value).rehashHashes ≤
      (table.insert key value).size := by
  simp [insertMissCost]
  split <;> simp_all

theorem insertMissCost_budget (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) (value : EqBoolFormula)
    {finalSize : Nat} (hsize : (table.insert key value).size ≤ finalSize) :
    (insertMissCost table key value).BudgetBound 0 1 finalSize := by
  constructor
  · simpa [OperationCost.BudgetBound, insertMissCost] using hsize
  · have htable : table.size ≤ finalSize :=
      (Std.HashMap.size_le_size_insert (m := table)).trans hsize
    simpa [OperationCost.BudgetBound, insertMissCost] using
      (hashedMemoBucket_entryCount_le_size table key).trans htable

end HashCost

open HashCost

structure CostedHashedEqualityOrbitMemoResult where
  result : HashedEqualityOrbitMemoResult
  cost : OperationCost

structure CostedHashedEqualityOrbitBranchResult where
  result : HashedEqualityOrbitBranchResult
  cost : OperationCost

mutual
  /-- Cost-instrumented replay of the production hash-memo recursion.  The
  `result` field is definitionally the production result; only `cost` replays
  the control flow and observes the physical buckets at each operation. -/
  def costedExpandQuantifiedEqualityOrbitsHashed
      (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
      (table : HashedEqualityOrbitMemoTable) :
      CostedHashedEqualityOrbitMemoResult :=
    let production := expandQuantifiedEqualityOrbitsHashed
      phi used available env table
    { result := production
      cost :=
        let key := recursiveEqualityOrbitMemoKey phi used available env
        let lookup := lookupCost table key
        let detailed := match table.get? key with
          | some _ => lookup
          | none =>
              let recursive : OperationCost × HashedEqualityOrbitMemoTable :=
                match phi with
                | .pred _ _ | .eq _ _ | .oplus _ _ => ({}, table)
                | .neg body =>
                    let child := costedExpandQuantifiedEqualityOrbitsHashed
                      body used available env table
                    (child.cost, child.result.table)
                | .conj left right | .disj left right =>
                    let leftResult := costedExpandQuantifiedEqualityOrbitsHashed
                      left used available env table
                    let rightResult := costedExpandQuantifiedEqualityOrbitsHashed
                      right used available env leftResult.result.table
                    (leftResult.cost.add rightResult.cost, rightResult.result.table)
                | .all x body | .ex x body =>
                    let oldQueries : List RecursiveEqualityOrbitBranchQuery :=
                      used.map fun representative =>
                        { used := used, available := available,
                          env := env.update x representative }
                    let freshQueries := match available with
                      | [] => []
                      | representative :: rest =>
                          let query : RecursiveEqualityOrbitBranchQuery :=
                            { used := used ++ [representative]
                              available := rest
                              env := env.update x representative }
                          [query]
                    let branches := costedExpandQuantifiedEqualityOrbitBranchesHashed
                      body (oldQueries ++ freshQueries) table
                    (branches.cost, branches.result.table)
              let insertion := insertMissCost recursive.2 key production.formula
              lookup.add (recursive.1.add insertion)
        detailed.withStats production.stats }
  termination_by (sizeOf phi, 0)

  def costedExpandQuantifiedEqualityOrbitBranchesHashed
      (body : QFormula) (queries : List RecursiveEqualityOrbitBranchQuery)
      (table : HashedEqualityOrbitMemoTable) :
      CostedHashedEqualityOrbitBranchResult :=
    let production := expandQuantifiedEqualityOrbitBranchesHashed body queries table
    { result := production
      cost :=
        let detailed : OperationCost := match queries with
          | [] => {}
          | query :: rest =>
              let headResult := costedExpandQuantifiedEqualityOrbitsHashed body
                query.used query.available query.env table
              let tailResult := costedExpandQuantifiedEqualityOrbitBranchesHashed
                body rest headResult.result.table
              headResult.cost.add tailResult.cost
        detailed.withStats production.stats }
  termination_by (sizeOf body, queries.length + 1)
end

@[simp] theorem costedExpandQuantifiedEqualityOrbitsHashed_result
    (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
    (table : HashedEqualityOrbitMemoTable) :
    (costedExpandQuantifiedEqualityOrbitsHashed
      phi used available env table).result =
        expandQuantifiedEqualityOrbitsHashed phi used available env table := by
  rw [costedExpandQuantifiedEqualityOrbitsHashed.eq_def]

@[simp] theorem costedExpandQuantifiedEqualityOrbitBranchesHashed_result
    (body : QFormula) (queries : List RecursiveEqualityOrbitBranchQuery)
    (table : HashedEqualityOrbitMemoTable) :
    (costedExpandQuantifiedEqualityOrbitBranchesHashed
      body queries table).result =
        expandQuantifiedEqualityOrbitBranchesHashed body queries table := by
  rw [costedExpandQuantifiedEqualityOrbitBranchesHashed.eq_def]

def runQuantifiedEqualityOrbitHashedCosted (k : Nat) (phi : QFormula) :
    CostedHashedEqualityOrbitMemoResult :=
  costedExpandQuantifiedEqualityOrbitsHashed phi [] (cutoffRepresentatives k) id
    emptyHashedEqualityOrbitMemoTable

theorem expandQuantifiedEqualityOrbitsHashed_table_size_mono
    (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
    (table : HashedEqualityOrbitMemoTable) :
    table.size ≤
      (expandQuantifiedEqualityOrbitsHashed phi used available env table).table.size := by
  have hexact := expandQuantifiedEqualityOrbitsHashed_size_eq_misses
    phi used available env table
  omega

theorem expandQuantifiedEqualityOrbitBranchesHashed_table_size_mono
    (body : QFormula) (queries : List RecursiveEqualityOrbitBranchQuery)
    (table : HashedEqualityOrbitMemoTable) :
    table.size ≤
      (expandQuantifiedEqualityOrbitBranchesHashed body queries table).table.size := by
  have hexact := expandQuantifiedEqualityOrbitBranchesHashed_size_eq_misses
    body queries table
  omega

mutual
  theorem costedExpandQuantifiedEqualityOrbitsHashed_cost_valid
      (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
      (table : HashedEqualityOrbitMemoTable) :
      (costedExpandQuantifiedEqualityOrbitsHashed
        phi used available env table).cost.Valid := by
    rw [costedExpandQuantifiedEqualityOrbitsHashed.eq_def]
    dsimp only
    apply OperationCost.Valid.withStats
    split
    next cached hlookup =>
      exact lookupCost_valid table
        (recursiveEqualityOrbitMemoKey phi used available env)
    next hlookup =>
      cases phi with
      | pred P xs =>
          exact (lookupCost_valid table _).add
            (OperationCost.Valid.zero.add (insertMissCost_valid table _ _))
      | eq x y =>
          exact (lookupCost_valid table _).add
            (OperationCost.Valid.zero.add (insertMissCost_valid table _ _))
      | neg body =>
          have hchild := costedExpandQuantifiedEqualityOrbitsHashed_cost_valid
            body used available env table
          exact (lookupCost_valid table _).add
            (hchild.add (insertMissCost_valid
              (costedExpandQuantifiedEqualityOrbitsHashed
                body used available env table).result.table _ _))
      | conj left right =>
          have hleft := costedExpandQuantifiedEqualityOrbitsHashed_cost_valid
            left used available env table
          let leftResult := costedExpandQuantifiedEqualityOrbitsHashed
            left used available env table
          have hright := costedExpandQuantifiedEqualityOrbitsHashed_cost_valid
            right used available env leftResult.result.table
          let rightResult := costedExpandQuantifiedEqualityOrbitsHashed
            right used available env leftResult.result.table
          exact (lookupCost_valid table _).add
            ((hleft.add hright).add
              (insertMissCost_valid rightResult.result.table _ _))
      | disj left right =>
          have hleft := costedExpandQuantifiedEqualityOrbitsHashed_cost_valid
            left used available env table
          let leftResult := costedExpandQuantifiedEqualityOrbitsHashed
            left used available env table
          have hright := costedExpandQuantifiedEqualityOrbitsHashed_cost_valid
            right used available env leftResult.result.table
          let rightResult := costedExpandQuantifiedEqualityOrbitsHashed
            right used available env leftResult.result.table
          exact (lookupCost_valid table _).add
            ((hleft.add hright).add
              (insertMissCost_valid rightResult.result.table _ _))
      | oplus left right =>
          exact (lookupCost_valid table _).add
            (OperationCost.Valid.zero.add (insertMissCost_valid table _ _))
      | all x body =>
          let oldQueries : List RecursiveEqualityOrbitBranchQuery :=
            used.map fun representative =>
            { used := used, available := available,
              env := env.update x representative }
          let freshQueries := match available with
            | [] => []
            | representative :: rest =>
                let query : RecursiveEqualityOrbitBranchQuery :=
                  { used := used ++ [representative]
                    available := rest
                    env := env.update x representative }
                [query]
          have hbranches :=
            costedExpandQuantifiedEqualityOrbitBranchesHashed_cost_valid
              body (oldQueries ++ freshQueries) table
          let branches := costedExpandQuantifiedEqualityOrbitBranchesHashed
            body (oldQueries ++ freshQueries) table
          exact (lookupCost_valid table _).add
            (hbranches.add (insertMissCost_valid branches.result.table _ _))
      | ex x body =>
          let oldQueries : List RecursiveEqualityOrbitBranchQuery :=
            used.map fun representative =>
            { used := used, available := available,
              env := env.update x representative }
          let freshQueries := match available with
            | [] => []
            | representative :: rest =>
                let query : RecursiveEqualityOrbitBranchQuery :=
                  { used := used ++ [representative]
                    available := rest
                    env := env.update x representative }
                [query]
          have hbranches :=
            costedExpandQuantifiedEqualityOrbitBranchesHashed_cost_valid
              body (oldQueries ++ freshQueries) table
          let branches := costedExpandQuantifiedEqualityOrbitBranchesHashed
            body (oldQueries ++ freshQueries) table
          exact (lookupCost_valid table _).add
            (hbranches.add (insertMissCost_valid branches.result.table _ _))
  termination_by (sizeOf phi, 0)

  theorem costedExpandQuantifiedEqualityOrbitBranchesHashed_cost_valid
      (body : QFormula) (queries : List RecursiveEqualityOrbitBranchQuery)
      (table : HashedEqualityOrbitMemoTable) :
      (costedExpandQuantifiedEqualityOrbitBranchesHashed
        body queries table).cost.Valid := by
    cases queries with
    | nil =>
        rw [costedExpandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        exact OperationCost.Valid.zero.withStats _
    | cons query rest =>
        rw [costedExpandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        let headResult := costedExpandQuantifiedEqualityOrbitsHashed body
          query.used query.available query.env table
        have hhead := costedExpandQuantifiedEqualityOrbitsHashed_cost_valid body
          query.used query.available query.env table
        have htail := costedExpandQuantifiedEqualityOrbitBranchesHashed_cost_valid
          body rest headResult.result.table
        exact (hhead.add htail).withStats _
  termination_by (sizeOf body, queries.length + 1)
end

mutual
  theorem costedExpandQuantifiedEqualityOrbitsHashed_cost_budget
      (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
      (table : HashedEqualityOrbitMemoTable) :
      let traced := costedExpandQuantifiedEqualityOrbitsHashed
        phi used available env table
      traced.cost.BudgetBound traced.result.stats.requests
        traced.result.stats.misses traced.result.table.size := by
    rw [costedExpandQuantifiedEqualityOrbitsHashed.eq_def]
    dsimp only
    apply OperationCost.BudgetBound.withStats
    split
    next cached hlookup =>
      have hproduction :
          expandQuantifiedEqualityOrbitsHashed phi used available env table =
            ⟨cached, table, EqualityOrbitMemoStats.hit⟩ := by
        rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
        dsimp only
        rw [hlookup]
      rw [hproduction]
      simpa [EqualityOrbitMemoStats.requests, EqualityOrbitMemoStats.hit] using
        (lookupCost_budget table
          (recursiveEqualityOrbitMemoKey phi used available env) (le_refl _))
    next hlookup =>
      cases phi with
      | pred P xs =>
          have hproduction :
              expandQuantifiedEqualityOrbitsHashed (.pred P xs)
                used available env table =
                ⟨.bot, table.insert
                  (recursiveEqualityOrbitMemoKey (.pred P xs) used available env)
                  .bot, EqualityOrbitMemoStats.miss⟩ := by
            rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
            dsimp only
            rw [hlookup]
            rfl
          rw [hproduction]
          have htable := Std.HashMap.size_le_size_insert (m := table)
            (k := recursiveEqualityOrbitMemoKey (.pred P xs) used available env)
            (v := EqBoolFormula.bot)
          have hlookupCost := lookupCost_budget table
            (recursiveEqualityOrbitMemoKey (.pred P xs) used available env) htable
          have hinsert := insertMissCost_budget table
            (recursiveEqualityOrbitMemoKey (.pred P xs) used available env)
            EqBoolFormula.bot (le_refl _)
          simpa [EqualityOrbitMemoStats.requests, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] using
            hlookupCost.add ((OperationCost.BudgetBound.zero _).add hinsert)
      | eq x y =>
          let value := if env x = env y then EqBoolFormula.top
            else EqBoolFormula.atom (normalizeEqAtom (env x) (env y))
          have hproduction :
              expandQuantifiedEqualityOrbitsHashed (.eq x y)
                used available env table =
                ⟨value, table.insert
                  (recursiveEqualityOrbitMemoKey (.eq x y) used available env)
                  value, EqualityOrbitMemoStats.miss⟩ := by
            rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
            dsimp only
            rw [hlookup]
            rfl
          rw [hproduction]
          have htable := Std.HashMap.size_le_size_insert (m := table)
            (k := recursiveEqualityOrbitMemoKey (.eq x y) used available env)
            (v := value)
          have hlookupCost := lookupCost_budget table
            (recursiveEqualityOrbitMemoKey (.eq x y) used available env) htable
          have hinsert := insertMissCost_budget table
            (recursiveEqualityOrbitMemoKey (.eq x y) used available env)
            value (le_refl _)
          simpa [EqualityOrbitMemoStats.requests, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] using
            hlookupCost.add ((OperationCost.BudgetBound.zero _).add hinsert)
      | neg body =>
          let childProduction := expandQuantifiedEqualityOrbitsHashed
            body used available env table
          let value := EqBoolFormula.neg childProduction.formula
          have hproduction :
              expandQuantifiedEqualityOrbitsHashed (.neg body)
                used available env table =
                ⟨value, childProduction.table.insert
                  (recursiveEqualityOrbitMemoKey (.neg body) used available env)
                  value, childProduction.stats.add EqualityOrbitMemoStats.miss⟩ := by
            rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
            dsimp only
            rw [hlookup]
          rw [hproduction]
          let child := costedExpandQuantifiedEqualityOrbitsHashed
            body used available env table
          have hchild := costedExpandQuantifiedEqualityOrbitsHashed_cost_budget
            body used available env table
          have hchildInsert := Std.HashMap.size_le_size_insert
            (m := child.result.table)
            (k := recursiveEqualityOrbitMemoKey (.neg body) used available env)
            (v := value)
          have hchildLift := hchild.mono_final hchildInsert
          have htableChild := expandQuantifiedEqualityOrbitsHashed_table_size_mono
            body used available env table
          have htableChild' : table.size ≤ child.result.table.size := by
            simpa [child] using htableChild
          have hlookupCost := lookupCost_budget table
            (recursiveEqualityOrbitMemoKey (.neg body) used available env)
            (htableChild'.trans hchildInsert)
          have hinsert := insertMissCost_budget child.result.table
            (recursiveEqualityOrbitMemoKey (.neg body) used available env)
            value (le_refl _)
          simpa [child, childProduction, value, EqualityOrbitMemoStats.requests,
            EqualityOrbitMemoStats.add, EqualityOrbitMemoStats.miss,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            hlookupCost.add (hchildLift.add hinsert)
      | conj left right =>
          let leftProduction := expandQuantifiedEqualityOrbitsHashed
            left used available env table
          let rightProduction := expandQuantifiedEqualityOrbitsHashed
            right used available env leftProduction.table
          let value := EqBoolFormula.conj leftProduction.formula rightProduction.formula
          have hproduction :
              expandQuantifiedEqualityOrbitsHashed (.conj left right)
                used available env table =
                ⟨value, rightProduction.table.insert
                  (recursiveEqualityOrbitMemoKey (.conj left right)
                    used available env) value,
                  (leftProduction.stats.add rightProduction.stats).add
                    EqualityOrbitMemoStats.miss⟩ := by
            rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
            dsimp only
            rw [hlookup]
          rw [hproduction]
          let leftResult := costedExpandQuantifiedEqualityOrbitsHashed
            left used available env table
          let rightResult := costedExpandQuantifiedEqualityOrbitsHashed
            right used available env leftResult.result.table
          have hleft := costedExpandQuantifiedEqualityOrbitsHashed_cost_budget
            left used available env table
          have hright := costedExpandQuantifiedEqualityOrbitsHashed_cost_budget
            right used available env leftResult.result.table
          have hleftRight := expandQuantifiedEqualityOrbitsHashed_table_size_mono
            right used available env leftResult.result.table
          have hleftRight' : leftResult.result.table.size ≤
              rightResult.result.table.size := by
            simpa [rightResult] using hleftRight
          have hrightInsert := Std.HashMap.size_le_size_insert
            (m := rightResult.result.table)
            (k := recursiveEqualityOrbitMemoKey (.conj left right) used available env)
            (v := value)
          have hleftLift := hleft.mono_final (hleftRight'.trans hrightInsert)
          have hrightLift := hright.mono_final hrightInsert
          have htableLeft := expandQuantifiedEqualityOrbitsHashed_table_size_mono
            left used available env table
          have htableLeft' : table.size ≤ leftResult.result.table.size := by
            simpa [leftResult] using htableLeft
          have hlookupCost := lookupCost_budget table
            (recursiveEqualityOrbitMemoKey (.conj left right) used available env)
            (htableLeft'.trans (hleftRight'.trans hrightInsert))
          have hinsert := insertMissCost_budget rightResult.result.table
            (recursiveEqualityOrbitMemoKey (.conj left right) used available env)
            value (le_refl _)
          simpa [leftResult, rightResult, leftProduction, rightProduction, value,
            EqualityOrbitMemoStats.requests,
            EqualityOrbitMemoStats.add, EqualityOrbitMemoStats.miss,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            hlookupCost.add ((hleftLift.add hrightLift).add hinsert)
      | disj left right =>
          let leftProduction := expandQuantifiedEqualityOrbitsHashed
            left used available env table
          let rightProduction := expandQuantifiedEqualityOrbitsHashed
            right used available env leftProduction.table
          let value := EqBoolFormula.disj leftProduction.formula rightProduction.formula
          have hproduction :
              expandQuantifiedEqualityOrbitsHashed (.disj left right)
                used available env table =
                ⟨value, rightProduction.table.insert
                  (recursiveEqualityOrbitMemoKey (.disj left right)
                    used available env) value,
                  (leftProduction.stats.add rightProduction.stats).add
                    EqualityOrbitMemoStats.miss⟩ := by
            rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
            dsimp only
            rw [hlookup]
          rw [hproduction]
          let leftResult := costedExpandQuantifiedEqualityOrbitsHashed
            left used available env table
          let rightResult := costedExpandQuantifiedEqualityOrbitsHashed
            right used available env leftResult.result.table
          have hleft := costedExpandQuantifiedEqualityOrbitsHashed_cost_budget
            left used available env table
          have hright := costedExpandQuantifiedEqualityOrbitsHashed_cost_budget
            right used available env leftResult.result.table
          have hleftRight := expandQuantifiedEqualityOrbitsHashed_table_size_mono
            right used available env leftResult.result.table
          have hleftRight' : leftResult.result.table.size ≤
              rightResult.result.table.size := by
            simpa [rightResult] using hleftRight
          have hrightInsert := Std.HashMap.size_le_size_insert
            (m := rightResult.result.table)
            (k := recursiveEqualityOrbitMemoKey (.disj left right) used available env)
            (v := value)
          have hleftLift := hleft.mono_final (hleftRight'.trans hrightInsert)
          have hrightLift := hright.mono_final hrightInsert
          have htableLeft := expandQuantifiedEqualityOrbitsHashed_table_size_mono
            left used available env table
          have htableLeft' : table.size ≤ leftResult.result.table.size := by
            simpa [leftResult] using htableLeft
          have hlookupCost := lookupCost_budget table
            (recursiveEqualityOrbitMemoKey (.disj left right) used available env)
            (htableLeft'.trans (hleftRight'.trans hrightInsert))
          have hinsert := insertMissCost_budget rightResult.result.table
            (recursiveEqualityOrbitMemoKey (.disj left right) used available env)
            value (le_refl _)
          simpa [leftResult, rightResult, leftProduction, rightProduction, value,
            EqualityOrbitMemoStats.requests,
            EqualityOrbitMemoStats.add, EqualityOrbitMemoStats.miss,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            hlookupCost.add ((hleftLift.add hrightLift).add hinsert)
      | oplus left right =>
          have hproduction :
              expandQuantifiedEqualityOrbitsHashed (.oplus left right)
                used available env table =
                ⟨.bot, table.insert
                  (recursiveEqualityOrbitMemoKey (.oplus left right)
                    used available env) .bot,
                  EqualityOrbitMemoStats.miss⟩ := by
            rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
            dsimp only
            rw [hlookup]
            rfl
          rw [hproduction]
          have htable := Std.HashMap.size_le_size_insert (m := table)
            (k := recursiveEqualityOrbitMemoKey (.oplus left right) used available env)
            (v := EqBoolFormula.bot)
          have hlookupCost := lookupCost_budget table
            (recursiveEqualityOrbitMemoKey (.oplus left right) used available env) htable
          have hinsert := insertMissCost_budget table
            (recursiveEqualityOrbitMemoKey (.oplus left right) used available env)
            EqBoolFormula.bot (le_refl _)
          simpa [EqualityOrbitMemoStats.requests, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] using
            hlookupCost.add ((OperationCost.BudgetBound.zero _).add hinsert)
      | all x body =>
          let oldQueries : List RecursiveEqualityOrbitBranchQuery :=
            used.map fun representative =>
              { used := used, available := available,
                env := env.update x representative }
          let freshQueries := match available with
            | [] => []
            | representative :: rest =>
                let query : RecursiveEqualityOrbitBranchQuery :=
                  { used := used ++ [representative]
                    available := rest
                    env := env.update x representative }
                [query]
          let branchProduction := expandQuantifiedEqualityOrbitBranchesHashed
            body (oldQueries ++ freshQueries) table
          let value := EqBoolFormula.conjList branchProduction.formulas
          have hproduction :
              expandQuantifiedEqualityOrbitsHashed (.all x body)
                used available env table =
                ⟨value, branchProduction.table.insert
                  (recursiveEqualityOrbitMemoKey (.all x body)
                    used available env) value,
                  branchProduction.stats.add EqualityOrbitMemoStats.miss⟩ := by
            rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
            dsimp only
            rw [hlookup]
            rfl
          rw [hproduction]
          let branches := costedExpandQuantifiedEqualityOrbitBranchesHashed
            body (oldQueries ++ freshQueries) table
          have hbranches :=
            costedExpandQuantifiedEqualityOrbitBranchesHashed_cost_budget
              body (oldQueries ++ freshQueries) table
          have hbranchInsert := Std.HashMap.size_le_size_insert
            (m := branches.result.table)
            (k := recursiveEqualityOrbitMemoKey (.all x body) used available env)
            (v := value)
          have hbranchesLift := hbranches.mono_final hbranchInsert
          have htableBranches :=
            expandQuantifiedEqualityOrbitBranchesHashed_table_size_mono
              body (oldQueries ++ freshQueries) table
          have htableBranches' : table.size ≤ branches.result.table.size := by
            simpa [branches] using htableBranches
          have hlookupCost := lookupCost_budget table
            (recursiveEqualityOrbitMemoKey (.all x body) used available env)
            (htableBranches'.trans hbranchInsert)
          have hinsert := insertMissCost_budget branches.result.table
            (recursiveEqualityOrbitMemoKey (.all x body) used available env)
            value (le_refl _)
          simpa [oldQueries, freshQueries, branches, branchProduction, value,
            EqualityOrbitMemoStats.requests, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using hlookupCost.add (hbranchesLift.add hinsert)
      | ex x body =>
          let oldQueries : List RecursiveEqualityOrbitBranchQuery :=
            used.map fun representative =>
              { used := used, available := available,
                env := env.update x representative }
          let freshQueries := match available with
            | [] => []
            | representative :: rest =>
                let query : RecursiveEqualityOrbitBranchQuery :=
                  { used := used ++ [representative]
                    available := rest
                    env := env.update x representative }
                [query]
          let branchProduction := expandQuantifiedEqualityOrbitBranchesHashed
            body (oldQueries ++ freshQueries) table
          let value := EqBoolFormula.disjList branchProduction.formulas
          have hproduction :
              expandQuantifiedEqualityOrbitsHashed (.ex x body)
                used available env table =
                ⟨value, branchProduction.table.insert
                  (recursiveEqualityOrbitMemoKey (.ex x body)
                    used available env) value,
                  branchProduction.stats.add EqualityOrbitMemoStats.miss⟩ := by
            rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
            dsimp only
            rw [hlookup]
            rfl
          rw [hproduction]
          let branches := costedExpandQuantifiedEqualityOrbitBranchesHashed
            body (oldQueries ++ freshQueries) table
          have hbranches :=
            costedExpandQuantifiedEqualityOrbitBranchesHashed_cost_budget
              body (oldQueries ++ freshQueries) table
          have hbranchInsert := Std.HashMap.size_le_size_insert
            (m := branches.result.table)
            (k := recursiveEqualityOrbitMemoKey (.ex x body) used available env)
            (v := value)
          have hbranchesLift := hbranches.mono_final hbranchInsert
          have htableBranches :=
            expandQuantifiedEqualityOrbitBranchesHashed_table_size_mono
              body (oldQueries ++ freshQueries) table
          have htableBranches' : table.size ≤ branches.result.table.size := by
            simpa [branches] using htableBranches
          have hlookupCost := lookupCost_budget table
            (recursiveEqualityOrbitMemoKey (.ex x body) used available env)
            (htableBranches'.trans hbranchInsert)
          have hinsert := insertMissCost_budget branches.result.table
            (recursiveEqualityOrbitMemoKey (.ex x body) used available env)
            value (le_refl _)
          simpa [oldQueries, freshQueries, branches, branchProduction, value,
            EqualityOrbitMemoStats.requests, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using hlookupCost.add (hbranchesLift.add hinsert)
  termination_by (sizeOf phi, 0)

  theorem costedExpandQuantifiedEqualityOrbitBranchesHashed_cost_budget
      (body : QFormula) (queries : List RecursiveEqualityOrbitBranchQuery)
      (table : HashedEqualityOrbitMemoTable) :
      let traced := costedExpandQuantifiedEqualityOrbitBranchesHashed
        body queries table
      traced.cost.BudgetBound traced.result.stats.requests
        traced.result.stats.misses traced.result.table.size := by
    cases queries with
    | nil =>
        rw [costedExpandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        simpa [EqualityOrbitMemoStats.requests] using
          (OperationCost.BudgetBound.zero table.size).withStats
            ({} : EqualityOrbitMemoStats)
    | cons query rest =>
        rw [costedExpandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        let headResult := costedExpandQuantifiedEqualityOrbitsHashed body
          query.used query.available query.env table
        let tailResult := costedExpandQuantifiedEqualityOrbitBranchesHashed
          body rest headResult.result.table
        have hhead := costedExpandQuantifiedEqualityOrbitsHashed_cost_budget body
          query.used query.available query.env table
        have htail := costedExpandQuantifiedEqualityOrbitBranchesHashed_cost_budget
          body rest headResult.result.table
        have hheadTail :=
          expandQuantifiedEqualityOrbitBranchesHashed_table_size_mono
            body rest headResult.result.table
        have hheadTail' : headResult.result.table.size ≤
            tailResult.result.table.size := by
          simpa [tailResult] using hheadTail
        have hheadLift := hhead.mono_final hheadTail'
        have hsum := hheadLift.add htail
        simpa [headResult, tailResult,
          EqualityOrbitMemoStats.requests,
          EqualityOrbitMemoStats.add, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hsum.withStats
            ((expandQuantifiedEqualityOrbitsHashed body
                query.used query.available query.env table).stats.add
              (expandQuantifiedEqualityOrbitBranchesHashed body rest
                (expandQuantifiedEqualityOrbitsHashed body
                  query.used query.available query.env table).table).stats)
  termination_by (sizeOf body, queries.length + 1)
end

@[simp] theorem costedExpandQuantifiedEqualityOrbitsHashed_cost_lookups
    (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
    (table : HashedEqualityOrbitMemoTable) :
    (costedExpandQuantifiedEqualityOrbitsHashed
      phi used available env table).cost.lookups =
        (expandQuantifiedEqualityOrbitsHashed
          phi used available env table).stats.requests := by
  rw [costedExpandQuantifiedEqualityOrbitsHashed.eq_def]
  simp [OperationCost.withStats]

@[simp] theorem costedExpandQuantifiedEqualityOrbitsHashed_cost_inserts
    (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
    (table : HashedEqualityOrbitMemoTable) :
    (costedExpandQuantifiedEqualityOrbitsHashed
      phi used available env table).cost.inserts =
        (expandQuantifiedEqualityOrbitsHashed
          phi used available env table).stats.misses := by
  rw [costedExpandQuantifiedEqualityOrbitsHashed.eq_def]
  simp [OperationCost.withStats]

@[simp] theorem runQuantifiedEqualityOrbitHashedCosted_result
    (k : Nat) (phi : QFormula) :
    (runQuantifiedEqualityOrbitHashedCosted k phi).result =
      runQuantifiedEqualityOrbitHashed k phi := by
  simp [runQuantifiedEqualityOrbitHashedCosted,
    runQuantifiedEqualityOrbitHashed]

/-- End-to-end accounting theorem for the pinned hash-table implementation.
The theorem deliberately exposes exact operation identities separately from
the deterministic envelopes for resize hashes and bucket comparisons. -/
theorem runQuantifiedEqualityOrbitHashed_verified_cost_model
    (k : Nat) (phi : QFormula) :
    let traced := runQuantifiedEqualityOrbitHashedCosted k phi
    let result := runQuantifiedEqualityOrbitHashed k phi
    traced.result = result ∧
      traced.cost.lookups = result.stats.requests ∧
      traced.cost.inserts = result.stats.misses ∧
      traced.cost.inserts = result.table.size ∧
      traced.cost.primaryHashes = result.stats.requests + result.stats.misses ∧
      traced.cost.bucketAccesses = result.stats.requests + result.stats.misses ∧
      traced.cost.rehashHashes ≤ traced.cost.rehashEnvelope ∧
      traced.cost.keyComparisons ≤ traced.cost.comparisonEnvelope ∧
      traced.cost.totalHashes ≤
        result.stats.requests + result.stats.misses + traced.cost.rehashEnvelope := by
  let traced := runQuantifiedEqualityOrbitHashedCosted k phi
  let result := runQuantifiedEqualityOrbitHashed k phi
  have hresult : traced.result = result := by
    simp [traced, result]
  have hvalid : traced.cost.Valid := by
    exact costedExpandQuantifiedEqualityOrbitsHashed_cost_valid phi []
      (cutoffRepresentatives k) id emptyHashedEqualityOrbitMemoTable
  have hlookups : traced.cost.lookups = result.stats.requests := by
    simp [traced, result, runQuantifiedEqualityOrbitHashedCosted,
      runQuantifiedEqualityOrbitHashed]
  have hinserts : traced.cost.inserts = result.stats.misses := by
    simp [traced, result, runQuantifiedEqualityOrbitHashedCosted,
      runQuantifiedEqualityOrbitHashed]
  have hsize := runQuantifiedEqualityOrbitHashed_unique_states_eq_misses k phi
  change result.table.size = result.stats.misses at hsize
  rcases hvalid with ⟨hcomparisons, hrehashes, hprimary, hbuckets⟩
  change traced.result = result ∧
    traced.cost.lookups = result.stats.requests ∧
    traced.cost.inserts = result.stats.misses ∧
    traced.cost.inserts = result.table.size ∧
    traced.cost.primaryHashes = result.stats.requests + result.stats.misses ∧
    traced.cost.bucketAccesses = result.stats.requests + result.stats.misses ∧
    traced.cost.rehashHashes ≤ traced.cost.rehashEnvelope ∧
    traced.cost.keyComparisons ≤ traced.cost.comparisonEnvelope ∧
    traced.cost.totalHashes ≤
      result.stats.requests + result.stats.misses + traced.cost.rehashEnvelope
  refine ⟨hresult, hlookups, hinserts, ?_, ?_, ?_, hrehashes,
    hcomparisons, ?_⟩
  · omega
  · omega
  · omega
  · have htotal := OperationCost.Valid.totalHashes_le
      (costedExpandQuantifiedEqualityOrbitsHashed_cost_valid phi []
        (cutoffRepresentatives k) id emptyHashedEqualityOrbitMemoTable)
    change traced.cost.totalHashes ≤
      traced.cost.lookups + traced.cost.inserts + traced.cost.rehashEnvelope at htotal
    omega

/-- Closed collision-independent bounds at the empty root.  If `U` is the
number of unique states and `A` the number of requests, resize hashing is at
most `U²`, while worst-case separate-chain comparison work is at most
`(A + U)U`.  The request term is necessary because cache hits still probe. -/
theorem runQuantifiedEqualityOrbitHashed_closed_state_cost_bounds
    (k : Nat) (phi : QFormula) :
    let traced := runQuantifiedEqualityOrbitHashedCosted k phi
    let result := runQuantifiedEqualityOrbitHashed k phi
    traced.cost.rehashHashes ≤ result.table.size * result.table.size ∧
      traced.cost.keyComparisons ≤
        (result.stats.requests + result.table.size) * result.table.size ∧
      traced.cost.totalHashes ≤
        result.stats.requests + result.table.size +
          result.table.size * result.table.size := by
  let traced := runQuantifiedEqualityOrbitHashedCosted k phi
  let result := runQuantifiedEqualityOrbitHashed k phi
  have hbudget := costedExpandQuantifiedEqualityOrbitsHashed_cost_budget phi []
    (cutoffRepresentatives k) id emptyHashedEqualityOrbitMemoTable
  have hbudget' : traced.cost.BudgetBound result.stats.requests
      result.stats.misses result.table.size := by
    simpa [traced, result, runQuantifiedEqualityOrbitHashedCosted,
      runQuantifiedEqualityOrbitHashed] using hbudget
  rcases hbudget' with ⟨hrehashEnvelope, hcomparisonEnvelope⟩
  have hvalid := costedExpandQuantifiedEqualityOrbitsHashed_cost_valid phi []
    (cutoffRepresentatives k) id emptyHashedEqualityOrbitMemoTable
  change traced.cost.Valid at hvalid
  rcases hvalid with ⟨hcomparison, hrehash, hprimary, hbuckets⟩
  have hsize := runQuantifiedEqualityOrbitHashed_unique_states_eq_misses k phi
  change result.table.size = result.stats.misses at hsize
  have hlookups : traced.cost.lookups = result.stats.requests := by
    simp [traced, result, runQuantifiedEqualityOrbitHashedCosted,
      runQuantifiedEqualityOrbitHashed]
  have hinserts : traced.cost.inserts = result.stats.misses := by
    simp [traced, result, runQuantifiedEqualityOrbitHashedCosted,
      runQuantifiedEqualityOrbitHashed]
  rw [← hsize] at hrehashEnvelope hcomparisonEnvelope hinserts
  constructor
  · exact hrehash.trans hrehashEnvelope
  constructor
  · exact hcomparison.trans hcomparisonEnvelope
  · have htotal := OperationCost.Valid.totalHashes_le
      (costedExpandQuantifiedEqualityOrbitsHashed_cost_valid phi []
        (cutoffRepresentatives k) id emptyHashedEqualityOrbitMemoTable)
    change traced.cost.totalHashes ≤
      traced.cost.lookups + traced.cost.inserts + traced.cost.rehashEnvelope at htotal
    calc
      traced.cost.totalHashes ≤
          traced.cost.lookups + traced.cost.inserts + traced.cost.rehashEnvelope := htotal
      _ = result.stats.requests + result.table.size +
          traced.cost.rehashEnvelope := by rw [hlookups, hinserts]
      _ ≤ result.stats.requests + result.table.size +
          result.table.size * result.table.size :=
        Nat.add_le_add_left hrehashEnvelope _

/-- Fully structural rank-root corollary.  With `W` the exact cache-free
depth-sensitive Bell weight, all resizing is bounded by `W²`, all key
comparisons by `2W²`, and all hashes by `W² + 2W`. -/
theorem runQuantifiedEqualityOrbitHashed_weighted_cost_bounds
    (phi : QFormula) :
    let k := QFormula.quantifierRank phi
    let weight := equalityOrbitWeightedRequestBound phi 0
    let traced := runQuantifiedEqualityOrbitHashedCosted k phi
    traced.cost.rehashHashes ≤ weight * weight ∧
      traced.cost.keyComparisons ≤ 2 * (weight * weight) ∧
      traced.cost.totalHashes ≤ weight * weight + 2 * weight := by
  let k := QFormula.quantifierRank phi
  let weight := equalityOrbitWeightedRequestBound phi 0
  let traced := runQuantifiedEqualityOrbitHashedCosted k phi
  let result := runQuantifiedEqualityOrbitHashed k phi
  have hclosed := runQuantifiedEqualityOrbitHashed_closed_state_cost_bounds k phi
  change traced.cost.rehashHashes ≤ result.table.size * result.table.size ∧
    traced.cost.keyComparisons ≤
      (result.stats.requests + result.table.size) * result.table.size ∧
    traced.cost.totalHashes ≤ result.stats.requests + result.table.size +
      result.table.size * result.table.size at hclosed
  rcases hclosed with ⟨hrehash, hcompare, htotal⟩
  have hrequests := runQuantifiedEqualityOrbitHashed_requests_le_weighted phi
  change result.stats.requests ≤ weight at hrequests
  have hstates : result.table.size ≤ weight := by
    have hsize := runQuantifiedEqualityOrbitHashed_unique_states_eq_misses k phi
    change result.table.size = result.stats.misses at hsize
    have hmisses : result.stats.misses ≤ result.stats.requests := by
      simp [EqualityOrbitMemoStats.requests]
    omega
  have hquadratic : result.table.size * result.table.size ≤ weight * weight :=
    Nat.mul_le_mul hstates hstates
  have hcomparisonProduct :
      (result.stats.requests + result.table.size) * result.table.size ≤
        (weight + weight) * weight :=
    Nat.mul_le_mul (Nat.add_le_add hrequests hstates) hstates
  change traced.cost.rehashHashes ≤ weight * weight ∧
    traced.cost.keyComparisons ≤ 2 * (weight * weight) ∧
    traced.cost.totalHashes ≤ weight * weight + 2 * weight
  constructor
  · exact hrehash.trans hquadratic
  constructor
  · calc
      traced.cost.keyComparisons ≤
          (result.stats.requests + result.table.size) * result.table.size := hcompare
      _ ≤ (weight + weight) * weight := hcomparisonProduct
      _ = 2 * (weight * weight) := by ring
  · calc
      traced.cost.totalHashes ≤ result.stats.requests + result.table.size +
          result.table.size * result.table.size := htotal
      _ ≤ (weight + weight) + weight * weight :=
        Nat.add_le_add (Nat.add_le_add hrequests hstates) hquadratic
      _ = weight * weight + 2 * weight := by ring

/-- Native audit for the first benchmark exhibiting genuine memo sharing.
The tuple records `(hits, misses, lookups, inserts, primary hashes, resize
hashes, total hashes, bucket accesses, key comparisons, final states)`. -/
theorem hashedCost_atLeastThree_regression :
    let traced := runQuantifiedEqualityOrbitHashedCosted 3 atLeastThreeSentence
    ((traced.result.stats.hits,
        traced.result.stats.misses,
        traced.cost.lookups,
        traced.cost.inserts,
        traced.cost.primaryHashes),
      (traced.cost.rehashHashes,
        traced.cost.totalHashes,
        traced.cost.bucketAccesses,
        traced.cost.keyComparisons,
        traced.result.table.size)) =
      ((2, 40, 42, 40, 82), (38, 120, 82, 34, 40)) := by
  native_decide

/-- Concrete separation between measured work and the proved
collision-independent closed bounds.  The pairs are respectively
`(resize hashes, U²)`, `(key comparisons, (A+U)U)`, and
`(total hashes, W²+2W)`. -/
theorem hashedCost_atLeastThree_closed_bound_regression :
    let phi := atLeastThreeSentence
    let k := QFormula.quantifierRank phi
    let traced := runQuantifiedEqualityOrbitHashedCosted k phi
    let result := traced.result
    let weight := equalityOrbitWeightedRequestBound phi 0
    ((traced.cost.rehashHashes, result.table.size * result.table.size),
      (traced.cost.keyComparisons,
        (result.stats.requests + result.table.size) * result.table.size),
      (traced.cost.totalHashes, weight * weight + 2 * weight)) =
      ((38, 1600), (34, 3280), (120, 2024)) := by
  native_decide

end

end Nullivance.InfiniteFO
