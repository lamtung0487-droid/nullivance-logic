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

end

end Nullivance.InfiniteFO
