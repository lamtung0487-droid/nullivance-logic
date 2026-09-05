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

/- Lean 4.32.1 keeps the recursion equation used to prove `Raw₀.expand`
private.  This command creates a kernel-checked public alias of that imported
theorem.  It copies neither an axiom nor an implementation: the declaration's
proof term, universe parameters, and type are reused verbatim. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some expandValue := (env.find? ``Std.DHashMap.Internal.Raw₀.expand).bind
      (ConstantInfo.value? (allowOpaque := true))
    | throwError "Lean 4.32.1 Raw₀.expand definition is unavailable"
  let mut goName := Name.anonymous
  for name in expandValue.getUsedConstants do
    if let .str _ "go" := name then goName := name
  let mut goEqName := Name.anonymous
  for (candidate, candidateInfo) in env.constants.toList do
    if let .str _ "go_eq" := candidate then
      if candidateInfo.type.getUsedConstants.any (fun used => used == goName) then
        goEqName := candidate
  let some (.thmInfo goEqInfo) := env.find? goEqName
    | throwError "Lean 4.32.1 private Raw₀.expand.go_eq theorem is unavailable"
  let publicName := Name.str
    (Name.str (Name.str (Name.str Name.anonymous "Nullivance") "InfiniteFO") "HashCost")
    "rawExpandGoEquationPinned"
  liftCoreM <| addDecl (.thmDecl { goEqInfo with name := publicName })
  let some emptyValue :=
      (env.find? ``Std.DHashMap.Internal.Raw₀.emptyWithCapacity).bind
        (ConstantInfo.value? (allowOpaque := true))
    | throwError "Lean 4.32.1 Raw₀.emptyWithCapacity definition is unavailable"
  let mut capacityName := Name.anonymous
  for name in emptyValue.getUsedConstants do
    if let .str _ "numBucketsForCapacity" := name then capacityName := name
  let some (.defnInfo capacityInfo) := env.find? capacityName
    | throwError "Lean 4.32.1 private numBucketsForCapacity definition is unavailable"
  let capacityPublic := Name.str
    (Name.str (Name.str (Name.str Name.anonymous "Nullivance") "InfiniteFO") "HashCost")
    "numBucketsForCapacityPinned"
  liftCoreM do
    addDecl (.defnDecl { capacityInfo with name := capacityPublic })
    enableRealizationsForConst capacityPublic
  let some nextPowerValue := (env.find? ``Nat.nextPowerOfTwo).bind
      (ConstantInfo.value? (allowOpaque := true))
    | throwError "Nat.nextPowerOfTwo definition is unavailable"
  let mut nextPowerGoName := Name.anonymous
  for name in nextPowerValue.getUsedConstants do
    if let .str _ "go" := name then nextPowerGoName := name
  let mut nextPowerEqName := Name.anonymous
  for (candidate, candidateInfo) in env.constants.toList do
    if let .str _ "eq_def" := candidate then
      if candidateInfo.type.getUsedConstants.any
          (fun used => used == nextPowerGoName) then
        nextPowerEqName := candidate
  let some (.thmInfo nextPowerEqInfo) := env.find? nextPowerEqName
    | throwError "private Nat.nextPowerOfTwo.go equation is unavailable"
  let nextPowerEqPublic := Name.str
    (Name.str (Name.str (Name.str Name.anonymous "Nullivance") "InfiniteFO") "HashCost")
    "nextPowerOfTwoGoEquationPinned"
  liftCoreM <| addDecl (.thmDecl { nextPowerEqInfo with name := nextPowerEqPublic })

/-- One low-level reinsertion changes a bucket's contents but not the physical
bucket-array length. -/
theorem reinsertAux_bucketCount
    {α : Type} {β : α → Type} [Hashable α]
    (target : { d : Array (AssocList α β) // 0 < d.size })
    (a : α) (b : β a) :
    (Raw₀.reinsertAux hash target a b).1.size = target.1.size := by
  simp [Raw₀.reinsertAux]

theorem foldl_reinsertAux_bucketCount
    {α : Type} {β : α → Type} [Hashable α]
    (entries : List ((a : α) × β a))
    (target : { d : Array (AssocList α β) // 0 < d.size }) :
    (entries.foldl (fun acc p => Raw₀.reinsertAux hash acc p.1 p.2) target).1.size =
      target.1.size := by
  induction entries generalizing target with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.foldl_cons]
      rw [ih, reinsertAux_bucketCount]

/-- Source-level doubling theorem for the pinned Lean 4.32.1 implementation:
`Raw₀.expand` allocates exactly twice as many physical buckets. -/
theorem rawExpand_bucketCount_eq_double
    {α : Type} {β : α → Type} [BEq α] [Hashable α] [PartialEquivBEq α]
    (data : { d : Array (AssocList α β) // 0 < d.size }) :
    (Raw₀.expand data).1.size = data.1.size * 2 := by
  rcases data with ⟨source, hsource⟩
  simp only [Raw₀.expand]
  rw [rawExpandGoEquationPinned]
  rw [foldl_reinsertAux_bucketCount]
  simp

theorem loadFactorBound_implies_spare
    {size buckets : Nat}
    (hload : size * 4 / 3 ≤ buckets) (hbuckets : 3 ≤ buckets) :
    size + 1 ≤ buckets := by
  have hlt : size * 4 < (buckets + 1) * 3 := by
    exact (Nat.div_lt_iff_lt_mul (by omega)).mp
      (lt_of_le_of_lt hload (by omega))
  omega

/-- At a missing-key insertion the physical bucket count is unchanged or
doubled; there is no third case. -/
theorem insert_missing_bucketCount_cases
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) (value : EqBoolFormula)
    (habsent : table.get? key = none) :
    hashedMemoBucketCount (table.insert key value) = hashedMemoBucketCount table ∨
      hashedMemoBucketCount (table.insert key value) =
        2 * hashedMemoBucketCount table := by
  have hcontains : table.inner.contains key = false := by
    rw [Std.DHashMap.Const.contains_eq_isSome_get?]
    change (table.get? key).isSome = false
    rw [habsent]
    rfl
  simp only [hashedMemoBucketCount, Std.HashMap.insert, Std.DHashMap.insert]
  simp only [Raw₀.insert]
  simp only [Std.DHashMap.contains, Raw₀.contains] at hcontains
  rw [hcontains]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Raw₀.expandIfNecessary]
  split
  · left
    simp
  · right
    rw [rawExpand_bucketCount_eq_double]
    simp [Nat.mul_comm]

/-- Capacity invariant sufficient for amortized resizing: at least one
physical bucket is spare. -/
def HasSpareBucket (table : HashedEqualityOrbitMemoTable) : Prop :=
  table.size < hashedMemoBucketCount table

def HasMinimumBuckets (table : HashedEqualityOrbitMemoTable) : Prop :=
  3 ≤ hashedMemoBucketCount table

theorem insert_missing_preserves_spare
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) (value : EqBoolFormula)
    (habsent : table.get? key = none)
    (hspare : HasSpareBucket table) (hfloor : HasMinimumBuckets table) :
    HasSpareBucket (table.insert key value) := by
  have hcontains : table.inner.contains key = false := by
    rw [Std.DHashMap.Const.contains_eq_isSome_get?]
    change (table.get? key).isSome = false
    rw [habsent]
    rfl
  have hnotmem : key ∉ table := by
    change table.inner.contains key ≠ true
    rw [hcontains]
    decide
  rw [HasSpareBucket, Std.HashMap.size_insert, if_neg hnotmem]
  simp only [hashedMemoBucketCount, Std.HashMap.insert, Std.DHashMap.insert]
  simp only [Raw₀.insert]
  simp only [Std.DHashMap.contains, Raw₀.contains] at hcontains
  rw [hcontains]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Raw₀.expandIfNecessary]
  split
  · rename_i hthreshold
    simp only [Array.size_uset] at hthreshold
    change (table.inner.inner.size + 1) * 4 / 3 ≤
      table.inner.inner.buckets.size at hthreshold
    have hstrict := loadFactorBound_implies_spare hthreshold hfloor
    simp only [Array.size_uset, Std.HashMap.size, Std.DHashMap.size]
    change table.inner.inner.size + 1 < table.inner.inner.buckets.size
    omega
  · rw [rawExpand_bucketCount_eq_double]
    simp only [Array.size_uset, Std.HashMap.size, Std.DHashMap.size]
    change table.inner.inner.size < table.inner.inner.buckets.size at hspare
    change 3 ≤ table.inner.inner.buckets.size at hfloor
    change table.inner.inner.size + 1 < table.inner.inner.buckets.size * 2
    omega

theorem insert_missing_preserves_minimumBuckets
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) (value : EqBoolFormula)
    (habsent : table.get? key = none) (hfloor : HasMinimumBuckets table) :
    HasMinimumBuckets (table.insert key value) := by
  rcases insert_missing_bucketCount_cases table key value habsent with hsame | hdouble
  · rw [HasMinimumBuckets, hsame]
    exact hfloor
  · rw [HasMinimumBuckets, hdouble]
    rw [HasMinimumBuckets] at hfloor
    omega

theorem insert_present_bucketCount_eq
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) (value cached : EqBoolFormula)
    (hpresent : table.get? key = some cached) :
    hashedMemoBucketCount (table.insert key value) = hashedMemoBucketCount table := by
  have hcontains : table.inner.contains key = true := by
    rw [Std.DHashMap.Const.contains_eq_isSome_get?]
    change (table.get? key).isSome = true
    rw [hpresent]
    rfl
  simp only [hashedMemoBucketCount, Std.HashMap.insert, Std.DHashMap.insert]
  simp only [Raw₀.insert]
  simp only [Std.DHashMap.contains, Raw₀.contains] at hcontains
  rw [hcontains]
  simp

theorem insert_preserves_spare
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) (value : EqBoolFormula)
    (hspare : HasSpareBucket table) (hfloor : HasMinimumBuckets table) :
    HasSpareBucket (table.insert key value) := by
  cases hpresent : table.get? key with
  | none => exact insert_missing_preserves_spare table key value hpresent hspare hfloor
  | some cached =>
      have hcontains : table.inner.contains key = true := by
        rw [Std.DHashMap.Const.contains_eq_isSome_get?]
        change (table.get? key).isSome = true
        rw [hpresent]
        rfl
      have hmem : key ∈ table := by exact hcontains
      rw [HasSpareBucket, Std.HashMap.size_insert, if_pos hmem,
        insert_present_bucketCount_eq table key value cached hpresent]
      exact hspare

theorem insert_preserves_minimumBuckets
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) (value : EqBoolFormula)
    (hfloor : HasMinimumBuckets table) :
    HasMinimumBuckets (table.insert key value) := by
  cases hpresent : table.get? key with
  | none =>
      exact insert_missing_preserves_minimumBuckets table key value hpresent hfloor
  | some cached =>
      rw [HasMinimumBuckets,
        insert_present_bucketCount_eq table key value cached hpresent]
      exact hfloor

/-- Root-capacity envelope for maps originating at capacity eight.  The
constant 16 is the actual initial bucket count in Lean 4.32.1. -/
def BucketCountLinearBound (table : HashedEqualityOrbitMemoTable) : Prop :=
  hashedMemoBucketCount table ≤ 16 + 3 * table.size

theorem insert_missing_preserves_bucketCountLinearBound
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) (value : EqBoolFormula)
    (habsent : table.get? key = none)
    (hbound : BucketCountLinearBound table) :
    BucketCountLinearBound (table.insert key value) := by
  have hcontains : table.inner.contains key = false := by
    rw [Std.DHashMap.Const.contains_eq_isSome_get?]
    change (table.get? key).isSome = false
    rw [habsent]
    rfl
  have hnotmem : key ∉ table := by
    change table.inner.contains key ≠ true
    rw [hcontains]
    decide
  rw [BucketCountLinearBound, Std.HashMap.size_insert, if_neg hnotmem]
  simp only [hashedMemoBucketCount, Std.HashMap.insert, Std.DHashMap.insert]
  simp only [Raw₀.insert]
  simp only [Std.DHashMap.contains, Raw₀.contains] at hcontains
  rw [hcontains]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Raw₀.expandIfNecessary]
  split
  · simp only [Array.size_uset, Std.HashMap.size, Std.DHashMap.size]
    rw [BucketCountLinearBound] at hbound
    change table.inner.inner.buckets.size ≤
      16 + 3 * table.inner.inner.size at hbound
    change table.inner.inner.buckets.size ≤
      16 + 3 * (table.inner.inner.size + 1)
    omega
  · rename_i hthreshold
    simp only [Array.size_uset] at hthreshold
    change ¬(table.inner.inner.size + 1) * 4 / 3 ≤
      table.inner.inner.buckets.size at hthreshold
    have htrigger : table.inner.inner.buckets.size <
        (table.inner.inner.size + 1) * 4 / 3 := Nat.lt_of_not_ge hthreshold
    have hmul := (Nat.lt_div_iff_mul_lt (by omega)).mp htrigger
    rw [rawExpand_bucketCount_eq_double]
    simp only [Array.size_uset, Std.HashMap.size, Std.DHashMap.size]
    change table.inner.inner.buckets.size * 2 ≤
      16 + 3 * (table.inner.inner.size + 1)
    omega

theorem insert_preserves_bucketCountLinearBound
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) (value : EqBoolFormula)
    (hbound : BucketCountLinearBound table) :
    BucketCountLinearBound (table.insert key value) := by
  cases hpresent : table.get? key with
  | none =>
      exact insert_missing_preserves_bucketCountLinearBound
        table key value hpresent hbound
  | some cached =>
      have hcontains : table.inner.contains key = true := by
        rw [Std.DHashMap.Const.contains_eq_isSome_get?]
        change (table.get? key).isSome = true
        rw [hpresent]
        rfl
      have hmem : key ∈ table := by exact hcontains
      rw [BucketCountLinearBound, Std.HashMap.size_insert, if_pos hmem,
        insert_present_bucketCount_eq table key value cached hpresent]
      exact hbound

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
  /-- Maximum length of a bucket actually probed by lookup or insertion.
  This is a maximum over the execution, not the final table's maximum. -/
  peakBucketEntries : Nat := 0
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
  peakBucketEntries := max left.peakBucketEntries right.peakBucketEntries

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
    comparisonEnvelope := assocEntryCount (hashedMemoBucket table key)
    peakBucketEntries := assocEntryCount (hashedMemoBucket table key) }

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
    comparisonEnvelope := assocEntryCount (hashedMemoBucket table key)
    peakBucketEntries := assocEntryCount (hashedMemoBucket table key) }

/-- A resizing transition is paid for by physical bucket growth.  Sequential
transitions compose by cancellation of their shared intermediate bucket count. -/
def OperationCost.RehashTransition (cost : OperationCost)
    (initial final : HashedEqualityOrbitMemoTable) : Prop :=
  cost.rehashHashes + hashedMemoBucketCount initial ≤ hashedMemoBucketCount final

theorem OperationCost.RehashTransition.zero
    (table : HashedEqualityOrbitMemoTable) :
    ({} : OperationCost).RehashTransition table table := by
  simp [OperationCost.RehashTransition]

theorem OperationCost.RehashTransition.add
    {left right : OperationCost}
    {initial middle final : HashedEqualityOrbitMemoTable}
    (hleft : left.RehashTransition initial middle)
    (hright : right.RehashTransition middle final) :
    (left.add right).RehashTransition initial final := by
  simp only [OperationCost.RehashTransition, OperationCost.add] at *
  omega

theorem OperationCost.RehashTransition.withStats
    {cost : OperationCost} {initial final : HashedEqualityOrbitMemoTable}
    (hcost : cost.RehashTransition initial final)
    (stats : EqualityOrbitMemoStats) :
    (cost.withStats stats).RehashTransition initial final := by
  exact hcost

theorem lookupCost_rehashTransition
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) :
    (lookupCost table key).RehashTransition table table := by
  simp [OperationCost.RehashTransition, lookupCost]

/-- Local amortized insertion theorem.  It is intentionally valid even when
the key is already present: replacement then has zero resizing charge. -/
theorem insertMissCost_rehashTransition
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) (value : EqBoolFormula)
    (hspare : HasSpareBucket table) (hfloor : HasMinimumBuckets table) :
    (insertMissCost table key value).RehashTransition table
      (table.insert key value) := by
  cases hpresent : table.get? key with
  | some cached =>
      have hsame := insert_present_bucketCount_eq table key value cached hpresent
      simp [OperationCost.RehashTransition, insertMissCost, hsame]
  | none =>
      have hcontains : table.inner.contains key = false := by
        rw [Std.DHashMap.Const.contains_eq_isSome_get?]
        change (table.get? key).isSome = false
        rw [hpresent]
        rfl
      have hnotmem : key ∉ table := by
        change table.inner.contains key ≠ true
        rw [hcontains]
        decide
      have hsize : (table.insert key value).size = table.size + 1 := by
        rw [Std.HashMap.size_insert, if_neg hnotmem]
      rcases insert_missing_bucketCount_cases table key value hpresent with
        hsame | hdouble
      · simp [OperationCost.RehashTransition, insertMissCost, hsame]
      · have hpositive : 0 < hashedMemoBucketCount table := by
          rw [HasMinimumBuckets] at hfloor
          omega
        have hgrowth : hashedMemoBucketCount table <
            hashedMemoBucketCount (table.insert key value) := by
          rw [hdouble]
          omega
        simp only [OperationCost.RehashTransition, insertMissCost,
          hgrowth, ↓reduceIte]
        rw [hdouble, hsize]
        rw [HasSpareBucket] at hspare
        omega

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

def HashCost.OperationCost.AmortizedExecution (cost : OperationCost)
    (initial final : HashedEqualityOrbitMemoTable) : Prop :=
  cost.RehashTransition initial final ∧
    HasSpareBucket final ∧ HasMinimumBuckets final

theorem HashCost.OperationCost.AmortizedExecution.zero
    (table : HashedEqualityOrbitMemoTable)
    (hspare : HasSpareBucket table) (hfloor : HasMinimumBuckets table) :
    ({} : OperationCost).AmortizedExecution table table := by
  exact ⟨OperationCost.RehashTransition.zero table, hspare, hfloor⟩

theorem HashCost.OperationCost.AmortizedExecution.add
    {left right : OperationCost}
    {initial middle final : HashedEqualityOrbitMemoTable}
    (hleft : left.AmortizedExecution initial middle)
    (hright : right.AmortizedExecution middle final) :
    (left.add right).AmortizedExecution initial final := by
  exact ⟨hleft.1.add hright.1, hright.2⟩

theorem HashCost.OperationCost.AmortizedExecution.withStats
    {cost : OperationCost} {initial final : HashedEqualityOrbitMemoTable}
    (hcost : cost.AmortizedExecution initial final)
    (stats : EqualityOrbitMemoStats) :
    (cost.withStats stats).AmortizedExecution initial final := by
  exact ⟨hcost.1.withStats stats, hcost.2⟩

theorem lookupCost_amortizedExecution
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey)
    (hspare : HasSpareBucket table) (hfloor : HasMinimumBuckets table) :
    (lookupCost table key).AmortizedExecution table table := by
  exact ⟨lookupCost_rehashTransition table key, hspare, hfloor⟩

theorem insertMissCost_amortizedExecution
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) (value : EqBoolFormula)
    (hspare : HasSpareBucket table) (hfloor : HasMinimumBuckets table) :
    (insertMissCost table key value).AmortizedExecution table
      (table.insert key value) := by
  exact ⟨insertMissCost_rehashTransition table key value hspare hfloor,
    insert_preserves_spare table key value hspare hfloor,
    insert_preserves_minimumBuckets table key value hfloor⟩

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
  /-- The amortized resizing invariant is threaded through every recursive
  orbit call and every binder-generated sibling branch. -/
  theorem costedExpandQuantifiedEqualityOrbitsHashed_amortized
      (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
      (table : HashedEqualityOrbitMemoTable)
      (hspare : HasSpareBucket table) (hfloor : HasMinimumBuckets table) :
      let traced := costedExpandQuantifiedEqualityOrbitsHashed
        phi used available env table
      traced.cost.AmortizedExecution table traced.result.table := by
    rw [costedExpandQuantifiedEqualityOrbitsHashed.eq_def]
    dsimp only
    apply OperationCost.AmortizedExecution.withStats
    split
    next cached hlookup =>
      rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
      dsimp only
      rw [hlookup]
      simpa using
        lookupCost_amortizedExecution table
          (recursiveEqualityOrbitMemoKey phi used available env) hspare hfloor
    next hlookup =>
      cases phi with
      | pred P xs =>
          let key := recursiveEqualityOrbitMemoKey (.pred P xs) used available env
          have hlookupCost := lookupCost_amortizedExecution table key hspare hfloor
          have hzero := OperationCost.AmortizedExecution.zero table hspare hfloor
          have hinsert := insertMissCost_amortizedExecution table key .bot hspare hfloor
          rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
          dsimp only
          rw [hlookup]
          simpa [key] using
            hlookupCost.add (hzero.add hinsert)
      | eq x y =>
          let key := recursiveEqualityOrbitMemoKey (.eq x y) used available env
          let value := if env x = env y then EqBoolFormula.top
            else EqBoolFormula.atom (normalizeEqAtom (env x) (env y))
          have hlookupCost := lookupCost_amortizedExecution table key hspare hfloor
          have hzero := OperationCost.AmortizedExecution.zero table hspare hfloor
          have hinsert := insertMissCost_amortizedExecution table key value hspare hfloor
          rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
          dsimp only
          rw [hlookup]
          simpa [key, value] using
            hlookupCost.add (hzero.add hinsert)
      | neg body =>
          let key := recursiveEqualityOrbitMemoKey (.neg body) used available env
          let child := costedExpandQuantifiedEqualityOrbitsHashed
            body used available env table
          let value := EqBoolFormula.neg child.result.formula
          have hlookupCost := lookupCost_amortizedExecution table key hspare hfloor
          have hchild := costedExpandQuantifiedEqualityOrbitsHashed_amortized
            body used available env table hspare hfloor
          have hinsert := insertMissCost_amortizedExecution child.result.table key value
            hchild.2.1 hchild.2.2
          rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
          dsimp only
          rw [hlookup]
          simpa [key, child, value] using hlookupCost.add (hchild.add hinsert)
      | conj left right =>
          let key := recursiveEqualityOrbitMemoKey (.conj left right)
            used available env
          let leftResult := costedExpandQuantifiedEqualityOrbitsHashed
            left used available env table
          let rightResult := costedExpandQuantifiedEqualityOrbitsHashed
            right used available env leftResult.result.table
          let value := EqBoolFormula.conj
            leftResult.result.formula rightResult.result.formula
          have hlookupCost := lookupCost_amortizedExecution table key hspare hfloor
          have hleft := costedExpandQuantifiedEqualityOrbitsHashed_amortized
            left used available env table hspare hfloor
          have hright := costedExpandQuantifiedEqualityOrbitsHashed_amortized
            right used available env leftResult.result.table hleft.2.1 hleft.2.2
          have hinsert := insertMissCost_amortizedExecution rightResult.result.table
            key value hright.2.1 hright.2.2
          rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
          dsimp only
          rw [hlookup]
          simpa [key, leftResult, rightResult, value] using
            hlookupCost.add ((hleft.add hright).add hinsert)
      | disj left right =>
          let key := recursiveEqualityOrbitMemoKey (.disj left right)
            used available env
          let leftResult := costedExpandQuantifiedEqualityOrbitsHashed
            left used available env table
          let rightResult := costedExpandQuantifiedEqualityOrbitsHashed
            right used available env leftResult.result.table
          let value := EqBoolFormula.disj
            leftResult.result.formula rightResult.result.formula
          have hlookupCost := lookupCost_amortizedExecution table key hspare hfloor
          have hleft := costedExpandQuantifiedEqualityOrbitsHashed_amortized
            left used available env table hspare hfloor
          have hright := costedExpandQuantifiedEqualityOrbitsHashed_amortized
            right used available env leftResult.result.table hleft.2.1 hleft.2.2
          have hinsert := insertMissCost_amortizedExecution rightResult.result.table
            key value hright.2.1 hright.2.2
          rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
          dsimp only
          rw [hlookup]
          simpa [key, leftResult, rightResult, value] using
            hlookupCost.add ((hleft.add hright).add hinsert)
      | oplus left right =>
          let key := recursiveEqualityOrbitMemoKey (.oplus left right)
            used available env
          have hlookupCost := lookupCost_amortizedExecution table key hspare hfloor
          have hzero := OperationCost.AmortizedExecution.zero table hspare hfloor
          have hinsert := insertMissCost_amortizedExecution table key .bot hspare hfloor
          rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
          dsimp only
          rw [hlookup]
          simpa [key] using
            hlookupCost.add (hzero.add hinsert)
      | all x body =>
          let key := recursiveEqualityOrbitMemoKey (.all x body) used available env
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
          let branchProduction := expandQuantifiedEqualityOrbitBranchesHashed
            body (oldQueries ++ freshQueries) table
          let value := EqBoolFormula.conjList branchProduction.formulas
          have hproduction :
              expandQuantifiedEqualityOrbitsHashed (.all x body)
                used available env table =
                ⟨value, branchProduction.table.insert key value,
                  branchProduction.stats.add EqualityOrbitMemoStats.miss⟩ := by
            rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
            dsimp only
            rw [hlookup]
            rfl
          rw [hproduction]
          have hlookupCost := lookupCost_amortizedExecution table key hspare hfloor
          have hbranches :=
            costedExpandQuantifiedEqualityOrbitBranchesHashed_amortized
              body (oldQueries ++ freshQueries) table hspare hfloor
          have hinsert := insertMissCost_amortizedExecution branches.result.table
            key value hbranches.2.1 hbranches.2.2
          simpa [key, oldQueries, freshQueries, branches, branchProduction,
            value] using
            hlookupCost.add (hbranches.add hinsert)
      | ex x body =>
          let key := recursiveEqualityOrbitMemoKey (.ex x body) used available env
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
          let branchProduction := expandQuantifiedEqualityOrbitBranchesHashed
            body (oldQueries ++ freshQueries) table
          let value := EqBoolFormula.disjList branchProduction.formulas
          have hproduction :
              expandQuantifiedEqualityOrbitsHashed (.ex x body)
                used available env table =
                ⟨value, branchProduction.table.insert key value,
                  branchProduction.stats.add EqualityOrbitMemoStats.miss⟩ := by
            rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
            dsimp only
            rw [hlookup]
            rfl
          rw [hproduction]
          have hlookupCost := lookupCost_amortizedExecution table key hspare hfloor
          have hbranches :=
            costedExpandQuantifiedEqualityOrbitBranchesHashed_amortized
              body (oldQueries ++ freshQueries) table hspare hfloor
          have hinsert := insertMissCost_amortizedExecution branches.result.table
            key value hbranches.2.1 hbranches.2.2
          simpa [key, oldQueries, freshQueries, branches, branchProduction,
            value] using
            hlookupCost.add (hbranches.add hinsert)
  termination_by (sizeOf phi, 0)

  theorem costedExpandQuantifiedEqualityOrbitBranchesHashed_amortized
      (body : QFormula) (queries : List RecursiveEqualityOrbitBranchQuery)
      (table : HashedEqualityOrbitMemoTable)
      (hspare : HasSpareBucket table) (hfloor : HasMinimumBuckets table) :
      let traced := costedExpandQuantifiedEqualityOrbitBranchesHashed
        body queries table
      traced.cost.AmortizedExecution table traced.result.table := by
    cases queries with
    | nil =>
        rw [costedExpandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        exact (OperationCost.AmortizedExecution.zero table hspare hfloor).withStats _
    | cons query rest =>
        rw [costedExpandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        let headResult := costedExpandQuantifiedEqualityOrbitsHashed body
          query.used query.available query.env table
        let tailResult := costedExpandQuantifiedEqualityOrbitBranchesHashed
          body rest headResult.result.table
        have hhead := costedExpandQuantifiedEqualityOrbitsHashed_amortized body
          query.used query.available query.env table hspare hfloor
        have htail := costedExpandQuantifiedEqualityOrbitBranchesHashed_amortized
          body rest headResult.result.table hhead.2.1 hhead.2.2
        simpa [headResult, tailResult] using (hhead.add htail).withStats _
  termination_by (sizeOf body, queries.length + 1)
end

mutual
  theorem expandQuantifiedEqualityOrbitsHashed_preserves_bucketCountLinearBound
      (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
      (table : HashedEqualityOrbitMemoTable)
      (hbound : BucketCountLinearBound table) :
      BucketCountLinearBound
        (expandQuantifiedEqualityOrbitsHashed phi used available env table).table := by
    rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
    dsimp only
    split
    next cached hlookup => exact hbound
    next hlookup =>
      cases phi with
      | pred P xs =>
          exact insert_preserves_bucketCountLinearBound table _ .bot hbound
      | eq x y =>
          exact insert_preserves_bucketCountLinearBound table _
            (if env x = env y then .top else .atom (normalizeEqAtom (env x) (env y)))
            hbound
      | neg body =>
          let child := expandQuantifiedEqualityOrbitsHashed
            body used available env table
          have hchild :=
            expandQuantifiedEqualityOrbitsHashed_preserves_bucketCountLinearBound
              body used available env table hbound
          exact insert_preserves_bucketCountLinearBound child.table _
            (.neg child.formula) hchild
      | conj left right =>
          let leftResult := expandQuantifiedEqualityOrbitsHashed
            left used available env table
          let rightResult := expandQuantifiedEqualityOrbitsHashed
            right used available env leftResult.table
          have hleft :=
            expandQuantifiedEqualityOrbitsHashed_preserves_bucketCountLinearBound
              left used available env table hbound
          have hright :=
            expandQuantifiedEqualityOrbitsHashed_preserves_bucketCountLinearBound
              right used available env leftResult.table hleft
          exact insert_preserves_bucketCountLinearBound rightResult.table _
            (.conj leftResult.formula rightResult.formula) hright
      | disj left right =>
          let leftResult := expandQuantifiedEqualityOrbitsHashed
            left used available env table
          let rightResult := expandQuantifiedEqualityOrbitsHashed
            right used available env leftResult.table
          have hleft :=
            expandQuantifiedEqualityOrbitsHashed_preserves_bucketCountLinearBound
              left used available env table hbound
          have hright :=
            expandQuantifiedEqualityOrbitsHashed_preserves_bucketCountLinearBound
              right used available env leftResult.table hleft
          exact insert_preserves_bucketCountLinearBound rightResult.table _
            (.disj leftResult.formula rightResult.formula) hright
      | oplus left right =>
          exact insert_preserves_bucketCountLinearBound table _ .bot hbound
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
          let branches := expandQuantifiedEqualityOrbitBranchesHashed
            body (oldQueries ++ freshQueries) table
          have hbranches :=
            expandQuantifiedEqualityOrbitBranchesHashed_preserves_bucketCountLinearBound
              body (oldQueries ++ freshQueries) table hbound
          exact insert_preserves_bucketCountLinearBound branches.table _
            (EqBoolFormula.conjList branches.formulas) hbranches
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
          let branches := expandQuantifiedEqualityOrbitBranchesHashed
            body (oldQueries ++ freshQueries) table
          have hbranches :=
            expandQuantifiedEqualityOrbitBranchesHashed_preserves_bucketCountLinearBound
              body (oldQueries ++ freshQueries) table hbound
          exact insert_preserves_bucketCountLinearBound branches.table _
            (EqBoolFormula.disjList branches.formulas) hbranches
  termination_by (sizeOf phi, 0)

  theorem expandQuantifiedEqualityOrbitBranchesHashed_preserves_bucketCountLinearBound
      (body : QFormula) (queries : List RecursiveEqualityOrbitBranchQuery)
      (table : HashedEqualityOrbitMemoTable)
      (hbound : BucketCountLinearBound table) :
      BucketCountLinearBound
        (expandQuantifiedEqualityOrbitBranchesHashed body queries table).table := by
    cases queries with
    | nil =>
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        exact hbound
    | cons query rest =>
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        let headResult := expandQuantifiedEqualityOrbitsHashed body
          query.used query.available query.env table
        have hhead :=
          expandQuantifiedEqualityOrbitsHashed_preserves_bucketCountLinearBound
            body query.used query.available query.env table hbound
        exact expandQuantifiedEqualityOrbitBranchesHashed_preserves_bucketCountLinearBound
          body rest headResult.table hhead
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

/-- Lean 4.32.1 turns requested capacity eight into sixteen physical buckets. -/
theorem emptyHashedEqualityOrbitMemoTable_bucketCount :
    hashedMemoBucketCount emptyHashedEqualityOrbitMemoTable = 16 := by
  unfold hashedMemoBucketCount emptyHashedEqualityOrbitMemoTable
    Std.HashMap.emptyWithCapacity Std.DHashMap.emptyWithCapacity
    Std.DHashMap.Raw.emptyWithCapacity
    Std.DHashMap.Internal.Raw₀.emptyWithCapacity
  simp only [Array.size_replicate]
  change (HashCost.numBucketsForCapacityPinned 8).nextPowerOfTwo = 16
  unfold HashCost.numBucketsForCapacityPinned
  unfold Nat.nextPowerOfTwo
  rw [HashCost.nextPowerOfTwoGoEquationPinned]
  rw [if_pos (by decide : 1 < 10)]
  rw [HashCost.nextPowerOfTwoGoEquationPinned]
  rw [if_pos (by decide : 2 < 10)]
  rw [HashCost.nextPowerOfTwoGoEquationPinned]
  rw [if_pos (by decide : 4 < 10)]
  rw [HashCost.nextPowerOfTwoGoEquationPinned]
  rw [if_pos (by decide : 8 < 10)]
  rw [HashCost.nextPowerOfTwoGoEquationPinned]
  rw [if_neg (by decide : ¬16 < 10)]

theorem emptyHashedEqualityOrbitMemoTable_hasSpareBucket :
    HasSpareBucket emptyHashedEqualityOrbitMemoTable := by
  rw [HasSpareBucket, emptyHashedEqualityOrbitMemoTable_bucketCount]
  simp [emptyHashedEqualityOrbitMemoTable]

theorem emptyHashedEqualityOrbitMemoTable_hasMinimumBuckets :
    HasMinimumBuckets emptyHashedEqualityOrbitMemoTable := by
  rw [HasMinimumBuckets, emptyHashedEqualityOrbitMemoTable_bucketCount]
  omega

theorem emptyHashedEqualityOrbitMemoTable_bucketCountLinearBound :
    BucketCountLinearBound emptyHashedEqualityOrbitMemoTable := by
  rw [BucketCountLinearBound, emptyHashedEqualityOrbitMemoTable_bucketCount]
  simp [emptyHashedEqualityOrbitMemoTable]

/-- Root transition theorem: all resize hashes plus the sixteen initial
buckets fit inside the final physical bucket count. -/
theorem runQuantifiedEqualityOrbitHashed_rehashTransition
    (k : Nat) (phi : QFormula) :
    let traced := runQuantifiedEqualityOrbitHashedCosted k phi
    let result := runQuantifiedEqualityOrbitHashed k phi
    traced.cost.rehashHashes + 16 ≤ hashedMemoBucketCount result.table := by
  have hrun := costedExpandQuantifiedEqualityOrbitsHashed_amortized phi []
    (cutoffRepresentatives k) id emptyHashedEqualityOrbitMemoTable
    emptyHashedEqualityOrbitMemoTable_hasSpareBucket
    emptyHashedEqualityOrbitMemoTable_hasMinimumBuckets
  have htransition := hrun.1
  simpa [OperationCost.RehashTransition,
    runQuantifiedEqualityOrbitHashedCosted,
    runQuantifiedEqualityOrbitHashed,
    emptyHashedEqualityOrbitMemoTable_bucketCount] using htransition

theorem runQuantifiedEqualityOrbitHashed_bucketCountLinearBound
    (k : Nat) (phi : QFormula) :
    let result := runQuantifiedEqualityOrbitHashed k phi
    hashedMemoBucketCount result.table ≤ 16 + 3 * result.table.size := by
  have hbound :=
    expandQuantifiedEqualityOrbitsHashed_preserves_bucketCountLinearBound
      phi [] (cutoffRepresentatives k) id emptyHashedEqualityOrbitMemoTable
      emptyHashedEqualityOrbitMemoTable_bucketCountLinearBound
  simpa [BucketCountLinearBound, runQuantifiedEqualityOrbitHashed] using hbound

/-- Coarse collision-independent envelope retained as the representation-
agnostic baseline: it charges every miss the final table size. -/
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

/-- Closed collision-independent bounds at the empty root.  If `U` is the
number of unique states and `A` the number of requests, doubling gives the
amortized resize bound `3U`, while worst-case separate-chain comparison work
is at most `(A + U)U`.  The request term is necessary because cache hits still
probe. -/
theorem runQuantifiedEqualityOrbitHashed_amortized_state_cost_bounds
    (k : Nat) (phi : QFormula) :
    let traced := runQuantifiedEqualityOrbitHashedCosted k phi
    let result := runQuantifiedEqualityOrbitHashed k phi
    traced.cost.rehashHashes ≤ 3 * result.table.size ∧
      traced.cost.keyComparisons ≤
        (result.stats.requests + result.table.size) * result.table.size ∧
      traced.cost.totalHashes ≤
        result.stats.requests + 4 * result.table.size := by
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
  have htransition := runQuantifiedEqualityOrbitHashed_rehashTransition k phi
  change traced.cost.rehashHashes + 16 ≤
    hashedMemoBucketCount result.table at htransition
  have hbucketBound := runQuantifiedEqualityOrbitHashed_bucketCountLinearBound k phi
  change hashedMemoBucketCount result.table ≤
    16 + 3 * result.table.size at hbucketBound
  have hrehashLinear : traced.cost.rehashHashes ≤ 3 * result.table.size := by
    omega
  constructor
  · exact hrehashLinear
  constructor
  · exact hcomparison.trans hcomparisonEnvelope
  · change traced.cost.primaryHashes + traced.cost.rehashHashes ≤
      result.stats.requests + 4 * result.table.size
    calc
      traced.cost.primaryHashes + traced.cost.rehashHashes =
          result.stats.requests + result.table.size +
            traced.cost.rehashHashes := by rw [hprimary, hlookups, hinserts]
      _ ≤ result.stats.requests + result.table.size +
          3 * result.table.size := Nat.add_le_add_left hrehashLinear _
      _ = result.stats.requests + 4 * result.table.size := by ring

/-- Fully structural rank-root corollary.  With `W` the exact cache-free
depth-sensitive Bell weight, all resizing is bounded by `3W`, all key
comparisons by `2W²`, and all hashes by `5W`. -/
theorem runQuantifiedEqualityOrbitHashed_weighted_amortized_cost_bounds
    (phi : QFormula) :
    let k := QFormula.quantifierRank phi
    let weight := equalityOrbitWeightedRequestBound phi 0
    let traced := runQuantifiedEqualityOrbitHashedCosted k phi
    traced.cost.rehashHashes ≤ 3 * weight ∧
      traced.cost.keyComparisons ≤ 2 * (weight * weight) ∧
      traced.cost.totalHashes ≤ 5 * weight := by
  let k := QFormula.quantifierRank phi
  let weight := equalityOrbitWeightedRequestBound phi 0
  let traced := runQuantifiedEqualityOrbitHashedCosted k phi
  let result := runQuantifiedEqualityOrbitHashed k phi
  have hclosed := runQuantifiedEqualityOrbitHashed_amortized_state_cost_bounds k phi
  change traced.cost.rehashHashes ≤ 3 * result.table.size ∧
    traced.cost.keyComparisons ≤
      (result.stats.requests + result.table.size) * result.table.size ∧
    traced.cost.totalHashes ≤ result.stats.requests + 4 * result.table.size at hclosed
  rcases hclosed with ⟨hrehash, hcompare, htotal⟩
  have hrequests := runQuantifiedEqualityOrbitHashed_requests_le_weighted phi
  change result.stats.requests ≤ weight at hrequests
  have hstates : result.table.size ≤ weight := by
    have hsize := runQuantifiedEqualityOrbitHashed_unique_states_eq_misses k phi
    change result.table.size = result.stats.misses at hsize
    have hmisses : result.stats.misses ≤ result.stats.requests := by
      simp [EqualityOrbitMemoStats.requests]
    omega
  have hcomparisonProduct :
      (result.stats.requests + result.table.size) * result.table.size ≤
        (weight + weight) * weight :=
    Nat.mul_le_mul (Nat.add_le_add hrequests hstates) hstates
  change traced.cost.rehashHashes ≤ 3 * weight ∧
    traced.cost.keyComparisons ≤ 2 * (weight * weight) ∧
    traced.cost.totalHashes ≤ 5 * weight
  constructor
  · exact hrehash.trans (Nat.mul_le_mul_left 3 hstates)
  constructor
  · calc
      traced.cost.keyComparisons ≤
          (result.stats.requests + result.table.size) * result.table.size := hcompare
      _ ≤ (weight + weight) * weight := hcomparisonProduct
      _ = 2 * (weight * weight) := by ring
  · calc
      traced.cost.totalHashes ≤
          result.stats.requests + 4 * result.table.size := htotal
      _ ≤ weight + 4 * weight :=
        Nat.add_le_add hrequests (Nat.mul_le_mul_left 4 hstates)
      _ = 5 * weight := by ring

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

/-- Concrete separation between measured work and the stronger amortized
bounds.  The pairs are respectively `(resize hashes, 3U)`,
`(key comparisons, (A+U)U)`, and `(total hashes, 5W)`. -/
theorem hashedCost_atLeastThree_amortized_bound_regression :
    let phi := atLeastThreeSentence
    let k := QFormula.quantifierRank phi
    let traced := runQuantifiedEqualityOrbitHashedCosted k phi
    let result := traced.result
    let weight := equalityOrbitWeightedRequestBound phi 0
    ((traced.cost.rehashHashes, 3 * result.table.size),
      (traced.cost.keyComparisons,
        (result.stats.requests + result.table.size) * result.table.size),
      (traced.cost.totalHashes, 5 * weight)) =
      ((38, 120), (34, 3280), (120, 220)) := by
  native_decide

/-- Concrete bucket-potential audit: resize hashes plus the sixteen starting
buckets, actual final buckets, and the proved `16 + 3U` capacity envelope. -/
theorem hashedCost_atLeastThree_bucket_potential_regression :
    let traced := runQuantifiedEqualityOrbitHashedCosted 3 atLeastThreeSentence
    (traced.cost.rehashHashes + 16,
      hashedMemoBucketCount traced.result.table,
      16 + 3 * traced.result.table.size) = (54, 64, 136) := by
  native_decide

end

end Nullivance.InfiniteFO
