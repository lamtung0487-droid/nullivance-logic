import Nullivance.QuantifiedEqualityHashCost

/-!
# Collision-sensitive bounds for the quantified-equality orbit engine

The peak is the largest physical chain observed immediately before an actual
lookup or insertion, including probes in all recursive binder branches.
No injectivity, distribution, or probabilistic assumption on the hash is used.
Operation counts treat a whole hash or key comparison as one unit; the work
inside hashes/comparisons, allocation, and array copying are not included.
-/

namespace Nullivance.InfiniteFO

open Nullivance.FiniteFO (Var QFormula)
open Nullivance.Semantics

noncomputable section

namespace HashCost

/-- A measurable comparison bound and a separate bound on its peak parameter.
The second conjunct makes the earlier state-only bound an immediate corollary. -/
def OperationCost.CollisionBound (cost : OperationCost)
    (requests misses finalSize : Nat) : Prop :=
  cost.comparisonEnvelope ≤ (requests + misses) * cost.peakBucketEntries ∧
    cost.peakBucketEntries ≤ finalSize

theorem OperationCost.CollisionBound.zero (finalSize : Nat) :
    ({} : OperationCost).CollisionBound 0 0 finalSize := by
  simp [OperationCost.CollisionBound]

theorem OperationCost.CollisionBound.mono_final
    {cost : OperationCost} {requests misses smaller larger : Nat}
    (hbound : cost.CollisionBound requests misses smaller)
    (hsize : smaller ≤ larger) :
    cost.CollisionBound requests misses larger :=
  ⟨hbound.1, hbound.2.trans hsize⟩

theorem OperationCost.CollisionBound.add
    {left right : OperationCost}
    {leftRequests leftMisses rightRequests rightMisses finalSize : Nat}
    (hleft : left.CollisionBound leftRequests leftMisses finalSize)
    (hright : right.CollisionBound rightRequests rightMisses finalSize) :
    (left.add right).CollisionBound
      (leftRequests + rightRequests) (leftMisses + rightMisses) finalSize := by
  rcases hleft with ⟨hl, hls⟩
  rcases hright with ⟨hr, hrs⟩
  constructor
  · change left.comparisonEnvelope + right.comparisonEnvelope ≤
      (leftRequests + rightRequests + (leftMisses + rightMisses)) *
        max left.peakBucketEntries right.peakBucketEntries
    calc
      _ ≤ (leftRequests + leftMisses) * left.peakBucketEntries +
          (rightRequests + rightMisses) * right.peakBucketEntries :=
        Nat.add_le_add hl hr
      _ ≤ (leftRequests + leftMisses) * max left.peakBucketEntries right.peakBucketEntries +
          (rightRequests + rightMisses) * max left.peakBucketEntries right.peakBucketEntries :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.le_max_left _ _))
          (Nat.mul_le_mul_left _ (Nat.le_max_right _ _))
      _ = _ := by ring
  · exact max_le hls hrs

theorem OperationCost.CollisionBound.withStats
    {cost : OperationCost} {requests misses finalSize : Nat}
    (hbound : cost.CollisionBound requests misses finalSize)
    (stats : EqualityOrbitMemoStats) :
    (cost.withStats stats).CollisionBound requests misses finalSize := hbound

theorem lookupCost_collision
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) {finalSize : Nat}
    (hsize : table.size ≤ finalSize) :
    (lookupCost table key).CollisionBound 1 0 finalSize := by
  constructor
  · simp [lookupCost]
  · exact (hashedMemoBucket_entryCount_le_size table key).trans hsize

theorem insertMissCost_collision
    (table : HashedEqualityOrbitMemoTable)
    (key : RecursiveEqualityOrbitMemoKey) (value : EqBoolFormula)
    {finalSize : Nat} (hsize : (table.insert key value).size ≤ finalSize) :
    (insertMissCost table key value).CollisionBound 0 1 finalSize := by
  constructor
  · simp [insertMissCost]
  · exact (hashedMemoBucket_entryCount_le_size table key).trans
      ((Std.HashMap.size_le_size_insert (m := table)).trans hsize)

/-- Hash calls plus whole-key comparisons only. -/
def OperationCost.hashComparisonWork (cost : OperationCost) : Nat :=
  cost.totalHashes + cost.keyComparisons

/-- Counted source operations: hash calls, whole-key comparisons, and the
primary bucket accesses already counted by the pinned cost model.
Allocation, resizing array scans, and work inside a key are excluded. -/
def OperationCost.countedWork (cost : OperationCost) : Nat :=
  cost.hashComparisonWork + cost.bucketAccesses

end HashCost

open HashCost

mutual
  theorem costedExpandQuantifiedEqualityOrbitsHashed_collision_bound
      (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
      (table : HashedEqualityOrbitMemoTable) :
      let traced := costedExpandQuantifiedEqualityOrbitsHashed
        phi used available env table
      traced.cost.CollisionBound traced.result.stats.requests
        traced.result.stats.misses traced.result.table.size := by
    rw [costedExpandQuantifiedEqualityOrbitsHashed.eq_def]
    dsimp only
    apply OperationCost.CollisionBound.withStats
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
        (lookupCost_collision table
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
          have hlookupCost := lookupCost_collision table
            (recursiveEqualityOrbitMemoKey (.pred P xs) used available env) htable
          have hinsert := insertMissCost_collision table
            (recursiveEqualityOrbitMemoKey (.pred P xs) used available env)
            EqBoolFormula.bot (le_refl _)
          simpa [EqualityOrbitMemoStats.requests, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] using
            hlookupCost.add ((OperationCost.CollisionBound.zero _).add hinsert)
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
          have hlookupCost := lookupCost_collision table
            (recursiveEqualityOrbitMemoKey (.eq x y) used available env) htable
          have hinsert := insertMissCost_collision table
            (recursiveEqualityOrbitMemoKey (.eq x y) used available env)
            value (le_refl _)
          simpa [EqualityOrbitMemoStats.requests, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] using
            hlookupCost.add ((OperationCost.CollisionBound.zero _).add hinsert)
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
          have hchild := costedExpandQuantifiedEqualityOrbitsHashed_collision_bound
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
          have hlookupCost := lookupCost_collision table
            (recursiveEqualityOrbitMemoKey (.neg body) used available env)
            (htableChild'.trans hchildInsert)
          have hinsert := insertMissCost_collision child.result.table
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
          have hleft := costedExpandQuantifiedEqualityOrbitsHashed_collision_bound
            left used available env table
          have hright := costedExpandQuantifiedEqualityOrbitsHashed_collision_bound
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
          have hlookupCost := lookupCost_collision table
            (recursiveEqualityOrbitMemoKey (.conj left right) used available env)
            (htableLeft'.trans (hleftRight'.trans hrightInsert))
          have hinsert := insertMissCost_collision rightResult.result.table
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
          have hleft := costedExpandQuantifiedEqualityOrbitsHashed_collision_bound
            left used available env table
          have hright := costedExpandQuantifiedEqualityOrbitsHashed_collision_bound
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
          have hlookupCost := lookupCost_collision table
            (recursiveEqualityOrbitMemoKey (.disj left right) used available env)
            (htableLeft'.trans (hleftRight'.trans hrightInsert))
          have hinsert := insertMissCost_collision rightResult.result.table
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
          have hlookupCost := lookupCost_collision table
            (recursiveEqualityOrbitMemoKey (.oplus left right) used available env) htable
          have hinsert := insertMissCost_collision table
            (recursiveEqualityOrbitMemoKey (.oplus left right) used available env)
            EqBoolFormula.bot (le_refl _)
          simpa [EqualityOrbitMemoStats.requests, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] using
            hlookupCost.add ((OperationCost.CollisionBound.zero _).add hinsert)
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
            costedExpandQuantifiedEqualityOrbitBranchesHashed_collision_bound
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
          have hlookupCost := lookupCost_collision table
            (recursiveEqualityOrbitMemoKey (.all x body) used available env)
            (htableBranches'.trans hbranchInsert)
          have hinsert := insertMissCost_collision branches.result.table
            (recursiveEqualityOrbitMemoKey (.all x body) used available env)
            value (le_refl _)
          cases available <;>
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
            costedExpandQuantifiedEqualityOrbitBranchesHashed_collision_bound
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
          have hlookupCost := lookupCost_collision table
            (recursiveEqualityOrbitMemoKey (.ex x body) used available env)
            (htableBranches'.trans hbranchInsert)
          have hinsert := insertMissCost_collision branches.result.table
            (recursiveEqualityOrbitMemoKey (.ex x body) used available env)
            value (le_refl _)
          cases available <;>
            simpa [oldQueries, freshQueries, branches, branchProduction, value,
            EqualityOrbitMemoStats.requests, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using hlookupCost.add (hbranchesLift.add hinsert)
  termination_by (sizeOf phi, 0)

  theorem costedExpandQuantifiedEqualityOrbitBranchesHashed_collision_bound
      (body : QFormula) (queries : List RecursiveEqualityOrbitBranchQuery)
      (table : HashedEqualityOrbitMemoTable) :
      let traced := costedExpandQuantifiedEqualityOrbitBranchesHashed
        body queries table
      traced.cost.CollisionBound traced.result.stats.requests
        traced.result.stats.misses traced.result.table.size := by
    cases queries with
    | nil =>
        rw [costedExpandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        simpa [EqualityOrbitMemoStats.requests] using
          (OperationCost.CollisionBound.zero table.size).withStats
            ({} : EqualityOrbitMemoStats)
    | cons query rest =>
        rw [costedExpandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        let headResult := costedExpandQuantifiedEqualityOrbitsHashed body
          query.used query.available query.env table
        let tailResult := costedExpandQuantifiedEqualityOrbitBranchesHashed
          body rest headResult.result.table
        have hhead := costedExpandQuantifiedEqualityOrbitsHashed_collision_bound body
          query.used query.available query.env table
        have htail := costedExpandQuantifiedEqualityOrbitBranchesHashed_collision_bound
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


/-- Closed root bound using the measured maximum probed chain length.
Both hash/comparison work and work including primary bucket accesses are
named explicitly, so the accounting does not silently drop an operation kind. -/
theorem runQuantifiedEqualityOrbitHashed_collision_bounds
    (k : Nat) (phi : QFormula) :
    let traced := runQuantifiedEqualityOrbitHashedCosted k phi
    let result := runQuantifiedEqualityOrbitHashed k phi
    let A := result.stats.requests
    let U := result.table.size
    let L := traced.cost.peakBucketEntries
    L ≤ U ∧
      traced.cost.keyComparisons ≤ (A + U) * L ∧
      traced.cost.hashComparisonWork ≤ A + 4 * U + (A + U) * L ∧
      traced.cost.countedWork ≤ 2 * A + 5 * U + (A + U) * L := by
  let traced := runQuantifiedEqualityOrbitHashedCosted k phi
  let result := runQuantifiedEqualityOrbitHashed k phi
  have hcollision := costedExpandQuantifiedEqualityOrbitsHashed_collision_bound
    phi [] (cutoffRepresentatives k) id emptyHashedEqualityOrbitMemoTable
  dsimp only at hcollision
  rw [costedExpandQuantifiedEqualityOrbitsHashed_result] at hcollision
  change traced.cost.CollisionBound result.stats.requests
    result.stats.misses result.table.size at hcollision
  have hsize := runQuantifiedEqualityOrbitHashed_unique_states_eq_misses k phi
  change result.table.size = result.stats.misses at hsize
  rw [← hsize] at hcollision
  have hvalid := costedExpandQuantifiedEqualityOrbitsHashed_cost_valid
    phi [] (cutoffRepresentatives k) id emptyHashedEqualityOrbitMemoTable
  change traced.cost.Valid at hvalid
  have hcmp : traced.cost.keyComparisons ≤
      (result.stats.requests + result.table.size) * traced.cost.peakBucketEntries :=
    hvalid.1.trans hcollision.1
  have ham := runQuantifiedEqualityOrbitHashed_amortized_state_cost_bounds k phi
  change traced.cost.rehashHashes ≤ 3 * result.table.size ∧
    traced.cost.keyComparisons ≤ (result.stats.requests + result.table.size) * result.table.size ∧
    traced.cost.totalHashes ≤ result.stats.requests + 4 * result.table.size at ham
  have hwork : traced.cost.hashComparisonWork ≤
      result.stats.requests + 4 * result.table.size +
        (result.stats.requests + result.table.size) * traced.cost.peakBucketEntries :=
    Nat.add_le_add ham.2.2 hcmp
  have hbuckets : traced.cost.bucketAccesses =
      result.stats.requests + result.table.size := by
    rw [hvalid.2.2.2, hsize]
    simp [traced, result, runQuantifiedEqualityOrbitHashedCosted,
      runQuantifiedEqualityOrbitHashed]
  refine ⟨hcollision.2, hcmp, hwork, ?_⟩
  change traced.cost.hashComparisonWork + traced.cost.bucketAccesses ≤ _
  rw [hbuckets]
  calc
    _ ≤ (result.stats.requests + 4 * result.table.size +
        (result.stats.requests + result.table.size) * traced.cost.peakBucketEntries) +
        (result.stats.requests + result.table.size) := Nat.add_le_add_right hwork _
    _ = _ := by ring

/-- A caller may supply any certified upper bound on the *observed bucket
peak*. Injectivity of the 64-bit hash alone does not imply this premise. -/
theorem runQuantifiedEqualityOrbitHashed_comparisons_of_peak_le
    (k : Nat) (phi : QFormula) (L : Nat)
    (hpeak : (runQuantifiedEqualityOrbitHashedCosted k phi).cost.peakBucketEntries ≤ L) :
    let traced := runQuantifiedEqualityOrbitHashedCosted k phi
    let result := runQuantifiedEqualityOrbitHashed k phi
    traced.cost.keyComparisons ≤ (result.stats.requests + result.table.size) * L := by
  exact (runQuantifiedEqualityOrbitHashed_collision_bounds k phi).2.1.trans
    (Nat.mul_le_mul_left _ hpeak)

theorem runQuantifiedEqualityOrbitHashed_comparisons_of_peak_le_one
    (k : Nat) (phi : QFormula)
    (hpeak : (runQuantifiedEqualityOrbitHashedCosted k phi).cost.peakBucketEntries ≤ 1) :
    let traced := runQuantifiedEqualityOrbitHashedCosted k phi
    let result := runQuantifiedEqualityOrbitHashed k phi
    traced.cost.keyComparisons ≤ result.stats.requests + result.table.size := by
  simpa using runQuantifiedEqualityOrbitHashed_comparisons_of_peak_le k phi 1 hpeak

/-- Depth-sensitive Bell weight bounds the request/state factors without
assuming a bound on the observed collision peak independent of the input. -/
theorem runQuantifiedEqualityOrbitHashed_weighted_collision_bounds (phi : QFormula) :
    let k := QFormula.quantifierRank phi
    let traced := runQuantifiedEqualityOrbitHashedCosted k phi
    let W := equalityOrbitWeightedRequestBound phi 0
    let L := traced.cost.peakBucketEntries
    L ≤ W ∧ traced.cost.keyComparisons ≤ 2 * W * L ∧
      traced.cost.countedWork ≤ 7 * W + 2 * W * L := by
  let k := QFormula.quantifierRank phi
  let traced := runQuantifiedEqualityOrbitHashedCosted k phi
  let result := runQuantifiedEqualityOrbitHashed k phi
  let W := equalityOrbitWeightedRequestBound phi 0
  let L := traced.cost.peakBucketEntries
  have hc := runQuantifiedEqualityOrbitHashed_collision_bounds k phi
  change L ≤ result.table.size ∧
    traced.cost.keyComparisons ≤ (result.stats.requests + result.table.size) * L ∧
    traced.cost.hashComparisonWork ≤
      result.stats.requests + 4 * result.table.size + (result.stats.requests + result.table.size) * L ∧
    traced.cost.countedWork ≤
      2 * result.stats.requests + 5 * result.table.size + (result.stats.requests + result.table.size) * L at hc
  have hdepth := runQuantifiedEqualityOrbitHashed_depth_sensitive_envelope phi
  change result.table.size ≤ result.stats.requests ∧ result.stats.requests ≤ W ∧ _ at hdepth
  have hu : result.table.size ≤ W := hdepth.1.trans hdepth.2.1
  have hm : (result.stats.requests + result.table.size) * L ≤ 2 * W * L := by
    apply Nat.mul_le_mul_right
    omega
  refine ⟨hc.1.trans hu, hc.2.1.trans hm, ?_⟩
  have hlinear : 2 * result.stats.requests + 5 * result.table.size ≤ 7 * W := by omega
  exact hc.2.2.2.trans (Nat.add_le_add hlinear hm)


/-- The chain-length envelope is sharp for a missing key: the scan must
visit every entry. This is structural and independent of a hash function. -/
theorem HashCost.probeAssocList_comparisons_eq_entries_of_missing
    {α β : Type} [BEq α] (query : α)
    (bucket : Std.DHashMap.Internal.AssocList α (fun _ => β))
    (hmissing : bucket.get? query = none) :
    (probeAssocList query bucket).comparisons = assocEntryCount bucket := by
  induction bucket with
  | nil => rfl
  | cons key value rest ih =>
      by_cases h : key == query
      · simp [Std.DHashMap.Internal.AssocList.get?, h] at hmissing
      · simp only [Std.DHashMap.Internal.AssocList.get?, h] at hmissing
        simp [probeAssocList, h, assocEntryCount, ih hmissing]

/-- Genuine bucket collision with *different* UInt64 hashes, disproving the
claim that injectivity of full hashes is sufficient for singleton chains. -/
theorem hashedCost_distinct_hashes_same_bucket_regression :
    let first := recursiveEqualityOrbitMemoKey (.eq 1 1) [] [] id
    let second := recursiveEqualityOrbitMemoKey (.eq 4 4) [] [] id
    let table := (emptyHashedEqualityOrbitMemoTable.insert first .bot).insert second .bot
    hash first ≠ hash second ∧ table.size = 2 ∧
      assocEntryCount (hashedMemoBucket table first) = 2 ∧
      (lookupCost table first).keyComparisons = 2 := by
  native_decide

/-- Each row is (requests, states, peak, comparisons), followed by
(comparison bound, counted work, counted-work bound). -/
theorem hashedCost_collision_rank_growth_regression :
    ([universalReflexivitySentence, atLeastTwoSentence, atLeastThreeSentence,
      repeatedUniversalReflexivitySentence].map fun phi =>
        let k := QFormula.quantifierRank phi
        let r := runQuantifiedEqualityOrbitHashedCosted k phi
        let A := r.result.stats.requests
        let U := r.result.table.size
        let L := r.cost.peakBucketEntries
        ((A, U, L, r.cost.keyComparisons),
          ((A + U) * L, r.cost.countedWork, 2 * A + 5 * U + (A + U) * L))) =
      [((2, 2, 0, 0), (0, 8, 14)), ((6, 6, 1, 1), (12, 25, 54)),
        ((42, 40, 2, 34), (164, 236, 448)), ((4, 3, 1, 1), (7, 15, 30))] := by
  native_decide

end

end Nullivance.InfiniteFO
