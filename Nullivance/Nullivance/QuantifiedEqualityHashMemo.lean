import Nullivance.QuantifiedEqualityComplexity
import Std.Data.HashMap

/-!
# Verified hash memoization for quantified equality orbits

The list memo table in `QuantifiedEqualityComplexity` is retained as a small
reference implementation.  This module runs the same recursive expansion over
`Std.HashMap`.  The key has lawful decidable equality and a structural hash;
hash collisions are therefore resolved by equality rather than trusted.

The formal cost result deliberately bounds *unique stored states*, not machine
time: from an empty table, `HashMap.size = misses`, and recursive requests are
bounded by a cache-free structural recurrence.  Thus the final table size has a
proved finite cutoff-dependent bound independently of observed cache hits.
-/

namespace Nullivance.InfiniteFO

open Nullivance.FiniteFO (Var QFormula)
open Nullivance.Semantics

noncomputable section

universe u

abbrev HashedEqualityOrbitMemoTable :=
  Std.HashMap RecursiveEqualityOrbitMemoKey EqBoolFormula

def emptyHashedEqualityOrbitMemoTable : HashedEqualityOrbitMemoTable :=
  Std.HashMap.emptyWithCapacity 8

structure HashedEqualityOrbitMemoResult where
  formula : EqBoolFormula
  table : HashedEqualityOrbitMemoTable
  stats : EqualityOrbitMemoStats

structure HashedEqualityOrbitBranchResult where
  formulas : List EqBoolFormula
  table : HashedEqualityOrbitMemoTable
  stats : EqualityOrbitMemoStats

mutual
  /-- Production hash-table version of recursive orbit expansion. -/
  def expandQuantifiedEqualityOrbitsHashed
      (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
      (table : HashedEqualityOrbitMemoTable) :
      HashedEqualityOrbitMemoResult :=
    let key := recursiveEqualityOrbitMemoKey phi used available env
    match table.get? key with
    | some cached =>
        ⟨cached, table, EqualityOrbitMemoStats.hit⟩
    | none =>
        let computed : HashedEqualityOrbitMemoResult := match phi with
          | .pred _ _ => ⟨.bot, table, {}⟩
          | .eq x y =>
              ⟨if env x = env y then .top
                else .atom (normalizeEqAtom (env x) (env y)), table, {}⟩
          | .neg body =>
              let child := expandQuantifiedEqualityOrbitsHashed
                body used available env table
              ⟨.neg child.formula, child.table, child.stats⟩
          | .conj left right =>
              let leftResult := expandQuantifiedEqualityOrbitsHashed
                left used available env table
              let rightResult := expandQuantifiedEqualityOrbitsHashed
                right used available env leftResult.table
              ⟨.conj leftResult.formula rightResult.formula,
                rightResult.table, leftResult.stats.add rightResult.stats⟩
          | .disj left right =>
              let leftResult := expandQuantifiedEqualityOrbitsHashed
                left used available env table
              let rightResult := expandQuantifiedEqualityOrbitsHashed
                right used available env leftResult.table
              ⟨.disj leftResult.formula rightResult.formula,
                rightResult.table, leftResult.stats.add rightResult.stats⟩
          | .oplus _ _ => ⟨.bot, table, {}⟩
          | .all x body =>
              let oldQueries := used.map fun representative =>
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
              ⟨EqBoolFormula.conjList branches.formulas,
                branches.table, branches.stats⟩
          | .ex x body =>
              let oldQueries := used.map fun representative =>
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
              ⟨EqBoolFormula.disjList branches.formulas,
                branches.table, branches.stats⟩
        ⟨computed.formula, computed.table.insert key computed.formula,
          computed.stats.add EqualityOrbitMemoStats.miss⟩
  termination_by (sizeOf phi, 0)

  /-- Branch siblings share the hash table sequentially. -/
  def expandQuantifiedEqualityOrbitBranchesHashed
      (body : QFormula) (queries : List RecursiveEqualityOrbitBranchQuery)
      (table : HashedEqualityOrbitMemoTable) :
      HashedEqualityOrbitBranchResult :=
    match queries with
    | [] => ⟨[], table, {}⟩
    | query :: rest =>
        let headResult := expandQuantifiedEqualityOrbitsHashed body
          query.used query.available query.env table
        let tailResult := expandQuantifiedEqualityOrbitBranchesHashed
          body rest headResult.table
        ⟨headResult.formula :: tailResult.formulas, tailResult.table,
          headResult.stats.add tailResult.stats⟩
  termination_by (sizeOf body, queries.length + 1)
end

def runQuantifiedEqualityOrbitHashed (k : Nat) (phi : QFormula) :
    HashedEqualityOrbitMemoResult :=
  expandQuantifiedEqualityOrbitsHashed phi [] (cutoffRepresentatives k) id
    emptyHashedEqualityOrbitMemoTable

def HashedEqualityOrbitMemoTable.Sound
    (table : HashedEqualityOrbitMemoTable) : Prop :=
  ∀ key value, table.get? key = some value →
    ∀ phi used available env,
      key = recursiveEqualityOrbitMemoKey phi used available env →
      value = expandQuantifiedEqualityOrbits used available env phi

/-- Extensional relation between the linear reference table and the hash map.
It compares lookup behavior, not bucket layout or insertion order. -/
def RecursiveEqualityOrbitMemoTablesEquivalent
    (reference : RecursiveEqualityOrbitMemoTable)
    (hashed : HashedEqualityOrbitMemoTable) : Prop :=
  ∀ key, recursiveEqualityOrbitMemoLookup key reference = hashed.get? key

theorem recursiveEqualityOrbitMemoTablesEquivalent_empty :
    RecursiveEqualityOrbitMemoTablesEquivalent []
      emptyHashedEqualityOrbitMemoTable := by
  intro key
  simp [recursiveEqualityOrbitMemoLookup, emptyHashedEqualityOrbitMemoTable]

/-- One logically identical insertion preserves extensional equivalence.
This is the representation-level simulation theorem used to justify replacing
linear lookup by hash lookup. -/
theorem RecursiveEqualityOrbitMemoTablesEquivalent.insert
    {reference : RecursiveEqualityOrbitMemoTable}
    {hashed : HashedEqualityOrbitMemoTable}
    (hequiv : RecursiveEqualityOrbitMemoTablesEquivalent reference hashed)
    (key : RecursiveEqualityOrbitMemoKey) (value : EqBoolFormula) :
    RecursiveEqualityOrbitMemoTablesEquivalent ((key, value) :: reference)
      (hashed.insert key value) := by
  intro query
  rw [Std.HashMap.get?_insert]
  by_cases hkey : key = query
  · simp [recursiveEqualityOrbitMemoLookup, hkey]
  · simp [recursiveEqualityOrbitMemoLookup, hkey, hequiv query]

theorem HashedEqualityOrbitMemoTable.Sound.insert_query
    {table : HashedEqualityOrbitMemoTable} (hsound : table.Sound)
    (phi : QFormula) (used available : List Var) (env : QuantifierEnv) :
    HashedEqualityOrbitMemoTable.Sound
      (table.insert (recursiveEqualityOrbitMemoKey phi used available env)
        (expandQuantifiedEqualityOrbits used available env phi)) := by
  intro key value hlookup psi otherUsed otherAvailable sigma hquery
  rw [Std.HashMap.get?_insert] at hlookup
  by_cases hkey : recursiveEqualityOrbitMemoKey phi used available env = key
  · simp [hkey] at hlookup
    subst value
    apply recursiveEqualityOrbitMemoKey_sound phi psi used otherUsed
      available otherAvailable env sigma
    exact hkey.trans hquery
  · simp [hkey] at hlookup
    exact hsound key value hlookup psi otherUsed otherAvailable sigma hquery

mutual
  /-- Exact output correctness and preservation of the hash-table collision
  invariant at every recursive call. -/
  theorem expandQuantifiedEqualityOrbitsHashed_correct
      (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
      (table : HashedEqualityOrbitMemoTable) (hsound : table.Sound) :
      let result := expandQuantifiedEqualityOrbitsHashed
        phi used available env table
      result.formula = expandQuantifiedEqualityOrbits used available env phi ∧
        result.table.Sound := by
    rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
    dsimp only
    split
    next cached hlookup =>
      exact ⟨hsound _ _ hlookup phi used available env rfl, hsound⟩
    next hlookup =>
      cases phi with
      | pred P xs =>
          simp only
          exact ⟨rfl, hsound.insert_query (.pred P xs) used available env⟩
      | eq x y =>
          simp only
          exact ⟨rfl, hsound.insert_query (.eq x y) used available env⟩
      | neg body =>
          simp only
          have hchild := expandQuantifiedEqualityOrbitsHashed_correct
            body used available env table hsound
          rcases hchild with ⟨hformula, htable⟩
          constructor
          · simp [expandQuantifiedEqualityOrbits, hformula]
          · simpa [hformula, expandQuantifiedEqualityOrbits] using
              htable.insert_query (.neg body) used available env
      | conj left right =>
          simp only
          have hleft := expandQuantifiedEqualityOrbitsHashed_correct
            left used available env table hsound
          rcases hleft with ⟨hleftFormula, hleftTable⟩
          have hright := expandQuantifiedEqualityOrbitsHashed_correct
            right used available env
              (expandQuantifiedEqualityOrbitsHashed left used available env table).table
              hleftTable
          rcases hright with ⟨hrightFormula, hrightTable⟩
          constructor
          · simp [expandQuantifiedEqualityOrbits, hleftFormula, hrightFormula]
          · simpa [hleftFormula, hrightFormula,
              expandQuantifiedEqualityOrbits] using
              hrightTable.insert_query (.conj left right) used available env
      | disj left right =>
          simp only
          have hleft := expandQuantifiedEqualityOrbitsHashed_correct
            left used available env table hsound
          rcases hleft with ⟨hleftFormula, hleftTable⟩
          have hright := expandQuantifiedEqualityOrbitsHashed_correct
            right used available env
              (expandQuantifiedEqualityOrbitsHashed left used available env table).table
              hleftTable
          rcases hright with ⟨hrightFormula, hrightTable⟩
          constructor
          · simp [expandQuantifiedEqualityOrbits, hleftFormula, hrightFormula]
          · simpa [hleftFormula, hrightFormula,
              expandQuantifiedEqualityOrbits] using
              hrightTable.insert_query (.disj left right) used available env
      | oplus left right =>
          simp only
          exact ⟨rfl, hsound.insert_query (.oplus left right) used available env⟩
      | all x body =>
          simp only
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
          have hbranches := expandQuantifiedEqualityOrbitBranchesHashed_correct
            body (oldQueries ++ freshQueries) table hsound
          rcases hbranches with ⟨hformulas, htable⟩
          clear hlookup
          have hbranchExact :
              (expandQuantifiedEqualityOrbitBranchesHashed body
                (oldQueries ++ freshQueries) table).formulas =
                (used.map fun representative =>
                  expandQuantifiedEqualityOrbits used available
                    (env.update x representative) body) ++
                match available with
                | [] => []
                | representative :: rest =>
                    [expandQuantifiedEqualityOrbits (used ++ [representative])
                      rest (env.update x representative) body] := by
            rw [hformulas]
            cases available <;> simp [oldQueries, freshQueries]
          constructor
          · exact congrArg EqBoolFormula.conjList hbranchExact
          · rw [hbranchExact]
            exact htable.insert_query (.all x body) used available env
      | ex x body =>
          simp only
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
          have hbranches := expandQuantifiedEqualityOrbitBranchesHashed_correct
            body (oldQueries ++ freshQueries) table hsound
          rcases hbranches with ⟨hformulas, htable⟩
          clear hlookup
          have hbranchExact :
              (expandQuantifiedEqualityOrbitBranchesHashed body
                (oldQueries ++ freshQueries) table).formulas =
                (used.map fun representative =>
                  expandQuantifiedEqualityOrbits used available
                    (env.update x representative) body) ++
                match available with
                | [] => []
                | representative :: rest =>
                    [expandQuantifiedEqualityOrbits (used ++ [representative])
                      rest (env.update x representative) body] := by
            rw [hformulas]
            cases available <;> simp [oldQueries, freshQueries]
          constructor
          · exact congrArg EqBoolFormula.disjList hbranchExact
          · rw [hbranchExact]
            exact htable.insert_query (.ex x body) used available env
  termination_by (sizeOf phi, 0)

  theorem expandQuantifiedEqualityOrbitBranchesHashed_correct
      (body : QFormula) (queries : List RecursiveEqualityOrbitBranchQuery)
      (table : HashedEqualityOrbitMemoTable) (hsound : table.Sound) :
      let result := expandQuantifiedEqualityOrbitBranchesHashed body queries table
      result.formulas = queries.map (fun query =>
          expandQuantifiedEqualityOrbits query.used query.available query.env body) ∧
        result.table.Sound := by
    cases queries with
    | nil =>
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        exact ⟨rfl, hsound⟩
    | cons query rest =>
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        have hhead := expandQuantifiedEqualityOrbitsHashed_correct body
          query.used query.available query.env table hsound
        rcases hhead with ⟨hheadFormula, hheadTable⟩
        have htail := expandQuantifiedEqualityOrbitBranchesHashed_correct body rest
          (expandQuantifiedEqualityOrbitsHashed body query.used query.available
            query.env table).table hheadTable
        rcases htail with ⟨htailFormulas, htailTable⟩
        exact ⟨by simp [hheadFormula, htailFormulas], htailTable⟩
  termination_by (sizeOf body, queries.length + 1)
end

theorem runQuantifiedEqualityOrbitHashed_correct (k : Nat) (phi : QFormula) :
    (runQuantifiedEqualityOrbitHashed k phi).formula =
      quantifiedEqualityOrbitBoolean k phi := by
  simpa [runQuantifiedEqualityOrbitHashed, quantifiedEqualityOrbitBoolean,
    emptyHashedEqualityOrbitMemoTable] using
    (expandQuantifiedEqualityOrbitsHashed_correct phi []
      (cutoffRepresentatives k) id emptyHashedEqualityOrbitMemoTable
      (by simp [HashedEqualityOrbitMemoTable.Sound,
        emptyHashedEqualityOrbitMemoTable])).1

/-- End-to-end observational equivalence with the list reference engine. -/
theorem runQuantifiedEqualityOrbitHashed_eq_list (k : Nat) (phi : QFormula) :
    (runQuantifiedEqualityOrbitHashed k phi).formula =
      (runQuantifiedEqualityOrbitMemoized k phi).formula := by
  rw [runQuantifiedEqualityOrbitHashed_correct,
    runQuantifiedEqualityOrbitMemoized_correct]

def quantifiedEqualityHashedROBDD (k : Nat) (phi : QFormula) : ROBDD :=
  ROBDD.compile (runQuantifiedEqualityOrbitHashed k phi).formula

theorem quantifiedEqualityHashedROBDD_eq_orbit (k : Nat) (phi : QFormula) :
    quantifiedEqualityHashedROBDD k phi = quantifiedEqualityOrbitROBDD k phi := by
  simp [quantifiedEqualityHashedROBDD, quantifiedEqualityOrbitROBDD,
    runQuantifiedEqualityOrbitHashed_correct, quantifiedEqualityOrbitBoolean]

def decideQuantifiedEqualityHashed (_D : Type u) (k : Nat)
    (phi : QFormula) : Bool :=
  (quantifiedEqualityHashedROBDD k phi).eval (capacityEqualityValuation k)

theorem decideQuantifiedEqualityHashed_eq_orbits (D : Type u)
    (k : Nat) (phi : QFormula) :
    decideQuantifiedEqualityHashed D k phi =
      decideQuantifiedEqualityOrbits D k phi := by
  rw [decideQuantifiedEqualityHashed, decideQuantifiedEqualityOrbits,
    quantifiedEqualityHashedROBDD_eq_orbit]

theorem decideQuantifiedEqualityHashed_infinite_correct {D : Type u}
    [Infinite D] [Nonempty D] (M : QModel D) (rho : Assignment D)
    (phi : QFormula)
    (hfragment : QFormula.QuantifiedEqualityFragment phi)
    (hclosed : QFormula.freeVars phi = ∅) :
    qeval M rho phi =
      if decideQuantifiedEqualityHashed D (QFormula.quantifierRank phi) phi
        then V4.T else V4.F := by
  rw [decideQuantifiedEqualityHashed_eq_orbits]
  exact decideQuantifiedEqualityOrbits_infinite_correct M rho phi hfragment hclosed

/-! ## Quantitative unique-state cutoff -/

/-- Total recursive calls actually executed by a memoized run.  Every call is
classified exactly once as either a cache hit or a cache miss. -/
def EqualityOrbitMemoStats.requests (stats : EqualityOrbitMemoStats) : Nat :=
  stats.hits + stats.misses

mutual
  /-- Cache-free number of recursive formula requests generated by the same
  orbit traversal.  A cache hit can only prune this request tree. -/
  def equalityOrbitRequestBound (phi : QFormula) (used available : List Var)
      (env : QuantifierEnv) : Nat :=
    1 + match phi with
      | .pred _ _ | .eq _ _ | .oplus _ _ => 0
      | .neg body => equalityOrbitRequestBound body used available env
      | .conj left right | .disj left right =>
          equalityOrbitRequestBound left used available env +
            equalityOrbitRequestBound right used available env
      | .all x body | .ex x body =>
          let oldQueries := used.map fun representative =>
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
          equalityOrbitBranchRequestBound body (oldQueries ++ freshQueries)
  termination_by (sizeOf phi, 0)

  def equalityOrbitBranchRequestBound (body : QFormula)
      (queries : List RecursiveEqualityOrbitBranchQuery) : Nat :=
    match queries with
    | [] => 0
    | query :: rest =>
        equalityOrbitRequestBound body query.used query.available query.env +
          equalityOrbitBranchRequestBound body rest
  termination_by (sizeOf body, queries.length + 1)
end

theorem equalityOrbitRequestBound_pos (phi : QFormula) (used available : List Var)
    (env : QuantifierEnv) : 0 < equalityOrbitRequestBound phi used available env := by
  rw [equalityOrbitRequestBound.eq_def]
  omega

namespace QFormula

/-- Number of syntax-tree nodes, counting every connective and binder once. -/
def syntaxNodeCount : QFormula → Nat
  | .pred _ _ | .eq _ _ => 1
  | .neg body => 1 + syntaxNodeCount body
  | .conj left right | .disj left right | .oplus left right =>
      1 + syntaxNodeCount left + syntaxNodeCount right
  | .all _ body | .ex _ body => 1 + syntaxNodeCount body

theorem syntaxNodeCount_pos (phi : QFormula) : 0 < syntaxNodeCount phi := by
  cases phi <;> simp [syntaxNodeCount]

end QFormula

/-- Depth-sensitive cache-free request weight.  The parameter `used` is the
number of equality classes already represented at the current binder depth.
Unlike the coarse `syntaxNodeCount * equalityOrbitLeafCount` envelope, this
recurrence charges each syntactic occurrence only for the orbit multiplicity
that can actually reach it.  `oplus` has weight one because the pure-equality
translator rejects it without traversing its children. -/
def equalityOrbitWeightedRequestBound : QFormula → Nat → Nat
  | .pred _ _, _ | .eq _ _, _ | .oplus _ _, _ => 1
  | .neg body, used => 1 + equalityOrbitWeightedRequestBound body used
  | .conj left right, used | .disj left right, used =>
      1 + equalityOrbitWeightedRequestBound left used +
        equalityOrbitWeightedRequestBound right used
  | .all _ body, used | .ex _ body, used =>
      1 + used * equalityOrbitWeightedRequestBound body used +
        equalityOrbitWeightedRequestBound body (used + 1)

theorem equalityOrbitWeightedRequestBound_pos (phi : QFormula) (used : Nat) :
    0 < equalityOrbitWeightedRequestBound phi used := by
  cases phi <;> simp [equalityOrbitWeightedRequestBound]

theorem equalityOrbitLeafCount_le_succ_remaining (remaining used : Nat) :
    equalityOrbitLeafCount remaining used ≤
      equalityOrbitLeafCount (remaining + 1) used := by
  have hmono := equalityOrbitLeafCount_mono_used remaining
    (Nat.le_add_right used 1)
  rw [equalityOrbitLeafCount_succ]
  omega

theorem equalityOrbitLeafCount_mono_remaining (used : Nat) :
    Monotone fun remaining => equalityOrbitLeafCount remaining used := by
  intro a b hab
  exact Nat.le_induction (by rfl)
    (fun n _ ih => ih.trans (equalityOrbitLeafCount_le_succ_remaining n used))
    b hab

@[simp] theorem equalityOrbitBranchRequestBound_nil (body : QFormula) :
    equalityOrbitBranchRequestBound body [] = 0 := by
  rw [equalityOrbitBranchRequestBound.eq_def]

@[simp] theorem equalityOrbitBranchRequestBound_cons (body : QFormula)
    (query : RecursiveEqualityOrbitBranchQuery)
    (rest : List RecursiveEqualityOrbitBranchQuery) :
    equalityOrbitBranchRequestBound body (query :: rest) =
      equalityOrbitRequestBound body query.used query.available query.env +
        equalityOrbitBranchRequestBound body rest := by
  rw [equalityOrbitBranchRequestBound.eq_def]

theorem equalityOrbitBranchRequestBound_append (body : QFormula)
    (left right : List RecursiveEqualityOrbitBranchQuery) :
    equalityOrbitBranchRequestBound body (left ++ right) =
      equalityOrbitBranchRequestBound body left +
        equalityOrbitBranchRequestBound body right := by
  induction left with
  | nil => simp
  | cons query rest ih =>
      simp [ih, Nat.add_assoc]

theorem equalityOrbitBranchRequestBound_map_le
    {α : Type} (body : QFormula) (xs : List α)
    (query : α → RecursiveEqualityOrbitBranchQuery) (bound : Nat)
    (hbound : ∀ x ∈ xs,
      equalityOrbitRequestBound body (query x).used (query x).available
        (query x).env ≤ bound) :
    equalityOrbitBranchRequestBound body (xs.map query) ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      have hhead := hbound x (by simp)
      have htail := ih (fun y hy => hbound y (by simp [hy]))
      calc
        equalityOrbitBranchRequestBound body ((x :: rest).map query) =
            equalityOrbitRequestBound body (query x).used (query x).available
              (query x).env + equalityOrbitBranchRequestBound body (rest.map query) := by
                simp
        _ ≤ bound + rest.length * bound := Nat.add_le_add hhead htail
        _ = (rest.length + 1) * bound := by ring

theorem equalityOrbitBranchRequestBound_map_eq
    {α : Type} (body : QFormula) (xs : List α)
    (query : α → RecursiveEqualityOrbitBranchQuery) (bound : Nat)
    (hbound : ∀ x ∈ xs,
      equalityOrbitRequestBound body (query x).used (query x).available
        (query x).env = bound) :
    equalityOrbitBranchRequestBound body (xs.map query) = xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      have hhead := hbound x (by simp)
      have htail := ih (fun y hy => hbound y (by simp [hy]))
      simp [hhead, htail]
      ring

/-- Exact identification of the executable cache-free traversal with the
depth-sensitive structural weight.  The capacity premise is load-bearing: it
ensures that every binder can take one genuinely fresh representative, so the
quantifier recurrence has exactly `used` old-class branches and one fresh
branch. -/
theorem equalityOrbitRequestBound_eq_weighted :
    ∀ (phi : QFormula) (used available : List Var) (env : QuantifierEnv),
      QFormula.quantifierRank phi ≤ available.length →
      equalityOrbitRequestBound phi used available env =
        equalityOrbitWeightedRequestBound phi used.length := by
  intro phi
  induction phi with
  | pred P xs =>
      intro used available env hcapacity
      rw [equalityOrbitRequestBound.eq_def]
      simp [equalityOrbitWeightedRequestBound]
  | eq x y =>
      intro used available env hcapacity
      rw [equalityOrbitRequestBound.eq_def]
      simp [equalityOrbitWeightedRequestBound]
  | neg body ih =>
      intro used available env hcapacity
      rw [equalityOrbitRequestBound.eq_def]
      simp only
      rw [ih used available env hcapacity]
      rfl
  | conj left right ihLeft ihRight =>
      intro used available env hcapacity
      have hleftRank : QFormula.quantifierRank left ≤ available.length :=
        le_trans (Nat.le_max_left _ _) hcapacity
      have hrightRank : QFormula.quantifierRank right ≤ available.length :=
        le_trans (Nat.le_max_right _ _) hcapacity
      rw [equalityOrbitRequestBound.eq_def]
      simp only
      rw [ihLeft used available env hleftRank,
        ihRight used available env hrightRank]
      simp [equalityOrbitWeightedRequestBound, Nat.add_assoc]
  | disj left right ihLeft ihRight =>
      intro used available env hcapacity
      have hleftRank : QFormula.quantifierRank left ≤ available.length :=
        le_trans (Nat.le_max_left _ _) hcapacity
      have hrightRank : QFormula.quantifierRank right ≤ available.length :=
        le_trans (Nat.le_max_right _ _) hcapacity
      rw [equalityOrbitRequestBound.eq_def]
      simp only
      rw [ihLeft used available env hleftRank,
        ihRight used available env hrightRank]
      simp [equalityOrbitWeightedRequestBound, Nat.add_assoc]
  | oplus left right ihLeft ihRight =>
      intro used available env hcapacity
      rw [equalityOrbitRequestBound.eq_def]
      rfl
  | all x body ih =>
      intro used available env hcapacity
      cases available with
      | nil =>
          simp [QFormula.quantifierRank] at hcapacity
      | cons fresh rest =>
          have hbodyOld : QFormula.quantifierRank body ≤ (fresh :: rest).length := by
            simp [QFormula.quantifierRank] at hcapacity ⊢
            omega
          have hbodyFresh : QFormula.quantifierRank body ≤ rest.length := by
            simp [QFormula.quantifierRank] at hcapacity
            omega
          let oldQuery : Var → RecursiveEqualityOrbitBranchQuery :=
            fun representative =>
              { used := used, available := fresh :: rest,
                env := env.update x representative }
          let freshQuery : RecursiveEqualityOrbitBranchQuery :=
            { used := used ++ [fresh], available := rest,
              env := env.update x fresh }
          have hold := equalityOrbitBranchRequestBound_map_eq body used oldQuery
            (equalityOrbitWeightedRequestBound body used.length) (by
              intro representative hrepresentative
              simpa [oldQuery] using
                ih used (fresh :: rest) (env.update x representative) hbodyOld)
          have hfresh := ih (used ++ [fresh]) rest (env.update x fresh) hbodyFresh
          rw [equalityOrbitRequestBound.eq_def]
          dsimp only
          change 1 + equalityOrbitBranchRequestBound body
              (used.map oldQuery ++ [freshQuery]) =
            equalityOrbitWeightedRequestBound (.all x body) used.length
          rw [equalityOrbitBranchRequestBound_append, hold]
          simp only [equalityOrbitBranchRequestBound_cons,
            equalityOrbitBranchRequestBound_nil, Nat.add_zero]
          rw [hfresh]
          simp [equalityOrbitWeightedRequestBound, Nat.add_assoc]
  | ex x body ih =>
      intro used available env hcapacity
      cases available with
      | nil =>
          simp [QFormula.quantifierRank] at hcapacity
      | cons fresh rest =>
          have hbodyOld : QFormula.quantifierRank body ≤ (fresh :: rest).length := by
            simp [QFormula.quantifierRank] at hcapacity ⊢
            omega
          have hbodyFresh : QFormula.quantifierRank body ≤ rest.length := by
            simp [QFormula.quantifierRank] at hcapacity
            omega
          let oldQuery : Var → RecursiveEqualityOrbitBranchQuery :=
            fun representative =>
              { used := used, available := fresh :: rest,
                env := env.update x representative }
          let freshQuery : RecursiveEqualityOrbitBranchQuery :=
            { used := used ++ [fresh], available := rest,
              env := env.update x fresh }
          have hold := equalityOrbitBranchRequestBound_map_eq body used oldQuery
            (equalityOrbitWeightedRequestBound body used.length) (by
              intro representative hrepresentative
              simpa [oldQuery] using
                ih used (fresh :: rest) (env.update x representative) hbodyOld)
          have hfresh := ih (used ++ [fresh]) rest (env.update x fresh) hbodyFresh
          rw [equalityOrbitRequestBound.eq_def]
          dsimp only
          change 1 + equalityOrbitBranchRequestBound body
              (used.map oldQuery ++ [freshQuery]) =
            equalityOrbitWeightedRequestBound (.ex x body) used.length
          rw [equalityOrbitBranchRequestBound_append, hold]
          simp only [equalityOrbitBranchRequestBound_cons,
            equalityOrbitBranchRequestBound_nil, Nat.add_zero]
          rw [hfresh]
          simp [equalityOrbitWeightedRequestBound, Nat.add_assoc]

/-- Bell/Touchard state bound for arbitrary syntax.  If enough fresh names
remain for the formula's quantifier rank, the cache-free request tree is at
most syntax size times the equality-partition leaf count at the current number
of used classes. -/
theorem equalityOrbitRequestBound_le_syntax_mul_leafCount :
    ∀ (phi : QFormula) (used available : List Var) (env : QuantifierEnv),
      QFormula.quantifierRank phi ≤ available.length →
      equalityOrbitRequestBound phi used available env ≤
        QFormula.syntaxNodeCount phi *
          equalityOrbitLeafCount (QFormula.quantifierRank phi) used.length := by
  intro phi
  induction phi with
  | pred P xs =>
      intro used available env hcapacity
      rw [equalityOrbitRequestBound.eq_def]
      simp [QFormula.syntaxNodeCount, QFormula.quantifierRank]
  | eq x y =>
      intro used available env hcapacity
      rw [equalityOrbitRequestBound.eq_def]
      simp [QFormula.syntaxNodeCount, QFormula.quantifierRank]
  | neg body ih =>
      intro used available env hcapacity
      have hbody := ih used available env hcapacity
      have hpositive := equalityOrbitLeafCount_pos
        (QFormula.quantifierRank body) used.length
      rw [equalityOrbitRequestBound.eq_def]
      dsimp only
      simp only [QFormula.syntaxNodeCount, QFormula.quantifierRank]
      nlinarith
  | conj left right ihLeft ihRight =>
      intro used available env hcapacity
      have hleftRank : QFormula.quantifierRank left ≤ available.length :=
        le_trans (Nat.le_max_left _ _) hcapacity
      have hrightRank : QFormula.quantifierRank right ≤ available.length :=
        le_trans (Nat.le_max_right _ _) hcapacity
      have hleft := ihLeft used available env hleftRank
      have hright := ihRight used available env hrightRank
      have hleftMono := equalityOrbitLeafCount_mono_remaining used.length
        (Nat.le_max_left (QFormula.quantifierRank left)
          (QFormula.quantifierRank right))
      have hrightMono := equalityOrbitLeafCount_mono_remaining used.length
        (Nat.le_max_right (QFormula.quantifierRank left)
          (QFormula.quantifierRank right))
      have hleft' := hleft.trans (Nat.mul_le_mul_left
        (QFormula.syntaxNodeCount left) hleftMono)
      have hright' := hright.trans (Nat.mul_le_mul_left
        (QFormula.syntaxNodeCount right) hrightMono)
      have hpositive := equalityOrbitLeafCount_pos
        (max (QFormula.quantifierRank left) (QFormula.quantifierRank right))
        used.length
      rw [equalityOrbitRequestBound.eq_def]
      dsimp only
      simp only [QFormula.syntaxNodeCount, QFormula.quantifierRank]
      nlinarith
  | disj left right ihLeft ihRight =>
      intro used available env hcapacity
      have hleftRank : QFormula.quantifierRank left ≤ available.length :=
        le_trans (Nat.le_max_left _ _) hcapacity
      have hrightRank : QFormula.quantifierRank right ≤ available.length :=
        le_trans (Nat.le_max_right _ _) hcapacity
      have hleft := ihLeft used available env hleftRank
      have hright := ihRight used available env hrightRank
      have hleftMono := equalityOrbitLeafCount_mono_remaining used.length
        (Nat.le_max_left (QFormula.quantifierRank left)
          (QFormula.quantifierRank right))
      have hrightMono := equalityOrbitLeafCount_mono_remaining used.length
        (Nat.le_max_right (QFormula.quantifierRank left)
          (QFormula.quantifierRank right))
      have hleft' := hleft.trans (Nat.mul_le_mul_left
        (QFormula.syntaxNodeCount left) hleftMono)
      have hright' := hright.trans (Nat.mul_le_mul_left
        (QFormula.syntaxNodeCount right) hrightMono)
      have hpositive := equalityOrbitLeafCount_pos
        (max (QFormula.quantifierRank left) (QFormula.quantifierRank right))
        used.length
      rw [equalityOrbitRequestBound.eq_def]
      dsimp only
      simp only [QFormula.syntaxNodeCount, QFormula.quantifierRank]
      nlinarith
  | oplus left right ihLeft ihRight =>
      intro used available env hcapacity
      have hpositive := equalityOrbitLeafCount_pos
        (max (QFormula.quantifierRank left) (QFormula.quantifierRank right))
        used.length
      have hnodesLeft := QFormula.syntaxNodeCount_pos left
      have hnodesRight := QFormula.syntaxNodeCount_pos right
      rw [equalityOrbitRequestBound.eq_def]
      dsimp only
      simp only [QFormula.syntaxNodeCount, QFormula.quantifierRank]
      nlinarith
  | all x body ih =>
      intro used available env hcapacity
      cases available with
      | nil =>
          simp [QFormula.quantifierRank] at hcapacity
      | cons fresh rest =>
          have hbodyOld : QFormula.quantifierRank body ≤ (fresh :: rest).length := by
            simp [QFormula.quantifierRank] at hcapacity ⊢
            omega
          have hbodyFresh : QFormula.quantifierRank body ≤ rest.length := by
            simp [QFormula.quantifierRank] at hcapacity
            omega
          let oldQuery : Var → RecursiveEqualityOrbitBranchQuery :=
            fun representative =>
              { used := used, available := fresh :: rest,
                env := env.update x representative }
          let freshQuery : RecursiveEqualityOrbitBranchQuery :=
            { used := used ++ [fresh], available := rest,
              env := env.update x fresh }
          let bodyBound := QFormula.syntaxNodeCount body *
            equalityOrbitLeafCount (QFormula.quantifierRank body) used.length
          have hold := equalityOrbitBranchRequestBound_map_le body used oldQuery
            bodyBound (by
              intro representative hrepresentative
              exact ih used (fresh :: rest) (env.update x representative)
                hbodyOld)
          have hfresh := ih (used ++ [fresh]) rest (env.update x fresh) hbodyFresh
          rw [equalityOrbitRequestBound.eq_def]
          dsimp only
          change 1 + equalityOrbitBranchRequestBound body
              (used.map oldQuery ++ [freshQuery]) ≤
            (1 + QFormula.syntaxNodeCount body) *
              equalityOrbitLeafCount (QFormula.quantifierRank body + 1) used.length
          rw [equalityOrbitBranchRequestBound_append]
          simp only [equalityOrbitBranchRequestBound_cons,
            equalityOrbitBranchRequestBound_nil, Nat.add_zero]
          simp [oldQuery, bodyBound] at hold hfresh
          rw [equalityOrbitLeafCount_succ]
          have hpositive := equalityOrbitLeafCount_pos
            (QFormula.quantifierRank body + 1) used.length
          rw [equalityOrbitLeafCount_succ] at hpositive
          calc
            1 + (equalityOrbitBranchRequestBound body (used.map oldQuery) +
                equalityOrbitRequestBound body freshQuery.used
                  freshQuery.available freshQuery.env) ≤
                1 + (used.length *
                    (QFormula.syntaxNodeCount body *
                      equalityOrbitLeafCount (QFormula.quantifierRank body)
                        used.length) +
                  QFormula.syntaxNodeCount body *
                    equalityOrbitLeafCount (QFormula.quantifierRank body)
                      (used.length + 1)) :=
              Nat.add_le_add_left (Nat.add_le_add hold hfresh) 1
            _ = 1 + QFormula.syntaxNodeCount body *
                (used.length *
                    equalityOrbitLeafCount (QFormula.quantifierRank body)
                      used.length +
                  equalityOrbitLeafCount (QFormula.quantifierRank body)
                    (used.length + 1)) := by ring
            _ ≤ (1 + QFormula.syntaxNodeCount body) *
                (used.length *
                    equalityOrbitLeafCount (QFormula.quantifierRank body)
                      used.length +
                  equalityOrbitLeafCount (QFormula.quantifierRank body)
                    (used.length + 1)) := by nlinarith
  | ex x body ih =>
      intro used available env hcapacity
      cases available with
      | nil =>
          simp [QFormula.quantifierRank] at hcapacity
      | cons fresh rest =>
          have hbodyOld : QFormula.quantifierRank body ≤ (fresh :: rest).length := by
            simp [QFormula.quantifierRank] at hcapacity ⊢
            omega
          have hbodyFresh : QFormula.quantifierRank body ≤ rest.length := by
            simp [QFormula.quantifierRank] at hcapacity
            omega
          let oldQuery : Var → RecursiveEqualityOrbitBranchQuery :=
            fun representative =>
              { used := used, available := fresh :: rest,
                env := env.update x representative }
          let freshQuery : RecursiveEqualityOrbitBranchQuery :=
            { used := used ++ [fresh], available := rest,
              env := env.update x fresh }
          let bodyBound := QFormula.syntaxNodeCount body *
            equalityOrbitLeafCount (QFormula.quantifierRank body) used.length
          have hold := equalityOrbitBranchRequestBound_map_le body used oldQuery
            bodyBound (by
              intro representative hrepresentative
              exact ih used (fresh :: rest) (env.update x representative)
                hbodyOld)
          have hfresh := ih (used ++ [fresh]) rest (env.update x fresh) hbodyFresh
          rw [equalityOrbitRequestBound.eq_def]
          dsimp only
          change 1 + equalityOrbitBranchRequestBound body
              (used.map oldQuery ++ [freshQuery]) ≤
            (1 + QFormula.syntaxNodeCount body) *
              equalityOrbitLeafCount (QFormula.quantifierRank body + 1) used.length
          rw [equalityOrbitBranchRequestBound_append]
          simp only [equalityOrbitBranchRequestBound_cons,
            equalityOrbitBranchRequestBound_nil, Nat.add_zero]
          simp [oldQuery, bodyBound] at hold hfresh
          rw [equalityOrbitLeafCount_succ]
          have hpositive := equalityOrbitLeafCount_pos
            (QFormula.quantifierRank body + 1) used.length
          rw [equalityOrbitLeafCount_succ] at hpositive
          calc
            1 + (equalityOrbitBranchRequestBound body (used.map oldQuery) +
                equalityOrbitRequestBound body freshQuery.used
                  freshQuery.available freshQuery.env) ≤
                1 + (used.length *
                    (QFormula.syntaxNodeCount body *
                      equalityOrbitLeafCount (QFormula.quantifierRank body)
                        used.length) +
                  QFormula.syntaxNodeCount body *
                    equalityOrbitLeafCount (QFormula.quantifierRank body)
                      (used.length + 1)) :=
              Nat.add_le_add_left (Nat.add_le_add hold hfresh) 1
            _ = 1 + QFormula.syntaxNodeCount body *
                (used.length *
                    equalityOrbitLeafCount (QFormula.quantifierRank body)
                      used.length +
                  equalityOrbitLeafCount (QFormula.quantifierRank body)
                    (used.length + 1)) := by ring
            _ ≤ (1 + QFormula.syntaxNodeCount body) *
                (used.length *
                    equalityOrbitLeafCount (QFormula.quantifierRank body)
                      used.length +
                  equalityOrbitLeafCount (QFormula.quantifierRank body)
                    (used.length + 1)) := by nlinarith

/-- The depth-sensitive bound is never larger than the earlier global
syntax-times-Bell envelope.  This comparison is derived from the exact
cache-free identification, so it does not assume an asymptotic estimate for
Bell numbers. -/
theorem equalityOrbitWeightedRequestBound_le_syntax_mul_leafCount
    (phi : QFormula) (used : Nat) :
    equalityOrbitWeightedRequestBound phi used ≤
      QFormula.syntaxNodeCount phi *
        equalityOrbitLeafCount (QFormula.quantifierRank phi) used := by
  let usedVars : List Var := List.range used
  let available : List Var := List.range (QFormula.quantifierRank phi)
  have hcapacity : QFormula.quantifierRank phi ≤ available.length := by
    simp [available]
  have hexact := equalityOrbitRequestBound_eq_weighted phi usedVars available id
    hcapacity
  have hcoarse := equalityOrbitRequestBound_le_syntax_mul_leafCount phi
    usedVars available id hcapacity
  rw [hexact] at hcoarse
  simpa [usedVars] using hcoarse

mutual
  /-- Actual requests (`hits + misses`) never exceed the cache-free request
  tree.  This theorem is independent of hash distribution. -/
  theorem expandQuantifiedEqualityOrbitsHashed_requests_le
      (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
      (table : HashedEqualityOrbitMemoTable) :
      let result := expandQuantifiedEqualityOrbitsHashed
        phi used available env table
      result.stats.hits + result.stats.misses ≤
        equalityOrbitRequestBound phi used available env := by
    rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
    dsimp only
    split
    next cached hlookup =>
      have hpos := equalityOrbitRequestBound_pos phi used available env
      simp [EqualityOrbitMemoStats.hit]
      omega
    next hlookup =>
      cases phi with
      | pred P xs =>
          simp [equalityOrbitRequestBound, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss]
      | eq x y =>
          simp [equalityOrbitRequestBound, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss]
      | neg body =>
          simp only
          have hchild := expandQuantifiedEqualityOrbitsHashed_requests_le
            body used available env table
          simp [equalityOrbitRequestBound, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] at *
          omega
      | conj left right =>
          simp only
          have hleft := expandQuantifiedEqualityOrbitsHashed_requests_le
            left used available env table
          have hright := expandQuantifiedEqualityOrbitsHashed_requests_le
            right used available env
              (expandQuantifiedEqualityOrbitsHashed left used available env table).table
          simp [equalityOrbitRequestBound, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] at *
          omega
      | disj left right =>
          simp only
          have hleft := expandQuantifiedEqualityOrbitsHashed_requests_le
            left used available env table
          have hright := expandQuantifiedEqualityOrbitsHashed_requests_le
            right used available env
              (expandQuantifiedEqualityOrbitsHashed left used available env table).table
          simp [equalityOrbitRequestBound, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] at *
          omega
      | oplus left right =>
          simp [equalityOrbitRequestBound, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss]
      | all x body =>
          simp only
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
            expandQuantifiedEqualityOrbitBranchesHashed_requests_le
              body (oldQueries ++ freshQueries) table
          rw [equalityOrbitRequestBound.eq_def]
          dsimp only
          simp [oldQueries, freshQueries, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] at *
          omega
      | ex x body =>
          simp only
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
            expandQuantifiedEqualityOrbitBranchesHashed_requests_le
              body (oldQueries ++ freshQueries) table
          rw [equalityOrbitRequestBound.eq_def]
          dsimp only
          simp [oldQueries, freshQueries, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] at *
          omega
  termination_by (sizeOf phi, 0)

  theorem expandQuantifiedEqualityOrbitBranchesHashed_requests_le
      (body : QFormula) (queries : List RecursiveEqualityOrbitBranchQuery)
      (table : HashedEqualityOrbitMemoTable) :
      let result := expandQuantifiedEqualityOrbitBranchesHashed body queries table
      result.stats.hits + result.stats.misses ≤
        equalityOrbitBranchRequestBound body queries := by
    cases queries with
    | nil =>
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def,
          equalityOrbitBranchRequestBound.eq_def]
        simp
    | cons query rest =>
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def,
          equalityOrbitBranchRequestBound.eq_def]
        have hhead := expandQuantifiedEqualityOrbitsHashed_requests_le body
          query.used query.available query.env table
        have htail := expandQuantifiedEqualityOrbitBranchesHashed_requests_le body rest
          (expandQuantifiedEqualityOrbitsHashed body query.used query.available
            query.env table).table
        simp [EqualityOrbitMemoStats.add] at *
        omega
  termination_by (sizeOf body, queries.length + 1)
end

/-! ## Exact accounting of distinct states -/

mutual
  /-- Every key newly created by a formula call belongs to that formula or one
  of its descendants; the structural size of its residual formula is bounded
  by the caller's size. -/
  theorem expandQuantifiedEqualityOrbitsHashed_new_key_size_le
      (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
      (table : HashedEqualityOrbitMemoTable)
      (key : RecursiveEqualityOrbitMemoKey)
      (hmem : key ∈ (expandQuantifiedEqualityOrbitsHashed
        phi used available env table).table)
      (hnew : key ∉ table) :
      sizeOf key.formula ≤ sizeOf phi := by
    rw [expandQuantifiedEqualityOrbitsHashed.eq_def] at hmem
    dsimp only at hmem
    split at hmem
    next cached hlookup =>
      exact False.elim (hnew hmem)
    next hlookup =>
      cases phi with
      | pred P xs =>
          simp only at hmem
          rw [Std.HashMap.mem_insert] at hmem
          rcases hmem with hkey | htail
          · have hk := eq_of_beq hkey
            subst key
            simp [recursiveEqualityOrbitMemoKey]
          · exact False.elim (hnew htail)
      | eq x y =>
          simp only at hmem
          rw [Std.HashMap.mem_insert] at hmem
          rcases hmem with hkey | htail
          · have hk := eq_of_beq hkey
            subst key
            simp [recursiveEqualityOrbitMemoKey]
          · exact False.elim (hnew htail)
      | neg body =>
          simp only at hmem
          rw [Std.HashMap.mem_insert] at hmem
          rcases hmem with hkey | htail
          · have hk := eq_of_beq hkey
            subst key
            simp [recursiveEqualityOrbitMemoKey]
          · have hchild := expandQuantifiedEqualityOrbitsHashed_new_key_size_le
              body used available env table key htail hnew
            simp_wf
            omega
      | conj left right =>
          simp only at hmem
          rw [Std.HashMap.mem_insert] at hmem
          rcases hmem with hkey | htail
          · have hk := eq_of_beq hkey
            subst key
            simp [recursiveEqualityOrbitMemoKey]
          · let leftTable := (expandQuantifiedEqualityOrbitsHashed
                left used available env table).table
            by_cases hleftMem : key ∈ leftTable
            · have hleft := expandQuantifiedEqualityOrbitsHashed_new_key_size_le
                left used available env table key hleftMem hnew
              simp_wf
              omega
            · have hright := expandQuantifiedEqualityOrbitsHashed_new_key_size_le
                right used available env leftTable key htail hleftMem
              simp_wf
              omega
      | disj left right =>
          simp only at hmem
          rw [Std.HashMap.mem_insert] at hmem
          rcases hmem with hkey | htail
          · have hk := eq_of_beq hkey
            subst key
            simp [recursiveEqualityOrbitMemoKey]
          · let leftTable := (expandQuantifiedEqualityOrbitsHashed
                left used available env table).table
            by_cases hleftMem : key ∈ leftTable
            · have hleft := expandQuantifiedEqualityOrbitsHashed_new_key_size_le
                left used available env table key hleftMem hnew
              simp_wf
              omega
            · have hright := expandQuantifiedEqualityOrbitsHashed_new_key_size_le
                right used available env leftTable key htail hleftMem
              simp_wf
              omega
      | oplus left right =>
          simp only at hmem
          rw [Std.HashMap.mem_insert] at hmem
          rcases hmem with hkey | htail
          · have hk := eq_of_beq hkey
            subst key
            simp [recursiveEqualityOrbitMemoKey]
          · exact False.elim (hnew htail)
      | all x body =>
          simp only at hmem
          rw [Std.HashMap.mem_insert] at hmem
          rcases hmem with hkey | htail
          · have hk := eq_of_beq hkey
            subst key
            simp [recursiveEqualityOrbitMemoKey]
          · let oldQueries : List RecursiveEqualityOrbitBranchQuery :=
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
              expandQuantifiedEqualityOrbitBranchesHashed_new_key_size_le
                body (oldQueries ++ freshQueries) table key htail hnew
            simp_wf
            omega
      | ex x body =>
          simp only at hmem
          rw [Std.HashMap.mem_insert] at hmem
          rcases hmem with hkey | htail
          · have hk := eq_of_beq hkey
            subst key
            simp [recursiveEqualityOrbitMemoKey]
          · let oldQueries : List RecursiveEqualityOrbitBranchQuery :=
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
              expandQuantifiedEqualityOrbitBranchesHashed_new_key_size_le
                body (oldQueries ++ freshQueries) table key htail hnew
            simp_wf
            omega
  termination_by (sizeOf phi, 0)

  theorem expandQuantifiedEqualityOrbitBranchesHashed_new_key_size_le
      (body : QFormula) (queries : List RecursiveEqualityOrbitBranchQuery)
      (table : HashedEqualityOrbitMemoTable)
      (key : RecursiveEqualityOrbitMemoKey)
      (hmem : key ∈ (expandQuantifiedEqualityOrbitBranchesHashed
        body queries table).table)
      (hnew : key ∉ table) :
      sizeOf key.formula ≤ sizeOf body := by
    cases queries with
    | nil =>
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def] at hmem
        exact False.elim (hnew hmem)
    | cons query rest =>
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def] at hmem
        let headTable := (expandQuantifiedEqualityOrbitsHashed body
          query.used query.available query.env table).table
        by_cases hheadMem : key ∈ headTable
        · exact expandQuantifiedEqualityOrbitsHashed_new_key_size_le body
            query.used query.available query.env table key hheadMem hnew
        · exact expandQuantifiedEqualityOrbitBranchesHashed_new_key_size_le body
            rest headTable key hmem hheadMem
  termination_by (sizeOf body, queries.length + 1)
end

theorem parent_key_not_mem_after_smaller_call
    (parent child : QFormula) (parentUsed parentAvailable childUsed childAvailable : List Var)
    (parentEnv childEnv : QuantifierEnv)
    (table : HashedEqualityOrbitMemoTable)
    (habsent : table.get?
      (recursiveEqualityOrbitMemoKey parent parentUsed parentAvailable parentEnv) = none)
    (hsize : sizeOf child < sizeOf parent) :
    recursiveEqualityOrbitMemoKey parent parentUsed parentAvailable parentEnv ∉
      (expandQuantifiedEqualityOrbitsHashed child childUsed childAvailable
        childEnv table).table := by
  intro hmem
  have hnew : recursiveEqualityOrbitMemoKey parent parentUsed parentAvailable
      parentEnv ∉ table := by
    simpa using habsent
  have hle := expandQuantifiedEqualityOrbitsHashed_new_key_size_le child
    childUsed childAvailable childEnv table _ hmem hnew
  simp [recursiveEqualityOrbitMemoKey] at hle
  omega

theorem parent_key_not_mem_after_smaller_branches
    (parent body : QFormula) (parentUsed parentAvailable : List Var)
    (parentEnv : QuantifierEnv)
    (queries : List RecursiveEqualityOrbitBranchQuery)
    (table : HashedEqualityOrbitMemoTable)
    (habsent : table.get?
      (recursiveEqualityOrbitMemoKey parent parentUsed parentAvailable parentEnv) = none)
    (hsize : sizeOf body < sizeOf parent) :
    recursiveEqualityOrbitMemoKey parent parentUsed parentAvailable parentEnv ∉
      (expandQuantifiedEqualityOrbitBranchesHashed body queries table).table := by
  intro hmem
  have hnew : recursiveEqualityOrbitMemoKey parent parentUsed parentAvailable
      parentEnv ∉ table := by
    simpa using habsent
  have hle := expandQuantifiedEqualityOrbitBranchesHashed_new_key_size_le body
    queries table _ hmem hnew
  simp [recursiveEqualityOrbitMemoKey] at hle
  omega

/- The hash map can grow by at most one cell per miss.  This remains true
even without proving that a parent key cannot be inserted by a descendant. -/
mutual
  theorem expandQuantifiedEqualityOrbitsHashed_size_le_misses
      (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
      (table : HashedEqualityOrbitMemoTable) :
      let result := expandQuantifiedEqualityOrbitsHashed
        phi used available env table
      result.table.size ≤ table.size + result.stats.misses := by
    rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
    dsimp only
    split
    next cached hlookup =>
      simp [EqualityOrbitMemoStats.hit]
    next hlookup =>
      cases phi with
      | pred P xs =>
          simp only
          have hins := Std.HashMap.size_insert_le
            (m := table)
            (k := recursiveEqualityOrbitMemoKey (.pred P xs) used available env)
            (v := EqBoolFormula.bot)
          simpa [EqualityOrbitMemoStats.add, EqualityOrbitMemoStats.miss] using hins
      | eq x y =>
          simp only
          have hins := Std.HashMap.size_insert_le
            (m := table)
            (k := recursiveEqualityOrbitMemoKey (.eq x y) used available env)
            (v := if env x = env y then EqBoolFormula.top
              else EqBoolFormula.atom (normalizeEqAtom (env x) (env y)))
          simpa [EqualityOrbitMemoStats.add, EqualityOrbitMemoStats.miss] using hins
      | neg body =>
          simp only
          have hchild := expandQuantifiedEqualityOrbitsHashed_size_le_misses
            body used available env table
          have hins := Std.HashMap.size_insert_le
            (m := (expandQuantifiedEqualityOrbitsHashed
              body used available env table).table)
            (k := recursiveEqualityOrbitMemoKey (.neg body) used available env)
            (v := (expandQuantifiedEqualityOrbitsHashed
              body used available env table).formula.neg)
          simp [EqualityOrbitMemoStats.add, EqualityOrbitMemoStats.miss] at *
          omega
      | conj left right =>
          simp only
          have hleft := expandQuantifiedEqualityOrbitsHashed_size_le_misses
            left used available env table
          have hright := expandQuantifiedEqualityOrbitsHashed_size_le_misses
            right used available env
              (expandQuantifiedEqualityOrbitsHashed left used available env table).table
          have hins := Std.HashMap.size_insert_le
            (m := (expandQuantifiedEqualityOrbitsHashed right used available env
              (expandQuantifiedEqualityOrbitsHashed left used available env table).table).table)
            (k := recursiveEqualityOrbitMemoKey (.conj left right) used available env)
            (v := EqBoolFormula.conj
              (expandQuantifiedEqualityOrbitsHashed left used available env table).formula
              (expandQuantifiedEqualityOrbitsHashed right used available env
                (expandQuantifiedEqualityOrbitsHashed left used available env table).table).formula)
          simp [EqualityOrbitMemoStats.add, EqualityOrbitMemoStats.miss] at *
          omega
      | disj left right =>
          simp only
          have hleft := expandQuantifiedEqualityOrbitsHashed_size_le_misses
            left used available env table
          have hright := expandQuantifiedEqualityOrbitsHashed_size_le_misses
            right used available env
              (expandQuantifiedEqualityOrbitsHashed left used available env table).table
          have hins := Std.HashMap.size_insert_le
            (m := (expandQuantifiedEqualityOrbitsHashed right used available env
              (expandQuantifiedEqualityOrbitsHashed left used available env table).table).table)
            (k := recursiveEqualityOrbitMemoKey (.disj left right) used available env)
            (v := EqBoolFormula.disj
              (expandQuantifiedEqualityOrbitsHashed left used available env table).formula
              (expandQuantifiedEqualityOrbitsHashed right used available env
                (expandQuantifiedEqualityOrbitsHashed left used available env table).table).formula)
          simp [EqualityOrbitMemoStats.add, EqualityOrbitMemoStats.miss] at *
          omega
      | oplus left right =>
          simp only
          have hins := Std.HashMap.size_insert_le
            (m := table)
            (k := recursiveEqualityOrbitMemoKey (.oplus left right) used available env)
            (v := EqBoolFormula.bot)
          simpa [EqualityOrbitMemoStats.add, EqualityOrbitMemoStats.miss] using hins
      | all x body =>
          simp only
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
            expandQuantifiedEqualityOrbitBranchesHashed_size_le_misses
              body (oldQueries ++ freshQueries) table
          have hins := Std.HashMap.size_insert_le
            (m := (expandQuantifiedEqualityOrbitBranchesHashed body
              (oldQueries ++ freshQueries) table).table)
            (k := recursiveEqualityOrbitMemoKey (.all x body) used available env)
            (v := EqBoolFormula.conjList
              (expandQuantifiedEqualityOrbitBranchesHashed body
                (oldQueries ++ freshQueries) table).formulas)
          simp [oldQueries, freshQueries, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] at *
          omega
      | ex x body =>
          simp only
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
            expandQuantifiedEqualityOrbitBranchesHashed_size_le_misses
              body (oldQueries ++ freshQueries) table
          have hins := Std.HashMap.size_insert_le
            (m := (expandQuantifiedEqualityOrbitBranchesHashed body
              (oldQueries ++ freshQueries) table).table)
            (k := recursiveEqualityOrbitMemoKey (.ex x body) used available env)
            (v := EqBoolFormula.disjList
              (expandQuantifiedEqualityOrbitBranchesHashed body
                (oldQueries ++ freshQueries) table).formulas)
          simp [oldQueries, freshQueries, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] at *
          omega
  termination_by (sizeOf phi, 0)

  theorem expandQuantifiedEqualityOrbitBranchesHashed_size_le_misses
      (body : QFormula) (queries : List RecursiveEqualityOrbitBranchQuery)
      (table : HashedEqualityOrbitMemoTable) :
      let result := expandQuantifiedEqualityOrbitBranchesHashed body queries table
      result.table.size ≤ table.size + result.stats.misses := by
    cases queries with
    | nil =>
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        simp
    | cons query rest =>
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        have hhead := expandQuantifiedEqualityOrbitsHashed_size_le_misses body
          query.used query.available query.env table
        have htail := expandQuantifiedEqualityOrbitBranchesHashed_size_le_misses
          body rest (expandQuantifiedEqualityOrbitsHashed body query.used
            query.available query.env table).table
        simp [EqualityOrbitMemoStats.add] at *
        omega
  termination_by (sizeOf body, queries.length + 1)
end

/- Exact state accounting.  A miss cannot be followed by insertion of the
same parent key in a strict descendant, so the final parent insertion is new.
Consequently every miss increases `HashMap.size` by exactly one. -/
mutual
  theorem expandQuantifiedEqualityOrbitsHashed_size_eq_misses
      (phi : QFormula) (used available : List Var) (env : QuantifierEnv)
      (table : HashedEqualityOrbitMemoTable) :
      let result := expandQuantifiedEqualityOrbitsHashed
        phi used available env table
      result.table.size = table.size + result.stats.misses := by
    rw [expandQuantifiedEqualityOrbitsHashed.eq_def]
    dsimp only
    split
    next cached hlookup =>
      simp [EqualityOrbitMemoStats.hit]
    next hlookup =>
      have habsent : recursiveEqualityOrbitMemoKey phi used available env ∉
          table := by simpa using hlookup
      cases phi with
      | pred P xs =>
          simp only
          rw [Std.HashMap.size_insert, if_neg habsent]
          simp [EqualityOrbitMemoStats.add, EqualityOrbitMemoStats.miss]
      | eq x y =>
          simp only
          rw [Std.HashMap.size_insert, if_neg habsent]
          simp [EqualityOrbitMemoStats.add, EqualityOrbitMemoStats.miss]
      | neg body =>
          simp only
          have hchild := expandQuantifiedEqualityOrbitsHashed_size_eq_misses
            body used available env table
          have hstrict : sizeOf body < sizeOf (QFormula.neg body) := by
            simp_wf
          have hparent := parent_key_not_mem_after_smaller_call
            (.neg body) body used available used available env env table
            hlookup hstrict
          rw [Std.HashMap.size_insert, if_neg hparent]
          simp [EqualityOrbitMemoStats.add, EqualityOrbitMemoStats.miss] at *
          omega
      | conj left right =>
          simp only
          let leftResult := expandQuantifiedEqualityOrbitsHashed
            left used available env table
          let rightResult := expandQuantifiedEqualityOrbitsHashed
            right used available env leftResult.table
          have hleft := expandQuantifiedEqualityOrbitsHashed_size_eq_misses
            left used available env table
          have hleftStrict : sizeOf left < sizeOf (QFormula.conj left right) := by
            simp_wf
            omega
          have hparentLeft := parent_key_not_mem_after_smaller_call
            (.conj left right) left used available used available env env table
            hlookup hleftStrict
          have hlookupLeft : leftResult.table.get?
              (recursiveEqualityOrbitMemoKey (.conj left right)
                used available env) = none := by
            simpa [leftResult] using hparentLeft
          have hright := expandQuantifiedEqualityOrbitsHashed_size_eq_misses
            right used available env leftResult.table
          have hrightStrict : sizeOf right < sizeOf (QFormula.conj left right) := by
            simp_wf
          have hparentRight := parent_key_not_mem_after_smaller_call
            (.conj left right) right used available used available env env
            leftResult.table hlookupLeft hrightStrict
          rw [Std.HashMap.size_insert, if_neg hparentRight]
          simp [leftResult, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] at *
          omega
      | disj left right =>
          simp only
          let leftResult := expandQuantifiedEqualityOrbitsHashed
            left used available env table
          let rightResult := expandQuantifiedEqualityOrbitsHashed
            right used available env leftResult.table
          have hleft := expandQuantifiedEqualityOrbitsHashed_size_eq_misses
            left used available env table
          have hleftStrict : sizeOf left < sizeOf (QFormula.disj left right) := by
            simp_wf
            omega
          have hparentLeft := parent_key_not_mem_after_smaller_call
            (.disj left right) left used available used available env env table
            hlookup hleftStrict
          have hlookupLeft : leftResult.table.get?
              (recursiveEqualityOrbitMemoKey (.disj left right)
                used available env) = none := by
            simpa [leftResult] using hparentLeft
          have hright := expandQuantifiedEqualityOrbitsHashed_size_eq_misses
            right used available env leftResult.table
          have hrightStrict : sizeOf right < sizeOf (QFormula.disj left right) := by
            simp_wf
          have hparentRight := parent_key_not_mem_after_smaller_call
            (.disj left right) right used available used available env env
            leftResult.table hlookupLeft hrightStrict
          rw [Std.HashMap.size_insert, if_neg hparentRight]
          simp [leftResult, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] at *
          omega
      | oplus left right =>
          simp only
          rw [Std.HashMap.size_insert, if_neg habsent]
          simp [EqualityOrbitMemoStats.add, EqualityOrbitMemoStats.miss]
      | all x body =>
          simp only
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
          let branchResult := expandQuantifiedEqualityOrbitBranchesHashed
            body (oldQueries ++ freshQueries) table
          have hbranches :=
            expandQuantifiedEqualityOrbitBranchesHashed_size_eq_misses
              body (oldQueries ++ freshQueries) table
          have hstrict : sizeOf body < sizeOf (QFormula.all x body) := by
            simp_wf
          have hparent := parent_key_not_mem_after_smaller_branches
            (.all x body) body used available env (oldQueries ++ freshQueries)
            table hlookup hstrict
          rw [Std.HashMap.size_insert, if_neg hparent]
          simp [oldQueries, freshQueries, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] at *
          omega
      | ex x body =>
          simp only
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
          let branchResult := expandQuantifiedEqualityOrbitBranchesHashed
            body (oldQueries ++ freshQueries) table
          have hbranches :=
            expandQuantifiedEqualityOrbitBranchesHashed_size_eq_misses
              body (oldQueries ++ freshQueries) table
          have hstrict : sizeOf body < sizeOf (QFormula.ex x body) := by
            simp_wf
          have hparent := parent_key_not_mem_after_smaller_branches
            (.ex x body) body used available env (oldQueries ++ freshQueries)
            table hlookup hstrict
          rw [Std.HashMap.size_insert, if_neg hparent]
          simp [oldQueries, freshQueries, EqualityOrbitMemoStats.add,
            EqualityOrbitMemoStats.miss] at *
          omega
  termination_by (sizeOf phi, 0)

  theorem expandQuantifiedEqualityOrbitBranchesHashed_size_eq_misses
      (body : QFormula) (queries : List RecursiveEqualityOrbitBranchQuery)
      (table : HashedEqualityOrbitMemoTable) :
      let result := expandQuantifiedEqualityOrbitBranchesHashed body queries table
      result.table.size = table.size + result.stats.misses := by
    cases queries with
    | nil =>
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        simp
    | cons query rest =>
        rw [expandQuantifiedEqualityOrbitBranchesHashed.eq_def]
        have hhead := expandQuantifiedEqualityOrbitsHashed_size_eq_misses body
          query.used query.available query.env table
        have htail := expandQuantifiedEqualityOrbitBranchesHashed_size_eq_misses
          body rest (expandQuantifiedEqualityOrbitsHashed body query.used
            query.available query.env table).table
        simp [EqualityOrbitMemoStats.add] at *
        omega
  termination_by (sizeOf body, queries.length + 1)
end

/-- Closed root bound: the cutoff parameter fixes the representative carrier,
and therefore a finite cache-free request tree. -/
def quantifiedEqualityUniqueStateCutoff (k : Nat) (phi : QFormula) : Nat :=
  equalityOrbitRequestBound phi [] (cutoffRepresentatives k) id

theorem runQuantifiedEqualityOrbitHashed_requests_le_cutoff
    (k : Nat) (phi : QFormula) :
    let result := runQuantifiedEqualityOrbitHashed k phi
    result.stats.hits + result.stats.misses ≤
      quantifiedEqualityUniqueStateCutoff k phi := by
  exact expandQuantifiedEqualityOrbitsHashed_requests_le phi []
    (cutoffRepresentatives k) id emptyHashedEqualityOrbitMemoTable

/-- At the empty canonical root, the number of distinct hash keys is exactly
the number of misses, not merely bounded by it. -/
theorem runQuantifiedEqualityOrbitHashed_unique_states_eq_misses
    (k : Nat) (phi : QFormula) :
    let result := runQuantifiedEqualityOrbitHashed k phi
    result.table.size = result.stats.misses := by
  have hexact := expandQuantifiedEqualityOrbitsHashed_size_eq_misses phi []
    (cutoffRepresentatives k) id emptyHashedEqualityOrbitMemoTable
  simpa [runQuantifiedEqualityOrbitHashed,
    emptyHashedEqualityOrbitMemoTable] using hexact

/-- Quantitative unique-state theorem.  `HashMap.size` counts distinct keys;
from the empty root it equals misses and is bounded by the structural cutoff
recurrence. -/
theorem runQuantifiedEqualityOrbitHashed_unique_states_le_cutoff
    (k : Nat) (phi : QFormula) :
    let result := runQuantifiedEqualityOrbitHashed k phi
    result.table.size = result.stats.misses ∧
      result.table.size ≤ quantifiedEqualityUniqueStateCutoff k phi := by
  let result := runQuantifiedEqualityOrbitHashed k phi
  have hsize := runQuantifiedEqualityOrbitHashed_unique_states_eq_misses k phi
  have hrequests := runQuantifiedEqualityOrbitHashed_requests_le_cutoff k phi
  change result.table.size = result.stats.misses ∧
    result.table.size ≤ quantifiedEqualityUniqueStateCutoff k phi
  change result.table.size = result.stats.misses at hsize
  change result.stats.hits + result.stats.misses ≤
    quantifiedEqualityUniqueStateCutoff k phi at hrequests
  constructor
  · exact hsize
  · omega

theorem runQuantifiedEqualityOrbitHashed_requests_le_rank_cutoff
    (phi : QFormula) :
    let k := QFormula.quantifierRank phi
    let result := runQuantifiedEqualityOrbitHashed k phi
    result.stats.hits + result.stats.misses ≤
      quantifiedEqualityUniqueStateCutoff k phi :=
  runQuantifiedEqualityOrbitHashed_requests_le_cutoff
    (QFormula.quantifierRank phi) phi

/-- Any cutoff with enough representatives realizes exactly the same
depth-sensitive cache-free weight; surplus representatives are never reached. -/
theorem quantifiedEqualityUniqueStateCutoff_eq_weighted_of_capacity
    (k : Nat) (phi : QFormula)
    (hcapacity : QFormula.quantifierRank phi ≤ (cutoffRepresentatives k).length) :
    quantifiedEqualityUniqueStateCutoff k phi =
      equalityOrbitWeightedRequestBound phi 0 := by
  have hexact := equalityOrbitRequestBound_eq_weighted phi []
    (cutoffRepresentatives k) id hcapacity
  simpa [quantifiedEqualityUniqueStateCutoff] using hexact

/-- At the canonical rank cutoff, the executable cache-free recurrence is
exactly the depth-sensitive structural weight. -/
theorem quantifiedEqualityUniqueStateCutoff_rank_eq_weighted
    (phi : QFormula) :
    quantifiedEqualityUniqueStateCutoff (QFormula.quantifierRank phi) phi =
      equalityOrbitWeightedRequestBound phi 0 :=
  quantifiedEqualityUniqueStateCutoff_eq_weighted_of_capacity
    (QFormula.quantifierRank phi) phi (by simp [cutoffRepresentatives])

/-- Actual memoized calls are bounded by the exact depth-sensitive
cache-free weight. -/
theorem runQuantifiedEqualityOrbitHashed_requests_le_weighted
    (phi : QFormula) :
    let k := QFormula.quantifierRank phi
    let result := runQuantifiedEqualityOrbitHashed k phi
    result.stats.requests ≤ equalityOrbitWeightedRequestBound phi 0 := by
  have hrequests := runQuantifiedEqualityOrbitHashed_requests_le_rank_cutoff phi
  have hcutoff := quantifiedEqualityUniqueStateCutoff_rank_eq_weighted phi
  change
    (runQuantifiedEqualityOrbitHashed (QFormula.quantifierRank phi) phi).stats.requests ≤
      equalityOrbitWeightedRequestBound phi 0
  change
    (runQuantifiedEqualityOrbitHashed (QFormula.quantifierRank phi) phi).stats.hits +
      (runQuantifiedEqualityOrbitHashed (QFormula.quantifierRank phi) phi).stats.misses ≤
      quantifiedEqualityUniqueStateCutoff (QFormula.quantifierRank phi) phi at hrequests
  simpa [EqualityOrbitMemoStats.requests, hcutoff] using hrequests

/-- Count-level pruning gap between the exact cache-free traversal and the
memoized run.  It is defined only after the proved `requests ≤ weight`
comparison.  This is a request-count measure, not yet a machine-time model. -/
def quantifiedEqualityPrunedRequestCount (phi : QFormula) : Nat :=
  let k := QFormula.quantifierRank phi
  let result := runQuantifiedEqualityOrbitHashed k phi
  equalityOrbitWeightedRequestBound phi 0 - result.stats.requests

/-- Exact three-way accounting at the canonical root:

* actual requests are unique stored states plus cache hits;
* structural weight is actual requests plus the count-level pruning gap.

Together with `table.size = misses`, this separates repeated-state requests
from the number of cache-free requests not executed by the memoized run. -/
theorem runQuantifiedEqualityOrbitHashed_weighted_accounting
    (phi : QFormula) :
    let k := QFormula.quantifierRank phi
    let result := runQuantifiedEqualityOrbitHashed k phi
    result.table.size = result.stats.misses ∧
      result.stats.requests = result.table.size + result.stats.hits ∧
      result.stats.requests + quantifiedEqualityPrunedRequestCount phi =
        equalityOrbitWeightedRequestBound phi 0 := by
  let k := QFormula.quantifierRank phi
  let result := runQuantifiedEqualityOrbitHashed k phi
  have hsize := runQuantifiedEqualityOrbitHashed_unique_states_eq_misses k phi
  have hrequests := runQuantifiedEqualityOrbitHashed_requests_le_weighted phi
  change result.table.size = result.stats.misses at hsize
  change result.stats.requests ≤ equalityOrbitWeightedRequestBound phi 0 at hrequests
  change result.table.size = result.stats.misses ∧
    result.stats.requests = result.table.size + result.stats.hits ∧
    result.stats.requests + quantifiedEqualityPrunedRequestCount phi =
      equalityOrbitWeightedRequestBound phi 0
  constructor
  · exact hsize
  constructor
  · simp [EqualityOrbitMemoStats.requests, hsize, Nat.add_comm]
  · change result.stats.requests +
      (equalityOrbitWeightedRequestBound phi 0 - result.stats.requests) =
        equalityOrbitWeightedRequestBound phi 0
    exact Nat.add_sub_of_le hrequests

/-- Complete depth-sensitive envelope.  The middle bound is the new
structure-aware quantity; the last two comparisons recover the published
Bell and factorial envelopes as formally weaker corollaries. -/
theorem runQuantifiedEqualityOrbitHashed_depth_sensitive_envelope
    (phi : QFormula) :
    let k := QFormula.quantifierRank phi
    let result := runQuantifiedEqualityOrbitHashed k phi
    result.table.size ≤ result.stats.requests ∧
      result.stats.requests ≤ equalityOrbitWeightedRequestBound phi 0 ∧
      equalityOrbitWeightedRequestBound phi 0 ≤
        QFormula.syntaxNodeCount phi * equalityOrbitLeafCount k 0 ∧
      QFormula.syntaxNodeCount phi * equalityOrbitLeafCount k 0 ≤
        QFormula.syntaxNodeCount phi * k.factorial := by
  let k := QFormula.quantifierRank phi
  let result := runQuantifiedEqualityOrbitHashed k phi
  have hsize := runQuantifiedEqualityOrbitHashed_unique_states_eq_misses k phi
  have hrequests := runQuantifiedEqualityOrbitHashed_requests_le_weighted phi
  have hweighted := equalityOrbitWeightedRequestBound_le_syntax_mul_leafCount phi 0
  have hfactorial := equalityOrbitLeafCount_zero_used_le_factorial k
  change result.table.size = result.stats.misses at hsize
  change result.stats.requests ≤ equalityOrbitWeightedRequestBound phi 0 at hrequests
  change equalityOrbitWeightedRequestBound phi 0 ≤
    QFormula.syntaxNodeCount phi * equalityOrbitLeafCount k 0 at hweighted
  constructor
  · change result.table.size ≤ result.stats.requests
    rw [hsize]
    simp [EqualityOrbitMemoStats.requests]
  constructor
  · exact hrequests
  constructor
  · exact hweighted
  · exact Nat.mul_le_mul_left (QFormula.syntaxNodeCount phi) hfactorial

/-- Closed Bell/Touchard envelope.  The left factor is the exact number of
syntax nodes; the right factor is the empty-root equality-partition count at
the formula's quantifier rank. -/
theorem runQuantifiedEqualityOrbitHashed_unique_states_le_syntax_mul_bell
    (phi : QFormula) :
    let k := QFormula.quantifierRank phi
    let result := runQuantifiedEqualityOrbitHashed k phi
    result.table.size ≤ QFormula.syntaxNodeCount phi *
      equalityOrbitLeafCount k 0 := by
  let k := QFormula.quantifierRank phi
  let result := runQuantifiedEqualityOrbitHashed k phi
  have hsize := runQuantifiedEqualityOrbitHashed_unique_states_eq_misses k phi
  have hrequests := runQuantifiedEqualityOrbitHashed_requests_le_cutoff k phi
  have hsyntax := equalityOrbitRequestBound_le_syntax_mul_leafCount phi []
    (cutoffRepresentatives k) id (by
      simp [k, cutoffRepresentatives])
  change result.table.size ≤ QFormula.syntaxNodeCount phi *
    equalityOrbitLeafCount k 0
  change result.table.size = result.stats.misses at hsize
  change result.stats.hits + result.stats.misses ≤
    quantifiedEqualityUniqueStateCutoff k phi at hrequests
  change quantifiedEqualityUniqueStateCutoff k phi ≤
    QFormula.syntaxNodeCount phi * equalityOrbitLeafCount k 0 at hsyntax
  omega

/-- Closed factorial envelope, obtained from the proved Bell/Touchard-to-
factorial comparison rather than from an asymptotic approximation. -/
theorem runQuantifiedEqualityOrbitHashed_unique_states_le_syntax_mul_factorial
    (phi : QFormula) :
    let k := QFormula.quantifierRank phi
    let result := runQuantifiedEqualityOrbitHashed k phi
    result.table.size ≤ QFormula.syntaxNodeCount phi * k.factorial := by
  let k := QFormula.quantifierRank phi
  let result := runQuantifiedEqualityOrbitHashed k phi
  have hbell :=
    runQuantifiedEqualityOrbitHashed_unique_states_le_syntax_mul_bell phi
  have hfactorial := equalityOrbitLeafCount_zero_used_le_factorial k
  change result.table.size ≤ QFormula.syntaxNodeCount phi * k.factorial
  change result.table.size ≤ QFormula.syntaxNodeCount phi *
    equalityOrbitLeafCount k 0 at hbell
  exact hbell.trans (Nat.mul_le_mul_left (QFormula.syntaxNodeCount phi) hfactorial)

/-- The numerical cutoff `k` allocates exactly `k+1` canonical names. -/
theorem hashed_cutoff_representative_count (k : Nat) :
    (cutoffRepresentatives k).length = k + 1 := by
  simp [cutoffRepresentatives]

/- Native regressions report `(hits, misses, unique states, proved cutoff)`.
The third component is the actual `HashMap.size`; the fourth is the structural
upper bound from `quantifiedEqualityUniqueStateCutoff`. -/
theorem hashedMemo_universalReflexivity_stats :
    let result := runQuantifiedEqualityOrbitHashed 1
      universalReflexivitySentence
    (result.stats.hits, result.stats.misses, result.table.size,
      quantifiedEqualityUniqueStateCutoff 1 universalReflexivitySentence) =
      (0, 2, 2, 2) := by
  native_decide

theorem hashedMemo_atLeastTwo_stats :
    let result := runQuantifiedEqualityOrbitHashed 2 atLeastTwoSentence
    (result.stats.hits, result.stats.misses, result.table.size,
      quantifiedEqualityUniqueStateCutoff 2 atLeastTwoSentence) =
      (0, 6, 6, 6) := by
  native_decide

theorem hashedMemo_atLeastThree_stats :
    let result := runQuantifiedEqualityOrbitHashed 3 atLeastThreeSentence
    (result.stats.hits, result.stats.misses, result.table.size,
      quantifiedEqualityUniqueStateCutoff 3 atLeastThreeSentence) =
      (2, 40, 40, 44) := by
  native_decide

/-- Concrete audit of the exact state count and the two closed envelopes:
`(unique states, misses, syntax × Bell, syntax × factorial)`. -/
theorem hashedMemo_atLeastThree_closed_envelopes :
    let phi := atLeastThreeSentence
    let k := QFormula.quantifierRank phi
    let result := runQuantifiedEqualityOrbitHashed k phi
    (result.table.size, result.stats.misses,
      QFormula.syntaxNodeCount phi * equalityOrbitLeafCount k 0,
      QFormula.syntaxNodeCount phi * k.factorial) = (40, 40, 55, 66) := by
  native_decide

/-- Auditable decomposition for the first example with genuine cross-branch
sharing.  The tuple is `(unique, hits, misses, actual requests, pruned
descendants, weighted bound, syntax×Bell, syntax×factorial)`. -/
theorem hashedMemo_atLeastThree_weighted_accounting :
    let phi := atLeastThreeSentence
    let k := QFormula.quantifierRank phi
    let result := runQuantifiedEqualityOrbitHashed k phi
    ((result.table.size, result.stats.hits, result.stats.misses,
        result.stats.requests),
      (quantifiedEqualityPrunedRequestCount phi,
        equalityOrbitWeightedRequestBound phi 0,
        QFormula.syntaxNodeCount phi * equalityOrbitLeafCount k 0,
        QFormula.syntaxNodeCount phi * k.factorial)) =
      ((40, 2, 40, 42), (2, 44, 55, 66)) := by
  native_decide

/-- Rank-one, rank-two, and rank-three executable cross-checks.  Each row is
`(actual requests, pruned descendants, cache-free weight)`. -/
theorem hashedMemo_weighted_rank_growth_regressions :
    let rankOne := runQuantifiedEqualityOrbitHashed 1 universalReflexivitySentence
    let rankTwo := runQuantifiedEqualityOrbitHashed 2 atLeastTwoSentence
    let rankThree := runQuantifiedEqualityOrbitHashed 3 atLeastThreeSentence
    ((rankOne.stats.requests,
        quantifiedEqualityPrunedRequestCount universalReflexivitySentence,
        equalityOrbitWeightedRequestBound universalReflexivitySentence 0),
      (rankTwo.stats.requests,
        quantifiedEqualityPrunedRequestCount atLeastTwoSentence,
        equalityOrbitWeightedRequestBound atLeastTwoSentence 0),
      (rankThree.stats.requests,
        quantifiedEqualityPrunedRequestCount atLeastThreeSentence,
        equalityOrbitWeightedRequestBound atLeastThreeSentence 0)) =
      ((2, 0, 2), (6, 0, 6), (42, 2, 44)) := by
  native_decide

theorem hashedMemo_repeatedSubformula_stats :
    let result := runQuantifiedEqualityOrbitHashed 1
      repeatedUniversalReflexivitySentence
    (result.stats.hits, result.stats.misses, result.table.size,
      quantifiedEqualityUniqueStateCutoff 1
        repeatedUniversalReflexivitySentence) = (1, 3, 3, 5) := by
  native_decide

end

end Nullivance.InfiniteFO
