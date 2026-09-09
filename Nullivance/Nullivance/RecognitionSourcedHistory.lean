import Nullivance.RecognitionConflictExtraction

/-! Materialized online interval summaries with original occurrence provenance.
The counter measures endpoint-selection comparisons, not rational bit costs. -/
namespace Nullivance.Recognition
open Generative Continuous

abbrev IndexedProbe := ProbeObservation × ℕ

structure SourcedInterval where
  lower : ℚ
  upper : ℚ
  lowerSource : Option IndexedProbe
  upperSource : Option IndexedProbe
  deriving DecidableEq, Repr

/-- Four stored fields, not a chain of coordinate-query closures. -/
structure SourcedBox where
  c0 : SourcedInterval
  c1 : SourcedInterval
  c2 : SourcedInterval
  c3 : SourcedInterval
  deriving DecidableEq, Repr

def SourcedBox.at (b : SourcedBox) (i : Fin 4) : SourcedInterval :=
  ![b.c0,b.c1,b.c2,b.c3] i

def SourcedBox.erase (b : SourcedBox) : ProbeBox := fun i =>
  ⟨(b.at i).lower, (b.at i).upper⟩

def initialSourcedInterval : SourcedInterval := ⟨0,1,none,none⟩
def initialSourcedBox : SourcedBox :=
  ⟨initialSourcedInterval,initialSourcedInterval,initialSourcedInterval,initialSourcedInterval⟩

def updateSourcedIntervalCounted (a : IndexedProbe) (i : Fin 4) (b : SourcedInterval) :
    SourcedInterval × ℕ :=
  let lo := readoutCoordinates a.1.2 i - a.1.1
  let hi := readoutCoordinates a.1.2 i + a.1.1
  let lower := if b.lower < lo then ((lo, some a), 1) else ((b.lower,b.lowerSource), 1)
  let upper := if hi < b.upper then ((hi, some a), 1) else ((b.upper,b.upperSource), 1)
  (⟨lower.1.1,upper.1.1,lower.1.2,upper.1.2⟩, lower.2 + upper.2)

def updateSourcedInterval (a : IndexedProbe) (i : Fin 4) (b : SourcedInterval) :
    SourcedInterval := (updateSourcedIntervalCounted a i b).1

def updateSourcedBoxCounted (a : IndexedProbe) (b : SourcedBox) : SourcedBox × ℕ :=
  let r0 := updateSourcedIntervalCounted a 0 b.c0
  let r1 := updateSourcedIntervalCounted a 1 b.c1
  let r2 := updateSourcedIntervalCounted a 2 b.c2
  let r3 := updateSourcedIntervalCounted a 3 b.c3
  (⟨r0.1,r1.1,r2.1,r3.1⟩, r0.2+r1.2+r2.2+r3.2)

def updateSourcedBox (a : IndexedProbe) (b : SourcedBox) : SourcedBox :=
  (updateSourcedBoxCounted a b).1

theorem updateSourcedIntervalCounted_comparisons (a : IndexedProbe) (i : Fin 4)
    (b : SourcedInterval) : (updateSourcedIntervalCounted a i b).2 = 2 := by
  unfold updateSourcedIntervalCounted
  dsimp only
  split_ifs <;> rfl

theorem updateSourcedBoxCounted_comparisons (a : IndexedProbe) (b : SourcedBox) :
    (updateSourcedBoxCounted a b).2 = 8 := by
  simp [updateSourcedBoxCounted, updateSourcedIntervalCounted_comparisons]

theorem updateSourcedBox_at (a : IndexedProbe) (b : SourcedBox) (i : Fin 4) :
    (updateSourcedBox a b).at i = updateSourcedInterval a i (b.at i) := by
  fin_cases i <;> rfl

theorem updateSourcedInterval_bounds (a : IndexedProbe) (i : Fin 4) (b : SourcedInterval) :
    (updateSourcedInterval a i b).lower = max b.lower (readoutCoordinates a.1.2 i - a.1.1) ∧
    (updateSourcedInterval a i b).upper = min b.upper (readoutCoordinates a.1.2 i + a.1.1) := by
  unfold updateSourcedInterval updateSourcedIntervalCounted
  dsimp only
  split_ifs <;> simp_all [le_of_lt]

theorem updateSourcedBox_erase (a : IndexedProbe) (b : SourcedBox) :
    (updateSourcedBox a b).erase = narrowProbeBox a.1 b.erase := by
  funext i
  simp only [SourcedBox.erase, updateSourcedBox_at, narrowProbeBox]
  rw [(updateSourcedInterval_bounds a i (b.at i)).1,
    (updateSourcedInterval_bounds a i (b.at i)).2]

theorem initialSourcedBox_erase : initialSourcedBox.erase = initialProbeBox := by
  funext i
  fin_cases i <;> rfl

def SourcedIntervalValid (rs : List ProbeObservation) (i : Fin 4) (b : SourcedInterval) : Prop :=
  (match b.lowerSource with
   | none => b.lower = 0
   | some a => rs[a.2]? = some a.1 ∧ b.lower = readoutCoordinates a.1.2 i - a.1.1) ∧
  (match b.upperSource with
   | none => b.upper = 1
   | some a => rs[a.2]? = some a.1 ∧ b.upper = readoutCoordinates a.1.2 i + a.1.1)

def SourcedBoxValid (rs : List ProbeObservation) (b : SourcedBox) : Prop :=
  ∀ i, SourcedIntervalValid rs i (b.at i)

theorem updateSourcedInterval_valid (rs : List ProbeObservation) (a : IndexedProbe)
    (ha : rs[a.2]? = some a.1) (i : Fin 4) (b : SourcedInterval)
    (hb : SourcedIntervalValid rs i b) :
    SourcedIntervalValid rs i (updateSourcedInterval a i b) := by
  unfold SourcedIntervalValid updateSourcedInterval updateSourcedIntervalCounted at *
  dsimp only
  split_ifs <;> simp_all

theorem updateSourcedBox_valid (rs : List ProbeObservation) (a : IndexedProbe)
    (ha : rs[a.2]? = some a.1) (b : SourcedBox) (hb : SourcedBoxValid rs b) :
    SourcedBoxValid rs (updateSourcedBox a b) := by
  intro i
  rw [updateSourcedBox_at]
  exact updateSourcedInterval_valid rs a ha i (b.at i) (hb i)

theorem initialSourcedBox_valid (rs : List ProbeObservation) :
    SourcedBoxValid rs initialSourcedBox := by
  intro i
  fin_cases i <;> constructor <;> rfl

/-- Each consumed record performs four materialized interval updates, each
with two endpoint-selection comparisons. The counter is accumulated online. -/
def scanSourced : List IndexedProbe → SourcedBox → ℕ → SourcedBox × ℕ
  | [], b, k => (b,k)
  | a :: rest, b, k =>
      let step := updateSourcedBoxCounted a b
      scanSourced rest step.1 (k+step.2)

theorem scanSourced_comparisons (xs : List IndexedProbe) (b : SourcedBox) (k : ℕ) :
    (scanSourced xs b k).2 = k + 8 * xs.length := by
  induction xs generalizing b k with
  | nil => simp [scanSourced]
  | cons a xs ih =>
    simp only [scanSourced, ih, updateSourcedBoxCounted_comparisons, List.length_cons]
    omega

theorem scanSourced_append (xs ys : List IndexedProbe) (b : SourcedBox) (k : ℕ) :
    scanSourced (xs ++ ys) b k =
      scanSourced ys (scanSourced xs b k).1 (scanSourced xs b k).2 := by
  induction xs generalizing b k with
  | nil => rfl
  | cons a xs ih =>
    simpa only [List.cons_append, scanSourced, updateSourcedBox] using ih (updateSourcedBox a b) _

theorem scanSourced_valid (rs : List ProbeObservation) (xs : List IndexedProbe)
    (hx : ∀ a ∈ xs, rs[a.2]? = some a.1) (b : SourcedBox)
    (hb : SourcedBoxValid rs b) (k : ℕ) : SourcedBoxValid rs (scanSourced xs b k).1 := by
  induction xs generalizing b k with
  | nil => exact hb
  | cons a xs ih =>
    apply ih (fun x h => hx x (by simp [h]))
    exact updateSourcedBox_valid rs a (hx a (by simp)) b hb

theorem summarizeProbes_snoc (seen : List ProbeObservation) (a : ProbeObservation) :
    summarizeProbes (seen ++ [a]) = narrowProbeBox a (summarizeProbes seen) := by
  induction seen with
  | nil => rfl
  | cons r seen ih =>
    simp only [List.cons_append, summarizeProbes, ih]
    exact narrowProbeBox_comm _ _ _

theorem scanSourced_erase (xs : List IndexedProbe) (seen : List ProbeObservation)
    (b : SourcedBox) (hb : b.erase = summarizeProbes seen) (k : ℕ) :
    (scanSourced xs b k).1.erase = summarizeProbes (seen ++ xs.map Prod.fst) := by
  induction xs generalizing seen b k with
  | nil => simpa [scanSourced] using hb
  | cons a xs ih =>
    have hstep : (updateSourcedBox a b).erase = summarizeProbes (seen ++ [a.1]) := by
      rw [updateSourcedBox_erase, hb, summarizeProbes_snoc]
    simpa [scanSourced, updateSourcedBox, updateSourcedBoxCounted_comparisons,
      List.append_assoc] using ih (seen ++ [a.1]) _ hstep (k+8)

def runSourcedHistory (rs : List ProbeObservation) : SourcedBox × ℕ :=
  scanSourced rs.zipIdx initialSourcedBox 0

theorem runSourcedHistory_comparisons (rs : List ProbeObservation) :
    (runSourcedHistory rs).2 = 8 * rs.length := by
  simp [runSourcedHistory, scanSourced_comparisons]

theorem runSourcedHistory_erase (rs : List ProbeObservation) :
    (runSourcedHistory rs).1.erase = summarizeProbes rs := by
  simpa [runSourcedHistory] using
    scanSourced_erase rs.zipIdx [] initialSourcedBox initialSourcedBox_erase 0

theorem runSourcedHistory_valid (rs : List ProbeObservation) :
    SourcedBoxValid rs (runSourcedHistory rs).1 := by
  apply scanSourced_valid rs rs.zipIdx _ _ (initialSourcedBox_valid rs)
  intro a ha
  exact (List.mem_zipIdx_iff_getElem?).mp ha

theorem runSourcedHistory_exact (rs : List ProbeObservation) (s : GenState scalarProbeFrame) :
    InProbeBox (runSourcedHistory rs).1.erase s ↔ HistoryFits rs s := by
  rw [runSourcedHistory_erase, summarizeProbes_exact]

/-- Resuming with correctly offset indices is exactly the batch computation. -/
theorem runSourcedHistory_append (rs ts : List ProbeObservation) :
    runSourcedHistory (rs ++ ts) =
      scanSourced (ts.zipIdx rs.length) (runSourcedHistory rs).1 (runSourcedHistory rs).2 := by
  simp [runSourcedHistory, List.zipIdx_append, scanSourced_append]

end Nullivance.Recognition
