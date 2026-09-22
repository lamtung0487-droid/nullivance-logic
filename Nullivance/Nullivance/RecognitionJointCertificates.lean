import Nullivance.RecognitionCheckedRefutation

/-! Joint exports distinguish rejection, timeout, affirmation and refutation.
These are operational outcomes, not the core logic's truth values. -/
namespace Nullivance.Recognition

theorem checked_certificates_exactly_one (r : ProbeStream) (c : SearchCursor)
    (fuel n : ℕ) (out : IncrementalSearchResult × ℕ)
    (h : checkedContinue r c fuel = some out) (hf : out.1.found = some n) :
    ((resultIndexedAffirmation out).1.isSome = true ∧
      (indexedResultRefutation out).isSome = false) ∨
    ((resultIndexedAffirmation out).1.isSome = false ∧
      (indexedResultRefutation out).isSome = true) := by
  have hp := checkedContinue_result r c fuel out h
  rw [hf] at hp
  have ht := (firstPassing_sound _ fuel c.next n hp.symm).2.2
  have hd : classifyHistory (probePrefix r n) = .affirmed ∨
      classifyHistory (probePrefix r n) = .refuted := of_decide_eq_true ht
  have ha := checkedAffirmation_complete r c fuel n out h hf
  have hr := checkedRefutation_complete r c fuel n out h hf
  have hx := checked_certificates_disjoint r c fuel n out h hf
  rcases hd with hd | hd
  · have a := ha.mpr hd
    have b : (indexedResultRefutation out).isSome = false := by
      cases hb : (indexedResultRefutation out).isSome
      · rfl
      · exact False.elim (hx ⟨a,hb⟩)
    exact Or.inl ⟨a,b⟩
  · have b := hr.mpr hd
    have a : (resultIndexedAffirmation out).1.isSome = false := by
      cases ha' : (resultIndexedAffirmation out).1.isSome
      · rfl
      · exact False.elim (hx ⟨ha',b⟩)
    exact Or.inr ⟨a,b⟩

def jointCertificates (out : IncrementalSearchResult × ℕ) :=
  ((resultIndexedAffirmation out).1,indexedResultRefutation out)

theorem jointCertificates_baseline (r : ProbeStream) (c : SearchCursor) (fuel : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out) :
    jointCertificates out = match firstPassing (prefixHasCertificate r) c.next fuel with
      | none => (none,none)
      | some n => (extractSourcedAffirmation (probePrefix r n),
          extractSourcedRefutation (probePrefix r n)) := by
  unfold jointCertificates
  rw [checkedAffirmation_baseline r c fuel out h,checkedRefutation_baseline r c fuel out h]
  rw [checkedContinue_result r c fuel out h]
  cases firstPassing (prefixHasCertificate r) c.next fuel <;> rfl

theorem jointCertificates_empty_iff (r : ProbeStream) (c : SearchCursor) (fuel : ℕ)
    (out : IncrementalSearchResult × ℕ) (h : checkedContinue r c fuel = some out) :
    jointCertificates out = (none,none) ↔ out.1.found = none := by
  cases hf : out.1.found with
  | none => simp [jointCertificates,resultIndexedAffirmation,indexedResultRefutation,hf]
  | some n =>
    constructor
    · intro he
      have he1 := congrArg (fun p => p.1.isSome) he
      have he2 := congrArg (fun p => p.2.isSome) he
      rcases checked_certificates_exactly_one r c fuel n out h hf with ha | hr
      · simp only [jointCertificates,Option.isSome_none] at he1
        rw [ha.1] at he1
        cases he1
      · simp only [jointCertificates,Option.isSome_none] at he2
        rw [hr.2] at he2
        cases he2
    · intro he
      cases he

def checkedJointCertificates (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :=
  (checkedContinue r c fuel).map jointCertificates

theorem checkedJointCertificates_rejected (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    checkedJointCertificates r c fuel = none ↔ ¬ CursorMatches r c := by
  rw [← checkSearchCursor_spec]
  unfold checkedJointCertificates checkedContinue
  split <;> simp_all

theorem checkedJointCertificates_spec (r : ProbeStream) (c : SearchCursor) (fuel : ℕ) :
    checkedJointCertificates r c fuel =
      if checkSearchCursor r c then
        some (match firstPassing (prefixHasCertificate r) c.next fuel with
          | none => (none,none)
          | some n => (extractSourcedAffirmation (probePrefix r n),
              extractSourcedRefutation (probePrefix r n)))
      else none := by
  by_cases hc : checkSearchCursor r c = true
  · have ho : checkedContinue r c fuel = some (searchEndpointCounted r c fuel) := by
      simp [checkedContinue,hc]
    simp only [checkedJointCertificates,ho,Option.map_some, hc,ite_true]
    exact congrArg some (jointCertificates_baseline r c fuel _ ho)
  · simp [checkedJointCertificates,checkedContinue,hc]

set_option maxRecDepth 4096 in
theorem joint_certificates_regression :
    let a : ProbeStream := fun _ => (0,((0,0),(0,0)))
    let b : ProbeStream := fun _ => (0,((1,0),(0,0)))
    let flags := fun p => (p.1.isSome,p.2.isSome)
    (checkedJointCertificates a ⟨1,initialSourcedBox⟩ 1).isSome = false ∧
      (checkedJointCertificates a initialSearchCursor 1).map flags = some (false,false) ∧
      (checkedJointCertificates a initialSearchCursor 2).map flags = some (true,false) ∧
      (checkedJointCertificates b initialSearchCursor 2).map flags = some (false,true) := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Nullivance.Recognition
