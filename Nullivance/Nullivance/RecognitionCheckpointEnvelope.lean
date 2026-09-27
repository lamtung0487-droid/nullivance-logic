import Nullivance.RecognitionCheckpointBytes
import Init.Data.ByteArray.Lemmas
import Init.Data.UInt.Lemmas

/-! Version-1 ByteArray envelope for the canonical cursor codec. The length
guard is a syntactic input bound, not a proved time or memory-complexity bound. -/
namespace Nullivance.Recognition

def envelopeHeader : List UInt8 := [78,80,1]

def wrapCheckpointBytes (payload : List CheckpointByte) : ByteArray :=
  (envelopeHeader ++ payload.map UInt8.ofFin).toByteArray

def unwrapCheckpointBytes (maxBytes : ℕ) (bytes : ByteArray) :
    Option (List CheckpointByte) :=
  if bytes.size ≤ maxBytes then
    match bytes.data.toList with
    | 78 :: 80 :: 1 :: rest => some (rest.map UInt8.toFin)
    | _ => none
  else none

theorem wrapCheckpointBytes_size (payload : List CheckpointByte) :
    (wrapCheckpointBytes payload).size = 3 + payload.length := by
  simp [wrapCheckpointBytes,envelopeHeader]
  omega

theorem unwrapCheckpointBytes_wrap (payload : List CheckpointByte)
    (maxBytes : ℕ) (h : 3 + payload.length ≤ maxBytes) :
    unwrapCheckpointBytes maxBytes (wrapCheckpointBytes payload) = some payload := by
  have hs : (wrapCheckpointBytes payload).size ≤ maxBytes := by
    rw [wrapCheckpointBytes_size]
    exact h
  simp only [unwrapCheckpointBytes,hs,ite_true]
  simp [wrapCheckpointBytes,envelopeHeader,Function.comp_def]

theorem unwrapCheckpointBytes_over_limit (maxBytes : ℕ) (bytes : ByteArray)
    (h : maxBytes < bytes.size) :
    unwrapCheckpointBytes maxBytes bytes = none := by
  simp [unwrapCheckpointBytes,not_le.mpr h]

theorem unwrapCheckpointBytes_wrong_version (maxBytes : ℕ)
    (payload : List CheckpointByte) :
    unwrapCheckpointBytes maxBytes
      (([78,80,2] ++ payload.map UInt8.ofFin).toByteArray) = none := by
  simp [unwrapCheckpointBytes]

def encodeCursorEnvelope (c : SearchCursor) : ByteArray :=
  wrapCheckpointBytes (encodeCursorBytes c)

def decodeCursorEnvelope (maxBytes : ℕ) (bytes : ByteArray) :
    Option SearchCursor :=
  (unwrapCheckpointBytes maxBytes bytes).bind decodeCursorBytes

theorem decodeCursorEnvelope_encode (c : SearchCursor) (maxBytes : ℕ)
    (h : 3 + (encodeCursorBytes c).length ≤ maxBytes) :
    decodeCursorEnvelope maxBytes (encodeCursorEnvelope c) = some c := by
  simp [decodeCursorEnvelope,encodeCursorEnvelope,
    unwrapCheckpointBytes_wrap _ _ h,decodeCursorBytes_encode]

theorem decodeCursorEnvelope_over_limit (maxBytes : ℕ) (bytes : ByteArray)
    (h : maxBytes < bytes.size) : decodeCursorEnvelope maxBytes bytes = none := by
  simp [decodeCursorEnvelope,unwrapCheckpointBytes_over_limit _ _ h]

def saveActiveEnvelope {r : ProbeStream} (s : TrustedSession r) :
    Option ByteArray :=
  (saveActiveBytes s).map wrapCheckpointBytes

theorem saveActiveEnvelope_output {r : ProbeStream} (s : TrustedSession r)
    (bytes : ByteArray) (h : saveActiveEnvelope s = some bytes) :
    ∃ payload : List CheckpointByte,
      saveActiveBytes s = some payload ∧ bytes = wrapCheckpointBytes payload := by
  unfold saveActiveEnvelope at h
  cases hs : saveActiveBytes s with
  | none => simp [hs] at h
  | some payload =>
    simp only [hs,Option.map_some,Option.some.injEq] at h
    exact ⟨payload,rfl,h.symm⟩

def restoreActiveEnvelopeCounted (r : ProbeStream) (maxBytes : ℕ)
    (bytes : ByteArray) : Option (TrustedSession r) × ℕ × ℕ :=
  match unwrapCheckpointBytes maxBytes bytes with
  | none => (none,0,0)
  | some payload => restoreActiveBytesCounted r payload

theorem restoreActiveEnvelopeCounted_over_limit (r : ProbeStream)
    (maxBytes : ℕ) (bytes : ByteArray) (h : maxBytes < bytes.size) :
    restoreActiveEnvelopeCounted r maxBytes bytes = (none,0,0) := by
  simp [restoreActiveEnvelopeCounted,unwrapCheckpointBytes_over_limit _ _ h]

theorem restoreActiveEnvelopeCounted_wrong_version (r : ProbeStream)
    (maxBytes : ℕ) (payload : List CheckpointByte) :
    restoreActiveEnvelopeCounted r maxBytes
      (([78,80,2] ++ payload.map UInt8.ofFin).toByteArray) = (none,0,0) := by
  rw [restoreActiveEnvelopeCounted,
    unwrapCheckpointBytes_wrong_version maxBytes payload]

theorem restoreActiveEnvelopeCounted_noncanonical (r : ProbeStream)
    (maxBytes : ℕ) (payload : List CheckpointByte)
    (hsize : 3 + payload.length ≤ maxBytes)
    (hbad : payload ≠ encodeNatBytes (decodeNatBytes payload)) :
    restoreActiveEnvelopeCounted r maxBytes (wrapCheckpointBytes payload) =
      (none,0,0) := by
  rw [restoreActiveEnvelopeCounted,
    unwrapCheckpointBytes_wrap payload maxBytes hsize]
  exact restoreActiveBytesCounted_noncanonical r payload hbad

theorem restoreActiveEnvelopeCounted_success (r : ProbeStream)
    (maxBytes : ℕ) (bytes : ByteArray) (restored : TrustedSession r)
    (h : (restoreActiveEnvelopeCounted r maxBytes bytes).1 = some restored) :
    ∃ payload : List CheckpointByte, ∃ c : SearchCursor,
      unwrapCheckpointBytes maxBytes bytes = some payload ∧
      payload = encodeCursorBytes c ∧ CursorMatches r c := by
  unfold restoreActiveEnvelopeCounted at h
  cases hu : unwrapCheckpointBytes maxBytes bytes with
  | none => simp [hu] at h
  | some payload =>
    have hp : (restoreActiveBytesCounted r payload).1 = some restored := by
      simpa only [hu] using h
    unfold restoreActiveBytesCounted at hp
    cases hd : decodeCursorBytes payload with
    | none => simp [hd] at hp
    | some c =>
      have henc := (decodeCursorBytes_iff payload c).mp hd
      have him : (importTrustedSessionCounted r c).1 = some restored := by
        simpa only [hd] using hp
      have hm : CursorMatches r c := by
        have hi : (importTrustedSessionCounted r c).1.isSome = true := by
          rw [him]
          rfl
        exact (importTrustedSessionCounted_isSome r c).mp hi
      exact ⟨payload,c,rfl,henc,hm⟩

theorem saveActiveEnvelope_restores {r : ProbeStream} (s : TrustedSession r)
    (bytes : ByteArray) (maxBytes : ℕ)
    (hs : saveActiveEnvelope s = some bytes)
    (hb : bytes.size ≤ maxBytes) :
    (restoreActiveEnvelopeCounted r maxBytes bytes).1.isSome = true := by
  obtain ⟨payload,hp,he⟩ := saveActiveEnvelope_output s bytes hs
  subst bytes
  have hsize : 3 + payload.length ≤ maxBytes := by
    simpa [wrapCheckpointBytes_size] using hb
  simp only [restoreActiveEnvelopeCounted,
    unwrapCheckpointBytes_wrap payload maxBytes hsize]
  exact saveActiveBytes_restores s payload hp

theorem restoredActiveEnvelope_observation (r : ProbeStream)
    (s restored : TrustedSession r) (bytes : ByteArray)
    (maxBytes : ℕ) (fuels : List ℕ)
    (hs : saveActiveEnvelope s = some bytes)
    (hr : (restoreActiveEnvelopeCounted r maxBytes bytes).1 = some restored) :
    (fuels.foldl (stepTrustedSession r) s).out.1.found =
        (fuels.foldl (stepTrustedSession r) restored).out.1.found ∧
    (fuels.foldl (stepTrustedSession r) s).out.1.cursor =
        (fuels.foldl (stepTrustedSession r) restored).out.1.cursor := by
  obtain ⟨payload,hp,he⟩ := saveActiveEnvelope_output s bytes hs
  subst bytes
  by_cases hb : (wrapCheckpointBytes payload).size ≤ maxBytes
  ·
    have hsize : 3 + payload.length ≤ maxBytes := by
      simpa [wrapCheckpointBytes_size] using hb
    simp only [restoreActiveEnvelopeCounted,
      unwrapCheckpointBytes_wrap payload maxBytes hsize] at hr
    exact restoredActiveBytes_observation r s restored payload fuels hp hr
  ·
    have hh : maxBytes < (wrapCheckpointBytes payload).size := by omega
    simp [restoreActiveEnvelopeCounted_over_limit r maxBytes _ hh] at hr

theorem restoredActiveEnvelope_certificates (r : ProbeStream)
    (s restored : TrustedSession r) (bytes : ByteArray)
    (maxBytes : ℕ) (fuels : List ℕ)
    (hs : saveActiveEnvelope s = some bytes)
    (hr : (restoreActiveEnvelopeCounted r maxBytes bytes).1 = some restored) :
    (sharedResultExport (fuels.foldl (stepTrustedSession r) s).out).1 =
      (sharedResultExport (fuels.foldl (stepTrustedSession r) restored).out).1 := by
  have ho := restoredActiveEnvelope_observation r s restored bytes maxBytes fuels hs hr
  exact sharedResultExport_observation_congr _ _ ho.1 ho.2

theorem restoredActiveEnvelope_abstract_cost_bound (r : ProbeStream)
    (s restored : TrustedSession r) (bytes : ByteArray)
    (maxBytes : ℕ) (fuels : List ℕ)
    (hs : saveActiveEnvelope s = some bytes)
    (hb : bytes.size ≤ maxBytes)
    (hr : (restoreActiveEnvelopeCounted r maxBytes bytes).1 = some restored) :
    (restoreActiveEnvelopeCounted r maxBytes bytes).2.1 + endpointSearchTotal
      (fuels.foldl (stepTrustedSession r) restored).out +
    (sharedResultExport (fuels.foldl (stepTrustedSession r) restored).out).2.1 ≤
      8*s.out.1.cursor.next + 24*fuels.sum + 16 := by
  obtain ⟨payload,hp,he⟩ := saveActiveEnvelope_output s bytes hs
  subst bytes
  have hsize : 3 + payload.length ≤ maxBytes := by
    simpa [wrapCheckpointBytes_size] using hb
  rw [restoreActiveEnvelopeCounted,
    unwrapCheckpointBytes_wrap payload maxBytes hsize] at hr ⊢
  exact restoredActiveBytes_abstract_cost_bound r s restored payload fuels hp hr

end Nullivance.Recognition
