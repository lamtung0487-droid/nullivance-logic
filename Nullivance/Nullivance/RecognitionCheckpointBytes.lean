import Nullivance.RecognitionCheckpoint
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Nat.Digits.Defs

/-! A lossless, canonical, data-only byte codec for SearchCursor. Bytes are
`Fin 256`; no filesystem, cryptographic, or resource-cost claim is made. -/
namespace Nullivance.Recognition

private instance : Encodable SourcedInterval :=
  Encodable.ofLeftInverse
    (fun s => (s.lower,s.upper,s.lowerSource,s.upperSource))
    (fun p : ℚ × ℚ × Option IndexedProbe × Option IndexedProbe =>
      ⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩)
    (by intro s; cases s; rfl)

private instance : Encodable SourcedBox :=
  Encodable.ofLeftInverse
    (fun b => (b.c0,b.c1,b.c2,b.c3))
    (fun p : SourcedInterval × SourcedInterval × SourcedInterval × SourcedInterval =>
      ⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩)
    (by intro b; cases b; rfl)

private instance : Encodable SearchCursor :=
  Encodable.ofLeftInverse
    (fun c => (c.next,c.box))
    (fun p : ℕ × SourcedBox => ⟨p.1,p.2⟩)
    (by intro c; cases c; rfl)

abbrev CheckpointByte := Fin 256

def encodeNatBytes (n : ℕ) : List CheckpointByte :=
  (Nat.digits 256 n).attach.map fun d =>
    ⟨d.1,Nat.digits_lt_base (by omega) d.2⟩

def decodeNatBytes (bytes : List CheckpointByte) : ℕ :=
  Nat.ofDigits 256 (bytes.map Fin.val)

theorem encodeNatBytes_values (n : ℕ) :
    (encodeNatBytes n).map Fin.val = Nat.digits 256 n := by
  simp [encodeNatBytes]

theorem decodeNatBytes_encode (n : ℕ) :
    decodeNatBytes (encodeNatBytes n) = n := by
  simp [decodeNatBytes,encodeNatBytes_values,Nat.ofDigits_digits]

def encodeCursorBytes (c : SearchCursor) : List CheckpointByte :=
  encodeNatBytes (Encodable.encode c)

/-- Reject noncanonical byte strings and natural-number codes outside the
image of the cursor encoder. -/
def decodeCursorBytes (bytes : List CheckpointByte) : Option SearchCursor :=
  let n := decodeNatBytes bytes
  if bytes = encodeNatBytes n then Encodable.decode₂ SearchCursor n else none

theorem decodeCursorBytes_encode (c : SearchCursor) :
    decodeCursorBytes (encodeCursorBytes c) = some c := by
  simp [decodeCursorBytes,encodeCursorBytes,decodeNatBytes_encode,
    Encodable.decode₂_encode]

theorem decodeCursorBytes_sound (bytes : List CheckpointByte) (c : SearchCursor)
    (h : decodeCursorBytes bytes = some c) : bytes = encodeCursorBytes c := by
  change (if bytes = encodeNatBytes (decodeNatBytes bytes) then
    Encodable.decode₂ SearchCursor (decodeNatBytes bytes) else none) = some c at h
  split_ifs at h with hc
  · have he := (Encodable.decode₂_eq_some).mp h
    simpa [encodeCursorBytes,he] using hc

theorem decodeCursorBytes_iff (bytes : List CheckpointByte) (c : SearchCursor) :
    decodeCursorBytes bytes = some c ↔ bytes = encodeCursorBytes c := by
  constructor
  · exact decodeCursorBytes_sound bytes c
  · intro h
    rw [h]
    exact decodeCursorBytes_encode c

theorem decodeCursorBytes_noncanonical (bytes : List CheckpointByte)
    (h : bytes ≠ encodeNatBytes (decodeNatBytes bytes)) :
    decodeCursorBytes bytes = none := by
  simp [decodeCursorBytes,h]

theorem encodeCursorBytes_injective : Function.Injective encodeCursorBytes := by
  intro a b h
  have ha := decodeCursorBytes_encode a
  have hb := decodeCursorBytes_encode b
  rw [h] at ha
  exact Option.some.inj (ha.symm.trans hb)

theorem malformed_zero_padding_rejected :
    decodeCursorBytes ([⟨0,by decide⟩] : List CheckpointByte) = none := by
  decide +kernel

def saveActiveBytes {r : ProbeStream} (s : TrustedSession r) :
    Option (List CheckpointByte) :=
  (saveActiveCursor s).map encodeCursorBytes

theorem saveActiveBytes_output {r : ProbeStream} (s : TrustedSession r)
    (bytes : List CheckpointByte) (h : saveActiveBytes s = some bytes) :
    ∃ c : SearchCursor,
      saveActiveCursor s = some c ∧ bytes = encodeCursorBytes c := by
  unfold saveActiveBytes at h
  cases hc : saveActiveCursor s with
  | none => simp [hc] at h
  | some c =>
    simp only [hc,Option.map_some,Option.some.injEq] at h
    exact ⟨c,rfl,h.symm⟩

def restoreActiveBytesCounted (r : ProbeStream) (bytes : List CheckpointByte) :
    Option (TrustedSession r) × ℕ × ℕ :=
  match decodeCursorBytes bytes with
  | none => (none,0,0)
  | some c => importTrustedSessionCounted r c

theorem restoreActiveBytesCounted_of_decode (r : ProbeStream)
    (bytes : List CheckpointByte) (c : SearchCursor)
    (h : decodeCursorBytes bytes = some c) :
    restoreActiveBytesCounted r bytes = importTrustedSessionCounted r c := by
  simp [restoreActiveBytesCounted,h]

theorem restoreActiveBytesCounted_noncanonical (r : ProbeStream)
    (bytes : List CheckpointByte)
    (h : bytes ≠ encodeNatBytes (decodeNatBytes bytes)) :
    restoreActiveBytesCounted r bytes = (none,0,0) := by
  simp [restoreActiveBytesCounted,decodeCursorBytes_noncanonical bytes h]

theorem encodedCursor_restore_iff (r : ProbeStream) (c : SearchCursor) :
    (restoreActiveBytesCounted r (encodeCursorBytes c)).1.isSome = true ↔
      CursorMatches r c := by
  rw [restoreActiveBytesCounted_of_decode r _ c (decodeCursorBytes_encode c)]
  exact importTrustedSessionCounted_isSome r c

theorem encodedCursor_restore_cost (r : ProbeStream) (c : SearchCursor) :
    (restoreActiveBytesCounted r (encodeCursorBytes c)).2 = (8*c.next,1) := by
  rw [restoreActiveBytesCounted_of_decode r _ c (decodeCursorBytes_encode c)]
  exact importedSchedule_validation_once r c

theorem encoded_forged_cursor_rejected (r : ProbeStream) (c : SearchCursor)
    (h : ¬ CursorMatches r c) :
    (restoreActiveBytesCounted r (encodeCursorBytes c)).1.isSome = false := by
  cases hv : (restoreActiveBytesCounted r (encodeCursorBytes c)).1.isSome with
  | false => rfl
  | true => exact False.elim (h ((encodedCursor_restore_iff r c).mp hv))

theorem saveActiveBytes_restores {r : ProbeStream} (s : TrustedSession r)
    (bytes : List CheckpointByte) (h : saveActiveBytes s = some bytes) :
    (restoreActiveBytesCounted r bytes).1.isSome = true := by
  obtain ⟨c,hc,hb⟩ := saveActiveBytes_output s bytes h
  rw [hb,restoreActiveBytesCounted_of_decode r _ c (decodeCursorBytes_encode c)]
  exact saveActiveCursor_accepts s c hc

theorem restoredActiveBytes_observation (r : ProbeStream)
    (s restored : TrustedSession r) (bytes : List CheckpointByte)
    (fuels : List ℕ) (hs : saveActiveBytes s = some bytes)
    (hr : (restoreActiveBytesCounted r bytes).1 = some restored) :
    (fuels.foldl (stepTrustedSession r) s).out.1.found =
        (fuels.foldl (stepTrustedSession r) restored).out.1.found ∧
    (fuels.foldl (stepTrustedSession r) s).out.1.cursor =
        (fuels.foldl (stepTrustedSession r) restored).out.1.cursor := by
  obtain ⟨c,hc,hb⟩ := saveActiveBytes_output s bytes hs
  rw [hb,restoreActiveBytesCounted_of_decode r _ c (decodeCursorBytes_encode c)] at hr
  exact restoredActive_observation r s restored c fuels hc hr

theorem restoredActiveBytes_certificates (r : ProbeStream)
    (s restored : TrustedSession r) (bytes : List CheckpointByte)
    (fuels : List ℕ) (hs : saveActiveBytes s = some bytes)
    (hr : (restoreActiveBytesCounted r bytes).1 = some restored) :
    (sharedResultExport (fuels.foldl (stepTrustedSession r) s).out).1 =
      (sharedResultExport (fuels.foldl (stepTrustedSession r) restored).out).1 := by
  have ho := restoredActiveBytes_observation r s restored bytes fuels hs hr
  exact sharedResultExport_observation_congr _ _ ho.1 ho.2

theorem restoredActiveBytes_abstract_cost_bound (r : ProbeStream)
    (s restored : TrustedSession r) (bytes : List CheckpointByte)
    (fuels : List ℕ) (hs : saveActiveBytes s = some bytes)
    (hr : (restoreActiveBytesCounted r bytes).1 = some restored) :
    (restoreActiveBytesCounted r bytes).2.1 + endpointSearchTotal
      (fuels.foldl (stepTrustedSession r) restored).out +
    (sharedResultExport (fuels.foldl (stepTrustedSession r) restored).out).2.1 ≤
      8*s.out.1.cursor.next + 24*fuels.sum + 16 := by
  obtain ⟨c,hc,hb⟩ := saveActiveBytes_output s bytes hs
  have he := (saveActiveCursor_output s c hc).2.1
  rw [hb,restoreActiveBytesCounted_of_decode r _ c (decodeCursorBytes_encode c)] at hr ⊢
  rw [he]
  exact importedSchedule_accepted_bound r c restored fuels hr

set_option maxRecDepth 4096 in
theorem encoded_forged_cursor_regression :
    let r : ProbeStream := fun _ => (0,((0,0),(0,0)))
    let forged : SearchCursor := ⟨1,initialSourcedBox⟩
    (restoreActiveBytesCounted r (encodeCursorBytes forged)).1.isSome = false := by
  apply encoded_forged_cursor_rejected
  unfold CursorMatches
  decide +kernel


end Nullivance.Recognition
