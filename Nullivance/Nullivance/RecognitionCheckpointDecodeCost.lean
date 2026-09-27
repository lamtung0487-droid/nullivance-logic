import Nullivance.RecognitionCheckpointEnvelope

/-! A scoped accounting for the base-256 fold only. It does not count the
generic `Encodable.decode₂`, canonicality re-encoding, or machine bit costs. -/
namespace Nullivance.Recognition

def decodeNatBytesCounted : List CheckpointByte → ℕ × ℕ
  | [] => (0,0)
  | b :: bs =>
      let tail := decodeNatBytesCounted bs
      (b.val + 256 * tail.1,tail.2 + 1)

theorem decodeNatBytesCounted_spec (bytes : List CheckpointByte) :
    decodeNatBytesCounted bytes = (decodeNatBytes bytes,bytes.length) := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
    simp [decodeNatBytesCounted,decodeNatBytes,Nat.ofDigits,ih]

theorem decodeNatBytes_lt_pow (bytes : List CheckpointByte) :
    decodeNatBytes bytes < 256 ^ bytes.length := by
  unfold decodeNatBytes
  have h : ∀ x ∈ bytes.map Fin.val, x < 256 := by
    intro x hx
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
    exact b.isLt
  simpa using Nat.ofDigits_lt_base_pow_length (by omega : 1 < 256) h

theorem decodeNatBytesCounted_cost (bytes : List CheckpointByte) :
    (decodeNatBytesCounted bytes).2 = bytes.length := by
  rw [decodeNatBytesCounted_spec]

theorem decodeNatBytesCounted_value_bound (bytes : List CheckpointByte) :
    (decodeNatBytesCounted bytes).1 < 256 ^ bytes.length := by
  rw [decodeNatBytesCounted_spec]
  exact decodeNatBytes_lt_pow bytes

theorem unwrapCheckpointBytes_size (maxBytes : ℕ) (bytes : ByteArray)
    (payload : List CheckpointByte)
    (h : unwrapCheckpointBytes maxBytes bytes = some payload) :
    3 + payload.length = bytes.size ∧ bytes.size ≤ maxBytes := by
  unfold unwrapCheckpointBytes at h
  split_ifs at h with hsize
  · split at h
    · rename_i x rest heq
      have hl := congrArg List.length heq
      have hp := congrArg List.length (Option.some.inj h)
      have hs : bytes.size = bytes.data.toList.length := by
        simp [ByteArray.size_data]
      simp only [List.length_cons,List.length_map] at hl hp
      constructor <;> omega
    all_goals simp_all

theorem unwrapCheckpointBytes_length_le (maxBytes : ℕ) (bytes : ByteArray)
    (payload : List CheckpointByte)
    (h : unwrapCheckpointBytes maxBytes bytes = some payload) :
    payload.length ≤ maxBytes := by
  have hs := unwrapCheckpointBytes_size maxBytes bytes payload h
  omega

theorem unwrapCheckpointBytes_counted_bounds (maxBytes : ℕ) (bytes : ByteArray)
    (payload : List CheckpointByte)
    (h : unwrapCheckpointBytes maxBytes bytes = some payload) :
    (decodeNatBytesCounted payload).2 ≤ maxBytes - 3 ∧
    (decodeNatBytesCounted payload).1 < 256 ^ (maxBytes - 3) := by
  have hs := unwrapCheckpointBytes_size maxBytes bytes payload h
  have hlen : payload.length ≤ maxBytes - 3 := by omega
  constructor
  · rw [decodeNatBytesCounted_cost]
    exact hlen
  · exact (decodeNatBytesCounted_value_bound payload).trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 256) hlen)

theorem decode_nat_cost_regression :
    decodeNatBytesCounted [] = (0,0) ∧
    decodeNatBytesCounted [⟨255,by decide⟩] = (255,1) ∧
    decodeNatBytesCounted [⟨0,by decide⟩,⟨1,by decide⟩] = (256,2) := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Nullivance.Recognition
