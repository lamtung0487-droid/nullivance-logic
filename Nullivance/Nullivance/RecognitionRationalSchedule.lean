import Nullivance.RecognitionSeparationStopping

/-! Computable reciprocal-error stopping budget from a supplied rational margin. -/
namespace Nullivance.Recognition
open Generative Continuous

def reciprocalMarginIndex (delta : ℚ) : ℕ := ⌊2 / delta⌋₊
def reciprocalMarginFuel (delta : ℚ) : ℕ := reciprocalMarginIndex delta + 2

theorem reciprocalMarginIndex_strict (delta : ℚ) (hd : 0 < delta) :
    2 * (1 / ((reciprocalMarginIndex delta : ℚ) + 1)) < delta := by
  have hf := Nat.lt_floor_add_one (2 / delta)
  have hx : 2 < ((reciprocalMarginIndex delta : ℚ) + 1) * delta :=
    (div_lt_iff₀ hd).mp hf
  have hn : (0 : ℚ) < (reciprocalMarginIndex delta : ℚ) + 1 := by positivity
  have hh := (div_lt_iff₀ hn).mpr (show (2 : ℚ) < delta *
    ((reciprocalMarginIndex delta : ℚ) + 1) by nlinarith)
  simpa only [mul_one_div] using hh

theorem reciprocal_schedule_margin (r : ProbeStream) (delta : ℚ) (hd : 0 < delta)
    (he : ∀ n, (r n).1 ≤ 1 / ((n : ℚ) + 1)) :
    2 * ((r (reciprocalMarginIndex delta)).1 : ℝ) < (delta : ℝ) := by
  have h := he (reciprocalMarginIndex delta)
  have hp := reciprocalMarginIndex_strict delta hd
  have hq : 2 * (r (reciprocalMarginIndex delta)).1 < delta := by linarith
  exact_mod_cast hq

theorem reciprocal_schedule_export (r : ProbeStream)
    (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (i : Fin 4) (hi : i = 0 ∨ i = 1) (delta : ℚ) (hd : 0 < delta)
    (hm : (delta : ℝ) ≤ realStateCoordinates s i)
    (he : ∀ n, (r n).1 ≤ 1 / ((n : ℚ) + 1)) :
    (resultRefutation (runEndpointSearch r (reciprocalMarginFuel delta))).isSome = true := by
  exact positive_margin_export_exists r s hs i hi delta (reciprocalMarginIndex delta)
    hm (reciprocal_schedule_margin r delta hd he)

theorem reciprocal_schedule_search (r : ProbeStream)
    (s : GenState scalarProbeFrame) (hs : StreamFits r s)
    (i : Fin 4) (hi : i = 0 ∨ i = 1) (delta : ℚ) (hd : 0 < delta)
    (hm : (delta : ℝ) ≤ realStateCoordinates s i)
    (he : ∀ n, (r n).1 ≤ 1 / ((n : ℚ) + 1)) :
    ∃ m, m ≤ reciprocalMarginIndex delta + 1 ∧
      (runEndpointSearch r (reciprocalMarginFuel delta)).1.found = some m := by
  exact positive_margin_search_budget r s hs i hi delta (reciprocalMarginIndex delta)
    hm (reciprocal_schedule_margin r delta hd he)

theorem reciprocal_schedule_order_budget (r : ProbeStream) (delta : ℚ) :
    searchExportOrderTotal (runEndpointSearch r (reciprocalMarginFuel delta)) ≤
      24 * (reciprocalMarginIndex delta + 2) + 10 :=
  searchExportOrderTotal_bound r (reciprocalMarginFuel delta)

theorem reciprocal_margin_budget_regression :
    [1,1/2,1/4,1/10].map reciprocalMarginFuel = [4,6,10,22] := by
  decide +kernel

/-- A total arithmetic function is not a termination guarantee at zero margin. -/
theorem reciprocal_zero_not_strict :
    ¬ (2 * (1 / ((reciprocalMarginIndex 0 : ℚ) + 1)) < 0) := by
  decide +kernel

end Nullivance.Recognition
