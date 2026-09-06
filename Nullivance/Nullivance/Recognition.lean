import Nullivance.Generative

/-! Observation-relative recognition: a specification layer, not a claim about
consciousness. Exact recognition means a predicate is recoverable from the
given observation. Existence of a Prop-valued decoder is not computability.
The original logic never imports this optional extension. -/
namespace Nullivance.Recognition

universe u v w

def Recognizable {S : Type u} {O : Type v} (observe : S → O) (P : S → Prop) : Prop :=
  ∃ decode : O → Prop, ∀ s, decode (observe s) ↔ P s

/-- Necessary and sufficient condition: the requested distinction must not
split two states that the observation identifies. -/
theorem recognizable_iff_fiber_constant {S : Type u} {O : Type v}
    (observe : S → O) (P : S → Prop) :
    Recognizable observe P ↔ ∀ s t, observe s = observe t → (P s ↔ P t) := by
  constructor
  · rintro ⟨decode, hdecode⟩ s t he
    rw [← hdecode s, ← hdecode t, he]
  · intro hc
    refine ⟨fun o => ∃ s, observe s = o ∧ P s, ?_⟩
    intro s
    constructor
    · rintro ⟨t, he, hp⟩
      exact (hc t s he).mp hp
    · intro hp
      exact ⟨s, rfl, hp⟩

theorem not_recognizable_of_indistinguishable {S : Type u} {O : Type v}
    (observe : S → O) (P : S → Prop) (s t : S)
    (he : observe s = observe t) (hs : P s) (ht : ¬ P t) :
    ¬ Recognizable observe P := by
  intro hr
  exact ht (((recognizable_iff_fiber_constant observe P).mp hr s t he).mp hs)

/-- Processing an observation cannot repair distinctions it has already lost. -/
theorem recognizable_of_postprocess {S : Type u} {O : Type v} {R : Type w}
    (observe : S → O) (process : O → R) (P : S → Prop)
    (hr : Recognizable (process ∘ observe) P) : Recognizable observe P := by
  obtain ⟨decode, hd⟩ := hr
  exact ⟨decode ∘ process, hd⟩

/-- Direct consequence for the existing alpha/Theta generative layer.
At least one admitted frame has no exact quasivance decoder from init alone. -/
theorem exists_frame_quasivance_not_recognizable :
    ∃ F : Generative.GenFrame,
      ¬ Recognizable (Generative.GenState.init (F := F)) Generative.GenState.Quasivant := by
  obtain ⟨F, s, t, hs, ht, he⟩ := Generative.init_not_injective
  exact ⟨F, not_recognizable_of_indistinguishable _ _ s t he hs ht⟩

/-- Adding observations can preserve recognition of an existing distinction. -/
theorem recognizable_with_extra_observation {S : Type u} {O : Type v} {R : Type w}
    (observe : S → O) (extra : S → R) (P : S → Prop)
    (hr : Recognizable observe P) :
    Recognizable (fun s => (observe s, extra s)) P := by
  obtain ⟨decode, hd⟩ := hr
  exact ⟨fun p => decode p.1, hd⟩

/-- A test family supplies sufficient information exactly when every pair
disagreeing on P is separated by at least one test. This is an information
criterion, not a terminating test-selection algorithm. -/
theorem recognizable_tests_iff_separates {S : Type u} {O : Type v} {E : Type w}
    (test : E → S → O) (P : S → Prop) :
    Recognizable (fun s e => test e s) P ↔
      ∀ s t, ¬ (P s ↔ P t) → ∃ e, test e s ≠ test e t := by
  classical
  rw [recognizable_iff_fiber_constant]
  constructor
  · intro hc s t hp
    by_contra h
    push Not at h
    exact hp (hc s t (funext h))
  · intro hs s t he
    by_contra hp
    obtain ⟨e, hne⟩ := hs s t hp
    exact hne (congrFun he e)

def ObservationStable {S : Type u} {O : Type v}
    (observe : S → O) (step : S → S) : Prop :=
  ∀ s t, observe s = observe t → observe (step s) = observe (step t)

/-- Criterion for a deterministic next-observation rule that depends only on
the current observation. The existence proof uses choice, not an algorithm. -/
theorem observationStable_iff_next_rule {S : Type u} {O : Type v} [Nonempty O]
    (observe : S → O) (step : S → S) :
    ObservationStable observe step ↔ ∃ next : O → O,
      ∀ s, observe (step s) = next (observe s) := by
  classical
  constructor
  · intro hs
    let next : O → O := fun o =>
      if h : ∃ s, observe s = o then observe (step (Classical.choose h))
      else Classical.choice inferInstance
    refine ⟨next, ?_⟩
    intro s
    have hex : ∃ t, observe t = observe s := ⟨s, rfl⟩
    dsimp only [next]
    rw [dif_pos hex]
    exact hs s (Classical.choose hex) (Classical.choose_spec hex).symm
  · rintro ⟨next, hn⟩ s t he
    rw [hn s, hn t, he]

def evolve {S : Type u} (step : S → S) : Nat → S → S
  | 0, s => s
  | n+1, s => step (evolve step n s)

theorem stable_evolution_indistinguishable {S : Type u} {O : Type v}
    (observe : S → O) (step : S → S) (hs : ObservationStable observe step)
    (s t : S) (he : observe s = observe t) (n : Nat) :
    observe (evolve step n s) = observe (evolve step n t) := by
  induction n with
  | zero => exact he
  | succ n ih => exact hs _ _ ih

/-- Even an entire infinite observation trace cannot reveal an initial
distinction if the dynamics preserve observation equivalence. -/
theorem stable_history_no_recognition {S : Type u} {O : Type v}
    (observe : S → O) (step : S → S) (hs : ObservationStable observe step)
    (P : S → Prop) (s t : S) (he : observe s = observe t) (hp : P s) (hn : ¬ P t) :
    ¬ Recognizable (fun s n => observe (evolve step n s)) P := by
  apply not_recognizable_of_indistinguishable _ P s t _ hp hn
  exact funext (stable_evolution_indistinguishable observe step hs s t he)

/-- The loss of quasivance is universal over admitted frames, not just a
feature of the canonical geometric-mean example. -/
theorem every_frame_silent_ambiguity (F : Generative.GenFrame) :
    ∃ s t : Generative.GenState F,
      s.Quasivant ∧ ¬ t.Quasivant ∧ s.init = t.init := by
  let polar : Generative.Channel F :=
    ⟨0, fun _ => 0, ⟨le_refl _, by norm_num⟩, fun _ => ⟨le_refl _, by norm_num⟩⟩
  let neutral : Generative.Channel F :=
    ⟨0, Generative.neutralΘ F, ⟨le_refl _, by norm_num⟩,
      fun _ => ⟨by norm_num [Generative.neutralΘ], by norm_num [Generative.neutralΘ]⟩⟩
  have hp : polar.Quasivant := by
    refine ⟨rfl, ?_⟩
    intro he
    have h := congrFun he ⟨0, F.d_pos⟩
    norm_num [polar, Generative.neutralΘ] at h
  refine ⟨⟨polar, polar⟩, ⟨neutral, neutral⟩, ⟨hp, hp⟩, ?_, ?_⟩
  · intro hn
    exact hn.1.2 rfl
  · simp [Generative.GenState.init, Generative.Channel.eff, polar, neutral]

theorem quasivance_not_recognizable (F : Generative.GenFrame) :
    ¬ Recognizable (Generative.GenState.init (F := F)) Generative.GenState.Quasivant := by
  obtain ⟨s, t, hp, hn, he⟩ := every_frame_silent_ambiguity F
  exact not_recognizable_of_indistinguishable _ _ s t he hp hn

theorem quasivance_not_recognizable_after_processing (F : Generative.GenFrame)
    {R : Type u} (process : Continuous.TruthObj → R) :
    ¬ Recognizable (process ∘ Generative.GenState.init (F := F))
      Generative.GenState.Quasivant := by
  intro hr
  exact quasivance_not_recognizable F (recognizable_of_postprocess _ process _ hr)

theorem quasivance_stable_history_impossible (F : Generative.GenFrame)
    (step : Generative.GenState F → Generative.GenState F)
    (hs : ObservationStable Generative.GenState.init step) :
    ¬ Recognizable (fun s n => (evolve step n s).init) Generative.GenState.Quasivant := by
  obtain ⟨s, t, hp, hn, he⟩ := every_frame_silent_ambiguity F
  exact stable_history_no_recognition _ step hs _ s t he hp hn

/- A finite constructive toy model: interaction exposes a previously hidden bit.
This is not an implementation of alpha/Theta dynamics or biological cognition. -/
def toyObserve (s : Bool × Bool) : Bool := s.1
def toyStep (s : Bool × Bool) : Bool × Bool := (s.2, s.1)
def toyHidden (s : Bool × Bool) : Prop := s.2 = true

theorem toy_hidden_not_initially_recognizable : ¬ Recognizable toyObserve toyHidden := by
  exact not_recognizable_of_indistinguishable _ _ (false, true) (false, false)
    rfl rfl (by simp [toyHidden])

theorem toy_hidden_recognizable_after_interaction :
    Recognizable (fun s => toyObserve (toyStep s)) toyHidden := by
  exact ⟨fun b => b = true, fun _ => Iff.rfl⟩

theorem toy_step_not_observation_stable : ¬ ObservationStable toyObserve toyStep := by
  intro hs
  have h := hs (false, true) (false, false) rfl
  cases h

/-- A proposed factive knowledge layer: P holds in every state compatible with
the observation. This is NOT the existing four-valued evidence consequence. -/
def Known {S : Type u} {O : Type v} (observe : S → O) (P : S → Prop) (s : S) : Prop :=
  ∀ t, observe t = observe s → P t

theorem known_factive {S : Type u} {O : Type v} (observe : S → O) (P : S → Prop)
    (s : S) (h : Known observe P s) : P s := h s rfl

theorem known_no_contradiction {S : Type u} {O : Type v}
    (observe : S → O) (P : S → Prop) (s : S) :
    ¬ (Known observe P s ∧ Known observe (fun t => ¬ P t) s) := by
  rintro ⟨hp, hn⟩
  exact known_factive _ _ _ hn (known_factive _ _ _ hp)

theorem known_with_extra_observation {S : Type u} {O : Type v} {R : Type w}
    (observe : S → O) (extra : S → R) (P : S → Prop) (s : S)
    (h : Known observe P s) : Known (fun t => (observe t, extra t)) P s := by
  intro t he
  exact h t (congrArg Prod.fst he)

theorem recognizable_iff_known_complete {S : Type u} {O : Type v}
    (observe : S → O) (P : S → Prop) :
    Recognizable observe P ↔ ∀ s, Known observe P s ↔ P s := by
  rw [recognizable_iff_fiber_constant]
  constructor
  · intro hc s
    refine ⟨known_factive _ _ _, ?_⟩
    intro hp t he
    exact (hc t s he).mpr hp
  · intro hc s t he
    constructor
    · intro hp
      exact (hc s).mpr hp t he.symm
    · intro hp
      exact (hc t).mpr hp s he

end Nullivance.Recognition
