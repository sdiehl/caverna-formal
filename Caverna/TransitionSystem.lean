/-
  Caverna.TransitionSystem -- Labeled Transition Systems
  ======================================================

  Defines labeled transition systems (LTS) with reachability,
  invariant proofs, safety, simulation, and product composition.
-/

import Mathlib.Tactic

namespace TransitionSystem

structure LTS (State : Type) (Action : Type) where
  init : State → Prop
  trans : State → Action → State → Prop

variable {State Action : Type}

inductive Reachable (sys : LTS State Action) : State → Prop where
  | init : ∀ s, sys.init s → Reachable sys s
  | step : ∀ s a s', Reachable sys s → sys.trans s a s' → Reachable sys s'

def InvariantHolds (sys : LTS State Action) (inv : State → Prop) : Prop :=
  ∀ s, Reachable sys s → inv s

def Safety (sys : LTS State Action) (bad : State → Prop) : Prop :=
  ∀ s, Reachable sys s → ¬bad s

def Liveness (sys : LTS State Action) (good : State → Prop) : Prop :=
  ∀ s, Reachable sys s → ∃ s', Reachable sys s' ∧ good s'

def Deterministic (sys : LTS State Action) : Prop :=
  ∀ s a s₁ s₂, sys.trans s a s₁ → sys.trans s a s₂ → s₁ = s₂

def Enabled (sys : LTS State Action) (s : State) (a : Action) : Prop :=
  ∃ s', sys.trans s a s'

def Terminal (sys : LTS State Action) (s : State) : Prop :=
  ∀ a, ¬Enabled sys s a

structure Inductive (sys : LTS State Action) (inv : State → Prop) : Prop where
  base : ∀ s, sys.init s → inv s
  step : ∀ s a s', inv s → sys.trans s a s' → inv s'

theorem inductive_implies_invariant (sys : LTS State Action) (inv : State → Prop) :
    Inductive sys inv → InvariantHolds sys inv := by
  intro h s h_reach
  induction h_reach with
  | init s h_init => exact h.base s h_init
  | step s a s' _ h_trans ih => exact h.step s a s' ih h_trans

theorem invariant_induction (sys : LTS State Action) (inv : State → Prop)
    (h_init : ∀ s, sys.init s → inv s)
    (h_step : ∀ s a s', inv s → sys.trans s a s' → inv s') :
    InvariantHolds sys inv :=
  inductive_implies_invariant sys inv ⟨h_init, h_step⟩

theorem conjunction_preserved (sys : LTS State Action) (inv₁ inv₂ : State → Prop) :
    InvariantHolds sys inv₁ →
    InvariantHolds sys inv₂ →
    InvariantHolds sys (fun s => inv₁ s ∧ inv₂ s) :=
  fun h₁ h₂ s h_reach => ⟨h₁ s h_reach, h₂ s h_reach⟩

theorem terminal_no_transitions (sys : LTS State Action) (s : State) :
    Terminal sys s → ∀ a s', ¬sys.trans s a s' := by
  intro h_term a s' h_trans
  exact h_term a ⟨s', h_trans⟩

section Simulation

variable {State₁ State₂ : Type}

structure Simulation (sys₁ : LTS State₁ Action) (sys₂ : LTS State₂ Action)
    (R : State₁ → State₂ → Prop) : Prop where
  init : ∀ s₁, sys₁.init s₁ → ∃ s₂, sys₂.init s₂ ∧ R s₁ s₂
  step : ∀ s₁ s₂ a s₁', R s₁ s₂ → sys₁.trans s₁ a s₁' →
    ∃ s₂', sys₂.trans s₂ a s₂' ∧ R s₁' s₂'

def Bisimulation (sys₁ : LTS State₁ Action) (sys₂ : LTS State₂ Action)
    (R : State₁ → State₂ → Prop) : Prop :=
  Simulation sys₁ sys₂ R ∧ Simulation sys₂ sys₁ (fun s₂ s₁ => R s₁ s₂)

end Simulation

section Product

variable {State₁ State₂ : Type}

def product (sys₁ : LTS State₁ Action) (sys₂ : LTS State₂ Action) :
    LTS (State₁ × State₂) Action where
  init := fun (s₁, s₂) => sys₁.init s₁ ∧ sys₂.init s₂
  trans := fun (s₁, s₂) a (s₁', s₂') => sys₁.trans s₁ a s₁' ∧ sys₂.trans s₂ a s₂'

theorem product_deterministic (sys₁ : LTS State₁ Action) (sys₂ : LTS State₂ Action)
    (h₁ : Deterministic sys₁) (h₂ : Deterministic sys₂) :
    Deterministic (product sys₁ sys₂) := by
  intro ⟨s₁, s₂⟩ a ⟨s₁', s₂'⟩ ⟨s₁'', s₂''⟩ ⟨ht₁, ht₂⟩ ⟨ht₁', ht₂'⟩
  exact Prod.mk.injEq .. |>.mpr ⟨h₁ _ _ _ _ ht₁ ht₁', h₂ _ _ _ _ ht₂ ht₂'⟩

end Product

section Enumeration

structure FiniteEnumeration (α : Type) where
  all : List α
  complete : ∀ a : α, a ∈ all

def FiniteEnumeration.size {α : Type} (enum : FiniteEnumeration α) : Nat :=
  enum.all.length

theorem FiniteEnumeration.mem_all {α : Type} (enum : FiniteEnumeration α) (a : α) :
    a ∈ enum.all := enum.complete a

end Enumeration

section SafetyCombinators

variable {State Action : Type}

theorem safety_from_invariant (sys : LTS State Action) (inv bad : State → Prop)
    (h_inv : InvariantHolds sys inv)
    (h_disjoint : ∀ s, inv s → ¬bad s) :
    Safety sys bad :=
  fun s h_reach => h_disjoint s (h_inv s h_reach)

theorem safety_by_induction (sys : LTS State Action) (bad : State → Prop)
    (h_init : ∀ s, sys.init s → ¬bad s)
    (h_step : ∀ s a s', ¬bad s → sys.trans s a s' → ¬bad s') :
    Safety sys bad := by
  intro s h_reach
  induction h_reach with
  | init s h => exact h_init s h
  | step s a s' _ h_trans ih => exact h_step s a s' ih h_trans

theorem disjunction_preserved (sys : LTS State Action) (inv₁ inv₂ : State → Prop)
    (h₁ : ∀ s, sys.init s → inv₁ s ∨ inv₂ s)
    (h₂ : ∀ s a s', (inv₁ s ∨ inv₂ s) → sys.trans s a s' → inv₁ s' ∨ inv₂ s') :
    InvariantHolds sys (fun s => inv₁ s ∨ inv₂ s) :=
  invariant_induction sys (fun s => inv₁ s ∨ inv₂ s) h₁ h₂

theorem invariant_weakening (sys : LTS State Action) (inv₁ inv₂ : State → Prop)
    (h_impl : ∀ s, inv₁ s → inv₂ s)
    (h_inv : InvariantHolds sys inv₁) :
    InvariantHolds sys inv₂ :=
  fun s h_reach => h_impl s (h_inv s h_reach)

end SafetyCombinators

end TransitionSystem
