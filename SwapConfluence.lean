/-
  Mechanized companion to "Markets as Rewriting Systems" (Lean 4 core, no Mathlib).

  Part I  (namespace `ARS`): abstract reduction systems and **Newman's Lemma**
          (terminating + locally confluent ⟹ confluent) — the engine of Proposition 4.4.
  Part II (namespace `SwapConfluence`): the housing-market bilateral-swap dynamics, and the
          machine-checked **non-confluence example** of Section 4.2, stated with the same
          `Confluent` that Newman characterizes.

  Newman's Lemma and the example (Parts I-II) are axiom-free; the termination and
  locality results use only `propext` and `Quot.sound` (well-founded recursion), with
  no `sorry` and no choice (see `#print axioms`); atomic facts are closed by `decide`.
-/

/-! # Part I — Abstract reduction systems and Newman's Lemma -/

namespace ARS

variable {α : Type}

/-- Reflexive-transitive closure (tail-recursive form). -/
inductive Star (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : Star R a a
  | tail {a b c : α} : Star R a b → R b c → Star R a c

namespace Star

theorem single {R : α → α → Prop} {a b : α} (h : R a b) : Star R a b :=
  Star.tail (Star.refl a) h

theorem trans {R : α → α → Prop} {a b c : α}
    (h₁ : Star R a b) (h₂ : Star R b c) : Star R a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hbc ih => exact Star.tail ih hbc

theorem head {R : α → α → Prop} {a b c : α} (h : R a b) (hbc : Star R b c) : Star R a c :=
  trans (single h) hbc

/-- Head decomposition: a reduction sequence is empty, or takes a first step. -/
theorem cases_head {R : α → α → Prop} {a c : α} (h : Star R a c) :
    a = c ∨ ∃ b, R a b ∧ Star R b c := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hab hbc ih =>
    cases ih with
    | inl he => subst he; exact Or.inr ⟨_, hbc, Star.refl _⟩
    | inr hex => cases hex with
      | intro d hd => exact Or.inr ⟨d, hd.1, Star.tail hd.2 hbc⟩

end Star

/-- Two states reduce to a common one. -/
def Joinable (R : α → α → Prop) (b c : α) : Prop := ∃ d, Star R b d ∧ Star R c d

/-- Confluence (Church–Rosser): any two reducts of a common source are joinable. -/
def Confluent (R : α → α → Prop) : Prop :=
  ∀ a b c, Star R a b → Star R a c → Joinable R b c

/-- Local (weak) confluence: single-step divergences are joinable. -/
def LocallyConfluent (R : α → α → Prop) : Prop :=
  ∀ a b c, R a b → R a c → Joinable R b c

/-- Termination (strong normalization): no infinite forward chain. -/
def Terminating (R : α → α → Prop) : Prop := WellFounded (fun x y => R y x)

/-- **Newman's Lemma.** A terminating, locally confluent ARS is confluent. -/
theorem newman (R : α → α → Prop)
    (hT : Terminating R) (hWCR : LocallyConfluent R) : Confluent R := by
  intro a
  refine hT.induction (C := fun a => ∀ b c, Star R a b → Star R a c → Joinable R b c) a ?_
  intro a ih b c hab hac
  cases Star.cases_head hab with
  | inl hb =>
    subst hb; exact ⟨c, hac, Star.refl c⟩
  | inr hbex => cases hbex with
    | intro b₁ hb₁ =>
      cases Star.cases_head hac with
      | inl hc =>
        subst hc; exact ⟨b, Star.refl b, hab⟩
      | inr hcex => cases hcex with
        | intro c₁ hc₁ =>
          cases hWCR a b₁ c₁ hb₁.1 hc₁.1 with
          | intro d hd =>
            cases ih b₁ hb₁.1 b d hb₁.2 hd.1 with
            | intro e he =>
              have hc₁e : Star R c₁ e := Star.trans hd.2 he.2
              cases ih c₁ hc₁.1 c e hc₁.2 hc₁e with
              | intro f hf => exact ⟨f, Star.trans he.1 hf.2, hf.1⟩

end ARS

/-! # Part II — Bilateral-swap dynamics and the non-confluence example (Section 4.2) -/

namespace SwapConfluence

open ARS

inductive Agent | a1 | a2 | a3
  deriving DecidableEq, Repr
inductive Obj | x | y | z
  deriving DecidableEq, Repr

open Agent Obj

/-- An allocation: `(holding of a1, holding of a2, holding of a3)`. -/
abbrev Alloc := Obj × Obj × Obj

def get (π : Alloc) : Agent → Obj
  | a1 => π.1
  | a2 => π.2.1
  | a3 => π.2.2

/-- Additive valuations of the example (Section 4.2). -/
def v : Agent → Obj → Nat
  | a1, x => 1 | a1, y => 3 | a1, z => 2
  | a2, x => 3 | a2, y => 1 | a2, z => 2
  | a3, x => 3 | a3, y => 2 | a3, z => 1

/-- The allocation after agents `i` and `j` swap their holdings. -/
def swapPair (π : Alloc) (i j : Agent) : Alloc :=
  let f : Agent → Obj := fun k => if k = i then get π j else if k = j then get π i else get π k
  (f a1, f a2, f a3)

/-- A bilateral swap between `i` and `j` is improving if both strictly gain. -/
def improving (π : Alloc) (i j : Agent) : Prop :=
  i ≠ j ∧ v i (get π j) > v i (get π i) ∧ v j (get π i) > v j (get π j)

instance (π : Alloc) (i j : Agent) : Decidable (improving π i j) := by
  unfold improving; infer_instance

/-- One reduction step of the swap dynamics. -/
def Step (π σ : Alloc) : Prop := ∃ i j : Agent, improving π i j ∧ σ = swapPair π i j

/-- A normal form (swap-stable allocation): no improving swap exists. -/
def normalForm (π : Alloc) : Prop := ∀ i j : Agent, ¬ improving π i j

def omega : Alloc := (x, y, z)
def A     : Alloc := (y, x, z)
def C     : Alloc := (z, y, x)
def B     : Alloc := (y, z, x)

theorem step_omega_A : Step omega A := ⟨a1, a2, by decide⟩
theorem step_omega_C : Step omega C := ⟨a1, a3, by decide⟩
theorem step_C_B     : Step C B     := ⟨a1, a2, by decide⟩

theorem reach_A : Star Step omega A := Star.tail (Star.refl omega) step_omega_A
theorem reach_B : Star Step omega B :=
  Star.tail (Star.tail (Star.refl omega) step_omega_C) step_C_B

theorem normalForm_A : normalForm A := by intro i j; cases i <;> cases j <;> decide
theorem normalForm_B : normalForm B := by intro i j; cases i <;> cases j <;> decide

theorem normalForm_no_step {π σ : Alloc} (h : normalForm π) : ¬ Step π σ := by
  intro hs
  cases hs with
  | intro i hi => cases hi with
    | intro j hj => exact h i j hj.1

theorem star_from_normal {π σ : Alloc} (h : normalForm π) (hs : Star Step π σ) : σ = π := by
  induction hs with
  | refl => rfl
  | tail _ hbc ih => subst ih; exact absurd hbc (normalForm_no_step h)

theorem not_joinable_AB : ¬ Joinable Step A B := by
  intro hj
  cases hj with
  | intro d hd =>
    have hA : d = A := star_from_normal normalForm_A hd.1
    have hB : d = B := star_from_normal normalForm_B hd.2
    rw [hA] at hB
    exact absurd hB (by decide)

/-- **Main result.** The bilateral-swap dynamics is not confluent: decentralized trade can
    reach distinct stable outcomes depending on the order of transactions. -/
theorem swap_dynamics_not_confluent : ¬ Confluent Step := by
  intro hc
  exact not_joinable_AB (hc omega A B reach_A reach_B)

theorem nonconfluence_witness :
    ∃ p q : Alloc,
      Star Step omega p ∧ Star Step omega q ∧
      normalForm p ∧ normalForm q ∧ p ≠ q :=
  ⟨A, B, reach_A, reach_B, normalForm_A, normalForm_B, by decide⟩

/-! ## Termination, and non-confluence is necessarily local (Newman's contrapositive) -/

/-- Total realized utility. Each improving swap strictly increases it. -/
def tot (π : Alloc) : Nat := v a1 (get π a1) + v a2 (get π a2) + v a3 (get π a3)

theorem tot_le (π : Alloc) : tot π ≤ 9 := by
  cases π with
  | mk p1 q => cases q with
    | mk p2 p3 => cases p1 <;> cases p2 <;> cases p3 <;> decide

theorem step_tot {π σ : Alloc} (h : Step π σ) : tot π < tot σ := by
  cases h with
  | intro i hi => cases hi with
    | intro j hj =>
      have himp := hj.1
      rw [hj.2]
      revert himp
      cases π with
      | mk p1 q => cases q with
        | mk p2 p3 =>
          cases i <;> cases j <;> cases p1 <;> cases p2 <;> cases p3 <;>
            intro himp <;> first | exact absurd himp (by decide) | decide

/-- A strictly decreasing rank into `Nat`, bounded because utility is bounded. -/
def rank (π : Alloc) : Nat := 9 - tot π

theorem step_rank {π σ : Alloc} (h : Step π σ) : rank σ < rank π := by
  have h1 := step_tot h
  have h2 := tot_le σ
  unfold rank; omega

/-- The swap dynamics terminates: no infinite sequence of improving swaps. -/
theorem terminating_Step : Terminating Step :=
  Subrelation.wf (fun {x y} (h : Step y x) => step_rank h) (measure rank).wf

/-- **Non-confluence is local.** Since the swap dynamics terminates, by Newman's Lemma it
    cannot be locally confluent (else it would be confluent, contradicting
    `swap_dynamics_not_confluent`). Hence its failure of order-independence is witnessed by a
    non-joinable critical pair, as analyzed in Section 4.2. -/
theorem swap_step_not_locallyConfluent : ¬ LocallyConfluent Step := by
  intro hWCR
  exact swap_dynamics_not_confluent (ARS.newman Step terminating_Step hWCR)

end SwapConfluence
