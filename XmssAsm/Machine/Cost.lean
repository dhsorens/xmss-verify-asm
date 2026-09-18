/-
  XmssAsm.Machine.Cost

  Step-counted execution. `Runs` says a region reaches its postcondition in
  *some* number of steps, which is what correctness needs. The benchmark
  needs the number itself, so `RunsN H s n Q` says the region reaches `Q` in
  *exactly* `n` steps of `stepH H`.

  This is how a cost claim becomes a theorem instead of an observation on
  fixtures. The two relations share the same step lemmas, so a cost proof is
  the same symbolic execution as a correctness proof with the count carried
  along; `RunsN.toRuns` discards the count.
-/

module

public import XmssAsm.Machine.Hash

@[expose] public section

namespace XmssAsm

open RiscvZkvm.Rv64

/-- From `s`, exactly `n` steps of `stepH H` reach a state satisfying `Q`. -/
def RunsN (H : List UInt8 → BitVec 256) (s : MachineState) (n : Nat)
    (Q : MachineState → Prop) : Prop :=
  ∃ s', (hashStepper H).iter n s = some s' ∧ Q s'

/-- The cost of a loop whose body cost depends on the iteration index. -/
def costSum (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => costSum c n + c n

@[simp] theorem costSum_zero (c : Nat → Nat) : costSum c 0 = 0 := rfl
@[simp] theorem costSum_succ (c : Nat → Nat) (n : Nat) :
    costSum c (n + 1) = costSum c n + c n := rfl

/-- A constant body cost. -/
theorem costSum_const (k n : Nat) : costSum (fun _ => k) n = n * k := by
  induction n with
  | zero => simp
  | succ n ih => rw [costSum_succ, ih, Nat.succ_mul]

/-- Body costs add termwise. -/
theorem costSum_add (c d : Nat → Nat) (n : Nat) :
    costSum (fun i => c i + d i) n = costSum c n + costSum d n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [costSum_succ, ih]; omega

theorem costSum_mul_left (k : Nat) (c : Nat → Nat) (n : Nat) :
    costSum (fun i => k * c i) n = k * costSum c n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [costSum_succ, ih]; rw [Nat.mul_add]

namespace RunsN

variable {H : List UInt8 → BitVec 256}

theorem done {s : MachineState} {Q : MachineState → Prop} (h : Q s) : RunsN H s 0 Q :=
  ⟨s, rfl, h⟩

theorem step {s s1 : MachineState} {n : Nat} {Q : MachineState → Prop}
    (h : stepH H s = some s1) (h2 : RunsN H s1 n Q) : RunsN H s (n + 1) Q := by
  obtain ⟨s', hk, hq⟩ := h2
  refine ⟨s', ?_, hq⟩
  rw [Decomp.Stepper.iter_succ]
  simp only [hashStepper_next, h, Option.bind_some, hk]

/-- One step, with the count written as a literal. The successor goal carries
    `n - 1`, which the symbolic-execution simp set reduces, so a cost proof
    reads exactly like a correctness proof. -/
theorem stepD {s s1 : MachineState} {n : Nat} {Q : MachineState → Prop} (hn : n ≠ 0)
    (h : stepH H s = some s1) (h2 : RunsN H s1 (n - 1) Q) : RunsN H s n Q := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simpa using step h h2

theorem mono {s : MachineState} {n : Nat} {Q Q' : MachineState → Prop}
    (h : RunsN H s n Q) (hQ : ∀ s', Q s' → Q' s') : RunsN H s n Q' := by
  obtain ⟨s', hk, hq⟩ := h
  exact ⟨s', hk, hQ s' hq⟩

/-- Sequential composition adds the counts. -/
theorem bind {s : MachineState} {n m : Nat} {Q R : MachineState → Prop}
    (h : RunsN H s n Q) (h2 : ∀ s', Q s' → RunsN H s' m R) : RunsN H s (n + m) R := by
  obtain ⟨s1, hk1, hq⟩ := h
  obtain ⟨s2, hk2, hR⟩ := h2 s1 hq
  exact ⟨s2, Decomp.Stepper.iter_add_eq hk1 hk2, hR⟩

/-- A count is a witness that the region runs at all. -/
theorem toRuns {s : MachineState} {n : Nat} {Q : MachineState → Prop}
    (h : RunsN H s n Q) : Runs H s Q := by
  obtain ⟨s', hk, hq⟩ := h
  exact ⟨s', ⟨n, hk⟩, hq⟩

/-- Bounded iteration with a per-iteration cost: the total is `costSum`. -/
theorem loopSum {Inv : Nat → MachineState → Prop} (c : Nat → Nat) (n : Nat)
    (hbody : ∀ i s, i < n → Inv i s → RunsN H s (c i) (Inv (i + 1))) :
    ∀ s, Inv 0 s → RunsN H s (costSum c n) (Inv n) := by
  induction n with
  | zero => intro s h; exact done h
  | succ n ih =>
    intro s h
    refine bind (ih (fun i s' hi hInv => hbody i s' (by omega) hInv) s h) ?_
    intro s' hInv
    exact hbody n s' (by omega) hInv

end RunsN

end XmssAsm
