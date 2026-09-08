/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Hofer's lemma

This is an elementary lemma about complete metric spaces. It is motivated by an
application to the bubbling-off analysis for holomorphic curves in symplectic topology.
We are *very* far away from having these applications, but the proof here is a nice
example of a proof needing to construct a sequence by induction in the middle of the proof.

## References:

* H. Hofer and C. Viterbo, *The Weinstein conjecture in the presence of holomorphic spheres*
-/

public section

open Topology Filter Finset

local notation "d" => dist

/-
**hofer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hofer {X : Type*} [MetricSpace X] [CompleteSpace X] (x : X) (ε : Real) (ε_
pos : 0 < ε) {ϕ : X -> Real} (cont : Continuous ϕ) (nonneg : forall y, 0 <= ϕ y)
 : exists ε' > 0, exists x' : X, ε' <= ε ∧ d x' x <= 2 * ε ∧ ε * ϕ x <= ε' * ϕ x
' ∧ forall y, d x' y <= ε' -> ϕ y <= 2 * ϕ x'
参数：x : X；ε : Real；ε_pos : 0 < ε；cont : Continuous ϕ；nonneg : forall y, 0 <= ϕ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `div_le_self`：div_le_self (ha : 0 <= a) (hb : 1 <= b) : a / b <= a
（共 112 条，此处仅展示前 30 条）
-/
theorem hofer {X : Type*} [MetricSpace X] [CompleteSpace X] (x : X) (ε : ℝ) (ε_pos : 0 < ε)
    {ϕ : X → ℝ} (cont : Continuous ϕ) (nonneg : ∀ y, 0 ≤ ϕ y) : ∃ ε' > 0, ∃ x' : X,
    ε' ≤ ε ∧ d x' x ≤ 2 * ε ∧ ε * ϕ x ≤ ε' * ϕ x' ∧ ∀ y, d x' y ≤ ε' → ϕ y ≤ 2 * ϕ x' := by
  by_contra! H
  have reformulation : ∀ (x') (k : ℕ), ε * ϕ x ≤ ε / 2 ^ k * ϕ x' ↔ 2 ^ k * ϕ x ≤ ϕ x' := by
    intro x' k
    rw [div_mul_eq_mul_div, le_div_iff₀, mul_assoc, mul_le_mul_iff_right₀ ε_pos, mul_comm]
    positivity
  -- Now let's specialize to `ε/2^k`
  replace H : ∀ k : ℕ, ∀ x', d x' x ≤ 2 * ε ∧ 2 ^ k * ϕ x ≤ ϕ x' →
      ∃ y, d x' y ≤ ε / 2 ^ k ∧ 2 * ϕ x' < ϕ y := by
    intro k x'
    have := H (ε / 2 ^ k) (by positivity) x' (div_le_self ε_pos.le <| one_le_pow₀ one_le_two)
    simpa [reformulation] using! this
  have : Nonempty X := ⟨x⟩
  choose! F hF using H
  -- Use the axiom of choice
  -- Now define u by induction starting at x, with u_{n+1} = F(n, u_n)
  let u : ℕ → X := fun n => Nat.recOn n x F
  -- The properties of F translate to properties of u
  have hu :
    ∀ n,
      d (u n) x ≤ 2 * ε ∧ 2 ^ n * ϕ x ≤ ϕ (u n) →
        d (u n) (u <| n + 1) ≤ ε / 2 ^ n ∧ 2 * ϕ (u n) < ϕ (u <| n + 1) := by
    exact fun n ↦ hF n (u n)
  -- Key properties of u, to be proven by induction
  have key : ∀ n, d (u n) (u (n + 1)) ≤ ε / 2 ^ n ∧ 2 * ϕ (u n) < ϕ (u (n + 1)) := by
    intro n
    induction n using Nat.case_strong_induction_on with
    | hz => simpa [u, ε_pos.le] using! hu 0
    | hi n IH =>
      have A : d (u (n + 1)) x ≤ 2 * ε := by
        rw [dist_comm]
        let r := range (n + 1) -- range (n+1) = {0, ..., n}
        calc
          d (u 0) (u (n + 1)) ≤ ∑ i ∈ r, d (u i) (u <| i + 1) := dist_le_range_sum_dist u (n + 1)
          _ ≤ ∑ i ∈ r, ε / 2 ^ i :=
            (sum_le_sum fun i i_in => (IH i <| Nat.lt_succ_iff.mp <| Finset.mem_range.mp i_in).1)
          _ = (∑ i ∈ r, (1 / 2 : ℝ) ^ i) * ε := by
            rw [Finset.sum_mul]
            simp
            field_simp
          _ ≤ 2 * ε := by gcongr; apply sum_geometric_two_le
      have B : 2 ^ (n + 1) * ϕ x ≤ ϕ (u (n + 1)) := by
        refine @geom_le (ϕ ∘ u) _ zero_le_two (n + 1) fun m hm => ?_
        exact (IH _ <| Nat.lt_add_one_iff.1 hm).2.le
      exact hu (n + 1) ⟨A, B⟩
  obtain ⟨key₁, key₂⟩ := forall_and.mp key
  -- Hence u is Cauchy
  have cauchy_u : CauchySeq u := by
    refine cauchySeq_of_le_geometric _ ε one_half_lt_one fun n => ?_
    simpa only [one_div, inv_pow] using! key₁ n
  -- So u converges to some y
  obtain ⟨y, limy⟩ : ∃ y, Tendsto u atTop (𝓝 y) := CompleteSpace.complete cauchy_u
  -- And ϕ ∘ u goes to +∞
  have lim_top : Tendsto (ϕ ∘ u) atTop atTop := by
    let v n := (ϕ ∘ u) (n + 1)
    suffices Tendsto v atTop atTop by rwa [tendsto_add_atTop_iff_nat] at this
    have hv₀ : 0 < v 0 := by
      calc
        0 ≤ 2 * ϕ (u 0) := by specialize nonneg x; positivity
        _ < ϕ (u (0 + 1)) := key₂ 0
    apply tendsto_atTop_of_geom_le hv₀ one_lt_two
    exact fun n => (key₂ (n + 1)).le
  -- But ϕ ∘ u also needs to go to ϕ(y)
  have lim : Tendsto (ϕ ∘ u) atTop (𝓝 (ϕ y)) := Tendsto.comp cont.continuousAt limy
  -- So we have our contradiction!
  exact not_tendsto_atTop_of_tendsto_nhds lim lim_top
