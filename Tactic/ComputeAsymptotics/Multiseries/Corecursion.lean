/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Data.Seq.Defs
public import Mathlib.Tactic.ENatToNat

/-!
# Non-primitive corecursion for sequences

Primitive corecursive definition of the form
```
def foo (x : X) := hd x :: foo (tlArg x)
```
(where hd and tlArg are arbitrary functions) can be encoded via the corecursor `Seq.corec`.

It is not enough, however, to define multiplication and `powser` operation for multiseries.

This file implements a more general form of corecursion in the spirit of [blanchette2015].
This is a bare minimum that needed for the tactic, it justifies a weaker class of
corecursive definitions than [blanchette2015] does, and only works for `Seq`.

A function `f : Seq α → Seq α` is called *friendly* if for all `n : ℕ` the `n`-prefix of its result
`f s` depends only on the `n`-prefix of its input `s`.

In this file we develop a theory that justifies corecursive definitions of the form
```
def foo (x : X) := hd x :: f (foo (tlArg x))
```
where f is friendly.

## Main definitions

* `FriendlyOperation f` means that `f` is friendly.
* `FriendlyOperationClass` is a typeclass meaning that some indexed family of operations
  are friendly.
* `gcorec`: a generalization of `Seq.corec` that allows a corecursive call to be guarded by
  a friendly function.
* `FriendlyOperation.coind`, `FriendlyOperation.coind_comp_friend_left`,
  `FriendlyOperation.coind_comp_friend_right`: coinduction principles for proving that an operation
  is friendly.
* `FriendlyOperation.eq_of_bisim`: a generalisation of `Seq.eq_of_bisim'` that allows using a
  friendly operation in the tail of the sequences.

## Implementation details

To prove that the definition of the form
```
def foo (x : X) := hd x :: f (foo (tlArg x))
```
is correct we prove that there exists a function satisfying this equation. For that we employ a
Banach fixed point theorem. We treat `Seq α` as a metric space here with the metric
`d(s, t) := 2 ^ (-n)` where `n` is the minimal index where `s` and `t` differ.

Then `f` is friendly iff it is `1`-Lipschitz.
-/

@[expose] public section

namespace Tactic.ComputeAsymptotics.Seq

open Stream' Stream'.Seq

open scoped UniformConvergence

variable {α β γ γ' : Type*}

/-- Metric space structure on `Stream' α` considering `α` as a discrete metric space. -/
noncomputable local instance : MetricSpace (Stream' α) :=
  letI := @PiNat.metricSpace (fun _ ↦ α) (fun _ ↦ ⊥) (fun _ ↦ discreteTopology_bot _)
  inferInstanceAs <| MetricSpace (ℕ → α)

/-- Metric space structure on `Seq α` considering `α` as a discrete metric space. -/
noncomputable local instance : MetricSpace (Seq α) :=
  inferInstanceAs <| MetricSpace (Subtype _)

local instance : CompleteSpace (Stream' α) :=
  @PiNat.completeSpace _ (fun _ ↦ ⊥) (fun _ ↦ discreteTopology_bot _)

set_option backward.isDefEq.respectTransparency false in
local instance : CompleteSpace (Seq α) := by
  suffices IsClosed (X := Stream' (Option α)) {x | ∀ {n : ℕ}, x n = none → x (n + 1) = none} by
    exact this.completeSpace_coe
  rw [isClosed_iff_clusterPt]
  intro s hs n hn
  rw [clusterPt_principal_iff] at hs
  obtain ⟨t, hts, ht⟩ := hs (Metric.ball s ((1 / 2 : ℝ) ^ (n + 1)))
    (Metric.ball_mem_nhds _ (by positivity))
  simp only [Metric.ball, Set.mem_ofPred_eq] at hts
  rw [← PiNat.apply_eq_of_dist_lt hts (by simp)] at hn
  rw [← PiNat.apply_eq_of_dist_lt hts (by rfl)]
  exact ht hn

set_option backward.isDefEq.respectTransparency false in
/-
**Tactic.ComputeAsymptotics.Seq.Stream'.dist_le_one** 是 Mathlib 中的一个定理，位于命名空间 `T
actic.ComputeAsymptotics.Seq.Stream'`。
形式化陈述：∀ {α : Type u_1} (s t : Stream' α), dist s t ≤ 1
参数：s t : Stream' α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `PiNat.dist_eq_of_ne`：dist_eq_of_ne {x y : forall n, E n} (h : x != y) : 
dist x y = (1 / 2 : Real) ^ firstDiff x y
· 使用引理 `pow_le_one₀`：pow_le_one₀ [PosMulMono M₀] {n : Nat} (ha₀ : 0 <= a) (ha₁ :
 a <= 1) : a ^ n <= 1
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `zero_le_two`：zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
 : (0 : α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
-/
theorem Stream'.dist_le_one (s t : Stream' α) : dist s t ≤ 1 := by
  by_cases h : s = t
  · simp [h]
  rw [PiNat.dist_eq_of_ne h]
  bound

@[simp]
/-
**Tactic.ComputeAsymptotics.Seq.dist_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.Co
mputeAsymptotics.Seq`。
形式化陈述：dist_le_one (s t : Seq α) : dist s t <= 1
参数：s t : Seq α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiNat.dist_le_one`：∀ {E : ℕ → Type u_1} (x y : (n : ℕ) → E n), dist x y 
≤ 1
-/
theorem dist_le_one (s t : Seq α) : dist s t ≤ 1 := PiNat.dist_le_one _ _

local instance : BoundedSpace (Stream' α) :=
  @PiNat.boundedSpace _ (fun _ ↦ ⊥) (fun _ ↦ discreteTopology_bot _)

local instance : BoundedSpace (Seq α) :=
  instBoundedSpaceSubtype

set_option backward.isDefEq.respectTransparency false in
/-
**Tactic.ComputeAsymptotics.Seq.dist_eq_two_inv_pow** 是 Mathlib 中的一个定理，位于命名空间 `T
actic.ComputeAsymptotics.Seq`。
形式化陈述：dist_eq_two_inv_pow {s t : Seq α} (h : s != t) : exists n, dist s t = 2⁻¹ 
^ n
参数：h : s != t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subtype.dist_eq`：dist_eq (x y : Subtype p) : dist x y = dist (x : α) y
· 使用定理 `PiNat.dist_eq_of_ne`：dist_eq_of_ne {x y : forall n, E n} (h : x != y) : 
dist x y = (1 / 2 : Real) ^ firstDiff x y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem dist_eq_two_inv_pow {s t : Seq α} (h : s ≠ t) : ∃ n, dist s t = 2⁻¹ ^ n := by
  rw [Subtype.dist_eq, PiNat.dist_eq_of_ne (Subtype.coe_ne_coe.mpr h)]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward false in
@[simp]
/-
**Tactic.ComputeAsymptotics.Seq.dist_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `Tactic
.ComputeAsymptotics.Seq`。
形式化陈述：dist_cons_cons (x : α) (s t : Seq α) : dist (cons x s) (cons x t) = 2⁻¹ * 
dist s t
参数：x : α；s t : Seq α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `Subtype.dist_eq`：dist_eq (x y : Subtype p) : dist x y = dist (x : α) y
· 使用定理 `PiNat.dist_eq_of_ne`：dist_eq_of_ne {x y : forall n, E n} (h : x != y) : 
dist x y = (1 / 2 : Real) ^ firstDiff x y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `PiNat.firstDiff_def`：∀ {E : ℕ → Type u_2} (x y : (n : ℕ) → E n), PiNat.f
irstDiff x y = if h : x ≠ y then Nat.find ⋯ else 0
· 使用定理 `Classical.dite_not`：∀ {p : Prop} {α : Sort u_1} [hn : Decidable ¬p] (x :
 ¬p → α) (y : ¬¬p → α), dite (¬p) x y = dite p (fun h => y ⋯) x
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用引理 `Nat.find_comp_succ`：find_comp_succ (h₁ : exists n, p n) (h₂ : exists n, 
p (n + 1)) (h0 : ¬p 0) : Nat.find h₁ = Nat.find h₂ + 1
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem dist_cons_cons (x : α) (s t : Seq α) : dist (cons x s) (cons x t) = 2⁻¹ * dist s t := by
  by_cases! h : s = t
  · simp [h]
  have h' : cons x s ≠ cons x t := by
    simpa
  rw [Subtype.dist_eq, Subtype.dist_eq, PiNat.dist_eq_of_ne (Subtype.coe_ne_coe.mpr h),
    PiNat.dist_eq_of_ne (Subtype.coe_ne_coe.mpr h')]
  simp only [show (1 / 2 : ℝ) = 2⁻¹ by simp, ← pow_succ']
  congr
  simp only [val_cons, PiNat.firstDiff, ne_eq, Classical.dite_not, Subtype.coe_ne_coe.mpr h,
    not_false_eq_true, ↓reduceDIte, val_eq_get]
  split_ifs with h_if
  · contrapose! h'
    apply_fun Subtype.val using Subtype.val_injective
    simpa
  · convert! Nat.find_comp_succ _ _ _
    simp [Stream'.cons]
/-
**Tactic.ComputeAsymptotics.Seq.dist_eq_half_of_head** 是 Mathlib 中的一个定理，位于命名空间 `
Tactic.ComputeAsymptotics.Seq`。
形式化陈述：dist_eq_half_of_head {s t : Seq α} (h : s.head = t.head) : dist s t = 2⁻¹ 
* dist s.tail t.tail
参数：h : s.head = t.head。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Stream'.Seq.head_cons`：head_cons (a : α) (s) : head (cons a s) = some a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_cons_cons`：dist_cons_cons (x : α) (s 
t : Seq α) : dist (cons x s) (cons x t) = 2⁻¹ * dist s t
-/
theorem dist_eq_half_of_head {s t : Seq α} (h : s.head = t.head) :
    dist s t = 2⁻¹ * dist s.tail t.tail := by
  cases s <;> cases t <;> simp at h <;> simp [h]

set_option backward.isDefEq.respectTransparency false in
/-
**Tactic.ComputeAsymptotics.Seq.dist_eq_one_of_head** 是 Mathlib 中的一个定理，位于命名空间 `T
actic.ComputeAsymptotics.Seq`。
形式化陈述：dist_eq_one_of_head {s t : Seq α} (h : s.head != t.head) : dist s t = 1
参数：h : s.head != t.head。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subtype.dist_eq`：dist_eq (x y : Subtype p) : dist x y = dist (x : α) y
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `PiNat.dist_eq_of_ne`：dist_eq_of_ne {x y : forall n, E n} (h : x != y) : 
dist x y = (1 / 2 : Real) ^ firstDiff x y
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PiNat.firstDiff_def`：∀ {E : ℕ → Type u_2} (x y : (n : ℕ) → E n), PiNat.f
irstDiff x y = if h : x ≠ y then Nat.find ⋯ else 0
· 使用定理 `Classical.dite_not`：∀ {p : Prop} {α : Sort u_1} [hn : Decidable ¬p] (x :
 ¬p → α) (y : ¬¬p → α), dite (¬p) x y = dite p (fun h => y ⋯) x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem dist_eq_one_of_head {s t : Seq α} (h : s.head ≠ t.head) : dist s t = 1 := by
  rw [Subtype.dist_eq, PiNat.dist_eq_of_ne]
  · convert! pow_zero _
    simp only [PiNat.firstDiff, ne_eq, Classical.dite_not, dite_eq_left_iff,
      Nat.find_eq_zero]
    intro h'
    simpa [Stream'.cons]
  · rw [Subtype.coe_ne_coe]
    contrapose h
    simp [h]
/-
**Tactic.ComputeAsymptotics.Seq.dist_cons_cons_eq_one** 是 Mathlib 中的一个定理，位于命名空间 
`Tactic.ComputeAsymptotics.Seq`。
形式化陈述：dist_cons_cons_eq_one {x y : α} {s t : Seq α} (h : x != y) : dist (cons x 
s) (cons y t) = 1
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_eq_one_of_head`：dist_eq_one_of_head {
s t : Seq α} (h : s.head != t.head) : dist s t = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Stream'.Seq.head_cons`：head_cons (a : α) (s) : head (cons a s) = some a
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
-/
theorem dist_cons_cons_eq_one {x y : α} {s t : Seq α} (h : x ≠ y) :
    dist (cons x s) (cons y t) = 1 := by
  apply dist_eq_one_of_head
  simpa

@[simp]
/-
**Tactic.ComputeAsymptotics.Seq.dist_cons_nil** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.
ComputeAsymptotics.Seq`。
形式化陈述：dist_cons_nil (x : α) (s : Seq α) : dist (cons x s) nil = 1
参数：x : α；s : Seq α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_eq_one_of_head`：dist_eq_one_of_head {
s t : Seq α} (h : s.head != t.head) : dist s t = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Stream'.Seq.head_cons`：head_cons (a : α) (s) : head (cons a s) = some a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem dist_cons_nil (x : α) (s : Seq α) : dist (cons x s) nil = 1 := by
  apply dist_eq_one_of_head
  simp

@[simp]
/-
**Tactic.ComputeAsymptotics.Seq.dist_nil_cons** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.
ComputeAsymptotics.Seq`。
形式化陈述：dist_nil_cons (x : α) (s : Seq α) : dist nil (cons x s) = 1
参数：x : α；s : Seq α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_cons_nil`：dist_cons_nil (x : α) (s : 
Seq α) : dist (cons x s) nil = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_nil_cons (x : α) (s : Seq α) : dist nil (cons x s) = 1 := by
  rw [dist_comm]
  simp
/-
**Tactic.ComputeAsymptotics.Seq.dist_le_half_iff** 是 Mathlib 中的一个定理，位于命名空间 `Tact
ic.ComputeAsymptotics.Seq`。
形式化陈述：dist_le_half_iff {s t : Seq α} : dist s t <= 2⁻¹ ↔ (s = .nil ∧ t = .nil) ∨
 exists hd s' t', s = .cons hd s' ∧ t = .cons hd t' where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_nil_cons`：dist_nil_cons (x : α) (s : 
Seq α) : dist nil (cons x s) = 1
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_false`：isRat_le_false [Ring α] [LinearOrde
r α] [IsStrictOrderedRing α] {a b : α} {na nb : Int} {da db : Nat} (ha : IsRat a
 na da) (hb : IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_cons_nil`：dist_cons_nil (x : α) (s : 
Seq α) : dist (cons x s) nil = 1
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
（共 38 条，此处仅展示前 30 条）
-/
theorem dist_le_half_iff {s t : Seq α} :
    dist s t ≤ 2⁻¹ ↔ (s = .nil ∧ t = .nil) ∨ ∃ hd s' t', s = .cons hd s' ∧ t = .cons hd t' where
  mp h := by
    cases s <;> cases t <;> norm_num at h <;> simp
    grind [dist_cons_cons_eq_one]
  mpr h := by
    obtain ⟨rfl, rfl⟩ | ⟨hd, s', t', rfl, rfl⟩ := h <;> simp

/-- A function on sequences is called a "friend" if any `n`-prefix of its output depends only on
the `n`-prefix of the input. Such functions can be used in the tail of (non-primitive) corecursive
definitions. -/
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation** 是 Mathlib 中的一个定义，位于命名空间 `Tac
tic.ComputeAsymptotics.Seq`。
形式化陈述：FriendlyOperation (op : Seq α -> Seq α) : Prop
参数：op : Seq α -> Seq α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function on sequences is called a "friend" if any `n`-prefix of its output dep
ends only on
the `n`-prefix of the input. Such functions can be used in the tail of (non-prim
itive) corecursive
definitions.
-/
def FriendlyOperation (op : Seq α → Seq α) : Prop := LipschitzWith 1 op

/-- A family of friendly operations on sequences indexed by a type `γ`. -/
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperationClass** 是 Mathlib 中的一个归纳类型，位于命名
空间 `Tactic.ComputeAsymptotics.Seq`。
形式化陈述：{α : Type u_1} → {γ : Type u_3} → (γ → Stream'.Seq α → Stream'.Seq α) → Pr
op
参数：γ → Stream'.Seq α → Stream'.Seq α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of friendly operations on sequences indexed by a type `γ`.
-/
class FriendlyOperationClass (F : γ → Seq α → Seq α) : Prop where
  friend : ∀ c : γ, FriendlyOperation (F c)
/-
**Tactic.ComputeAsymptotics.Seq.friendlyOperation_iff_dist_le_dist** 是 Mathlib 中
的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.Seq`。
形式化陈述：friendlyOperation_iff_dist_le_dist (op : Seq α -> Seq α) : FriendlyOperati
on op ↔ forall s t, dist (op s) (op t) <= dist s t
参数：op : Seq α -> Seq α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem friendlyOperation_iff_dist_le_dist (op : Seq α → Seq α) :
    FriendlyOperation op ↔ ∀ s t, dist (op s) (op t) ≤ dist s t := by
  simp [FriendlyOperation, lipschitzWith_iff_dist_le_mul]
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation.id** 是 Mathlib 中的一个定理，位于命名空间 `
Tactic.ComputeAsymptotics.Seq.FriendlyOperation`。
形式化陈述：∀ {α : Type u_1}, Tactic.ComputeAsymptotics.Seq.FriendlyOperation id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.id`：∀ {α : Type u} [inst : PseudoEMetricSpace α], Lipschit
zWith 1 id
-/
theorem FriendlyOperation.id : FriendlyOperation (id : Seq α → Seq α) :=
  LipschitzWith.id
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation.comp** 是 Mathlib 中的一个定理，位于命名空间
 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation`。
形式化陈述：∀ {α : Type u_1} {op op' : Stream'.Seq α → Stream'.Seq α},   Tactic.Comput
eAsymptotics.Seq.FriendlyOperation op →     Tactic.ComputeAsymptotics.Seq.Friend
lyOperation op' → Tactic.ComputeAsymptotics.Seq.FriendlyOperation (op ∘ op')
参数：op ∘ op'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.eq_1`：∀ {α : Type u_1} (
op : Stream'.Seq α → Stream'.Seq α),   Tactic.ComputeAsymptotics.Seq.FriendlyOpe
ration op = LipschitzWith 1 op
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LipschitzWith.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpac
e γ] {Kf…
-/
theorem FriendlyOperation.comp {op op' : Seq α → Seq α}
    (h : FriendlyOperation op) (h' : FriendlyOperation op') :
    FriendlyOperation (op ∘ op') := by
  rw [FriendlyOperation] at h h' ⊢
  convert! h.comp h'
  simp
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation.const** 是 Mathlib 中的一个定理，位于命名空
间 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation`。
形式化陈述：∀ {α : Type u_1} {s : Stream'.Seq α}, Tactic.ComputeAsymptotics.Seq.Friend
lyOperation fun x => s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem FriendlyOperation.const {s : Seq α} : FriendlyOperation (fun _ ↦ s) := by
  simp [friendlyOperation_iff_dist_le_dist]
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperationClass.comp** 是 Mathlib 中的一个定理，位
于命名空间 `Tactic.ComputeAsymptotics.Seq.FriendlyOperationClass`。
形式化陈述：∀ {α : Type u_1} {γ : Type u_3} {γ' : Type u_4} (F : γ → Stream'.Seq α → S
tream'.Seq α) (g : γ' → γ)   [h : Tactic.ComputeAsymptotics.Seq.FriendlyOperatio
nClass F],   Tactic.ComputeAsymptotics.Seq.FriendlyOperationClass fun c => F (g 
c)
参数：F : γ → Stream'.Seq α → Stream'.Seq α；g : γ' → γ；g c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem FriendlyOperationClass.comp (F : γ → Seq α → Seq α) (g : γ' → γ)
    [h : FriendlyOperationClass F] : FriendlyOperationClass (fun c ↦ F (g c)) := by
  grind [FriendlyOperationClass]
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation.ite** 是 Mathlib 中的一个定理，位于命名空间 
`Tactic.ComputeAsymptotics.Seq.FriendlyOperation`。
形式化陈述：∀ {α : Type u_1} {op₁ op₂ : Stream'.Seq α → Stream'.Seq α},   Tactic.Compu
teAsymptotics.Seq.FriendlyOperation op₁ →     Tactic.ComputeAsymptotics.Seq.Frie
ndlyOperation op₂ →       ∀ {P : Option α → Prop} [inst : DecidablePred P],     
    Tactic.ComputeAsymptotics.Seq.FriendlyOperation fun s => if P s.head then op
₁ s else op₂ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.Seq.friendlyOperation_iff_dist_le_dist`：friend
lyOperation_iff_dist_le_dist (op : Seq α -> Seq α) : FriendlyOperation op ↔ fora
ll s t, dist (op s) (op t) <= dist s t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_eq_one_of_head`：dist_eq_one_of_head {
s t : Seq α} (h : s.head != t.head) : dist s t = 1
-/
theorem FriendlyOperation.ite {op₁ op₂ : Seq α → Seq α}
    (h₁ : FriendlyOperation op₁) (h₂ : FriendlyOperation op₂)
    {P : Option α → Prop} [DecidablePred P] :
    FriendlyOperation (fun s ↦ if P s.head then op₁ s else op₂ s) := by
  rw [friendlyOperation_iff_dist_le_dist] at h₁ h₂ ⊢
  intro s t
  by_cases! h_head : s.head ≠ t.head
  · simp [dist_eq_one_of_head h_head]
  grind
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation.dist_le** 是 Mathlib 中的一个定理，位于命
名空间 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation`。
形式化陈述：∀ {α : Type u_1} {op : Stream'.Seq α → Stream'.Seq α},   Tactic.ComputeAsy
mptotics.Seq.FriendlyOperation op → ∀ {s t : Stream'.Seq α}, dist (op s) (op t) 
≤ dist s t
参数：op s；op t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `lipschitzWith_iff_dist_le_mul`：lipschitzWith_iff_dist_le_mul [PseudoMetr
icSpace α] [PseudoMetricSpace β] {K : Real>=0} {f : α -> β} : LipschitzWith K f 
↔ forall x y, dist …
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.eq_1`：∀ {α : Type u_1} (
op : Stream'.Seq α → Stream'.Seq α),   Tactic.ComputeAsymptotics.Seq.FriendlyOpe
ration op = LipschitzWith 1 op
-/
theorem FriendlyOperation.dist_le {op : Seq α → Seq α} (h : FriendlyOperation op)
    {s t : Seq α} : dist (op s) (op t) ≤ dist s t := by
  rw [FriendlyOperation, lipschitzWith_iff_dist_le_mul] at h
  simpa using h s t
/-
**Tactic.ComputeAsymptotics.Seq.exists_fixed_point_of_contractible** 是 Mathlib 中
的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.Seq`。
形式化陈述：exists_fixed_point_of_contractible (F : (β ->ᵤ Seq α) -> (β ->ᵤ Seq α)) (h
 : LipschitzWith 2⁻¹ F) : exists f : β -> Seq α, Function.IsFixedPt F f
参数：F : (β ->ᵤ Seq α) -> (β ->ᵤ Seq α)；h : LipschitzWith 2⁻¹ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Tactic.ComputeAsymptotics.Seq.instBoundedSpaceSeq`：∀ {α : Type u_1}, Bou
ndedSpace (Stream'.Seq α)
· 使用定理 `instNonemptyUniformFun`：∀ {α : Type u_1} {β : Type u_2} [Nonempty β], No
nempty (UniformFun α β)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `UniformFun.instCompleteSpace`：∀ {α : Type u_1} {β : Type u_2} [inst : Un
iformSpace β] [CompleteSpace β], CompleteSpace (UniformFun α β)
· 使用定理 `Tactic.ComputeAsymptotics.Seq.instCompleteSpaceSeq`：∀ {α : Type u_1}, Co
mpleteSpace (Stream'.Seq α)
· 使用定理 `ContractingWith.fixedPoint_isFixedPt`：fixedPoint_isFixedPt : IsFixedPt f
 (fixedPoint f hf)
-/
theorem exists_fixed_point_of_contractible (F : (β →ᵤ Seq α) → (β →ᵤ Seq α))
    (h : LipschitzWith 2⁻¹ F) :
    ∃ f : β → Seq α, Function.IsFixedPt F f := by
  have hF : ContractingWith 2⁻¹ F := by
    constructor
    · norm_num
    · exact h
  let f := hF.fixedPoint _
  use f
  exact hF.fixedPoint_isFixedPt

set_option backward.isDefEq.respectTransparency false in
/-- Main theorem of this file. It shows that there exists a function satisfying the corecursive
definition of the form `def foo (x : X) := hd x :: op (foo (tlArg x))` where `f` is friendly. -/
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation.exists_fixed_point** 是 Mathlib
 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (F : β → Option (α × γ × β)
) (op : γ → Stream'.Seq α → Stream'.Seq α)   [h : Tactic.ComputeAsymptotics.Seq.
FriendlyOperationClass op],   ∃ f,     ∀ (b : β),       match F b with       | n
one => f b = Stream'.Seq.nil       | some (a, c, b') => f b = Stream'.Seq.cons a
 (op c (f b'))
参数：F : β → Option (α × γ × β)；op : γ → Stream'.Seq α → Stream'.Seq α；b : β；a, c,
 b'；op c (f b')。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Tactic.ComputeAsymptotics.Seq.instBoundedSpaceSeq`：∀ {α : Type u_1}, Bou
ndedSpace (Stream'.Seq α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lipschitzWith_iff_dist_le_mul`：lipschitzWith_iff_dist_le_mul [PseudoMetr
icSpace α] [PseudoMetricSpace β] {K : Real>=0} {f : α -> β} : LipschitzWith K f 
↔ forall x y, dist …
· 使用引理 `UniformFun.dist_le`：dist_le [BoundedSpace β] {f g : α ->ᵤ β} {C : Real} 
(hC : 0 <= C) : dist f g <= C ↔ forall x, dist (toFun f x) (toFun g x) <= C
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Mathlib.Meta.Positivity.nnreal_coe_pos`：∀ {r : NNReal}, 0 < r → 0 < ↑r
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_cons_cons`：dist_cons_cons (x : α) (s 
t : Seq α) : dist (cons x s) (cons x t) = 2⁻¹ * dist s t
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperationClass.friend`：∀ {α : Type
 u_1} {γ : Type u_3} {F : γ → Stream'.Seq α → Stream'.Seq α}   [self : Tactic.Co
mputeAsymptotics.Seq.FriendlyOperationClass F] (c…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.eq_1`：∀ {α : Type u_1} (
op : Stream'.Seq α → Stream'.Seq α),   Tactic.ComputeAsymptotics.Seq.FriendlyOpe
ration op = LipschitzWith 1 op
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Main theorem of this file. It shows that there exists a function satisfying the 
corecursive
definition of the form `def foo (x : X) := hd x :: op (foo (tlArg x))` where `f`
 is friendly.
-/
theorem FriendlyOperation.exists_fixed_point (F : β → Option (α × γ × β)) (op : γ → Seq α → Seq α)
    [h : FriendlyOperationClass op] :
    ∃ f : β → Seq α, ∀ b : β,
    match F b with
    | none => f b = nil
    | some (a, c, b') => f b = Seq.cons a (op c (f b')) := by
  let T : (β →ᵤ Seq α) → (β →ᵤ Seq α) := fun f b =>
    match F b with
    | none => nil
    | some (a, c, b') => Seq.cons a (op c (f b'))
  have hT : LipschitzWith 2⁻¹ T := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro f g
    rw [UniformFun.dist_le (by positivity)]
    intro b
    simp only [UniformFun.toFun, UniformFun.ofFun, Equiv.coe_fn_symm_mk, NNReal.coe_inv,
      NNReal.coe_ofNat, T]
    cases F b with
    | none => simp
    | some v =>
      obtain ⟨a, c, b'⟩ := v
      simp
      calc
        _ ≤ dist (f b') (g b') := by
          have := h.friend c
          rw [FriendlyOperation, lipschitzWith_iff_dist_le_mul] at this
          specialize this (f b') (g b')
          simpa using this
        _ ≤ _ := by
          simp only [UniformFun.dist_def]
          apply le_ciSup (f := fun b ↦ dist (f b) (g b))
          have : ∃ C, ∀ (a b : Seq α), dist a b ≤ C := by
            rw [← Metric.boundedSpace_iff]
            infer_instance
          obtain ⟨C, hC⟩ := this
          use C
          simp [upperBounds]
          grind
  obtain ⟨f, hf⟩ := exists_fixed_point_of_contractible T hT
  use f
  intro b
  rw [← hf]
  simp only [T]
  cases hb : F b with
  | none =>
    simp
  | some v =>
    obtain ⟨a, c, b'⟩ := v
    simp only [cons_eq_cons, true_and]
    congr
    change f b' = T f b'
    rw [hf]

/-- (General) non-primitive corecursor for `Seq α` that allows using a friendly operation in the
tail of the corecursive definition. -/
/-
**Tactic.ComputeAsymptotics.Seq.gcorec** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.Compute
Asymptotics.Seq`。
形式化陈述：gcorec (F : β -> Option (α × γ × β)) (op : γ -> Seq α -> Seq α) [FriendlyO
perationClass op] : β -> Seq α
参数：F : β -> Option (α × γ × β)；op : γ -> Seq α -> Seq α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.exists_fixed_point`：∀ {α
 : Type u_1} {β : Type u_2} {γ : Type u_3} (F : β → Option (α × γ × β)) (op : γ 
→ Stream'.Seq α → Stream'.Seq α)   [h : Tactic.ComputeAs…

--- 原说明 ---
(General) non-primitive corecursor for `Seq α` that allows using a friendly oper
ation in the
tail of the corecursive definition.
-/
noncomputable def gcorec (F : β → Option (α × γ × β)) (op : γ → Seq α → Seq α)
    [FriendlyOperationClass op] :
  β → Seq α := (FriendlyOperation.exists_fixed_point F op).choose
/-
**Tactic.ComputeAsymptotics.Seq.gcorec_nil** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.Com
puteAsymptotics.Seq`。
形式化陈述：gcorec_nil {F : β -> Option (α × γ × β)} {op : γ -> Seq α -> Seq α} [Frien
dlyOperationClass op] {b : β} (h : F b = none) : gcorec F op b = nil
参数：α × γ × β；h : F b = none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.exists_fixed_point`：∀ {α
 : Type u_1} {β : Type u_2} {γ : Type u_3} (F : β → Option (α × γ × β)) (op : γ 
→ Stream'.Seq α → Stream'.Seq α)   [h : Tactic.ComputeAs…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem gcorec_nil {F : β → Option (α × γ × β)} {op : γ → Seq α → Seq α}
    [FriendlyOperationClass op] {b : β}
    (h : F b = none) :
    gcorec F op b = nil := by
  have := (FriendlyOperation.exists_fixed_point F op).choose_spec b
  simpa [h] using! this
/-
**Tactic.ComputeAsymptotics.Seq.gcorec_some** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.Co
mputeAsymptotics.Seq`。
形式化陈述：gcorec_some {F : β -> Option (α × γ × β)} {op : γ -> Seq α -> Seq α} [Frie
ndlyOperationClass op] {b : β} {a : α} {c : γ} {b' : β} (h : F b = some (a, c, b
')) : gcorec F op b = Seq.cons a (op c (gcorec F op b'))
参数：α × γ × β；h : F b = some (a, c, b')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.exists_fixed_point`：∀ {α
 : Type u_1} {β : Type u_2} {γ : Type u_3} (F : β → Option (α × γ × β)) (op : γ 
→ Stream'.Seq α → Stream'.Seq α)   [h : Tactic.ComputeAs…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem gcorec_some {F : β → Option (α × γ × β)} {op : γ → Seq α → Seq α}
    [FriendlyOperationClass op] {b : β}
    {a : α} {c : γ} {b' : β}
    (h : F b = some (a, c, b')) :
    gcorec F op b = Seq.cons a (op c (gcorec F op b')) := by
  have := (FriendlyOperation.exists_fixed_point F op).choose_spec b
  simpa [h] using! this

/-- The operation `cons hd ·` is friendly. -/
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation.cons** 是 Mathlib 中的一个定理，位于命名空间
 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation`。
形式化陈述：∀ {α : Type u_1} (hd : α), Tactic.ComputeAsymptotics.Seq.FriendlyOperation
 (Stream'.Seq.cons hd)
参数：hd : α；Stream'.Seq.cons hd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_cons_cons`：dist_cons_cons (x : α) (s 
t : Seq α) : dist (cons x s) (cons x t) = 2⁻¹ * dist s t
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
The operation `cons hd ·` is friendly.
-/
theorem FriendlyOperation.cons (hd : α) : FriendlyOperation (cons hd) := by
  simp only [friendlyOperation_iff_dist_le_dist, dist_cons_cons]
  intro x y
  linarith [dist_nonneg (x := x) (y := y)]

/-- If two sequences have the same head and applying `op` reduces their distance, then
it also reduces the distance of their tails. -/
/-
**Tactic.ComputeAsymptotics.Seq.dist_const_tail_cons_tail_le** 是 Mathlib 中的一个引理，
位于命名空间 `Tactic.ComputeAsymptotics.Seq`。
形式化陈述：dist_const_tail_cons_tail_le {op : Seq α -> Seq α} {hd : α} {x y : Stream'
.Seq α} (h : dist (op (cons hd x)) (op (cons hd y)) <= dist (cons hd x) (cons hd
 y)) : dist (op (cons hd x)).tail (op (cons hd y)).tail <= dist x y
参数：h : dist (op (cons hd x)) (op (cons hd y)) <= dist (cons hd x) (cons hd y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_eq_half_of_head`：dist_eq_half_of_head
 {s t : Seq α} (h : s.head = t.head) : dist s t = 2⁻¹ * dist s.tail t.tail
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_le_half_iff`：dist_le_half_iff {s t : 
Seq α} : dist s t <= 2⁻¹ ↔ (s = .nil ∧ t = .nil) ∨ exists hd s' t', s = .cons hd
 s' ∧ t = .cons hd t' where mp h
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_le_one`：dist_le_one (s t : Seq α) : d
ist s t <= 1
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_cons_cons`：dist_cons_cons (x : α) (s 
t : Seq α) : dist (cons x s) (cons x t) = 2⁻¹ * dist s t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If two sequences have the same head and applying `op` reduces their distance, th
en
it also reduces the distance of their tails.
-/
lemma dist_const_tail_cons_tail_le
    {op : Seq α → Seq α} {hd : α} {x y : Stream'.Seq α}
    (h : dist (op (cons hd x)) (op (cons hd y)) ≤ dist (cons hd x) (cons hd y)) :
    dist (op (cons hd x)).tail (op (cons hd y)).tail ≤ dist x y := by
  rwa [dist_cons_cons, dist_eq_half_of_head, mul_le_mul_iff_right₀ (by norm_num)] at h
  grw [dist_le_one x y, mul_one] at h
  obtain (⟨hx, hy⟩ | ⟨_, _, _, hx, hy⟩) := dist_le_half_iff.mp h <;> simp [hx, hy]

/-- The operation `(op (.cons hd ·)).tail` is friendly if `op` is friendly. -/
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation.cons_tail** 是 Mathlib 中的一个定理，位
于命名空间 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation`。
形式化陈述：∀ {α : Type u_1} {op : Stream'.Seq α → Stream'.Seq α} {hd : α},   Tactic.C
omputeAsymptotics.Seq.FriendlyOperation op →     Tactic.ComputeAsymptotics.Seq.F
riendlyOperation fun s => (op (Stream'.Seq.cons hd s)).tail
参数：op (Stream'.Seq.cons hd s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Tactic.ComputeAsymptotics.Seq.dist_const_tail_cons_tail_le`：dist_const_t
ail_cons_tail_le {op : Seq α -> Seq α} {hd : α} {x y : Stream'.Seq α} (h : dist 
(op (cons hd x)) (op (cons hd y)) <= dist (cons …

--- 原说明 ---
The operation `(op (.cons hd ·)).tail` is friendly if `op` is friendly.
-/
theorem FriendlyOperation.cons_tail {op : Seq α → Seq α} {hd : α} (h : FriendlyOperation op) :
    FriendlyOperation (fun s ↦ (op (.cons hd s)).tail) := by
  simp_rw [friendlyOperation_iff_dist_le_dist] at h ⊢
  intro x y
  specialize h (.cons hd x) (.cons hd y)
  exact dist_const_tail_cons_tail_le h

/-- The first element of `op (a :: s)` depends only on `a`. -/
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation.op_cons_head_eq** 是 Mathlib 中的
一个定理，位于命名空间 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation`。
形式化陈述：∀ {α : Type u_1} {op : Stream'.Seq α → Stream'.Seq α},   Tactic.ComputeAsy
mptotics.Seq.FriendlyOperation op →     ∀ {a : α} {s t : Stream'.Seq α}, (op (St
ream'.Seq.cons a s)).head = (op (Stream'.Seq.cons a t)).head
参数：op (Stream'.Seq.cons a s)；op (Stream'.Seq.cons a t)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_cons_cons`：dist_cons_cons (x : α) (s 
t : Seq α) : dist (cons x s) (cons x t) = 2⁻¹ * dist s t
· 使用定理 `Tactic.ComputeAsymptotics.Seq.friendlyOperation_iff_dist_le_dist`：friend
lyOperation_iff_dist_le_dist (op : Seq α -> Seq α) : FriendlyOperation op ↔ fora
ll s t, dist (op s) (op t) <= dist s t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_le_half_iff`：dist_le_half_iff {s t : 
Seq α} : dist s t <= 2⁻¹ ↔ (s = .nil ∧ t = .nil) ∨ exists hd s' t', s = .cons hd
 s' ∧ t = .cons hd t' where mp h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The first element of `op (a :: s)` depends only on `a`.
-/
theorem FriendlyOperation.op_cons_head_eq {op : Seq α → Seq α} (h : FriendlyOperation op) {a : α}
    {s t : Seq α} : (op <| .cons a s).head = (op <| .cons a t).head := by
  rw [friendlyOperation_iff_dist_le_dist] at h
  specialize h (.cons a s) (.cons a t)
  simp only [dist_cons_cons] at h
  replace h : dist (op (.cons a s)) (op (.cons a t)) ≤ 2⁻¹ := by
    apply h.trans
    simp
  rw [dist_le_half_iff] at h
  generalize op (Seq.cons a s) = s' at *
  generalize op (Seq.cons a t) = t' at *
  obtain ⟨rfl, rfl⟩ | ⟨hd, s_tl, t_tl, rfl, rfl⟩ := h <;> rfl

/-- Decomposes a friendly operation by the head of the input sequence. Returns `none` if the output
is `nil`, or `some (out_hd, op')` where `out_hd` is the head of the output and `op'` is a friendly
operation mapping the tail of the input to the tail of the output. See
`destruct_apply_eq_unfold` for the correctness statement. -/
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation.unfold** 是 Mathlib 中的一个定义，位于命名
空间 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation`。
形式化陈述：{α : Type u_1} →   {op : Stream'.Seq α → Stream'.Seq α} →     Tactic.Compu
teAsymptotics.Seq.FriendlyOperation op →       Option α → Option (α × Subtype Ta
ctic.ComputeAsymptotics.Seq.FriendlyOperation)
参数：α × Subtype Tactic.ComputeAsymptotics.Seq.FriendlyOperation。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.const`：∀ {α : Type u_1} 
{s : Stream'.Seq α}, Tactic.ComputeAsymptotics.Seq.FriendlyOperation fun x => s
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.cons_tail`：∀ {α : Type u
_1} {op : Stream'.Seq α → Stream'.Seq α} {hd : α},   Tactic.ComputeAsymptotics.S
eq.FriendlyOperation op →     Tactic.ComputeAsy…

--- 原说明 ---
Decomposes a friendly operation by the head of the input sequence. Returns `none
` if the output
is `nil`, or `some (out_hd, op')` where `out_hd` is the head of the output and `
op'` is a friendly
operation mapping the tail of the input to the tail of the output. See
`destruct_apply_eq_unfold` for the correctness statement.
-/
def FriendlyOperation.unfold {op : Seq α → Seq α} (h : FriendlyOperation op) (hd? : Option α) :
    Option (α × Subtype (@FriendlyOperation α)) :=
  match hd? with
  | none =>
    match (op nil).destruct with
    | none => none
    | some (t_hd, t_tl) =>
      some (t_hd, ⟨fun _ ↦ t_tl, FriendlyOperation.const⟩)
  | some s_hd =>
    match (op <| .cons s_hd nil).destruct with
    | none => none
    | some (t_hd, _) =>
      some (t_hd, ⟨fun s_tl ↦ (op (.cons s_hd s_tl)).tail, FriendlyOperation.cons_tail h⟩)

set_option backward.isDefEq.respectTransparency false in
/-- `unfold` correctly decomposes a friendly operation: the head of `op s` depends only on the
head of `s` (and is given by `unfold`), while the tail of `op s` is obtained by applying the
friendly operation returned by `unfold` to the tail of `s`. This gives a coinductive
characterization of `FriendlyOperation`. For the coinduction principle, see
`FriendlyOperation.coind`. -/
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation.destruct_apply_eq_unfold** 是 M
athlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation`。
形式化陈述：∀ {α : Type u_1} {op : Stream'.Seq α → Stream'.Seq α} (h : Tactic.ComputeA
symptotics.Seq.FriendlyOperation op)   {s : Stream'.Seq α},   (op s).destruct = 
    Option.map       (fun x =>         match x with         | (hd, op') => (hd, 
↑op' s.tail))       (h.unfold s.head)
参数：h : Tactic.ComputeAsymptotics.Seq.FriendlyOperation op；op s；fun x =>         
match x with         | (hd, op') => (hd, ↑op' s.tail)；h.unfold s.head。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.const`：∀ {α : Type u_1} 
{s : Stream'.Seq α}, Tactic.ComputeAsymptotics.Seq.FriendlyOperation fun x => s
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.cons_tail`：∀ {α : Type u
_1} {op : Stream'.Seq α → Stream'.Seq α} {hd : α},   Tactic.ComputeAsymptotics.S
eq.FriendlyOperation op →     Tactic.ComputeAsy…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Stream'.Seq.destruct_cons`：∀ {α : Type u} (a : α) (s : Stream'.Seq α), (
Stream'.Seq.cons a s).destruct = some (a, s)
· 使用定理 `Stream'.Seq.head_cons`：head_cons (a : α) (s) : head (cons a s) = some a
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.op_cons_head_eq`：∀ {α : 
Type u_1} {op : Stream'.Seq α → Stream'.Seq α},   Tactic.ComputeAsymptotics.Seq.
FriendlyOperation op →     ∀ {a : α} {s t : Stream'.S…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)

--- 原说明 ---
`unfold` correctly decomposes a friendly operation: the head of `op s` depends o
nly on the
head of `s` (and is given by `unfold`), while the tail of `op s` is obtained by 
applying the
friendly operation returned by `unfold` to the tail of `s`. This gives a coinduc
tive
characterization of `FriendlyOperation`. For the coinduction principle, see
`FriendlyOperation.coind`.
-/
theorem FriendlyOperation.destruct_apply_eq_unfold {op : Seq α → Seq α} (h : FriendlyOperation op)
    {s : Seq α} :
    destruct (op s) = (h.unfold s.head).map (fun (hd, op') => (hd, op'.val s.tail)) := by
  unfold unfold
  cases s with
  | nil =>
    generalize op nil = t
    cases t <;> simp
  | cons s_hd s_tl =>
    simp only [Seq.tail_cons, Seq.head_cons]
    generalize ht0 : op (.cons s_hd nil) = t0 at *
    generalize ht : op (.cons s_hd s_tl) = t at *
    have : t0.head = t.head := by
      rw [← ht0, ← ht, FriendlyOperation.op_cons_head_eq h]
    cases t0 with
    | nil =>
      cases t with
      | nil => simp
      | cons => simp at this
    | cons =>
      cases t with
      | nil => simp at this
      | cons => simp_all

set_option backward.isDefEq.respectTransparency false in
/-- If `op` is friendly, then `op s` and `op t` have the same head if `s` and `t`
have the same head. -/
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation.op_head_eq** 是 Mathlib 中的一个定理，
位于命名空间 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation`。
形式化陈述：∀ {α : Type u_1} {op : Stream'.Seq α → Stream'.Seq α},   Tactic.ComputeAsy
mptotics.Seq.FriendlyOperation op →     ∀ {s t : Stream'.Seq α}, s.head = t.head
 → (op s).head = (op t).head
参数：op s；op t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Stream'.Seq.head_eq_destruct`：head_eq_destruct (s : Seq α) : head s = Pr
od.fst < > destruct.{u} s
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.destruct_apply_eq_unfold
`：∀ {α : Type u_1} {op : Stream'.Seq α → Stream'.Seq α} (h : Tactic.ComputeAsymp
totics.Seq.FriendlyOperation op)   {s : Stream'.Seq α},   (op …
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.unfold.congr_simp`：∀ {α 
: Type u_1} {op op_1 : Stream'.Seq α → Stream'.Seq α} (e_op : op = op_1)   (h : 
Tactic.ComputeAsymptotics.Seq.FriendlyOperation op) (hd…
· 使用定理 `Option.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} (h : β → 
γ) (g : α → β) (x : Option α),   Option.map h (Option.map g x) = Option.map (h ∘
 g) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
If `op` is friendly, then `op s` and `op t` have the same head if `s` and `t`
have the same head.
-/
theorem FriendlyOperation.op_head_eq {op : Seq α → Seq α} (h : FriendlyOperation op) {s t : Seq α}
    (h_head : s.head = t.head) : (op s).head = (op t).head := by
  simp only [head_eq_destruct, Option.map_eq_map, h.destruct_apply_eq_unfold, Option.map_map]
    at h_head ⊢
  simp [h_head]
  rfl
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation.of_dist_le_pow** 是 Mathlib 中的一
个定理，位于命名空间 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation`。
形式化陈述：∀ {α : Type u_1} {op : Stream'.Seq α → Stream'.Seq α},   (∀ (s t : Stream'
.Seq α) (n : ℕ), dist s t ≤ 2⁻¹ ^ n → dist (op s) (op t) ≤ 2⁻¹ ^ n) →     Tactic
.ComputeAsymptotics.Seq.FriendlyOperation op
参数：∀ (s t : Stream'.Seq α) (n : ℕ), dist s t ≤ 2⁻¹ ^ n → dist (op s) (op t) ≤ 2⁻
¹ ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.Seq.friendlyOperation_iff_dist_le_dist`：friend
lyOperation_iff_dist_le_dist (op : Seq α -> Seq α) : FriendlyOperation op ↔ fora
ll s t, dist (op s) (op t) <= dist s t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_eq_two_inv_pow`：dist_eq_two_inv_pow {
s t : Seq α} (h : s != t) : exists n, dist s t = 2⁻¹ ^ n
-/
theorem FriendlyOperation.of_dist_le_pow {op : Seq α → Seq α}
    (h : ∀ s t n, dist s t ≤ (2⁻¹ : ℝ) ^ n → dist (op s) (op t) ≤ (2⁻¹ : ℝ) ^ n) :
    FriendlyOperation op := by
  rw [friendlyOperation_iff_dist_le_dist]
  intro s t
  by_cases hst : s = t
  · simp [hst]
  obtain ⟨n, hst⟩ := dist_eq_two_inv_pow hst
  grind

set_option backward.isDefEq.respectTransparency.types false in
/-- Coinduction principle for proving that an operation is friendly. -/
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation.coind** 是 Mathlib 中的一个定理，位于命名空
间 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation`。
形式化陈述：∀ {α : Type u_1} (motive : (Stream'.Seq α → Stream'.Seq α) → Prop) {op : S
tream'.Seq α → Stream'.Seq α},   motive op →     (∀ (op : Stream'.Seq α → Stream
'.Seq α),         motive op →           ∃ T,             ∀ (s : Stream'.Seq α), 
              (op s).destruct =                 Option.map                   (fu
n x =>                     match x with                     | (hd, op') => (hd, 
↑op' s.tail))                   (T s.head)) →       Tactic.ComputeAsymptotics.Se
q.FriendlyOperation op
参数：motive : (Stream'.Seq α → Stream'.Seq α) → Prop；∀ (op : Stream'.Seq α → Strea
m'.Seq α),         motive op →           ∃ T,             ∀ (s : Stream'.Seq α),
               (op s).destruct =                 Option.map                   (f
un x =>                     match x with                     | (hd, op') => (hd,
 ↑op' s.tail))                   (T s.head)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.of_dist_le_pow`：∀ {α : T
ype u_1} {op : Stream'.Seq α → Stream'.Seq α},   (∀ (s t : Stream'.Seq α) (n : ℕ
), dist s t ≤ 2⁻¹ ^ n → dist (op s) (op t) ≤ 2⁻¹ ^ n…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `pow_le_one₀`：pow_le_one₀ [PosMulMono M₀] {n : Nat} (ha₀ : 0 <= a) (ha₁ :
 a <= 1) : a ^ n <= 1
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_le_half_iff`：dist_le_half_iff {s t : 
Seq α} : dist s t <= 2⁻¹ ↔ (s = .nil ∧ t = .nil) ∨ exists hd s' t', s = .cons hd
 s' ∧ t = .cons hd t' where mp h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Coinduction principle for proving that an operation is friendly.
-/
theorem FriendlyOperation.coind (motive : (Seq α → Seq α) → Prop)
    {op : Seq α → Seq α}
    (h_base : motive op)
    (h_step : ∀ op, motive op → ∃ T : Option α → Option (α × Subtype motive),
      ∀ s, (op s).destruct = (T s.head).map (fun (hd, op') => (hd, op'.val s.tail))) :
    FriendlyOperation op := by
  apply of_dist_le_pow
  intro s t n hn
  induction n generalizing op s t with
  | zero => simp
  | succ n ih =>
    obtain ⟨T, hT⟩ := h_step _ h_base
    have h_head : s.head = t.head := by
      replace hn : dist s t ≤ 2⁻¹ := by
        apply hn.trans
        simp only [pow_succ, inv_pos, Nat.ofNat_pos, mul_le_iff_le_one_left]
        apply pow_le_one₀ <;> norm_num
      rw [dist_le_half_iff] at hn
      obtain ⟨rfl, rfl⟩ | ⟨hd, s_tl, t_tl, rfl, rfl⟩ := hn <;> rfl
    have hs := hT s
    have ht := hT t
    cases hT_head : T s.head with
    | none =>
      simp only [hT_head, Option.map_none, ← h_head] at hs ht
      simp [hs, ht, destruct_eq_none]
    | some v =>
      obtain ⟨hd, op', h_next⟩ := v
      simp only [hT_head, Option.map_some, ← h_head] at hs ht
      simp only [destruct_eq_cons hs, destruct_eq_cons ht, dist_cons_cons, pow_succ', inv_pos,
        Nat.ofNat_pos, mul_le_mul_iff_right₀, ge_iff_le]
      apply ih h_next
      simpa [dist_eq_half_of_head h_head, pow_succ'] using hn

set_option backward.isDefEq.respectTransparency false in
/-- A generalisation of `FriendlyOperation.coind` which allows using `opf ∘ op'` in the tail
of `op s` where `opf` is friendly and `op'` is a function satisfying `motive`. -/
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation.coind_comp_friend_left** 是 Mat
hlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation`。
形式化陈述：∀ {α : Type u_1} {op : Stream'.Seq α → Stream'.Seq α} (motive : (Stream'.S
eq α → Stream'.Seq α) → Prop),   motive op →     (∀ (op : Stream'.Seq α → Stream
'.Seq α),         motive op →           ∃ T,             ∀ (s : Stream'.Seq α), 
              (op s).destruct =                 Option.map                   (fu
n x =>                     match x with                     | (hd, opf, op') => 
(hd, ↑opf (↑op' s.tail)))                   (T s.head)) →       Tactic.ComputeAs
ymptotics.Seq.FriendlyOperation op
参数：motive : (Stream'.Seq α → Stream'.Seq α) → Prop；∀ (op : Stream'.Seq α → Strea
m'.Seq α),         motive op →           ∃ T,             ∀ (s : Stream'.Seq α),
               (op s).destruct =                 Option.map                   (f
un x =>                     match x with                     | (hd, opf, op') =>
 (hd, ↑opf (↑op' s.tail)))                   (T s.head)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.coind`：∀ {α : Type u_1} 
(motive : (Stream'.Seq α → Stream'.Seq α) → Prop) {op : Stream'.Seq α → Stream'.
Seq α},   motive op →     (∀ (op : Stream'.…
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.id`：∀ {α : Type u_1}, Ta
ctic.ComputeAsymptotics.Seq.FriendlyOperation id
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.const`：∀ {α : Type u_1} 
{s : Stream'.Seq α}, Tactic.ComputeAsymptotics.Seq.FriendlyOperation fun x => s
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.comp`：∀ {α : Type u_1} {
op op' : Stream'.Seq α → Stream'.Seq α},   Tactic.ComputeAsymptotics.Seq.Friendl
yOperation op →     Tactic.ComputeAsymptot…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.destruct_apply_eq_unfold
`：∀ {α : Type u_1} {op : Stream'.Seq α → Stream'.Seq α} (h : Tactic.ComputeAsymp
totics.Seq.FriendlyOperation op)   {s : Stream'.Seq α},   (op …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} (h : β → 
γ) (g : α → β) (x : Option α),   Option.map h (Option.map g x) = Option.map (h ∘
 g) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.unfold.congr_simp`：∀ {α 
: Type u_1} {op op_1 : Stream'.Seq α → Stream'.Seq α} (e_op : op = op_1)   (h : 
Tactic.ComputeAsymptotics.Seq.FriendlyOperation op) (hd…
· 使用定理 `Stream'.Seq.head_cons`：head_cons (a : α) (s) : head (cons a s) = some a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Stream'.Seq.destruct_cons`：∀ {α : Type u} (a : α) (s : Stream'.Seq α), (
Stream'.Seq.cons a s).destruct = some (a, s)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)

--- 原说明 ---
A generalisation of `FriendlyOperation.coind` which allows using `opf ∘ op'` in 
the tail
of `op s` where `opf` is friendly and `op'` is a function satisfying `motive`.
-/
theorem FriendlyOperation.coind_comp_friend_left {op : Seq α → Seq α}
    (motive : (Seq α → Seq α) → Prop)
    (h_base : motive op)
    (h_step : ∀ op, motive op →
      ∃ T : Option α → Option (α × Subtype FriendlyOperation × Subtype motive),
      ∀ s, (op s).destruct = (T s.head).map fun (hd, opf, op') => (hd, opf.val <| op'.val s.tail)) :
    FriendlyOperation op := by
  let motive' (op : Seq α → Seq α) : Prop :=
    ∃ opf op', op = opf ∘ op' ∧ FriendlyOperation opf ∧ motive op'
  apply FriendlyOperation.coind motive'
  · exact ⟨_root_.id, op, rfl, FriendlyOperation.id, h_base⟩
  rintro _ ⟨opf, op, rfl, h_opf, h_op⟩
  obtain ⟨T, hT⟩ := h_step _ h_op
  use fun hd? ↦
    match (T hd?) with
    | none => (h_opf.unfold none).map fun (hd, opf') =>
      (hd, ⟨_, fun _ ↦ opf'.val nil, op, rfl, FriendlyOperation.const, h_op⟩)
    | some (hd, opf', op') => (h_opf.unfold (some hd)).map fun (hd', opf'') =>
      (hd', ⟨_, opf''.val ∘ opf'.val, op'.val, rfl,
        FriendlyOperation.comp opf''.prop opf'.prop, op'.prop⟩)
  intro s
  specialize hT s
  simp only [Function.comp_apply]
  generalize op s = s' at *
  cases s' with
  | nil =>
    symm at hT
    simp at hT
    simp [hT, destruct_apply_eq_unfold h_opf]
    rfl
  | cons s_hd s_tl =>
    simp only [destruct_cons] at hT
    simp only [destruct_apply_eq_unfold h_opf, Seq.tail_cons, Seq.head_cons]
    generalize T s.head = t? at *
    cases t? with
    | none => simp at hT
    | some v =>
      obtain ⟨hd, opf', op'⟩ := v
      simp at hT
      simp [hT]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- A generalisation of `FriendlyOperation.coind` that allows using `op' ∘ opf` in the tail
of `op s` where `opf` is friendly and `op'` is a function satisfying `motive`. -/
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperation.coind_comp_friend_right** 是 Ma
thlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation`。
形式化陈述：∀ {α : Type u_1} {op : Stream'.Seq α → Stream'.Seq α} (motive : (Stream'.S
eq α → Stream'.Seq α) → Prop),   motive op →     (∀ (op : Stream'.Seq α → Stream
'.Seq α),         motive op →           ∃ T,             ∀ (s : Stream'.Seq α), 
              (op s).destruct =                 Option.map                   (fu
n x =>                     match x with                     | (hd, opf, op') => 
(hd, ↑op' (↑opf s.tail)))                   (T s.head)) →       Tactic.ComputeAs
ymptotics.Seq.FriendlyOperation op
参数：motive : (Stream'.Seq α → Stream'.Seq α) → Prop；∀ (op : Stream'.Seq α → Strea
m'.Seq α),         motive op →           ∃ T,             ∀ (s : Stream'.Seq α),
               (op s).destruct =                 Option.map                   (f
un x =>                     match x with                     | (hd, opf, op') =>
 (hd, ↑op' (↑opf s.tail)))                   (T s.head)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.coind`：∀ {α : Type u_1} 
(motive : (Stream'.Seq α → Stream'.Seq α) → Prop) {op : Stream'.Seq α → Stream'.
Seq α},   motive op →     (∀ (op : Stream'.…
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.id`：∀ {α : Type u_1}, Ta
ctic.ComputeAsymptotics.Seq.FriendlyOperation id
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.const`：∀ {α : Type u_1} 
{s : Stream'.Seq α}, Tactic.ComputeAsymptotics.Seq.FriendlyOperation fun x => s
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.comp`：∀ {α : Type u_1} {
op op' : Stream'.Seq α → Stream'.Seq α},   Tactic.ComputeAsymptotics.Seq.Friendl
yOperation op →     Tactic.ComputeAsymptot…
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.destruct_apply_eq_unfold
`：∀ {α : Type u_1} {op : Stream'.Seq α → Stream'.Seq α} (h : Tactic.ComputeAsymp
totics.Seq.FriendlyOperation op)   {s : Stream'.Seq α},   (op …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} (h : β → 
γ) (g : α → β) (x : Option α),   Option.map h (Option.map g x) = Option.map (h ∘
 g) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Stream'.Seq.destruct_cons`：∀ {α : Type u} (a : α) (s : Stream'.Seq α), (
Stream'.Seq.cons a s).destruct = some (a, s)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)

--- 原说明 ---
A generalisation of `FriendlyOperation.coind` that allows using `op' ∘ opf` in t
he tail
of `op s` where `opf` is friendly and `op'` is a function satisfying `motive`.
-/
theorem FriendlyOperation.coind_comp_friend_right {op : Seq α → Seq α}
    (motive : (Seq α → Seq α) → Prop)
    (h_base : motive op)
    (h_step : ∀ op, motive op →
      ∃ T : Option α → Option (α × Subtype FriendlyOperation × Subtype motive),
      ∀ s, (op s).destruct = (T s.head).map fun (hd, opf, op') => (hd, op'.val <| opf.val s.tail)) :
    FriendlyOperation op := by
  let motive' (op : Seq α → Seq α) : Prop :=
    ∃ opf op', op = op' ∘ opf ∧ FriendlyOperation opf ∧ motive op'
  apply FriendlyOperation.coind motive'
  · exact ⟨_root_.id, op, rfl, FriendlyOperation.id, h_base⟩
  clear h_base op
  rintro _ ⟨opf, op, rfl, h_opf, h_op⟩
  obtain ⟨T, hT⟩ := h_step _ h_op
  use fun hd? ↦
    match (h_opf.unfold hd?) with
    | none => (T none).map fun (hd, opf', op') =>
      (hd, ⟨_, fun _ ↦ opf'.val nil, op', rfl, FriendlyOperation.const, op'.prop⟩)
    | some (hd, opf') => (T (some hd)).map fun (hd', opf'', op') =>
      (hd', ⟨_, opf''.val ∘ opf'.val, op'.val, rfl,
        FriendlyOperation.comp opf''.prop opf'.prop, op'.prop⟩)
  intro s
  simp only [Function.comp_apply]
  have hF := h_opf.destruct_apply_eq_unfold (s := s)
  generalize opf s = s' at *
  cases s' with
  | nil =>
    symm at hF
    simp only [destruct_nil, Option.map_eq_none_iff] at hF
    simp only [hF, Option.map_map]
    specialize hT nil
    simp only [tail_nil, head_nil] at hT
    simp [hT]
    rfl
  | cons s_hd s_tl =>
  simp only [destruct_cons] at hF
  generalize h_opf.unfold s.head = t? at *
  cases t? with
  | none => simp at hF
  | some v =>
  obtain ⟨hd, opf', op'⟩ := v
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hF
  simp only [hF, Option.map_map]
  rw [hT]
  rfl

/-- A generalisation of `Seq.eq_of_bisim'` that allows using a friendly operation in the tail
of the sequences. -/
/-
**Tactic.ComputeAsymptotics.Seq.FriendlyOperationClass.eq_of_bisim** 是 Mathlib 中
的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.Seq.FriendlyOperationClass`。
形式化陈述：∀ {α : Type u_1} {γ : Type u_3} {s t : Stream'.Seq α} {op : γ → Stream'.Se
q α → Stream'.Seq α}   [Tactic.ComputeAsymptotics.Seq.FriendlyOperationClass op]
 (motive : Stream'.Seq α → Stream'.Seq α → Prop),   motive s t →     (∀ (u v : S
tream'.Seq α),         motive u v →           u = v ∨ ∃ hd u' v' c, u = Stream'.
Seq.cons hd (op c u') ∧ v = Stream'.Seq.cons hd (op c v') ∧ motive u' v') →     
  s = t
参数：motive : Stream'.Seq α → Stream'.Seq α → Prop；∀ (u v : Stream'.Seq α),       
  motive u v →           u = v ∨ ∃ hd u' v' c, u = Stream'.Seq.cons hd (op c u')
 ∧ v = Stream'.Seq.cons hd (op c v') ∧ motive u' v'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Tactic.ComputeAsymptotics.Seq.dist_cons_cons`：dist_cons_cons (x : α) (s 
t : Seq α) : dist (cons x s) (cons x t) = 2⁻¹ * dist s t
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.dist_le`：∀ {α : Type u_1
} {op : Stream'.Seq α → Stream'.Seq α},   Tactic.ComputeAsymptotics.Seq.Friendly
Operation op → ∀ {s t : Stream'.Seq α}, dist …
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperationClass.friend`：∀ {α : Type
 u_1} {γ : Type u_3} {F : γ → Stream'.Seq α → Stream'.Seq α}   [self : Tactic.Co
mputeAsymptotics.Seq.FriendlyOperationClass F] (c…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `ge_of_tendsto'`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter 
β} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
A generalisation of `Seq.eq_of_bisim'` that allows using a friendly operation in
 the tail
of the sequences.
-/
theorem FriendlyOperationClass.eq_of_bisim {s t : Seq α} {op : γ → Seq α → Seq α}
    [FriendlyOperationClass op]
    (motive : Seq α → Seq α → Prop)
    (base : motive s t)
    (step : ∀ u v, motive u v → (u = v) ∨
      ∃ hd u' v' c, u = cons hd (op c u') ∧ v = cons hd (op c v') ∧
        motive u' v') :
    s = t := by
  suffices dist s t = 0 by simpa using this
  suffices ∀ n, dist s t ≤ (2⁻¹ : ℝ) ^ n by
    apply eq_of_le_of_ge
    · apply ge_of_tendsto' (x := Filter.atTop) _ this
      rw [tendsto_pow_atTop_nhds_zero_iff]
      norm_num
    · simp
  intro n
  induction n generalizing s t with
  | zero => simp
  | succ n ih =>
    obtain step | ⟨hd, u, v, c, rfl, rfl, h_next⟩ := step s t base
    · simp [step]
    simp only [dist_cons_cons]
    specialize ih h_next
    calc
      _ ≤ 2⁻¹ * dist u v := by
        gcongr
        exact (FriendlyOperationClass.friend _).dist_le
      _ ≤ _ := by
        grw [ih, pow_succ']

end Tactic.ComputeAsymptotics.Seq

