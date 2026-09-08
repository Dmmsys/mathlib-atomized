/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Infinite sum in a ring

This file provides lemmas about the interaction between infinite sums and multiplication.

## Main results

* `tsum_mul_tsum_eq_tsum_sum_antidiagonal`: Cauchy product formula
* `Summable.tsum_pow_mul_one_sub`, `Summable.one_sub_mul_tsum_pow`: geometric series formula.
* `tprod_one_add`: expanding `∏' i : ι, (1 + f i)` as infinite sum.
-/

public section

open Filter Finset Function

variable {ι κ α : Type*} {L : SummationFilter ι}

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [IsTopologicalSemiring α] {f : ι → α}
  {a₁ : α}

/-
**HasSum.mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun i => a₂ * f i) (a₂ 
* a₁) L
参数：a₂；h : HasSum f a₁ L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun i ↦ a₂ * f i) (a₂ * a₁) L := by
  simpa only using! h.map (AddMonoidHom.mulLeft a₂) (continuous_const.mul continuous_id)
/-
**HasSum.mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.mul_right (a₂) (hf : HasSum f a₁ L) : HasSum (fun i => f i * a₂) (a
₁ * a₂) L
参数：a₂；hf : HasSum f a₁ L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem HasSum.mul_right (a₂) (hf : HasSum f a₁ L) : HasSum (fun i ↦ f i * a₂) (a₁ * a₂) L := by
  simpa only using! hf.map (AddMonoidHom.mulRight a₂) (continuous_id.mul continuous_const)
/-
**Summable.mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.mul_left (a) (hf : Summable f L) : Summable (fun i => a * f i) L
参数：a；hf : Summable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.mul_left (a) (hf : Summable f L) : Summable (fun i ↦ a * f i) L :=
  (hf.hasSum.mul_left _).summable
/-
**Summable.mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.mul_right (a) (hf : Summable f L) : Summable (fun i => f i * a) L
参数：a；hf : Summable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.mul_right`：HasSum.mul_right (a₂) (hf : HasSum f a₁ L) : HasSum (f
un i => f i * a₂) (a₁ * a₂) L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.mul_right (a) (hf : Summable f L) : Summable (fun i ↦ f i * a) L :=
  (hf.hasSum.mul_right _).summable

section tsum

variable [T2Space α] [L.NeBot]

/-
**Summable.tsum_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Summable`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [inst : NonUnitalN
onAssocSemiring α]   [inst_1 : TopologicalSpace α] [IsTopologicalSemiring α] {f 
: ι → α} [T2Space α] [L.NeBot] (a : α),   Summable f L → ∑'[L] (i : ι), a * f i 
= a * ∑'[L] (i : ι), f i
参数：a : α；i : ι；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
protected theorem Summable.tsum_mul_left (a) (hf : Summable f L) :
      ∑'[L] i, a * f i = a * ∑'[L] i, f i :=
  (hf.hasSum.mul_left _).tsum_eq
/-
**Summable.tsum_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Summable`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [inst : NonUnitalN
onAssocSemiring α]   [inst_1 : TopologicalSpace α] [IsTopologicalSemiring α] {f 
: ι → α} [T2Space α] [L.NeBot] (a : α),   Summable f L → ∑'[L] (i : ι), f i * a 
= (∑'[L] (i : ι), f i) * a
参数：a : α；i : ι；∑'[L] (i : ι), f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `HasSum.mul_right`：HasSum.mul_right (a₂) (hf : HasSum f a₁ L) : HasSum (f
un i => f i * a₂) (a₁ * a₂) L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
protected theorem Summable.tsum_mul_right (a) (hf : Summable f L) :
    ∑'[L] i, f i * a = (∑'[L] i, f i) * a :=
  (hf.hasSum.mul_right _).tsum_eq
/-
**SemiconjBy.tsum_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemiconjBy.tsum_left {a b : α} (h : forall (i : ι), SemiconjBy (f i) a b) 
: SemiconjBy (∑'[L] (i : ι), f i) a b
参数：h : forall (i : ι), SemiconjBy (f i) a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.tsum_mul_right`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationF
ilter ι} [inst : NonUnitalNonAssocSemiring α]   [inst_1 : TopologicalSpace α] [I
sTopologicalS…
· 使用定理 `Summable.tsum_mul_left`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFi
lter ι} [inst : NonUnitalNonAssocSemiring α]   [inst_1 : TopologicalSpace α] [Is
TopologicalS…
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsum_eq_zero_of_not_summable`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → 
α}, ¬Summable f L …
-/
theorem SemiconjBy.tsum_left {a b : α} (h : ∀ (i : ι), SemiconjBy (f i) a b) :
    SemiconjBy (∑'[L] (i : ι), f i) a b := by
  by_cases hf : Summable f L
  · rw [SemiconjBy, ← hf.tsum_mul_right a, ← hf.tsum_mul_left b, tsum_congr h]
  · simp [tsum_eq_zero_of_not_summable hf]
/-
**SemiconjBy.tsum_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemiconjBy.tsum_right {f g : ι -> α} (a : α) (hf : Summable f L) (hg : Sum
mable g L) (h : forall (i : ι), SemiconjBy a (f i) (g i)) : SemiconjBy a (∑'[L] 
(i : ι), f i) (∑'[L] (i : ι), g i)
参数：a : α；hf : Summable f L；hg : Summable g L；h : forall (i : ι), SemiconjBy a (f
 i) (g i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.tsum_mul_left`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFi
lter ι} [inst : NonUnitalNonAssocSemiring α]   [inst_1 : TopologicalSpace α] [Is
TopologicalS…
· 使用定理 `Summable.tsum_mul_right`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationF
ilter ι} [inst : NonUnitalNonAssocSemiring α]   [inst_1 : TopologicalSpace α] [I
sTopologicalS…
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
-/
theorem SemiconjBy.tsum_right {f g : ι → α} (a : α) (hf : Summable f L) (hg : Summable g L)
    (h : ∀ (i : ι), SemiconjBy a (f i) (g i)) :
    SemiconjBy a (∑'[L] (i : ι), f i) (∑'[L] (i : ι), g i) := by
  rw [SemiconjBy, ← hf.tsum_mul_left a, ← hg.tsum_mul_right a]
  exact tsum_congr h
/-
**Commute.tsum_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Commute.tsum_left (a) (h : forall i, Commute (f i) a) : Commute (∑'[L] i, 
f i) a
参数：a；h : forall i, Commute (f i) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.tsum_left`：SemiconjBy.tsum_left {a b : α} (h : forall (i : ι)
, SemiconjBy (f i) a b) : SemiconjBy (∑'[L] (i : ι), f i) a b
-/
theorem Commute.tsum_left (a) (h : ∀ i, Commute (f i) a) : Commute (∑'[L] i, f i) a :=
  SemiconjBy.tsum_left h
/-
**Commute.tsum_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Commute.tsum_right (a) (h : forall i, Commute a (f i)) : Commute a (∑'[L] 
i, f i)
参数：a；h : forall i, Commute a (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Commute.tsum_left`：Commute.tsum_left (a) (h : forall i, Commute (f i) a)
 : Commute (∑'[L] i, f i) a
-/
theorem Commute.tsum_right (a) (h : ∀ i, Commute a (f i)) : Commute a (∑'[L] i, f i) :=
  (Commute.tsum_left _ fun i ↦ (h i).symm).symm

end tsum

end NonUnitalNonAssocSemiring

section DivisionSemiring

variable [DivisionSemiring α] [TopologicalSpace α] [IsTopologicalSemiring α]
    {f : ι → α} {a a₁ a₂ : α}

/-
**HasSum.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.div_const (h : HasSum f a L) (b : α) : HasSum (fun i => f i / b) (a
 / b) L
参数：h : HasSum f a L；b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `HasSum.mul_right`：HasSum.mul_right (a₂) (hf : HasSum f a₁ L) : HasSum (f
un i => f i * a₂) (a₁ * a₂) L
-/
theorem HasSum.div_const (h : HasSum f a L) (b : α) : HasSum (fun i ↦ f i / b) (a / b) L := by
  simp only [div_eq_mul_inv, h.mul_right b⁻¹]
/-
**Summable.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.div_const (h : Summable f L) (b : α) : Summable (fun i => f i / b
) L
参数：h : Summable f L；b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.div_const`：HasSum.div_const (h : HasSum f a L) (b : α) : HasSum (
fun i => f i / b) (a / b) L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.div_const (h : Summable f L) (b : α) : Summable (fun i ↦ f i / b) L :=
  (h.hasSum.div_const _).summable
/-
**hasSum_mul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_mul_left_iff (h : a₂ != 0) : HasSum (fun i => a₂ * f i) (a₂ * a₁) L
 ↔ HasSum f a₁ L
参数：h : a₂ != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
-/
theorem hasSum_mul_left_iff (h : a₂ ≠ 0) : HasSum (fun i ↦ a₂ * f i) (a₂ * a₁) L ↔ HasSum f a₁ L :=
  ⟨fun H ↦ by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a₂⁻¹, HasSum.mul_left _⟩
/-
**hasSum_mul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_mul_right_iff (h : a₂ != 0) : HasSum (fun i => f i * a₂) (a₁ * a₂) 
L ↔ HasSum f a₁ L
参数：h : a₂ != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_inv_cancel_right₀`：mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b * b⁻¹ = a
· 使用定理 `HasSum.mul_right`：HasSum.mul_right (a₂) (hf : HasSum f a₁ L) : HasSum (f
un i => f i * a₂) (a₁ * a₂) L
-/
theorem hasSum_mul_right_iff (h : a₂ ≠ 0) : HasSum (fun i ↦ f i * a₂) (a₁ * a₂) L ↔ HasSum f a₁ L :=
  ⟨fun H ↦ by simpa only [mul_inv_cancel_right₀ h] using H.mul_right a₂⁻¹, HasSum.mul_right _⟩
/-
**hasSum_div_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_div_const_iff (h : a₂ != 0) : HasSum (fun i => f i / a₂) (a₁ / a₂) 
L ↔ HasSum f a₁ L
参数：h : a₂ != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `hasSum_mul_right_iff`：hasSum_mul_right_iff (h : a₂ != 0) : HasSum (fun i
 => f i * a₂) (a₁ * a₂) L ↔ HasSum f a₁ L
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem hasSum_div_const_iff (h : a₂ ≠ 0) :
    HasSum (fun i ↦ f i / a₂) (a₁ / a₂) L ↔ HasSum f a₁ L := by
  simpa only [div_eq_mul_inv] using hasSum_mul_right_iff (inv_ne_zero h)
/-
**summable_mul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_mul_left_iff (h : a != 0) : (Summable (fun i => a * f i) L) ↔ Sum
mable f L
参数：h : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
-/
theorem summable_mul_left_iff (h : a ≠ 0) : (Summable (fun i ↦ a * f i) L) ↔ Summable f L :=
  ⟨fun H ↦ by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a⁻¹, fun H ↦ H.mul_left _⟩
/-
**summable_mul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_mul_right_iff (h : a != 0) : (Summable (fun i => f i * a) L) ↔ Su
mmable f L
参数：h : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_inv_cancel_right₀`：mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b * b⁻¹ = a
· 使用定理 `Summable.mul_right`：Summable.mul_right (a) (hf : Summable f L) : Summabl
e (fun i => f i * a) L
-/
theorem summable_mul_right_iff (h : a ≠ 0) : (Summable (fun i ↦ f i * a) L) ↔ Summable f L :=
  ⟨fun H ↦ by simpa only [mul_inv_cancel_right₀ h] using H.mul_right a⁻¹, fun H ↦ H.mul_right _⟩
/-
**summable_div_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_div_const_iff (h : a != 0) : (Summable (fun i => f i / a) L) ↔ Su
mmable f L
参数：h : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `summable_mul_right_iff`：summable_mul_right_iff (h : a != 0) : (Summable 
(fun i => f i * a) L) ↔ Summable f L
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem summable_div_const_iff (h : a ≠ 0) : (Summable (fun i ↦ f i / a) L) ↔ Summable f L := by
  simpa only [div_eq_mul_inv] using summable_mul_right_iff (inv_ne_zero h)
/-
**tsum_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_mul_left [T2Space α] : ∑'[L] x, a * f x = a * ∑'[L] x, f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsClosedEmbedding.map_tsum`：∀ {ι : Type u_4} {α : Type u_5} {α'
 : Type u_6} {G : Type u_7} [inst : AddCommMonoid α] [inst_1 : AddCommMonoid α']
   [inst_2 : TopologicalS…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
-/
theorem tsum_mul_left [T2Space α] :
    ∑'[L] x, a * f x = a * ∑'[L] x, f x := by
  by_cases ha : a = 0
  · simp [ha]
  · exact ((Homeomorph.mulLeft₀ a ha).isClosedEmbedding.map_tsum f
      (g := AddMonoidHom.mulLeft a)).symm
/-
**tsum_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_mul_right [T2Space α] : ∑'[L] x, f x * a = (∑'[L] x, f x) * a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsClosedEmbedding.map_tsum`：∀ {ι : Type u_4} {α : Type u_5} {α'
 : Type u_6} {G : Type u_7} [inst : AddCommMonoid α] [inst_1 : AddCommMonoid α']
   [inst_2 : TopologicalS…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
-/
theorem tsum_mul_right [T2Space α] : ∑'[L] x, f x * a = (∑'[L] x, f x) * a := by
  by_cases ha : a = 0
  · simp [ha]
  · exact ((Homeomorph.mulRight₀ a ha).isClosedEmbedding.map_tsum f
      (g := AddMonoidHom.mulRight a)).symm
/-
**tsum_div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_div_const [T2Space α] : ∑'[L] x, f x / a = (∑'[L] x, f x) / a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `tsum_mul_right`：tsum_mul_right [T2Space α] : ∑'[L] x, f x * a = (∑'[L] x
, f x) * a
-/
theorem tsum_div_const [T2Space α] : ∑'[L] x, f x / a = (∑'[L] x, f x) / a := by
  simpa only [div_eq_mul_inv] using tsum_mul_right
/-
**HasSum.const_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.const_div (h : HasSum (fun x => 1 / f x) a L) (b : α) : HasSum (fun
 i => b / f i) (b * a) L
参数：h : HasSum (fun x => 1 / f x) a L；b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem HasSum.const_div (h : HasSum (fun x ↦ 1 / f x) a L) (b : α) :
    HasSum (fun i ↦ b / f i) (b * a) L := by
  have := h.mul_left b
  simpa only [div_eq_mul_inv, one_mul] using this
/-
**Summable.const_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.const_div (h : Summable (fun x => 1 / f x) L) (b : α) : Summable 
(fun i => b / f i) L
参数：h : Summable (fun x => 1 / f x) L；b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.const_div`：HasSum.const_div (h : HasSum (fun x => 1 / f x) a L) (
b : α) : HasSum (fun i => b / f i) (b * a) L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.const_div (h : Summable (fun x ↦ 1 / f x) L) (b : α) :
    Summable (fun i ↦ b / f i) L :=
  (h.hasSum.const_div b).summable
/-
**hasSum_const_div_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_const_div_iff (h : a₂ != 0) : HasSum (fun i => a₂ / f i) (a₂ * a₁) 
L ↔ HasSum (1 / f) a₁ L
参数：h : a₂ != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `hasSum_mul_left_iff`：hasSum_mul_left_iff (h : a₂ != 0) : HasSum (fun i =
> a₂ * f i) (a₂ * a₁) L ↔ HasSum f a₁ L
-/
theorem hasSum_const_div_iff (h : a₂ ≠ 0) :
    HasSum (fun i ↦ a₂ / f i) (a₂ * a₁) L ↔ HasSum (1 / f) a₁ L := by
  simpa only [div_eq_mul_inv, one_mul] using! hasSum_mul_left_iff h
/-
**summable_const_div_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_const_div_iff (h : a != 0) : (Summable (fun i => a / f i) L) ↔ Su
mmable (1 / f) L
参数：h : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `summable_mul_left_iff`：summable_mul_left_iff (h : a != 0) : (Summable (f
un i => a * f i) L) ↔ Summable f L
-/
theorem summable_const_div_iff (h : a ≠ 0) :
    (Summable (fun i ↦ a / f i) L) ↔ Summable (1 / f) L := by
  simpa only [div_eq_mul_inv, one_mul] using! summable_mul_left_iff h

end DivisionSemiring

/-!
### Multiplying two infinite sums

In this section, we prove various results about `(∑' x : ι, f x) * (∑' y : κ, g y)`. Note that we
always assume that the family `fun x : ι × κ ↦ f x.1 * g x.2` is summable, since there is no way to
deduce this from the summabilities of `f` and `g` in general, but if you are working in a normed
space, you may want to use the analogous lemmas in `Analysis.Normed.Module.Basic`
(e.g `tsum_mul_tsum_of_summable_norm`).

We first establish results about arbitrary index types, `ι` and `κ`, and then we specialize to
`ι = κ = ℕ` to prove the Cauchy product formula (see `tsum_mul_tsum_eq_tsum_sum_antidiagonal`).

#### Arbitrary index types
-/


section tsum_mul_tsum

variable [TopologicalSpace α] [T3Space α] [NonUnitalNonAssocSemiring α] [IsTopologicalSemiring α]
  {f : ι → α} {g : κ → α} {s t u : α}

/-
**HasSum.mul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.mul_eq (hf : HasSum f s) (hg : HasSum g t) (hfg : HasSum (fun x : ι
 × κ => f x.1 * g x.2) u) : s * t = u
参数：hf : HasSum f s；hg : HasSum g t；hfg : HasSum (fun x : ι × κ => f x.1 * g x.2)
 u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.mul_right`：HasSum.mul_right (a₂) (hf : HasSum f a₁ L) : HasSum (f
un i => f i * a₂) (a₁ * a₂) L
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
· 使用定理 `HasSum.prod_fiberwise`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [i
nst : AddCommMonoid α] [inst_1 : TopologicalSpace α] [ContinuousAdd α]   [Regula
rSpace α] {…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
· 使用定理 `HasSum.unique`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} [T2Space α] 
[L.…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
-/
theorem HasSum.mul_eq (hf : HasSum f s) (hg : HasSum g t)
    (hfg : HasSum (fun x : ι × κ ↦ f x.1 * g x.2) u) : s * t = u :=
  have key₁ : HasSum (fun i ↦ f i * t) (s * t) := hf.mul_right t
  have : ∀ i : ι, HasSum (fun c : κ ↦ f i * g c) (f i * t) := fun i ↦ hg.mul_left (f i)
  have key₂ : HasSum (fun i ↦ f i * t) u := HasSum.prod_fiberwise hfg this
  key₁.unique key₂
/-
**HasSum.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.mul (hf : HasSum f s) (hg : HasSum g t) (hfg : Summable fun x : ι ×
 κ => f x.1 * g x.2) : HasSum (fun x : ι × κ => f x.1 * g x.2) (s * t)
参数：hf : HasSum f s；hg : HasSum g t；hfg : Summable fun x : ι × κ => f x.1 * g x.2
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.mul_eq`：HasSum.mul_eq (hf : HasSum f s) (hg : HasSum g t) (hfg : 
HasSum (fun x : ι × κ => f x.1 * g x.2) u) : s * t = u
-/
theorem HasSum.mul (hf : HasSum f s) (hg : HasSum g t)
    (hfg : Summable fun x : ι × κ ↦ f x.1 * g x.2) :
    HasSum (fun x : ι × κ ↦ f x.1 * g x.2) (s * t) :=
  let ⟨_u, hu⟩ := hfg
  (hf.mul_eq hg hu).symm ▸ hu

/-- Product of two infinite sums indexed by arbitrary types.
See also `tsum_mul_tsum_of_summable_norm` if `f` and `g` are absolutely summable. -/
/-
**Summable.tsum_mul_tsum** 是 Mathlib 中的一个定理，位于命名空间 `Summable`。
形式化陈述：∀ {ι : Type u_1} {κ : Type u_2} {α : Type u_3} [inst : TopologicalSpace α]
 [T3Space α]   [inst_2 : NonUnitalNonAssocSemiring α] [IsTopologicalSemiring α] 
{f : ι → α} {g : κ → α},   Summable f →     Summable g → (Summable fun x => f x.
1 * g x.2) → (∑' (x : ι), f x) * ∑' (y : κ), g y = ∑' (z : ι × κ), f z.1 * g z.2
参数：Summable fun x => f x.1 * g x.2；∑' (x : ι), f x；y : κ；z : ι × κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.mul_eq`：HasSum.mul_eq (hf : HasSum f s) (hg : HasSum g t) (hfg : 
HasSum (fun x : ι × κ => f x.1 * g x.2) u) : s * t = u
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…

--- 原说明 ---
Product of two infinite sums indexed by arbitrary types.
See also `tsum_mul_tsum_of_summable_norm` if `f` and `g` are absolutely summable
.
-/
protected theorem Summable.tsum_mul_tsum (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ι × κ ↦ f x.1 * g x.2) :
    ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × κ, f z.1 * g z.2 :=
  hf.hasSum.mul_eq hg.hasSum hfg.hasSum

end tsum_mul_tsum

/-!
#### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range`, where the `n`-th term is a sum over `Finset.range (n+1)`
involving `Nat` subtraction.
In order to avoid `Nat` subtraction, we also provide `tsum_mul_tsum_eq_tsum_sum_antidiagonal`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`Finset` `Finset.antidiagonal n`.
This in fact allows us to generalize to any type satisfying `[Finset.HasAntidiagonal A]`
-/


section CauchyProduct

section HasAntidiagonal
variable {A : Type*} [AddCommMonoid A] [HasAntidiagonal A]
variable [TopologicalSpace α] [NonUnitalNonAssocSemiring α] {f g : A → α}

/-- The family `(k, l) : ℕ × ℕ ↦ f k * g l` is summable if and only if the family
`(n, k, l) : Σ (n : ℕ), antidiagonal n ↦ f k * g l` is summable. -/
/-
**summable_mul_prod_iff_summable_mul_sigma_antidiagonal** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：summable_mul_prod_iff_summable_mul_sigma_antidiagonal : (Summable fun x : 
A × A => f x.1 * g x.2) ↔ Summable fun x : Σ n : A, antidiagonal n => f (x.2 : A
 × A).1 * g (x.2 : A × A).2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.summable_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   (e : γ ≃ β), Sum
mable (f…

--- 原说明 ---
The family `(k, l) : ℕ × ℕ ↦ f k * g l` is summable if and only if the family
`(n, k, l) : Σ (n : ℕ), antidiagonal n ↦ f k * g l` is summable.
-/
theorem summable_mul_prod_iff_summable_mul_sigma_antidiagonal :
    (Summable fun x : A × A ↦ f x.1 * g x.2) ↔
      Summable fun x : Σ n : A, antidiagonal n ↦ f (x.2 : A × A).1 * g (x.2 : A × A).2 :=
  Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.symm

variable [T3Space α] [IsTopologicalSemiring α]
/-
**summable_sum_mul_antidiagonal_of_summable_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_sum_mul_antidiagonal_of_summable_mul (h : Summable fun x : A × A 
=> f x.1 * g x.2) : Summable fun n => ∑ kl in antidiagonal n, f kl.1 * g kl.2
参数：h : Summable fun x : A × A => f x.1 * g x.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_finset_coe`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMo
noid M] (f : ι → M) (s : Finset ι), ∑ i, f ↑i = ∑ i ∈ s, f i
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Summable.sigma'`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] [ContinuousAdd α]   [RegularSpace α] {γ : β → Ty
pe u_…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
· 使用定理 `summable_mul_prod_iff_summable_mul_sigma_antidiagonal`：summable_mul_prod
_iff_summable_mul_sigma_antidiagonal : (Summable fun x : A × A => f x.1 * g x.2)
 ↔ Summable fun x : Σ n : A, antidiagonal n…
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `hasSum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] [inst_2 : Fintype β] (f : β → α)   (L : optParam 
(Sum…
-/
theorem summable_sum_mul_antidiagonal_of_summable_mul
    (h : Summable fun x : A × A ↦ f x.1 * g x.2) :
    Summable fun n ↦ ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 := by
  rw [summable_mul_prod_iff_summable_mul_sigma_antidiagonal] at h
  conv => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  exact h.sigma' fun n ↦ (hasSum_fintype _).summable

/-- The **Cauchy product formula** for the product of two infinite sums indexed by `ℕ`, expressed
by summing on `Finset.HasAntidiagonal.antidiagonal`.

See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` if `f` and `g` are absolutely
summable. -/
/-
**Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Sum
mable`。
形式化陈述：∀ {α : Type u_3} {A : Type u_4} [inst : AddCommMonoid A] [inst_1 : Finset.
HasAntidiagonal A]   [inst_2 : TopologicalSpace α] [inst_3 : NonUnitalNonAssocSe
miring α] {f g : A → α} [T3Space α]   [IsTopologicalSemiring α],   Summable f → 
    Summable g →       (Summable fun x => f x.1 * g x.2) →         (∑' (n : A), 
f n) * ∑' (n : A), g n = ∑' (n : A), ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal 
n, f kl.1 * g kl.2
参数：Summable fun x => f x.1 * g x.2；∑' (n : A), f n；n : A；n : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_finset_coe`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMo
noid M] (f : ι → M) (s : Finset ι), ∑ i, f ↑i = ∑ i ∈ s, f i
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Summable.tsum_mul_tsum`：∀ {ι : Type u_1} {κ : Type u_2} {α : Type u_3} [
inst : TopologicalSpace α] [T3Space α]   [inst_2 : NonUnitalNonAssocSemiring α] 
[IsTopologic…
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `Summable.tsum_sigma'`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMon
oid α] [inst_1 : TopologicalSpace α] [ContinuousAdd α] [T3Space α]   {γ : β → Ty
pe u_4} {f…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `hasSum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] [inst_2 : Fintype β] (f : β → α)   (L : optParam 
(Sum…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `summable_mul_prod_iff_summable_mul_sigma_antidiagonal`：summable_mul_prod
_iff_summable_mul_sigma_antidiagonal : (Summable fun x : A × A => f x.1 * g x.2)
 ↔ Summable fun x : Σ n : A, antidiagonal n…

--- 原说明 ---
The **Cauchy product formula** for the product of two infinite sums indexed by `
ℕ`, expressed
by summing on `Finset.HasAntidiagonal.antidiagonal`.

See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` if `f` and `g
` are absolutely
summable.
-/
protected theorem Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal (hf : Summable f)
    (hg : Summable g) (hfg : Summable fun x : A × A ↦ f x.1 * g x.2) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 := by
  conv_rhs => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  rw [hf.tsum_mul_tsum hg hfg, ← HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq (_ : A × A → α)]
  exact (summable_mul_prod_iff_summable_mul_sigma_antidiagonal.mp hfg).tsum_sigma'
    (fun n ↦ (hasSum_fintype _).summable)

end HasAntidiagonal

section Nat

variable [TopologicalSpace α] [NonUnitalNonAssocSemiring α] {f g : ℕ → α}
variable [T3Space α] [IsTopologicalSemiring α]

/-
**summable_sum_mul_range_of_summable_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_sum_mul_range_of_summable_mul (h : Summable fun x : Nat × Nat => 
f x.1 * g x.2) : Summable fun n => ∑ k in range (n + 1), f k * g (n - k)
参数：h : Summable fun x : Nat × Nat => f x.1 * g x.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`：∀ {M : Type u_3} [inst : 
AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.antidi
agonal n, f ij.1 ij.2 = ∑ k ∈ Finse…
· 使用定理 `summable_sum_mul_antidiagonal_of_summable_mul`：summable_sum_mul_antidiag
onal_of_summable_mul (h : Summable fun x : A × A => f x.1 * g x.2) : Summable fu
n n => ∑ kl in antidiagonal n, f kl…
-/
theorem summable_sum_mul_range_of_summable_mul (h : Summable fun x : ℕ × ℕ ↦ f x.1 * g x.2) :
    Summable fun n ↦ ∑ k ∈ range (n + 1), f k * g (n - k) := by
  simp_rw [← Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k * g l]
  exact summable_sum_mul_antidiagonal_of_summable_mul h

/-- The **Cauchy product formula** for the product of two infinite sums indexed by `ℕ`, expressed
by summing on `Finset.range`.

See also `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm` if `f` and `g` are absolutely summable.
-/
/-
**Summable.tsum_mul_tsum_eq_tsum_sum_range** 是 Mathlib 中的一个定理，位于命名空间 `Summable`。
形式化陈述：∀ {α : Type u_3} [inst : TopologicalSpace α] [inst_1 : NonUnitalNonAssocSe
miring α] {f g : ℕ → α} [T3Space α]   [IsTopologicalSemiring α],   Summable f → 
    Summable g →       (Summable fun x => f x.1 * g x.2) →         (∑' (n : ℕ), 
f n) * ∑' (n : ℕ), g n = ∑' (n : ℕ), ∑ k ∈ Finset.range (n + 1), f k * g (n - k)
参数：Summable fun x => f x.1 * g x.2；∑' (n : ℕ), f n；n : ℕ；n : ℕ；n + 1；n - k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`：∀ {M : Type u_3} [inst : 
AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.antidi
agonal n, f ij.1 ij.2 = ∑ k ∈ Finse…
· 使用定理 `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`：∀ {α : Type u_3} {A : T
ype u_4} [inst : AddCommMonoid A] [inst_1 : Finset.HasAntidiagonal A]   [inst_2 
: TopologicalSpace α] [inst_3 : NonUn…

--- 原说明 ---
The **Cauchy product formula** for the product of two infinite sums indexed by `
ℕ`, expressed
by summing on `Finset.range`.

See also `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm` if `f` and `g` are a
bsolutely summable.
-/
protected theorem Summable.tsum_mul_tsum_eq_tsum_sum_range (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ℕ × ℕ ↦ f x.1 * g x.2) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k ∈ range (n + 1), f k * g (n - k) := by
  simp_rw [← Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k * g l]
  exact hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hfg

end Nat

end CauchyProduct

section GeomSeries

/-!
### Geometric series `∑' n : ℕ, x ^ n`

This section gives a general result about geometric series without assuming additional structure on
the topological ring. For normed ring, see also `geom_series_mul_neg` and friends.
-/

variable [Ring α] [TopologicalSpace α] [IsTopologicalRing α] [T2Space α]

/-
**Summable.tsum_pow_mul_one_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.tsum_pow_mul_one_sub {x : α} (h : Summable (x ^ ·)) : (∑' (i : Na
t), x ^ i) * (1 - x) = 1
参数：h : Summable (x ^ ·)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `HasSum.tendsto_sum_nat`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {m : M} {f : ℕ → M},   HasSum f m → Filter.Tendsto (fun 
n => ∑ i ∈ F…
· 使用定理 `HasSum.mul_right`：HasSum.mul_right (a₂) (hf : HasSum f a₁ L) : HasSum (f
un i => f i * a₂) (a₁ * a₂) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `geom_sum_mul_neg`：geom_sum_mul_neg (x : R) (n : Nat) : (∑ i in range n, 
x ^ i) * (1 - x) = 1 - x ^ n
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Summable.tendsto_atTop_zero`：∀ {G : Type u_2} [inst : AddCommGroup G] [i
nst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G},   Summable f 
→ Filter.Tendsto …
-/
theorem Summable.tsum_pow_mul_one_sub {x : α} (h : Summable (x ^ ·)) :
    (∑' (i : ℕ), x ^ i) * (1 - x) = 1 := by
  refine tendsto_nhds_unique (h.hasSum.mul_right (1 - x)).tendsto_sum_nat ?_
  simpa [← Finset.sum_mul, geom_sum_mul_neg] using tendsto_const_nhds.sub h.tendsto_atTop_zero
/-
**Summable.one_sub_mul_tsum_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.one_sub_mul_tsum_pow {x : α} (h : Summable (x ^ ·)) : (1 - x) * ∑
' (i : Nat), x ^ i = 1
参数：h : Summable (x ^ ·)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `HasSum.tendsto_sum_nat`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {m : M} {f : ℕ → M},   HasSum f m → Filter.Tendsto (fun 
n => ∑ i ∈ F…
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `mul_neg_geom_sum`：mul_neg_geom_sum (x : R) (n : Nat) : ((1 - x) * ∑ i in
 range n, x ^ i) = 1 - x ^ n
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Summable.tendsto_atTop_zero`：∀ {G : Type u_2} [inst : AddCommGroup G] [i
nst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G},   Summable f 
→ Filter.Tendsto …
-/
theorem Summable.one_sub_mul_tsum_pow {x : α} (h : Summable (x ^ ·)) :
    (1 - x) * ∑' (i : ℕ), x ^ i = 1 := by
  refine tendsto_nhds_unique (h.hasSum.mul_left (1 - x)).tendsto_sum_nat ?_
  simpa [← Finset.mul_sum, mul_neg_geom_sum] using tendsto_const_nhds.sub h.tendsto_atTop_zero

end GeomSeries

section ProdOneSum

/-!
### Infinite product of `1 + f i`

This section extends `Finset.prod_one_add` to the infinite product
`∏' i : ι, (1 + f i) = ∑' s : Finset ι, ∏ i ∈ s, f i`.
-/

variable [CommSemiring α] [TopologicalSpace α] {f : ι → α}

/-
**hasProd_one_add_of_hasSum_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_one_add_of_hasSum_prod {a : α} (h : HasSum (∏ i in ·, f i) a) : Ha
sProd (1 + f ·) a
参数：h : HasSum (∏ i in ·, f i) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_one_add`：prod_one_add {f : ι -> R} (s : Finset ι) : ∏ i in s
, (1 + f i) = ∑ t in s.powerset, ∏ i in t, f i
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_finset_powerset_atTop_atTop`：tendsto_finset_powerset_atTo
p_atTop : Tendsto (Finset.powerset (α
-/
theorem hasProd_one_add_of_hasSum_prod {a : α} (h : HasSum (∏ i ∈ ·, f i) a) :
    HasProd (1 + f ·) a := by
  simp_rw [HasProd, prod_one_add]
  exact h.comp tendsto_finset_powerset_atTop_atTop

/-- `∏' i : ι, (1 + f i)` is convergent if `∑' s : Finset ι, ∏ i ∈ s, f i` is convergent.

For complete normed ring, see also `multipliable_one_add_of_summable`. -/
/-
**multipliable_one_add_of_summable_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_one_add_of_summable_prod (h : Summable (∏ i in ·, f i)) : Mul
tipliable (1 + f ·)
参数：h : Summable (∏ i in ·, f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasProd_one_add_of_hasSum_prod`：hasProd_one_add_of_hasSum_prod {a : α} (
h : HasSum (∏ i in ·, f i) a) : HasProd (1 + f ·) a

--- 原说明 ---
`∏' i : ι, (1 + f i)` is convergent if `∑' s : Finset ι, ∏ i ∈ s, f i` is conver
gent.

For complete normed ring, see also `multipliable_one_add_of_summable`.
-/
theorem multipliable_one_add_of_summable_prod (h : Summable (∏ i ∈ ·, f i)) :
    Multipliable (1 + f ·) := by
  obtain ⟨a, h⟩ := h
  exact ⟨a, hasProd_one_add_of_hasSum_prod h⟩
/-
**tprod_one_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_one_add [T2Space α] (h : Summable (∏ i in ·, f i)) : ∏' i, (1 + f i)
 = ∑' s, ∏ i in s, f i
参数：h : Summable (∏ i in ·, f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `hasProd_one_add_of_hasSum_prod`：hasProd_one_add_of_hasSum_prod {a : α} (
h : HasSum (∏ i in ·, f i) a) : HasProd (1 + f ·) a
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem tprod_one_add [T2Space α] (h : Summable (∏ i ∈ ·, f i)) :
    ∏' i, (1 + f i) = ∑' s, ∏ i ∈ s, f i :=
  HasProd.tprod_eq <| hasProd_one_add_of_hasSum_prod h.hasSum

section Ordered
variable [LinearOrder ι] [LocallyFiniteOrderBot ι]

/-- The infinite version of `Finset.prod_one_add_ordered`. -/
/-
**tprod_one_add_ordered** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_one_add_ordered [T2Space α] [ContinuousAdd α] (hsum : Summable fun i
 => f i * ∏ j in Iio i, (1 + f j)) (hprod : Multipliable (1 + f ·)) : ∏' i, (1 +
 f i) = 1 + ∑' i, f i * ∏ j in Iio i, (1 + f j)
参数：hsum : Summable fun i => f i * ∏ j in Iio i, (1 + f j)；hprod : Multipliable (
1 + f ·)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_empty`：tprod_empty [IsEmpty β] : ∏'[L] b, f b = 1
· 使用定理 `tsum_empty`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [IsEmpty β], ∑'
…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_one_add_ordered`：prod_one_add_ordered [LinearOrder ι] (s : F
inset ι) (f : ι -> R) : ∏ i in s, (1 + f i) = 1 + ∑ i in s, f i * ∏ j in s with 
j < i, (1 + f j)
· 使用定理 `Filter.tendsto_finset_Iic_atTop_atTop`：tendsto_finset_Iic_atTop_atTop [P
reorder α] [LocallyFiniteOrderBot α] : Tendsto (Finset.Iic (α
· 使用定理 `Filter.Tendsto.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [
inst_1 : Add M] [SeparatelyContinuousAdd M] {α : Type u_2} {f : α → M}   {x : Fi
lter α} {a : M…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a

--- 原说明 ---
The infinite version of `Finset.prod_one_add_ordered`.
-/
theorem tprod_one_add_ordered [T2Space α] [ContinuousAdd α]
    (hsum : Summable fun i ↦ f i * ∏ j ∈ Iio i, (1 + f j))
    (hprod : Multipliable (1 + f ·)) :
    ∏' i, (1 + f i) = 1 + ∑' i, f i * ∏ j ∈ Iio i, (1 + f j) := by
  rcases isEmpty_or_nonempty ι with _ | _
  · simp
  obtain ⟨x, hx⟩ := hprod
  obtain ⟨a, ha⟩ := hsum
  convert! hx.tprod_eq
  unfold HasProd at hx
  conv at hx in fun _ ↦ _ => ext _; rw [prod_one_add_ordered] -- simp_rw would cause loop
  rw [ha.tsum_eq]
  refine (tendsto_nhds_unique (hx.comp tendsto_finset_Iic_atTop_atTop) ?_).symm
  apply Tendsto.const_add
  convert! ha.comp tendsto_finset_Iic_atTop_atTop using 2 with s
  refine sum_congr rfl (fun i hi ↦ ?_)
  congr
  grind

/-- The infinite version of `Finset.prod_one_sub_ordered`. -/
/-
**tprod_one_sub_ordered** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_one_sub_ordered {α : Type*} {f : ι -> α} [CommRing α] [TopologicalSp
ace α] [T2Space α] [IsTopologicalAddGroup α] (hsum : Summable fun i => f i * ∏ j
 in Iio i, (1 - f j)) (hprod : Multipliable (1 - f ·)) : ∏' i, (1 - f i) = 1 - ∑
' i, f i * ∏ j in Iio i, (1 - f j)
参数：hsum : Summable fun i => f i * ∏ j in Iio i, (1 - f j)；hprod : Multipliable (
1 - f ·)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `tprod_one_add_ordered`：tprod_one_add_ordered [T2Space α] [ContinuousAdd 
α] (hsum : Summable fun i => f i * ∏ j in Iio i, (1 + f j)) (hprod : Multipliabl
e (1 + f ·)…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Summable.neg`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [i
nst : AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGroup α] 
{f…

--- 原说明 ---
The infinite version of `Finset.prod_one_sub_ordered`.
-/
theorem tprod_one_sub_ordered {α : Type*} {f : ι → α}
    [CommRing α] [TopologicalSpace α] [T2Space α] [IsTopologicalAddGroup α]
    (hsum : Summable fun i ↦ f i * ∏ j ∈ Iio i, (1 - f j))
    (hprod : Multipliable (1 - f ·)) :
    ∏' i, (1 - f i) = 1 - ∑' i, f i * ∏ j ∈ Iio i, (1 - f j) := by
  simp_rw [sub_eq_add_neg] at hsum hprod ⊢
  obtain hsum' := hsum.neg
  simp_rw [← neg_mul] at hsum'
  simp_rw [← tsum_neg, ← neg_mul]
  exact tprod_one_add_ordered hsum' hprod

end Ordered

end ProdOneSum

