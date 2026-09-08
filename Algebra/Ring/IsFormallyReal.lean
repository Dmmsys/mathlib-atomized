/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Formally real rings

A ring `R` is *formally real* if, whenever `∑ i, x i ^ 2 = 0`, in fact `x i = 0` for all `i`.

We define formally real rings in an index-free manner using the inductive predicate
`IsSumNonzeroSq`, which asserts that an element is a finite sum of squares of nonzero elements.
A ring is then formally real if `¬ IsSumNonzeroSq 0`.

## Main declaration

- `IsFormallyReal`: typeclass stating that a ring is formally real.

-/

@[expose] public section

variable {R : Type*}

section IsSumNonzeroSq

/--
The property of being a sum of squares of nonzero elements (S) is defined inductively by:
`a * a : R` is (S) for all nonzero `a`, and
if `s : R` is (S), and `a ≠ 0`, then `a * a + s` is (S).
-/
@[mk_iff]
/-
**IsSumNonzeroSq** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} → [Mul R] → [Add R] → [Zero R] → R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of being a sum of squares of nonzero elements (S) is defined induct
ively by:
`a * a : R` is (S) for all nonzero `a`, and
if `s : R` is (S), and `a ≠ 0`, then `a * a + s` is (S).
-/
inductive IsSumNonzeroSq [Mul R] [Add R] [Zero R] : R → Prop
  | sq {a : R} (ha : a ≠ 0) : IsSumNonzeroSq (a * a)
  | sq_add {a s : R} (ha : a ≠ 0) (hs : IsSumNonzeroSq s) : IsSumNonzeroSq (a * a + s)

attribute [aesop 90%] IsSumNonzeroSq.sq

@[aesop 90%]
/-
**IsSumNonzeroSq.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSumNonzeroSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R} (h₁ : IsSumNonzeroSq 
s₁) (h₂ : IsSumNonzeroSq s₂) : IsSumNonzeroSq (s₁ + s₂)
参数：h₁ : IsSumNonzeroSq s₁；h₂ : IsSumNonzeroSq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem IsSumNonzeroSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R}
    (h₁ : IsSumNonzeroSq s₁) (h₂ : IsSumNonzeroSq s₂) : IsSumNonzeroSq (s₁ + s₂) := by
  induction h₁ <;> simp_all [sq_add, add_assoc]
/-
**IsSumNonzeroSq.isSumSq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSumNonzeroSq.isSumSq [AddMonoid R] [Mul R] {s : R} (h : IsSumNonzeroSq s
) : IsSumSq s
参数：h : IsSumNonzeroSq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsSumSq.add`：IsSumSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R} (h₁ : IsSumSq
 s₁) (h₂ : IsSumSq s₂) : IsSumSq (s₁ + s₂)
-/
theorem IsSumNonzeroSq.isSumSq [AddMonoid R] [Mul R] {s : R}
    (h : IsSumNonzeroSq s) : IsSumSq s := by
  induction h <;> aesop
/-
**isSumNonzeroSq_iff_isSumSq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSumNonzeroSq_iff_isSumSq [NonUnitalNonAssocSemiring R] {s : R} (hs : s !
= 0) : IsSumNonzeroSq s ↔ IsSumSq s where mp
参数：hs : s != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSumNonzeroSq.isSumSq`：IsSumNonzeroSq.isSumSq [AddMonoid R] [Mul R] {s 
: R} (h : IsSumNonzeroSq s) : IsSumSq s
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem isSumNonzeroSq_iff_isSumSq [NonUnitalNonAssocSemiring R] {s : R} (hs : s ≠ 0) :
    IsSumNonzeroSq s ↔ IsSumSq s where
  mp := IsSumNonzeroSq.isSumSq
  mpr h := by
    induction h with
    | zero => grind
    | @sq_add a s hs ih =>
    rcases eq_or_ne a 0 with (rfl | ne_a)
    · simp_all
    · rcases eq_or_ne s 0 with (rfl | ne_s)
      · simpa using IsSumNonzeroSq.sq ne_a
      · exact IsSumNonzeroSq.sq_add ne_a (ih ne_s)

alias ⟨_, IsSumSq.isSumNonzeroSq_of_ne_zero⟩ := isSumNonzeroSq_iff_isSumSq

namespace AddSubsemigroup

variable [AddMonoid R] [Mul R] {s : R}

variable (R) in
/-- The subsemigroup of sums of squares of nonzero elements. -/
@[simps]
/-
**AddSubsemigroup.sumNonzeroSq** 是 Mathlib 中的一个定义，位于命名空间 `AddSubsemigroup`。
形式化陈述：sumNonzeroSq : AddSubsemigroup R where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsSumNonzeroSq.add`：IsSumNonzeroSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R}
 (h₁ : IsSumNonzeroSq s₁) (h₂ : IsSumNonzeroSq s₂) : IsSumNonzeroSq (s₁ + s₂)

--- 原说明 ---
The subsemigroup of sums of squares of nonzero elements.
-/
def sumNonzeroSq : AddSubsemigroup R where
  carrier := {s : R | IsSumNonzeroSq s}
  add_mem' := .add

attribute [norm_cast] coe_sumNonzeroSq
/-
**AddSubsemigroup.mem_sumNonzeroSq** 是 Mathlib 中的一个定理，位于命名空间 `AddSubsemigroup`。
形式化陈述：∀ {R : Type u_1} [inst : AddMonoid R] [inst_1 : Mul R] {s : R}, s ∈ AddSub
semigroup.sumNonzeroSq R ↔ IsSumNonzeroSq s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mem_sumNonzeroSq : s ∈ sumNonzeroSq R ↔ IsSumNonzeroSq s := .rfl

@[simp]
/-
**AddSubsemigroup.closure_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `AddSubsemigroup`。
形式化陈述：closure_mul_self : closure {x * x | x != (0 : R)} = sumNonzeroSq R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubsemigroup.closure_eq_of_le`：∀ {M : Type u_1} [inst : Add M] {s : S
et M} {S : AddSubsemigroup M},   s ⊆ ↑S → S ≤ AddSubsemigroup.closure s → AddSub
semigroup.closure s = …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubsemigroup.coe_sumNonzeroSq`：∀ (R : Type u_1) [inst : AddMonoid R] 
[inst_1 : Mul R], ↑(AddSubsemigroup.sumNonzeroSq R) = {s | IsSumNonzeroSq s}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AddSubsemigroup.mem_closure_of_mem`：∀ {M : Type u_1} [inst : Add M] {s :
 Set M} {x : M}, x ∈ s → x ∈ AddSubsemigroup.closure s
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubsemigroup.instAddMemClass`：∀ {M : Type u_1} [inst : Add M], AddMem
Class (AddSubsemigroup M) M
-/
theorem closure_mul_self : closure {x * x | x ≠ (0 : R)} = sumNonzeroSq R := by
  refine closure_eq_of_le (fun x hx ↦ by aesop) (fun x hx ↦ ?_)
  -- TODO : fix aesop timeout and change to `induction hx <;> aesop`
  induction hx with
  | sq ha => aesop
  | sq_add ha hs ih =>
    -- `aesop` times out
    apply add_mem
    · apply AddSubsemigroup.mem_closure_of_mem
      aesop
    aesop

end AddSubsemigroup

end IsSumNonzeroSq

variable (R) in
/--
A ring is formally real if, whenever `∑ i, x i ^ 2 = 0`, we in fact have `x i = 0` for all `i`.
-/
/-
**IsFormallyReal** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [AddCommMonoid R] → [Mul R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring is formally real if, whenever `∑ i, x i ^ 2 = 0`, we in fact have `x i = 
0` for all `i`.
-/
class IsFormallyReal [AddCommMonoid R] [Mul R] : Prop where
  not_isSumNonzeroSq_zero : ¬ IsSumNonzeroSq (0 : R)

namespace IsFormallyReal

/-
**IsFormallyReal.of_eq_zero_of_mul_self_of_eq_zero_of_add** 是 Mathlib 中的一个定理，位于命
名空间 `IsFormallyReal`。
形式化陈述：of_eq_zero_of_mul_self_of_eq_zero_of_add [AddCommMonoid R] [Mul R] (hz : f
orall {a : R}, a * a = 0 -> a = 0) (ha : forall {s₁ s₂ : R}, IsSumSq s₁ -> IsSum
Sq s₂ -> s₁ + s₂ = 0 -> s₁ = 0) : IsFormallyReal R where not_isSumNonzeroSq_zero
参数：hz : forall {a : R}, a * a = 0 -> a = 0；ha : forall {s₁ s₂ : R}, IsSumSq s₁ -
> IsSumSq s₂ -> s₁ + s₂ = 0 -> s₁ = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_eq_zero_of_mul_self_of_eq_zero_of_add [AddCommMonoid R] [Mul R]
    (hz : ∀ {a : R}, a * a = 0 → a = 0)
    (ha : ∀ {s₁ s₂ : R}, IsSumSq s₁ → IsSumSq s₂ → s₁ + s₂ = 0 → s₁ = 0) : IsFormallyReal R where
  not_isSumNonzeroSq_zero := by
    suffices ∀ (x : R), IsSumNonzeroSq x → x ≠ 0 by grind
    intro x hx
    induction hx with
    | sq ha => grind
    | @sq_add b s hb hs ih => grind [ha (IsSumSq.mul_self b) hs.isSumSq]
/-
**IsFormallyReal.of_eq_zero_of_eq_zero_of_mul_self_add** 是 Mathlib 中的一个定理，位于命名空间
 `IsFormallyReal`。
形式化陈述：of_eq_zero_of_eq_zero_of_mul_self_add [NonUnitalNonAssocSemiring R] (h : f
orall {s a : R}, IsSumSq s -> a * a + s = 0 -> a = 0) : IsFormallyReal R where n
ot_isSumNonzeroSq_zero
参数：h : forall {s a : R}, IsSumSq s -> a * a + s = 0 -> a = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem of_eq_zero_of_eq_zero_of_mul_self_add [NonUnitalNonAssocSemiring R]
    (h : ∀ {s a : R}, IsSumSq s → a * a + s = 0 → a = 0) : IsFormallyReal R where
  not_isSumNonzeroSq_zero := by
    suffices ∀ (x : R), IsSumNonzeroSq x → x ≠ 0 by grind
    intro x hx
    induction hx with
    | sq ha => exact fun hc ↦ ha (h IsSumSq.zero (by simpa using hc))
    | sq_add ha hs ih => grind [hs.isSumSq]
/-
**IsFormallyReal.** 是 Mathlib 中的一个实例，位于命名空间 `IsFormallyReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring R] [LinearOrder R] [IsStrictOrderedRing R] : IsFormallyReal R :=
  of_eq_zero_of_mul_self_of_eq_zero_of_add mul_self_eq_zero.mp <|
    fun hs₁ hs₂ h ↦ ((add_eq_zero_iff_of_nonneg (IsSumSq.nonneg hs₁) (IsSumSq.nonneg hs₂)).mp h).1
/-
**IsFormallyReal.** 是 Mathlib 中的一个实例，位于命名空间 `IsFormallyReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring R] [IsFormallyReal R] : IsReduced R := by
  rw [isReduced_iff_pow_one_lt 2 (by lia)]
  intro x hx
  by_contra! hc
  exact not_isSumNonzeroSq_zero <| by simpa [← pow_two, hx] using IsSumNonzeroSq.sq hc
/-
**IsFormallyReal.eq_zero_of_add_right** 是 Mathlib 中的一个定理，位于命名空间 `IsFormallyReal`
。
形式化陈述：eq_zero_of_add_right [NonUnitalNonAssocSemiring R] [IsFormallyReal R] {s₁ 
s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0) : s₁ = 0
参数：hs₁ : IsSumSq s₁；hs₂ : IsSumSq s₂；h : s₁ + s₂ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `IsFormallyReal.not_isSumNonzeroSq_zero`：∀ {R : Type u_1} {inst : AddComm
Monoid R} {inst_1 : Mul R} [self : IsFormallyReal R], ¬IsSumNonzeroSq 0
· 使用定理 `IsSumNonzeroSq.add`：IsSumNonzeroSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R}
 (h₁ : IsSumNonzeroSq s₁) (h₂ : IsSumNonzeroSq s₂) : IsSumNonzeroSq (s₁ + s₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isSumNonzeroSq_iff_isSumSq`：isSumNonzeroSq_iff_isSumSq [NonUnitalNonAsso
cSemiring R] {s : R} (hs : s != 0) : IsSumNonzeroSq s ↔ IsSumSq s where mp
-/
theorem eq_zero_of_add_right [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
    {s₁ s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0) : s₁ = 0 := by
  by_contra! h₁
  have h₂ : s₂ ≠ 0 := fun hc ↦ by simp_all
  rw [← isSumNonzeroSq_iff_isSumSq h₁] at hs₁
  rw [← isSumNonzeroSq_iff_isSumSq h₂] at hs₂
  exact not_isSumNonzeroSq_zero (h ▸ IsSumNonzeroSq.add hs₁ hs₂)
/-
**IsFormallyReal.eq_zero_of_add_left** 是 Mathlib 中的一个定理，位于命名空间 `IsFormallyReal`。
形式化陈述：eq_zero_of_add_left [NonUnitalNonAssocSemiring R] [IsFormallyReal R] {s₁ s
₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0) : s₂ = 0
参数：hs₁ : IsSumSq s₁；hs₂ : IsSumSq s₂；h : s₁ + s₂ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFormallyReal.eq_zero_of_add_right`：eq_zero_of_add_right [NonUnitalNonA
ssocSemiring R] [IsFormallyReal R] {s₁ s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq
 s₂) (h : s₁ + s₂ = 0) : …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_zero_of_add_left [NonUnitalNonAssocSemiring R] [IsFormallyReal R]
    {s₁ s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq s₂) (h : s₁ + s₂ = 0) : s₂ = 0 := by
  simp_all [eq_zero_of_add_right hs₁ hs₂ h]
/-
**IsFormallyReal.eq_zero_of_isSumSq_of_neg_isSumSq** 是 Mathlib 中的一个定理，位于命名空间 `Is
FormallyReal`。
形式化陈述：eq_zero_of_isSumSq_of_neg_isSumSq [NonUnitalNonAssocRing R] [IsFormallyRea
l R] {s : R} (h₁ : IsSumSq s) (h₂ : IsSumSq (-s)) : s = 0
参数：h₁ : IsSumSq s；h₂ : IsSumSq (-s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFormallyReal.eq_zero_of_add_right`：eq_zero_of_add_right [NonUnitalNonA
ssocSemiring R] [IsFormallyReal R] {s₁ s₂ : R} (hs₁ : IsSumSq s₁) (hs₂ : IsSumSq
 s₂) (h : s₁ + s₂ = 0) : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_zero_of_isSumSq_of_neg_isSumSq [NonUnitalNonAssocRing R] [IsFormallyReal R]
    {s : R} (h₁ : IsSumSq s) (h₂ : IsSumSq (-s)) : s = 0 :=
  eq_zero_of_add_right h₁ h₂ (by simp)

end IsFormallyReal

