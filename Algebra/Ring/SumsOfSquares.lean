/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
module

public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Ring.Parity -- Algebra.Group.Even can't prove `IsSquare 0` by simp
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Tactic.ApplyFun

/-!
# Sums of squares

We introduce a predicate for sums of squares in a ring.

## Main declarations

- `IsSumSq : R → Prop`: for a type `R` with addition, multiplication and a zero,
  an inductive predicate defining the property of being a sum of squares in `R`.
  `0 : R` is a sum of squares and if `S` is a sum of squares, then, for all `a : R`,
  `a * a + s` is a sum of squares.
- `AddMonoid.sumSq R` and `Subsemiring.sumSq R`: respectively
  the submonoid or subsemiring of sums of squares in an additive monoid or semiring `R`
  with multiplication.
-/

@[expose] public section

variable {R : Type*}

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
The property of being a sum of squares is defined inductively by:
`0 : R` is a sum of squares and if `s : R` is a sum of squares,
then for all `a : R`, `a * a + s` is a sum of squares in `R`.
-/
@[mk_iff]
/-
**IsSumSq** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} → [Mul R] → [Add R] → [Zero R] → R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of being a sum of squares is defined inductively by:
`0 : R` is a sum of squares and if `s : R` is a sum of squares,
then for all `a : R`, `a * a + s` is a sum of squares in `R`.
-/
inductive IsSumSq [Mul R] [Add R] [Zero R] : R → Prop
  | zero                                    : IsSumSq 0
  | sq_add (a : R) {s : R} (hs : IsSumSq s) : IsSumSq (a * a + s)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Alternative induction scheme for `IsSumSq` which uses `IsSquare`. -/
/-
**IsSumSq.rec'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSumSq.rec' [Mul R] [Add R] [Zero R] {motive : (s : R) -> (h : IsSumSq s)
 -> Prop} (zero : motive 0 zero) (sq_add : forall {x s}, (hx : IsSquare x) -> (h
s : IsSumSq s) -> motive s hs -> motive (x + s) (by rcases hx with ⟨_, rfl⟩; exa
ct sq_add _ hs)) {s : R} (h : IsSumSq s) : motive s h
参数：s : R；h : IsSumSq s；zero : motive 0 zero；sq_add : forall {x s}, (hx : IsSquar
e x) -> (hs : IsSumSq s) -> motive s hs -> motive (x + s) (by rcases hx with ⟨_,
 rfl⟩; exact sq_add _ hs)；h : IsSumSq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSumSq.brecOn`：∀ {R : Type u_1} [inst : Mul R] [inst_1 : Add R] [inst_2
 : Zero R] {motive : (a : R) → IsSumSq a → Prop} {a : R}   (t : IsSumSq a), (∀ (
a : …
· 使用引理 `IsSquare.mul_self`：IsSquare.mul_self (r : α) : IsSquare (r * r)

--- 原说明 ---
Alternative induction scheme for `IsSumSq` which uses `IsSquare`.
-/
theorem IsSumSq.rec' [Mul R] [Add R] [Zero R]
    {motive : (s : R) → (h : IsSumSq s) → Prop}
    (zero : motive 0 zero)
    (sq_add : ∀ {x s}, (hx : IsSquare x) → (hs : IsSumSq s) → motive s hs →
      motive (x + s) (by rcases hx with ⟨_, rfl⟩; exact sq_add _ hs))
    {s : R} (h : IsSumSq s) : motive s h :=
  match h with
  | .zero        => zero
  | .sq_add _ hs => sq_add (.mul_self _) hs (rec' zero sq_add _)

/--
In an additive monoid with multiplication,
if `s₁` and `s₂` are sums of squares, then `s₁ + s₂` is a sum of squares.
-/
@[aesop unsafe 90% apply]
/-
**IsSumSq.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSumSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R} (h₁ : IsSumSq s₁) (h₂ : IsSu
mSq s₂) : IsSumSq (s₁ + s₂)
参数：h₁ : IsSumSq s₁；h₂ : IsSumSq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)

--- 原说明 ---
In an additive monoid with multiplication,
if `s₁` and `s₂` are sums of squares, then `s₁ + s₂` is a sum of squares.
-/
theorem IsSumSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R}
    (h₁ : IsSumSq s₁) (h₂ : IsSumSq s₂) : IsSumSq (s₁ + s₂) := by
  induction h₁ <;> simp_all [add_assoc, sq_add]

namespace AddSubmonoid
variable {T : Type*} [AddMonoid T] [Mul T] {s : T}

set_option linter.style.whitespace false in -- manual alignment is not recognised
variable (T) in
/--
In an additive monoid with multiplication `R`, `AddSubmonoid.sumSq R` is the submonoid of sums of
squares in `R`.
-/
@[simps]
/-
**AddSubmonoid.sumSq** 是 Mathlib 中的一个定义，位于命名空间 `AddSubmonoid`。
形式化陈述：sumSq : AddSubmonoid T where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsSumSq.add`：IsSumSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R} (h₁ : IsSumSq
 s₁) (h₂ : IsSumSq s₂) : IsSumSq (s₁ + s₂)

--- 原说明 ---
In an additive monoid with multiplication `R`, `AddSubmonoid.sumSq R` is the sub
monoid of sums of
squares in `R`.
-/
def sumSq : AddSubmonoid T where
  carrier   := {s : T | IsSumSq s}
  zero_mem' := .zero
  add_mem'  := .add

attribute [norm_cast] coe_sumSq
/-
**AddSubmonoid.mem_sumSq** 是 Mathlib 中的一个定理，位于命名空间 `AddSubmonoid`。
形式化陈述：∀ {T : Type u_2} [inst : AddMonoid T] [inst_1 : Mul T] {s : T}, s ∈ AddSub
monoid.sumSq T ↔ IsSumSq s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mem_sumSq : s ∈ sumSq T ↔ IsSumSq s := Iff.rfl

end AddSubmonoid

/-- In an additive unital magma with multiplication, `x * x` is a sum of squares for all `x`. -/
/-
**IsSumSq.mul_self** 是 Mathlib 中的一个定理，位于命名空间 `IsSumSq`。
形式化陈述：∀ {R : Type u_1} [inst : AddZeroClass R] [inst_1 : Mul R] (a : R), IsSumSq
 (a * a)
参数：a : R；a * a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
In an additive unital magma with multiplication, `x * x` is a sum of squares for
 all `x`.
-/
@[simp] theorem IsSumSq.mul_self [AddZeroClass R] [Mul R] (a : R) : IsSumSq (a * a) := by
  simpa using sq_add a zero

/--
In an additive unital magma with multiplication, squares are sums of squares
(see Mathlib.Algebra.Group.Even).
-/
@[aesop unsafe 80% apply]
/-
**IsSquare.isSumSq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSquare.isSumSq [AddZeroClass R] [Mul R] {x : R} (hx : IsSquare x) : IsSu
mSq x
参数：hx : IsSquare x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSquare.exists_mul_self`：∀ {α : Type u_2} [inst : Mul α] (a : α), IsSqu
are a → ∃ r, a = r * r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
In an additive unital magma with multiplication, squares are sums of squares
(see Mathlib.Algebra.Group.Even).
-/
theorem IsSquare.isSumSq [AddZeroClass R] [Mul R] {x : R} (hx : IsSquare x) : IsSumSq x := by aesop

attribute [simp, aesop safe] IsSumSq.zero

@[simp, aesop safe]
/-
**IsSumSq.one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSumSq.one [AddZeroClass R] [MulOneClass R] : IsSumSq (1 : R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSquare.isSumSq`：IsSquare.isSumSq [AddZeroClass R] [Mul R] {x : R} (hx 
: IsSquare x) : IsSumSq x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem IsSumSq.one [AddZeroClass R] [MulOneClass R] : IsSumSq (1 : R) := by aesop

/--
In an additive monoid with multiplication `R`, the submonoid generated by the squares is the set of
sums of squares in `R`.
-/
@[simp]
/-
**AddSubmonoid.closure_isSquare** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubmonoid.closure_isSquare [AddMonoid R] [Mul R] : closure {x : R | IsS
quare x} = sumSq R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.closure_eq_of_le`：∀ {M : Type u_1} [inst : AddZeroClass M] 
{s : Set M} {S : AddSubmonoid M},   s ⊆ ↑S → S ≤ AddSubmonoid.closure s → AddSub
monoid.closure s = …
· 使用定理 `IsSquare.isSumSq`：IsSquare.isSumSq [AddZeroClass R] [Mul R] {x : R} (hx 
: IsSquare x) : IsSumSq x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddSubmonoid.mem_closure_of_mem`：∀ {M : Type u_1} [inst : AddZeroClass M
] {s : Set M} {x : M}, x ∈ s → x ∈ AddSubmonoid.closure s

--- 原说明 ---
In an additive monoid with multiplication `R`, the submonoid generated by the sq
uares is the set of
sums of squares in `R`.
-/
theorem AddSubmonoid.closure_isSquare [AddMonoid R] [Mul R] :
    closure {x : R | IsSquare x} = sumSq R := by
  refine closure_eq_of_le (fun x hx ↦ IsSquare.isSumSq hx) (fun x hx ↦ ?_)
  induction hx <;> aesop

/--
In an additive commutative monoid with multiplication, a finite sum of sums of squares
is a sum of squares.
-/
@[aesop unsafe 90% apply]
/-
**IsSumSq.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSumSq.sum [AddCommMonoid R] [Mul R] {ι : Type*} {I : Finset ι} {s : ι ->
 R} (hs : forall i in I, IsSumSq <| s i) : IsSumSq (∑ i in I, s i)
参数：hs : forall i in I, IsSumSq <| s i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M

--- 原说明 ---
In an additive commutative monoid with multiplication, a finite sum of sums of s
quares
is a sum of squares.
-/
theorem IsSumSq.sum [AddCommMonoid R] [Mul R] {ι : Type*} {I : Finset ι} {s : ι → R}
    (hs : ∀ i ∈ I, IsSumSq <| s i) : IsSumSq (∑ i ∈ I, s i) := by
  simpa using sum_mem (S := AddSubmonoid.sumSq _) hs

/--
In an additive commutative monoid with multiplication,
`∑ i ∈ I, x i`, where each `x i` is a square, is a sum of squares.
-/
/-
**IsSumSq.sum_isSquare** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSumSq.sum_isSquare [AddCommMonoid R] [Mul R] {ι : Type*} (I : Finset ι) 
{x : ι -> R} (hx : forall i in I, IsSquare <| x i) : IsSumSq (∑ i in I, x i)
参数：I : Finset ι；hx : forall i in I, IsSquare <| x i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSumSq.sum`：IsSumSq.sum [AddCommMonoid R] [Mul R] {ι : Type*} {I : Fins
et ι} {s : ι -> R} (hs : forall i in I, IsSumSq <| s i) : IsSumSq (∑ i in I, s i
)
· 使用定理 `IsSquare.isSumSq`：IsSquare.isSumSq [AddZeroClass R] [Mul R] {x : R} (hx 
: IsSquare x) : IsSumSq x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
In an additive commutative monoid with multiplication,
`∑ i ∈ I, x i`, where each `x i` is a square, is a sum of squares.
-/
theorem IsSumSq.sum_isSquare [AddCommMonoid R] [Mul R] {ι : Type*} (I : Finset ι) {x : ι → R}
    (hx : ∀ i ∈ I, IsSquare <| x i) : IsSumSq (∑ i ∈ I, x i) := by aesop

/--
In an additive commutative monoid with multiplication,
`∑ i ∈ I, a i * a i` is a sum of squares.
-/
@[simp↓]
/-
**IsSumSq.sum_mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSumSq.sum_mul_self [AddCommMonoid R] [Mul R] {ι : Type*} (I : Finset ι) 
(a : ι -> R) : IsSumSq (∑ i in I, a i * a i)
参数：I : Finset ι；a : ι -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSumSq.sum`：IsSumSq.sum [AddCommMonoid R] [Mul R] {ι : Type*} {I : Fins
et ι} {s : ι -> R} (hs : forall i in I, IsSumSq <| s i) : IsSumSq (∑ i in I, s i
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
In an additive commutative monoid with multiplication,
`∑ i ∈ I, a i * a i` is a sum of squares.
-/
theorem IsSumSq.sum_mul_self [AddCommMonoid R] [Mul R] {ι : Type*} (I : Finset ι) (a : ι → R) :
    IsSumSq (∑ i ∈ I, a i * a i) := by aesop

@[simp↓]
/-
**IsSumSq.sum_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSumSq.sum_sq [CommSemiring R] {ι : Type*} (I : Finset ι) (a : ι -> R) : 
IsSumSq (∑ i in I, a i ^ 2)
参数：I : Finset ι；a : ι -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSumSq.sum`：IsSumSq.sum [AddCommMonoid R] [Mul R] {ι : Type*} {I : Fins
et ι} {s : ι -> R} (hs : forall i in I, IsSumSq <| s i) : IsSumSq (∑ i in I, s i
)
· 使用定理 `IsSquare.isSumSq`：IsSquare.isSumSq [AddZeroClass R] [Mul R] {x : R} (hx 
: IsSquare x) : IsSumSq x
· 使用引理 `IsSquare.sq`：IsSquare.sq (r : α) : IsSquare (r ^ 2)
-/
theorem IsSumSq.sum_sq [CommSemiring R] {ι : Type*} (I : Finset ι) (a : ι → R) :
    IsSumSq (∑ i ∈ I, a i ^ 2) := by aesop

namespace NonUnitalSubsemiring
variable {T : Type*} [NonUnitalCommSemiring T]

variable (T) in
/--
In a commutative (possibly non-unital) semiring `R`, `NonUnitalSubsemiring.sumSq R` is
the (possibly non-unital) subsemiring of sums of squares in `R`.
-/
/-
**NonUnitalSubsemiring.sumSq** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：sumSq : NonUnitalSubsemiring T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a commutative (possibly non-unital) semiring `R`, `NonUnitalSubsemiring.sumSq
 R` is
the (possibly non-unital) subsemiring of sums of squares in `R`.
-/
def sumSq : NonUnitalSubsemiring T := (Subsemigroup.square T).nonUnitalSubsemiringClosure
/-
**NonUnitalSubsemiring.sumSq_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
Subsemiring`。
形式化陈述：∀ {T : Type u_2} [inst : NonUnitalCommSemiring T], (NonUnitalSubsemiring.s
umSq T).toAddSubmonoid = AddSubmonoid.sumSq T
参数：NonUnitalSubsemiring.sumSq T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem sumSq_toAddSubmonoid : (sumSq T).toAddSubmonoid = .sumSq T := by
  simp [sumSq, ← AddSubmonoid.closure_isSquare,
    Subsemigroup.nonUnitalSubsemiringClosure_toAddSubmonoid]

@[simp]
/-
**NonUnitalSubsemiring.mem_sumSq** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring
`。
形式化陈述：mem_sumSq {s : T} : s in sumSq T ↔ IsSumSq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubsemiring.sumSq_toAddSubmonoid`：∀ {T : Type u_2} [inst : NonU
nitalCommSemiring T], (NonUnitalSubsemiring.sumSq T).toAddSubmonoid = AddSubmono
id.sumSq T
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sumSq {s : T} : s ∈ sumSq T ↔ IsSumSq s := by
  simp [← NonUnitalSubsemiring.mem_toAddSubmonoid]
/-
**NonUnitalSubsemiring.coe_sumSq** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring
`。
形式化陈述：∀ {T : Type u_2} [inst : NonUnitalCommSemiring T], ↑(NonUnitalSubsemiring.
sumSq T) = {s | IsSumSq s}
参数：NonUnitalSubsemiring.sumSq T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp, norm_cast] theorem coe_sumSq : sumSq T = {s : T | IsSumSq s} := by ext; simp
/-
**NonUnitalSubsemiring.closure_isSquare** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubs
emiring`。
形式化陈述：∀ {T : Type u_2} [inst : NonUnitalCommSemiring T],   NonUnitalSubsemiring.
closure {x | IsSquare x} = NonUnitalSubsemiring.sumSq T
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsemigroup.nonUnitalSubsemiringClosure_eq_closure`：nonUnitalSubsemirin
gClosure_eq_closure : M.nonUnitalSubsemiringClosure = NonUnitalSubsemiring.closu
re (M : Set R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem closure_isSquare : closure {x : T | IsSquare x} = sumSq T := by
  simp [sumSq, Subsemigroup.nonUnitalSubsemiringClosure_eq_closure]

end NonUnitalSubsemiring

@[simp, aesop safe]
/-
**IsSumSq.natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSumSq.natCast {R : Type*} [NonAssocSemiring R] (n : Nat) : IsSumSq (n : 
R)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsSumSq.add`：IsSumSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R} (h₁ : IsSumSq
 s₁) (h₂ : IsSumSq s₂) : IsSumSq (s₁ + s₂)
-/
theorem IsSumSq.natCast {R : Type*} [NonAssocSemiring R] (n : ℕ) : IsSumSq (n : R) := by
  induction n <;> aesop

@[simp]
/-
**Nat.isSumSq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.isSumSq (n : Nat) : IsSumSq n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSumSq.natCast`：IsSumSq.natCast {R : Type*} [NonAssocSemiring R] (n : N
at) : IsSumSq (n : R)
-/
theorem Nat.isSumSq (n : ℕ) : IsSumSq n := IsSumSq.natCast n

/--
In a commutative (possibly non-unital) semiring,
if `s₁` and `s₂` are sums of squares, then `s₁ * s₂` is a sum of squares.
-/
@[aesop unsafe 90% apply]
/-
**IsSumSq.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSumSq.mul [NonUnitalCommSemiring R] {s₁ s₂ : R} (h₁ : IsSumSq s₁) (h₂ : 
IsSumSq s₂) : IsSumSq (s₁ * s₂)
参数：h₁ : IsSumSq s₁；h₂ : IsSumSq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R

--- 原说明 ---
In a commutative (possibly non-unital) semiring,
if `s₁` and `s₂` are sums of squares, then `s₁ * s₂` is a sum of squares.
-/
theorem IsSumSq.mul [NonUnitalCommSemiring R] {s₁ s₂ : R}
    (h₁ : IsSumSq s₁) (h₂ : IsSumSq s₂) : IsSumSq (s₁ * s₂) := by
  simpa using mul_mem (by simpa : _ ∈ NonUnitalSubsemiring.sumSq R) (by simpa)
/-
**Submonoid.square_subsemiringClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem Submonoid.square_subsemiringClosure {T : Type*} [CommSemiring T] :
    (Submonoid.square T).subsemiringClosure = .closure {x : T | IsSquare x} := by
  simp [Submonoid.subsemiringClosure_eq_closure]

namespace Subsemiring
variable {T : Type*} [CommSemiring T]

variable (T) in
/--
In a commutative semiring `R`, `Subsemiring.sumSq R` is the subsemiring of sums of squares in `R`.
-/
/-
**Subsemiring.sumSq** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：sumSq : Subsemiring T where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a commutative semiring `R`, `Subsemiring.sumSq R` is the subsemiring of sums 
of squares in `R`.
-/
def sumSq : Subsemiring T where
  __ := NonUnitalSubsemiring.sumSq T
  one_mem' := by simp
/-
**Subsemiring.sumSq_toNonUnitalSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Subsemirin
g`。
形式化陈述：∀ {T : Type u_2} [inst : CommSemiring T], (Subsemiring.sumSq T).toNonUnita
lSubsemiring = NonUnitalSubsemiring.sumSq T
参数：Subsemiring.sumSq T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem sumSq_toNonUnitalSubsemiring :
    (sumSq T).toNonUnitalSubsemiring = .sumSq T := rfl

@[simp]
/-
**Subsemiring.mem_sumSq** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_sumSq {s : T} : s in sumSq T ↔ IsSumSq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sumSq {s : T} : s ∈ sumSq T ↔ IsSumSq s := by
  simp [← Subsemiring.mem_toNonUnitalSubsemiring]
/-
**Subsemiring.coe_sumSq** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {T : Type u_2} [inst : CommSemiring T], ↑(Subsemiring.sumSq T) = {s | Is
SumSq s}
参数：Subsemiring.sumSq T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp, norm_cast] theorem coe_sumSq : sumSq T = {s : T | IsSumSq s} := by ext; simp
/-
**Subsemiring.closure_isSquare** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {T : Type u_2} [inst : CommSemiring T], Subsemiring.closure {x | IsSquar
e x} = Subsemiring.sumSq T
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subsemiring.toNonUnitalSubsemiring_injective`：toNonUnitalSubsemiring_inj
ective : Function.Injective (toNonUnitalSubsemiring : Subsemiring R -> _)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.subsemiringClosure_toNonUnitalSubsemiring`：∀ {R : Type u} [ins
t : NonAssocSemiring R] (M : Submonoid R),   M.subsemiringClosure.toNonUnitalSub
semiring = NonUnitalSubsemiring.closure ↑…
· 使用定理 `NonUnitalSubsemiring.closure_isSquare`：∀ {T : Type u_2} [inst : NonUnita
lCommSemiring T],   NonUnitalSubsemiring.closure {x | IsSquare x} = NonUnitalSub
semiring.sumSq T
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem closure_isSquare : closure {x : T | IsSquare x} = sumSq T := by
  apply_fun toNonUnitalSubsemiring using toNonUnitalSubsemiring_injective
  simp [← Submonoid.square_subsemiringClosure]

end Subsemiring

/-- In a commutative semiring, a finite product of sums of squares is a sum of squares. -/
@[aesop unsafe 50% apply]
/-
**IsSumSq.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSumSq.prod [CommSemiring R] {ι : Type*} {I : Finset ι} {x : ι -> R} (hx 
: forall i in I, IsSumSq <| x i) : IsSumSq (∏ i in I, x i)
参数：hx : forall i in I, IsSumSq <| x i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prod_mem`：prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidCl
ass B M] {ι : Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S)…
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
In a commutative semiring, a finite product of sums of squares is a sum of squar
es.
-/
theorem IsSumSq.prod [CommSemiring R] {ι : Type*} {I : Finset ι} {x : ι → R}
    (hx : ∀ i ∈ I, IsSumSq <| x i) : IsSumSq (∏ i ∈ I, x i) := by
  simpa using prod_mem (S := Subsemiring.sumSq R) (by simpa)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
In a linearly ordered semiring with the property `a ≤ b → ∃ c, a + c = b` (e.g. `ℕ`),
sums of squares are non-negative.
-/
/-
**IsSumSq.nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSumSq.nonneg {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRi
ng R] [ExistsAddOfLE R] {s : R} (hs : IsSumSq s) : 0 <= s
参数：hs : IsSumSq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSumSq.rec'`：IsSumSq.rec' [Mul R] [Add R] [Zero R] {motive : (s : R) ->
 (h : IsSumSq s) -> Prop} (zero : motive 0 zero) (sq_add : forall {x s}, (hx : I
sS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsSquare.nonneg`：IsSquare.nonneg [Semiring R] [LinearOrder R] [ExistsAdd
OfLE R] [PosMulMono R] [AddLeftMono R] {x : R} (h : IsSquare x) : 0 <= x
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
In a linearly ordered semiring with the property `a ≤ b → ∃ c, a + c = b` (e.g. 
`ℕ`),
sums of squares are non-negative.
-/
theorem IsSumSq.nonneg {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] {s : R} (hs : IsSumSq s) : 0 ≤ s := by
  induction hs using IsSumSq.rec' with
  | zero          => simp
  | sq_add hx _ h => exact add_nonneg (IsSquare.nonneg hx) h
