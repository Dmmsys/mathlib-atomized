/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Order.Preorder.Finsupp

/-!
# Flooring, ceiling division

This file defines division rounded up and down.

The setup is an ordered monoid `α` acting on an ordered monoid `β`. If `a : α`, `b : β`, we would
like to be able to "divide" `b` by `a`, namely find `c : β` such that `a • c = b`.
This is of course not always possible, but in some cases at least there is a least `c` such that
`b ≤ a • c` and a greatest `c` such that `a • c ≤ b`. We call the first one the "ceiling division
of `b` by `a`" and the second one the "flooring division of `b` by `a`"

If `α` and `β` are both `ℕ`, then one can check that our flooring and ceiling divisions really are
the floor and ceil of the exact division.
If `α` is `ℕ` and `β` is the functions `ι → ℕ`, then the flooring and ceiling divisions are taken
pointwise.

In order theory terms, those operations are respectively the right and left adjoints to the map
`b ↦ a • b`.

## Main declarations

* `FloorDiv`: Typeclass for the existence of a flooring division, denoted `b ⌊/⌋ a`.
* `CeilDiv`: Typeclass for the existence of a ceiling division, denoted `b ⌈/⌉ a`.

Note in both cases we only allow dividing by positive inputs. We enforce the following junk values:
* `b ⌊/⌋ a = b ⌈/⌉ a = 0` if `a ≤ 0`
* `0 ⌊/⌋ a = 0 ⌈/⌉ a = 0`

## Notation

* `b ⌊/⌋ a` for the flooring division of `b` by `a`
* `b ⌈/⌉ a` for the ceiling division of `b` by `a`

## TODO

* `norm_num` extension
* Prove `⌈a / b⌉ = a ⌈/⌉ b` when `a, b : ℕ`
-/

@[expose] public section

variable {ι α β : Type*}

section OrderedAddCommMonoid
variable (α β) [AddCommMonoid α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β]
  [SMulZeroClass α β]

/-- Typeclass for division rounded down. For each `a > 0`, this asserts the existence of a right
adjoint to the map `b ↦ a • b : β → β`. -/
/-
**FloorDiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) →   (β : Type u_3) →     [AddCommMonoid α] →       [Partial
Order α] → [inst : AddCommMonoid β] → [PartialOrder β] → [SMulZeroClass α β] → T
ype (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for division rounded down. For each `a > 0`, this asserts the existenc
e of a right
adjoint to the map `b ↦ a • b : β → β`.
-/
class FloorDiv where
  /-- Flooring division. If `a > 0`, then `b ⌊/⌋ a` is the greatest `c` such that `a • c ≤ b`. -/
  floorDiv : β → α → β
  /-- Do not use this. Use `gc_floorDiv_smul` or `gc_floorDiv_mul` instead. -/
  protected floorDiv_gc ⦃a⦄ : 0 < a → GaloisConnection (a • ·) (floorDiv · a)
  /-- Do not use this. Use `floorDiv_nonpos` instead. -/
  protected floorDiv_nonpos ⦃a⦄ : a ≤ 0 → ∀ b, floorDiv b a = 0
  /-- Do not use this. Use `zero_floorDiv` instead. -/
  protected zero_floorDiv (a) : floorDiv 0 a = 0

/-- Typeclass for division rounded up. For each `a > 0`, this asserts the existence of a left
adjoint to the map `b ↦ a • b : β → β`. -/
/-
**CeilDiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) →   (β : Type u_3) →     [AddCommMonoid α] →       [Partial
Order α] → [inst : AddCommMonoid β] → [PartialOrder β] → [SMulZeroClass α β] → T
ype (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for division rounded up. For each `a > 0`, this asserts the existence 
of a left
adjoint to the map `b ↦ a • b : β → β`.
-/
class CeilDiv where
  /-- Ceiling division. If `a > 0`, then `b ⌈/⌉ a` is the least `c` such that `b ≤ a • c`. -/
  ceilDiv : β → α → β
  /-- Do not use this. Use `gc_smul_ceilDiv` or `gc_mul_ceilDiv` instead. -/
  protected ceilDiv_gc ⦃a⦄ : 0 < a → GaloisConnection (ceilDiv · a) (a • ·)
  /-- Do not use this. Use `ceilDiv_nonpos` instead. -/
  protected ceilDiv_nonpos ⦃a⦄ : a ≤ 0 → ∀ b, ceilDiv b a = 0
  /-- Do not use this. Use `zero_ceilDiv` instead. -/
  protected zero_ceilDiv (a) : ceilDiv 0 a = 0

@[inherit_doc] infixl:70 " ⌊/⌋ " => FloorDiv.floorDiv
@[inherit_doc] infixl:70 " ⌈/⌉ " => CeilDiv.ceilDiv

variable {α β}

section FloorDiv
variable [FloorDiv α β] {a : α} {b c : β}

/-
**gc_floorDiv_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：gc_floorDiv_smul (ha : 0 < a) : GaloisConnection (a • · : β -> β) (· ⌊/⌋ a
)
参数：ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorDiv.floorDiv_gc`：∀ {α : Type u_2} {β : Type u_3} {inst : AddCommMon
oid α} {inst_1 : PartialOrder α} {inst_2 : AddCommMonoid β}   {inst_3 : PartialO
rder β} {i…
-/
lemma gc_floorDiv_smul (ha : 0 < a) : GaloisConnection (a • · : β → β) (· ⌊/⌋ a) :=
  FloorDiv.floorDiv_gc ha
/-
**le_floorDiv_iff_smul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] [inst_1 : Partial
Order α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β] [inst_4 : SMulZe
roClass α β] [inst_5 : FloorDiv α β] {a : α} {b c : β},   0 < a → (c ≤ b ⌊/⌋ a ↔
 a • c ≤ b)
参数：c ≤ b ⌊/⌋ a ↔ a • c ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `gc_floorDiv_smul`：gc_floorDiv_smul (ha : 0 < a) : GaloisConnection (a • 
· : β -> β) (· ⌊/⌋ a)
-/
@[simp] lemma le_floorDiv_iff_smul_le (ha : 0 < a) : c ≤ b ⌊/⌋ a ↔ a • c ≤ b :=
  (gc_floorDiv_smul ha _ _).symm
/-
**floorDiv_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] [inst_1 : Partial
Order α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β] [inst_4 : SMulZe
roClass α β] [inst_5 : FloorDiv α β] {a : α}, a ≤ 0 → ∀ (b : β), b ⌊/⌋ a = 0
参数：b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorDiv.floorDiv_nonpos`：∀ {α : Type u_2} {β : Type u_3} {inst : AddCom
mMonoid α} {inst_1 : PartialOrder α} {inst_2 : AddCommMonoid β}   {inst_3 : Part
ialOrder β} {i…
-/
@[simp] lemma floorDiv_of_nonpos (ha : a ≤ 0) (b : β) : b ⌊/⌋ a = 0 := FloorDiv.floorDiv_nonpos ha _
/-
**floorDiv_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：floorDiv_zero (b : β) : b ⌊/⌋ (0 : α) = 0
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `floorDiv_of_nonpos`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoi
d α] [inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrd
er β] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma floorDiv_zero (b : β) : b ⌊/⌋ (0 : α) = 0 := by simp
/-
**zero_floorDiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] [inst_1 : Partial
Order α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β] [inst_4 : SMulZe
roClass α β] [inst_5 : FloorDiv α β] (a : α), 0 ⌊/⌋ a = 0
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorDiv.zero_floorDiv`：∀ {α : Type u_2} {β : Type u_3} {inst : AddCommM
onoid α} {inst_1 : PartialOrder α} {inst_2 : AddCommMonoid β}   {inst_3 : Partia
lOrder β} {i…
-/
@[simp] lemma zero_floorDiv (a : α) : (0 : β) ⌊/⌋ a = 0 := FloorDiv.zero_floorDiv _
/-
**smul_floorDiv_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_floorDiv_le (ha : 0 < a) : a • (b ⌊/⌋ a) <= b
参数：ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_floorDiv_iff_smul_le`：∀ {α : Type u_2} {β : Type u_3} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : Parti
alOrder β] [i…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma smul_floorDiv_le (ha : 0 < a) : a • (b ⌊/⌋ a) ≤ b := (le_floorDiv_iff_smul_le ha).1 le_rfl

end FloorDiv

section CeilDiv
variable [CeilDiv α β] {a : α} {b c : β}

/-
**gc_smul_ceilDiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：gc_smul_ceilDiv (ha : 0 < a) : GaloisConnection (· ⌈/⌉ a) (a • · : β -> β)
参数：ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CeilDiv.ceilDiv_gc`：∀ {α : Type u_2} {β : Type u_3} {inst : AddCommMonoi
d α} {inst_1 : PartialOrder α} {inst_2 : AddCommMonoid β}   {inst_3 : PartialOrd
er β} {i…
-/
lemma gc_smul_ceilDiv (ha : 0 < a) : GaloisConnection (· ⌈/⌉ a) (a • · : β → β) :=
  CeilDiv.ceilDiv_gc ha

@[simp]
/-
**ceilDiv_le_iff_le_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ceilDiv_le_iff_le_smul (ha : 0 < a) : b ⌈/⌉ a <= c ↔ b <= a • c
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `gc_smul_ceilDiv`：gc_smul_ceilDiv (ha : 0 < a) : GaloisConnection (· ⌈/⌉ 
a) (a • · : β -> β)
-/
lemma ceilDiv_le_iff_le_smul (ha : 0 < a) : b ⌈/⌉ a ≤ c ↔ b ≤ a • c := gc_smul_ceilDiv ha _ _
/-
**ceilDiv_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] [inst_1 : Partial
Order α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β] [inst_4 : SMulZe
roClass α β] [inst_5 : CeilDiv α β] {a : α}, a ≤ 0 → ∀ (b : β), b ⌈/⌉ a = 0
参数：b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CeilDiv.ceilDiv_nonpos`：∀ {α : Type u_2} {β : Type u_3} {inst : AddCommM
onoid α} {inst_1 : PartialOrder α} {inst_2 : AddCommMonoid β}   {inst_3 : Partia
lOrder β} {i…
-/
@[simp] lemma ceilDiv_of_nonpos (ha : a ≤ 0) (b : β) : b ⌈/⌉ a = 0 := CeilDiv.ceilDiv_nonpos ha _
/-
**ceilDiv_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ceilDiv_zero (b : β) : b ⌈/⌉ (0 : α) = 0
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ceilDiv_of_nonpos`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid
 α] [inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrde
r β] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ceilDiv_zero (b : β) : b ⌈/⌉ (0 : α) = 0 := by simp
/-
**zero_ceilDiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] [inst_1 : Partial
Order α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β] [inst_4 : SMulZe
roClass α β] [inst_5 : CeilDiv α β] (a : α), 0 ⌈/⌉ a = 0
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CeilDiv.zero_ceilDiv`：∀ {α : Type u_2} {β : Type u_3} {inst : AddCommMon
oid α} {inst_1 : PartialOrder α} {inst_2 : AddCommMonoid β}   {inst_3 : PartialO
rder β} {i…
-/
@[simp] lemma zero_ceilDiv (a : α) : (0 : β) ⌈/⌉ a = 0 := CeilDiv.zero_ceilDiv _
/-
**le_smul_ceilDiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_smul_ceilDiv (ha : 0 < a) : b <= a • (b ⌈/⌉ a)
参数：ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ceilDiv_le_iff_le_smul`：ceilDiv_le_iff_le_smul (ha : 0 < a) : b ⌈/⌉ a <=
 c ↔ b <= a • c
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma le_smul_ceilDiv (ha : 0 < a) : b ≤ a • (b ⌈/⌉ a) := (ceilDiv_le_iff_le_smul ha).1 le_rfl

end CeilDiv
end OrderedAddCommMonoid

section LinearOrderedAddCommMonoid
variable [AddCommMonoid α] [LinearOrder α] [AddCommMonoid β] [PartialOrder β] [SMulZeroClass α β]
  [PosSMulReflectLE α β] [FloorDiv α β] [CeilDiv α β] {a : α} {b : β}

/-
**floorDiv_le_ceilDiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：floorDiv_le_ceilDiv : b ⌊/⌋ a <= b ⌈/⌉ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `floorDiv_of_nonpos`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoi
d α] [inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrd
er β] [i…
· 使用定理 `ceilDiv_of_nonpos`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid
 α] [inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrde
r β] [i…
· 使用引理 `le_of_smul_le_smul_left`：le_of_smul_le_smul_left [PosSMulReflectLE α β] 
(h : a • b₁ <= a • b₂) (ha : 0 < a) : b₁ <= b₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `smul_floorDiv_le`：smul_floorDiv_le (ha : 0 < a) : a • (b ⌊/⌋ a) <= b
· 使用引理 `le_smul_ceilDiv`：le_smul_ceilDiv (ha : 0 < a) : b <= a • (b ⌈/⌉ a)
-/
lemma floorDiv_le_ceilDiv : b ⌊/⌋ a ≤ b ⌈/⌉ a := by
  obtain ha | ha := le_or_gt a 0
  · simp [ha]
  · exact le_of_smul_le_smul_left ((smul_floorDiv_le ha).trans <| le_smul_ceilDiv ha) ha

end LinearOrderedAddCommMonoid

section OrderedSemiring
variable [Semiring α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β] [MulActionWithZero α β]

section FloorDiv
variable [FloorDiv α β] {a : α}

/-
**floorDiv_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [inst_1 : PartialOrder
 α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β] [inst_4 : MulActionWi
thZero α β] [inst_5 : FloorDiv α β] [IsOrderedRing α] [Nontrivial α]   (b : β), 
b ⌊/⌋ 1 = b
参数：b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zero_lt_one'`：zero_lt_one' : (0 : α) < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma floorDiv_one [IsOrderedRing α] [Nontrivial α] (b : β) : b ⌊/⌋ (1 : α) = b :=
  eq_of_forall_le_iff <| fun c ↦ by simp [zero_lt_one' α]
/-
**smul_floorDiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [inst_1 : PartialOrder
 α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β] [inst_4 : MulActionWi
thZero α β] [inst_5 : FloorDiv α β] {a : α} [PosSMulMono α β]   [PosSMulReflectL
E α β], 0 < a → ∀ (b : β), a • b ⌊/⌋ a = b
参数：b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma smul_floorDiv [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) (b : β) :
    a • b ⌊/⌋ a = b :=
  eq_of_forall_le_iff <| by simp [smul_le_smul_iff_of_pos_left, ha]

end FloorDiv

section CeilDiv
variable [CeilDiv α β] {a : α}

/-
**ceilDiv_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [inst_1 : PartialOrder
 α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β] [inst_4 : MulActionWi
thZero α β] [inst_5 : CeilDiv α β] [IsOrderedRing α] [Nontrivial α]   (b : β), b
 ⌈/⌉ 1 = b
参数：b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zero_lt_one'`：zero_lt_one' : (0 : α) < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma ceilDiv_one [IsOrderedRing α] [Nontrivial α] (b : β) : b ⌈/⌉ (1 : α) = b :=
  eq_of_forall_ge_iff <| fun c ↦ by simp [zero_lt_one' α]
/-
**smul_ceilDiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [inst_1 : PartialOrder
 α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β] [inst_4 : MulActionWi
thZero α β] [inst_5 : CeilDiv α β] {a : α} [PosSMulMono α β]   [PosSMulReflectLE
 α β], 0 < a → ∀ (b : β), a • b ⌈/⌉ a = b
参数：b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma smul_ceilDiv [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) (b : β) :
    a • b ⌈/⌉ a = b :=
  eq_of_forall_ge_iff <| by simp [smul_le_smul_iff_of_pos_left, ha]

end CeilDiv

section FloorDiv
variable [FloorDiv α α] {a b c : α}

/-
**gc_floorDiv_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：gc_floorDiv_mul (ha : 0 < a) : GaloisConnection (a * ·) (· ⌊/⌋ a)
参数：ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `gc_floorDiv_smul`：gc_floorDiv_smul (ha : 0 < a) : GaloisConnection (a • 
· : β -> β) (· ⌊/⌋ a)
-/
lemma gc_floorDiv_mul (ha : 0 < a) : GaloisConnection (a * ·) (· ⌊/⌋ a) := gc_floorDiv_smul ha
/-
**le_floorDiv_iff_mul_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_floorDiv_iff_mul_le (ha : 0 < a) : c <= b ⌊/⌋ a ↔ a • c <= b
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_floorDiv_iff_smul_le`：∀ {α : Type u_2} {β : Type u_3} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : Parti
alOrder β] [i…
-/
lemma le_floorDiv_iff_mul_le (ha : 0 < a) : c ≤ b ⌊/⌋ a ↔ a • c ≤ b := le_floorDiv_iff_smul_le ha

end FloorDiv

section CeilDiv
variable [CeilDiv α α] {a b c : α}

/-
**gc_mul_ceilDiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：gc_mul_ceilDiv (ha : 0 < a) : GaloisConnection (· ⌈/⌉ a) (a * ·)
参数：ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `gc_smul_ceilDiv`：gc_smul_ceilDiv (ha : 0 < a) : GaloisConnection (· ⌈/⌉ 
a) (a • · : β -> β)
-/
lemma gc_mul_ceilDiv (ha : 0 < a) : GaloisConnection (· ⌈/⌉ a) (a * ·) := gc_smul_ceilDiv ha
/-
**ceilDiv_le_iff_le_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ceilDiv_le_iff_le_mul (ha : 0 < a) : b ⌈/⌉ a <= c ↔ b <= a * c
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ceilDiv_le_iff_le_smul`：ceilDiv_le_iff_le_smul (ha : 0 < a) : b ⌈/⌉ a <=
 c ↔ b <= a • c
-/
lemma ceilDiv_le_iff_le_mul (ha : 0 < a) : b ⌈/⌉ a ≤ c ↔ b ≤ a * c := ceilDiv_le_iff_le_smul ha

end CeilDiv
end OrderedSemiring

namespace Nat

/-
**Nat.instFloorDiv** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instFloorDiv : FloorDiv Nat Nat where floorDiv
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
-/
instance instFloorDiv : FloorDiv ℕ ℕ where
  floorDiv := HDiv.hDiv
  floorDiv_gc a ha := by simpa [mul_comm] using Nat.galoisConnection_mul_div ha
  floorDiv_nonpos a ha b := by rw [ha.antisymm <| zero_le _, Nat.div_zero]
  zero_floorDiv := Nat.zero_div
/-
**Nat.instCeilDiv** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instCeilDiv : CeilDiv Nat Nat where ceilDiv a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCeilDiv : CeilDiv ℕ ℕ where
  ceilDiv a b := (a + b - 1) / b
  ceilDiv_gc a ha b c := by
    simp [div_le_iff_le_mul_add_pred ha, add_assoc, tsub_add_cancel_of_le <| succ_le_iff.2 ha]
  ceilDiv_nonpos a ha b := by simp_rw [ha.antisymm <| zero_le _, Nat.div_zero]
  zero_ceilDiv a := by cases a <;> simp [Nat.div_eq_zero_iff]
/-
**Nat.floorDiv_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (a b : ℕ), a ⌊/⌋ b = a / b
参数：a b : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma floorDiv_eq_div (a b : ℕ) : a ⌊/⌋ b = a / b := rfl
/-
**Nat.ceilDiv_eq_add_pred_div** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：ceilDiv_eq_add_pred_div (a b : Nat) : a ⌈/⌉ b = (a + b - 1) / b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ceilDiv_eq_add_pred_div (a b : ℕ) : a ⌈/⌉ b = (a + b - 1) / b := rfl

end Nat

namespace Pi
variable {π : ι → Type*} [AddCommMonoid α] [PartialOrder α]
  [∀ i, AddCommMonoid (π i)] [∀ i, PartialOrder (π i)]
  [∀ i, SMulZeroClass α (π i)]

section FloorDiv
variable [∀ i, FloorDiv α (π i)]

/-
**Pi.instFloorDiv** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instFloorDiv : FloorDiv α (forall i, π i) where floorDiv f a i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFloorDiv : FloorDiv α (∀ i, π i) where
  floorDiv f a i := f i ⌊/⌋ a
  floorDiv_gc _a ha _f _g := forall_congr' fun _i ↦ gc_floorDiv_smul ha _ _
  floorDiv_nonpos a ha f := by ext i; exact floorDiv_of_nonpos ha _
  zero_floorDiv a := by ext i; exact zero_floorDiv a

@[push ←]
/-
**Pi.floorDiv_def** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：floorDiv_def (f : forall i, π i) (a : α) : f ⌊/⌋ a = fun i => f i ⌊/⌋ a
参数：f : forall i, π i；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma floorDiv_def (f : ∀ i, π i) (a : α) : f ⌊/⌋ a = fun i ↦ f i ⌊/⌋ a := rfl
/-
**Pi.floorDiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {π : ι → Type u_4} [inst : AddCommMonoid α
] [inst_1 : PartialOrder α]   [inst_2 : (i : ι) → AddCommMonoid (π i)] [inst_3 :
 (i : ι) → PartialOrder (π i)]   [inst_4 : (i : ι) → SMulZeroClass α (π i)] [ins
t_5 : (i : ι) → FloorDiv α (π i)] (f : (i : ι) → π i) (a : α) (i : ι),   (f ⌊/⌋ 
a) i = f i ⌊/⌋ a
参数：i : ι；π i；i : ι；π i；i : ι；π i；i : ι；π i；f : (i : ι) → π i；a : α；i : ι；f ⌊/⌋ a
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma floorDiv_apply (f : ∀ i, π i) (a : α) (i : ι) : (f ⌊/⌋ a) i = f i ⌊/⌋ a := rfl

end FloorDiv

section CeilDiv
variable [∀ i, CeilDiv α (π i)]

/-
**Pi.instCeilDiv** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instCeilDiv : CeilDiv α (forall i, π i) where ceilDiv f a i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCeilDiv : CeilDiv α (∀ i, π i) where
  ceilDiv f a i := f i ⌈/⌉ a
  ceilDiv_gc _a ha _f _g := forall_congr' fun _i ↦ gc_smul_ceilDiv ha _ _
  ceilDiv_nonpos a ha f := by ext i; exact ceilDiv_of_nonpos ha _
  zero_ceilDiv a := by ext; exact zero_ceilDiv _
/-
**Pi.ceilDiv_def** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：ceilDiv_def (f : forall i, π i) (a : α) : f ⌈/⌉ a = fun i => f i ⌈/⌉ a
参数：f : forall i, π i；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ceilDiv_def (f : ∀ i, π i) (a : α) : f ⌈/⌉ a = fun i ↦ f i ⌈/⌉ a := rfl
/-
**Pi.ceilDiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {π : ι → Type u_4} [inst : AddCommMonoid α
] [inst_1 : PartialOrder α]   [inst_2 : (i : ι) → AddCommMonoid (π i)] [inst_3 :
 (i : ι) → PartialOrder (π i)]   [inst_4 : (i : ι) → SMulZeroClass α (π i)] [ins
t_5 : (i : ι) → CeilDiv α (π i)] (f : (i : ι) → π i) (a : α) (i : ι),   (f ⌈/⌉ a
) i = f i ⌈/⌉ a
参数：i : ι；π i；i : ι；π i；i : ι；π i；i : ι；π i；f : (i : ι) → π i；a : α；i : ι；f ⌈/⌉ a
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ceilDiv_apply (f : ∀ i, π i) (a : α) (i : ι) : (f ⌈/⌉ a) i = f i ⌈/⌉ a := rfl

end CeilDiv
end Pi

namespace Finsupp
variable [AddCommMonoid α] [PartialOrder α]
  [AddCommMonoid β] [PartialOrder β] [SMulZeroClass α β]

section FloorDiv
variable [FloorDiv α β] {f : ι →₀ β} {a : α}

/-
**Finsupp.instFloorDiv** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instFloorDiv : FloorDiv α (ι ->₀ β) where floorDiv f a
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_floorDiv`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] 
[inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β]
 [i…
-/
noncomputable instance instFloorDiv : FloorDiv α (ι →₀ β) where
  floorDiv f a := f.mapRange (· ⌊/⌋ a) <| zero_floorDiv _
  floorDiv_gc _a ha f _g := forall_congr' fun i ↦ by
    simpa only [coe_smul, Pi.smul_apply, mapRange_apply] using gc_floorDiv_smul ha (f i) _
  floorDiv_nonpos a ha f := by ext i; exact floorDiv_of_nonpos ha _
  zero_floorDiv a := by ext; exact zero_floorDiv _
/-
**Finsupp.floorDiv_def** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：floorDiv_def (f : ι ->₀ β) (a : α) : f ⌊/⌋ a = f.mapRange (· ⌊/⌋ a) (zero_
floorDiv _)
参数：f : ι ->₀ β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma floorDiv_def (f : ι →₀ β) (a : α) : f ⌊/⌋ a = f.mapRange (· ⌊/⌋ a) (zero_floorDiv _) := rfl
set_option warning.simp.otherHead false in
/-
**Finsupp.coe_floorDiv** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] [i
nst_1 : PartialOrder α]   [inst_2 : AddCommMonoid β] [inst_3 : PartialOrder β] [
inst_4 : SMulZeroClass α β] [inst_5 : FloorDiv α β] (f : ι →₀ β)   (a : α), ⇑(f 
⌊/⌋ a) = fun i => f i ⌊/⌋ a
参数：f : ι →₀ β；a : α；f ⌊/⌋ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] lemma coe_floorDiv (f : ι →₀ β) (a : α) : f ⌊/⌋ a = fun i ↦ f i ⌊/⌋ a := rfl
/-
**Finsupp.floorDiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] [i
nst_1 : PartialOrder α]   [inst_2 : AddCommMonoid β] [inst_3 : PartialOrder β] [
inst_4 : SMulZeroClass α β] [inst_5 : FloorDiv α β] (f : ι →₀ β)   (a : α) (i : 
ι), (f ⌊/⌋ a) i = f i ⌊/⌋ a
参数：f : ι →₀ β；a : α；i : ι；f ⌊/⌋ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma floorDiv_apply (f : ι →₀ β) (a : α) (i : ι) : (f ⌊/⌋ a) i = f i ⌊/⌋ a := rfl
/-
**Finsupp.support_floorDiv_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_floorDiv_subset : (f ⌊/⌋ a).support subseteq f.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_floorDiv`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] 
[inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β]
 [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma support_floorDiv_subset : (f ⌊/⌋ a).support ⊆ f.support := by
  simp +contextual [Finset.subset_iff, not_imp_not]

end FloorDiv

section CeilDiv
variable [CeilDiv α β] {f : ι →₀ β} {a : α}

/-
**Finsupp.instCeilDiv** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instCeilDiv : CeilDiv α (ι ->₀ β) where ceilDiv f a
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_ceilDiv`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] [
inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β] 
[i…
-/
noncomputable instance instCeilDiv : CeilDiv α (ι →₀ β) where
  ceilDiv f a := f.mapRange (· ⌈/⌉ a) <| zero_ceilDiv _
  ceilDiv_gc _a ha f _g := forall_congr' fun i ↦ by
    simpa only [coe_smul, Pi.smul_apply, mapRange_apply] using gc_smul_ceilDiv ha (f i) _
  ceilDiv_nonpos a ha f := by ext i; exact ceilDiv_of_nonpos ha _
  zero_ceilDiv a := by ext; exact zero_ceilDiv _
/-
**Finsupp.ceilDiv_def** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：ceilDiv_def (f : ι ->₀ β) (a : α) : f ⌈/⌉ a = f.mapRange (· ⌈/⌉ a) (zero_c
eilDiv _)
参数：f : ι ->₀ β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ceilDiv_def (f : ι →₀ β) (a : α) : f ⌈/⌉ a = f.mapRange (· ⌈/⌉ a) (zero_ceilDiv _) := rfl
set_option warning.simp.otherHead false in
/-
**Finsupp.coe_ceilDiv_def** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] [i
nst_1 : PartialOrder α]   [inst_2 : AddCommMonoid β] [inst_3 : PartialOrder β] [
inst_4 : SMulZeroClass α β] [inst_5 : CeilDiv α β] (f : ι →₀ β)   (a : α), ⇑(f ⌈
/⌉ a) = fun i => f i ⌈/⌉ a
参数：f : ι →₀ β；a : α；f ⌈/⌉ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] lemma coe_ceilDiv_def (f : ι →₀ β) (a : α) : f ⌈/⌉ a = fun i ↦ f i ⌈/⌉ a := rfl
/-
**Finsupp.ceilDiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] [i
nst_1 : PartialOrder α]   [inst_2 : AddCommMonoid β] [inst_3 : PartialOrder β] [
inst_4 : SMulZeroClass α β] [inst_5 : CeilDiv α β] (f : ι →₀ β)   (a : α) (i : ι
), (f ⌈/⌉ a) i = f i ⌈/⌉ a
参数：f : ι →₀ β；a : α；i : ι；f ⌈/⌉ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ceilDiv_apply (f : ι →₀ β) (a : α) (i : ι) : (f ⌈/⌉ a) i = f i ⌈/⌉ a := rfl
/-
**Finsupp.support_ceilDiv_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_ceilDiv_subset : (f ⌈/⌉ a).support subseteq f.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_ceilDiv`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] [
inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β] 
[i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma support_ceilDiv_subset : (f ⌈/⌉ a).support ⊆ f.support := by
  simp +contextual [Finset.subset_iff, not_imp_not]

end CeilDiv
end Finsupp

/-- This is the motivating example. -/
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the motivating example.
-/
noncomputable example : FloorDiv ℕ (ℕ →₀ ℕ) := inferInstance
