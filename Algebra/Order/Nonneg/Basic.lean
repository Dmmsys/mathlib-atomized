/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# The type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

Currently we only state instances and states some `simp`/`norm_cast` lemmas.

When `α` is `ℝ`, this will give us some properties about `ℝ≥0`.

## Implementation Notes

Instead of `{x : α // 0 ≤ x}` we could also use `Set.Ici (0 : α)`, which is definitionally equal.
However, using the explicit subtype has a big advantage: when writing an element explicitly
with a proof of nonnegativity as `⟨x, hx⟩`, the `hx` is expected to have type `0 ≤ x`. If we would
use `Ici 0`, then the type is expected to be `x ∈ Ici 0`. Although these types are definitionally
equal, this often confuses the elaborator. Similar problems arise when doing cases on an element.

The disadvantage is that we have to duplicate some instances about `Set.Ici` to this subtype.
-/

@[expose] public section
assert_not_exists GeneralizedHeytingAlgebra
assert_not_exists IsOrderedMonoid
-- TODO -- assert_not_exists PosMulMono
assert_not_exists mem_upperBounds

open Set

variable {α : Type*}

namespace Nonneg

/-
**Nonneg.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：inhabited [Preorder α] {a : α} : Inhabited { x : α // a <= x }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
instance inhabited [Preorder α] {a : α} : Inhabited { x : α // a ≤ x } :=
  ⟨⟨a, le_rfl⟩⟩
/-
**Nonneg.zero** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：zero [Zero α] [Preorder α] : Zero { x : α // 0 <= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance zero [Zero α] [Preorder α] : Zero { x : α // 0 ≤ x } :=
  ⟨⟨0, le_rfl⟩⟩

@[simp, norm_cast]
/-
**Nonneg.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {α : Type u_1} [inst : Zero α] [inst_1 : Preorder α], ↑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_zero [Zero α] [Preorder α] : ((0 : { x : α // 0 ≤ x }) : α) = 0 :=
  rfl

@[simp]
/-
**Nonneg.mk_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：mk_eq_zero [Zero α] [Preorder α] {x : α} (hx : 0 <= x) : (⟨x, hx⟩ : { x : 
α // 0 <= x }) = 0 ↔ x = 0
参数：hx : 0 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem mk_eq_zero [Zero α] [Preorder α] {x : α} (hx : 0 ≤ x) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) = 0 ↔ x = 0 :=
  Subtype.ext_iff
/-
**Nonneg.add** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：add [AddZeroClass α] [Preorder α] [AddLeftMono α] : Add { x : α // 0 <= x 
}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance add [AddZeroClass α] [Preorder α] [AddLeftMono α] : Add { x : α // 0 ≤ x } :=
  ⟨fun x y => ⟨x + y, add_nonneg x.2 y.2⟩⟩

@[simp]
/-
**Nonneg.mk_add_mk** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：mk_add_mk [AddZeroClass α] [Preorder α] [AddLeftMono α] {x y : α} (hx : 0 
<= x) (hy : 0 <= y) : (⟨x, hx⟩ : { x : α // 0 <= x }) + ⟨y, hy⟩ = ⟨x + y, add_no
nneg hx hy⟩
参数：hx : 0 <= x；hy : 0 <= y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_add_mk [AddZeroClass α] [Preorder α] [AddLeftMono α] {x y : α}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) + ⟨y, hy⟩ = ⟨x + y, add_nonneg hx hy⟩ :=
  rfl

@[simp, norm_cast]
/-
**Nonneg.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] [inst_2 : A
ddLeftMono α] (a b : { x // 0 ≤ x }),   ↑(a + b) = ↑a + ↑b
参数：a b : { x // 0 ≤ x }；a + b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_add [AddZeroClass α] [Preorder α] [AddLeftMono α]
    (a b : { x : α // 0 ≤ x }) : ((a + b : { x : α // 0 ≤ x }) : α) = a + b :=
  rfl
/-
**Nonneg.** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddZeroClass α] [Preorder α] [AddLeftMono α] [IsLeftCancelAdd α] :
    IsLeftCancelAdd { x : α // 0 ≤ x } where
  add_left_cancel _ _ _ eq := Subtype.ext (add_left_cancel congr($eq))
/-
**Nonneg.** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddZeroClass α] [Preorder α] [AddLeftMono α] [IsRightCancelAdd α] :
    IsRightCancelAdd { x : α // 0 ≤ x } where
  add_right_cancel _ _ _ eq := Subtype.ext (add_right_cancel congr($eq))
/-
**Nonneg.** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddZeroClass α] [Preorder α] [AddLeftMono α] [IsCancelAdd α] :
    IsCancelAdd { x : α // 0 ≤ x } where
/-
**Nonneg.nsmul** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：nsmul [AddMonoid α] [Preorder α] [AddLeftMono α] : SMul Nat { x : α // 0 <
= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nsmul [AddMonoid α] [Preorder α] [AddLeftMono α] : SMul ℕ { x : α // 0 ≤ x } :=
  ⟨fun n x => ⟨n • (x : α), nsmul_nonneg x.prop n⟩⟩

@[simp]
/-
**Nonneg.nsmul_mk** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：nsmul_mk [AddMonoid α] [Preorder α] [AddLeftMono α] (n : Nat) {x : α} (hx 
: 0 <= x) : (n • (⟨x, hx⟩ : { x : α // 0 <= x })) = ⟨n • x, nsmul_nonneg hx n⟩
参数：n : Nat；hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nsmul_mk [AddMonoid α] [Preorder α] [AddLeftMono α] (n : ℕ) {x : α}
    (hx : 0 ≤ x) : (n • (⟨x, hx⟩ : { x : α // 0 ≤ x })) = ⟨n • x, nsmul_nonneg hx n⟩ :=
  rfl

@[simp, norm_cast]
/-
**Nonneg.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {α : Type u_1} [inst : AddMonoid α] [inst_1 : Preorder α] [inst_2 : AddL
eftMono α] (n : ℕ) (a : { x // 0 ≤ x }),   ↑(n • a) = n • ↑a
参数：n : ℕ；a : { x // 0 ≤ x }；n • a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_nsmul [AddMonoid α] [Preorder α] [AddLeftMono α]
    (n : ℕ) (a : { x : α // 0 ≤ x }) : ((n • a : { x : α // 0 ≤ x }) : α) = n • (a : α) :=
  rfl

section One

variable [Zero α] [One α] [LE α] [ZeroLEOneClass α]

/-
**Nonneg.one** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：one : One { x : α // 0 <= x } where one
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
instance one : One { x : α // 0 ≤ x } where
  one := ⟨1, zero_le_one⟩

@[simp, norm_cast]
/-
**Nonneg.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : LE α] [inst_3 
: ZeroLEOneClass α], ↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_one : ((1 : { x : α // 0 ≤ x }) : α) = 1 :=
  rfl

@[simp]
/-
**Nonneg.mk_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：mk_eq_one {x : α} (hx : 0 <= x) : (⟨x, hx⟩ : { x : α // 0 <= x }) = 1 ↔ x 
= 1
参数：hx : 0 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem mk_eq_one {x : α} (hx : 0 ≤ x) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) = 1 ↔ x = 1 :=
  Subtype.ext_iff

end One

section Mul

variable [MulZeroClass α] [Preorder α] [PosMulMono α]

/-
**Nonneg.mul** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：mul : Mul { x : α // 0 <= x } where mul x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mul : Mul { x : α // 0 ≤ x } where
  mul x y := ⟨x * y, mul_nonneg x.2 y.2⟩

@[simp, norm_cast]
/-
**Nonneg.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {α : Type u_1} [inst : MulZeroClass α] [inst_1 : Preorder α] [inst_2 : P
osMulMono α] (a b : { x // 0 ≤ x }),   ↑(a * b) = ↑a * ↑b
参数：a b : { x // 0 ≤ x }；a * b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_mul (a b : { x : α // 0 ≤ x }) :
    ((a * b : { x : α // 0 ≤ x }) : α) = a * b :=
  rfl

@[simp]
/-
**Nonneg.mk_mul_mk** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：mk_mul_mk {x y : α} (hx : 0 <= x) (hy : 0 <= y) : (⟨x, hx⟩ : { x : α // 0 
<= x }) * ⟨y, hy⟩ = ⟨x * y, mul_nonneg hx hy⟩
参数：hx : 0 <= x；hy : 0 <= y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_mul_mk {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) * ⟨y, hy⟩ = ⟨x * y, mul_nonneg hx hy⟩ :=
  rfl

end Mul

section AddMonoid

variable [AddMonoid α] [Preorder α] [AddLeftMono α]

/-
**Nonneg.addMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：addMonoid : AddMonoid { x : α // 0 <= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoid : AddMonoid { x : α // 0 ≤ x } :=
  fast_instance% Subtype.coe_injective.addMonoid _ Nonneg.coe_zero (fun _ _ => rfl) fun _ _ => rfl

/-- Coercion `{x : α // 0 ≤ x} → α` as an `AddMonoidHom`. -/
@[simps]
/-
**Nonneg.coeAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Nonneg`。
形式化陈述：coeAddMonoidHom : { x : α // 0 <= x } ->+ α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion `{x : α // 0 ≤ x} → α` as an `AddMonoidHom`.
-/
def coeAddMonoidHom : { x : α // 0 ≤ x } →+ α :=
  { toFun := ((↑) : { x : α // 0 ≤ x } → α)
    map_zero' := Nonneg.coe_zero
    map_add' := Nonneg.coe_add }

@[norm_cast]
/-
**Nonneg.nsmul_coe** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：nsmul_coe (n : Nat) (r : { x : α // 0 <= x }) : ↑(n • r) = n • (r : α)
参数：n : Nat；r : { x : α // 0 <= x }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_nsmul`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoi
d M] [inst_1 : AddMonoid N] (f : M →+ N) (n : ℕ) (a : M),   f (n • a) = n • f a
-/
theorem nsmul_coe (n : ℕ) (r : { x : α // 0 ≤ x }) :
    ↑(n • r) = n • (r : α) :=
  Nonneg.coeAddMonoidHom.map_nsmul _ _

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid α] [Preorder α] [AddLeftMono α]

/-
**Nonneg.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：addCommMonoid : AddCommMonoid { x : α // 0 <= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid : AddCommMonoid { x : α // 0 ≤ x } :=
  fast_instance%
    Subtype.coe_injective.addCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) (fun _ _ => rfl)

end AddCommMonoid

section AddCancelCommMonoid
variable [AddCancelCommMonoid α] [Preorder α] [AddLeftMono α]

/-
**Nonneg.addCancelCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：addCancelCommMonoid : AddCancelCommMonoid {x : α // 0 <= x}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCancelCommMonoid : AddCancelCommMonoid {x : α // 0 ≤ x} :=
  fast_instance%
    Subtype.coe_injective.addCancelCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) (fun _ _ => rfl)

end AddCancelCommMonoid

section AddMonoidWithOne

variable [AddMonoidWithOne α] [PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α]

/-
**Nonneg.natCast** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：natCast : NatCast { x : α // 0 <= x }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
-/
instance natCast : NatCast { x : α // 0 ≤ x } :=
  ⟨fun n => ⟨n, Nat.cast_nonneg' n⟩⟩

@[simp, norm_cast]
/-
**Nonneg.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α] [in
st_2 : AddLeftMono α]   [inst_3 : ZeroLEOneClass α] (n : ℕ), ↑↑n = ↑n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_natCast (n : ℕ) : ((↑n : { x : α // 0 ≤ x }) : α) = n :=
  rfl

@[simp]
/-
**Nonneg.mk_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：mk_natCast (n : Nat) : (⟨n, n.cast_nonneg'⟩ : { x : α // 0 <= x }) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
-/
theorem mk_natCast (n : ℕ) : (⟨n, n.cast_nonneg'⟩ : { x : α // 0 ≤ x }) = n :=
  rfl
/-
**Nonneg.addMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：addMonoidWithOne : AddMonoidWithOne { x : α // 0 <= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoidWithOne : AddMonoidWithOne { x : α // 0 ≤ x } :=
  { Nonneg.one (α := α) with
    toNatCast := Nonneg.natCast
    natCast_zero := by ext; simp
    natCast_succ := fun _ => by ext; simp }

end AddMonoidWithOne

section Pow

variable [MonoidWithZero α] [Preorder α] [ZeroLEOneClass α] [PosMulMono α]

/-
**Nonneg.pow** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：pow : Pow { x : α // 0 <= x } Nat where pow x n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pow : Pow { x : α // 0 ≤ x } ℕ where
  pow x n := ⟨(x : α) ^ n, pow_nonneg x.2 n⟩

@[simp, norm_cast]
/-
**Nonneg.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Preorder α] [inst_2 :
 ZeroLEOneClass α] [inst_3 : PosMulMono α]   (a : { x // 0 ≤ x }) (n : ℕ), ↑(a ^
 n) = ↑a ^ n
参数：a : { x // 0 ≤ x }；n : ℕ；a ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_pow (a : { x : α // 0 ≤ x }) (n : ℕ) :
    (↑(a ^ n) : α) = (a : α) ^ n :=
  rfl

@[simp]
/-
**Nonneg.mk_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：mk_pow {x : α} (hx : 0 <= x) (n : Nat) : (⟨x, hx⟩ : { x : α // 0 <= x }) ^
 n = ⟨x ^ n, pow_nonneg hx n⟩
参数：hx : 0 <= x；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_pow {x : α} (hx : 0 ≤ x) (n : ℕ) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) ^ n = ⟨x ^ n, pow_nonneg hx n⟩ :=
  rfl

end Pow

section Semiring

variable [Semiring α] [PartialOrder α] [ZeroLEOneClass α]
  [AddLeftMono α] [PosMulMono α]

/-
**Nonneg.semiring** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：semiring : Semiring { x : α // 0 <= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semiring : Semiring { x : α // 0 ≤ x } :=
  fast_instance% Subtype.coe_injective.semiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl
/-
**Nonneg.monoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：monoidWithZero : MonoidWithZero { x : α // 0 <= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoidWithZero : MonoidWithZero { x : α // 0 ≤ x } := by infer_instance

/-- Coercion `{x : α // 0 ≤ x} → α` as a `RingHom`. -/
/-
**Nonneg.coeRingHom** 是 Mathlib 中的一个定义，位于命名空间 `Nonneg`。
形式化陈述：coeRingHom : { x : α // 0 <= x } ->+* α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion `{x : α // 0 ≤ x} → α` as a `RingHom`.
-/
def coeRingHom : { x : α // 0 ≤ x } →+* α :=
  { toFun := ((↑) : { x : α // 0 ≤ x } → α)
    map_one' := Nonneg.coe_one
    map_mul' := Nonneg.coe_mul
    map_zero' := Nonneg.coe_zero,
    map_add' := Nonneg.coe_add }

end Semiring

section CommSemiring

variable [CommSemiring α] [PartialOrder α] [ZeroLEOneClass α]
  [AddLeftMono α] [PosMulMono α]

/-
**Nonneg.commSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：commSemiring : CommSemiring { x : α // 0 <= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commSemiring : CommSemiring { x : α // 0 ≤ x } :=
  fast_instance% Subtype.coe_injective.commSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl
/-
**Nonneg.commMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：commMonoidWithZero : CommMonoidWithZero { x : α // 0 <= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commMonoidWithZero : CommMonoidWithZero { x : α // 0 ≤ x } := inferInstance

end CommSemiring

section SemilatticeSup
variable [Zero α] [SemilatticeSup α]

/-- The function `a ↦ max a 0` of type `α → {x : α // 0 ≤ x}`. -/
/-
**Nonneg.toNonneg** 是 Mathlib 中的一个定义，位于命名空间 `Nonneg`。
形式化陈述：toNonneg (a : α) : { x : α // 0 <= x }
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `a ↦ max a 0` of type `α → {x : α // 0 ≤ x}`.
-/
def toNonneg (a : α) : { x : α // 0 ≤ x } :=
  ⟨max a 0, le_sup_right⟩

@[simp]
/-
**Nonneg.coe_toNonneg** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：coe_toNonneg {a : α} : (toNonneg a : α) = max a 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toNonneg {a : α} : (toNonneg a : α) = max a 0 :=
  rfl

@[simp]
/-
**Nonneg.toNonneg_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：toNonneg_of_nonneg {a : α} (h : 0 <= a) : toNonneg a = ⟨a, h⟩
参数：h : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toNonneg_of_nonneg {a : α} (h : 0 ≤ a) : toNonneg a = ⟨a, h⟩ := by simp [toNonneg, h]

@[simp]
/-
**Nonneg.toNonneg_coe** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：toNonneg_coe {a : { x : α // 0 <= x }} : toNonneg (a : α) = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonneg.toNonneg_of_nonneg`：toNonneg_of_nonneg {a : α} (h : 0 <= a) : toN
onneg a = ⟨a, h⟩
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem toNonneg_coe {a : { x : α // 0 ≤ x }} : toNonneg (a : α) = a :=
  toNonneg_of_nonneg a.2

@[simp]
/-
**Nonneg.toNonneg_le** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：toNonneg_le {a : α} {b : { x : α // 0 <= x }} : toNonneg a <= b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toNonneg_le {a : α} {b : { x : α // 0 ≤ x }} : toNonneg a ≤ b ↔ a ≤ b := by
  obtain ⟨b, hb⟩ := b
  simp [toNonneg, hb]
/-
**Nonneg.sub** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：sub [Sub α] : Sub { x : α // 0 <= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sub [Sub α] : Sub { x : α // 0 ≤ x } :=
  ⟨fun x y => toNonneg (x - y)⟩

@[simp]
/-
**Nonneg.mk_sub_mk** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：mk_sub_mk [Sub α] {x y : α} (hx : 0 <= x) (hy : 0 <= y) : (⟨x, hx⟩ : { x :
 α // 0 <= x }) - ⟨y, hy⟩ = toNonneg (x - y)
参数：hx : 0 <= x；hy : 0 <= y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_sub_mk [Sub α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) - ⟨y, hy⟩ = toNonneg (x - y) :=
  rfl

end SemilatticeSup

section LinearOrder
variable [Zero α] [LinearOrder α]

@[simp]
/-
**Nonneg.toNonneg_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：toNonneg_lt {a : { x : α // 0 <= x }} {b : α} : a < toNonneg b ↔ ↑a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toNonneg_lt {a : { x : α // 0 ≤ x }} {b : α} : a < toNonneg b ↔ ↑a < b := by
  obtain ⟨a, ha⟩ := a
  simp [toNonneg, ha.not_gt]

end LinearOrder

end Nonneg

