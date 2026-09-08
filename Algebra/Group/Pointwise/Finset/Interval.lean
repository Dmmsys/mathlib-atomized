/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-! # Pointwise operations on intervals

This should be kept in sync with `Mathlib/Algebra/Order/Group/Pointwise/Interval.lean`.
-/

public section

variable {α : Type*}

namespace Finset

open scoped Pointwise

/-! ### Binary pointwise operations

Note that the subset operations below only cover the cases with the largest possible intervals on
the LHS: to conclude that `Ioo a b * Ioo c d ⊆ Ioo (a * c) (c * d)`, you can use monotonicity of `*`
and `Finset.Ico_mul_Ioc_subset`.

TODO: repeat these lemmas for the generality of `mul_le_mul` (which assumes nonnegativity), which
the unprimed names have been reserved for
-/

section ContravariantLE

variable [Mul α] [Preorder α] [DecidableEq α]
variable [MulLeftMono α] [MulRightMono α]

@[to_additive Icc_add_Icc_subset]
/-
**Finset.Icc_mul_Icc_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_mul_Icc_subset' [LocallyFiniteOrder α] (a b c d : α) : Icc a b * Icc c
 d subseteq Icc (a * c) (b * d)
参数：a b c d : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.Icc_mul_Icc_subset'`：Icc_mul_Icc_subset' (a b c d : α) : Icc a b * I
cc c d subseteq Icc (a * c) (b * d)
-/
theorem Icc_mul_Icc_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Icc a b * Icc c d ⊆ Icc (a * c) (b * d) :=
  Finset.coe_subset.mp <| by simpa using Set.Icc_mul_Icc_subset' _ _ _ _

@[to_additive Iic_add_Iic_subset]
/-
**Finset.Iic_mul_Iic_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iic_mul_Iic_subset' [LocallyFiniteOrderBot α] (a b : α) : Iic a * Iic b su
bseteq Iic (a * b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `Set.Iic_mul_Iic_subset'`：Iic_mul_Iic_subset' (a b : α) : Iic a * Iic b s
ubseteq Iic (a * b)
-/
theorem Iic_mul_Iic_subset' [LocallyFiniteOrderBot α] (a b : α) : Iic a * Iic b ⊆ Iic (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Iic_mul_Iic_subset' _ _

@[to_additive Ici_add_Ici_subset]
/-
**Finset.Ici_mul_Ici_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ici_mul_Ici_subset' [LocallyFiniteOrderTop α] (a b : α) : Ici a * Ici b su
bseteq Ici (a * b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `Set.Ici_mul_Ici_subset'`：Ici_mul_Ici_subset' (a b : α) : Ici a * Ici b s
ubseteq Ici (a * b)
-/
theorem Ici_mul_Ici_subset' [LocallyFiniteOrderTop α] (a b : α) : Ici a * Ici b ⊆ Ici (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Ici_mul_Ici_subset' _ _

end ContravariantLE

section ContravariantLT

variable [Mul α] [PartialOrder α] [DecidableEq α]
variable [MulLeftStrictMono α] [MulRightStrictMono α]

@[to_additive Icc_add_Ico_subset]
/-
**Finset.Icc_mul_Ico_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_mul_Ico_subset' [LocallyFiniteOrder α] (a b c d : α) : Icc a b * Ico c
 d subseteq Ico (a * c) (b * d)
参数：a b c d : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.Icc_mul_Ico_subset'`：Icc_mul_Ico_subset' (a b c d : α) : Icc a b * I
co c d subseteq Ico (a * c) (b * d)
-/
theorem Icc_mul_Ico_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Icc a b * Ico c d ⊆ Ico (a * c) (b * d) :=
  Finset.coe_subset.mp <| by simpa using Set.Icc_mul_Ico_subset' _ _ _ _

@[to_additive Ico_add_Icc_subset]
/-
**Finset.Ico_mul_Icc_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_mul_Icc_subset' [LocallyFiniteOrder α] (a b c d : α) : Ico a b * Icc c
 d subseteq Ico (a * c) (b * d)
参数：a b c d : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.Ico_mul_Icc_subset'`：Ico_mul_Icc_subset' (a b c d : α) : Ico a b * I
cc c d subseteq Ico (a * c) (b * d)
-/
theorem Ico_mul_Icc_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Ico a b * Icc c d ⊆ Ico (a * c) (b * d) :=
  Finset.coe_subset.mp <| by simpa using Set.Ico_mul_Icc_subset' _ _ _ _

@[to_additive Ioc_add_Ico_subset]
/-
**Finset.Ioc_mul_Ico_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_mul_Ico_subset' [LocallyFiniteOrder α] (a b c d : α) : Ioc a b * Ico c
 d subseteq Ioo (a * c) (b * d)
参数：a b c d : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Set.Ioc_mul_Ico_subset'`：Ioc_mul_Ico_subset' (a b c d : α) : Ioc a b * I
co c d subseteq Ioo (a * c) (b * d)
-/
theorem Ioc_mul_Ico_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Ioc a b * Ico c d ⊆ Ioo (a * c) (b * d) :=
  Finset.coe_subset.mp <| by simpa using Set.Ioc_mul_Ico_subset' _ _ _ _

@[to_additive Ico_add_Ioc_subset]
/-
**Finset.Ico_mul_Ioc_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_mul_Ioc_subset' [LocallyFiniteOrder α] (a b c d : α) : Ico a b * Ioc c
 d subseteq Ioo (a * c) (b * d)
参数：a b c d : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Set.Ico_mul_Ioc_subset'`：Ico_mul_Ioc_subset' (a b c d : α) : Ico a b * I
oc c d subseteq Ioo (a * c) (b * d)
-/
theorem Ico_mul_Ioc_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Ico a b * Ioc c d ⊆ Ioo (a * c) (b * d) :=
  Finset.coe_subset.mp <| by simpa using Set.Ico_mul_Ioc_subset' _ _ _ _

@[to_additive Iic_add_Iio_subset]
/-
**Finset.Iic_mul_Iio_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iic_mul_Iio_subset' [LocallyFiniteOrderBot α] (a b : α) : Iic a * Iio b su
bseteq Iio (a * b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Set.Iic_mul_Iio_subset'`：Iic_mul_Iio_subset' (a b : α) : Iic a * Iio b s
ubseteq Iio (a * b)
-/
theorem Iic_mul_Iio_subset' [LocallyFiniteOrderBot α] (a b : α) : Iic a * Iio b ⊆ Iio (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Iic_mul_Iio_subset' _ _

@[to_additive Iio_add_Iic_subset]
/-
**Finset.Iio_mul_Iic_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iio_mul_Iic_subset' [LocallyFiniteOrderBot α] (a b : α) : Iio a * Iic b su
bseteq Iio (a * b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `Set.Iio_mul_Iic_subset'`：Iio_mul_Iic_subset' (a b : α) : Iio a * Iic b s
ubseteq Iio (a * b)
-/
theorem Iio_mul_Iic_subset' [LocallyFiniteOrderBot α] (a b : α) : Iio a * Iic b ⊆ Iio (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Iio_mul_Iic_subset' _ _

@[to_additive Ioi_add_Ici_subset]
/-
**Finset.Ioi_mul_Ici_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioi_mul_Ici_subset' [LocallyFiniteOrderTop α] (a b : α) : Ioi a * Ici b su
bseteq Ioi (a * b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `Set.Ioi_mul_Ici_subset'`：Ioi_mul_Ici_subset' (a b : α) : Ioi a * Ici b s
ubseteq Ioi (a * b)
-/
theorem Ioi_mul_Ici_subset' [LocallyFiniteOrderTop α] (a b : α) : Ioi a * Ici b ⊆ Ioi (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Ioi_mul_Ici_subset' _ _

@[to_additive Ici_add_Ioi_subset]
/-
**Finset.Ici_mul_Ioi_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ici_mul_Ioi_subset' [LocallyFiniteOrderTop α] (a b : α) : Ici a * Ioi b su
bseteq Ioi (a * b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Set.Ici_mul_Ioi_subset'`：Ici_mul_Ioi_subset' (a b : α) : Ici a * Ioi b s
ubseteq Ioi (a * b)
-/
theorem Ici_mul_Ioi_subset' [LocallyFiniteOrderTop α] (a b : α) : Ici a * Ioi b ⊆ Ioi (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Ici_mul_Ioi_subset' _ _

end ContravariantLT

end Finset

