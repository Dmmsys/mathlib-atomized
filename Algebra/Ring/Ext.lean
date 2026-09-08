/-
Copyright (c) 2024 Raghuram Sundararajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raghuram Sundararajan
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Group.Ext

/-!
# Extensionality lemmas for rings and similar structures

In this file we prove extensionality lemmas for the ring-like structures defined in
`Mathlib/Algebra/Ring/Defs.lean`, ranging from `NonUnitalNonAssocSemiring` to `CommRing`. These
extensionality lemmas take the form of asserting that two algebraic structures on a type are equal
whenever the addition and multiplication defined by them are both the same.

## Implementation details

We follow `Mathlib/Algebra/Group/Ext.lean` in using the term `(letI := i; HMul.hMul : R → R → R)` to
refer to the multiplication specified by a typeclass instance `i` on a type `R` (and similarly for
addition). We abbreviate these using some local notations.

Since `Mathlib/Algebra/Group/Ext.lean` proved several injectivity lemmas, we do so as well — even if
sometimes we don't need them to prove extensionality.

## Tags
semiring, ring, extensionality
-/

public section

local macro:max "local_hAdd[" type:term ", " inst:term "]" : term =>
  `(term| (letI := $inst; HAdd.hAdd : $type → $type → $type))
local macro:max "local_hMul[" type:term ", " inst:term "]" : term =>
  `(term| (letI := $inst; HMul.hMul : $type → $type → $type))

universe u

variable {R : Type u}

/-! ### Distrib -/
namespace Distrib

/-
**Distrib.ext** 是 Mathlib 中的一个定理，位于命名空间 `Distrib`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : Distrib R⦄, HAdd.hAdd = HAdd.hAdd → HMul.hMu
l = HMul.hMul → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[ext] theorem ext ⦃inst₁ inst₂ : Distrib R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Split into `add` and `mul` functions and properties.
  rcases inst₁ with @⟨⟨⟩, ⟨⟩⟩
  rcases inst₂ with @⟨⟨⟩, ⟨⟩⟩
  -- Prove equality of parts using function extensionality.
  congr

end Distrib

/-! ### NonUnitalNonAssocSemiring -/
namespace NonUnitalNonAssocSemiring

/-
**NonUnitalNonAssocSemiring.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalNonAssocSemi
ring`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalNonAssocSemiring R⦄,   HAdd.hAdd = 
HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommMonoid.ext`：∀ {M : Type u_1} ⦃m₁ m₂ : AddCommMonoid M⦄, HAdd.hAdd
 = HAdd.hAdd → m₁ = m₂
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Split into `AddMonoid` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, ⟨⟩⟩
  rcases inst₂ with @⟨_, ⟨⟩⟩
  -- Prove equality of parts using already-proved extensionality lemmas.
  congr; ext : 1; assumption
/-
**NonUnitalNonAssocSemiring.toDistrib_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUn
italNonAssocSemiring`。
形式化陈述：toDistrib_injective : Function.Injective (@toDistrib R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalNonAssocSemiring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalNo
nAssocSemiring R⦄,   HAdd.hAdd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = ins
t₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem toDistrib_injective : Function.Injective (@toDistrib R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end NonUnitalNonAssocSemiring

/-! ### NonUnitalSemiring -/
namespace NonUnitalSemiring

/-
**NonUnitalSemiring.toNonUnitalNonAssocSemiring_injective** 是 Mathlib 中的一个定理，位于命
名空间 `NonUnitalSemiring`。
形式化陈述：toNonUnitalNonAssocSemiring_injective : Function.Injective (@toNonUnitalNo
nAssocSemiring R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr
/-
**NonUnitalSemiring.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSemiring`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalSemiring R⦄, HAdd.hAdd = HAdd.hAdd 
→ HMul.hMul = HMul.hMul → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSemiring.toNonUnitalNonAssocSemiring_injective`：toNonUnitalNonA
ssocSemiring_injective : Function.Injective (@toNonUnitalNonAssocSemiring R)
· 使用定理 `NonUnitalNonAssocSemiring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalNo
nAssocSemiring R⦄,   HAdd.hAdd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = ins
t₂
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
  toNonUnitalNonAssocSemiring_injective <|
    NonUnitalNonAssocSemiring.ext h_add h_mul

end NonUnitalSemiring

/-! ### NonAssocSemiring and its ancestors

This section also includes results for `AddMonoidWithOne`, `AddCommMonoidWithOne`, etc.
as these are considered implementation detail of the ring classes.
TODO consider relocating these lemmas.
-/
/-
**AddMonoidWithOne.ext** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidWithOne`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : AddMonoidWithOne R⦄, HAdd.hAdd = HAdd.hAdd →
 One.one = One.one → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoid.ext`：∀ {M : Type u} ⦃m₁ m₂ : AddMonoid M⦄, HAdd.hAdd = HAdd.hA
dd → m₁ = m₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddMonoidWithOne.natCast_zero`：∀ {R : Type u_2} [self : AddMonoidWithOne
 R], ↑0 = 0
· 使用定理 `AddMonoidWithOne.natCast_succ`：∀ {R : Type u_2} [self : AddMonoidWithOne
 R] (n : ℕ), ↑(n + 1) = ↑n + 1
· 使用定理 `congrArg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ
) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'

--- 原说明 ---
### NonAssocSemiring and its ancestors

This section also includes results for `AddMonoidWithOne`, `AddCommMonoidWithOne
`, etc.
as these are considered implementation detail of the ring classes.
TODO consider relocating these lemmas.
-/
@[ext] theorem AddMonoidWithOne.ext ⦃inst₁ inst₂ : AddMonoidWithOne R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_one : (letI := inst₁; One.one : R) = (letI := inst₂; One.one : R)) :
    inst₁ = inst₂ := by
  have h_monoid : inst₁.toAddMonoid = inst₂.toAddMonoid := by ext : 1; exact h_add
  have h_zero' : inst₁.toZero = inst₂.toZero := congrArg (·.toZero) h_monoid
  have h_one' : inst₁.toOne = inst₂.toOne :=
    congrArg One.mk h_one
  have h_natCast : inst₁.toNatCast.natCast = inst₂.toNatCast.natCast := by
    funext n; induction n with
    | zero => rewrite [inst₁.natCast_zero, inst₂.natCast_zero]
              exact congrArg (@Zero.zero R) h_zero'
    | succ n h => rw [inst₁.natCast_succ, inst₂.natCast_succ, h_add]
                  exact congrArg₂ _ h h_one
  rcases inst₁ with @⟨⟨⟩⟩; rcases inst₂ with @⟨⟨⟩⟩
  congr
/-
**AddCommMonoidWithOne.toAddMonoidWithOne_injective** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：AddCommMonoidWithOne.toAddMonoidWithOne_injective : Function.Injective (@A
ddCommMonoidWithOne.toAddMonoidWithOne R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddCommMonoidWithOne.toAddMonoidWithOne_injective :
    Function.Injective (@AddCommMonoidWithOne.toAddMonoidWithOne R) := by
  rintro ⟨⟩ ⟨⟩ _; congr
/-
**AddCommMonoidWithOne.ext** 是 Mathlib 中的一个定理，位于命名空间 `AddCommMonoidWithOne`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : AddCommMonoidWithOne R⦄, HAdd.hAdd = HAdd.hA
dd → One.one = One.one → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommMonoidWithOne.toAddMonoidWithOne_injective`：AddCommMonoidWithOne.
toAddMonoidWithOne_injective : Function.Injective (@AddCommMonoidWithOne.toAddMo
noidWithOne R)
· 使用定理 `AddMonoidWithOne.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : AddMonoidWithOne R⦄,
 HAdd.hAdd = HAdd.hAdd → One.one = One.one → inst₁ = inst₂
-/
@[ext] theorem AddCommMonoidWithOne.ext ⦃inst₁ inst₂ : AddCommMonoidWithOne R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_one : (letI := inst₁; One.one : R) = (letI := inst₂; One.one : R)) :
    inst₁ = inst₂ :=
  AddCommMonoidWithOne.toAddMonoidWithOne_injective <|
    AddMonoidWithOne.ext h_add h_one

namespace NonAssocSemiring

/-! The best place to prove that the `NatCast` is determined by the other operations is probably in
an extensionality lemma for `AddMonoidWithOne`, in which case we may as well do the typeclasses
defined in `Mathlib/Algebra/GroupWithZero/Defs.lean` as well. -/
/-
**NonAssocSemiring.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonAssocSemiring`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : NonAssocSemiring R⦄, HAdd.hAdd = HAdd.hAdd →
 HMul.hMul = HMul.hMul → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalNonAssocSemiring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalNo
nAssocSemiring R⦄,   HAdd.hAdd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = ins
t₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `MulOneClass.ext`：MulOneClass.ext {M : Type u} : forall ⦃m₁ m₂ : MulOneCl
ass M⦄, m₁.mul = m₂.mul -> m₁ = m₂
· 使用定理 `AddCommMonoidWithOne.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : AddCommMonoidWit
hOne R⦄, HAdd.hAdd = HAdd.hAdd → One.one = One.one → inst₁ = inst₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The best place to prove that the `NatCast` is determined by the other operations
 is probably in
an extensionality lemma for `AddMonoidWithOne`, in which case we may as well do 
the typeclasses
defined in `Mathlib/Algebra/GroupWithZero/Defs.lean` as well.
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonAssocSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  have h : inst₁.toNonUnitalNonAssocSemiring = inst₂.toNonUnitalNonAssocSemiring := by
    ext : 1 <;> assumption
  have h_zero : (inst₁.toMulZeroClass).toZero.zero = (inst₂.toMulZeroClass).toZero.zero :=
    congrArg (fun inst => (inst.toMulZeroClass).toZero.zero) h
  have h_one' : (inst₁.toMulZeroOneClass).toMulOneClass.toOne
                = (inst₂.toMulZeroOneClass).toMulOneClass.toOne := by
    congr 2; ext : 1; exact h_mul
  have h_one : (inst₁.toMulZeroOneClass).toMulOneClass.toOne.one
               = (inst₂.toMulZeroOneClass).toMulOneClass.toOne.one :=
    congrArg (@One.one R) h_one'
  have : inst₁.toAddCommMonoidWithOne = inst₂.toAddCommMonoidWithOne := by
    ext : 1 <;> assumption
  have : inst₁.toNatCast = inst₂.toNatCast :=
    congrArg (·.toNatCast) this
  -- Split into `NonUnitalNonAssocSemiring`, `One` and `natCast` instances.
  cases inst₁; cases inst₂
  congr
/-
**NonAssocSemiring.toNonUnitalNonAssocSemiring_injective** 是 Mathlib 中的一个定理，位于命名
空间 `NonAssocSemiring`。
形式化陈述：toNonUnitalNonAssocSemiring_injective : Function.Injective (@toNonUnitalNo
nAssocSemiring R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonAssocSemiring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonAssocSemiring R⦄,
 HAdd.hAdd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  intro _ _ _
  ext <;> congr

end NonAssocSemiring

/-! ### NonUnitalNonAssocRing -/
namespace NonUnitalNonAssocRing

/-
**NonUnitalNonAssocRing.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalNonAssocRing`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalNonAssocRing R⦄, HAdd.hAdd = HAdd.h
Add → HMul.hMul = HMul.hMul → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.ext`：∀ {G : Type u_1} ⦃g₁ g₂ : AddCommGroup G⦄, HAdd.hAdd =
 HAdd.hAdd → g₁ = g₂
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Split into `AddCommGroup` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, ⟨⟩⟩; rcases inst₂ with @⟨_, ⟨⟩⟩
  congr; (ext : 1; assumption)
/-
**NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring_injective** 是 Mathlib 中的一个定理
，位于命名空间 `NonUnitalNonAssocRing`。
形式化陈述：toNonUnitalNonAssocSemiring_injective : Function.Injective (@toNonUnitalNo
nAssocSemiring R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalNonAssocRing.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalNonAss
ocRing R⦄, HAdd.hAdd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  intro _ _ h
  -- Use above extensionality lemma to prove injectivity by showing that `h_add` and `h_mul` hold.
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end NonUnitalNonAssocRing

/-! ### NonUnitalRing -/
namespace NonUnitalRing

/-
**NonUnitalRing.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRing`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalRing R⦄, HAdd.hAdd = HAdd.hAdd → HM
ul.hMul = HMul.hMul → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalNonAssocRing.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalNonAss
ocRing R⦄, HAdd.hAdd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  have : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext : 1 <;> assumption
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr
/-
**NonUnitalRing.toNonUnitalSemiring_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alRing`。
形式化陈述：toNonUnitalSemiring_injective : Function.Injective (@toNonUnitalSemiring R
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRing.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalRing R⦄, HAdd.
hAdd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h
/-
**NonUnitalRing.toNonUnitalNonAssocring_injective** 是 Mathlib 中的一个定理，位于命名空间 `Non
UnitalRing`。
形式化陈述：toNonUnitalNonAssocring_injective : Function.Injective (@toNonUnitalNonAss
ocRing R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRing.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalRing R⦄, HAdd.
hAdd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
theorem toNonUnitalNonAssocring_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

end NonUnitalRing

/-! ### NonAssocRing and its ancestors

This section also includes results for `AddGroupWithOne`, `AddCommGroupWithOne`, etc.
as these are considered implementation detail of the ring classes.
TODO consider relocating these lemmas. -/
/-
**AddGroupWithOne.ext** 是 Mathlib 中的一个定理，位于命名空间 `AddGroupWithOne`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : AddGroupWithOne R⦄, HAdd.hAdd = HAdd.hAdd → 
One.one = One.one → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidWithOne.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : AddMonoidWithOne R⦄,
 HAdd.hAdd = HAdd.hAdd → One.one = One.one → inst₁ = inst₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddGroup.ext`：∀ {G : Type u_1} ⦃g₁ g₂ : AddGroup G⦄, HAdd.hAdd = HAdd.hA
dd → g₁ = g₂
· 使用定理 `AddGroupWithOne.sub_eq_add_neg`：∀ {R : Type u} [self : AddGroupWithOne R
] (a b : R), a - b = a + -b
· 使用定理 `AddGroupWithOne.zsmul_zero'`：∀ {R : Type u} [self : AddGroupWithOne R] (
a : R), 0 • a = 0
· 使用定理 `AddGroupWithOne.zsmul_succ'`：∀ {R : Type u} [self : AddGroupWithOne R] (
n : ℕ) (a : R), ↑n.succ • a = ↑n • a + a
· 使用定理 `AddGroupWithOne.zsmul_neg'`：∀ {R : Type u} [self : AddGroupWithOne R] (n
 : ℕ) (a : R), Int.negSucc n • a = -(↑n.succ • a)
· 使用定理 `AddGroupWithOne.neg_add_cancel`：∀ {R : Type u} [self : AddGroupWithOne R
] (a : R), -a + a = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `AddGroupWithOne.intCast_ofNat`：∀ {R : Type u} [self : AddGroupWithOne R]
 (n : ℕ), IntCast.intCast ↑n = ↑n
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddGroupWithOne.intCast_negSucc`：∀ {R : Type u} [self : AddGroupWithOne 
R] (n : ℕ), IntCast.intCast (Int.negSucc n) = -↑(n + 1)

--- 原说明 ---
### NonAssocRing and its ancestors

This section also includes results for `AddGroupWithOne`, `AddCommGroupWithOne`,
 etc.
as these are considered implementation detail of the ring classes.
TODO consider relocating these lemmas.
-/
@[ext] theorem AddGroupWithOne.ext ⦃inst₁ inst₂ : AddGroupWithOne R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_one : (letI := inst₁; One.one : R) = (letI := inst₂; One.one)) :
    inst₁ = inst₂ := by
  have : inst₁.toAddMonoidWithOne = inst₂.toAddMonoidWithOne :=
    AddMonoidWithOne.ext h_add h_one
  have : inst₁.toNatCast = inst₂.toNatCast := congrArg (·.toNatCast) this
  have h_group : inst₁.toAddGroup = inst₂.toAddGroup := by ext : 1; exact h_add
  -- Extract equality of necessary substructures from h_group
  injection h_group with h_group; injection h_group
  have : inst₁.toIntCast.intCast = inst₂.toIntCast.intCast := by
    funext n; cases n with
    | ofNat n => rewrite [Int.ofNat_eq_natCast, inst₁.intCast_ofNat, inst₂.intCast_ofNat]; congr
    | negSucc n => rewrite [inst₁.intCast_negSucc, inst₂.intCast_negSucc]; congr
  rcases inst₁ with @⟨⟨⟩⟩; rcases inst₂ with @⟨⟨⟩⟩
  congr
/-
**AddCommGroupWithOne.ext** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroupWithOne`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : AddCommGroupWithOne R⦄, HAdd.hAdd = HAdd.hAd
d → One.one = One.one → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.ext`：∀ {G : Type u_1} ⦃g₁ g₂ : AddCommGroup G⦄, HAdd.hAdd =
 HAdd.hAdd → g₁ = g₂
· 使用定理 `AddGroupWithOne.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : AddGroupWithOne R⦄, H
Add.hAdd = HAdd.hAdd → One.one = One.one → inst₁ = inst₂
· 使用定理 `AddCommGroupWithOne.natCast_zero`：∀ {R : Type u} [self : AddCommGroupWit
hOne R], ↑0 = 0
· 使用定理 `AddCommGroupWithOne.natCast_succ`：∀ {R : Type u} [self : AddCommGroupWit
hOne R] (n : ℕ), ↑(n + 1) = ↑n + 1
· 使用定理 `SubNegMonoid.sub_eq_add_neg`：∀ {G : Type u} [self : SubNegMonoid G] (a b
 : G), a - b = a + -b
· 使用定理 `SubNegMonoid.zsmul_zero'`：∀ {G : Type u} [self : SubNegMonoid G] (a : G)
, 0 • a = 0
· 使用定理 `SubNegMonoid.zsmul_succ'`：∀ {G : Type u} [self : SubNegMonoid G] (n : ℕ)
 (a : G), ↑n.succ • a = ↑n • a + a
· 使用定理 `SubNegMonoid.zsmul_neg'`：∀ {G : Type u} [self : SubNegMonoid G] (n : ℕ) 
(a : G), Int.negSucc n • a = -(↑n.succ • a)
· 使用定理 `AddGroup.neg_add_cancel`：∀ {A : Type u} [self : AddGroup A] (a : A), -a 
+ a = 0
· 使用定理 `AddCommGroupWithOne.intCast_ofNat`：∀ {R : Type u} [self : AddCommGroupWi
thOne R] (n : ℕ), IntCast.intCast ↑n = ↑n
· 使用定理 `AddCommGroupWithOne.intCast_negSucc`：∀ {R : Type u} [self : AddCommGroup
WithOne R] (n : ℕ), IntCast.intCast (Int.negSucc n) = -↑(n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[ext] theorem AddCommGroupWithOne.ext ⦃inst₁ inst₂ : AddCommGroupWithOne R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_one : (letI := inst₁; One.one : R) = (letI := inst₂; One.one)) :
    inst₁ = inst₂ := by
  have : inst₁.toAddCommGroup = inst₂.toAddCommGroup :=
    AddCommGroup.ext h_add
  have : inst₁.toAddGroupWithOne = inst₂.toAddGroupWithOne :=
    AddGroupWithOne.ext h_add h_one
  injection this with _ h_addMonoidWithOne; injection h_addMonoidWithOne
  cases inst₁; cases inst₂
  congr

namespace NonAssocRing

/-
**NonAssocRing.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonAssocRing`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : NonAssocRing R⦄, HAdd.hAdd = HAdd.hAdd → HMu
l.hMul = HMul.hMul → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalNonAssocRing.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalNonAss
ocRing R⦄, HAdd.hAdd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `NonAssocSemiring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonAssocSemiring R⦄,
 HAdd.hAdd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `AddCommGroupWithOne.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : AddCommGroupWithO
ne R⦄, HAdd.hAdd = HAdd.hAdd → One.one = One.one → inst₁ = inst₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.add_comm`：∀ {G : Type u} [self : AddCommGroup G] (a b : G),
 a + b = b + a
· 使用定理 `NonUnitalNonAssocRing.left_distrib`：∀ {α : Type u} [self : NonUnitalNonA
ssocRing α] (a b c : α), a * (b + c) = a * b + a * c
· 使用定理 `NonUnitalNonAssocRing.right_distrib`：∀ {α : Type u} [self : NonUnitalNon
AssocRing α] (a b c : α), (a + b) * c = a * c + b * c
· 使用定理 `NonUnitalNonAssocRing.zero_mul`：∀ {α : Type u} [self : NonUnitalNonAssoc
Ring α] (a : α), 0 * a = 0
· 使用定理 `NonUnitalNonAssocRing.mul_zero`：∀ {α : Type u} [self : NonUnitalNonAssoc
Ring α] (a : α), a * 0 = 0
· 使用定理 `NonAssocRing.one_mul`：∀ {α : Type u_1} [self : NonAssocRing α] (a : α), 
1 * a = a
· 使用定理 `NonAssocRing.mul_one`：∀ {α : Type u_1} [self : NonAssocRing α] (a : α), 
a * 1 = a
· 使用定理 `NonAssocRing.natCast_zero`：∀ {α : Type u_1} [self : NonAssocRing α], ↑0 
= 0
· 使用定理 `NonAssocRing.natCast_succ`：∀ {α : Type u_1} [self : NonAssocRing α] (n :
 ℕ), ↑(n + 1) = ↑n + 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `NonAssocRing.intCast_ofNat`：∀ {α : Type u_1} [self : NonAssocRing α] (n 
: ℕ), IntCast.intCast ↑n = ↑n
· 使用定理 `NonAssocRing.intCast_negSucc`：∀ {α : Type u_1} [self : NonAssocRing α] (
n : ℕ), IntCast.intCast (Int.negSucc n) = -↑(n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonAssocRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  have h₁ : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemiring := by
    ext : 1 <;> assumption
  -- Mathematically non-trivial fact: `intCast` is determined by the rest.
  have h₃ : inst₁.toAddCommGroupWithOne = inst₂.toAddCommGroupWithOne :=
    AddCommGroupWithOne.ext h_add (congrArg (·.toOne.one) h₂)
  cases inst₁; cases inst₂
  congr <;> solve | injection h₁ | injection h₂ | injection h₃
/-
**NonAssocRing.toNonAssocSemiring_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonAssocR
ing`。
形式化陈述：toNonAssocSemiring_injective : Function.Injective (@toNonAssocSemiring R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonAssocRing.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonAssocRing R⦄, HAdd.hA
dd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem toNonAssocSemiring_injective :
    Function.Injective (@toNonAssocSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h
/-
**NonAssocRing.toNonUnitalNonAssocring_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonA
ssocRing`。
形式化陈述：toNonUnitalNonAssocring_injective : Function.Injective (@toNonUnitalNonAss
ocRing R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonAssocRing.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonAssocRing R⦄, HAdd.hA
dd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
theorem toNonUnitalNonAssocring_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

end NonAssocRing

/-! ### Semiring -/
namespace Semiring

/-
**Semiring.ext** 是 Mathlib 中的一个定理，位于命名空间 `Semiring`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : Semiring R⦄, HAdd.hAdd = HAdd.hAdd → HMul.hM
ul = HMul.hMul → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommMonoid.ext`：∀ {M : Type u_1} ⦃m₁ m₂ : AddCommMonoid M⦄, HAdd.hAdd
 = HAdd.hAdd → m₁ = m₂
· 使用定理 `NonUnitalSemiring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalSemiring R
⦄, HAdd.hAdd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `NonAssocSemiring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonAssocSemiring R⦄,
 HAdd.hAdd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `Monoid.ext`：Monoid.ext {M : Type u} ⦃m₁ m₂ : Monoid M⦄ (h_mul : (letI
· 使用定理 `Semiring.left_distrib`：∀ {α : Type u} [self : Semiring α] (a b c : α), a
 * (b + c) = a * b + a * c
· 使用定理 `Semiring.right_distrib`：∀ {α : Type u} [self : Semiring α] (a b c : α), 
(a + b) * c = a * c + b * c
· 使用定理 `Semiring.zero_mul`：∀ {α : Type u} [self : Semiring α] (a : α), 0 * a = 0
· 使用定理 `Semiring.mul_zero`：∀ {α : Type u} [self : Semiring α] (a : α), a * 0 = 0
· 使用定理 `Monoid.one_mul`：∀ {M : Type u} [self : Monoid M] (a : M), 1 * a = a
· 使用定理 `Monoid.mul_one`：∀ {M : Type u} [self : Monoid M] (a : M), a * 1 = a
· 使用定理 `Semiring.natCast_zero`：∀ {α : Type u} [self : Semiring α], ↑0 = 0
· 使用定理 `Semiring.natCast_succ`：∀ {α : Type u} [self : Semiring α] (n : ℕ), ↑(n +
 1) = ↑n + 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[ext] theorem ext ⦃inst₁ inst₂ : Semiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Show that enough substructures are equal.
  have h₀ : inst₁.toAddCommMonoid = inst₂.toAddCommMonoid := by
    ext : 1 <;> assumption
  have h₁ : inst₁.toNonUnitalSemiring = inst₂.toNonUnitalSemiring := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemiring := by
    ext : 1 <;> assumption
  have h₃ : (inst₁.toMonoidWithZero).toMonoid = (inst₂.toMonoidWithZero).toMonoid := by
    ext : 1; exact h_mul
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr <;> solve | injection h₁ | injection h₂
/-
**Semiring.toNonUnitalSemiring_injective** 是 Mathlib 中的一个定理，位于命名空间 `Semiring`。
形式化陈述：toNonUnitalSemiring_injective : Function.Injective (@toNonUnitalSemiring R
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semiring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : Semiring R⦄, HAdd.hAdd = HAd
d.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h
/-
**Semiring.toNonAssocSemiring_injective** 是 Mathlib 中的一个定理，位于命名空间 `Semiring`。
形式化陈述：toNonAssocSemiring_injective : Function.Injective (@toNonAssocSemiring R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semiring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : Semiring R⦄, HAdd.hAdd = HAd
d.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem toNonAssocSemiring_injective :
    Function.Injective (@toNonAssocSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end Semiring

/-! ### Ring -/
namespace Ring

/-
**Ring.ext** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : Ring R⦄, HAdd.hAdd = HAdd.hAdd → HMul.hMul =
 HMul.hMul → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semiring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : Semiring R⦄, HAdd.hAdd = HAd
d.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `NonAssocRing.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonAssocRing R⦄, HAdd.hA
dd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddGroup.ext`：∀ {G : Type u_1} ⦃g₁ g₂ : AddGroup G⦄, HAdd.hAdd = HAdd.hA
dd → g₁ = g₂
· 使用定理 `Ring.sub_eq_add_neg`：∀ {R : Type u} [self : Ring R] (a b : R), a - b = a
 + -b
· 使用定理 `Ring.zsmul_zero'`：∀ {R : Type u} [self : Ring R] (a : R), 0 • a = 0
· 使用定理 `Ring.zsmul_succ'`：∀ {R : Type u} [self : Ring R] (n : ℕ) (a : R), ↑n.suc
c • a = ↑n • a + a
· 使用定理 `Ring.zsmul_neg'`：∀ {R : Type u} [self : Ring R] (n : ℕ) (a : R), Int.neg
Succ n • a = -(↑n.succ • a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Ring.neg_add_cancel`：∀ {R : Type u} [self : Ring R] (a : R), -a + a = 0
· 使用定理 `Ring.intCast_ofNat`：∀ {R : Type u} [self : Ring R] (n : ℕ), IntCast.intC
ast ↑n = ↑n
· 使用定理 `Ring.intCast_negSucc`：∀ {R : Type u} [self : Ring R] (n : ℕ), IntCast.in
tCast (Int.negSucc n) = -↑(n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[ext] theorem ext ⦃inst₁ inst₂ : Ring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Show that enough substructures are equal.
  have h₁ : inst₁.toSemiring = inst₂.toSemiring := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocRing = inst₂.toNonAssocRing := by
    ext : 1 <;> assumption
  /- We prove that the `SubNegMonoid`s are equal because they are one
  field away from `Sub` and `Neg`, enabling use of `injection`. -/
  have h₃ : (inst₁.toAddCommGroup).toAddGroup.toSubNegMonoid
            = (inst₂.toAddCommGroup).toAddGroup.toSubNegMonoid :=
    congrArg (@AddGroup.toSubNegMonoid R) <| by ext : 1; exact h_add
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr <;> solve | injection h₂ | injection h₃
/-
**Ring.toNonUnitalRing_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：toNonUnitalRing_injective : Function.Injective (@toNonUnitalRing R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : Ring R⦄, HAdd.hAdd = HAdd.hAdd →
 HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem toNonUnitalRing_injective :
    Function.Injective (@toNonUnitalRing R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h
/-
**Ring.toNonAssocRing_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：toNonAssocRing_injective : Function.Injective (@toNonAssocRing R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : Ring R⦄, HAdd.hAdd = HAdd.hAdd →
 HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem toNonAssocRing_injective :
    Function.Injective (@toNonAssocRing R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h
/-
**Ring.toSemiring_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：toSemiring_injective : Function.Injective (@toSemiring R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : Ring R⦄, HAdd.hAdd = HAdd.hAdd →
 HMul.hMul = HMul.hMul → inst₁ = inst₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem toSemiring_injective :
    Function.Injective (@toSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end Ring

/-! ### NonUnitalNonAssocCommSemiring -/
namespace NonUnitalNonAssocCommSemiring

/-
**NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring_injective** 是 Mathli
b 中的一个定理，位于命名空间 `NonUnitalNonAssocCommSemiring`。
形式化陈述：toNonUnitalNonAssocSemiring_injective : Function.Injective (@toNonUnitalNo
nAssocSemiring R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr
/-
**NonUnitalNonAssocCommSemiring.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalNonAssoc
CommSemiring`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalNonAssocCommSemiring R⦄,   HAdd.hAd
d = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring_injective`：toN
onUnitalNonAssocSemiring_injective : Function.Injective (@toNonUnitalNonAssocSem
iring R)
· 使用定理 `NonUnitalNonAssocSemiring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalNo
nAssocSemiring R⦄,   HAdd.hAdd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = ins
t₂
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocCommSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
  toNonUnitalNonAssocSemiring_injective <|
    NonUnitalNonAssocSemiring.ext h_add h_mul

end NonUnitalNonAssocCommSemiring

/-! ### NonUnitalCommSemiring -/
namespace NonUnitalCommSemiring

/-
**NonUnitalCommSemiring.toNonUnitalSemiring_injective** 是 Mathlib 中的一个定理，位于命名空间 
`NonUnitalCommSemiring`。
形式化陈述：toNonUnitalSemiring_injective : Function.Injective (@toNonUnitalSemiring R
)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr
/-
**NonUnitalCommSemiring.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalCommSemiring`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalCommSemiring R⦄, HAdd.hAdd = HAdd.h
Add → HMul.hMul = HMul.hMul → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalCommSemiring.toNonUnitalSemiring_injective`：toNonUnitalSemiring
_injective : Function.Injective (@toNonUnitalSemiring R)
· 使用定理 `NonUnitalSemiring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalSemiring R
⦄, HAdd.hAdd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalCommSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
  toNonUnitalSemiring_injective <|
    NonUnitalSemiring.ext h_add h_mul

end NonUnitalCommSemiring

-- At present, there is no `NonAssocCommSemiring` in Mathlib.

/-! ### NonUnitalNonAssocCommRing -/
namespace NonUnitalNonAssocCommRing

/-
**NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing_injective** 是 Mathlib 中的一个定理
，位于命名空间 `NonUnitalNonAssocCommRing`。
形式化陈述：toNonUnitalNonAssocRing_injective : Function.Injective (@toNonUnitalNonAss
ocRing R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNonUnitalNonAssocRing_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr
/-
**NonUnitalNonAssocCommRing.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalNonAssocComm
Ring`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalNonAssocCommRing R⦄,   HAdd.hAdd = 
HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing_injective`：toNonUnital
NonAssocRing_injective : Function.Injective (@toNonUnitalNonAssocRing R)
· 使用定理 `NonUnitalNonAssocRing.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalNonAss
ocRing R⦄, HAdd.hAdd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocCommRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
  toNonUnitalNonAssocRing_injective <|
    NonUnitalNonAssocRing.ext h_add h_mul

end NonUnitalNonAssocCommRing

/-! ### NonUnitalCommRing -/
namespace NonUnitalCommRing

/-
**NonUnitalCommRing.toNonUnitalRing_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alCommRing`。
形式化陈述：toNonUnitalRing_injective : Function.Injective (@toNonUnitalRing R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNonUnitalRing_injective :
    Function.Injective (@toNonUnitalRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr
/-
**NonUnitalCommRing.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalCommRing`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalCommRing R⦄, HAdd.hAdd = HAdd.hAdd 
→ HMul.hMul = HMul.hMul → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalCommRing.toNonUnitalRing_injective`：toNonUnitalRing_injective :
 Function.Injective (@toNonUnitalRing R)
· 使用定理 `NonUnitalRing.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : NonUnitalRing R⦄, HAdd.
hAdd = HAdd.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalCommRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
  toNonUnitalRing_injective <|
    NonUnitalRing.ext h_add h_mul

end NonUnitalCommRing

-- At present, there is no `NonAssocCommRing` in Mathlib.

/-! ### CommSemiring -/
namespace CommSemiring

/-
**CommSemiring.toSemiring_injective** 是 Mathlib 中的一个定理，位于命名空间 `CommSemiring`。
形式化陈述：toSemiring_injective : Function.Injective (@toSemiring R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSemiring_injective :
    Function.Injective (@toSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr
/-
**CommSemiring.ext** 是 Mathlib 中的一个定理，位于命名空间 `CommSemiring`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : CommSemiring R⦄, HAdd.hAdd = HAdd.hAdd → HMu
l.hMul = HMul.hMul → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommSemiring.toSemiring_injective`：toSemiring_injective : Function.Injec
tive (@toSemiring R)
· 使用定理 `Semiring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : Semiring R⦄, HAdd.hAdd = HAd
d.hAdd → HMul.hMul = HMul.hMul → inst₁ = inst₂
-/
@[ext] theorem ext ⦃inst₁ inst₂ : CommSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
  toSemiring_injective <|
    Semiring.ext h_add h_mul

end CommSemiring

/-! ### CommRing -/
namespace CommRing

/-
**CommRing.toRing_injective** 是 Mathlib 中的一个定理，位于命名空间 `CommRing`。
形式化陈述：toRing_injective : Function.Injective (@toRing R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRing_injective : Function.Injective (@toRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr
/-
**CommRing.ext** 是 Mathlib 中的一个定理，位于命名空间 `CommRing`。
形式化陈述：∀ {R : Type u} ⦃inst₁ inst₂ : CommRing R⦄, HAdd.hAdd = HAdd.hAdd → HMul.hM
ul = HMul.hMul → inst₁ = inst₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommRing.toRing_injective`：toRing_injective : Function.Injective (@toRin
g R)
· 使用定理 `Ring.ext`：∀ {R : Type u} ⦃inst₁ inst₂ : Ring R⦄, HAdd.hAdd = HAdd.hAdd →
 HMul.hMul = HMul.hMul → inst₁ = inst₂
-/
@[ext] theorem ext ⦃inst₁ inst₂ : CommRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
  toRing_injective <| Ring.ext h_add h_mul

end CommRing

