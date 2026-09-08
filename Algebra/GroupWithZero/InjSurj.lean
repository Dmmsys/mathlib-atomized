/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.GroupWithZero.NeZero

/-!
# Lifting groups with zero along injective/surjective maps

-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

open Function

variable {M₀ G₀ M₀' G₀' : Type*}

section MulZeroClass

variable [MulZeroClass M₀]

/-- Pull back a `MulZeroClass` instance along an injective function.
See note [reducible non-instances]. -/
/-
**Function.Injective.mulZeroClass** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`
。
形式化陈述：{M₀ : Type u_1} →   {M₀' : Type u_3} →     [inst : MulZeroClass M₀] →     
  [inst_1 : Mul M₀'] →         [inst_2 : Zero M₀'] →           (f : M₀' → M₀) → 
Function.Injective f → f 0 = 0 → (∀ (a b : M₀'), f (a * b) = f a * f b) → MulZer
oClass M₀'
参数：f : M₀' → M₀；∀ (a b : M₀'), f (a * b) = f a * f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a `MulZeroClass` instance along an injective function.
See note [reducible non-instances].
-/
protected abbrev Function.Injective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀' → M₀)
    (hf : Injective f) (zero : f 0 = 0) (mul : ∀ a b, f (a * b) = f a * f b) :
    MulZeroClass M₀' where
  zero_mul a := hf <| by simp only [mul, zero, zero_mul]
  mul_zero a := hf <| by simp only [mul, zero, mul_zero]

/-- Push forward a `MulZeroClass` instance along a surjective function.
See note [reducible non-instances]. -/
/-
**Function.Surjective.mulZeroClass** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjectiv
e`。
形式化陈述：{M₀ : Type u_1} →   {M₀' : Type u_3} →     [inst : MulZeroClass M₀] →     
  [inst_1 : Mul M₀'] →         [inst_2 : Zero M₀'] →           (f : M₀ → M₀') → 
Function.Surjective f → f 0 = 0 → (∀ (a b : M₀), f (a * b) = f a * f b) → MulZer
oClass M₀'
参数：f : M₀ → M₀'；∀ (a b : M₀), f (a * b) = f a * f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Push forward a `MulZeroClass` instance along a surjective function.
See note [reducible non-instances].
-/
protected abbrev Function.Surjective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀ → M₀')
    (hf : Surjective f) (zero : f 0 = 0) (mul : ∀ a b, f (a * b) = f a * f b) :
    MulZeroClass M₀' where
  mul_zero := hf.forall.2 fun x => by simp only [← zero, ← mul, mul_zero]
  zero_mul := hf.forall.2 fun x => by simp only [← zero, ← mul, zero_mul]

end MulZeroClass

section NoZeroDivisors

variable [Mul M₀] [Zero M₀] [Mul M₀'] [Zero M₀']
  (f : M₀ → M₀') (hf : Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)

include hf zero mul

/-- Pull back a `NoZeroDivisors` instance along an injective function. -/
/-
**Function.Injective.noZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injectiv
e`。
形式化陈述：∀ {M₀ : Type u_1} {M₀' : Type u_3} [inst : Mul M₀] [inst_1 : Zero M₀] [ins
t_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : M₀ → M₀'),   Function.Injective f → f 
0 = 0 → (∀ (x y : M₀), f (x * y) = f x * f y) → ∀ [NoZeroDivisors M₀'], NoZeroDi
visors M₀
参数：f : M₀ → M₀'；∀ (x y : M₀), f (x * y) = f x * f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0

--- 原说明 ---
Pull back a `NoZeroDivisors` instance along an injective function.
-/
protected theorem Function.Injective.noZeroDivisors [NoZeroDivisors M₀'] : NoZeroDivisors M₀ where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} H :=
    have : f a * f b = 0 := by rw [← mul, H, zero]
    (eq_zero_or_eq_zero_of_mul_eq_zero this).imp
      (fun H ↦ hf <| by rwa [zero]) fun H ↦ hf <| by rwa [zero]
/-
**Function.Injective.isLeftCancelMulZero** 是 Mathlib 中的一个定理，位于命名空间 `Function.Inj
ective`。
形式化陈述：∀ {M₀ : Type u_1} {M₀' : Type u_3} [inst : Mul M₀] [inst_1 : Zero M₀] [ins
t_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : M₀ → M₀'),   Function.Injective f →   
  f 0 = 0 → (∀ (x y : M₀), f (x * y) = f x * f y) → ∀ [IsLeftCancelMulZero M₀'],
 IsLeftCancelMulZero M₀
参数：f : M₀ → M₀'；∀ (x y : M₀), f (x * y) = f x * f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
protected theorem Function.Injective.isLeftCancelMulZero
    [IsLeftCancelMulZero M₀'] : IsLeftCancelMulZero M₀ where
  mul_left_cancel_of_ne_zero Hne _ _ He := by
    have := congr_arg f He
    rw [mul, mul] at this
    exact hf (mul_left_cancel₀ (fun Hfa => Hne <| hf <| by rw [Hfa, zero]) this)
/-
**Function.Injective.isRightCancelMulZero** 是 Mathlib 中的一个定理，位于命名空间 `Function.In
jective`。
形式化陈述：∀ {M₀ : Type u_1} {M₀' : Type u_3} [inst : Mul M₀] [inst_1 : Zero M₀] [ins
t_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : M₀ → M₀'),   Function.Injective f →   
  f 0 = 0 → (∀ (x y : M₀), f (x * y) = f x * f y) → ∀ [IsRightCancelMulZero M₀']
, IsRightCancelMulZero M₀
参数：f : M₀ → M₀'；∀ (x y : M₀), f (x * y) = f x * f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
protected theorem Function.Injective.isRightCancelMulZero
    [IsRightCancelMulZero M₀'] : IsRightCancelMulZero M₀ where
  mul_right_cancel_of_ne_zero Hne _ _ He := by
    have := congr_arg f He
    rw [mul, mul] at this
    exact hf (mul_right_cancel₀ (fun Hfa => Hne <| hf <| by rw [Hfa, zero]) this)
/-
**Function.Injective.isCancelMulZero** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injecti
ve`。
形式化陈述：∀ {M₀ : Type u_1} {M₀' : Type u_3} [inst : Mul M₀] [inst_1 : Zero M₀] [ins
t_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : M₀ → M₀'),   Function.Injective f → f 
0 = 0 → (∀ (x y : M₀), f (x * y) = f x * f y) → ∀ [IsCancelMulZero M₀'], IsCance
lMulZero M₀
参数：f : M₀ → M₀'；∀ (x y : M₀), f (x * y) = f x * f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isLeftCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u_
3} [inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (
f : M₀ → M₀'),   Function.In…
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Function.Injective.isRightCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u
_3} [inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   
(f : M₀ → M₀'),   Function.In…
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
-/
protected theorem Function.Injective.isCancelMulZero
    [IsCancelMulZero M₀'] : IsCancelMulZero M₀ where
  __ := hf.isLeftCancelMulZero f zero mul
  __ := hf.isRightCancelMulZero f zero mul

end NoZeroDivisors

section MulZeroOneClass

variable [MulZeroOneClass M₀]

/-- Pull back a `MulZeroOneClass` instance along an injective function.
See note [reducible non-instances]. -/
/-
**Function.Injective.mulZeroOneClass** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injecti
ve`。
形式化陈述：{M₀ : Type u_1} →   {M₀' : Type u_3} →     [inst : MulZeroOneClass M₀] →  
     [inst_1 : Mul M₀'] →         [inst_2 : Zero M₀'] →           [inst_3 : One 
M₀'] →             (f : M₀' → M₀) →               Function.Injective f → f 0 = 0
 → f 1 = 1 → (∀ (a b : M₀'), f (a * b) = f a * f b) → MulZeroOneClass M₀'
参数：f : M₀' → M₀；∀ (a b : M₀'), f (a * b) = f a * f b。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulOneClass.one_mul`：∀ {M : Type u} [self : MulOneClass M] (a : M), 1 * 
a = a
· 使用定理 `MulOneClass.mul_one`：∀ {M : Type u} [self : MulOneClass M] (a : M), a * 
1 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
Pull back a `MulZeroOneClass` instance along an injective function.
See note [reducible non-instances].
-/
protected abbrev Function.Injective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀' → M₀)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) :
    MulZeroOneClass M₀' :=
  { hf.mulZeroClass f zero mul, hf.mulOneClass f one mul with }

/-- Push forward a `MulZeroOneClass` instance along a surjective function.
See note [reducible non-instances]. -/
/-
**Function.Surjective.mulZeroOneClass** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjec
tive`。
形式化陈述：{M₀ : Type u_1} →   {M₀' : Type u_3} →     [inst : MulZeroOneClass M₀] →  
     [inst_1 : Mul M₀'] →         [inst_2 : Zero M₀'] →           [inst_3 : One 
M₀'] →             (f : M₀ → M₀') →               Function.Surjective f → f 0 = 
0 → f 1 = 1 → (∀ (a b : M₀), f (a * b) = f a * f b) → MulZeroOneClass M₀'
参数：f : M₀ → M₀'；∀ (a b : M₀), f (a * b) = f a * f b。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulOneClass.one_mul`：∀ {M : Type u} [self : MulOneClass M] (a : M), 1 * 
a = a
· 使用定理 `MulOneClass.mul_one`：∀ {M : Type u} [self : MulOneClass M] (a : M), a * 
1 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
Push forward a `MulZeroOneClass` instance along a surjective function.
See note [reducible non-instances].
-/
protected abbrev Function.Surjective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀ → M₀')
    (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) :
    MulZeroOneClass M₀' :=
  { hf.mulZeroClass f zero mul, hf.mulOneClass f one mul with }

end MulZeroOneClass

section SemigroupWithZero

/-- Pull back a `SemigroupWithZero` along an injective function.
See note [reducible non-instances]. -/
/-
**Function.Injective.semigroupWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injec
tive`。
形式化陈述：{M₀ : Type u_1} →   {M₀' : Type u_3} →     [inst : Zero M₀'] →       [inst
_1 : Mul M₀'] →         [inst_2 : SemigroupWithZero M₀] →           (f : M₀' → M
₀) →             Function.Injective f → f 0 = 0 → (∀ (x y : M₀'), f (x * y) = f 
x * f y) → SemigroupWithZero M₀'
参数：f : M₀' → M₀；∀ (x y : M₀'), f (x * y) = f x * f y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Semigroup.mul_assoc`：∀ {G : Type u} [self : Semigroup G] (a b c : G), a 
* b * c = a * (b * c)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
Pull back a `SemigroupWithZero` along an injective function.
See note [reducible non-instances].
-/
protected abbrev Function.Injective.semigroupWithZero [Zero M₀'] [Mul M₀'] [SemigroupWithZero M₀]
    (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) :
    SemigroupWithZero M₀' :=
  { hf.mulZeroClass f zero mul, ‹Zero M₀'›, hf.semigroup f mul with }

/-- Push forward a `SemigroupWithZero` along a surjective function.
See note [reducible non-instances]. -/
/-
**Function.Surjective.semigroupWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surj
ective`。
形式化陈述：{M₀ : Type u_1} →   {M₀' : Type u_3} →     [inst : SemigroupWithZero M₀] →
       [inst_1 : Zero M₀'] →         [inst_2 : Mul M₀'] →           (f : M₀ → M₀
') →             Function.Surjective f → f 0 = 0 → (∀ (x y : M₀), f (x * y) = f 
x * f y) → SemigroupWithZero M₀'
参数：f : M₀ → M₀'；∀ (x y : M₀), f (x * y) = f x * f y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Semigroup.mul_assoc`：∀ {G : Type u} [self : Semigroup G] (a b c : G), a 
* b * c = a * (b * c)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
Push forward a `SemigroupWithZero` along a surjective function.
See note [reducible non-instances].
-/
protected abbrev Function.Surjective.semigroupWithZero [SemigroupWithZero M₀] [Zero M₀'] [Mul M₀']
    (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) :
    SemigroupWithZero M₀' :=
  { hf.mulZeroClass f zero mul, ‹Zero M₀'›, hf.semigroup f mul with }

end SemigroupWithZero

section MonoidWithZero

/-- Pull back a `MonoidWithZero` along an injective function.
See note [reducible non-instances]. -/
/-
**Function.Injective.monoidWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injectiv
e`。
形式化陈述：{M₀ : Type u_1} →   {M₀' : Type u_3} →     [inst : Zero M₀'] →       [inst
_1 : Mul M₀'] →         [inst_2 : One M₀'] →           [inst_3 : Pow M₀' ℕ] →   
          [inst_4 : MonoidWithZero M₀] →               (f : M₀' → M₀) →         
        Function.Injective f →                   f 0 = 0 →                     f
 1 = 1 →                       (∀ (x y : M₀'), f (x * y) = f x * f y) →         
                (∀ (x : M₀') (n : ℕ), f (x ^ n) = f x ^ n) → MonoidWithZero M₀'
参数：f : M₀' → M₀；∀ (x y : M₀'), f (x * y) = f x * f y；∀ (x : M₀') (n : ℕ), f (x ^
 n) = f x ^ n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
Pull back a `MonoidWithZero` along an injective function.
See note [reducible non-instances].
-/
protected abbrev Function.Injective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    [MonoidWithZero M₀] (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    MonoidWithZero M₀' :=
  { hf.monoid f one mul npow, hf.mulZeroClass f zero mul with }

/-- Push forward a `MonoidWithZero` along a surjective function.
See note [reducible non-instances]. -/
/-
**Function.Surjective.monoidWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surject
ive`。
形式化陈述：{M₀ : Type u_1} →   {M₀' : Type u_3} →     [inst : Zero M₀'] →       [inst
_1 : Mul M₀'] →         [inst_2 : One M₀'] →           [inst_3 : Pow M₀' ℕ] →   
          [inst_4 : MonoidWithZero M₀] →               (f : M₀ → M₀') →         
        Function.Surjective f →                   f 0 = 0 →                     
f 1 = 1 →                       (∀ (x y : M₀), f (x * y) = f x * f y) →         
                (∀ (x : M₀) (n : ℕ), f (x ^ n) = f x ^ n) → MonoidWithZero M₀'
参数：f : M₀ → M₀'；∀ (x y : M₀), f (x * y) = f x * f y；∀ (x : M₀) (n : ℕ), f (x ^ n
) = f x ^ n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
Push forward a `MonoidWithZero` along a surjective function.
See note [reducible non-instances].
-/
protected abbrev Function.Surjective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    [MonoidWithZero M₀] (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    MonoidWithZero M₀' :=
  { hf.monoid f one mul npow, hf.mulZeroClass f zero mul with }

/-- Pull back a `CommMonoidWithZero` along an injective function.
See note [reducible non-instances]. -/
/-
**Function.Injective.commMonoidWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Function.Inje
ctive`。
形式化陈述：{M₀ : Type u_1} →   {M₀' : Type u_3} →     [inst : Zero M₀'] →       [inst
_1 : Mul M₀'] →         [inst_2 : One M₀'] →           [inst_3 : Pow M₀' ℕ] →   
          [inst_4 : CommMonoidWithZero M₀] →               (f : M₀' → M₀) →     
            Function.Injective f →                   f 0 = 0 →                  
   f 1 = 1 →                       (∀ (x y : M₀'), f (x * y) = f x * f y) →     
                    (∀ (x : M₀') (n : ℕ), f (x ^ n) = f x ^ n) → CommMonoidWithZ
ero M₀'
参数：f : M₀' → M₀；∀ (x y : M₀'), f (x * y) = f x * f y；∀ (x : M₀') (n : ℕ), f (x ^
 n) = f x ^ n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
Pull back a `CommMonoidWithZero` along an injective function.
See note [reducible non-instances].
-/
protected abbrev Function.Injective.commMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    [CommMonoidWithZero M₀] (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CommMonoidWithZero M₀' :=
  { hf.commMonoid f one mul npow, hf.mulZeroClass f zero mul with }

/-- Push forward a `CommMonoidWithZero` along a surjective function.
See note [reducible non-instances]. -/
/-
**Function.Surjective.commMonoidWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Function.Sur
jective`。
形式化陈述：{M₀ : Type u_1} →   {M₀' : Type u_3} →     [inst : Zero M₀'] →       [inst
_1 : Mul M₀'] →         [inst_2 : One M₀'] →           [inst_3 : Pow M₀' ℕ] →   
          [inst_4 : CommMonoidWithZero M₀] →               (f : M₀ → M₀') →     
            Function.Surjective f →                   f 0 = 0 →                 
    f 1 = 1 →                       (∀ (x y : M₀), f (x * y) = f x * f y) →     
                    (∀ (x : M₀) (n : ℕ), f (x ^ n) = f x ^ n) → CommMonoidWithZe
ro M₀'
参数：f : M₀ → M₀'；∀ (x y : M₀), f (x * y) = f x * f y；∀ (x : M₀) (n : ℕ), f (x ^ n
) = f x ^ n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
Push forward a `CommMonoidWithZero` along a surjective function.
See note [reducible non-instances].
-/
protected abbrev Function.Surjective.commMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    [CommMonoidWithZero M₀] (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CommMonoidWithZero M₀' :=
  { hf.commMonoid f one mul npow, hf.mulZeroClass f zero mul with }

end MonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀]

/-- Pull back a `GroupWithZero` along an injective function.
See note [reducible non-instances]. -/
/-
**Function.Injective.groupWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective
`。
形式化陈述：{G₀ : Type u_2} →   {G₀' : Type u_4} →     [inst : GroupWithZero G₀] →    
   [inst_1 : Zero G₀'] →         [inst_2 : Mul G₀'] →           [inst_3 : One G₀
'] →             [inst_4 : Inv G₀'] →               [inst_5 : Div G₀'] →        
         [inst_6 : Pow G₀' ℕ] →                   [inst_7 : Pow G₀' ℤ] →        
             (f : G₀' → G₀) →                       Function.Injective f →      
                   f 0 = 0 →                           f 1 = 1 →                
             (∀ (x y : G₀'), f (x * y) = f x * f y) →                           
    (∀ (x : G₀'), f x⁻¹ = (f x)⁻¹) →                                 (∀ (x y : G
₀'), f (x / y) = f x / f y) →                                   (∀ (x : G₀') (n 
: ℕ), f (x ^ n) = f x ^ n) →                                     (∀ (x : G₀') (n
 : ℤ), f (x ^ n) = f x ^ n) → GroupWithZero G₀'
参数：f : G₀' → G₀；∀ (x y : G₀'), f (x * y) = f x * f y；∀ (x : G₀'), f x⁻¹ = (f x)⁻
¹；∀ (x y : G₀'), f (x / y) = f x / f y；∀ (x : G₀') (n : ℕ), f (x ^ n) = f x ^ n；
∀ (x : G₀') (n : ℤ), f (x ^ n) = f x ^ n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DivInvMonoid.div_eq_mul_inv`：∀ {G : Type u} [self : DivInvMonoid G] (a b
 : G), a / b = a * b⁻¹
· 使用定理 `DivInvMonoid.zpow_zero'`：∀ {G : Type u} [self : DivInvMonoid G] (a : G),
 a ^ 0 = 1
· 使用定理 `DivInvMonoid.zpow_succ'`：∀ {G : Type u} [self : DivInvMonoid G] (n : ℕ) 
(a : G), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `DivInvMonoid.zpow_neg'`：∀ {G : Type u} [self : DivInvMonoid G] (n : ℕ) (
a : G), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹

--- 原说明 ---
Pull back a `GroupWithZero` along an injective function.
See note [reducible non-instances].
-/
protected abbrev Function.Injective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀']
    [Pow G₀' ℕ] [Pow G₀' ℤ] (f : G₀' → G₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : GroupWithZero G₀' :=
  { hf.monoidWithZero f zero one mul npow,
    hf.divInvMonoid f one mul inv div npow zpow,
    domain_nontrivial f zero one with
    inv_zero := hf <| by rw [inv, zero, inv_zero],
    mul_inv_cancel := fun x hx => hf <| by
      rw [one, mul, inv, mul_inv_cancel₀ ((hf.ne_iff' zero).2 hx)] }

/-- Push forward a `GroupWithZero` along a surjective function.
See note [reducible non-instances]. -/
/-
**Function.Surjective.groupWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjecti
ve`。
形式化陈述：{G₀ : Type u_2} →   {G₀' : Type u_4} →     [inst : GroupWithZero G₀] →    
   [inst_1 : Zero G₀'] →         [inst_2 : Mul G₀'] →           [inst_3 : One G₀
'] →             [inst_4 : Inv G₀'] →               [inst_5 : Div G₀'] →        
         [inst_6 : Pow G₀' ℕ] →                   [inst_7 : Pow G₀' ℤ] →        
             0 ≠ 1 →                       (f : G₀ → G₀') →                     
    Function.Surjective f →                           f 0 = 0 →                 
            f 1 = 1 →                               (∀ (x y : G₀), f (x * y) = f
 x * f y) →                                 (∀ (x : G₀), f x⁻¹ = (f x)⁻¹) →     
                              (∀ (x y : G₀), f (x / y) = f x / f y) →           
                          (∀ (x : G₀) (n : ℕ), f (x ^ n) = f x ^ n) →           
                            (∀ (x : G₀) (n : ℤ), f (x ^ n) = f x ^ n) → GroupWit
hZero G₀'
参数：f : G₀ → G₀'；∀ (x y : G₀), f (x * y) = f x * f y；∀ (x : G₀), f x⁻¹ = (f x)⁻¹；
∀ (x y : G₀), f (x / y) = f x / f y；∀ (x : G₀) (n : ℕ), f (x ^ n) = f x ^ n；∀ (x
 : G₀) (n : ℤ), f (x ^ n) = f x ^ n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DivInvMonoid.div_eq_mul_inv`：∀ {G : Type u} [self : DivInvMonoid G] (a b
 : G), a / b = a * b⁻¹
· 使用定理 `DivInvMonoid.zpow_zero'`：∀ {G : Type u} [self : DivInvMonoid G] (a : G),
 a ^ 0 = 1
· 使用定理 `DivInvMonoid.zpow_succ'`：∀ {G : Type u} [self : DivInvMonoid G] (n : ℕ) 
(a : G), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `DivInvMonoid.zpow_neg'`：∀ {G : Type u} [self : DivInvMonoid G] (n : ℕ) (
a : G), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹

--- 原说明 ---
Push forward a `GroupWithZero` along a surjective function.
See note [reducible non-instances].
-/
protected abbrev Function.Surjective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀']
    [Div G₀'] [Pow G₀' ℕ] [Pow G₀' ℤ] (h01 : (0 : G₀') ≠ 1) (f : G₀ → G₀') (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) :
    GroupWithZero G₀' :=
  { hf.monoidWithZero f zero one mul npow, hf.divInvMonoid f one mul inv div npow zpow with
    inv_zero := by rw [← zero, ← inv, inv_zero],
    mul_inv_cancel := hf.forall.2 fun x hx => by
        rw [← inv, ← mul, mul_inv_cancel₀ (mt (congr_arg f) fun h ↦ hx (h.trans zero)), one]
    exists_pair_ne := ⟨0, 1, h01⟩ }

end GroupWithZero

section CommGroupWithZero

variable [CommGroupWithZero G₀]

/-- Pull back a `CommGroupWithZero` along an injective function.
See note [reducible non-instances]. -/
/-
**Function.Injective.commGroupWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injec
tive`。
形式化陈述：{G₀ : Type u_2} →   {G₀' : Type u_4} →     [inst : CommGroupWithZero G₀] →
       [inst_1 : Zero G₀'] →         [inst_2 : Mul G₀'] →           [inst_3 : On
e G₀'] →             [inst_4 : Inv G₀'] →               [inst_5 : Div G₀'] →    
             [inst_6 : Pow G₀' ℕ] →                   [inst_7 : Pow G₀' ℤ] →    
                 (f : G₀' → G₀) →                       Function.Injective f →  
                       f 0 = 0 →                           f 1 = 1 →            
                 (∀ (x y : G₀'), f (x * y) = f x * f y) →                       
        (∀ (x : G₀'), f x⁻¹ = (f x)⁻¹) →                                 (∀ (x y
 : G₀'), f (x / y) = f x / f y) →                                   (∀ (x : G₀')
 (n : ℕ), f (x ^ n) = f x ^ n) →                                     (∀ (x : G₀'
) (n : ℤ), f (x ^ n) = f x ^ n) → CommGroupWithZero G₀'
参数：f : G₀' → G₀；∀ (x y : G₀'), f (x * y) = f x * f y；∀ (x : G₀'), f x⁻¹ = (f x)⁻
¹；∀ (x y : G₀'), f (x / y) = f x / f y；∀ (x : G₀') (n : ℕ), f (x ^ n) = f x ^ n；
∀ (x : G₀') (n : ℤ), f (x ^ n) = f x ^ n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommSemigroup.mul_comm`：∀ {G : Type u} [self : CommSemigroup G] (a b : G
), a * b = b * a
· 使用定理 `GroupWithZero.div_eq_mul_inv`：∀ {G₀ : Type u} [self : GroupWithZero G₀] 
(a b : G₀), a / b = a * b⁻¹
· 使用定理 `GroupWithZero.zpow_zero'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (a :
 G₀), a ^ 0 = 1
· 使用定理 `GroupWithZero.zpow_succ'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (n :
 ℕ) (a : G₀), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `GroupWithZero.zpow_neg'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (n : 
ℕ) (a : G₀), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `GroupWithZero.inv_zero`：∀ {G₀ : Type u} [self : GroupWithZero G₀], 0⁻¹ =
 0
· 使用定理 `GroupWithZero.mul_inv_cancel`：∀ {G₀ : Type u} [self : GroupWithZero G₀] 
(a : G₀), a ≠ 0 → a * a⁻¹ = 1

--- 原说明 ---
Pull back a `CommGroupWithZero` along an injective function.
See note [reducible non-instances].
-/
protected abbrev Function.Injective.commGroupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀']
    [Div G₀'] [Pow G₀' ℕ] [Pow G₀' ℤ] (f : G₀' → G₀) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroupWithZero G₀' :=
  { hf.groupWithZero f zero one mul inv div npow zpow, hf.commSemigroup f mul with }

/-- Push forward a `CommGroupWithZero` along a surjective function.
See note [reducible non-instances]. -/
@[instance_reducible]
/-
**Function.Surjective.commGroupWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surj
ective`。
形式化陈述：{G₀ : Type u_2} →   {G₀' : Type u_4} →     [inst : CommGroupWithZero G₀] →
       [inst_1 : Zero G₀'] →         [inst_2 : Mul G₀'] →           [inst_3 : On
e G₀'] →             [inst_4 : Inv G₀'] →               [inst_5 : Div G₀'] →    
             [inst_6 : Pow G₀' ℕ] →                   [inst_7 : Pow G₀' ℤ] →    
                 0 ≠ 1 →                       (f : G₀ → G₀') →                 
        Function.Surjective f →                           f 0 = 0 →             
                f 1 = 1 →                               (∀ (x y : G₀), f (x * y)
 = f x * f y) →                                 (∀ (x : G₀), f x⁻¹ = (f x)⁻¹) → 
                                  (∀ (x y : G₀), f (x / y) = f x / f y) →       
                              (∀ (x : G₀) (n : ℕ), f (x ^ n) = f x ^ n) →       
                                (∀ (x : G₀) (n : ℤ), f (x ^ n) = f x ^ n) → Comm
GroupWithZero G₀'
参数：f : G₀ → G₀'；∀ (x y : G₀), f (x * y) = f x * f y；∀ (x : G₀), f x⁻¹ = (f x)⁻¹；
∀ (x y : G₀), f (x / y) = f x / f y；∀ (x : G₀) (n : ℕ), f (x ^ n) = f x ^ n；∀ (x
 : G₀) (n : ℤ), f (x ^ n) = f x ^ n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommSemigroup.mul_comm`：∀ {G : Type u} [self : CommSemigroup G] (a b : G
), a * b = b * a
· 使用定理 `GroupWithZero.div_eq_mul_inv`：∀ {G₀ : Type u} [self : GroupWithZero G₀] 
(a b : G₀), a / b = a * b⁻¹
· 使用定理 `GroupWithZero.zpow_zero'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (a :
 G₀), a ^ 0 = 1
· 使用定理 `GroupWithZero.zpow_succ'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (n :
 ℕ) (a : G₀), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `GroupWithZero.zpow_neg'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (n : 
ℕ) (a : G₀), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `GroupWithZero.inv_zero`：∀ {G₀ : Type u} [self : GroupWithZero G₀], 0⁻¹ =
 0
· 使用定理 `GroupWithZero.mul_inv_cancel`：∀ {G₀ : Type u} [self : GroupWithZero G₀] 
(a : G₀), a ≠ 0 → a * a⁻¹ = 1

--- 原说明 ---
Push forward a `CommGroupWithZero` along a surjective function.
See note [reducible non-instances].
-/
protected def Function.Surjective.commGroupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀']
    [Div G₀'] [Pow G₀' ℕ] [Pow G₀' ℤ] (h01 : (0 : G₀') ≠ 1) (f : G₀ → G₀') (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) :
    CommGroupWithZero G₀' :=
  { hf.groupWithZero h01 f zero one mul inv div npow zpow, hf.commSemigroup f mul with }

end CommGroupWithZero

