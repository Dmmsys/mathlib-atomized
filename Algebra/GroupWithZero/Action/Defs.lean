/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Opposite
public import Mathlib.Algebra.Notation.Pi.Basic

/-!
# Definitions of group actions

This file defines a hierarchy of group action type-classes on top of the previously defined
notation classes `SMul` and its additive version `VAdd`:

* `SMulZeroClass` is a typeclass for an action that preserves zero
* `DistribSMul M A` is a typeclass for an action on an additive monoid (`AddZeroClass`) that
  preserves addition and zero
* `DistribMulAction M A` is a typeclass for an action of a multiplicative monoid on
  an additive monoid such that `a • (b + c) = a • b + a • c` and `a • 0 = 0`.

The hierarchy is extended further by `Module`, defined elsewhere.

## Notation

- `a • b` is used as notation for `SMul.smul a b`.

## Implementation details

This file should avoid depending on other parts of `GroupTheory`, to avoid import cycles.
More sophisticated lemmas belong in `GroupTheory.GroupAction`.

## Tags

group action
-/

@[expose] public section

assert_not_exists Equiv.Perm.equivUnitsEnd Prod.fst_mul Ring

open Function

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

/-- Typeclass for scalar multiplication that preserves `0` on the right. -/
/-
**SMulZeroClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_12 → (A : Type u_13) → [Zero A] → Type (max u_12 u_13)
参数：A : Type u_13；max u_12 u_13。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for scalar multiplication that preserves `0` on the right.
-/
class SMulZeroClass (M A : Type*) [Zero A] extends SMul M A where
  /-- Multiplying `0` by a scalar gives `0` -/
  smul_zero : ∀ a : M, a • (0 : A) = 0

section smul_zero

variable [Zero A] [SMulZeroClass M A]

@[simp]
/-
**smul_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_zero (a : M) : a • (0 : A) = 0
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulZeroClass.smul_zero`：∀ {M : Type u_12} {A : Type u_13} {inst : Zero 
A} [self : SMulZeroClass M A] (a : M), a • 0 = 0
-/
theorem smul_zero (a : M) : a • (0 : A) = 0 :=
  SMulZeroClass.smul_zero _
/-
**smul_ite_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_ite_zero (p : Prop) [Decidable p] (a : M) (b : A) : (a • if p then b 
else 0) = if p then a • b else 0
参数：p : Prop；a : M；b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma smul_ite_zero (p : Prop) [Decidable p] (a : M) (b : A) :
    (a • if p then b else 0) = if p then a • b else 0 := by split_ifs <;> simp
/-
**smul_eq_zero_of_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_eq_zero_of_right (a : M) {b : A} (h : b = 0) : a • b = 0
参数：a : M；h : b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma smul_eq_zero_of_right (a : M) {b : A} (h : b = 0) : a • b = 0 := h.symm ▸ smul_zero a
/-
**right_ne_zero_of_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：right_ne_zero_of_smul {a : M} {b : A} : a • b != 0 -> b != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `smul_eq_zero_of_right`：smul_eq_zero_of_right (a : M) {b : A} (h : b = 0)
 : a • b = 0
-/
lemma right_ne_zero_of_smul {a : M} {b : A} : a • b ≠ 0 → b ≠ 0 := mt <| smul_eq_zero_of_right a

/-- Pullback a zero-preserving scalar multiplication along an injective zero-preserving map.
See note [reducible non-instances]. -/
/-
**Function.Injective.smulZeroClass** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective
`。
形式化陈述：{M : Type u_1} →   {A : Type u_7} →     {B : Type u_9} →       [inst : Zer
o A] →         [inst_1 : SMulZeroClass M A] →           [inst_2 : Zero B] →     
        [inst_3 : SMul M B] →               (f : ZeroHom B A) → Function.Injecti
ve ⇑f → (∀ (c : M) (x : B), f (c • x) = c • f x) → SMulZeroClass M B
参数：f : ZeroHom B A；∀ (c : M) (x : B), f (c • x) = c • f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback a zero-preserving scalar multiplication along an injective zero-preserv
ing map.
See note [reducible non-instances].
-/
protected abbrev Function.Injective.smulZeroClass [Zero B] [SMul M B] (f : ZeroHom B A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) :
    SMulZeroClass M B where
  smul_zero c := hf <| by simp only [smul, map_zero, smul_zero]

/-- Pushforward a zero-preserving scalar multiplication along a zero-preserving map.
See note [reducible non-instances]. -/
/-
**ZeroHom.smulZeroClass** 是 Mathlib 中的一个定义，位于命名空间 `ZeroHom`。
形式化陈述：{M : Type u_1} →   {A : Type u_7} →     {B : Type u_9} →       [inst : Zer
o A] →         [inst_1 : SMulZeroClass M A] →           [inst_2 : Zero B] →     
        [inst_3 : SMul M B] → (f : ZeroHom A B) → (∀ (c : M) (x : A), f (c • x) 
= c • f x) → SMulZeroClass M B
参数：f : ZeroHom A B；∀ (c : M) (x : A), f (c • x) = c • f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pushforward a zero-preserving scalar multiplication along a zero-preserving map.
See note [reducible non-instances].
-/
protected abbrev ZeroHom.smulZeroClass [Zero B] [SMul M B] (f : ZeroHom A B)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) :
    SMulZeroClass M B where
  smul_zero c := by rw [← map_zero f, ← smul, smul_zero]

/-- Push forward the multiplication of `R` on `M` along a compatible surjective map `f : R → S`.

See also `Function.Surjective.distribMulActionLeft`.
-/
/-
**Function.Surjective.smulZeroClassLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Function.Surjective.smulZeroClassLeft {R S M : Type*} [Zero M] [SMulZeroCl
ass R M] [SMul S M] (f : R -> S) (hf : Function.Surjective f) (hsmul : forall (c
) (x : M), f c • x = c • x) : SMulZeroClass S M where smul_zero
参数：f : R -> S；hf : Function.Surjective f；hsmul : forall (c) (x : M), f c • x = c
 • x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Push forward the multiplication of `R` on `M` along a compatible surjective map 
`f : R → S`.

See also `Function.Surjective.distribMulActionLeft`.
-/
abbrev Function.Surjective.smulZeroClassLeft {R S M : Type*} [Zero M] [SMulZeroClass R M]
    [SMul S M] (f : R → S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) :
    SMulZeroClass S M where
  smul_zero := hf.forall.mpr fun c => by rw [hsmul, smul_zero]

variable (A)

/-- Compose a `SMulZeroClass` with a function, with scalar multiplication `f r' • m`.
See note [reducible non-instances]. -/
/-
**SMulZeroClass.compFun** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：SMulZeroClass.compFun (f : N -> M) : SMulZeroClass N A where smul
参数：f : N -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose a `SMulZeroClass` with a function, with scalar multiplication `f r' • m`
.
See note [reducible non-instances].
-/
abbrev SMulZeroClass.compFun (f : N → M) :
    SMulZeroClass N A where
  smul := SMul.comp.smul f
  smul_zero x := smul_zero (f x)

/-- Each element of the scalars defines a zero-preserving map. -/
@[simps]
/-
**SMulZeroClass.toZeroHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SMulZeroClass.toZeroHom (x : M) : ZeroHom A A where toFun
参数：x : M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SMulZeroClass.smul_zero`：∀ {M : Type u_12} {A : Type u_13} {inst : Zero 
A} [self : SMulZeroClass M A] (a : M), a • 0 = 0

--- 原说明 ---
Each element of the scalars defines a zero-preserving map.
-/
def SMulZeroClass.toZeroHom (x : M) :
    ZeroHom A A where
  toFun := (x • ·)
  map_zero' := smul_zero x

end smul_zero

section Zero
variable (M₀ A)

/-- `SMulWithZero` is a class consisting of a Type `M₀` with `0 ∈ M₀` and a scalar multiplication
of `M₀` on a Type `A` with `0`, such that the equality `r • m = 0` holds if at least one among `r`
or `m` equals `0`. -/
/-
**SMulWithZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M₀ : Type u_2) → (A : Type u_7) → [Zero M₀] → [Zero A] → Type (max u_2 u_
7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SMulWithZero` is a class consisting of a Type `M₀` with `0 ∈ M₀` and a scalar m
ultiplication
of `M₀` on a Type `A` with `0`, such that the equality `r • m = 0` holds if at l
east one among `r`
or `m` equals `0`.
-/
class SMulWithZero [Zero M₀] [Zero A] extends SMulZeroClass M₀ A where
  /-- Scalar multiplication by the scalar `0` is `0`. -/
  zero_smul : ∀ m : A, (0 : M₀) • m = 0

-- see Note [higher instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 1100) MulZeroClass.toSMulWithZero [MulZeroClass M₀] : SMulWithZero M₀ M₀ where
  smul := (· * ·)
  smul_zero := mul_zero
  zero_smul := zero_mul

/-- Like `MulZeroClass.toSMulWithZero`, but multiplies on the right. -/
/-
**MulZeroClass.toOppositeSMulWithZero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulZeroClass.toOppositeSMulWithZero [MulZeroClass M₀] : SMulWithZero M₀ᵐᵒᵖ
 M₀ where smul_zero _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
Like `MulZeroClass.toSMulWithZero`, but multiplies on the right.
-/
instance MulZeroClass.toOppositeSMulWithZero [MulZeroClass M₀] : SMulWithZero M₀ᵐᵒᵖ M₀ where
  smul_zero _ := zero_mul _
  zero_smul := mul_zero

variable {A} [Zero M₀] [Zero A] [SMulWithZero M₀ A]

@[simp]
/-
**zero_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_smul (m : A) : (0 : M₀) • m = 0
参数：m : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulWithZero.zero_smul`：∀ {M₀ : Type u_2} {A : Type u_7} {inst : Zero M₀
} {inst_1 : Zero A} [self : SMulWithZero M₀ A] (m : A), 0 • m = 0
-/
theorem zero_smul (m : A) : (0 : M₀) • m = 0 :=
  SMulWithZero.zero_smul m

variable {M₀} {a : M₀} {b : A}
/-
**smul_eq_zero_of_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_eq_zero_of_left (h : a = 0) (b : A) : a • b = 0
参数：h : a = 0；b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma smul_eq_zero_of_left (h : a = 0) (b : A) : a • b = 0 := h.symm ▸ zero_smul _ b
/-
**left_ne_zero_of_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：left_ne_zero_of_smul : a • b != 0 -> a != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `smul_eq_zero_of_left`：smul_eq_zero_of_left (h : a = 0) (b : A) : a • b =
 0
-/
lemma left_ne_zero_of_smul : a • b ≠ 0 → a ≠ 0 := mt fun h ↦ smul_eq_zero_of_left h b

variable [Zero M₀'] [Zero A'] [SMul M₀ A']

/-- Pullback a `SMulWithZero` structure along an injective zero-preserving homomorphism. -/
-- See note [reducible non-instances]
/-
**Function.Injective.smulWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`
。
形式化陈述：{M₀ : Type u_2} →   {A : Type u_7} →     {A' : Type u_8} →       [inst : Z
ero M₀] →         [inst_1 : Zero A] →           [inst_2 : SMulWithZero M₀ A] →  
           [inst_3 : Zero A'] →               [inst_4 : SMul M₀ A'] →           
      (f : ZeroHom A' A) →                   Function.Injective ⇑f → (∀ (a : M₀)
 (b : A'), f (a • b) = a • f b) → SMulWithZero M₀ A'
参数：f : ZeroHom A' A；∀ (a : M₀) (b : A'), f (a • b) = a • f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev Function.Injective.smulWithZero (f : ZeroHom A' A) (hf : Injective f)
    (smul : ∀ (a : M₀) (b), f (a • b) = a • f b) : SMulWithZero M₀ A' where
  zero_smul a := hf <| by simp [smul]
  smul_zero a := hf <| by simp [smul]

/-- Pushforward a `SMulWithZero` structure along a surjective zero-preserving homomorphism. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.smulWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjectiv
e`。
形式化陈述：{M₀ : Type u_2} →   {A : Type u_7} →     {A' : Type u_8} →       [inst : Z
ero M₀] →         [inst_1 : Zero A] →           [inst_2 : SMulWithZero M₀ A] →  
           [inst_3 : Zero A'] →               [inst_4 : SMul M₀ A'] →           
      (f : ZeroHom A A') →                   Function.Surjective ⇑f → (∀ (a : M₀
) (b : A), f (a • b) = a • f b) → SMulWithZero M₀ A'
参数：f : ZeroHom A A'；∀ (a : M₀) (b : A), f (a • b) = a • f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev Function.Surjective.smulWithZero (f : ZeroHom A A') (hf : Surjective f)
    (smul : ∀ (a : M₀) (b), f (a • b) = a • f b) : SMulWithZero M₀ A' where
  zero_smul m := by
    rcases hf m with ⟨x, rfl⟩
    simp [← smul]
  smul_zero c := by rw [← f.map_zero, ← smul, smul_zero]

variable (A)

/-- Compose a `SMulWithZero` with a `ZeroHom`, with action `f r' • m` -/
@[instance_reducible]
/-
**SMulWithZero.compHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SMulWithZero.compHom (f : ZeroHom M₀' M₀) : SMulWithZero M₀' A where smul
参数：f : ZeroHom M₀' M₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose a `SMulWithZero` with a `ZeroHom`, with action `f r' • m`
-/
def SMulWithZero.compHom (f : ZeroHom M₀' M₀) : SMulWithZero M₀' A where
  smul := (f · • ·)
  smul_zero m := smul_zero (f m)
  zero_smul m := by change (f 0) • m = 0; rw [map_zero, zero_smul]

end Zero

/-
**AddMonoid.natSMulWithZero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddMonoid.natSMulWithZero [AddMonoid A] : SMulWithZero Nat A where smul_ze
ro
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
-/
instance AddMonoid.natSMulWithZero [AddMonoid A] : SMulWithZero ℕ A where
  smul_zero := _root_.nsmul_zero
  zero_smul := zero_nsmul
/-
**AddGroup.intSMulWithZero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddGroup.intSMulWithZero [AddGroup A] : SMulWithZero Int A where smul_zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance AddGroup.intSMulWithZero [AddGroup A] : SMulWithZero ℤ A where
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul

section MonoidWithZero
variable (M₀ A) [MonoidWithZero M₀] [MonoidWithZero M₀'] [Zero A]

/-- An action of a monoid with zero `M₀` on a Type `A`, also with `0`, extends `MulAction` and
is compatible with `0` (both in `M₀` and in `A`), with `1 ∈ M₀`, and with associativity of
multiplication on the monoid `A`. -/
/-
**MulActionWithZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M₀ : Type u_2) → (A : Type u_7) → [MonoidWithZero M₀] → [Zero A] → Type (
max u_2 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An action of a monoid with zero `M₀` on a Type `A`, also with `0`, extends `MulA
ction` and
is compatible with `0` (both in `M₀` and in `A`), with `1 ∈ M₀`, and with associ
ativity of
multiplication on the monoid `A`.
-/
class MulActionWithZero extends MulAction M₀ A where
  -- these fields are copied from `SMulWithZero`, as `extends` behaves poorly
  /-- Scalar multiplication by any element send `0` to `0`. -/
  smul_zero : ∀ r : M₀, r • (0 : A) = 0
  /-- Scalar multiplication by the scalar `0` is `0`. -/
  zero_smul : ∀ m : A, (0 : M₀) • m = 0

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulActionWithZero.toSMulWithZero (M₀ A) {_ : MonoidWithZero M₀}
    {_ : Zero A} [m : MulActionWithZero M₀ A] : SMulWithZero M₀ A :=
  { m with }

-- see Note [higher instance priority]
/-- See also `Semiring.toModule` -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `Semiring.toModule`
-/
instance (priority := 1100) MonoidWithZero.toMulActionWithZero : MulActionWithZero M₀ M₀ :=
  { MulZeroClass.toSMulWithZero M₀, Monoid.toMulAction M₀ with }

/-- Like `MonoidWithZero.toMulActionWithZero`, but multiplies on the right. See also
`Semiring.toOppositeModule` -/
/-
**MonoidWithZero.toOppositeMulActionWithZero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MonoidWithZero.toOppositeMulActionWithZero : MulActionWithZero M₀ᵐᵒᵖ M₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Like `MonoidWithZero.toMulActionWithZero`, but multiplies on the right. See also
`Semiring.toOppositeModule`
-/
instance MonoidWithZero.toOppositeMulActionWithZero : MulActionWithZero M₀ᵐᵒᵖ M₀ :=
  { MulZeroClass.toOppositeSMulWithZero M₀, Monoid.toOppositeMulAction with }
/-
**MulActionWithZero.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `MulActionWithZero`。
形式化陈述：∀ (M₀ : Type u_2) (A : Type u_7) [inst : MonoidWithZero M₀] [inst_1 : Zero
 A] [MulActionWithZero M₀ A]   [Subsingleton M₀], Subsingleton A
参数：M₀ : Type u_2；A : Type u_7。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `MulActionWithZero.zero_smul`：∀ {M₀ : Type u_2} {A : Type u_7} {inst : Mo
noidWithZero M₀} {inst_1 : Zero A} [self : MulActionWithZero M₀ A] (m : A),   0 
• m = 0
-/
protected lemma MulActionWithZero.subsingleton [MulActionWithZero M₀ A] [Subsingleton M₀] :
    Subsingleton A where
  allEq x y := by
    rw [← one_smul M₀ x, ← one_smul M₀ y, Subsingleton.elim (1 : M₀) 0, zero_smul, zero_smul]
/-
**MulActionWithZero.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `MulActionWithZero`。
形式化陈述：∀ (M₀ : Type u_2) (A : Type u_7) [inst : MonoidWithZero M₀] [inst_1 : Zero
 A] [MulActionWithZero M₀ A] [Nontrivial A],   Nontrivial M₀
参数：M₀ : Type u_2；A : Type u_7。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用定理 `MulActionWithZero.subsingleton`：∀ (M₀ : Type u_2) (A : Type u_7) [inst :
 MonoidWithZero M₀] [inst_1 : Zero A] [MulActionWithZero M₀ A]   [Subsingleton M
₀], Subsingleton A
-/
protected lemma MulActionWithZero.nontrivial
    [MulActionWithZero M₀ A] [Nontrivial A] : Nontrivial M₀ :=
  (subsingleton_or_nontrivial M₀).resolve_left fun _ =>
    not_subsingleton A <| MulActionWithZero.subsingleton M₀ A

variable {M₀ A} [MulActionWithZero M₀ A] [Zero A'] [SMul M₀ A'] (p : Prop) [Decidable p]
/-
**ite_zero_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ite_zero_smul (a : M₀) (b : A) : (if p then a else 0 : M₀) • b = if p then
 a • b else 0
参数：a : M₀；b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
lemma ite_zero_smul (a : M₀) (b : A) : (if p then a else 0 : M₀) • b = if p then a • b else 0 := by
  rw [ite_smul, zero_smul]
/-
**boole_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：boole_smul (a : A) : (if p then 1 else 0 : M₀) • a = if p then a else 0
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma boole_smul (a : A) : (if p then 1 else 0 : M₀) • a = if p then a else 0 := by simp
/-
**Pi.single_apply_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.single_apply_smul {ι : Type*} [DecidableEq ι] (x : A) (i j : ι) : (Pi.s
ingle i 1 : ι -> M₀) j • x = (Pi.single i x : ι -> A) j
参数：x : A；i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
lemma Pi.single_apply_smul {ι : Type*} [DecidableEq ι] (x : A) (i j : ι) :
    (Pi.single i 1 : ι → M₀) j • x = (Pi.single i x : ι → A) j := by
  rw [single_apply, ite_smul, one_smul, zero_smul, single_apply]

/-- Pullback a `MulActionWithZero` structure along an injective zero-preserving homomorphism. -/
-- See note [reducible non-instances]
/-
**Function.Injective.mulActionWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injec
tive`。
形式化陈述：{M₀ : Type u_2} →   {A : Type u_7} →     {A' : Type u_8} →       [inst : M
onoidWithZero M₀] →         [inst_1 : Zero A] →           [inst_2 : MulActionWit
hZero M₀ A] →             [inst_3 : Zero A'] →               [inst_4 : SMul M₀ A
'] →                 (f : ZeroHom A' A) →                   Function.Injective ⇑
f → (∀ (a : M₀) (b : A'), f (a • b) = a • f b) → MulActionWithZero M₀ A'
参数：f : ZeroHom A' A；∀ (a : M₀) (b : A'), f (a • b) = a • f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev Function.Injective.mulActionWithZero (f : ZeroHom A' A) (hf : Injective f)
    (smul : ∀ (a : M₀) (b), f (a • b) = a • f b) : MulActionWithZero M₀ A' :=
  { hf.mulAction f smul, hf.smulWithZero f smul with }

/-- Pushforward a `MulActionWithZero` structure along a surjective zero-preserving homomorphism. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.mulActionWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surj
ective`。
形式化陈述：{M₀ : Type u_2} →   {A : Type u_7} →     {A' : Type u_8} →       [inst : M
onoidWithZero M₀] →         [inst_1 : Zero A] →           [inst_2 : MulActionWit
hZero M₀ A] →             [inst_3 : Zero A'] →               [inst_4 : SMul M₀ A
'] →                 (f : ZeroHom A A') →                   Function.Surjective 
⇑f → (∀ (a : M₀) (b : A), f (a • b) = a • f b) → MulActionWithZero M₀ A'
参数：f : ZeroHom A A'；∀ (a : M₀) (b : A), f (a • b) = a • f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev Function.Surjective.mulActionWithZero (f : ZeroHom A A') (hf : Surjective f)
    (smul : ∀ (a : M₀) (b), f (a • b) = a • f b) : MulActionWithZero M₀ A' :=
  { hf.mulAction f smul, hf.smulWithZero f smul with }

variable (A)

/-- Compose a `MulActionWithZero` with a `MonoidWithZeroHom`, with action `f r' • m` -/
@[instance_reducible]
/-
**MulActionWithZero.compHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulActionWithZero.compHom (f : M₀' ->*₀ M₀) : MulActionWithZero M₀' A wher
e __
参数：f : M₀' ->*₀ M₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose a `MulActionWithZero` with a `MonoidWithZeroHom`, with action `f r' • m`
-/
def MulActionWithZero.compHom (f : M₀' →*₀ M₀) : MulActionWithZero M₀' A where
  __ := SMulWithZero.compHom A f.toZeroHom
  mul_smul r s m := by change f (r * s) • m = f r • f s • m; simp [mul_smul]
  one_smul m := by change f 1 • m = m; simp

end MonoidWithZero

section GroupWithZero
variable [GroupWithZero G₀] [GroupWithZero G₀'] [MulActionWithZero G₀ G₀']
  [SMulCommClass G₀ G₀' G₀'] [IsScalarTower G₀ G₀' G₀']

/-
**smul_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_inv (g : G) (a : H) : (g • a)⁻¹ = g⁻¹ • a⁻¹
参数：g : G；a : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_eq_of_mul_eq_one_right`：inv_eq_of_mul_eq_one_right : a * b = 1 -> a⁻
¹ = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_mul_smul_comm`：smul_mul_smul_comm [Mul α] [Mul β] [SMul α β] [IsSca
larTower α β β] [IsScalarTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c :
 α) (d :…
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma smul_inv₀ (c : G₀) (x : G₀') : (c • x)⁻¹ = c⁻¹ • x⁻¹ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp only [inv_zero, zero_smul]
  obtain rfl | hx := eq_or_ne x 0
  · simp only [inv_zero, smul_zero]
  · refine inv_eq_of_mul_eq_one_left ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, inv_mul_cancel₀ hx, one_smul]

end GroupWithZero

/-- Typeclass for scalar multiplication that preserves `0` and `+` on the right.

This is exactly `DistribMulAction` without the `MulAction` part.
-/
@[ext]
/-
**DistribSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_12 → (A : Type u_13) → [AddZeroClass A] → Type (max u_12 u_13)
参数：A : Type u_13；max u_12 u_13。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for scalar multiplication that preserves `0` and `+` on the right.

This is exactly `DistribMulAction` without the `MulAction` part.
-/
class DistribSMul (M A : Type*) [AddZeroClass A] extends SMulZeroClass M A where
  /-- Scalar multiplication distributes across addition -/
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y

section DistribSMul

variable [AddZeroClass A] [DistribSMul M A]

/-
**smul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
参数：a : M；b₁ b₂ : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribSMul.smul_add`：∀ {M : Type u_12} {A : Type u_13} {inst : AddZeroC
lass A} [self : DistribSMul M A] (a : M) (x y : A),   a • (x + y) = a • x + a • 
y
-/
theorem smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂ :=
  DistribSMul.smul_add _ _ _

/-- Pullback a distributive scalar multiplication along an injective additive monoid
homomorphism.
See note [reducible non-instances]. -/
/-
**Function.Injective.distribSMul** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`。
形式化陈述：{M : Type u_1} →   {A : Type u_7} →     {B : Type u_9} →       [inst : Add
ZeroClass A] →         [inst_1 : DistribSMul M A] →           [inst_2 : AddZeroC
lass B] →             [inst_3 : SMul M B] →               (f : B →+ A) → Functio
n.Injective ⇑f → (∀ (c : M) (x : B), f (c • x) = c • f x) → DistribSMul M B
参数：f : B →+ A；∀ (c : M) (x : B), f (c • x) = c • f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback a distributive scalar multiplication along an injective additive monoid
homomorphism.
See note [reducible non-instances].
-/
protected abbrev Function.Injective.distribSMul [AddZeroClass B] [SMul M B] (f : B →+ A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribSMul M B :=
  { hf.smulZeroClass f.toZeroHom smul with
    smul_add := fun c x y => hf <| by simp only [smul, map_add, smul_add] }

/-- Pushforward a distributive scalar multiplication along a surjective additive monoid
homomorphism.
See note [reducible non-instances]. -/
/-
**Function.Surjective.distribSMul** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjective
`。
形式化陈述：{M : Type u_1} →   {A : Type u_7} →     {B : Type u_9} →       [inst : Add
ZeroClass A] →         [inst_1 : DistribSMul M A] →           [inst_2 : AddZeroC
lass B] →             [inst_3 : SMul M B] →               (f : A →+ B) → Functio
n.Surjective ⇑f → (∀ (c : M) (x : A), f (c • x) = c • f x) → DistribSMul M B
参数：f : A →+ B；∀ (c : M) (x : A), f (c • x) = c • f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pushforward a distributive scalar multiplication along a surjective additive mon
oid
homomorphism.
See note [reducible non-instances].
-/
protected abbrev Function.Surjective.distribSMul [AddZeroClass B] [SMul M B] (f : A →+ B)
    (hf : Surjective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribSMul M B :=
  { f.toZeroHom.smulZeroClass smul with
    smul_add := fun c x y => by
      rcases hf x with ⟨x, rfl⟩
      rcases hf y with ⟨y, rfl⟩
      simp only [smul_add, ← smul, ← map_add] }

/-- Push forward the multiplication of `R` on `M` along a compatible surjective map `f : R → S`.

See also `Function.Surjective.distribMulActionLeft`.
-/
/-
**Function.Surjective.distribSMulLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Function.Surjective.distribSMulLeft {R S M : Type*} [AddZeroClass M] [Dist
ribSMul R M] [SMul S M] (f : R -> S) (hf : Function.Surjective f) (hsmul : foral
l (c) (x : M), f c • x = c • x) : DistribSMul S M
参数：f : R -> S；hf : Function.Surjective f；hsmul : forall (c) (x : M), f c • x = c
 • x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Push forward the multiplication of `R` on `M` along a compatible surjective map 
`f : R → S`.

See also `Function.Surjective.distribMulActionLeft`.
-/
abbrev Function.Surjective.distribSMulLeft {R S M : Type*} [AddZeroClass M] [DistribSMul R M]
    [SMul S M] (f : R → S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) : DistribSMul S M :=
  { hf.smulZeroClassLeft f hsmul with
    smul_add := hf.forall.mpr fun c x y => by simp only [hsmul, smul_add] }

variable (A)

/-- Compose a `DistribSMul` with a function, with scalar multiplication `f r' • m`.
See note [reducible non-instances]. -/
/-
**DistribSMul.compFun** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：DistribSMul.compFun (f : N -> M) : DistribSMul N A
参数：f : N -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose a `DistribSMul` with a function, with scalar multiplication `f r' • m`.
See note [reducible non-instances].
-/
abbrev DistribSMul.compFun (f : N → M) : DistribSMul N A :=
  { SMulZeroClass.compFun A f with
    smul_add := fun x => smul_add (f x) }

/-- Each element of the scalars defines an additive monoid homomorphism. -/
@[simps]
/-
**DistribSMul.toAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DistribSMul.toAddMonoidHom (x : M) : A ->+ A
参数：x : M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DistribSMul.smul_add`：∀ {M : Type u_12} {A : Type u_13} {inst : AddZeroC
lass A} [self : DistribSMul M A] (a : M) (x y : A),   a • (x + y) = a • x + a • 
y

--- 原说明 ---
Each element of the scalars defines an additive monoid homomorphism.
-/
def DistribSMul.toAddMonoidHom (x : M) : A →+ A :=
  { SMulZeroClass.toZeroHom A x with toFun := (x • ·), map_add' := smul_add x }
/-
**AddMonoid.nat_smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddMonoid.nat_smulCommClass {M A : Type*} [AddMonoid A] [DistribSMul M A] 
: SMulCommClass Nat M A where smul_comm n x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidHom.map_nsmul`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoi
d M] [inst_1 : AddMonoid N] (f : M →+ N) (n : ℕ) (a : M),   f (n • a) = n • f a
-/
instance AddMonoid.nat_smulCommClass {M A : Type*} [AddMonoid A] [DistribSMul M A] :
    SMulCommClass ℕ M A where
  smul_comm n x y := ((DistribSMul.toAddMonoidHom A x).map_nsmul n y).symm

-- `SMulCommClass.symm` is not registered as an instance, as it would cause a loop
/-
**AddMonoid.nat_smulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddMonoid.nat_smulCommClass' {M A : Type*} [AddMonoid A] [DistribSMul M A]
 : SMulCommClass M Nat A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance AddMonoid.nat_smulCommClass' {M A : Type*} [AddMonoid A] [DistribSMul M A] :
    SMulCommClass M ℕ A :=
  .symm _ _ _

end DistribSMul

/-- Typeclass for multiplicative actions on additive structures.

For example, if `G` is a group (with group law written as multiplication) and `A` is an
abelian group (with group law written as addition), then to give `A` a `G`-module
structure (for example, to use the theory of group cohomology) is to say `[DistribMulAction G A]`.
Note in that we do not use the `Module` typeclass for `G`-modules, as the `Module` typeclass
is for modules over a ring rather than a group.

Mathematically, `DistribMulAction G A` is equivalent to giving `A` the structure of
a `ℤ[G]`-module.
-/
@[ext]
/-
**DistribMulAction** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_12) → (A : Type u_13) → [Monoid M] → [AddMonoid A] → Type (max
 u_12 u_13)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for multiplicative actions on additive structures.

For example, if `G` is a group (with group law written as multiplication) and `A
` is an
abelian group (with group law written as addition), then to give `A` a `G`-modul
e
structure (for example, to use the theory of group cohomology) is to say `[Distr
ibMulAction G A]`.
Note in that we do not use the `Module` typeclass for `G`-modules, as the `Modul
e` typeclass
is for modules over a ring rather than a group.

Mathematically, `DistribMulAction G A` is equivalent to giving `A` the structure
 of
a `ℤ[G]`-module.
-/
class DistribMulAction (M A : Type*) [Monoid M] [AddMonoid A] extends MulAction M A where
  /-- Multiplying `0` by a scalar gives `0` -/
  smul_zero : ∀ a : M, a • (0 : A) = 0
  /-- Scalar multiplication distributes across addition -/
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y

section

variable [Monoid M] [AddMonoid A] [DistribMulAction M A]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) DistribMulAction.toDistribSMul : DistribSMul M A :=
  { ‹DistribMulAction M A› with }

/-! We make sure that the definition of `DistribMulAction.toDistribSMul` was done correctly,
and the two paths from `DistribMulAction` to `SMul` are indeed definitionally equal. -/
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We make sure that the definition of `DistribMulAction.toDistribSMul` was done co
rrectly,
and the two paths from `DistribMulAction` to `SMul` are indeed definitionally eq
ual.
-/
example :
    (DistribMulAction.toMulAction.toSMul : SMul M A) =
      DistribMulAction.toDistribSMul.toSMul :=
  rfl

/-- Pullback a distributive multiplicative action along an injective additive monoid
homomorphism.
See note [reducible non-instances]. -/
/-
**Function.Injective.distribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Function.Inject
ive`。
形式化陈述：{M : Type u_1} →   {A : Type u_7} →     {B : Type u_9} →       [inst : Mon
oid M] →         [inst_1 : AddMonoid A] →           [inst_2 : DistribMulAction M
 A] →             [inst_3 : AddMonoid B] →               [inst_4 : SMul M B] →  
               (f : B →+ A) → Function.Injective ⇑f → (∀ (c : M) (x : B), f (c •
 x) = c • f x) → DistribMulAction M B
参数：f : B →+ A；∀ (c : M) (x : B), f (c • x) = c • f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.one_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Monoid α} [
self : MulAction α β] (b : β), 1 • b = b

--- 原说明 ---
Pullback a distributive multiplicative action along an injective additive monoid
homomorphism.
See note [reducible non-instances].
-/
protected abbrev Function.Injective.distribMulAction [AddMonoid B] [SMul M B] (f : B →+ A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribMulAction M B :=
  { hf.distribSMul f smul, hf.mulAction f smul with }

/-- Pushforward a distributive multiplicative action along a surjective additive monoid
homomorphism.
See note [reducible non-instances]. -/
/-
**Function.Surjective.distribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surje
ctive`。
形式化陈述：{M : Type u_1} →   {A : Type u_7} →     {B : Type u_9} →       [inst : Mon
oid M] →         [inst_1 : AddMonoid A] →           [inst_2 : DistribMulAction M
 A] →             [inst_3 : AddMonoid B] →               [inst_4 : SMul M B] →  
               (f : A →+ B) → Function.Surjective ⇑f → (∀ (c : M) (x : A), f (c 
• x) = c • f x) → DistribMulAction M B
参数：f : A →+ B；∀ (c : M) (x : A), f (c • x) = c • f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.one_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Monoid α} [
self : MulAction α β] (b : β), 1 • b = b

--- 原说明 ---
Pushforward a distributive multiplicative action along a surjective additive mon
oid
homomorphism.
See note [reducible non-instances].
-/
protected abbrev Function.Surjective.distribMulAction [AddMonoid B] [SMul M B] (f : A →+ B)
    (hf : Surjective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribMulAction M B :=
  { hf.distribSMul f smul, hf.mulAction f smul with }

variable (A)

/-- Each element of the monoid defines an additive monoid homomorphism. -/
@[simps!, deprecated DistribSMul.toAddMonoidHom (since := "2026-01-07")]
/-
**DistribMulAction.toAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DistribMulAction.toAddMonoidHom (x : M) : A ->+ A
参数：x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each element of the monoid defines an additive monoid homomorphism.
-/
def DistribMulAction.toAddMonoidHom (x : M) : A →+ A :=
  DistribSMul.toAddMonoidHom A x

variable (M)

/-- Each element of the monoid defines an additive monoid homomorphism. -/
@[simps]
/-
**DistribMulAction.toAddMonoidEnd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DistribMulAction.toAddMonoidEnd : M ->* AddMonoid.End A where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each element of the monoid defines an additive monoid homomorphism.
-/
def DistribMulAction.toAddMonoidEnd :
    M →* AddMonoid.End A where
  toFun := DistribSMul.toAddMonoidHom A
  map_one' := AddMonoidHom.ext <| one_smul M
  map_mul' x y := AddMonoidHom.ext <| mul_smul x y

end

section

variable [AddGroup A] [DistribSMul M A]

/-
**AddGroup.int_smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddGroup.int_smulCommClass : SMulCommClass Int M A where smul_comm n x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidHom.map_zsmul`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup
 α] [inst_1 : SubtractionMonoid β] (f : α →+ β) (n : ℤ) (g : α),   f (n • g) = n
 • f g
-/
instance AddGroup.int_smulCommClass : SMulCommClass ℤ M A where
  smul_comm n x y := ((DistribSMul.toAddMonoidHom A x).map_zsmul n y).symm

-- `SMulCommClass.symm` is not registered as an instance, as it would cause a loop
/-
**AddGroup.int_smulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddGroup.int_smulCommClass' : SMulCommClass M Int A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance AddGroup.int_smulCommClass' : SMulCommClass M ℤ A :=
  SMulCommClass.symm _ _ _

@[simp]
/-
**smul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_neg (r : M) (x : A) : r • -x = -(r • x)
参数：r : M；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_neg_of_add_eq_zero_left`：∀ {G : Type u_1} [inst : SubtractionMonoid G
] {a b : G}, a + b = 0 → a = -b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem smul_neg (r : M) (x : A) : r • -x = -(r • x) :=
  eq_neg_of_add_eq_zero_left <| by rw [← smul_add, neg_add_cancel, smul_zero]
/-
**smul_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
参数：r : M；x y : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
-/
theorem smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, smul_add, smul_neg]

end

section DistribMulAction
variable [Group α] [AddMonoid β] [DistribMulAction α β]

/-
**smul_eq_zero_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_eq_zero_iff_eq (a : α) {x : β} : a • x = 0 ↔ x = 0
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma smul_eq_zero_iff_eq (a : α) {x : β} : a • x = 0 ↔ x = 0 :=
  ⟨fun h => by rw [← inv_smul_smul a x, h, smul_zero], fun h => h.symm ▸ smul_zero _⟩
/-
**smul_ne_zero_iff_ne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_ne_zero_iff_ne (a : α) {x : β} : a • x != 0 ↔ x != 0
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `smul_eq_zero_iff_eq`：smul_eq_zero_iff_eq (a : α) {x : β} : a • x = 0 ↔ x
 = 0
-/
lemma smul_ne_zero_iff_ne (a : α) {x : β} : a • x ≠ 0 ↔ x ≠ 0 :=
  not_congr <| smul_eq_zero_iff_eq a

end DistribMulAction

section MulDistribMulAction
variable [Group α] [GroupWithZero β] [MulDistribMulAction α β]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulZeroClass α β where
  smul_zero g := not_imp_comm.mp mul_inv_cancel₀ <| by
    rw [← smul_one g, ← inv_smul_eq_iff, smul_mul', inv_smul_smul, zero_mul]
    exact zero_ne_one

/-- A version of `smul_inv'` for groups with zero. -/
/-
**smul_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_inv (g : G) (a : H) : (g • a)⁻¹ = g⁻¹ • a⁻¹
参数：g : G；a : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_eq_of_mul_eq_one_right`：inv_eq_of_mul_eq_one_right : a * b = 1 -> a⁻
¹ = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_mul_smul_comm`：smul_mul_smul_comm [Mul α] [Mul β] [SMul α β] [IsSca
larTower α β β] [IsScalarTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c :
 α) (d :…
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
A version of `smul_inv'` for groups with zero.
-/
@[simp] theorem smul_inv₀' (g : α) (x : β) : g • x⁻¹ = (g • x)⁻¹ := by
  by_cases hx : x = 0
  · rw [hx, inv_zero, smul_zero, inv_zero]
  · apply eq_inv_of_mul_eq_one_right
    rw [← smul_mul', mul_inv_cancel₀ hx, smul_one]
/-
**smul_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_div₀' (g : α) (x y : β) : g • (x / y) = (g • x) / (g • y) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, smul_mul', smul_inv₀']

end MulDistribMulAction

