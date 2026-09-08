/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# Characters from additive to multiplicative monoids

Let `A` be an additive monoid, and `M` a multiplicative one. An *additive character* of `A` with
values in `M` is simply a map `A → M` which intertwines the addition operation on `A` with the
multiplicative operation on `M`.

We define these objects, using the namespace `AddChar`, and show that if `A` is a commutative group
under addition, then the additive characters are also a group (written multiplicatively). Note that
we do not need `M` to be a group here.

We also include some constructions specific to the case when `A = R` is a ring; then we define
`mulShift ψ r`, where `ψ : AddChar R M` and `r : R`, to be the character defined by
`x ↦ ψ (r * x)`.

For more refined results of a number-theoretic nature (primitive characters, Gauss sums, etc)
see `Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean`.

## Implementation notes

Due to their role as the dual of an additive group, additive characters must themselves be an
additive group. This contrasts to their pointwise operations which make them a multiplicative group.
We simply define both the additive and multiplicative group structures and prove them equal.

For more information on this design decision, see the following zulip thread:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Additive.20characters

## Tags

additive character
-/

@[expose] public section

/-!
### Definitions related to and results on additive characters
-/

open Function Multiplicative
open Finset hiding card
open Fintype (card)

section AddCharDef

-- The domain of our additive characters
variable (A : Type*) [AddMonoid A]

-- The target
variable (M : Type*) [Monoid M]

/-- `AddChar A M` is the type of maps `A → M`, for `A` an additive monoid and `M` a multiplicative
monoid, which intertwine addition in `A` with multiplication in `M`.

We only put the typeclasses needed for the definition, although in practice we are usually
interested in much more specific cases (e.g. when `A` is a group and `M` a commutative ring).
-/
/-
**AddChar** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_1) → [AddMonoid A] → (M : Type u_2) → [Monoid M] → Type (max u
_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddChar A M` is the type of maps `A → M`, for `A` an additive monoid and `M` a 
multiplicative
monoid, which intertwine addition in `A` with multiplication in `M`.

We only put the typeclasses needed for the definition, although in practice we a
re usually
interested in much more specific cases (e.g. when `A` is a group and `M` a commu
tative ring).
-/
structure AddChar where
  /-- The underlying function.

  Do not use this function directly. Instead use the coercion coming from the `FunLike`
  instance. -/
  toFun : A → M
  /-- The function maps `0` to `1`.

  Do not use this directly. Instead use `AddChar.map_zero_eq_one`. -/
  map_zero_eq_one' : toFun 0 = 1
  /-- The function maps addition in `A` to multiplication in `M`.

  Do not use this directly. Instead use `AddChar.map_add_eq_mul`. -/
  map_add_eq_mul' : ∀ a b : A, toFun (a + b) = toFun a * toFun b

end AddCharDef

namespace AddChar

section Basic
-- results which don't require commutativity or inverses

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

/-- Define coercion to a function. -/
/-
**AddChar.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `AddChar`。
形式化陈述：instFunLike : FunLike (AddChar A M) A M where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define coercion to a function.
-/
instance instFunLike : FunLike (AddChar A M) A M where
  coe := AddChar.toFun
  coe_injective φ ψ h := by cases φ; cases ψ; congr

initialize_simps_projections AddChar (toFun → apply) -- needs to come after FunLike instance
/-
**AddChar.ext** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M] (
f g : AddChar A M),   (∀ (x : A), f x = g x) → f = g
参数：f g : AddChar A M；∀ (x : A), f x = g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
@[ext] lemma ext (f g : AddChar A M) (h : ∀ x : A, f x = g x) : f = g :=
  DFunLike.ext f g h
/-
**AddChar.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M] (
f : A → M) (map_zero_eq_one' : f 0 = 1)   (map_add_eq_mul' : ∀ (a b : A), f (a +
 b) = f a * f b),   ⇑{ toFun := f, map_zero_eq_one' := map_zero_eq_one', map_add
_eq_mul' := map_add_eq_mul' } = f
参数：f : A → M；map_zero_eq_one' : f 0 = 1；map_add_eq_mul' : ∀ (a b : A), f (a + b)
 = f a * f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mk (f : A → M)
    (map_zero_eq_one' : f 0 = 1) (map_add_eq_mul' : ∀ a b : A, f (a + b) = f a * f b) :
    AddChar.mk f map_zero_eq_one' map_add_eq_mul' = f := by
  rfl

/-- An additive character maps `0` to `1`. -/
/-
**AddChar.map_zero_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M] (
ψ : AddChar A M), ψ 0 = 1
参数：ψ : AddChar A M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.map_zero_eq_one'`：∀ {A : Type u_1} [inst : AddMonoid A] {M : Typ
e u_2} [inst_1 : Monoid M] (self : AddChar A M), self.toFun 0 = 1

--- 原说明 ---
An additive character maps `0` to `1`.
-/
@[simp] lemma map_zero_eq_one (ψ : AddChar A M) : ψ 0 = 1 := ψ.map_zero_eq_one'

/-- An additive character maps sums to products. -/
/-
**AddChar.map_add_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (x + y) = ψ x * ψ y
参数：ψ : AddChar A M；x y : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.map_add_eq_mul'`：∀ {A : Type u_1} [inst : AddMonoid A] {M : Type
 u_2} [inst_1 : Monoid M] (self : AddChar A M) (a b : A),   self.toFun (a + b) =
 self.toFun a…

--- 原说明 ---
An additive character maps sums to products.
-/
lemma map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (x + y) = ψ x * ψ y := ψ.map_add_eq_mul' x y

/-- Interpret an additive character as a monoid homomorphism. -/
/-
**AddChar.toMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：toMonoidHom (φ : AddChar A M) : Multiplicative A ->* M where toFun
参数：φ : AddChar A M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.map_zero_eq_one'`：∀ {A : Type u_1} [inst : AddMonoid A] {M : Typ
e u_2} [inst_1 : Monoid M] (self : AddChar A M), self.toFun 0 = 1
· 使用定理 `AddChar.map_add_eq_mul'`：∀ {A : Type u_1} [inst : AddMonoid A] {M : Type
 u_2} [inst_1 : Monoid M] (self : AddChar A M) (a b : A),   self.toFun (a + b) =
 self.toFun a…

--- 原说明 ---
Interpret an additive character as a monoid homomorphism.
-/
def toMonoidHom (φ : AddChar A M) : Multiplicative A →* M where
  toFun := φ.toFun
  map_one' := φ.map_zero_eq_one'
  map_mul' := φ.map_add_eq_mul'

-- this instance was a bad idea and conflicted with `instFunLike` above
/-
**AddChar.toMonoidHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M] (
ψ : AddChar A M) (a : Multiplicative A),   ψ.toMonoidHom a = ψ (Multiplicative.t
oAdd a)
参数：ψ : AddChar A M；a : Multiplicative A；Multiplicative.toAdd a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMonoidHom_apply (ψ : AddChar A M) (a : Multiplicative A) :
    ψ.toMonoidHom a = ψ a.toAdd :=
  rfl

/-- An additive character maps multiples by natural numbers to powers. -/
/-
**AddChar.map_nsmul_eq_pow** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：map_nsmul_eq_pow (ψ : AddChar A M) (n : Nat) (x : A) : ψ (n • x) = ψ x ^ n
参数：ψ : AddChar A M；n : Nat；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n

--- 原说明 ---
An additive character maps multiples by natural numbers to powers.
-/
lemma map_nsmul_eq_pow (ψ : AddChar A M) (n : ℕ) (x : A) : ψ (n • x) = ψ x ^ n :=
  ψ.toMonoidHom.map_pow x n

/-- Additive characters `A → M` are the same thing as monoid homomorphisms from `Multiplicative A`
to `M`. -/
/-
**AddChar.toMonoidHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：toMonoidHomEquiv : AddChar A M ≃ (Multiplicative A ->* M) where toFun φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Additive characters `A → M` are the same thing as monoid homomorphisms from `Mul
tiplicative A`
to `M`.
-/
def toMonoidHomEquiv : AddChar A M ≃ (Multiplicative A →* M) where
  toFun φ := φ.toMonoidHom
  invFun f :=
  { toFun := f.toFun
    map_zero_eq_one' := f.map_one'
    map_add_eq_mul' := f.map_mul' }
/-
**AddChar.coe_toMonoidHomEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M] (
ψ : AddChar A M),   ⇑(AddChar.toMonoidHomEquiv ψ) = ⇑ψ ∘ ⇑Multiplicative.toAdd
参数：ψ : AddChar A M；AddChar.toMonoidHomEquiv ψ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_toMonoidHomEquiv (ψ : AddChar A M) :
    ⇑(toMonoidHomEquiv ψ) = ψ ∘ Multiplicative.toAdd := rfl
/-
**AddChar.coe_toMonoidHomEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M] (
ψ : Multiplicative A →* M),   ⇑(AddChar.toMonoidHomEquiv.symm ψ) = ⇑ψ ∘ ⇑Multipl
icative.ofAdd
参数：ψ : Multiplicative A →* M；AddChar.toMonoidHomEquiv.symm ψ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp, norm_cast] lemma coe_toMonoidHomEquiv_symm (ψ : Multiplicative A →* M) :
    ⇑(toMonoidHomEquiv.symm ψ) = ψ ∘ Multiplicative.ofAdd := rfl
/-
**AddChar.toMonoidHomEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M] (
ψ : AddChar A M) (a : Multiplicative A),   (AddChar.toMonoidHomEquiv ψ) a = ψ (M
ultiplicative.toAdd a)
参数：ψ : AddChar A M；a : Multiplicative A；AddChar.toMonoidHomEquiv ψ；Multiplicativ
e.toAdd a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMonoidHomEquiv_apply (ψ : AddChar A M) (a : Multiplicative A) :
    toMonoidHomEquiv ψ a = ψ a.toAdd := rfl
/-
**AddChar.toMonoidHomEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M] (
ψ : Multiplicative A →* M) (a : A),   (AddChar.toMonoidHomEquiv.symm ψ) a = ψ (M
ultiplicative.ofAdd a)
参数：ψ : Multiplicative A →* M；a : A；AddChar.toMonoidHomEquiv.symm ψ；Multiplicativ
e.ofAdd a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma toMonoidHomEquiv_symm_apply (ψ : Multiplicative A →* M) (a : A) :
    toMonoidHomEquiv.symm ψ a = ψ (Multiplicative.ofAdd a) := rfl

/-- Interpret an additive character as a monoid homomorphism. -/
/-
**AddChar.toAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：toAddMonoidHom (φ : AddChar A M) : A ->+ Additive M where toFun
参数：φ : AddChar A M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.map_zero_eq_one'`：∀ {A : Type u_1} [inst : AddMonoid A] {M : Typ
e u_2} [inst_1 : Monoid M] (self : AddChar A M), self.toFun 0 = 1
· 使用定理 `AddChar.map_add_eq_mul'`：∀ {A : Type u_1} [inst : AddMonoid A] {M : Type
 u_2} [inst_1 : Monoid M] (self : AddChar A M) (a b : A),   self.toFun (a + b) =
 self.toFun a…

--- 原说明 ---
Interpret an additive character as a monoid homomorphism.
-/
def toAddMonoidHom (φ : AddChar A M) : A →+ Additive M where
  toFun := φ.toFun
  map_zero' := φ.map_zero_eq_one'
  map_add' := φ.map_add_eq_mul'
/-
**AddChar.coe_toAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M] (
ψ : AddChar A M),   ⇑ψ.toAddMonoidHom = ⇑Additive.ofMul ∘ ⇑ψ
参数：ψ : AddChar A M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toAddMonoidHom (ψ : AddChar A M) : ⇑ψ.toAddMonoidHom = Additive.ofMul ∘ ψ := rfl
/-
**AddChar.toAddMonoidHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M] (
ψ : AddChar A M) (a : A),   ψ.toAddMonoidHom a = Additive.ofMul (ψ a)
参数：ψ : AddChar A M；a : A；ψ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAddMonoidHom_apply (ψ : AddChar A M) (a : A) :
    ψ.toAddMonoidHom a = Additive.ofMul (ψ a) := rfl

/-- Additive characters `A → M` are the same thing as additive homomorphisms from `A` to
`Additive M`. -/
/-
**AddChar.toAddMonoidHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：toAddMonoidHomEquiv : AddChar A M ≃ (A ->+ Additive M) where toFun φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Additive characters `A → M` are the same thing as additive homomorphisms from `A
` to
`Additive M`.
-/
def toAddMonoidHomEquiv : AddChar A M ≃ (A →+ Additive M) where
  toFun φ := φ.toAddMonoidHom
  invFun f :=
  { toFun := f.toFun
    map_zero_eq_one' := f.map_zero'
    map_add_eq_mul' := f.map_add' }

@[simp, norm_cast]
/-
**AddChar.coe_toAddMonoidHomEquiv** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：coe_toAddMonoidHomEquiv (ψ : AddChar A M) : ⇑(toAddMonoidHomEquiv ψ) = Add
itive.ofMul ∘ ψ
参数：ψ : AddChar A M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toAddMonoidHomEquiv (ψ : AddChar A M) :
    ⇑(toAddMonoidHomEquiv ψ) = Additive.ofMul ∘ ψ := rfl
/-
**AddChar.coe_toAddMonoidHomEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M] (
ψ : A →+ Additive M),   ⇑(AddChar.toAddMonoidHomEquiv.symm ψ) = ⇑Additive.toMul 
∘ ⇑ψ
参数：ψ : A →+ Additive M；AddChar.toAddMonoidHomEquiv.symm ψ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp, norm_cast] lemma coe_toAddMonoidHomEquiv_symm (ψ : A →+ Additive M) :
    ⇑(toAddMonoidHomEquiv.symm ψ) = Additive.toMul ∘ ψ := rfl
/-
**AddChar.toAddMonoidHomEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M] (
ψ : AddChar A M) (a : A),   (AddChar.toAddMonoidHomEquiv ψ) a = Additive.ofMul (
ψ a)
参数：ψ : AddChar A M；a : A；AddChar.toAddMonoidHomEquiv ψ；ψ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAddMonoidHomEquiv_apply (ψ : AddChar A M) (a : A) :
    toAddMonoidHomEquiv ψ a = Additive.ofMul (ψ a) := rfl
/-
**AddChar.toAddMonoidHomEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M] (
ψ : A →+ Additive M) (a : A),   (AddChar.toAddMonoidHomEquiv.symm ψ) a = Additiv
e.toMul (ψ a)
参数：ψ : A →+ Additive M；a : A；AddChar.toAddMonoidHomEquiv.symm ψ；ψ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma toAddMonoidHomEquiv_symm_apply (ψ : A →+ Additive M) (a : A) :
    toAddMonoidHomEquiv.symm ψ a = (ψ a).toMul := rfl

/-- The trivial additive character (sending everything to `1`). -/
/-
**AddChar.instOne** 是 Mathlib 中的一个实例，位于命名空间 `AddChar`。
形式化陈述：instOne : One (AddChar A M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial additive character (sending everything to `1`).
-/
instance instOne : One (AddChar A M) := toMonoidHomEquiv.one

/-- The trivial additive character (sending everything to `1`). -/
/-
**AddChar.instZero** 是 Mathlib 中的一个实例，位于命名空间 `AddChar`。
形式化陈述：instZero : Zero (AddChar A M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial additive character (sending everything to `1`).
-/
instance instZero : Zero (AddChar A M) := ⟨1⟩
/-
**AddChar.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M], 
⇑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_one : ⇑(1 : AddChar A M) = 1 := rfl
/-
**AddChar.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M], 
⇑0 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_zero : ⇑(0 : AddChar A M) = 1 := rfl
/-
**AddChar.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M] (
a : A), 1 a = 1
参数：a : A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma one_apply (a : A) : (1 : AddChar A M) a = 1 := rfl
/-
**AddChar.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M] (
a : A), 0 a = 1
参数：a : A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zero_apply (a : A) : (0 : AddChar A M) a = 1 := rfl
/-
**AddChar.one_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：one_eq_zero : (1 : AddChar A M) = (0 : AddChar A M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_eq_zero : (1 : AddChar A M) = (0 : AddChar A M) := rfl
/-
**AddChar.coe_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M] {
ψ : AddChar A M}, ⇑ψ = 1 ↔ ψ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddChar.coe_zero`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [
inst_1 : Monoid M], ⇑0 = 1
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma coe_eq_one : ⇑ψ = 1 ↔ ψ = 0 := by rw [← coe_zero, DFunLike.coe_fn_eq]
/-
**AddChar.toMonoidHomEquiv_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M], 
AddChar.toMonoidHomEquiv 0 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMonoidHomEquiv_zero : toMonoidHomEquiv (0 : AddChar A M) = 1 := rfl
/-
**AddChar.toMonoidHomEquiv_symm_one** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M], 
AddChar.toMonoidHomEquiv.symm 1 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma toMonoidHomEquiv_symm_one :
    toMonoidHomEquiv.symm (1 : Multiplicative A →* M) = 0 := rfl
/-
**AddChar.toAddMonoidHomEquiv_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M], 
AddChar.toAddMonoidHomEquiv 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAddMonoidHomEquiv_zero : toAddMonoidHomEquiv (0 : AddChar A M) = 0 := rfl
/-
**AddChar.toAddMonoidHomEquiv_symm_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_1 : Monoid M], 
AddChar.toAddMonoidHomEquiv.symm 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma toAddMonoidHomEquiv_symm_zero :
    toAddMonoidHomEquiv.symm (0 : A →+ Additive M) = 0 := rfl
/-
**AddChar.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `AddChar`。
形式化陈述：instInhabited : Inhabited (AddChar A M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (AddChar A M) := ⟨1⟩

/-- Composing a `MonoidHom` with an `AddChar` yields another `AddChar`. -/
/-
**AddChar._root_.MonoidHom.compAddChar** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing a `MonoidHom` with an `AddChar` yields another `AddChar`.
-/
def _root_.MonoidHom.compAddChar {N : Type*} [Monoid N] (f : M →* N) (φ : AddChar A M) :
    AddChar A N := toMonoidHomEquiv.symm (f.comp φ.toMonoidHom)

@[simp, norm_cast]
/-
**AddChar._root_.MonoidHom.coe_compAddChar** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MonoidHom.coe_compAddChar {N : Type*} [Monoid N] (f : M →* N) (φ : AddChar A M) :
    f.compAddChar φ = f ∘ φ :=
  rfl

@[simp, norm_cast]
/-
**AddChar._root_.MonoidHom.compAddChar_apply** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MonoidHom.compAddChar_apply (f : M →* N) (φ : AddChar A M) : f.compAddChar φ = f ∘ φ :=
  rfl
/-
**AddChar._root_.MonoidHom.compAddChar_injective_left** 是 Mathlib 中的一个引理，位于命名空间 
`AddChar`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MonoidHom.compAddChar_injective_left (ψ : AddChar A M) (hψ : Surjective ψ) :
    Injective fun f : M →* N ↦ f.compAddChar ψ := by
  rintro f g h; rw [DFunLike.ext'_iff] at h ⊢; exact hψ.injective_comp_right h
/-
**AddChar._root_.MonoidHom.compAddChar_injective_right** 是 Mathlib 中的一个引理，位于命名空间
 `AddChar`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MonoidHom.compAddChar_injective_right (f : M →* N) (hf : Injective f) :
    Injective fun ψ : AddChar B M ↦ f.compAddChar ψ := by
  rintro ψ χ h; rw [DFunLike.ext'_iff] at h ⊢; exact hf.comp_left h

/-- Composing an `AddChar` with an `AddMonoidHom` yields another `AddChar`. -/
/-
**AddChar.compAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：compAddMonoidHom (φ : AddChar B M) (f : A ->+ B) : AddChar A M
参数：φ : AddChar B M；f : A ->+ B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Composing an `AddChar` with an `AddMonoidHom` yields another `AddChar`.
-/
def compAddMonoidHom (φ : AddChar B M) (f : A →+ B) : AddChar A M :=
  toAddMonoidHomEquiv.symm (φ.toAddMonoidHom.comp f)

@[simp, norm_cast]
/-
**AddChar.coe_compAddMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：coe_compAddMonoidHom (φ : AddChar B M) (f : A ->+ B) : φ.compAddMonoidHom 
f = φ ∘ f
参数：φ : AddChar B M；f : A ->+ B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_compAddMonoidHom (φ : AddChar B M) (f : A →+ B) : φ.compAddMonoidHom f = φ ∘ f := rfl
/-
**AddChar.compAddMonoidHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {M : Type u_3} [inst : AddMonoid A] [inst_
1 : AddMonoid B] [inst_2 : Monoid M]   (ψ : AddChar B M) (f : A →+ B) (a : A), (
ψ.compAddMonoidHom f) a = ψ (f a)
参数：ψ : AddChar B M；f : A →+ B；a : A；ψ.compAddMonoidHom f；f a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compAddMonoidHom_apply (ψ : AddChar B M) (f : A →+ B)
    (a : A) : ψ.compAddMonoidHom f a = ψ (f a) := rfl
/-
**AddChar.compAddMonoidHom_injective_left** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：compAddMonoidHom_injective_left (f : A ->+ B) (hf : Surjective f) : Inject
ive fun ψ : AddChar B M => ψ.compAddMonoidHom f
参数：f : A ->+ B；hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFunLike.ext'_iff`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [i
 : DFunLike F α β] {f g : F}, f = g ↔ ⇑f = ⇑g
· 使用定理 `Function.Surjective.injective_comp_right`：∀ {α : Sort u_1} {β : Sort u_2
} {γ : Sort u_3} {f : α → β}, Function.Surjective f → Function.Injective fun g =
> g ∘ f
-/
lemma compAddMonoidHom_injective_left (f : A →+ B) (hf : Surjective f) :
    Injective fun ψ : AddChar B M ↦ ψ.compAddMonoidHom f := by
  rintro ψ χ h; rw [DFunLike.ext'_iff] at h ⊢; exact hf.injective_comp_right h
/-
**AddChar.compAddMonoidHom_injective_right** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：compAddMonoidHom_injective_right (ψ : AddChar B M) (hψ : Injective ψ) : In
jective fun f : A ->+ B => ψ.compAddMonoidHom f
参数：ψ : AddChar B M；hψ : Injective ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFunLike.ext'_iff`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [i
 : DFunLike F α β] {f g : F}, f = g ↔ ⇑f = ⇑g
· 使用定理 `Function.Injective.comp_left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort 
u_3} {g : β → γ}, Function.Injective g → Function.Injective fun x => g ∘ x
-/
lemma compAddMonoidHom_injective_right (ψ : AddChar B M) (hψ : Injective ψ) :
    Injective fun f : A →+ B ↦ ψ.compAddMonoidHom f := by
  rintro f g h
  rw [DFunLike.ext'_iff] at h ⊢; exact hψ.comp_left h
/-
**AddChar.eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：eq_one_iff : ψ = 1 ↔ forall x, ψ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
lemma eq_one_iff : ψ = 1 ↔ ∀ x, ψ x = 1 := DFunLike.ext_iff
/-
**AddChar.eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：eq_zero_iff : ψ = 0 ↔ forall x, ψ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
lemma eq_zero_iff : ψ = 0 ↔ ∀ x, ψ x = 1 := DFunLike.ext_iff
/-
**AddChar.ne_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：ne_one_iff : ψ != 1 ↔ exists x, ψ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ne_iff`：ne_iff {f g : F} : f != g ↔ exists a, f a != g a
-/
lemma ne_one_iff : ψ ≠ 1 ↔ ∃ x, ψ x ≠ 1 := DFunLike.ne_iff
/-
**AddChar.ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：ne_zero_iff : ψ != 0 ↔ exists x, ψ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ne_iff`：ne_iff {f g : F} : f != g ↔ exists a, f a != g a
-/
lemma ne_zero_iff : ψ ≠ 0 ↔ ∃ x, ψ x ≠ 1 := DFunLike.ne_iff
/-
**AddChar.** 是 Mathlib 中的一个实例，位于命名空间 `AddChar`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : DecidableEq (AddChar A M) := Classical.decEq _

end Basic

section toCommMonoid

variable {ι A M : Type*} [AddMonoid A] [CommMonoid M]

/-- When `M` is commutative, `AddChar A M` is a commutative monoid. -/
/-
**AddChar.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `AddChar`。
形式化陈述：instCommMonoid : CommMonoid (AddChar A M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `M` is commutative, `AddChar A M` is a commutative monoid.
-/
instance instCommMonoid : CommMonoid (AddChar A M) :=
  fast_instance% toMonoidHomEquiv.commMonoid

/-- When `M` is commutative, `AddChar A M` is an additive commutative monoid. -/
/-
**AddChar.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `AddChar`。
形式化陈述：instAddCommMonoid : AddCommMonoid (AddChar A M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `M` is commutative, `AddChar A M` is an additive commutative monoid.
-/
instance instAddCommMonoid : AddCommMonoid (AddChar A M) :=
  inferInstanceAs (AddCommMonoid (Additive (AddChar A M)))
/-
**AddChar.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_2} {M : Type u_3} [inst : AddMonoid A] [inst_1 : CommMonoid 
M] (ψ χ : AddChar A M), ⇑(ψ * χ) = ⇑ψ * ⇑χ
参数：ψ χ : AddChar A M；ψ * χ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mul (ψ χ : AddChar A M) : ⇑(ψ * χ) = ψ * χ := rfl
/-
**AddChar.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_2} {M : Type u_3} [inst : AddMonoid A] [inst_1 : CommMonoid 
M] (ψ χ : AddChar A M), ⇑(ψ + χ) = ⇑ψ * ⇑χ
参数：ψ χ : AddChar A M；ψ + χ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_add (ψ χ : AddChar A M) : ⇑(ψ + χ) = ψ * χ := rfl
/-
**AddChar.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_2} {M : Type u_3} [inst : AddMonoid A] [inst_1 : CommMonoid 
M] (ψ : AddChar A M) (n : ℕ),   ⇑(ψ ^ n) = ⇑ψ ^ n
参数：ψ : AddChar A M；n : ℕ；ψ ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_pow (ψ : AddChar A M) (n : ℕ) : ⇑(ψ ^ n) = ψ ^ n := rfl
/-
**AddChar.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_2} {M : Type u_3} [inst : AddMonoid A] [inst_1 : CommMonoid 
M] (n : ℕ) (ψ : AddChar A M),   ⇑(n • ψ) = ⇑ψ ^ n
参数：n : ℕ；ψ : AddChar A M；n • ψ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_nsmul (n : ℕ) (ψ : AddChar A M) : ⇑(n • ψ) = ψ ^ n := rfl

@[simp, norm_cast]
/-
**AddChar.coe_prod** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：coe_prod (s : Finset ι) (ψ : ι -> AddChar A M) : ∏ i in s, ψ i = ∏ i in s,
 ⇑(ψ i)
参数：s : Finset ι；ψ : ι -> AddChar A M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
-/
lemma coe_prod (s : Finset ι) (ψ : ι → AddChar A M) : ∏ i ∈ s, ψ i = ∏ i ∈ s, ⇑(ψ i) := by
  induction s using Finset.cons_induction <;> simp [*]

@[simp, norm_cast]
/-
**AddChar.coe_sum** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：coe_sum (s : Finset ι) (ψ : ι -> AddChar A M) : ∑ i in s, ψ i = ∏ i in s, 
⇑(ψ i)
参数：s : Finset ι；ψ : ι -> AddChar A M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
-/
lemma coe_sum (s : Finset ι) (ψ : ι → AddChar A M) : ∑ i ∈ s, ψ i = ∏ i ∈ s, ⇑(ψ i) := by
  induction s using Finset.cons_induction <;> simp [*]
/-
**AddChar.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_2} {M : Type u_3} [inst : AddMonoid A] [inst_1 : CommMonoid 
M] (ψ φ : AddChar A M) (a : A),   (ψ * φ) a = ψ a * φ a
参数：ψ φ : AddChar A M；a : A；ψ * φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mul_apply (ψ φ : AddChar A M) (a : A) : (ψ * φ) a = ψ a * φ a := rfl
/-
**AddChar.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_2} {M : Type u_3} [inst : AddMonoid A] [inst_1 : CommMonoid 
M] (ψ φ : AddChar A M) (a : A),   (ψ + φ) a = ψ a * φ a
参数：ψ φ : AddChar A M；a : A；ψ + φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma add_apply (ψ φ : AddChar A M) (a : A) : (ψ + φ) a = ψ a * φ a := rfl
/-
**AddChar.pow_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_2} {M : Type u_3} [inst : AddMonoid A] [inst_1 : CommMonoid 
M] (ψ : AddChar A M) (n : ℕ) (a : A),   (ψ ^ n) a = ψ a ^ n
参数：ψ : AddChar A M；n : ℕ；a : A；ψ ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pow_apply (ψ : AddChar A M) (n : ℕ) (a : A) : (ψ ^ n) a = (ψ a) ^ n := rfl
/-
**AddChar.nsmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_2} {M : Type u_3} [inst : AddMonoid A] [inst_1 : CommMonoid 
M] (ψ : AddChar A M) (n : ℕ) (a : A),   (n • ψ) a = ψ a ^ n
参数：ψ : AddChar A M；n : ℕ；a : A；n • ψ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nsmul_apply (ψ : AddChar A M) (n : ℕ) (a : A) : (n • ψ) a = (ψ a) ^ n := rfl
/-
**AddChar.prod_apply** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：prod_apply (s : Finset ι) (ψ : ι -> AddChar A M) (a : A) : (∏ i in s, ψ i)
 a = ∏ i in s, ψ i a
参数：s : Finset ι；ψ : ι -> AddChar A M；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddChar.coe_prod`：coe_prod (s : Finset ι) (ψ : ι -> AddChar A M) : ∏ i i
n s, ψ i = ∏ i in s, ⇑(ψ i)
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
-/
lemma prod_apply (s : Finset ι) (ψ : ι → AddChar A M) (a : A) :
    (∏ i ∈ s, ψ i) a = ∏ i ∈ s, ψ i a := by rw [coe_prod, Finset.prod_apply]
/-
**AddChar.sum_apply** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：sum_apply (s : Finset ι) (ψ : ι -> AddChar A M) (a : A) : (∑ i in s, ψ i) 
a = ∏ i in s, ψ i a
参数：s : Finset ι；ψ : ι -> AddChar A M；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddChar.coe_sum`：coe_sum (s : Finset ι) (ψ : ι -> AddChar A M) : ∑ i in 
s, ψ i = ∏ i in s, ⇑(ψ i)
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
-/
lemma sum_apply (s : Finset ι) (ψ : ι → AddChar A M) (a : A) :
    (∑ i ∈ s, ψ i) a = ∏ i ∈ s, ψ i a := by rw [coe_sum, Finset.prod_apply]
/-
**AddChar.mul_eq_add** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：mul_eq_add (ψ χ : AddChar A M) : ψ * χ = ψ + χ
参数：ψ χ : AddChar A M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_eq_add (ψ χ : AddChar A M) : ψ * χ = ψ + χ := rfl
/-
**AddChar.pow_eq_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：pow_eq_nsmul (ψ : AddChar A M) (n : Nat) : ψ ^ n = n • ψ
参数：ψ : AddChar A M；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_eq_nsmul (ψ : AddChar A M) (n : ℕ) : ψ ^ n = n • ψ := rfl
/-
**AddChar.prod_eq_sum** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：prod_eq_sum (s : Finset ι) (ψ : ι -> AddChar A M) : ∏ i in s, ψ i = ∑ i in
 s, ψ i
参数：s : Finset ι；ψ : ι -> AddChar A M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prod_eq_sum (s : Finset ι) (ψ : ι → AddChar A M) : ∏ i ∈ s, ψ i = ∑ i ∈ s, ψ i := rfl
/-
**AddChar.toMonoidHomEquiv_add** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_2} {M : Type u_3} [inst : AddMonoid A] [inst_1 : CommMonoid 
M] (ψ φ : AddChar A M),   AddChar.toMonoidHomEquiv (ψ + φ) = AddChar.toMonoidHom
Equiv ψ * AddChar.toMonoidHomEquiv φ
参数：ψ φ : AddChar A M；ψ + φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMonoidHomEquiv_add (ψ φ : AddChar A M) :
    toMonoidHomEquiv (ψ + φ) = toMonoidHomEquiv ψ * toMonoidHomEquiv φ := rfl
/-
**AddChar.toMonoidHomEquiv_symm_mul** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_2} {M : Type u_3} [inst : AddMonoid A] [inst_1 : CommMonoid 
M] (ψ φ : Multiplicative A →* M),   AddChar.toMonoidHomEquiv.symm (ψ * φ) = AddC
har.toMonoidHomEquiv.symm ψ + AddChar.toMonoidHomEquiv.symm φ
参数：ψ φ : Multiplicative A →* M；ψ * φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma toMonoidHomEquiv_symm_mul (ψ φ : Multiplicative A →* M) :
    toMonoidHomEquiv.symm (ψ * φ) = toMonoidHomEquiv.symm ψ + toMonoidHomEquiv.symm φ := rfl

/-- The natural equivalence to `(Multiplicative A →* M)` is a monoid isomorphism. -/
/-
**AddChar.toMonoidHomMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：toMonoidHomMulEquiv : AddChar A M ≃* (Multiplicative A ->* M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural equivalence to `(Multiplicative A →* M)` is a monoid isomorphism.
-/
def toMonoidHomMulEquiv : AddChar A M ≃* (Multiplicative A →* M) :=
  { toMonoidHomEquiv with map_mul' := fun φ ψ ↦ by rfl }

/-- Additive characters `A → M` are the same thing as additive homomorphisms from `A` to
`Additive M`. -/
/-
**AddChar.toAddMonoidAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：toAddMonoidAddEquiv : Additive (AddChar A M) ≃+ (A ->+ Additive M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Additive characters `A → M` are the same thing as additive homomorphisms from `A
` to
`Additive M`.
-/
def toAddMonoidAddEquiv : Additive (AddChar A M) ≃+ (A →+ Additive M) :=
  { toAddMonoidHomEquiv with map_add' := fun φ ψ ↦ by rfl }

/-- The double dual embedding. -/
/-
**AddChar.doubleDualEmb** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：doubleDualEmb : A ->+ AddChar (AddChar A M) M where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The double dual embedding.
-/
def doubleDualEmb : A →+ AddChar (AddChar A M) M where
  toFun a := { toFun := fun ψ ↦ ψ a
               map_zero_eq_one' := by simp
               map_add_eq_mul' := by simp }
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [map_add_eq_mul]
/-
**AddChar.doubleDualEmb_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_2} {M : Type u_3} [inst : AddMonoid A] [inst_1 : CommMonoid 
M] (a : A) (ψ : AddChar A M),   (AddChar.doubleDualEmb a) ψ = ψ a
参数：a : A；ψ : AddChar A M；AddChar.doubleDualEmb a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma doubleDualEmb_apply (a : A) (ψ : AddChar A M) : doubleDualEmb a ψ = ψ a := rfl

end toCommMonoid

section CommSemiring
variable {A R : Type*} [AddGroup A] [Fintype A] [CommSemiring R] [IsDomain R]
  {ψ : AddChar A R}

/-
**AddChar.sum_eq_ite** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：sum_eq_ite (ψ : AddChar A R) [Decidable (ψ = 0)] : ∑ a, ψ a = if ψ = 0 the
n ↑(card A) else 0
参数：ψ : AddChar A R；ψ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AddChar.ne_one_iff`：ne_one_iff : ψ != 1 ↔ exists x, ψ x != 1
· 使用定理 `eq_zero_of_mul_eq_self_left`：eq_zero_of_mul_eq_self_left [IsRightCancelM
ulZero M₀] (h₁ : b != 1) (h₂ : b * a = a) : a = 0
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AddChar.map_add_eq_mul`：map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (
x + y) = ψ x * ψ y
-/
lemma sum_eq_ite (ψ : AddChar A R) [Decidable (ψ = 0)] :
    ∑ a, ψ a = if ψ = 0 then ↑(card A) else 0 := by
  split_ifs with h
  · simp [h]
  obtain ⟨x, hx⟩ := ne_one_iff.1 h
  refine eq_zero_of_mul_eq_self_left hx ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addLeft x) _ _ fun y ↦ (map_add_eq_mul ..).symm

variable [CharZero R]
/-
**AddChar.sum_eq_zero_iff_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：sum_eq_zero_iff_ne_zero : ∑ x, ψ x = 0 ↔ ψ != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddChar.sum_eq_ite`：sum_eq_ite (ψ : AddChar A R) [Decidable (ψ = 0)] : ∑
 a, ψ a = if ψ = 0 then ↑(card A) else 0
· 使用定理 `Ne.ite_eq_right_iff`：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a
 b : α}, a ≠ b → ((if P then a else b) = b ↔ ¬P)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Fintype.card_ne_zero`：card_ne_zero [Nonempty α] : card α != 0
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sum_eq_zero_iff_ne_zero : ∑ x, ψ x = 0 ↔ ψ ≠ 0 := by
  rw [sum_eq_ite, Ne.ite_eq_right_iff]; exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
/-
**AddChar.sum_ne_zero_iff_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：sum_ne_zero_iff_eq_zero : ∑ x, ψ x != 0 ↔ ψ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用引理 `AddChar.sum_eq_zero_iff_ne_zero`：sum_eq_zero_iff_ne_zero : ∑ x, ψ x = 0 
↔ ψ != 0
-/
lemma sum_ne_zero_iff_eq_zero : ∑ x, ψ x ≠ 0 ↔ ψ = 0 := sum_eq_zero_iff_ne_zero.not_left

end CommSemiring

/-!
## Additive characters of additive abelian groups
-/
section fromAddCommGroup

variable {A M : Type*} [AddCommGroup A] [CommMonoid M]

/-- The additive characters on a commutative additive group form a commutative group.

Note that the inverse is defined using negation on the domain; we do not assume `M` has an
inversion operation for the definition (but see `AddChar.map_neg_eq_inv` below). -/
/-
**AddChar.instCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `AddChar`。
形式化陈述：instCommGroup : CommGroup (AddChar A M) where inv ψ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive characters on a commutative additive group form a commutative group
.

Note that the inverse is defined using negation on the domain; we do not assume 
`M` has an
inversion operation for the definition (but see `AddChar.map_neg_eq_inv` below).
-/
instance instCommGroup : CommGroup (AddChar A M) where
  inv ψ := ψ.compAddMonoidHom negAddMonoidHom
  inv_mul_cancel ψ := by ext1 x; simp [negAddMonoidHom, ← map_add_eq_mul]

/-- The additive characters on a commutative additive group form a commutative group. -/
/-
**AddChar.** 是 Mathlib 中的一个实例，位于命名空间 `AddChar`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive characters on a commutative additive group form a commutative group
.
-/
instance : AddCommGroup (AddChar A M) := inferInstanceAs <| AddCommGroup (Additive (AddChar A M))
/-
**AddChar.inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_2} [inst : AddCommGroup A] [inst_1 : CommMono
id M] (ψ : AddChar A M) (a : A),   ψ⁻¹ a = ψ (-a)
参数：ψ : AddChar A M；a : A；-a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inv_apply (ψ : AddChar A M) (a : A) : ψ⁻¹ a = ψ (-a) := rfl
/-
**AddChar.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_2} [inst : AddCommGroup A] [inst_1 : CommMono
id M] (ψ : AddChar A M) (a : A),   (-ψ) a = ψ (-a)
参数：ψ : AddChar A M；a : A；-ψ；-a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma neg_apply (ψ : AddChar A M) (a : A) : (-ψ) a = ψ (-a) := rfl
/-
**AddChar.div_apply** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：div_apply (ψ χ : AddChar A M) (a : A) : (ψ / χ) a = ψ a * χ (-a)
参数：ψ χ : AddChar A M；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma div_apply (ψ χ : AddChar A M) (a : A) : (ψ / χ) a = ψ a * χ (-a) := rfl
/-
**AddChar.sub_apply** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：sub_apply (ψ χ : AddChar A M) (a : A) : (ψ - χ) a = ψ a * χ (-a)
参数：ψ χ : AddChar A M；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sub_apply (ψ χ : AddChar A M) (a : A) : (ψ - χ) a = ψ a * χ (-a) := rfl

end fromAddCommGroup

section fromAddGrouptoCommMonoid

/-- The values of an additive character on an additive group are units. -/
/-
**AddChar.val_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：val_isUnit {A M} [AddGroup A] [Monoid M] (φ : AddChar A M) (a : A) : IsUni
t (φ a)
参数：φ : AddChar A M；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用引理 `Group.isUnit`：Group.isUnit [Group α] (a : α) : IsUnit a

--- 原说明 ---
The values of an additive character on an additive group are units.
-/
lemma val_isUnit {A M} [AddGroup A] [Monoid M] (φ : AddChar A M) (a : A) : IsUnit (φ a) :=
  IsUnit.map φ.toMonoidHom <| Group.isUnit (Multiplicative.ofAdd a)

end fromAddGrouptoCommMonoid

section fromAddGrouptoDivisionMonoid

variable {A M : Type*} [AddGroup A] [DivisionMonoid M]

/-- An additive character maps negatives to inverses (when defined) -/
/-
**AddChar.map_neg_eq_inv** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：map_neg_eq_inv (ψ : AddChar A M) (a : A) : ψ (-a) = (ψ a)⁻¹
参数：ψ : AddChar A M；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_inv_of_mul_eq_one_left`：eq_inv_of_mul_eq_one_left (h : a * b = 1) : a
 = b⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An additive character maps negatives to inverses (when defined)
-/
lemma map_neg_eq_inv (ψ : AddChar A M) (a : A) : ψ (-a) = (ψ a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simp only [← map_add_eq_mul, neg_add_cancel, map_zero_eq_one]

/-- An additive character maps integer scalar multiples to integer powers. -/
/-
**AddChar.map_zsmul_eq_zpow** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：map_zsmul_eq_zpow (ψ : AddChar A M) (n : Int) (a : A) : ψ (n • a) = (ψ a) 
^ n
参数：ψ : AddChar A M；n : Int；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_zpow`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [in
st_1 : DivisionMonoid β] (f : α →* β) (g : α) (n : ℤ),   f (g ^ n) = f g ^ n

--- 原说明 ---
An additive character maps integer scalar multiples to integer powers.
-/
lemma map_zsmul_eq_zpow (ψ : AddChar A M) (n : ℤ) (a : A) : ψ (n • a) = (ψ a) ^ n :=
  ψ.toMonoidHom.map_zpow a n

end fromAddGrouptoDivisionMonoid

section fromAddCommGrouptoDivisionCommMonoid
variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

/-
**AddChar.inv_apply'** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：inv_apply' (ψ : AddChar A M) (a : A) : ψ⁻¹ a = (ψ a)⁻¹
参数：ψ : AddChar A M；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddChar.inv_apply`：∀ {A : Type u_1} {M : Type u_2} [inst : AddCommGroup 
A] [inst_1 : CommMonoid M] (ψ : AddChar A M) (a : A),   ψ⁻¹ a = ψ (-a)
· 使用引理 `AddChar.map_neg_eq_inv`：map_neg_eq_inv (ψ : AddChar A M) (a : A) : ψ (-a
) = (ψ a)⁻¹
-/
lemma inv_apply' (ψ : AddChar A M) (a : A) : ψ⁻¹ a = (ψ a)⁻¹ := by rw [inv_apply, map_neg_eq_inv]
/-
**AddChar.neg_apply'** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：neg_apply' (ψ : AddChar A M) (a : A) : (-ψ) a = (ψ a)⁻¹
参数：ψ : AddChar A M；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AddChar.map_neg_eq_inv`：map_neg_eq_inv (ψ : AddChar A M) (a : A) : ψ (-a
) = (ψ a)⁻¹
-/
lemma neg_apply' (ψ : AddChar A M) (a : A) : (-ψ) a = (ψ a)⁻¹ := map_neg_eq_inv _ _
/-
**AddChar.div_apply'** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：div_apply' (ψ χ : AddChar A M) (a : A) : (ψ / χ) a = ψ a / χ a
参数：ψ χ : AddChar A M；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddChar.div_apply`：div_apply (ψ χ : AddChar A M) (a : A) : (ψ / χ) a = ψ
 a * χ (-a)
· 使用引理 `AddChar.map_neg_eq_inv`：map_neg_eq_inv (ψ : AddChar A M) (a : A) : ψ (-a
) = (ψ a)⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
lemma div_apply' (ψ χ : AddChar A M) (a : A) : (ψ / χ) a = ψ a / χ a := by
  rw [div_apply, map_neg_eq_inv, div_eq_mul_inv]
/-
**AddChar.sub_apply'** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：sub_apply' (ψ χ : AddChar A M) (a : A) : (ψ - χ) a = ψ a / χ a
参数：ψ χ : AddChar A M；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddChar.sub_apply`：sub_apply (ψ χ : AddChar A M) (a : A) : (ψ - χ) a = ψ
 a * χ (-a)
· 使用引理 `AddChar.map_neg_eq_inv`：map_neg_eq_inv (ψ : AddChar A M) (a : A) : ψ (-a
) = (ψ a)⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
lemma sub_apply' (ψ χ : AddChar A M) (a : A) : (ψ - χ) a = ψ a / χ a := by
  rw [sub_apply, map_neg_eq_inv, div_eq_mul_inv]
/-
**AddChar.zsmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_2} [inst : AddCommGroup A] [inst_1 : Division
CommMonoid M] (n : ℤ) (ψ : AddChar A M)   (a : A), (n • ψ) a = ψ a ^ n
参数：n : ℤ；ψ : AddChar A M；a : A；n • ψ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `negSucc_zsmul`：negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : Nat) : In
t.negSucc n • a = -((n + 1) • a)
· 使用引理 `AddChar.neg_apply'`：neg_apply' (ψ : AddChar A M) (a : A) : (-ψ) a = (ψ a
)⁻¹
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
-/
@[simp] lemma zsmul_apply (n : ℤ) (ψ : AddChar A M) (a : A) : (n • ψ) a = ψ a ^ n := by
  cases n <;> simp [-neg_apply, neg_apply']
/-
**AddChar.zpow_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M : Type u_2} [inst : AddCommGroup A] [inst_1 : Division
CommMonoid M] (ψ : AddChar A M) (n : ℤ)   (a : A), (ψ ^ n) a = ψ a ^ n
参数：ψ : AddChar A M；n : ℤ；a : A；ψ ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.zsmul_apply`：∀ {A : Type u_1} {M : Type u_2} [inst : AddCommGrou
p A] [inst_1 : DivisionCommMonoid M] (n : ℤ) (ψ : AddChar A M)   (a : A), (n • ψ
) a = ψ a…
-/
@[simp] lemma zpow_apply (ψ : AddChar A M) (n : ℤ) (a : A) : (ψ ^ n) a = ψ a ^ n := zsmul_apply ..
/-
**AddChar.map_sub_eq_div** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：map_sub_eq_div (ψ : AddChar A M) (a b : A) : ψ (a - b) = ψ a / ψ b
参数：ψ : AddChar A M；a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_div`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (g h : α),   f (g / h) = f g / f h
-/
lemma map_sub_eq_div (ψ : AddChar A M) (a b : A) : ψ (a - b) = ψ a / ψ b :=
  ψ.toMonoidHom.map_div _ _
/-
**AddChar.injective_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：injective_iff {ψ : AddChar A M} : Injective ψ ↔ forall ⦃x⦄, ψ x = 1 -> x =
 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MonoidHom.ker_eq_bot_iff`：ker_eq_bot_iff (f : G ->* M) : f.ker = ⊥ ↔ Fun
ction.Injective f
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
-/
lemma injective_iff {ψ : AddChar A M} : Injective ψ ↔ ∀ ⦃x⦄, ψ x = 1 → x = 0 :=
  ψ.toMonoidHom.ker_eq_bot_iff.symm.trans eq_bot_iff

end fromAddCommGrouptoDivisionCommMonoid

section MonoidWithZero
variable {A M₀ : Type*} [AddGroup A] [MonoidWithZero M₀] [Nontrivial M₀]

/-
**AddChar.coe_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {A : Type u_1} {M₀ : Type u_2} [inst : AddGroup A] [inst_1 : MonoidWithZ
ero M₀] [Nontrivial M₀] (ψ : AddChar A M₀),   ⇑ψ ≠ 0
参数：ψ : AddChar A M₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1
-/
@[simp] lemma coe_ne_zero (ψ : AddChar A M₀) : (ψ : A → M₀) ≠ 0 :=
  ne_iff.2 ⟨0, fun h ↦ by simpa only [h, Pi.zero_apply, zero_ne_one] using map_zero_eq_one ψ⟩

end MonoidWithZero

/-!
## Additive characters of rings
-/
section Ring

-- The domain and target of our additive characters. Now we restrict to a ring in the domain.
variable {R M : Type*} [Ring R] [CommMonoid M]

/-- Define the multiplicative shift of an additive character.
This satisfies `mulShift ψ a x = ψ (a * x)`. -/
/-
**AddChar.mulShift** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：mulShift (ψ : AddChar R M) (r : R) : AddChar R M
参数：ψ : AddChar R M；r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define the multiplicative shift of an additive character.
This satisfies `mulShift ψ a x = ψ (a * x)`.
-/
def mulShift (ψ : AddChar R M) (r : R) : AddChar R M :=
  ψ.compAddMonoidHom (AddMonoidHom.mulLeft r)
/-
**AddChar.mulShift_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst_1 : CommMonoid M] {ψ
 : AddChar R M} {r x : R},   (ψ.mulShift r) x = ψ (r * x)
参数：ψ.mulShift r；r * x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mulShift_apply {ψ : AddChar R M} {r : R} {x : R} : mulShift ψ r x = ψ (r * x) :=
  rfl

/-- `ψ⁻¹ = mulShift ψ (-1))`. -/
/-
**AddChar.inv_mulShift** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：inv_mulShift (ψ : AddChar R M) : ψ⁻¹ = mulShift ψ (-1)
参数：ψ : AddChar R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.ext`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_
1 : Monoid M] (f g : AddChar A M),   (∀ (x : A), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddChar.inv_apply`：∀ {A : Type u_1} {M : Type u_2} [inst : AddCommGroup 
A] [inst_1 : CommMonoid M] (ψ : AddChar A M) (a : A),   ψ⁻¹ a = ψ (-a)
· 使用定理 `AddChar.mulShift_apply`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] 
[inst_1 : CommMonoid M] {ψ : AddChar R M} {r x : R},   (ψ.mulShift r) x = ψ (r *
 x)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
`ψ⁻¹ = mulShift ψ (-1))`.
-/
theorem inv_mulShift (ψ : AddChar R M) : ψ⁻¹ = mulShift ψ (-1) := by
  ext
  rw [inv_apply, mulShift_apply, neg_mul, one_mul]

/-- If `n` is a natural number, then `mulShift ψ n x = (ψ x) ^ n`. -/
/-
**AddChar.mulShift_spec'** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：mulShift_spec' (ψ : AddChar R M) (n : Nat) (x : R) : mulShift ψ n x = ψ x 
^ n
参数：ψ : AddChar R M；n : Nat；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddChar.mulShift_apply`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] 
[inst_1 : CommMonoid M] {ψ : AddChar R M} {r x : R},   (ψ.mulShift r) x = ψ (r *
 x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `AddChar.map_nsmul_eq_pow`：map_nsmul_eq_pow (ψ : AddChar A M) (n : Nat) (
x : A) : ψ (n • x) = ψ x ^ n

--- 原说明 ---
If `n` is a natural number, then `mulShift ψ n x = (ψ x) ^ n`.
-/
theorem mulShift_spec' (ψ : AddChar R M) (n : ℕ) (x : R) : mulShift ψ n x = ψ x ^ n := by
  rw [mulShift_apply, ← nsmul_eq_mul, map_nsmul_eq_pow]

/-- If `n` is a natural number, then `ψ ^ n = mulShift ψ n`. -/
/-
**AddChar.pow_mulShift** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：pow_mulShift (ψ : AddChar R M) (n : Nat) : ψ ^ n = mulShift ψ n
参数：ψ : AddChar R M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.ext`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_
1 : Monoid M] (f g : AddChar A M),   (∀ (x : A), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddChar.pow_apply`：∀ {A : Type u_2} {M : Type u_3} [inst : AddMonoid A] 
[inst_1 : CommMonoid M] (ψ : AddChar A M) (n : ℕ) (a : A),   (ψ ^ n) a = ψ a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddChar.mulShift_spec'`：mulShift_spec' (ψ : AddChar R M) (n : Nat) (x : 
R) : mulShift ψ n x = ψ x ^ n

--- 原说明 ---
If `n` is a natural number, then `ψ ^ n = mulShift ψ n`.
-/
theorem pow_mulShift (ψ : AddChar R M) (n : ℕ) : ψ ^ n = mulShift ψ n := by
  ext x
  rw [pow_apply, ← mulShift_spec']

/-- The product of `mulShift ψ r` and `mulShift ψ s` is `mulShift ψ (r + s)`. -/
/-
**AddChar.mulShift_mul** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：mulShift_mul (ψ : AddChar R M) (r s : R) : mulShift ψ r * mulShift ψ s = m
ulShift ψ (r + s)
参数：ψ : AddChar R M；r s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.ext`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_
1 : Monoid M] (f g : AddChar A M),   (∀ (x : A), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddChar.mulShift_apply`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] 
[inst_1 : CommMonoid M] {ψ : AddChar R M} {r x : R},   (ψ.mulShift r) x = ψ (r *
 x)
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用引理 `AddChar.map_add_eq_mul`：map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (
x + y) = ψ x * ψ y

--- 原说明 ---
The product of `mulShift ψ r` and `mulShift ψ s` is `mulShift ψ (r + s)`.
-/
theorem mulShift_mul (ψ : AddChar R M) (r s : R) :
    mulShift ψ r * mulShift ψ s = mulShift ψ (r + s) := by
  ext
  rw [mulShift_apply, right_distrib, map_add_eq_mul]; norm_cast
/-
**AddChar.mulShift_mulShift** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：mulShift_mulShift (ψ : AddChar R M) (r s : R) : mulShift (mulShift ψ r) s 
= mulShift ψ (r * s)
参数：ψ : AddChar R M；r s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.ext`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_
1 : Monoid M] (f g : AddChar A M),   (∀ (x : A), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulShift_mulShift (ψ : AddChar R M) (r s : R) :
    mulShift (mulShift ψ r) s = mulShift ψ (r * s) := by
  ext
  simp only [mulShift_apply, mul_assoc]

/-- `mulShift ψ 0` is the trivial character. -/
@[simp]
/-
**AddChar.mulShift_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：mulShift_zero (ψ : AddChar R M) : mulShift ψ 0 = 1
参数：ψ : AddChar R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.ext`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_
1 : Monoid M] (f g : AddChar A M),   (∀ (x : A), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddChar.mulShift_apply`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] 
[inst_1 : CommMonoid M] {ψ : AddChar R M} {r x : R},   (ψ.mulShift r) x = ψ (r *
 x)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1
· 使用定理 `AddChar.one_apply`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] 
[inst_1 : Monoid M] (a : A), 1 a = 1

--- 原说明 ---
`mulShift ψ 0` is the trivial character.
-/
theorem mulShift_zero (ψ : AddChar R M) : mulShift ψ 0 = 1 := by
  ext; rw [mulShift_apply, zero_mul, map_zero_eq_one, one_apply]

@[simp]
/-
**AddChar.mulShift_one** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：mulShift_one (ψ : AddChar R M) : mulShift ψ 1 = ψ
参数：ψ : AddChar R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.ext`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_
1 : Monoid M] (f g : AddChar A M),   (∀ (x : A), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddChar.mulShift_apply`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] 
[inst_1 : CommMonoid M] {ψ : AddChar R M} {r x : R},   (ψ.mulShift r) x = ψ (r *
 x)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma mulShift_one (ψ : AddChar R M) : mulShift ψ 1 = ψ := by
  ext; rw [mulShift_apply, one_mul]
/-
**AddChar.mulShift_unit_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：mulShift_unit_eq_one_iff (ψ : AddChar R M) {u : R} (hu : IsUnit u) : ψ.mul
Shift u = 1 ↔ ψ = 1
参数：ψ : AddChar R M；hu : IsUnit u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.ext`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_
1 : Monoid M] (f g : AddChar A M),   (∀ (x : A), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
lemma mulShift_unit_eq_one_iff (ψ : AddChar R M) {u : R} (hu : IsUnit u) :
    ψ.mulShift u = 1 ↔ ψ = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · ext1 y
    rw [show y = u * (hu.unit⁻¹ * y) by rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]]
    simpa only [mulShift_apply] using! DFunLike.ext_iff.mp h (hu.unit⁻¹ * y)
  · solve_by_elim

end Ring

end AddChar

