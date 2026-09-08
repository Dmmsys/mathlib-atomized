/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Opposite

/-!
# Group isomorphism between a group and its opposite
-/

@[expose] public section

variable {M α : Type*}

namespace MulOpposite
variable [CommMonoid M]

/-- `MulOpposite.op` on a commutative monoid is an isomorphism. -/
@[to_additive (attr := simps!)
/-- `AddOpposite.op` on a commutative additive monoid is an isomorphism. -/]
/-
**MulOpposite.opMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：opMulEquiv : M ≃* Mᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def opMulEquiv : M ≃* Mᵐᵒᵖ where
  __ := opEquiv
  map_mul' _ _ := mul_comm ..

@[to_additive (attr := simp, norm_cast)]
/-
**MulOpposite.coe_opMulEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：coe_opMulEquiv : ⇑opMulEquiv = op (α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_opMulEquiv : ⇑opMulEquiv = op (α := M) := rfl

@[to_additive (attr := simp, norm_cast)]
/-
**MulOpposite.coe_symm_opMulEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：coe_symm_opMulEquiv : ⇑opMulEquiv.symm = unop (α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_symm_opMulEquiv : ⇑opMulEquiv.symm = unop (α := M) := rfl

end MulOpposite

namespace MulOpposite

/-- The function `MulOpposite.op` is an additive equivalence. -/
@[simps! -fullyApplied +simpRhs apply symm_apply]
/-
**MulOpposite.opAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：opAddEquiv [Add α] : α ≃+ αᵐᵒᵖ where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `MulOpposite.op` is an additive equivalence.
-/
def opAddEquiv [Add α] : α ≃+ αᵐᵒᵖ where
  toEquiv := opEquiv
  map_add' _ _ := rfl
/-
**MulOpposite.opAddEquiv_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_2} [inst : Add α], ↑MulOpposite.opAddEquiv = MulOpposite.opE
quiv
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma opAddEquiv_toEquiv [Add α] : ((opAddEquiv : α ≃+ αᵐᵒᵖ) : α ≃ αᵐᵒᵖ) = opEquiv := rfl

end MulOpposite

namespace AddOpposite

/-- The function `AddOpposite.op` is a multiplicative equivalence. -/
@[simps! -fullyApplied +simpRhs]
/-
**AddOpposite.opMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddOpposite`。
形式化陈述：opMulEquiv [Mul α] : α ≃* αᵃᵒᵖ where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `AddOpposite.op` is a multiplicative equivalence.
-/
def opMulEquiv [Mul α] : α ≃* αᵃᵒᵖ where
  toEquiv := opEquiv
  map_mul' _ _ := rfl
/-
**AddOpposite.opMulEquiv_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {α : Type u_2} [inst : Mul α], ↑AddOpposite.opMulEquiv = AddOpposite.opE
quiv
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma opMulEquiv_toEquiv [Mul α] : ((opMulEquiv : α ≃* αᵃᵒᵖ) : α ≃ αᵃᵒᵖ) = opEquiv := rfl

end AddOpposite

open MulOpposite

/-- Inversion on a group is a `MulEquiv` to the opposite group. When `G` is commutative, there is
`MulEquiv.inv`. -/
@[to_additive (attr := simps! -fullyApplied +simpRhs)
      /-- Negation on an additive group is an `AddEquiv` to the opposite group. When `G`
      is commutative, there is `AddEquiv.inv`. -/]
/-
**MulEquiv.inv'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.inv' (G : Type*) [DivisionMonoid G] : G ≃* Gᵐᵒᵖ
参数：G : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
def MulEquiv.inv' (G : Type*) [DivisionMonoid G] : G ≃* Gᵐᵒᵖ :=
  { (Equiv.inv G).trans opEquiv with map_mul' x y := unop_injective <| mul_inv_rev x y }

/-- A semigroup homomorphism `f : M →ₙ* N` such that `f x` commutes with `f y` for all `x, y`
defines a semigroup homomorphism to `Nᵐᵒᵖ`. -/
@[to_additive (attr := simps -fullyApplied)
/-- An additive semigroup homomorphism `f : AddHom M N` such that `f x` additively
commutes with `f y` for all `x, y` defines an additive semigroup homomorphism to `Sᵃᵒᵖ`. -/]
/-
**MulHom.toOpposite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulHom.toOpposite {M N : Type*} [Mul M] [Mul N] (f : M ->ₙ* N) (hf : foral
l x y, Commute (f x) (f y)) : M ->ₙ* Nᵐᵒᵖ where toFun
参数：f : M ->ₙ* N；hf : forall x y, Commute (f x) (f y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulHom.toOpposite {M N : Type*} [Mul M] [Mul N] (f : M →ₙ* N)
    (hf : ∀ x y, Commute (f x) (f y)) : M →ₙ* Nᵐᵒᵖ where
  toFun := op ∘ f
  map_mul' x y := by simp [(hf x y).eq]

/-- A semigroup homomorphism `f : M →ₙ* N` such that `f x` commutes with `f y` for all `x, y`
defines a semigroup homomorphism from `Mᵐᵒᵖ`. -/
@[to_additive (attr := simps -fullyApplied)
/-- An additive semigroup homomorphism `f : AddHom M N` such that `f x` additively
commutes with `f y` for all `x`, `y` defines an additive semigroup homomorphism from `Mᵃᵒᵖ`. -/]
/-
**MulHom.fromOpposite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulHom.fromOpposite {M N : Type*} [Mul M] [Mul N] (f : M ->ₙ* N) (hf : for
all x y, Commute (f x) (f y)) : Mᵐᵒᵖ ->ₙ* N where toFun
参数：f : M ->ₙ* N；hf : forall x y, Commute (f x) (f y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulHom.fromOpposite {M N : Type*} [Mul M] [Mul N] (f : M →ₙ* N)
    (hf : ∀ x y, Commute (f x) (f y)) : Mᵐᵒᵖ →ₙ* N where
  toFun := f ∘ MulOpposite.unop
  map_mul' _ _ := (f.map_mul _ _).trans (hf _ _).eq

/-- A monoid homomorphism `f : M →* N` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism to `Nᵐᵒᵖ`. -/
@[to_additive (attr := simps -fullyApplied)
/-- An additive monoid homomorphism `f : M →+ N` such that `f x` additively commutes
with `f y` for all `x, y` defines an additive monoid homomorphism to `Sᵃᵒᵖ`. -/]
/-
**MonoidHom.toOpposite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.toOpposite {M N : Type*} [MulOneClass M] [MulOneClass N] (f : M 
->* N) (hf : forall x y, Commute (f x) (f y)) : M ->* Nᵐᵒᵖ where toFun
参数：f : M ->* N；hf : forall x y, Commute (f x) (f y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MonoidHom.toOpposite {M N : Type*} [MulOneClass M] [MulOneClass N] (f : M →* N)
    (hf : ∀ x y, Commute (f x) (f y)) : M →* Nᵐᵒᵖ where
  toFun := op ∘ f
  map_one' := congrArg op f.map_one
  map_mul' x y := by simp [(hf x y).eq]

/-- A monoid homomorphism `f : M →* N` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism from `Mᵐᵒᵖ`. -/
@[to_additive (attr := simps -fullyApplied)
/-- An additive monoid homomorphism `f : M →+ N` such that `f x` additively commutes
with `f y` for all `x`, `y` defines an additive monoid homomorphism from `Mᵃᵒᵖ`. -/]
/-
**MonoidHom.fromOpposite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.fromOpposite {M N : Type*} [MulOneClass M] [MulOneClass N] (f : 
M ->* N) (hf : forall x y, Commute (f x) (f y)) : Mᵐᵒᵖ ->* N where toFun
参数：f : M ->* N；hf : forall x y, Commute (f x) (f y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MonoidHom.fromOpposite {M N : Type*} [MulOneClass M] [MulOneClass N] (f : M →* N)
    (hf : ∀ x y, Commute (f x) (f y)) : Mᵐᵒᵖ →* N where
  toFun := f ∘ MulOpposite.unop
  map_one' := f.map_one
  map_mul' _ _ := (f.map_mul _ _).trans (hf _ _).eq

/-- A semigroup homomorphism `M →ₙ* N` can equivalently be viewed as a semigroup homomorphism
`Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[to_additive (attr := simps)
/-- An additive semigroup homomorphism `AddHom M N` can equivalently be viewed as an additive
semigroup homomorphism `AddHom Mᵃᵒᵖ Nᵃᵒᵖ`. This is the action of the (fully faithful)`ᵃᵒᵖ`-functor
on morphisms. -/]
/-
**MulHom.op** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulHom.op {M N} [Mul M] [Mul N] : (M ->ₙ* N) ≃ (Mᵐᵒᵖ ->ₙ* Nᵐᵒᵖ) where toFu
n f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulHom.op {M N} [Mul M] [Mul N] : (M →ₙ* N) ≃ (Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ) where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ unop,
      map_mul' x y := unop_injective (f.map_mul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ MulOpposite.op,
      map_mul' x y := congrArg unop (f.map_mul (MulOpposite.op y) (MulOpposite.op x)) }

/-- The 'unopposite' of a semigroup homomorphism `Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ`. Inverse to `MulHom.op`. -/
@[to_additive (attr := simp) /-- The 'unopposite' of an additive semigroup homomorphism
`Mᵃᵒᵖ →ₙ+ Nᵃᵒᵖ`. Inverse to `AddHom.op`. -/]
/-
**MulHom.unop** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulHom.unop {M N} [Mul M] [Mul N] : (Mᵐᵒᵖ ->ₙ* Nᵐᵒᵖ) ≃ (M ->ₙ* N)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def MulHom.unop {M N} [Mul M] [Mul N] : (Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ) ≃ (M →ₙ* N) :=
  MulHom.op.symm

/-- An additive semigroup homomorphism `AddHom M N` can equivalently be viewed as an additive
homomorphism `AddHom Mᵐᵒᵖ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on
morphisms. -/
@[simps]
/-
**AddHom.mulOp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddHom.mulOp {M N} [Add M] [Add N] : AddHom M N ≃ AddHom Mᵐᵒᵖ Nᵐᵒᵖ where t
oFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive semigroup homomorphism `AddHom M N` can equivalently be viewed as an
 additive
homomorphism `AddHom Mᵐᵒᵖ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ
`-functor on
morphisms.
-/
def AddHom.mulOp {M N} [Add M] [Add N] : AddHom M N ≃ AddHom Mᵐᵒᵖ Nᵐᵒᵖ where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ MulOpposite.unop,
      map_add' x y := unop_injective (f.map_add x.unop y.unop) }
  invFun f :=
    { toFun := MulOpposite.unop ∘ f ∘ MulOpposite.op,
      map_add' :=
        fun x y => congrArg MulOpposite.unop (f.map_add (MulOpposite.op x) (MulOpposite.op y)) }

/-- The 'unopposite' of an additive semigroup hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to
`AddHom.mul_op`. -/
@[simp]
/-
**AddHom.mulUnop** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddHom.mulUnop {α β} [Add α] [Add β] : AddHom αᵐᵒᵖ βᵐᵒᵖ ≃ AddHom α β
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The 'unopposite' of an additive semigroup hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to
`AddHom.mul_op`.
-/
def AddHom.mulUnop {α β} [Add α] [Add β] : AddHom αᵐᵒᵖ βᵐᵒᵖ ≃ AddHom α β :=
  AddHom.mulOp.symm

/-- A monoid homomorphism `M →* N` can equivalently be viewed as a monoid homomorphism
`Mᵐᵒᵖ →* Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[to_additive (attr := simps)
/-- An additive monoid homomorphism `M →+ N` can equivalently be viewed as an additive monoid
homomorphism `Mᵃᵒᵖ →+ Nᵃᵒᵖ`. This is the action of the (fully faithful)
`ᵃᵒᵖ`-functor on morphisms. -/]
/-
**MonoidHom.op** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.op {M N} [MulOneClass M] [MulOneClass N] : (M ->* N) ≃ (Mᵐᵒᵖ ->*
 Nᵐᵒᵖ) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MonoidHom.op {M N} [MulOneClass M] [MulOneClass N] : (M →* N) ≃ (Mᵐᵒᵖ →* Nᵐᵒᵖ) where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ unop, map_one' := congrArg MulOpposite.op f.map_one,
      map_mul' x y := unop_injective (f.map_mul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ MulOpposite.op, map_one' := congrArg unop f.map_one,
      map_mul' x y := congrArg unop (f.map_mul (MulOpposite.op y) (MulOpposite.op x)) }

/-- The 'unopposite' of a monoid homomorphism `Mᵐᵒᵖ →* Nᵐᵒᵖ`. Inverse to `MonoidHom.op`. -/
@[to_additive (attr := simp) /-- The 'unopposite' of an additive monoid homomorphism
`Mᵃᵒᵖ →+ Nᵃᵒᵖ`. Inverse to `AddMonoidHom.op`. -/]
/-
**MonoidHom.unop** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.unop {M N} [MulOneClass M] [MulOneClass N] : (Mᵐᵒᵖ ->* Nᵐᵒᵖ) ≃ (
M ->* N)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def MonoidHom.unop {M N} [MulOneClass M] [MulOneClass N] : (Mᵐᵒᵖ →* Nᵐᵒᵖ) ≃ (M →* N) :=
  MonoidHom.op.symm

/-- A monoid is isomorphic to the opposite of its opposite. -/
@[to_additive (attr := simps!)
      /-- An additive monoid is isomorphic to the opposite of its opposite. -/]
/-
**MulEquiv.opOp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.opOp (M : Type*) [Mul M] : M ≃* Mᵐᵒᵖᵐᵒᵖ where __
参数：M : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
def MulEquiv.opOp (M : Type*) [Mul M] : M ≃* Mᵐᵒᵖᵐᵒᵖ where
  __ := MulOpposite.opEquiv.trans MulOpposite.opEquiv
  map_mul' _ _ := rfl

/-- An additive homomorphism `M →+ N` can equivalently be viewed as an additive homomorphism
`Mᵐᵒᵖ →+ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
/-
**AddMonoidHom.mulOp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddMonoidHom.mulOp {M N} [AddZeroClass M] [AddZeroClass N] : (M ->+ N) ≃ (
Mᵐᵒᵖ ->+ Nᵐᵒᵖ) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive homomorphism `M →+ N` can equivalently be viewed as an additive homo
morphism
`Mᵐᵒᵖ →+ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morp
hisms.
-/
def AddMonoidHom.mulOp {M N} [AddZeroClass M] [AddZeroClass N] : (M →+ N) ≃ (Mᵐᵒᵖ →+ Nᵐᵒᵖ) where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ MulOpposite.unop, map_zero' := unop_injective f.map_zero,
      map_add' x y := unop_injective (f.map_add x.unop y.unop) }
  invFun f :=
    { toFun := MulOpposite.unop ∘ f ∘ MulOpposite.op,
      map_zero' := congrArg MulOpposite.unop f.map_zero,
      map_add' :=
        fun x y => congrArg MulOpposite.unop (f.map_add (MulOpposite.op x) (MulOpposite.op y)) }

/-- The 'unopposite' of an additive monoid hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to
`AddMonoidHom.mul_op`. -/
@[simp]
/-
**AddMonoidHom.mulUnop** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddMonoidHom.mulUnop {α β} [AddZeroClass α] [AddZeroClass β] : (αᵐᵒᵖ ->+ β
ᵐᵒᵖ) ≃ (α ->+ β)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The 'unopposite' of an additive monoid hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to
`AddMonoidHom.mul_op`.
-/
def AddMonoidHom.mulUnop {α β} [AddZeroClass α] [AddZeroClass β] : (αᵐᵒᵖ →+ βᵐᵒᵖ) ≃ (α →+ β) :=
  AddMonoidHom.mulOp.symm

/-- An iso `α ≃+ β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. -/
@[simps]
/-
**AddEquiv.mulOp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddEquiv.mulOp {α β} [Add α] [Add β] : α ≃+ β ≃ (αᵐᵒᵖ ≃+ βᵐᵒᵖ) where toFun
 f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An iso `α ≃+ β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`.
-/
def AddEquiv.mulOp {α β} [Add α] [Add β] : α ≃+ β ≃ (αᵐᵒᵖ ≃+ βᵐᵒᵖ) where
  toFun f := opAddEquiv.symm.trans (f.trans opAddEquiv)
  invFun f := opAddEquiv.trans (f.trans opAddEquiv.symm)

/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. Inverse to `AddEquiv.mul_op`. -/
@[simp]
/-
**AddEquiv.mulUnop** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddEquiv.mulUnop {α β} [Add α] [Add β] : αᵐᵒᵖ ≃+ βᵐᵒᵖ ≃ (α ≃+ β)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The 'unopposite' of an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. Inverse to `AddEquiv.mul_op`.
-/
def AddEquiv.mulUnop {α β} [Add α] [Add β] : αᵐᵒᵖ ≃+ βᵐᵒᵖ ≃ (α ≃+ β) :=
  AddEquiv.mulOp.symm

/-- An iso `α ≃* β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃* βᵐᵒᵖ`. -/
@[to_additive (attr := simps)
  /-- An iso `α ≃+ β` can equivalently be viewed as an iso `αᵃᵒᵖ ≃+ βᵃᵒᵖ`. -/]
/-
**MulEquiv.op** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.op {α β} [Mul α] [Mul β] : α ≃* β ≃ (αᵐᵒᵖ ≃* βᵐᵒᵖ) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulEquiv.op {α β} [Mul α] [Mul β] : α ≃* β ≃ (αᵐᵒᵖ ≃* βᵐᵒᵖ) where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ unop, invFun := MulOpposite.op ∘ f.symm ∘ unop,
      left_inv x := unop_injective (f.symm_apply_apply x.unop),
      right_inv x := unop_injective (f.apply_symm_apply x.unop),
      map_mul' x y := unop_injective (map_mul f y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ MulOpposite.op, invFun := unop ∘ f.symm ∘ MulOpposite.op,
      left_inv x := by simp,
      right_inv x := by simp,
      map_mul' x y := congr_arg unop (map_mul f (MulOpposite.op y) (MulOpposite.op x)) }

/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃* βᵐᵒᵖ`. Inverse to `MulEquiv.op`. -/
@[to_additive (attr := simp)
  /-- The 'unopposite' of an iso `αᵃᵒᵖ ≃+ βᵃᵒᵖ`. Inverse to `AddEquiv.op`. -/]
/-
**MulEquiv.unop** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.unop {α β} [Mul α] [Mul β] : αᵐᵒᵖ ≃* βᵐᵒᵖ ≃ (α ≃* β)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def MulEquiv.unop {α β} [Mul α] [Mul β] : αᵐᵒᵖ ≃* βᵐᵒᵖ ≃ (α ≃* β) := MulEquiv.op.symm

section Ext

/-- This ext lemma changes equalities on `αᵐᵒᵖ →+ β` to equalities on `α →+ β`.
This is useful because there are often ext lemmas for specific `α`s that will apply
to an equality of `α →+ β` such as `Finsupp.addHom_ext'`. -/
@[ext]
/-
**AddMonoidHom.mul_op_ext** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddMonoidHom.mul_op_ext {α β} [AddZeroClass α] [AddZeroClass β] (f g : αᵐᵒ
ᵖ ->+ β) (h : f.comp (opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom = g.comp (opAddEqui
v : α ≃+ αᵐᵒᵖ).toAddMonoidHom) : f = g
参数：f g : αᵐᵒᵖ ->+ β；h : f.comp (opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom = g.comp 
(opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
This ext lemma changes equalities on `αᵐᵒᵖ →+ β` to equalities on `α →+ β`.
This is useful because there are often ext lemmas for specific `α`s that will ap
ply
to an equality of `α →+ β` such as `Finsupp.addHom_ext'`.
-/
lemma AddMonoidHom.mul_op_ext {α β} [AddZeroClass α] [AddZeroClass β] (f g : αᵐᵒᵖ →+ β)
    (h :
      f.comp (opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom =
        g.comp (opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom) :
    f = g :=
  AddMonoidHom.ext <| MulOpposite.rec' fun x => (DFunLike.congr_fun h :) x

end Ext

