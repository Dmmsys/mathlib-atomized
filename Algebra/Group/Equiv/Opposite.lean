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
/--
Definition of `opMulEquiv` / `opMulEquiv` 的定义

English:
definition opMulEquiv
  signature: : M ≃* Mᵐᵒᵖ where
  body: opEquiv
  map_mul' _ _ := mul_comm ..

@[to_additive (attr := simp, norm_cast)]

中文:
定义 opMulEquiv
  签名: : M ≃* Mᵐᵒᵖ where
  定义体: opEquiv
  map_mul' _ _ := mul_comm ..

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: opEquiv
-/
def opMulEquiv : M ≃* Mᵐᵒᵖ where
  __ := opEquiv
  map_mul' _ _ := mul_comm ..

@[to_additive (attr := simp, norm_cast)]
/--
lemma `coe_opMulEquiv` / 引理 `coe_opMulEquiv`

English:
lemma coe_opMulEquiv
  statement: ⇑opMulEquiv = op (α := M)
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
引理 coe_opMulEquiv
  结论: ⇑opMulEquiv = op (α := M)
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
lemma coe_opMulEquiv : ⇑opMulEquiv = op (α := M) := rfl

@[to_additive (attr := simp, norm_cast)]
/--
lemma `coe_symm_opMulEquiv` / 引理 `coe_symm_opMulEquiv`

English:
lemma coe_symm_opMulEquiv
  statement: ⇑opMulEquiv.symm = unop (α := M)
  proof: rfl

中文:
引理 coe_symm_opMulEquiv
  结论: ⇑opMulEquiv.symm = unop (α := M)
  证明: rfl
-/
lemma coe_symm_opMulEquiv : ⇑opMulEquiv.symm = unop (α := M) := rfl

end MulOpposite

namespace MulOpposite

/-- The function `MulOpposite.op` is an additive equivalence. -/
@[simps! -fullyApplied +simpRhs apply symm_apply]
/--
Definition of `opAddEquiv` / `opAddEquiv` 的定义

English:
definition opAddEquiv
  signature: [Add α]
  body: opEquiv
  map_add' _ _ := rfl

中文:
定义 opAddEquiv
  签名: [加法 α]
  定义体: opEquiv
  map_add' _ _ := rfl

Depends on / 依赖: opEquiv
-/
def opAddEquiv [Add α] : α ≃+ αᵐᵒᵖ where
  toEquiv := opEquiv
  map_add' _ _ := rfl

/--
lemma `opAddEquiv_toEquiv` / 引理 `opAddEquiv_toEquiv`

English:
lemma opAddEquiv_toEquiv
  given: [Add α]
  statement: ((opAddEquiv : α ≃+ αᵐᵒᵖ) : α ≃ αᵐᵒᵖ) = opEquiv
  proof: rfl

中文:
引理 opAddEquiv_toEquiv
  条件: [加法 α]
  结论: ((opAddEquiv : α ≃+ αᵐᵒᵖ) : α ≃ αᵐᵒᵖ) = opEquiv
  证明: rfl

Depends on / 依赖: instMulHomClass
-/
@[simp] lemma opAddEquiv_toEquiv [Add α] : ((opAddEquiv : α ≃+ αᵐᵒᵖ) : α ≃ αᵐᵒᵖ) = opEquiv := rfl

end MulOpposite

namespace AddOpposite

/-- The function `AddOpposite.op` is a multiplicative equivalence. -/
@[simps! -fullyApplied +simpRhs]
/--
Definition of `opMulEquiv` / `opMulEquiv` 的定义

English:
definition opMulEquiv
  signature: [Mul α]
  body: opEquiv
  map_mul' _ _ := rfl

中文:
定义 opMulEquiv
  签名: [乘法 α]
  定义体: opEquiv
  map_mul' _ _ := rfl

Depends on / 依赖: instMonoidHomClass, opEquiv
-/
def opMulEquiv [Mul α] : α ≃* αᵃᵒᵖ where
  toEquiv := opEquiv
  map_mul' _ _ := rfl

/--
lemma `opMulEquiv_toEquiv` / 引理 `opMulEquiv_toEquiv`

English:
lemma opMulEquiv_toEquiv
  given: [Mul α]
  statement: ((opMulEquiv : α ≃* αᵃᵒᵖ) : α ≃ αᵃᵒᵖ) = opEquiv
  proof: rfl

中文:
引理 opMulEquiv_toEquiv
  条件: [乘法 α]
  结论: ((opMulEquiv : α ≃* αᵃᵒᵖ) : α ≃ αᵃᵒᵖ) = opEquiv
  证明: rfl
-/
@[simp] lemma opMulEquiv_toEquiv [Mul α] : ((opMulEquiv : α ≃* αᵃᵒᵖ) : α ≃ αᵃᵒᵖ) = opEquiv := rfl

end AddOpposite

open MulOpposite

/-- Inversion on a group is a `MulEquiv` to the opposite group. When `G` is commutative, there is
`MulEquiv.inv`. -/
@[to_additive (attr := simps! -fullyApplied +simpRhs)
      /-- Negation on an additive group is an `AddEquiv` to the opposite group. When `G`
      is commutative, there is `AddEquiv.inv`. -/]
/--
Definition of `MulEquiv.inv'` / `MulEquiv.inv'` 的定义

English:
definition MulEquiv.inv'
  signature: (G : Type*) [DivisionMonoid G]
  body: { (Equiv.inv G).trans opEquiv with map_mul' x y := unop_injective <| mul_inv_rev x y }

中文:
定义 乘法等价.inv'
  签名: (G : 类型) [Division幺半群 G]
  定义体: { (Equiv.inv G).trans opEquiv with map_mul' x y := unop_injective <| mul_inv_rev x y }

Depends on / 依赖: Equiv.inv, map_mul, mul_inv_rev, opEquiv, unop_injective
-/
def MulEquiv.inv' (G : Type*) [DivisionMonoid G] : G ≃* Gᵐᵒᵖ :=
  { (Equiv.inv G).trans opEquiv with map_mul' x y := unop_injective <| mul_inv_rev x y }

/-- A semigroup homomorphism `f : M →ₙ* N` such that `f x` commutes with `f y` for all `x, y`
defines a semigroup homomorphism to `Nᵐᵒᵖ`. -/
@[to_additive (attr := simps -fullyApplied)
/-- An additive semigroup homomorphism `f : AddHom M N` such that `f x` additively
commutes with `f y` for all `x, y` defines an additive semigroup homomorphism to `Sᵃᵒᵖ`. -/]
/--
Definition of `MulHom.toOpposite` / `MulHom.toOpposite` 的定义

English:
definition MulHom.toOpposite
  signature: {M N : Type*} [Mul M] [Mul N] (f : M ->ₙ* N)
  body: op ∘ f
  map_mul' x y := by simp [(hf x y).eq]

中文:
定义 乘法半群态射.toOpposite
  签名: {M N : 类型} [乘法 M] [乘法 N] (f : M ->ₙ* N)
  定义体: op ∘ f
  map_mul' x y := by simp [(hf x y).eq]
-/
def MulHom.toOpposite {M N : Type*} [Mul M] [Mul N] (f : M ->ₙ* N)
    (hf : forall x y, Commute (f x) (f y)) : M ->ₙ* Nᵐᵒᵖ where
  toFun := op ∘ f
  map_mul' x y := by simp [(hf x y).eq]

/-- A semigroup homomorphism `f : M →ₙ* N` such that `f x` commutes with `f y` for all `x, y`
defines a semigroup homomorphism from `Mᵐᵒᵖ`. -/
@[to_additive (attr := simps -fullyApplied)
/-- An additive semigroup homomorphism `f : AddHom M N` such that `f x` additively
commutes with `f y` for all `x`, `y` defines an additive semigroup homomorphism from `Mᵃᵒᵖ`. -/]
/--
Definition of `MulHom.fromOpposite` / `MulHom.fromOpposite` 的定义

English:
definition MulHom.fromOpposite
  signature: {M N : Type*} [Mul M] [Mul N] (f : M ->ₙ* N)
  body: f ∘ MulOpposite.unop
  map_mul' _ _ := (f.map_mul _ _).trans (hf _ _).eq

中文:
定义 乘法半群态射.fromOpposite
  签名: {M N : 类型} [乘法 M] [乘法 N] (f : M ->ₙ* N)
  定义体: f ∘ MulOpposite.unop
  map_mul' _ _ := (f.map_mul _ _).trans (hf _ _).eq

Depends on / 依赖: MulOpposite, MulOpposite.unop
-/
def MulHom.fromOpposite {M N : Type*} [Mul M] [Mul N] (f : M ->ₙ* N)
    (hf : forall x y, Commute (f x) (f y)) : Mᵐᵒᵖ ->ₙ* N where
  toFun := f ∘ MulOpposite.unop
  map_mul' _ _ := (f.map_mul _ _).trans (hf _ _).eq

/-- A monoid homomorphism `f : M →* N` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism to `Nᵐᵒᵖ`. -/
@[to_additive (attr := simps -fullyApplied)
/-- An additive monoid homomorphism `f : M →+ N` such that `f x` additively commutes
with `f y` for all `x, y` defines an additive monoid homomorphism to `Sᵃᵒᵖ`. -/]
/--
Definition of `MonoidHom.toOpposite` / `MonoidHom.toOpposite` 的定义

English:
definition MonoidHom.toOpposite
  signature: {M N : Type*} [MulOneClass M] [MulOneClass N] (f : M ->* N)
  body: op ∘ f
  map_one' := congrArg op f.map_one
  map_mul' x y := by simp [(hf x y).eq]

中文:
定义 幺半群态射.toOpposite
  签名: {M N : 类型} [MulOne类 M] [MulOne类 N] (f : M ->* N)
  定义体: op ∘ f
  map_one' := congrArg op f.map_one
  map_mul' x y := by simp [(hf x y).eq]
-/
def MonoidHom.toOpposite {M N : Type*} [MulOneClass M] [MulOneClass N] (f : M ->* N)
    (hf : forall x y, Commute (f x) (f y)) : M ->* Nᵐᵒᵖ where
  toFun := op ∘ f
  map_one' := congrArg op f.map_one
  map_mul' x y := by simp [(hf x y).eq]

/-- A monoid homomorphism `f : M →* N` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism from `Mᵐᵒᵖ`. -/
@[to_additive (attr := simps -fullyApplied)
/-- An additive monoid homomorphism `f : M →+ N` such that `f x` additively commutes
with `f y` for all `x`, `y` defines an additive monoid homomorphism from `Mᵃᵒᵖ`. -/]
/--
Definition of `MonoidHom.fromOpposite` / `MonoidHom.fromOpposite` 的定义

English:
definition MonoidHom.fromOpposite
  signature: {M N : Type*} [MulOneClass M] [MulOneClass N] (f : M ->* N)
  body: f ∘ MulOpposite.unop
  map_one' := f.map_one
  map_mul' _ _ := (f.map_mul _ _).trans (hf _ _).eq

中文:
定义 幺半群态射.fromOpposite
  签名: {M N : 类型} [MulOne类 M] [MulOne类 N] (f : M ->* N)
  定义体: f ∘ MulOpposite.unop
  map_one' := f.map_one
  map_mul' _ _ := (f.map_mul _ _).trans (hf _ _).eq

Depends on / 依赖: MulOpposite, MulOpposite.unop
-/
def MonoidHom.fromOpposite {M N : Type*} [MulOneClass M] [MulOneClass N] (f : M ->* N)
    (hf : forall x y, Commute (f x) (f y)) : Mᵐᵒᵖ ->* N where
  toFun := f ∘ MulOpposite.unop
  map_one' := f.map_one
  map_mul' _ _ := (f.map_mul _ _).trans (hf _ _).eq

/-- A semigroup homomorphism `M →ₙ* N` can equivalently be viewed as a semigroup homomorphism
`Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[to_additive (attr := simps)
/-- An additive semigroup homomorphism `AddHom M N` can equivalently be viewed as an additive
semigroup homomorphism `AddHom Mᵃᵒᵖ Nᵃᵒᵖ`. This is the action of the (fully faithful)`ᵃᵒᵖ`-functor
on morphisms. -/]
/--
Definition of `MulHom.op` / `MulHom.op` 的定义

English:
definition MulHom.op
  signature: {M N} [Mul M] [Mul N]
  body: { toFun := MulOpposite.op ∘ f ∘ unop,
      map_mul' x y := unop_injective (f.map_mul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ MulOpposite.op,
      map_mul' x y := congrArg unop (f.map_mul (MulOpposite.op y) (MulOpposite.op x)) }

中文:
定义 乘法半群态射.op
  签名: {M N} [乘法 M] [乘法 N]
  定义体: { toFun := MulOpposite.op ∘ f ∘ unop,
      map_mul' x y := unop_injective (f.map_mul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ MulOpposite.op,
      map_mul' x y := congrArg unop (f.map_mul (MulOpposite.op y) (MulOpposite.op x)) }

Depends on / 依赖: MulOpposite, MulOpposite.op, f.map_mul, invFun, map_mul, unop_injective, x.unop, y.unop
-/
def MulHom.op {M N} [Mul M] [Mul N] : (M ->ₙ* N) ≃ (Mᵐᵒᵖ ->ₙ* Nᵐᵒᵖ) where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ unop,
      map_mul' x y := unop_injective (f.map_mul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ MulOpposite.op,
      map_mul' x y := congrArg unop (f.map_mul (MulOpposite.op y) (MulOpposite.op x)) }

/-- The 'unopposite' of a semigroup homomorphism `Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ`. Inverse to `MulHom.op`. -/
@[to_additive (attr := simp) /-- The 'unopposite' of an additive semigroup homomorphism
`Mᵃᵒᵖ →ₙ+ Nᵃᵒᵖ`. Inverse to `AddHom.op`. -/]
/--
Definition of `MulHom.unop` / `MulHom.unop` 的定义

English:
definition MulHom.unop
  signature: {M N} [Mul M] [Mul N]
  body: MulHom.op.symm

中文:
定义 乘法半群态射.unop
  签名: {M N} [乘法 M] [乘法 N]
  定义体: MulHom.op.symm

Depends on / 依赖: MulHom, MulHom.op.symm
-/
def MulHom.unop {M N} [Mul M] [Mul N] : (Mᵐᵒᵖ ->ₙ* Nᵐᵒᵖ) ≃ (M ->ₙ* N) :=
  MulHom.op.symm

/-- An additive semigroup homomorphism `AddHom M N` can equivalently be viewed as an additive
homomorphism `AddHom Mᵐᵒᵖ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on
morphisms. -/
@[simps]
/--
Definition of `AddHom.mulOp` / `AddHom.mulOp` 的定义

English:
definition AddHom.mulOp
  signature: {M N} [Add M] [Add N]
  body: { toFun := MulOpposite.op ∘ f ∘ MulOpposite.unop,
      map_add' x y := unop_injective (f.map_add x.unop y.unop) }
  invFun f :=
    { toFun := MulOpposite.unop ∘ f ∘ MulOpposite.op,
      map_add' :=
        fun x y => congrArg MulOpposite.unop (f.map_add (MulOpposite.op x) (MulOpposite.op y)) }

中文:
定义 加法半群态射.mulOp
  签名: {M N} [加法 M] [加法 N]
  定义体: { toFun := MulOpposite.op ∘ f ∘ MulOpposite.unop,
      map_add' x y := unop_injective (f.map_add x.unop y.unop) }
  invFun f :=
    { toFun := MulOpposite.unop ∘ f ∘ MulOpposite.op,
      map_add' :=
        fun x y => congrArg MulOpposite.unop (f.map_add (MulOpposite.op x) (MulOpposite.op y)) }

Depends on / 依赖: MulOpposite, MulOpposite.op, MulOpposite.unop, f.map_add, invFun, map_add, unop_injective, x.unop, y.unop
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
/--
Definition of `AddHom.mulUnop` / `AddHom.mulUnop` 的定义

English:
definition AddHom.mulUnop
  signature: {α β} [Add α] [Add β]
  body: AddHom.mulOp.symm

中文:
定义 加法半群态射.mulUnop
  签名: {α β} [加法 α] [加法 β]
  定义体: AddHom.mulOp.symm

Depends on / 依赖: AddHom, AddHom.mulOp.symm
-/
def AddHom.mulUnop {α β} [Add α] [Add β] : AddHom αᵐᵒᵖ βᵐᵒᵖ ≃ AddHom α β :=
  AddHom.mulOp.symm

/-- A monoid homomorphism `M →* N` can equivalently be viewed as a monoid homomorphism
`Mᵐᵒᵖ →* Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[to_additive (attr := simps)
/-- An additive monoid homomorphism `M →+ N` can equivalently be viewed as an additive monoid
homomorphism `Mᵃᵒᵖ →+ Nᵃᵒᵖ`. This is the action of the (fully faithful)
`ᵃᵒᵖ`-functor on morphisms. -/]
/--
Definition of `MonoidHom.op` / `MonoidHom.op` 的定义

English:
definition MonoidHom.op
  signature: {M N} [MulOneClass M] [MulOneClass N]
  body: { toFun := MulOpposite.op ∘ f ∘ unop, map_one' := congrArg MulOpposite.op f.map_one,
      map_mul' x y := unop_injective (f.map_mul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ MulOpposite.op, map_one' := congrArg unop f.map_one,
      map_mul' x y := congrArg unop (f.map_mul (MulOpposi

中文:
定义 幺半群态射.op
  签名: {M N} [MulOne类 M] [MulOne类 N]
  定义体: { toFun := MulOpposite.op ∘ f ∘ unop, map_one' := congrArg MulOpposite.op f.map_one,
      map_mul' x y := unop_injective (f.map_mul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ MulOpposite.op, map_one' := congrArg unop f.map_one,
      map_mul' x y := congrArg unop (f.map_mul (MulOpposi

Depends on / 依赖: MulOpposite, MulOpposite.op, f.map_mul, f.map_one, invFun, map_mul, map_one, unop_injective, x.unop, y.unop
-/
def MonoidHom.op {M N} [MulOneClass M] [MulOneClass N] : (M ->* N) ≃ (Mᵐᵒᵖ ->* Nᵐᵒᵖ) where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ unop, map_one' := congrArg MulOpposite.op f.map_one,
      map_mul' x y := unop_injective (f.map_mul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ MulOpposite.op, map_one' := congrArg unop f.map_one,
      map_mul' x y := congrArg unop (f.map_mul (MulOpposite.op y) (MulOpposite.op x)) }

/-- The 'unopposite' of a monoid homomorphism `Mᵐᵒᵖ →* Nᵐᵒᵖ`. Inverse to `MonoidHom.op`. -/
@[to_additive (attr := simp) /-- The 'unopposite' of an additive monoid homomorphism
`Mᵃᵒᵖ →+ Nᵃᵒᵖ`. Inverse to `AddMonoidHom.op`. -/]
/--
Definition of `MonoidHom.unop` / `MonoidHom.unop` 的定义

English:
definition MonoidHom.unop
  signature: {M N} [MulOneClass M] [MulOneClass N]
  body: MonoidHom.op.symm

中文:
定义 幺半群态射.unop
  签名: {M N} [MulOne类 M] [MulOne类 N]
  定义体: MonoidHom.op.symm

Depends on / 依赖: MonoidHom, MonoidHom.op.symm
-/
def MonoidHom.unop {M N} [MulOneClass M] [MulOneClass N] : (Mᵐᵒᵖ ->* Nᵐᵒᵖ) ≃ (M ->* N) :=
  MonoidHom.op.symm

/-- A monoid is isomorphic to the opposite of its opposite. -/
@[to_additive (attr := simps!)
      /-- An additive monoid is isomorphic to the opposite of its opposite. -/]
/--
Definition of `MulEquiv.opOp` / `MulEquiv.opOp` 的定义

English:
definition MulEquiv.opOp
  signature: (M : Type*) [Mul M]
  body: MulOpposite.opEquiv.trans MulOpposite.opEquiv
  map_mul' _ _ := rfl

中文:
定义 乘法等价.opOp
  签名: (M : 类型) [乘法 M]
  定义体: MulOpposite.opEquiv.trans MulOpposite.opEquiv
  map_mul' _ _ := rfl

Depends on / 依赖: MulOpposite, MulOpposite.opEquiv, MulOpposite.opEquiv.trans, opEquiv
-/
def MulEquiv.opOp (M : Type*) [Mul M] : M ≃* Mᵐᵒᵖᵐᵒᵖ where
  __ := MulOpposite.opEquiv.trans MulOpposite.opEquiv
  map_mul' _ _ := rfl

/-- An additive homomorphism `M →+ N` can equivalently be viewed as an additive homomorphism
`Mᵐᵒᵖ →+ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
/--
Definition of `AddMonoidHom.mulOp` / `AddMonoidHom.mulOp` 的定义

English:
definition AddMonoidHom.mulOp
  signature: {M N} [AddZeroClass M] [AddZeroClass N]
  body: { toFun := MulOpposite.op ∘ f ∘ MulOpposite.unop, map_zero' := unop_injective f.map_zero,
      map_add' x y := unop_injective (f.map_add x.unop y.unop) }
  invFun f :=
    { toFun := MulOpposite.unop ∘ f ∘ MulOpposite.op,
      map_zero' := congrArg MulOpposite.unop f.map_zero,
      map_add' :=
  

中文:
定义 加法幺半群态射.mulOp
  签名: {M N} [加法零类 M] [加法零类 N]
  定义体: { toFun := MulOpposite.op ∘ f ∘ MulOpposite.unop, map_zero' := unop_injective f.map_zero,
      map_add' x y := unop_injective (f.map_add x.unop y.unop) }
  invFun f :=
    { toFun := MulOpposite.unop ∘ f ∘ MulOpposite.op,
      map_zero' := congrArg MulOpposite.unop f.map_zero,
      map_add' :=
  

Depends on / 依赖: MulOpposite, MulOpposite.op, MulOpposite.unop, f.map_add, f.map_zero, invFun, map_add, map_zero, unop_injective, x.unop, y.unop
-/
def AddMonoidHom.mulOp {M N} [AddZeroClass M] [AddZeroClass N] : (M ->+ N) ≃ (Mᵐᵒᵖ ->+ Nᵐᵒᵖ) where
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
/--
Definition of `AddMonoidHom.mulUnop` / `AddMonoidHom.mulUnop` 的定义

English:
definition AddMonoidHom.mulUnop
  signature: {α β} [AddZeroClass α] [AddZeroClass β]
  body: AddMonoidHom.mulOp.symm

中文:
定义 加法幺半群态射.mulUnop
  签名: {α β} [加法零类 α] [加法零类 β]
  定义体: AddMonoidHom.mulOp.symm

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulOp.symm
-/
def AddMonoidHom.mulUnop {α β} [AddZeroClass α] [AddZeroClass β] : (αᵐᵒᵖ ->+ βᵐᵒᵖ) ≃ (α ->+ β) :=
  AddMonoidHom.mulOp.symm

/-- An iso `α ≃+ β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. -/
@[simps]
/--
Definition of `AddEquiv.mulOp` / `AddEquiv.mulOp` 的定义

English:
definition AddEquiv.mulOp
  signature: {α β} [Add α] [Add β]
  body: opAddEquiv.symm.trans (f.trans opAddEquiv)
  invFun f := opAddEquiv.trans (f.trans opAddEquiv.symm)

中文:
定义 加法等价.mulOp
  签名: {α β} [加法 α] [加法 β]
  定义体: opAddEquiv.symm.trans (f.trans opAddEquiv)
  invFun f := opAddEquiv.trans (f.trans opAddEquiv.symm)

Depends on / 依赖: f.trans, opAddEquiv, opAddEquiv.symm.trans
-/
def AddEquiv.mulOp {α β} [Add α] [Add β] : α ≃+ β ≃ (αᵐᵒᵖ ≃+ βᵐᵒᵖ) where
  toFun f := opAddEquiv.symm.trans (f.trans opAddEquiv)
  invFun f := opAddEquiv.trans (f.trans opAddEquiv.symm)

/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. Inverse to `AddEquiv.mul_op`. -/
@[simp]
/--
Definition of `AddEquiv.mulUnop` / `AddEquiv.mulUnop` 的定义

English:
definition AddEquiv.mulUnop
  signature: {α β} [Add α] [Add β]
  body: AddEquiv.mulOp.symm

中文:
定义 加法等价.mulUnop
  签名: {α β} [加法 α] [加法 β]
  定义体: AddEquiv.mulOp.symm

Depends on / 依赖: AddEquiv, AddEquiv.mulOp.symm
-/
def AddEquiv.mulUnop {α β} [Add α] [Add β] : αᵐᵒᵖ ≃+ βᵐᵒᵖ ≃ (α ≃+ β) :=
  AddEquiv.mulOp.symm

/-- An iso `α ≃* β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃* βᵐᵒᵖ`. -/
@[to_additive (attr := simps)
  /-- An iso `α ≃+ β` can equivalently be viewed as an iso `αᵃᵒᵖ ≃+ βᵃᵒᵖ`. -/]
/--
Definition of `MulEquiv.op` / `MulEquiv.op` 的定义

English:
definition MulEquiv.op
  signature: {α β} [Mul α] [Mul β]
  body: { toFun := MulOpposite.op ∘ f ∘ unop, invFun := MulOpposite.op ∘ f.symm ∘ unop,
      left_inv x := unop_injective (f.symm_apply_apply x.unop),
      right_inv x := unop_injective (f.apply_symm_apply x.unop),
      map_mul' x y := unop_injective (map_mul f y.unop x.unop) }
  invFun f :=
    { toFun 

中文:
定义 乘法等价.op
  签名: {α β} [乘法 α] [乘法 β]
  定义体: { toFun := MulOpposite.op ∘ f ∘ unop, invFun := MulOpposite.op ∘ f.symm ∘ unop,
      left_inv x := unop_injective (f.symm_apply_apply x.unop),
      right_inv x := unop_injective (f.apply_symm_apply x.unop),
      map_mul' x y := unop_injective (map_mul f y.unop x.unop) }
  invFun f :=
    { toFun 

Depends on / 依赖: MulOpposite, MulOpposite.op, apply_symm_apply, congr_arg, f.apply_symm_apply, f.symm, f.symm_apply_apply, invFun, left_inv, map_mul, right_inv, symm_apply_apply, unop_injective, x.unop, y.unop
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
/--
Definition of `MulEquiv.unop` / `MulEquiv.unop` 的定义

English:
definition MulEquiv.unop
  signature: {α β} [Mul α] [Mul β]
  body: MulEquiv.op.symm

中文:
定义 乘法等价.unop
  签名: {α β} [乘法 α] [乘法 β]
  定义体: MulEquiv.op.symm

Depends on / 依赖: MulEquiv, MulEquiv.op.symm
-/
def MulEquiv.unop {α β} [Mul α] [Mul β] : αᵐᵒᵖ ≃* βᵐᵒᵖ ≃ (α ≃* β) := MulEquiv.op.symm

section Ext

/-- This ext lemma changes equalities on `αᵐᵒᵖ →+ β` to equalities on `α →+ β`.
This is useful because there are often ext lemmas for specific `α`s that will apply
to an equality of `α →+ β` such as `Finsupp.addHom_ext'`. -/
@[ext]
/--
lemma `AddMonoidHom.mul_op_ext` / 引理 `AddMonoidHom.mul_op_ext`

English:
lemma AddMonoidHom.mul_op_ext
  statement: {α β} [AddZeroClass α] [AddZeroClass β] (f g : αᵐᵒᵖ ->+ β)
  proof: AddMonoidHom.ext MulOpposite.rec' fun x => (DFunLike.congr_fun h :) x

中文:
引理 加法幺半群态射.mul_op_ext
  结论: {α β} [加法零类 α] [加法零类 β] (f g : αᵐᵒᵖ ->+ β)
  证明: AddMonoidHom.ext MulOpposite.rec' fun x => (DFunLike.congr_fun h :) x

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, DFunLike, DFunLike.congr_fun, MulOpposite, MulOpposite.rec, congr_fun
-/
lemma AddMonoidHom.mul_op_ext {α β} [AddZeroClass α] [AddZeroClass β] (f g : αᵐᵒᵖ ->+ β)
    (h :
      f.comp (opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom =
        g.comp (opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom) :
    f = g :=
AddMonoidHom.ext MulOpposite.rec' fun x => (DFunLike.congr_fun h :) x

end Ext
