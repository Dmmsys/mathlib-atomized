/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Extensionality lemmas for monoid and group structures

In this file we prove extensionality lemmas for `Monoid` and higher algebraic structures with one
binary operation. Extensionality lemmas for structures that are lower in the hierarchy can be found
in `Algebra.Group.Defs`.

## Implementation details

To get equality of `npow` etc, we define a monoid homomorphism between two monoid structures on the
same type, then apply lemmas like `MonoidHom.map_div`, `MonoidHom.map_pow` etc.

To refer to the `*` operator of a particular instance `i`, we use
`(letI := i; HMul.hMul : M → M → M)` instead of `i.mul` (which elaborates to `Mul.mul`), as the
former uses `HMul.hMul` which is the canonical spelling.

## Tags
monoid, group, extensionality
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

open Function

universe u

@[to_additive (attr := ext)]
/--
theorem `Monoid.ext` / 定理 `Monoid.ext`

English:
theorem Monoid.ext
  given: {M : Type u} ⦃m₁ m₂
  statement: Monoid M⦄
  proof: by
  have : m₁.toMulOneClass = m₂.toMulOneClass := MulOneClass.ext h_mul
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) this
  let f : @MonoidHom M M m₁.toMulOne m₂.toMulOne :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.n

中文:
定理 幺半群.ext
  条件: {M : 类型u} ⦃m₁ m₂
  结论: 幺半群 M⦄
  证明: by
  have : m₁.toMulOneClass = m₂.toMulOneClass := MulOneClass.ext h_mul
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) this
  let f : @MonoidHom M M m₁.toMulOne m₂.toMulOne :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.n

Depends on / 依赖: HMul.hMul
-/
theorem Monoid.ext {M : Type u} ⦃m₁ m₂ : Monoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M -> M -> M) = (letI := m₂; HMul.hMul : M -> M -> M)) :
    m₁ = m₂ := by
  have : m₁.toMulOneClass = m₂.toMulOneClass := MulOneClass.ext h_mul
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) this
  let f : @MonoidHom M M m₁.toMulOne m₂.toMulOne :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.npow = m₂.npow := by
    ext n x
    exact @MonoidHom.map_pow M M m₁ m₂ f x n
  rcases m₁ with @⟨@⟨⟨_⟩⟩, ⟨_⟩, _, _, ⟨_⟩⟩
  congr

@[to_additive]
/--
theorem `CommMonoid.toMonoid_injective` / 定理 `CommMonoid.toMonoid_injective`

English:
theorem CommMonoid.toMonoid_injective
  given: {M : Type u}
  proof: by
  rintro ⟨⟩ ⟨⟩ h
  congr

@[to_additive (attr := ext)]

中文:
定理 交换幺半群.toMonoid_injective
  条件: {M : 类型u}
  证明: by
  rintro ⟨⟩ ⟨⟩ h
  congr

@[to_additive (attr := ext)]
-/
theorem CommMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@CommMonoid.toMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr

@[to_additive (attr := ext)]
/--
theorem `CommMonoid.ext` / 定理 `CommMonoid.ext`

English:
theorem CommMonoid.ext
  given: {M : Type*} ⦃m₁ m₂
  statement: CommMonoid M⦄
  proof: CommMonoid.toMonoid_injective Monoid.ext h_mul

@[to_additive]

中文:
定理 交换幺半群.ext
  条件: {M : 类型} ⦃m₁ m₂
  结论: 交换幺半群 M⦄
  证明: CommMonoid.toMonoid_injective Monoid.ext h_mul

@[to_additive]

Depends on / 依赖: HMul.hMul
-/
theorem CommMonoid.ext {M : Type*} ⦃m₁ m₂ : CommMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M -> M -> M) = (letI := m₂; HMul.hMul : M -> M -> M)) : m₁ = m₂ :=
CommMonoid.toMonoid_injective Monoid.ext h_mul

@[to_additive]
/--
theorem `LeftCancelMonoid.toMonoid_injective` / 定理 `LeftCancelMonoid.toMonoid_injective`

English:
theorem LeftCancelMonoid.toMonoid_injective
  given: {M : Type u}
  proof: by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  congr <;> injection h

@[to_additive (attr := ext)]

中文:
定理 左消去幺半群.toMonoid_injective
  条件: {M : 类型u}
  证明: by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  congr <;> injection h

@[to_additive (attr := ext)]

Depends on / 依赖: injection
-/
theorem LeftCancelMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@LeftCancelMonoid.toMonoid M) := by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  congr <;> injection h

@[to_additive (attr := ext)]
/--
theorem `LeftCancelMonoid.ext` / 定理 `LeftCancelMonoid.ext`

English:
theorem LeftCancelMonoid.ext
  given: {M : Type u} ⦃m₁ m₂
  statement: LeftCancelMonoid M⦄
  proof: LeftCancelMonoid.toMonoid_injective Monoid.ext h_mul

@[to_additive]

中文:
定理 左消去幺半群.ext
  条件: {M : 类型u} ⦃m₁ m₂
  结论: 左消去幺半群 M⦄
  证明: LeftCancelMonoid.toMonoid_injective Monoid.ext h_mul

@[to_additive]

Depends on / 依赖: HMul.hMul
-/
theorem LeftCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : LeftCancelMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M -> M -> M) = (letI := m₂; HMul.hMul : M -> M -> M)) :
    m₁ = m₂ :=
LeftCancelMonoid.toMonoid_injective Monoid.ext h_mul

@[to_additive]
/--
theorem `RightCancelMonoid.toMonoid_injective` / 定理 `RightCancelMonoid.toMonoid_injective`

English:
theorem RightCancelMonoid.toMonoid_injective
  given: {M : Type u}
  proof: by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  congr <;> injection h

@[to_additive (attr := ext)]

中文:
定理 右消去幺半群.toMonoid_injective
  条件: {M : 类型u}
  证明: by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  congr <;> injection h

@[to_additive (attr := ext)]

Depends on / 依赖: injection
-/
theorem RightCancelMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@RightCancelMonoid.toMonoid M) := by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  congr <;> injection h

@[to_additive (attr := ext)]
/--
theorem `RightCancelMonoid.ext` / 定理 `RightCancelMonoid.ext`

English:
theorem RightCancelMonoid.ext
  given: {M : Type u} ⦃m₁ m₂
  statement: RightCancelMonoid M⦄
  proof: RightCancelMonoid.toMonoid_injective Monoid.ext h_mul

@[to_additive]

中文:
定理 右消去幺半群.ext
  条件: {M : 类型u} ⦃m₁ m₂
  结论: 右消去幺半群 M⦄
  证明: RightCancelMonoid.toMonoid_injective Monoid.ext h_mul

@[to_additive]

Depends on / 依赖: HMul.hMul
-/
theorem RightCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : RightCancelMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M -> M -> M) = (letI := m₂; HMul.hMul : M -> M -> M)) :
    m₁ = m₂ :=
RightCancelMonoid.toMonoid_injective Monoid.ext h_mul

@[to_additive]
/--
theorem `CancelMonoid.toLeftCancelMonoid_injective` / 定理 `CancelMonoid.toLeftCancelMonoid_injective`

English:
theorem CancelMonoid.toLeftCancelMonoid_injective
  given: {M : Type u}
  proof: by
  rintro ⟨⟩ ⟨⟩ h
  congr

@[to_additive (attr := ext)]

中文:
定理 消去幺半群.toLeftCancelMonoid_injective
  条件: {M : 类型u}
  证明: by
  rintro ⟨⟩ ⟨⟩ h
  congr

@[to_additive (attr := ext)]
-/
theorem CancelMonoid.toLeftCancelMonoid_injective {M : Type u} :
    Function.Injective (@CancelMonoid.toLeftCancelMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr

@[to_additive (attr := ext)]
/--
theorem `CancelMonoid.ext` / 定理 `CancelMonoid.ext`

English:
theorem CancelMonoid.ext
  given: {M : Type*} ⦃m₁ m₂
  statement: CancelMonoid M⦄
  proof: CancelMonoid.toLeftCancelMonoid_injective LeftCancelMonoid.ext h_mul

@[to_additive]

中文:
定理 消去幺半群.ext
  条件: {M : 类型} ⦃m₁ m₂
  结论: 消去幺半群 M⦄
  证明: CancelMonoid.toLeftCancelMonoid_injective LeftCancelMonoid.ext h_mul

@[to_additive]

Depends on / 依赖: HMul.hMul
-/
theorem CancelMonoid.ext {M : Type*} ⦃m₁ m₂ : CancelMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M -> M -> M) = (letI := m₂; HMul.hMul : M -> M -> M)) :
    m₁ = m₂ :=
CancelMonoid.toLeftCancelMonoid_injective LeftCancelMonoid.ext h_mul

@[to_additive]
/--
theorem `CancelMonoid.toRightCancelMonoid_injective` / 定理 `CancelMonoid.toRightCancelMonoid_injective`

English:
theorem CancelMonoid.toRightCancelMonoid_injective
  given: {M : Type u}
  proof: by
  intro m₁ m₂ h
  apply CancelMonoid.ext
exact congrArg (fun m : Monoid M => (letI := m; HMul.hMul : M -> M -> M))
    congrArg (@RightCancelMonoid.toMonoid M) h

@[to_additive]

中文:
定理 消去幺半群.toRightCancelMonoid_injective
  条件: {M : 类型u}
  证明: by
  intro m₁ m₂ h
  apply CancelMonoid.ext
exact congrArg (fun m : Monoid M => (letI := m; HMul.hMul : M -> M -> M))
    congrArg (@RightCancelMonoid.toMonoid M) h

@[to_additive]

Depends on / 依赖: CancelMonoid, CancelMonoid.ext, HMul.hMul, Monoid, RightCancelMonoid, RightCancelMonoid.toMonoid, toMonoid
-/
theorem CancelMonoid.toRightCancelMonoid_injective {M : Type u} :
    Function.Injective (@CancelMonoid.toRightCancelMonoid M) := by
  intro m₁ m₂ h
  apply CancelMonoid.ext
exact congrArg (fun m : Monoid M => (letI := m; HMul.hMul : M -> M -> M))
    congrArg (@RightCancelMonoid.toMonoid M) h

@[to_additive]
/--
theorem `CancelCommMonoid.toCommMonoid_injective` / 定理 `CancelCommMonoid.toCommMonoid_injective`

English:
theorem CancelCommMonoid.toCommMonoid_injective
  given: {M : Type u}
  proof: by
  rintro @⟨@⟨@⟨⟩⟩⟩ @⟨@⟨@⟨⟩⟩⟩ h
  grind

@[to_additive (attr := ext)]

中文:
定理 消去交换幺半群.toCommMonoid_injective
  条件: {M : 类型u}
  证明: by
  rintro @⟨@⟨@⟨⟩⟩⟩ @⟨@⟨@⟨⟩⟩⟩ h
  grind

@[to_additive (attr := ext)]
-/
theorem CancelCommMonoid.toCommMonoid_injective {M : Type u} :
    Function.Injective (@CancelCommMonoid.toCommMonoid M) := by
  rintro @⟨@⟨@⟨⟩⟩⟩ @⟨@⟨@⟨⟩⟩⟩ h
  grind

@[to_additive (attr := ext)]
/--
theorem `CancelCommMonoid.ext` / 定理 `CancelCommMonoid.ext`

English:
theorem CancelCommMonoid.ext
  given: {M : Type*} ⦃m₁ m₂
  statement: CancelCommMonoid M⦄
  proof: CancelCommMonoid.toCommMonoid_injective CommMonoid.ext h_mul

@[to_additive (attr := ext)]

中文:
定理 消去交换幺半群.ext
  条件: {M : 类型} ⦃m₁ m₂
  结论: 消去交换幺半群 M⦄
  证明: CancelCommMonoid.toCommMonoid_injective CommMonoid.ext h_mul

@[to_additive (attr := ext)]

Depends on / 依赖: HMul.hMul
-/
theorem CancelCommMonoid.ext {M : Type*} ⦃m₁ m₂ : CancelCommMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M -> M -> M) = (letI := m₂; HMul.hMul : M -> M -> M)) :
    m₁ = m₂ :=
CancelCommMonoid.toCommMonoid_injective CommMonoid.ext h_mul

@[to_additive (attr := ext)]
/--
theorem `DivInvMonoid.ext` / 定理 `DivInvMonoid.ext`

English:
theorem DivInvMonoid.ext
  given: {M : Type*} ⦃m₁ m₂
  statement: DivInvMonoid M⦄
  proof: by
  have h_mon := Monoid.ext h_mul
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) h_mon
  let f : @MonoidHom M M m₁.toMulOne m₂.toMulOne :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.zpow = m₂.zpow := by
    ext m x
    

中文:
定理 除逆幺半群.ext
  条件: {M : 类型} ⦃m₁ m₂
  结论: 除逆幺半群 M⦄
  证明: by
  have h_mon := Monoid.ext h_mul
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) h_mon
  let f : @MonoidHom M M m₁.toMulOne m₂.toMulOne :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.zpow = m₂.zpow := by
    ext m x
    

Depends on / 依赖: HMul.hMul
-/
theorem DivInvMonoid.ext {M : Type*} ⦃m₁ m₂ : DivInvMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M -> M -> M) = (letI := m₂; HMul.hMul : M -> M -> M))
    (h_inv : (letI := m₁; Inv.inv : M -> M) = (letI := m₂; Inv.inv : M -> M)) : m₁ = m₂ := by
  have h_mon := Monoid.ext h_mul
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) h_mon
  let f : @MonoidHom M M m₁.toMulOne m₂.toMulOne :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.zpow = m₂.zpow := by
    ext m x
    exact @MonoidHom.map_zpow' M M m₁ m₂ f (congr_fun h_inv) x m
  have : m₁.div = m₂.div := by
    ext a b
    exact (@div_eq_mul_inv _ m₁ a b).trans
      (((congr_fun (congr_fun h_mul a) _).trans
        (congr_arg _ (congr_fun h_inv b))).trans (@div_eq_mul_inv _ m₂ a b).symm)
  rcases m₁ with @⟨_, ⟨_⟩, ⟨_⟩, ⟨_⟩⟩
  congr

@[to_additive]
/--
lemma `Group.toDivInvMonoid_injective` / 引理 `Group.toDivInvMonoid_injective`

English:
lemma Group.toDivInvMonoid_injective
  given: {G : Type*}
  statement: Injective (@Group.toDivInvMonoid G)
  proof: by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

@[to_additive (attr := ext)]

中文:
引理 群.toDivInvMonoid_injective
  条件: {G : 类型}
  结论: 单射 (@群.toDivInvMonoid G)
  证明: by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

@[to_additive (attr := ext)]
-/
lemma Group.toDivInvMonoid_injective {G : Type*} : Injective (@Group.toDivInvMonoid G) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

@[to_additive (attr := ext)]
/--
theorem `Group.ext` / 定理 `Group.ext`

English:
theorem Group.ext
  given: {G : Type*} ⦃g₁ g₂
  statement: Group G⦄
  proof: by
  have h₁ : g₁.one = g₂.one := congr_arg (·.one) (Monoid.ext h_mul)
  let f : @MonoidHom G G g₁.toMulOne g₂.toMulOne :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  exact
    Group.toDivInvMonoid_injective
      (DivInvMonoid.ext h_

中文:
定理 群.ext
  条件: {G : 类型} ⦃g₁ g₂
  结论: 群 G⦄
  证明: by
  have h₁ : g₁.one = g₂.one := congr_arg (·.one) (Monoid.ext h_mul)
  let f : @MonoidHom G G g₁.toMulOne g₂.toMulOne :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  exact
    Group.toDivInvMonoid_injective
      (DivInvMonoid.ext h_

Depends on / 依赖: HMul.hMul
-/
theorem Group.ext {G : Type*} ⦃g₁ g₂ : Group G⦄
    (h_mul : (letI := g₁; HMul.hMul : G -> G -> G) = (letI := g₂; HMul.hMul : G -> G -> G)) :
    g₁ = g₂ := by
  have h₁ : g₁.one = g₂.one := congr_arg (·.one) (Monoid.ext h_mul)
  let f : @MonoidHom G G g₁.toMulOne g₂.toMulOne :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  exact
    Group.toDivInvMonoid_injective
      (DivInvMonoid.ext h_mul
        (funext <| @MonoidHom.map_inv G G g₁ g₂.toDivisionMonoid f))

@[to_additive]
/--
lemma `CommGroup.toGroup_injective` / 引理 `CommGroup.toGroup_injective`

English:
lemma CommGroup.toGroup_injective
  given: {G : Type*}
  statement: Injective (@CommGroup.toGroup G)
  proof: by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

@[to_additive (attr := ext)]

中文:
引理 交换群.toGroup_injective
  条件: {G : 类型}
  结论: 单射 (@交换群.toGroup G)
  证明: by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

@[to_additive (attr := ext)]
-/
lemma CommGroup.toGroup_injective {G : Type*} : Injective (@CommGroup.toGroup G) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

@[to_additive (attr := ext)]
/--
theorem `CommGroup.ext` / 定理 `CommGroup.ext`

English:
theorem CommGroup.ext
  given: {G : Type*} ⦃g₁ g₂
  statement: CommGroup G⦄
  proof: CommGroup.toGroup_injective Group.ext h_mul

中文:
定理 交换群.ext
  条件: {G : 类型} ⦃g₁ g₂
  结论: 交换群 G⦄
  证明: CommGroup.toGroup_injective Group.ext h_mul

Depends on / 依赖: HMul.hMul
-/
theorem CommGroup.ext {G : Type*} ⦃g₁ g₂ : CommGroup G⦄
    (h_mul : (letI := g₁; HMul.hMul : G -> G -> G) = (letI := g₂; HMul.hMul : G -> G -> G)) : g₁ = g₂ :=
CommGroup.toGroup_injective Group.ext h_mul
