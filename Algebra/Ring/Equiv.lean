/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.GroupWithZero.Equiv
public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Util.Delaborators

import Mathlib.Tactic.DSimpPercent

/-!
# (Semi)ring equivs

In this file we define an extension of `Equiv` called `RingEquiv`, which is a datatype representing
an isomorphism of `Semiring`s, `Ring`s, `DivisionRing`s, or `Field`s.

## Notation

* ``infixl ` ≃+* `:25 := RingEquiv``

The extended equiv have coercions to functions, and the coercion is the canonical notation when
treating the isomorphism as maps.

## Implementation notes

The fields for `RingEquiv` now avoid the unbundled `isMulHom` and `isAddHom`, as these are
deprecated.

Definition of multiplication in the groups of automorphisms agrees with function composition,
multiplication in `Equiv.Perm`, and multiplication in `CategoryTheory.End`, not with
`CategoryTheory.CategoryStruct.comp`.

## Tags

Equiv, MulEquiv, AddEquiv, RingEquiv, MulAut, AddAut, RingAut
-/

@[expose] public section

-- guard against import creep
assert_not_exists Field Fintype

variable {F α β R S S' : Type*}


/--
Definition of `NonUnitalRingHom.inverse` / `NonUnitalRingHom.inverse` 的定义

English:
definition NonUnitalRingHom.inverse
  body: { (f : R ->+ S).inverse g h₁ h₂, (f : R ->ₙ* S).inverse g h₁ h₂ with toFun := g }

中文:
定义 非幺环态射.inverse
  定义体: { (f : R ->+ S).inverse g h₁ h₂, (f : R ->ₙ* S).inverse g h₁ h₂ with toFun := g }
-/
@[simps] def NonUnitalRingHom.inverse
    [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    (f : R ->ₙ+* S) (g : S -> R)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : S ->ₙ+* R :=
  { (f : R ->+ S).inverse g h₁ h₂, (f : R ->ₙ* S).inverse g h₁ h₂ with toFun := g }

/--
Definition of `RingHom.inverse` / `RingHom.inverse` 的定义

English:
definition RingHom.inverse
  signature: [NonAssocSemiring R] [NonAssocSemiring S]
  body: { (f : OneHom R S).inverse g h₁,
    (f : MulHom R S).inverse g h₁ h₂,
    (f : R ->+ S).inverse g h₁ h₂ with toFun := g }

中文:
定义 环态射.inverse
  签名: [非结合半环 R] [非结合半环 S]
  定义体: { (f : OneHom R S).inverse g h₁,
    (f : MulHom R S).inverse g h₁ h₂,
    (f : R ->+ S).inverse g h₁ h₂ with toFun := g }
-/
@[simps] def RingHom.inverse [NonAssocSemiring R] [NonAssocSemiring S]
    (f : RingHom R S) (g : S -> R)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : S ->+* R :=
  { (f : OneHom R S).inverse g h₁,
    (f : MulHom R S).inverse g h₁ h₂,
    (f : R ->+ S).inverse g h₁ h₂ with toFun := g }

/--
Definition of `RingEquiv` / `RingEquiv` 的定义

English:
structure RingEquiv
  parameters: (R S : Type*) [Mul R] [Mul S] [Add R] [Add S]
  extends: R ≃ S, R ≃* S, R ≃+ S
  (no additional axioms)

中文:
结构 环等价
  参数: (R S : 类型) [乘法 R] [乘法 S] [加法 R] [加法 S]
  继承: R ≃ S, R ≃* S, R ≃+ S
  (无附加公理)
-/
structure RingEquiv (R S : Type*) [Mul R] [Mul S] [Add R] [Add S] extends R ≃ S, R ≃* S, R ≃+ S

/-- Notation for `RingEquiv`. -/
infixl:25 " ≃+* " => RingEquiv

/-- The "plain" equivalence of types underlying an equivalence of (semi)rings. -/
add_decl_doc RingEquiv.toEquiv

/-- The equivalence of additive monoids underlying an equivalence of (semi)rings. -/
add_decl_doc RingEquiv.toAddEquiv

/-- The equivalence of multiplicative monoids underlying an equivalence of (semi)rings. -/
add_decl_doc RingEquiv.toMulEquiv

/--
Definition of `RingEquivClass` / `RingEquivClass` 的定义

English:
class RingEquivClass
  parameters: (F R S : Type*) [Mul R] [Add R] [Mul S] [Add S] [EquivLike F R S]
  extends: MulEquivClass F R S
  axioms and operations (1):
    - map_add : forall (f : F) (a b), f (a + b) = f a + f b

中文:
类 环等价类
  参数: (F R S : 类型) [乘法 R] [加法 R] [乘法 S] [加法 S] [等价状 F R S]
  继承: 乘法等价类 F R S
  公理与运算 (1 个):
    - map_add : 对任意 (f : F) (a b), f (a + b) = f a + f b
-/
class RingEquivClass (F R S : Type*) [Mul R] [Add R] [Mul S] [Add S] [EquivLike F R S] : Prop
  extends MulEquivClass F R S where
  /-- By definition, a ring isomorphism preserves the additive structure. -/
  map_add : forall (f : F) (a b), f (a + b) = f a + f b

namespace RingEquivClass

variable [EquivLike F R S]

-- See note [lower instance priority]
instance (priority := 100) toAddEquivClass [Mul R] [Add R]
    [Mul S] [Add S] [h : RingEquivClass F R S] : AddEquivClass F R S :=
  { h with }

-- See note [lower instance priority]
instance (priority := 100) toRingHomClass [NonAssocSemiring R] [NonAssocSemiring S]
    [h : RingEquivClass F R S] : RingHomClass F R S :=
  { h with
    map_zero := map_zero
    map_one := map_one }

-- See note [lower instance priority]
instance (priority := 100) toNonUnitalRingHomClass [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] [h : RingEquivClass F R S] : NonUnitalRingHomClass F R S :=
  { h with
    map_zero := map_zero }

/-- Turn an element of a type `F` satisfying `RingEquivClass F α β` into an actual
`RingEquiv`. This is declared as the default coercion from `F` to `α ≃+* β`. -/
@[coe]
/--
Definition of `toRingEquiv` / `toRingEquiv` 的定义

English:
definition toRingEquiv
  signature: [Mul α] [Add α] [Mul β] [Add β] [EquivLike F α β] [RingEquivClass F α β] (f : F)
  body: { (f : α ≃* β), (f : α ≃+ β) with }

中文:
定义 toRingEquiv
  签名: [乘法 α] [加法 α] [乘法 β] [加法 β] [等价状 F α β] [环等价类 F α β] (f : F)
  定义体: { (f : α ≃* β), (f : α ≃+ β) with }
-/
def toRingEquiv [Mul α] [Add α] [Mul β] [Add β] [EquivLike F α β] [RingEquivClass F α β] (f : F) :
    α ≃+* β :=
  { (f : α ≃* β), (f : α ≃+ β) with }

end RingEquivClass

namespace RingEquiv

section Basic

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

section coe

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (R ≃+* S) R S
  body: f.toFun
  inv f := f.invFun
  coe_injective' e f h₁ h₂ := by
    cases e
    cases f
    congr
    apply Equiv.coe_fn_injective h₁
  left_inv f := f.left_inv
  right_inv f := f.right_inv

中文:
实例 :
  签名: 等价状 (R ≃+* S) R S
  定义体: f.toFun
  inv f := f.invFun
  coe_injective' e f h₁ h₂ := by
    cases e
    cases f
    congr
    apply Equiv.coe_fn_injective h₁
  left_inv f := f.left_inv
  right_inv f := f.right_inv

Depends on / 依赖: f.toFun
-/
instance : EquivLike (R ≃+* S) R S where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' e f h₁ h₂ := by
    cases e
    cases f
    congr
    apply Equiv.coe_fn_injective h₁
  left_inv f := f.left_inv
  right_inv f := f.right_inv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RingEquivClass (R ≃+* S) R S
  body: f.map_add'
  map_mul f := f.map_mul'

中文:
实例 :
  签名: 环等价类 (R ≃+* S) R S
  定义体: f.map_add'
  map_mul f := f.map_mul'

Depends on / 依赖: f.map_add, map_add
-/
instance : RingEquivClass (R ≃+* S) R S where
  map_add f := f.map_add'
  map_mul f := f.map_mul'

/-- Two ring isomorphisms agree if they are defined by the same underlying function. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : R ≃+* S} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : R ≃+* S} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: {f : R ≃+* S} {x x' : R}
  statement: x = x' -> f x = f x'
  proof: DFunLike.congr_arg f

中文:
定理 congr_arg
  条件: {f : R ≃+* S} {x x' : R}
  结论: x = x' -> f x = f x'
  证明: DFunLike.congr_arg f
-/
protected theorem congr_arg {f : R ≃+* S} {x x' : R} : x = x' -> f x = f x' :=
  DFunLike.congr_arg f

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : R ≃+* S} (h : f = g) (x : R)
  statement: f x = g x
  proof: DFunLike.congr_fun h x

@[simp]

中文:
定理 congr_fun
  条件: {f g : R ≃+* S} (h : f = g) (x : R)
  结论: f x = g x
  证明: DFunLike.congr_fun h x

@[simp]
-/
protected theorem congr_fun {f g : R ≃+* S} (h : f = g) (x : R) : f x = g x :=
  DFunLike.congr_fun h x

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (e h₃ h₄)
  statement: ⇑(⟨e, h₃, h₄⟩ : R ≃+* S) = e
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (e h₃ h₄)
  结论: ⇑(⟨e, h₃, h₄⟩ : R ≃+* S) = e
  证明: rfl

@[simp]
-/
theorem coe_mk (e h₃ h₄) : ⇑(⟨e, h₃, h₄⟩ : R ≃+* S) = e :=
  rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (e : R ≃+* S) (e' h₁ h₂ h₃ h₄)
  statement: (⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩ : R ≃+* S) = e
  proof: ext fun _ => rfl

@[simp]

中文:
定理 mk_coe
  条件: (e : R ≃+* S) (e' h₁ h₂ h₃ h₄)
  结论: (⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩ : R ≃+* S) = e
  证明: ext fun _ => rfl

@[simp]
-/
theorem mk_coe (e : R ≃+* S) (e' h₁ h₂ h₃ h₄) : (⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩ : R ≃+* S) = e :=
  ext fun _ => rfl

@[simp]
/--
theorem `toEquiv_eq_coe` / 定理 `toEquiv_eq_coe`

English:
theorem toEquiv_eq_coe
  given: (f : R ≃+* S)
  statement: f.toEquiv = f
  proof: rfl

@[simp]

中文:
定理 toEquiv_eq_coe
  条件: (f : R ≃+* S)
  结论: f.toEquiv = f
  证明: rfl

@[simp]
-/
theorem toEquiv_eq_coe (f : R ≃+* S) : f.toEquiv = f :=
  rfl

@[simp]
/--
theorem `coe_toEquiv` / 定理 `coe_toEquiv`

English:
theorem coe_toEquiv
  given: (f : R ≃+* S)
  statement: ⇑(f : R ≃ S) = f
  proof: rfl

@[simp]

中文:
定理 coe_toEquiv
  条件: (f : R ≃+* S)
  结论: ⇑(f : R ≃ S) = f
  证明: rfl

@[simp]
-/
theorem coe_toEquiv (f : R ≃+* S) : ⇑(f : R ≃ S) = f :=
  rfl

@[simp]
/--
theorem `toAddEquiv_eq_coe` / 定理 `toAddEquiv_eq_coe`

English:
theorem toAddEquiv_eq_coe
  given: (f : R ≃+* S)
  statement: f.toAddEquiv = ↑f
  proof: rfl

@[simp]

中文:
定理 toAddEquiv_eq_coe
  条件: (f : R ≃+* S)
  结论: f.toAddEquiv = ↑f
  证明: rfl

@[simp]
-/
theorem toAddEquiv_eq_coe (f : R ≃+* S) : f.toAddEquiv = ↑f :=
  rfl

@[simp]
/--
theorem `toMulEquiv_eq_coe` / 定理 `toMulEquiv_eq_coe`

English:
theorem toMulEquiv_eq_coe
  given: (f : R ≃+* S)
  statement: f.toMulEquiv = ↑f
  proof: rfl

@[simp, norm_cast]

中文:
定理 toMulEquiv_eq_coe
  条件: (f : R ≃+* S)
  结论: f.toMulEquiv = ↑f
  证明: rfl

@[simp, norm_cast]
-/
theorem toMulEquiv_eq_coe (f : R ≃+* S) : f.toMulEquiv = ↑f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_toMulEquiv` / 定理 `coe_toMulEquiv`

English:
theorem coe_toMulEquiv
  given: (f : R ≃+* S)
  statement: ⇑(f : R ≃* S) = f
  proof: rfl

@[simp]

中文:
定理 coe_toMulEquiv
  条件: (f : R ≃+* S)
  结论: ⇑(f : R ≃* S) = f
  证明: rfl

@[simp]
-/
theorem coe_toMulEquiv (f : R ≃+* S) : ⇑(f : R ≃* S) = f :=
  rfl

@[simp]
/--
theorem `coe_toAddEquiv` / 定理 `coe_toAddEquiv`

English:
theorem coe_toAddEquiv
  given: (f : R ≃+* S)
  statement: ⇑(f : R ≃+ S) = f
  proof: rfl

中文:
定理 coe_toAddEquiv
  条件: (f : R ≃+* S)
  结论: ⇑(f : R ≃+ S) = f
  证明: rfl
-/
theorem coe_toAddEquiv (f : R ≃+* S) : ⇑(f : R ≃+ S) = f :=
  rfl

end coe

section map

/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  given: (e : R ≃+* S) (x y : R)
  statement: e (x * y) = e x * e y
  proof: map_mul e x y

中文:
定理 map_mul
  条件: (e : R ≃+* S) (x y : R)
  结论: e (x * y) = e x * e y
  证明: map_mul e x y
-/
protected theorem map_mul (e : R ≃+* S) (x y : R) : e (x * y) = e x * e y :=
  map_mul e x y

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (e : R ≃+* S) (x y : R)
  statement: e (x + y) = e x + e y
  proof: map_add e x y

中文:
定理 map_add
  条件: (e : R ≃+* S) (x y : R)
  结论: e (x + y) = e x + e y
  证明: map_add e x y
-/
protected theorem map_add (e : R ≃+* S) (x y : R) : e (x + y) = e x + e y :=
  map_add e x y

end map

section bijective

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (e : R ≃+* S)
  statement: Function.Bijective e
  proof: EquivLike.bijective e

中文:
定理 bijective
  条件: (e : R ≃+* S)
  结论: 函数.双射 e
  证明: EquivLike.bijective e
-/
protected theorem bijective (e : R ≃+* S) : Function.Bijective e :=
  EquivLike.bijective e

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (e : R ≃+* S)
  statement: Function.Injective e
  proof: EquivLike.injective e

中文:
定理 injective
  条件: (e : R ≃+* S)
  结论: 函数.单射 e
  证明: EquivLike.injective e
-/
protected theorem injective (e : R ≃+* S) : Function.Injective e :=
  EquivLike.injective e

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (e : R ≃+* S)
  statement: Function.Surjective e
  proof: EquivLike.surjective e

中文:
定理 surjective
  条件: (e : R ≃+* S)
  结论: 函数.满射 e
  证明: EquivLike.surjective e
-/
protected theorem surjective (e : R ≃+* S) : Function.Surjective e :=
  EquivLike.surjective e

end bijective

variable (R)

section refl

/-- The identity map is a ring isomorphism. -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : R ≃+* R
  body: { MulEquiv.refl R, AddEquiv.refl R with }

中文:
定义 refl
  签名: : R ≃+* R
  定义体: { MulEquiv.refl R, AddEquiv.refl R with }

Depends on / 依赖: AddEquiv, AddEquiv.refl, MulEquiv, MulEquiv.refl
-/
def refl : R ≃+* R :=
  { MulEquiv.refl R, AddEquiv.refl R with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (R ≃+* R)
  body: ⟨RingEquiv.refl R⟩

@[simp]

中文:
实例 :
  签名: 可居 (R ≃+* R)
  定义体: ⟨RingEquiv.refl R⟩

@[simp]

Depends on / 依赖: RingEquiv, RingEquiv.refl
-/
instance : Inhabited (R ≃+* R) :=
  ⟨RingEquiv.refl R⟩

@[simp]
/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: (x : R)
  statement: RingEquiv.refl R x = x
  proof: rfl

@[simp]

中文:
定理 refl_apply
  条件: (x : R)
  结论: 环等价.refl R x = x
  证明: rfl

@[simp]
-/
theorem refl_apply (x : R) : RingEquiv.refl R x = x :=
  rfl

@[simp]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  given: (R : Type*) [Mul R] [Add R]
  statement: ⇑(RingEquiv.refl R) = id
  proof: rfl

@[simp]

中文:
定理 coe_refl
  条件: (R : 类型) [乘法 R] [加法 R]
  结论: ⇑(环等价.refl R) = id
  证明: rfl

@[simp]
-/
theorem coe_refl (R : Type*) [Mul R] [Add R] : ⇑(RingEquiv.refl R) = id :=
  rfl

@[simp]
/--
theorem `coe_addEquiv_refl` / 定理 `coe_addEquiv_refl`

English:
theorem coe_addEquiv_refl
  statement: (RingEquiv.refl R : R ≃+ R) = AddEquiv.refl R
  proof: rfl

@[simp]

中文:
定理 coe_addEquiv_refl
  结论: (环等价.refl R : R ≃+ R) = 加法等价.refl R
  证明: rfl

@[simp]
-/
theorem coe_addEquiv_refl : (RingEquiv.refl R : R ≃+ R) = AddEquiv.refl R :=
  rfl

@[simp]
/--
theorem `coe_mulEquiv_refl` / 定理 `coe_mulEquiv_refl`

English:
theorem coe_mulEquiv_refl
  statement: (RingEquiv.refl R : R ≃* R) = MulEquiv.refl R
  proof: rfl

中文:
定理 coe_mulEquiv_refl
  结论: (环等价.refl R : R ≃* R) = 乘法等价.refl R
  证明: rfl
-/
theorem coe_mulEquiv_refl : (RingEquiv.refl R : R ≃* R) = MulEquiv.refl R :=
  rfl

end refl

variable {R}

section symm

/-- The inverse of a ring isomorphism is a ring isomorphism. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : R ≃+* S)
  body: { e.toMulEquiv.symm, e.toAddEquiv.symm with }

@[simp]

中文:
定义 symm
  签名: (e : R ≃+* S)
  定义体: { e.toMulEquiv.symm, e.toAddEquiv.symm with }

@[simp]
-/
protected def symm (e : R ≃+* S) : S ≃+* R :=
  { e.toMulEquiv.symm, e.toAddEquiv.symm with }

@[simp]
/--
theorem `invFun_eq_symm` / 定理 `invFun_eq_symm`

English:
theorem invFun_eq_symm
  given: (f : R ≃+* S)
  statement: EquivLike.inv f = f.symm
  proof: rfl

@[simp]

中文:
定理 invFun_eq_symm
  条件: (f : R ≃+* S)
  结论: 等价状.inv f = f.symm
  证明: rfl

@[simp]
-/
theorem invFun_eq_symm (f : R ≃+* S) : EquivLike.inv f = f.symm :=
  rfl

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (e : R ≃+* S)
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  条件: (e : R ≃+* S)
  结论: e.symm.symm = e
  证明: rfl
-/
theorem symm_symm (e : R ≃+* S) : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (RingEquiv.symm : (R ≃+* S) -> S ≃+* R)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

中文:
定理 symm_bijective
  结论: 函数.双射 (环等价.symm : (R ≃+* S) -> S ≃+* R)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (RingEquiv.symm : (R ≃+* S) -> S ≃+* R) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/--
theorem `mk_coe'` / 定理 `mk_coe'`

English:
theorem mk_coe'
  given: (e : R ≃+* S) (f h₁ h₂ h₃ h₄)
  proof: symm_bijective.injective ext fun _ => rfl

@[simp]

中文:
定理 mk_coe'
  条件: (e : R ≃+* S) (f h₁ h₂ h₃ h₄)
  证明: symm_bijective.injective ext fun _ => rfl

@[simp]

Depends on / 依赖: injective, symm_bijective, symm_bijective.injective
-/
theorem mk_coe' (e : R ≃+* S) (f h₁ h₂ h₃ h₄) :
    (⟨⟨f, ⇑e, h₁, h₂⟩, h₃, h₄⟩ : S ≃+* R) = e.symm :=
symm_bijective.injective ext fun _ => rfl

@[simp]
/--
theorem `symm_mk` / 定理 `symm_mk`

English:
theorem symm_mk
  given: (e : R ≃ S) (h₁ h₂)
  statement: dsimp%
  proof: rfl

@[simp]

中文:
定理 symm_mk
  条件: (e : R ≃ S) (h₁ h₂)
  结论: dsimp%
  证明: rfl

@[simp]

Depends on / 依赖: e.symm
-/
theorem symm_mk (e : R ≃ S) (h₁ h₂) : dsimp%
    (mk e h₁ h₂).symm =
      { (mk e h₁ h₂).symm with
        toEquiv := e.symm } :=
  rfl

@[simp]
/--
theorem `symm_refl` / 定理 `symm_refl`

English:
theorem symm_refl
  statement: (RingEquiv.refl R).symm = RingEquiv.refl R
  proof: rfl

@[simp]

中文:
定理 symm_refl
  结论: (环等价.refl R).symm = 环等价.refl R
  证明: rfl

@[simp]
-/
theorem symm_refl : (RingEquiv.refl R).symm = RingEquiv.refl R :=
  rfl

@[simp]
/--
theorem `coe_toEquiv_symm` / 定理 `coe_toEquiv_symm`

English:
theorem coe_toEquiv_symm
  given: (e : R ≃+* S)
  statement: (e.symm : S ≃ R) = (e : R ≃ S).symm
  proof: rfl

@[simp]

中文:
定理 coe_toEquiv_symm
  条件: (e : R ≃+* S)
  结论: (e.symm : S ≃ R) = (e : R ≃ S).symm
  证明: rfl

@[simp]
-/
theorem coe_toEquiv_symm (e : R ≃+* S) : (e.symm : S ≃ R) = (e : R ≃ S).symm :=
  rfl

@[simp]
/--
theorem `coe_toMulEquiv_symm` / 定理 `coe_toMulEquiv_symm`

English:
theorem coe_toMulEquiv_symm
  given: (e : R ≃+* S)
  statement: (e.symm : S ≃* R) = (e : R ≃* S).symm
  proof: rfl

@[simp]

中文:
定理 coe_toMulEquiv_symm
  条件: (e : R ≃+* S)
  结论: (e.symm : S ≃* R) = (e : R ≃* S).symm
  证明: rfl

@[simp]
-/
theorem coe_toMulEquiv_symm (e : R ≃+* S) : (e.symm : S ≃* R) = (e : R ≃* S).symm :=
  rfl

@[simp]
/--
theorem `coe_toAddEquiv_symm` / 定理 `coe_toAddEquiv_symm`

English:
theorem coe_toAddEquiv_symm
  given: (e : R ≃+* S)
  statement: (e.symm : S ≃+ R) = (e : R ≃+ S).symm
  proof: rfl

@[simp]

中文:
定理 coe_toAddEquiv_symm
  条件: (e : R ≃+* S)
  结论: (e.symm : S ≃+ R) = (e : R ≃+ S).symm
  证明: rfl

@[simp]
-/
theorem coe_toAddEquiv_symm (e : R ≃+* S) : (e.symm : S ≃+ R) = (e : R ≃+ S).symm :=
  rfl

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : R ≃+* S)
  statement: forall x, e (e.symm x) = x
  proof: e.toEquiv.apply_symm_apply

@[simp]

中文:
定理 apply_symm_apply
  条件: (e : R ≃+* S)
  结论: 对任意 x, e (e.symm x) = x
  证明: e.toEquiv.apply_symm_apply

@[simp]

Depends on / 依赖: apply_symm_apply, e.toEquiv.apply_symm_apply, toEquiv
-/
theorem apply_symm_apply (e : R ≃+* S) : forall x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : R ≃+* S)
  statement: forall x, e.symm (e x) = x
  proof: e.toEquiv.symm_apply_apply

中文:
定理 symm_apply_apply
  条件: (e : R ≃+* S)
  结论: 对任意 x, e.symm (e x) = x
  证明: e.toEquiv.symm_apply_apply

Depends on / 依赖: e.toEquiv.symm_apply_apply, symm_apply_apply, toEquiv
-/
theorem symm_apply_apply (e : R ≃+* S) : forall x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply

/--
lemma `image_symm_eq_preimage` / 引理 `image_symm_eq_preimage`

English:
lemma image_symm_eq_preimage
  given: (e : R ≃+* S) (s : Set S)
  statement: e.symm '' s = e ⁻¹' s
  proof: e.toEquiv.image_symm_eq_preimage _

中文:
引理 image_symm_eq_preimage
  条件: (e : R ≃+* S) (s : 集合 S)
  结论: e.symm '' s = e ⁻¹' s
  证明: e.toEquiv.image_symm_eq_preimage _

Depends on / 依赖: e.toEquiv.image_symm_eq_preimage, image_symm_eq_preimage, toEquiv
-/
lemma image_symm_eq_preimage (e : R ≃+* S) (s : Set S) : e.symm '' s = e ⁻¹' s :=
  e.toEquiv.image_symm_eq_preimage _

/--
lemma `image_eq_preimage_symm` / 引理 `image_eq_preimage_symm`

English:
lemma image_eq_preimage_symm
  given: (e : R ≃+* S) (s : Set R)
  statement: e '' s = e.symm ⁻¹' s
  proof: e.toEquiv.image_eq_preimage_symm _

@[simp]

中文:
引理 image_eq_preimage_symm
  条件: (e : R ≃+* S) (s : 集合 R)
  结论: e '' s = e.symm ⁻¹' s
  证明: e.toEquiv.image_eq_preimage_symm _

@[simp]

Depends on / 依赖: e.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
lemma image_eq_preimage_symm (e : R ≃+* S) (s : Set R) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage_symm _

@[simp]
/--
lemma `coe_coe_toEquiv_symm` / 引理 `coe_coe_toEquiv_symm`

English:
lemma coe_coe_toEquiv_symm
  given: (e : R ≃+* S)
  statement: ⇑(e : R ≃ S).symm = ⇑e.symm
  proof: rfl

@[simp]

中文:
引理 coe_coe_toEquiv_symm
  条件: (e : R ≃+* S)
  结论: ⇑(e : R ≃ S).symm = ⇑e.symm
  证明: rfl

@[simp]
-/
lemma coe_coe_toEquiv_symm (e : R ≃+* S) : ⇑(e : R ≃ S).symm = ⇑e.symm := rfl

@[simp]
/--
lemma `coe_coe_toMulEquiv_symm` / 引理 `coe_coe_toMulEquiv_symm`

English:
lemma coe_coe_toMulEquiv_symm
  given: (e : R ≃+* S)
  statement: ⇑(e : R ≃* S).symm = ⇑e.symm
  proof: rfl

@[simp]

中文:
引理 coe_coe_toMulEquiv_symm
  条件: (e : R ≃+* S)
  结论: ⇑(e : R ≃* S).symm = ⇑e.symm
  证明: rfl

@[simp]
-/
lemma coe_coe_toMulEquiv_symm (e : R ≃+* S) : ⇑(e : R ≃* S).symm = ⇑e.symm := rfl

@[simp]
/--
lemma `coe_coe_toAddEquiv_symm` / 引理 `coe_coe_toAddEquiv_symm`

English:
lemma coe_coe_toAddEquiv_symm
  given: (e : R ≃+* S)
  statement: ⇑(e : R ≃+ S).symm = ⇑e.symm
  proof: rfl

中文:
引理 coe_coe_toAddEquiv_symm
  条件: (e : R ≃+* S)
  结论: ⇑(e : R ≃+ S).symm = ⇑e.symm
  证明: rfl
-/
lemma coe_coe_toAddEquiv_symm (e : R ≃+* S) : ⇑(e : R ≃+ S).symm = ⇑e.symm := rfl

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (e : R ≃+* S) {x : S} {y : R}
  proof: Equiv.symm_apply_eq _

中文:
定理 symm_apply_eq
  条件: (e : R ≃+* S) {x : S} {y : R}
  证明: Equiv.symm_apply_eq _

Depends on / 依赖: Equiv.symm_apply_eq, symm_apply_eq
-/
theorem symm_apply_eq (e : R ≃+* S) {x : S} {y : R} :
    e.symm x = y ↔ x = e y := Equiv.symm_apply_eq _

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (e : R ≃+* S) {x : S} {y : R}
  proof: Equiv.eq_symm_apply _

中文:
定理 eq_symm_apply
  条件: (e : R ≃+* S) {x : S} {y : R}
  证明: Equiv.eq_symm_apply _

Depends on / 依赖: Equiv.eq_symm_apply, eq_symm_apply
-/
theorem eq_symm_apply (e : R ≃+* S) {x : S} {y : R} :
    y = e.symm x ↔ e y = x := Equiv.eq_symm_apply _

end symm

section simps

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (e : R ≃+* S)
  body: e.symm

initialize_simps_projections RingEquiv (toFun -> apply, invFun -> symm_apply)

中文:
定义 Simps.symm_apply
  签名: (e : R ≃+* S)
  定义体: e.symm

initialize_simps_projections RingEquiv (toFun -> apply, invFun -> symm_apply)
-/
def Simps.symm_apply (e : R ≃+* S) : S -> R :=
  e.symm

initialize_simps_projections RingEquiv (toFun -> apply, invFun -> symm_apply)

end simps

section trans

/-- Transitivity of `RingEquiv`. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  body: { e₁.toMulEquiv.trans e₂.toMulEquiv, e₁.toAddEquiv.trans e₂.toAddEquiv with }

@[simp]

中文:
定义 trans
  签名: (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  定义体: { e₁.toMulEquiv.trans e₂.toMulEquiv, e₁.toAddEquiv.trans e₂.toAddEquiv with }

@[simp]
-/
protected def trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : R ≃+* S' :=
  { e₁.toMulEquiv.trans e₂.toMulEquiv, e₁.toAddEquiv.trans e₂.toAddEquiv with }

@[simp]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  statement: (e₁.trans e₂ : R -> S') = e₂ ∘ e₁
  proof: rfl

中文:
定理 coe_trans
  条件: (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  结论: (e₁.trans e₂ : R -> S') = e₂ ∘ e₁
  证明: rfl
-/
theorem coe_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂ : R -> S') = e₂ ∘ e₁ :=
  rfl

/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : R)
  statement: e₁.trans e₂ a = e₂ (e₁ a)
  proof: rfl

@[simp]

中文:
定理 trans_apply
  条件: (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : R)
  结论: e₁.trans e₂ a = e₂ (e₁ a)
  证明: rfl

@[simp]
-/
theorem trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : R) : e₁.trans e₂ a = e₂ (e₁ a) :=
  rfl

@[simp]
/--
theorem `symm_trans_apply` / 定理 `symm_trans_apply`

English:
theorem symm_trans_apply
  given: (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : S')
  proof: rfl

中文:
定理 symm_trans_apply
  条件: (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : S')
  证明: rfl
-/
theorem symm_trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : S') :
    (e₁.trans e₂).symm a = e₁.symm (e₂.symm a) :=
  rfl

/--
theorem `symm_trans` / 定理 `symm_trans`

English:
theorem symm_trans
  given: (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  statement: (e₁.trans e₂).symm = e₂.symm.trans e₁.symm
  proof: rfl

@[simp]

中文:
定理 symm_trans
  条件: (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  结论: (e₁.trans e₂).symm = e₂.symm.trans e₁.symm
  证明: rfl

@[simp]
-/
theorem symm_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl

@[simp]
/--
theorem `coe_mulEquiv_trans` / 定理 `coe_mulEquiv_trans`

English:
theorem coe_mulEquiv_trans
  given: (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  proof: rfl

@[simp]

中文:
定理 coe_mulEquiv_trans
  条件: (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  证明: rfl

@[simp]
-/
theorem coe_mulEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R ≃* S') = (e₁ : R ≃* S).trans ↑e₂ :=
  rfl

@[simp]
/--
theorem `coe_addEquiv_trans` / 定理 `coe_addEquiv_trans`

English:
theorem coe_addEquiv_trans
  given: (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  proof: rfl

中文:
定理 coe_addEquiv_trans
  条件: (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  证明: rfl
-/
theorem coe_addEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R ≃+ S') = (e₁ : R ≃+ S).trans ↑e₂ :=
  rfl

end trans

section unique

/--
Definition of `ofUnique` / `ofUnique` 的定义

English:
definition ofUnique
  signature: {M N} [Unique M] [Unique N] [Add M] [Mul M] [Add N] [Mul N]
  body: { AddEquiv.ofUnique, MulEquiv.ofUnique with }

中文:
定义 ofUnique
  签名: {M N} [唯一 M] [唯一 N] [加法 M] [乘法 M] [加法 N] [乘法 N]
  定义体: { AddEquiv.ofUnique, MulEquiv.ofUnique with }

Depends on / 依赖: AddEquiv, AddEquiv.ofUnique, MulEquiv, MulEquiv.ofUnique, ofUnique
-/
def ofUnique {M N} [Unique M] [Unique N] [Add M] [Mul M] [Add N] [Mul N] : M ≃+* N :=
  { AddEquiv.ofUnique, MulEquiv.ofUnique with }

instance {M N} [Unique M] [Unique N] [Add M] [Mul M] [Add N] [Mul N] :
    Unique (M ≃+* N) where
  default := .ofUnique
  uniq _ := ext fun _ => Subsingleton.elim _ _

end unique

end Basic

section Opposite

open MulOpposite

/-- A ring iso `α ≃+* β` can equivalently be viewed as a ring iso `αᵐᵒᵖ ≃+* βᵐᵒᵖ`. -/
@[simps! symm_apply_apply symm_apply_symm_apply apply_apply apply_symm_apply]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: {α β} [Add α] [Mul α] [Add β] [Mul β]
  body: { AddEquiv.mulOp f.toAddEquiv, MulEquiv.op f.toMulEquiv with }
  invFun f := { AddEquiv.mulOp.symm f.toAddEquiv, MulEquiv.op.symm f.toMulEquiv with }

中文:
定义 op
  签名: {α β} [加法 α] [乘法 α] [加法 β] [乘法 β]
  定义体: { AddEquiv.mulOp f.toAddEquiv, MulEquiv.op f.toMulEquiv with }
  invFun f := { AddEquiv.mulOp.symm f.toAddEquiv, MulEquiv.op.symm f.toMulEquiv with }
-/
protected def op {α β} [Add α] [Mul α] [Add β] [Mul β] :
    α ≃+* β ≃ (αᵐᵒᵖ ≃+* βᵐᵒᵖ) where
  toFun f := { AddEquiv.mulOp f.toAddEquiv, MulEquiv.op f.toMulEquiv with }
  invFun f := { AddEquiv.mulOp.symm f.toAddEquiv, MulEquiv.op.symm f.toMulEquiv with }

/-- The 'unopposite' of a ring iso `αᵐᵒᵖ ≃+* βᵐᵒᵖ`. Inverse to `RingEquiv.op`. -/
@[simp]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {α β} [Add α] [Mul α] [Add β] [Mul β]
  body: RingEquiv.op.symm

中文:
定义 unop
  签名: {α β} [加法 α] [乘法 α] [加法 β] [乘法 β]
  定义体: RingEquiv.op.symm
-/
protected def unop {α β} [Add α] [Mul α] [Add β] [Mul β] : αᵐᵒᵖ ≃+* βᵐᵒᵖ ≃ (α ≃+* β) :=
  RingEquiv.op.symm

/-- A ring is isomorphic to the opposite of its opposite. -/
@[simps!]
/--
Definition of `opOp` / `opOp` 的定义

English:
definition opOp
  signature: (R : Type*) [Add R] [Mul R]
  body: MulEquiv.opOp R
  map_add' _ _ := rfl

中文:
定义 opOp
  签名: (R : 类型) [加法 R] [乘法 R]
  定义体: MulEquiv.opOp R
  map_add' _ _ := rfl

Depends on / 依赖: MulEquiv, MulEquiv.opOp
-/
def opOp (R : Type*) [Add R] [Mul R] : R ≃+* Rᵐᵒᵖᵐᵒᵖ where
  __ := MulEquiv.opOp R
  map_add' _ _ := rfl

section NonUnitalCommSemiring

variable (R) [NonUnitalCommSemiring R]

/--
Definition of `toOpposite` / `toOpposite` 的定义

English:
definition toOpposite
  signature: : R ≃+* Rᵐᵒᵖ
  body: { MulOpposite.opEquiv with
    map_add' := fun _ _ => rfl
    map_mul' := fun x y => mul_comm (op y) (op x) }

@[simp]

中文:
定义 toOpposite
  签名: : R ≃+* Rᵐᵒᵖ
  定义体: { MulOpposite.opEquiv with
    map_add' := fun _ _ => rfl
    map_mul' := fun x y => mul_comm (op y) (op x) }

@[simp]

Depends on / 依赖: MulOpposite, MulOpposite.opEquiv, map_add, map_mul, mul_comm, opEquiv
-/
def toOpposite : R ≃+* Rᵐᵒᵖ :=
  { MulOpposite.opEquiv with
    map_add' := fun _ _ => rfl
    map_mul' := fun x y => mul_comm (op y) (op x) }

@[simp]
/--
theorem `toOpposite_apply` / 定理 `toOpposite_apply`

English:
theorem toOpposite_apply
  given: (r : R)
  statement: toOpposite R r = op r
  proof: rfl

@[simp]

中文:
定理 toOpposite_apply
  条件: (r : R)
  结论: toOpposite R r = op r
  证明: rfl

@[simp]
-/
theorem toOpposite_apply (r : R) : toOpposite R r = op r :=
  rfl

@[simp]
/--
theorem `toOpposite_symm_apply` / 定理 `toOpposite_symm_apply`

English:
theorem toOpposite_symm_apply
  given: (r : Rᵐᵒᵖ)
  statement: (toOpposite R).symm r = unop r
  proof: rfl

中文:
定理 toOpposite_symm_apply
  条件: (r : Rᵐᵒᵖ)
  结论: (toOpposite R).symm r = unop r
  证明: rfl

Depends on / 依赖: infer_instance
-/
theorem toOpposite_symm_apply (r : Rᵐᵒᵖ) : (toOpposite R).symm r = unop r :=
  rfl

end NonUnitalCommSemiring

end Opposite

section NonUnitalSemiring

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R ≃+* S) (x : R)

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: f 0 = 0
  proof: map_zero f

中文:
定理 map_zero
  结论: f 0 = 0
  证明: map_zero f
-/
protected theorem map_zero : f 0 = 0 :=
  map_zero f

variable {x}

/--
theorem `map_eq_zero_iff` / 定理 `map_eq_zero_iff`

English:
theorem map_eq_zero_iff
  statement: f x = 0 ↔ x = 0
  proof: EmbeddingLike.map_eq_zero_iff

中文:
定理 map_eq_zero_iff
  结论: f x = 0 ↔ x = 0
  证明: EmbeddingLike.map_eq_zero_iff
-/
protected theorem map_eq_zero_iff : f x = 0 ↔ x = 0 :=
  EmbeddingLike.map_eq_zero_iff

/--
theorem `map_ne_zero_iff` / 定理 `map_ne_zero_iff`

English:
theorem map_ne_zero_iff
  statement: f x != 0 ↔ x != 0
  proof: EmbeddingLike.map_ne_zero_iff

中文:
定理 map_ne_zero_iff
  结论: f x != 0 ↔ x != 0
  证明: EmbeddingLike.map_ne_zero_iff

Depends on / 依赖: EmbeddingLike, EmbeddingLike.map_ne_zero_iff, map_ne_zero_iff
-/
theorem map_ne_zero_iff : f x != 0 ↔ x != 0 :=
  EmbeddingLike.map_ne_zero_iff

variable [FunLike F R S]

/--
Definition of `ofBijective` / `ofBijective` 的定义

English:
definition ofBijective
  signature: [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f)
  body: { Equiv.ofBijective f hf with
    map_mul' := map_mul f
    map_add' := map_add f }

@[simp]

中文:
定义 ofBijective
  签名: [非幺环态射类 F R S] (f : F) (hf : 函数.双射 f)
  定义体: { Equiv.ofBijective f hf with
    map_mul' := map_mul f
    map_add' := map_add f }

@[simp]

Depends on / 依赖: Equiv.ofBijective, map_add, map_mul, ofBijective
-/
noncomputable def ofBijective [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f) :
    R ≃+* S :=
  { Equiv.ofBijective f hf with
    map_mul' := map_mul f
    map_add' := map_add f }

@[simp]
/--
theorem `coe_ofBijective` / 定理 `coe_ofBijective`

English:
theorem coe_ofBijective
  given: [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f)
  proof: rfl

中文:
定理 coe_ofBijective
  条件: [非幺环态射类 F R S] (f : F) (hf : 函数.双射 f)
  证明: rfl
-/
theorem coe_ofBijective [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f) :
    (ofBijective f hf : R -> S) = f :=
  rfl

/--
theorem `ofBijective_apply` / 定理 `ofBijective_apply`

English:
theorem ofBijective_apply
  statement: [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f)
  proof: rfl

@[simp]

中文:
定理 ofBijective_apply
  结论: [非幺环态射类 F R S] (f : F) (hf : 函数.双射 f)
  证明: rfl

@[simp]
-/
theorem ofBijective_apply [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f)
    (x : R) : ofBijective f hf x = f x :=
  rfl

@[simp]
/--
lemma `ofBijective_symm_comp` / 引理 `ofBijective_symm_comp`

English:
lemma ofBijective_symm_comp
  given: (f : R ->ₙ+* S) (hf : Function.Bijective f)
  proof: by
  ext
exact (RingEquiv.ofBijective f hf).injective RingEquiv.apply_symm_apply ..

@[simp]

中文:
引理 ofBijective_symm_comp
  条件: (f : R ->ₙ+* S) (hf : 函数.双射 f)
  证明: by
  ext
exact (RingEquiv.ofBijective f hf).injective RingEquiv.apply_symm_apply ..

@[simp]

Depends on / 依赖: RingEquiv, RingEquiv.apply_symm_apply, RingEquiv.ofBijective, apply_symm_apply, injective, ofBijective
-/
lemma ofBijective_symm_comp (f : R ->ₙ+* S) (hf : Function.Bijective f) :
    ((RingEquiv.ofBijective f hf).symm : _ ->ₙ+* _).comp f = NonUnitalRingHom.id R := by
  ext
exact (RingEquiv.ofBijective f hf).injective RingEquiv.apply_symm_apply ..

@[simp]
/--
lemma `comp_ofBijective_symm` / 引理 `comp_ofBijective_symm`

English:
lemma comp_ofBijective_symm
  given: (f : R ->ₙ+* S) (hf : Function.Bijective f)
  proof: by
  ext
exact (RingEquiv.ofBijective f hf).symm.injective RingEquiv.apply_symm_apply ..

中文:
引理 comp_ofBijective_symm
  条件: (f : R ->ₙ+* S) (hf : 函数.双射 f)
  证明: by
  ext
exact (RingEquiv.ofBijective f hf).symm.injective RingEquiv.apply_symm_apply ..

Depends on / 依赖: RingEquiv, RingEquiv.apply_symm_apply, RingEquiv.ofBijective, apply_symm_apply, injective, ofBijective, symm.injective
-/
lemma comp_ofBijective_symm (f : R ->ₙ+* S) (hf : Function.Bijective f) :
    f.comp ((RingEquiv.ofBijective f hf).symm : _ ->ₙ+* _) = NonUnitalRingHom.id S := by
  ext
exact (RingEquiv.ofBijective f hf).symm.injective RingEquiv.apply_symm_apply ..

/-- Product of a singleton family of (non-unital non-associative semi)rings is isomorphic
to the only member of this family. -/
@[simps! -fullyApplied]
/--
Definition of `piUnique` / `piUnique` 的定义

English:
definition piUnique
  signature: {ι : Type*} (R : ι -> Type*) [Unique ι] [forall i, NonUnitalNonAssocSemiring (R i)]
  body: Equiv.piUnique R
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

中文:
定义 piUnique
  签名: {ι : 类型} (R : ι -> 类型) [唯一 ι] [对任意 i, 非幺非结合半环 (R i)]
  定义体: Equiv.piUnique R
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: Equiv.piUnique, piUnique
-/
def piUnique {ι : Type*} (R : ι -> Type*) [Unique ι] [forall i, NonUnitalNonAssocSemiring (R i)] :
    (forall i, R i) ≃+* R default where
  __ := Equiv.piUnique R
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- `Equiv.cast (congrArg _ h)` as a ring equiv.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an equality of types,
to avoid having to deal with an equality of the algebraic structure itself. -/
@[simps!]
/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  body: AddEquiv.cast h
  __ := MulEquiv.cast h

中文:
定义 cast
  定义体: AddEquiv.cast h
  __ := MulEquiv.cast h
-/
protected def cast
    {ι : Type*} {R : ι -> Type*} [forall i, Mul (R i)] [forall i, Add (R i)] {i j : ι} (h : i = j) :
    R i ≃+* R j where
  __ := AddEquiv.cast h
  __ := MulEquiv.cast h

/-- A family of ring isomorphisms `∀ j, (R j ≃+* S j)` generates a
ring isomorphisms between `∀ j, R j` and `∀ j, S j`.

This is the `RingEquiv` version of `Equiv.piCongrRight`, and the dependent version of
`RingEquiv.arrowCongr`.
-/
@[simps apply]
/--
Definition of `piCongrRight` / `piCongrRight` 的定义

English:
definition piCongrRight
  signature: {ι : Type*} {R S : ι -> Type*} [forall i, NonUnitalNonAssocSemiring (R i)]
  body: { @MulEquiv.piCongrRight ι R S _ _ fun i => (e i).toMulEquiv,
    @AddEquiv.piCongrRight ι R S _ _ fun i => (e i).toAddEquiv with
    toFun := fun x j => e j (x j)
    invFun := fun x j => (e j).symm (x j) }

@[simp]

中文:
定义 piCongrRight
  签名: {ι : 类型} {R S : ι -> 类型} [对任意 i, 非幺非结合半环 (R i)]
  定义体: { @MulEquiv.piCongrRight ι R S _ _ fun i => (e i).toMulEquiv,
    @AddEquiv.piCongrRight ι R S _ _ fun i => (e i).toAddEquiv with
    toFun := fun x j => e j (x j)
    invFun := fun x j => (e j).symm (x j) }

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.piCongrRight, MulEquiv, MulEquiv.piCongrRight, invFun, piCongrRight, toAddEquiv, toMulEquiv
-/
def piCongrRight {ι : Type*} {R S : ι -> Type*} [forall i, NonUnitalNonAssocSemiring (R i)]
    [forall i, NonUnitalNonAssocSemiring (S i)] (e : forall i, R i ≃+* S i) : (forall i, R i) ≃+* forall i, S i :=
  { @MulEquiv.piCongrRight ι R S _ _ fun i => (e i).toMulEquiv,
    @AddEquiv.piCongrRight ι R S _ _ fun i => (e i).toAddEquiv with
    toFun := fun x j => e j (x j)
    invFun := fun x j => (e j).symm (x j) }

@[simp]
/--
theorem `piCongrRight_refl` / 定理 `piCongrRight_refl`

English:
theorem piCongrRight_refl
  given: {ι : Type*} {R : ι -> Type*} [forall i, NonUnitalNonAssocSemiring (R i)]
  proof: rfl

@[simp]

中文:
定理 piCongrRight_refl
  条件: {ι : 类型} {R : ι -> 类型} [对任意 i, 非幺非结合半环 (R i)]
  证明: rfl

@[simp]
-/
theorem piCongrRight_refl {ι : Type*} {R : ι -> Type*} [forall i, NonUnitalNonAssocSemiring (R i)] :
    (piCongrRight fun i => RingEquiv.refl (R i)) = RingEquiv.refl _ :=
  rfl

@[simp]
/--
theorem `piCongrRight_symm` / 定理 `piCongrRight_symm`

English:
theorem piCongrRight_symm
  statement: {ι : Type*} {R S : ι -> Type*} [forall i, NonUnitalNonAssocSemiring (R i)]
  proof: rfl

@[simp]

中文:
定理 piCongrRight_symm
  结论: {ι : 类型} {R S : ι -> 类型} [对任意 i, 非幺非结合半环 (R i)]
  证明: rfl

@[simp]
-/
theorem piCongrRight_symm {ι : Type*} {R S : ι -> Type*} [forall i, NonUnitalNonAssocSemiring (R i)]
    [forall i, NonUnitalNonAssocSemiring (S i)] (e : forall i, R i ≃+* S i) :
    (piCongrRight e).symm = piCongrRight fun i => (e i).symm :=
  rfl

@[simp]
/--
theorem `piCongrRight_trans` / 定理 `piCongrRight_trans`

English:
theorem piCongrRight_trans
  statement: {ι : Type*} {R S T : ι -> Type*}
  proof: rfl

中文:
定理 piCongrRight_trans
  结论: {ι : 类型} {R S T : ι -> 类型}
  证明: rfl
-/
theorem piCongrRight_trans {ι : Type*} {R S T : ι -> Type*}
    [forall i, NonUnitalNonAssocSemiring (R i)] [forall i, NonUnitalNonAssocSemiring (S i)]
    [forall i, NonUnitalNonAssocSemiring (T i)] (e : forall i, R i ≃+* S i) (f : forall i, S i ≃+* T i) :
    (piCongrRight e).trans (piCongrRight f) = piCongrRight fun i => (e i).trans (f i) :=
  rfl

/-- Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft'` as a `RingEquiv`. -/
@[simps!]
/--
Definition of `piCongrLeft'` / `piCongrLeft'` 的定义

English:
definition piCongrLeft'
  signature: {ι ι' : Type*} (R : ι -> Type*) (e : ι ≃ ι')
  body: Equiv.piCongrLeft' R e
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]

中文:
定义 piCongrLeft'
  签名: {ι ι' : 类型} (R : ι -> 类型) (e : ι ≃ ι')
  定义体: Equiv.piCongrLeft' R e
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]

Depends on / 依赖: Equiv.piCongrLeft, piCongrLeft
-/
def piCongrLeft' {ι ι' : Type*} (R : ι -> Type*) (e : ι ≃ ι')
    [forall i, NonUnitalNonAssocSemiring (R i)] :
    ((i : ι) -> R i) ≃+* ((i : ι') -> R (e.symm i)) where
  toEquiv := Equiv.piCongrLeft' R e
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
/--
theorem `piCongrLeft'_symm` / 定理 `piCongrLeft'_symm`

English:
theorem piCongrLeft'_symm
  given: {R : Type*} [NonUnitalNonAssocSemiring R] (e : α ≃ β)
  proof: by
  simp only [piCongrLeft', RingEquiv.symm, MulEquiv.symm, Equiv.piCongrLeft'_symm]

#adaptation_note

中文:
定理 piCongrLeft'_symm
  条件: {R : 类型} [非幺非结合半环 R] (e : α ≃ β)
  证明: by
  simp only [piCongrLeft', RingEquiv.symm, MulEquiv.symm, Equiv.piCongrLeft'_symm]

#adaptation_note
-/
theorem piCongrLeft'_symm {R : Type*} [NonUnitalNonAssocSemiring R] (e : α ≃ β) :
    (RingEquiv.piCongrLeft' (fun _ => R) e).symm = RingEquiv.piCongrLeft' _ e.symm := by
  simp only [piCongrLeft', RingEquiv.symm, MulEquiv.symm, Equiv.piCongrLeft'_symm]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft` as a `RingEquiv`. -/
@[simps!]
/--
Definition of `piCongrLeft` / `piCongrLeft` 的定义

English:
definition piCongrLeft
  signature: {ι ι' : Type*} (S : ι' -> Type*) (e : ι ≃ ι')
  body: (RingEquiv.piCongrLeft' S e.symm).symm

中文:
定义 piCongrLeft
  签名: {ι ι' : 类型} (S : ι' -> 类型) (e : ι ≃ ι')
  定义体: (RingEquiv.piCongrLeft' S e.symm).symm

Depends on / 依赖: RingEquiv, RingEquiv.piCongrLeft, e.symm, piCongrLeft
-/
def piCongrLeft {ι ι' : Type*} (S : ι' -> Type*) (e : ι ≃ ι')
    [forall i, NonUnitalNonAssocSemiring (S i)] :
    ((i : ι) -> S (e i)) ≃+* ((i : ι') -> S i) :=
  (RingEquiv.piCongrLeft' S e.symm).symm

/-- Splits the indices of ring `∀ (i : ι), Y i` along the predicate `p`. This is
`Equiv.piEquivPiSubtypeProd` as a `RingEquiv`. -/
@[simps!]
/--
Definition of `piEquivPiSubtypeProd` / `piEquivPiSubtypeProd` 的定义

English:
definition piEquivPiSubtypeProd
  signature: {ι : Type*} (p : ι -> Prop) [DecidablePred p] (Y : ι -> Type*)
  body: Equiv.piEquivPiSubtypeProd p Y
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

中文:
定义 piEquivPiSubtypeProd
  签名: {ι : 类型} (p : ι -> 命题) [DecidablePred p] (Y : ι -> 类型)
  定义体: Equiv.piEquivPiSubtypeProd p Y
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

Depends on / 依赖: Equiv.piEquivPiSubtypeProd, piEquivPiSubtypeProd
-/
def piEquivPiSubtypeProd {ι : Type*} (p : ι -> Prop) [DecidablePred p] (Y : ι -> Type*)
    [forall i, NonUnitalNonAssocSemiring (Y i)] :
    ((i : ι) -> Y i) ≃+* ((i : { x : ι // p x }) -> Y i) × ((i : { x : ι // ¬p x }) -> Y i) where
  toEquiv := Equiv.piEquivPiSubtypeProd p Y
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/--
Definition of `piMulOpposite` / `piMulOpposite` 的定义

English:
definition piMulOpposite
  signature: {ι : Type*} (S : ι -> Type*) [forall i, NonUnitalNonAssocSemiring (S i)]
  body: .op (f.unop i)
  invFun f := .op fun i => (f i).unop
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

中文:
定义 piMulOpposite
  签名: {ι : 类型} (S : ι -> 类型) [对任意 i, 非幺非结合半环 (S i)]
  定义体: .op (f.unop i)
  invFun f := .op fun i => (f i).unop
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

Depends on / 依赖: f.unop
-/
def piMulOpposite {ι : Type*} (S : ι -> Type*) [forall i, NonUnitalNonAssocSemiring (S i)] :
    (Π i, S i)ᵐᵒᵖ ≃+* Π i, (S i)ᵐᵒᵖ where
  toFun f i := .op (f.unop i)
  invFun f := .op fun i => (f i).unop
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Product of ring equivalences. This is `Equiv.prodCongr` as a `RingEquiv`. -/
@[simps!]
/--
Definition of `prodCongr` / `prodCongr` 的定义

English:
definition prodCongr
  signature: {R R' S S' : Type*} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring R']
  body: Equiv.prodCongr f g
  map_mul' _ _ := by
    simp only [Equiv.toFun_as_coe, Equiv.prodCongr_apply, EquivLike.coe_coe,
      Prod.map, map_mul, Prod.mk_mul_mk]
  map_add' _ _ := by
    simp only [Equiv.toFun_as_coe, Equiv.prodCongr_apply, EquivLike.coe_coe,
      Prod.map, map_add, Prod.mk_add_mk]

@[simp]

中文:
定义 prodCongr
  签名: {R R' S S' : 类型} [非幺非结合半环 R] [非幺非结合半环 R']
  定义体: Equiv.prodCongr f g
  map_mul' _ _ := by
    simp only [Equiv.toFun_as_coe, Equiv.prodCongr_apply, EquivLike.coe_coe,
      Prod.map, map_mul, Prod.mk_mul_mk]
  map_add' _ _ := by
    simp only [Equiv.toFun_as_coe, Equiv.prodCongr_apply, EquivLike.coe_coe,
      Prod.map, map_add, Prod.mk_add_mk]

@[simp]

Depends on / 依赖: Equiv.prodCongr, prodCongr
-/
def prodCongr {R R' S S' : Type*} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring R']
    [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']
    (f : R ≃+* R') (g : S ≃+* S') :
    R × S ≃+* R' × S' where
  toEquiv := Equiv.prodCongr f g
  map_mul' _ _ := by
    simp only [Equiv.toFun_as_coe, Equiv.prodCongr_apply, EquivLike.coe_coe,
      Prod.map, map_mul, Prod.mk_mul_mk]
  map_add' _ _ := by
    simp only [Equiv.toFun_as_coe, Equiv.prodCongr_apply, EquivLike.coe_coe,
      Prod.map, map_add, Prod.mk_add_mk]

@[simp]
/--
theorem `coe_prodCongr` / 定理 `coe_prodCongr`

English:
theorem coe_prodCongr
  statement: {R R' S S' : Type*} [NonUnitalNonAssocSemiring R]
  proof: rfl

中文:
定理 coe_prodCongr
  结论: {R R' S S' : 类型} [非幺非结合半环 R]
  证明: rfl
-/
theorem coe_prodCongr {R R' S S' : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring R'] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']
    (f : R ≃+* R') (g : S ≃+* S') :
    ⇑(RingEquiv.prodCongr f g) = Prod.map f g :=
  rfl

/-- This is `Equiv.piOptionEquivProd` as a `RingEquiv`. -/
@[simps!]
/--
Definition of `piOptionEquivProd` / `piOptionEquivProd` 的定义

English:
definition piOptionEquivProd
  signature: {ι : Type*} {R : Option ι -> Type*} [Π i, NonUnitalNonAssocSemiring (R i)]
  body: Equiv.piOptionEquivProd
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

中文:
定义 piOptionEquivProd
  签名: {ι : 类型} {R : 选项类型 ι -> 类型} [Π i, 非幺非结合半环 (R i)]
  定义体: Equiv.piOptionEquivProd
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: Equiv.piOptionEquivProd, piOptionEquivProd
-/
def piOptionEquivProd {ι : Type*} {R : Option ι -> Type*} [Π i, NonUnitalNonAssocSemiring (R i)] :
    (Π i, R i) ≃+* R none × (Π i, R (some i)) where
  toEquiv := Equiv.piOptionEquivProd
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end NonUnitalSemiring

section Semiring

variable [NonAssocSemiring R] [NonAssocSemiring S] (f : R ≃+* S) (x : R)

/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  statement: f 1 = 1
  proof: map_one f

中文:
定理 map_one
  结论: f 1 = 1
  证明: map_one f
-/
protected theorem map_one : f 1 = 1 :=
  map_one f

variable {x}

/--
theorem `map_eq_one_iff` / 定理 `map_eq_one_iff`

English:
theorem map_eq_one_iff
  statement: f x = 1 ↔ x = 1
  proof: EmbeddingLike.map_eq_one_iff

中文:
定理 map_eq_one_iff
  结论: f x = 1 ↔ x = 1
  证明: EmbeddingLike.map_eq_one_iff
-/
protected theorem map_eq_one_iff : f x = 1 ↔ x = 1 :=
  EmbeddingLike.map_eq_one_iff

/--
theorem `map_ne_one_iff` / 定理 `map_ne_one_iff`

English:
theorem map_ne_one_iff
  statement: f x != 1 ↔ x != 1
  proof: EmbeddingLike.map_ne_one_iff

中文:
定理 map_ne_one_iff
  结论: f x != 1 ↔ x != 1
  证明: EmbeddingLike.map_ne_one_iff

Depends on / 依赖: EmbeddingLike, EmbeddingLike.map_ne_one_iff, map_ne_one_iff
-/
theorem map_ne_one_iff : f x != 1 ↔ x != 1 :=
  EmbeddingLike.map_ne_one_iff

/--
theorem `coe_monoidHom_refl` / 定理 `coe_monoidHom_refl`

English:
theorem coe_monoidHom_refl
  statement: (RingEquiv.refl R : R ->* R) = MonoidHom.id R
  proof: rfl

@[simp]

中文:
定理 coe_monoidHom_refl
  结论: (环等价.refl R : R ->* R) = 幺半群态射.id R
  证明: rfl

@[simp]
-/
theorem coe_monoidHom_refl : (RingEquiv.refl R : R ->* R) = MonoidHom.id R :=
  rfl

@[simp]
/--
theorem `coe_addMonoidHom_refl` / 定理 `coe_addMonoidHom_refl`

English:
theorem coe_addMonoidHom_refl
  statement: (RingEquiv.refl R : R ->+ R) = AddMonoidHom.id R
  proof: rfl

中文:
定理 coe_addMonoidHom_refl
  结论: (环等价.refl R : R ->+ R) = 加法幺半群态射.id R
  证明: rfl
-/
theorem coe_addMonoidHom_refl : (RingEquiv.refl R : R ->+ R) = AddMonoidHom.id R :=
  rfl

/-! `RingEquiv.coe_mulEquiv_refl` and `RingEquiv.coe_addEquiv_refl` are proved above
in higher generality -/


@[simp]
/--
theorem `coe_ringHom_refl` / 定理 `coe_ringHom_refl`

English:
theorem coe_ringHom_refl
  statement: (RingEquiv.refl R : R ->+* R) = RingHom.id R
  proof: rfl

@[simp]

中文:
定理 coe_ringHom_refl
  结论: (环等价.refl R : R ->+* R) = 环态射.id R
  证明: rfl

@[simp]
-/
theorem coe_ringHom_refl : (RingEquiv.refl R : R ->+* R) = RingHom.id R :=
  rfl

@[simp]
/--
theorem `coe_monoidHom_trans` / 定理 `coe_monoidHom_trans`

English:
theorem coe_monoidHom_trans
  given: [NonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  proof: rfl

@[simp]

中文:
定理 coe_monoidHom_trans
  条件: [非结合半环 S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  证明: rfl

@[simp]
-/
theorem coe_monoidHom_trans [NonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R ->* S') = (e₂ : S ->* S').comp ↑e₁ :=
  rfl

@[simp]
/--
theorem `coe_addMonoidHom_trans` / 定理 `coe_addMonoidHom_trans`

English:
theorem coe_addMonoidHom_trans
  given: [NonUnitalNonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  proof: rfl

中文:
定理 coe_addMonoidHom_trans
  条件: [非幺非结合半环 S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  证明: rfl
-/
theorem coe_addMonoidHom_trans [NonUnitalNonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R ->+ S') = (e₂ : S ->+ S').comp ↑e₁ :=
  rfl

/-! `RingEquiv.coe_mulEquiv_trans` and `RingEquiv.coe_addEquiv_trans` are proved above
in higher generality -/

@[simp]
/--
theorem `coe_ringHom_trans` / 定理 `coe_ringHom_trans`

English:
theorem coe_ringHom_trans
  given: [NonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  proof: rfl

@[simp]

中文:
定理 coe_ringHom_trans
  条件: [非结合半环 S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  证明: rfl

@[simp]
-/
theorem coe_ringHom_trans [NonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R ->+* S') = (e₂ : S ->+* S').comp ↑e₁ :=
  rfl

@[simp]
/--
theorem `comp_symm` / 定理 `comp_symm`

English:
theorem comp_symm
  given: (e : R ≃+* S)
  statement: (e : R ->+* S).comp (e.symm : S ->+* R) = RingHom.id S
  proof: RingHom.ext e.apply_symm_apply

@[simp]

中文:
定理 comp_symm
  条件: (e : R ≃+* S)
  结论: (e : R ->+* S).comp (e.symm : S ->+* R) = 环态射.id S
  证明: RingHom.ext e.apply_symm_apply

@[simp]

Depends on / 依赖: RingHom, RingHom.ext, apply_symm_apply, e.apply_symm_apply
-/
theorem comp_symm (e : R ≃+* S) : (e : R ->+* S).comp (e.symm : S ->+* R) = RingHom.id S :=
  RingHom.ext e.apply_symm_apply

@[simp]
/--
theorem `symm_comp` / 定理 `symm_comp`

English:
theorem symm_comp
  given: (e : R ≃+* S)
  statement: (e.symm : S ->+* R).comp (e : R ->+* S) = RingHom.id R
  proof: RingHom.ext e.symm_apply_apply

中文:
定理 symm_comp
  条件: (e : R ≃+* S)
  结论: (e.symm : S ->+* R).comp (e : R ->+* S) = 环态射.id R
  证明: RingHom.ext e.symm_apply_apply

Depends on / 依赖: RingHom, RingHom.ext, e.symm_apply_apply, symm_apply_apply
-/
theorem symm_comp (e : R ≃+* S) : (e.symm : S ->+* R).comp (e : R ->+* S) = RingHom.id R :=
  RingHom.ext e.symm_apply_apply

end Semiring

section NonUnitalRing

variable [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] (f : R ≃+* S) (x y : R)

/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  statement: f (-x) = -f x
  proof: map_neg f x

中文:
定理 map_neg
  结论: f (-x) = -f x
  证明: map_neg f x
-/
protected theorem map_neg : f (-x) = -f x :=
  map_neg f x

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  statement: f (x - y) = f x - f y
  proof: map_sub f x y

中文:
定理 map_sub
  结论: f (x - y) = f x - f y
  证明: map_sub f x y
-/
protected theorem map_sub : f (x - y) = f x - f y :=
  map_sub f x y

end NonUnitalRing

section Ring

variable [NonAssocRing R] [NonAssocRing S] (f : R ≃+* S)

@[simp]
/--
theorem `map_neg_one` / 定理 `map_neg_one`

English:
theorem map_neg_one
  statement: f (-1) = -1
  proof: f.map_one ▸ f.map_neg 1

中文:
定理 map_neg_one
  结论: f (-1) = -1
  证明: f.map_one ▸ f.map_neg 1

Depends on / 依赖: f.map_neg, f.map_one, map_neg, map_one
-/
theorem map_neg_one : f (-1) = -1 :=
  f.map_one ▸ f.map_neg 1

/--
theorem `map_eq_neg_one_iff` / 定理 `map_eq_neg_one_iff`

English:
theorem map_eq_neg_one_iff
  given: {x : R}
  statement: f x = -1 ↔ x = -1
  proof: by
  rw [← neg_eq_iff_eq_neg]; rw [← neg_eq_iff_eq_neg]; rw [← map_neg]; rw [RingEquiv.map_eq_one_iff]

中文:
定理 map_eq_neg_one_iff
  条件: {x : R}
  结论: f x = -1 ↔ x = -1
  证明: by
  rw [← neg_eq_iff_eq_neg]; rw [← neg_eq_iff_eq_neg]; rw [← map_neg]; rw [RingEquiv.map_eq_one_iff]

Depends on / 依赖: RingEquiv, RingEquiv.map_eq_one_iff, map_eq_one_iff, map_neg, neg_eq_iff_eq_neg
-/
theorem map_eq_neg_one_iff {x : R} : f x = -1 ↔ x = -1 := by
  rw [← neg_eq_iff_eq_neg]; rw [← neg_eq_iff_eq_neg]; rw [← map_neg]; rw [RingEquiv.map_eq_one_iff]

end Ring

section NonUnitalSemiringHom

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']

/--
Definition of `toNonUnitalRingHom` / `toNonUnitalRingHom` 的定义

English:
definition toNonUnitalRingHom
  signature: (e : R ≃+* S)
  body: { e.toMulEquiv.toMulHom, e.toAddEquiv.toAddMonoidHom with }

中文:
定义 toNonUnitalRingHom
  签名: (e : R ≃+* S)
  定义体: { e.toMulEquiv.toMulHom, e.toAddEquiv.toAddMonoidHom with }

Depends on / 依赖: e.toAddEquiv.toAddMonoidHom, e.toMulEquiv.toMulHom, toAddEquiv, toAddMonoidHom, toMulEquiv, toMulHom
-/
def toNonUnitalRingHom (e : R ≃+* S) : R ->ₙ+* S :=
  { e.toMulEquiv.toMulHom, e.toAddEquiv.toAddMonoidHom with }

/--
theorem `toNonUnitalRingHom_injective` / 定理 `toNonUnitalRingHom_injective`

English:
theorem toNonUnitalRingHom_injective
  proof: fun _ _ h =>
  RingEquiv.ext (NonUnitalRingHom.ext_iff.1 h)

中文:
定理 toNonUnitalRingHom_injective
  证明: fun _ _ h =>
  RingEquiv.ext (NonUnitalRingHom.ext_iff.1 h)
-/
theorem toNonUnitalRingHom_injective :
    Function.Injective (toNonUnitalRingHom : R ≃+* S -> R ->ₙ+* S) := fun _ _ h =>
  RingEquiv.ext (NonUnitalRingHom.ext_iff.1 h)

/--
theorem `toNonUnitalRingHom_eq_coe` / 定理 `toNonUnitalRingHom_eq_coe`

English:
theorem toNonUnitalRingHom_eq_coe
  given: (f : R ≃+* S)
  statement: f.toNonUnitalRingHom = ↑f
  proof: rfl

@[simp, norm_cast]

中文:
定理 toNonUnitalRingHom_eq_coe
  条件: (f : R ≃+* S)
  结论: f.toNonUnitalRingHom = ↑f
  证明: rfl

@[simp, norm_cast]
-/
theorem toNonUnitalRingHom_eq_coe (f : R ≃+* S) : f.toNonUnitalRingHom = ↑f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_toNonUnitalRingHom` / 定理 `coe_toNonUnitalRingHom`

English:
theorem coe_toNonUnitalRingHom
  given: (f : R ≃+* S)
  statement: ⇑(f : R ->ₙ+* S) = f
  proof: rfl

@[simp]

中文:
定理 coe_toNonUnitalRingHom
  条件: (f : R ≃+* S)
  结论: ⇑(f : R ->ₙ+* S) = f
  证明: rfl

@[simp]
-/
theorem coe_toNonUnitalRingHom (f : R ≃+* S) : ⇑(f : R ->ₙ+* S) = f :=
  rfl

@[simp]
/--
theorem `coe_toNonUnitalRingHom'` / 定理 `coe_toNonUnitalRingHom'`

English:
theorem coe_toNonUnitalRingHom'
  given: (f : R ≃+* S)
  statement: ⇑f.toNonUnitalRingHom = f
  proof: rfl

中文:
定理 coe_toNonUnitalRingHom'
  条件: (f : R ≃+* S)
  结论: ⇑f.toNonUnitalRingHom = f
  证明: rfl
-/
theorem coe_toNonUnitalRingHom' (f : R ≃+* S) : ⇑f.toNonUnitalRingHom = f :=
  rfl

/--
theorem `coe_nonUnitalRingHom_inj_iff` / 定理 `coe_nonUnitalRingHom_inj_iff`

English:
theorem coe_nonUnitalRingHom_inj_iff
  statement: {R S : Type*} [NonUnitalNonAssocSemiring R]
  proof: ⟨fun h => by rw [h], fun h => ext NonUnitalRingHom.ext_iff.mp h⟩

@[simp]

中文:
定理 coe_nonUnitalRingHom_inj_iff
  结论: {R S : 类型} [非幺非结合半环 R]
  证明: ⟨fun h => by rw [h], fun h => ext NonUnitalRingHom.ext_iff.mp h⟩

@[simp]

Depends on / 依赖: NonUnitalRingHom, NonUnitalRingHom.ext_iff.mp, ext_iff
-/
theorem coe_nonUnitalRingHom_inj_iff {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f g : R ≃+* S) : f = g ↔ (f : R ->ₙ+* S) = g :=
⟨fun h => by rw [h], fun h => ext NonUnitalRingHom.ext_iff.mp h⟩

@[simp]
/--
theorem `toNonUnitalRingHom_refl` / 定理 `toNonUnitalRingHom_refl`

English:
theorem toNonUnitalRingHom_refl
  proof: rfl

@[deprecated apply_symm_apply (since := "2026-06-16")]

中文:
定理 toNonUnitalRingHom_refl
  证明: rfl

@[deprecated apply_symm_apply (since := "2026-06-16")]
-/
theorem toNonUnitalRingHom_refl :
    (RingEquiv.refl R).toNonUnitalRingHom = NonUnitalRingHom.id R :=
  rfl

@[deprecated apply_symm_apply (since := "2026-06-16")]
/--
theorem `toNonUnitalRingHom_apply_symm_toNonUnitalRingHom_apply` / 定理 `toNonUnitalRingHom_apply_symm_toNonUnitalRingHom_apply`

English:
theorem toNonUnitalRingHom_apply_symm_toNonUnitalRingHom_apply
  given: (e : R ≃+* S)
  proof: e.toEquiv.apply_symm_apply

@[deprecated symm_apply_apply (since := "2026-06-16")]

中文:
定理 toNonUnitalRingHom_apply_symm_toNonUnitalRingHom_apply
  条件: (e : R ≃+* S)
  证明: e.toEquiv.apply_symm_apply

@[deprecated symm_apply_apply (since := "2026-06-16")]

Depends on / 依赖: IsLocallyArtinian, IsLocallyArtinian.discreteTopology, apply_symm_apply, discreteTopology, e.toEquiv.apply_symm_apply, toEquiv
-/
theorem toNonUnitalRingHom_apply_symm_toNonUnitalRingHom_apply (e : R ≃+* S) :
    forall y : S, e.toNonUnitalRingHom (e.symm.toNonUnitalRingHom y) = y :=
  e.toEquiv.apply_symm_apply

@[deprecated symm_apply_apply (since := "2026-06-16")]
/--
theorem `symm_toNonUnitalRingHom_apply_toNonUnitalRingHom_apply` / 定理 `symm_toNonUnitalRingHom_apply_toNonUnitalRingHom_apply`

English:
theorem symm_toNonUnitalRingHom_apply_toNonUnitalRingHom_apply
  given: (e : R ≃+* S)
  proof: Equiv.symm_apply_apply e.toEquiv

@[simp]

中文:
定理 symm_toNonUnitalRingHom_apply_toNonUnitalRingHom_apply
  条件: (e : R ≃+* S)
  证明: Equiv.symm_apply_apply e.toEquiv

@[simp]

Depends on / 依赖: Equiv.symm_apply_apply, e.toEquiv, symm_apply_apply, toEquiv
-/
theorem symm_toNonUnitalRingHom_apply_toNonUnitalRingHom_apply (e : R ≃+* S) :
    forall x : R, e.symm.toNonUnitalRingHom (e.toNonUnitalRingHom x) = x :=
  Equiv.symm_apply_apply e.toEquiv

@[simp]
/--
theorem `toNonUnitalRingHom_trans` / 定理 `toNonUnitalRingHom_trans`

English:
theorem toNonUnitalRingHom_trans
  given: (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  proof: rfl

@[simp]

中文:
定理 toNonUnitalRingHom_trans
  条件: (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  证明: rfl

@[simp]
-/
theorem toNonUnitalRingHom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂).toNonUnitalRingHom = e₂.toNonUnitalRingHom.comp e₁.toNonUnitalRingHom :=
  rfl

@[simp]
/--
theorem `toNonUnitalRingHomm_comp_symm_toNonUnitalRingHom` / 定理 `toNonUnitalRingHomm_comp_symm_toNonUnitalRingHom`

English:
theorem toNonUnitalRingHomm_comp_symm_toNonUnitalRingHom
  given: (e : R ≃+* S)
  proof: by
  ext
  simp

@[simp]

中文:
定理 toNonUnitalRingHomm_comp_symm_toNonUnitalRingHom
  条件: (e : R ≃+* S)
  证明: by
  ext
  simp

@[simp]
-/
theorem toNonUnitalRingHomm_comp_symm_toNonUnitalRingHom (e : R ≃+* S) :
    e.toNonUnitalRingHom.comp e.symm.toNonUnitalRingHom = NonUnitalRingHom.id _ := by
  ext
  simp

@[simp]
/--
theorem `symm_toNonUnitalRingHom_comp_toNonUnitalRingHom` / 定理 `symm_toNonUnitalRingHom_comp_toNonUnitalRingHom`

English:
theorem symm_toNonUnitalRingHom_comp_toNonUnitalRingHom
  given: (e : R ≃+* S)
  proof: by
  ext
  simp

中文:
定理 symm_toNonUnitalRingHom_comp_toNonUnitalRingHom
  条件: (e : R ≃+* S)
  证明: by
  ext
  simp
-/
theorem symm_toNonUnitalRingHom_comp_toNonUnitalRingHom (e : R ≃+* S) :
    e.symm.toNonUnitalRingHom.comp e.toNonUnitalRingHom = NonUnitalRingHom.id _ := by
  ext
  simp

end NonUnitalSemiringHom

section SemiringHom

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring S']

/--
Definition of `toRingHom` / `toRingHom` 的定义

English:
definition toRingHom
  signature: (e : R ≃+* S)
  body: { e.toMulEquiv.toMonoidHom, e.toAddEquiv.toAddMonoidHom with }

中文:
定义 toRingHom
  签名: (e : R ≃+* S)
  定义体: { e.toMulEquiv.toMonoidHom, e.toAddEquiv.toAddMonoidHom with }

Depends on / 依赖: IsEmpty, IsLocallyArtinian, Scheme, e.toAddEquiv.toAddMonoidHom, e.toMulEquiv.toMonoidHom, toAddEquiv, toAddMonoidHom, toMonoidHom, toMulEquiv
-/
def toRingHom (e : R ≃+* S) : R ->+* S :=
  { e.toMulEquiv.toMonoidHom, e.toAddEquiv.toAddMonoidHom with }

/--
theorem `toRingHom_injective` / 定理 `toRingHom_injective`

English:
theorem toRingHom_injective
  statement: Function.Injective (toRingHom : R ≃+* S -> R ->+* S)
  proof: fun _ _ h =>
  RingEquiv.ext (RingHom.ext_iff.1 h)

中文:
定理 toRingHom_injective
  结论: 函数.单射 (toRingHom : R ≃+* S -> R ->+* S)
  证明: fun _ _ h =>
  RingEquiv.ext (RingHom.ext_iff.1 h)

Depends on / 依赖: DiscreteTopology, IsReduced, Scheme
-/
theorem toRingHom_injective : Function.Injective (toRingHom : R ≃+* S -> R ->+* S) := fun _ _ h =>
  RingEquiv.ext (RingHom.ext_iff.1 h)

/--
theorem `toRingHom_eq_coe` / 定理 `toRingHom_eq_coe`

English:
theorem toRingHom_eq_coe
  given: (f : R ≃+* S)
  statement: f.toRingHom = ↑f
  proof: rfl

@[simp, norm_cast]

中文:
定理 toRingHom_eq_coe
  条件: (f : R ≃+* S)
  结论: f.toRingHom = ↑f
  证明: rfl

@[simp, norm_cast]

Depends on / 依赖: IsArtinianScheme, IsArtinianScheme.finite, finite
-/
@[simp] theorem toRingHom_eq_coe (f : R ≃+* S) : f.toRingHom = ↑f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_toRingHom` / 定理 `coe_toRingHom`

English:
theorem coe_toRingHom
  given: (f : R ≃+* S)
  statement: ⇑(f : R ->+* S) = f
  proof: rfl

中文:
定理 coe_toRingHom
  条件: (f : R ≃+* S)
  结论: ⇑(f : R ->+* S) = f
  证明: rfl

Depends on / 依赖: IsArtinianScheme, IsArtinianScheme.isNoetherianScheme, isNoetherianScheme
-/
theorem coe_toRingHom (f : R ≃+* S) : ⇑(f : R ->+* S) = f :=
  rfl

/--
theorem `coe_ringHom_inj_iff` / 定理 `coe_ringHom_inj_iff`

English:
theorem coe_ringHom_inj_iff
  statement: {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
  proof: ⟨fun h => by rw [h], fun h => ext RingHom.ext_iff.mp h⟩

中文:
定理 coe_ringHom_inj_iff
  结论: {R S : 类型} [非结合半环 R] [非结合半环 S]
  证明: ⟨fun h => by rw [h], fun h => ext RingHom.ext_iff.mp h⟩

Depends on / 依赖: RingHom, RingHom.ext_iff.mp, ext_iff
-/
theorem coe_ringHom_inj_iff {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f g : R ≃+* S) : f = g ↔ (f : R ->+* S) = g :=
⟨fun h => by rw [h], fun h => ext RingHom.ext_iff.mp h⟩

/-- The two paths coercion can take to a `NonUnitalRingEquiv` are equivalent -/
@[simp, norm_cast]
/--
theorem `toNonUnitalRingHom_commutes` / 定理 `toNonUnitalRingHom_commutes`

English:
theorem toNonUnitalRingHom_commutes
  given: (f : R ≃+* S)
  proof: rfl

中文:
定理 toNonUnitalRingHom_commutes
  条件: (f : R ≃+* S)
  证明: rfl

Depends on / 依赖: DiscreteTopology, IsArtinianScheme, IsArtinianScheme.iff_isNoetherian_and_discreteTopology.mpr, PrimeSpectrum, iff_isNoetherian_and_discreteTopology
-/
theorem toNonUnitalRingHom_commutes (f : R ≃+* S) :
    ((f : R ->+* S) : R ->ₙ+* S) = (f : R ->ₙ+* S) :=
  rfl

/--
Definition of `toMonoidHom` / `toMonoidHom` 的定义

English:
abbreviation toMonoidHom
  signature: (e : R ≃+* S)
  body: e.toRingHom.toMonoidHom

中文:
缩写 toMonoidHom
  签名: (e : R ≃+* S)
  定义体: e.toRingHom.toMonoidHom

Depends on / 依赖: IsReduced, Scheme, Subsingleton, e.toRingHom.toMonoidHom, toMonoidHom, toRingHom
-/
abbrev toMonoidHom (e : R ≃+* S) : R ->* S :=
  e.toRingHom.toMonoidHom

/--
Definition of `toAddMonoidHom` / `toAddMonoidHom` 的定义

English:
abbreviation toAddMonoidHom
  signature: (e : R ≃+* S)
  body: e.toRingHom.toAddMonoidHom

中文:
缩写 toAddMonoidHom
  签名: (e : R ≃+* S)
  定义体: e.toRingHom.toAddMonoidHom

Depends on / 依赖: e.toRingHom.toAddMonoidHom, toAddMonoidHom, toRingHom
-/
abbrev toAddMonoidHom (e : R ≃+* S) : R ->+ S :=
  e.toRingHom.toAddMonoidHom

/--
theorem `toAddMonoidMom_commutes` / 定理 `toAddMonoidMom_commutes`

English:
theorem toAddMonoidMom_commutes
  given: (f : R ≃+* S)
  proof: rfl

中文:
定理 toAddMonoidMom_commutes
  条件: (f : R ≃+* S)
  证明: rfl
-/
theorem toAddMonoidMom_commutes (f : R ≃+* S) :
    (f : R ->+* S).toAddMonoidHom = (f : R ≃+ S).toAddMonoidHom :=
  rfl

/--
theorem `toMonoidHom_commutes` / 定理 `toMonoidHom_commutes`

English:
theorem toMonoidHom_commutes
  given: (f : R ≃+* S)
  proof: rfl

中文:
定理 toMonoidHom_commutes
  条件: (f : R ≃+* S)
  证明: rfl
-/
theorem toMonoidHom_commutes (f : R ≃+* S) :
    (f : R ->+* S).toMonoidHom = (f : R ≃* S).toMonoidHom :=
  rfl

/--
theorem `toEquiv_commutes` / 定理 `toEquiv_commutes`

English:
theorem toEquiv_commutes
  given: (f : R ≃+* S)
  statement: (f : R ≃+ S).toEquiv = (f : R ≃* S).toEquiv
  proof: rfl

@[simp]

中文:
定理 toEquiv_commutes
  条件: (f : R ≃+* S)
  结论: (f : R ≃+ S).toEquiv = (f : R ≃* S).toEquiv
  证明: rfl

@[simp]
-/
theorem toEquiv_commutes (f : R ≃+* S) : (f : R ≃+ S).toEquiv = (f : R ≃* S).toEquiv :=
  rfl

@[simp]
/--
theorem `toRingHom_refl` / 定理 `toRingHom_refl`

English:
theorem toRingHom_refl
  statement: (RingEquiv.refl R).toRingHom = RingHom.id R
  proof: rfl

@[simp]

中文:
定理 toRingHom_refl
  结论: (环等价.refl R).toRingHom = 环态射.id R
  证明: rfl

@[simp]
-/
theorem toRingHom_refl : (RingEquiv.refl R).toRingHom = RingHom.id R :=
  rfl

@[simp]
/--
theorem `toMonoidHom_refl` / 定理 `toMonoidHom_refl`

English:
theorem toMonoidHom_refl
  statement: (RingEquiv.refl R).toMonoidHom = MonoidHom.id R
  proof: rfl

@[simp]

中文:
定理 toMonoidHom_refl
  结论: (环等价.refl R).toMonoidHom = 幺半群态射.id R
  证明: rfl

@[simp]
-/
theorem toMonoidHom_refl : (RingEquiv.refl R).toMonoidHom = MonoidHom.id R :=
  rfl

@[simp]
/--
theorem `toAddMonoidHom_refl` / 定理 `toAddMonoidHom_refl`

English:
theorem toAddMonoidHom_refl
  statement: (RingEquiv.refl R).toAddMonoidHom = AddMonoidHom.id R
  proof: rfl

中文:
定理 toAddMonoidHom_refl
  结论: (环等价.refl R).toAddMonoidHom = 加法幺半群态射.id R
  证明: rfl
-/
theorem toAddMonoidHom_refl : (RingEquiv.refl R).toAddMonoidHom = AddMonoidHom.id R :=
  rfl

/--
theorem `toRingHom_apply_symm_toRingHom_apply` / 定理 `toRingHom_apply_symm_toRingHom_apply`

English:
theorem toRingHom_apply_symm_toRingHom_apply
  given: (e : R ≃+* S)
  proof: e.toEquiv.apply_symm_apply

中文:
定理 toRingHom_apply_symm_toRingHom_apply
  条件: (e : R ≃+* S)
  证明: e.toEquiv.apply_symm_apply

Depends on / 依赖: apply_symm_apply, e.toEquiv.apply_symm_apply, toEquiv
-/
theorem toRingHom_apply_symm_toRingHom_apply (e : R ≃+* S) :
    forall y : S, e.toRingHom (e.symm.toRingHom y) = y :=
  e.toEquiv.apply_symm_apply

/--
theorem `symm_toRingHom_apply_toRingHom_apply` / 定理 `symm_toRingHom_apply_toRingHom_apply`

English:
theorem symm_toRingHom_apply_toRingHom_apply
  given: (e : R ≃+* S)
  proof: Equiv.symm_apply_apply e.toEquiv

@[simp]

中文:
定理 symm_toRingHom_apply_toRingHom_apply
  条件: (e : R ≃+* S)
  证明: Equiv.symm_apply_apply e.toEquiv

@[simp]

Depends on / 依赖: Equiv.symm_apply_apply, e.toEquiv, symm_apply_apply, toEquiv
-/
theorem symm_toRingHom_apply_toRingHom_apply (e : R ≃+* S) :
    forall x : R, e.symm.toRingHom (e.toRingHom x) = x :=
  Equiv.symm_apply_apply e.toEquiv

@[simp]
/--
theorem `toRingHom_trans` / 定理 `toRingHom_trans`

English:
theorem toRingHom_trans
  given: (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  proof: rfl

中文:
定理 toRingHom_trans
  条件: (e₁ : R ≃+* S) (e₂ : S ≃+* S')
  证明: rfl
-/
theorem toRingHom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂).toRingHom = e₂.toRingHom.comp e₁.toRingHom :=
  rfl

/--
theorem `toRingHom_comp_symm_toRingHom` / 定理 `toRingHom_comp_symm_toRingHom`

English:
theorem toRingHom_comp_symm_toRingHom
  given: (e : R ≃+* S)
  proof: by
  simp

中文:
定理 toRingHom_comp_symm_toRingHom
  条件: (e : R ≃+* S)
  证明: by
  simp
-/
theorem toRingHom_comp_symm_toRingHom (e : R ≃+* S) :
    e.toRingHom.comp e.symm.toRingHom = RingHom.id _ := by
  simp

/--
theorem `symm_toRingHom_comp_toRingHom` / 定理 `symm_toRingHom_comp_toRingHom`

English:
theorem symm_toRingHom_comp_toRingHom
  given: (e : R ≃+* S)
  proof: by
  simp

中文:
定理 symm_toRingHom_comp_toRingHom
  条件: (e : R ≃+* S)
  证明: by
  simp
-/
theorem symm_toRingHom_comp_toRingHom (e : R ≃+* S) :
    e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := by
  simp

end SemiringHom

variable [Semiring R] [Semiring S]

section GroupPower

/--
theorem `map_pow` / 定理 `map_pow`

English:
theorem map_pow
  given: (f : R ≃+* S) (a)
  statement: forall n : Nat, f (a ^ n) = f a ^ n
  proof: map_pow f a

中文:
定理 map_pow
  条件: (f : R ≃+* S) (a)
  结论: 对任意 n : 自然数, f (a ^ n) = f a ^ n
  证明: map_pow f a
-/
protected theorem map_pow (f : R ≃+* S) (a) : forall n : Nat, f (a ^ n) = f a ^ n :=
  map_pow f a

end GroupPower

end RingEquiv

namespace MulEquiv

/--
Definition of `toRingEquiv` / `toRingEquiv` 的定义

English:
definition toRingEquiv
  signature: {R S F : Type*} [Add R] [Add S] [Mul R] [Mul S] [EquivLike F R S]
  body: { (f : R ≃* S).toEquiv, (f : R ≃* S), AddEquiv.mk' (f : R ≃* S).toEquiv H with }

中文:
定义 toRingEquiv
  签名: {R S F : 类型} [加法 R] [加法 S] [乘法 R] [乘法 S] [等价状 F R S]
  定义体: { (f : R ≃* S).toEquiv, (f : R ≃* S), AddEquiv.mk' (f : R ≃* S).toEquiv H with }

Depends on / 依赖: AddEquiv, AddEquiv.mk, toEquiv
-/
def toRingEquiv {R S F : Type*} [Add R] [Add S] [Mul R] [Mul S] [EquivLike F R S]
    [MulEquivClass F R S] (f : F)
    (H : forall x y : R, f (x + y) = f x + f y) : R ≃+* S :=
  { (f : R ≃* S).toEquiv, (f : R ≃* S), AddEquiv.mk' (f : R ≃* S).toEquiv H with }

end MulEquiv

namespace AddEquiv

/--
Definition of `toRingEquiv` / `toRingEquiv` 的定义

English:
definition toRingEquiv
  signature: {R S F : Type*} [Add R] [Add S] [Mul R] [Mul S] [EquivLike F R S]
  body: { (f : R ≃+ S).toEquiv, (f : R ≃+ S), MulEquiv.mk' (f : R ≃+ S).toEquiv H with }

中文:
定义 toRingEquiv
  签名: {R S F : 类型} [加法 R] [加法 S] [乘法 R] [乘法 S] [等价状 F R S]
  定义体: { (f : R ≃+ S).toEquiv, (f : R ≃+ S), MulEquiv.mk' (f : R ≃+ S).toEquiv H with }

Depends on / 依赖: MulEquiv, MulEquiv.mk, toEquiv
-/
def toRingEquiv {R S F : Type*} [Add R] [Add S] [Mul R] [Mul S] [EquivLike F R S]
    [AddEquivClass F R S] (f : F)
    (H : forall x y : R, f (x * y) = f x * f y) : R ≃+* S :=
  { (f : R ≃+ S).toEquiv, (f : R ≃+ S), MulEquiv.mk' (f : R ≃+ S).toEquiv H with }

end AddEquiv

namespace RingEquiv

variable [Add R] [Add S] [Mul R] [Mul S]

@[simp]
/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (e : R ≃+* S)
  statement: e.trans e.symm = RingEquiv.refl R
  proof: ext e.left_inv

@[simp]

中文:
定理 self_trans_symm
  条件: (e : R ≃+* S)
  结论: e.trans e.symm = 环等价.refl R
  证明: ext e.left_inv

@[simp]

Depends on / 依赖: e.left_inv, left_inv
-/
theorem self_trans_symm (e : R ≃+* S) : e.trans e.symm = RingEquiv.refl R :=
  ext e.left_inv

@[simp]
/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (e : R ≃+* S)
  statement: e.symm.trans e = RingEquiv.refl S
  proof: ext e.right_inv

中文:
定理 symm_trans_self
  条件: (e : R ≃+* S)
  结论: e.symm.trans e = 环等价.refl S
  证明: ext e.right_inv

Depends on / 依赖: e.right_inv, right_inv
-/
theorem symm_trans_self (e : R ≃+* S) : e.symm.trans e = RingEquiv.refl S :=
  ext e.right_inv

end RingEquiv

namespace RingEquiv

section NonUnital

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

/-- If a non-unital ring homomorphism has an inverse, it is a ring isomorphism. -/
@[simps -isSimp]
/--
Definition of `ofNonUnitalRingHom` / `ofNonUnitalRingHom` 的定义

English:
definition ofNonUnitalRingHom
  signature: (hom : R ->ₙ+* S) (inv : S ->ₙ+* R)
  body: hom
  invFun := inv
  left_inv := DFunLike.congr_fun hom_inv_id
  right_inv := DFunLike.congr_fun inv_hom_id
  map_mul' := map_mul hom
  map_add' := map_add hom

中文:
定义 ofNonUnitalRingHom
  签名: (hom : R ->ₙ+* S) (inv : S ->ₙ+* R)
  定义体: hom
  invFun := inv
  left_inv := DFunLike.congr_fun hom_inv_id
  right_inv := DFunLike.congr_fun inv_hom_id
  map_mul' := map_mul hom
  map_add' := map_add hom
-/
def ofNonUnitalRingHom (hom : R ->ₙ+* S) (inv : S ->ₙ+* R)
    (hom_inv_id : inv.comp hom = .id R) (inv_hom_id : hom.comp inv = .id S) :
    R ≃+* S where
  toFun := hom
  invFun := inv
  left_inv := DFunLike.congr_fun hom_inv_id
  right_inv := DFunLike.congr_fun inv_hom_id
  map_mul' := map_mul hom
  map_add' := map_add hom

attribute [simp] ofNonUnitalRingHom_apply

@[simp]
/--
theorem `symm_ofNonUnitalRingHom` / 定理 `symm_ofNonUnitalRingHom`

English:
theorem symm_ofNonUnitalRingHom
  given: (f : R ->ₙ+* S) (g : S ->ₙ+* R) (h₁ h₂)
  proof: rfl

中文:
定理 symm_ofNonUnitalRingHom
  条件: (f : R ->ₙ+* S) (g : S ->ₙ+* R) (h₁ h₂)
  证明: rfl
-/
theorem symm_ofNonUnitalRingHom (f : R ->ₙ+* S) (g : S ->ₙ+* R) (h₁ h₂) :
    (ofNonUnitalRingHom f g h₁ h₂).symm = ofNonUnitalRingHom g f h₂ h₁ :=
  rfl

end NonUnital

section Unital

variable [NonAssocSemiring R] [NonAssocSemiring S]

/-- If a ring homomorphism has an inverse, it is a ring isomorphism. -/
@[simps -isSimp]
/--
Definition of `ofRingHom` / `ofRingHom` 的定义

English:
definition ofRingHom
  signature: (f : R ->+* S) (g : S ->+* R) (h₁ : f.comp g = RingHom.id S)
  body: { f with
    toFun := f
    invFun := g
    left_inv := RingHom.ext_iff.1 h₂
    right_inv := RingHom.ext_iff.1 h₁ }

中文:
定义 ofRingHom
  签名: (f : R ->+* S) (g : S ->+* R) (h₁ : f.comp g = 环态射.id S)
  定义体: { f with
    toFun := f
    invFun := g
    left_inv := RingHom.ext_iff.1 h₂
    right_inv := RingHom.ext_iff.1 h₁ }

Depends on / 依赖: RingHom, RingHom.ext_iff, ext_iff, invFun, left_inv, right_inv
-/
def ofRingHom (f : R ->+* S) (g : S ->+* R) (h₁ : f.comp g = RingHom.id S)
    (h₂ : g.comp f = RingHom.id R) : R ≃+* S :=
  { f with
    toFun := f
    invFun := g
    left_inv := RingHom.ext_iff.1 h₂
    right_inv := RingHom.ext_iff.1 h₁ }

attribute [simp] ofRingHom_apply

/--
theorem `coe_ringHom_ofRingHom` / 定理 `coe_ringHom_ofRingHom`

English:
theorem coe_ringHom_ofRingHom
  given: (f : R ->+* S) (g : S ->+* R) (h₁ h₂)
  statement: ofRingHom f g h₁ h₂ = f
  proof: rfl

@[simp]

中文:
定理 coe_ringHom_ofRingHom
  条件: (f : R ->+* S) (g : S ->+* R) (h₁ h₂)
  结论: ofRingHom f g h₁ h₂ = f
  证明: rfl

@[simp]
-/
theorem coe_ringHom_ofRingHom (f : R ->+* S) (g : S ->+* R) (h₁ h₂) : ofRingHom f g h₁ h₂ = f :=
  rfl

@[simp]
/--
theorem `ofRingHom_coe_ringHom` / 定理 `ofRingHom_coe_ringHom`

English:
theorem ofRingHom_coe_ringHom
  given: (f : R ≃+* S) (g : S ->+* R) (h₁ h₂)
  statement: ofRingHom (↑f) g h₁ h₂ = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 ofRingHom_coe_ringHom
  条件: (f : R ≃+* S) (g : S ->+* R) (h₁ h₂)
  结论: ofRingHom (↑f) g h₁ h₂ = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem ofRingHom_coe_ringHom (f : R ≃+* S) (g : S ->+* R) (h₁ h₂) : ofRingHom (↑f) g h₁ h₂ = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `ofRingHom_symm` / 定理 `ofRingHom_symm`

English:
theorem ofRingHom_symm
  given: (f : R ->+* S) (g : S ->+* R) (h₁ h₂)
  proof: rfl

中文:
定理 ofRingHom_symm
  条件: (f : R ->+* S) (g : S ->+* R) (h₁ h₂)
  证明: rfl

Depends on / 依赖: f.fiber
-/
theorem ofRingHom_symm (f : R ->+* S) (g : S ->+* R) (h₁ h₂) :
    (ofRingHom f g h₁ h₂).symm = ofRingHom g f h₂ h₁ :=
  rfl

variable (α β R) in
/--
Definition of `sumArrowEquivProdArrow` / `sumArrowEquivProdArrow` 的定义

English:
definition sumArrowEquivProdArrow
  signature: : (α oplus β -> R) ≃+* (α -> R) × (β -> R) where
  body: Equiv.sumArrowEquivProdArrow α β R
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

中文:
定义 sumArrowEquivProdArrow
  签名: : (α oplus β -> R) ≃+* (α -> R) × (β -> R) where
  定义体: Equiv.sumArrowEquivProdArrow α β R
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

Depends on / 依赖: Equiv.sumArrowEquivProdArrow, sumArrowEquivProdArrow
-/
def sumArrowEquivProdArrow : (α oplus β -> R) ≃+* (α -> R) × (β -> R) where
  __ := Equiv.sumArrowEquivProdArrow α β R
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/--
lemma `sumArrowEquivProdArrow_apply` / 引理 `sumArrowEquivProdArrow_apply`

English:
lemma sumArrowEquivProdArrow_apply
  given: (x)
  proof: rfl

中文:
引理 sumArrowEquivProdArrow_apply
  条件: (x)
  证明: rfl
-/
lemma sumArrowEquivProdArrow_apply (x) :
    sumArrowEquivProdArrow α β R x = Equiv.sumArrowEquivProdArrow α β R x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/--
lemma `sumArrowEquivProdArrow_symm_apply` / 引理 `sumArrowEquivProdArrow_symm_apply`

English:
lemma sumArrowEquivProdArrow_symm_apply
  given: (x : (α -> R) × (β -> R))
  proof: rfl

中文:
引理 sumArrowEquivProdArrow_symm_apply
  条件: (x : (α -> R) × (β -> R))
  证明: rfl
-/
lemma sumArrowEquivProdArrow_symm_apply (x : (α -> R) × (β -> R)) :
    (sumArrowEquivProdArrow α β R).symm x = (Equiv.sumArrowEquivProdArrow α β R).symm x := rfl

end Unital

end RingEquiv

namespace MulEquiv

/--
theorem `noZeroDivisors` / 定理 `noZeroDivisors`

English:
theorem noZeroDivisors
  statement: {A : Type*} (B : Type*) [MulZeroClass A] [MulZeroClass B]
  proof: e.injective.noZeroDivisors e (map_zero e) (map_mul e)

中文:
定理 noZeroDivisors
  结论: {A : 类型} (B : 类型) [乘零类 A] [乘零类 B]
  证明: e.injective.noZeroDivisors e (map_zero e) (map_mul e)
-/
protected theorem noZeroDivisors {A : Type*} (B : Type*) [MulZeroClass A] [MulZeroClass B]
    [NoZeroDivisors B] (e : A ≃* B) : NoZeroDivisors A :=
  e.injective.noZeroDivisors e (map_zero e) (map_mul e)

/--
theorem `isDomain` / 定理 `isDomain`

English:
theorem isDomain
  statement: {A : Type*} (B : Type*) [Semiring A] [Semiring B] [IsDomain B]
  proof: { e.injective.isLeftCancelMulZero e (map_zero e) (map_mul e),
    e.injective.isRightCancelMulZero e (map_zero e) (map_mul e) with
    exists_pair_ne := ⟨e.symm 0, e.symm 1, e.symm.injective.ne zero_ne_one⟩ }

中文:
定理 isDomain
  结论: {A : 类型} (B : 类型) [半环 A] [半环 B] [是整环 B]
  证明: { e.injective.isLeftCancelMulZero e (map_zero e) (map_mul e),
    e.injective.isRightCancelMulZero e (map_zero e) (map_mul e) with
    exists_pair_ne := ⟨e.symm 0, e.symm 1, e.symm.injective.ne zero_ne_one⟩ }
-/
protected theorem isDomain {A : Type*} (B : Type*) [Semiring A] [Semiring B] [IsDomain B]
    (e : A ≃* B) : IsDomain A :=
  { e.injective.isLeftCancelMulZero e (map_zero e) (map_mul e),
    e.injective.isRightCancelMulZero e (map_zero e) (map_mul e) with
    exists_pair_ne := ⟨e.symm 0, e.symm 1, e.symm.injective.ne zero_ne_one⟩ }

/--
theorem `isDomain_iff` / 定理 `isDomain_iff`

English:
theorem isDomain_iff
  given: {A B : Type*} [Semiring A] [Semiring B] (e : A ≃* B)
  proof: e.symm.isDomain
  mpr _ := e.isDomain

中文:
定理 isDomain_iff
  条件: {A B : 类型} [半环 A] [半环 B] (e : A ≃* B)
  证明: e.symm.isDomain
  mpr _ := e.isDomain

Depends on / 依赖: e.symm.isDomain, isDomain
-/
theorem isDomain_iff {A B : Type*} [Semiring A] [Semiring B] (e : A ≃* B) :
    IsDomain A ↔ IsDomain B where
  mp _ := e.symm.isDomain
  mpr _ := e.isDomain

variable {A B : Type*} [MulZeroClass A] [MulZeroClass B]

/--
theorem `noZeroDivisors_iff` / 定理 `noZeroDivisors_iff`

English:
theorem noZeroDivisors_iff
  given: (e : A ≃* B)
  statement: NoZeroDivisors A ↔ NoZeroDivisors B where
  proof: e.symm.noZeroDivisors
  mpr _ := e.noZeroDivisors

中文:
定理 noZeroDivisors_iff
  条件: (e : A ≃* B)
  结论: 无零因子 A ↔ 无零因子 B where
  证明: e.symm.noZeroDivisors
  mpr _ := e.noZeroDivisors

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, e.symm.noZeroDivisors, noZeroDivisors, pullback_fst
-/
theorem noZeroDivisors_iff (e : A ≃* B) : NoZeroDivisors A ↔ NoZeroDivisors B where
  mp _ := e.symm.noZeroDivisors
  mpr _ := e.noZeroDivisors

/--
theorem `isLeftCancelMulZero_iff` / 定理 `isLeftCancelMulZero_iff`

English:
theorem isLeftCancelMulZero_iff
  given: (e : A ≃* B)
  statement: IsLeftCancelMulZero A ↔ IsLeftCancelMulZero B where
  proof: e.symm.injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)
  mpr _ := e.injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)

中文:
定理 isLeftCancelMulZero_iff
  条件: (e : A ≃* B)
  结论: 是左消去MulZero A ↔ 是左消去MulZero B where
  证明: e.symm.injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)
  mpr _ := e.injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)

Depends on / 依赖: e.symm.injective.isLeftCancelMulZero, injective, isLeftCancelMulZero, map_mul, map_zero
-/
theorem isLeftCancelMulZero_iff (e : A ≃* B) : IsLeftCancelMulZero A ↔ IsLeftCancelMulZero B where
  mp _ := e.symm.injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)
  mpr _ := e.injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)

/--
theorem `isRightCancelMulZero_iff` / 定理 `isRightCancelMulZero_iff`

English:
theorem isRightCancelMulZero_iff
  given: (e : A ≃* B)
  proof: e.symm.injective.isRightCancelMulZero _ (map_zero _) (map_mul _)
  mpr _ := e.injective.isRightCancelMulZero _ (map_zero _) (map_mul _)

中文:
定理 isRightCancelMulZero_iff
  条件: (e : A ≃* B)
  证明: e.symm.injective.isRightCancelMulZero _ (map_zero _) (map_mul _)
  mpr _ := e.injective.isRightCancelMulZero _ (map_zero _) (map_mul _)

Depends on / 依赖: e.symm.injective.isRightCancelMulZero, injective, isRightCancelMulZero, map_mul, map_zero
-/
theorem isRightCancelMulZero_iff (e : A ≃* B) :
    IsRightCancelMulZero A ↔ IsRightCancelMulZero B where
  mp _ := e.symm.injective.isRightCancelMulZero _ (map_zero _) (map_mul _)
  mpr _ := e.injective.isRightCancelMulZero _ (map_zero _) (map_mul _)

/--
theorem `isCancelMulZero_iff` / 定理 `isCancelMulZero_iff`

English:
theorem isCancelMulZero_iff
  given: (e : A ≃* B)
  statement: IsCancelMulZero A ↔ IsCancelMulZero B where
  proof: e.symm.injective.isCancelMulZero _ (map_zero _) (map_mul _)
  mpr _ := e.injective.isCancelMulZero _ (map_zero _) (map_mul _)

中文:
定理 isCancelMulZero_iff
  条件: (e : A ≃* B)
  结论: 是乘零消去 A ↔ 是乘零消去 B where
  证明: e.symm.injective.isCancelMulZero _ (map_zero _) (map_mul _)
  mpr _ := e.injective.isCancelMulZero _ (map_zero _) (map_mul _)

Depends on / 依赖: e.symm.injective.isCancelMulZero, injective, isCancelMulZero, map_mul, map_zero
-/
theorem isCancelMulZero_iff (e : A ≃* B) : IsCancelMulZero A ↔ IsCancelMulZero B where
  mp _ := e.symm.injective.isCancelMulZero _ (map_zero _) (map_mul _)
  mpr _ := e.injective.isCancelMulZero _ (map_zero _) (map_mul _)

end MulEquiv
