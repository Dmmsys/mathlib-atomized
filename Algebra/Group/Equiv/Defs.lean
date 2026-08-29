/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Logic.Equiv.Defs

/-!
# Multiplicative and additive equivs

In this file we define two extensions of `Equiv` called `AddEquiv` and `MulEquiv`, which are
datatypes representing isomorphisms of `AddMonoid`s/`AddGroup`s and `Monoid`s/`Group`s.

## Main definitions
* `≃*` (`MulEquiv`), `≃+` (`AddEquiv`): bundled equivalences that preserve multiplication/addition
  (and are therefore monoid and group isomorphisms).
* `MulEquivClass`, `AddEquivClass`: classes for types containing bundled equivalences that
  preserve multiplication/addition.

## Notation

* ``infix ` ≃* `:25 := MulEquiv``
* ``infix ` ≃+ `:25 := AddEquiv``

The extended equivs all have coercions to functions, and the coercions are the canonical
notation when treating the isomorphisms as maps.

## Tags

Equiv, MulEquiv, AddEquiv
-/

@[expose] public section

open Function

variable {F α β M N P G H : Type*}

namespace EmbeddingLike
variable [One M] [One N] [FunLike F M N] [EmbeddingLike F M N] [OneHomClass F M N]

@[to_additive (attr := simp)]
/--
theorem `map_eq_one_iff` / 定理 `map_eq_one_iff`

English:
theorem map_eq_one_iff
  given: {f : F} {x : M}
  proof: _root_.map_eq_one_iff f (EmbeddingLike.injective f)

@[to_additive]

中文:
定理 map_eq_one_iff
  条件: {f : F} {x : M}
  证明: _root_.map_eq_one_iff f (EmbeddingLike.injective f)

@[to_additive]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.injective, _root_, _root_.map_eq_one_iff, injective, map_eq_one_iff
-/
theorem map_eq_one_iff {f : F} {x : M} :
    f x = 1 ↔ x = 1 :=
  _root_.map_eq_one_iff f (EmbeddingLike.injective f)

@[to_additive]
/--
theorem `map_ne_one_iff` / 定理 `map_ne_one_iff`

English:
theorem map_ne_one_iff
  given: {f : F} {x : M}
  proof: map_eq_one_iff.not

中文:
定理 map_ne_one_iff
  条件: {f : F} {x : M}
  证明: map_eq_one_iff.not

Depends on / 依赖: map_eq_one_iff, map_eq_one_iff.not
-/
theorem map_ne_one_iff {f : F} {x : M} :
    f x != 1 ↔ x != 1 :=
  map_eq_one_iff.not

end EmbeddingLike

/--
Definition of `AddEquiv` / `AddEquiv` 的定义

English:
structure AddEquiv
  parameters: (A B : Type*) [Add A] [Add B]
  extends: A ≃ B, AddHom A B
  (no additional axioms)

中文:
结构 AddEquiv
  参数: (A B : 类型) [Add A] [Add B]
  继承: A ≃ B, AddHom A B
  (无附加公理)
-/
structure AddEquiv (A B : Type*) [Add A] [Add B] extends A ≃ B, AddHom A B

/--
Definition of `AddEquivClass` / `AddEquivClass` 的定义

English:
class AddEquivClass
  parameters: (F : Type*) (A B : outParam Type*) [Add A] [Add B] [EquivLike F A B]
  axioms and operations (1):
    - map_add : forall (f : F) (a b), f (a + b) = f a + f b

中文:
类 AddEquivClass
  参数: (F : 类型) (A B : outParam 类型) [Add A] [Add B] [EquivLike F A B]
  公理与运算 (1 个):
    - map_add : 对任意 (f : F) (a b), f (a + b) = f a + f b
-/
class AddEquivClass (F : Type*) (A B : outParam Type*) [Add A] [Add B] [EquivLike F A B] :
    Prop where
  /-- Preserves addition. -/
  map_add : forall (f : F) (a b), f (a + b) = f a + f b

/-- The `Equiv` underlying an `AddEquiv`. -/
add_decl_doc AddEquiv.toEquiv

/-- The `AddHom` underlying an `AddEquiv`. -/
add_decl_doc AddEquiv.toAddHom

/-- `MulEquiv α β` is the type of an equiv `α ≃ β` which preserves multiplication. -/
@[to_additive]
/--
Definition of `MulEquiv` / `MulEquiv` 的定义

English:
structure MulEquiv
  parameters: (M N : Type*) [Mul M] [Mul N]
  extends: M ≃ N, M ->ₙ* N
  (no additional axioms)

中文:
结构 MulEquiv
  参数: (M N : 类型) [Mul M] [Mul N]
  继承: M ≃ N, M ->ₙ* N
  (无附加公理)
-/
structure MulEquiv (M N : Type*) [Mul M] [Mul N] extends M ≃ N, M ->ₙ* N

/-- The `Equiv` underlying a `MulEquiv`. -/
add_decl_doc MulEquiv.toEquiv

/-- The `MulHom` underlying a `MulEquiv`. -/
add_decl_doc MulEquiv.toMulHom

/-- Notation for a `MulEquiv`. -/
infixl:25 " ≃* " => MulEquiv

/-- Notation for an `AddEquiv`. -/
infixl:25 " ≃+ " => AddEquiv

@[to_additive]
/--
lemma `MulEquiv.toEquiv_injective` / 引理 `MulEquiv.toEquiv_injective`

English:
lemma MulEquiv.toEquiv_injective
  given: {α β : Type*} [Mul α] [Mul β]

中文:
引理 MulEquiv.toEquiv_injective
  条件: {α β : 类型} [Mul α] [Mul β]
-/
lemma MulEquiv.toEquiv_injective {α β : Type*} [Mul α] [Mul β] :
    Function.Injective (toEquiv : (α ≃* β) -> (α ≃ β))
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- `MulEquivClass F A B` states that `F` is a type of multiplication-preserving morphisms.
You should extend this class when you extend `MulEquiv`. -/
-- TODO: make this a synonym for MulHomClass?
@[to_additive]
/--
Definition of `MulEquivClass` / `MulEquivClass` 的定义

English:
class MulEquivClass
  parameters: (F : Type*) (A B : outParam Type*) [Mul A] [Mul B] [EquivLike F A B]
  axioms and operations (1):
    - map_mul : forall (f : F) (a b), f (a * b) = f a * f b

中文:
类 MulEquivClass
  参数: (F : 类型) (A B : outParam 类型) [Mul A] [Mul B] [EquivLike F A B]
  公理与运算 (1 个):
    - map_mul : 对任意 (f : F) (a b), f (a * b) = f a * f b
-/
class MulEquivClass (F : Type*) (A B : outParam Type*) [Mul A] [Mul B] [EquivLike F A B] :
    Prop where
  /-- Preserves multiplication. -/
  map_mul : forall (f : F) (a b), f (a * b) = f a * f b

@[to_additive]
alias MulEquivClass.map_eq_one_iff := EmbeddingLike.map_eq_one_iff

@[to_additive]
alias MulEquivClass.map_ne_one_iff := EmbeddingLike.map_ne_one_iff

namespace MulEquivClass

variable (F)
variable [EquivLike F M N]

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) instMulHomClass (F : Type*)
    [Mul M] [Mul N] [EquivLike F M N] [h : MulEquivClass F M N] : MulHomClass F M N :=
  { h with }

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) instMonoidHomClass
    [MulOneClass M] [MulOneClass N] [MulEquivClass F M N] :
    MonoidHomClass F M N :=
  { MulEquivClass.instMulHomClass F with
    map_one := fun e =>
      calc
        e 1 = e 1 * 1 := (mul_one _).symm
        _ = e 1 * e (EquivLike.inv e (1 : N) : M) :=
          congr_arg _ (EquivLike.right_inv e 1).symm
        _ = e (EquivLike.inv e (1 : N)) := by rw [← map_mul, one_mul]
        _ = 1 := EquivLike.right_inv e 1 }

end MulEquivClass

variable [EquivLike F α β]

/-- Turn an element of a type `F` satisfying `MulEquivClass F α β` into an actual
`MulEquiv`. This is declared as the default coercion from `F` to `α ≃* β`. -/
@[to_additive (attr := coe)
/-- Turn an element of a type `F` satisfying `AddEquivClass F α β` into an actual
`AddEquiv`. This is declared as the default coercion from `F` to `α ≃+ β`. -/]
/--
Definition of `MulEquivClass.toMulEquiv` / `MulEquivClass.toMulEquiv` 的定义

English:
definition MulEquivClass.toMulEquiv
  signature: [Mul α] [Mul β] [MulEquivClass F α β] (f : F)
  body: { (f : α ≃ β), (f : α ->ₙ* β) with }

中文:
定义 MulEquivClass.toMulEquiv
  签名: [Mul α] [Mul β] [MulEquivClass F α β] (f : F)
  定义体: { (f : α ≃ β), (f : α ->ₙ* β) with }
-/
def MulEquivClass.toMulEquiv [Mul α] [Mul β] [MulEquivClass F α β] (f : F) : α ≃* β :=
  { (f : α ≃ β), (f : α ->ₙ* β) with }

/-- Any type satisfying `MulEquivClass` can be cast into `MulEquiv` via
`MulEquivClass.toMulEquiv`. -/
@[to_additive /-- Any type satisfying `AddEquivClass` can be cast into `AddEquiv` via
`AddEquivClass.toAddEquiv`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [Mul β] [MulEquivClass F α β] : CoeTC F (α ≃* β)
  body: ⟨MulEquivClass.toMulEquiv⟩

中文:
实例 [Mul
  签名: α] [Mul β] [MulEquivClass F α β] : CoeTC F (α ≃* β)
  定义体: ⟨MulEquivClass.toMulEquiv⟩

Depends on / 依赖: MulEquivClass, MulEquivClass.toMulEquiv, toMulEquiv
-/
instance [Mul α] [Mul β] [MulEquivClass F α β] : CoeTC F (α ≃* β) :=
  ⟨MulEquivClass.toMulEquiv⟩

namespace MulEquiv
section Mul
variable [Mul M] [Mul N] [Mul P]

section coe

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (M ≃* N) M N
  body: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    apply Equiv.coe_fn_injective h₁

@[to_additive] -- shortcut instance that doesn't generate any subgoals

中文:
实例 :
  签名: EquivLike (M ≃* N) M N
  定义体: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    apply Equiv.coe_fn_injective h₁

@[to_additive] -- shortcut instance that doesn't generate any subgoals

Depends on / 依赖: f.toFun
-/
instance : EquivLike (M ≃* N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    apply Equiv.coe_fn_injective h₁

@[to_additive] -- shortcut instance that doesn't generate any subgoals
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (M ≃* N) fun _ => M -> N
  body: f

@[to_additive]

中文:
实例 :
  签名: CoeFun (M ≃* N) fun _ => M -> N
  定义体: f

@[to_additive]
-/
instance : CoeFun (M ≃* N) fun _ => M -> N where
  coe f := f

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulEquivClass (M ≃* N) M N
  body: f.map_mul'

中文:
实例 :
  签名: MulEquivClass (M ≃* N) M N
  定义体: f.map_mul'

Depends on / 依赖: f.map_mul, map_mul
-/
instance : MulEquivClass (M ≃* N) M N where
  map_mul f := f.map_mul'

/-- Two multiplicative isomorphisms agree if they are defined by the
same underlying function. -/
@[to_additive (attr := ext)
  /-- Two additive isomorphisms agree if they are defined by the same underlying function. -/]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : MulEquiv M N} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

@[to_additive]

中文:
定理 ext
  条件: {f g : MulEquiv M N} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[to_additive]
/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: {f : MulEquiv M N} {x x' : M}
  statement: x = x' -> f x = f x'
  proof: DFunLike.congr_arg f

@[to_additive]

中文:
定理 congr_arg
  条件: {f : MulEquiv M N} {x x' : M}
  结论: x = x' -> f x = f x'
  证明: DFunLike.congr_arg f

@[to_additive]
-/
protected theorem congr_arg {f : MulEquiv M N} {x x' : M} : x = x' -> f x = f x' :=
  DFunLike.congr_arg f

@[to_additive]
/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : MulEquiv M N} (h : f = g) (x : M)
  statement: f x = g x
  proof: DFunLike.congr_fun h x

@[to_additive (attr := simp)]

中文:
定理 congr_fun
  条件: {f g : MulEquiv M N} (h : f = g) (x : M)
  结论: f x = g x
  证明: DFunLike.congr_fun h x

@[to_additive (attr := simp)]
-/
protected theorem congr_fun {f g : MulEquiv M N} (h : f = g) (x : M) : f x = g x :=
  DFunLike.congr_fun h x

@[to_additive (attr := simp)]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : M ≃ N) (hf : forall x y, f (x * y) = f x * f y)
  statement: (mk f hf : M -> N) = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_mk
  条件: (f : M ≃ N) (hf : 对任意 x y, f (x * y) = f x * f y)
  结论: (mk f hf : M -> N) = f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_mk (f : M ≃ N) (hf : forall x y, f (x * y) = f x * f y) : (mk f hf : M -> N) = f := rfl

@[to_additive (attr := simp)]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (e : M ≃* N) (e' h₁ h₂ h₃)
  statement: (⟨⟨e, e', h₁, h₂⟩, h₃⟩ : M ≃* N) = e
  proof: ext fun _ => rfl

@[to_additive (attr := simp)]

中文:
定理 mk_coe
  条件: (e : M ≃* N) (e' h₁ h₂ h₃)
  结论: (⟨⟨e, e', h₁, h₂⟩, h₃⟩ : M ≃* N) = e
  证明: ext fun _ => rfl

@[to_additive (attr := simp)]
-/
theorem mk_coe (e : M ≃* N) (e' h₁ h₂ h₃) : (⟨⟨e, e', h₁, h₂⟩, h₃⟩ : M ≃* N) = e :=
  ext fun _ => rfl

@[to_additive (attr := simp)]
/--
theorem `toEquiv_eq_coe` / 定理 `toEquiv_eq_coe`

English:
theorem toEquiv_eq_coe
  given: (f : M ≃* N)
  statement: f.toEquiv = f
  proof: rfl

中文:
定理 toEquiv_eq_coe
  条件: (f : M ≃* N)
  结论: f.toEquiv = f
  证明: rfl
-/
theorem toEquiv_eq_coe (f : M ≃* N) : f.toEquiv = f :=
  rfl

/-- The `simp`-normal form to turn something into a `MulHom` is via `MulHomClass.toMulHom`. -/
@[to_additive (attr := simp)]
/--
theorem `toMulHom_eq_coe` / 定理 `toMulHom_eq_coe`

English:
theorem toMulHom_eq_coe
  given: (f : M ≃* N)
  statement: f.toMulHom = ↑f
  proof: rfl

@[to_additive]

中文:
定理 toMulHom_eq_coe
  条件: (f : M ≃* N)
  结论: f.toMulHom = ↑f
  证明: rfl

@[to_additive]
-/
theorem toMulHom_eq_coe (f : M ≃* N) : f.toMulHom = ↑f :=
  rfl

@[to_additive]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : M ≃* N)
  statement: f.toFun = f
  proof: rfl

中文:
定理 toFun_eq_coe
  条件: (f : M ≃* N)
  结论: f.toFun = f
  证明: rfl
-/
theorem toFun_eq_coe (f : M ≃* N) : f.toFun = f := rfl

/-- `simp`-normal form of `toFun_eq_coe`. -/
@[to_additive (attr := simp)]
/--
theorem `coe_toEquiv` / 定理 `coe_toEquiv`

English:
theorem coe_toEquiv
  given: (f : M ≃* N)
  statement: ⇑(f : M ≃ N) = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_toEquiv
  条件: (f : M ≃* N)
  结论: ⇑(f : M ≃ N) = f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_toEquiv (f : M ≃* N) : ⇑(f : M ≃ N) = f := rfl

@[to_additive (attr := simp)]
/--
theorem `coe_toMulHom` / 定理 `coe_toMulHom`

English:
theorem coe_toMulHom
  given: {f : M ≃* N}
  statement: (f.toMulHom : M -> N) = f
  proof: rfl

中文:
定理 coe_toMulHom
  条件: {f : M ≃* N}
  结论: (f.toMulHom : M -> N) = f
  证明: rfl
-/
theorem coe_toMulHom {f : M ≃* N} : (f.toMulHom : M -> N) = f := rfl

/-- Makes a multiplicative isomorphism from a bijection which preserves multiplication. -/
@[to_additive /-- Makes an additive isomorphism from a bijection which preserves addition. -/]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (f : M ≃ N) (h : forall x y, f (x * y) = f x * f y)
  body: ⟨f, h⟩

中文:
定义 mk'
  签名: (f : M ≃ N) (h : 对任意 x y, f (x * y) = f x * f y)
  定义体: ⟨f, h⟩
-/
def mk' (f : M ≃ N) (h : forall x y, f (x * y) = f x * f y) : M ≃* N := ⟨f, h⟩

end coe

section map

/-- A multiplicative isomorphism preserves multiplication. -/
@[to_additive /-- An additive isomorphism preserves addition. -/]
/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  given: (f : M ≃* N)
  statement: forall x y, f (x * y) = f x * f y
  proof: map_mul f

中文:
定理 map_mul
  条件: (f : M ≃* N)
  结论: 对任意 x y, f (x * y) = f x * f y
  证明: map_mul f
-/
protected theorem map_mul (f : M ≃* N) : forall x y, f (x * y) = f x * f y :=
  map_mul f

end map

section bijective

@[to_additive]
/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (e : M ≃* N)
  statement: Function.Bijective e
  proof: EquivLike.bijective e

@[to_additive]

中文:
定理 bijective
  条件: (e : M ≃* N)
  结论: Function.Bijective e
  证明: EquivLike.bijective e

@[to_additive]
-/
protected theorem bijective (e : M ≃* N) : Function.Bijective e :=
  EquivLike.bijective e

@[to_additive]
/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (e : M ≃* N)
  statement: Function.Injective e
  proof: EquivLike.injective e

@[to_additive]

中文:
定理 injective
  条件: (e : M ≃* N)
  结论: Function.Injective e
  证明: EquivLike.injective e

@[to_additive]
-/
protected theorem injective (e : M ≃* N) : Function.Injective e :=
  EquivLike.injective e

@[to_additive]
/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (e : M ≃* N)
  statement: Function.Surjective e
  proof: EquivLike.surjective e

@[to_additive]

中文:
定理 surjective
  条件: (e : M ≃* N)
  结论: Function.Surjective e
  证明: EquivLike.surjective e

@[to_additive]
-/
protected theorem surjective (e : M ≃* N) : Function.Surjective e :=
  EquivLike.surjective e

@[to_additive]
/--
theorem `apply_eq_iff_eq` / 定理 `apply_eq_iff_eq`

English:
theorem apply_eq_iff_eq
  given: (e : M ≃* N) {x y : M}
  statement: e x = e y ↔ x = y
  proof: e.injective.eq_iff

中文:
定理 apply_eq_iff_eq
  条件: (e : M ≃* N) {x y : M}
  结论: e x = e y ↔ x = y
  证明: e.injective.eq_iff

Depends on / 依赖: e.injective.eq_iff, eq_iff, injective
-/
theorem apply_eq_iff_eq (e : M ≃* N) {x y : M} : e x = e y ↔ x = y :=
  e.injective.eq_iff

end bijective

section refl

/-- The identity map is a multiplicative isomorphism. -/
@[to_additive (attr := refl) /-- The identity map is an additive isomorphism. -/]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (M : Type*) [Mul M]
  body: { Equiv.refl _ with map_mul' := fun _ _ => rfl }

@[to_additive]

中文:
定义 refl
  签名: (M : 类型) [Mul M]
  定义体: { Equiv.refl _ with map_mul' := fun _ _ => rfl }

@[to_additive]

Depends on / 依赖: Equiv.refl, map_mul
-/
def refl (M : Type*) [Mul M] : M ≃* M :=
  { Equiv.refl _ with map_mul' := fun _ _ => rfl }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (M ≃* M)
  body: ⟨refl M⟩

@[to_additive (attr := simp)]

中文:
实例 :
  签名: Inhabited (M ≃* M)
  定义体: ⟨refl M⟩

@[to_additive (attr := simp)]
-/
instance : Inhabited (M ≃* M) := ⟨refl M⟩

@[to_additive (attr := simp)]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  statement: ↑(refl M) = id
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_refl
  结论: ↑(refl M) = id
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_refl : ↑(refl M) = id := rfl

@[to_additive (attr := simp)]
/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: (m : M)
  statement: refl M m = m
  proof: rfl

中文:
定理 refl_apply
  条件: (m : M)
  结论: refl M m = m
  证明: rfl
-/
theorem refl_apply (m : M) : refl M m = m := rfl

end refl

section symm

/-- An alias for `h.symm.map_mul`. Introduced to fix the issue in
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/!4.234183.20.60simps.60.20maximum.20recursion.20depth
-/
@[to_additive]
/--
lemma `symm_map_mul` / 引理 `symm_map_mul`

English:
lemma symm_map_mul
  given: {M N : Type*} [Mul M] [Mul N] (h : M ≃* N) (x y : N)
  proof: map_mul (h.toMulHom.inverse h.toEquiv.symm h.left_inv h.right_inv) x y

中文:
引理 symm_map_mul
  条件: {M N : 类型} [Mul M] [Mul N] (h : M ≃* N) (x y : N)
  证明: map_mul (h.toMulHom.inverse h.toEquiv.symm h.left_inv h.right_inv) x y

Depends on / 依赖: h.left_inv, h.right_inv, h.toEquiv.symm, h.toMulHom.inverse, inverse, left_inv, map_mul, right_inv, toEquiv, toMulHom
-/
lemma symm_map_mul {M N : Type*} [Mul M] [Mul N] (h : M ≃* N) (x y : N) :
    h.symm (x * y) = h.symm x * h.symm y :=
  map_mul (h.toMulHom.inverse h.toEquiv.symm h.left_inv h.right_inv) x y

/-- The inverse of an isomorphism is an isomorphism. -/
@[to_additive (attr := symm) /-- The inverse of an isomorphism is an isomorphism. -/]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: {M N : Type*} [Mul M] [Mul N] (h : M ≃* N)
  body: ⟨h.toEquiv.symm, h.symm_map_mul⟩

@[to_additive]

中文:
定义 symm
  签名: {M N : 类型} [Mul M] [Mul N] (h : M ≃* N)
  定义体: ⟨h.toEquiv.symm, h.symm_map_mul⟩

@[to_additive]

Depends on / 依赖: h.symm_map_mul, h.toEquiv.symm, symm_map_mul, toEquiv
-/
def symm {M N : Type*} [Mul M] [Mul N] (h : M ≃* N) : N ≃* M :=
  ⟨h.toEquiv.symm, h.symm_map_mul⟩

@[to_additive]
/--
theorem `invFun_eq_symm` / 定理 `invFun_eq_symm`

English:
theorem invFun_eq_symm
  given: {f : M ≃* N}
  statement: f.invFun = f.symm
  proof: rfl

中文:
定理 invFun_eq_symm
  条件: {f : M ≃* N}
  结论: f.invFun = f.symm
  证明: rfl
-/
theorem invFun_eq_symm {f : M ≃* N} : f.invFun = f.symm := rfl

/-- `simp`-normal form of `invFun_eq_symm`. -/
@[to_additive (attr := simp)]
/--
theorem `coe_toEquiv_symm` / 定理 `coe_toEquiv_symm`

English:
theorem coe_toEquiv_symm
  given: (f : M ≃* N)
  statement: ((f : M ≃ N).symm : N -> M) = f.symm
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_toEquiv_symm
  条件: (f : M ≃* N)
  结论: ((f : M ≃ N).symm : N -> M) = f.symm
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_toEquiv_symm (f : M ≃* N) : ((f : M ≃ N).symm : N -> M) = f.symm := rfl

@[to_additive (attr := simp)]
/--
theorem `equivLike_inv_eq_symm` / 定理 `equivLike_inv_eq_symm`

English:
theorem equivLike_inv_eq_symm
  given: (f : M ≃* N)
  statement: EquivLike.inv f = f.symm
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 equivLike_inv_eq_symm
  条件: (f : M ≃* N)
  结论: EquivLike.inv f = f.symm
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem equivLike_inv_eq_symm (f : M ≃* N) : EquivLike.inv f = f.symm := rfl

@[to_additive (attr := simp)]
/--
theorem `toEquiv_symm` / 定理 `toEquiv_symm`

English:
theorem toEquiv_symm
  given: (f : M ≃* N)
  statement: (f.symm : N ≃ M) = (f : M ≃ N).symm
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toEquiv_symm
  条件: (f : M ≃* N)
  结论: (f.symm : N ≃ M) = (f : M ≃ N).symm
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toEquiv_symm (f : M ≃* N) : (f.symm : N ≃ M) = (f : M ≃ N).symm := rfl

@[to_additive (attr := simp)]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (f : M ≃* N)
  statement: f.symm.symm = f
  proof: rfl

@[to_additive]

中文:
定理 symm_symm
  条件: (f : M ≃* N)
  结论: f.symm.symm = f
  证明: rfl

@[to_additive]
-/
theorem symm_symm (f : M ≃* N) : f.symm.symm = f := rfl

@[to_additive]
/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (symm : (M ≃* N) -> N ≃* M)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[to_additive (attr := simp)]

中文:
定理 symm_bijective
  结论: Function.Bijective (symm : (M ≃* N) -> N ≃* M)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (symm : (M ≃* N) -> N ≃* M) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[to_additive (attr := simp)]
/--
theorem `mk_coe'` / 定理 `mk_coe'`

English:
theorem mk_coe'
  given: (e : M ≃* N) (f h₁ h₂ h₃)
  statement: (MulEquiv.mk ⟨f, e, h₁, h₂⟩ h₃ : N ≃* M) = e.symm
  proof: symm_bijective.injective ext fun _ => rfl

@[to_additive (attr := simp)]

中文:
定理 mk_coe'
  条件: (e : M ≃* N) (f h₁ h₂ h₃)
  结论: (MulEquiv.mk ⟨f, e, h₁, h₂⟩ h₃ : N ≃* M) = e.symm
  证明: symm_bijective.injective ext fun _ => rfl

@[to_additive (attr := simp)]

Depends on / 依赖: injective, symm_bijective, symm_bijective.injective
-/
theorem mk_coe' (e : M ≃* N) (f h₁ h₂ h₃) : (MulEquiv.mk ⟨f, e, h₁, h₂⟩ h₃ : N ≃* M) = e.symm :=
symm_bijective.injective ext fun _ => rfl

@[to_additive (attr := simp)]
/--
theorem `symm_mk` / 定理 `symm_mk`

English:
theorem symm_mk
  given: (f : M ≃ N) (h)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 symm_mk
  条件: (f : M ≃ N) (h)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem symm_mk (f : M ≃ N) (h) :
    (MulEquiv.mk f h).symm = ⟨f.symm, (MulEquiv.mk f h).symm_map_mul⟩ := rfl

@[to_additive (attr := simp)]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (refl M).symm = refl M
  proof: rfl

中文:
定理 refl_symm
  结论: (refl M).symm = refl M
  证明: rfl
-/
theorem refl_symm : (refl M).symm = refl M := rfl

/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/
@[to_additive (attr := simp)
/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : M ≃* N) (y : N)
  statement: e (e.symm y) = y
  proof: e.toEquiv.apply_symm_apply y

中文:
定理 apply_symm_apply
  条件: (e : M ≃* N) (y : N)
  结论: e (e.symm y) = y
  证明: e.toEquiv.apply_symm_apply y

Depends on / 依赖: apply_symm_apply, e.toEquiv.apply_symm_apply, toEquiv
-/
theorem apply_symm_apply (e : M ≃* N) (y : N) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y

/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/
@[to_additive (attr := simp)
/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : M ≃* N) (x : M)
  statement: e.symm (e x) = x
  proof: e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]

中文:
定理 symm_apply_apply
  条件: (e : M ≃* N) (x : M)
  结论: e.symm (e x) = x
  证明: e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]

Depends on / 依赖: e.toEquiv.symm_apply_apply, symm_apply_apply, toEquiv
-/
theorem symm_apply_apply (e : M ≃* N) (x : M) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]
/--
theorem `symm_comp_self` / 定理 `symm_comp_self`

English:
theorem symm_comp_self
  given: (e : M ≃* N)
  statement: e.symm ∘ e = id
  proof: funext e.symm_apply_apply

@[to_additive (attr := simp)]

中文:
定理 symm_comp_self
  条件: (e : M ≃* N)
  结论: e.symm ∘ e = id
  证明: funext e.symm_apply_apply

@[to_additive (attr := simp)]

Depends on / 依赖: e.symm_apply_apply, symm_apply_apply
-/
theorem symm_comp_self (e : M ≃* N) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[to_additive (attr := simp)]
/--
theorem `self_comp_symm` / 定理 `self_comp_symm`

English:
theorem self_comp_symm
  given: (e : M ≃* N)
  statement: e ∘ e.symm = id
  proof: funext e.apply_symm_apply

@[to_additive]

中文:
定理 self_comp_symm
  条件: (e : M ≃* N)
  结论: e ∘ e.symm = id
  证明: funext e.apply_symm_apply

@[to_additive]

Depends on / 依赖: apply_symm_apply, e.apply_symm_apply
-/
theorem self_comp_symm (e : M ≃* N) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

@[to_additive]
/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (e : M ≃* N) {x y}
  statement: e.symm x = y ↔ x = e y
  proof: e.toEquiv.symm_apply_eq

@[to_additive]

中文:
定理 symm_apply_eq
  条件: (e : M ≃* N) {x y}
  结论: e.symm x = y ↔ x = e y
  证明: e.toEquiv.symm_apply_eq

@[to_additive]

Depends on / 依赖: e.toEquiv.symm_apply_eq, symm_apply_eq, toEquiv
-/
theorem symm_apply_eq (e : M ≃* N) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

@[to_additive]
/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (e : M ≃* N) {x y}
  statement: y = e.symm x ↔ e y = x
  proof: e.toEquiv.eq_symm_apply

@[to_additive (attr := deprecated eq_symm_apply (since := "2026-07-26"))]

中文:
定理 eq_symm_apply
  条件: (e : M ≃* N) {x y}
  结论: y = e.symm x ↔ e y = x
  证明: e.toEquiv.eq_symm_apply

@[to_additive (attr := deprecated eq_symm_apply (since := "2026-07-26"))]

Depends on / 依赖: e.toEquiv.eq_symm_apply, eq_symm_apply, toEquiv
-/
theorem eq_symm_apply (e : M ≃* N) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[to_additive (attr := deprecated eq_symm_apply (since := "2026-07-26"))]
/--
theorem `apply_eq_iff_symm_apply` / 定理 `apply_eq_iff_symm_apply`

English:
theorem apply_eq_iff_symm_apply
  given: (e : M ≃* N) {x : M} {y : N}
  statement: e x = y ↔ x = e.symm y
  proof: e.eq_symm_apply.symm

@[to_additive]

中文:
定理 apply_eq_iff_symm_apply
  条件: (e : M ≃* N) {x : M} {y : N}
  结论: e x = y ↔ x = e.symm y
  证明: e.eq_symm_apply.symm

@[to_additive]

Depends on / 依赖: e.eq_symm_apply.symm, eq_symm_apply
-/
theorem apply_eq_iff_symm_apply (e : M ≃* N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
  e.eq_symm_apply.symm

@[to_additive]
/--
theorem `eq_comp_symm` / 定理 `eq_comp_symm`

English:
theorem eq_comp_symm
  given: {α : Type*} (e : M ≃* N) (f : N -> α) (g : M -> α)
  proof: e.toEquiv.eq_comp_symm f g

@[to_additive]

中文:
定理 eq_comp_symm
  条件: {α : 类型} (e : M ≃* N) (f : N -> α) (g : M -> α)
  证明: e.toEquiv.eq_comp_symm f g

@[to_additive]

Depends on / 依赖: e.toEquiv.eq_comp_symm, eq_comp_symm, toEquiv
-/
theorem eq_comp_symm {α : Type*} (e : M ≃* N) (f : N -> α) (g : M -> α) :
    f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

@[to_additive]
/--
theorem `comp_symm_eq` / 定理 `comp_symm_eq`

English:
theorem comp_symm_eq
  given: {α : Type*} (e : M ≃* N) (f : N -> α) (g : M -> α)
  proof: e.toEquiv.comp_symm_eq f g

@[to_additive]

中文:
定理 comp_symm_eq
  条件: {α : 类型} (e : M ≃* N) (f : N -> α) (g : M -> α)
  证明: e.toEquiv.comp_symm_eq f g

@[to_additive]

Depends on / 依赖: comp_symm_eq, e.toEquiv.comp_symm_eq, toEquiv
-/
theorem comp_symm_eq {α : Type*} (e : M ≃* N) (f : N -> α) (g : M -> α) :
    g ∘ e.symm = f ↔ g = f ∘ e :=
  e.toEquiv.comp_symm_eq f g

@[to_additive]
/--
theorem `eq_symm_comp` / 定理 `eq_symm_comp`

English:
theorem eq_symm_comp
  given: {α : Type*} (e : M ≃* N) (f : α -> M) (g : α -> N)
  proof: e.toEquiv.eq_symm_comp f g

@[to_additive]

中文:
定理 eq_symm_comp
  条件: {α : 类型} (e : M ≃* N) (f : α -> M) (g : α -> N)
  证明: e.toEquiv.eq_symm_comp f g

@[to_additive]

Depends on / 依赖: e.toEquiv.eq_symm_comp, eq_symm_comp, toEquiv
-/
theorem eq_symm_comp {α : Type*} (e : M ≃* N) (f : α -> M) (g : α -> N) :
    f = e.symm ∘ g ↔ e ∘ f = g :=
  e.toEquiv.eq_symm_comp f g

@[to_additive]
/--
theorem `symm_comp_eq` / 定理 `symm_comp_eq`

English:
theorem symm_comp_eq
  given: {α : Type*} (e : M ≃* N) (f : α -> M) (g : α -> N)
  proof: e.toEquiv.symm_comp_eq f g

@[to_additive (attr := simp)]

中文:
定理 symm_comp_eq
  条件: {α : 类型} (e : M ≃* N) (f : α -> M) (g : α -> N)
  证明: e.toEquiv.symm_comp_eq f g

@[to_additive (attr := simp)]

Depends on / 依赖: e.toEquiv.symm_comp_eq, symm_comp_eq, toEquiv
-/
theorem symm_comp_eq {α : Type*} (e : M ≃* N) (f : α -> M) (g : α -> N) :
    e.symm ∘ g = f ↔ g = e ∘ f :=
  e.toEquiv.symm_comp_eq f g

@[to_additive (attr := simp)]
/--
theorem `_root_.MulEquivClass.apply_coe_symm_apply` / 定理 `_root_.MulEquivClass.apply_coe_symm_apply`

English:
theorem _root_.MulEquivClass.apply_coe_symm_apply
  statement: {α β} [Mul α] [Mul β] {F} [EquivLike F α β]
  proof: (e : α ≃* β).right_inv x

@[to_additive (attr := simp)]

中文:
定理 _root_.MulEquivClass.apply_coe_symm_apply
  结论: {α β} [Mul α] [Mul β] {F} [EquivLike F α β]
  证明: (e : α ≃* β).right_inv x

@[to_additive (attr := simp)]

Depends on / 依赖: right_inv
-/
theorem _root_.MulEquivClass.apply_coe_symm_apply {α β} [Mul α] [Mul β] {F} [EquivLike F α β]
    [MulEquivClass F α β] (e : F) (x : β) :
    e ((e : α ≃* β).symm x) = x :=
  (e : α ≃* β).right_inv x

@[to_additive (attr := simp)]
/--
theorem `_root_.MulEquivClass.coe_symm_apply_apply` / 定理 `_root_.MulEquivClass.coe_symm_apply_apply`

English:
theorem _root_.MulEquivClass.coe_symm_apply_apply
  statement: {α β} [Mul α] [Mul β] {F} [EquivLike F α β]
  proof: (e : α ≃* β).left_inv x

中文:
定理 _root_.MulEquivClass.coe_symm_apply_apply
  结论: {α β} [Mul α] [Mul β] {F} [EquivLike F α β]
  证明: (e : α ≃* β).left_inv x

Depends on / 依赖: left_inv
-/
theorem _root_.MulEquivClass.coe_symm_apply_apply {α β} [Mul α] [Mul β] {F} [EquivLike F α β]
    [MulEquivClass F α β] (e : F) (x : α) :
    (e : α ≃* β).symm (e x) = x :=
  (e : α ≃* β).left_inv x

end symm

section simps

-- we don't hyperlink the note in the additive version, since that breaks syntax highlighting
-- in the whole file.

/-- See Note [custom simps projection] -/
@[to_additive /-- See Note [custom simps projection] -/]
/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (e : M ≃* N)
  body: e.symm

initialize_simps_projections AddEquiv (toFun -> apply, invFun -> symm_apply)

initialize_simps_projections MulEquiv (toFun -> apply, invFun -> symm_apply)

中文:
定义 Simps.symm_apply
  签名: (e : M ≃* N)
  定义体: e.symm

initialize_simps_projections AddEquiv (toFun -> apply, invFun -> symm_apply)

initialize_simps_projections MulEquiv (toFun -> apply, invFun -> symm_apply)
-/
def Simps.symm_apply (e : M ≃* N) : N -> M :=
  e.symm

initialize_simps_projections AddEquiv (toFun -> apply, invFun -> symm_apply)

initialize_simps_projections MulEquiv (toFun -> apply, invFun -> symm_apply)

end simps

section trans

/-- Transitivity of multiplication-preserving isomorphisms -/
@[to_additive (attr := trans) /-- Transitivity of addition-preserving isomorphisms -/]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (h1 : M ≃* N) (h2 : N ≃* P)
  body: { h1.toEquiv.trans h2.toEquiv with
    map_mul' := fun x y => show h2 (h1 (x * y)) = h2 (h1 x) * h2 (h1 y) by
      rw [map_mul]; rw [map_mul] }

@[to_additive (attr := simp)]

中文:
定义 trans
  签名: (h1 : M ≃* N) (h2 : N ≃* P)
  定义体: { h1.toEquiv.trans h2.toEquiv with
    map_mul' := fun x y => show h2 (h1 (x * y)) = h2 (h1 x) * h2 (h1 y) by
      rw [map_mul]; rw [map_mul] }

@[to_additive (attr := simp)]

Depends on / 依赖: h1.toEquiv.trans, h2.toEquiv, map_mul, toEquiv
-/
def trans (h1 : M ≃* N) (h2 : N ≃* P) : M ≃* P :=
  { h1.toEquiv.trans h2.toEquiv with
    map_mul' := fun x y => show h2 (h1 (x * y)) = h2 (h1 x) * h2 (h1 y) by
      rw [map_mul]; rw [map_mul] }

@[to_additive (attr := simp)]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (e₁ : M ≃* N) (e₂ : N ≃* P)
  statement: ↑(e₁.trans e₂) = e₂ ∘ e₁
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_trans
  条件: (e₁ : M ≃* N) (e₂ : N ≃* P)
  结论: ↑(e₁.trans e₂) = e₂ ∘ e₁
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_trans (e₁ : M ≃* N) (e₂ : N ≃* P) : ↑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

@[to_additive (attr := simp)]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (e₁ : M ≃* N) (e₂ : N ≃* P) (m : M)
  statement: e₁.trans e₂ m = e₂ (e₁ m)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 trans_apply
  条件: (e₁ : M ≃* N) (e₂ : N ≃* P) (m : M)
  结论: e₁.trans e₂ m = e₂ (e₁ m)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (m : M) : e₁.trans e₂ m = e₂ (e₁ m) := rfl

@[to_additive (attr := simp)]
/--
theorem `symm_trans_apply` / 定理 `symm_trans_apply`

English:
theorem symm_trans_apply
  given: (e₁ : M ≃* N) (e₂ : N ≃* P) (p : P)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 symm_trans_apply
  条件: (e₁ : M ≃* N) (e₂ : N ≃* P) (p : P)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem symm_trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (p : P) :
    (e₁.trans e₂).symm p = e₁.symm (e₂.symm p) := rfl

@[to_additive (attr := simp)]
/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (e : M ≃* N)
  statement: e.symm.trans e = refl N
  proof: DFunLike.ext _ _ e.apply_symm_apply

@[to_additive (attr := simp)]

中文:
定理 symm_trans_self
  条件: (e : M ≃* N)
  结论: e.symm.trans e = refl N
  证明: DFunLike.ext _ _ e.apply_symm_apply

@[to_additive (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.ext, apply_symm_apply, e.apply_symm_apply
-/
theorem symm_trans_self (e : M ≃* N) : e.symm.trans e = refl N :=
  DFunLike.ext _ _ e.apply_symm_apply

@[to_additive (attr := simp)]
/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (e : M ≃* N)
  statement: e.trans e.symm = refl M
  proof: DFunLike.ext _ _ e.symm_apply_apply

中文:
定理 self_trans_symm
  条件: (e : M ≃* N)
  结论: e.trans e.symm = refl M
  证明: DFunLike.ext _ _ e.symm_apply_apply

Depends on / 依赖: DFunLike, DFunLike.ext, e.symm_apply_apply, symm_apply_apply
-/
theorem self_trans_symm (e : M ≃* N) : e.trans e.symm = refl M :=
  DFunLike.ext _ _ e.symm_apply_apply

end trans

/-- `MulEquiv.symm` defines an equivalence between `α ≃* β` and `β ≃* α`. -/
@[to_additive (attr := simps!)
/-- `AddEquiv.symm` defines an equivalence between `α ≃+ β` and `β ≃+ α` -/]
/--
Definition of `symmEquiv` / `symmEquiv` 的定义

English:
definition symmEquiv
  signature: (P Q : Type*) [Mul P] [Mul Q]
  body: .symm
  invFun := .symm

中文:
定义 symmEquiv
  签名: (P Q : 类型) [Mul P] [Mul Q]
  定义体: .symm
  invFun := .symm
-/
def symmEquiv (P Q : Type*) [Mul P] [Mul Q] : (P ≃* Q) ≃ (Q ≃* P) where
  toFun := .symm
  invFun := .symm

end Mul

/-- `Equiv.cast (congrArg _ h)` as a `MulEquiv`.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an equality of types,
to avoid having to deal with an equality of the algebraic structure itself. -/
@[to_additive (attr := simps!) /-- `Equiv.cast (congrArg _ h)` as an `AddEquiv`.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an equality of types,
to avoid having to deal with an equality of the algebraic structure itself. -/]
/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: {ι : Type*} {M : ι -> Type*} [forall i, Mul (M i)] {i j : ι} (h : i = j)
  body: Equiv.cast (congrArg _ h)
  map_mul' _ _ := by cases h; rfl

中文:
定义 cast
  签名: {ι : 类型} {M : ι -> 类型} [对任意 i, Mul (M i)] {i j : ι} (h : i = j)
  定义体: Equiv.cast (congrArg _ h)
  map_mul' _ _ := by cases h; rfl
-/
protected def cast {ι : Type*} {M : ι -> Type*} [forall i, Mul (M i)] {i j : ι} (h : i = j) :
    M i ≃* M j where
  toEquiv := Equiv.cast (congrArg _ h)
  map_mul' _ _ := by cases h; rfl

/-!
### Monoids
-/

section MulOneClass
variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

@[to_additive (attr := simp)]
/--
theorem `coe_monoidHom_refl` / 定理 `coe_monoidHom_refl`

English:
theorem coe_monoidHom_refl
  statement: (refl M : M ->* M) = MonoidHom.id M
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_monoidHom_refl
  结论: (refl M : M ->* M) = MonoidHom.id M
  证明: rfl

@[to_additive (attr := simp)]

Depends on / 依赖: ofUnique
-/
theorem coe_monoidHom_refl : (refl M : M ->* M) = MonoidHom.id M := rfl

@[to_additive (attr := simp)]
/--
lemma `coe_monoidHom_trans` / 引理 `coe_monoidHom_trans`

English:
lemma coe_monoidHom_trans
  given: (e₁ : M ≃* N) (e₂ : N ≃* P)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 coe_monoidHom_trans
  条件: (e₁ : M ≃* N) (e₂ : N ≃* P)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma coe_monoidHom_trans (e₁ : M ≃* N) (e₂ : N ≃* P) :
    (e₁.trans e₂ : M ->* P) = (e₂ : N ->* P).comp ↑e₁ := rfl

@[to_additive (attr := simp)]
/--
lemma `coe_monoidHom_comp_coe_monoidHom_symm` / 引理 `coe_monoidHom_comp_coe_monoidHom_symm`

English:
lemma coe_monoidHom_comp_coe_monoidHom_symm
  given: (e : M ≃* N)
  proof: by ext; simp

@[to_additive (attr := simp)]

中文:
引理 coe_monoidHom_comp_coe_monoidHom_symm
  条件: (e : M ≃* N)
  证明: by ext; simp

@[to_additive (attr := simp)]
-/
lemma coe_monoidHom_comp_coe_monoidHom_symm (e : M ≃* N) :
    (e : M ->* N).comp e.symm = MonoidHom.id _ := by ext; simp

@[to_additive (attr := simp)]
/--
lemma `coe_monoidHom_symm_comp_coe_monoidHom` / 引理 `coe_monoidHom_symm_comp_coe_monoidHom`

English:
lemma coe_monoidHom_symm_comp_coe_monoidHom
  given: (e : M ≃* N)
  proof: by ext; simp

@[to_additive]

中文:
引理 coe_monoidHom_symm_comp_coe_monoidHom
  条件: (e : M ≃* N)
  证明: by ext; simp

@[to_additive]
-/
lemma coe_monoidHom_symm_comp_coe_monoidHom (e : M ≃* N) :
    (e.symm : N ->* M).comp e = MonoidHom.id _ := by ext; simp

@[to_additive]
/--
lemma `comp_left_injective` / 引理 `comp_left_injective`

English:
lemma comp_left_injective
  given: (e : M ≃* N)
  statement: Injective fun f : N ->* P => f.comp (e : M ->* N)
  proof: LeftInverse.injective (g := fun f => f.comp e.symm) fun f => by simp [MonoidHom.comp_assoc]

@[to_additive]

中文:
引理 comp_left_injective
  条件: (e : M ≃* N)
  结论: Injective fun f : N ->* P => f.comp (e : M ->* N)
  证明: LeftInverse.injective (g := fun f => f.comp e.symm) fun f => by simp [MonoidHom.comp_assoc]

@[to_additive]

Depends on / 依赖: LeftInverse, LeftInverse.injective, MonoidHom, MonoidHom.comp_assoc, comp_assoc, e.symm, f.comp, injective
-/
lemma comp_left_injective (e : M ≃* N) : Injective fun f : N ->* P => f.comp (e : M ->* N) :=
  LeftInverse.injective (g := fun f => f.comp e.symm) fun f => by simp [MonoidHom.comp_assoc]

@[to_additive]
/--
lemma `comp_right_injective` / 引理 `comp_right_injective`

English:
lemma comp_right_injective
  given: (e : M ≃* N)
  statement: Injective fun f : P ->* M => (e : M ->* N).comp f
  proof: LeftInverse.injective (g := (e.symm : N ->* M).comp) fun f => by simp [← MonoidHom.comp_assoc]

中文:
引理 comp_right_injective
  条件: (e : M ≃* N)
  结论: Injective fun f : P ->* M => (e : M ->* N).comp f
  证明: LeftInverse.injective (g := (e.symm : N ->* M).comp) fun f => by simp [← MonoidHom.comp_assoc]

Depends on / 依赖: LeftInverse, LeftInverse.injective, MonoidHom, MonoidHom.comp_assoc, comp_assoc, e.symm, injective
-/
lemma comp_right_injective (e : M ≃* N) : Injective fun f : P ->* M => (e : M ->* N).comp f :=
  LeftInverse.injective (g := (e.symm : N ->* M).comp) fun f => by simp [← MonoidHom.comp_assoc]

/-- A multiplicative isomorphism of monoids sends `1` to `1` (and is hence a monoid isomorphism). -/
@[to_additive
  /-- An additive isomorphism of additive monoids sends `0` to `0`
  (and is hence an additive monoid isomorphism). -/]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  given: (h : M ≃* N)
  statement: h 1 = 1
  proof: map_one h

@[to_additive]

中文:
定理 map_one
  条件: (h : M ≃* N)
  结论: h 1 = 1
  证明: map_one h

@[to_additive]
-/
protected theorem map_one (h : M ≃* N) : h 1 = 1 := map_one h

@[to_additive]
/--
theorem `map_eq_one_iff` / 定理 `map_eq_one_iff`

English:
theorem map_eq_one_iff
  given: (h : M ≃* N) {x : M}
  statement: h x = 1 ↔ x = 1
  proof: EmbeddingLike.map_eq_one_iff

@[to_additive]

中文:
定理 map_eq_one_iff
  条件: (h : M ≃* N) {x : M}
  结论: h x = 1 ↔ x = 1
  证明: EmbeddingLike.map_eq_one_iff

@[to_additive]
-/
protected theorem map_eq_one_iff (h : M ≃* N) {x : M} : h x = 1 ↔ x = 1 :=
  EmbeddingLike.map_eq_one_iff

@[to_additive]
/--
theorem `map_ne_one_iff` / 定理 `map_ne_one_iff`

English:
theorem map_ne_one_iff
  given: (h : M ≃* N) {x : M}
  statement: h x != 1 ↔ x != 1
  proof: EmbeddingLike.map_ne_one_iff

中文:
定理 map_ne_one_iff
  条件: (h : M ≃* N) {x : M}
  结论: h x != 1 ↔ x != 1
  证明: EmbeddingLike.map_ne_one_iff

Depends on / 依赖: EmbeddingLike, EmbeddingLike.map_ne_one_iff, map_ne_one_iff
-/
theorem map_ne_one_iff (h : M ≃* N) {x : M} : h x != 1 ↔ x != 1 :=
  EmbeddingLike.map_ne_one_iff

/-- A bijective `Semigroup` homomorphism is an isomorphism -/
@[to_additive (attr := simps! apply)
/-- A bijective `AddSemigroup` homomorphism is an isomorphism -/]
/--
Definition of `ofBijective` / `ofBijective` 的定义

English:
definition ofBijective
  signature: {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
  body: { Equiv.ofBijective f hf with map_mul' := map_mul f }

@[to_additive (attr := simp)]

中文:
定义 ofBijective
  签名: {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
  定义体: { Equiv.ofBijective f hf with map_mul' := map_mul f }

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.ofBijective, map_mul, ofBijective
-/
noncomputable def ofBijective {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
    (f : F) (hf : Bijective f) : M ≃* N :=
  { Equiv.ofBijective f hf with map_mul' := map_mul f }

@[to_additive (attr := simp)]
/--
theorem `ofBijective_apply_symm_apply` / 定理 `ofBijective_apply_symm_apply`

English:
theorem ofBijective_apply_symm_apply
  given: {n : N} (f : M ->* N) (hf : Bijective f)
  proof: (ofBijective f hf).apply_symm_apply n

中文:
定理 ofBijective_apply_symm_apply
  条件: {n : N} (f : M ->* N) (hf : Bijective f)
  证明: (ofBijective f hf).apply_symm_apply n

Depends on / 依赖: apply_symm_apply, ofBijective
-/
theorem ofBijective_apply_symm_apply {n : N} (f : M ->* N) (hf : Bijective f) :
    f ((ofBijective f hf).symm n) = n := (ofBijective f hf).apply_symm_apply n

/-- Extract the forward direction of a multiplicative equivalence
as a multiplication-preserving function.
-/
@[to_additive /-- Extract the forward direction of an additive equivalence
  as an addition-preserving function. -/]
/--
Definition of `toMonoidHom` / `toMonoidHom` 的定义

English:
definition toMonoidHom
  signature: (h : M ≃* N)
  body: { h with map_one' := h.map_one }

@[to_additive (attr := simp)]

中文:
定义 toMonoidHom
  签名: (h : M ≃* N)
  定义体: { h with map_one' := h.map_one }

@[to_additive (attr := simp)]

Depends on / 依赖: h.map_one, map_one
-/
def toMonoidHom (h : M ≃* N) : M ->* N :=
  { h with map_one' := h.map_one }

@[to_additive (attr := simp)]
/--
theorem `coe_toMonoidHom` / 定理 `coe_toMonoidHom`

English:
theorem coe_toMonoidHom
  given: (e : M ≃* N)
  statement: ⇑e.toMonoidHom = e
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_toMonoidHom
  条件: (e : M ≃* N)
  结论: ⇑e.toMonoidHom = e
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_toMonoidHom (e : M ≃* N) : ⇑e.toMonoidHom = e := rfl

@[to_additive (attr := simp)]
/--
theorem `toMonoidHom_eq_coe` / 定理 `toMonoidHom_eq_coe`

English:
theorem toMonoidHom_eq_coe
  given: (f : M ≃* N)
  statement: f.toMonoidHom = (f : M ->* N)
  proof: rfl

@[to_additive]

中文:
定理 toMonoidHom_eq_coe
  条件: (f : M ≃* N)
  结论: f.toMonoidHom = (f : M ->* N)
  证明: rfl

@[to_additive]
-/
theorem toMonoidHom_eq_coe (f : M ≃* N) : f.toMonoidHom = (f : M ->* N) :=
  rfl

@[to_additive]
/--
theorem `toMonoidHom_injective` / 定理 `toMonoidHom_injective`

English:
theorem toMonoidHom_injective
  statement: Injective (toMonoidHom : M ≃* N -> M ->* N)
  proof: Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

中文:
定理 toMonoidHom_injective
  结论: Injective (toMonoidHom : M ≃* N -> M ->* N)
  证明: Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Injective, Injective.of_comp, coe_injective, of_comp
-/
theorem toMonoidHom_injective : Injective (toMonoidHom : M ≃* N -> M ->* N) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

end MulOneClass

/-!
### Groups
-/

/-- A multiplicative equivalence of groups preserves inversion. -/
@[to_additive /-- An additive equivalence of additive groups preserves negation. -/]
/--
theorem `map_inv` / 定理 `map_inv`

English:
theorem map_inv
  given: [Group G] [DivisionMonoid H] (h : G ≃* H) (x : G)
  proof: map_inv h x

中文:
定理 map_inv
  条件: [Group G] [DivisionMonoid H] (h : G ≃* H) (x : G)
  证明: map_inv h x
-/
protected theorem map_inv [Group G] [DivisionMonoid H] (h : G ≃* H) (x : G) :
    h x⁻¹ = (h x)⁻¹ :=
  map_inv h x

/-- A multiplicative equivalence of groups preserves division. -/
@[to_additive /-- An additive equivalence of additive groups preserves subtractions. -/]
/--
theorem `map_div` / 定理 `map_div`

English:
theorem map_div
  given: [Group G] [DivisionMonoid H] (h : G ≃* H) (x y : G)
  proof: map_div h x y

中文:
定理 map_div
  条件: [Group G] [DivisionMonoid H] (h : G ≃* H) (x y : G)
  证明: map_div h x y
-/
protected theorem map_div [Group G] [DivisionMonoid H] (h : G ≃* H) (x y : G) :
    h (x / y) = h x / h y :=
  map_div h x y

end MulEquiv

/-- Given a pair of multiplicative homomorphisms `f`, `g` such that `g.comp f = id` and
`f.comp g = id`, returns a multiplicative equivalence with `toFun = f` and `invFun = g`. This
constructor is useful if the underlying type(s) have specialized `ext` lemmas for multiplicative
homomorphisms. -/
@[to_additive (attr := simps -fullyApplied)
  /-- Given a pair of additive homomorphisms `f`, `g` such that `g.comp f = id` and
  `f.comp g = id`, returns an additive equivalence with `toFun = f` and `invFun = g`. This
  constructor is useful if the underlying type(s) have specialized `ext` lemmas for additive
  homomorphisms. -/]
/--
Definition of `MulHom.toMulEquiv` / `MulHom.toMulEquiv` 的定义

English:
definition MulHom.toMulEquiv
  signature: [Mul M] [Mul N] (f : M ->ₙ* N) (g : N ->ₙ* M) (h₁ : g.comp f = MulHom.id _)
  body: f
  invFun := g
  left_inv := DFunLike.congr_fun h₁
  right_inv := DFunLike.congr_fun h₂
  map_mul' := f.map_mul

中文:
定义 MulHom.toMulEquiv
  签名: [Mul M] [Mul N] (f : M ->ₙ* N) (g : N ->ₙ* M) (h₁ : g.comp f = MulHom.id _)
  定义体: f
  invFun := g
  left_inv := DFunLike.congr_fun h₁
  right_inv := DFunLike.congr_fun h₂
  map_mul' := f.map_mul
-/
def MulHom.toMulEquiv [Mul M] [Mul N] (f : M ->ₙ* N) (g : N ->ₙ* M) (h₁ : g.comp f = MulHom.id _)
    (h₂ : f.comp g = MulHom.id _) : M ≃* N where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₁
  right_inv := DFunLike.congr_fun h₂
  map_mul' := f.map_mul

/-- Given a pair of monoid homomorphisms `f`, `g` such that `g.comp f = id` and `f.comp g = id`,
returns a multiplicative equivalence with `toFun = f` and `invFun = g`. This constructor is
useful if the underlying type(s) have specialized `ext` lemmas for monoid homomorphisms. -/
@[to_additive (attr := simps -fullyApplied)
  /-- Given a pair of additive monoid homomorphisms `f`, `g` such that `g.comp f = id`
  and `f.comp g = id`, returns an additive equivalence with `toFun = f` and `invFun = g`. This
  constructor is useful if the underlying type(s) have specialized `ext` lemmas for additive
  monoid homomorphisms. -/]
/--
Definition of `MonoidHom.toMulEquiv` / `MonoidHom.toMulEquiv` 的定义

English:
definition MonoidHom.toMulEquiv
  signature: [MulOneClass M] [MulOneClass N] (f : M ->* N) (g : N ->* M)
  body: f
  invFun := g
  left_inv := DFunLike.congr_fun h₁
  right_inv := DFunLike.congr_fun h₂
  map_mul' := f.map_mul

中文:
定义 MonoidHom.toMulEquiv
  签名: [MulOneClass M] [MulOneClass N] (f : M ->* N) (g : N ->* M)
  定义体: f
  invFun := g
  left_inv := DFunLike.congr_fun h₁
  right_inv := DFunLike.congr_fun h₂
  map_mul' := f.map_mul
-/
def MonoidHom.toMulEquiv [MulOneClass M] [MulOneClass N] (f : M ->* N) (g : N ->* M)
    (h₁ : g.comp f = MonoidHom.id _) (h₂ : f.comp g = MonoidHom.id _) : M ≃* N where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₁
  right_inv := DFunLike.congr_fun h₂
  map_mul' := f.map_mul

/-- The identity equivalence between the monoid of endomorphisms `Monoid.End M` and the type
`M →* M` of monoid homomorphisms from `M` to itself. `Monoid.End M` is definitionally (but not
reducibly) equal to `M →* M`. -/
@[to_additive /-- The identity equivalence between the additive monoid of endomorphisms
`AddMonoid.End M` and the type `M →+ M` of additive monoid homomorphisms from `M` to itself.
`AddMonoid.End M` is definitionally (but not reducibly) equal to `M →+ M`. -/]
/--
Definition of `Monoid.End.equiv` / `Monoid.End.equiv` 的定义

English:
definition Monoid.End.equiv
  signature: (M : Type*) [MulOne M]
  body: id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

@[to_additive (attr := simp)]

中文:
定义 Monoid.End.equiv
  签名: (M : 类型) [MulOne M]
  定义体: id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

@[to_additive (attr := simp)]
-/
def Monoid.End.equiv (M : Type*) [MulOne M] : Monoid.End M ≃ (M ->* M) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

@[to_additive (attr := simp)]
/--
theorem `Monoid.End.equiv_apply` / 定理 `Monoid.End.equiv_apply`

English:
theorem Monoid.End.equiv_apply
  given: {M : Type*} [MulOne M] (f : Monoid.End M) (x : M)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 Monoid.End.equiv_apply
  条件: {M : 类型} [MulOne M] (f : Monoid.End M) (x : M)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem Monoid.End.equiv_apply {M : Type*} [MulOne M] (f : Monoid.End M) (x : M) :
    Monoid.End.equiv M f x = f x := rfl

@[to_additive (attr := simp)]
/--
theorem `Monoid.End.equiv_symm_apply` / 定理 `Monoid.End.equiv_symm_apply`

English:
theorem Monoid.End.equiv_symm_apply
  given: {M : Type*} [MulOne M] (f : M ->* M) (x : M)
  proof: rfl

中文:
定理 Monoid.End.equiv_symm_apply
  条件: {M : 类型} [MulOne M] (f : M ->* M) (x : M)
  证明: rfl
-/
theorem Monoid.End.equiv_symm_apply {M : Type*} [MulOne M] (f : M ->* M) (x : M) :
    (Monoid.End.equiv M).symm f x = f x := rfl
