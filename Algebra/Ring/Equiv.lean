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


/-- makes a `NonUnitalRingHom` from the bijective inverse of a `NonUnitalRingHom` -/
/-
**NonUnitalRingHom.inverse** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalRingHom`。
形式化陈述：{R : Type u_4} →   {S : Type u_5} →     [inst : NonUnitalNonAssocSemiring 
R] →       [inst_1 : NonUnitalNonAssocSemiring S] →         (f : R →ₙ+* S) → (g 
: S → R) → Function.LeftInverse g ⇑f → Function.RightInverse g ⇑f → S →ₙ+* R
参数：f : R →ₙ+* S；g : S → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
makes a `NonUnitalRingHom` from the bijective inverse of a `NonUnitalRingHom`
-/
@[simps] def NonUnitalRingHom.inverse
    [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    (f : R →ₙ+* S) (g : S → R)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : S →ₙ+* R :=
  { (f : R →+ S).inverse g h₁ h₂, (f : R →ₙ* S).inverse g h₁ h₂ with toFun := g }

/-- makes a `RingHom` from the bijective inverse of a `RingHom` -/
/-
**RingHom.inverse** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：{R : Type u_4} →   {S : Type u_5} →     [inst : NonAssocSemiring R] →     
  [inst_1 : NonAssocSemiring S] →         (f : R →+* S) → (g : S → R) → Function
.LeftInverse g ⇑f → Function.RightInverse g ⇑f → S →+* R
参数：f : R →+* S；g : S → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
makes a `RingHom` from the bijective inverse of a `RingHom`
-/
@[simps] def RingHom.inverse [NonAssocSemiring R] [NonAssocSemiring S]
    (f : RingHom R S) (g : S → R)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : S →+* R :=
  { (f : OneHom R S).inverse g h₁,
    (f : MulHom R S).inverse g h₁ h₂,
    (f : R →+ S).inverse g h₁ h₂ with toFun := g }

/-- An equivalence between two (non-unital non-associative semi)rings that preserves the
algebraic structure. -/
/-
**RingEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_7) → (S : Type u_8) → [Mul R] → [Mul S] → [Add R] → [Add S] → 
Type (max u_7 u_8)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between two (non-unital non-associative semi)rings that preserves
 the
algebraic structure.
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

/-- `RingEquivClass F R S` states that `F` is a type of ring structure preserving equivalences.
You should extend this class when you extend `RingEquiv`. -/
/-
**RingEquivClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_7) → (R : Type u_8) → (S : Type u_9) → [Mul R] → [Add R] → [Mu
l S] → [Add S] → [EquivLike F R S] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RingEquivClass F R S` states that `F` is a type of ring structure preserving eq
uivalences.
You should extend this class when you extend `RingEquiv`.
-/
class RingEquivClass (F R S : Type*) [Mul R] [Add R] [Mul S] [Add S] [EquivLike F R S] : Prop
  extends MulEquivClass F R S where
  /-- By definition, a ring isomorphism preserves the additive structure. -/
  map_add : ∀ (f : F) (a b), f (a + b) = f a + f b

namespace RingEquivClass

variable [EquivLike F R S]

-- See note [lower instance priority]
/-
**RingEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `RingEquivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toAddEquivClass [Mul R] [Add R]
    [Mul S] [Add S] [h : RingEquivClass F R S] : AddEquivClass F R S :=
  { h with }

-- See note [lower instance priority]
/-
**RingEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `RingEquivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toRingHomClass [NonAssocSemiring R] [NonAssocSemiring S]
    [h : RingEquivClass F R S] : RingHomClass F R S :=
  { h with
    map_zero := map_zero
    map_one := map_one }

-- See note [lower instance priority]
/-
**RingEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `RingEquivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toNonUnitalRingHomClass [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] [h : RingEquivClass F R S] : NonUnitalRingHomClass F R S :=
  { h with
    map_zero := map_zero }

/-- Turn an element of a type `F` satisfying `RingEquivClass F α β` into an actual
`RingEquiv`. This is declared as the default coercion from `F` to `α ≃+* β`. -/
@[coe]
/-
**RingEquivClass.toRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RingEquivClass`。
形式化陈述：toRingEquiv [Mul α] [Add α] [Mul β] [Add β] [EquivLike F α β] [RingEquivCl
ass F α β] (f : F) : α ≃+* β
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `RingEquivClass.toAddEquivClass`：∀ {F : Type u_1} {R : Type u_4} {S : Typ
e u_5} [inst : EquivLike F R S] [inst_1 : Mul R] [inst_2 : Add R]   [inst_3 : Mu
l S] [inst_4 : Add S…
· 使用定理 `MulEquiv.map_mul'`：∀ {M : Type u_9} {N : Type u_10} [inst : Mul M] [inst
_1 : Mul N] (self : M ≃* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toFun…
· 使用定理 `AddEquiv.map_add'`：∀ {A : Type u_9} {B : Type u_10} [inst : Add A] [inst
_1 : Add B] (self : A ≃+ B) (x y : A),   self.toFun (x + y) = self.toFun x + sel
f.toFun…

--- 原说明 ---
Turn an element of a type `F` satisfying `RingEquivClass F α β` into an actual
`RingEquiv`. This is declared as the default coercion from `F` to `α ≃+* β`.
-/
def toRingEquiv [Mul α] [Add α] [Mul β] [Add β] [EquivLike F α β] [RingEquivClass F α β] (f : F) :
    α ≃+* β :=
  { (f : α ≃* β), (f : α ≃+ β) with }

end RingEquivClass

namespace RingEquiv

section Basic

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

section coe

/-
**RingEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `RingEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**RingEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `RingEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RingEquivClass (R ≃+* S) R S where
  map_add f := f.map_add'
  map_mul f := f.map_mul'

/-- Two ring isomorphisms agree if they are defined by the same underlying function. -/
@[ext]
/-
**RingEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g

--- 原说明 ---
Two ring isomorphisms agree if they are defined by the same underlying function.
-/
theorem ext {f g : R ≃+* S} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h
/-
**RingEquiv.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [inst_1 : Mul S] [inst_2 : 
Add R] [inst_3 : Add S] {f : R ≃+* S}   {x x' : R}, x = x' → f x = f x'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
-/
protected theorem congr_arg {f : R ≃+* S} {x x' : R} : x = x' → f x = f x' :=
  DFunLike.congr_arg f
/-
**RingEquiv.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [inst_1 : Mul S] [inst_2 : 
Add R] [inst_3 : Add S] {f g : R ≃+* S},   f = g → ∀ (x : R), f x = g x
参数：x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun {f g : R ≃+* S} (h : f = g) (x : R) : f x = g x :=
  DFunLike.congr_fun h x

@[simp]
/-
**RingEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_mk (e h₃ h₄) : ⇑(⟨e, h₃, h₄⟩ : R ≃+* S) = e
参数：e h₃ h₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (e h₃ h₄) : ⇑(⟨e, h₃, h₄⟩ : R ≃+* S) = e :=
  rfl

@[simp]
/-
**RingEquiv.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：mk_coe (e : R ≃+* S) (e' h₁ h₂ h₃ h₄) : (⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩ : R ≃+*
 S) = e
参数：e : R ≃+* S；e' h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
-/
theorem mk_coe (e : R ≃+* S) (e' h₁ h₂ h₃ h₄) : (⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩ : R ≃+* S) = e :=
  ext fun _ => rfl

@[simp]
/-
**RingEquiv.toEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toEquiv_eq_coe (f : R ≃+* S) : f.toEquiv = f
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_eq_coe (f : R ≃+* S) : f.toEquiv = f :=
  rfl

@[simp]
/-
**RingEquiv.coe_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_toEquiv (f : R ≃+* S) : ⇑(f : R ≃ S) = f
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEquiv (f : R ≃+* S) : ⇑(f : R ≃ S) = f :=
  rfl

@[simp]
/-
**RingEquiv.toAddEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toAddEquiv_eq_coe (f : R ≃+* S) : f.toAddEquiv = ↑f
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddEquiv_eq_coe (f : R ≃+* S) : f.toAddEquiv = ↑f :=
  rfl

@[simp]
/-
**RingEquiv.toMulEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toMulEquiv_eq_coe (f : R ≃+* S) : f.toMulEquiv = ↑f
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMulEquiv_eq_coe (f : R ≃+* S) : f.toMulEquiv = ↑f :=
  rfl

@[simp, norm_cast]
/-
**RingEquiv.coe_toMulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_toMulEquiv (f : R ≃+* S) : ⇑(f : R ≃* S) = f
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem coe_toMulEquiv (f : R ≃+* S) : ⇑(f : R ≃* S) = f :=
  rfl

@[simp]
/-
**RingEquiv.coe_toAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_toAddEquiv (f : R ≃+* S) : ⇑(f : R ≃+ S) = f
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toAddEquivClass`：∀ {F : Type u_1} {R : Type u_4} {S : Typ
e u_5} [inst : EquivLike F R S] [inst_1 : Mul R] [inst_2 : Add R]   [inst_3 : Mu
l S] [inst_4 : Add S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem coe_toAddEquiv (f : R ≃+* S) : ⇑(f : R ≃+ S) = f :=
  rfl

end coe

section map

/-- A ring isomorphism preserves multiplication. -/
/-
**RingEquiv.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [inst_1 : Mul S] [inst_2 : 
Add R] [inst_3 : Add S] (e : R ≃+* S)   (x y : R), e (x * y) = e x * e y
参数：e : R ≃+* S；x y : R；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S

--- 原说明 ---
A ring isomorphism preserves multiplication.
-/
protected theorem map_mul (e : R ≃+* S) (x y : R) : e (x * y) = e x * e y :=
  map_mul e x y

/-- A ring isomorphism preserves addition. -/
/-
**RingEquiv.map_add** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [inst_1 : Mul S] [inst_2 : 
Add R] [inst_3 : Add S] (e : R ≃+* S)   (x y : R), e (x + y) = e x + e y
参数：e : R ≃+* S；x y : R；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddEquivClass.instAddHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Add M] [inst_1 : Add N] [inst_2 : EquivLike F M N]   [h : AddEquiv
Class F M N], AddHo…
· 使用定理 `RingEquivClass.toAddEquivClass`：∀ {F : Type u_1} {R : Type u_4} {S : Typ
e u_5} [inst : EquivLike F R S] [inst_1 : Mul R] [inst_2 : Add R]   [inst_3 : Mu
l S] [inst_4 : Add S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S

--- 原说明 ---
A ring isomorphism preserves addition.
-/
protected theorem map_add (e : R ≃+* S) (x y : R) : e (x + y) = e x + e y :=
  map_add e x y

end map

section bijective

/-
**RingEquiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [inst_1 : Mul S] [inst_2 : 
Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijective ⇑e
参数：e : R ≃+* S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.bijective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Bijective ⇑e
-/
protected theorem bijective (e : R ≃+* S) : Function.Bijective e :=
  EquivLike.bijective e
/-
**RingEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [inst_1 : Mul S] [inst_2 : 
Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injective ⇑e
参数：e : R ≃+* S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
-/
protected theorem injective (e : R ≃+* S) : Function.Injective e :=
  EquivLike.injective e
/-
**RingEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [inst_1 : Mul S] [inst_2 : 
Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjective ⇑e
参数：e : R ≃+* S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
-/
protected theorem surjective (e : R ≃+* S) : Function.Surjective e :=
  EquivLike.surjective e

end bijective

variable (R)

section refl

/-- The identity map is a ring isomorphism. -/
@[refl]
/-
**RingEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：refl : R ≃+* R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.map_mul'`：∀ {M : Type u_9} {N : Type u_10} [inst : Mul M] [inst
_1 : Mul N] (self : M ≃* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toFun…
· 使用定理 `AddEquiv.map_add'`：∀ {A : Type u_9} {B : Type u_10} [inst : Add A] [inst
_1 : Add B] (self : A ≃+ B) (x y : A),   self.toFun (x + y) = self.toFun x + sel
f.toFun…

--- 原说明 ---
The identity map is a ring isomorphism.
-/
def refl : R ≃+* R :=
  { MulEquiv.refl R, AddEquiv.refl R with }
/-
**RingEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `RingEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (R ≃+* R) :=
  ⟨RingEquiv.refl R⟩

@[simp]
/-
**RingEquiv.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：refl_apply (x : R) : RingEquiv.refl R x = x
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_apply (x : R) : RingEquiv.refl R x = x :=
  rfl

@[simp]
/-
**RingEquiv.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_refl (R : Type*) [Mul R] [Add R] : ⇑(RingEquiv.refl R) = id
参数：R : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl (R : Type*) [Mul R] [Add R] : ⇑(RingEquiv.refl R) = id :=
  rfl

@[simp]
/-
**RingEquiv.coe_addEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_addEquiv_refl : (RingEquiv.refl R : R ≃+ R) = AddEquiv.refl R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toAddEquivClass`：∀ {F : Type u_1} {R : Type u_4} {S : Typ
e u_5} [inst : EquivLike F R S] [inst_1 : Mul R] [inst_2 : Add R]   [inst_3 : Mu
l S] [inst_4 : Add S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem coe_addEquiv_refl : (RingEquiv.refl R : R ≃+ R) = AddEquiv.refl R :=
  rfl

@[simp]
/-
**RingEquiv.coe_mulEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_mulEquiv_refl : (RingEquiv.refl R : R ≃* R) = MulEquiv.refl R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem coe_mulEquiv_refl : (RingEquiv.refl R : R ≃* R) = MulEquiv.refl R :=
  rfl

end refl

variable {R}

section symm

/-- The inverse of a ring isomorphism is a ring isomorphism. -/
@[symm]
/-
**RingEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：{R : Type u_4} →   {S : Type u_5} → [inst : Mul R] → [inst_1 : Mul S] → [i
nst_2 : Add R] → [inst_3 : Add S] → R ≃+* S → S ≃+* R
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.map_mul'`：∀ {M : Type u_9} {N : Type u_10} [inst : Mul M] [inst
_1 : Mul N] (self : M ≃* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toFun…
· 使用定理 `AddEquiv.map_add'`：∀ {A : Type u_9} {B : Type u_10} [inst : Add A] [inst
_1 : Add B] (self : A ≃+ B) (x y : A),   self.toFun (x + y) = self.toFun x + sel
f.toFun…

--- 原说明 ---
The inverse of a ring isomorphism is a ring isomorphism.
-/
protected def symm (e : R ≃+* S) : S ≃+* R :=
  { e.toMulEquiv.symm, e.toAddEquiv.symm with }

@[simp]
/-
**RingEquiv.invFun_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：invFun_eq_symm (f : R ≃+* S) : EquivLike.inv f = f.symm
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invFun_eq_symm (f : R ≃+* S) : EquivLike.inv f = f.symm :=
  rfl

@[simp]
/-
**RingEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：symm_symm (e : R ≃+* S) : e.symm.symm = e
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (e : R ≃+* S) : e.symm.symm = e := rfl
/-
**RingEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：symm_bijective : Function.Bijective (RingEquiv.symm : (R ≃+* S) -> S ≃+* R
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `RingEquiv.symm_symm`：symm_symm (e : R ≃+* S) : e.symm.symm = e
-/
theorem symm_bijective : Function.Bijective (RingEquiv.symm : (R ≃+* S) → S ≃+* R) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/-
**RingEquiv.mk_coe'** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：mk_coe' (e : R ≃+* S) (f h₁ h₂ h₃ h₄) : (⟨⟨f, ⇑e, h₁, h₂⟩, h₃, h₄⟩ : S ≃+*
 R) = e.symm
参数：e : R ≃+* S；f h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `RingEquiv.symm_bijective`：symm_bijective : Function.Bijective (RingEquiv
.symm : (R ≃+* S) -> S ≃+* R)
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
-/
theorem mk_coe' (e : R ≃+* S) (f h₁ h₂ h₃ h₄) :
    (⟨⟨f, ⇑e, h₁, h₂⟩, h₃, h₄⟩ : S ≃+* R) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl

@[simp]
/-
**RingEquiv.symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：symm_mk (e : R ≃ S) (h₁ h₂) : dsimp% (mk e h₁ h₂).symm = { (mk e h₁ h₂).sy
mm with toEquiv
参数：e : R ≃ S；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_mk (e : R ≃ S) (h₁ h₂) : dsimp%
    (mk e h₁ h₂).symm =
      { (mk e h₁ h₂).symm with
        toEquiv := e.symm } :=
  rfl

@[simp]
/-
**RingEquiv.symm_refl** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：symm_refl : (RingEquiv.refl R).symm = RingEquiv.refl R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_refl : (RingEquiv.refl R).symm = RingEquiv.refl R :=
  rfl

@[simp]
/-
**RingEquiv.coe_toEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_toEquiv_symm (e : R ≃+* S) : (e.symm : S ≃ R) = (e : R ≃ S).symm
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEquiv_symm (e : R ≃+* S) : (e.symm : S ≃ R) = (e : R ≃ S).symm :=
  rfl

@[simp]
/-
**RingEquiv.coe_toMulEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_toMulEquiv_symm (e : R ≃+* S) : (e.symm : S ≃* R) = (e : R ≃* S).symm
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem coe_toMulEquiv_symm (e : R ≃+* S) : (e.symm : S ≃* R) = (e : R ≃* S).symm :=
  rfl

@[simp]
/-
**RingEquiv.coe_toAddEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_toAddEquiv_symm (e : R ≃+* S) : (e.symm : S ≃+ R) = (e : R ≃+ S).symm
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toAddEquivClass`：∀ {F : Type u_1} {R : Type u_4} {S : Typ
e u_5} [inst : EquivLike F R S] [inst_1 : Mul R] [inst_2 : Add R]   [inst_3 : Mu
l S] [inst_4 : Add S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem coe_toAddEquiv_symm (e : R ≃+* S) : (e.symm : S ≃+ R) = (e : R ≃+ S).symm :=
  rfl

@[simp]
/-
**RingEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：apply_symm_apply (e : R ≃+* S) : forall x, e (e.symm x) = x
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem apply_symm_apply (e : R ≃+* S) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply

@[simp]
/-
**RingEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：symm_apply_apply (e : R ≃+* S) : forall x, e.symm (e x) = x
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem symm_apply_apply (e : R ≃+* S) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply
/-
**RingEquiv.image_symm_eq_preimage** 是 Mathlib 中的一个引理，位于命名空间 `RingEquiv`。
形式化陈述：image_symm_eq_preimage (e : R ≃+* S) (s : Set S) : e.symm '' s = e ⁻¹' s
参数：e : R ≃+* S；s : Set S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_symm_eq_preimage`：image_symm_eq_preimage (e : α ≃ β) (s : Se
t β) : e.symm '' s = e ⁻¹' s
-/
lemma image_symm_eq_preimage (e : R ≃+* S) (s : Set S) : e.symm '' s = e ⁻¹' s :=
  e.toEquiv.image_symm_eq_preimage _
/-
**RingEquiv.image_eq_preimage_symm** 是 Mathlib 中的一个引理，位于命名空间 `RingEquiv`。
形式化陈述：image_eq_preimage_symm (e : R ≃+* S) (s : Set R) : e '' s = e.symm ⁻¹' s
参数：e : R ≃+* S；s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
lemma image_eq_preimage_symm (e : R ≃+* S) (s : Set R) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage_symm _

@[simp]
/-
**RingEquiv.coe_coe_toEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `RingEquiv`。
形式化陈述：coe_coe_toEquiv_symm (e : R ≃+* S) : ⇑(e : R ≃ S).symm = ⇑e.symm
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma coe_coe_toEquiv_symm (e : R ≃+* S) : ⇑(e : R ≃ S).symm = ⇑e.symm := rfl

@[simp]
/-
**RingEquiv.coe_coe_toMulEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `RingEquiv`。
形式化陈述：coe_coe_toMulEquiv_symm (e : R ≃+* S) : ⇑(e : R ≃* S).symm = ⇑e.symm
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
lemma coe_coe_toMulEquiv_symm (e : R ≃+* S) : ⇑(e : R ≃* S).symm = ⇑e.symm := rfl

@[simp]
/-
**RingEquiv.coe_coe_toAddEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `RingEquiv`。
形式化陈述：coe_coe_toAddEquiv_symm (e : R ≃+* S) : ⇑(e : R ≃+ S).symm = ⇑e.symm
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toAddEquivClass`：∀ {F : Type u_1} {R : Type u_4} {S : Typ
e u_5} [inst : EquivLike F R S] [inst_1 : Mul R] [inst_2 : Add R]   [inst_3 : Mu
l S] [inst_4 : Add S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
lemma coe_coe_toAddEquiv_symm (e : R ≃+* S) : ⇑(e : R ≃+ S).symm = ⇑e.symm := rfl
/-
**RingEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：symm_apply_eq (e : R ≃+* S) {x : S} {y : R} : e.symm x = y ↔ x = e y
参数：e : R ≃+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq (e : R ≃+* S) {x : S} {y : R} :
    e.symm x = y ↔ x = e y := Equiv.symm_apply_eq _
/-
**RingEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：eq_symm_apply (e : R ≃+* S) {x : S} {y : R} : y = e.symm x ↔ e y = x
参数：e : R ≃+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply (e : R ≃+* S) {x : S} {y : R} :
    y = e.symm x ↔ e y = x := Equiv.eq_symm_apply _

end symm

section simps

/-- See Note [custom simps projection] -/
/-
**RingEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv.Simps`。
形式化陈述：{R : Type u_4} →   {S : Type u_5} → [inst : Mul R] → [inst_1 : Mul S] → [i
nst_2 : Add R] → [inst_3 : Add S] → R ≃+* S → S → R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (e : R ≃+* S) : S → R :=
  e.symm

initialize_simps_projections RingEquiv (toFun → apply, invFun → symm_apply)

end simps

section trans

/-- Transitivity of `RingEquiv`. -/
@[trans]
/-
**RingEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：{R : Type u_4} →   {S : Type u_5} →     {S' : Type u_6} →       [inst : Mu
l R] →         [inst_1 : Mul S] →           [inst_2 : Add R] → [inst_3 : Add S] 
→ [inst_4 : Mul S'] → [inst_5 : Add S'] → R ≃+* S → S ≃+* S' → R ≃+* S'
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.map_mul'`：∀ {M : Type u_9} {N : Type u_10} [inst : Mul M] [inst
_1 : Mul N] (self : M ≃* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toFun…
· 使用定理 `AddEquiv.map_add'`：∀ {A : Type u_9} {B : Type u_10} [inst : Add A] [inst
_1 : Add B] (self : A ≃+ B) (x y : A),   self.toFun (x + y) = self.toFun x + sel
f.toFun…

--- 原说明 ---
Transitivity of `RingEquiv`.
-/
protected def trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : R ≃+* S' :=
  { e₁.toMulEquiv.trans e₂.toMulEquiv, e₁.toAddEquiv.trans e₂.toAddEquiv with }

@[simp]
/-
**RingEquiv.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂ : R -> S') = e₂ ∘ 
e₁
参数：e₁ : R ≃+* S；e₂ : S ≃+* S'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂ : R → S') = e₂ ∘ e₁ :=
  rfl
/-
**RingEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : R) : e₁.trans e₂ a = e₂ (e
₁ a)
参数：e₁ : R ≃+* S；e₂ : S ≃+* S'；a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : R) : e₁.trans e₂ a = e₂ (e₁ a) :=
  rfl

@[simp]
/-
**RingEquiv.symm_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：symm_trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : S') : (e₁.trans e₂).s
ymm a = e₁.symm (e₂.symm a)
参数：e₁ : R ≃+* S；e₂ : S ≃+* S'；a : S'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : S') :
    (e₁.trans e₂).symm a = e₁.symm (e₂.symm a) :=
  rfl
/-
**RingEquiv.symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：symm_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂).symm = e₂.symm.t
rans e₁.symm
参数：e₁ : R ≃+* S；e₂ : S ≃+* S'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl

@[simp]
/-
**RingEquiv.coe_mulEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_mulEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂ : R ≃* S'
) = (e₁ : R ≃* S).trans ↑e₂
参数：e₁ : R ≃+* S；e₂ : S ≃+* S'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem coe_mulEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R ≃* S') = (e₁ : R ≃* S).trans ↑e₂ :=
  rfl

@[simp]
/-
**RingEquiv.coe_addEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_addEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂ : R ≃+ S'
) = (e₁ : R ≃+ S).trans ↑e₂
参数：e₁ : R ≃+* S；e₂ : S ≃+* S'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toAddEquivClass`：∀ {F : Type u_1} {R : Type u_4} {S : Typ
e u_5} [inst : EquivLike F R S] [inst_1 : Mul R] [inst_2 : Add R]   [inst_3 : Mu
l S] [inst_4 : Add S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem coe_addEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R ≃+ S') = (e₁ : R ≃+ S).trans ↑e₂ :=
  rfl

end trans

section unique

/-- The `RingEquiv` between two semirings with a unique element. -/
/-
**RingEquiv.ofUnique** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：ofUnique {M N} [Unique M] [Unique N] [Add M] [Mul M] [Add N] [Mul N] : M ≃
+* N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.map_mul'`：∀ {M : Type u_9} {N : Type u_10} [inst : Mul M] [inst
_1 : Mul N] (self : M ≃* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toFun…
· 使用定理 `AddEquiv.map_add'`：∀ {A : Type u_9} {B : Type u_10} [inst : Add A] [inst
_1 : Add B] (self : A ≃+ B) (x y : A),   self.toFun (x + y) = self.toFun x + sel
f.toFun…

--- 原说明 ---
The `RingEquiv` between two semirings with a unique element.
-/
def ofUnique {M N} [Unique M] [Unique N] [Add M] [Mul M] [Add N] [Mul N] : M ≃+* N :=
  { AddEquiv.ofUnique, MulEquiv.ofUnique with }
/-
**RingEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `RingEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
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
/-
**RingEquiv.op** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：{α : Type u_7} →   {β : Type u_8} → [inst : Add α] → [inst_1 : Mul α] → [i
nst_2 : Add β] → [inst_3 : Mul β] → α ≃+* β ≃ (αᵐᵒᵖ ≃+* βᵐᵒᵖ)
参数：αᵐᵒᵖ ≃+* βᵐᵒᵖ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MulEquiv.map_mul'`：∀ {M : Type u_9} {N : Type u_10} [inst : Mul M] [inst
_1 : Mul N] (self : M ≃* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toFun…
· 使用定理 `AddEquiv.map_add'`：∀ {A : Type u_9} {B : Type u_10} [inst : Add A] [inst
_1 : Add B] (self : A ≃+ B) (x y : A),   self.toFun (x + y) = self.toFun x + sel
f.toFun…

--- 原说明 ---
A ring iso `α ≃+* β` can equivalently be viewed as a ring iso `αᵐᵒᵖ ≃+* βᵐᵒᵖ`.
-/
protected def op {α β} [Add α] [Mul α] [Add β] [Mul β] :
    α ≃+* β ≃ (αᵐᵒᵖ ≃+* βᵐᵒᵖ) where
  toFun f := { AddEquiv.mulOp f.toAddEquiv, MulEquiv.op f.toMulEquiv with }
  invFun f := { AddEquiv.mulOp.symm f.toAddEquiv, MulEquiv.op.symm f.toMulEquiv with }

/-- The 'unopposite' of a ring iso `αᵐᵒᵖ ≃+* βᵐᵒᵖ`. Inverse to `RingEquiv.op`. -/
@[simp]
/-
**RingEquiv.unop** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：{α : Type u_7} →   {β : Type u_8} → [inst : Add α] → [inst_1 : Mul α] → [i
nst_2 : Add β] → [inst_3 : Mul β] → αᵐᵒᵖ ≃+* βᵐᵒᵖ ≃ (α ≃+* β)
参数：α ≃+* β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The 'unopposite' of a ring iso `αᵐᵒᵖ ≃+* βᵐᵒᵖ`. Inverse to `RingEquiv.op`.
-/
protected def unop {α β} [Add α] [Mul α] [Add β] [Mul β] : αᵐᵒᵖ ≃+* βᵐᵒᵖ ≃ (α ≃+* β) :=
  RingEquiv.op.symm

/-- A ring is isomorphic to the opposite of its opposite. -/
@[simps!]
/-
**RingEquiv.opOp** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：opOp (R : Type*) [Add R] [Mul R] : R ≃+* Rᵐᵒᵖᵐᵒᵖ where __
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring is isomorphic to the opposite of its opposite.
-/
def opOp (R : Type*) [Add R] [Mul R] : R ≃+* Rᵐᵒᵖᵐᵒᵖ where
  __ := MulEquiv.opOp R
  map_add' _ _ := rfl

section NonUnitalCommSemiring

variable (R) [NonUnitalCommSemiring R]

/-- A non-unital commutative ring is isomorphic to its opposite. -/
/-
**RingEquiv.toOpposite** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：toOpposite : R ≃+* Rᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital commutative ring is isomorphic to its opposite.
-/
def toOpposite : R ≃+* Rᵐᵒᵖ :=
  { MulOpposite.opEquiv with
    map_add' := fun _ _ => rfl
    map_mul' := fun x y => mul_comm (op y) (op x) }

@[simp]
/-
**RingEquiv.toOpposite_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toOpposite_apply (r : R) : toOpposite R r = op r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOpposite_apply (r : R) : toOpposite R r = op r :=
  rfl

@[simp]
/-
**RingEquiv.toOpposite_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toOpposite_symm_apply (r : Rᵐᵒᵖ) : (toOpposite R).symm r = unop r
参数：r : Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOpposite_symm_apply (r : Rᵐᵒᵖ) : (toOpposite R).symm r = unop r :=
  rfl

end NonUnitalCommSemiring

end Opposite

section NonUnitalSemiring

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R ≃+* S) (x : R)

/-- A ring isomorphism sends zero to zero. -/
/-
**RingEquiv.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} [inst : NonUnitalNonAssocSemiring R] [inst
_1 : NonUnitalNonAssocSemiring S]   (f : R ≃+* S), f 0 = 0
参数：f : R ≃+* S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S

--- 原说明 ---
A ring isomorphism sends zero to zero.
-/
protected theorem map_zero : f 0 = 0 :=
  map_zero f

variable {x}
/-
**RingEquiv.map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} [inst : NonUnitalNonAssocSemiring R] [inst
_1 : NonUnitalNonAssocSemiring S]   (f : R ≃+* S) {x : R}, f x = 0 ↔ x = 0
参数：f : R ≃+* S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EmbeddingLike.map_eq_zero_iff`：∀ {F : Type u_1} {M : Type u_4} {N : Type
 u_5} [inst : Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [EmbeddingLik
e F M N] [ZeroHomCl…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
protected theorem map_eq_zero_iff : f x = 0 ↔ x = 0 :=
  EmbeddingLike.map_eq_zero_iff
/-
**RingEquiv.map_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：map_ne_zero_iff : f x != 0 ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EmbeddingLike.map_ne_zero_iff`：∀ {F : Type u_1} {M : Type u_4} {N : Type
 u_5} [inst : Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [EmbeddingLik
e F M N] [ZeroHomCl…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem map_ne_zero_iff : f x ≠ 0 ↔ x ≠ 0 :=
  EmbeddingLike.map_ne_zero_iff

variable [FunLike F R S]

/-- Produce a ring isomorphism from a bijective ring homomorphism. -/
/-
**RingEquiv.ofBijective** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：ofBijective [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective
 f) : R ≃+* S
参数：f : F；hf : Function.Bijective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produce a ring isomorphism from a bijective ring homomorphism.
-/
noncomputable def ofBijective [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f) :
    R ≃+* S :=
  { Equiv.ofBijective f hf with
    map_mul' := map_mul f
    map_add' := map_add f }

@[simp]
/-
**RingEquiv.coe_ofBijective** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_ofBijective [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijec
tive f) : (ofBijective f hf : R -> S) = f
参数：f : F；hf : Function.Bijective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofBijective [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f) :
    (ofBijective f hf : R → S) = f :=
  rfl
/-
**RingEquiv.ofBijective_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：ofBijective_apply [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bij
ective f) (x : R) : ofBijective f hf x = f x
参数：f : F；hf : Function.Bijective f；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBijective_apply [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f)
    (x : R) : ofBijective f hf x = f x :=
  rfl

@[simp]
/-
**RingEquiv.ofBijective_symm_comp** 是 Mathlib 中的一个引理，位于命名空间 `RingEquiv`。
形式化陈述：ofBijective_symm_comp (f : R ->ₙ+* S) (hf : Function.Bijective f) : ((Ring
Equiv.ofBijective f hf).symm : _ ->ₙ+* _).comp f = NonUnitalRingHom.id R
参数：f : R ->ₙ+* S；hf : Function.Bijective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
-/
lemma ofBijective_symm_comp (f : R →ₙ+* S) (hf : Function.Bijective f) :
    ((RingEquiv.ofBijective f hf).symm : _ →ₙ+* _).comp f = NonUnitalRingHom.id R := by
  ext
  exact (RingEquiv.ofBijective f hf).injective <| RingEquiv.apply_symm_apply ..

@[simp]
/-
**RingEquiv.comp_ofBijective_symm** 是 Mathlib 中的一个引理，位于命名空间 `RingEquiv`。
形式化陈述：comp_ofBijective_symm (f : R ->ₙ+* S) (hf : Function.Bijective f) : f.comp
 ((RingEquiv.ofBijective f hf).symm : _ ->ₙ+* _) = NonUnitalRingHom.id S
参数：f : R ->ₙ+* S；hf : Function.Bijective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
-/
lemma comp_ofBijective_symm (f : R →ₙ+* S) (hf : Function.Bijective f) :
    f.comp ((RingEquiv.ofBijective f hf).symm : _ →ₙ+* _) = NonUnitalRingHom.id S := by
  ext
  exact (RingEquiv.ofBijective f hf).symm.injective <| RingEquiv.apply_symm_apply ..

/-- Product of a singleton family of (non-unital non-associative semi)rings is isomorphic
to the only member of this family. -/
@[simps! -fullyApplied]
/-
**RingEquiv.piUnique** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：piUnique {ι : Type*} (R : ι -> Type*) [Unique ι] [forall i, NonUnitalNonAs
socSemiring (R i)] : (forall i, R i) ≃+* R default where __
参数：R : ι -> Type*；R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of a singleton family of (non-unital non-associative semi)rings is isomo
rphic
to the only member of this family.
-/
def piUnique {ι : Type*} (R : ι → Type*) [Unique ι] [∀ i, NonUnitalNonAssocSemiring (R i)] :
    (∀ i, R i) ≃+* R default where
  __ := Equiv.piUnique R
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- `Equiv.cast (congrArg _ h)` as a ring equiv.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an equality of types,
to avoid having to deal with an equality of the algebraic structure itself. -/
@[simps!]
/-
**RingEquiv.cast** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：{ι : Type u_7} →   {R : ι → Type u_8} → [inst : (i : ι) → Mul (R i)] → [in
st_1 : (i : ι) → Add (R i)] → {i j : ι} → i = j → R i ≃+* R j
参数：i : ι；R i；i : ι；R i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.cast (congrArg _ h)` as a ring equiv.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an 
equality of types,
to avoid having to deal with an equality of the algebraic structure itself.
-/
protected def cast
    {ι : Type*} {R : ι → Type*} [∀ i, Mul (R i)] [∀ i, Add (R i)] {i j : ι} (h : i = j) :
    R i ≃+* R j where
  __ := AddEquiv.cast h
  __ := MulEquiv.cast h

/-- A family of ring isomorphisms `∀ j, (R j ≃+* S j)` generates a
ring isomorphisms between `∀ j, R j` and `∀ j, S j`.

This is the `RingEquiv` version of `Equiv.piCongrRight`, and the dependent version of
`RingEquiv.arrowCongr`.
-/
@[simps apply]
/-
**RingEquiv.piCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：piCongrRight {ι : Type*} {R S : ι -> Type*} [forall i, NonUnitalNonAssocSe
miring (R i)] [forall i, NonUnitalNonAssocSemiring (S i)] (e : forall i, R i ≃+*
 S i) : (forall i, R i) ≃+* forall i, S i
参数：R i；S i；e : forall i, R i ≃+* S i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of ring isomorphisms `∀ j, (R j ≃+* S j)` generates a
ring isomorphisms between `∀ j, R j` and `∀ j, S j`.

This is the `RingEquiv` version of `Equiv.piCongrRight`, and the dependent versi
on of
`RingEquiv.arrowCongr`.
-/
def piCongrRight {ι : Type*} {R S : ι → Type*} [∀ i, NonUnitalNonAssocSemiring (R i)]
    [∀ i, NonUnitalNonAssocSemiring (S i)] (e : ∀ i, R i ≃+* S i) : (∀ i, R i) ≃+* ∀ i, S i :=
  { @MulEquiv.piCongrRight ι R S _ _ fun i => (e i).toMulEquiv,
    @AddEquiv.piCongrRight ι R S _ _ fun i => (e i).toAddEquiv with
    toFun := fun x j => e j (x j)
    invFun := fun x j => (e j).symm (x j) }

@[simp]
/-
**RingEquiv.piCongrRight_refl** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：piCongrRight_refl {ι : Type*} {R : ι -> Type*} [forall i, NonUnitalNonAsso
cSemiring (R i)] : (piCongrRight fun i => RingEquiv.refl (R i)) = RingEquiv.refl
 _
参数：R i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_refl {ι : Type*} {R : ι → Type*} [∀ i, NonUnitalNonAssocSemiring (R i)] :
    (piCongrRight fun i => RingEquiv.refl (R i)) = RingEquiv.refl _ :=
  rfl

@[simp]
/-
**RingEquiv.piCongrRight_symm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：piCongrRight_symm {ι : Type*} {R S : ι -> Type*} [forall i, NonUnitalNonAs
socSemiring (R i)] [forall i, NonUnitalNonAssocSemiring (S i)] (e : forall i, R 
i ≃+* S i) : (piCongrRight e).symm = piCongrRight fun i => (e i).symm
参数：R i；S i；e : forall i, R i ≃+* S i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_symm {ι : Type*} {R S : ι → Type*} [∀ i, NonUnitalNonAssocSemiring (R i)]
    [∀ i, NonUnitalNonAssocSemiring (S i)] (e : ∀ i, R i ≃+* S i) :
    (piCongrRight e).symm = piCongrRight fun i => (e i).symm :=
  rfl

@[simp]
/-
**RingEquiv.piCongrRight_trans** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：piCongrRight_trans {ι : Type*} {R S T : ι -> Type*} [forall i, NonUnitalNo
nAssocSemiring (R i)] [forall i, NonUnitalNonAssocSemiring (S i)] [forall i, Non
UnitalNonAssocSemiring (T i)] (e : forall i, R i ≃+* S i) (f : forall i, S i ≃+*
 T i) : (piCongrRight e).trans (piCongrRight f) = piCongrRight fun i => (e i).tr
ans (f i)
参数：R i；S i；T i；e : forall i, R i ≃+* S i；f : forall i, S i ≃+* T i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_trans {ι : Type*} {R S T : ι → Type*}
    [∀ i, NonUnitalNonAssocSemiring (R i)] [∀ i, NonUnitalNonAssocSemiring (S i)]
    [∀ i, NonUnitalNonAssocSemiring (T i)] (e : ∀ i, R i ≃+* S i) (f : ∀ i, S i ≃+* T i) :
    (piCongrRight e).trans (piCongrRight f) = piCongrRight fun i => (e i).trans (f i) :=
  rfl

/-- Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft'` as a `RingEquiv`. -/
@[simps!]
/-
**RingEquiv.piCongrLeft'** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：piCongrLeft' {ι ι' : Type*} (R : ι -> Type*) (e : ι ≃ ι') [forall i, NonUn
italNonAssocSemiring (R i)] : ((i : ι) -> R i) ≃+* ((i : ι') -> R (e.symm i)) wh
ere toEquiv
参数：R : ι -> Type*；e : ι ≃ ι'；R i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft'` as a `RingEquiv`.
-/
def piCongrLeft' {ι ι' : Type*} (R : ι → Type*) (e : ι ≃ ι')
    [∀ i, NonUnitalNonAssocSemiring (R i)] :
    ((i : ι) → R i) ≃+* ((i : ι') → R (e.symm i)) where
  toEquiv := Equiv.piCongrLeft' R e
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
/-
**RingEquiv.piCongrLeft'_symm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {R : Type u_7} [inst : NonUnitalNonAssocSe
miring R] (e : α ≃ β),   (RingEquiv.piCongrLeft' (fun x => R) e).symm = RingEqui
v.piCongrLeft' (fun i => R) e.symm
参数：e : α ≃ β；RingEquiv.piCongrLeft' (fun x => R) e；fun i => R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulEquiv.map_mul'`：∀ {M : Type u_9} {N : Type u_10} [inst : Mul M] [inst
_1 : Mul N] (self : M ≃* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toFun…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MulEquiv.symm_map_mul`：symm_map_mul {M N : Type*} [Mul M] [Mul N] (h : M
 ≃* N) (x y : N) : h.symm (x * y) = h.symm x * h.symm y
· 使用定理 `Equiv.piCongrLeft'_symm`：∀ {α : Sort u_1} {β : Sort u_4} (P : Sort u_9) 
(e : α ≃ β),   (Equiv.piCongrLeft' (fun x => P) e).symm = Equiv.piCongrLeft' (fu
n a => P) e.s…
· 使用定理 `MulEquiv.mk.congr_simp`：∀ {M : Type u_9} {N : Type u_10} [inst : Mul M] 
[inst_1 : Mul N] (toEquiv toEquiv_1 : M ≃ N)   (e_toEquiv : toEquiv = toEquiv_1)
 (map_mul' :…
· 使用定理 `AddEquiv.map_add'`：∀ {A : Type u_9} {B : Type u_10} [inst : Add A] [inst
_1 : Add B] (self : A ≃+ B) (x y : A),   self.toFun (x + y) = self.toFun x + sel
f.toFun…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingEquiv.mk.congr_simp`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] 
[inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S]   (toEquiv toEquiv_1 : R ≃ S)
 (e_toEquiv :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-
**RingEquiv.piCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：piCongrLeft {ι ι' : Type*} (S : ι' -> Type*) (e : ι ≃ ι') [forall i, NonUn
italNonAssocSemiring (S i)] : ((i : ι) -> S (e i)) ≃+* ((i : ι') -> S i)
参数：S : ι' -> Type*；e : ι ≃ ι'；S i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft` as a `RingEquiv`.
-/
def piCongrLeft {ι ι' : Type*} (S : ι' → Type*) (e : ι ≃ ι')
    [∀ i, NonUnitalNonAssocSemiring (S i)] :
    ((i : ι) → S (e i)) ≃+* ((i : ι') → S i) :=
  (RingEquiv.piCongrLeft' S e.symm).symm

/-- Splits the indices of ring `∀ (i : ι), Y i` along the predicate `p`. This is
`Equiv.piEquivPiSubtypeProd` as a `RingEquiv`. -/
@[simps!]
/-
**RingEquiv.piEquivPiSubtypeProd** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：piEquivPiSubtypeProd {ι : Type*} (p : ι -> Prop) [DecidablePred p] (Y : ι 
-> Type*) [forall i, NonUnitalNonAssocSemiring (Y i)] : ((i : ι) -> Y i) ≃+* ((i
 : { x : ι // p x }) -> Y i) × ((i : { x : ι // ¬p x }) -> Y i) where toEquiv
参数：p : ι -> Prop；Y : ι -> Type*；Y i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Splits the indices of ring `∀ (i : ι), Y i` along the predicate `p`. This is
`Equiv.piEquivPiSubtypeProd` as a `RingEquiv`.
-/
def piEquivPiSubtypeProd {ι : Type*} (p : ι → Prop) [DecidablePred p] (Y : ι → Type*)
    [∀ i, NonUnitalNonAssocSemiring (Y i)] :
    ((i : ι) → Y i) ≃+* ((i : { x : ι // p x }) → Y i) × ((i : { x : ι // ¬p x }) → Y i) where
  toEquiv := Equiv.piEquivPiSubtypeProd p Y
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The opposite of a direct product is isomorphic to the direct product of the opposites
as rings. -/
/-
**RingEquiv.piMulOpposite** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：piMulOpposite {ι : Type*} (S : ι -> Type*) [forall i, NonUnitalNonAssocSem
iring (S i)] : (Π i, S i)ᵐᵒᵖ ≃+* Π i, (S i)ᵐᵒᵖ where toFun f i
参数：S : ι -> Type*；S i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a direct product is isomorphic to the direct product of the oppo
sites
as rings.
-/
def piMulOpposite {ι : Type*} (S : ι → Type*) [∀ i, NonUnitalNonAssocSemiring (S i)] :
    (Π i, S i)ᵐᵒᵖ ≃+* Π i, (S i)ᵐᵒᵖ where
  toFun f i := .op (f.unop i)
  invFun f := .op fun i ↦ (f i).unop
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Product of ring equivalences. This is `Equiv.prodCongr` as a `RingEquiv`. -/
@[simps!]
/-
**RingEquiv.prodCongr** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：prodCongr {R R' S S' : Type*} [NonUnitalNonAssocSemiring R] [NonUnitalNonA
ssocSemiring R'] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S'] (f
 : R ≃+* R') (g : S ≃+* S') : R × S ≃+* R' × S' where toEquiv
参数：f : R ≃+* R'；g : S ≃+* S'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of ring equivalences. This is `Equiv.prodCongr` as a `RingEquiv`.
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
/-
**RingEquiv.coe_prodCongr** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_prodCongr {R R' S S' : Type*} [NonUnitalNonAssocSemiring R] [NonUnital
NonAssocSemiring R'] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S'
] (f : R ≃+* R') (g : S ≃+* S') : ⇑(RingEquiv.prodCongr f g) = Prod.map f g
参数：f : R ≃+* R'；g : S ≃+* S'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodCongr {R R' S S' : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring R'] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']
    (f : R ≃+* R') (g : S ≃+* S') :
    ⇑(RingEquiv.prodCongr f g) = Prod.map f g :=
  rfl

/-- This is `Equiv.piOptionEquivProd` as a `RingEquiv`. -/
@[simps!]
/-
**RingEquiv.piOptionEquivProd** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：piOptionEquivProd {ι : Type*} {R : Option ι -> Type*} [Π i, NonUnitalNonAs
socSemiring (R i)] : (Π i, R i) ≃+* R none × (Π i, R (some i)) where toEquiv
参数：R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is `Equiv.piOptionEquivProd` as a `RingEquiv`.
-/
def piOptionEquivProd {ι : Type*} {R : Option ι → Type*} [Π i, NonUnitalNonAssocSemiring (R i)] :
    (Π i, R i) ≃+* R none × (Π i, R (some i)) where
  toEquiv := Equiv.piOptionEquivProd
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end NonUnitalSemiring

section Semiring

variable [NonAssocSemiring R] [NonAssocSemiring S] (f : R ≃+* S) (x : R)

/-- A ring isomorphism sends one to one. -/
/-
**RingEquiv.map_one** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} [inst : NonAssocSemiring R] [inst_1 : NonA
ssocSemiring S] (f : R ≃+* S), f 1 = 1
参数：f : R ≃+* S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S

--- 原说明 ---
A ring isomorphism sends one to one.
-/
protected theorem map_one : f 1 = 1 :=
  map_one f

variable {x}
/-
**RingEquiv.map_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} [inst : NonAssocSemiring R] [inst_1 : NonA
ssocSemiring S] (f : R ≃+* S) {x : R},   f x = 1 ↔ x = 1
参数：f : R ≃+* S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EmbeddingLike.map_eq_one_iff`：map_eq_one_iff {f : F} {x : M} : f x = 1 ↔
 x = 1
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
protected theorem map_eq_one_iff : f x = 1 ↔ x = 1 :=
  EmbeddingLike.map_eq_one_iff
/-
**RingEquiv.map_ne_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：map_ne_one_iff : f x != 1 ↔ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EmbeddingLike.map_ne_one_iff`：map_ne_one_iff {f : F} {x : M} : f x != 1 
↔ x != 1
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem map_ne_one_iff : f x ≠ 1 ↔ x ≠ 1 :=
  EmbeddingLike.map_ne_one_iff
/-
**RingEquiv.coe_monoidHom_refl** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_monoidHom_refl : (RingEquiv.refl R : R ->* R) = MonoidHom.id R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem coe_monoidHom_refl : (RingEquiv.refl R : R →* R) = MonoidHom.id R :=
  rfl

@[simp]
/-
**RingEquiv.coe_addMonoidHom_refl** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_addMonoidHom_refl : (RingEquiv.refl R : R ->+ R) = AddMonoidHom.id R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem coe_addMonoidHom_refl : (RingEquiv.refl R : R →+ R) = AddMonoidHom.id R :=
  rfl

/-! `RingEquiv.coe_mulEquiv_refl` and `RingEquiv.coe_addEquiv_refl` are proved above
in higher generality -/


@[simp]
/-
**RingEquiv.coe_ringHom_refl** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_ringHom_refl : (RingEquiv.refl R : R ->+* R) = RingHom.id R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S

--- 原说明 ---
`RingEquiv.coe_mulEquiv_refl` and `RingEquiv.coe_addEquiv_refl` are proved above
in higher generality
-/
theorem coe_ringHom_refl : (RingEquiv.refl R : R →+* R) = RingHom.id R :=
  rfl

@[simp]
/-
**RingEquiv.coe_monoidHom_trans** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_monoidHom_trans [NonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
 (e₁.trans e₂ : R ->* S') = (e₂ : S ->* S').comp ↑e₁
参数：e₁ : R ≃+* S；e₂ : S ≃+* S'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem coe_monoidHom_trans [NonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R →* S') = (e₂ : S →* S').comp ↑e₁ :=
  rfl

@[simp]
/-
**RingEquiv.coe_addMonoidHom_trans** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_addMonoidHom_trans [NonUnitalNonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ :
 S ≃+* S') : (e₁.trans e₂ : R ->+ S') = (e₂ : S ->+ S').comp ↑e₁
参数：e₁ : R ≃+* S；e₂ : S ≃+* S'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem coe_addMonoidHom_trans [NonUnitalNonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R →+ S') = (e₂ : S →+ S').comp ↑e₁ :=
  rfl

/-! `RingEquiv.coe_mulEquiv_trans` and `RingEquiv.coe_addEquiv_trans` are proved above
in higher generality -/

@[simp]
/-
**RingEquiv.coe_ringHom_trans** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_ringHom_trans [NonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (
e₁.trans e₂ : R ->+* S') = (e₂ : S ->+* S').comp ↑e₁
参数：e₁ : R ≃+* S；e₂ : S ≃+* S'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S

--- 原说明 ---
`RingEquiv.coe_mulEquiv_trans` and `RingEquiv.coe_addEquiv_trans` are proved abo
ve
in higher generality
-/
theorem coe_ringHom_trans [NonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R →+* S') = (e₂ : S →+* S').comp ↑e₁ :=
  rfl

@[simp]
/-
**RingEquiv.comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：comp_symm (e : R ≃+* S) : (e : R ->+* S).comp (e.symm : S ->+* R) = RingHo
m.id S
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
-/
theorem comp_symm (e : R ≃+* S) : (e : R →+* S).comp (e.symm : S →+* R) = RingHom.id S :=
  RingHom.ext e.apply_symm_apply

@[simp]
/-
**RingEquiv.symm_comp** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：symm_comp (e : R ≃+* S) : (e.symm : S ->+* R).comp (e : R ->+* S) = RingHo
m.id R
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
-/
theorem symm_comp (e : R ≃+* S) : (e.symm : S →+* R).comp (e : R →+* S) = RingHom.id R :=
  RingHom.ext e.symm_apply_apply

end Semiring

section NonUnitalRing

variable [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] (f : R ≃+* S) (x y : R)

/-
**RingEquiv.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} [inst : NonUnitalNonAssocRing R] [inst_1 :
 NonUnitalNonAssocRing S] (f : R ≃+* S)   (x : R), f (-x) = -f x
参数：f : R ≃+* S；x : R；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
protected theorem map_neg : f (-x) = -f x :=
  map_neg f x
/-
**RingEquiv.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} [inst : NonUnitalNonAssocRing R] [inst_1 :
 NonUnitalNonAssocRing S] (f : R ≃+* S)   (x y : R), f (x - y) = f x - f y
参数：f : R ≃+* S；x y : R；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
protected theorem map_sub : f (x - y) = f x - f y :=
  map_sub f x y

end NonUnitalRing

section Ring

variable [NonAssocRing R] [NonAssocRing S] (f : R ≃+* S)

@[simp]
/-
**RingEquiv.map_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：map_neg_one : f (-1) = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.map_neg`：∀ {R : Type u_4} {S : Type u_5} [inst : NonUnitalNonA
ssocRing R] [inst_1 : NonUnitalNonAssocRing S] (f : R ≃+* S)   (x : R), f (-x) =
 -f x
· 使用定理 `RingEquiv.map_one`：∀ {R : Type u_4} {S : Type u_5} [inst : NonAssocSemir
ing R] [inst_1 : NonAssocSemiring S] (f : R ≃+* S), f 1 = 1
-/
theorem map_neg_one : f (-1) = -1 :=
  f.map_one ▸ f.map_neg 1
/-
**RingEquiv.map_eq_neg_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：map_eq_neg_one_iff {x : R} : f x = -1 ↔ x = -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.map_eq_one_iff`：∀ {R : Type u_4} {S : Type u_5} [inst : NonAss
ocSemiring R] [inst_1 : NonAssocSemiring S] (f : R ≃+* S) {x : R},   f x = 1 ↔ x
 = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_eq_neg_one_iff {x : R} : f x = -1 ↔ x = -1 := by
  rw [← neg_eq_iff_eq_neg, ← neg_eq_iff_eq_neg, ← map_neg, RingEquiv.map_eq_one_iff]

end Ring

section NonUnitalSemiringHom

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']

/-- Reinterpret a ring equivalence as a non-unital ring homomorphism. -/
/-
**RingEquiv.toNonUnitalRingHom** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：toNonUnitalRingHom (e : R ≃+* S) : R ->ₙ+* S
参数：e : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a ring equivalence as a non-unital ring homomorphism.
-/
def toNonUnitalRingHom (e : R ≃+* S) : R →ₙ+* S :=
  { e.toMulEquiv.toMulHom, e.toAddEquiv.toAddMonoidHom with }
/-
**RingEquiv.toNonUnitalRingHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toNonUnitalRingHom_injective : Function.Injective (toNonUnitalRingHom : R 
≃+* S -> R ->ₙ+* S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NonUnitalRingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : NonUni
talNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β]   {f g : α →ₙ+* β}
, f = g ↔ ∀ (x…
-/
theorem toNonUnitalRingHom_injective :
    Function.Injective (toNonUnitalRingHom : R ≃+* S → R →ₙ+* S) := fun _ _ h =>
  RingEquiv.ext (NonUnitalRingHom.ext_iff.1 h)
/-
**RingEquiv.toNonUnitalRingHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toNonUnitalRingHom_eq_coe (f : R ≃+* S) : f.toNonUnitalRingHom = ↑f
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNonUnitalRingHom_eq_coe (f : R ≃+* S) : f.toNonUnitalRingHom = ↑f :=
  rfl

@[simp, norm_cast]
/-
**RingEquiv.coe_toNonUnitalRingHom** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_toNonUnitalRingHom (f : R ≃+* S) : ⇑(f : R ->ₙ+* S) = f
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem coe_toNonUnitalRingHom (f : R ≃+* S) : ⇑(f : R →ₙ+* S) = f :=
  rfl

@[simp]
/-
**RingEquiv.coe_toNonUnitalRingHom'** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_toNonUnitalRingHom' (f : R ≃+* S) : ⇑f.toNonUnitalRingHom = f
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toNonUnitalRingHom' (f : R ≃+* S) : ⇑f.toNonUnitalRingHom = f :=
  rfl
/-
**RingEquiv.coe_nonUnitalRingHom_inj_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_nonUnitalRingHom_inj_iff {R S : Type*} [NonUnitalNonAssocSemiring R] [
NonUnitalNonAssocSemiring S] (f g : R ≃+* S) : f = g ↔ (f : R ->ₙ+* S) = g
参数：f g : R ≃+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NonUnitalRingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : NonUni
talNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β]   {f g : α →ₙ+* β}
, f = g ↔ ∀ (x…
-/
theorem coe_nonUnitalRingHom_inj_iff {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f g : R ≃+* S) : f = g ↔ (f : R →ₙ+* S) = g :=
  ⟨fun h => by rw [h], fun h => ext <| NonUnitalRingHom.ext_iff.mp h⟩

@[simp]
/-
**RingEquiv.toNonUnitalRingHom_refl** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toNonUnitalRingHom_refl : (RingEquiv.refl R).toNonUnitalRingHom = NonUnita
lRingHom.id R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNonUnitalRingHom_refl :
    (RingEquiv.refl R).toNonUnitalRingHom = NonUnitalRingHom.id R :=
  rfl

@[deprecated apply_symm_apply (since := "2026-06-16")]
/-
**RingEquiv.toNonUnitalRingHom_apply_symm_toNonUnitalRingHom_apply** 是 Mathlib 中
的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toNonUnitalRingHom_apply_symm_toNonUnitalRingHom_apply (e : R ≃+* S) : for
all y : S, e.toNonUnitalRingHom (e.symm.toNonUnitalRingHom y) = y
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem toNonUnitalRingHom_apply_symm_toNonUnitalRingHom_apply (e : R ≃+* S) :
    ∀ y : S, e.toNonUnitalRingHom (e.symm.toNonUnitalRingHom y) = y :=
  e.toEquiv.apply_symm_apply

@[deprecated symm_apply_apply (since := "2026-06-16")]
/-
**RingEquiv.symm_toNonUnitalRingHom_apply_toNonUnitalRingHom_apply** 是 Mathlib 中
的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：symm_toNonUnitalRingHom_apply_toNonUnitalRingHom_apply (e : R ≃+* S) : for
all x : R, e.symm.toNonUnitalRingHom (e.toNonUnitalRingHom x) = x
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem symm_toNonUnitalRingHom_apply_toNonUnitalRingHom_apply (e : R ≃+* S) :
    ∀ x : R, e.symm.toNonUnitalRingHom (e.toNonUnitalRingHom x) = x :=
  Equiv.symm_apply_apply e.toEquiv

@[simp]
/-
**RingEquiv.toNonUnitalRingHom_trans** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toNonUnitalRingHom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂).to
NonUnitalRingHom = e₂.toNonUnitalRingHom.comp e₁.toNonUnitalRingHom
参数：e₁ : R ≃+* S；e₂ : S ≃+* S'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNonUnitalRingHom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂).toNonUnitalRingHom = e₂.toNonUnitalRingHom.comp e₁.toNonUnitalRingHom :=
  rfl

@[simp]
/-
**RingEquiv.toNonUnitalRingHomm_comp_symm_toNonUnitalRingHom** 是 Mathlib 中的一个定理，
位于命名空间 `RingEquiv`。
形式化陈述：toNonUnitalRingHomm_comp_symm_toNonUnitalRingHom (e : R ≃+* S) : e.toNonUn
italRingHom.comp e.symm.toNonUnitalRingHom = NonUnitalRingHom.id _
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toNonUnitalRingHomm_comp_symm_toNonUnitalRingHom (e : R ≃+* S) :
    e.toNonUnitalRingHom.comp e.symm.toNonUnitalRingHom = NonUnitalRingHom.id _ := by
  ext
  simp

@[simp]
/-
**RingEquiv.symm_toNonUnitalRingHom_comp_toNonUnitalRingHom** 是 Mathlib 中的一个定理，位
于命名空间 `RingEquiv`。
形式化陈述：symm_toNonUnitalRingHom_comp_toNonUnitalRingHom (e : R ≃+* S) : e.symm.toN
onUnitalRingHom.comp e.toNonUnitalRingHom = NonUnitalRingHom.id _
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_toNonUnitalRingHom_comp_toNonUnitalRingHom (e : R ≃+* S) :
    e.symm.toNonUnitalRingHom.comp e.toNonUnitalRingHom = NonUnitalRingHom.id _ := by
  ext
  simp

end NonUnitalSemiringHom

section SemiringHom

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring S']

/-- Reinterpret a ring equivalence as a ring homomorphism. -/
/-
**RingEquiv.toRingHom** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：toRingHom (e : R ≃+* S) : R ->+* S
参数：e : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a ring equivalence as a ring homomorphism.
-/
def toRingHom (e : R ≃+* S) : R →+* S :=
  { e.toMulEquiv.toMonoidHom, e.toAddEquiv.toAddMonoidHom with }
/-
**RingEquiv.toRingHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toRingHom_injective : Function.Injective (toRingHom : R ≃+* S -> R ->+* S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g ↔ ∀ (x_2 : α), f x_2 = g x
_2
-/
theorem toRingHom_injective : Function.Injective (toRingHom : R ≃+* S → R →+* S) := fun _ _ h =>
  RingEquiv.ext (RingHom.ext_iff.1 h)
/-
**RingEquiv.toRingHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} [inst : NonAssocSemiring R] [inst_1 : NonA
ssocSemiring S] (f : R ≃+* S),   f.toRingHom = ↑f
参数：f : R ≃+* S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toRingHom_eq_coe (f : R ≃+* S) : f.toRingHom = ↑f :=
  rfl

@[simp, norm_cast]
/-
**RingEquiv.coe_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_toRingHom (f : R ≃+* S) : ⇑(f : R ->+* S) = f
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem coe_toRingHom (f : R ≃+* S) : ⇑(f : R →+* S) = f :=
  rfl
/-
**RingEquiv.coe_ringHom_inj_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_ringHom_inj_iff {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S
] (f g : R ≃+* S) : f = g ↔ (f : R ->+* S) = g
参数：f g : R ≃+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g ↔ ∀ (x_2 : α), f x_2 = g x
_2
-/
theorem coe_ringHom_inj_iff {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f g : R ≃+* S) : f = g ↔ (f : R →+* S) = g :=
  ⟨fun h => by rw [h], fun h => ext <| RingHom.ext_iff.mp h⟩

/-- The two paths coercion can take to a `NonUnitalRingEquiv` are equivalent -/
@[simp, norm_cast]
/-
**RingEquiv.toNonUnitalRingHom_commutes** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toNonUnitalRingHom_commutes (f : R ≃+* S) : ((f : R ->+* S) : R ->ₙ+* S) =
 (f : R ->ₙ+* S)
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S

--- 原说明 ---
The two paths coercion can take to a `NonUnitalRingEquiv` are equivalent
-/
theorem toNonUnitalRingHom_commutes (f : R ≃+* S) :
    ((f : R →+* S) : R →ₙ+* S) = (f : R →ₙ+* S) :=
  rfl

/-- Reinterpret a ring equivalence as a monoid homomorphism. -/
/-
**RingEquiv.toMonoidHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `RingEquiv`。
形式化陈述：toMonoidHom (e : R ≃+* S) : R ->* S
参数：e : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a ring equivalence as a monoid homomorphism.
-/
abbrev toMonoidHom (e : R ≃+* S) : R →* S :=
  e.toRingHom.toMonoidHom

/-- Reinterpret a ring equivalence as an `AddMonoid` homomorphism. -/
/-
**RingEquiv.toAddMonoidHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `RingEquiv`。
形式化陈述：toAddMonoidHom (e : R ≃+* S) : R ->+ S
参数：e : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a ring equivalence as an `AddMonoid` homomorphism.
-/
abbrev toAddMonoidHom (e : R ≃+* S) : R →+ S :=
  e.toRingHom.toAddMonoidHom

/-- The two paths coercion can take to an `AddMonoidHom` are equivalent -/
/-
**RingEquiv.toAddMonoidMom_commutes** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toAddMonoidMom_commutes (f : R ≃+* S) : (f : R ->+* S).toAddMonoidHom = (f
 : R ≃+ S).toAddMonoidHom
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S

--- 原说明 ---
The two paths coercion can take to an `AddMonoidHom` are equivalent
-/
theorem toAddMonoidMom_commutes (f : R ≃+* S) :
    (f : R →+* S).toAddMonoidHom = (f : R ≃+ S).toAddMonoidHom :=
  rfl

/-- The two paths coercion can take to a `MonoidHom` are equivalent -/
/-
**RingEquiv.toMonoidHom_commutes** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toMonoidHom_commutes (f : R ≃+* S) : (f : R ->+* S).toMonoidHom = (f : R ≃
* S).toMonoidHom
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S

--- 原说明 ---
The two paths coercion can take to a `MonoidHom` are equivalent
-/
theorem toMonoidHom_commutes (f : R ≃+* S) :
    (f : R →+* S).toMonoidHom = (f : R ≃* S).toMonoidHom :=
  rfl

/-- The two paths coercion can take to an `Equiv` are equivalent -/
/-
**RingEquiv.toEquiv_commutes** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toEquiv_commutes (f : R ≃+* S) : (f : R ≃+ S).toEquiv = (f : R ≃* S).toEqu
iv
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toAddEquivClass`：∀ {F : Type u_1} {R : Type u_4} {S : Typ
e u_5} [inst : EquivLike F R S] [inst_1 : Mul R] [inst_2 : Add R]   [inst_3 : Mu
l S] [inst_4 : Add S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S

--- 原说明 ---
The two paths coercion can take to an `Equiv` are equivalent
-/
theorem toEquiv_commutes (f : R ≃+* S) : (f : R ≃+ S).toEquiv = (f : R ≃* S).toEquiv :=
  rfl

@[simp]
/-
**RingEquiv.toRingHom_refl** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toRingHom_refl : (RingEquiv.refl R).toRingHom = RingHom.id R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRingHom_refl : (RingEquiv.refl R).toRingHom = RingHom.id R :=
  rfl

@[simp]
/-
**RingEquiv.toMonoidHom_refl** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toMonoidHom_refl : (RingEquiv.refl R).toMonoidHom = MonoidHom.id R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMonoidHom_refl : (RingEquiv.refl R).toMonoidHom = MonoidHom.id R :=
  rfl

@[simp]
/-
**RingEquiv.toAddMonoidHom_refl** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toAddMonoidHom_refl : (RingEquiv.refl R).toAddMonoidHom = AddMonoidHom.id 
R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddMonoidHom_refl : (RingEquiv.refl R).toAddMonoidHom = AddMonoidHom.id R :=
  rfl
/-
**RingEquiv.toRingHom_apply_symm_toRingHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ring
Equiv`。
形式化陈述：toRingHom_apply_symm_toRingHom_apply (e : R ≃+* S) : forall y : S, e.toRin
gHom (e.symm.toRingHom y) = y
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem toRingHom_apply_symm_toRingHom_apply (e : R ≃+* S) :
    ∀ y : S, e.toRingHom (e.symm.toRingHom y) = y :=
  e.toEquiv.apply_symm_apply
/-
**RingEquiv.symm_toRingHom_apply_toRingHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ring
Equiv`。
形式化陈述：symm_toRingHom_apply_toRingHom_apply (e : R ≃+* S) : forall x : R, e.symm.
toRingHom (e.toRingHom x) = x
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem symm_toRingHom_apply_toRingHom_apply (e : R ≃+* S) :
    ∀ x : R, e.symm.toRingHom (e.toRingHom x) = x :=
  Equiv.symm_apply_apply e.toEquiv

@[simp]
/-
**RingEquiv.toRingHom_trans** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toRingHom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂).toRingHom =
 e₂.toRingHom.comp e₁.toRingHom
参数：e₁ : R ≃+* S；e₂ : S ≃+* S'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRingHom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂).toRingHom = e₂.toRingHom.comp e₁.toRingHom :=
  rfl
/-
**RingEquiv.toRingHom_comp_symm_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toRingHom_comp_symm_toRingHom (e : R ≃+* S) : e.toRingHom.comp e.symm.toRi
ngHom = RingHom.id _
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.comp_symm`：comp_symm (e : R ≃+* S) : (e : R ->+* S).comp (e.sy
mm : S ->+* R) = RingHom.id S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toRingHom_comp_symm_toRingHom (e : R ≃+* S) :
    e.toRingHom.comp e.symm.toRingHom = RingHom.id _ := by
  simp
/-
**RingEquiv.symm_toRingHom_comp_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：symm_toRingHom_comp_toRingHom (e : R ≃+* S) : e.symm.toRingHom.comp e.toRi
ngHom = RingHom.id _
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.symm_comp`：symm_comp (e : R ≃+* S) : (e.symm : S ->+* R).comp 
(e : R ->+* S) = RingHom.id R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_toRingHom_comp_toRingHom (e : R ≃+* S) :
    e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := by
  simp

end SemiringHom

variable [Semiring R] [Semiring S]

section GroupPower

/-
**RingEquiv.map_pow** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u_4} {S : Type u_5} [inst : Semiring R] [inst_1 : Semiring S] 
(f : R ≃+* S) (a : R) (n : ℕ),   f (a ^ n) = f a ^ n
参数：f : R ≃+* S；a : R；n : ℕ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
protected theorem map_pow (f : R ≃+* S) (a) : ∀ n : ℕ, f (a ^ n) = f a ^ n :=
  map_pow f a

end GroupPower

end RingEquiv

namespace MulEquiv

/-- Gives a `RingEquiv` from an element of a `MulEquivClass` preserving addition. -/
/-
**MulEquiv.toRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：toRingEquiv {R S F : Type*} [Add R] [Add S] [Mul R] [Mul S] [EquivLike F R
 S] [MulEquivClass F R S] (f : F) (H : forall x y : R, f (x + y) = f x + f y) : 
R ≃+* S
参数：f : F；H : forall x y : R, f (x + y) = f x + f y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.map_mul'`：∀ {M : Type u_9} {N : Type u_10} [inst : Mul M] [inst
_1 : Mul N] (self : M ≃* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toFun…
· 使用定理 `AddEquiv.map_add'`：∀ {A : Type u_9} {B : Type u_10} [inst : Add A] [inst
_1 : Add B] (self : A ≃+ B) (x y : A),   self.toFun (x + y) = self.toFun x + sel
f.toFun…

--- 原说明 ---
Gives a `RingEquiv` from an element of a `MulEquivClass` preserving addition.
-/
def toRingEquiv {R S F : Type*} [Add R] [Add S] [Mul R] [Mul S] [EquivLike F R S]
    [MulEquivClass F R S] (f : F)
    (H : ∀ x y : R, f (x + y) = f x + f y) : R ≃+* S :=
  { (f : R ≃* S).toEquiv, (f : R ≃* S), AddEquiv.mk' (f : R ≃* S).toEquiv H with }

end MulEquiv

namespace AddEquiv

/-- Gives a `RingEquiv` from an element of an `AddEquivClass` preserving addition. -/
/-
**AddEquiv.toRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddEquiv`。
形式化陈述：toRingEquiv {R S F : Type*} [Add R] [Add S] [Mul R] [Mul S] [EquivLike F R
 S] [AddEquivClass F R S] (f : F) (H : forall x y : R, f (x * y) = f x * f y) : 
R ≃+* S
参数：f : F；H : forall x y : R, f (x * y) = f x * f y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.map_mul'`：∀ {M : Type u_9} {N : Type u_10} [inst : Mul M] [inst
_1 : Mul N] (self : M ≃* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toFun…
· 使用定理 `AddEquiv.map_add'`：∀ {A : Type u_9} {B : Type u_10} [inst : Add A] [inst
_1 : Add B] (self : A ≃+ B) (x y : A),   self.toFun (x + y) = self.toFun x + sel
f.toFun…

--- 原说明 ---
Gives a `RingEquiv` from an element of an `AddEquivClass` preserving addition.
-/
def toRingEquiv {R S F : Type*} [Add R] [Add S] [Mul R] [Mul S] [EquivLike F R S]
    [AddEquivClass F R S] (f : F)
    (H : ∀ x y : R, f (x * y) = f x * f y) : R ≃+* S :=
  { (f : R ≃+ S).toEquiv, (f : R ≃+ S), MulEquiv.mk' (f : R ≃+ S).toEquiv H with }

end AddEquiv

namespace RingEquiv

variable [Add R] [Add S] [Mul R] [Mul S]

@[simp]
/-
**RingEquiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：self_trans_symm (e : R ≃+* S) : e.trans e.symm = RingEquiv.refl R
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem self_trans_symm (e : R ≃+* S) : e.trans e.symm = RingEquiv.refl R :=
  ext e.left_inv

@[simp]
/-
**RingEquiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：symm_trans_self (e : R ≃+* S) : e.symm.trans e = RingEquiv.refl S
参数：e : R ≃+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem symm_trans_self (e : R ≃+* S) : e.symm.trans e = RingEquiv.refl S :=
  ext e.right_inv

end RingEquiv

namespace RingEquiv

section NonUnital

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

/-- If a non-unital ring homomorphism has an inverse, it is a ring isomorphism. -/
@[simps -isSimp]
/-
**RingEquiv.ofNonUnitalRingHom** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：ofNonUnitalRingHom (hom : R ->ₙ+* S) (inv : S ->ₙ+* R) (hom_inv_id : inv.c
omp hom = .id R) (inv_hom_id : hom.comp inv = .id S) : R ≃+* S where toFun
参数：hom : R ->ₙ+* S；inv : S ->ₙ+* R；hom_inv_id : inv.comp hom = .id R；inv_hom_id 
: hom.comp inv = .id S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a non-unital ring homomorphism has an inverse, it is a ring isomorphism.
-/
def ofNonUnitalRingHom (hom : R →ₙ+* S) (inv : S →ₙ+* R)
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
/-
**RingEquiv.symm_ofNonUnitalRingHom** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：symm_ofNonUnitalRingHom (f : R ->ₙ+* S) (g : S ->ₙ+* R) (h₁ h₂) : (ofNonUn
italRingHom f g h₁ h₂).symm = ofNonUnitalRingHom g f h₂ h₁
参数：f : R ->ₙ+* S；g : S ->ₙ+* R；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_ofNonUnitalRingHom (f : R →ₙ+* S) (g : S →ₙ+* R) (h₁ h₂) :
    (ofNonUnitalRingHom f g h₁ h₂).symm = ofNonUnitalRingHom g f h₂ h₁ :=
  rfl

end NonUnital

section Unital

variable [NonAssocSemiring R] [NonAssocSemiring S]

/-- If a ring homomorphism has an inverse, it is a ring isomorphism. -/
@[simps -isSimp]
/-
**RingEquiv.ofRingHom** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：ofRingHom (f : R ->+* S) (g : S ->+* R) (h₁ : f.comp g = RingHom.id S) (h₂
 : g.comp f = RingHom.id R) : R ≃+* S
参数：f : R ->+* S；g : S ->+* R；h₁ : f.comp g = RingHom.id S；h₂ : g.comp f = RingHo
m.id R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemiri
ng α] [inst_1 : NonAssocSemiring β] (self : α →+* β) (x y : α),   (↑↑self).toFun
 (x + …

--- 原说明 ---
If a ring homomorphism has an inverse, it is a ring isomorphism.
-/
def ofRingHom (f : R →+* S) (g : S →+* R) (h₁ : f.comp g = RingHom.id S)
    (h₂ : g.comp f = RingHom.id R) : R ≃+* S :=
  { f with
    toFun := f
    invFun := g
    left_inv := RingHom.ext_iff.1 h₂
    right_inv := RingHom.ext_iff.1 h₁ }

attribute [simp] ofRingHom_apply
/-
**RingEquiv.coe_ringHom_ofRingHom** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_ringHom_ofRingHom (f : R ->+* S) (g : S ->+* R) (h₁ h₂) : ofRingHom f 
g h₁ h₂ = f
参数：f : R ->+* S；g : S ->+* R；h₁ h₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem coe_ringHom_ofRingHom (f : R →+* S) (g : S →+* R) (h₁ h₂) : ofRingHom f g h₁ h₂ = f :=
  rfl

@[simp]
/-
**RingEquiv.ofRingHom_coe_ringHom** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：ofRingHom_coe_ringHom (f : R ≃+* S) (g : S ->+* R) (h₁ h₂) : ofRingHom (↑f
) g h₁ h₂ = f
参数：f : R ≃+* S；g : S ->+* R；h₁ h₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
-/
theorem ofRingHom_coe_ringHom (f : R ≃+* S) (g : S →+* R) (h₁ h₂) : ofRingHom (↑f) g h₁ h₂ = f :=
  ext fun _ ↦ rfl

@[simp]
/-
**RingEquiv.ofRingHom_symm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：ofRingHom_symm (f : R ->+* S) (g : S ->+* R) (h₁ h₂) : (ofRingHom f g h₁ h
₂).symm = ofRingHom g f h₂ h₁
参数：f : R ->+* S；g : S ->+* R；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRingHom_symm (f : R →+* S) (g : S →+* R) (h₁ h₂) :
    (ofRingHom f g h₁ h₂).symm = ofRingHom g f h₂ h₁ :=
  rfl

variable (α β R) in
/-- `Equiv.sumArrowEquivProdArrow` as a ring isomorphism. -/
/-
**RingEquiv.sumArrowEquivProdArrow** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：sumArrowEquivProdArrow : (α oplus β -> R) ≃+* (α -> R) × (β -> R) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.sumArrowEquivProdArrow` as a ring isomorphism.
-/
def sumArrowEquivProdArrow : (α ⊕ β → R) ≃+* (α → R) × (β → R) where
  __ := Equiv.sumArrowEquivProdArrow α β R
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/-
**RingEquiv.sumArrowEquivProdArrow_apply** 是 Mathlib 中的一个引理，位于命名空间 `RingEquiv`。
形式化陈述：sumArrowEquivProdArrow_apply (x) : sumArrowEquivProdArrow α β R x = Equiv.
sumArrowEquivProdArrow α β R x
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumArrowEquivProdArrow_apply (x) :
    sumArrowEquivProdArrow α β R x = Equiv.sumArrowEquivProdArrow α β R x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/-
**RingEquiv.sumArrowEquivProdArrow_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `RingEqu
iv`。
形式化陈述：sumArrowEquivProdArrow_symm_apply (x : (α -> R) × (β -> R)) : (sumArrowEqu
ivProdArrow α β R).symm x = (Equiv.sumArrowEquivProdArrow α β R).symm x
参数：x : (α -> R) × (β -> R)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumArrowEquivProdArrow_symm_apply (x : (α → R) × (β → R)) :
    (sumArrowEquivProdArrow α β R).symm x = (Equiv.sumArrowEquivProdArrow α β R).symm x := rfl

end Unital

end RingEquiv

namespace MulEquiv

/-- If two rings are isomorphic, and the second doesn't have zero divisors,
then so does the first. -/
/-
**MulEquiv.noZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {A : Type u_7} (B : Type u_8) [inst : MulZeroClass A] [inst_1 : MulZeroC
lass B] [NoZeroDivisors B] (e : A ≃* B),   NoZeroDivisors A
参数：B : Type u_8；e : A ≃* B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.noZeroDivisors`：∀ {M₀ : Type u_1} {M₀' : Type u_3} [i
nst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : M
₀ → M₀'),   Function.In…
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MulEquivClass.toZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : EquivLike F α β] [inst_1 : MulZeroClass α]   [inst_2 : MulZeroClass
 β] [MulEquivClass…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…

--- 原说明 ---
If two rings are isomorphic, and the second doesn't have zero divisors,
then so does the first.
-/
protected theorem noZeroDivisors {A : Type*} (B : Type*) [MulZeroClass A] [MulZeroClass B]
    [NoZeroDivisors B] (e : A ≃* B) : NoZeroDivisors A :=
  e.injective.noZeroDivisors e (map_zero e) (map_mul e)

/-- If two rings are isomorphic, and the second is a domain, then so is the first. -/
/-
**MulEquiv.isDomain** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {A : Type u_7} (B : Type u_8) [inst : Semiring A] [inst_1 : Semiring B] 
[IsDomain B] (e : A ≃* B), IsDomain A
参数：B : Type u_8；e : A ≃* B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isLeftCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u_
3} [inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (
f : M₀ → M₀'),   Function.In…
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `MulEquivClass.toMonoidWithZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulZeroOneClass α]   [inst_2 :
 MulZeroOneClass β] [MulEqui…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Function.Injective.isRightCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u
_3} [inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   
(f : M₀ → M₀'),   Function.In…
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
If two rings are isomorphic, and the second is a domain, then so is the first.
-/
protected theorem isDomain {A : Type*} (B : Type*) [Semiring A] [Semiring B] [IsDomain B]
    (e : A ≃* B) : IsDomain A :=
  { e.injective.isLeftCancelMulZero e (map_zero e) (map_mul e),
    e.injective.isRightCancelMulZero e (map_zero e) (map_mul e) with
    exists_pair_ne := ⟨e.symm 0, e.symm 1, e.symm.injective.ne zero_ne_one⟩ }
/-
**MulEquiv.isDomain_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：isDomain_iff {A B : Type*} [Semiring A] [Semiring B] (e : A ≃* B) : IsDoma
in A ↔ IsDomain B where mp _
参数：e : A ≃* B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.isDomain`：∀ {A : Type u_7} (B : Type u_8) [inst : Semiring A] [
inst_1 : Semiring B] [IsDomain B] (e : A ≃* B), IsDomain A
-/
theorem isDomain_iff {A B : Type*} [Semiring A] [Semiring B] (e : A ≃* B) :
    IsDomain A ↔ IsDomain B where
  mp _ := e.symm.isDomain
  mpr _ := e.isDomain

variable {A B : Type*} [MulZeroClass A] [MulZeroClass B]
/-
**MulEquiv.noZeroDivisors_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：noZeroDivisors_iff (e : A ≃* B) : NoZeroDivisors A ↔ NoZeroDivisors B wher
e mp _
参数：e : A ≃* B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.noZeroDivisors`：∀ {A : Type u_7} (B : Type u_8) [inst : MulZero
Class A] [inst_1 : MulZeroClass B] [NoZeroDivisors B] (e : A ≃* B),   NoZeroDivi
sors A
-/
theorem noZeroDivisors_iff (e : A ≃* B) : NoZeroDivisors A ↔ NoZeroDivisors B where
  mp _ := e.symm.noZeroDivisors
  mpr _ := e.noZeroDivisors
/-
**MulEquiv.isLeftCancelMulZero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：isLeftCancelMulZero_iff (e : A ≃* B) : IsLeftCancelMulZero A ↔ IsLeftCance
lMulZero B where mp _
参数：e : A ≃* B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isLeftCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u_
3} [inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (
f : M₀ → M₀'),   Function.In…
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MulEquivClass.toZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : EquivLike F α β] [inst_1 : MulZeroClass α]   [inst_2 : MulZeroClass
 β] [MulEquivClass…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
-/
theorem isLeftCancelMulZero_iff (e : A ≃* B) : IsLeftCancelMulZero A ↔ IsLeftCancelMulZero B where
  mp _ := e.symm.injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)
  mpr _ := e.injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)
/-
**MulEquiv.isRightCancelMulZero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：isRightCancelMulZero_iff (e : A ≃* B) : IsRightCancelMulZero A ↔ IsRightCa
ncelMulZero B where mp _
参数：e : A ≃* B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isRightCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u
_3} [inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   
(f : M₀ → M₀'),   Function.In…
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MulEquivClass.toZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : EquivLike F α β] [inst_1 : MulZeroClass α]   [inst_2 : MulZeroClass
 β] [MulEquivClass…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
-/
theorem isRightCancelMulZero_iff (e : A ≃* B) :
    IsRightCancelMulZero A ↔ IsRightCancelMulZero B where
  mp _ := e.symm.injective.isRightCancelMulZero _ (map_zero _) (map_mul _)
  mpr _ := e.injective.isRightCancelMulZero _ (map_zero _) (map_mul _)
/-
**MulEquiv.isCancelMulZero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：isCancelMulZero_iff (e : A ≃* B) : IsCancelMulZero A ↔ IsCancelMulZero B w
here mp _
参数：e : A ≃* B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u_3} [
inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : 
M₀ → M₀'),   Function.In…
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MulEquivClass.toZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : EquivLike F α β] [inst_1 : MulZeroClass α]   [inst_2 : MulZeroClass
 β] [MulEquivClass…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
-/
theorem isCancelMulZero_iff (e : A ≃* B) : IsCancelMulZero A ↔ IsCancelMulZero B where
  mp _ := e.symm.injective.isCancelMulZero _ (map_zero _) (map_mul _)
  mpr _ := e.injective.isCancelMulZero _ (map_zero _) (map_mul _)

end MulEquiv

