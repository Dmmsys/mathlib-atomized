/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Nailin Guan
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Topology.Algebra.Group.Defs

/-!

# Continuous Monoid Homs

This file defines the space of continuous homomorphisms between two topological groups.

## Main definitions

* `ContinuousMonoidHom A B`: The continuous homomorphisms `A →* B`.
* `ContinuousAddMonoidHom A B`: The continuous additive homomorphisms `A →+ B`.
-/

@[expose] public section

assert_not_exists ContinuousLinearMap
assert_not_exists ContinuousLinearEquiv

section

open Function Topology

variable (F A B C D E : Type*)
variable [Monoid A] [Monoid B] [Monoid C] [Monoid D]
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]

/-- The type of continuous additive monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : ContinuousAddMonoidHom A B)`,
you should parametrize
over `(F : Type*) [FunLike F A B] [ContinuousMapClass F A B] [AddMonoidHomClass F A B] (f : F)`.

When you extend this structure,
make sure to extend `ContinuousMapClass` and/or `AddMonoidHomClass`, if needed. -/
/-
**ContinuousAddMonoidHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_7) →   (B : Type u_8) → [AddMonoid A] → [AddMonoid B] → [Topol
ogicalSpace A] → [TopologicalSpace B] → Type (max u_7 u_8)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of continuous additive monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : ContinuousAddMonoidHo
m A B)`,
you should parametrize
over `(F : Type*) [FunLike F A B] [ContinuousMapClass F A B] [AddMonoidHomClass 
F A B] (f : F)`.

When you extend this structure,
make sure to extend `ContinuousMapClass` and/or `AddMonoidHomClass`, if needed.
-/
structure ContinuousAddMonoidHom (A B : Type*) [AddMonoid A] [AddMonoid B] [TopologicalSpace A]
  [TopologicalSpace B] extends A →+ B, C(A, B)

/-- The type of continuous monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : ContinuousMonoidHom A B)`,
you should parametrize
over `(F : Type*) [FunLike F A B] [ContinuousMapClass F A B] [MonoidHomClass F A B] (f : F)`.

When you extend this structure,
make sure to extend `ContinuousMapClass` and/or `MonoidHomClass`, if needed. -/
@[to_additive]
/-
**ContinuousMonoidHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_2) →   (B : Type u_3) → [Monoid A] → [Monoid B] → [Topological
Space A] → [TopologicalSpace B] → Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of continuous monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : ContinuousMonoidHom A
 B)`,
you should parametrize
over `(F : Type*) [FunLike F A B] [ContinuousMapClass F A B] [MonoidHomClass F A
 B] (f : F)`.

When you extend this structure,
make sure to extend `ContinuousMapClass` and/or `MonoidHomClass`, if needed.
-/
structure ContinuousMonoidHom extends A →* B, C(A, B)

/-- Reinterpret a `ContinuousMonoidHom` as a `MonoidHom`. -/
add_decl_doc ContinuousMonoidHom.toMonoidHom

/-- Reinterpret a `ContinuousAddMonoidHom` as an `AddMonoidHom`. -/
add_decl_doc ContinuousAddMonoidHom.toAddMonoidHom

/-- Reinterpret a `ContinuousMonoidHom` as a `ContinuousMap`. -/
add_decl_doc ContinuousMonoidHom.toContinuousMap

/-- Reinterpret a `ContinuousAddMonoidHom` as a `ContinuousMap`. -/
add_decl_doc ContinuousAddMonoidHom.toContinuousMap

namespace ContinuousMonoidHom

/-- The type of continuous monoid homomorphisms from `A` to `B`.-/
infixr:25 " →ₜ+ " => ContinuousAddMonoidHom
/-- The type of continuous monoid homomorphisms from `A` to `B`.-/
infixr:25 " →ₜ* " => ContinuousMonoidHom

variable {A B C D E}

@[to_additive]
/-
**ContinuousMonoidHom.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMonoidHom
`。
形式化陈述：instFunLike : FunLike (A ->ₜ* B) A B where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (A →ₜ* B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

@[to_additive]
/-
**ContinuousMonoidHom.instMonoidHomClass** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMo
noidHom`。
形式化陈述：instMonoidHomClass : MonoidHomClass (A ->ₜ* B) A B where map_mul f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
· 使用定理 `OneHom.map_one'`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [inst_
1 : One N] (self : OneHom M N), self.toFun 1 = 1
-/
instance instMonoidHomClass : MonoidHomClass (A →ₜ* B) A B where
  map_mul f := f.map_mul'
  map_one f := f.map_one'

@[to_additive]
/-
**ContinuousMonoidHom.instContinuousMapClass** 是 Mathlib 中的一个实例，位于命名空间 `Continuo
usMonoidHom`。
形式化陈述：instContinuousMapClass : ContinuousMapClass (A ->ₜ* B) A B where map_conti
nuous f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMonoidHom.continuous_toFun`：∀ {A : Type u_2} {B : Type u_3} [i
nst : Monoid A] [inst_1 : Monoid B] [inst_2 : TopologicalSpace A]   [inst_3 : To
pologicalSpace B] (self : …
-/
instance instContinuousMapClass : ContinuousMapClass (A →ₜ* B) A B where
  map_continuous f := f.continuous_toFun

@[to_additive (attr := simp)]
/-
**ContinuousMonoidHom.coe_toMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMonoi
dHom`。
形式化陈述：coe_toMonoidHom (f : A ->ₜ* B) : f.toMonoidHom = f
参数：f : A ->ₜ* B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toMonoidHom (f : A →ₜ* B) : f.toMonoidHom = f := rfl

@[to_additive (attr := simp)]
/-
**ContinuousMonoidHom.coe_toContinuousMap** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousM
onoidHom`。
形式化陈述：coe_toContinuousMap (f : A ->ₜ* B) : f.toContinuousMap = f
参数：f : A ->ₜ* B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toContinuousMap (f : A →ₜ* B) : f.toContinuousMap = f := rfl

section

variable {F : Type*} [FunLike F A B]

/-- Turn an element of a type `F` satisfying `MonoidHomClass F A B` and `ContinuousMapClass F A B`
into a `ContinuousMonoidHom`. This is declared as the default coercion from `F` to
`(A →ₜ* B)`. -/
@[to_additive (attr := coe) /-- Turn an element of a type `F` satisfying
`AddMonoidHomClass F A B` and `ContinuousMapClass F A B` into a `ContinuousAddMonoidHom`.
This is declared as the default coercion from `F` to `ContinuousAddMonoidHom A B`. -/]
/-
**ContinuousMonoidHom.toContinuousMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Continuou
sMonoidHom`。
形式化陈述：toContinuousMonoidHom [MonoidHomClass F A B] [ContinuousMapClass F A B] (f
 : F) : A ->ₜ* B
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toContinuousMonoidHom [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F) : A →ₜ* B :=
  { MonoidHomClass.toMonoidHom f with
    continuous_toFun := by dsimp; fun_prop }

/-- Any type satisfying `MonoidHomClass` and `ContinuousMapClass` can be cast into
`ContinuousMonoidHom` via `ContinuousMonoidHom.toContinuousMonoidHom`. -/
@[to_additive /-- Any type satisfying `AddMonoidHomClass` and `ContinuousMapClass` can be cast into
`ContinuousAddMonoidHom` via `ContinuousAddMonoidHom.toContinuousAddMonoidHom`. -/]
/-
**ContinuousMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MonoidHomClass F A B] [ContinuousMapClass F A B] : CoeOut F (A →ₜ* B) :=
  ⟨ContinuousMonoidHom.toContinuousMonoidHom⟩

@[to_additive (attr := simp)]
/-
**ContinuousMonoidHom.coe_coe** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：coe_coe [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F) : ⇑(f : 
A ->ₜ* B) = f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_coe [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F) :
    ⇑(f : A →ₜ* B) = f := rfl

@[to_additive (attr := simp, norm_cast)]
/-
**ContinuousMonoidHom.toMonoidHom_toContinuousMonoidHom** 是 Mathlib 中的一个引理，位于命名空
间 `ContinuousMonoidHom`。
形式化陈述：toMonoidHom_toContinuousMonoidHom [MonoidHomClass F A B] [ContinuousMapCla
ss F A B] (f : F) : ((f : A ->ₜ* B) : A ->* B) = f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toMonoidHom_toContinuousMonoidHom [MonoidHomClass F A B] [ContinuousMapClass F A B] (f : F) :
    ((f : A →ₜ* B) : A →* B) = f := rfl

@[to_additive (attr := simp, norm_cast)]
/-
**ContinuousMonoidHom.toContinuousMap_toContinuousMonoidHom** 是 Mathlib 中的一个引理，位
于命名空间 `ContinuousMonoidHom`。
形式化陈述：toContinuousMap_toContinuousMonoidHom [MonoidHomClass F A B] [ContinuousMa
pClass F A B] (f : F) : ((f : A ->ₜ* B) : C(A, B)) = f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousMap_toContinuousMonoidHom [MonoidHomClass F A B] [ContinuousMapClass F A B]
    (f : F) : ((f : A →ₜ* B) : C(A, B)) = f := rfl

end

@[to_additive (attr := ext)]
/-
**ContinuousMonoidHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：ext {f g : A ->ₜ* B} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : A →ₜ* B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[to_additive]
/-
**ContinuousMonoidHom.toContinuousMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousMonoidHom`。
形式化陈述：toContinuousMap_injective : Injective (toContinuousMap : _ -> C(A, B))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMonoidHom.ext`：ext {f g : A ->ₜ* B} (h : forall x, f x = g x) 
: f = g
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem toContinuousMap_injective : Injective (toContinuousMap : _ → C(A, B)) := fun f g h =>
  ext <| by convert! DFunLike.ext_iff.1 h

@[to_additive]
/-
**ContinuousMonoidHom.toMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sMonoidHom`。
形式化陈述：toMonoidHom_injective : Injective (toMonoidHom : _ -> A ->* B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMonoidHom.ext`：ext {f g : A ->ₜ* B} (h : forall x, f x = g x) 
: f = g
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem toMonoidHom_injective : Injective (toMonoidHom : _ → A →* B) := fun f g h =>
  ext <| by convert! DFunLike.ext_iff.1 h

/-- Composition of two continuous homomorphisms. -/
@[to_additive (attr := simps!) /-- Composition of two continuous homomorphisms. -/]
/-
**ContinuousMonoidHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：comp (g : B ->ₜ* C) (f : A ->ₜ* B) : A ->ₜ* C
参数：g : B ->ₜ* C；f : A ->ₜ* B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of two continuous homomorphisms.
-/
def comp (g : B →ₜ* C) (f : A →ₜ* B) : A →ₜ* C :=
  ⟨g.toMonoidHom.comp f.toMonoidHom, (map_continuous g).comp (map_continuous f)⟩

@[to_additive (attr := simp)]
/-
**ContinuousMonoidHom.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：coe_comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) : ⇑(g
.comp f) = ⇑g ∘ ⇑f
参数：g : ContinuousMonoidHom B C；f : ContinuousMonoidHom A B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) :
    ⇑(g.comp f) = ⇑g ∘ ⇑f := rfl

/-- Product of two continuous homomorphisms on the same space. -/
@[to_additive (attr := simps!) prod
/-- Product of two continuous homomorphisms on the same space. -/]
/-
**ContinuousMonoidHom.prod** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：prod (f : A ->ₜ* B) (g : A ->ₜ* C) : A ->ₜ* (B × C)
参数：f : A ->ₜ* B；g : A ->ₜ* C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prod (f : A →ₜ* B) (g : A →ₜ* C) : A →ₜ* (B × C) :=
  ⟨f.toMonoidHom.prod g.toMonoidHom, f.continuous_toFun.prodMk g.continuous_toFun⟩

/-- Product of two continuous homomorphisms on different spaces. -/
@[to_additive (attr := simps!) prodMap
  /-- Product of two continuous homomorphisms on different spaces. -/]
/-
**ContinuousMonoidHom.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：prodMap (f : A ->ₜ* C) (g : B ->ₜ* D) : (A × B) ->ₜ* (C × D)
参数：f : A ->ₜ* C；g : B ->ₜ* D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prodMap (f : A →ₜ* C) (g : B →ₜ* D) :
    (A × B) →ₜ* (C × D) :=
  ⟨f.toMonoidHom.prodMap g.toMonoidHom, f.continuous_toFun.prodMap g.continuous_toFun⟩

variable (A B C D E)

/-- The trivial continuous homomorphism. -/
@[to_additive (attr := simps!) /-- The trivial continuous homomorphism. -/]
/-
**ContinuousMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial continuous homomorphism.
-/
instance : One (A →ₜ* B) where
  one := ⟨1, continuous_const⟩

@[to_additive (attr := simp)]
/-
**ContinuousMonoidHom.coe_one** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：coe_one : ⇑(1 : A ->ₜ* B) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_one : ⇑(1 : A →ₜ* B) = 1 :=
  rfl

@[to_additive]
/-
**ContinuousMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (A →ₜ* B) := ⟨1⟩

/-- The identity continuous homomorphism. -/
@[to_additive (attr := simps!) /-- The identity continuous homomorphism. -/]
/-
**ContinuousMonoidHom.id** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：id : A ->ₜ* A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
The identity continuous homomorphism.
-/
def id : A →ₜ* A := ⟨.id A, continuous_id⟩

@[to_additive (attr := simp)]
/-
**ContinuousMonoidHom.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：coe_id : ⇑(ContinuousMonoidHom.id A) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_id : ⇑(ContinuousMonoidHom.id A) = _root_.id :=
  rfl

/-- The continuous homomorphism given by projection onto the first factor. -/
@[to_additive (attr := simps!)
  /-- The continuous homomorphism given by projection onto the first factor. -/]
/-
**ContinuousMonoidHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：fst : (A × B) ->ₜ* A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
-/
def fst : (A × B) →ₜ* A := ⟨MonoidHom.fst A B, continuous_fst⟩

/-- The continuous homomorphism given by projection onto the second factor. -/
@[to_additive (attr := simps!)
  /-- The continuous homomorphism given by projection onto the second factor. -/]
/-
**ContinuousMonoidHom.snd** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：snd : (A × B) ->ₜ* B
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
def snd : (A × B) →ₜ* B :=
  ⟨MonoidHom.snd A B, continuous_snd⟩

/-- The continuous homomorphism given by inclusion of the first factor. -/
@[to_additive (attr := simps!)
  /-- The continuous homomorphism given by inclusion of the first factor. -/]
/-
**ContinuousMonoidHom.inl** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：inl : A ->ₜ* (A × B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def inl : A →ₜ* (A × B) :=
  prod (id A) 1

/-- The continuous homomorphism given by inclusion of the second factor. -/
@[to_additive (attr := simps!)
  /-- The continuous homomorphism given by inclusion of the second factor. -/]
/-
**ContinuousMonoidHom.inr** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：inr : B ->ₜ* (A × B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def inr : B →ₜ* (A × B) :=
  prod 1 (id B)


/-- The continuous homomorphism given by the diagonal embedding. -/
@[to_additive (attr := simps!) /-- The continuous homomorphism given by the diagonal embedding. -/]
/-
**ContinuousMonoidHom.diag** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：diag : A ->ₜ* (A × A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous homomorphism given by the diagonal embedding.
-/
def diag : A →ₜ* (A × A) := prod (id A) (id A)

/-- The continuous homomorphism given by swapping components. -/
@[to_additive (attr := simps!) /-- The continuous homomorphism given by swapping components. -/]
/-
**ContinuousMonoidHom.swap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：swap : (A × B) ->ₜ* (B × A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous homomorphism given by swapping components.
-/
def swap : (A × B) →ₜ* (B × A) := prod (snd A B) (fst A B)

section CommMonoid
variable [CommMonoid E] [TopologicalSpace E] [ContinuousMul E]

/-- The continuous homomorphism given by multiplication. -/
@[to_additive (attr := simps!) /-- The continuous homomorphism given by addition. -/]
/-
**ContinuousMonoidHom.mul** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：mul : (E × E) ->ₜ* E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous homomorphism given by multiplication.
-/
def mul : (E × E) →ₜ* E := ⟨mulMonoidHom, continuous_mul⟩

variable {A B C D E}

@[to_additive]
/-
**ContinuousMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommMonoid (A →ₜ* E) where
  mul f g := (mul E).comp (f.prod g)
  mul_comm f g := ext fun x => mul_comm (f x) (g x)
  mul_assoc f g h := ext fun x => mul_assoc (f x) (g x) (h x)
  one_mul f := ext fun x => one_mul (f x)
  mul_one f := ext fun x => mul_one (f x)

@[to_additive (attr := simp)]
/-
**ContinuousMonoidHom.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：mul_apply (f g : A ->ₜ* E) (a : A) : (f * g) a = f a * g a
参数：f g : A ->ₜ* E；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (f g : A →ₜ* E) (a : A) : (f * g) a = f a * g a := by
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMonoidHom.pow_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：pow_apply (f : A ->ₜ* E) (n : Nat) (a : A) : (f ^ n) a = (f a) ^ n
参数：f : A ->ₜ* E；n : Nat；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `ContinuousMonoidHom.one_toFun`：∀ (A : Type u_2) (B : Type u_3) [inst : M
onoid A] [inst_1 : Monoid B] [inst_2 : TopologicalSpace A]   [inst_3 : Topologic
alSpace B] (x : A),…
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `ContinuousMonoidHom.mul_apply`：mul_apply (f g : A ->ₜ* E) (a : A) : (f *
 g) a = f a * g a
-/
theorem pow_apply (f : A →ₜ* E) (n : ℕ) (a : A) : (f ^ n) a = (f a) ^ n := by
  induction n
  case zero => rw [pow_zero, pow_zero, one_toFun]
  case succ n ih => rw [pow_succ, pow_succ, ContinuousMonoidHom.mul_apply, ih]

/-- Coproduct of two continuous homomorphisms to the same space. -/
@[to_additive (attr := simps!) /-- Coproduct of two continuous homomorphisms to the same space. -/]
/-
**ContinuousMonoidHom.coprod** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：coprod (f : ContinuousMonoidHom A E) (g : ContinuousMonoidHom B E) : Conti
nuousMonoidHom (A × B) E
参数：f : ContinuousMonoidHom A E；g : ContinuousMonoidHom B E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coproduct of two continuous homomorphisms to the same space.
-/
def coprod (f : ContinuousMonoidHom A E) (g : ContinuousMonoidHom B E) :
    ContinuousMonoidHom (A × B) E :=
  (mul E).comp (f.prodMap g)

end CommMonoid

section CommGroup

variable [CommGroup E] [TopologicalSpace E] [IsTopologicalGroup E]
/-- The continuous homomorphism given by inversion. -/
@[to_additive (attr := simps!) /-- The continuous homomorphism given by negation. -/]
/-
**ContinuousMonoidHom.inv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：inv : ContinuousMonoidHom E E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous homomorphism given by inversion.
-/
def inv : ContinuousMonoidHom E E :=
  ⟨invMonoidHom, continuous_inv⟩

@[to_additive]
/-
**ContinuousMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommGroup (ContinuousMonoidHom A E) where
  __ : CommMonoid (ContinuousMonoidHom A E) := inferInstance
  inv f := (inv E).comp f
  inv_mul_cancel f := ext fun x => inv_mul_cancel (f x)
  div f g := .comp ⟨divMonoidHom, continuous_div'⟩ (f.prod g)
  div_eq_mul_inv f g := ext fun x => div_eq_mul_inv (f x) (g x)

end CommGroup

/-- For `f : F` where `F` is a class of continuous monoid hom, this yields an element
`ContinuousMonoidHom A B`. -/
@[to_additive /-- For `f : F` where `F` is a class of continuous additive monoid hom, this yields
an element `ContinuousAddMonoidHom A B`. -/]
/-
**ContinuousMonoidHom.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMonoidHom`。
形式化陈述：ofClass (F : Type*) [FunLike F A B] [ContinuousMapClass F A B] [MonoidHomC
lass F A B] (f : F) : (ContinuousMonoidHom A B)
参数：F : Type*；f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofClass (F : Type*) [FunLike F A B] [ContinuousMapClass F A B]
    [MonoidHomClass F A B] (f : F) : (ContinuousMonoidHom A B) := toContinuousMonoidHom f

end ContinuousMonoidHom

end

section

/-!

### Continuous MulEquiv

This section defines the space of continuous isomorphisms between two topological groups.
-/

universe u v

variable (G : Type u) [TopologicalSpace G] (H : Type v) [TopologicalSpace H]

/-- The structure of two-sided continuous isomorphisms between additive groups.
Note that both the map and its inverse have to be continuous. -/
/-
**ContinuousAddEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u) → [TopologicalSpace G] → (H : Type v) → [TopologicalSpace H] 
→ [Add G] → [Add H] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure of two-sided continuous isomorphisms between additive groups.
Note that both the map and its inverse have to be continuous.
-/
structure ContinuousAddEquiv [Add G] [Add H] extends G ≃+ H, G ≃ₜ H

/-- The structure of two-sided continuous isomorphisms between groups.
Note that both the map and its inverse have to be continuous. -/
@[to_additive]
/-
**ContinuousMulEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u) → [TopologicalSpace G] → (H : Type v) → [TopologicalSpace H] 
→ [Mul G] → [Mul H] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure of two-sided continuous isomorphisms between groups.
Note that both the map and its inverse have to be continuous.
-/
structure ContinuousMulEquiv [Mul G] [Mul H] extends G ≃* H, G ≃ₜ H

/-- The homeomorphism induced from a two-sided continuous isomorphism of groups. -/
add_decl_doc ContinuousMulEquiv.toHomeomorph

/-- The homeomorphism induced from a two-sided continuous isomorphism additive groups. -/
add_decl_doc ContinuousAddEquiv.toHomeomorph

@[inherit_doc]
infixl:25 " ≃ₜ* " => ContinuousMulEquiv

@[inherit_doc]
infixl:25 " ≃ₜ+ " => ContinuousAddEquiv

section

namespace ContinuousMulEquiv

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [Mul M] [Mul N]

section coe

@[to_additive]
/-
**ContinuousMulEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (M ≃ₜ* N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    exact MulEquiv.ext_iff.mpr (congrFun h₁)

@[to_additive]
/-
**ContinuousMulEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulEquivClass (M ≃ₜ* N) M N where
  map_mul f := f.map_mul'

@[to_additive]
/-
**ContinuousMulEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HomeomorphClass (M ≃ₜ* N) M N where
  map_continuous f := f.continuous_toFun
  inv_continuous f := f.continuous_invFun

/-- Two continuous multiplicative isomorphisms agree if they are defined by the
same underlying function. -/
@[to_additive (attr := ext) /-- Two continuous additive isomorphisms agree if they are defined by
the same underlying function. -/]
/-
**ContinuousMulEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEquiv`。
形式化陈述：ext {f g : M ≃ₜ* N} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : M ≃ₜ* N} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[to_additive (attr := simp)]
/-
**ContinuousMulEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEquiv`。
形式化陈述：coe_mk (f : M ≃* N) (hf1 hf2) : ⇑(mk f hf1 hf2) = f
参数：f : M ≃* N；hf1 hf2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : M ≃* N) (hf1 hf2) : ⇑(mk f hf1 hf2) = f := rfl

@[to_additive]
/-
**ContinuousMulEquiv.toEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEqui
v`。
形式化陈述：toEquiv_eq_coe (f : M ≃ₜ* N) : f.toEquiv = f
参数：f : M ≃ₜ* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_eq_coe (f : M ≃ₜ* N) : f.toEquiv = f :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMulEquiv.toMulEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulE
quiv`。
形式化陈述：toMulEquiv_eq_coe (f : M ≃ₜ* N) : f.toMulEquiv = f
参数：f : M ≃ₜ* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMulEquiv_eq_coe (f : M ≃ₜ* N) : f.toMulEquiv = f :=
  rfl

@[to_additive]
/-
**ContinuousMulEquiv.toHomeomorph_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMu
lEquiv`。
形式化陈述：toHomeomorph_eq_coe (f : M ≃ₜ* N) : f.toHomeomorph = f
参数：f : M ≃ₜ* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHomeomorph_eq_coe (f : M ≃ₜ* N) : f.toHomeomorph = f :=
  rfl

/-- Makes a continuous multiplicative isomorphism from
a homeomorphism which preserves multiplication. -/
@[to_additive /-- Makes a continuous additive isomorphism from
a homeomorphism which preserves addition. -/]
/-
**ContinuousMulEquiv.mk'** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMulEquiv`。
形式化陈述：mk' (f : M ≃ₜ N) (h : forall x y, f (x * y) = f x * f y) : M ≃ₜ* N
参数：f : M ≃ₜ N；h : forall x y, f (x * y) = f x * f y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.continuous_toFun`：∀ {X : Type u_5} {Y : Type u_6} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (self : X ≃ₜ Y),   Continuous sel
f.toFun
· 使用定理 `Homeomorph.continuous_invFun`：∀ {X : Type u_5} {Y : Type u_6} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] (self : X ≃ₜ Y),   Continuous se
lf.invFun
-/
def mk' (f : M ≃ₜ N) (h : ∀ x y, f (x * y) = f x * f y) : M ≃ₜ* N :=
  ⟨⟨f.toEquiv,h⟩, f.continuous_toFun, f.continuous_invFun⟩

set_option linter.docPrime false in -- This is about `ContinuousMulEquiv.mk'`
@[simp]
/-
**ContinuousMulEquiv.coe_mk'** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMulEquiv`。
形式化陈述：coe_mk' (f : M ≃ₜ N) (h : forall x y, f (x * y) = f x * f y) : ⇑(mk' f h) 
= f
参数：f : M ≃ₜ N；h : forall x y, f (x * y) = f x * f y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk' (f : M ≃ₜ N) (h : ∀ x y, f (x * y) = f x * f y) : ⇑(mk' f h) = f := rfl

end coe

section bijective

@[to_additive]
/-
**ContinuousMulEquiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEquiv`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : TopologicalSpace M] [inst_1 : Topo
logicalSpace N] [inst_2 : Mul M]   [inst_3 : Mul N] (e : M ≃ₜ* N), Function.Bije
ctive ⇑e
参数：e : M ≃ₜ* N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.bijective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Bijective ⇑e
-/
protected theorem bijective (e : M ≃ₜ* N) : Function.Bijective e :=
  EquivLike.bijective e

@[to_additive]
/-
**ContinuousMulEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEquiv`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : TopologicalSpace M] [inst_1 : Topo
logicalSpace N] [inst_2 : Mul M]   [inst_3 : Mul N] (e : M ≃ₜ* N), Function.Inje
ctive ⇑e
参数：e : M ≃ₜ* N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
-/
protected theorem injective (e : M ≃ₜ* N) : Function.Injective e :=
  EquivLike.injective e

@[to_additive]
/-
**ContinuousMulEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEquiv`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : TopologicalSpace M] [inst_1 : Topo
logicalSpace N] [inst_2 : Mul M]   [inst_3 : Mul N] (e : M ≃ₜ* N), Function.Surj
ective ⇑e
参数：e : M ≃ₜ* N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
-/
protected theorem surjective (e : M ≃ₜ* N) : Function.Surjective e :=
  EquivLike.surjective e

@[to_additive]
/-
**ContinuousMulEquiv.apply_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEqu
iv`。
形式化陈述：apply_eq_iff_eq (e : M ≃ₜ* N) {x y : M} : e x = e y ↔ x = y
参数：e : M ≃ₜ* N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `ContinuousMulEquiv.injective`：∀ {M : Type u_1} {N : Type u_2} [inst : To
pologicalSpace M] [inst_1 : TopologicalSpace N] [inst_2 : Mul M]   [inst_3 : Mul
 N] (e : M ≃ₜ* N),…
-/
theorem apply_eq_iff_eq (e : M ≃ₜ* N) {x y : M} : e x = e y ↔ x = y :=
  e.injective.eq_iff

end bijective

section refl

variable (M)

/-- The identity map is a continuous multiplicative isomorphism. -/
@[to_additive (attr := refl) /-- The identity map is a continuous additive isomorphism. -/]
/-
**ContinuousMulEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMulEquiv`。
形式化陈述：refl : M ≃ₜ* M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map is a continuous multiplicative isomorphism.
-/
def refl : M ≃ₜ* M :=
  { MulEquiv.refl _ with
    continuous_toFun := by dsimp; fun_prop
    continuous_invFun := by dsimp; fun_prop }

@[to_additive]
/-
**ContinuousMulEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (M ≃ₜ* M) := ⟨ContinuousMulEquiv.refl M⟩

@[to_additive (attr := simp, norm_cast)]
/-
**ContinuousMulEquiv.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEquiv`。
形式化陈述：coe_refl : ↑(refl M) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl : ↑(refl M) = id := rfl

@[to_additive (attr := simp)]
/-
**ContinuousMulEquiv.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEquiv`。
形式化陈述：refl_apply (m : M) : refl M m = m
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_apply (m : M) : refl M m = m := rfl

end refl

section symm

/-- The inverse of a ContinuousMulEquiv. -/
@[to_additive (attr := symm) /-- The inverse of a ContinuousAddEquiv. -/]
/-
**ContinuousMulEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMulEquiv`。
形式化陈述：symm (cme : M ≃ₜ* N) : N ≃ₜ* M
参数：cme : M ≃ₜ* N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMulEquiv.continuous_invFun`：∀ {G : Type u} [inst : Topological
Space G] {H : Type v} [inst_1 : TopologicalSpace H] [inst_2 : Mul G] [inst_3 : M
ul H]   (self : G ≃ₜ* H), …
· 使用定理 `ContinuousMulEquiv.continuous_toFun`：∀ {G : Type u} [inst : TopologicalS
pace G] {H : Type v} [inst_1 : TopologicalSpace H] [inst_2 : Mul G] [inst_3 : Mu
l H]   (self : G ≃ₜ* H), …

--- 原说明 ---
The inverse of a ContinuousMulEquiv.
-/
def symm (cme : M ≃ₜ* N) : N ≃ₜ* M :=
  { cme.toMulEquiv.symm with
  continuous_toFun := cme.continuous_invFun
  continuous_invFun := cme.continuous_toFun }

/-- See Note [custom simps projection] -/
@[to_additive /-- See Note [custom simps projection] -/]
/-
**ContinuousMulEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMulEq
uiv.Simps`。
形式化陈述：(G : Type u) →   [inst : TopologicalSpace G] →     (H : Type v) → [inst_1 
: TopologicalSpace H] → [inst_2 : Mul G] → [inst_3 : Mul H] → G ≃ₜ* H → H → G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply [Mul G] [Mul H] (e : G ≃ₜ* H) : H → G :=
  e.symm

initialize_simps_projections ContinuousMulEquiv (toFun → apply, invFun → symm_apply)

initialize_simps_projections ContinuousAddEquiv (toFun → apply, invFun → symm_apply)

@[to_additive]
/-
**ContinuousMulEquiv.invFun_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEqui
v`。
形式化陈述：invFun_eq_symm {f : M ≃ₜ* N} : f.invFun = f.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invFun_eq_symm {f : M ≃ₜ* N} : f.invFun = f.symm := rfl

@[to_additive (attr := simp)]
/-
**ContinuousMulEquiv.coe_toHomeomorph_symm** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
MulEquiv`。
形式化陈述：coe_toHomeomorph_symm (f : M ≃ₜ* N) : (f : M ≃ₜ N).symm = (f.symm : N ≃ₜ M
)
参数：f : M ≃ₜ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMulEquiv.instHomeomorphClass`：∀ {M : Type u_1} {N : Type u_2} 
[inst : TopologicalSpace M] [inst_1 : TopologicalSpace N] [inst_2 : Mul M]   [in
st_3 : Mul N], HomeomorphCla…
-/
theorem coe_toHomeomorph_symm (f : M ≃ₜ* N) : (f : M ≃ₜ N).symm = (f.symm : N ≃ₜ M) := rfl

@[to_additive (attr := simp)]
/-
**ContinuousMulEquiv.equivLike_inv_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
MulEquiv`。
形式化陈述：equivLike_inv_eq_symm (f : M ≃ₜ* N) : EquivLike.inv f = f.symm
参数：f : M ≃ₜ* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivLike_inv_eq_symm (f : M ≃ₜ* N) : EquivLike.inv f = f.symm := rfl

@[to_additive (attr := simp)]
/-
**ContinuousMulEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEquiv`。
形式化陈述：symm_symm (f : M ≃ₜ* N) : f.symm.symm = f
参数：f : M ≃ₜ* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (f : M ≃ₜ* N) : f.symm.symm = f := rfl

@[to_additive]
/-
**ContinuousMulEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEqui
v`。
形式化陈述：symm_bijective : Function.Bijective (symm : M ≃ₜ* N -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `ContinuousMulEquiv.symm_symm`：symm_symm (f : M ≃ₜ* N) : f.symm.symm = f
-/
theorem symm_bijective : Function.Bijective (symm : M ≃ₜ* N → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/
@[to_additive (attr := simp)
/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/]
/-
**ContinuousMulEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEq
uiv`。
形式化陈述：apply_symm_apply (e : M ≃ₜ* N) (y : N) : e (e.symm y) = y
参数：e : M ≃ₜ* N；y : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem apply_symm_apply (e : M ≃ₜ* N) (y : N) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y

/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/
@[to_additive (attr := simp)
/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/]
/-
**ContinuousMulEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEq
uiv`。
形式化陈述：symm_apply_apply (e : M ≃ₜ* N) (x : M) : e.symm (e x) = x
参数：e : M ≃ₜ* N；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem symm_apply_apply (e : M ≃ₜ* N) (x : M) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]
/-
**ContinuousMulEquiv.symm_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEqui
v`。
形式化陈述：symm_comp_self (e : M ≃ₜ* N) : e.symm ∘ e = id
参数：e : M ≃ₜ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃ₜ* N) (x :
 M) : e.symm (e x) = x
-/
theorem symm_comp_self (e : M ≃ₜ* N) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[to_additive (attr := simp)]
/-
**ContinuousMulEquiv.self_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEqui
v`。
形式化陈述：self_comp_symm (e : M ≃ₜ* N) : e ∘ e.symm = id
参数：e : M ≃ₜ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃ₜ* N) (y :
 N) : e (e.symm y) = y
-/
theorem self_comp_symm (e : M ≃ₜ* N) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

@[to_additive]
/-
**ContinuousMulEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEquiv
`。
形式化陈述：symm_apply_eq (e : M ≃ₜ* N) {x y} : e.symm x = y ↔ x = e y
参数：e : M ≃ₜ* N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq (e : M ≃ₜ* N) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

@[to_additive]
/-
**ContinuousMulEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEquiv
`。
形式化陈述：eq_symm_apply (e : M ≃ₜ* N) {x y} : y = e.symm x ↔ e y = x
参数：e : M ≃ₜ* N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply (e : M ≃ₜ* N) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[to_additive (attr := deprecated eq_symm_apply (since := "2026-07-26"))]
/-
**ContinuousMulEquiv.apply_eq_iff_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMulEquiv`。
形式化陈述：apply_eq_iff_symm_apply (e : M ≃ₜ* N) {x : M} {y : N} : e x = y ↔ x = e.sy
mm y
参数：e : M ≃ₜ* N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ContinuousMulEquiv.eq_symm_apply`：eq_symm_apply (e : M ≃ₜ* N) {x y} : y 
= e.symm x ↔ e y = x
-/
theorem apply_eq_iff_symm_apply (e : M ≃ₜ* N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
  e.eq_symm_apply.symm

@[to_additive]
/-
**ContinuousMulEquiv.eq_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEquiv`
。
形式化陈述：eq_comp_symm {α : Type*} (e : M ≃ₜ* N) (f : N -> α) (g : M -> α) : f = g ∘
 e.symm ↔ f ∘ e = g
参数：e : M ≃ₜ* N；f : N -> α；g : M -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_comp_symm`：eq_comp_symm {α β γ} (e : α ≃ β) (f : β -> γ) (g : α
 -> γ) : f = g ∘ e.symm ↔ f ∘ e = g
-/
theorem eq_comp_symm {α : Type*} (e : M ≃ₜ* N) (f : N → α) (g : M → α) :
    f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

@[to_additive]
/-
**ContinuousMulEquiv.comp_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEquiv`
。
形式化陈述：comp_symm_eq {α : Type*} (e : M ≃ₜ* N) (f : N -> α) (g : M -> α) : g ∘ e.s
ymm = f ↔ g = f ∘ e
参数：e : M ≃ₜ* N；f : N -> α；g : M -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.comp_symm_eq`：comp_symm_eq {α β γ} (e : α ≃ β) (f : β -> γ) (g : α
 -> γ) : g ∘ e.symm = f ↔ g = f ∘ e
-/
theorem comp_symm_eq {α : Type*} (e : M ≃ₜ* N) (f : N → α) (g : M → α) :
    g ∘ e.symm = f ↔ g = f ∘ e :=
  e.toEquiv.comp_symm_eq f g

@[to_additive]
/-
**ContinuousMulEquiv.eq_symm_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEquiv`
。
形式化陈述：eq_symm_comp {α : Type*} (e : M ≃ₜ* N) (f : α -> M) (g : α -> N) : f = e.s
ymm ∘ g ↔ e ∘ f = g
参数：e : M ≃ₜ* N；f : α -> M；g : α -> N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_comp`：eq_symm_comp {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ
 -> β) : f = e.symm ∘ g ↔ e ∘ f = g
-/
theorem eq_symm_comp {α : Type*} (e : M ≃ₜ* N) (f : α → M) (g : α → N) :
    f = e.symm ∘ g ↔ e ∘ f = g :=
  e.toEquiv.eq_symm_comp f g

@[to_additive]
/-
**ContinuousMulEquiv.symm_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEquiv`
。
形式化陈述：symm_comp_eq {α : Type*} (e : M ≃ₜ* N) (f : α -> M) (g : α -> N) : e.symm 
∘ g = f ↔ g = e ∘ f
参数：e : M ≃ₜ* N；f : α -> M；g : α -> N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_comp_eq`：symm_comp_eq {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ
 -> β) : e.symm ∘ g = f ↔ g = e ∘ f
-/
theorem symm_comp_eq {α : Type*} (e : M ≃ₜ* N) (f : α → M) (g : α → N) :
    e.symm ∘ g = f ↔ g = e ∘ f :=
  e.toEquiv.symm_comp_eq f g

end symm

section trans

variable {L : Type*} [Mul L] [TopologicalSpace L]

/-- The composition of two ContinuousMulEquiv. -/
@[to_additive /-- The composition of two ContinuousAddEquiv. -/]
/-
**ContinuousMulEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMulEquiv`。
形式化陈述：trans (cme1 : M ≃ₜ* N) (cme2 : N ≃ₜ* L) : M ≃ₜ* L where __
参数：cme1 : M ≃ₜ* N；cme2 : N ≃ₜ* L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two ContinuousMulEquiv.
-/
def trans (cme1 : M ≃ₜ* N) (cme2 : N ≃ₜ* L) : M ≃ₜ* L where
  __ := cme1.toMulEquiv.trans cme2.toMulEquiv
  continuous_toFun := by convert! Continuous.comp cme2.continuous_toFun cme1.continuous_toFun
  continuous_invFun := by convert! Continuous.comp cme1.continuous_invFun cme2.continuous_invFun

@[to_additive (attr := simp)]
/-
**ContinuousMulEquiv.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEquiv`。
形式化陈述：coe_trans (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) : ↑(e₁.trans e₂) = e₂ ∘ e₁
参数：e₁ : M ≃ₜ* N；e₂ : N ≃ₜ* L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) : ↑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

@[to_additive (attr := simp)]
/-
**ContinuousMulEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEquiv`。
形式化陈述：trans_apply (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) (m : M) : e₁.trans e₂ m = e₂ (e₁
 m)
参数：e₁ : M ≃ₜ* N；e₂ : N ≃ₜ* L；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) (m : M) : e₁.trans e₂ m = e₂ (e₁ m) := rfl

@[to_additive (attr := simp)]
/-
**ContinuousMulEquiv.symm_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEq
uiv`。
形式化陈述：symm_trans_apply (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) (l : L) : (e₁.trans e₂).sym
m l = e₁.symm (e₂.symm l)
参数：e₁ : M ≃ₜ* N；e₂ : N ≃ₜ* L；l : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans_apply (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) (l : L) :
    (e₁.trans e₂).symm l = e₁.symm (e₂.symm l) := rfl

@[to_additive (attr := simp)]
/-
**ContinuousMulEquiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEqu
iv`。
形式化陈述：symm_trans_self (e : M ≃ₜ* N) : e.symm.trans e = refl N
参数：e : M ≃ₜ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `ContinuousMulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃ₜ* N) (y :
 N) : e (e.symm y) = y
-/
theorem symm_trans_self (e : M ≃ₜ* N) : e.symm.trans e = refl N :=
  DFunLike.ext _ _ e.apply_symm_apply

@[to_additive (attr := simp)]
/-
**ContinuousMulEquiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulEqu
iv`。
形式化陈述：self_trans_symm (e : M ≃ₜ* N) : e.trans e.symm = refl M
参数：e : M ≃ₜ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `ContinuousMulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃ₜ* N) (x :
 M) : e.symm (e x) = x
-/
theorem self_trans_symm (e : M ≃ₜ* N) : e.trans e.symm = refl M :=
  DFunLike.ext _ _ e.symm_apply_apply

end trans

section unique

/-- The `MulEquiv` between two monoids with a unique element. -/
@[to_additive /-- The `AddEquiv` between two `AddMonoid`s with a unique element. -/]
/-
**ContinuousMulEquiv.ofUnique** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMulEquiv`。
形式化陈述：ofUnique {M N} [Unique M] [Unique N] [Mul M] [Mul N] [TopologicalSpace M] 
[TopologicalSpace N] : M ≃ₜ* N where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `MulEquiv` between two monoids with a unique element.
-/
def ofUnique {M N} [Unique M] [Unique N] [Mul M] [Mul N]
    [TopologicalSpace M] [TopologicalSpace N] : M ≃ₜ* N where
  __ := MulEquiv.ofUnique

/-- There is a unique monoid homomorphism between two monoids with a unique element. -/
@[to_additive /-- There is a unique additive monoid homomorphism between two additive monoids with
  a unique element. -/]
/-
**ContinuousMulEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N} [Unique M] [Unique N] [Mul M] [Mul N]
    [TopologicalSpace M] [TopologicalSpace N] : Unique (M ≃ₜ* N) where
  default := ofUnique
  uniq _ := ext fun _ ↦ Subsingleton.elim _ _

end unique

end ContinuousMulEquiv

namespace MulEquiv

variable {G H} [Mul G] [Mul H] (e : G ≃* H) (he : ∀ s, IsOpen (e ⁻¹' s) ↔ IsOpen s)
include he

/-- A `MulEquiv` that respects open sets is a `ContinuousMulEquiv`. -/
@[to_additive (attr := simps apply symm_apply)
/-- An `AddEquiv` that respects open sets is a `ContinuousAddEquiv`. -/]
/-
**MulEquiv.toContinuousMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：toContinuousMulEquiv : G ≃ₜ* H where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.map_mul'`：∀ {M : Type u_9} {N : Type u_10} [inst : Mul M] [inst
_1 : Mul N] (self : M ≃* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toFun…
· 使用定理 `Homeomorph.continuous_toFun`：∀ {X : Type u_5} {Y : Type u_6} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (self : X ≃ₜ Y),   Continuous sel
f.toFun
· 使用定理 `Homeomorph.continuous_invFun`：∀ {X : Type u_5} {Y : Type u_6} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] (self : X ≃ₜ Y),   Continuous se
lf.invFun
-/
def toContinuousMulEquiv : G ≃ₜ* H where
  toFun := e
  invFun := e.symm
  __ := e
  __ := e.toEquiv.toHomeomorph he

variable {e}

@[to_additive, simp]
/-
**MulEquiv.toMulEquiv_toContinuousMulEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：toMulEquiv_toContinuousMulEquiv : (e.toContinuousMulEquiv he : G ≃* H) = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMulEquiv.instMulEquivClass`：∀ {M : Type u_1} {N : Type u_2} [i
nst : TopologicalSpace M] [inst_1 : TopologicalSpace N] [inst_2 : Mul M]   [inst
_3 : Mul N], MulEquivClass…
-/
lemma toMulEquiv_toContinuousMulEquiv : (e.toContinuousMulEquiv he : G ≃* H) = e :=
  rfl
/-
**MulEquiv.toHomeomorph_toContinuousMulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv
`。
形式化陈述：∀ {G : Type u} [inst : TopologicalSpace G] {H : Type v} [inst_1 : Topologi
calSpace H] [inst_2 : Mul G] [inst_3 : Mul H]   {e : G ≃* H} (he : ∀ (s : Set H)
, IsOpen (⇑e ⁻¹' s) ↔ IsOpen s), ↑(e.toContinuousMulEquiv he) = e.toHomeomorph h
e
参数：he : ∀ (s : Set H), IsOpen (⇑e ⁻¹' s) ↔ IsOpen s；e.toContinuousMulEquiv he。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMulEquiv.instHomeomorphClass`：∀ {M : Type u_1} {N : Type u_2} 
[inst : TopologicalSpace M] [inst_1 : TopologicalSpace N] [inst_2 : Mul M]   [in
st_3 : Mul N], HomeomorphCla…
-/
@[to_additive, simp] lemma toHomeomorph_toContinuousMulEquiv :
    (e.toContinuousMulEquiv he : G ≃ₜ H) = e.toHomeomorph he :=
  rfl

@[to_additive]
/-
**MulEquiv.symm_toContinuousMulEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：symm_toContinuousMulEquiv : (e.toContinuousMulEquiv he).symm = e.symm.toCo
ntinuousMulEquiv (fun s => by convert! (he _).symm; exact (e.preimage_symm_preim
age s).symm)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_toContinuousMulEquiv :
    (e.toContinuousMulEquiv he).symm = e.symm.toContinuousMulEquiv
      (fun s ↦ by convert! (he _).symm; exact (e.preimage_symm_preimage s).symm) :=
  rfl

end MulEquiv

end

end

