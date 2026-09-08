/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Group.ULift
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Category instances for `Monoid`, `AddMonoid`, `CommMonoid`, and `AddCommMonoid`.

We introduce the bundled categories:
* `MonCat`
* `AddMonCat`
* `CommMonCat`
* `AddCommMonCat`

along with the relevant forgetful functors between them.
-/

@[expose] public section

assert_not_exists MonoidWithZero

universe u v

open CategoryTheory

/-- The category of additive monoids and monoid morphisms. -/
/-
**AddMonCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of additive monoids and monoid morphisms.
-/
structure AddMonCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddMonoid carrier]

/-- The category of monoids and monoid morphisms. -/
@[to_additive AddMonCat]
/-
**MonCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of monoids and monoid morphisms.
-/
structure MonCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : Monoid carrier]

attribute [instance] AddMonCat.str MonCat.str

initialize_simps_projections AddMonCat (carrier → coe, -str)
initialize_simps_projections MonCat (carrier → coe, -str)

namespace MonCat

@[to_additive]
/-
**MonCat.** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort MonCat (Type u) :=
  ⟨MonCat.carrier⟩

attribute [coe] AddMonCat.carrier MonCat.carrier

/-- Construct a bundled `MonCat` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddMonCat` from the underlying type and typeclass. -/]
/-
**MonCat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `MonCat`。
形式化陈述：of (M : Type u) [Monoid M] : MonCat
参数：M : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `MonCat` from the underlying type and typeclass.
-/
abbrev of (M : Type u) [Monoid M] : MonCat := ⟨M⟩

end MonCat

/-- The type of morphisms in `AddMonCat`. -/
@[ext]
/-
**AddMonCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddMonCat`。
形式化陈述：AddMonCat → AddMonCat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `AddMonCat`.
-/
structure AddMonCat.Hom (A B : AddMonCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →+ B

/-- The type of morphisms in `MonCat`. -/
@[to_additive, ext]
/-
**MonCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `MonCat`。
形式化陈述：MonCat → MonCat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `MonCat`.
-/
structure MonCat.Hom (A B : MonCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →* B

namespace MonCat

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/-
**MonCat.** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category MonCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/-
**MonCat.** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory MonCat (· →* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `MonCat` back into a `MonoidHom`. -/
@[to_additive /-- Turn a morphism in `AddMonCat` back into an `AddMonoidHom`. -/]
/-
**MonCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `MonCat.Hom`。
形式化陈述：{X Y : MonCat} → X.Hom Y → ↑X →* ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `MonCat` back into a `MonoidHom`.
-/
abbrev Hom.hom {X Y : MonCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := MonCat) f

/-- Typecheck a `MonoidHom` as a morphism in `MonCat`. -/
@[to_additive /-- Typecheck an `AddMonoidHom` as a morphism in `AddMonCat`. -/]
/-
**MonCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `MonCat`。
形式化陈述：ofHom {X Y : Type u} [Monoid X] [Monoid Y] (f : X ->* Y) : of X ⟶ of Y
参数：f : X ->* Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `MonoidHom` as a morphism in `MonCat`.
-/
abbrev ofHom {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := MonCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
@[to_additive /-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/]
/-
**MonCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `MonCat.Hom.Simps`。
形式化陈述：(X Y : MonCat) → X.Hom Y → ↑X →* ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : MonCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)
initialize_simps_projections AddMonCat.Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
/-
**MonCat.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：coe_id {X : MonCat} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : MonCat} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
/-
**MonCat.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：coe_comp {X Y Z : MonCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘
 f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : MonCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive (attr := simp)]
/-
**MonCat.forget_map** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：forget_map {X Y : MonCat} (f : X ⟶ Y) : (forget MonCat).map f = (f : _ -> 
_)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map {X Y : MonCat} (f : X ⟶ Y) :
    (forget MonCat).map f = (f : _ → _) := rfl

@[to_additive (attr := ext)]
/-
**MonCat.ext** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：ext {X Y : MonCat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : MonCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
/-
**MonCat.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `MonCat`。
形式化陈述：coe_of (M : Type u) [Monoid M] : (MonCat.of M : Type u) = M
参数：M : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (M : Type u) [Monoid M] : (MonCat.of M : Type u) = M := rfl

@[to_additive (attr := simp)]
/-
**MonCat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：hom_id {M : MonCat} : (𝟙 M : M ⟶ M).hom = MonoidHom.id M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {M : MonCat} : (𝟙 M : M ⟶ M).hom = MonoidHom.id M := rfl

/- Provided for rewriting. -/
@[to_additive]
/-
**MonCat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：id_apply (M : MonCat) (x : M) : (𝟙 M : M ⟶ M) x = x
参数：M : MonCat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (M : MonCat) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

@[to_additive (attr := simp)]
/-
**MonCat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：hom_comp {M N T : MonCat} (f : M ⟶ N) (g : N ⟶ T) : (f ≫ g).hom = g.hom.co
mp f.hom
参数：f : M ⟶ N；g : N ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {M N T : MonCat} (f : M ⟶ N) (g : N ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
/-
**MonCat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：comp_apply {M N T : MonCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) : (f ≫ g) x = 
g (f x)
参数：f : M ⟶ N；g : N ⟶ T；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {M N T : MonCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
/-
**MonCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：hom_ext {M N : MonCat} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonCat.Hom.ext`：∀ {A B : MonCat} {x y : A.Hom B}, x.hom' = y.hom' → x = 
y
-/
lemma hom_ext {M N : MonCat} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
/-
**MonCat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：hom_ofHom {M N : Type u} [Monoid M] [Monoid N] (f : M ->* N) : (ofHom f).h
om = f
参数：f : M ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {M N : Type u} [Monoid M] [Monoid N] (f : M →* N) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
/-
**MonCat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：ofHom_hom {M N : MonCat} (f : M ⟶ N) : ofHom (Hom.hom f) = f
参数：f : M ⟶ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {M N : MonCat} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
/-
**MonCat.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：ofHom_id {M : Type u} [Monoid M] : ofHom (MonoidHom.id M) = 𝟙 (of M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {M : Type u} [Monoid M] : ofHom (MonoidHom.id M) = 𝟙 (of M) := rfl

@[to_additive (attr := simp)]
/-
**MonCat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：ofHom_comp {M N P : Type u} [Monoid M] [Monoid N] [Monoid P] (f : M ->* N)
 (g : N ->* P) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : M ->* N；g : N ->* P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {M N P : Type u} [Monoid M] [Monoid N] [Monoid P]
    (f : M →* N) (g : N →* P) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
/-
**MonCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：ofHom_apply {X Y : Type u} [Monoid X] [Monoid Y] (f : X ->* Y) (x : X) : (
ofHom f) x = f x
参数：f : X ->* Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl

@[to_additive]
/-
**MonCat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：inv_hom_apply {M N : MonCat} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x
参数：e : M ≅ N；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_hom_apply {M N : MonCat} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  simp

@[to_additive]
/-
**MonCat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：hom_inv_apply {M N : MonCat} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s
参数：e : M ≅ N；s : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_inv_apply {M N : MonCat} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  simp

@[to_additive]
/-
**MonCat.** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited MonCat :=
  -- The default instance for `Monoid PUnit` is derived via `CommRing` which breaks to_additive
  ⟨@of PUnit (@DivInvMonoid.toMonoid _ (@Group.toDivInvMonoid _
    (@CommGroup.toGroup _ PUnit.commGroup)))⟩

@[to_additive]
/-
**MonCat.** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : MonCat.{u}) : One (X ⟶ Y) := ⟨ofHom 1⟩

@[to_additive (attr := simp)]
/-
**MonCat.hom_one** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：hom_one (X Y : MonCat.{u}) : (1 : X ⟶ Y).hom = 1
参数：X Y : MonCat.{u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_one (X Y : MonCat.{u}) : (1 : X ⟶ Y).hom = 1 := rfl

@[to_additive]
/-
**MonCat.oneHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：oneHom_apply (X Y : MonCat.{u}) (x : X) : (1 : X ⟶ Y).hom x = 1
参数：X Y : MonCat.{u}；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma oneHom_apply (X Y : MonCat.{u}) (x : X) : (1 : X ⟶ Y).hom x = 1 := rfl

@[to_additive (attr := simp)]
/-
**MonCat.one_of** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：one_of {A : Type*} [Monoid A] : (1 : MonCat.of A) = (1 : A)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_of {A : Type*} [Monoid A] : (1 : MonCat.of A) = (1 : A) := rfl

@[to_additive (attr := simp)]
/-
**MonCat.mul_of** 是 Mathlib 中的一个引理，位于命名空间 `MonCat`。
形式化陈述：mul_of {A : Type*} [Monoid A] (a b : A) : @HMul.hMul (MonCat.of A) (MonCat
.of A) (MonCat.of A) _ a b = a * b
参数：a b : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_of {A : Type*} [Monoid A] (a b : A) :
    @HMul.hMul (MonCat.of A) (MonCat.of A) (MonCat.of A) _ a b = a * b := rfl

/-- Universe lift functor for monoids. -/
@[to_additive (attr := simps)
  /-- Universe lift functor for additive monoids. -/]
/-
**MonCat.uliftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `MonCat`。
形式化陈述：uliftFunctor : MonCat.{v} ⥤ MonCat.{max v u} where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def uliftFunctor : MonCat.{v} ⥤ MonCat.{max v u} where
  obj X := MonCat.of (ULift.{u, v} X)
  map {_ _} f := MonCat.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end MonCat

/-- The category of additive commutative monoids and monoid morphisms. -/
/-
**AddCommMonCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of additive commutative monoids and monoid morphisms.
-/
structure AddCommMonCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddCommMonoid carrier]

/-- The category of commutative monoids and monoid morphisms. -/
@[to_additive AddCommMonCat]
/-
**CommMonCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of commutative monoids and monoid morphisms.
-/
structure CommMonCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : CommMonoid carrier]

attribute [instance] AddCommMonCat.str CommMonCat.str

initialize_simps_projections AddCommMonCat (carrier → coe, -str)
initialize_simps_projections CommMonCat (carrier → coe, -str)

namespace CommMonCat

@[to_additive]
/-
**CommMonCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort CommMonCat (Type u) :=
  ⟨CommMonCat.carrier⟩

attribute [coe] AddCommMonCat.carrier CommMonCat.carrier

/-- Construct a bundled `CommMonCat` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddCommMonCat` from the underlying type and typeclass. -/]
/-
**CommMonCat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommMonCat`。
形式化陈述：of (M : Type u) [CommMonoid M] : CommMonCat
参数：M : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `CommMonCat` from the underlying type and typeclass.
-/
abbrev of (M : Type u) [CommMonoid M] : CommMonCat := ⟨M⟩

end CommMonCat

/-- The type of morphisms in `AddCommMonCat`. -/
@[ext]
/-
**AddCommMonCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddCommMonCat`。
形式化陈述：AddCommMonCat → AddCommMonCat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `AddCommMonCat`.
-/
structure AddCommMonCat.Hom (A B : AddCommMonCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →+ B

/-- The type of morphisms in `CommMonCat`. -/
@[to_additive, ext]
/-
**CommMonCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CommMonCat`。
形式化陈述：CommMonCat → CommMonCat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `CommMonCat`.
-/
structure CommMonCat.Hom (A B : CommMonCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →* B

namespace CommMonCat

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/-
**CommMonCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category CommMonCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/-
**CommMonCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory CommMonCat (· →* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommMonCat` back into a `MonoidHom`. -/
@[to_additive /-- Turn a morphism in `AddCommMonCat` back into an `AddMonoidHom`. -/]
/-
**CommMonCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `CommMonCat.Hom`。
形式化陈述：{X Y : CommMonCat} → X.Hom Y → ↑X →* ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `CommMonCat` back into a `MonoidHom`.
-/
abbrev Hom.hom {X Y : CommMonCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := CommMonCat) f

/-- Typecheck a `MonoidHom` as a morphism in `CommMonCat`. -/
@[to_additive /-- Typecheck an `AddMonoidHom` as a morphism in `AddCommMonCat`. -/]
/-
**CommMonCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommMonCat`。
形式化陈述：ofHom {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X ->* Y) : of X ⟶ 
of Y
参数：f : X ->* Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `MonoidHom` as a morphism in `CommMonCat`.
-/
abbrev ofHom {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X →* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := CommMonCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
@[to_additive /-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/]
/-
**CommMonCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `CommMonCat.Hom.Simps`。
形式化陈述：(X Y : CommMonCat) → X.Hom Y → ↑X →* ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : CommMonCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)
initialize_simps_projections AddCommMonCat.Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
/-
**CommMonCat.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
形式化陈述：coe_id {X : CommMonCat} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : CommMonCat} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
/-
**CommMonCat.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
形式化陈述：coe_comp {X Y Z : CommMonCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) =
 g ∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : CommMonCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[deprecated (since := "2026-02-15")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
/-
**CommMonCat.ext** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
形式化陈述：ext {X Y : CommMonCat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : CommMonCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive (attr := simp)]
/-
**CommMonCat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
形式化陈述：hom_id {M : CommMonCat} : (𝟙 M : M ⟶ M).hom = MonoidHom.id M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {M : CommMonCat} : (𝟙 M : M ⟶ M).hom = MonoidHom.id M := rfl

/- Provided for rewriting. -/
@[to_additive]
/-
**CommMonCat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
形式化陈述：id_apply (M : CommMonCat) (x : M) : (𝟙 M : M ⟶ M) x = x
参数：M : CommMonCat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (M : CommMonCat) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

@[to_additive (attr := simp)]
/-
**CommMonCat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
形式化陈述：hom_comp {M N T : CommMonCat} (f : M ⟶ N) (g : N ⟶ T) : (f ≫ g).hom = g.ho
m.comp f.hom
参数：f : M ⟶ N；g : N ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {M N T : CommMonCat} (f : M ⟶ N) (g : N ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
/-
**CommMonCat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
形式化陈述：comp_apply {M N T : CommMonCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) : (f ≫ g) 
x = g (f x)
参数：f : M ⟶ N；g : N ⟶ T；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {M N T : CommMonCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
/-
**CommMonCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
形式化陈述：hom_ext {M N : CommMonCat} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommMonCat.Hom.ext`：∀ {A B : CommMonCat} {x y : A.Hom B}, x.hom' = y.hom
' → x = y
-/
lemma hom_ext {M N : CommMonCat} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
/-
**CommMonCat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
形式化陈述：hom_ofHom {M N : Type u} [CommMonoid M] [CommMonoid N] (f : M ->* N) : (of
Hom f).hom = f
参数：f : M ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {M N : Type u} [CommMonoid M] [CommMonoid N] (f : M →* N) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
/-
**CommMonCat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
形式化陈述：ofHom_hom {M N : CommMonCat} (f : M ⟶ N) : ofHom (Hom.hom f) = f
参数：f : M ⟶ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {M N : CommMonCat} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
/-
**CommMonCat.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
形式化陈述：ofHom_id {M : Type u} [CommMonoid M] : ofHom (MonoidHom.id M) = 𝟙 (of M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {M : Type u} [CommMonoid M] : ofHom (MonoidHom.id M) = 𝟙 (of M) := rfl

@[to_additive (attr := simp)]
/-
**CommMonCat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
形式化陈述：ofHom_comp {M N P : Type u} [CommMonoid M] [CommMonoid N] [CommMonoid P] (
f : M ->* N) (g : N ->* P) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : M ->* N；g : N ->* P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {M N P : Type u} [CommMonoid M] [CommMonoid N] [CommMonoid P]
    (f : M →* N) (g : N →* P) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
/-
**CommMonCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
形式化陈述：ofHom_apply {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X ->* Y) (x 
: X) : (ofHom f) x = f x
参数：f : X ->* Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl

@[to_additive]
/-
**CommMonCat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
形式化陈述：inv_hom_apply {M N : CommMonCat} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x
参数：e : M ≅ N；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_hom_apply {M N : CommMonCat} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  simp

@[to_additive]
/-
**CommMonCat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
形式化陈述：hom_inv_apply {M N : CommMonCat} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s
参数：e : M ≅ N；s : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_inv_apply {M N : CommMonCat} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  simp

@[to_additive]
/-
**CommMonCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited CommMonCat :=
  -- The default instance for `CommMonoid PUnit` is derived via `CommRing` which breaks to_additive
  ⟨@of PUnit (@CommGroup.toCommMonoid _ PUnit.commGroup)⟩

@[to_additive]
/-
**CommMonCat.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `CommMonCat`。
形式化陈述：coe_of (R : Type u) [CommMonoid R] : (CommMonCat.of R : Type u) = R
参数：R : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (R : Type u) [CommMonoid R] : (CommMonCat.of R : Type u) = R :=
  rfl

@[to_additive hasForgetToAddMonCat]
/-
**CommMonCat.hasForgetToMonCat** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
形式化陈述：hasForgetToMonCat : HasForget₂ CommMonCat MonCat where forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToMonCat : HasForget₂ CommMonCat MonCat where
  forget₂ :=
    { obj R := MonCat.of R
      map f := MonCat.ofHom f.hom }
/-
**CommMonCat.coe_forget** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma coe_forget₂_obj (X : CommMonCat) :
    ((forget₂ CommMonCat MonCat).obj X : Type _) = X := rfl
/-
**CommMonCat.hom_forget** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma hom_forget₂_map {X Y : CommMonCat}
    (f : X ⟶ Y) :
    ((forget₂ CommMonCat MonCat).map f).hom = f.hom := rfl
/-
**CommMonCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `CommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma forget₂_map_ofHom {X Y : Type u} [CommMonoid X] [CommMonoid Y]
    (f : X →* Y) :
    (forget₂ CommMonCat MonCat).map (ofHom f) = MonCat.ofHom f := rfl

/-- The forgetful functor from `CommMonCat` to `MonCat` is fully faithful. -/
@[to_additive fullyFaithfulForgetToAddMonCat
  /-- The forgetful functor from `AddCommMonCat` to `AddMonCat` is fully faithful. -/]
/-
**CommMonCat.fullyFaithfulForgetToMonCat** 是 Mathlib 中的一个定义，位于命名空间 `CommMonCat`。
形式化陈述：fullyFaithfulForgetToMonCat : (forget₂ CommMonCat.{u} MonCat.{u}).FullyFai
thful where preimage f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def fullyFaithfulForgetToMonCat : (forget₂ CommMonCat.{u} MonCat.{u}).FullyFaithful where
  preimage f := ofHom f.hom

@[to_additive]
/-
**CommMonCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ CommMonCat.{u} MonCat.{u}).Full :=
  fullyFaithfulForgetToMonCat.full

@[to_additive]
/-
**CommMonCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe CommMonCat.{u} MonCat.{u} where coe := (forget₂ CommMonCat MonCat).obj

/-- Universe lift functor for commutative monoids. -/
@[to_additive (attr := simps)
  /-- Universe lift functor for additive commutative monoids. -/]
/-
**CommMonCat.uliftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CommMonCat`。
形式化陈述：uliftFunctor : CommMonCat.{v} ⥤ CommMonCat.{max v u} where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def uliftFunctor : CommMonCat.{v} ⥤ CommMonCat.{max v u} where
  obj X := CommMonCat.of (ULift.{u, v} X)
  map {_ _} f := CommMonCat.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end CommMonCat

variable {X Y : Type u}

section

variable [Monoid X] [Monoid Y]

/-- Build an isomorphism in the category `MonCat` from a `MulEquiv` between `Monoid`s. -/
@[to_additive (attr := simps) AddEquiv.toAddMonCatIso
      /-- Build an isomorphism in the category `AddMonCat` from
an `AddEquiv` between `AddMonoid`s. -/]
/-
**MulEquiv.toMonCatIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.toMonCatIso (e : X ≃* Y) : MonCat.of X ≅ MonCat.of Y where hom
参数：e : X ≃* Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulEquiv.toMonCatIso (e : X ≃* Y) : MonCat.of X ≅ MonCat.of Y where
  hom := MonCat.ofHom e.toMonoidHom
  inv := MonCat.ofHom e.symm.toMonoidHom

end

section

variable [CommMonoid X] [CommMonoid Y]

/-- Build an isomorphism in the category `CommMonCat` from a `MulEquiv` between `CommMonoid`s. -/
@[to_additive (attr := simps) AddEquiv.toAddCommMonCatIso]
/-
**MulEquiv.toCommMonCatIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.toCommMonCatIso (e : X ≃* Y) : CommMonCat.of X ≅ CommMonCat.of Y 
where hom
参数：e : X ≃* Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an isomorphism in the category `CommMonCat` from a `MulEquiv` between `Com
mMonoid`s.
-/
def MulEquiv.toCommMonCatIso (e : X ≃* Y) : CommMonCat.of X ≅ CommMonCat.of Y where
  hom := CommMonCat.ofHom e.toMonoidHom
  inv := CommMonCat.ofHom e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddCommMonCat`
from an `AddEquiv` between `AddCommMonoid`s. -/
add_decl_doc AddEquiv.toAddCommMonCatIso

end

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `MonCat`. -/
@[to_additive addMonCatIsoToAddEquiv
      /-- Build an `AddEquiv` from an isomorphism in the category
`AddMonCat`. -/]
/-
**CategoryTheory.Iso.monCatIsoToMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Iso`。
形式化陈述：monCatIsoToMulEquiv {X Y : MonCat} (i : X ≅ Y) : X ≃* Y
参数：i : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def monCatIsoToMulEquiv {X Y : MonCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

/-- Build a `MulEquiv` from an isomorphism in the category `CommMonCat`. -/
@[to_additive /-- Build an `AddEquiv` from an isomorphism in the category
`AddCommMonCat`. -/]
/-
**CategoryTheory.Iso.commMonCatIsoToMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Iso`。
形式化陈述：commMonCatIsoToMulEquiv {X Y : CommMonCat} (i : X ≅ Y) : X ≃* Y
参数：i : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def commMonCatIsoToMulEquiv {X Y : CommMonCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

end CategoryTheory.Iso

/-- multiplicative equivalences between `Monoid`s are the same as (isomorphic to) isomorphisms
in `MonCat` -/
@[to_additive addEquivIsoAddMonCatIso]
/-
**mulEquivIsoMonCatIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulEquivIsoMonCatIso {X Y : Type u} [Monoid X] [Monoid Y] : (X ≃* Y) ≅ (Mo
nCat.of X ≅ MonCat.of Y) where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
multiplicative equivalences between `Monoid`s are the same as (isomorphic to) is
omorphisms
in `MonCat`
-/
def mulEquivIsoMonCatIso {X Y : Type u} [Monoid X] [Monoid Y] :
    (X ≃* Y) ≅ (MonCat.of X ≅ MonCat.of Y) where
  hom := ↾fun e ↦ e.toMonCatIso
  inv := ↾fun i ↦ i.monCatIsoToMulEquiv

/-- additive equivalences between `AddMonoid`s are the same
as (isomorphic to) isomorphisms in `AddMonCat` -/
add_decl_doc addEquivIsoAddMonCatIso

/-- multiplicative equivalences between `CommMonoid`s are the same as (isomorphic to) isomorphisms
in `CommMonCat` -/
@[to_additive addEquivIsoAddCommMonCatIso]
/-
**mulEquivIsoCommMonCatIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulEquivIsoCommMonCatIso {X Y : Type u} [CommMonoid X] [CommMonoid Y] : (X
 ≃* Y) ≅ (CommMonCat.of X ≅ CommMonCat.of Y) where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
multiplicative equivalences between `CommMonoid`s are the same as (isomorphic to
) isomorphisms
in `CommMonCat`
-/
def mulEquivIsoCommMonCatIso {X Y : Type u} [CommMonoid X] [CommMonoid Y] :
    (X ≃* Y) ≅ (CommMonCat.of X ≅ CommMonCat.of Y) where
  hom := ↾fun e ↦ e.toCommMonCatIso
  inv := ↾fun i ↦ i.commMonCatIsoToMulEquiv

/-- additive equivalences between `AddCommMonoid`s are
the same as (isomorphic to) isomorphisms in `AddCommMonCat` -/
add_decl_doc addEquivIsoAddCommMonCatIso

@[to_additive]
/-
**MonCat.forget_reflects_isos** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MonCat.forget_reflects_isos : (forget MonCat.{u}).ReflectsIsomorphisms whe
re reflects {X Y} f _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance MonCat.forget_reflects_isos : (forget MonCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget MonCat).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toMonCatIso.isIso_hom

@[to_additive]
/-
**CommMonCat.forget_reflects_isos** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CommMonCat.forget_reflects_isos : (forget CommMonCat.{u}).ReflectsIsomorph
isms where reflects {X Y} f _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance CommMonCat.forget_reflects_isos : (forget CommMonCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommMonCat).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toCommMonCatIso.isIso_hom

/-- Ensure that `forget₂ CommMonCat MonCat` automatically reflects isomorphisms. -/
@[to_additive
  /-- Ensure that `forget₂ AddCommMonCat AddMonCat` automatically reflects isomorphisms. -/]
/-
**CommMonCat.forget** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance CommMonCat.forget₂_full : (forget₂ CommMonCat MonCat).Full where
  map_surjective f := ⟨ofHom f.hom, rfl⟩
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (forget₂ CommMonCat MonCat).ReflectsIsomorphisms := inferInstance

/-!
`@[simp]` lemmas for `MonoidHom.comp` and categorical identities.
-/

/-- The equivalence between `AddMonCat` and `MonCat`. -/
@[simps]
/-
**AddMonCat.equivalence** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddMonCat.equivalence : AddMonCat ≌ MonCat where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `AddMonCat` and `MonCat`.
-/
def AddMonCat.equivalence : AddMonCat ≌ MonCat where
  functor := { obj X := .of (Multiplicative X), map f := MonCat.ofHom f.hom.toMultiplicative }
  inverse := { obj X := .of (Additive X), map f := ofHom f.hom.toAdditive }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The equivalence between `AddCommMonCat` and `CommMonCat`. -/
@[simps]
/-
**AddCommMonCat.equivalence** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddCommMonCat.equivalence : AddCommMonCat ≌ CommMonCat where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `AddCommMonCat` and `CommMonCat`.
-/
def AddCommMonCat.equivalence : AddCommMonCat ≌ CommMonCat where
  functor := { obj X := .of (Multiplicative X), map f := CommMonCat.ofHom f.hom.toMultiplicative }
  inverse := { obj X := .of (Additive X), map f := ofHom f.hom.toAdditive }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
