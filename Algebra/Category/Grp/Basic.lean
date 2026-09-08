/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Category instances for Group, AddGroup, CommGroup, and AddCommGroup.

We introduce the bundled categories:
* `GrpCat`
* `AddGrpCat`
* `CommGrpCat`
* `AddCommGrpCat`

along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/

@[expose] public section

universe u v

open CategoryTheory

/-- The category of additive groups and group morphisms. -/
/-
**AddGrpCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of additive groups and group morphisms.
-/
structure AddGrpCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddGroup carrier]

/-- The category of groups and group morphisms. -/
@[to_additive]
/-
**GrpCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of groups and group morphisms.
-/
structure GrpCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : Group carrier]

attribute [instance] AddGrpCat.str GrpCat.str

initialize_simps_projections AddGrpCat (carrier → coe, -str)
initialize_simps_projections GrpCat (carrier → coe, -str)

namespace GrpCat

@[to_additive]
/-
**GrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort GrpCat (Type u) :=
  ⟨GrpCat.carrier⟩

attribute [coe] AddGrpCat.carrier GrpCat.carrier

/-- Construct a bundled `GrpCat` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddGrpCat` from the underlying type and typeclass. -/]
/-
**GrpCat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `GrpCat`。
形式化陈述：of (M : Type u) [Group M] : GrpCat
参数：M : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `GrpCat` from the underlying type and typeclass.
-/
abbrev of (M : Type u) [Group M] : GrpCat := ⟨M⟩

end GrpCat

/-- The type of morphisms in `AddGrpCat R`. -/
@[ext]
/-
**AddGrpCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddGrpCat`。
形式化陈述：AddGrpCat → AddGrpCat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `AddGrpCat R`.
-/
structure AddGrpCat.Hom (A B : AddGrpCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →+ B

/-- The type of morphisms in `GrpCat R`. -/
@[to_additive, ext]
/-
**GrpCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `GrpCat`。
形式化陈述：GrpCat → GrpCat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `GrpCat R`.
-/
structure GrpCat.Hom (A B : GrpCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →* B

namespace GrpCat

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/-
**GrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category GrpCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/-
**GrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory GrpCat (· →* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `GrpCat` back into a `MonoidHom`. -/
@[to_additive /-- Turn a morphism in `AddGrpCat` back into an `AddMonoidHom`. -/]
/-
**GrpCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat.Hom`。
形式化陈述：{X Y : GrpCat} → X.Hom Y → ↑X →* ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `GrpCat` back into a `MonoidHom`.
-/
abbrev Hom.hom {X Y : GrpCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := GrpCat) f

/-- Typecheck a `MonoidHom` as a morphism in `GrpCat`. -/
@[to_additive /-- Typecheck an `AddMonoidHom` as a morphism in `AddGrpCat`. -/]
/-
**GrpCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `GrpCat`。
形式化陈述：ofHom {X Y : Type u} [Group X] [Group Y] (f : X ->* Y) : of X ⟶ of Y
参数：f : X ->* Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `MonoidHom` as a morphism in `GrpCat`.
-/
abbrev ofHom {X Y : Type u} [Group X] [Group Y] (f : X →* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := GrpCat) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**GrpCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat.Hom.Simps`。
形式化陈述：(X Y : GrpCat) → X.Hom Y → ↑X →* ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : GrpCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)
initialize_simps_projections AddGrpCat.Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
/-
**GrpCat.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：coe_id {X : GrpCat} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : GrpCat} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
/-
**GrpCat.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：coe_comp {X Y Z : GrpCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘
 f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : GrpCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
/-
**GrpCat.ext** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：ext {X Y : GrpCat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : GrpCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
/-
**GrpCat.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat`。
形式化陈述：coe_of (R : Type u) [Group R] : ↑(GrpCat.of R) = R
参数：R : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (R : Type u) [Group R] : ↑(GrpCat.of R) = R :=
  rfl

@[to_additive (attr := simp)]
/-
**GrpCat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：hom_id {X : GrpCat} : (𝟙 X : X ⟶ X).hom = MonoidHom.id X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {X : GrpCat} : (𝟙 X : X ⟶ X).hom = MonoidHom.id X := rfl

/- Provided for rewriting. -/
@[to_additive]
/-
**GrpCat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：id_apply (X : GrpCat) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : GrpCat；x : X。
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
lemma id_apply (X : GrpCat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[to_additive (attr := simp)]
/-
**GrpCat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：hom_comp {X Y T : GrpCat} (f : X ⟶ Y) (g : Y ⟶ T) : (f ≫ g).hom = g.hom.co
mp f.hom
参数：f : X ⟶ Y；g : Y ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y T : GrpCat} (f : X ⟶ Y) (g : Y ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
/-
**GrpCat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：comp_apply {X Y T : GrpCat} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) : (f ≫ g) x = 
g (f x)
参数：f : X ⟶ Y；g : Y ⟶ T；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {X Y T : GrpCat} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
/-
**GrpCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：hom_ext {X Y : GrpCat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GrpCat.Hom.ext`：∀ {A B : GrpCat} {x y : A.Hom B}, x.hom' = y.hom' → x = 
y
-/
lemma hom_ext {X Y : GrpCat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
/-
**GrpCat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：hom_ofHom {R S : Type u} [Group R] [Group S] (f : R ->* S) : (ofHom f).hom
 = f
参数：f : R ->* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {R S : Type u} [Group R] [Group S] (f : R →* S) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
/-
**GrpCat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：ofHom_hom {X Y : GrpCat} (f : X ⟶ Y) : ofHom (Hom.hom f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {X Y : GrpCat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
/-
**GrpCat.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：ofHom_id {X : Type u} [Group X] : ofHom (MonoidHom.id X) = 𝟙 (of X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {X : Type u} [Group X] : ofHom (MonoidHom.id X) = 𝟙 (of X) := rfl

@[to_additive (attr := simp)]
/-
**GrpCat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：ofHom_comp {X Y Z : Type u} [Group X] [Group Y] [Group Z] (f : X ->* Y) (g
 : Y ->* Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : X ->* Y；g : Y ->* Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {X Y Z : Type u} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (g : Y →* Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
/-
**GrpCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：ofHom_apply {X Y : Type u} [Group X] [Group Y] (f : X ->* Y) (x : X) : (of
Hom f) x = f x
参数：f : X ->* Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [Group X] [Group Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl

-- This is essentially an alias for `Iso.hom_inv_id_apply`; consider deprecation?
@[to_additive]
/-
**GrpCat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：inv_hom_apply {X Y : GrpCat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x
参数：e : X ≅ Y；x : X。
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
lemma inv_hom_apply {X Y : GrpCat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

-- This is essentially an alias for `Iso.inv_hom_id_apply`; consider deprecation?
@[to_additive]
/-
**GrpCat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：hom_inv_apply {X Y : GrpCat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s
参数：e : X ≅ Y；s : Y。
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
lemma hom_inv_apply {X Y : GrpCat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

@[to_additive]
/-
**GrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited GrpCat :=
  ⟨GrpCat.of PUnit⟩

@[to_additive hasForgetToAddMonCat]
/-
**GrpCat.hasForgetToMonCat** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat`。
形式化陈述：hasForgetToMonCat : HasForget₂ GrpCat MonCat where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToMonCat : HasForget₂ GrpCat MonCat where
  forget₂.obj X := MonCat.of X
  forget₂.map f := MonCat.ofHom f.hom
/-
**GrpCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma forget₂_map_ofHom {X Y : Type u} [Group X] [Group Y]
    (f : X →* Y) :
    (forget₂ GrpCat MonCat).map (ofHom f) = MonCat.ofHom f := rfl
/-
**GrpCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma forget₂_map {R S : GrpCat} (f : R ⟶ S) (x) :
    (forget₂ GrpCat MonCat).map f x = f x := rfl

@[to_additive]
/-
**GrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe GrpCat.{u} MonCat.{u} where coe := (forget₂ GrpCat MonCat).obj

@[to_additive]
/-
**GrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G H : GrpCat) : One (G ⟶ H) where
  one := ofHom 1

@[to_additive (attr := simp)]
/-
**GrpCat.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat`。
形式化陈述：one_apply (G H : GrpCat) (g : G) : ((1 : G ⟶ H) : G -> H) g = 1
参数：G H : GrpCat；g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (G H : GrpCat) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
  rfl

@[to_additive]
/-
**GrpCat.ofHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：ofHom_injective {X Y : Type u} [Group X] [Group Y] : Function.Injective (f
un (f : X ->* Y) => ofHom f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
-/
lemma ofHom_injective {X Y : Type u} [Group X] [Group Y] :
    Function.Injective (fun (f : X →* Y) ↦ ofHom f) := by
  intro _ _ h
  ext
  apply ConcreteCategory.congr_hom h

/-- The forgetful functor from groups to monoids is fully faithful. -/
@[to_additive fullyFaihtfulForget₂ToAddMonCat
  /-- The forgetful functor from additive groups to additive monoids is fully faithful. -/]
/-
**GrpCat.fullyFaithfulForget** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def fullyFaithfulForget₂ToMonCat : (forget₂ GrpCat.{u} MonCat).FullyFaithful where
  preimage f := ofHom f.hom

@[to_additive]
/-
**GrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ GrpCat.{u} MonCat).Full :=
  fullyFaithfulForget₂ToMonCat.full

-- We verify that simp lemmas apply when coercing morphisms to functions.
@[to_additive]
/-
**GrpCat.** 是 Mathlib 中的一个示例，位于命名空间 `GrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {R S : GrpCat} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

/-- Universe lift functor for groups. -/
@[to_additive (attr := simps obj map)
  /-- Universe lift functor for additive groups. -/]
/-
**GrpCat.uliftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat`。
形式化陈述：uliftFunctor : GrpCat.{v} ⥤ GrpCat.{max v u} where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def uliftFunctor : GrpCat.{v} ⥤ GrpCat.{max v u} where
  obj X := GrpCat.of (ULift.{u, v} X)
  map {_ _} f := GrpCat.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end GrpCat

/-- The category of additive groups and group morphisms. -/
/-
**AddCommGrpCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of additive groups and group morphisms.
-/
structure AddCommGrpCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddCommGroup carrier]

/-- The category of groups and group morphisms. -/
@[to_additive]
/-
**CommGrpCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of groups and group morphisms.
-/
structure CommGrpCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : CommGroup carrier]

attribute [instance] AddCommGrpCat.str CommGrpCat.str

initialize_simps_projections AddCommGrpCat (carrier → coe, -str)
initialize_simps_projections CommGrpCat (carrier → coe, -str)

/-- `Ab` is an abbreviation for `AddCommGrpCat`, for the sake of mathematicians' sanity. -/
/-
**Ab** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Ab
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Ab` is an abbreviation for `AddCommGrpCat`, for the sake of mathematicians' san
ity.
-/
abbrev Ab := AddCommGrpCat

namespace CommGrpCat

@[to_additive]
/-
**CommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort CommGrpCat (Type u) :=
  ⟨CommGrpCat.carrier⟩

attribute [coe] AddCommGrpCat.carrier CommGrpCat.carrier

/-- Construct a bundled `CommGrpCat` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddCommGrpCat` from the underlying type and typeclass. -/]
/-
**CommGrpCat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommGrpCat`。
形式化陈述：of (M : Type u) [CommGroup M] : CommGrpCat
参数：M : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `CommGrpCat` from the underlying type and typeclass.
-/
abbrev of (M : Type u) [CommGroup M] : CommGrpCat := ⟨M⟩

end CommGrpCat

/-- The type of morphisms in `AddCommGrpCat R`. -/
@[ext]
/-
**AddCommGrpCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddCommGrpCat`。
形式化陈述：AddCommGrpCat → AddCommGrpCat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `AddCommGrpCat R`.
-/
structure AddCommGrpCat.Hom (A B : AddCommGrpCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →+ B

/-- The type of morphisms in `CommGrpCat R`. -/
@[to_additive, ext]
/-
**CommGrpCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CommGrpCat`。
形式化陈述：CommGrpCat → CommGrpCat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `CommGrpCat R`.
-/
structure CommGrpCat.Hom (A B : CommGrpCat.{u}) where
  private mk ::
  /-- The underlying monoid homomorphism. -/
  hom' : A →* B

namespace CommGrpCat

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/-
**CommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category CommGrpCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MonoidHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/-
**CommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory CommGrpCat (· →* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommGrpCat` back into a `MonoidHom`. -/
@[to_additive /-- Turn a morphism in `AddCommGrpCat` back into an `AddMonoidHom`. -/]
/-
**CommGrpCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `CommGrpCat.Hom`。
形式化陈述：{X Y : CommGrpCat} → X.Hom Y → ↑X →* ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `CommGrpCat` back into a `MonoidHom`.
-/
abbrev Hom.hom {X Y : CommGrpCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := CommGrpCat) f

/-- Typecheck a `MonoidHom` as a morphism in `CommGrpCat`. -/
@[to_additive /-- Typecheck an `AddMonoidHom` as a morphism in `AddCommGrpCat`. -/]
/-
**CommGrpCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommGrpCat`。
形式化陈述：ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X ->* Y) : of X ⟶ of
 Y
参数：f : X ->* Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `MonoidHom` as a morphism in `CommGrpCat`.
-/
abbrev ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := CommGrpCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
@[to_additive /-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/]
/-
**CommGrpCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `CommGrpCat.Hom.Simps`。
形式化陈述：(X Y : CommGrpCat) → X.Hom Y → ↑X →* ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : CommGrpCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)
initialize_simps_projections AddCommGrpCat.Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
/-
**CommGrpCat.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：coe_id {X : CommGrpCat} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : CommGrpCat} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
/-
**CommGrpCat.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：coe_comp {X Y Z : CommGrpCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) =
 g ∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : CommGrpCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
/-
**CommGrpCat.ext** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：ext {X Y : CommGrpCat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : CommGrpCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
/-
**CommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited CommGrpCat :=
  ⟨CommGrpCat.of PUnit⟩

@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
/-
**CommGrpCat.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `CommGrpCat`。
形式化陈述：coe_of (R : Type u) [CommGroup R] : ↑(CommGrpCat.of R) = R
参数：R : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (R : Type u) [CommGroup R] : ↑(CommGrpCat.of R) = R :=
  rfl

@[to_additive (attr := simp)]
/-
**CommGrpCat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：hom_id {X : CommGrpCat} : (𝟙 X : X ⟶ X).hom = MonoidHom.id X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {X : CommGrpCat} : (𝟙 X : X ⟶ X).hom = MonoidHom.id X := rfl

/- Provided for rewriting. -/
@[to_additive]
/-
**CommGrpCat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：id_apply (X : CommGrpCat) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : CommGrpCat；x : X。
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
lemma id_apply (X : CommGrpCat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[to_additive (attr := simp)]
/-
**CommGrpCat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：hom_comp {X Y T : CommGrpCat} (f : X ⟶ Y) (g : Y ⟶ T) : (f ≫ g).hom = g.ho
m.comp f.hom
参数：f : X ⟶ Y；g : Y ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y T : CommGrpCat} (f : X ⟶ Y) (g : Y ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
/-
**CommGrpCat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：comp_apply {X Y T : CommGrpCat} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) : (f ≫ g) 
x = g (f x)
参数：f : X ⟶ Y；g : Y ⟶ T；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {X Y T : CommGrpCat} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
/-
**CommGrpCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：hom_ext {X Y : CommGrpCat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommGrpCat.Hom.ext`：∀ {A B : CommGrpCat} {x y : A.Hom B}, x.hom' = y.hom
' → x = y
-/
lemma hom_ext {X Y : CommGrpCat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
/-
**CommGrpCat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：hom_ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X ->* Y) : (ofHo
m f).hom = f
参数：f : X ->* Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
/-
**CommGrpCat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：ofHom_hom {X Y : CommGrpCat} (f : X ⟶ Y) : ofHom (Hom.hom f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {X Y : CommGrpCat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
/-
**CommGrpCat.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：ofHom_id {X : Type u} [CommGroup X] : ofHom (MonoidHom.id X) = 𝟙 (of X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {X : Type u} [CommGroup X] : ofHom (MonoidHom.id X) = 𝟙 (of X) := rfl

@[to_additive (attr := simp)]
/-
**CommGrpCat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：ofHom_comp {X Y Z : Type u} [CommGroup X] [CommGroup Y] [CommGroup Z] (f :
 X ->* Y) (g : Y ->* Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : X ->* Y；g : Y ->* Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {X Y Z : Type u} [CommGroup X] [CommGroup Y] [CommGroup Z]
    (f : X →* Y) (g : Y →* Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
/-
**CommGrpCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：ofHom_apply {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X ->* Y) (x : 
X) : (ofHom f) x = f x
参数：f : X ->* Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl

-- This is essentially an alias for `Iso.hom_inv_id_apply`; consider deprecation?
@[to_additive]
/-
**CommGrpCat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：inv_hom_apply {X Y : CommGrpCat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x
参数：e : X ≅ Y；x : X。
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
lemma inv_hom_apply {X Y : CommGrpCat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

-- This is essentially an alias for `Iso.inv_hom_id_apply`; consider deprecation?
@[to_additive]
/-
**CommGrpCat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：hom_inv_apply {X Y : CommGrpCat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s
参数：e : X ≅ Y；s : Y。
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
lemma hom_inv_apply {X Y : CommGrpCat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

@[to_additive]
/-
**CommGrpCat.hasForgetToGroup** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat`。
形式化陈述：hasForgetToGroup : HasForget₂ CommGrpCat GrpCat where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToGroup : HasForget₂ CommGrpCat GrpCat where
  forget₂.obj X := GrpCat.of X
  forget₂.map f := GrpCat.ofHom f.hom
/-
**CommGrpCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma forget₂_grp_map_ofHom {X Y : Type u} [CommGroup X] [CommGroup Y]
    (f : X →* Y) :
    (forget₂ CommGrpCat GrpCat).map (ofHom f) = GrpCat.ofHom f := rfl
/-
**CommGrpCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma forget₂_map {R S : CommGrpCat} (f : R ⟶ S) (x) :
    (forget₂ CommGrpCat GrpCat).map f x = f x := rfl

@[to_additive]
/-
**CommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe CommGrpCat.{u} GrpCat.{u} where coe := (forget₂ CommGrpCat GrpCat).obj

/-- The forgetful functor from commutative groups to groups is fully faithful. -/
@[to_additive fullyFaihtfulForget₂ToAddGrp
/-- The forgetful functor from additive commutative groups to additive groups is fully faithful. -/]
/-
**CommGrpCat.fullyFaithfulForget** 是 Mathlib 中的一个定义，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def fullyFaithfulForget₂ToGrp : (forget₂ CommGrpCat.{u} GrpCat).FullyFaithful where
  preimage f := ofHom f.hom

@[to_additive]
/-
**CommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ CommGrpCat.{u} GrpCat).Full :=
  fullyFaithfulForget₂ToGrp.full

@[to_additive hasForgetToAddCommMonCat]
/-
**CommGrpCat.hasForgetToCommMonCat** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat`。
形式化陈述：hasForgetToCommMonCat : HasForget₂ CommGrpCat CommMonCat where forget₂.obj
 X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToCommMonCat : HasForget₂ CommGrpCat CommMonCat where
  forget₂.obj X := CommMonCat.of X
  forget₂.map f := CommMonCat.ofHom f.hom
/-
**CommGrpCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma forget₂_commMonCat_map_ofHom {X Y : Type u}
    [CommGroup X] [CommGroup Y] (f : X →* Y) :
    (forget₂ CommGrpCat CommMonCat).map (ofHom f) = CommMonCat.ofHom f := rfl

@[to_additive]
/-
**CommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe CommGrpCat.{u} CommMonCat.{u} where coe := (forget₂ CommGrpCat CommMonCat).obj

@[to_additive]
/-
**CommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G H : CommGrpCat) : One (G ⟶ H) where
  one := ofHom 1

@[to_additive (attr := simp)]
/-
**CommGrpCat.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `CommGrpCat`。
形式化陈述：one_apply (G H : CommGrpCat) (g : G) : ((1 : G ⟶ H) : G -> H) g = 1
参数：G H : CommGrpCat；g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (G H : CommGrpCat) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
  rfl

@[to_additive]
/-
**CommGrpCat.ofHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：ofHom_injective {X Y : Type u} [CommGroup X] [CommGroup Y] : Function.Inje
ctive (fun (f : X ->* Y) => ofHom f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
-/
lemma ofHom_injective {X Y : Type u} [CommGroup X] [CommGroup Y] :
    Function.Injective (fun (f : X →* Y) ↦ ofHom f) := by
  intro _ _ h
  ext
  apply ConcreteCategory.congr_hom h

-- We verify that simp lemmas apply when coercing morphisms to functions.
@[to_additive]
/-
**CommGrpCat.** 是 Mathlib 中的一个示例，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {R S : CommGrpCat} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

/-- Universe lift functor for commutative groups. -/
@[to_additive (attr := simps obj map)
  /-- Universe lift functor for additive commutative groups. -/]
/-
**CommGrpCat.uliftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CommGrpCat`。
形式化陈述：uliftFunctor : CommGrpCat.{v} ⥤ CommGrpCat.{max v u} where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def uliftFunctor : CommGrpCat.{v} ⥤ CommGrpCat.{max v u} where
  obj X := CommGrpCat.of (ULift.{u, v} X)
  map {_ _} f := CommGrpCat.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.hom.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end CommGrpCat

namespace AddCommGrpCat

-- Note that because `ℤ : Type 0`, this forces `G : AddCommGrpCat.{0}`,
-- so we write this explicitly to be clear.
-- TODO generalize this, requiring a `ULiftInstances.lean` file
/-- Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element. -/
@[simps!]
/-
**AddCommGrpCat.asHom** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
形式化陈述：asHom {G : AddCommGrpCat.{0}} (g : G) : AddCommGrpCat.of Int ⟶ G
参数：g : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element.
-/
def asHom {G : AddCommGrpCat.{0}} (g : G) : AddCommGrpCat.of ℤ ⟶ G :=
  ofHom (zmultiplesHom G g)
/-
**AddCommGrpCat.asHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat`。
形式化陈述：asHom_injective {G : AddCommGrpCat.{0}} : Function.Injective (@asHom G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddCommGrpCat.asHom_hom_apply`：∀ {G : AddCommGrpCat} (g : ↑G) (n : ℤ), (
AddCommGrpCat.Hom.hom (AddCommGrpCat.asHom g)) n = n • g
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `CategoryTheory.congr_fun`：∀ {C : Type u_1} [inst : CategoryTheory.Catego
ry.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C → Type w
)} [inst_1 : o…
-/
theorem asHom_injective {G : AddCommGrpCat.{0}} : Function.Injective (@asHom G) := fun h k w => by
  simpa using CategoryTheory.congr_fun w 1

@[ext]
/-
**AddCommGrpCat.int_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat`。
形式化陈述：int_hom_ext {G : AddCommGrpCat.{0}} (f g : AddCommGrpCat.of Int ⟶ G) (w : 
f (1 : Int) = g (1 : Int)) : f = g
参数：f g : AddCommGrpCat.of Int ⟶ G；w : f (1 : Int) = g (1 : Int)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGrpCat.hom_ext`：∀ {X Y : AddCommGrpCat} {f g : X ⟶ Y}, AddCommGrp
Cat.Hom.hom f = AddCommGrpCat.Hom.hom g → f = g
· 使用定理 `AddMonoidHom.ext_int`：ext_int [AddMonoid A] {f g : Int ->+ A} (h1 : f 1 
= g 1) : f = g
-/
theorem int_hom_ext {G : AddCommGrpCat.{0}} (f g : AddCommGrpCat.of ℤ ⟶ G)
    (w : f (1 : ℤ) = g (1 : ℤ)) : f = g :=
  hom_ext (AddMonoidHom.ext_int w)

-- TODO: this argument should be generalised to the situation where
-- the forgetful functor is representable.
/-
**AddCommGrpCat.injective_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat`。
形式化陈述：injective_of_mono {G H : AddCommGrpCat.{0}} (f : G ⟶ H) [Mono f] : Functio
n.Injective f
参数：f : G ⟶ H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGrpCat.int_hom_ext`：int_hom_ext {G : AddCommGrpCat.{0}} (f g : Ad
dCommGrpCat.of Int ⟶ G) (w : f (1 : Int) = g (1 : Int)) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGrpCat.asHom_hom_apply`：∀ {G : AddCommGrpCat} (g : ↑G) (n : ℤ), (
AddCommGrpCat.Hom.hom (AddCommGrpCat.asHom g)) n = n • g
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AddCommGrpCat.asHom_injective`：asHom_injective {G : AddCommGrpCat.{0}} :
 Function.Injective (@asHom G)
-/
theorem injective_of_mono {G H : AddCommGrpCat.{0}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  fun g₁ g₂ h => by
  have t0 : asHom g₁ ≫ f = asHom g₂ ≫ f := by cat_disch
  have t1 : asHom g₁ = asHom g₂ := (cancel_mono _).1 t0
  apply asHom_injective t1

end AddCommGrpCat

/-- Build an isomorphism in the category `GrpCat` from a `MulEquiv` between `Group`s. -/
@[to_additive (attr := simps)]
/-
**MulEquiv.toGrpIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.toGrpIso {X Y : GrpCat} (e : X ≃* Y) : X ≅ Y where hom
参数：e : X ≃* Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an isomorphism in the category `GrpCat` from a `MulEquiv` between `Group`s
.
-/
def MulEquiv.toGrpIso {X Y : GrpCat} (e : X ≃* Y) : X ≅ Y where
  hom := GrpCat.ofHom e.toMonoidHom
  inv := GrpCat.ofHom e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddGrpCat` from an `AddEquiv` between `AddGroup`s. -/
add_decl_doc AddEquiv.toAddGrpIso

/-- Build an isomorphism in the category `CommGrpCat` from a `MulEquiv`
between `CommGroup`s. -/
@[to_additive (attr := simps)]
/-
**MulEquiv.toCommGrpIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.toCommGrpIso {X Y : CommGrpCat} (e : X ≃* Y) : X ≅ Y where hom
参数：e : X ≃* Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an isomorphism in the category `CommGrpCat` from a `MulEquiv`
between `CommGroup`s.
-/
def MulEquiv.toCommGrpIso {X Y : CommGrpCat} (e : X ≃* Y) : X ≅ Y where
  hom := CommGrpCat.ofHom e.toMonoidHom
  inv := CommGrpCat.ofHom e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddCommGrpCat` from an `AddEquiv`
between `AddCommGroup`s. -/
add_decl_doc AddEquiv.toAddCommGrpIso

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `GrpCat`. -/
@[to_additive (attr := simp)]
/-
**CategoryTheory.Iso.groupIsoToMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Iso`。
形式化陈述：groupIsoToMulEquiv {X Y : GrpCat} (i : X ≅ Y) : X ≃* Y
参数：i : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `MulEquiv` from an isomorphism in the category `GrpCat`.
-/
def groupIsoToMulEquiv {X Y : GrpCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

/-- Build an `addEquiv` from an isomorphism in the category `AddGrpCat` -/
add_decl_doc addGroupIsoToAddEquiv

/-- Build a `MulEquiv` from an isomorphism in the category `CommGrpCat`. -/
@[to_additive (attr := simps!)]
/-
**CategoryTheory.Iso.commGroupIsoToMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Iso`。
形式化陈述：commGroupIsoToMulEquiv {X Y : CommGrpCat} (i : X ≅ Y) : X ≃* Y
参数：i : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `MulEquiv` from an isomorphism in the category `CommGrpCat`.
-/
def commGroupIsoToMulEquiv {X Y : CommGrpCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

/-- Build an `AddEquiv` from an isomorphism in the category `AddCommGrpCat`. -/
add_decl_doc addCommGroupIsoToAddEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `Group`s are the same as (isomorphic to) isomorphisms
in `GrpCat` -/
@[to_additive]
/-
**mulEquivIsoGroupIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulEquivIsoGroupIso {X Y : GrpCat.{u}} : (X ≃* Y) ≅ (X ≅ Y) where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
multiplicative equivalences between `Group`s are the same as (isomorphic to) iso
morphisms
in `GrpCat`
-/
def mulEquivIsoGroupIso {X Y : GrpCat.{u}} : (X ≃* Y) ≅ (X ≅ Y) where
  hom := ↾fun e ↦ e.toGrpIso
  inv := ↾fun i ↦ i.groupIsoToMulEquiv

/-- Additive equivalences between `AddGroup`s are the same
as (isomorphic to) isomorphisms in `AddGrpCat`. -/
add_decl_doc addEquivIsoAddGroupIso

/-- Multiplicative equivalences between `CommGroup`s are the same as (isomorphic to) isomorphisms
in `CommGrpCat`. -/
@[to_additive]
/-
**mulEquivIsoCommGroupIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulEquivIsoCommGroupIso {X Y : CommGrpCat.{u}} : (X ≃* Y) ≅ (X ≅ Y) where 
hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplicative equivalences between `CommGroup`s are the same as (isomorphic to)
 isomorphisms
in `CommGrpCat`.
-/
def mulEquivIsoCommGroupIso {X Y : CommGrpCat.{u}} : (X ≃* Y) ≅ (X ≅ Y) where
  hom := ↾fun e ↦ e.toCommGrpIso
  inv := ↾fun i ↦ i.commGroupIsoToMulEquiv

/-- Additive equivalences between `AddCommGroup`s are
the same as (isomorphic to) isomorphisms in `AddCommGrpCat`. -/
add_decl_doc addEquivIsoAddCommGroupIso

namespace CategoryTheory.Aut

/-- The (bundled) group of automorphisms of a type is isomorphic to the (bundled) group
of permutations. -/
/-
**CategoryTheory.Aut.isoPerm** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Aut`。
形式化陈述：isoPerm {α : Type u} : GrpCat.of (Aut α) ≅ GrpCat.of (Equiv.Perm α) where 
hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (bundled) group of automorphisms of a type is isomorphic to the (bundled) gr
oup
of permutations.
-/
def isoPerm {α : Type u} : GrpCat.of (Aut α) ≅ GrpCat.of (Equiv.Perm α) where
  hom := GrpCat.ofHom
    { toFun := fun g => g.toEquiv
      map_one' := by aesop
      map_mul' := by aesop }
  inv := GrpCat.ofHom
    { toFun := fun g => g.toIso
      map_one' := by aesop
      map_mul' := by aesop }

/-- The (unbundled) group of automorphisms of a type is `MulEquiv` to the (unbundled) group
of permutations. -/
/-
**CategoryTheory.Aut.mulEquivPerm** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Aut`
。
形式化陈述：mulEquivPerm {α : Type u} : Aut α ≃* Equiv.Perm α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (unbundled) group of automorphisms of a type is `MulEquiv` to the (unbundled
) group
of permutations.
-/
def mulEquivPerm {α : Type u} : Aut α ≃* Equiv.Perm α :=
  isoPerm.groupIsoToMulEquiv

end CategoryTheory.Aut

@[to_additive]
/-
**GrpCat.forget_reflects_isos** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：GrpCat.forget_reflects_isos : (forget GrpCat.{u}).ReflectsIsomorphisms whe
re reflects {X Y} f _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance GrpCat.forget_reflects_isos : (forget GrpCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget GrpCat).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := by simp [Iso.toEquiv, i] }
    exact e.toGrpIso.isIso_hom

@[to_additive]
/-
**CommGrpCat.forget_reflects_isos** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CommGrpCat.forget_reflects_isos : (forget CommGrpCat.{u}).ReflectsIsomorph
isms where reflects {X Y} f _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance CommGrpCat.forget_reflects_isos : (forget CommGrpCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommGrpCat).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := by simp [Iso.toEquiv, i] }
    exact e.toCommGrpIso.isIso_hom

-- note: in the following definitions, there is a problem with `@[to_additive]`
-- as the `Category` instance is not found on the additive variant
-- this variant is then renamed with an `Aux` suffix
set_option linter.checkUnivs false in
/-- An alias for `GrpCat.{max u v}`, to deal around unification issues. -/
@[to_additive GrpMaxAux
  /-- An alias for `AddGrpCat.{max u v}`, to deal around unification issues. -/]
/-
**GrpMax.** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev GrpMax.{u1, u2} := GrpCat.{max u1 u2}

set_option linter.checkUnivs false in
/-- An alias for `AddGrpCat.{max u v}`, to deal around unification issues. -/
/-
**AddGrpMax.** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alias for `AddGrpCat.{max u v}`, to deal around unification issues.
-/
abbrev AddGrpMax.{u1, u2} := AddGrpCat.{max u1 u2}

set_option linter.checkUnivs false in
/-- An alias for `CommGrpCat.{max u v}`, to deal around unification issues. -/
@[to_additive AddCommGrpMaxAux
  /-- An alias for `AddCommGrpCat.{max u v}`, to deal around unification issues. -/]
/-
**CommGrpMax.** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev CommGrpMax.{u1, u2} := CommGrpCat.{max u1 u2}

set_option linter.checkUnivs false in
/-- An alias for `AddCommGrpCat.{max u v}`, to deal around unification issues. -/
/-
**AddCommGrpMax.** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alias for `AddCommGrpCat.{max u v}`, to deal around unification issues.
-/
abbrev AddCommGrpMax.{u1, u2} := AddCommGrpCat.{max u1 u2}
