/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.Logic.Equiv.Defs

/-!
# Full and faithful functors

We define typeclasses `Full` and `Faithful`, decorating functors. These typeclasses
carry no data. However, we also introduce a structure `Functor.FullyFaithful` which
contains the data of the inverse map `(F.obj X ⟶ F.obj Y) ⟶ (X ⟶ Y)` of the
map induced on morphisms by a functor `F`.

## Main definitions and results
* Use `F.map_injective` to retrieve the fact that `F.map` is injective when `[Faithful F]`.
* Similarly, `F.map_surjective` states that `F.map` is surjective when `[Full F]`.
* Use `F.preimage` to obtain preimages of morphisms when `[Full F]`.
* We prove some basic "cancellation" lemmas for full and/or faithful functors, as well as a
  construction for "dividing" a functor by a faithful functor, see `Faithful.div`.

See `CategoryTheory.Equivalence.of_fullyFaithful_ess_surj` for the fact that a functor is an
equivalence if and only if it is fully faithful and essentially surjective.

-/

@[expose] public section


-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type*} [Category* E]

namespace Functor

/-- A functor `F : C ⥤ D` is full if for each `X Y : C`, `F.map` is surjective. -/
@[stacks 001C]
/-
**CategoryTheory.Functor.Full** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：Full (F : C ⥤ D) : Prop where map_surjective {X Y : C} : Function.Surjecti
ve (F.map (X
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` is full if for each `X Y : C`, `F.map` is surjective.
-/
class Full (F : C ⥤ D) : Prop where
  map_surjective {X Y : C} : Function.Surjective (F.map (X := X) (Y := Y))

attribute [to_dual self] Full.map_surjective Full.mk

/-- A functor `F : C ⥤ D` is faithful if for each `X Y : C`, `F.map` is injective. -/
@[stacks 001C]
/-
**CategoryTheory.Functor.Faithful** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：Faithful (F : C ⥤ D) : Prop where /-- `F.map` is injective for each `X Y :
 C`. -/ map_injective : forall {X Y : C}, Function.Injective (F.map : (X ⟶ Y) ->
 (F.obj X ⟶ F.obj Y))
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` is faithful if for each `X Y : C`, `F.map` is injective.
-/
class Faithful (F : C ⥤ D) : Prop where
  /-- `F.map` is injective for each `X Y : C`. -/
  map_injective : ∀ {X Y : C}, Function.Injective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
    cat_disch

attribute [to_dual self] Faithful.map_injective Faithful.mk

variable {X Y : C}

@[grind inj, to_dual self]
/-
**CategoryTheory.Functor.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：map_injective (F : C ⥤ D) [Faithful F] : Function.Injective (F.map : (X ⟶ 
Y) -> (F.obj X ⟶ F.obj Y))
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Faithful.map_injective`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
-/
theorem map_injective (F : C ⥤ D) [Faithful F] :
    Function.Injective <| (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  Faithful.map_injective
/-
**CategoryTheory.Functor.map_injective_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：map_injective_iff (F : C ⥤ D) [Faithful F] {X Y : C} (f g : X ⟶ Y) : F.map
 f = F.map g ↔ f = g
参数：F : C ⥤ D；f g : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma map_injective_iff (F : C ⥤ D) [Faithful F] {X Y : C} (f g : X ⟶ Y) :
    F.map f = F.map g ↔ f = g :=
  ⟨fun h => F.map_injective h, fun h => by rw [h]⟩
/-
**CategoryTheory.Functor.mapIso_injective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：mapIso_injective (F : C ⥤ D) [Faithful F] : Function.Injective (F.mapIso :
 (X ≅ Y) -> (F.obj X ≅ F.obj Y))
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem mapIso_injective (F : C ⥤ D) [Faithful F] :
    Function.Injective <| (F.mapIso : (X ≅ Y) → (F.obj X ≅ F.obj Y)) := fun _ _ h =>
  Iso.ext (map_injective F (congr_arg Iso.hom h :))
/-
**CategoryTheory.Functor.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：map_surjective (F : C ⥤ D) [Full F] : Function.Surjective (F.map : (X ⟶ Y)
 -> (F.obj X ⟶ F.obj Y))
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Full.map_surjective`：∀ {C : Type u₁} {inst : Cate
goryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.
{v₂, u₂} D}   {F : CategoryTheor…
-/
theorem map_surjective (F : C ⥤ D) [Full F] :
    Function.Surjective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  Full.map_surjective

/-- The choice of a preimage of a morphism under a full functor. -/
@[to_dual self]
/-
**CategoryTheory.Functor.preimage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：preimage (F : C ⥤ D) [Full F] (f : F.obj X ⟶ F.obj Y) : X ⟶ Y
参数：F : C ⥤ D；f : F.obj X ⟶ F.obj Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))

--- 原说明 ---
The choice of a preimage of a morphism under a full functor.
-/
noncomputable def preimage (F : C ⥤ D) [Full F] (f : F.obj X ⟶ F.obj Y) : X ⟶ Y :=
  (F.map_surjective f).choose

-- TODO: `to_dual` should deal with this automatically:
attribute [to_dual self] preimage.congr_simp

@[simp, to_dual self]
/-
**CategoryTheory.Functor.map_preimage** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：map_preimage (F : C ⥤ D) [Full F] {X Y : C} (f : F.obj X ⟶ F.obj Y) : F.ma
p (preimage F f) = f
参数：F : C ⥤ D；f : F.obj X ⟶ F.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
-/
theorem map_preimage (F : C ⥤ D) [Full F] {X Y : C} (f : F.obj X ⟶ F.obj Y) :
    F.map (preimage F f) = f :=
  (F.map_surjective f).choose_spec

variable {F : C ⥤ D} {X Y Z : C}

section
variable [Full F] [F.Faithful]

@[simp]
/-
**CategoryTheory.Functor.preimage_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：preimage_id : F.preimage (𝟙 (F.obj X)) = 𝟙 X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_id : F.preimage (𝟙 (F.obj X)) = 𝟙 X :=
  F.map_injective (by simp)

@[simp, to_dual self]
/-
**CategoryTheory.Functor.preimage_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：preimage_comp (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) : F.preimage
 (f ≫ g) = F.preimage f ≫ F.preimage g
参数：f : F.obj X ⟶ F.obj Y；g : F.obj Y ⟶ F.obj Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_comp (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) :
    F.preimage (f ≫ g) = F.preimage f ≫ F.preimage g :=
  F.map_injective (by simp)

@[simp, to_dual self]
/-
**CategoryTheory.Functor.preimage_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：preimage_map (f : X ⟶ Y) : F.preimage (F.map f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_map (f : X ⟶ Y) : F.preimage (F.map f) = f :=
  F.map_injective (by simp)

variable (F)

/-- If `F : C ⥤ D` is fully faithful, every isomorphism `F.obj X ≅ F.obj Y` has a preimage. -/
@[simps]
/-
**CategoryTheory.Functor.preimageIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：preimageIso (f : F.obj X ≅ F.obj Y) : X ≅ Y where hom
参数：f : F.obj X ≅ F.obj Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` is fully faithful, every isomorphism `F.obj X ≅ F.obj Y` has a pr
eimage.
-/
noncomputable def preimageIso (f : F.obj X ≅ F.obj Y) :
    X ≅ Y where
  hom := F.preimage f.hom
  inv := F.preimage f.inv
  hom_inv_id := F.map_injective (by simp)
  inv_hom_id := F.map_injective (by simp)

@[simp]
/-
**CategoryTheory.Functor.preimageIso_mapIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：preimageIso_mapIso (f : X ≅ Y) : F.preimageIso (F.mapIso f) = f
参数：f : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.preimageIso_hom`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.preimage_map`：preimage_map (f : X ⟶ Y) : F.preima
ge (F.map f) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimageIso_mapIso (f : X ≅ Y) : F.preimageIso (F.mapIso f) = f := by
  ext
  simp

end

variable (F) in
/-- Structure containing the data of inverse map `(F.obj X ⟶ F.obj Y) ⟶ (X ⟶ Y)` of `F.map`
in order to express that `F` is a fully faithful functor. -/
/-
**CategoryTheory.Functor.FullyFaithful** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：FullyFaithful where /-- The inverse map `(F.obj X ⟶ F.obj Y) ⟶ (X ⟶ Y)` of
 `F.map`. -/ preimage {X Y : C} (f : F.obj X ⟶ F.obj Y) : X ⟶ Y map_preimage {X 
Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage f) = f
参数：F.obj X ⟶ F.obj Y；X ⟶ Y；f : F.obj X ⟶ F.obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure containing the data of inverse map `(F.obj X ⟶ F.obj Y) ⟶ (X ⟶ Y)` of 
`F.map`
in order to express that `F` is a fully faithful functor.
-/
structure FullyFaithful where
  /-- The inverse map `(F.obj X ⟶ F.obj Y) ⟶ (X ⟶ Y)` of `F.map`. -/
  preimage {X Y : C} (f : F.obj X ⟶ F.obj Y) : X ⟶ Y
  map_preimage {X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage f) = f := by cat_disch
  preimage_map {X Y : C} (f : X ⟶ Y) : preimage (F.map f) = f := by cat_disch

namespace FullyFaithful

attribute [simp] map_preimage preimage_map

variable (F) in
/-- A `FullyFaithful` structure can be obtained from the assumption the `F` is both
full and faithful. -/
/-
**CategoryTheory.Functor.FullyFaithful.ofFullyFaithful** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor.FullyFaithful`。
形式化陈述：ofFullyFaithful [F.Full] [F.Faithful] : F.FullyFaithful where preimage
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FullyFaithful` structure can be obtained from the assumption the `F` is both
full and faithful.
-/
noncomputable def ofFullyFaithful [F.Full] [F.Faithful] :
    F.FullyFaithful where
  preimage := F.preimage

variable (C) in
/-- The identity functor is fully faithful. -/
@[simps]
/-
**CategoryTheory.Functor.FullyFaithful.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor.FullyFaithful`。
形式化陈述：id : (𝟭 C).FullyFaithful where preimage f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity functor is fully faithful.
-/
def id : (𝟭 C).FullyFaithful where
  preimage f := f

section
variable (hF : F.FullyFaithful)

include hF

/-- The equivalence `(X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y)` given by `h : F.FullyFaithful`. -/
@[simps]
/-
**CategoryTheory.Functor.FullyFaithful.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor.FullyFaithful`。
形式化陈述：homEquiv {X Y : C} : (X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `(X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y)` given by `h : F.FullyFaithful`.
-/
def homEquiv {X Y : C} : (X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  invFun := hF.preimage
  left_inv _ := by simp
  right_inv _ := by simp
/-
**CategoryTheory.Functor.FullyFaithful.map_injective** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor.FullyFaithful`。
形式化陈述：map_injective {X Y : C} {f g : X ⟶ Y} (h : F.map f = F.map g) : f = g
参数：h : F.map f = F.map g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma map_injective {X Y : C} {f g : X ⟶ Y} (h : F.map f = F.map g) : f = g :=
  hF.homEquiv.injective h
/-
**CategoryTheory.Functor.FullyFaithful.map_surjective** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor.FullyFaithful`。
形式化陈述：map_surjective {X Y : C} : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj 
X ⟶ F.obj Y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
lemma map_surjective {X Y : C} :
    Function.Surjective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  hF.homEquiv.surjective
/-
**CategoryTheory.Functor.FullyFaithful.map_bijective** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor.FullyFaithful`。
形式化陈述：map_bijective (X Y : C) : Function.Bijective (F.map : (X ⟶ Y) -> (F.obj X 
⟶ F.obj Y))
参数：X Y : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
lemma map_bijective (X Y : C) :
    Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  hF.homEquiv.bijective

@[simp]
/-
**CategoryTheory.Functor.FullyFaithful.preimage_id** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor.FullyFaithful`。
形式化陈述：preimage_id {X : C} : hF.preimage (𝟙 (F.obj X)) = 𝟙 X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.map_injective`：map_injective {X Y :
 C} {f g : X ⟶ Y} (h : F.map f = F.map g) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_id {X : C} :
    hF.preimage (𝟙 (F.obj X)) = 𝟙 X :=
  hF.map_injective (by simp)

@[simp, reassoc]
/-
**CategoryTheory.Functor.FullyFaithful.preimage_comp** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor.FullyFaithful`。
形式化陈述：preimage_comp {X Y Z : C} (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) 
: hF.preimage (f ≫ g) = hF.preimage f ≫ hF.preimage g
参数：f : F.obj X ⟶ F.obj Y；g : F.obj Y ⟶ F.obj Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.map_injective`：map_injective {X Y :
 C} {f g : X ⟶ Y} (h : F.map f = F.map g) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_comp {X Y Z : C} (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) :
    hF.preimage (f ≫ g) = hF.preimage f ≫ hF.preimage g :=
  hF.map_injective (by simp)
/-
**CategoryTheory.Functor.FullyFaithful.full** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Functor.FullyFaithful`。
形式化陈述：full : F.Full where map_surjective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.map_surjective`：map_surjective {X Y
 : C} : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
-/
lemma full : F.Full where
  map_surjective := hF.map_surjective
/-
**CategoryTheory.Functor.FullyFaithful.faithful** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor.FullyFaithful`。
形式化陈述：faithful : F.Faithful where map_injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.map_injective`：map_injective {X Y :
 C} {f g : X ⟶ Y} (h : F.map f = F.map g) : f = g
-/
lemma faithful : F.Faithful where
  map_injective := hF.map_injective
/-
**CategoryTheory.Functor.FullyFaithful.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Functor.FullyFaithful`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton F.FullyFaithful where
  allEq h₁ h₂ := by
    have := h₁.faithful
    cases h₁ with | mk f₁ hf₁ _ => cases h₂ with | mk f₂ hf₂ _ =>
    simp only [Functor.FullyFaithful.mk.injEq]
    ext
    apply F.map_injective
    rw [hf₁, hf₂]

/-- The unique isomorphism `X ≅ Y` which induces an isomorphism `F.obj X ≅ F.obj Y`
when `hF : F.FullyFaithful`. -/
@[simps]
/-
**CategoryTheory.Functor.FullyFaithful.preimageIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor.FullyFaithful`。
形式化陈述：preimageIso {X Y : C} (e : F.obj X ≅ F.obj Y) : X ≅ Y where hom
参数：e : F.obj X ≅ F.obj Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique isomorphism `X ≅ Y` which induces an isomorphism `F.obj X ≅ F.obj Y`
when `hF : F.FullyFaithful`.
-/
def preimageIso {X Y : C} (e : F.obj X ≅ F.obj Y) : X ≅ Y where
  hom := hF.preimage e.hom
  inv := hF.preimage e.inv
  hom_inv_id := hF.map_injective (by simp)
  inv_hom_id := hF.map_injective (by simp)
/-
**CategoryTheory.Functor.FullyFaithful.isIso_of_isIso_map** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor.FullyFaithful`。
形式化陈述：isIso_of_isIso_map {X Y : C} (f : X ⟶ Y) [IsIso (F.map f)] : IsIso f
参数：f : X ⟶ Y；F.map f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.FullyFaithful.preimageIso_hom`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory
.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.preimage_map`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma isIso_of_isIso_map {X Y : C} (f : X ⟶ Y) [IsIso (F.map f)] :
    IsIso f := by
  simpa using (hF.preimageIso (asIso (F.map f))).isIso_hom

/-- The equivalence `(X ≅ Y) ≃ (F.obj X ≅ F.obj Y)` given by `h : F.FullyFaithful`. -/
@[simps]
/-
**CategoryTheory.Functor.FullyFaithful.isoEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor.FullyFaithful`。
形式化陈述：isoEquiv {X Y : C} : (X ≅ Y) ≃ (F.obj X ≅ F.obj Y) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `(X ≅ Y) ≃ (F.obj X ≅ F.obj Y)` given by `h : F.FullyFaithful`.
-/
def isoEquiv {X Y : C} : (X ≅ Y) ≃ (F.obj X ≅ F.obj Y) where
  toFun := F.mapIso
  invFun := hF.preimageIso
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Fully faithful functors are stable by composition. -/
@[simps]
/-
**CategoryTheory.Functor.FullyFaithful.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor.FullyFaithful`。
形式化陈述：comp {G : D ⥤ E} (hG : G.FullyFaithful) : (F ⋙ G).FullyFaithful where prei
mage f
参数：hG : G.FullyFaithful。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fully faithful functors are stable by composition.
-/
def comp {G : D ⥤ E} (hG : G.FullyFaithful) : (F ⋙ G).FullyFaithful where
  preimage f := hF.preimage (hG.preimage f)

/-- If `F` is fully faithful and `F ≅ G`, then `G` is fully faithful. -/
/-
**CategoryTheory.Functor.FullyFaithful.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Functor.FullyFaithful`。
形式化陈述：ofIso {G : C ⥤ D} (e : F ≅ G) : G.FullyFaithful where preimage f
参数：e : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is fully faithful and `F ≅ G`, then `G` is fully faithful.
-/
def ofIso {G : C ⥤ D} (e : F ≅ G) : G.FullyFaithful where
  preimage f := hF.preimage (e.hom.app _ ≫ f ≫ e.inv.app _)
  map_preimage f := by simp [← NatIso.naturality_1 e]

end

variable (F) in
/-
**CategoryTheory.Functor.FullyFaithful.nonempty_iff_map_bijective** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Functor.FullyFaithful`。
形式化陈述：nonempty_iff_map_bijective : Nonempty F.FullyFaithful ↔ forall (X Y : C), 
Function.Bijective (F.map : (X ⟶ Y) -> _)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.map_bijective`：map_bijective (X Y :
 C) : Function.Bijective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
-/
lemma nonempty_iff_map_bijective :
    Nonempty F.FullyFaithful ↔ ∀ (X Y : C), Function.Bijective (F.map : (X ⟶ Y) → _) :=
  ⟨fun ⟨hF⟩ ↦ hF.map_bijective, fun hF ↦ by
    have : F.Faithful := ⟨fun h ↦ (hF _ _).injective h⟩
    have : F.Full := ⟨(hF _ _).surjective⟩
    exact ⟨.ofFullyFaithful _⟩⟩

/-- If `F ⋙ G` is fully faithful and `G` is faithful, then `F` is fully faithful. -/
/-
**CategoryTheory.Functor.FullyFaithful.ofCompFaithful** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor.FullyFaithful`。
形式化陈述：ofCompFaithful {G : D ⥤ E} [G.Faithful] (hFG : (F ⋙ G).FullyFaithful) : F.
FullyFaithful where preimage f
参数：hFG : (F ⋙ G).FullyFaithful。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F ⋙ G` is fully faithful and `G` is faithful, then `F` is fully faithful.
-/
def ofCompFaithful {G : D ⥤ E} [G.Faithful] (hFG : (F ⋙ G).FullyFaithful) :
    F.FullyFaithful where
  preimage f := hFG.preimage (G.map f)
  map_preimage f := G.map_injective (hFG.map_preimage (G.map f))
  preimage_map f := hFG.preimage_map f

end FullyFaithful

end Functor


section

variable (F : C ⥤ D) [F.Full] [F.Faithful] {X Y : C}

/-- If the image of a morphism under a fully faithful functor in an isomorphism,
then the original morphisms is also an isomorphism.
-/
/-
**CategoryTheory.isIso_of_fully_faithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：isIso_of_fully_faithful (f : X ⟶ Y) [IsIso (F.map f)] : IsIso f
参数：f : X ⟶ Y；F.map f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y

--- 原说明 ---
If the image of a morphism under a fully faithful functor in an isomorphism,
then the original morphisms is also an isomorphism.
-/
theorem isIso_of_fully_faithful (f : X ⟶ Y) [IsIso (F.map f)] : IsIso f :=
  ⟨⟨F.preimage (inv (F.map f)), ⟨F.map_injective (by simp), F.map_injective (by simp)⟩⟩⟩


end

end CategoryTheory

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v₁} C]

/-
**CategoryTheory.Functor.Full.id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Funct
or.Full`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C], (CategoryTheo
ry.Functor.id C).Full
参数：CategoryTheory.Functor.id C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
-/
instance Full.id : Full (𝟭 C) where map_surjective := Function.surjective_id
/-
**CategoryTheory.Functor.Faithful.id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor.Faithful`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C], (CategoryTheo
ry.Functor.id C).Faithful
参数：CategoryTheory.Functor.id C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Faithful.id : Functor.Faithful (𝟭 C) := { }

variable {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
variable (F F' : C ⥤ D) (G : D ⥤ E)
/-
**CategoryTheory.Functor.Faithful.comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Functor.Faithful`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] (F : CategoryTheory.Functor C D)   (G : CategoryTheo
ry.Functor D E) [F.Faithful] [G.Faithful], (F.comp G).Faithful
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
-/
instance Faithful.comp [F.Faithful] [G.Faithful] : (F ⋙ G).Faithful where
  map_injective p := F.map_injective (G.map_injective p)
/-
**CategoryTheory.Functor.Faithful.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor.Faithful`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] (F : CategoryTheory.Functor C D)   (G : CategoryTheo
ry.Functor D E) [(F.comp G).Faithful], F.Faithful
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
-/
theorem Faithful.of_comp [(F ⋙ G).Faithful] : F.Faithful :=
  -- Porting note: (F ⋙ G).map_injective.of_comp has the incorrect type
  { map_injective := fun {_ _} => Function.Injective.of_comp (F ⋙ G).map_injective }
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [Quiver.IsThin C] : F.Faithful where

section

variable {F F'}

/-- If `F` is full, and naturally isomorphic to some `F'`, then `F'` is also full. -/
/-
**CategoryTheory.Functor.Full.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor.Full`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F F' : CategoryTheory.Functor C
 D} [F.Full] (α : F ≅ F'), F'.Full
参数：α : F ≅ F'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.naturality_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `F` is full, and naturally isomorphic to some `F'`, then `F'` is also full.
-/
lemma Full.of_iso [Full F] (α : F ≅ F') : Full F' where
  map_surjective {X Y} f :=
    ⟨F.preimage ((α.app X).hom ≫ f ≫ (α.app Y).inv), by simp [← NatIso.naturality_1 α]⟩
/-
**CategoryTheory.Functor.Faithful.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor.Faithful`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F F' : CategoryTheory.Functor C
 D} [F.Faithful] (α : F ≅ F'), F'.Faithful
参数：α : F ≅ F'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.naturality_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem Faithful.of_iso [F.Faithful] (α : F ≅ F') : F'.Faithful :=
  { map_injective := fun h =>
      F.map_injective (by rw [← NatIso.naturality_1 α.symm, h, NatIso.naturality_1 α.symm]) }

end

variable {F G}

/-
**CategoryTheory.Functor.Faithful.of_comp_iso** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor.Faithful`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] {F : CategoryTheory.Functor C D}   {G : CategoryTheo
ry.Functor D E} {H : CategoryTheory.Functor C E} [H.Faithful] (h : F.comp G ≅ H)
, F.Faithful
参数：h : F.comp G ≅ H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Faithful.of_comp`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.Faithful.of_iso`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {F F' : CategoryTh…
-/
theorem Faithful.of_comp_iso {H : C ⥤ E} [H.Faithful] (h : F ⋙ G ≅ H) : F.Faithful :=
  @Faithful.of_comp _ _ _ _ _ _ F G (Faithful.of_iso h.symm)

alias _root_.CategoryTheory.Iso.faithful_of_comp := Faithful.of_comp_iso

-- We could prove this from `Faithful.of_comp_iso` using `eq_to_iso`,
-- but that would introduce a cyclic import.
/-
**CategoryTheory.Functor.Faithful.of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor.Faithful`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] {F : CategoryTheory.Functor C D}   {G : CategoryTheo
ry.Functor D E} {H : CategoryTheory.Functor C E} [ℋ : H.Faithful], F.comp G = H 
→ F.Faithful
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Faithful.of_comp`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Faithful.of_comp_eq {H : C ⥤ E} [ℋ : H.Faithful] (h : F ⋙ G = H) : F.Faithful :=
  @Faithful.of_comp _ _ _ _ _ _ F G (h.symm ▸ ℋ)

alias _root_.Eq.faithful_of_comp := Faithful.of_comp_eq

variable (F G)
/-- “Divide” a functor by a faithful functor. -/
/-
**CategoryTheory.Functor.Faithful.div** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor.Faithful`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {E : Typ
e u₃} →           [inst_2 : CategoryTheory.Category.{v₃, u₃} E] →             (F
 : CategoryTheory.Functor C E) →               (G : CategoryTheory.Functor D E) 
→                 [G.Faithful] →                   (obj : C → D) →              
       (∀ (X : C), G.obj (obj X) = F.obj X) →                       (map : {X Y 
: C} → (X ⟶ Y) → (obj X ⟶ obj Y)) →                         (∀ {X Y : C} {f : X 
⟶ Y}, G.map (map f) ≍ F.map f) → CategoryTheory.Functor C D
参数：F : CategoryTheory.Functor C E；G : CategoryTheory.Functor D E；obj : C → D；∀ (
X : C), G.obj (obj X) = F.obj X；map : {X Y : C} → (X ⟶ Y) → (obj X ⟶ obj Y)；∀ {X
 Y : C} {f : X ⟶ Y}, G.map (map f) ≍ F.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
“Divide” a functor by a faithful functor.
-/
protected def Faithful.div (F : C ⥤ E) (G : D ⥤ E) [G.Faithful] (obj : C → D)
    (h_obj : ∀ X, G.obj (obj X) = F.obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, G.map (map f) ≍ F.map f) : C ⥤ D :=
  { obj, map := @map,
    map_id := by
      intro X
      apply G.map_injective
      grind
    map_comp := by grind }

-- This follows immediately from `Functor.hext` (`Functor.hext h_obj @h_map`),
-- but importing `CategoryTheory.EqToHom` causes an import loop:
-- CategoryTheory.EqToHom → CategoryTheory.Opposites →
-- CategoryTheory.Equivalence → CategoryTheory.FullyFaithful
/-
**CategoryTheory.Functor.Faithful.div_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor.Faithful`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] (F : CategoryTheory.Functor C E) [F.Faithful]   (G :
 CategoryTheory.Functor D E) [inst_4 : G.Faithful] (obj : C → D) (h_obj : ∀ (X :
 C), G.obj (obj X) = F.obj X)   (map : {X Y : C} → (X ⟶ Y) → (obj X ⟶ obj Y)) (h
_map : ∀ {X Y : C} {f : X ⟶ Y}, G.map (map f) ≍ F.map f),   (CategoryTheory.Func
tor.Faithful.div F G obj h_obj map h_map).comp G = F
参数：F : CategoryTheory.Functor C E；G : CategoryTheory.Functor D E；obj : C → D；h_o
bj : ∀ (X : C), G.obj (obj X) = F.obj X；map : {X Y : C} → (X ⟶ Y) → (obj X ⟶ obj
 Y)；h_map : ∀ {X Y : C} {f : X ⟶ Y}, G.map (map f) ≍ F.map f；CategoryTheory.Func
tor.Faithful.div F G obj h_obj map h_map。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
-/
theorem Faithful.div_comp (F : C ⥤ E) [F.Faithful] (G : D ⥤ E) [G.Faithful] (obj : C → D)
    (h_obj : ∀ X, G.obj (obj X) = F.obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, G.map (map f) ≍ F.map f) :
    Faithful.div F G obj @h_obj @map @h_map ⋙ G = F := by
  obtain ⟨F_obj, _, _, _⟩ := F; obtain ⟨G_obj, _, _, _⟩ := G
  unfold Faithful.div Functor.comp
  have : F_obj = G_obj ∘ obj := (funext h_obj).symm
  subst this
  congr
  simp only [Function.comp_apply, heq_eq_eq] at h_map
  ext
  exact h_map
/-
**CategoryTheory.Functor.Faithful.div_faithful** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor.Faithful`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] (F : CategoryTheory.Functor C E) [F.Faithful]   (G :
 CategoryTheory.Functor D E) [inst_4 : G.Faithful] (obj : C → D) (h_obj : ∀ (X :
 C), G.obj (obj X) = F.obj X)   (map : {X Y : C} → (X ⟶ Y) → (obj X ⟶ obj Y)) (h
_map : ∀ {X Y : C} {f : X ⟶ Y}, G.map (map f) ≍ F.map f),   (CategoryTheory.Func
tor.Faithful.div F G obj h_obj map h_map).Faithful
参数：F : CategoryTheory.Functor C E；G : CategoryTheory.Functor D E；obj : C → D；h_o
bj : ∀ (X : C), G.obj (obj X) = F.obj X；map : {X Y : C} → (X ⟶ Y) → (obj X ⟶ obj
 Y)；h_map : ∀ {X Y : C} {f : X ⟶ Y}, G.map (map f) ≍ F.map f；CategoryTheory.Func
tor.Faithful.div F G obj h_obj map h_map。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.faithful_of_comp`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁
, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type
 u₃} [ins…
· 使用定理 `CategoryTheory.Functor.Faithful.div_comp`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {E : Type u₃} [ins…
-/
theorem Faithful.div_faithful (F : C ⥤ E) [F.Faithful] (G : D ⥤ E) [G.Faithful] (obj : C → D)
    (h_obj : ∀ X, G.obj (obj X) = F.obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, G.map (map f) ≍ F.map f) :
    Functor.Faithful (Faithful.div F G obj @h_obj @map @h_map) :=
  (Faithful.div_comp F G _ h_obj _ @h_map).faithful_of_comp
/-
**CategoryTheory.Functor.Full.comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Fun
ctor.Full`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] (F : CategoryTheory.Functor C D)   (G : CategoryTheo
ry.Functor D E) [F.Full] [G.Full], (F.comp G).Full
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Full.comp [Full F] [Full G] : Full (F ⋙ G) where
  map_surjective f := ⟨F.preimage (G.preimage f), by simp⟩

/-- If `F ⋙ G` is full and `G` is faithful, then `F` is full. -/
/-
**CategoryTheory.Functor.Full.of_comp_faithful** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor.Full`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] (F : CategoryTheory.Functor C D)   (G : CategoryTheo
ry.Functor D E) [(F.comp G).Full] [G.Faithful], F.Full
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f

--- 原说明 ---
If `F ⋙ G` is full and `G` is faithful, then `F` is full.
-/
lemma Full.of_comp_faithful [Full <| F ⋙ G] [G.Faithful] : Full F where
  map_surjective f := ⟨(F ⋙ G).preimage (G.map f), G.map_injective ((F ⋙ G).map_preimage _)⟩

/-- If `F ⋙ G` is full and `G` is faithful, then `F` is full. -/
/-
**CategoryTheory.Functor.Full.of_comp_faithful_iso** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor.Full`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] {F : CategoryTheory.Functor C D}   {G : CategoryTheo
ry.Functor D E} {H : CategoryTheory.Functor C E} [H.Full] [G.Faithful] (h : F.co
mp G ≅ H), F.Full
参数：h : F.comp G ≅ H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Full.of_iso`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F F' : CategoryTh…
· 使用定理 `CategoryTheory.Functor.Full.of_comp_faithful`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {E : Type u₃} [ins…

--- 原说明 ---
If `F ⋙ G` is full and `G` is faithful, then `F` is full.
-/
lemma Full.of_comp_faithful_iso {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [Full H] [G.Faithful]
    (h : F ⋙ G ≅ H) : Full F := by
  have := Full.of_iso h.symm
  exact Full.of_comp_faithful F G

/-- Given a natural isomorphism between `F ⋙ H` and `G ⋙ H` for a fully faithful functor `H`, we
can 'cancel' it to give a natural iso between `F` and `G`.
-/
/-
**CategoryTheory.Functor.fullyFaithfulCancelRight** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：fullyFaithfulCancelRight {F G : C ⥤ D} (H : D ⥤ E) [Full H] [H.Faithful] (
comp_iso : F ⋙ H ≅ G ⋙ H) : F ≅ G
参数：H : D ⥤ E；comp_iso : F ⋙ H ≅ G ⋙ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural isomorphism between `F ⋙ H` and `G ⋙ H` for a fully faithful fun
ctor `H`, we
can 'cancel' it to give a natural iso between `F` and `G`.
-/
noncomputable def fullyFaithfulCancelRight {F G : C ⥤ D} (H : D ⥤ E) [Full H] [H.Faithful]
    (comp_iso : F ⋙ H ≅ G ⋙ H) : F ≅ G :=
  NatIso.ofComponents (fun X => H.preimageIso (comp_iso.app X)) fun f =>
    H.map_injective (by simpa using! comp_iso.hom.naturality f)

@[simp]
/-
**CategoryTheory.Functor.fullyFaithfulCancelRight_hom_app** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：fullyFaithfulCancelRight_hom_app {F G : C ⥤ D} {H : D ⥤ E} [Full H] [H.Fai
thful] (comp_iso : F ⋙ H ≅ G ⋙ H) (X : C) : (fullyFaithfulCancelRight H comp_iso
).hom.app X = H.preimage (comp_iso.hom.app X)
参数：comp_iso : F ⋙ H ≅ G ⋙ H；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fullyFaithfulCancelRight_hom_app {F G : C ⥤ D} {H : D ⥤ E} [Full H] [H.Faithful]
    (comp_iso : F ⋙ H ≅ G ⋙ H) (X : C) :
    (fullyFaithfulCancelRight H comp_iso).hom.app X = H.preimage (comp_iso.hom.app X) :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.fullyFaithfulCancelRight_inv_app** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：fullyFaithfulCancelRight_inv_app {F G : C ⥤ D} {H : D ⥤ E} [Full H] [H.Fai
thful] (comp_iso : F ⋙ H ≅ G ⋙ H) (X : C) : (fullyFaithfulCancelRight H comp_iso
).inv.app X = H.preimage (comp_iso.inv.app X)
参数：comp_iso : F ⋙ H ≅ G ⋙ H；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fullyFaithfulCancelRight_inv_app {F G : C ⥤ D} {H : D ⥤ E} [Full H] [H.Faithful]
    (comp_iso : F ⋙ H ≅ G ⋙ H) (X : C) :
    (fullyFaithfulCancelRight H comp_iso).inv.app X = H.preimage (comp_iso.inv.app X) :=
  rfl

end Functor
end CategoryTheory

