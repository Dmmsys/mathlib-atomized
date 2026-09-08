/-
Copyright (c) 2019 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer, Markus Himmel
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Semi
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# The category of `R`-modules

`ModuleCat.{v} R` is the category of bundled `R`-modules with carrier in the universe `v`. We show
that it is preadditive and show that being an isomorphism, monomorphism and epimorphism is
equivalent to being a linear equivalence, an injective linear map and a surjective linear map,
respectively.

## Implementation details

To construct an object in the category of `R`-modules from a type `M` with an instance of the
`Module` typeclass, write `of R M`. There is a coercion in the other direction.
The roundtrip `↑(of R M)` is definitionally equal to `M` itself (when `M` is a type with `Module`
instance), and so is `of R ↑M` (when `M : ModuleCat R M`).

The morphisms are given their own type, not identified with `LinearMap`.
There is a cast from morphisms in `Module R` to linear maps, written `f.hom` (`ModuleCat.Hom.hom`).
To go from linear maps to morphisms in `Module R`, use `ModuleCat.ofHom`.

Similarly, given an isomorphism `f : M ≅ N` use `f.toLinearEquiv` and given a linear equiv
`f : M ≃ₗ[R] N`, use `f.toModuleIso`.
-/

@[expose] public section


open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.WalkingParallelPair

universe v u

variable (R : Type u) [Ring R]

/-- The category of R-modules and their morphisms.

Note that in the case of `R = ℤ`, we cannot
impose here that the `ℤ`-multiplication field from the module structure is defeq to the one coming
from the `isAddCommGroup` structure (contrary to what we do for all module structures in
mathlib), which creates some difficulties down the road. -/
/-
**ModuleCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [Ring R] → Type (max u (v + 1))
参数：v + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of R-modules and their morphisms.

Note that in the case of `R = ℤ`, we cannot
impose here that the `ℤ`-multiplication field from the module structure is defeq
 to the one coming
from the `isAddCommGroup` structure (contrary to what we do for all module struc
tures in
mathlib), which creates some difficulties down the road.
-/
structure ModuleCat where
  private mk ::
  /-- the underlying type of an object in `ModuleCat R` -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module R carrier]

initialize_simps_projections ModuleCat (-isModule, -isAddCommGroup)
attribute [instance] ModuleCat.isAddCommGroup
attribute [instance 1100] ModuleCat.isModule

namespace ModuleCat

/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (ModuleCat.{v} R) (Type v) :=
  ⟨ModuleCat.carrier⟩

attribute [coe] ModuleCat.carrier

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `ModuleCat R`. -/
/-
**ModuleCat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `ModuleCat`。
形式化陈述：of (X : Type v) [AddCommGroup X] [Module R X] : ModuleCat.{v} R
参数：X : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object in the category of R-algebras associated to a type equipped with the 
appropriate
typeclasses. This is the preferred way to construct a term of `ModuleCat R`.
-/
abbrev of (X : Type v) [AddCommGroup X] [Module R X] : ModuleCat.{v} R :=
  ⟨X⟩
/-
**ModuleCat.coe_of** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：coe_of (X : Type v) [Ring X] [Module R X] : (of R X : Type v) = X
参数：X : Type v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_of (X : Type v) [Ring X] [Module R X] : (of R X : Type v) = X :=
  rfl

-- Ensure the roundtrips are reducibly defeq (so tactics like `rw` can see through them).
/-
**ModuleCat.** 是 Mathlib 中的一个示例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (X : Type v) [Ring X] [Module R X] : (of R X : Type v) = X := by with_reducible rfl
/-
**ModuleCat.** 是 Mathlib 中的一个示例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (M : ModuleCat.{v} R) : of R M = M := by with_reducible rfl

set_option backward.privateInPublic true in
variable {R} in
/-- The type of morphisms in `ModuleCat R`. -/
@[ext]
/-
**ModuleCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `ModuleCat`。
形式化陈述：{R : Type u} → [inst : Ring R] → ModuleCat R → ModuleCat R → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `ModuleCat R`.
-/
structure Hom (M N : ModuleCat.{v} R) where
  private mk ::
  /-- The underlying linear map. -/
  hom' : M →ₗ[R] N

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**ModuleCat.moduleCategory** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：moduleCategory : Category.{v, max (v + 1) u} (ModuleCat.{v} R) where Hom M
 N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance moduleCategory : Category.{v, max (v + 1) u} (ModuleCat.{v} R) where
  Hom M N := Hom M N
  id _ := ⟨LinearMap.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory (ModuleCat.{v} R) (· →ₗ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

section

variable {R}

/-- Turn a morphism in `ModuleCat` back into a `LinearMap`. -/
/-
**ModuleCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.Hom`。
形式化陈述：{R : Type u} → [inst : Ring R] → {A B : ModuleCat R} → A.Hom B → ↑A →ₗ[R] 
↑B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `ModuleCat` back into a `LinearMap`.
-/
abbrev Hom.hom {A B : ModuleCat.{v} R} (f : Hom A B) :=
  ConcreteCategory.hom (C := ModuleCat R) f

/-- Typecheck a `LinearMap` as a morphism in `ModuleCat`. -/
/-
**ModuleCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `ModuleCat`。
形式化陈述：ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Modul
e R Y] (f : X ->ₗ[R] Y) : of R X ⟶ of R Y
参数：f : X ->ₗ[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `LinearMap` as a morphism in `ModuleCat`.
-/
abbrev ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y) : of R X ⟶ of R Y :=
  ConcreteCategory.ofHom (C := ModuleCat R) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**ModuleCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.Hom.Simps`。
形式化陈述：{R : Type u} → [inst : Ring R] → (A B : ModuleCat R) → A.Hom B → ↑A →ₗ[R] 
↑B
参数：A B : ModuleCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (A B : ModuleCat.{v} R) (f : Hom A B) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/-
**ModuleCat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：hom_id {M : ModuleCat.{v} R} : (𝟙 M : M ⟶ M).hom = LinearMap.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma hom_id {M : ModuleCat.{v} R} : (𝟙 M : M ⟶ M).hom = LinearMap.id := rfl

/- Provided for rewriting. -/
/-
**ModuleCat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：id_apply (M : ModuleCat.{v} R) (x : M) : (𝟙 M : M ⟶ M) x = x
参数：M : ModuleCat.{v} R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (M : ModuleCat.{v} R) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

@[simp]
/-
**ModuleCat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：hom_comp {M N O : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) : (f ≫ g).hom =
 g.hom.comp f.hom
参数：f : M ⟶ N；g : N ⟶ O。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {M N O : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**ModuleCat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：comp_apply {M N O : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) (x : M) : (f 
≫ g) x = g (f x)
参数：f : M ⟶ N；g : N ⟶ O；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {M N O : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) (x : M) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/-
**ModuleCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.Hom.ext`：∀ {R : Type u} {inst : Ring R} {M N : ModuleCat R} {x
 y : M.Hom N}, x.hom' = y.hom' → x = y
-/
lemma hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf
/-
**ModuleCat.hom_bijective** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：hom_bijective {M N : ModuleCat.{v} R} : Function.Bijective (Hom.hom : (M ⟶
 N) -> (M ->ₗ[R] N)) where left f g h
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.Category.ModuleCat.Basic.0.ModuleCat.Hom.mk.inj
Eq`：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R} (hom' hom'_1 : ↑M →ₗ[R] ↑
N),   ({ hom' := hom' } = { hom' := hom'_1 }) = (hom' = hom'_1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma hom_bijective {M N : ModuleCat.{v} R} :
    Function.Bijective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) where
  left f g h := by cases f; cases g; simpa using! h
  right f := ⟨⟨f⟩, rfl⟩

/-- Convenience shortcut for `ModuleCat.hom_bijective.injective`. -/
/-
**ModuleCat.hom_injective** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：hom_injective {M N : ModuleCat.{v} R} : Function.Injective (Hom.hom : (M ⟶
 N) -> (M ->ₗ[R] N))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用引理 `ModuleCat.hom_bijective`：hom_bijective {M N : ModuleCat.{v} R} : Functio
n.Bijective (Hom.hom : (M ⟶ N) -> (M ->ₗ[R] N)) where left f g h

--- 原说明 ---
Convenience shortcut for `ModuleCat.hom_bijective.injective`.
-/
lemma hom_injective {M N : ModuleCat.{v} R} :
    Function.Injective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) :=
  hom_bijective.injective

/-- Convenience shortcut for `ModuleCat.hom_bijective.surjective`. -/
/-
**ModuleCat.hom_surjective** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：hom_surjective {M N : ModuleCat.{v} R} : Function.Surjective (Hom.hom : (M
 ⟶ N) -> (M ->ₗ[R] N))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用引理 `ModuleCat.hom_bijective`：hom_bijective {M N : ModuleCat.{v} R} : Functio
n.Bijective (Hom.hom : (M ⟶ N) -> (M ->ₗ[R] N)) where left f g h

--- 原说明 ---
Convenience shortcut for `ModuleCat.hom_bijective.surjective`.
-/
lemma hom_surjective {M N : ModuleCat.{v} R} :
    Function.Surjective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) :=
  hom_bijective.surjective

@[simp]
/-
**ModuleCat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：hom_ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [M
odule R Y] (f : X ->ₗ[R] Y) : (ofHom f).hom = f
参数：f : X ->ₗ[R] Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] (f : X →ₗ[R] Y) : (ofHom f).hom = f := rfl

@[simp]
/-
**ModuleCat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：ofHom_hom {M N : ModuleCat.{v} R} (f : M ⟶ N) : ofHom (Hom.hom f) = f
参数：f : M ⟶ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**ModuleCat.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：ofHom_id {M : Type v} [AddCommGroup M] [Module R M] : ofHom LinearMap.id =
 𝟙 (of R M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {M : Type v} [AddCommGroup M] [Module R M] : ofHom LinearMap.id = 𝟙 (of R M) := rfl

@[simp]
/-
**ModuleCat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：ofHom_comp {M N O : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGrou
p O] [Module R M] [Module R N] [Module R O] (f : M ->ₗ[R] N) (g : N ->ₗ[R] O) : 
ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] O。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {M N O : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup O] [Module R M]
    [Module R N] [Module R O] (f : M →ₗ[R] N) (g : N →ₗ[R] O) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/- Doesn't need to be `@[simp]` since `simp only` can solve this. -/
/-
**ModuleCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：ofHom_apply {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] 
[Module R N] (f : M ->ₗ[R] N) (x : M) : ofHom f x = f x
参数：f : M ->ₗ[R] N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Doesn't need to be `@[simp]` since `simp only` can solve this.
-/
lemma ofHom_apply {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (x : M) : ofHom f x = f x := rfl
/-
**ModuleCat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：inv_hom_apply {M N : ModuleCat.{v} R} (e : M ≅ N) (x : M) : e.inv (e.hom x
) = x
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
lemma inv_hom_apply {M N : ModuleCat.{v} R} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  simp
/-
**ModuleCat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：hom_inv_apply {M N : ModuleCat.{v} R} (e : M ≅ N) (x : N) : e.hom (e.inv x
) = x
参数：e : M ≅ N；x : N。
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
lemma hom_inv_apply {M N : ModuleCat.{v} R} (e : M ≅ N) (x : N) : e.hom (e.inv x) = x := by
  simp

/-- `ModuleCat.Hom.hom` bundled as an `Equiv`. -/
/-
**ModuleCat.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：homEquiv {M N : ModuleCat.{v} R} : (M ⟶ N) ≃ (M ->ₗ[R] N) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ModuleCat.Hom.hom` bundled as an `Equiv`.
-/
def homEquiv {M N : ModuleCat.{v} R} : (M ⟶ N) ≃ (M →ₗ[R] N) where
  toFun := Hom.hom
  invFun := ofHom

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The categorical equivalence between `ModuleCat` and `SemimoduleCat`.

In the inverse direction, data (such as the negation operation) is created which may lead to
diamonds when applied to semi-modules that already have an existing additive group structure. -/
/-
**ModuleCat.equivalenceSemimoduleCat** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：equivalenceSemimoduleCat : ModuleCat.{v} R ≌ SemimoduleCat.{v} R where fun
ctor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical equivalence between `ModuleCat` and `SemimoduleCat`.

In the inverse direction, data (such as the negation operation) is created which
 may lead to
diamonds when applied to semi-modules that already have an existing additive gro
up structure.
-/
def equivalenceSemimoduleCat : ModuleCat.{v} R ≌ SemimoduleCat.{v} R where
  functor :=
  { obj M := .of R M
    map f := SemimoduleCat.ofHom f.hom' }
  inverse := letI := Module.addCommMonoidToAddCommGroup
  { obj M := of R M
    map {M N} f := ofHom f.hom }
  unitIso := NatIso.ofComponents fun _ ↦ { hom := ⟨.id⟩, inv := ⟨.id⟩ }
  counitIso := NatIso.ofComponents fun _ ↦ { hom := ⟨.id⟩, inv := ⟨.id⟩ }

end

/- Not a `@[simp]` lemma since it will rewrite the (co)domain of maps and cause
definitional equality issues. -/
/-
**ModuleCat.forget_obj** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：forget_obj {M : ModuleCat.{v} R} : (forget (ModuleCat.{v} R)).obj M = M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Not a `@[simp]` lemma since it will rewrite the (co)domain of maps and cause
definitional equality issues.
-/
lemma forget_obj {M : ModuleCat.{v} R} : (forget (ModuleCat.{v} R)).obj M = M := rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-03-02")]
/-
**ModuleCat.forget_map** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：forget_map {M N : ModuleCat.{v} R} (f : M ⟶ N) : (forget (ModuleCat.{v} R)
).map f = (f : _ -> _)
参数：f : M ⟶ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (forget (ModuleCat.{v} R)).map f = (f : _ → _) :=
  rfl
/-
**ModuleCat.hasForgetToAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：hasForgetToAddCommGroup : HasForget₂ (ModuleCat R) AddCommGrpCat where for
get₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToAddCommGroup : HasForget₂ (ModuleCat R) AddCommGrpCat where
  forget₂ :=
    { obj := fun M => AddCommGrpCat.of M
      map := fun f => AddCommGrpCat.ofHom f.hom.toAddMonoidHom }

@[simp]
/-
**ModuleCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_obj (X : ModuleCat R) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj X = AddCommGrpCat.of X :=
  rfl
/-
**ModuleCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_obj_moduleCat_of (X : Type v) [AddCommGroup X] [Module R X] :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj (of R X) = AddCommGrpCat.of X :=
  rfl

@[simp]
/-
**ModuleCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_map (X Y : ModuleCat R) (f : X ⟶ Y) :
    (forget₂ (ModuleCat R) AddCommGrpCat).map f = AddCommGrpCat.ofHom f.hom :=
  rfl
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (ModuleCat R) :=
  ⟨of R PUnit⟩
/-
**ModuleCat.of_coe** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：∀ (R : Type u) [inst : Ring R] (X : ModuleCat R), ModuleCat.of R ↑X = X
参数：R : Type u；X : ModuleCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem of_coe (X : ModuleCat R) : of R X = X := rfl

variable {R}
/-
**ModuleCat.isZero_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：isZero_of_subsingleton (M : ModuleCat R) [Subsingleton M] : IsZero M where
 unique_to X
参数：M : ModuleCat R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isZero_of_subsingleton (M : ModuleCat R) [Subsingleton M] : IsZero M where
  unique_to X := ⟨⟨⟨ofHom (0 : M →ₗ[R] X)⟩, fun f => by
    ext x
    rw [Subsingleton.elim x (0 : M)]
    simp⟩⟩
  unique_from X := ⟨⟨⟨ofHom (0 : X →ₗ[R] M)⟩, fun f => by
    ext x
    subsingleton⟩⟩
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasZeroObject (ModuleCat.{v} R) :=
  ⟨⟨of R PUnit, isZero_of_subsingleton _⟩⟩

end ModuleCat

variable {R}
variable {X₁ X₂ : Type v}

open ModuleCat

/-- Reinterpreting a linear map in the category of `R`-modules -/
scoped[ModuleCat] notation "↟" f:1024 => ModuleCat.ofHom f

section

/-- Build an isomorphism in the category `Module R` from a `LinearEquiv` between `Module`s. -/
@[simps]
/-
**LinearEquiv.toModuleIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearEquiv.toModuleIso {g₁ : AddCommGroup X₁} {g₂ : AddCommGroup X₂} {m₁ 
: Module R X₁} {m₂ : Module R X₂} (e : X₁ ≃ₗ[R] X₂) : ModuleCat.of R X₁ ≅ Module
Cat.of R X₂ where hom
参数：e : X₁ ≃ₗ[R] X₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an isomorphism in the category `Module R` from a `LinearEquiv` between `Mo
dule`s.
-/
def LinearEquiv.toModuleIso {g₁ : AddCommGroup X₁} {g₂ : AddCommGroup X₂} {m₁ : Module R X₁}
    {m₂ : Module R X₂} (e : X₁ ≃ₗ[R] X₂) : ModuleCat.of R X₁ ≅ ModuleCat.of R X₂ where
  hom := ofHom (e : X₁ →ₗ[R] X₂)
  inv := ofHom (e.symm : X₂ →ₗ[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv

namespace CategoryTheory.Iso
variable {X Y : ModuleCat R}

/-- Build a `LinearEquiv` from an isomorphism in the category `ModuleCat R`. -/
/-
**CategoryTheory.Iso.toLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso
`。
形式化陈述：toLinearEquiv (i : X ≅ Y) : X ≃ₗ[R] Y
参数：i : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `LinearEquiv` from an isomorphism in the category `ModuleCat R`.
-/
def toLinearEquiv (i : X ≅ Y) : X ≃ₗ[R] Y :=
  .ofLinearMap i.hom.hom i.inv.hom (by aesop) (by aesop)
/-
**CategoryTheory.Iso.toLinearEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Iso`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {X Y : ModuleCat R} (i : X ≅ Y) (x : ↑X),  
 i.toLinearEquiv x = (CategoryTheory.ConcreteCategory.hom i.hom) x
参数：i : X ≅ Y；x : ↑X；CategoryTheory.ConcreteCategory.hom i.hom。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearEquiv_apply (i : X ≅ Y) (x : X) : i.toLinearEquiv x = i.hom x := rfl
/-
**CategoryTheory.Iso.toLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Iso`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {X Y : ModuleCat R} (i : X ≅ Y), i.toLinear
Equiv.symm = i.symm.toLinearEquiv
参数：i : X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearEquiv_symm (i : X ≅ Y) : i.toLinearEquiv.symm = i.symm.toLinearEquiv := rfl
/-
**CategoryTheory.Iso.toLinearMap_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Iso`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {X Y : ModuleCat R} (i : X ≅ Y), ↑i.toLinea
rEquiv = ModuleCat.Hom.hom i.hom
参数：i : X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap_toLinearEquiv (i : X ≅ Y) : i.toLinearEquiv = i.hom.hom := rfl

end CategoryTheory.Iso

/-- linear equivalences between `Module`s are the same as (isomorphic to) isomorphisms
in `ModuleCat` -/
@[simps]
/-
**linearEquivIsoModuleIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：linearEquivIsoModuleIso {X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [
Module R X] [Module R Y] : (X ≃ₗ[R] Y) ≅ (ModuleCat.of R X ≅ ModuleCat.of R Y) w
here hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
linear equivalences between `Module`s are the same as (isomorphic to) isomorphis
ms
in `ModuleCat`
-/
def linearEquivIsoModuleIso {X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Module R X]
    [Module R Y] : (X ≃ₗ[R] Y) ≅ (ModuleCat.of R X ≅ ModuleCat.of R Y) where
  hom := ↾fun e ↦ e.toModuleIso
  inv := ↾fun i ↦ i.toLinearEquiv

end

namespace ModuleCat

section AddCommGroup

variable {M N : ModuleCat.{v} R}

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (M ⟶ N) where
  add f g := ⟨f.hom + g.hom⟩
/-
**ModuleCat.hom_add** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R} (f g : M ⟶ N),   Module
Cat.Hom.hom (f + g) = ModuleCat.Hom.hom f + ModuleCat.Hom.hom g
参数：f g : M ⟶ N；f + g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (M ⟶ N) where
  zero := ⟨0⟩
/-
**ModuleCat.hom_zero** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R}, ModuleCat.Hom.hom 0 = 
0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_zero : (0 : M ⟶ N).hom = 0 := rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℕ (M ⟶ N) where
  smul n f := ⟨n • f.hom⟩
/-
**ModuleCat.hom_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R} (n : ℕ) (f : M ⟶ N),   
ModuleCat.Hom.hom (n • f) = n • ModuleCat.Hom.hom f
参数：n : ℕ；f : M ⟶ N；n • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_nsmul (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (M ⟶ N) where
  neg f := ⟨-f.hom⟩
/-
**ModuleCat.hom_neg** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R} (f : M ⟶ N), ModuleCat.
Hom.hom (-f) = -ModuleCat.Hom.hom f
参数：f : M ⟶ N；-f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_neg (f : M ⟶ N) : (-f).hom = -f.hom := rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (M ⟶ N) where
  sub f g := ⟨f.hom - g.hom⟩
/-
**ModuleCat.hom_sub** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R} (f g : M ⟶ N),   Module
Cat.Hom.hom (f - g) = ModuleCat.Hom.hom f - ModuleCat.Hom.hom g
参数：f g : M ⟶ N；f - g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_sub (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom := rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℤ (M ⟶ N) where
  smul n f := ⟨n • f.hom⟩
/-
**ModuleCat.hom_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R} (n : ℤ) (f : M ⟶ N),   
ModuleCat.Hom.hom (n • f) = n • ModuleCat.Hom.hom f
参数：n : ℤ；f : M ⟶ N；n • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_zsmul (n : ℤ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup (Hom.hom) hom_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
/-
**ModuleCat.hom_sum** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R} {ι : Type u_1} (f : ι →
 (M ⟶ N)) (s : Finset ι),   ModuleCat.Hom.hom (∑ i ∈ s, f i) = ∑ i ∈ s, ModuleCa
t.Hom.hom (f i)
参数：f : ι → (M ⟶ N)；s : Finset ι；∑ i ∈ s, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `ModuleCat.hom_zero`：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R}, 
ModuleCat.Hom.hom 0 = 0
· 使用定理 `ModuleCat.hom_add`：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R} (f
 g : M ⟶ N),   ModuleCat.Hom.hom (f + g) = ModuleCat.Hom.hom f + ModuleCat.Hom.h
om g
-/
@[simp] lemma hom_sum {ι : Type*} (f : ι → (M ⟶ N)) (s : Finset ι) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom :=
  map_sum ({ toFun := ModuleCat.Hom.hom, map_zero' := ModuleCat.hom_zero, map_add' := hom_add } :
    (M ⟶ N) →+ (M →ₗ[R] N)) _ _
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive (ModuleCat.{v} R) where
/-
**ModuleCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂_addCommGrp_additive :
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat).Additive where

/-- `ModuleCat.Hom.hom` bundled as an additive equivalence. -/
@[simps!]
/-
**ModuleCat.homAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：homAddEquiv : (M ⟶ N) ≃+ (M ->ₗ[R] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ModuleCat.Hom.hom` bundled as an additive equivalence.
-/
def homAddEquiv : (M ⟶ N) ≃+ (M →ₗ[R] N) :=
  { homEquiv with
    map_add' := fun _ _ => rfl }
/-
**ModuleCat.subsingleton_of_isZero** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：subsingleton_of_isZero (h : IsZero M) : Subsingleton M
参数：h : IsZero M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_forall_eq`：∀ {α : Sort u_1} (x : α), (∀ (y : α), y = x) 
→ Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.id_apply`：id_apply (x : M) : @id R M _ _ _ x = x
· 使用引理 `ModuleCat.hom_id`：hom_id {M : ModuleCat.{v} R} : (𝟙 M : M ⟶ M).hom = Lin
earMap.id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subsingleton_of_isZero (h : IsZero M) : Subsingleton M := by
  refine subsingleton_of_forall_eq 0 (fun x ↦ ?_)
  rw [← LinearMap.id_apply (R := R) x, ← ModuleCat.hom_id]
  simp only [(CategoryTheory.Limits.IsZero.iff_id_eq_zero M).mp h, hom_zero, LinearMap.zero_apply]
/-
**ModuleCat.isZero_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：isZero_iff_subsingleton : IsZero M ↔ Subsingleton M where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.subsingleton_of_isZero`：subsingleton_of_isZero (h : IsZero M) 
: Subsingleton M
· 使用定理 `ModuleCat.isZero_of_subsingleton`：isZero_of_subsingleton (M : ModuleCat 
R) [Subsingleton M] : IsZero M where unique_to X
-/
lemma isZero_iff_subsingleton : IsZero M ↔ Subsingleton M where
  mp := subsingleton_of_isZero
  mpr _ := isZero_of_subsingleton M

@[simp]
/-
**ModuleCat.isZero_of_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：isZero_of_iff_subsingleton {M : Type*} [AddCommGroup M] [Module R M] : IsZ
ero (of R M) ↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.isZero_iff_subsingleton`：isZero_iff_subsingleton : IsZero M ↔ 
Subsingleton M where mp
-/
lemma isZero_of_iff_subsingleton {M : Type*} [AddCommGroup M] [Module R M] :
    IsZero (of R M) ↔ Subsingleton M := isZero_iff_subsingleton

@[simp]
/-
**ModuleCat.ofHom_zero** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：ofHom_zero {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [
Module R N] : ModuleCat.ofHom (0 : M ->ₗ[R] N) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_zero {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : ModuleCat.ofHom (0 : M →ₗ[R] N) = 0 := rfl

@[simp]
/-
**ModuleCat.ofHom_add** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：ofHom_add {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [M
odule R N] (f g : M ->ₗ[R] N) : ModuleCat.ofHom (f + g) = ModuleCat.ofHom f + Mo
duleCat.ofHom g
参数：f g : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_add {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f g : M →ₗ[R] N) :
    ModuleCat.ofHom (f + g) = ModuleCat.ofHom f + ModuleCat.ofHom g := rfl

end AddCommGroup

section SMul

variable {M N : ModuleCat.{v} R} {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul S (M ⟶ N) where
  smul c f := ⟨c • f.hom⟩
/-
**ModuleCat.hom_smul** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R} {S : Type u_1} [inst_1 
: Monoid S] [inst_2 : DistribMulAction S ↑N]   [inst_3 : SMulCommClass R S ↑N] (
s : S) (f : M ⟶ N), ModuleCat.Hom.hom (s • f) = s • ModuleCat.Hom.hom f
参数：s : S；f : M ⟶ N；s • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_smul (s : S) (f : M ⟶ N) : (s • f).hom = s • f.hom := rfl

end SMul

section Module

variable {M N : ModuleCat.{v} R} {S : Type*} [Semiring S] [Module S N] [SMulCommClass R S N]

/-
**ModuleCat.Hom.instModule** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.Hom`。
形式化陈述：{R : Type u} →   [inst : Ring R] →     {M N : ModuleCat R} →       {S : Ty
pe u_1} →         [inst_1 : Semiring S] → [inst_2 : _root_.Module S ↑N] → [SMulC
ommClass R S ↑N] → _root_.Module S (M ⟶ N)
参数：M ⟶ N。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.hom_zero`：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R}, 
ModuleCat.Hom.hom 0 = 0
· 使用定理 `ModuleCat.hom_add`：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R} (f
 g : M ⟶ N),   ModuleCat.Hom.hom (f + g) = ModuleCat.Hom.hom f + ModuleCat.Hom.h
om g
· 使用引理 `ModuleCat.hom_injective`：hom_injective {M N : ModuleCat.{v} R} : Functio
n.Injective (Hom.hom : (M ⟶ N) -> (M ->ₗ[R] N))
-/
instance Hom.instModule : Module S (M ⟶ N) :=
  Function.Injective.module S
    { toFun := Hom.hom, map_zero' := hom_zero, map_add' := hom_add }
    hom_injective
    (fun _ _ => rfl)

/-- `ModuleCat.Hom.hom` bundled as a linear equivalence. -/
@[simps]
/-
**ModuleCat.homLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：homLinearEquiv : (M ⟶ N) ≃ₗ[S] (M ->ₗ[R] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ModuleCat.Hom.hom` bundled as a linear equivalence.
-/
def homLinearEquiv : (M ⟶ N) ≃ₗ[S] (M →ₗ[R] N) :=
  { homAddEquiv with
    map_smul' := fun _ _ => rfl }

end Module

section

universe u₀

namespace Algebra

variable {S₀ : Type u₀} [CommSemiring S₀] {S : Type u} [Ring S] [Algebra S₀ S]

variable {M N : ModuleCat.{v} S}

/--
Let `S` be an `S₀`-algebra. Then `S`-modules are modules over `S₀`.
-/
/-
**ModuleCat.Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat.Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `S` be an `S₀`-algebra. Then `S`-modules are modules over `S₀`.
-/
scoped instance : Module S₀ M := Module.compHom _ (algebraMap S₀ S)
/-
**ModuleCat.Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat.Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance : IsScalarTower S₀ S M where
  smul_assoc _ _ _ := by rw [Algebra.smul_def, mul_smul]; rfl
/-
**ModuleCat.Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat.Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance : SMulCommClass S S₀ M where
  smul_comm s s₀ n :=
    show s • algebraMap S₀ S s₀ • n = algebraMap S₀ S s₀ • s • n by
    rw [← smul_assoc, smul_eq_mul, ← Algebra.commutes, mul_smul]

/--
Let `S` be an `S₀`-algebra. Then the category of `S`-modules is `S₀`-linear.
-/
/-
**ModuleCat.Algebra.instLinear** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.Algebra`。
形式化陈述：{S₀ : Type u₀} →   [inst : CommSemiring S₀] → {S : Type u} → [inst_1 : Rin
g S] → [Algebra S₀ S] → CategoryTheory.Linear S₀ (ModuleCat S)
参数：ModuleCat S。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.Algebra.instSMulCommClassCarrier`：∀ {S₀ : Type u₀} [inst : Com
mSemiring S₀] {S : Type u} [inst_1 : Ring S] [inst_2 : Algebra S₀ S] {M : Module
Cat S},   SMulCommClass S S₀ ↑M

--- 原说明 ---
Let `S` be an `S₀`-algebra. Then the category of `S`-modules is `S₀`-linear.
-/
scoped instance instLinear : Linear S₀ (ModuleCat.{v} S) where
  smul_comp _ M N s₀ f g := by ext; simp

end Algebra

section

variable {S : Type u} [CommRing S]

/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Linear S (ModuleCat.{v} S) := ModuleCat.Algebra.instLinear
/-
**ModuleCat.lsmul_eq_smul_id** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：lsmul_eq_smul_id (M : ModuleCat.{v} S) (s : S) : ModuleCat.ofHom (LinearMa
p.lsmul S M s) = s • 𝟙 M
参数：M : ModuleCat.{v} S；s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lsmul_eq_smul_id (M : ModuleCat.{v} S) (s : S) :
    ModuleCat.ofHom (LinearMap.lsmul S M s) = s • 𝟙 M := rfl

variable {X Y X' Y' : ModuleCat.{v} S}

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**ModuleCat.Iso.homCongr_eq_arrowCongr** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.Iso`
。
形式化陈述：∀ {S : Type u} [inst : CommRing S] {X Y X' Y' : ModuleCat S} (i : X ≅ X') 
(j : Y ≅ Y') (f : X ⟶ Y),   (i.homCongr j) f = { hom' := (i.toLinearEquiv.arrowC
ongr j.toLinearEquiv) (ModuleCat.Hom.hom f) }
参数：i : X ≅ X'；j : Y ≅ Y'；f : X ⟶ Y；i.homCongr j；i.toLinearEquiv.arrowCongr j.toL
inearEquiv；ModuleCat.Hom.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iso.homCongr_eq_arrowCongr (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y) :
    Iso.homCongr i j f = ⟨LinearEquiv.arrowCongr i.toLinearEquiv j.toLinearEquiv f.hom⟩ :=
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**ModuleCat.Iso.conj_eq_conj** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.Iso`。
形式化陈述：∀ {S : Type u} [inst : CommRing S] {X X' : ModuleCat S} (i : X ≅ X') (f : 
CategoryTheory.End X),   i.conj f = { hom' := i.toLinearEquiv.conj (ModuleCat.Ho
m.hom f) }
参数：i : X ≅ X'；f : CategoryTheory.End X；ModuleCat.Hom.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iso.conj_eq_conj (i : X ≅ X') (f : End X) :
    Iso.conj i f = ⟨LinearEquiv.conj i.toLinearEquiv f.hom⟩ :=
  rfl

end

end

variable (M N : ModuleCat.{v} R)

/-- `ModuleCat.Hom.hom` as an isomorphism of rings. -/
/-
**ModuleCat.endRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：{R : Type u} → [inst : Ring R] → (M : ModuleCat R) → CategoryTheory.End M 
≃+* (↑M →ₗ[R] ↑M)
参数：M : ModuleCat R；↑M →ₗ[R] ↑M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ModuleCat.Hom.hom` as an isomorphism of rings.
-/
@[simps!] def endRingEquiv : End M ≃+* (M →ₗ[R] M) where
  toFun := ModuleCat.Hom.hom
  invFun := ModuleCat.ofHom
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The scalar multiplication on an object of `ModuleCat R` considered as
a morphism of rings from `R` to the endomorphisms of the underlying abelian group. -/
/-
**ModuleCat.smul** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：smul : R ->+* End ((forget₂ (ModuleCat R) AddCommGrpCat).obj M) where toFu
n r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The scalar multiplication on an object of `ModuleCat R` considered as
a morphism of rings from `R` to the endomorphisms of the underlying abelian grou
p.
-/
def smul : R →+* End ((forget₂ (ModuleCat R) AddCommGrpCat).obj M) where
  toFun r := AddCommGrpCat.ofHom
    { toFun := fun (m : M) => r • m
      map_zero' := by rw [smul_zero]
      map_add' := fun x y => by rw [smul_add] }
  map_one' := AddCommGrpCat.ext (fun x => by simp)
  map_zero' := AddCommGrpCat.ext (fun x => by simp)
  map_mul' r s := AddCommGrpCat.ext (fun (x : M) => (smul_smul r s x).symm)
  map_add' r s := AddCommGrpCat.ext (fun (x : M) => add_smul r s x)
/-
**ModuleCat.smul_naturality** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：smul_naturality {M N : ModuleCat.{v} R} (f : M ⟶ N) (r : R) : (forget₂ (Mo
duleCat R) AddCommGrpCat).map f ≫ N.smul r = M.smul r ≫ (forget₂ (ModuleCat R) A
ddCommGrpCat).map f
参数：f : M ⟶ N；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGrpCat.hom_ext`：∀ {X Y : AddCommGrpCat} {f g : X ⟶ Y}, AddCommGrp
Cat.Hom.hom f = AddCommGrpCat.Hom.hom g → f = g
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
lemma smul_naturality {M N : ModuleCat.{v} R} (f : M ⟶ N) (r : R) :
    (forget₂ (ModuleCat R) AddCommGrpCat).map f ≫ N.smul r =
      M.smul r ≫ (forget₂ (ModuleCat R) AddCommGrpCat).map f := by
  ext x
  exact (f.hom.map_smul r x).symm

variable (R) in
/-- The scalar multiplication on `ModuleCat R` considered as a morphism of rings
to the endomorphisms of the forgetful functor to `AddCommGrpCat)`. -/
@[simps]
/-
**ModuleCat.smulNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：smulNatTrans : R ->+* End (forget₂ (ModuleCat R) AddCommGrpCat) where toFu
n r
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.smul_naturality`：smul_naturality {M N : ModuleCat.{v} R} (f : 
M ⟶ N) (r : R) : (forget₂ (ModuleCat R) AddCommGrpCat).map f ≫ N.smul r = M.smul
 r ≫ (forget₂ (…

--- 原说明 ---
The scalar multiplication on `ModuleCat R` considered as a morphism of rings
to the endomorphisms of the forgetful functor to `AddCommGrpCat)`.
-/
def smulNatTrans : R →+* End (forget₂ (ModuleCat R) AddCommGrpCat) where
  toFun r :=
    { app := fun M => M.smul r
      naturality := fun _ _ _ => smul_naturality _ r }
  map_one' := by cat_disch
  map_zero' := by cat_disch
  map_mul' _ _ := by cat_disch
  map_add' _ _ := by cat_disch

/-- Given `A : AddCommGrpCat` and a ring morphism `R →+* End A`, this is a type synonym
for `A`, on which we shall define a structure of `R`-module. -/
@[nolint unusedArguments]
/-
**ModuleCat.mkOfSMul'** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：mkOfSMul' {A : AddCommGrpCat} (_ : R ->+* End A)
参数：_ : R ->+* End A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `A : AddCommGrpCat` and a ring morphism `R →+* End A`, this is a type syno
nym
for `A`, on which we shall define a structure of `R`-module.
-/
def mkOfSMul' {A : AddCommGrpCat} (_ : R →+* End A) := A

section

variable {A : AddCommGrpCat} (φ : R →+* End A)

/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (mkOfSMul' φ) :=
  inferInstanceAs <| AddCommGroup A
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul R (mkOfSMul' φ) := ⟨fun r (x : A) => (show A ⟶ A from φ r) x⟩

@[simp]
/-
**ModuleCat.mkOfSMul'_smul** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {A : AddCommGrpCat} (φ : R →+* CategoryTheo
ry.End A) (r : R)   (x : ↑(ModuleCat.mkOfSMul' φ)),   r • x =     (CategoryTheor
y.ConcreteCategory.hom         (have this := φ r;         this))       x
参数：φ : R →+* CategoryTheory.End A；r : R；x : ↑(ModuleCat.mkOfSMul' φ)；CategoryThe
ory.ConcreteCategory.hom         (have this := φ r;         this)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkOfSMul'_smul (r : R) (x : mkOfSMul' φ) :
    r • x = (show A ⟶ A from φ r) x := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R (mkOfSMul' φ) where
  smul_zero _ := map_zero (N := A) _
  smul_add _ _ _ := map_add (N := A) _ _ _
  one_smul := by simp
  mul_smul := by simp
  add_smul _ _ _ := by simp; rfl
  zero_smul := by simp

/-- Given `A : AddCommGrpCat` and a ring morphism `R →+* End A`, this is an object in
`ModuleCat R`, whose underlying abelian group is `A` and whose scalar multiplication is
given by `R`. -/
/-
**ModuleCat.mkOfSMul** 是 Mathlib 中的一个缩写定义，位于命名空间 `ModuleCat`。
形式化陈述：mkOfSMul
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `A : AddCommGrpCat` and a ring morphism `R →+* End A`, this is an object i
n
`ModuleCat R`, whose underlying abelian group is `A` and whose scalar multiplica
tion is
given by `R`.
-/
abbrev mkOfSMul := ModuleCat.of R (mkOfSMul' φ)
/-
**ModuleCat.mkOfSMul_smul** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：mkOfSMul_smul (r : R) : (mkOfSMul φ).smul r = φ r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkOfSMul_smul (r : R) : (mkOfSMul φ).smul r = φ r := rfl

end

section

variable {M N}
  (φ : (forget₂ (ModuleCat R) AddCommGrpCat).obj M ⟶
      (forget₂ (ModuleCat R) AddCommGrpCat).obj N)
  (hφ : ∀ (r : R), φ ≫ N.smul r = M.smul r ≫ φ)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Constructor for morphisms in `ModuleCat R` which takes as inputs
a morphism between the underlying objects in `AddCommGrpCat` and the compatibility
with the scalar multiplication. -/
@[simps]
/-
**ModuleCat.homMk** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：homMk : M ⟶ N where hom'.toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `ModuleCat R` which takes as inputs
a morphism between the underlying objects in `AddCommGrpCat` and the compatibili
ty
with the scalar multiplication.
-/
def homMk : M ⟶ N where
  hom'.toFun := φ
  hom'.map_add' _ _ := φ.hom.map_add _ _
  hom'.map_smul' r x := (ConcreteCategory.congr_hom (hφ r) x).symm
/-
**ModuleCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget₂_map_homMk :
    (forget₂ (ModuleCat R) AddCommGrpCat).map (homMk φ hφ) = φ := rfl

/-- Constructor for isomorphisms in `ModuleCat R` taking an isomorphism in `AddCommGrpCat`
and a compatibility condition. -/
/-
**ModuleCat.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：isoMk (φ : (forget₂ (ModuleCat R) Ab).obj M ≅ (forget₂ _ _).obj N) (hφ : f
orall r, φ.hom ≫ N.smul r = M.smul r ≫ φ.hom) : M ≅ N
参数：φ : (forget₂ (ModuleCat R) Ab).obj M ≅ (forget₂ _ _).obj N；hφ : forall r, φ.h
om ≫ N.smul r = M.smul r ≫ φ.hom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in `ModuleCat R` taking an isomorphism in `AddCommG
rpCat`
and a compatibility condition.
-/
def isoMk (φ : (forget₂ (ModuleCat R) Ab).obj M ≅ (forget₂ _ _).obj N)
    (hφ : ∀ r, φ.hom ≫ N.smul r = M.smul r ≫ φ.hom) :
    M ≅ N :=
  LinearEquiv.toModuleIso
    { __ := φ.addCommGroupIsoToAddEquiv
      map_smul' r x := congr($(hφ r) x).symm }

@[simp]
/-
**ModuleCat.isoMk_hom** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：isoMk_hom (φ : (forget₂ (ModuleCat R) Ab).obj M ≅ (forget₂ _ _).obj N) (hφ
 : forall r, φ.hom ≫ N.smul r = M.smul r ≫ φ.hom) : (isoMk φ hφ).hom = homMk φ.h
om hφ
参数：φ : (forget₂ (ModuleCat R) Ab).obj M ≅ (forget₂ _ _).obj N；hφ : forall r, φ.h
om ≫ N.smul r = M.smul r ≫ φ.hom。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoMk_hom (φ : (forget₂ (ModuleCat R) Ab).obj M ≅ (forget₂ _ _).obj N)
    (hφ : ∀ r, φ.hom ≫ N.smul r = M.smul r ≫ φ.hom) :
    (isoMk φ hφ).hom = homMk φ.hom hφ :=
  rfl

@[simp]
/-
**ModuleCat.isoMk_inv** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：isoMk_inv (φ : (forget₂ (ModuleCat R) Ab).obj M ≅ (forget₂ _ _).obj N) (hφ
 : forall r, φ.hom ≫ N.smul r = M.smul r ≫ φ.hom) : (isoMk φ hφ).inv = homMk φ.i
nv (ModuleCat.smul_naturality (isoMk φ hφ).inv)
参数：φ : (forget₂ (ModuleCat R) Ab).obj M ≅ (forget₂ _ _).obj N；hφ : forall r, φ.h
om ≫ N.smul r = M.smul r ≫ φ.hom。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoMk_inv (φ : (forget₂ (ModuleCat R) Ab).obj M ≅ (forget₂ _ _).obj N)
    (hφ : ∀ r, φ.hom ≫ N.smul r = M.smul r ≫ φ.hom) :
    (isoMk φ hφ).inv = homMk φ.inv (ModuleCat.smul_naturality (isoMk φ hφ).inv) :=
  rfl

@[simp]
/-
**ModuleCat.isoMk_symm** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：isoMk_symm (φ : (forget₂ (ModuleCat R) Ab).obj M ≅ (forget₂ _ _).obj N) (h
φ : forall r, φ.hom ≫ N.smul r = M.smul r ≫ φ.hom) : (isoMk φ hφ).symm = isoMk φ
.symm (ModuleCat.smul_naturality (isoMk φ hφ).inv)
参数：φ : (forget₂ (ModuleCat R) Ab).obj M ≅ (forget₂ _ _).obj N；hφ : forall r, φ.h
om ≫ N.smul r = M.smul r ≫ φ.hom。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoMk_symm (φ : (forget₂ (ModuleCat R) Ab).obj M ≅ (forget₂ _ _).obj N)
    (hφ : ∀ r, φ.hom ≫ N.smul r = M.smul r ≫ φ.hom) :
    (isoMk φ hφ).symm = isoMk φ.symm (ModuleCat.smul_naturality (isoMk φ hφ).inv) :=
  rfl

end

/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget (ModuleCat.{v} R)).ReflectsIsomorphisms where
  reflects f _ :=
    (inferInstance : IsIso ((LinearEquiv.mk f.hom
      (asIso ((forget (ModuleCat R)).map f)).toEquiv.invFun
      (Equiv.left_inv _) (Equiv.right_inv _)).toModuleIso).hom)
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).ReflectsIsomorphisms where
  reflects f _ := by
    have : IsIso ((forget _).map f) := by
      change IsIso ((forget _).map ((forget₂ _ AddCommGrpCat).map f))
      infer_instance
    apply isIso_of_reflects_iso _ (forget _)

end ModuleCat

section Bilinear

variable {R : Type*} [CommRing R]

namespace ModuleCat

/-- Turn a bilinear map into a homomorphism. -/
@[simps!]
/-
**ModuleCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `ModuleCat`。
形式化陈述：ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Modul
e R Y] (f : X ->ₗ[R] Y) : of R X ⟶ of R Y
参数：f : X ->ₗ[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a bilinear map into a homomorphism.
-/
def ofHom₂ {M N P : ModuleCat.{u} R} (f : M →ₗ[R] N →ₗ[R] P) :
    M ⟶ of R (N ⟶ P) :=
  ofHom <| homLinearEquiv.symm.toLinearMap ∘ₗ f

/-- Turn a homomorphism into a bilinear map. -/
@[simps!]
/-
**ModuleCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.Hom`。
形式化陈述：{R : Type u} → [inst : Ring R] → {A B : ModuleCat R} → A.Hom B → ↑A →ₗ[R] 
↑B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a homomorphism into a bilinear map.
-/
def Hom.hom₂ {M N P : ModuleCat.{u} R} (f : M ⟶ (of R (N ⟶ P))) : M →ₗ[R] N →ₗ[R] P :=
  (f ≫ ofHom homLinearEquiv.toLinearMap).hom
/-
**ModuleCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.Hom`。
形式化陈述：{R : Type u} → [inst : Ring R] → {A B : ModuleCat R} → A.Hom B → ↑A →ₗ[R] 
↑B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Hom.hom₂_ofHom₂ {M N P : ModuleCat.{u} R} (f : M →ₗ[R] N →ₗ[R] P) :
    (ofHom₂ f).hom₂ = f := rfl
/-
**ModuleCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `ModuleCat`。
形式化陈述：ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Modul
e R Y] (f : X ->ₗ[R] Y) : of R X ⟶ of R Y
参数：f : X ->ₗ[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofHom₂_hom₂ {M N P : ModuleCat.{u} R} (f : M ⟶ of R (N ⟶ P)) :
    ofHom₂ f.hom₂ = f := rfl

end ModuleCat

end Bilinear

/-!
`@[simp]` lemmas for `LinearMap.comp` and categorical identities.
-/

/-
**LinearMap.comp_id_moduleCat** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {G : ModuleCat R} {H : Type u} [inst_1 : 
AddCommGroup H] [inst_2 : _root_.Module R H]   (f : ↑G →ₗ[R] H), f ∘ₗ ModuleCat.
Hom.hom (CategoryTheory.CategoryStruct.id G) = f
参数：f : ↑G →ₗ[R] H；CategoryTheory.CategoryStruct.id G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`@[simp]` lemmas for `LinearMap.comp` and categorical identities.
-/
@[simp] theorem LinearMap.comp_id_moduleCat
    {R} [Ring R] {G : ModuleCat.{u} R} {H : Type u} [AddCommGroup H] [Module R H] (f : G →ₗ[R] H) :
    f.comp (𝟙 G : G ⟶ G).hom = f := by simp
/-
**LinearMap.id_moduleCat_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {G : Type u} [inst_1 : AddCommGroup G] [i
nst_2 : _root_.Module R G] {H : ModuleCat R}   (f : G →ₗ[R] ↑H), ModuleCat.Hom.h
om (CategoryTheory.CategoryStruct.id H) ∘ₗ f = f
参数：f : G →ₗ[R] ↑H；CategoryTheory.CategoryStruct.id H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem LinearMap.id_moduleCat_comp
    {R} [Ring R] {G : Type u} [AddCommGroup G] [Module R G] {H : ModuleCat.{u} R} (f : G →ₗ[R] H) :
    LinearMap.comp (𝟙 H : H ⟶ H).hom f = f := by simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S : Type*} [Ring R] [Ring S] (F : ModuleCat R ⥤ ModuleCat S) [F.Full] [F.Faithful]
    (M : ModuleCat R) [h : Nontrivial M] : Nontrivial (F.obj M) := by
  by_contra!
  exact ((not_iff_not.2 ModuleCat.isZero_iff_subsingleton).2 <|
    not_subsingleton_iff_nontrivial.2 h) <| IsZero.of_full_of_faithful_of_isZero F _ <|
    ModuleCat.isZero_of_subsingleton <| F.obj M
