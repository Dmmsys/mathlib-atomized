/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer, Junyan Xu
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# The category of `R`-modules

If `R` is a semiring, `SemimoduleCat.{v} R` is the category of bundled `R`-semimodules with carrier
in the universe `v`. We show that it is preadditive and show that being an isomorphism and
monomorphism are equivalent to being a linear equivalence and an injective linear map respectively.

## Implementation details

To construct an object in the category of `R`-semimodules from a type `M` with an instance of the
`Module` typeclass, write `of R M`. There is a coercion in the other direction.
The roundtrip `↑(of R M)` is definitionally equal to `M` itself (when `M` is a type with `Module`
instance), and so is `of R ↑M` (when `M : SemimoduleCat R M`).

The morphisms are given their own type, not identified with `LinearMap`.
There is a cast from morphisms in `Module R` to linear maps,
written `f.hom` (`SemimoduleCat.Hom.hom`).
To go from linear maps to morphisms in `Module R`, use `SemimoduleCat.ofHom`.

Similarly, given an isomorphism `f : M ≅ N` use `f.toLinearEquiv` and given a linear equiv
`f : M ≃ₗ[R] N`, use `f.toModuleIso`.
-/

@[expose] public section


open CategoryTheory Limits WalkingParallelPair

universe v u

variable (R : Type u) [Semiring R]

/-- The category of R-semimodules and their morphisms.

Note that in the case of `R = ℕ`, we can not
impose here that the `ℕ`-multiplication field from the module structure is defeq to the one coming
from the `isAddCommMonoid` structure (contrary to what we do for all module structures in
mathlib), which creates some difficulties down the road. -/
/-
**SemimoduleCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [Semiring R] → Type (max u (v + 1))
参数：v + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of R-semimodules and their morphisms.

Note that in the case of `R = ℕ`, we can not
impose here that the `ℕ`-multiplication field from the module structure is defeq
 to the one coming
from the `isAddCommMonoid` structure (contrary to what we do for all module stru
ctures in
mathlib), which creates some difficulties down the road.
-/
structure SemimoduleCat where
  private mk ::
  /-- the underlying type of an object in `SemimoduleCat R` -/
  carrier : Type v
  [isAddCommMonoid : AddCommMonoid carrier]
  [isModule : Module R carrier]

initialize_simps_projections SemimoduleCat (-isModule, -isAddCommMonoid)
attribute [instance] SemimoduleCat.isAddCommMonoid SemimoduleCat.isModule

namespace SemimoduleCat

/-
**SemimoduleCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (SemimoduleCat.{v} R) (Type v) :=
  ⟨SemimoduleCat.carrier⟩

attribute [coe] SemimoduleCat.carrier

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `SemimoduleCat R`. -/
/-
**SemimoduleCat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `SemimoduleCat`。
形式化陈述：of (X : Type v) [AddCommMonoid X] [Module R X] : SemimoduleCat.{v} R
参数：X : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object in the category of R-algebras associated to a type equipped with the 
appropriate
typeclasses. This is the preferred way to construct a term of `SemimoduleCat R`.
-/
abbrev of (X : Type v) [AddCommMonoid X] [Module R X] : SemimoduleCat.{v} R :=
  ⟨X⟩
/-
**SemimoduleCat.coe_of** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：coe_of (X : Type v) [Semiring X] [Module R X] : (of R X : Type v) = X
参数：X : Type v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_of (X : Type v) [Semiring X] [Module R X] : (of R X : Type v) = X :=
  rfl

-- Ensure the roundtrips are reducibly defeq (so tactics like `rw` can see through them).
/-
**SemimoduleCat.** 是 Mathlib 中的一个示例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (X : Type v) [Semiring X] [Module R X] : (of R X : Type v) = X := by with_reducible rfl
/-
**SemimoduleCat.** 是 Mathlib 中的一个示例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (M : SemimoduleCat.{v} R) : of R M = M := by with_reducible rfl

variable {R} in
/-- The type of morphisms in `SemimoduleCat R`. -/
@[ext]
/-
**SemimoduleCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `SemimoduleCat`。
形式化陈述：{R : Type u} → [inst : Semiring R] → SemimoduleCat R → SemimoduleCat R → T
ype v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `SemimoduleCat R`.
-/
structure Hom (M N : SemimoduleCat.{v} R) where
  mk ::
  /-- The underlying linear map. -/
  hom' : M →ₗ[R] N
/-
**SemimoduleCat.moduleCategory** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
形式化陈述：moduleCategory : Category.{v, max (v + 1) u} (SemimoduleCat.{v} R) where H
om M N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance moduleCategory : Category.{v, max (v + 1) u} (SemimoduleCat.{v} R) where
  Hom M N := Hom M N
  id _ := ⟨LinearMap.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
/-
**SemimoduleCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory (SemimoduleCat.{v} R) (· →ₗ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

section

variable {R}

/-- Turn a morphism in `SemimoduleCat` back into a `LinearMap`. -/
/-
**SemimoduleCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `SemimoduleCat.Hom`。
形式化陈述：{R : Type u} → [inst : Semiring R] → {A B : SemimoduleCat R} → A.Hom B → ↑
A →ₗ[R] ↑B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `SemimoduleCat` back into a `LinearMap`.
-/
abbrev Hom.hom {A B : SemimoduleCat.{v} R} (f : Hom A B) :=
  ConcreteCategory.hom (C := SemimoduleCat R) f

/-- Typecheck a `LinearMap` as a morphism in `SemimoduleCat`. -/
/-
**SemimoduleCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `SemimoduleCat`。
形式化陈述：ofHom {X Y : Type v} [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Mod
ule R Y] (f : X ->ₗ[R] Y) : of R X ⟶ of R Y
参数：f : X ->ₗ[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `LinearMap` as a morphism in `SemimoduleCat`.
-/
abbrev ofHom {X Y : Type v} [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y]
    (f : X →ₗ[R] Y) : of R X ⟶ of R Y :=
  ConcreteCategory.ofHom (C := SemimoduleCat R) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**SemimoduleCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `SemimoduleCat.Hom.Simps
`。
形式化陈述：{R : Type u} → [inst : Semiring R] → (A B : SemimoduleCat R) → A.Hom B → ↑
A →ₗ[R] ↑B
参数：A B : SemimoduleCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (A B : SemimoduleCat.{v} R) (f : Hom A B) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/-
**SemimoduleCat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_id {M : SemimoduleCat.{v} R} : (𝟙 M : M ⟶ M).hom = LinearMap.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma hom_id {M : SemimoduleCat.{v} R} : (𝟙 M : M ⟶ M).hom = LinearMap.id := rfl

/- Provided for rewriting. -/
/-
**SemimoduleCat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：id_apply (M : SemimoduleCat.{v} R) (x : M) : (𝟙 M : M ⟶ M) x = x
参数：M : SemimoduleCat.{v} R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (M : SemimoduleCat.{v} R) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

@[simp]
/-
**SemimoduleCat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_comp {M N O : SemimoduleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) : (f ≫ g).h
om = g.hom.comp f.hom
参数：f : M ⟶ N；g : N ⟶ O。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {M N O : SemimoduleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**SemimoduleCat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：comp_apply {M N O : SemimoduleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) (x : M) :
 (f ≫ g) x = g (f x)
参数：f : M ⟶ N；g : N ⟶ O；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {M N O : SemimoduleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) (x : M) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/-
**SemimoduleCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N} (hf : f.hom = g.hom) : f
 = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemimoduleCat.Hom.ext`：∀ {R : Type u} {inst : Semiring R} {M N : Semimod
uleCat R} {x y : M.Hom N}, x.hom' = y.hom' → x = y
-/
lemma hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf
/-
**SemimoduleCat.hom_bijective** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_bijective {M N : SemimoduleCat.{v} R} : Function.Bijective (Hom.hom : 
(M ⟶ N) -> (M ->ₗ[R] N)) where left f g h
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemimoduleCat.Hom.mk.injEq`：∀ {R : Type u} [inst : Semiring R] {M N : Se
mimoduleCat R} (hom' hom'_1 : ↑M →ₗ[R] ↑N),   ({ hom' := hom' } = { hom' := hom'
_1 }) = (hom' = …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma hom_bijective {M N : SemimoduleCat.{v} R} :
    Function.Bijective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) where
  left f g h := by cases f; cases g; simpa using! h
  right f := ⟨⟨f⟩, rfl⟩

/-- Convenience shortcut for `SemimoduleCat.hom_bijective.injective`. -/
/-
**SemimoduleCat.hom_injective** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_injective {M N : SemimoduleCat.{v} R} : Function.Injective (Hom.hom : 
(M ⟶ N) -> (M ->ₗ[R] N))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用引理 `SemimoduleCat.hom_bijective`：hom_bijective {M N : SemimoduleCat.{v} R} :
 Function.Bijective (Hom.hom : (M ⟶ N) -> (M ->ₗ[R] N)) where left f g h

--- 原说明 ---
Convenience shortcut for `SemimoduleCat.hom_bijective.injective`.
-/
lemma hom_injective {M N : SemimoduleCat.{v} R} :
    Function.Injective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) :=
  hom_bijective.injective

/-- Convenience shortcut for `SemimoduleCat.hom_bijective.surjective`. -/
/-
**SemimoduleCat.hom_surjective** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_surjective {M N : SemimoduleCat.{v} R} : Function.Surjective (Hom.hom 
: (M ⟶ N) -> (M ->ₗ[R] N))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用引理 `SemimoduleCat.hom_bijective`：hom_bijective {M N : SemimoduleCat.{v} R} :
 Function.Bijective (Hom.hom : (M ⟶ N) -> (M ->ₗ[R] N)) where left f g h

--- 原说明 ---
Convenience shortcut for `SemimoduleCat.hom_bijective.surjective`.
-/
lemma hom_surjective {M N : SemimoduleCat.{v} R} :
    Function.Surjective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) :=
  hom_bijective.surjective

@[simp]
/-
**SemimoduleCat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_ofHom {X Y : Type v} [AddCommMonoid X] [Module R X] [AddCommMonoid Y] 
[Module R Y] (f : X ->ₗ[R] Y) : (ofHom f).hom = f
参数：f : X ->ₗ[R] Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type v} [AddCommMonoid X] [Module R X] [AddCommMonoid Y]
    [Module R Y] (f : X →ₗ[R] Y) : (ofHom f).hom = f := rfl

@[simp]
/-
**SemimoduleCat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：ofHom_hom {M N : SemimoduleCat.{v} R} (f : M ⟶ N) : ofHom (Hom.hom f) = f
参数：f : M ⟶ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {M N : SemimoduleCat.{v} R} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**SemimoduleCat.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：ofHom_id {M : Type v} [AddCommMonoid M] [Module R M] : ofHom LinearMap.id 
= 𝟙 (of R M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {M : Type v} [AddCommMonoid M] [Module R M] : ofHom LinearMap.id = 𝟙 (of R M) := rfl

@[simp]
/-
**SemimoduleCat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：ofHom_comp {M N O : Type v} [AddCommMonoid M] [AddCommMonoid N] [AddCommMo
noid O] [Module R M] [Module R N] [Module R O] (f : M ->ₗ[R] N) (g : N ->ₗ[R] O)
 : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] O。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {M N O : Type v} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O] [Module R M]
    [Module R N] [Module R O] (f : M →ₗ[R] N) (g : N →ₗ[R] O) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/- Doesn't need to be `@[simp]` since `simp only` can solve this. -/
/-
**SemimoduleCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：ofHom_apply {M N : Type v} [AddCommMonoid M] [AddCommMonoid N] [Module R M
] [Module R N] (f : M ->ₗ[R] N) (x : M) : ofHom f x = f x
参数：f : M ->ₗ[R] N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Doesn't need to be `@[simp]` since `simp only` can solve this.
-/
lemma ofHom_apply {M N : Type v} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (x : M) : ofHom f x = f x := rfl
/-
**SemimoduleCat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：inv_hom_apply {M N : SemimoduleCat.{v} R} (e : M ≅ N) (x : M) : e.inv (e.h
om x) = x
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
lemma inv_hom_apply {M N : SemimoduleCat.{v} R} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  simp
/-
**SemimoduleCat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：hom_inv_apply {M N : SemimoduleCat.{v} R} (e : M ≅ N) (x : N) : e.hom (e.i
nv x) = x
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
lemma hom_inv_apply {M N : SemimoduleCat.{v} R} (e : M ≅ N) (x : N) : e.hom (e.inv x) = x := by
  simp

/-- `SemimoduleCat.Hom.hom` bundled as an `Equiv`. -/
/-
**SemimoduleCat.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SemimoduleCat`。
形式化陈述：homEquiv {M N : SemimoduleCat.{v} R} : (M ⟶ N) ≃ (M ->ₗ[R] N) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SemimoduleCat.Hom.hom` bundled as an `Equiv`.
-/
def homEquiv {M N : SemimoduleCat.{v} R} : (M ⟶ N) ≃ (M →ₗ[R] N) where
  toFun := Hom.hom
  invFun := ofHom

end

/- Not a `@[simp]` lemma since it will rewrite the (co)domain of maps and cause
definitional equality issues. -/
/-
**SemimoduleCat.forget_obj** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：forget_obj {M : SemimoduleCat.{v} R} : ((forget (SemimoduleCat.{v} R)).obj
 M : Type _) = M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Not a `@[simp]` lemma since it will rewrite the (co)domain of maps and cause
definitional equality issues.
-/
lemma forget_obj {M : SemimoduleCat.{v} R} : ((forget (SemimoduleCat.{v} R)).obj M : Type _) = M :=
  rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-02-25")]
/-
**SemimoduleCat.forget_map** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat`。
形式化陈述：forget_map {M N : SemimoduleCat.{v} R} (f : M ⟶ N) : (forget (SemimoduleCa
t.{v} R)).map f = (f : _ -> _)
参数：f : M ⟶ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map {M N : SemimoduleCat.{v} R} (f : M ⟶ N) :
    (forget (SemimoduleCat.{v} R)).map f = (f : _ → _) :=
  rfl
/-
**SemimoduleCat.hasForgetToAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCa
t`。
形式化陈述：hasForgetToAddCommMonoid : HasForget₂ (SemimoduleCat R) AddCommMonCat wher
e forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToAddCommMonoid : HasForget₂ (SemimoduleCat R) AddCommMonCat where
  forget₂ :=
    { obj := fun M => .of M
      map := fun f => AddCommMonCat.ofHom f.hom.toAddMonoidHom }

@[simp]
/-
**SemimoduleCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_obj (X : SemimoduleCat R) :
    (forget₂ (SemimoduleCat R) AddCommMonCat).obj X = .of X :=
  rfl
/-
**SemimoduleCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_obj_moduleCat_of (X : Type v) [AddCommMonoid X] [Module R X] :
    (forget₂ (SemimoduleCat R) AddCommMonCat).obj (of R X) = .of X :=
  rfl

@[simp]
/-
**SemimoduleCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_map (X Y : SemimoduleCat R) (f : X ⟶ Y) :
    (forget₂ (SemimoduleCat R) AddCommMonCat).map f = AddCommMonCat.ofHom f.hom :=
  rfl
/-
**SemimoduleCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (SemimoduleCat R) :=
  ⟨of R PUnit⟩
/-
**SemimoduleCat.of_coe** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
形式化陈述：∀ (R : Type u) [inst : Semiring R] (X : SemimoduleCat R), SemimoduleCat.of
 R ↑X = X
参数：R : Type u；X : SemimoduleCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem of_coe (X : SemimoduleCat R) : of R X = X := rfl

variable {R}
/-
**SemimoduleCat.isZero_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`
。
形式化陈述：isZero_of_subsingleton (M : SemimoduleCat R) [Subsingleton M] : IsZero M w
here unique_to X
参数：M : SemimoduleCat R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemimoduleCat.hom_ext`：hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N}
 (hf : f.hom = g.hom) : f = g
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
theorem isZero_of_subsingleton (M : SemimoduleCat R) [Subsingleton M] : IsZero M where
  unique_to X := ⟨⟨⟨ofHom (0 : M →ₗ[R] X)⟩, fun f => by
    ext x
    rw [Subsingleton.elim x (0 : M)]
    simp⟩⟩
  unique_from X := ⟨⟨⟨ofHom (0 : X →ₗ[R] M)⟩, fun f => by
    ext x
    subsingleton⟩⟩
/-
**SemimoduleCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasZeroObject (SemimoduleCat.{v} R) :=
  ⟨⟨of R PUnit, isZero_of_subsingleton _⟩⟩

end SemimoduleCat

variable {R}
variable {X₁ X₂ : Type v}

open SemimoduleCat

/-- Reinterpreting a linear map in the category of `R`-modules -/
scoped[SemimoduleCat] notation "↟" f:1024 => SemimoduleCat.ofHom f

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
def LinearEquiv.toModuleIsoₛ {g₁ : AddCommMonoid X₁} {g₂ : AddCommMonoid X₂} {m₁ : Module R X₁}
    {m₂ : Module R X₂} (e : X₁ ≃ₗ[R] X₂) : SemimoduleCat.of R X₁ ≅ SemimoduleCat.of R X₂ where
  hom := ofHom (e : X₁ →ₗ[R] X₂)
  inv := ofHom (e.symm : X₂ →ₗ[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv

namespace CategoryTheory.Iso

/-- Build a `LinearEquiv` from an isomorphism in the category `SemimoduleCat R`. -/
/-
**CategoryTheory.Iso.toLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso
`。
形式化陈述：toLinearEquiv (i : X ≅ Y) : X ≃ₗ[R] Y
参数：i : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `LinearEquiv` from an isomorphism in the category `SemimoduleCat R`.
-/
def toLinearEquivₛ {X Y : SemimoduleCat R} (i : X ≅ Y) : X ≃ₗ[R] Y :=
  LinearEquiv.ofLinearMap i.hom.hom i.inv.hom (by aesop) (by aesop)

end CategoryTheory.Iso

/-- linear equivalences between `Module`s are the same as (isomorphic to) isomorphisms
in `SemimoduleCat` -/
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
in `SemimoduleCat`
-/
def linearEquivIsoModuleIsoₛ {X Y : Type u} [AddCommMonoid X] [AddCommMonoid Y] [Module R X]
    [Module R Y] : (X ≃ₗ[R] Y) ≅
      ((SemimoduleCat.of R X) ≅ (SemimoduleCat.of R Y)) where
  hom := ↾fun e ↦ e.toModuleIsoₛ
  inv := ↾fun i ↦ i.toLinearEquivₛ

end

namespace SemimoduleCat

section AddCommMonoid

variable {M N : SemimoduleCat.{v} R}

/-
**SemimoduleCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (M ⟶ N) where
  add f g := ⟨f.hom + g.hom⟩
/-
**SemimoduleCat.hom_add** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {M N : SemimoduleCat R} (f g : M ⟶ N), 
  SemimoduleCat.Hom.hom (f + g) = SemimoduleCat.Hom.hom f + SemimoduleCat.Hom.ho
m g
参数：f g : M ⟶ N；f + g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl
/-
**SemimoduleCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (M ⟶ N) where
  zero := ⟨0⟩
/-
**SemimoduleCat.hom_zero** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {M N : SemimoduleCat R}, SemimoduleCat.
Hom.hom 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_zero : (0 : M ⟶ N).hom = 0 := rfl
/-
**SemimoduleCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℕ (M ⟶ N) where
  smul n f := ⟨n • f.hom⟩
/-
**SemimoduleCat.hom_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {M N : SemimoduleCat R} (n : ℕ) (f : M 
⟶ N),   SemimoduleCat.Hom.hom (n • f) = n • SemimoduleCat.Hom.hom f
参数：n : ℕ；f : M ⟶ N；n • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_nsmul (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

-- There is no `ℤ`-smul operation on a general semimodule!
@[deprecated (since := "2026-01-06")]
alias hom_zsmul := hom_nsmul
/-
**SemimoduleCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (M ⟶ N) :=
  Function.Injective.addCommMonoid Hom.hom hom_injective rfl (fun _ _ => rfl) (fun _ _ => rfl)
/-
**SemimoduleCat.hom_sum** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {M N : SemimoduleCat R} {ι : Type u_1} 
(f : ι → (M ⟶ N)) (s : Finset ι),   SemimoduleCat.Hom.hom (∑ i ∈ s, f i) = ∑ i ∈
 s, SemimoduleCat.Hom.hom (f i)
参数：f : ι → (M ⟶ N)；s : Finset ι；∑ i ∈ s, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `SemimoduleCat.hom_zero`：∀ {R : Type u} [inst : Semiring R] {M N : Semimo
duleCat R}, SemimoduleCat.Hom.hom 0 = 0
· 使用定理 `SemimoduleCat.hom_add`：∀ {R : Type u} [inst : Semiring R] {M N : Semimod
uleCat R} (f g : M ⟶ N),   SemimoduleCat.Hom.hom (f + g) = SemimoduleCat.Hom.hom
 f + Semimo…
-/
@[simp] lemma hom_sum {ι : Type*} (f : ι → (M ⟶ N)) (s : Finset ι) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom :=
  map_sum ({ toFun := SemimoduleCat.Hom.hom, map_zero' := SemimoduleCat.hom_zero,
             map_add' := hom_add } : (M ⟶ N) →+ (M →ₗ[R] N)) _ _

/- TODO: generalize Preadditive and Functor.Additive, see #28826.
instance : Presemiadditive (SemimoduleCat.{v} R) where
/-
**SemimoduleCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ (SemimoduleCat.{v} R) AddCommMonCat).Additive where -/
/-
**SemimoduleCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
TODO: generalize Preadditive and Functor.Additive, see #28826.
instance : Presemiadditive (SemimoduleCat.{v} R) where
instance : (forget₂ (SemimoduleCat.{v} R) AddCommMonCat).Additive where
-/
instance : HasZeroMorphisms (SemimoduleCat.{v} R) where

/-- `SemimoduleCat.Hom.hom` bundled as an additive equivalence. -/
@[simps!]
/-
**SemimoduleCat.homAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SemimoduleCat`。
形式化陈述：homAddEquiv : (M ⟶ N) ≃+ (M ->ₗ[R] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SemimoduleCat.Hom.hom` bundled as an additive equivalence.
-/
def homAddEquiv : (M ⟶ N) ≃+ (M →ₗ[R] N) :=
  { homEquiv with
    map_add' := fun _ _ => rfl }
/-
**SemimoduleCat.subsingleton_of_isZero** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`
。
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
· 使用引理 `SemimoduleCat.hom_id`：hom_id {M : SemimoduleCat.{v} R} : (𝟙 M : M ⟶ M).h
om = LinearMap.id
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
  rw [← LinearMap.id_apply (R := R) x, ← SemimoduleCat.hom_id]
  simp only [(CategoryTheory.Limits.IsZero.iff_id_eq_zero M).mp h, hom_zero, LinearMap.zero_apply]
/-
**SemimoduleCat.isZero_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `SemimoduleCat
`。
形式化陈述：isZero_iff_subsingleton : IsZero M ↔ Subsingleton M where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemimoduleCat.subsingleton_of_isZero`：subsingleton_of_isZero (h : IsZero
 M) : Subsingleton M
· 使用定理 `SemimoduleCat.isZero_of_subsingleton`：isZero_of_subsingleton (M : Semimo
duleCat R) [Subsingleton M] : IsZero M where unique_to X
-/
lemma isZero_iff_subsingleton : IsZero M ↔ Subsingleton M where
  mp := subsingleton_of_isZero
  mpr _ := isZero_of_subsingleton M

@[simp]
/-
**SemimoduleCat.isZero_of_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Semimodule
Cat`。
形式化陈述：isZero_of_iff_subsingleton {M : Type*} [AddCommMonoid M] [Module R M] : Is
Zero (of R M) ↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemimoduleCat.isZero_iff_subsingleton`：isZero_iff_subsingleton : IsZero 
M ↔ Subsingleton M where mp
-/
lemma isZero_of_iff_subsingleton {M : Type*} [AddCommMonoid M] [Module R M] :
    IsZero (of R M) ↔ Subsingleton M := isZero_iff_subsingleton

end AddCommMonoid

section SMul

variable {M N : SemimoduleCat.{v} R}
variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

/-
**SemimoduleCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul S (M ⟶ N) where
  smul c f := ⟨c • f.hom⟩
/-
**SemimoduleCat.hom_smul** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {M N : SemimoduleCat R} {S : Type u_1} 
[inst_1 : Monoid S]   [inst_2 : DistribMulAction S ↑N] [inst_3 : SMulCommClass R
 S ↑N] (s : S) (f : M ⟶ N),   SemimoduleCat.Hom.hom (s • f) = s • SemimoduleCat.
Hom.hom f
参数：s : S；f : M ⟶ N；s • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_smul (s : S) (f : M ⟶ N) : (s • f).hom = s • f.hom := rfl

end SMul

section Module

variable {M N : SemimoduleCat.{v} R} {S : Type*} [Semiring S] [Module S N] [SMulCommClass R S N]

/-
**SemimoduleCat.Hom.instModule** 是 Mathlib 中的一个定义，位于命名空间 `SemimoduleCat.Hom`。
形式化陈述：{R : Type u} →   [inst : Semiring R] →     {M N : SemimoduleCat R} →      
 {S : Type u_1} →         [inst_1 : Semiring S] → [inst_2 : _root_.Module S ↑N] 
→ [SMulCommClass R S ↑N] → _root_.Module S (M ⟶ N)
参数：M ⟶ N。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SemimoduleCat.hom_zero`：∀ {R : Type u} [inst : Semiring R] {M N : Semimo
duleCat R}, SemimoduleCat.Hom.hom 0 = 0
· 使用定理 `SemimoduleCat.hom_add`：∀ {R : Type u} [inst : Semiring R] {M N : Semimod
uleCat R} (f g : M ⟶ N),   SemimoduleCat.Hom.hom (f + g) = SemimoduleCat.Hom.hom
 f + Semimo…
· 使用引理 `SemimoduleCat.hom_injective`：hom_injective {M N : SemimoduleCat.{v} R} :
 Function.Injective (Hom.hom : (M ⟶ N) -> (M ->ₗ[R] N))
-/
instance Hom.instModule : Module S (M ⟶ N) :=
  Function.Injective.module S
    { toFun := Hom.hom, map_zero' := hom_zero, map_add' := hom_add }
    hom_injective
    (fun _ _ => rfl)

/-- `SemimoduleCat.Hom.hom` bundled as a linear equivalence. -/
@[simps]
/-
**SemimoduleCat.homLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SemimoduleCat`。
形式化陈述：homLinearEquiv : (M ⟶ N) ≃ₗ[S] (M ->ₗ[R] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SemimoduleCat.Hom.hom` bundled as a linear equivalence.
-/
def homLinearEquiv : (M ⟶ N) ≃ₗ[S] (M →ₗ[R] N) :=
  { homAddEquiv with
    map_smul' := fun _ _ => rfl }

end Module

section

universe u₀

namespace Algebra

variable {S₀ : Type u₀} [CommSemiring S₀] {S : Type u} [Semiring S] [Algebra S₀ S]

variable {M N : SemimoduleCat.{v} S}

/--
Let `S` be an `S₀`-algebra. Then `S`-modules are modules over `S₀`.
-/
/-
**SemimoduleCat.Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat.Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `S` be an `S₀`-algebra. Then `S`-modules are modules over `S₀`.
-/
scoped instance : Module S₀ M := Module.compHom _ (algebraMap S₀ S)
/-
**SemimoduleCat.Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat.Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance : IsScalarTower S₀ S M where
  smul_assoc _ _ _ := by rw [Algebra.smul_def, mul_smul]; rfl
/-
**SemimoduleCat.Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat.Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance : SMulCommClass S S₀ M where
  smul_comm s s₀ n :=
    show s • algebraMap S₀ S s₀ • n = algebraMap S₀ S s₀ • s • n by
    rw [← smul_assoc, smul_eq_mul, ← Algebra.commutes, mul_smul]

/- TODO: generalize `Functor.Linear`, see #28826.
Let `S` be an `S₀`-algebra. Then the category of `S`-modules is `S₀`-linear.
scoped instance instLinear : Linear S₀ (SemimoduleCat.{v} S) where
  smul_comp _ M N s₀ f g := by ext; simp -/

end Algebra

section

variable {S : Type u} [CommSemiring S]

/- TODO: generalize `Functor.Linear`, see #28826.
/-
**SemimoduleCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Linear S (SemimoduleCat.{v} S) := SemimoduleCat.Algebra.instLinear -/

variable {X Y X' Y' : SemimoduleCat.{v} S}
/-
**SemimoduleCat.Iso.homCongr_eq_arrowCongr** 是 Mathlib 中的一个定理，位于命名空间 `Semimodule
Cat.Iso`。
形式化陈述：∀ {S : Type u} [inst : CommSemiring S] {X Y X' Y' : SemimoduleCat S} (i : 
X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y),   (i.homCongr j) f = { hom' := (i.toLinearEqui
vₛ.arrowCongr j.toLinearEquivₛ) (SemimoduleCat.Hom.hom f) }
参数：i : X ≅ X'；j : Y ≅ Y'；f : X ⟶ Y；i.homCongr j；i.toLinearEquivₛ.arrowCongr j.to
LinearEquivₛ；SemimoduleCat.Hom.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iso.homCongr_eq_arrowCongr (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y) :
    Iso.homCongr i j f = ⟨LinearEquiv.arrowCongr i.toLinearEquivₛ j.toLinearEquivₛ f.hom⟩ :=
  rfl
/-
**SemimoduleCat.Iso.conj_eq_conj** 是 Mathlib 中的一个定理，位于命名空间 `SemimoduleCat.Iso`。
形式化陈述：∀ {S : Type u} [inst : CommSemiring S] {X X' : SemimoduleCat S} (i : X ≅ X
') (f : CategoryTheory.End X),   i.conj f = { hom' := i.toLinearEquivₛ.conj (Sem
imoduleCat.Hom.hom f) }
参数：i : X ≅ X'；f : CategoryTheory.End X；SemimoduleCat.Hom.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iso.conj_eq_conj (i : X ≅ X') (f : End X) :
    Iso.conj i f = ⟨LinearEquiv.conj i.toLinearEquivₛ f.hom⟩ :=
  rfl

end

end

/- TODO: Declarations in #28826 from `endSemiringEquiv` to `forget₂_map_homMk` can be added back
after appropriate generalizations. -/

/-
**SemimoduleCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
TODO: Declarations in #28826 from `endSemiringEquiv` to `forget₂_map_homMk` can 
be added back
after appropriate generalizations.
-/
instance : (forget (SemimoduleCat.{v} R)).ReflectsIsomorphisms where
  reflects f _ :=
    (inferInstance : IsIso ((LinearEquiv.mk f.hom
      (asIso ((forget (SemimoduleCat R)).map f)).toEquiv.invFun
      (Equiv.left_inv _) (Equiv.right_inv _)).toModuleIsoₛ).hom)
/-
**SemimoduleCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemimoduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ (SemimoduleCat.{v} R) AddCommMonCat.{v}).ReflectsIsomorphisms where
  reflects f _ := by
    have : IsIso ((forget _).map f) := by
      change IsIso ((forget _).map ((forget₂ _ AddCommMonCat).map f))
      infer_instance
    apply isIso_of_reflects_iso _ (forget _)

end SemimoduleCat

section Bilinear

variable {R : Type*} [CommSemiring R]

namespace SemimoduleCat

/-- Turn a bilinear map into a homomorphism. -/
@[simps!]
/-
**SemimoduleCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `SemimoduleCat`。
形式化陈述：ofHom {X Y : Type v} [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Mod
ule R Y] (f : X ->ₗ[R] Y) : of R X ⟶ of R Y
参数：f : X ->ₗ[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a bilinear map into a homomorphism.
-/
def ofHom₂ {M N P : SemimoduleCat.{u} R} (f : M →ₗ[R] N →ₗ[R] P) :
    M ⟶ of R (N ⟶ P) :=
  ofHom <| homLinearEquiv.symm.toLinearMap ∘ₗ f

/-- Turn a homomorphism into a bilinear map. -/
@[simps!]
/-
**SemimoduleCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `SemimoduleCat.Hom`。
形式化陈述：{R : Type u} → [inst : Semiring R] → {A B : SemimoduleCat R} → A.Hom B → ↑
A →ₗ[R] ↑B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a homomorphism into a bilinear map.
-/
def Hom.hom₂ {M N P : SemimoduleCat.{u} R} (f : M ⟶ (of R (N ⟶ P))) : M →ₗ[R] N →ₗ[R] P :=
  (f ≫ ofHom homLinearEquiv.toLinearMap).hom
/-
**SemimoduleCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `SemimoduleCat.Hom`。
形式化陈述：{R : Type u} → [inst : Semiring R] → {A B : SemimoduleCat R} → A.Hom B → ↑
A →ₗ[R] ↑B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Hom.hom₂_ofHom₂ {M N P : SemimoduleCat.{u} R} (f : M →ₗ[R] N →ₗ[R] P) :
    (ofHom₂ f).hom₂ = f := rfl
/-
**SemimoduleCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `SemimoduleCat`。
形式化陈述：ofHom {X Y : Type v} [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Mod
ule R Y] (f : X ->ₗ[R] Y) : of R X ⟶ of R Y
参数：f : X ->ₗ[R] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofHom₂_hom₂ {M N P : SemimoduleCat.{u} R} (f : M ⟶ of R (N ⟶ P)) :
    ofHom₂ f.hom₂ = f := rfl

end SemimoduleCat

end Bilinear

/-!
`@[simp]` lemmas for `LinearMap.comp` and categorical identities.
-/

/-
**LinearMap.comp_id_semiModuleCat** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {G : SemimoduleCat R} {H : Type u} [i
nst_1 : AddCommMonoid H]   [inst_2 : _root_.Module R H] (f : ↑G →ₗ[R] H), f ∘ₗ S
emimoduleCat.Hom.hom (CategoryTheory.CategoryStruct.id G) = f
参数：f : ↑G →ₗ[R] H；CategoryTheory.CategoryStruct.id G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`@[simp]` lemmas for `LinearMap.comp` and categorical identities.
-/
@[simp] theorem LinearMap.comp_id_semiModuleCat {R} [Semiring R]
    {G : SemimoduleCat.{u} R} {H : Type u} [AddCommMonoid H] [Module R H] (f : G →ₗ[R] H) :
    f.comp (𝟙 G : G ⟶ G).hom = f := by simp
/-
**LinearMap.id_semiModuleCat_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {G : Type u} [inst_1 : AddCommMonoid 
G] [inst_2 : _root_.Module R G]   {H : SemimoduleCat R} (f : G →ₗ[R] ↑H), Semimo
duleCat.Hom.hom (CategoryTheory.CategoryStruct.id H) ∘ₗ f = f
参数：f : G →ₗ[R] ↑H；CategoryTheory.CategoryStruct.id H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem LinearMap.id_semiModuleCat_comp {R} [Semiring R]
    {G : Type u} [AddCommMonoid G] [Module R G] {H : SemimoduleCat.{u} R} (f : G →ₗ[R] H) :
    LinearMap.comp (𝟙 H : H ⟶ H).hom f = f := by simp
