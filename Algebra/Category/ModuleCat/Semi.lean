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

/--
Definition of `SemimoduleCat` / `SemimoduleCat` 的定义

English:
structure SemimoduleCat
  parameters: where
  axioms and operations (4):
    - private(mk) : :
    - carrier : Type v
    - [isAddCommMonoid : AddCommMonoid carrier]
    - [isModule : Module R carrier]

中文:
结构 Semimodule范畴
  参数: where
  公理与运算 (4 个):
    - private(mk) : :
    - carrier : 类型v
    - [isAddCommMonoid : 加法交换幺半群 carrier]
    - [isModule : 模 R carrier]
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (SemimoduleCat.{v} R) (Type v)
  body: ⟨SemimoduleCat.carrier⟩

中文:
实例 :
  签名: CoeSort (Semimodule范畴.{v} R) (类型v)
  定义体: ⟨SemimoduleCat.carrier⟩

Depends on / 依赖: SemimoduleCat, SemimoduleCat.carrier, carrier
-/
instance : CoeSort (SemimoduleCat.{v} R) (Type v) :=
  ⟨SemimoduleCat.carrier⟩

attribute [coe] SemimoduleCat.carrier

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (X : Type v) [AddCommMonoid X] [Module R X]
  body: ⟨X⟩

中文:
缩写 of
  签名: (X : 类型v) [加法交换幺半群 X] [模 R X]
  定义体: ⟨X⟩
-/
abbrev of (X : Type v) [AddCommMonoid X] [Module R X] : SemimoduleCat.{v} R :=
  ⟨X⟩

/--
lemma `coe_of` / 引理 `coe_of`

English:
lemma coe_of
  given: (X : Type v) [Semiring X] [Module R X]
  statement: (of R X : Type v) = X
  proof: rfl

中文:
引理 coe_of
  条件: (X : 类型v) [半环 X] [模 R X]
  结论: (of R X : 类型v) = X
  证明: rfl
-/
lemma coe_of (X : Type v) [Semiring X] [Module R X] : (of R X : Type v) = X :=
  rfl

-- Ensure the roundtrips are reducibly defeq (so tactics like `rw` can see through them).
example (X : Type v) [Semiring X] [Module R X] : (of R X : Type v) = X := by with_reducible rfl
example (M : SemimoduleCat.{v} R) : of R M = M := by with_reducible rfl

variable {R} in
/-- The type of morphisms in `SemimoduleCat R`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (M N : SemimoduleCat.{v} R)
  axioms and operations (2):
    - mk : :
    - hom' : M ->ₗ[R] N

中文:
结构 态射
  参数: (M N : Semimodule范畴.{v} R)
  公理与运算 (2 个):
    - mk : :
    - hom' : M ->ₗ[R] N
-/
structure Hom (M N : SemimoduleCat.{v} R) where
  mk ::
  /-- The underlying linear map. -/
  hom' : M ->ₗ[R] N

/--
Instance `moduleCategory` / 实例 `moduleCategory`

English:
instance moduleCategory
  signature: : Category.{v, max (v + 1) u} (SemimoduleCat.{v} R) where
  body: Hom M N
  id _ := ⟨LinearMap.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 moduleCategory
  签名: : 范畴.{v, 最大值 (v + 1) u} (Semimodule范畴.{v} R) where
  定义体: Hom M N
  id _ := ⟨LinearMap.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance moduleCategory : Category.{v, max (v + 1) u} (SemimoduleCat.{v} R) where
  Hom M N := Hom M N
  id _ := ⟨LinearMap.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory (SemimoduleCat.{v} R) (· ->ₗ[R] ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: 余ncrete范畴 (Semimodule范畴.{v} R) (· ->ₗ[R] ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory (SemimoduleCat.{v} R) (· ->ₗ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

section

variable {R}

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {A B : SemimoduleCat.{v} R} (f : Hom A B)
  body: ConcreteCategory.hom (C := SemimoduleCat R) f

中文:
缩写 态射.hom
  签名: {A B : Semimodule范畴.{v} R} (f : 态射 A B)
  定义体: ConcreteCategory.hom (C := SemimoduleCat R) f
-/
abbrev Hom.hom {A B : SemimoduleCat.{v} R} (f : Hom A B) :=
  ConcreteCategory.hom (C := SemimoduleCat R) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type v} [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y]
  body: ConcreteCategory.ofHom (C := SemimoduleCat R) f

中文:
缩写 ofHom
  签名: {X Y : 类型v} [加法交换幺半群 X] [模 R X] [加法交换幺半群 Y] [模 R Y]
  定义体: ConcreteCategory.ofHom (C := SemimoduleCat R) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, SemimoduleCat
-/
abbrev ofHom {X Y : Type v} [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y]
    (f : X ->ₗ[R] Y) : of R X ⟶ of R Y :=
  ConcreteCategory.ofHom (C := SemimoduleCat R) f

/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (A B : SemimoduleCat.{v} R) (f : Hom A B)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 态射.Simps.hom
  签名: (A B : Semimodule范畴.{v} R) (f : 态射 A B)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (A B : SemimoduleCat.{v} R) (f : Hom A B) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {M : SemimoduleCat.{v} R}
  statement: (𝟙 M : M ⟶ M).hom = LinearMap.id
  proof: rfl

中文:
引理 hom_id
  条件: {M : Semimodule范畴.{v} R}
  结论: (𝟙 M : M ⟶ M).hom = 线性映射.id
  证明: rfl
-/
lemma hom_id {M : SemimoduleCat.{v} R} : (𝟙 M : M ⟶ M).hom = LinearMap.id := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (M : SemimoduleCat.{v} R) (x : M)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (M : Semimodule范畴.{v} R) (x : M)
  证明: by simp

@[simp]
-/
lemma id_apply (M : SemimoduleCat.{v} R) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {M N O : SemimoduleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O)
  proof: rfl

中文:
引理 hom_comp
  条件: {M N O : Semimodule范畴.{v} R} (f : M ⟶ N) (g : N ⟶ O)
  证明: rfl
-/
lemma hom_comp {M N O : SemimoduleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {M N O : SemimoduleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) (x : M)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {M N O : Semimodule范畴.{v} R} (f : M ⟶ N) (g : N ⟶ O) (x : M)
  证明: by simp

@[ext]
-/
lemma comp_apply {M N O : SemimoduleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) (x : M) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {M N : SemimoduleCat.{v} R} {f g : M ⟶ N} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

中文:
引理 hom_ext
  条件: {M N : Semimodule范畴.{v} R} {f g : M ⟶ N} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

/--
lemma `hom_bijective` / 引理 `hom_bijective`

English:
lemma hom_bijective
  given: {M N : SemimoduleCat.{v} R}
  proof: by cases f; cases g; simpa using! h
  right f := ⟨⟨f⟩, rfl⟩

中文:
引理 hom_bijective
  条件: {M N : Semimodule范畴.{v} R}
  证明: by cases f; cases g; simpa using! h
  right f := ⟨⟨f⟩, rfl⟩
-/
lemma hom_bijective {M N : SemimoduleCat.{v} R} :
    Function.Bijective (Hom.hom : (M ⟶ N) -> (M ->ₗ[R] N)) where
  left f g h := by cases f; cases g; simpa using! h
  right f := ⟨⟨f⟩, rfl⟩

/--
lemma `hom_injective` / 引理 `hom_injective`

English:
lemma hom_injective
  given: {M N : SemimoduleCat.{v} R}
  proof: hom_bijective.injective

中文:
引理 hom_injective
  条件: {M N : Semimodule范畴.{v} R}
  证明: hom_bijective.injective

Depends on / 依赖: hom_bijective, hom_bijective.injective, injective
-/
lemma hom_injective {M N : SemimoduleCat.{v} R} :
    Function.Injective (Hom.hom : (M ⟶ N) -> (M ->ₗ[R] N)) :=
  hom_bijective.injective

/--
lemma `hom_surjective` / 引理 `hom_surjective`

English:
lemma hom_surjective
  given: {M N : SemimoduleCat.{v} R}
  proof: hom_bijective.surjective

@[simp]

中文:
引理 hom_surjective
  条件: {M N : Semimodule范畴.{v} R}
  证明: hom_bijective.surjective

@[simp]

Depends on / 依赖: hom_bijective, hom_bijective.surjective, surjective
-/
lemma hom_surjective {M N : SemimoduleCat.{v} R} :
    Function.Surjective (Hom.hom : (M ⟶ N) -> (M ->ₗ[R] N)) :=
  hom_bijective.surjective

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  statement: {X Y : Type v} [AddCommMonoid X] [Module R X] [AddCommMonoid Y]
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  结论: {X Y : 类型v} [加法交换幺半群 X] [模 R X] [加法交换幺半群 Y]
  证明: rfl

@[simp]
-/
lemma hom_ofHom {X Y : Type v} [AddCommMonoid X] [Module R X] [AddCommMonoid Y]
    [Module R Y] (f : X ->ₗ[R] Y) : (ofHom f).hom = f := rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {M N : SemimoduleCat.{v} R} (f : M ⟶ N)
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {M N : Semimodule范畴.{v} R} (f : M ⟶ N)
  证明: rfl

@[simp]
-/
lemma ofHom_hom {M N : SemimoduleCat.{v} R} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {M : Type v} [AddCommMonoid M] [Module R M]
  statement: ofHom LinearMap.id = 𝟙 (of R M)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {M : 类型v} [加法交换幺半群 M] [模 R M]
  结论: ofHom 线性映射.id = 𝟙 (of R M)
  证明: rfl

@[simp]
-/
lemma ofHom_id {M : Type v} [AddCommMonoid M] [Module R M] : ofHom LinearMap.id = 𝟙 (of R M) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {M N O : Type v} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O] [Module R M]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {M N O : 类型v} [加法交换幺半群 M] [加法交换幺半群 N] [加法交换幺半群 O] [模 R M]
  证明: rfl
-/
lemma ofHom_comp {M N O : Type v} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O] [Module R M]
    [Module R N] [Module R O] (f : M ->ₗ[R] N) (g : N ->ₗ[R] O) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  statement: {M N : Type v} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  proof: rfl

中文:
引理 ofHom_apply
  结论: {M N : 类型v} [加法交换幺半群 M] [加法交换幺半群 N] [模 R M] [模 R N]
  证明: rfl
-/
lemma ofHom_apply {M N : Type v} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (f : M ->ₗ[R] N) (x : M) : ofHom f x = f x := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {M N : SemimoduleCat.{v} R} (e : M ≅ N) (x : M)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {M N : Semimodule范畴.{v} R} (e : M ≅ N) (x : M)
  结论: e.inv (e.hom x) = x
  证明: by
  simp
-/
lemma inv_hom_apply {M N : SemimoduleCat.{v} R} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {M N : SemimoduleCat.{v} R} (e : M ≅ N) (x : N)
  statement: e.hom (e.inv x) = x
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {M N : Semimodule范畴.{v} R} (e : M ≅ N) (x : N)
  结论: e.hom (e.inv x) = x
  证明: by
  simp
-/
lemma hom_inv_apply {M N : SemimoduleCat.{v} R} (e : M ≅ N) (x : N) : e.hom (e.inv x) = x := by
  simp

/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: {M N : SemimoduleCat.{v} R}
  body: Hom.hom
  invFun := ofHom

中文:
定义 homEquiv
  签名: {M N : Semimodule范畴.{v} R}
  定义体: Hom.hom
  invFun := ofHom

Depends on / 依赖: Hom.hom
-/
def homEquiv {M N : SemimoduleCat.{v} R} : (M ⟶ N) ≃ (M ->ₗ[R] N) where
  toFun := Hom.hom
  invFun := ofHom

end

/--
lemma `forget_obj` / 引理 `forget_obj`

English:
lemma forget_obj
  given: {M : SemimoduleCat.{v} R}
  statement: ((forget (SemimoduleCat.{v} R)).obj M : Type _) = M
  proof: rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-02-25")]

中文:
引理 forget_obj
  条件: {M : Semimodule范畴.{v} R}
  结论: ((forget (Semimodule范畴.{v} R)).obj M : 类型 _) = M
  证明: rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-02-25")]
-/
lemma forget_obj {M : SemimoduleCat.{v} R} : ((forget (SemimoduleCat.{v} R)).obj M : Type _) = M :=
  rfl

@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-02-25")]
/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: {M N : SemimoduleCat.{v} R} (f : M ⟶ N)
  proof: rfl

中文:
引理 forget_map
  条件: {M N : Semimodule范畴.{v} R} (f : M ⟶ N)
  证明: rfl
-/
lemma forget_map {M N : SemimoduleCat.{v} R} (f : M ⟶ N) :
    (forget (SemimoduleCat.{v} R)).map f = (f : _ -> _) :=
  rfl

/--
Instance `hasForgetToAddCommMonoid` / 实例 `hasForgetToAddCommMonoid`

English:
instance hasForgetToAddCommMonoid
  signature: : HasForget₂ (SemimoduleCat R) AddCommMonCat where
  body: { obj := fun M => .of M
      map := fun f => AddCommMonCat.ofHom f.hom.toAddMonoidHom }

@[simp]

中文:
实例 hasForgetToAddCommMonoid
  签名: : 有Forget₂ (Semimodule范畴 R) 加法交换幺半群范畴 where
  定义体: { obj := fun M => .of M
      map := fun f => AddCommMonCat.ofHom f.hom.toAddMonoidHom }

@[simp]

Depends on / 依赖: AddCommMonCat, AddCommMonCat.ofHom, f.hom.toAddMonoidHom, toAddMonoidHom
-/
instance hasForgetToAddCommMonoid : HasForget₂ (SemimoduleCat R) AddCommMonCat where
  forget₂ :=
    { obj := fun M => .of M
      map := fun f => AddCommMonCat.ofHom f.hom.toAddMonoidHom }

@[simp]
/--
theorem `forget₂_obj` / 定理 `forget₂_obj`

English:
theorem forget₂_obj
  given: (X : SemimoduleCat R)
  proof: rfl

中文:
定理 forget₂_obj
  条件: (X : Semimodule范畴 R)
  证明: rfl
-/
theorem forget₂_obj (X : SemimoduleCat R) :
    (forget₂ (SemimoduleCat R) AddCommMonCat).obj X = .of X :=
  rfl

/--
theorem `forget₂_obj_moduleCat_of` / 定理 `forget₂_obj_moduleCat_of`

English:
theorem forget₂_obj_moduleCat_of
  given: (X : Type v) [AddCommMonoid X] [Module R X]
  proof: rfl

@[simp]

中文:
定理 forget₂_obj_moduleCat_of
  条件: (X : 类型v) [加法交换幺半群 X] [模 R X]
  证明: rfl

@[simp]
-/
theorem forget₂_obj_moduleCat_of (X : Type v) [AddCommMonoid X] [Module R X] :
    (forget₂ (SemimoduleCat R) AddCommMonCat).obj (of R X) = .of X :=
  rfl

@[simp]
/--
theorem `forget₂_map` / 定理 `forget₂_map`

English:
theorem forget₂_map
  given: (X Y : SemimoduleCat R) (f : X ⟶ Y)
  proof: rfl

中文:
定理 forget₂_map
  条件: (X Y : Semimodule范畴 R) (f : X ⟶ Y)
  证明: rfl
-/
theorem forget₂_map (X Y : SemimoduleCat R) (f : X ⟶ Y) :
    (forget₂ (SemimoduleCat R) AddCommMonCat).map f = AddCommMonCat.ofHom f.hom :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (SemimoduleCat R)
  body: ⟨of R PUnit⟩

中文:
实例 :
  签名: 可居 (Semimodule范畴 R)
  定义体: ⟨of R PUnit⟩
-/
instance : Inhabited (SemimoduleCat R) :=
  ⟨of R PUnit⟩

/--
theorem `of_coe` / 定理 `of_coe`

English:
theorem of_coe
  given: (X : SemimoduleCat R)
  statement: of R X = X
  proof: rfl

中文:
定理 of_coe
  条件: (X : Semimodule范畴 R)
  结论: of R X = X
  证明: rfl
-/
@[simp] theorem of_coe (X : SemimoduleCat R) : of R X = X := rfl

variable {R}

/--
theorem `isZero_of_subsingleton` / 定理 `isZero_of_subsingleton`

English:
theorem isZero_of_subsingleton
  given: (M : SemimoduleCat R) [Subsingleton M]
  statement: IsZero M where
  proof: ⟨⟨⟨ofHom (0 : M ->ₗ[R] X)⟩, fun f => by
    ext x
    rw [Subsingleton.elim x (0 : M)]
    simp⟩⟩
  unique_from X := ⟨⟨⟨ofHom (0 : X ->ₗ[R] M)⟩, fun f => by
    ext x
    subsingleton⟩⟩

中文:
定理 isZero_of_subsingleton
  条件: (M : Semimodule范畴 R) [子单例 M]
  结论: 是零 M where
  证明: ⟨⟨⟨ofHom (0 : M ->ₗ[R] X)⟩, fun f => by
    ext x
    rw [Subsingleton.elim x (0 : M)]
    simp⟩⟩
  unique_from X := ⟨⟨⟨ofHom (0 : X ->ₗ[R] M)⟩, fun f => by
    ext x
    subsingleton⟩⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, subsingleton, unique_from
-/
theorem isZero_of_subsingleton (M : SemimoduleCat R) [Subsingleton M] : IsZero M where
  unique_to X := ⟨⟨⟨ofHom (0 : M ->ₗ[R] X)⟩, fun f => by
    ext x
    rw [Subsingleton.elim x (0 : M)]
    simp⟩⟩
  unique_from X := ⟨⟨⟨ofHom (0 : X ->ₗ[R] M)⟩, fun f => by
    ext x
    subsingleton⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasZeroObject (SemimoduleCat.{v} R)
  body: ⟨⟨of R PUnit, isZero_of_subsingleton _⟩⟩

中文:
实例 :
  签名: 有ZeroObject (Semimodule范畴.{v} R)
  定义体: ⟨⟨of R PUnit, isZero_of_subsingleton _⟩⟩

Depends on / 依赖: isZero_of_subsingleton
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
/--
Definition of `LinearEquiv.toModuleIsoₛ` / `LinearEquiv.toModuleIsoₛ` 的定义

English:
definition LinearEquiv.toModuleIsoₛ
  signature: {g₁ : AddCommMonoid X₁} {g₂ : AddCommMonoid X₂} {m₁ : Module R X₁}
  body: ofHom (e : X₁ ->ₗ[R] X₂)
  inv := ofHom (e.symm : X₂ ->ₗ[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv

中文:
定义 线性等价.toModuleIsoₛ
  签名: {g₁ : 加法交换幺半群 X₁} {g₂ : 加法交换幺半群 X₂} {m₁ : 模 R X₁}
  定义体: ofHom (e : X₁ ->ₗ[R] X₂)
  inv := ofHom (e.symm : X₂ ->ₗ[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv
-/
def LinearEquiv.toModuleIsoₛ {g₁ : AddCommMonoid X₁} {g₂ : AddCommMonoid X₂} {m₁ : Module R X₁}
    {m₂ : Module R X₂} (e : X₁ ≃ₗ[R] X₂) : SemimoduleCat.of R X₁ ≅ SemimoduleCat.of R X₂ where
  hom := ofHom (e : X₁ ->ₗ[R] X₂)
  inv := ofHom (e.symm : X₂ ->ₗ[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv

namespace CategoryTheory.Iso

/--
Definition of `toLinearEquivₛ` / `toLinearEquivₛ` 的定义

English:
definition toLinearEquivₛ
  signature: {X Y : SemimoduleCat R} (i : X ≅ Y)
  body: LinearEquiv.ofLinearMap i.hom.hom i.inv.hom (by aesop) (by aesop)

中文:
定义 toLinearEquivₛ
  签名: {X Y : Semimodule范畴 R} (i : X ≅ Y)
  定义体: LinearEquiv.ofLinearMap i.hom.hom i.inv.hom (by aesop) (by aesop)

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, i.hom.hom, i.inv.hom, ofLinearMap
-/
def toLinearEquivₛ {X Y : SemimoduleCat R} (i : X ≅ Y) : X ≃ₗ[R] Y :=
  LinearEquiv.ofLinearMap i.hom.hom i.inv.hom (by aesop) (by aesop)

end CategoryTheory.Iso

/-- linear equivalences between `Module`s are the same as (isomorphic to) isomorphisms
in `SemimoduleCat` -/
@[simps]
/--
Definition of `linearEquivIsoModuleIsoₛ` / `linearEquivIsoModuleIsoₛ` 的定义

English:
definition linearEquivIsoModuleIsoₛ
  signature: {X Y : Type u} [AddCommMonoid X] [AddCommMonoid Y] [Module R X]
  body: ↾fun e => e.toModuleIsoₛ
  inv := ↾fun i => i.toLinearEquivₛ

中文:
定义 linearEquivIsoModuleIsoₛ
  签名: {X Y : 类型u} [加法交换幺半群 X] [加法交换幺半群 Y] [模 R X]
  定义体: ↾fun e => e.toModuleIsoₛ
  inv := ↾fun i => i.toLinearEquivₛ

Depends on / 依赖: LinearMap, LinearMap.range, e.toModuleIso, f.hom, subtype
-/
def linearEquivIsoModuleIsoₛ {X Y : Type u} [AddCommMonoid X] [AddCommMonoid Y] [Module R X]
    [Module R Y] : (X ≃ₗ[R] Y) ≅
      ((SemimoduleCat.of R X) ≅ (SemimoduleCat.of R Y)) where
  hom := ↾fun e => e.toModuleIsoₛ
  inv := ↾fun i => i.toLinearEquivₛ

end

namespace SemimoduleCat

section AddCommMonoid

variable {M N : SemimoduleCat.{v} R}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (M ⟶ N)
  body: ⟨f.hom + g.hom⟩

中文:
实例 :
  签名: 加法 (M ⟶ N)
  定义体: ⟨f.hom + g.hom⟩

Depends on / 依赖: f.hom, g.hom
-/
instance : Add (M ⟶ N) where
  add f g := ⟨f.hom + g.hom⟩

/--
lemma `hom_add` / 引理 `hom_add`

English:
lemma hom_add
  given: (f g : M ⟶ N)
  statement: (f + g).hom = f.hom + g.hom
  proof: rfl

中文:
引理 hom_add
  条件: (f g : M ⟶ N)
  结论: (f + g).hom = f.hom + g.hom
  证明: rfl
-/
@[simp] lemma hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (M ⟶ N)
  body: ⟨0⟩

中文:
实例 :
  签名: 零 (M ⟶ N)
  定义体: ⟨0⟩
-/
instance : Zero (M ⟶ N) where
  zero := ⟨0⟩

/--
lemma `hom_zero` / 引理 `hom_zero`

English:
lemma hom_zero
  statement: (0 : M ⟶ N).hom = 0
  proof: rfl

中文:
引理 hom_zero
  结论: (0 : M ⟶ N).hom = 0
  证明: rfl

Depends on / 依赖: Classical, Classical.indefiniteDesc, Classical.indefiniteDescription, indefiniteDesc, indefiniteDescription, infer_instance, map_add, map_smul, mono_iff_injective, simp_rw
-/
@[simp] lemma hom_zero : (0 : M ⟶ N).hom = 0 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Nat (M ⟶ N)
  body: ⟨n • f.hom⟩

中文:
实例 :
  签名: 标量乘法 自然数 (M ⟶ N)
  定义体: ⟨n • f.hom⟩

Depends on / 依赖: Classical, Classical.indefiniteDescription, f.hom, indefiniteDescription
-/
instance : SMul Nat (M ⟶ N) where
  smul n f := ⟨n • f.hom⟩

/--
lemma `hom_nsmul` / 引理 `hom_nsmul`

English:
lemma hom_nsmul
  given: (n : Nat) (f : M ⟶ N)
  statement: (n • f).hom = n • f.hom
  proof: rfl

中文:
引理 hom_nsmul
  条件: (n : 自然数) (f : M ⟶ N)
  结论: (n • f).hom = n • f.hom
  证明: rfl
-/
@[simp] lemma hom_nsmul (n : Nat) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

-- There is no `ℤ`-smul operation on a general semimodule!
@[deprecated (since := "2026-01-06")]
alias hom_zsmul := hom_nsmul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (M ⟶ N)
  body: Function.Injective.addCommMonoid Hom.hom hom_injective rfl (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 :
  签名: 加法交换幺半群 (M ⟶ N)
  定义体: Function.Injective.addCommMonoid Hom.hom hom_injective rfl (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: Function, Function.Injective.addCommMonoid, Hom.hom, Injective, addCommMonoid, hom_injective
-/
instance : AddCommMonoid (M ⟶ N) :=
  Function.Injective.addCommMonoid Hom.hom hom_injective rfl (fun _ _ => rfl) (fun _ _ => rfl)

/--
lemma `hom_sum` / 引理 `hom_sum`

English:
lemma hom_sum
  given: {ι : Type*} (f : ι -> (M ⟶ N)) (s : Finset ι)
  proof: map_sum ({ toFun := SemimoduleCat.Hom.hom, map_zero' := SemimoduleCat.hom_zero,
             map_add' := hom_add } : (M ⟶ N) ->+ (M ->ₗ[R] N)) _ _

中文:
引理 hom_sum
  条件: {ι : 类型} (f : ι -> (M ⟶ N)) (s : 有限集 ι)
  证明: map_sum ({ toFun := SemimoduleCat.Hom.hom, map_zero' := SemimoduleCat.hom_zero,
             map_add' := hom_add } : (M ⟶ N) ->+ (M ->ₗ[R] N)) _ _
-/
@[simp] lemma hom_sum {ι : Type*} (f : ι -> (M ⟶ N)) (s : Finset ι) :
    (∑ i in s, f i).hom = ∑ i in s, (f i).hom :=
  map_sum ({ toFun := SemimoduleCat.Hom.hom, map_zero' := SemimoduleCat.hom_zero,
             map_add' := hom_add } : (M ⟶ N) ->+ (M ->ₗ[R] N)) _ _


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasZeroMorphisms (SemimoduleCat.{v} R)

中文:
实例 :
  签名: 有ZeroMorphisms (Semimodule范畴.{v} R)
-/
instance : HasZeroMorphisms (SemimoduleCat.{v} R) where

/-- `SemimoduleCat.Hom.hom` bundled as an additive equivalence. -/
@[simps!]
/--
Definition of `homAddEquiv` / `homAddEquiv` 的定义

English:
definition homAddEquiv
  signature: : (M ⟶ N) ≃+ (M ->ₗ[R] N)
  body: { homEquiv with
    map_add' := fun _ _ => rfl }

中文:
定义 homAddEquiv
  签名: : (M ⟶ N) ≃+ (M ->ₗ[R] N)
  定义体: { homEquiv with
    map_add' := fun _ _ => rfl }

Depends on / 依赖: homEquiv, map_add
-/
def homAddEquiv : (M ⟶ N) ≃+ (M ->ₗ[R] N) :=
  { homEquiv with
    map_add' := fun _ _ => rfl }

/--
theorem `subsingleton_of_isZero` / 定理 `subsingleton_of_isZero`

English:
theorem subsingleton_of_isZero
  given: (h : IsZero M)
  statement: Subsingleton M
  proof: by
  refine subsingleton_of_forall_eq 0 (fun x => ?_)
  rw [← LinearMap.id_apply (R := R) x]; rw [← SemimoduleCat.hom_id]
  simp only [(CategoryTheory.Limits.IsZero.iff_id_eq_zero M).mp h, hom_zero, LinearMap.zero_apply]

中文:
定理 subsingleton_of_isZero
  条件: (h : 是零 M)
  结论: 子单例 M
  证明: by
  refine subsingleton_of_forall_eq 0 (fun x => ?_)
  rw [← LinearMap.id_apply (R := R) x]; rw [← SemimoduleCat.hom_id]
  simp only [(CategoryTheory.Limits.IsZero.iff_id_eq_zero M).mp h, hom_zero, LinearMap.zero_apply]

Depends on / 依赖: CategoryTheory, CategoryTheory.Limits.IsZero.iff_id_eq_zero, IsZero, Limits, LinearMap, LinearMap.id_apply, LinearMap.zero_apply, SemimoduleCat, SemimoduleCat.hom_id, hom_id, hom_zero, id_apply, iff_id_eq_zero, subsingleton_of_forall_eq, zero_apply
-/
theorem subsingleton_of_isZero (h : IsZero M) : Subsingleton M := by
  refine subsingleton_of_forall_eq 0 (fun x => ?_)
  rw [← LinearMap.id_apply (R := R) x]; rw [← SemimoduleCat.hom_id]
  simp only [(CategoryTheory.Limits.IsZero.iff_id_eq_zero M).mp h, hom_zero, LinearMap.zero_apply]

/--
lemma `isZero_iff_subsingleton` / 引理 `isZero_iff_subsingleton`

English:
lemma isZero_iff_subsingleton
  statement: IsZero M ↔ Subsingleton M where
  proof: subsingleton_of_isZero
  mpr _ := isZero_of_subsingleton M

@[simp]

中文:
引理 isZero_iff_subsingleton
  结论: 是零 M ↔ 子单例 M where
  证明: subsingleton_of_isZero
  mpr _ := isZero_of_subsingleton M

@[simp]

Depends on / 依赖: subsingleton_of_isZero
-/
lemma isZero_iff_subsingleton : IsZero M ↔ Subsingleton M where
  mp := subsingleton_of_isZero
  mpr _ := isZero_of_subsingleton M

@[simp]
/--
lemma `isZero_of_iff_subsingleton` / 引理 `isZero_of_iff_subsingleton`

English:
lemma isZero_of_iff_subsingleton
  given: {M : Type*} [AddCommMonoid M] [Module R M]
  proof: isZero_iff_subsingleton

中文:
引理 isZero_of_iff_subsingleton
  条件: {M : 类型} [加法交换幺半群 M] [模 R M]
  证明: isZero_iff_subsingleton

Depends on / 依赖: isZero_iff_subsingleton
-/
lemma isZero_of_iff_subsingleton {M : Type*} [AddCommMonoid M] [Module R M] :
    IsZero (of R M) ↔ Subsingleton M := isZero_iff_subsingleton

end AddCommMonoid

section SMul

variable {M N : SemimoduleCat.{v} R}
variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul S (M ⟶ N)
  body: ⟨c • f.hom⟩

中文:
实例 :
  签名: 标量乘法 S (M ⟶ N)
  定义体: ⟨c • f.hom⟩

Depends on / 依赖: f.hom
-/
instance : SMul S (M ⟶ N) where
  smul c f := ⟨c • f.hom⟩

/--
lemma `hom_smul` / 引理 `hom_smul`

English:
lemma hom_smul
  given: (s : S) (f : M ⟶ N)
  statement: (s • f).hom = s • f.hom
  proof: rfl

中文:
引理 hom_smul
  条件: (s : S) (f : M ⟶ N)
  结论: (s • f).hom = s • f.hom
  证明: rfl
-/
@[simp] lemma hom_smul (s : S) (f : M ⟶ N) : (s • f).hom = s • f.hom := rfl

end SMul

section Module

variable {M N : SemimoduleCat.{v} R} {S : Type*} [Semiring S] [Module S N] [SMulCommClass R S N]

/--
Instance `Hom.instModule` / 实例 `Hom.instModule`

English:
instance Hom.instModule
  signature: : Module S (M ⟶ N)
  body: Function.Injective.module S
    { toFun := Hom.hom, map_zero' := hom_zero, map_add' := hom_add }
    hom_injective
    (fun _ _ => rfl)

中文:
实例 态射.instModule
  签名: : 模 S (M ⟶ N)
  定义体: Function.Injective.module S
    { toFun := Hom.hom, map_zero' := hom_zero, map_add' := hom_add }
    hom_injective
    (fun _ _ => rfl)
-/
instance Hom.instModule : Module S (M ⟶ N) :=
  Function.Injective.module S
    { toFun := Hom.hom, map_zero' := hom_zero, map_add' := hom_add }
    hom_injective
    (fun _ _ => rfl)

/-- `SemimoduleCat.Hom.hom` bundled as a linear equivalence. -/
@[simps]
/--
Definition of `homLinearEquiv` / `homLinearEquiv` 的定义

English:
definition homLinearEquiv
  signature: : (M ⟶ N) ≃ₗ[S] (M ->ₗ[R] N)
  body: { homAddEquiv with
    map_smul' := fun _ _ => rfl }

中文:
定义 homLinearEquiv
  签名: : (M ⟶ N) ≃ₗ[S] (M ->ₗ[R] N)
  定义体: { homAddEquiv with
    map_smul' := fun _ _ => rfl }

Depends on / 依赖: homAddEquiv, map_smul
-/
def homLinearEquiv : (M ⟶ N) ≃ₗ[S] (M ->ₗ[R] N) :=
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
scoped instance : Module S₀ M := Module.compHom _ (algebraMap S₀ S)

scoped instance : IsScalarTower S₀ S M where
  smul_assoc _ _ _ := by rw [Algebra.smul_def, mul_smul]; rfl

scoped instance : SMulCommClass S S₀ M where
  smul_comm s s₀ n :=
    show s • algebraMap S₀ S s₀ • n = algebraMap S₀ S s₀ • s • n by
    rw [← smul_assoc]; rw [smul_eq_mul]; rw [← Algebra.commutes]; rw [mul_smul]

/- TODO: generalize `Functor.Linear`, see #28826.
Let `S` be an `S₀`-algebra. Then the category of `S`-modules is `S₀`-linear.
scoped instance instLinear : Linear S₀ (SemimoduleCat.{v} S) where
  smul_comp _ M N s₀ f g := by ext; simp -/

end Algebra

section

variable {S : Type u} [CommSemiring S]

/- TODO: generalize `Functor.Linear`, see #28826.
instance : Linear S (SemimoduleCat.{v} S) := SemimoduleCat.Algebra.instLinear -/

variable {X Y X' Y' : SemimoduleCat.{v} S}

/--
theorem `Iso.homCongr_eq_arrowCongr` / 定理 `Iso.homCongr_eq_arrowCongr`

English:
theorem Iso.homCongr_eq_arrowCongr
  given: (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y)
  proof: rfl

中文:
定理 同构.homCongr_eq_arrowCongr
  条件: (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y)
  证明: rfl
-/
theorem Iso.homCongr_eq_arrowCongr (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y) :
    Iso.homCongr i j f = ⟨LinearEquiv.arrowCongr i.toLinearEquivₛ j.toLinearEquivₛ f.hom⟩ :=
  rfl

/--
theorem `Iso.conj_eq_conj` / 定理 `Iso.conj_eq_conj`

English:
theorem Iso.conj_eq_conj
  given: (i : X ≅ X') (f : End X)
  proof: rfl

中文:
定理 同构.conj_eq_conj
  条件: (i : X ≅ X') (f : End X)
  证明: rfl
-/
theorem Iso.conj_eq_conj (i : X ≅ X') (f : End X) :
    Iso.conj i f = ⟨LinearEquiv.conj i.toLinearEquivₛ f.hom⟩ :=
  rfl

end

end


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget (SemimoduleCat.{v} R)).ReflectsIsomorphisms
  body: (inferInstance : IsIso ((LinearEquiv.mk f.hom
      (asIso ((forget (SemimoduleCat R)).map f)).toEquiv.invFun
      (Equiv.left_inv _) (Equiv.right_inv _)).toModuleIsoₛ).hom)

中文:
实例 :
  签名: (forget (Semimodule范畴.{v} R)).反映同构
  定义体: (inferInstance : IsIso ((LinearEquiv.mk f.hom
      (asIso ((forget (SemimoduleCat R)).map f)).toEquiv.invFun
      (Equiv.left_inv _) (Equiv.right_inv _)).toModuleIsoₛ).hom)

Depends on / 依赖: Equiv.left_inv, Equiv.right_inv, LinearEquiv, LinearEquiv.mk, SemimoduleCat, f.hom, forget, invFun, left_inv, right_inv, toEquiv, toEquiv.invFun
-/
instance : (forget (SemimoduleCat.{v} R)).ReflectsIsomorphisms where
  reflects f _ :=
    (inferInstance : IsIso ((LinearEquiv.mk f.hom
      (asIso ((forget (SemimoduleCat R)).map f)).toEquiv.invFun
      (Equiv.left_inv _) (Equiv.right_inv _)).toModuleIsoₛ).hom)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (SemimoduleCat.{v} R) AddCommMonCat.{v}).ReflectsIsomorphisms
  body: by
    have : IsIso ((forget _).map f) := by
      change IsIso ((forget _).map ((forget₂ _ AddCommMonCat).map f))
      infer_instance
    apply isIso_of_reflects_iso _ (forget _)

中文:
实例 :
  签名: (forget₂ (Semimodule范畴.{v} R) 加法交换幺半群范畴.{v}).反映同构
  定义体: by
    have : IsIso ((forget _).map f) := by
      change IsIso ((forget _).map ((forget₂ _ AddCommMonCat).map f))
      infer_instance
    apply isIso_of_reflects_iso _ (forget _)

Depends on / 依赖: AddCommMonCat, forget, infer_instance, isIso_of_reflects_iso
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
/--
Definition of `ofHom₂` / `ofHom₂` 的定义

English:
definition ofHom₂
  signature: {M N P : SemimoduleCat.{u} R} (f : M ->ₗ[R] N ->ₗ[R] P)
  body: ofHom homLinearEquiv.symm.toLinearMap ∘ₗ f

中文:
定义 ofHom₂
  签名: {M N P : Semimodule范畴.{u} R} (f : M ->ₗ[R] N ->ₗ[R] P)
  定义体: ofHom homLinearEquiv.symm.toLinearMap ∘ₗ f

Depends on / 依赖: homLinearEquiv, homLinearEquiv.symm.toLinearMap, toLinearMap
-/
def ofHom₂ {M N P : SemimoduleCat.{u} R} (f : M ->ₗ[R] N ->ₗ[R] P) :
    M ⟶ of R (N ⟶ P) :=
ofHom homLinearEquiv.symm.toLinearMap ∘ₗ f

/-- Turn a homomorphism into a bilinear map. -/
@[simps!]
/--
Definition of `Hom.hom₂` / `Hom.hom₂` 的定义

English:
definition Hom.hom₂
  signature: {M N P : SemimoduleCat.{u} R} (f : M ⟶ (of R (N ⟶ P)))
  body: (f ≫ ofHom homLinearEquiv.toLinearMap).hom

中文:
定义 态射.hom₂
  签名: {M N P : Semimodule范畴.{u} R} (f : M ⟶ (of R (N ⟶ P)))
  定义体: (f ≫ ofHom homLinearEquiv.toLinearMap).hom
-/
def Hom.hom₂ {M N P : SemimoduleCat.{u} R} (f : M ⟶ (of R (N ⟶ P))) : M ->ₗ[R] N ->ₗ[R] P :=
  (f ≫ ofHom homLinearEquiv.toLinearMap).hom

/--
lemma `Hom.hom₂_ofHom₂` / 引理 `Hom.hom₂_ofHom₂`

English:
lemma Hom.hom₂_ofHom₂
  given: {M N P : SemimoduleCat.{u} R} (f : M ->ₗ[R] N ->ₗ[R] P)
  proof: rfl

中文:
引理 态射.hom₂_ofHom₂
  条件: {M N P : Semimodule范畴.{u} R} (f : M ->ₗ[R] N ->ₗ[R] P)
  证明: rfl
-/
@[simp] lemma Hom.hom₂_ofHom₂ {M N P : SemimoduleCat.{u} R} (f : M ->ₗ[R] N ->ₗ[R] P) :
    (ofHom₂ f).hom₂ = f := rfl

/--
lemma `ofHom₂_hom₂` / 引理 `ofHom₂_hom₂`

English:
lemma ofHom₂_hom₂
  given: {M N P : SemimoduleCat.{u} R} (f : M ⟶ of R (N ⟶ P))
  proof: rfl

中文:
引理 ofHom₂_hom₂
  条件: {M N P : Semimodule范畴.{u} R} (f : M ⟶ of R (N ⟶ P))
  证明: rfl
-/
@[simp] lemma ofHom₂_hom₂ {M N P : SemimoduleCat.{u} R} (f : M ⟶ of R (N ⟶ P)) :
    ofHom₂ f.hom₂ = f := rfl

end SemimoduleCat

end Bilinear


/--
theorem `LinearMap.comp_id_semiModuleCat` / 定理 `LinearMap.comp_id_semiModuleCat`

English:
theorem LinearMap.comp_id_semiModuleCat
  statement: {R} [Semiring R]
  proof: by simp

中文:
定理 线性映射.comp_id_semiModuleCat
  结论: {R} [半环 R]
  证明: by simp
-/
@[simp] theorem LinearMap.comp_id_semiModuleCat {R} [Semiring R]
    {G : SemimoduleCat.{u} R} {H : Type u} [AddCommMonoid H] [Module R H] (f : G ->ₗ[R] H) :
    f.comp (𝟙 G : G ⟶ G).hom = f := by simp

/--
theorem `LinearMap.id_semiModuleCat_comp` / 定理 `LinearMap.id_semiModuleCat_comp`

English:
theorem LinearMap.id_semiModuleCat_comp
  statement: {R} [Semiring R]
  proof: by simp

中文:
定理 线性映射.id_semiModuleCat_comp
  结论: {R} [半环 R]
  证明: by simp
-/
@[simp] theorem LinearMap.id_semiModuleCat_comp {R} [Semiring R]
    {G : Type u} [AddCommMonoid G] [Module R G] {H : SemimoduleCat.{u} R} (f : G ->ₗ[R] H) :
    LinearMap.comp (𝟙 H : H ⟶ H).hom f = f := by simp
