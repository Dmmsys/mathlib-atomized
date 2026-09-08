/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Richard Hill
-/
module

public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.RepresentationTheory.Continuous.Basic

/-!
# Topological representations

This file defines the category `TopRep k G` of topological representations of a monoid `G` over a
topological ring `k`, and shows that it is equivalent to the category `Action (TopModuleCat k) G`.

For a topological group `G` we define the invariants functor `TopRep.invariantsFunctor`, the
coinduction functor `TopRep.coind₁Functor`, the restriction functor `TopRep.resFunctor` along a
group homomorphism `φ : H →* G`, and the morphism `TopRep.invariantsResMap φ f` between invariant
submodules induced by a morphism `f : res φ X ⟶ Y`.
-/

@[expose] public section

universe w u v

/-- The category of topological representations of a monoid `G` over a topological ring `k`, and
their morphisms. -/
/-
**TopRep** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(k : Type u) → (G : Type v) → [Ring k] → [TopologicalSpace k] → [Monoid G]
 → Type (max (max u v) (w + 1))
参数：max u v；w + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of topological representations of a monoid `G` over a topological r
ing `k`, and
their morphisms.
-/
structure TopRep (k : Type u) (G : Type v) [Ring k] [TopologicalSpace k] [Monoid G] where
  private mk ::
  /-- the underlying type of an object in `TopRep k G` -/
  V : Type w
  [hV1 : AddCommGroup V]
  [hV2 : Module k V]
  [hV3 : TopologicalSpace V]
  [hV4 : IsTopologicalAddGroup V]
  [hV5 : ContinuousSMul k V]
  /-- the underlying continuous representation of an object in `TopRep k G` -/
  ρ : ContRepresentation k G V

namespace TopRep

variable {k : Type u} {G : Type v} {X Y : Type w} [TopologicalSpace k] [Ring k]
  [Monoid G] [AddCommGroup X] [Module k X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul k X] [AddCommGroup Y] [Module k Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul k Y] {ρ : ContRepresentation k G X}
  {σ : ContRepresentation k G Y}

open ContRepresentation CategoryTheory

attribute [instance] hV1 hV2 hV3 hV4 hV5

initialize_simps_projections TopRep (-hV1, -hV2)

/-
**TopRep.** 是 Mathlib 中的一个实例，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (TopRep k G) (Type w) := ⟨TopRep.V⟩

attribute [coe] V

variable (ρ) in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object in the category of topological representations associated to a type equipped with a
continuous representation. This is the preferred way to construct a term of `TopRep k G`. -/
/-
**TopRep.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopRep`。
形式化陈述：of : TopRep k G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object in the category of topological representations associated to a type e
quipped with a
continuous representation. This is the preferred way to construct a term of `Top
Rep k G`.
-/
abbrev of : TopRep k G := ⟨X, ρ⟩

variable (X ρ) in
/-
**TopRep.of_V** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：of_V : (of ρ).V = X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_V : (of ρ).V = X := by with_reducible rfl

variable (X ρ) in
/-
**TopRep.of_** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_ρ : (of ρ).ρ = ρ := by with_reducible rfl

/-- The type of morphisms in `TopRep k G`. -/
@[ext]
/-
**TopRep.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopRep`。
形式化陈述：{k : Type u} →   {G : Type v} →     [inst : TopologicalSpace k] → [inst_1 
: Ring k] → [inst_2 : Monoid G] → TopRep k G → TopRep k G → Type (max u_1 u_2)
参数：max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `TopRep k G`.
-/
structure Hom (A B : TopRep k G) where
  private mk ::
  /-- The underlying `G`-equivariant linear map. -/
  hom' : A.ρ →ⁱL B.ρ

variable (A B C : TopRep.{w} k G)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**TopRep.** 是 Mathlib 中的一个实例，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (TopRep.{w} k G) where
  Hom A B := Hom A B
  id A := ⟨.id (π₁ := A.ρ)⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**TopRep.** 是 Mathlib 中的一个实例，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory (TopRep.{w} k G) (fun A B ↦ A.ρ →ⁱL B.ρ) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {A B} in
/-- Turn a morphism in `TopRep` back into an `IntertwiningMap`. -/
/-
**TopRep.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `TopRep.Hom`。
形式化陈述：{k : Type u} →   {G : Type v} →     [inst : TopologicalSpace k] →       [i
nst_1 : Ring k] → [inst_2 : Monoid G] → {A B : TopRep k G} → A.Hom B → ContInter
twiningMap A.ρ B.ρ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…

--- 原说明 ---
Turn a morphism in `TopRep` back into an `IntertwiningMap`.
-/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := TopRep k G) f

variable {A B} in
/-- Typecheck an `IntertwiningMap` as a morphism in `TopRep`. -/
/-
**TopRep.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopRep`。
形式化陈述：ofHom (f : ρ ->ⁱL σ) : of ρ ⟶ of σ
参数：f : ρ ->ⁱL σ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…

--- 原说明 ---
Typecheck an `IntertwiningMap` as a morphism in `TopRep`.
-/
abbrev ofHom (f : ρ →ⁱL σ) : of ρ ⟶ of σ :=
  ConcreteCategory.ofHom (C := TopRep.{w} k G) f
/-
**TopRep.hom_ofHom** 是 Mathlib 中的一个定理，位于命名空间 `TopRep`。
形式化陈述：∀ {k : Type u} {G : Type v} {X Y : Type w} [inst : TopologicalSpace k] [in
st_1 : Ring k] [inst_2 : Monoid G]   [inst_3 : AddCommGroup X] [inst_4 : _root_.
Module k X] [inst_5 : TopologicalSpace X]   [inst_6 : IsTopologicalAddGroup X] [
inst_7 : ContinuousSMul k X] [inst_8 : AddCommGroup Y]   [inst_9 : _root_.Module
 k Y] [inst_10 : TopologicalSpace Y] [inst_11 : IsTopologicalAddGroup Y]   [inst
_12 : ContinuousSMul k Y] {ρ : ContRepresentation k G X} {σ : ContRepresentation
 k G Y}   (f : ContIntertwiningMap ρ σ), TopRep.Hom.hom (TopRep.ofHom f) = f
参数：f : ContIntertwiningMap ρ σ；TopRep.ofHom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
-/
@[simp] lemma hom_ofHom (f : ρ →ⁱL σ) : (ofHom f).hom = f := rfl
/-
**TopRep.ofHom_hom** 是 Mathlib 中的一个定理，位于命名空间 `TopRep`。
形式化陈述：∀ {k : Type u} {G : Type v} [inst : TopologicalSpace k] [inst_1 : Ring k] 
[inst_2 : Monoid G] (A B : TopRep k G)   (f : A ⟶ B), TopRep.ofHom (TopRep.Hom.h
om f) = f
参数：A B : TopRep k G；f : A ⟶ B；TopRep.Hom.hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
· 使用定理 `TopRep.hV5`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   ContinuousSMul k ↑self
-/
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

variable {A B} in
/-- The morphism of topological modules underlying a morphism in `TopRep k G`. -/
/-
**TopRep.Hom.toTopModuleCatHom** 是 Mathlib 中的一个定义，位于命名空间 `TopRep.Hom`。
形式化陈述：{k : Type u} →   {G : Type v} →     [inst : TopologicalSpace k] →       [i
nst_1 : Ring k] →         [inst_2 : Monoid G] → {A B : TopRep k G} → A.Hom B → (
TopModuleCat.of k ↑A ⟶ TopModuleCat.of k ↑B)
参数：TopModuleCat.of k ↑A ⟶ TopModuleCat.of k ↑B。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV5`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   ContinuousSMul k ↑self
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…

--- 原说明 ---
The morphism of topological modules underlying a morphism in `TopRep k G`.
-/
abbrev Hom.toTopModuleCatHom (f : Hom A B) :
    TopModuleCat.of k A ⟶ TopModuleCat.of k B :=
  TopModuleCat.ofHom f.hom.toContinuousLinearMap

/-
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/
/-
**TopRep.hom_id** 是 Mathlib 中的一个定理，位于命名空间 `TopRep`。
形式化陈述：∀ {k : Type u} {G : Type v} [inst : TopologicalSpace k] [inst_1 : Ring k] 
[inst_2 : Monoid G] (A : TopRep k G),   TopRep.Hom.hom (CategoryTheory.CategoryS
truct.id A) = ContIntertwiningMap.id
参数：A : TopRep k G；CategoryTheory.CategoryStruct.id A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = .id (π₁ := A.ρ) := rfl

/- Provided for rewriting. -/
/-
**TopRep.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：id_apply (a : A) : (𝟙 A : A ⟶ A) a = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (a : A) : (𝟙 A : A ⟶ A) a = a := rfl
/-
**TopRep.hom_comp** 是 Mathlib 中的一个定理，位于命名空间 `TopRep`。
形式化陈述：∀ {k : Type u} {G : Type v} [inst : TopologicalSpace k] [inst_1 : Ring k] 
[inst_2 : Monoid G] (A B C : TopRep k G)   (f : A ⟶ B) (g : B ⟶ C),   TopRep.Hom
.hom (CategoryTheory.CategoryStruct.comp f g) = (TopRep.Hom.hom g).comp (TopRep.
Hom.hom f)
参数：A B C : TopRep k G；f : A ⟶ B；g : B ⟶ C；CategoryTheory.CategoryStruct.comp f g
；TopRep.Hom.hom g；TopRep.Hom.hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
-/
@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
variable {A B C} in
/-
**TopRep.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a)
参数：f : A ⟶ B；g : B ⟶ C；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
-/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := rfl

variable {A B} in
/-
**TopRep.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `TopRep`。
形式化陈述：∀ {k : Type u} {G : Type v} [inst : TopologicalSpace k] [inst_1 : Ring k] 
[inst_2 : Monoid G] {A B : TopRep k G}   {f g : A ⟶ B}, TopRep.Hom.hom f = TopRe
p.Hom.hom g → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
· 使用定理 `TopRep.Hom.ext`：∀ {k : Type u} {G : Type v} {inst : TopologicalSpace k} 
{inst_1 : Ring k} {inst_2 : Monoid G} {A : TopRep k G}   {B : TopRep k G} {x y :
 A.H…
-/
@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

variable {A B} in
/-
**TopRep.hom_comm_apply** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：hom_comm_apply (f : A ⟶ B) (g : G) (a : A) : f.hom (A.ρ g a) = B.ρ g (f.ho
m a)
参数：f : A ⟶ B；g : G；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContIntertwiningMap.isIntertwining'`：∀ {R : Type u_1} {G : Type u_2} {V 
: Type u_3} {W : Type u_4} [inst : Monoid G] [inst_1 : Ring R]   [inst_2 : AddCo
mmGroup V] [inst_3 : Topo…
-/
lemma hom_comm_apply (f : A ⟶ B) (g : G) (a : A) : f.hom (A.ρ g a) = B.ρ g (f.hom a) := by
  simpa using! congr($(f.hom.2 g) a)
/-
**TopRep.** 是 Mathlib 中的一个实例，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (A ⟶ B) := fast_instance% ConcreteCategory.homEquiv.addCommGroup
/-
**TopRep.hom_zero** 是 Mathlib 中的一个定理，位于命名空间 `TopRep`。
形式化陈述：∀ {k : Type u} {G : Type v} [inst : TopologicalSpace k] [inst_1 : Ring k] 
[inst_2 : Monoid G] (A B : TopRep k G),   TopRep.Hom.hom 0 = 0
参数：A B : TopRep k G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
-/
@[simp] lemma hom_zero : (0 : A ⟶ B).hom = 0 := rfl
/-
**TopRep.hom_add** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：hom_add (f g : A ⟶ B) : (f + g).hom = f.hom + g.hom
参数：f g : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
-/
lemma hom_add (f g : A ⟶ B) : (f + g).hom = f.hom + g.hom := rfl
/-
**TopRep.hom_sub** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：hom_sub (f g : A ⟶ B) : (f - g).hom = f.hom - g.hom
参数：f g : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
-/
lemma hom_sub (f g : A ⟶ B) : (f - g).hom = f.hom - g.hom := rfl
/-
**TopRep.ofHom_add** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：ofHom_add (f g : ρ ->ⁱL σ) : ofHom (f + g) = ofHom f + ofHom g
参数：f g : ρ ->ⁱL σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_add (f g : ρ →ⁱL σ) : ofHom (f + g) = ofHom f + ofHom g := rfl
/-
**TopRep.ofHom_sub** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：ofHom_sub (f g : ρ ->ⁱL σ) : ofHom (f - g) = ofHom f - ofHom g
参数：f g : ρ ->ⁱL σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_sub (f g : ρ →ⁱL σ) : ofHom (f - g) = ofHom f - ofHom g := rfl
/-
**TopRep.comp_add'** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：comp_add' (f : A ⟶ B) (g h : B ⟶ C) : f ≫ (g + h) = f ≫ g + f ≫ h
参数：f : A ⟶ B；g h : B ⟶ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : TopologicalSpace k] 
[inst_1 : Ring k] [inst_2 : Monoid G] {A B : TopRep k G}   {f g : A ⟶ B}, TopRep
.Hom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContIntertwiningMap.add_comp`：add_comp (f g : π₂ ->ⁱL π₃) (h : π₁ ->ⁱL π
₂) : (f + g).comp h = f.comp h + g.comp h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_add' (f : A ⟶ B) (g h : B ⟶ C) : f ≫ (g + h) = f ≫ g + f ≫ h := by
  ext : 1; simp [hom_add, ContIntertwiningMap.add_comp]
/-
**TopRep.add_comp'** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：add_comp' (f g : A ⟶ B) (h : B ⟶ C) : (f + g) ≫ h = f ≫ h + g ≫ h
参数：f g : A ⟶ B；h : B ⟶ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : TopologicalSpace k] 
[inst_1 : Ring k] [inst_2 : Monoid G] {A B : TopRep k G}   {f g : A ⟶ B}, TopRep
.Hom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContIntertwiningMap.comp_add`：comp_add (f : π₂ ->ⁱL π₃) (g h : π₁ ->ⁱL π
₂) : f.comp (g + h) = f.comp g + f.comp h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_comp' (f g : A ⟶ B) (h : B ⟶ C) : (f + g) ≫ h = f ≫ h + g ≫ h := by
  ext : 1; simp [hom_add, ContIntertwiningMap.comp_add]
/-
**TopRep.** 是 Mathlib 中的一个实例，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive (TopRep k G) where
  homGroup := inferInstance
  add_comp := TopRep.add_comp'
  comp_add := TopRep.comp_add'

section Linear

variable {k : Type u} {G : Type v} {X Y : Type w} [TopologicalSpace k] [CommRing k]
  [Monoid G] [AddCommGroup X] [Module k X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul k X] [AddCommGroup Y] [Module k Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul k Y] {ρ : ContRepresentation k G X}
  {σ : ContRepresentation k G Y} {A B C : TopRep k G}

/-
**TopRep.** 是 Mathlib 中的一个实例，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module k (A ⟶ B) := fast_instance% ConcreteCategory.homEquiv.module k
/-
**TopRep.hom_smul** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：hom_smul (r : k) (f : A ⟶ B) : (r • f).hom = r • f.hom
参数：r : k；f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
-/
lemma hom_smul (r : k) (f : A ⟶ B) : (r • f).hom = r • f.hom := rfl
/-
**TopRep.ofHom_smul** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：ofHom_smul (r : k) (f : ρ ->ⁱL σ) : ofHom (r • f) = r • ofHom f
参数：r : k；f : ρ ->ⁱL σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
lemma ofHom_smul (r : k) (f : ρ →ⁱL σ) : ofHom (r • f) = r • ofHom f := rfl

variable (A B C) in
/-
**TopRep.smul_comp'** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：smul_comp' (r : k) (f : A ⟶ B) (g : B ⟶ C) : (r • f) ≫ g = r • (f ≫ g)
参数：r : k；f : A ⟶ B；g : B ⟶ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : TopologicalSpace k] 
[inst_1 : Ring k] [inst_2 : Monoid G] {A B : TopRep k G}   {f g : A ⟶ B}, TopRep
.Hom…
· 使用引理 `ContIntertwiningMap.ext`：ext {π₁ : ContRepresentation R G V} {π₂ : ContR
epresentation R G W} {f g : π₁ ->ⁱL π₂} (h : f.toContinuousLinearMap = g.toConti
nuousLinearMa…
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `TopRep.hV5`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   ContinuousSMul k ↑self
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用引理 `ContIntertwiningMap.comp_smul`：comp_smul {S : Type*} [Monoid S] [Distrib
MulAction S U] [SMulCommClass R S U] [ContinuousConstSMul S U] [LinearMap.Compat
ibleSMul U U S R] […
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_comp' (r : k) (f : A ⟶ B) (g : B ⟶ C) : (r • f) ≫ g = r • (f ≫ g) := by
  ext; simp [hom_smul, ContIntertwiningMap.comp_smul]

variable (A B C) in
/-
**TopRep.comp_smul'** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：comp_smul' (f : A ⟶ B) (r : k) (g : B ⟶ C) : f ≫ (r • g) = r • (f ≫ g)
参数：f : A ⟶ B；r : k；g : B ⟶ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : TopologicalSpace k] 
[inst_1 : Ring k] [inst_2 : Monoid G] {A B : TopRep k G}   {f g : A ⟶ B}, TopRep
.Hom…
· 使用引理 `ContIntertwiningMap.ext`：ext {π₁ : ContRepresentation R G V} {π₂ : ContR
epresentation R G W} {f g : π₁ ->ⁱL π₂} (h : f.toContinuousLinearMap = g.toConti
nuousLinearMa…
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `TopRep.hV5`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   ContinuousSMul k ↑self
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用引理 `ContIntertwiningMap.smul_comp`：smul_comp {S : Type*} [Monoid S] [Distrib
MulAction S U] [SMulCommClass R S U] [ContinuousConstSMul S U] [LinearMap.Compat
ibleSMul U U S R] (…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_smul' (f : A ⟶ B) (r : k) (g : B ⟶ C) : f ≫ (r • g) = r • (f ≫ g) := by
  ext; simp [hom_smul, ContIntertwiningMap.smul_comp]
/-
**TopRep.** 是 Mathlib 中的一个实例，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CategoryTheory.Linear k (TopRep k G) where
  homModule := inferInstance
  smul_comp := smul_comp'
  comp_smul := comp_smul'

end Linear

section equivAction

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor sending a topological representation to the corresponding object in
`Action (TopModuleCat k) G`. -/
/-
**TopRep.toActionTopModFunc** 是 Mathlib 中的一个定义，位于命名空间 `TopRep`。
形式化陈述：toActionTopModFunc : TopRep k G ⥤ Action (TopModuleCat k) G where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV5`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   ContinuousSMul k ↑self
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…

--- 原说明 ---
The functor sending a topological representation to the corresponding object in
`Action (TopModuleCat k) G`.
-/
def toActionTopModFunc : TopRep k G ⥤ Action (TopModuleCat k) G where
  obj X := ⟨.of k X.V, (TopModuleCat.endRingEquiv (.of k X.V)).symm.toMonoidHom.comp X.ρ⟩
  map f := ⟨f.toTopModuleCatHom, fun g => by ext1; simp [TopModuleCat.endRingEquiv, f.hom.2 g]⟩

/-- The functor sending an object in `Action (TopModuleCat k) G` to the corresponding topological
representation. -/
/-
**TopRep.fromActionTopModFunc** 是 Mathlib 中的一个定义，位于命名空间 `TopRep`。
形式化陈述：fromActionTopModFunc : Action (TopModuleCat.{w} k) G ⥤ TopRep k G where ob
j X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor sending an object in `Action (TopModuleCat k) G` to the correspondin
g topological
representation.
-/
def fromActionTopModFunc : Action (TopModuleCat.{w} k) G ⥤ TopRep k G where
  obj X := .of <| .ofMonoidHom <| (TopModuleCat.endRingEquiv X.V).toMonoidHom.comp X.ρ
  map {X Y} f := ofHom ⟨f.hom.hom, fun g ↦ by
    simpa [← toMonoidHom_apply] using congr(TopModuleCat.Hom.hom $(f.comm g))⟩

/-- The unit isomorphism of the equivalence `TopRepIsoActionTop`. -/
/-
**TopRep.toActionFromAction** 是 Mathlib 中的一个定义，位于命名空间 `TopRep`。
形式化陈述：toActionFromAction (X : TopRep.{w} k G) : fromActionTopModFunc.obj (toActi
onTopModFunc.obj X) ≅ X where hom
参数：X : TopRep.{w} k G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
· 使用定理 `TopRep.hV5`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   ContinuousSMul k ↑self

--- 原说明 ---
The unit isomorphism of the equivalence `TopRepIsoActionTop`.
-/
def toActionFromAction (X : TopRep.{w} k G) :
    fromActionTopModFunc.obj (toActionTopModFunc.obj X) ≅ X where
  hom := ofHom ⟨ContinuousLinearMap.id k X.V, fun _ ↦ rfl⟩
  inv := ofHom ⟨ContinuousLinearMap.id k X.V, fun _ ↦ rfl⟩

/-- The counit isomorphism of the equivalence `TopRepIsoActionTop`. -/
/-
**TopRep.fromActionToAction** 是 Mathlib 中的一个定义，位于命名空间 `TopRep`。
形式化陈述：fromActionToAction (X : Action (TopModuleCat.{w} k) G) : toActionTopModFun
c.obj (fromActionTopModFunc.obj X) ≅ X where hom
参数：X : Action (TopModuleCat.{w} k) G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit isomorphism of the equivalence `TopRepIsoActionTop`.
-/
def fromActionToAction (X : Action (TopModuleCat.{w} k) G) :
    toActionTopModFunc.obj (fromActionTopModFunc.obj X) ≅ X where
  hom := ⟨𝟙 _, fun _ ↦ rfl⟩
  inv := ⟨𝟙 _, fun _ ↦ rfl⟩

/-- The equivalence of categories between `TopRep k G` and `Action (TopModuleCat k) G`. -/
/-
**TopRep.TopRepEquivActionTop** 是 Mathlib 中的一个定义，位于命名空间 `TopRep`。
形式化陈述：TopRepEquivActionTop : TopRep.{w} k G ≌ Action (TopModuleCat.{w} k) G wher
e functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories between `TopRep k G` and `Action (TopModuleCat k) 
G`.
-/
def TopRepEquivActionTop : TopRep.{w} k G ≌ Action (TopModuleCat.{w} k) G where
  functor := toActionTopModFunc
  inverse := fromActionTopModFunc
  unitIso := NatIso.ofComponents toActionFromAction
  counitIso := NatIso.ofComponents fromActionToAction
/-
**TopRep.** 是 Mathlib 中的一个实例，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toActionTopModFunc (k := k) (G := G)).IsEquivalence :=
  TopRepEquivActionTop (k := k) (G := G).isEquivalence_functor
/-
**TopRep.** 是 Mathlib 中的一个实例，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (fromActionTopModFunc (k := k) (G := G)).IsEquivalence :=
  TopRepEquivActionTop (k := k) (G := G).isEquivalence_inverse

end equivAction

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The `G`-invariant topologicalsubmodule of a topological representation. -/
/-
**TopRep.invariants** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopRep`。
形式化陈述：invariants (X : TopRep k G) : TopModuleCat k
参数：X : TopRep k G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `G`-invariant topologicalsubmodule of a topological representation.
-/
abbrev invariants (X : TopRep k G) : TopModuleCat k := .of k X.ρ.invariants

variable (k G) in
/-- The functor taking an `R`-linear `G`-representation to its `G`-invariant submodule. -/
/-
**TopRep.invariantsFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopRep`。
形式化陈述：invariantsFunctor : TopRep k G ⥤ TopModuleCat k where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor taking an `R`-linear `G`-representation to its `G`-invariant submodu
le.
-/
abbrev invariantsFunctor : TopRep k G ⥤ TopModuleCat k where
  obj A := .of k A.ρ.invariants
  map f := TopModuleCat.ofHom f.hom.mapInvariants
/-
**TopRep.** 是 Mathlib 中的一个实例，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (invariantsFunctor k G).Additive where
/-
**TopRep.** 是 Mathlib 中的一个实例，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {k : Type u} [CommRing k] [TopologicalSpace k] : (invariantsFunctor k G).Linear k where

/-- The top rep induced by the coinduced representation. -/
/-
**TopRep.coind** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The top rep induced by the coinduced representation.
-/
abbrev coind₁ (A : TopRep k G) : TopRep k G := of A.ρ.coind₁

variable (k G) in
/-- The functor taking a representation `rep` to the representation `C(G, rep)`.
The `G` action is defined by `g • f := x ↦ g • f (g⁻¹ * x)`. -/
/-
**TopRep.coind** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor taking a representation `rep` to the representation `C(G, rep)`.
The `G` action is defined by `g • f := x ↦ g • f (g⁻¹ * x)`.
-/
abbrev coind₁Functor : TopRep k G ⥤ TopRep k G where
  obj := coind₁
  map φ := ofHom <| ContRepresentation.coind₁Map φ.hom
/-
**TopRep.** 是 Mathlib 中的一个实例，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (TopRep.coind₁Functor k G).Additive where
/-
**TopRep.** 是 Mathlib 中的一个实例，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {k : Type u} [CommRing k] [TopologicalSpace k] : (coind₁Functor k G).Linear k where

/-- The constant function `rep ⟶ C(G, rep)` as a natural transformation. -/
@[implicit_reducible, simps]
/-
**TopRep.coind** 是 Mathlib 中的一个定义，位于命名空间 `TopRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant function `rep ⟶ C(G, rep)` as a natural transformation.
-/
def coind₁ι : 𝟭 (TopRep k G) ⟶ coind₁Functor k G where
  app rep := ofHom rep.ρ.coind₁ι

/-- The restriction of a topological representation along a monoid homomorphism. -/
/-
**TopRep.res** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopRep`。
形式化陈述：res {H : Type*} [Monoid H] (φ : H ->* G) (A : TopRep k G) : TopRep k H
参数：φ : H ->* G；A : TopRep k G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a topological representation along a monoid homomorphism.
-/
abbrev res {H : Type*} [Monoid H] (φ : H →* G) (A : TopRep k G) : TopRep k H := of (A.ρ.restrict φ)

/-- The functor taking a topological `G`-representation to a topological `H`-representation
along a monoid homomorphism `φ : H →* G`. -/
/-
**TopRep.resFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopRep`。
形式化陈述：resFunctor {H : Type*} [Monoid H] (φ : H ->* G) : TopRep k G ⥤ TopRep k H 
where obj
参数：φ : H ->* G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor taking a topological `G`-representation to a topological `H`-represe
ntation
along a monoid homomorphism `φ : H →* G`.
-/
abbrev resFunctor {H : Type*} [Monoid H] (φ : H →* G) :
    TopRep k G ⥤ TopRep k H where
  obj := res φ
  map f := ofHom <| f.hom.restrict φ

section invariantsResMap

variable {G H : Type*} [Group G]

@[simp]
/-
**TopRep.resFunctor_map_hom** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：resFunctor_map_hom [Monoid H] (φ : H ->* G) {A B : TopRep k G} (f : A ⟶ B)
 : ((resFunctor φ).map f).hom = f.hom.restrict φ
参数：φ : H ->* G；f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopRep.hV4`：∀ {k : Type u} {G : Type v} [inst : Ring k] [inst_1 : Topolo
gicalSpace k] [inst_2 : Monoid G] (self : TopRep k G),   IsTopologicalAddGroup ↑
…
-/
lemma resFunctor_map_hom [Monoid H] (φ : H →* G) {A B : TopRep k G} (f : A ⟶ B) :
    ((resFunctor φ).map f).hom = f.hom.restrict φ := rfl

variable [Group H]

/-- The morphism between invariant submodules induced by a morphism `res φ X ⟶ Y` of
topological `H`-representations, where `φ : H →* G` is a group homomorphism. -/
/-
**TopRep.invariantsResMap** 是 Mathlib 中的一个定义，位于命名空间 `TopRep`。
形式化陈述：invariantsResMap (φ : H ->* G) {X : TopRep k G} {Y : TopRep k H} (f : res 
φ X ⟶ Y) : X.invariants ⟶ Y.invariants
参数：φ : H ->* G；f : res φ X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism between invariant submodules induced by a morphism `res φ X ⟶ Y` of
topological `H`-representations, where `φ : H →* G` is a group homomorphism.
-/
def invariantsResMap (φ : H →* G) {X : TopRep k G} {Y : TopRep k H} (f : res φ X ⟶ Y) :
    X.invariants ⟶ Y.invariants :=
  TopModuleCat.ofHom (f.hom.mapInvariantsOfRes φ)
/-
**TopRep.invariantsResMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：invariantsResMap_comp {X : TopRep k G} {Y Y' : TopRep k H} (φ : H ->* G) (
f : res φ X ⟶ Y) (g : Y ⟶ Y') : invariantsResMap φ (f ≫ g) = invariantsResMap φ 
f ≫ (invariantsFunctor k H).map g
参数：φ : H ->* G；f : res φ X ⟶ Y；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma invariantsResMap_comp {X : TopRep k G} {Y Y' : TopRep k H} (φ : H →* G)
    (f : res φ X ⟶ Y) (g : Y ⟶ Y') :
    invariantsResMap φ (f ≫ g) = invariantsResMap φ f ≫ (invariantsFunctor k H).map g := rfl
/-
**TopRep.invariantsResMap_map_comp** 是 Mathlib 中的一个引理，位于命名空间 `TopRep`。
形式化陈述：invariantsResMap_map_comp {X X' : TopRep k G} {Y : TopRep k H} (φ : H ->* 
G) (f : X ⟶ X') (g : res φ X' ⟶ Y) : invariantsResMap φ ((resFunctor φ).map f ≫ 
g) = (invariantsFunctor k G).map f ≫ invariantsResMap φ g
参数：φ : H ->* G；f : X ⟶ X'；g : res φ X' ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma invariantsResMap_map_comp {X X' : TopRep k G} {Y : TopRep k H} (φ : H →* G)
    (f : X ⟶ X') (g : res φ X' ⟶ Y) :
    invariantsResMap φ ((resFunctor φ).map f ≫ g) =
      (invariantsFunctor k G).map f ≫ invariantsResMap φ g := rfl

end invariantsResMap

end TopRep

