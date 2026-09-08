/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Yuyang Zhao
-/
module

public import Mathlib.Algebra.Category.Grp.FiniteGrp
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.Separation.Connected
/-!

# Category of Profinite Groups

We say `G` is a profinite group if it is a topological group which is compact and totally
disconnected.

## Main definitions and results

* `ProfiniteGrp` is the category of profinite groups.

* `ProfiniteGrp.pi` : The pi-type of profinite groups is also a profinite group.

* `ofFiniteGrp` : A `FiniteGrp` when given the discrete topology can be considered as a
  profinite group.

* `ofClosedSubgroup` : A closed subgroup of a profinite group is profinite.

-/

@[expose] public section

universe u v

open CategoryTheory Topology

/--
The category of profinite groups. A term of this type consists of a profinite
set with a topological group structure.
-/
@[pp_with_univ]
/-
**ProfiniteGrp** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of profinite groups. A term of this type consists of a profinite
set with a topological group structure.
-/
structure ProfiniteGrp where
  /-- The underlying profinite topological space. -/
  toProfinite : Profinite.{u}
  /-- The group structure. -/
  [group : Group toProfinite]
  /-- The above data together form a topological group. -/
  [topologicalGroup : IsTopologicalGroup toProfinite]

/--
The category of profinite additive groups. A term of this type consists of a profinite
set with a topological additive group structure.
-/
@[pp_with_univ]
/-
**ProfiniteAddGrp** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of profinite additive groups. A term of this type consists of a pro
finite
set with a topological additive group structure.
-/
structure ProfiniteAddGrp where
  /-- The underlying profinite topological space. -/
  toProfinite : Profinite.{u}
  /-- The additive group structure. -/
  [addGroup : AddGroup toProfinite]
  /-- The above data together form a topological additive group. -/
  [topologicalAddGroup : IsTopologicalAddGroup toProfinite]

attribute [to_additive] ProfiniteGrp

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort ProfiniteGrp (Type u) where
  coe G := G.toProfinite

attribute [instance] ProfiniteGrp.group ProfiniteGrp.topologicalGroup
    ProfiniteAddGrp.addGroup ProfiniteAddGrp.topologicalAddGroup

/-- Construct a term of `ProfiniteGrp` from a type endowed with the structure of a
compact and totally disconnected topological group.
(The condition of being Hausdorff can be omitted here because totally disconnected implies that
`{1}` is a closed set, thus implying Hausdorff in a topological group.) -/
@[to_additive /-- Construct a term of `ProfiniteAddGrp` from a type endowed with the structure of a
compact and totally disconnected topological additive group.
(The condition of being Hausdorff can be omitted here because totally disconnected implies that
`{0}` is a closed set, thus implying Hausdorff in a topological additive group.) -/]
/-
**ProfiniteGrp.of** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ProfiniteGrp.of (G : Type u) [Group G] [TopologicalSpace G] [IsTopological
Group G] [CompactSpace G] [TotallyDisconnectedSpace G] : ProfiniteGrp.{u} where 
toProfinite
参数：G : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev ProfiniteGrp.of (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] : ProfiniteGrp.{u} where
  toProfinite := .of G
  group := ‹_›
  topologicalGroup := ‹_›

@[to_additive]
/-
**ProfiniteGrp.coe_of** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ProfiniteGrp.coe_of (G : Type u) [Group G] [TopologicalSpace G] [IsTopolog
icalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] : (ProfiniteGrp.of G 
: Type u) = G
参数：G : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ProfiniteGrp.coe_of (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] : (ProfiniteGrp.of G : Type u) = G :=
  rfl

/-- The type of morphisms in `ProfiniteAddGrp`. -/
@[ext]
/-
**ProfiniteAddGrp.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `ProfiniteAddGrp`。
形式化陈述：ProfiniteAddGrp.{u} → ProfiniteAddGrp.{u} → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `ProfiniteAddGrp`.
-/
structure ProfiniteAddGrp.Hom (A B : ProfiniteAddGrp.{u}) where
  private mk ::
  /-- The underlying `ContinuousAddMonoidHom`. -/
  hom' : A →ₜ+ B

/-- The type of morphisms in `ProfiniteGrp`. -/
@[to_additive existing (attr := ext)]
/-
**ProfiniteGrp.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `ProfiniteGrp`。
形式化陈述：ProfiniteGrp.{u} → ProfiniteGrp.{u} → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `ProfiniteGrp`.
-/
structure ProfiniteGrp.Hom (A B : ProfiniteGrp.{u}) where
  private mk ::
  /-- The underlying `ContinuousMonoidHom`. -/
  hom' : A →ₜ* B

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category ProfiniteGrp where
  Hom A B := ProfiniteGrp.Hom A B
  id A := ⟨ContinuousMonoidHom.id A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory ProfiniteGrp (fun X Y => X →ₜ* Y) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- The underlying `ContinuousMonoidHom`. -/
@[to_additive /-- The underlying `ContinuousAddMonoidHom`. -/]
/-
**ProfiniteGrp.Hom.hom** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ProfiniteGrp.Hom.hom {M N : ProfiniteGrp.{u}} (f : ProfiniteGrp.Hom M N) :
 M ->ₜ* N
参数：f : ProfiniteGrp.Hom M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying `ContinuousMonoidHom`.
-/
abbrev ProfiniteGrp.Hom.hom {M N : ProfiniteGrp.{u}} (f : ProfiniteGrp.Hom M N) :
    M →ₜ* N :=
  ConcreteCategory.hom (C := ProfiniteGrp) f

/-- Typecheck a `ContinuousMonoidHom` as a morphism in `ProfiniteGrp`. -/
@[to_additive /-- Typecheck a `ContinuousAddMonoidHom` as a morphism in `ProfiniteAddGrp`. -/]
/-
**ProfiniteGrp.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ProfiniteGrp.ofHom {X Y : Type u} [Group X] [TopologicalSpace X] [IsTopolo
gicalGroup X] [CompactSpace X] [TotallyDisconnectedSpace X] [Group Y] [Topologic
alSpace Y] [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] 
(f : X ->ₜ* Y) : ProfiniteGrp.of X ⟶ ProfiniteGrp.of Y
参数：f : X ->ₜ* Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `ContinuousMonoidHom` as a morphism in `ProfiniteGrp`.
-/
abbrev ProfiniteGrp.ofHom {X Y : Type u} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [CompactSpace X] [TotallyDisconnectedSpace X] [Group Y] [TopologicalSpace Y]
    [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y]
    (f : X →ₜ* Y) : ProfiniteGrp.of X ⟶ ProfiniteGrp.of Y :=
  ConcreteCategory.ofHom f

namespace ProfiniteGrp

@[to_additive]
/-
**ProfiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `ProfiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : ProfiniteGrp.{u}} : CoeFun (M ⟶ N) (fun _ ↦ M → N) where
  coe f := f.hom

@[to_additive (attr := simp)]
/-
**ProfiniteGrp.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `ProfiniteGrp`。
形式化陈述：hom_id {A : ProfiniteGrp.{u}} : (𝟙 A : A ⟶ A).hom = ContinuousMonoidHom.id
 A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {A : ProfiniteGrp.{u}} : (𝟙 A : A ⟶ A).hom = ContinuousMonoidHom.id A := rfl

/- Provided for rewriting. -/
@[to_additive]
/-
**ProfiniteGrp.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `ProfiniteGrp`。
形式化陈述：id_apply (A : ProfiniteGrp.{u}) (a : A) : (𝟙 A : A ⟶ A) a = a
参数：A : ProfiniteGrp.{u}；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMonoidHom.id_toFun`：∀ (A : Type u_2) [inst : Monoid A] [inst_1
 : TopologicalSpace A] (x : A), (ContinuousMonoidHom.id A) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (A : ProfiniteGrp.{u}) (a : A) :
    (𝟙 A : A ⟶ A) a = a := by simp

@[to_additive (attr := simp)]
/-
**ProfiniteGrp.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `ProfiniteGrp`。
形式化陈述：hom_comp {A B C : ProfiniteGrp.{u}} (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom 
= g.hom.comp f.hom
参数：f : A ⟶ B；g : B ⟶ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {A B C : ProfiniteGrp.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
/-
**ProfiniteGrp.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `ProfiniteGrp`。
形式化陈述：comp_apply {A B C : ProfiniteGrp.{u}} (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f
 ≫ g) a = g (f a)
参数：f : A ⟶ B；g : B ⟶ C；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMonoidHom.comp_toFun`：∀ {A : Type u_2} {B : Type u_3} {C : Typ
e u_4} [inst : Monoid A] [inst_1 : Monoid B] [inst_2 : Monoid C]   [inst_3 : Top
ologicalSpace A] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {A B C : ProfiniteGrp.{u}} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := by
  simp only [hom_comp, ContinuousMonoidHom.comp_toFun]

@[to_additive (attr := ext)]
/-
**ProfiniteGrp.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `ProfiniteGrp`。
形式化陈述：hom_ext {A B : ProfiniteGrp.{u}} {f g : A ⟶ B} (hf : f.hom = g.hom) : f = 
g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProfiniteGrp.Hom.ext`：∀ {A B : ProfiniteGrp.{u}} {x y : A.Hom B}, x.hom'
 = y.hom' → x = y
-/
lemma hom_ext {A B : ProfiniteGrp.{u}} {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

variable {X Y Z : Type u} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [CompactSpace X] [TotallyDisconnectedSpace X] [Group Y] [TopologicalSpace Y]
    [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] [Group Z]
    [TopologicalSpace Z] [IsTopologicalGroup Z] [CompactSpace Z] [TotallyDisconnectedSpace Z]

@[to_additive (attr := simp)]
/-
**ProfiniteGrp.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `ProfiniteGrp`。
形式化陈述：hom_ofHom (f : X ->ₜ* Y) : (ofHom f).hom = f
参数：f : X ->ₜ* Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom (f : X →ₜ* Y) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
/-
**ProfiniteGrp.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `ProfiniteGrp`。
形式化陈述：ofHom_hom {A B : ProfiniteGrp.{u}} (f : A ⟶ B) : ofHom (Hom.hom f) = f
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProfiniteGrp.topologicalGroup`：∀ (self : ProfiniteGrp.{u}), IsTopologica
lGroup ↑self.toProfinite.toTop
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `Profinite.instTotallyDisconnectedSpaceCarrierToTop`：∀ {X : Profinite}, T
otallyDisconnectedSpace ↑X.toTop
-/
lemma ofHom_hom {A B : ProfiniteGrp.{u}} (f : A ⟶ B) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
/-
**ProfiniteGrp.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `ProfiniteGrp`。
形式化陈述：ofHom_id : ofHom (ContinuousMonoidHom.id X) = 𝟙 (of X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id : ofHom (ContinuousMonoidHom.id X) = 𝟙 (of X) := rfl

@[to_additive (attr := simp)]
/-
**ProfiniteGrp.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `ProfiniteGrp`。
形式化陈述：ofHom_comp (f : X ->ₜ* Y) (g : Y ->ₜ* Z) : ofHom (g.comp f) = ofHom f ≫ of
Hom g
参数：f : X ->ₜ* Y；g : Y ->ₜ* Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp (f : X →ₜ* Y) (g : Y →ₜ* Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
/-
**ProfiniteGrp.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `ProfiniteGrp`。
形式化陈述：ofHom_apply (f : X ->ₜ* Y) (x : X) : ofHom f x = f x
参数：f : X ->ₜ* Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply (f : X →ₜ* Y) (x : X) : ofHom f x = f x := rfl

@[to_additive]
/-
**ProfiniteGrp.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `ProfiniteGrp`。
形式化陈述：inv_hom_apply {A B : ProfiniteGrp.{u}} (e : A ≅ B) (x : A) : e.inv (e.hom 
x) = x
参数：e : A ≅ B；x : A。
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
lemma inv_hom_apply {A B : ProfiniteGrp.{u}} (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by
  simp

@[to_additive]
/-
**ProfiniteGrp.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `ProfiniteGrp`。
形式化陈述：hom_inv_apply {A B : ProfiniteGrp.{u}} (e : A ≅ B) (x : B) : e.hom (e.inv 
x) = x
参数：e : A ≅ B；x : B。
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
lemma hom_inv_apply {A B : ProfiniteGrp.{u}} (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by
  simp

@[to_additive (attr := simp)]
/-
**ProfiniteGrp.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `ProfiniteGrp`。
形式化陈述：coe_id (X : ProfiniteGrp) : (𝟙 X : X -> X) = id
参数：X : ProfiniteGrp。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id (X : ProfiniteGrp) : (𝟙 X : X → X) = id :=
  rfl

@[to_additive (attr := simp)]
/-
**ProfiniteGrp.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `ProfiniteGrp`。
形式化陈述：coe_comp {X Y Z : ProfiniteGrp} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X -> Z)
 = g ∘ f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp {X Y Z : ProfiniteGrp} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : X → Z) = g ∘ f :=
  rfl

/-- Construct a term of `ProfiniteGrp` from a type endowed with the structure of a
profinite topological group. -/
@[to_additive /-- Construct a term of `ProfiniteAddGrp` from a type endowed with the structure of a
profinite topological additive group. -/]
/-
**ProfiniteGrp.ofProfinite** 是 Mathlib 中的一个缩写定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：ofProfinite (G : Profinite) [Group G] [IsTopologicalGroup G] : ProfiniteGr
p
参数：G : Profinite。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Profinite.instTotallyDisconnectedSpaceCarrierToTop`：∀ {X : Profinite}, T
otallyDisconnectedSpace ↑X.toTop
-/
abbrev ofProfinite (G : Profinite) [Group G] [IsTopologicalGroup G] :
    ProfiniteGrp := of G

/-- The pi-type of profinite groups is a profinite group. -/
@[to_additive /-- The pi-type of profinite additive groups is a
profinite additive group. -/]
/-
**ProfiniteGrp.pi** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：pi {α : Type u} (β : α -> ProfiniteGrp) : ProfiniteGrp
参数：β : α -> ProfiniteGrp。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pi {α : Type u} (β : α → ProfiniteGrp) : ProfiniteGrp :=
  let pitype := Profinite.pi fun (a : α) => (β a).toProfinite
  letI (a : α) : Group (β a).toProfinite := (β a).group
  letI : Group pitype := Pi.group
  letI : IsTopologicalGroup pitype := Pi.topologicalGroup
  ofProfinite pitype

/-- A `FiniteGrp` when given the discrete topology can be considered as a profinite group. -/
@[to_additive /-- A `FiniteAddGrp` when given the discrete topology can be considered as a
profinite additive group. -/]
/-
**ProfiniteGrp.ofFiniteGrp** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：ofFiniteGrp (G : FiniteGrp) : ProfiniteGrp
参数：G : FiniteGrp。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofFiniteGrp (G : FiniteGrp) : ProfiniteGrp :=
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : IsTopologicalGroup G := {}
  of G

/-- A morphism of `FiniteGrp` induces a morphism of the associated profinite groups. -/
@[to_additive /-- A morphism of `FiniteAddGrp` induces a morphism of the associated profinite
additive groups. -/]
/-
**ProfiniteGrp.ofFiniteGrpHom** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：ofFiniteGrpHom {G H : FiniteGrp.{u}} (f : G ⟶ H) : ofFiniteGrp G ⟶ ofFinit
eGrp H
参数：f : G ⟶ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofFiniteGrpHom {G H : FiniteGrp.{u}} (f : G ⟶ H) : ofFiniteGrp G ⟶ ofFiniteGrp H :=
  ConcreteCategory.ofHom ⟨f.hom.hom, by fun_prop⟩

@[to_additive]
/-
**ProfiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `ProfiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasForget₂ FiniteGrp ProfiniteGrp where
  forget₂ :=
  { obj := ofFiniteGrp
    map := ofFiniteGrpHom }

@[to_additive]
/-
**ProfiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `ProfiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasForget₂ ProfiniteGrp GrpCat where
  forget₂.obj P := GrpCat.of P
  forget₂.map f := GrpCat.ofHom f.hom.toMonoidHom

/-- A closed subgroup of a profinite group is profinite. -/
@[to_additive /-- A closed additive subgroup of a profinite additive group is profinite. -/]
/-
**ProfiniteGrp.ofClosedSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：ofClosedSubgroup {G : ProfiniteGrp} (H : ClosedSubgroup G) : ProfiniteGrp
参数：H : ClosedSubgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A closed subgroup of a profinite group is profinite.
-/
def ofClosedSubgroup {G : ProfiniteGrp} (H : ClosedSubgroup G) : ProfiniteGrp :=
  letI : CompactSpace H := inferInstance
  of H.1

/-- A topological group that has a `ContinuousMulEquiv` to a profinite group is profinite. -/
@[to_additive /-- A topological additive group that has a `ContinuousAddEquiv` to a
profinite additive group is profinite. -/]
/-
**ProfiniteGrp.ofContinuousMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：ofContinuousMulEquiv {G : ProfiniteGrp.{u}} {H : Type v} [TopologicalSpace
 H] [Group H] [IsTopologicalGroup H] (e : G ≃ₜ* H) : ProfiniteGrp.{v}
参数：e : G ≃ₜ* H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofContinuousMulEquiv {G : ProfiniteGrp.{u}} {H : Type v} [TopologicalSpace H]
    [Group H] [IsTopologicalGroup H] (e : G ≃ₜ* H) : ProfiniteGrp.{v} :=
  let _ : CompactSpace H := Homeomorph.compactSpace e.toHomeomorph
  let _ : TotallyDisconnectedSpace H := Homeomorph.totallyDisconnectedSpace e.toHomeomorph
  .of H

/-- Build an isomorphism in the category `ProfiniteGrp` from
a `ContinuousMulEquiv` between `ProfiniteGrp`s. -/
@[to_additive /-- Build an isomorphism in the category `ProfiniteAddGrp` from
a `ContinuousAddEquiv` between `ProfiniteAddGrp`s. -/]
/-
**ProfiniteGrp.ContinuousMulEquiv.toProfiniteGrpIso** 是 Mathlib 中的一个定义，位于命名空间 `P
rofiniteGrp.ContinuousMulEquiv`。
形式化陈述：{X Y : ProfiniteGrp.{u_1}} → ↑X.toProfinite.toTop ≃ₜ* ↑Y.toProfinite.toTop
 → (X ≅ Y)
参数：X ≅ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ProfiniteGrp.topologicalGroup`：∀ (self : ProfiniteGrp.{u}), IsTopologica
lGroup ↑self.toProfinite.toTop
-/
def ContinuousMulEquiv.toProfiniteGrpIso {X Y : ProfiniteGrp} (e : X ≃ₜ* Y) : X ≅ Y where
  hom := ofHom e
  inv := ofHom e.symm

/-- The functor mapping a profinite group to its underlying profinite space. -/
@[to_additive]
/-
**ProfiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `ProfiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor mapping a profinite group to its underlying profinite space.
-/
instance : HasForget₂ ProfiniteGrp Profinite where
  forget₂ := {
    obj G := G.toProfinite
    map f := CompHausLike.ofHom _ ⟨f, by fun_prop⟩}

@[to_additive]
/-
**ProfiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `ProfiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ ProfiniteGrp Profinite).Faithful := {
  map_injective := fun {_ _} _ _ h =>
    ConcreteCategory.hom_ext _ _ fun x ↦ CategoryTheory.congr_fun h x }

@[to_additive]
/-
**ProfiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `ProfiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ ProfiniteGrp Profinite).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget₂ ProfiniteGrp Profinite).map f)
    let e : X ≃ₜ* Y :=
      { CompHausLike.homeoOfIso i with
          map_mul' := map_mul f.hom }
    exact (ContinuousMulEquiv.toProfiniteGrpIso e).isIso_hom

@[to_additive]
/-
**ProfiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `ProfiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget ProfiniteGrp.{u}).ReflectsIsomorphisms :=
  CategoryTheory.reflectsIsomorphisms_comp (forget₂ ProfiniteGrp Profinite) (forget Profinite)

end ProfiniteGrp

/-!
### Limits in the category of profinite groups

In this section, we construct limits in the category of profinite groups.

* `ProfiniteGrp.limitCone` : The explicit limit cone in `ProfiniteGrp`.

* `ProfiniteGrp.limitConeIsLimit`: `ProfiniteGrp.limitCone` is a limit cone.

-/

section Limits

namespace ProfiniteGrp

variable {J : Type v} [SmallCategory J] (F : J ⥤ ProfiniteGrp.{max v u})

/-- Auxiliary construction to obtain the group structure on the limit of profinite groups. -/
@[to_additive /-- Auxiliary construction to obtain the additive group structure on the limit of
profinite additive groups. -/]
/-
**ProfiniteGrp.limitConePtAux** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：limitConePtAux : Subgroup (Π j : J, F.obj j) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def limitConePtAux : Subgroup (Π j : J, F.obj j) where
  carrier := {x | ∀ ⦃i j : J⦄ (π : i ⟶ j), F.map π (x i) = x j}
  mul_mem' hx hy _ _ π := by simp only [Pi.mul_apply, map_mul, hx π, hy π]
  one_mem' := by simp only [Set.mem_ofPred_eq, Pi.one_apply, map_one, implies_true]
  inv_mem' h _ _ π := by simp only [Pi.inv_apply, map_inv, h π]

@[to_additive]
/-
**ProfiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `ProfiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt :=
  inferInstanceAs (Group (limitConePtAux F))

@[to_additive]
/-
**ProfiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `ProfiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalGroup (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt :=
  inferInstanceAs (IsTopologicalGroup (limitConePtAux F))

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The explicit limit cone in `ProfiniteGrp`. -/
@[to_additive /-- The explicit limit cone in `ProfiniteAddGrp`. -/]
/-
**ProfiniteGrp.limitCone** 是 Mathlib 中的一个缩写定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：limitCone : Limits.Cone F where pt
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ProfiniteGrp.instIsTopologicalGroupCarrierToTopTotallyDisconnectedSpaceP
tProfiniteLimitConeCompForget₂ContinuousMonoidHomToProfiniteContinuousMap`：∀ {J 
: Type v} [inst : CategoryTheory.SmallCategory J] (F : CategoryTheory.Functor J 
ProfiniteGrp.{max v u}),   IsTopologicalGroup ↑(Profini…

--- 原说明 ---
The explicit limit cone in `ProfiniteGrp`.
-/
abbrev limitCone : Limits.Cone F where
  pt := ofProfinite (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt
  π :=
  { app := fun j => ⟨{
      toFun := fun x => x.1 j
      map_one' := rfl
      map_mul' := fun x y => rfl
      continuous_toFun := by
        exact (continuous_apply j).comp (continuous_iff_le_induced.mpr fun U a => a) }⟩
    naturality := fun i j f => by
      simp only [Functor.const_obj_obj, Functor.comp_obj,
        Functor.const_obj_map, Category.id_comp, Functor.comp_map]
      congr
      exact funext fun x => (x.2 f).symm }

/-- `ProfiniteGrp.limitCone` is a limit cone. -/
@[to_additive /-- `ProfiniteAddGrp.limitCone` is a limit cone. -/]
/-
**ProfiniteGrp.limitConeIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：limitConeIsLimit : Limits.IsLimit (limitCone F) where lift cone
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ProfiniteGrp.instIsTopologicalGroupCarrierToTopTotallyDisconnectedSpaceP
tProfiniteLimitConeCompForget₂ContinuousMonoidHomToProfiniteContinuousMap`：∀ {J 
: Type v} [inst : CategoryTheory.SmallCategory J] (F : CategoryTheory.Functor J 
ProfiniteGrp.{max v u}),   IsTopologicalGroup ↑(Profini…

--- 原说明 ---
`ProfiniteGrp.limitCone` is a limit cone.
-/
def limitConeIsLimit : Limits.IsLimit (limitCone F) where
  lift cone := ofHom
    { ((Profinite.limitConeIsLimit (F ⋙ (forget₂ ProfiniteGrp Profinite))).lift
        ((forget₂ ProfiniteGrp Profinite).mapCone cone)).hom.hom with
      map_one' := Subtype.ext (funext fun j ↦ map_one (cone.π.app j).hom)
      -- TODO: investigate whether it's possible to set up `ext` lemmas for the `TopCat`-related
      -- categories so that `by ext j; exact map_one (cone.π.app j)` works here, similarly below.
      map_mul' := fun _ _ ↦ Subtype.ext (funext fun j ↦ map_mul (cone.π.app j).hom _ _) }
  uniq cone m h := by
    apply (forget₂ ProfiniteGrp Profinite).map_injective
    simpa using! (Profinite.limitConeIsLimit (F ⋙ (forget₂ ProfiniteGrp Profinite))).uniq
      ((forget₂ ProfiniteGrp Profinite).mapCone cone) ((forget₂ ProfiniteGrp Profinite).map m)
      (fun j ↦ congrArg (forget₂ ProfiniteGrp Profinite).map (h j))

@[to_additive]
/-
**ProfiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `ProfiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.HasLimit F where
  exists_limit := Nonempty.intro
    { cone := limitCone F
      isLimit := limitConeIsLimit F }

@[to_additive]
/-
**ProfiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `ProfiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.PreservesLimits (forget₂ ProfiniteGrp Profinite) where
  preservesLimitsOfShape := {
    preservesLimit := fun {F} ↦ CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone
      (limitConeIsLimit F) (Profinite.limitConeIsLimit (F ⋙ (forget₂ ProfiniteGrp Profinite))) }

@[to_additive]
/-
**ProfiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `ProfiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompactSpace (limitConePtAux F) :=
  inferInstanceAs (CompactSpace (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt)

/-- The abbreviation for the limit of `ProfiniteGrp`s. -/
@[to_additive /-- The abbreviation for the limit of `ProfiniteAddGrp`s. -/]
/-
**ProfiniteGrp.limit** 是 Mathlib 中的一个缩写定义，位于命名空间 `ProfiniteGrp`。
形式化陈述：limit : ProfiniteGrp
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ProfiniteGrp.instCompactSpaceSubtypeForallCarrierToTopTotallyDisconnecte
dSpaceToProfiniteObjMemSubgroupLimitConePtAux`：∀ {J : Type v} [inst : CategoryTh
eory.SmallCategory J] (F : CategoryTheory.Functor J ProfiniteGrp.{max v u}),   C
ompactSpace ↥(ProfiniteGrp.…

--- 原说明 ---
The abbreviation for the limit of `ProfiniteGrp`s.
-/
abbrev limit : ProfiniteGrp := ProfiniteGrp.of (ProfiniteGrp.limitConePtAux F)

@[to_additive (attr := ext)]
/-
**ProfiniteGrp.limit_ext** 是 Mathlib 中的一个引理，位于命名空间 `ProfiniteGrp`。
形式化陈述：limit_ext (x y : limit F) (hxy : forall j, x.val j = y.val j) : x = y
参数：x y : limit F；hxy : forall j, x.val j = y.val j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma limit_ext (x y : limit F) (hxy : ∀ j, x.val j = y.val j) : x = y :=
  Subtype.ext (funext hxy)

@[to_additive (attr := simp)]
/-
**ProfiniteGrp.limit_one_val** 是 Mathlib 中的一个引理，位于命名空间 `ProfiniteGrp`。
形式化陈述：limit_one_val (j : J) : (1 : limit F).val j = 1
参数：j : J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma limit_one_val (j : J) : (1 : limit F).val j = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**ProfiniteGrp.limit_mul_val** 是 Mathlib 中的一个引理，位于命名空间 `ProfiniteGrp`。
形式化陈述：limit_mul_val (x y : limit F) (j : J) : (x * y).val j = x.val j * y.val j
参数：x y : limit F；j : J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma limit_mul_val (x y : limit F) (j : J) : (x * y).val j = x.val j * y.val j :=
  rfl

end ProfiniteGrp

end Limits

