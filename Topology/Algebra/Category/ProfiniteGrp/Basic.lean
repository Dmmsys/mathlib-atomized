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
/--
Definition of `ProfiniteGrp` / `ProfiniteGrp` 的定义

English:
structure ProfiniteGrp
  parameters: where
  axioms and operations (3):
    - toProfinite : Profinite.{u}
    - [group : Group toProfinite]
    - [topologicalGroup : IsTopologicalGroup toProfinite]

中文:
结构 ProfiniteGrp
  参数: where
  公理与运算 (3 个):
    - toProfinite : Profinite.{u}
    - [group : Group toProfinite]
    - [topologicalGroup : IsTopologicalGroup toProfinite]
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
/--
Definition of `ProfiniteAddGrp` / `ProfiniteAddGrp` 的定义

English:
structure ProfiniteAddGrp
  parameters: where
  axioms and operations (3):
    - toProfinite : Profinite.{u}
    - [addGroup : AddGroup toProfinite]
    - [topologicalAddGroup : IsTopologicalAddGroup toProfinite]

中文:
结构 ProfiniteAddGrp
  参数: where
  公理与运算 (3 个):
    - toProfinite : Profinite.{u}
    - [addGroup : AddGroup toProfinite]
    - [topologicalAddGroup : IsTopologicalAddGroup toProfinite]
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
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort ProfiniteGrp (Type u)
  body: G.toProfinite

中文:
实例 :
  签名: CoeSort ProfiniteGrp (类型u)
  定义体: G.toProfinite
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
/--
Definition of `ProfiniteGrp.of` / `ProfiniteGrp.of` 的定义

English:
abbreviation ProfiniteGrp.of
  signature: (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  body: .of G
  group := ‹_›
  topologicalGroup := ‹_›

@[to_additive]

中文:
缩写 ProfiniteGrp.of
  签名: (G : 类型u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  定义体: .of G
  group := ‹_›
  topologicalGroup := ‹_›

@[to_additive]
-/
abbrev ProfiniteGrp.of (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] : ProfiniteGrp.{u} where
  toProfinite := .of G
  group := ‹_›
  topologicalGroup := ‹_›

@[to_additive]
/--
lemma `ProfiniteGrp.coe_of` / 引理 `ProfiniteGrp.coe_of`

English:
lemma ProfiniteGrp.coe_of
  statement: (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  proof: rfl

中文:
引理 ProfiniteGrp.coe_of
  结论: (G : 类型u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  证明: rfl
-/
lemma ProfiniteGrp.coe_of (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] : (ProfiniteGrp.of G : Type u) = G :=
  rfl

/-- The type of morphisms in `ProfiniteAddGrp`. -/
@[ext]
/--
Definition of `ProfiniteAddGrp.Hom` / `ProfiniteAddGrp.Hom` 的定义

English:
structure ProfiniteAddGrp.Hom
  parameters: (A B : ProfiniteAddGrp.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->ₜ+ B

中文:
结构 ProfiniteAddGrp.Hom
  参数: (A B : ProfiniteAddGrp.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->ₜ+ B
-/
structure ProfiniteAddGrp.Hom (A B : ProfiniteAddGrp.{u}) where
  private mk ::
  /-- The underlying `ContinuousAddMonoidHom`. -/
  hom' : A ->ₜ+ B

/-- The type of morphisms in `ProfiniteGrp`. -/
@[to_additive existing (attr := ext)]
/--
Definition of `ProfiniteGrp.Hom` / `ProfiniteGrp.Hom` 的定义

English:
structure ProfiniteGrp.Hom
  parameters: (A B : ProfiniteGrp.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : A ->ₜ* B

中文:
结构 ProfiniteGrp.Hom
  参数: (A B : ProfiniteGrp.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A ->ₜ* B
-/
structure ProfiniteGrp.Hom (A B : ProfiniteGrp.{u}) where
  private mk ::
  /-- The underlying `ContinuousMonoidHom`. -/
  hom' : A ->ₜ* B

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category ProfiniteGrp
  body: ProfiniteGrp.Hom A B
  id A := ⟨ContinuousMonoidHom.id A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: Category ProfiniteGrp
  定义体: ProfiniteGrp.Hom A B
  id A := ⟨ContinuousMonoidHom.id A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category ProfiniteGrp where
  Hom A B := ProfiniteGrp.Hom A B
  id A := ⟨ContinuousMonoidHom.id A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory ProfiniteGrp (fun X Y => X ->ₜ* Y)
  body: f.hom'
  ofHom f := ⟨f⟩

中文:
实例 :
  签名: ConcreteCategory ProfiniteGrp (fun X Y => X ->ₜ* Y)
  定义体: f.hom'
  ofHom f := ⟨f⟩
-/
instance : ConcreteCategory ProfiniteGrp (fun X Y => X ->ₜ* Y) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- The underlying `ContinuousMonoidHom`. -/
@[to_additive /-- The underlying `ContinuousAddMonoidHom`. -/]
/--
Definition of `ProfiniteGrp.Hom.hom` / `ProfiniteGrp.Hom.hom` 的定义

English:
abbreviation ProfiniteGrp.Hom.hom
  signature: {M N : ProfiniteGrp.{u}} (f : ProfiniteGrp.Hom M N)
  body: ConcreteCategory.hom (C := ProfiniteGrp) f

中文:
缩写 ProfiniteGrp.Hom.hom
  签名: {M N : ProfiniteGrp.{u}} (f : ProfiniteGrp.Hom M N)
  定义体: ConcreteCategory.hom (C := ProfiniteGrp) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, ProfiniteGrp
-/
abbrev ProfiniteGrp.Hom.hom {M N : ProfiniteGrp.{u}} (f : ProfiniteGrp.Hom M N) :
    M ->ₜ* N :=
  ConcreteCategory.hom (C := ProfiniteGrp) f

/-- Typecheck a `ContinuousMonoidHom` as a morphism in `ProfiniteGrp`. -/
@[to_additive /-- Typecheck a `ContinuousAddMonoidHom` as a morphism in `ProfiniteAddGrp`. -/]
/--
Definition of `ProfiniteGrp.ofHom` / `ProfiniteGrp.ofHom` 的定义

English:
abbreviation ProfiniteGrp.ofHom
  signature: {X Y : Type u} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
  body: ConcreteCategory.ofHom f

中文:
缩写 ProfiniteGrp.ofHom
  签名: {X Y : 类型u} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
  定义体: ConcreteCategory.ofHom f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ProfiniteGrp.ofHom {X Y : Type u} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [CompactSpace X] [TotallyDisconnectedSpace X] [Group Y] [TopologicalSpace Y]
    [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y]
    (f : X ->ₜ* Y) : ProfiniteGrp.of X ⟶ ProfiniteGrp.of Y :=
  ConcreteCategory.ofHom f

namespace ProfiniteGrp

@[to_additive]
instance {M N : ProfiniteGrp.{u}} : CoeFun (M ⟶ N) (fun _ => M -> N) where
  coe f := f.hom

@[to_additive (attr := simp)]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {A : ProfiniteGrp.{u}}
  statement: (𝟙 A : A ⟶ A).hom = ContinuousMonoidHom.id A
  proof: rfl

中文:
引理 hom_id
  条件: {A : ProfiniteGrp.{u}}
  结论: (𝟙 A : A ⟶ A).hom = ContinuousMonoidHom.id A
  证明: rfl
-/
lemma hom_id {A : ProfiniteGrp.{u}} : (𝟙 A : A ⟶ A).hom = ContinuousMonoidHom.id A := rfl

/- Provided for rewriting. -/
@[to_additive]
/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (A : ProfiniteGrp.{u}) (a : A)
  proof: by simp

@[to_additive (attr := simp)]

中文:
引理 id_apply
  条件: (A : ProfiniteGrp.{u}) (a : A)
  证明: by simp

@[to_additive (attr := simp)]
-/
lemma id_apply (A : ProfiniteGrp.{u}) (a : A) :
    (𝟙 A : A ⟶ A) a = a := by simp

@[to_additive (attr := simp)]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {A B C : ProfiniteGrp.{u}} (f : A ⟶ B) (g : B ⟶ C)
  proof: rfl

中文:
引理 hom_comp
  条件: {A B C : ProfiniteGrp.{u}} (f : A ⟶ B) (g : B ⟶ C)
  证明: rfl
-/
lemma hom_comp {A B C : ProfiniteGrp.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {A B C : ProfiniteGrp.{u}} (f : A ⟶ B) (g : B ⟶ C) (a : A)
  proof: by
  simp only [hom_comp, ContinuousMonoidHom.comp_toFun]

@[to_additive (attr := ext)]

中文:
引理 comp_apply
  条件: {A B C : ProfiniteGrp.{u}} (f : A ⟶ B) (g : B ⟶ C) (a : A)
  证明: by
  simp only [hom_comp, ContinuousMonoidHom.comp_toFun]

@[to_additive (attr := ext)]

Depends on / 依赖: ContinuousMonoidHom, ContinuousMonoidHom.comp_toFun, comp_toFun, hom_comp
-/
lemma comp_apply {A B C : ProfiniteGrp.{u}} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := by
  simp only [hom_comp, ContinuousMonoidHom.comp_toFun]

@[to_additive (attr := ext)]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {A B : ProfiniteGrp.{u}} {f g : A ⟶ B} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

中文:
引理 hom_ext
  条件: {A B : ProfiniteGrp.{u}} {f g : A ⟶ B} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {A B : ProfiniteGrp.{u}} {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

variable {X Y Z : Type u} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [CompactSpace X] [TotallyDisconnectedSpace X] [Group Y] [TopologicalSpace Y]
    [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] [Group Z]
    [TopologicalSpace Z] [IsTopologicalGroup Z] [CompactSpace Z] [TotallyDisconnectedSpace Z]

@[to_additive (attr := simp)]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: (f : X ->ₜ* Y)
  statement: (ofHom f).hom = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 hom_ofHom
  条件: (f : X ->ₜ* Y)
  结论: (ofHom f).hom = f
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma hom_ofHom (f : X ->ₜ* Y) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {A B : ProfiniteGrp.{u}} (f : A ⟶ B)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 ofHom_hom
  条件: {A B : ProfiniteGrp.{u}} (f : A ⟶ B)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma ofHom_hom {A B : ProfiniteGrp.{u}} (f : A ⟶ B) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  statement: ofHom (ContinuousMonoidHom.id X) = 𝟙 (of X)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 ofHom_id
  结论: ofHom (ContinuousMonoidHom.id X) = 𝟙 (of X)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma ofHom_id : ofHom (ContinuousMonoidHom.id X) = 𝟙 (of X) := rfl

@[to_additive (attr := simp)]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  given: (f : X ->ₜ* Y) (g : Y ->ₜ* Z)
  proof: rfl

@[to_additive]

中文:
引理 ofHom_comp
  条件: (f : X ->ₜ* Y) (g : Y ->ₜ* Z)
  证明: rfl

@[to_additive]
-/
lemma ofHom_comp (f : X ->ₜ* Y) (g : Y ->ₜ* Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: (f : X ->ₜ* Y) (x : X)
  statement: ofHom f x = f x
  proof: rfl

@[to_additive]

中文:
引理 ofHom_apply
  条件: (f : X ->ₜ* Y) (x : X)
  结论: ofHom f x = f x
  证明: rfl

@[to_additive]
-/
lemma ofHom_apply (f : X ->ₜ* Y) (x : X) : ofHom f x = f x := rfl

@[to_additive]
/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {A B : ProfiniteGrp.{u}} (e : A ≅ B) (x : A)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

@[to_additive]

中文:
引理 inv_hom_apply
  条件: {A B : ProfiniteGrp.{u}} (e : A ≅ B) (x : A)
  结论: e.inv (e.hom x) = x
  证明: by
  simp

@[to_additive]
-/
lemma inv_hom_apply {A B : ProfiniteGrp.{u}} (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by
  simp

@[to_additive]
/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {A B : ProfiniteGrp.{u}} (e : A ≅ B) (x : B)
  statement: e.hom (e.inv x) = x
  proof: by
  simp

@[to_additive (attr := simp)]

中文:
引理 hom_inv_apply
  条件: {A B : ProfiniteGrp.{u}} (e : A ≅ B) (x : B)
  结论: e.hom (e.inv x) = x
  证明: by
  simp

@[to_additive (attr := simp)]
-/
lemma hom_inv_apply {A B : ProfiniteGrp.{u}} (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by
  simp

@[to_additive (attr := simp)]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  given: (X : ProfiniteGrp)
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_id
  条件: (X : ProfiniteGrp)
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_id (X : ProfiniteGrp) : (𝟙 X : X -> X) = id :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: {X Y Z : ProfiniteGrp} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
定理 coe_comp
  条件: {X Y Z : ProfiniteGrp} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
theorem coe_comp {X Y Z : ProfiniteGrp} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : X -> Z) = g ∘ f :=
  rfl

/-- Construct a term of `ProfiniteGrp` from a type endowed with the structure of a
profinite topological group. -/
@[to_additive /-- Construct a term of `ProfiniteAddGrp` from a type endowed with the structure of a
profinite topological additive group. -/]
/--
Definition of `ofProfinite` / `ofProfinite` 的定义

English:
abbreviation ofProfinite
  signature: (G : Profinite) [Group G] [IsTopologicalGroup G]
  body: of G

中文:
缩写 ofProfinite
  签名: (G : Profinite) [Group G] [IsTopologicalGroup G]
  定义体: of G
-/
abbrev ofProfinite (G : Profinite) [Group G] [IsTopologicalGroup G] :
    ProfiniteGrp := of G

/-- The pi-type of profinite groups is a profinite group. -/
@[to_additive /-- The pi-type of profinite additive groups is a
profinite additive group. -/]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: {α : Type u} (β : α -> ProfiniteGrp)
  body: let pitype := Profinite.pi fun (a : α) => (β a).toProfinite
  letI (a : α) : Group (β a).toProfinite := (β a).group
  letI : Group pitype := Pi.group
  letI : IsTopologicalGroup pitype := Pi.topologicalGroup
  ofProfinite pitype

中文:
定义 pi
  签名: {α : 类型u} (β : α -> ProfiniteGrp)
  定义体: let pitype := Profinite.pi fun (a : α) => (β a).toProfinite
  letI (a : α) : Group (β a).toProfinite := (β a).group
  letI : Group pitype := Pi.group
  letI : IsTopologicalGroup pitype := Pi.topologicalGroup
  ofProfinite pitype

Depends on / 依赖: IsTopologicalGroup, Pi.group, Pi.topologicalGroup, Profinite, Profinite.pi, ofProfinite, pitype, toProfinite, topologicalGroup
-/
def pi {α : Type u} (β : α -> ProfiniteGrp) : ProfiniteGrp :=
  let pitype := Profinite.pi fun (a : α) => (β a).toProfinite
  letI (a : α) : Group (β a).toProfinite := (β a).group
  letI : Group pitype := Pi.group
  letI : IsTopologicalGroup pitype := Pi.topologicalGroup
  ofProfinite pitype

/-- A `FiniteGrp` when given the discrete topology can be considered as a profinite group. -/
@[to_additive /-- A `FiniteAddGrp` when given the discrete topology can be considered as a
profinite additive group. -/]
/--
Definition of `ofFiniteGrp` / `ofFiniteGrp` 的定义

English:
definition ofFiniteGrp
  signature: (G : FiniteGrp)
  body: letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : IsTopologicalGroup G := {}
  of G

中文:
定义 ofFiniteGrp
  签名: (G : FiniteGrp)
  定义体: letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : IsTopologicalGroup G := {}
  of G

Depends on / 依赖: DiscreteTopology, IsTopologicalGroup, TopologicalSpace
-/
def ofFiniteGrp (G : FiniteGrp) : ProfiniteGrp :=
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : IsTopologicalGroup G := {}
  of G

/-- A morphism of `FiniteGrp` induces a morphism of the associated profinite groups. -/
@[to_additive /-- A morphism of `FiniteAddGrp` induces a morphism of the associated profinite
additive groups. -/]
/--
Definition of `ofFiniteGrpHom` / `ofFiniteGrpHom` 的定义

English:
definition ofFiniteGrpHom
  signature: {G H : FiniteGrp.{u}} (f : G ⟶ H)
  body: ConcreteCategory.ofHom ⟨f.hom.hom, by fun_prop⟩

@[to_additive]

中文:
定义 ofFiniteGrpHom
  签名: {G H : FiniteGrp.{u}} (f : G ⟶ H)
  定义体: ConcreteCategory.ofHom ⟨f.hom.hom, by fun_prop⟩

@[to_additive]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, f.hom.hom, fun_prop
-/
def ofFiniteGrpHom {G H : FiniteGrp.{u}} (f : G ⟶ H) : ofFiniteGrp G ⟶ ofFiniteGrp H :=
  ConcreteCategory.ofHom ⟨f.hom.hom, by fun_prop⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ FiniteGrp ProfiniteGrp
  body: { obj := ofFiniteGrp
    map := ofFiniteGrpHom }

@[to_additive]

中文:
实例 :
  签名: HasForget₂ FiniteGrp ProfiniteGrp
  定义体: { obj := ofFiniteGrp
    map := ofFiniteGrpHom }

@[to_additive]

Depends on / 依赖: ofFiniteGrp, ofFiniteGrpHom
-/
instance : HasForget₂ FiniteGrp ProfiniteGrp where
  forget₂ :=
  { obj := ofFiniteGrp
    map := ofFiniteGrpHom }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ ProfiniteGrp GrpCat
  body: GrpCat.of P
  forget₂.map f := GrpCat.ofHom f.hom.toMonoidHom

中文:
实例 :
  签名: HasForget₂ ProfiniteGrp GrpCat
  定义体: GrpCat.of P
  forget₂.map f := GrpCat.ofHom f.hom.toMonoidHom

Depends on / 依赖: GrpCat, GrpCat.of
-/
instance : HasForget₂ ProfiniteGrp GrpCat where
  forget₂.obj P := GrpCat.of P
  forget₂.map f := GrpCat.ofHom f.hom.toMonoidHom

/-- A closed subgroup of a profinite group is profinite. -/
@[to_additive /-- A closed additive subgroup of a profinite additive group is profinite. -/]
/--
Definition of `ofClosedSubgroup` / `ofClosedSubgroup` 的定义

English:
definition ofClosedSubgroup
  signature: {G : ProfiniteGrp} (H : ClosedSubgroup G)
  body: letI : CompactSpace H := inferInstance
  of H.1

中文:
定义 ofClosedSubgroup
  签名: {G : ProfiniteGrp} (H : ClosedSubgroup G)
  定义体: letI : CompactSpace H := inferInstance
  of H.1

Depends on / 依赖: CompactSpace
-/
def ofClosedSubgroup {G : ProfiniteGrp} (H : ClosedSubgroup G) : ProfiniteGrp :=
  letI : CompactSpace H := inferInstance
  of H.1

/-- A topological group that has a `ContinuousMulEquiv` to a profinite group is profinite. -/
@[to_additive /-- A topological additive group that has a `ContinuousAddEquiv` to a
profinite additive group is profinite. -/]
/--
Definition of `ofContinuousMulEquiv` / `ofContinuousMulEquiv` 的定义

English:
definition ofContinuousMulEquiv
  signature: {G : ProfiniteGrp.{u}} {H : Type v} [TopologicalSpace H]
  body: let _ : CompactSpace H := Homeomorph.compactSpace e.toHomeomorph
  let _ : TotallyDisconnectedSpace H := Homeomorph.totallyDisconnectedSpace e.toHomeomorph
  .of H

中文:
定义 ofContinuousMulEquiv
  签名: {G : ProfiniteGrp.{u}} {H : 类型v} [TopologicalSpace H]
  定义体: let _ : CompactSpace H := Homeomorph.compactSpace e.toHomeomorph
  let _ : TotallyDisconnectedSpace H := Homeomorph.totallyDisconnectedSpace e.toHomeomorph
  .of H

Depends on / 依赖: CompactSpace, Homeomorph, Homeomorph.compactSpace, Homeomorph.totallyDisconnectedSpace, TotallyDisconnectedSpace, compactSpace, e.toHomeomorph, toHomeomorph, totallyDisconnectedSpace
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
/--
Definition of `ContinuousMulEquiv.toProfiniteGrpIso` / `ContinuousMulEquiv.toProfiniteGrpIso` 的定义

English:
definition ContinuousMulEquiv.toProfiniteGrpIso
  signature: {X Y : ProfiniteGrp} (e : X ≃ₜ* Y)
  body: ofHom e
  inv := ofHom e.symm

中文:
定义 ContinuousMulEquiv.toProfiniteGrpIso
  签名: {X Y : ProfiniteGrp} (e : X ≃ₜ* Y)
  定义体: ofHom e
  inv := ofHom e.symm
-/
def ContinuousMulEquiv.toProfiniteGrpIso {X Y : ProfiniteGrp} (e : X ≃ₜ* Y) : X ≅ Y where
  hom := ofHom e
  inv := ofHom e.symm

/-- The functor mapping a profinite group to its underlying profinite space. -/
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ ProfiniteGrp Profinite
  body: {
    obj G := G.toProfinite
    map f := CompHausLike.ofHom _ ⟨f, by fun_prop⟩}

@[to_additive]

中文:
实例 :
  签名: HasForget₂ ProfiniteGrp Profinite
  定义体: {
    obj G := G.toProfinite
    map f := CompHausLike.ofHom _ ⟨f, by fun_prop⟩}

@[to_additive]
-/
instance : HasForget₂ ProfiniteGrp Profinite where
  forget₂ := {
    obj G := G.toProfinite
    map f := CompHausLike.ofHom _ ⟨f, by fun_prop⟩}

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ ProfiniteGrp Profinite).Faithful
  body: {
  map_injective := fun {_ _} _ _ h =>
    ConcreteCategory.hom_ext _ _ fun x => CategoryTheory.congr_fun h x }

@[to_additive]

中文:
实例 :
  签名: (forget₂ ProfiniteGrp Profinite).Faithful
  定义体: {
  map_injective := fun {_ _} _ _ h =>
    ConcreteCategory.hom_ext _ _ fun x => CategoryTheory.congr_fun h x }

@[to_additive]
-/
instance : (forget₂ ProfiniteGrp Profinite).Faithful := {
  map_injective := fun {_ _} _ _ h =>
    ConcreteCategory.hom_ext _ _ fun x => CategoryTheory.congr_fun h x }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ ProfiniteGrp Profinite).ReflectsIsomorphisms
  body: by
    let i := asIso ((forget₂ ProfiniteGrp Profinite).map f)
    let e : X ≃ₜ* Y :=
      { CompHausLike.homeoOfIso i with
          map_mul' := map_mul f.hom }
    exact (ContinuousMulEquiv.toProfiniteGrpIso e).isIso_hom

@[to_additive]

中文:
实例 :
  签名: (forget₂ ProfiniteGrp Profinite).ReflectsIsomorphisms
  定义体: by
    let i := asIso ((forget₂ ProfiniteGrp Profinite).map f)
    let e : X ≃ₜ* Y :=
      { CompHausLike.homeoOfIso i with
          map_mul' := map_mul f.hom }
    exact (ContinuousMulEquiv.toProfiniteGrpIso e).isIso_hom

@[to_additive]

Depends on / 依赖: CompHausLike, CompHausLike.homeoOfIso, ContinuousMulEquiv, ContinuousMulEquiv.toProfiniteGrpIso, Profinite, ProfiniteGrp, f.hom, homeoOfIso, isIso_hom, map_mul, toProfiniteGrpIso
-/
instance : (forget₂ ProfiniteGrp Profinite).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget₂ ProfiniteGrp Profinite).map f)
    let e : X ≃ₜ* Y :=
      { CompHausLike.homeoOfIso i with
          map_mul' := map_mul f.hom }
    exact (ContinuousMulEquiv.toProfiniteGrpIso e).isIso_hom

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget ProfiniteGrp.{u}).ReflectsIsomorphisms
  body: CategoryTheory.reflectsIsomorphisms_comp (forget₂ ProfiniteGrp Profinite) (forget Profinite)

中文:
实例 :
  签名: (forget ProfiniteGrp.{u}).ReflectsIsomorphisms
  定义体: CategoryTheory.reflectsIsomorphisms_comp (forget₂ ProfiniteGrp Profinite) (forget Profinite)

Depends on / 依赖: CategoryTheory, CategoryTheory.reflectsIsomorphisms_comp, Profinite, ProfiniteGrp, forget, reflectsIsomorphisms_comp
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
/--
Definition of `limitConePtAux` / `limitConePtAux` 的定义

English:
definition limitConePtAux
  signature: : Subgroup (Π j : J, F.obj j) where
  body: {x | forall ⦃i j : J⦄ (π : i ⟶ j), F.map π (x i) = x j}
  mul_mem' hx hy _ _ π := by simp only [Pi.mul_apply, map_mul, hx π, hy π]
  one_mem' := by simp only [Set.mem_ofPred_eq, Pi.one_apply, map_one, implies_true]
  inv_mem' h _ _ π := by simp only [Pi.inv_apply, map_inv, h π]

@[to_additive]

中文:
定义 limitConePtAux
  签名: : Subgroup (Π j : J, F.obj j) where
  定义体: {x | forall ⦃i j : J⦄ (π : i ⟶ j), F.map π (x i) = x j}
  mul_mem' hx hy _ _ π := by simp only [Pi.mul_apply, map_mul, hx π, hy π]
  one_mem' := by simp only [Set.mem_ofPred_eq, Pi.one_apply, map_one, implies_true]
  inv_mem' h _ _ π := by simp only [Pi.inv_apply, map_inv, h π]

@[to_additive]

Depends on / 依赖: F.map
-/
def limitConePtAux : Subgroup (Π j : J, F.obj j) where
  carrier := {x | forall ⦃i j : J⦄ (π : i ⟶ j), F.map π (x i) = x j}
  mul_mem' hx hy _ _ π := by simp only [Pi.mul_apply, map_mul, hx π, hy π]
  one_mem' := by simp only [Set.mem_ofPred_eq, Pi.one_apply, map_one, implies_true]
  inv_mem' h _ _ π := by simp only [Pi.inv_apply, map_inv, h π]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt
  body: inferInstanceAs (Group (limitConePtAux F))

@[to_additive]

中文:
实例 :
  签名: Group (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt
  定义体: inferInstanceAs (Group (limitConePtAux F))

@[to_additive]

Depends on / 依赖: limitConePtAux
-/
instance : Group (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt :=
  inferInstanceAs (Group (limitConePtAux F))

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalGroup (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt
  body: inferInstanceAs (IsTopologicalGroup (limitConePtAux F))

中文:
实例 :
  签名: IsTopologicalGroup (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt
  定义体: inferInstanceAs (IsTopologicalGroup (limitConePtAux F))

Depends on / 依赖: IsTopologicalGroup, limitConePtAux
-/
instance : IsTopologicalGroup (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt :=
  inferInstanceAs (IsTopologicalGroup (limitConePtAux F))

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The explicit limit cone in `ProfiniteGrp`. -/
@[to_additive /-- The explicit limit cone in `ProfiniteAddGrp`. -/]
/--
Definition of `limitCone` / `limitCone` 的定义

English:
abbreviation limitCone
  signature: : Limits.Cone F where
  body: ofProfinite (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt
  π :=
  { app := fun j => ⟨{
      toFun := fun x => x.1 j
      map_one' := rfl
      map_mul' := fun x y => rfl
      continuous_toFun := by
        exact (continuous_apply j).comp (continuous_iff_le_induced.mpr fun U a =

中文:
缩写 limitCone
  签名: : Limits.Cone F where
  定义体: ofProfinite (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt
  π :=
  { app := fun j => ⟨{
      toFun := fun x => x.1 j
      map_one' := rfl
      map_mul' := fun x y => rfl
      continuous_toFun := by
        exact (continuous_apply j).comp (continuous_iff_le_induced.mpr fun U a =

Depends on / 依赖: Profinite, Profinite.limitCone, ProfiniteGrp, limitCone, ofProfinite
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
/--
Definition of `limitConeIsLimit` / `limitConeIsLimit` 的定义

English:
definition limitConeIsLimit
  signature: : Limits.IsLimit (limitCone F) where
  body: ofHom
    { ((Profinite.limitConeIsLimit (F ⋙ (forget₂ ProfiniteGrp Profinite))).lift
        ((forget₂ ProfiniteGrp Profinite).mapCone cone)).hom.hom with
      map_one' := Subtype.ext (funext fun j => map_one (cone.π.app j).hom)
      -- TODO: investigate whether it's possible to set up `ext` lemm

中文:
定义 limitConeIsLimit
  签名: : Limits.IsLimit (limitCone F) where
  定义体: ofHom
    { ((Profinite.limitConeIsLimit (F ⋙ (forget₂ ProfiniteGrp Profinite))).lift
        ((forget₂ ProfiniteGrp Profinite).mapCone cone)).hom.hom with
      map_one' := Subtype.ext (funext fun j => map_one (cone.π.app j).hom)
      -- TODO: investigate whether it's possible to set up `ext` lemm
-/
def limitConeIsLimit : Limits.IsLimit (limitCone F) where
  lift cone := ofHom
    { ((Profinite.limitConeIsLimit (F ⋙ (forget₂ ProfiniteGrp Profinite))).lift
        ((forget₂ ProfiniteGrp Profinite).mapCone cone)).hom.hom with
      map_one' := Subtype.ext (funext fun j => map_one (cone.π.app j).hom)
      -- TODO: investigate whether it's possible to set up `ext` lemmas for the `TopCat`-related
      -- categories so that `by ext j; exact map_one (cone.π.app j)` works here, similarly below.
      map_mul' := fun _ _ => Subtype.ext (funext fun j => map_mul (cone.π.app j).hom _ _) }
  uniq cone m h := by
    apply (forget₂ ProfiniteGrp Profinite).map_injective
    simpa using! (Profinite.limitConeIsLimit (F ⋙ (forget₂ ProfiniteGrp Profinite))).uniq
      ((forget₂ ProfiniteGrp Profinite).mapCone cone) ((forget₂ ProfiniteGrp Profinite).map m)
      (fun j => congrArg (forget₂ ProfiniteGrp Profinite).map (h j))

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.HasLimit F
  body: Nonempty.intro
    { cone := limitCone F
      isLimit := limitConeIsLimit F }

@[to_additive]

中文:
实例 :
  签名: Limits.HasLimit F
  定义体: Nonempty.intro
    { cone := limitCone F
      isLimit := limitConeIsLimit F }

@[to_additive]

Depends on / 依赖: Nonempty, Nonempty.intro
-/
instance : Limits.HasLimit F where
  exists_limit := Nonempty.intro
    { cone := limitCone F
      isLimit := limitConeIsLimit F }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.PreservesLimits (forget₂ ProfiniteGrp Profinite)
  body: {
    preservesLimit := fun {F} => CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone
      (limitConeIsLimit F) (Profinite.limitConeIsLimit (F ⋙ (forget₂ ProfiniteGrp Profinite))) }

@[to_additive]

中文:
实例 :
  签名: Limits.PreservesLimits (forget₂ ProfiniteGrp Profinite)
  定义体: {
    preservesLimit := fun {F} => CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone
      (limitConeIsLimit F) (Profinite.limitConeIsLimit (F ⋙ (forget₂ ProfiniteGrp Profinite))) }

@[to_additive]
-/
instance : Limits.PreservesLimits (forget₂ ProfiniteGrp Profinite) where
  preservesLimitsOfShape := {
    preservesLimit := fun {F} => CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone
      (limitConeIsLimit F) (Profinite.limitConeIsLimit (F ⋙ (forget₂ ProfiniteGrp Profinite))) }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompactSpace (limitConePtAux F)
  body: inferInstanceAs (CompactSpace (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt)

中文:
实例 :
  签名: CompactSpace (limitConePtAux F)
  定义体: inferInstanceAs (CompactSpace (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt)

Depends on / 依赖: CompactSpace, Profinite, Profinite.limitCone, ProfiniteGrp, limitCone
-/
instance : CompactSpace (limitConePtAux F) :=
  inferInstanceAs (CompactSpace (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt)

/-- The abbreviation for the limit of `ProfiniteGrp`s. -/
@[to_additive /-- The abbreviation for the limit of `ProfiniteAddGrp`s. -/]
/--
Definition of `limit` / `limit` 的定义

English:
abbreviation limit
  signature: : ProfiniteGrp
  body: ProfiniteGrp.of (ProfiniteGrp.limitConePtAux F)

@[to_additive (attr := ext)]

中文:
缩写 limit
  签名: : ProfiniteGrp
  定义体: ProfiniteGrp.of (ProfiniteGrp.limitConePtAux F)

@[to_additive (attr := ext)]

Depends on / 依赖: ProfiniteGrp, ProfiniteGrp.limitConePtAux, ProfiniteGrp.of, limitConePtAux
-/
abbrev limit : ProfiniteGrp := ProfiniteGrp.of (ProfiniteGrp.limitConePtAux F)

@[to_additive (attr := ext)]
/--
lemma `limit_ext` / 引理 `limit_ext`

English:
lemma limit_ext
  given: (x y : limit F) (hxy : forall j, x.val j = y.val j)
  statement: x = y
  proof: Subtype.ext (funext hxy)

@[to_additive (attr := simp)]

中文:
引理 limit_ext
  条件: (x y : limit F) (hxy : 对任意 j, x.val j = y.val j)
  结论: x = y
  证明: Subtype.ext (funext hxy)

@[to_additive (attr := simp)]

Depends on / 依赖: Subtype, Subtype.ext
-/
lemma limit_ext (x y : limit F) (hxy : forall j, x.val j = y.val j) : x = y :=
  Subtype.ext (funext hxy)

@[to_additive (attr := simp)]
/--
lemma `limit_one_val` / 引理 `limit_one_val`

English:
lemma limit_one_val
  given: (j : J)
  statement: (1 : limit F).val j = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 limit_one_val
  条件: (j : J)
  结论: (1 : limit F).val j = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma limit_one_val (j : J) : (1 : limit F).val j = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `limit_mul_val` / 引理 `limit_mul_val`

English:
lemma limit_mul_val
  given: (x y : limit F) (j : J)
  statement: (x * y).val j = x.val j * y.val j
  proof: rfl

中文:
引理 limit_mul_val
  条件: (x y : limit F) (j : J)
  结论: (x * y).val j = x.val j * y.val j
  证明: rfl
-/
lemma limit_mul_val (x y : limit F) (j : J) : (x * y).val j = x.val j * y.val j :=
  rfl

end ProfiniteGrp

end Limits
