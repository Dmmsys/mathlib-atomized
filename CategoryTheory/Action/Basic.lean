/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Ring.PUnit
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Tactic.ApplyFun

/-!
# `Action V G`, the category of actions of a monoid `G` inside some category `V`.

The prototypical example is `V = ModuleCat R`,
where `Action (ModuleCat R) G` is the category of `R`-linear representations of `G`.

We check `Action V G ≌ (CategoryTheory.SingleObj G ⥤ V)`,
and construct the restriction functors
`res {G H} [Monoid G] [Monoid H] (f : G →* H) : Action V H ⥤ Action V G`.
-/

@[expose] public section


universe u v

open CategoryTheory Limits

variable (V : Type*) [Category* V]

-- Note: this is _not_ a categorical action of `G` on `V`.
/--
Definition of `Action` / `Action` 的定义

English:
structure Action
  parameters: (G : Type*) [Monoid G]
  axioms and operations (2):
    - V : V
    - ρ : G ->* End V

中文:
结构 作用
  参数: (G : 类型) [幺半群 G]
  公理与运算 (2 个):
    - V : V
    - ρ : G ->* End V
-/
structure Action (G : Type*) [Monoid G] where
  /-- The object this action acts on -/
  V : V
  /-- The underlying monoid homomorphism of this action -/
  ρ : G ->* End V

namespace Action

variable {V}

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `ρ_one` / 定理 `ρ_one`

English:
theorem ρ_one
  given: {G : Type*} [Monoid G] (A : Action V G)
  statement: A.ρ 1 = 𝟙 A.V
  proof: by simp

中文:
定理 ρ_one
  条件: {G : 类型} [幺半群 G] (A : 作用 V G)
  结论: A.ρ 1 = 𝟙 A.V
  证明: by simp

Depends on / 依赖: Finite, Finite.exists_type_univ_nonempty_mulEquiv, Limits, Limits.preservesColimitsOfShape_of_equiv, exists_type_univ_nonempty_mulEquiv, he.some.toSingleObjEquiv.symm, preservesColimitsOfShape_of_equiv, toSingleObjEquiv
-/
theorem ρ_one {G : Type*} [Monoid G] (A : Action V G) : A.ρ 1 = 𝟙 A.V := by simp

/-- When a group acts, we can lift the action to the group of automorphisms. -/
@[simps]
/--
Definition of `ρAut` / `ρAut` 的定义

English:
definition ρAut
  signature: {G : Type*} [Group G] (A : Action V G)
  body: { hom := A.ρ g
      inv := A.ρ (g⁻¹ : G)
      hom_inv_id := (A.ρ.map_mul (g⁻¹ : G) g).symm.trans (by rw [inv_mul_cancel, ρ_one])
      inv_hom_id := (A.ρ.map_mul g (g⁻¹ : G)).symm.trans (by rw [mul_inv_cancel, ρ_one]) }
  map_one' := Aut.ext A.ρ.map_one
  map_mul' x y := Aut.ext (A.ρ.map_mul x y)

中文:
定义 ρAut
  签名: {G : 类型} [群 G] (A : 作用 V G)
  定义体: { hom := A.ρ g
      inv := A.ρ (g⁻¹ : G)
      hom_inv_id := (A.ρ.map_mul (g⁻¹ : G) g).symm.trans (by rw [inv_mul_cancel, ρ_one])
      inv_hom_id := (A.ρ.map_mul g (g⁻¹ : G)).symm.trans (by rw [mul_inv_cancel, ρ_one]) }
  map_one' := Aut.ext A.ρ.map_one
  map_mul' x y := Aut.ext (A.ρ.map_mul x y)

Depends on / 依赖: Aut.ext, hom_inv_id, inv_hom_id, inv_mul_cancel, map_mul, map_one, mul_inv_cancel, symm.trans
-/
def ρAut {G : Type*} [Group G] (A : Action V G) : G ->* Aut A.V where
  toFun g :=
    { hom := A.ρ g
      inv := A.ρ (g⁻¹ : G)
      hom_inv_id := (A.ρ.map_mul (g⁻¹ : G) g).symm.trans (by rw [inv_mul_cancel, ρ_one])
      inv_hom_id := (A.ρ.map_mul g (g⁻¹ : G)).symm.trans (by rw [mul_inv_cancel, ρ_one]) }
  map_one' := Aut.ext A.ρ.map_one
  map_mul' x y := Aut.ext (A.ρ.map_mul x y)

variable (G : Type*) [Monoid G]

section

/-- The action defined by sending every monoid element to the identity. -/
@[simps]
/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: (X : V)
  body: { V := X, ρ := 1 }

中文:
定义 trivial
  签名: (X : V)
  定义体: { V := X, ρ := 1 }
-/
def trivial (X : V) : Action V G := { V := X, ρ := 1 }

/--
Instance `inhabited'` / 实例 `inhabited'`

English:
instance inhabited'
  signature: : Inhabited (Action Type* G)
  body: ⟨⟨PUnit, 1⟩⟩

中文:
实例 inhabited'
  签名: : 可居 (作用 类型 G)
  定义体: ⟨⟨PUnit, 1⟩⟩
-/
instance inhabited' : Inhabited (Action Type* G) :=
  ⟨⟨PUnit, 1⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Action AddCommGrpCat G)
  body: ⟨trivial G AddCommGrpCat.of PUnit⟩

中文:
实例 :
  签名: 可居 (作用 加法交换群范畴 G)
  定义体: ⟨trivial G AddCommGrpCat.of PUnit⟩

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.of, hom.app
-/
instance : Inhabited (Action AddCommGrpCat G) :=
⟨trivial G AddCommGrpCat.of PUnit⟩

end

variable {G}

/-- A homomorphism of `Action V G`s is a morphism between the underlying objects,
commuting with the action of `G`.
-/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (M N : Action V G)
  axioms and operations (2):
    - hom : M.V ⟶ N.V
    - comm : forall g : G, M.ρ g ≫ hom = hom ≫ N.ρ g  [default: by cat_disch]

中文:
结构 态射
  参数: (M N : 作用 V G)
  公理与运算 (2 个):
    - hom : M.V ⟶ N.V
    - comm : 对任意 g : G, M.ρ g ≫ hom = hom ≫ N.ρ g  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (M N : Action V G) where
  /-- The morphism between the underlying objects of this action -/
  hom : M.V ⟶ N.V
  comm : forall g : G, M.ρ g ≫ hom = hom ≫ N.ρ g := by cat_disch

namespace Hom

attribute [reassoc] comm
attribute [local simp] comm comm_assoc

set_option backward.isDefEq.respectTransparency.types false in
/-- The identity morphism on an `Action V G`. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (M : Action V G)
  body: 𝟙 M.V

中文:
定义 id
  签名: (M : 作用 V G)
  定义体: 𝟙 M.V
-/
def id (M : Action V G) : Action.Hom M M where hom := 𝟙 M.V

instance (M : Action V G) : Inhabited (Action.Hom M M) :=
  ⟨id M⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The composition of two `Action V G` homomorphisms is the composition of the underlying maps.
-/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {M N K : Action V G} (p : Action.Hom M N) (q : Action.Hom N K)
  body: p.hom ≫ q.hom
  comm := by
    intro g
    simp_all only [comm_assoc, comm, Category.assoc]

中文:
定义 comp
  签名: {M N K : 作用 V G} (p : 作用.态射 M N) (q : 作用.态射 N K)
  定义体: p.hom ≫ q.hom
  comm := by
    intro g
    simp_all only [comm_assoc, comm, Category.assoc]

Depends on / 依赖: p.hom, q.hom
-/
def comp {M N K : Action V G} (p : Action.Hom M N) (q : Action.Hom N K) : Action.Hom M K where
  hom := p.hom ≫ q.hom
  comm := by
    intro g
    simp_all only [comm_assoc, comm, Category.assoc]

end Hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Action V G)
  body: Hom M N
  id M := Hom.id M
  comp f g := Hom.comp f g

中文:
实例 :
  签名: 范畴 (作用 V G)
  定义体: Hom M N
  id M := Hom.id M
  comp f g := Hom.comp f g
-/
instance : Category (Action V G) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp f g := Hom.comp f g

/--
lemma `hom_injective` / 引理 `hom_injective`

English:
lemma hom_injective
  given: {M N : Action V G}
  statement: Function.Injective (Hom.hom : (M ⟶ N) -> (M.V ⟶ N.V))
  proof: fun _ _ => Hom.ext

@[ext]

中文:
引理 hom_injective
  条件: {M N : 作用 V G}
  结论: 函数.单射 (态射.hom : (M ⟶ N) -> (M.V ⟶ N.V))
  证明: fun _ _ => Hom.ext

@[ext]

Depends on / 依赖: Hom.ext
-/
lemma hom_injective {M N : Action V G} : Function.Injective (Hom.hom : (M ⟶ N) -> (M.V ⟶ N.V)) :=
  fun _ _ => Hom.ext

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {M N : Action V G} (φ₁ φ₂ : M ⟶ N) (h : φ₁.hom = φ₂.hom)
  statement: φ₁ = φ₂
  proof: Hom.ext h

中文:
引理 hom_ext
  条件: {M N : 作用 V G} (φ₁ φ₂ : M ⟶ N) (h : φ₁.hom = φ₂.hom)
  结论: φ₁ = φ₂
  证明: Hom.ext h

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {M N : Action V G} (φ₁ φ₂ : M ⟶ N) (h : φ₁.hom = φ₂.hom) : φ₁ = φ₂ :=
  Hom.ext h

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `id_hom` / 定理 `id_hom`

English:
theorem id_hom
  given: (M : Action V G)
  statement: (𝟙 M : Hom M M).hom = 𝟙 M.V
  proof: rfl

中文:
定理 id_hom
  条件: (M : 作用 V G)
  结论: (𝟙 M : 态射 M M).hom = 𝟙 M.V
  证明: rfl
-/
theorem id_hom (M : Action V G) : (𝟙 M : Hom M M).hom = 𝟙 M.V :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp, reassoc]
/--
theorem `comp_hom` / 定理 `comp_hom`

English:
theorem comp_hom
  given: {M N K : Action V G} (f : M ⟶ N) (g : N ⟶ K)
  proof: rfl

@[reassoc (attr := simp)]

中文:
定理 comp_hom
  条件: {M N K : 作用 V G} (f : M ⟶ N) (g : N ⟶ K)
  证明: rfl

@[reassoc (attr := simp)]
-/
theorem comp_hom {M N K : Action V G} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl

@[reassoc (attr := simp)]
/--
theorem `hom_inv_hom` / 定理 `hom_inv_hom`

English:
theorem hom_inv_hom
  given: {M N : Action V G} (f : M ≅ N)
  proof: by
  rw [← comp_hom]; rw [Iso.hom_inv_id]; rw [id_hom]

@[reassoc (attr := simp)]

中文:
定理 hom_inv_hom
  条件: {M N : 作用 V G} (f : M ≅ N)
  证明: by
  rw [← comp_hom]; rw [Iso.hom_inv_id]; rw [id_hom]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id, comp_hom, hom_inv_id, id_hom
-/
theorem hom_inv_hom {M N : Action V G} (f : M ≅ N) :
    f.hom.hom ≫ f.inv.hom = 𝟙 M.V := by
  rw [← comp_hom]; rw [Iso.hom_inv_id]; rw [id_hom]

@[reassoc (attr := simp)]
/--
theorem `inv_hom_hom` / 定理 `inv_hom_hom`

English:
theorem inv_hom_hom
  given: {M N : Action V G} (f : M ≅ N)
  proof: by
  rw [← comp_hom]; rw [Iso.inv_hom_id]; rw [id_hom]

中文:
定理 inv_hom_hom
  条件: {M N : 作用 V G} (f : M ≅ N)
  证明: by
  rw [← comp_hom]; rw [Iso.inv_hom_id]; rw [id_hom]

Depends on / 依赖: Iso.inv_hom_id, comp_hom, id_hom, inv_hom_id
-/
theorem inv_hom_hom {M N : Action V G} (f : M ≅ N) :
    f.inv.hom ≫ f.hom.hom = 𝟙 N.V := by
  rw [← comp_hom]; rw [Iso.inv_hom_id]; rw [id_hom]

set_option backward.isDefEq.respectTransparency.types false in
/-- Construct an isomorphism of `G` actions/representations
from an isomorphism of the underlying objects,
where the forward direction commutes with the group action. -/
@[simps]
/--
Definition of `mkIso` / `mkIso` 的定义

English:
definition mkIso
  signature: {M N : Action V G} (f : M.V ≅ N.V)
  body: { hom := f.hom
      comm := comm }
  inv :=
    { hom := f.inv
      comm := fun g => by have w := comm g =≫ f.inv; simp at w; simp [w] }

中文:
定义 mkIso
  签名: {M N : 作用 V G} (f : M.V ≅ N.V)
  定义体: { hom := f.hom
      comm := comm }
  inv :=
    { hom := f.inv
      comm := fun g => by have w := comm g =≫ f.inv; simp at w; simp [w] }

Depends on / 依赖: cat_disch, f.hom, f.inv
-/
def mkIso {M N : Action V G} (f : M.V ≅ N.V)
    (comm : forall g : G, M.ρ g ≫ f.hom = f.hom ≫ N.ρ g := by cat_disch) : M ≅ N where
  hom :=
    { hom := f.hom
      comm := comm }
  inv :=
    { hom := f.inv
      comm := fun g => by have w := comm g =≫ f.inv; simp at w; simp [w] }

set_option backward.isDefEq.respectTransparency.types false in
instance (priority := 100) isIso_of_hom_isIso {M N : Action V G} (f : M ⟶ N) [IsIso f.hom] :
    IsIso f := (mkIso (asIso f.hom) f.comm).isIso_hom

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `isIso_hom_mk` / 实例 `isIso_hom_mk`

English:
instance isIso_hom_mk
  signature: {M N : Action V G} (f : M.V ⟶ N.V) [IsIso f] (w)
  body: (mkIso (asIso f) w).isIso_hom

中文:
实例 isIso_hom_mk
  签名: {M N : 作用 V G} (f : M.V ⟶ N.V) [是同构 f] (w)
  定义体: (mkIso (asIso f) w).isIso_hom

Depends on / 依赖: isIso_hom
-/
instance isIso_hom_mk {M N : Action V G} (f : M.V ⟶ N.V) [IsIso f] (w) :
    @IsIso _ _ M N (Hom.mk f w) :=
  (mkIso (asIso f) w).isIso_hom

instance {M N : Action V G} (f : M ≅ N) : IsIso f.hom.hom where
  out := ⟨f.inv.hom, by simp⟩

instance {M N : Action V G} (f : M ≅ N) : IsIso f.inv.hom where
  out := ⟨f.hom.hom, by simp⟩

namespace FunctorCategoryEquivalence

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `functorCategoryEquivalence`. -/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : Action V G ⥤ SingleObj G ⥤ V where
  body: { obj := fun _ => M.V
      map := fun g => M.ρ g
      map_id := fun _ => M.ρ.map_one
      map_comp := fun g h => M.ρ.map_mul h g }
  map f :=
    { app := fun _ => f.hom
      naturality := fun _ _ g => f.comm g }

中文:
定义 functor
  签名: : 作用 V G ⥤ SingleObj G ⥤ V where
  定义体: { obj := fun _ => M.V
      map := fun g => M.ρ g
      map_id := fun _ => M.ρ.map_one
      map_comp := fun g h => M.ρ.map_mul h g }
  map f :=
    { app := fun _ => f.hom
      naturality := fun _ _ g => f.comm g }

Depends on / 依赖: f.comm, f.hom, map_comp, map_id, map_mul, map_one, naturality
-/
def functor : Action V G ⥤ SingleObj G ⥤ V where
  obj M :=
    { obj := fun _ => M.V
      map := fun g => M.ρ g
      map_id := fun _ => M.ρ.map_one
      map_comp := fun g h => M.ρ.map_mul h g }
  map f :=
    { app := fun _ => f.hom
      naturality := fun _ _ g => f.comm g }

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `functorCategoryEquivalence`. -/
@[simps]
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : (SingleObj G ⥤ V) ⥤ Action V G where
  body: { V := F.obj PUnit.unit
      ρ :=
        { toFun := fun g => F.map g
          map_one' := F.map_id PUnit.unit
          map_mul' := fun g h => F.map_comp h g } }
  map f :=
    { hom := f.app PUnit.unit
      comm := fun g => f.naturality g }

中文:
定义 inverse
  签名: : (SingleObj G ⥤ V) ⥤ 作用 V G where
  定义体: { V := F.obj PUnit.unit
      ρ :=
        { toFun := fun g => F.map g
          map_one' := F.map_id PUnit.unit
          map_mul' := fun g h => F.map_comp h g } }
  map f :=
    { hom := f.app PUnit.unit
      comm := fun g => f.naturality g }

Depends on / 依赖: F.map, F.map_comp, F.map_id, F.obj, PUnit.unit, f.app, f.naturality, map_comp, map_id, map_mul, map_one, naturality
-/
def inverse : (SingleObj G ⥤ V) ⥤ Action V G where
  obj F :=
    { V := F.obj PUnit.unit
      ρ :=
        { toFun := fun g => F.map g
          map_one' := F.map_id PUnit.unit
          map_mul' := fun g h => F.map_comp h g } }
  map f :=
    { hom := f.app PUnit.unit
      comm := fun g => f.naturality g }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `functorCategoryEquivalence`. -/
@[simps!]
/--
Definition of `unitIso` / `unitIso` 的定义

English:
definition unitIso
  signature: : 𝟭 (Action V G) ≅ functor ⋙ inverse
  body: NatIso.ofComponents fun M => mkIso (Iso.refl _)

中文:
定义 unitIso
  签名: : 𝟭 (作用 V G) ≅ functor ⋙ inverse
  定义体: NatIso.ofComponents fun M => mkIso (Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def unitIso : 𝟭 (Action V G) ≅ functor ⋙ inverse :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `functorCategoryEquivalence`. -/
@[simps!]
/--
Definition of `counitIso` / `counitIso` 的定义

English:
definition counitIso
  signature: : inverse ⋙ functor ≅ 𝟭 (SingleObj G ⥤ V)
  body: NatIso.ofComponents fun M => NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 counitIso
  签名: : inverse ⋙ functor ≅ 𝟭 (SingleObj G ⥤ V)
  定义体: NatIso.ofComponents fun M => NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def counitIso : inverse ⋙ functor ≅ 𝟭 (SingleObj G ⥤ V) :=
  NatIso.ofComponents fun M => NatIso.ofComponents fun _ => Iso.refl _

end FunctorCategoryEquivalence

section

open FunctorCategoryEquivalence

variable (V G)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The category of actions of `G` in the category `V`
is equivalent to the functor category `SingleObj G ⥤ V`.
-/
@[simps]
/--
Definition of `functorCategoryEquivalence` / `functorCategoryEquivalence` 的定义

English:
definition functorCategoryEquivalence
  signature: : Action V G ≌ SingleObj G ⥤ V where
  body: functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

中文:
定义 functorCategoryEquivalence
  签名: : 作用 V G ≌ SingleObj G ⥤ V where
  定义体: functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

Depends on / 依赖: functor
-/
def functorCategoryEquivalence : Action V G ≌ SingleObj G ⥤ V where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (FunctorCategoryEquivalence.functor (V := V) (G := G)).IsEquivalence
  body: (functorCategoryEquivalence V G).isEquivalence_functor

中文:
实例 :
  签名: (FunctorCategoryEquivalence.functor (V := V) (G := G)).是等价
  定义体: (functorCategoryEquivalence V G).isEquivalence_functor

Depends on / 依赖: IsEquivalence
-/
instance : (FunctorCategoryEquivalence.functor (V := V) (G := G)).IsEquivalence :=
  (functorCategoryEquivalence V G).isEquivalence_functor

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (FunctorCategoryEquivalence.inverse (V := V) (G := G)).IsEquivalence
  body: (functorCategoryEquivalence V G).isEquivalence_inverse

中文:
实例 :
  签名: (FunctorCategoryEquivalence.inverse (V := V) (G := G)).是等价
  定义体: (functorCategoryEquivalence V G).isEquivalence_inverse

Depends on / 依赖: IsEquivalence
-/
instance : (FunctorCategoryEquivalence.inverse (V := V) (G := G)).IsEquivalence :=
  (functorCategoryEquivalence V G).isEquivalence_inverse

end

section Forget

variable (V G)

set_option backward.isDefEq.respectTransparency.types false in
/-- (implementation) The forgetful functor from bundled actions to the underlying objects.

Use the `CategoryTheory.forget` API provided by the `ConcreteCategory` instance below,
rather than using this directly.
-/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Action V G ⥤ V where
  body: M.V
  map f := f.hom

中文:
定义 forget
  签名: : 作用 V G ⥤ V where
  定义体: M.V
  map f := f.hom
-/
def forget : Action V G ⥤ V where
  obj M := M.V
  map f := f.hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget V G).Faithful
  body: Hom.ext w

中文:
实例 :
  签名: (forget V G).忠实
  定义体: Hom.ext w

Depends on / 依赖: Hom.ext
-/
instance : (forget V G).Faithful where map_injective w := Hom.ext w

/--
Definition of `HomSubtype` / `HomSubtype` 的定义

English:
abbreviation HomSubtype
  signature: {FV : V -> V -> Type*} {CV : V -> Type*} [forall X Y, FunLike (FV X Y) (CV X) (CV Y)]
  body: { f : FV M.V N.V // forall g : G,
      f ∘ ConcreteCategory.hom (M.ρ g) = ConcreteCategory.hom (N.ρ g) ∘ f }

中文:
缩写 HomSubtype
  签名: {FV : V -> V -> 类型} {CV : V -> 类型} [对任意 X Y, 函数状 (FV X Y) (CV X) (CV Y)]
  定义体: { f : FV M.V N.V // forall g : G,
      f ∘ ConcreteCategory.hom (M.ρ g) = ConcreteCategory.hom (N.ρ g) ∘ f }

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom
-/
abbrev HomSubtype {FV : V -> V -> Type*} {CV : V -> Type*} [forall X Y, FunLike (FV X Y) (CV X) (CV Y)]
    [ConcreteCategory V FV] (M N : Action V G) :=
  { f : FV M.V N.V // forall g : G,
      f ∘ ConcreteCategory.hom (M.ρ g) = ConcreteCategory.hom (N.ρ g) ∘ f }

instance {FV : V -> V -> Type*} {CV : V -> Type*} [forall X Y, FunLike (FV X Y) (CV X) (CV Y)]
    [ConcreteCategory V FV] (M N : Action V G) :
    FunLike (HomSubtype V G M N) (CV M.V) (CV N.V) where
  coe f := f.1
  coe_injective _ _ h := Subtype.ext (DFunLike.coe_injective h)

set_option backward.isDefEq.respectTransparency.types false in
instance {FV : V -> V -> Type*} {CV : V -> Type*} [forall X Y, FunLike (FV X Y) (CV X) (CV Y)]
    [ConcreteCategory V FV] : ConcreteCategory (Action V G) (HomSubtype V G) where
  hom f := ⟨ConcreteCategory.hom (C := V) f.1, fun g => by
    ext
    simpa using CategoryTheory.congr_fun (f.2 g) _⟩
  ofHom f := ⟨ConcreteCategory.ofHom (C := V) f, fun g => ConcreteCategory.ext_apply fun x => by
    simpa [ConcreteCategory.hom_ofHom] using congr_fun (f.2 g) x⟩
  hom_ofHom _ := by dsimp; ext; simp [ConcreteCategory.hom_ofHom]
  ofHom_hom _ := by ext; simp [ConcreteCategory.ofHom_hom]
  id_apply := ConcreteCategory.id_apply (C := V)
  comp_apply _ _ := ConcreteCategory.comp_apply (C := V) _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `hasForgetToV` / 实例 `hasForgetToV`

English:
instance hasForgetToV
  signature: {FV : V -> V -> Type*} {CV : V -> Type*} [forall X Y, FunLike (FV X Y) (CV X) (CV Y)]
  body: forget V G

中文:
实例 hasForgetToV
  签名: {FV : V -> V -> 类型} {CV : V -> 类型} [对任意 X Y, 函数状 (FV X Y) (CV X) (CV Y)]
  定义体: forget V G

Depends on / 依赖: forget
-/
instance hasForgetToV {FV : V -> V -> Type*} {CV : V -> Type*} [forall X Y, FunLike (FV X Y) (CV X) (CV Y)]
    [ConcreteCategory V FV] : HasForget₂ (Action V G) V where forget₂ := forget V G

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `functorCategoryEquivalenceCompEvaluation` / `functorCategoryEquivalenceCompEvaluation` 的定义

English:
definition functorCategoryEquivalenceCompEvaluation
  signature: :
  body: Iso.refl _

中文:
定义 functorCategoryEquivalenceCompEvaluation
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def functorCategoryEquivalenceCompEvaluation :
    (functorCategoryEquivalence V G).functor ⋙ (evaluation _ _).obj PUnit.unit ≅ forget V G :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `preservesLimits_forget` / 实例 `preservesLimits_forget`

English:
instance preservesLimits_forget
  signature: [HasLimits V]
  body: Limits.preservesLimits_of_natIso (Action.functorCategoryEquivalenceCompEvaluation V G)

中文:
实例 preservesLimits_forget
  签名: [有极限 V]
  定义体: Limits.preservesLimits_of_natIso (Action.functorCategoryEquivalenceCompEvaluation V G)

Depends on / 依赖: Action, Action.functorCategoryEquivalenceCompEvaluation, Limits, Limits.preservesLimits_of_natIso, functorCategoryEquivalenceCompEvaluation, preservesLimits_of_natIso
-/
noncomputable instance preservesLimits_forget [HasLimits V] :
    PreservesLimits (forget V G) :=
  Limits.preservesLimits_of_natIso (Action.functorCategoryEquivalenceCompEvaluation V G)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `preservesColimits_forget` / 实例 `preservesColimits_forget`

English:
instance preservesColimits_forget
  signature: [HasColimits V]
  body: preservesColimits_of_natIso (Action.functorCategoryEquivalenceCompEvaluation V G)

中文:
实例 preservesColimits_forget
  签名: [有余极限 V]
  定义体: preservesColimits_of_natIso (Action.functorCategoryEquivalenceCompEvaluation V G)

Depends on / 依赖: Action, Action.functorCategoryEquivalenceCompEvaluation, functorCategoryEquivalenceCompEvaluation, preservesColimits_of_natIso
-/
noncomputable instance preservesColimits_forget [HasColimits V] :
    PreservesColimits (forget V G) :=
  preservesColimits_of_natIso (Action.functorCategoryEquivalenceCompEvaluation V G)

-- TODO construct categorical images?
end Forget

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Iso.conj_ρ` / 定理 `Iso.conj_ρ`

English:
theorem Iso.conj_ρ
  given: {M N : Action V G} (f : M ≅ N) (g : G)
  proof: by
      rw [Iso.conj_apply]; rw [Iso.eq_inv_comp]; simp [f.hom.comm]

中文:
定理 同构.conj_ρ
  条件: {M N : 作用 V G} (f : M ≅ N) (g : G)
  证明: by
      rw [Iso.conj_apply]; rw [Iso.eq_inv_comp]; simp [f.hom.comm]

Depends on / 依赖: Iso.conj_apply, Iso.eq_inv_comp, conj_apply, eq_inv_comp, f.hom.comm
-/
theorem Iso.conj_ρ {M N : Action V G} (f : M ≅ N) (g : G) :
    N.ρ g = ((forget V G).mapIso f).conj (M.ρ g) := by
      rw [Iso.conj_apply]; rw [Iso.eq_inv_comp]; simp [f.hom.comm]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `actionPUnitEquivalence` / `actionPUnitEquivalence` 的定义

English:
definition actionPUnitEquivalence
  signature: : Action V PUnit ≌ V where
  body: forget V _
  inverse :=
    { obj := fun X => ⟨X, 1⟩
      map := fun f => ⟨f, fun ⟨⟩ => by simp⟩ }
  unitIso :=
    NatIso.ofComponents fun X => mkIso (Iso.refl _) fun ⟨⟩ => by
      simp only [Functor.id_obj, MonoidHom.one_apply, End.one_def, Functor.comp_obj,
        forget_obj, Iso.refl_hom, Category.comp_id]
      exact ρ_one X
  counitIso := NatIso.ofComponents fun _ => Iso.refl _

@[deprecated (since := "2026-02-08")] alias actionPunitEquivalence := actionPUnitEquivalence

中文:
定义 actionPUnitEquivalence
  签名: : 作用 V 命题单元 ≌ V where
  定义体: forget V _
  inverse :=
    { obj := fun X => ⟨X, 1⟩
      map := fun f => ⟨f, fun ⟨⟩ => by simp⟩ }
  unitIso :=
    NatIso.ofComponents fun X => mkIso (Iso.refl _) fun ⟨⟩ => by
      simp only [Functor.id_obj, MonoidHom.one_apply, End.one_def, Functor.comp_obj,
        forget_obj, Iso.refl_hom, Category.comp_id]
      exact ρ_one X
  counitIso := NatIso.ofComponents fun _ => Iso.refl _

@[deprecated (since := "2026-02-08")] alias actionPunitEquivalence := actionPUnitEquivalence

Depends on / 依赖: forget
-/
def actionPUnitEquivalence : Action V PUnit ≌ V where
  functor := forget V _
  inverse :=
    { obj := fun X => ⟨X, 1⟩
      map := fun f => ⟨f, fun ⟨⟩ => by simp⟩ }
  unitIso :=
    NatIso.ofComponents fun X => mkIso (Iso.refl _) fun ⟨⟩ => by
      simp only [Functor.id_obj, MonoidHom.one_apply, End.one_def, Functor.comp_obj,
        forget_obj, Iso.refl_hom, Category.comp_id]
      exact ρ_one X
  counitIso := NatIso.ofComponents fun _ => Iso.refl _

@[deprecated (since := "2026-02-08")] alias actionPunitEquivalence := actionPUnitEquivalence

variable (V)

set_option backward.isDefEq.respectTransparency.types false in
/-- The "restriction" functor along a monoid homomorphism `f : G →* H`,
taking actions of `H` to actions of `G`.

(This makes sense for any homomorphism, but the name is natural when `f` is a monomorphism.)
-/
@[simps]
/--
Definition of `res` / `res` 的定义

English:
definition res
  signature: {G H : Type*} [Monoid G] [Monoid H] (f : G ->* H)
  body: { V := M.V
      ρ := M.ρ.comp f }
  map p :=
    { hom := p.hom
      comm := fun g => p.comm (f g) }

中文:
定义 res
  签名: {G H : 类型} [幺半群 G] [幺半群 H] (f : G ->* H)
  定义体: { V := M.V
      ρ := M.ρ.comp f }
  map p :=
    { hom := p.hom
      comm := fun g => p.comm (f g) }

Depends on / 依赖: p.comm, p.hom
-/
def res {G H : Type*} [Monoid G] [Monoid H] (f : G ->* H) : Action V H ⥤ Action V G where
  obj M :=
    { V := M.V
      ρ := M.ρ.comp f }
  map p :=
    { hom := p.hom
      comm := fun g => p.comm (f g) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism from restriction along the identity homomorphism to
the identity functor on `Action V G`.
-/
@[simps!]
/--
Definition of `resId` / `resId` 的定义

English:
definition resId
  signature: {G : Type*} [Monoid G]
  body: NatIso.ofComponents fun M => mkIso (Iso.refl _)

中文:
定义 resId
  签名: {G : 类型} [幺半群 G]
  定义体: NatIso.ofComponents fun M => mkIso (Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def resId {G : Type*} [Monoid G] : res V (MonoidHom.id G) ≅ 𝟭 (Action V G) :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism from the composition of restrictions along homomorphisms
to the restriction along the composition of homomorphism.
-/
@[simps!]
/--
Definition of `resComp` / `resComp` 的定义

English:
definition resComp
  signature: {G H K : Type*} [Monoid G] [Monoid H] [Monoid K]
  body: NatIso.ofComponents fun M => mkIso (Iso.refl _)

中文:
定义 resComp
  签名: {G H K : 类型} [幺半群 G] [幺半群 H] [幺半群 K]
  定义体: NatIso.ofComponents fun M => mkIso (Iso.refl _)

Depends on / 依赖: F.map, Finite, Finite.of_injective, GaloisCategory, GaloisCategory.getFiberFunctor, Iso.refl, NatIso, NatIso.ofComponents, evaluation_injective_of_isConnected, getFiberFunctor, nonempty_fiber_of_isConnected, ofComponents, of_injective
-/
def resComp {G H K : Type*} [Monoid G] [Monoid H] [Monoid K]
    (f : G ->* H) (g : H ->* K) : res V g ⋙ res V f ≅ res V (g.comp f) :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting scalars along equal maps is naturally isomorphic. -/
@[simps! hom inv]
/--
Definition of `resCongr` / `resCongr` 的定义

English:
definition resCongr
  signature: {G H : Type*} [Monoid G] [Monoid H] {f f' : G ->* H} (h : f = f')
  body: NatIso.ofComponents (fun _ => Action.mkIso (Iso.refl _))

中文:
定义 resCongr
  签名: {G H : 类型} [幺半群 G] [幺半群 H] {f f' : G ->* H} (h : f = f')
  定义体: NatIso.ofComponents (fun _ => Action.mkIso (Iso.refl _))

Depends on / 依赖: Action, Action.mkIso, F.map, Finite, Finite.of_injective, GaloisCategory, GaloisCategory.getFiberFunctor, Iso.refl, NatIso, NatIso.ofComponents, evaluation_aut_injective_of_isConnected, f.hom, getFiberFunctor, nonempty_fiber_of_isConnected, ofComponents, of_injective
-/
def resCongr {G H : Type*} [Monoid G] [Monoid H] {f f' : G ->* H} (h : f = f') :
    Action.res V f ≅ Action.res V f' :=
  NatIso.ofComponents (fun _ => Action.mkIso (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Restricting scalars along a monoid isomorphism induces an equivalence of categories. -/
@[simps! functor inverse]
/--
Definition of `resEquiv` / `resEquiv` 的定义

English:
definition resEquiv
  signature: {G H : Type*} [Monoid G] [Monoid H] (f : G ≃* H)
  body: Action.res _ f
  inverse := Action.res _ f.symm
  unitIso := Action.resCongr (f := MonoidHom.id H) V (by ext; simp) ≪≫ (Action.resComp _ _ _).symm
  counitIso := Action.resComp _ _ _ ≪≫
    Action.resCongr (f' := MonoidHom.id G) V (by ext; simp)

中文:
定义 resEquiv
  签名: {G H : 类型} [幺半群 G] [幺半群 H] (f : G ≃* H)
  定义体: Action.res _ f
  inverse := Action.res _ f.symm
  unitIso := Action.resCongr (f := MonoidHom.id H) V (by ext; simp) ≪≫ (Action.resComp _ _ _).symm
  counitIso := Action.resComp _ _ _ ≪≫
    Action.resCongr (f' := MonoidHom.id G) V (by ext; simp)

Depends on / 依赖: Action, Action.res
-/
def resEquiv {G H : Type*} [Monoid G] [Monoid H] (f : G ≃* H) :
    Action V H ≌ Action V G where
  functor := Action.res _ f
  inverse := Action.res _ f.symm
  unitIso := Action.resCongr (f := MonoidHom.id H) V (by ext; simp) ≪≫ (Action.resComp _ _ _).symm
  counitIso := Action.resComp _ _ _ ≪≫
    Action.resCongr (f' := MonoidHom.id G) V (by ext; simp)

-- TODO promote `res` to a pseudofunctor from
-- the locally discrete bicategory constructed from `Monᵒᵖ` to `Cat`, sending `G` to `Action V G`.

variable {G H : Type*} [Monoid G] [Monoid H] (f : G ->* H)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (res V f).Faithful
  body: by
    ext
    rw [← res_map_hom _ f g₁]; rw [← res_map_hom _ f g₂]; rw [h]

中文:
实例 :
  签名: (res V f).忠实
  定义体: by
    ext
    rw [← res_map_hom _ f g₁]; rw [← res_map_hom _ f g₂]; rw [h]

Depends on / 依赖: res_map_hom
-/
instance : (res V f).Faithful where
  map_injective {X} {Y} g₁ g₂ h := by
    ext
    rw [← res_map_hom _ f g₁]; rw [← res_map_hom _ f g₂]; rw [h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `full_res` / 引理 `full_res`

English:
lemma full_res
  given: (f_surj : Function.Surjective f)
  statement: (res V f).Full where
  proof: by
    use ⟨g.hom, fun h => ?_⟩
    · ext
      simp
    · obtain ⟨a, rfl⟩ := f_surj h
      have : X.ρ (f a) = ((res V f).obj X).ρ a := rfl
      rw [this]; rw [g.comm a]
      simp

中文:
引理 full_res
  条件: (f_surj : 函数.满射 f)
  结论: (res V f).满 where
  证明: by
    use ⟨g.hom, fun h => ?_⟩
    · ext
      simp
    · obtain ⟨a, rfl⟩ := f_surj h
      have : X.ρ (f a) = ((res V f).obj X).ρ a := rfl
      rw [this]; rw [g.comm a]
      simp

Depends on / 依赖: f_surj, g.comm, g.hom
-/
lemma full_res (f_surj : Function.Surjective f) : (res V f).Full where
  map_surjective {X} {Y} g := by
    use ⟨g.hom, fun h => ?_⟩
    · ext
      simp
    · obtain ⟨a, rfl⟩ := f_surj h
      have : X.ρ (f a) = ((res V f).obj X).ρ a := rfl
      rw [this]; rw [g.comm a]
      simp

end Action

namespace CategoryTheory.Functor

variable {V} {W : Type*} [Category* W]

set_option backward.isDefEq.respectTransparency.types false in
/-- A functor between categories induces a functor between
the categories of `G`-actions within those categories. -/
@[simps]
/--
Definition of `mapAction` / `mapAction` 的定义

English:
definition mapAction
  signature: (F : V ⥤ W) (G : Type*) [Monoid G]
  body: { V := F.obj M.V
      ρ :=
        { toFun := fun g => F.map (M.ρ g)
          map_one' := by simp
          map_mul' := fun g h => by
            dsimp
            rw [map_mul]; rw [End.mul_def]; rw [F.map_comp] } }
  map f :=
    { hom := F.map f.hom
      comm := fun g => by dsimp; rw [← F.map_comp, f.comm, F.map_comp] }
  map_id M := by ext; simp only [Action.id_hom, F.map_id]
  map_comp f g := by ext; simp only [Action.comp_hom, F.map_comp]

中文:
定义 mapAction
  签名: (F : V ⥤ W) (G : 类型) [幺半群 G]
  定义体: { V := F.obj M.V
      ρ :=
        { toFun := fun g => F.map (M.ρ g)
          map_one' := by simp
          map_mul' := fun g h => by
            dsimp
            rw [map_mul]; rw [End.mul_def]; rw [F.map_comp] } }
  map f :=
    { hom := F.map f.hom
      comm := fun g => by dsimp; rw [← F.map_comp, f.comm, F.map_comp] }
  map_id M := by ext; simp only [Action.id_hom, F.map_id]
  map_comp f g := by ext; simp only [Action.comp_hom, F.map_comp]

Depends on / 依赖: Action, Action.comp_hom, Action.id_hom, End.mul_def, F.map, F.map_comp, F.map_id, F.obj, comp_hom, f.comm, f.hom, id_hom, map_comp, map_id, map_mul, map_one, mul_def
-/
def mapAction (F : V ⥤ W) (G : Type*) [Monoid G] : Action V G ⥤ Action W G where
  obj M :=
    { V := F.obj M.V
      ρ :=
        { toFun := fun g => F.map (M.ρ g)
          map_one' := by simp
          map_mul' := fun g h => by
            dsimp
            rw [map_mul]; rw [End.mul_def]; rw [F.map_comp] } }
  map f :=
    { hom := F.map f.hom
      comm := fun g => by dsimp; rw [← F.map_comp, f.comm, F.map_comp] }
  map_id M := by ext; simp only [Action.id_hom, F.map_id]
  map_comp f g := by ext; simp only [Action.comp_hom, F.map_comp]

set_option backward.isDefEq.respectTransparency.types false in
instance (F : V ⥤ W) (G : Type*) [Monoid G] [F.Faithful] : (F.mapAction G).Faithful where
  map_injective eq := by
    ext
    apply_fun (fun f => f.hom) at eq
    exact F.map_injective eq

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `FullyFaithful.mapAction` / `FullyFaithful.mapAction` 的定义

English:
definition FullyFaithful.mapAction
  signature: {F : V ⥤ W} (h : F.FullyFaithful) (G : Type*) [Monoid G]
  body: by
    refine ⟨h.preimage f.hom, fun _ => h.map_injective ?_⟩
    simp only [map_comp, map_preimage]
    exact f.comm _

中文:
定义 满忠实.mapAction
  签名: {F : V ⥤ W} (h : F.满忠实) (G : 类型) [幺半群 G]
  定义体: by
    refine ⟨h.preimage f.hom, fun _ => h.map_injective ?_⟩
    simp only [map_comp, map_preimage]
    exact f.comm _

Depends on / 依赖: f.comm, f.hom, h.map_injective, h.preimage, map_comp, map_injective, map_preimage, preimage
-/
def FullyFaithful.mapAction {F : V ⥤ W} (h : F.FullyFaithful) (G : Type*) [Monoid G] :
    (F.mapAction G).FullyFaithful where
  preimage f := by
    refine ⟨h.preimage f.hom, fun _ => h.map_injective ?_⟩
    simp only [map_comp, map_preimage]
    exact f.comm _

instance (F : V ⥤ W) (G : Type*) [Monoid G] [F.Faithful] [F.Full] : (F.mapAction G).Full :=
  ((Functor.FullyFaithful.ofFullyFaithful F).mapAction G).full

variable (G : Type*) [Monoid G]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `Functor.mapAction` is functorial in the functor. -/
@[simps! hom inv]
/--
Definition of `mapActionComp` / `mapActionComp` 的定义

English:
definition mapActionComp
  signature: {T : Type*} [Category* T] (F : V ⥤ W) (F' : W ⥤ T)
  body: NatIso.ofComponents (fun X => Iso.refl _)

中文:
定义 mapActionComp
  签名: {T : 类型} [范畴* T] (F : V ⥤ W) (F' : W ⥤ T)
  定义体: NatIso.ofComponents (fun X => Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def mapActionComp {T : Type*} [Category* T] (F : V ⥤ W) (F' : W ⥤ T) :
    (F ⋙ F').mapAction G ≅ F.mapAction G ⋙ F'.mapAction G :=
  NatIso.ofComponents (fun X => Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `Functor.mapAction` preserves isomorphisms of functors. -/
@[simps! hom inv]
/--
Definition of `mapActionCongr` / `mapActionCongr` 的定义

English:
definition mapActionCongr
  signature: {F F' : V ⥤ W} (e : F ≅ F')
  body: NatIso.ofComponents (fun X => Action.mkIso (e.app X.V))

中文:
定义 mapActionCongr
  签名: {F F' : V ⥤ W} (e : F ≅ F')
  定义体: NatIso.ofComponents (fun X => Action.mkIso (e.app X.V))

Depends on / 依赖: Action, Action.mkIso, NatIso, NatIso.ofComponents, e.app, ofComponents
-/
def mapActionCongr {F F' : V ⥤ W} (e : F ≅ F') :
    F.mapAction G ≅ F'.mapAction G :=
  NatIso.ofComponents (fun X => Action.mkIso (e.app X.V))

end Functor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An equivalence of categories induces an equivalence of
the categories of `G`-actions within those categories. -/
@[simps functor inverse]
/--
Definition of `Equivalence.mapAction` / `Equivalence.mapAction` 的定义

English:
definition Equivalence.mapAction
  signature: {V W : Type*} [Category* V] [Category* W] (G : Type*) [Monoid G]
  body: E.functor.mapAction G
  inverse := E.inverse.mapAction G
  unitIso := Functor.mapActionCongr G E.unitIso ≪≫ Functor.mapActionComp G _ _
  counitIso := (Functor.mapActionComp G _ _).symm ≪≫ Functor.mapActionCongr G E.counitIso
  functor_unitIso_comp X := by ext; simp

中文:
定义 等价.mapAction
  签名: {V W : 类型} [范畴* V] [范畴* W] (G : 类型) [幺半群 G]
  定义体: E.functor.mapAction G
  inverse := E.inverse.mapAction G
  unitIso := Functor.mapActionCongr G E.unitIso ≪≫ Functor.mapActionComp G _ _
  counitIso := (Functor.mapActionComp G _ _).symm ≪≫ Functor.mapActionCongr G E.counitIso
  functor_unitIso_comp X := by ext; simp

Depends on / 依赖: E.functor.mapAction, functor, mapAction
-/
def Equivalence.mapAction {V W : Type*} [Category* V] [Category* W] (G : Type*) [Monoid G]
    (E : V ≌ W) : Action V G ≌ Action W G where
  functor := E.functor.mapAction G
  inverse := E.inverse.mapAction G
  unitIso := Functor.mapActionCongr G E.unitIso ≪≫ Functor.mapActionComp G _ _
  counitIso := (Functor.mapActionComp G _ _).symm ≪≫ Functor.mapActionCongr G E.counitIso
  functor_unitIso_comp X := by ext; simp

end CategoryTheory
