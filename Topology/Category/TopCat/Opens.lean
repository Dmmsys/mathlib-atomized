/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Topology.Category.TopCat.EpiMono
public import Mathlib.Topology.Sets.Opens

/-!
# The category of open sets in a topological space.

We define `toTopCat : Opens X ⥤ TopCat` and
`map (f : X ⟶ Y) : Opens Y ⥤ Opens X`, given by taking preimages of open sets.

Unfortunately `Opens` isn't (usefully) a functor `TopCat ⥤ Cat`.
(One can in fact define such a functor,
but using it results in unresolvable `Eq.rec` terms in goals.)

Really it's a 2-functor from (spaces, continuous functions, equalities)
to (categories, functors, natural isomorphisms).
We don't attempt to set up the full theory here, but do provide the natural isomorphisms
`mapId : map (𝟙 X) ≅ 𝟭 (Opens X)` and
`mapComp : map (f ≫ g) ≅ map g ⋙ map f`.

Beyond that, there's a collection of simp lemmas for working with these constructions.
-/

@[expose] public section


open CategoryTheory TopologicalSpace Opposite Topology

universe u

namespace TopologicalSpace.Opens

variable {X Y Z : TopCat.{u}} {U V W : Opens X}


/--
Instance `opensHom.instFunLike` / 实例 `opensHom.instFunLike`

English:
instance opensHom.instFunLike
  signature: : FunLike (U ⟶ V) U V where
  body: Set.inclusion f.le
  coe_injective := by rintro ⟨⟨_⟩⟩ _ _; congr!

中文:
实例 opensHom.instFunLike
  签名: : FunLike (U ⟶ V) U V where
  定义体: Set.inclusion f.le
  coe_injective := by rintro ⟨⟨_⟩⟩ _ _; congr!

Depends on / 依赖: Set.inclusion, f.le, inclusion
-/
instance opensHom.instFunLike : FunLike (U ⟶ V) U V where
  coe f := Set.inclusion f.le
  coe_injective := by rintro ⟨⟨_⟩⟩ _ _; congr!

/--
lemma `apply_def` / 引理 `apply_def`

English:
lemma apply_def
  given: (f : U ⟶ V) (x : U)
  statement: f x = ⟨x, f.le x.2⟩
  proof: rfl

中文:
引理 apply_def
  条件: (f : U ⟶ V) (x : U)
  结论: f x = ⟨x, f.le x.2⟩
  证明: rfl
-/
lemma apply_def (f : U ⟶ V) (x : U) : f x = ⟨x, f.le x.2⟩ := rfl

/--
lemma `apply_mk` / 引理 `apply_mk`

English:
lemma apply_mk
  given: (f : U ⟶ V) (x : X) (hx)
  statement: f ⟨x, hx⟩ = ⟨x, f.le hx⟩
  proof: rfl

中文:
引理 apply_mk
  条件: (f : U ⟶ V) (x : X) (hx)
  结论: f ⟨x, hx⟩ = ⟨x, f.le hx⟩
  证明: rfl
-/
@[simp] lemma apply_mk (f : U ⟶ V) (x : X) (hx) : f ⟨x, hx⟩ = ⟨x, f.le hx⟩ := rfl

/--
lemma `val_apply` / 引理 `val_apply`

English:
lemma val_apply
  given: (f : U ⟶ V) (x : U)
  statement: (f x : X) = x
  proof: rfl

中文:
引理 val_apply
  条件: (f : U ⟶ V) (x : U)
  结论: (f x : X) = x
  证明: rfl
-/
@[simp] lemma val_apply (f : U ⟶ V) (x : U) : (f x : X) = x := rfl

/--
lemma `coe_id` / 引理 `coe_id`

English:
lemma coe_id
  given: (f : U ⟶ U)
  statement: ⇑f = id
  proof: rfl

中文:
引理 coe_id
  条件: (f : U ⟶ U)
  结论: ⇑f = id
  证明: rfl
-/
@[simp, norm_cast] lemma coe_id (f : U ⟶ U) : ⇑f = id := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (f : U ⟶ U) (x : U)
  statement: f x = x
  proof: rfl

中文:
引理 id_apply
  条件: (f : U ⟶ U) (x : U)
  结论: f x = x
  证明: rfl
-/
lemma id_apply (f : U ⟶ U) (x : U) : f x = x := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: (f : U ⟶ V) (g : V ⟶ W) (x : U)
  statement: (f ≫ g) x = g (f x)
  proof: rfl

中文:
引理 comp_apply
  条件: (f : U ⟶ V) (g : V ⟶ W) (x : U)
  结论: (f ≫ g) x = g (f x)
  证明: rfl
-/
@[simp] lemma comp_apply (f : U ⟶ V) (g : V ⟶ W) (x : U) : (f ≫ g) x = g (f x) := rfl

/-!
We now construct as morphisms various inclusions of open sets.
-/


-- This is tedious, but necessary because we decided not to allow Prop as morphisms in a category...
/--
Definition of `infLELeft` / `infLELeft` 的定义

English:
definition infLELeft
  signature: (U V : Opens X)
  body: inf_le_left.hom

中文:
定义 infLELeft
  签名: (U V : Opens X)
  定义体: inf_le_left.hom

Depends on / 依赖: inf_le_left, inf_le_left.hom
-/
noncomputable def infLELeft (U V : Opens X) : U ⊓ V ⟶ U :=
  inf_le_left.hom

/--
Definition of `infLERight` / `infLERight` 的定义

English:
definition infLERight
  signature: (U V : Opens X)
  body: inf_le_right.hom

中文:
定义 infLERight
  签名: (U V : Opens X)
  定义体: inf_le_right.hom

Depends on / 依赖: inf_le_right, inf_le_right.hom
-/
noncomputable def infLERight (U V : Opens X) : U ⊓ V ⟶ V :=
  inf_le_right.hom

/--
Definition of `leSupr` / `leSupr` 的定义

English:
definition leSupr
  signature: {ι : Type*} (U : ι -> Opens X) (i : ι)
  body: (le_iSup U i).hom

中文:
定义 leSupr
  签名: {ι : 类型} (U : ι -> Opens X) (i : ι)
  定义体: (le_iSup U i).hom

Depends on / 依赖: le_iSup
-/
noncomputable def leSupr {ι : Type*} (U : ι -> Opens X) (i : ι) : U i ⟶ iSup U :=
  (le_iSup U i).hom

/--
Definition of `botLE` / `botLE` 的定义

English:
definition botLE
  signature: (U : Opens X)
  body: bot_le.hom

中文:
定义 botLE
  签名: (U : Opens X)
  定义体: bot_le.hom

Depends on / 依赖: bot_le, bot_le.hom
-/
noncomputable def botLE (U : Opens X) : ⊥ ⟶ U :=
  bot_le.hom

/--
Definition of `leTop` / `leTop` 的定义

English:
definition leTop
  signature: (U : Opens X)
  body: le_top.hom

中文:
定义 leTop
  签名: (U : Opens X)
  定义体: le_top.hom

Depends on / 依赖: le_top, le_top.hom
-/
noncomputable def leTop (U : Opens X) : U ⟶ ⊤ :=
  le_top.hom

-- We do not mark this as a simp lemma because it breaks open `x`.
-- Nevertheless, it is useful in `SheafOfFunctions`.
/--
theorem `infLELeft_apply` / 定理 `infLELeft_apply`

English:
theorem infLELeft_apply
  given: (U V : Opens X) (x)
  proof: rfl

@[simp]

中文:
定理 infLELeft_apply
  条件: (U V : Opens X) (x)
  证明: rfl

@[simp]
-/
theorem infLELeft_apply (U V : Opens X) (x) :
    (infLELeft U V) x = ⟨x.1, (@inf_le_left _ _ U V : _ <= _) x.2⟩ :=
  rfl

@[simp]
/--
theorem `infLELeft_apply_mk` / 定理 `infLELeft_apply_mk`

English:
theorem infLELeft_apply_mk
  given: (U V : Opens X) (x) (m)
  proof: rfl

@[simp]

中文:
定理 infLELeft_apply_mk
  条件: (U V : Opens X) (x) (m)
  证明: rfl

@[simp]
-/
theorem infLELeft_apply_mk (U V : Opens X) (x) (m) :
    (infLELeft U V) ⟨x, m⟩ = ⟨x, (@inf_le_left _ _ U V : _ <= _) m⟩ :=
  rfl

@[simp]
/--
theorem `leSupr_apply_mk` / 定理 `leSupr_apply_mk`

English:
theorem leSupr_apply_mk
  given: {ι : Type*} (U : ι -> Opens X) (i : ι) (x) (m)
  proof: rfl

中文:
定理 leSupr_apply_mk
  条件: {ι : 类型} (U : ι -> Opens X) (i : ι) (x) (m)
  证明: rfl
-/
theorem leSupr_apply_mk {ι : Type*} (U : ι -> Opens X) (i : ι) (x) (m) :
    (leSupr U i) ⟨x, m⟩ = ⟨x, (le_iSup U i :) m⟩ :=
  rfl

/--
Definition of `toTopCat` / `toTopCat` 的定义

English:
definition toTopCat
  signature: (X : TopCat.{u})
  body: TopCat.of U
  map i := TopCat.ofHom ⟨fun x => ⟨x.1, i.le x.2⟩,
    IsEmbedding.subtypeVal.continuous_iff.2 continuous_induced_dom⟩

@[simp]

中文:
定义 toTopCat
  签名: (X : TopCat.{u})
  定义体: TopCat.of U
  map i := TopCat.ofHom ⟨fun x => ⟨x.1, i.le x.2⟩,
    IsEmbedding.subtypeVal.continuous_iff.2 continuous_induced_dom⟩

@[simp]

Depends on / 依赖: TopCat, TopCat.of
-/
def toTopCat (X : TopCat.{u}) : Opens X ⥤ TopCat where
  obj U := TopCat.of U
  map i := TopCat.ofHom ⟨fun x => ⟨x.1, i.le x.2⟩,
    IsEmbedding.subtypeVal.continuous_iff.2 continuous_induced_dom⟩

@[simp]
/--
theorem `toTopCat_map` / 定理 `toTopCat_map`

English:
theorem toTopCat_map
  given: (X : TopCat.{u}) {U V : Opens X} {f : U ⟶ V} {x} {h}
  proof: rfl

中文:
定理 toTopCat_map
  条件: (X : TopCat.{u}) {U V : Opens X} {f : U ⟶ V} {x} {h}
  证明: rfl
-/
theorem toTopCat_map (X : TopCat.{u}) {U V : Opens X} {f : U ⟶ V} {x} {h} :
    ((toTopCat X).map f) ⟨x, h⟩ = ⟨x, f.le h⟩ :=
  rfl

/-- The inclusion map from an open subset to the whole space, as a morphism in `TopCat`.
-/
@[simps! -fullyApplied]
/--
Definition of `inclusion'` / `inclusion'` 的定义

English:
definition inclusion'
  signature: {X : TopCat.{u}} (U : Opens X)
  body: TopCat.ofHom
  { toFun := _
    continuous_toFun := continuous_subtype_val }

@[simp]

中文:
定义 inclusion'
  签名: {X : TopCat.{u}} (U : Opens X)
  定义体: TopCat.ofHom
  { toFun := _
    continuous_toFun := continuous_subtype_val }

@[simp]

Depends on / 依赖: TopCat, TopCat.ofHom, continuous_subtype_val, continuous_toFun
-/
def inclusion' {X : TopCat.{u}} (U : Opens X) : (toTopCat X).obj U ⟶ X :=
  TopCat.ofHom
  { toFun := _
    continuous_toFun := continuous_subtype_val }

@[simp]
/--
theorem `coe_inclusion'` / 定理 `coe_inclusion'`

English:
theorem coe_inclusion'
  given: {X : TopCat.{u}} {U : Opens X}
  proof: rfl

中文:
定理 coe_inclusion'
  条件: {X : TopCat.{u}} {U : Opens X}
  证明: rfl
-/
theorem coe_inclusion' {X : TopCat.{u}} {U : Opens X} :
    (inclusion' U : U -> X) = Subtype.val := rfl

/--
theorem `isOpenEmbedding` / 定理 `isOpenEmbedding`

English:
theorem isOpenEmbedding
  given: {X : TopCat.{u}} (U : Opens X)
  statement: IsOpenEmbedding (inclusion' U)
  proof: U.2.isOpenEmbedding_subtypeVal

中文:
定理 isOpenEmbedding
  条件: {X : TopCat.{u}} (U : Opens X)
  结论: IsOpenEmbedding (inclusion' U)
  证明: U.2.isOpenEmbedding_subtypeVal

Depends on / 依赖: isOpenEmbedding_subtypeVal
-/
theorem isOpenEmbedding {X : TopCat.{u}} (U : Opens X) : IsOpenEmbedding (inclusion' U) :=
  U.2.isOpenEmbedding_subtypeVal

/--
Definition of `inclusionTopIso` / `inclusionTopIso` 的定义

English:
definition inclusionTopIso
  signature: (X : TopCat.{u})
  body: inclusion' ⊤
  inv := TopCat.ofHom ⟨fun x => ⟨x, trivial⟩, continuous_def.2 fun _ ⟨_, hS, hSU⟩ => hSU ▸ hS⟩

中文:
定义 inclusionTopIso
  签名: (X : TopCat.{u})
  定义体: inclusion' ⊤
  inv := TopCat.ofHom ⟨fun x => ⟨x, trivial⟩, continuous_def.2 fun _ ⟨_, hS, hSU⟩ => hSU ▸ hS⟩

Depends on / 依赖: inclusion
-/
def inclusionTopIso (X : TopCat.{u}) : (toTopCat X).obj ⊤ ≅ X where
  hom := inclusion' ⊤
  inv := TopCat.ofHom ⟨fun x => ⟨x, trivial⟩, continuous_def.2 fun _ ⟨_, hS, hSU⟩ => hSU ▸ hS⟩

/-- The FrameHom sending an open in `Y` to its preimage in `X` -/
@[simps]
/--
Definition of `_root_.TopCat.Hom.frameHom` / `_root_.TopCat.Hom.frameHom` 的定义

English:
definition _root_.TopCat.Hom.frameHom
  signature: (f : X ⟶ Y)
  body: ⟨f ⁻¹' (U : Set Y), U.isOpen.preimage f.hom.continuous⟩
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' _ := by ext; simp

中文:
定义 _root_.TopCat.Hom.frameHom
  签名: (f : X ⟶ Y)
  定义体: ⟨f ⁻¹' (U : Set Y), U.isOpen.preimage f.hom.continuous⟩
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' _ := by ext; simp

Depends on / 依赖: U.isOpen.preimage, continuous, f.hom.continuous, isOpen, preimage
-/
def _root_.TopCat.Hom.frameHom (f : X ⟶ Y) : FrameHom (Opens Y) (Opens X) where
  toFun U := ⟨f ⁻¹' (U : Set Y), U.isOpen.preimage f.hom.continuous⟩
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' _ := by ext; simp

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : X ⟶ Y)
  body: (OrderHomClass.toOrderHom f.frameHom).toFunctor

中文:
定义 map
  签名: (f : X ⟶ Y)
  定义体: (OrderHomClass.toOrderHom f.frameHom).toFunctor

Depends on / 依赖: OrderHomClass, OrderHomClass.toOrderHom, f.frameHom, frameHom, toFunctor, toOrderHom
-/
def map (f : X ⟶ Y) : Opens Y ⥤ Opens X :=
  (OrderHomClass.toOrderHom f.frameHom).toFunctor

/--
lemma `map_def` / 引理 `map_def`

English:
lemma map_def
  given: (f : X ⟶ Y)
  statement: map f =
  proof: rfl

@[simp]

中文:
引理 map_def
  条件: (f : X ⟶ Y)
  结论: map f =
  证明: rfl

@[simp]

Depends on / 依赖: U.isOpen.preimage, continuous, f.hom.continuous, isOpen, preimage
-/
lemma map_def (f : X ⟶ Y) : map f =
  { obj U := ⟨f ⁻¹' (U : Set Y), U.isOpen.preimage f.hom.continuous⟩
    map i := ⟨⟨fun _ h => i.le h⟩⟩ } := rfl

@[simp]
/--
theorem `map_coe` / 定理 `map_coe`

English:
theorem map_coe
  given: (f : X ⟶ Y) (U : Opens Y)
  statement: ((map f).obj U : Set X) = f ⁻¹' (U : Set Y)
  proof: rfl

@[simp]

中文:
定理 map_coe
  条件: (f : X ⟶ Y) (U : Opens Y)
  结论: ((map f).obj U : Set X) = f ⁻¹' (U : Set Y)
  证明: rfl

@[simp]
-/
theorem map_coe (f : X ⟶ Y) (U : Opens Y) : ((map f).obj U : Set X) = f ⁻¹' (U : Set Y) :=
  rfl

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : X ⟶ Y} {U : Opens Y} {x : X}
  proof: .rfl

@[simp]

中文:
定理 mem_map
  条件: {f : X ⟶ Y} {U : Opens Y} {x : X}
  证明: .rfl

@[simp]
-/
theorem mem_map {f : X ⟶ Y} {U : Opens Y} {x : X} :
    x in (map f).obj U ↔ f.hom x in U := .rfl

@[simp]
/--
theorem `map_obj` / 定理 `map_obj`

English:
theorem map_obj
  given: (f : X ⟶ Y) (U) (p)
  statement: (map f).obj ⟨U, p⟩ = ⟨f ⁻¹' U, p.preimage f.hom.continuous⟩
  proof: rfl

@[simp]

中文:
定理 map_obj
  条件: (f : X ⟶ Y) (U) (p)
  结论: (map f).obj ⟨U, p⟩ = ⟨f ⁻¹' U, p.preimage f.hom.continuous⟩
  证明: rfl

@[simp]
-/
theorem map_obj (f : X ⟶ Y) (U) (p) : (map f).obj ⟨U, p⟩ = ⟨f ⁻¹' U, p.preimage f.hom.continuous⟩ :=
  rfl

@[simp]
/--
lemma `map_homOfLE` / 引理 `map_homOfLE`

English:
lemma map_homOfLE
  given: (f : X ⟶ Y) {U V : Opens Y} (e : U <= V)
  proof: rfl

@[simp]

中文:
引理 map_homOfLE
  条件: (f : X ⟶ Y) {U V : Opens Y} (e : U <= V)
  证明: rfl

@[simp]
-/
lemma map_homOfLE (f : X ⟶ Y) {U V : Opens Y} (e : U <= V) :
    (TopologicalSpace.Opens.map f).map (homOfLE e) =
      homOfLE (show (Opens.map f).obj U <= (Opens.map f).obj V from fun _ hx => e hx) :=
  rfl

@[simp]
/--
theorem `map_id_obj` / 定理 `map_id_obj`

English:
theorem map_id_obj
  given: (U : Opens X)
  statement: (map (𝟙 X)).obj U = U
  proof: let ⟨_, _⟩ := U
  rfl

@[simp]

中文:
定理 map_id_obj
  条件: (U : Opens X)
  结论: (map (𝟙 X)).obj U = U
  证明: let ⟨_, _⟩ := U
  rfl

@[simp]
-/
theorem map_id_obj (U : Opens X) : (map (𝟙 X)).obj U = U :=
  let ⟨_, _⟩ := U
  rfl

@[simp]
/--
theorem `map_id_obj'` / 定理 `map_id_obj'`

English:
theorem map_id_obj'
  given: (U) (p)
  statement: (map (𝟙 X)).obj ⟨U, p⟩ = ⟨U, p⟩
  proof: rfl

中文:
定理 map_id_obj'
  条件: (U) (p)
  结论: (map (𝟙 X)).obj ⟨U, p⟩ = ⟨U, p⟩
  证明: rfl
-/
theorem map_id_obj' (U) (p) : (map (𝟙 X)).obj ⟨U, p⟩ = ⟨U, p⟩ :=
  rfl

/--
theorem `map_id_obj_unop` / 定理 `map_id_obj_unop`

English:
theorem map_id_obj_unop
  given: (U : (Opens X)ᵒᵖ)
  statement: (map (𝟙 X)).obj (unop U) = unop U
  proof: by
  simp

中文:
定理 map_id_obj_unop
  条件: (U : (Opens X)ᵒᵖ)
  结论: (map (𝟙 X)).obj (unop U) = unop U
  证明: by
  simp
-/
theorem map_id_obj_unop (U : (Opens X)ᵒᵖ) : (map (𝟙 X)).obj (unop U) = unop U := by
  simp

/--
theorem `op_map_id_obj` / 定理 `op_map_id_obj`

English:
theorem op_map_id_obj
  given: (U : (Opens X)ᵒᵖ)
  statement: (map (𝟙 X)).op.obj U = U
  proof: by simp

@[simp]

中文:
定理 op_map_id_obj
  条件: (U : (Opens X)ᵒᵖ)
  结论: (map (𝟙 X)).op.obj U = U
  证明: by simp

@[simp]
-/
theorem op_map_id_obj (U : (Opens X)ᵒᵖ) : (map (𝟙 X)).op.obj U = U := by simp

@[simp]
/--
lemma `map_top` / 引理 `map_top`

English:
lemma map_top
  given: (f : X ⟶ Y)
  statement: (Opens.map f).obj ⊤ = ⊤
  proof: rfl

中文:
引理 map_top
  条件: (f : X ⟶ Y)
  结论: (Opens.map f).obj ⊤ = ⊤
  证明: rfl
-/
lemma map_top (f : X ⟶ Y) : (Opens.map f).obj ⊤ = ⊤ := rfl

/--
Definition of `leMapTop` / `leMapTop` 的定义

English:
definition leMapTop
  signature: (f : X ⟶ Y) (U : Opens X)
  body: leTop U

@[simp]

中文:
定义 leMapTop
  签名: (f : X ⟶ Y) (U : Opens X)
  定义体: leTop U

@[simp]
-/
noncomputable def leMapTop (f : X ⟶ Y) (U : Opens X) : U ⟶ (map f).obj ⊤ :=
  leTop U

@[simp]
/--
theorem `map_comp_obj` / 定理 `map_comp_obj`

English:
theorem map_comp_obj
  given: (f : X ⟶ Y) (g : Y ⟶ Z) (U)
  proof: rfl

@[simp]

中文:
定理 map_comp_obj
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) (U)
  证明: rfl

@[simp]
-/
theorem map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (map (f ≫ g)).obj U = (map f).obj ((map g).obj U) :=
  rfl

@[simp]
/--
theorem `map_comp_obj'` / 定理 `map_comp_obj'`

English:
theorem map_comp_obj'
  given: (f : X ⟶ Y) (g : Y ⟶ Z) (U) (p)
  proof: rfl

@[simp]

中文:
定理 map_comp_obj'
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) (U) (p)
  证明: rfl

@[simp]
-/
theorem map_comp_obj' (f : X ⟶ Y) (g : Y ⟶ Z) (U) (p) :
    (map (f ≫ g)).obj ⟨U, p⟩ = (map f).obj ((map g).obj ⟨U, p⟩) :=
  rfl

@[simp]
/--
theorem `map_comp_map` / 定理 `map_comp_map`

English:
theorem map_comp_map
  given: (f : X ⟶ Y) (g : Y ⟶ Z) {U V} (i : U ⟶ V)
  proof: rfl

@[simp]

中文:
定理 map_comp_map
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) {U V} (i : U ⟶ V)
  证明: rfl

@[simp]
-/
theorem map_comp_map (f : X ⟶ Y) (g : Y ⟶ Z) {U V} (i : U ⟶ V) :
    (map (f ≫ g)).map i = (map f).map ((map g).map i) :=
  rfl

@[simp]
/--
theorem `map_comp_obj_unop` / 定理 `map_comp_obj_unop`

English:
theorem map_comp_obj_unop
  given: (f : X ⟶ Y) (g : Y ⟶ Z) (U)
  proof: rfl

@[simp]

中文:
定理 map_comp_obj_unop
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) (U)
  证明: rfl

@[simp]
-/
theorem map_comp_obj_unop (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (map (f ≫ g)).obj (unop U) = (map f).obj ((map g).obj (unop U)) :=
  rfl

@[simp]
/--
theorem `op_map_comp_obj` / 定理 `op_map_comp_obj`

English:
theorem op_map_comp_obj
  given: (f : X ⟶ Y) (g : Y ⟶ Z) (U)
  proof: rfl

中文:
定理 op_map_comp_obj
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) (U)
  证明: rfl
-/
theorem op_map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (map (f ≫ g)).op.obj U = (map f).op.obj ((map g).op.obj U) :=
  rfl

/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: (f : X ⟶ Y) {ι : Type*} (U : ι -> Opens Y)
  proof: by
  ext
  simp

中文:
定理 map_iSup
  条件: (f : X ⟶ Y) {ι : 类型} (U : ι -> Opens Y)
  证明: by
  ext
  simp
-/
theorem map_iSup (f : X ⟶ Y) {ι : Type*} (U : ι -> Opens Y) :
    (map f).obj (iSup U) = iSup ((map f).obj ∘ U) := by
  ext
  simp

section

variable (X)

/-- The functor `Opens X ⥤ Opens X` given by taking preimages under the identity function
is naturally isomorphic to the identity functor.
-/
@[simps]
/--
Definition of `mapId` / `mapId` 的定义

English:
definition mapId
  signature: : map (𝟙 X) ≅ 𝟭 (Opens X) where
  body: { app := fun U => eqToHom (map_id_obj U) }
  inv := { app := fun U => eqToHom (map_id_obj U).symm }

中文:
定义 mapId
  签名: : map (𝟙 X) ≅ 𝟭 (Opens X) where
  定义体: { app := fun U => eqToHom (map_id_obj U) }
  inv := { app := fun U => eqToHom (map_id_obj U).symm }

Depends on / 依赖: eqToHom, map_id_obj
-/
def mapId : map (𝟙 X) ≅ 𝟭 (Opens X) where
  hom := { app := fun U => eqToHom (map_id_obj U) }
  inv := { app := fun U => eqToHom (map_id_obj U).symm }

/--
theorem `map_id_eq` / 定理 `map_id_eq`

English:
theorem map_id_eq
  statement: map (𝟙 X) = 𝟭 (Opens X)
  proof: by
  rfl

中文:
定理 map_id_eq
  结论: map (𝟙 X) = 𝟭 (Opens X)
  证明: by
  rfl
-/
theorem map_id_eq : map (𝟙 X) = 𝟭 (Opens X) := by
  rfl

end

/-- The natural isomorphism between taking preimages under `f ≫ g`, and the composite
of taking preimages under `g`, then preimages under `f`.
-/
@[simps]
/--
Definition of `mapComp` / `mapComp` 的定义

English:
definition mapComp
  signature: (f : X ⟶ Y) (g : Y ⟶ Z)
  body: { app := fun U => eqToHom (map_comp_obj f g U) }
  inv := { app := fun U => eqToHom (map_comp_obj f g U).symm }

中文:
定义 mapComp
  签名: (f : X ⟶ Y) (g : Y ⟶ Z)
  定义体: { app := fun U => eqToHom (map_comp_obj f g U) }
  inv := { app := fun U => eqToHom (map_comp_obj f g U).symm }

Depends on / 依赖: eqToHom, map_comp_obj
-/
def mapComp (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f where
  hom := { app := fun U => eqToHom (map_comp_obj f g U) }
  inv := { app := fun U => eqToHom (map_comp_obj f g U).symm }

/--
theorem `map_comp_eq` / 定理 `map_comp_eq`

English:
theorem map_comp_eq
  given: (f : X ⟶ Y) (g : Y ⟶ Z)
  statement: map (f ≫ g) = map g ⋙ map f
  proof: rfl

中文:
定理 map_comp_eq
  条件: (f : X ⟶ Y) (g : Y ⟶ Z)
  结论: map (f ≫ g) = map g ⋙ map f
  证明: rfl
-/
theorem map_comp_eq (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map g ⋙ map f :=
  rfl

-- We could make `f g` implicit here, but it's nice to be able to see when
-- they are the identity (often!)
/--
Definition of `mapIso` / `mapIso` 的定义

English:
definition mapIso
  signature: (f g : X ⟶ Y) (h : f = g)
  body: NatIso.ofComponents fun U => eqToIso (by rw [congr_arg map h])

中文:
定义 mapIso
  签名: (f g : X ⟶ Y) (h : f = g)
  定义体: NatIso.ofComponents fun U => eqToIso (by rw [congr_arg map h])

Depends on / 依赖: NatIso, NatIso.ofComponents, congr_arg, eqToIso, ofComponents
-/
def mapIso (f g : X ⟶ Y) (h : f = g) : map f ≅ map g :=
  NatIso.ofComponents fun U => eqToIso (by rw [congr_arg map h])

/--
theorem `map_eq` / 定理 `map_eq`

English:
theorem map_eq
  given: (f g : X ⟶ Y) (h : f = g)
  statement: map f = map g
  proof: by
  subst h
  rfl

@[simp]

中文:
定理 map_eq
  条件: (f g : X ⟶ Y) (h : f = g)
  结论: map f = map g
  证明: by
  subst h
  rfl

@[simp]
-/
theorem map_eq (f g : X ⟶ Y) (h : f = g) : map f = map g := by
  subst h
  rfl

@[simp]
/--
theorem `mapIso_refl` / 定理 `mapIso_refl`

English:
theorem mapIso_refl
  given: (f : X ⟶ Y) (h)
  statement: mapIso f f h = Iso.refl (map _)
  proof: rfl

@[simp]

中文:
定理 mapIso_refl
  条件: (f : X ⟶ Y) (h)
  结论: mapIso f f h = Iso.refl (map _)
  证明: rfl

@[simp]
-/
theorem mapIso_refl (f : X ⟶ Y) (h) : mapIso f f h = Iso.refl (map _) :=
  rfl

@[simp]
/--
theorem `mapIso_hom_app` / 定理 `mapIso_hom_app`

English:
theorem mapIso_hom_app
  given: (f g : X ⟶ Y) (h : f = g) (U : Opens Y)
  proof: rfl

@[simp]

中文:
定理 mapIso_hom_app
  条件: (f g : X ⟶ Y) (h : f = g) (U : Opens Y)
  证明: rfl

@[simp]
-/
theorem mapIso_hom_app (f g : X ⟶ Y) (h : f = g) (U : Opens Y) :
    (mapIso f g h).hom.app U = eqToHom (by rw [h]) :=
  rfl

@[simp]
/--
theorem `mapIso_inv_app` / 定理 `mapIso_inv_app`

English:
theorem mapIso_inv_app
  given: (f g : X ⟶ Y) (h : f = g) (U : Opens Y)
  proof: rfl

中文:
定理 mapIso_inv_app
  条件: (f g : X ⟶ Y) (h : f = g) (U : Opens Y)
  证明: rfl
-/
theorem mapIso_inv_app (f g : X ⟶ Y) (h : f = g) (U : Opens Y) :
    (mapIso f g h).inv.app U = eqToHom (by rw [h]) :=
  rfl

/--
Definition of `mapMapIso` / `mapMapIso` 的定义

English:
definition mapMapIso
  signature: {X Y : TopCat.{u}} (H : X ≅ Y)
  body: (TopCat.homeoOfIso H).opensCongr.equivalence.symm

@[simp]

中文:
定义 mapMapIso
  签名: {X Y : TopCat.{u}} (H : X ≅ Y)
  定义体: (TopCat.homeoOfIso H).opensCongr.equivalence.symm

@[simp]

Depends on / 依赖: TopCat, TopCat.homeoOfIso, equivalence, homeoOfIso, opensCongr, opensCongr.equivalence.symm
-/
def mapMapIso {X Y : TopCat.{u}} (H : X ≅ Y) : Opens Y ≌ Opens X :=
  (TopCat.homeoOfIso H).opensCongr.equivalence.symm

@[simp]
/--
lemma `mapMapIso_functor` / 引理 `mapMapIso_functor`

English:
lemma mapMapIso_functor
  given: {X Y : TopCat.{u}} (H : X ≅ Y)
  proof: rfl

@[simp]

中文:
引理 mapMapIso_functor
  条件: {X Y : TopCat.{u}} (H : X ≅ Y)
  证明: rfl

@[simp]
-/
lemma mapMapIso_functor {X Y : TopCat.{u}} (H : X ≅ Y) :
    (mapMapIso H).functor = map H.hom := rfl

@[simp]
/--
lemma `mapMapIso_inverse` / 引理 `mapMapIso_inverse`

English:
lemma mapMapIso_inverse
  given: {X Y : TopCat.{u}} (H : X ≅ Y)
  proof: rfl

@[simp]

中文:
引理 mapMapIso_inverse
  条件: {X Y : TopCat.{u}} (H : X ≅ Y)
  证明: rfl

@[simp]
-/
lemma mapMapIso_inverse {X Y : TopCat.{u}} (H : X ≅ Y) :
    (mapMapIso H).inverse = map H.inv := rfl

@[simp]
/--
lemma `mapMapIso_unitIso` / 引理 `mapMapIso_unitIso`

English:
lemma mapMapIso_unitIso
  given: {X Y : TopCat.{u}} (H : X ≅ Y)
  proof: rfl

@[simp]

中文:
引理 mapMapIso_unitIso
  条件: {X Y : TopCat.{u}} (H : X ≅ Y)
  证明: rfl

@[simp]
-/
lemma mapMapIso_unitIso {X Y : TopCat.{u}} (H : X ≅ Y) :
    (mapMapIso H).unitIso = NatIso.ofComponents (fun U => eqToIso (by cat_disch))
    (by cat_disch) := rfl

@[simp]
/--
lemma `mapMapIso_counitIso` / 引理 `mapMapIso_counitIso`

English:
lemma mapMapIso_counitIso
  given: {X Y : TopCat.{u}} (H : X ≅ Y)
  proof: rfl

中文:
引理 mapMapIso_counitIso
  条件: {X Y : TopCat.{u}} (H : X ≅ Y)
  证明: rfl
-/
lemma mapMapIso_counitIso {X Y : TopCat.{u}} (H : X ≅ Y) :
    (mapMapIso H).counitIso = NatIso.ofComponents (fun U => eqToIso (by cat_disch))
    (by cat_disch) := rfl

end TopologicalSpace.Opens

/--
Definition of `IsOpenMap.functorMap` / `IsOpenMap.functorMap` 的定义

English:
definition IsOpenMap.functorMap
  signature: {X Y : TopCat.{u}} {f : X ⟶ Y} {U V : Opens X}
  body: ⟨⟨Set.image_mono le⟩⟩

中文:
定义 IsOpenMap.functorMap
  签名: {X Y : TopCat.{u}} {f : X ⟶ Y} {U V : Opens X}
  定义体: ⟨⟨Set.image_mono le⟩⟩

Depends on / 依赖: Set.image_mono, image_mono
-/
def IsOpenMap.functorMap {X Y : TopCat.{u}} {f : X ⟶ Y} {U V : Opens X}
     (HU : IsOpen (f '' U)) (HV : IsOpen (f '' V)) (le : U <= V) :
     (⟨_, HU⟩ : Opens Y) ⟶ ⟨_, HV⟩ := ⟨⟨Set.image_mono le⟩⟩

/-- An open map `f : X ⟶ Y` induces a functor `Opens X ⥤ Opens Y`.
-/
@[simps obj_coe]
/--
Definition of `IsOpenMap.functor` / `IsOpenMap.functor` 的定义

English:
definition IsOpenMap.functor
  signature: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f)
  body: ⟨f '' (U : Set X), hf (U : Set X) U.2⟩
  map {U V} h := IsOpenMap.functorMap (hf _ U.2) (hf _ V.2) h.down.down

中文:
定义 IsOpenMap.functor
  签名: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f)
  定义体: ⟨f '' (U : Set X), hf (U : Set X) U.2⟩
  map {U V} h := IsOpenMap.functorMap (hf _ U.2) (hf _ V.2) h.down.down
-/
def IsOpenMap.functor {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f) : Opens X ⥤ Opens Y where
  obj U := ⟨f '' (U : Set X), hf (U : Set X) U.2⟩
  map {U V} h := IsOpenMap.functorMap (hf _ U.2) (hf _ V.2) h.down.down

/--
Definition of `IsOpenMap.adjunction` / `IsOpenMap.adjunction` 的定义

English:
definition IsOpenMap.adjunction
  signature: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f)
  body: { app := fun _ => homOfLE fun x hxU => ⟨x, hxU, rfl⟩ }
  counit := { app := fun _ => homOfLE fun _ ⟨_, hfxV, hxy⟩ => hxy ▸ hfxV }

中文:
定义 IsOpenMap.adjunction
  签名: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f)
  定义体: { app := fun _ => homOfLE fun x hxU => ⟨x, hxU, rfl⟩ }
  counit := { app := fun _ => homOfLE fun _ ⟨_, hfxV, hxy⟩ => hxy ▸ hfxV }

Depends on / 依赖: homOfLE
-/
def IsOpenMap.adjunction {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f) :
    hf.functor ⊣ Opens.map f where
  unit := { app := fun _ => homOfLE fun x hxU => ⟨x, hxU, rfl⟩ }
  counit := { app := fun _ => homOfLE fun _ ⟨_, hfxV, hxy⟩ => hxy ▸ hfxV }

/--
Instance `IsOpenMap.functorFullOfMono` / 实例 `IsOpenMap.functorFullOfMono`

English:
instance IsOpenMap.functorFullOfMono
  signature: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f)
  body: ⟨homOfLE fun x hx => by
      obtain ⟨y, hy, eq⟩ := i.le ⟨x, hx, rfl⟩
      exact (TopCat.mono_iff_injective f).mp H eq ▸ hy, rfl⟩

中文:
实例 IsOpenMap.functorFullOfMono
  签名: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f)
  定义体: ⟨homOfLE fun x hx => by
      obtain ⟨y, hy, eq⟩ := i.le ⟨x, hx, rfl⟩
      exact (TopCat.mono_iff_injective f).mp H eq ▸ hy, rfl⟩

Depends on / 依赖: TopCat, TopCat.mono_iff_injective, homOfLE, i.le, mono_iff_injective
-/
instance IsOpenMap.functorFullOfMono {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f)
    [H : Mono f] : hf.functor.Full where
  map_surjective i :=
    ⟨homOfLE fun x hx => by
      obtain ⟨y, hy, eq⟩ := i.le ⟨x, hx, rfl⟩
      exact (TopCat.mono_iff_injective f).mp H eq ▸ hy, rfl⟩

/--
Instance `IsOpenMap.functor_faithful` / 实例 `IsOpenMap.functor_faithful`

English:
instance IsOpenMap.functor_faithful
  signature: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f)

中文:
实例 IsOpenMap.functor_faithful
  签名: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f)
-/
instance IsOpenMap.functor_faithful {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f) :
    hf.functor.Faithful where

/--
Definition of `Topology.IsOpenEmbedding.functor` / `Topology.IsOpenEmbedding.functor` 的定义

English:
abbreviation Topology.IsOpenEmbedding.functor
  signature: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenEmbedding f)
  body: hf.isOpenMap.functor

中文:
缩写 Topology.IsOpenEmbedding.functor
  签名: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenEmbedding f)
  定义体: hf.isOpenMap.functor

Depends on / 依赖: functor, hf.isOpenMap.functor, isOpenMap
-/
abbrev Topology.IsOpenEmbedding.functor {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenEmbedding f) :=
    hf.isOpenMap.functor

/--
lemma `Topology.IsOpenEmbedding.functor_obj_injective` / 引理 `Topology.IsOpenEmbedding.functor_obj_injective`

English:
lemma Topology.IsOpenEmbedding.functor_obj_injective
  statement: {X Y : TopCat.{u}} {f : X ⟶ Y}
  proof: fun _ _ e => Opens.ext (Set.image_injective.mpr hf.injective (congr_arg (↑· : Opens Y -> Set Y) e))

中文:
引理 Topology.IsOpenEmbedding.functor_obj_injective
  结论: {X Y : TopCat.{u}} {f : X ⟶ Y}
  证明: fun _ _ e => Opens.ext (Set.image_injective.mpr hf.injective (congr_arg (↑· : Opens Y -> Set Y) e))

Depends on / 依赖: Opens.ext, Set.image_injective.mpr, congr_arg, hf.injective, image_injective, injective
-/
lemma Topology.IsOpenEmbedding.functor_obj_injective {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : IsOpenEmbedding f) : Function.Injective hf.functor.obj :=
  fun _ _ e => Opens.ext (Set.image_injective.mpr hf.injective (congr_arg (↑· : Opens Y -> Set Y) e))

/--
lemma `Topology.IsOpenEmbedding.functor_obj_iInf` / 引理 `Topology.IsOpenEmbedding.functor_obj_iInf`

English:
lemma Topology.IsOpenEmbedding.functor_obj_iInf
  statement: {X Y : TopCat.{u}} (f : X ⟶ Y)
  proof: by
  ext : 1
  simp only [IsOpenMap.coe_functor_obj, TopologicalSpace.Opens.coe_iInf]
  rw [Set.InjOn.image_iInter_eq]
  exact hf.injective.injOn

中文:
引理 Topology.IsOpenEmbedding.functor_obj_iInf
  结论: {X Y : TopCat.{u}} (f : X ⟶ Y)
  证明: by
  ext : 1
  simp only [IsOpenMap.coe_functor_obj, TopologicalSpace.Opens.coe_iInf]
  rw [Set.InjOn.image_iInter_eq]
  exact hf.injective.injOn

Depends on / 依赖: IsOpenMap, IsOpenMap.coe_functor_obj, Set.InjOn.image_iInter_eq, TopologicalSpace, TopologicalSpace.Opens.coe_iInf, coe_functor_obj, coe_iInf, hf.injective.injOn, image_iInter_eq, injective
-/
lemma Topology.IsOpenEmbedding.functor_obj_iInf {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : Topology.IsOpenEmbedding f) {ι : Type*} [Nonempty ι] [Finite ι]
    (g : ι -> TopologicalSpace.Opens X) :
    hf.functor.obj (⨅ i, g i) = ⨅ i, hf.functor.obj (g i) := by
  ext : 1
  simp only [IsOpenMap.coe_functor_obj, TopologicalSpace.Opens.coe_iInf]
  rw [Set.InjOn.image_iInter_eq]
  exact hf.injective.injOn

namespace Topology.IsInducing

/-- Given an inducing map `X ⟶ Y` and some `U : Opens X`, this is the union of all open sets
whose preimage is `U`. This is right adjoint to `Opens.map`. -/
@[nolint unusedArguments]
/--
Definition of `functorObj` / `functorObj` 的定义

English:
definition functorObj
  signature: {X Y : TopCat.{u}} {f : X ⟶ Y} (_ : IsInducing f) (U : Opens X)
  body: sSup { s : Opens Y | (Opens.map f).obj s = U }

中文:
定义 functorObj
  签名: {X Y : TopCat.{u}} {f : X ⟶ Y} (_ : IsInducing f) (U : Opens X)
  定义体: sSup { s : Opens Y | (Opens.map f).obj s = U }

Depends on / 依赖: Opens.map
-/
def functorObj {X Y : TopCat.{u}} {f : X ⟶ Y} (_ : IsInducing f) (U : Opens X) : Opens Y :=
  sSup { s : Opens Y | (Opens.map f).obj s = U }

/--
lemma `map_functorObj` / 引理 `map_functorObj`

English:
lemma map_functorObj
  statement: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f)
  proof: by
  apply le_antisymm
  · rintro x ⟨_, ⟨s, rfl⟩, _, ⟨rfl : _ = U, rfl⟩, hx : f x in s⟩; exact hx
  · intro x hx
    obtain ⟨U, hU⟩ := U
    obtain ⟨t, ht, rfl⟩ := hf.isOpen_iff.mp hU
    exact Opens.mem_sSup.mpr ⟨⟨_, ht⟩, rfl, hx⟩

中文:
引理 map_functorObj
  结论: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f)
  证明: by
  apply le_antisymm
  · rintro x ⟨_, ⟨s, rfl⟩, _, ⟨rfl : _ = U, rfl⟩, hx : f x in s⟩; exact hx
  · intro x hx
    obtain ⟨U, hU⟩ := U
    obtain ⟨t, ht, rfl⟩ := hf.isOpen_iff.mp hU
    exact Opens.mem_sSup.mpr ⟨⟨_, ht⟩, rfl, hx⟩

Depends on / 依赖: Opens.mem_sSup.mpr, hf.isOpen_iff.mp, isOpen_iff, le_antisymm, mem_sSup
-/
lemma map_functorObj {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f)
    (U : Opens X) :
    (Opens.map f).obj (hf.functorObj U) = U := by
  apply le_antisymm
  · rintro x ⟨_, ⟨s, rfl⟩, _, ⟨rfl : _ = U, rfl⟩, hx : f x in s⟩; exact hx
  · intro x hx
    obtain ⟨U, hU⟩ := U
    obtain ⟨t, ht, rfl⟩ := hf.isOpen_iff.mp hU
    exact Opens.mem_sSup.mpr ⟨⟨_, ht⟩, rfl, hx⟩

/--
lemma `mem_functorObj_iff` / 引理 `mem_functorObj_iff`

English:
lemma mem_functorObj_iff
  statement: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) (U : Opens X)
  proof: by
  conv_rhs => rw [← hf.map_functorObj U]
  rfl

中文:
引理 mem_functorObj_iff
  结论: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) (U : Opens X)
  证明: by
  conv_rhs => rw [← hf.map_functorObj U]
  rfl

Depends on / 依赖: conv_rhs, hf.map_functorObj, map_functorObj
-/
lemma mem_functorObj_iff {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) (U : Opens X)
    {x : X} : f x in hf.functorObj U ↔ x in U := by
  conv_rhs => rw [← hf.map_functorObj U]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `le_functorObj_iff` / 引理 `le_functorObj_iff`

English:
lemma le_functorObj_iff
  statement: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) {U : Opens X}
  proof: by
  obtain ⟨U, hU⟩ := U
  obtain ⟨t, ht, rfl⟩ := hf.isOpen_iff.mp hU
  constructor
  · exact fun i x hx => (hf.mem_functorObj_iff ((Opens.map f).obj ⟨t, ht⟩)).mp (i hx)
  · intro h x hx
    refine Opens.mem_sSup.mpr ⟨⟨_, V.2.union ht⟩, Opens.ext ?_, Set.mem_union_left t hx⟩
    dsimp
    rwa [Set.u

中文:
引理 le_functorObj_iff
  结论: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) {U : Opens X}
  证明: by
  obtain ⟨U, hU⟩ := U
  obtain ⟨t, ht, rfl⟩ := hf.isOpen_iff.mp hU
  constructor
  · exact fun i x hx => (hf.mem_functorObj_iff ((Opens.map f).obj ⟨t, ht⟩)).mp (i hx)
  · intro h x hx
    refine Opens.mem_sSup.mpr ⟨⟨_, V.2.union ht⟩, Opens.ext ?_, Set.mem_union_left t hx⟩
    dsimp
    rwa [Set.u

Depends on / 依赖: Opens.ext, Opens.map, Opens.mem_sSup.mpr, Set.mem_union_left, Set.union_eq_right, hf.isOpen_iff.mp, hf.mem_functorObj_iff, isOpen_iff, mem_functorObj_iff, mem_sSup, mem_union_left, union_eq_right
-/
lemma le_functorObj_iff {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) {U : Opens X}
    {V : Opens Y} : V <= hf.functorObj U ↔ (Opens.map f).obj V <= U := by
  obtain ⟨U, hU⟩ := U
  obtain ⟨t, ht, rfl⟩ := hf.isOpen_iff.mp hU
  constructor
  · exact fun i x hx => (hf.mem_functorObj_iff ((Opens.map f).obj ⟨t, ht⟩)).mp (i hx)
  · intro h x hx
    refine Opens.mem_sSup.mpr ⟨⟨_, V.2.union ht⟩, Opens.ext ?_, Set.mem_union_left t hx⟩
    dsimp
    rwa [Set.union_eq_right]

/--
Definition of `opensGI` / `opensGI` 的定义

English:
definition opensGI
  signature: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f)
  body: ⟨_, fun _ _ => hf.le_functorObj_iff.symm, fun U => (hf.map_functorObj U).ge, fun _ _ => rfl⟩

中文:
定义 opensGI
  签名: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f)
  定义体: ⟨_, fun _ _ => hf.le_functorObj_iff.symm, fun U => (hf.map_functorObj U).ge, fun _ _ => rfl⟩

Depends on / 依赖: hf.le_functorObj_iff.symm, hf.map_functorObj, le_functorObj_iff, map_functorObj
-/
def opensGI {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) :
    GaloisInsertion (Opens.map f).obj hf.functorObj :=
  ⟨_, fun _ _ => hf.le_functorObj_iff.symm, fun U => (hf.map_functorObj U).ge, fun _ _ => rfl⟩

/-- An inducing map `f : X ⟶ Y` induces a functor `Opens X ⥤ Opens Y`. -/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f)
  body: hf.functorObj
  map {U V} h := homOfLE (hf.le_functorObj_iff.mpr ((hf.map_functorObj U).trans_le h.le))

中文:
定义 functor
  签名: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f)
  定义体: hf.functorObj
  map {U V} h := homOfLE (hf.le_functorObj_iff.mpr ((hf.map_functorObj U).trans_le h.le))

Depends on / 依赖: functorObj, hf.functorObj
-/
def functor {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) :
    Opens X ⥤ Opens Y where
  obj := hf.functorObj
  map {U V} h := homOfLE (hf.le_functorObj_iff.mpr ((hf.map_functorObj U).trans_le h.le))

/--
Definition of `adjunction` / `adjunction` 的定义

English:
definition adjunction
  signature: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f)
  body: hf.opensGI.gc.adjunction

中文:
定义 adjunction
  签名: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f)
  定义体: hf.opensGI.gc.adjunction

Depends on / 依赖: adjunction, hf.opensGI.gc.adjunction, opensGI
-/
def adjunction {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) :
    Opens.map f ⊣ hf.functor :=
  hf.opensGI.gc.adjunction

end Topology.IsInducing

namespace TopologicalSpace.Opens

open TopologicalSpace

@[simp]
/--
theorem `isOpenEmbedding_obj_top` / 定理 `isOpenEmbedding_obj_top`

English:
theorem isOpenEmbedding_obj_top
  given: {X : TopCat.{u}} (U : Opens X)
  proof: by
  ext1
  exact Set.image_univ.trans Subtype.range_coe

@[simp]

中文:
定理 isOpenEmbedding_obj_top
  条件: {X : TopCat.{u}} (U : Opens X)
  证明: by
  ext1
  exact Set.image_univ.trans Subtype.range_coe

@[simp]

Depends on / 依赖: Set.image_univ.trans, Subtype, Subtype.range_coe, image_univ, range_coe
-/
theorem isOpenEmbedding_obj_top {X : TopCat.{u}} (U : Opens X) :
    U.isOpenEmbedding.functor.obj ⊤ = U := by
  ext1
  exact Set.image_univ.trans Subtype.range_coe

@[simp]
/--
theorem `inclusion'_map_eq_top` / 定理 `inclusion'_map_eq_top`

English:
theorem inclusion'_map_eq_top
  given: {X : TopCat.{u}} (U : Opens X)
  proof: by
  ext1
  exact Subtype.coe_preimage_self _

@[simp]

中文:
定理 inclusion'_map_eq_top
  条件: {X : TopCat.{u}} (U : Opens X)
  证明: by
  ext1
  exact Subtype.coe_preimage_self _

@[simp]
-/
theorem inclusion'_map_eq_top {X : TopCat.{u}} (U : Opens X) :
    (Opens.map U.inclusion').obj U = ⊤ := by
  ext1
  exact Subtype.coe_preimage_self _

@[simp]
/--
theorem `adjunction_counit_app_self` / 定理 `adjunction_counit_app_self`

English:
theorem adjunction_counit_app_self
  given: {X : TopCat.{u}} (U : Opens X)
  proof: Subsingleton.elim _ _

中文:
定理 adjunction_counit_app_self
  条件: {X : TopCat.{u}} (U : Opens X)
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem adjunction_counit_app_self {X : TopCat.{u}} (U : Opens X) :
    U.isOpenEmbedding.isOpenMap.adjunction.counit.app U = eqToHom (by simp) := Subsingleton.elim _ _

/--
theorem `inclusion'_top_functor` / 定理 `inclusion'_top_functor`

English:
theorem inclusion'_top_functor
  given: (X : TopCat)
  proof: by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro U
    ext x
    exact ⟨fun ⟨⟨_, _⟩, h, rfl⟩ => h, fun h => ⟨⟨x, trivial⟩, h, rfl⟩⟩
  · subsingleton

中文:
定理 inclusion'_top_functor
  条件: (X : TopCat)
  证明: by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro U
    ext x
    exact ⟨fun ⟨⟨_, _⟩, h, rfl⟩ => h, fun h => ⟨⟨x, trivial⟩, h, rfl⟩⟩
  · subsingleton
-/
theorem inclusion'_top_functor (X : TopCat) :
    (@Opens.isOpenEmbedding X ⊤).functor = map (inclusionTopIso X).inv := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro U
    ext x
    exact ⟨fun ⟨⟨_, _⟩, h, rfl⟩ => h, fun h => ⟨⟨x, trivial⟩, h, rfl⟩⟩
  · subsingleton

/--
theorem `functor_obj_map_obj` / 定理 `functor_obj_map_obj`

English:
theorem functor_obj_map_obj
  given: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f) (U : Opens Y)
  proof: by
  ext
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, trivial, rfl⟩, hx⟩
  · rintro ⟨⟨x, -, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩

中文:
定理 functor_obj_map_obj
  条件: {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f) (U : Opens Y)
  证明: by
  ext
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, trivial, rfl⟩, hx⟩
  · rintro ⟨⟨x, -, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩
-/
theorem functor_obj_map_obj {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f) (U : Opens Y) :
    hf.functor.obj ((Opens.map f).obj U) = hf.functor.obj ⊤ ⊓ U := by
  ext
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, trivial, rfl⟩, hx⟩
  · rintro ⟨⟨x, -, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩

/--
lemma `set_range_inclusion'` / 引理 `set_range_inclusion'`

English:
lemma set_range_inclusion'
  given: {X : TopCat.{u}} (U : Opens X)
  proof: by
  ext x
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

@[simp]

中文:
引理 set_range_inclusion'
  条件: {X : TopCat.{u}} (U : Opens X)
  证明: by
  ext x
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

@[simp]
-/
lemma set_range_inclusion' {X : TopCat.{u}} (U : Opens X) :
    Set.range (inclusion' U) = (U : Set X) := by
  ext x
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

@[simp]
/--
theorem `functor_map_eq_inf` / 定理 `functor_map_eq_inf`

English:
theorem functor_map_eq_inf
  given: {X : TopCat.{u}} (U V : Opens X)
  proof: by
  ext1
  simp only [IsOpenMap.coe_functor_obj, map_coe, coe_inf,
    Set.image_preimage_eq_inter_range, set_range_inclusion' U]

中文:
定理 functor_map_eq_inf
  条件: {X : TopCat.{u}} (U V : Opens X)
  证明: by
  ext1
  simp only [IsOpenMap.coe_functor_obj, map_coe, coe_inf,
    Set.image_preimage_eq_inter_range, set_range_inclusion' U]

Depends on / 依赖: IsOpenMap, IsOpenMap.coe_functor_obj, Set.image_preimage_eq_inter_range, coe_functor_obj, coe_inf, image_preimage_eq_inter_range, map_coe, set_range_inclusion
-/
theorem functor_map_eq_inf {X : TopCat.{u}} (U V : Opens X) :
    U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) = V ⊓ U := by
  ext1
  simp only [IsOpenMap.coe_functor_obj, map_coe, coe_inf,
    Set.image_preimage_eq_inter_range, set_range_inclusion' U]

/--
theorem `map_functor_eq'` / 定理 `map_functor_eq'`

English:
theorem map_functor_eq'
  given: {X U : TopCat.{u}} (f : U ⟶ X) (hf : IsOpenEmbedding f) (V)
  proof: Opens.ext Set.preimage_image_eq _ hf.injective

@[simp]

中文:
定理 map_functor_eq'
  条件: {X U : TopCat.{u}} (f : U ⟶ X) (hf : IsOpenEmbedding f) (V)
  证明: Opens.ext Set.preimage_image_eq _ hf.injective

@[simp]

Depends on / 依赖: Opens.ext, Set.preimage_image_eq, hf.injective, injective, preimage_image_eq
-/
theorem map_functor_eq' {X U : TopCat.{u}} (f : U ⟶ X) (hf : IsOpenEmbedding f) (V) :
    ((Opens.map f).obj <| hf.functor.obj V) = V :=
Opens.ext Set.preimage_image_eq _ hf.injective

@[simp]
/--
theorem `map_functor_eq` / 定理 `map_functor_eq`

English:
theorem map_functor_eq
  given: {X : TopCat.{u}} {U : Opens X} (V : Opens U)
  proof: TopologicalSpace.Opens.map_functor_eq' _ U.isOpenEmbedding V

中文:
定理 map_functor_eq
  条件: {X : TopCat.{u}} {U : Opens X} (V : Opens U)
  证明: TopologicalSpace.Opens.map_functor_eq' _ U.isOpenEmbedding V

Depends on / 依赖: TopologicalSpace, TopologicalSpace.Opens.map_functor_eq, U.isOpenEmbedding, isOpenEmbedding, map_functor_eq
-/
theorem map_functor_eq {X : TopCat.{u}} {U : Opens X} (V : Opens U) :
    ((Opens.map U.inclusion').obj <| U.isOpenEmbedding.functor.obj V) = V :=
  TopologicalSpace.Opens.map_functor_eq' _ U.isOpenEmbedding V

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `adjunction_counit_map_functor` / 定理 `adjunction_counit_map_functor`

English:
theorem adjunction_counit_map_functor
  given: {X : TopCat.{u}} {U : Opens X} (V : Opens U)
  proof: by
  subsingleton

中文:
定理 adjunction_counit_map_functor
  条件: {X : TopCat.{u}} {U : Opens X} (V : Opens U)
  证明: by
  subsingleton

Depends on / 依赖: subsingleton
-/
theorem adjunction_counit_map_functor {X : TopCat.{u}} {U : Opens X} (V : Opens U) :
    U.isOpenEmbedding.isOpenMap.adjunction.counit.app (U.isOpenEmbedding.functor.obj V) =
      eqToHom (by dsimp; rw [map_functor_eq V]) := by
  subsingleton

open Limits in
instance {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f) {ι : Type*}
    [Nonempty ι] [Finite ι] :
    PreservesLimitsOfShape (Discrete ι) hf.functor := by
  apply +allowSynthFailures preservesLimitsOfShape_of_discrete
  intro g
  refine preservesLimit_of_preserves_limit_cone (Preorder.isLimitIInf g) ?_
  refine (Limits.Fan.isLimitMapConeEquiv _ _ _).symm (Preorder.isLimitOfIsGLB _ _ ?_)
  simp only [Discrete.range_functor, homOfLE_leOfHom, Fan.mk_pt, hf.functor_obj_iInf]
  apply isGLB_iInf

end TopologicalSpace.Opens
