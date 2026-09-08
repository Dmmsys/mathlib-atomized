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

/-!
Since `Opens X` has a partial order, it automatically receives a `Category` instance.
Unfortunately, because we do not allow morphisms in `Prop`,
the morphisms `U ⟶ V` are not just proofs `U ≤ V`, but rather
`ULift (PLift (U ≤ V))`.
-/

/-
**TopologicalSpace.Opens.opensHom.instFunLike** 是 Mathlib 中的一个定义，位于命名空间 `Topolog
icalSpace.Opens.opensHom`。
形式化陈述：{X : TopCat} → {U V : TopologicalSpace.Opens ↑X} → FunLike (U ⟶ V) ↥U ↥V
参数：U ⟶ V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Since `Opens X` has a partial order, it automatically receives a `Category` inst
ance.
Unfortunately, because we do not allow morphisms in `Prop`,
the morphisms `U ⟶ V` are not just proofs `U ≤ V`, but rather
`ULift (PLift (U ≤ V))`.
-/
instance opensHom.instFunLike : FunLike (U ⟶ V) U V where
  coe f := Set.inclusion f.le
  coe_injective := by rintro ⟨⟨_⟩⟩ _ _; congr!
/-
**TopologicalSpace.Opens.apply_def** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.O
pens`。
形式化陈述：apply_def (f : U ⟶ V) (x : U) : f x = ⟨x, f.le x.2⟩
参数：f : U ⟶ V；x : U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma apply_def (f : U ⟶ V) (x : U) : f x = ⟨x, f.le x.2⟩ := rfl
/-
**TopologicalSpace.Opens.apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：∀ {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (f : U ⟶ V) (x : ↑X) (hx 
: x ∈ U), f ⟨x, hx⟩ = ⟨x, ⋯⟩
参数：f : U ⟶ V；x : ↑X；hx : x ∈ U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma apply_mk (f : U ⟶ V) (x : X) (hx) : f ⟨x, hx⟩ = ⟨x, f.le hx⟩ := rfl
/-
**TopologicalSpace.Opens.val_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.O
pens`。
形式化陈述：∀ {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (f : U ⟶ V) (x : ↥U), ↑(f
 x) = ↑x
参数：f : U ⟶ V；x : ↥U；f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma val_apply (f : U ⟶ V) (x : U) : (f x : X) = x := rfl
/-
**TopologicalSpace.Opens.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Open
s`。
形式化陈述：∀ {X : TopCat} {U : TopologicalSpace.Opens ↑X} (f : U ⟶ U), ⇑f = id
参数：f : U ⟶ U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_id (f : U ⟶ U) : ⇑f = id := rfl
/-
**TopologicalSpace.Opens.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：id_apply (f : U ⟶ U) (x : U) : f x = x
参数：f : U ⟶ U；x : U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_apply (f : U ⟶ U) (x : U) : f x = x := rfl
/-
**TopologicalSpace.Opens.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Opens`。
形式化陈述：∀ {X : TopCat} {U V W : TopologicalSpace.Opens ↑X} (f : U ⟶ V) (g : V ⟶ W)
 (x : ↥U),   (CategoryTheory.CategoryStruct.comp f g) x = g (f x)
参数：f : U ⟶ V；g : V ⟶ W；x : ↥U；CategoryTheory.CategoryStruct.comp f g；f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comp_apply (f : U ⟶ V) (g : V ⟶ W) (x : U) : (f ≫ g) x = g (f x) := rfl

/-!
We now construct as morphisms various inclusions of open sets.
-/


-- This is tedious, but necessary because we decided not to allow Prop as morphisms in a category...
/-- The inclusion `U ⊓ V ⟶ U` as a morphism in the category of open sets.
-/
/-
**TopologicalSpace.Opens.infLELeft** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.O
pens`。
形式化陈述：infLELeft (U V : Opens X) : U ⊓ V ⟶ U
参数：U V : Opens X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `U ⊓ V ⟶ U` as a morphism in the category of open sets.
-/
noncomputable def infLELeft (U V : Opens X) : U ⊓ V ⟶ U :=
  inf_le_left.hom

/-- The inclusion `U ⊓ V ⟶ V` as a morphism in the category of open sets.
-/
/-
**TopologicalSpace.Opens.infLERight** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.
Opens`。
形式化陈述：infLERight (U V : Opens X) : U ⊓ V ⟶ V
参数：U V : Opens X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `U ⊓ V ⟶ V` as a morphism in the category of open sets.
-/
noncomputable def infLERight (U V : Opens X) : U ⊓ V ⟶ V :=
  inf_le_right.hom

/-- The inclusion `U i ⟶ iSup U` as a morphism in the category of open sets.
-/
/-
**TopologicalSpace.Opens.leSupr** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Open
s`。
形式化陈述：leSupr {ι : Type*} (U : ι -> Opens X) (i : ι) : U i ⟶ iSup U
参数：U : ι -> Opens X；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `U i ⟶ iSup U` as a morphism in the category of open sets.
-/
noncomputable def leSupr {ι : Type*} (U : ι → Opens X) (i : ι) : U i ⟶ iSup U :=
  (le_iSup U i).hom

/-- The inclusion `⊥ ⟶ U` as a morphism in the category of open sets.
-/
/-
**TopologicalSpace.Opens.botLE** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Opens
`。
形式化陈述：botLE (U : Opens X) : ⊥ ⟶ U
参数：U : Opens X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `⊥ ⟶ U` as a morphism in the category of open sets.
-/
noncomputable def botLE (U : Opens X) : ⊥ ⟶ U :=
  bot_le.hom

/-- The inclusion `U ⟶ ⊤` as a morphism in the category of open sets.
-/
/-
**TopologicalSpace.Opens.leTop** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Opens
`。
形式化陈述：leTop (U : Opens X) : U ⟶ ⊤
参数：U : Opens X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `U ⟶ ⊤` as a morphism in the category of open sets.
-/
noncomputable def leTop (U : Opens X) : U ⟶ ⊤ :=
  le_top.hom

-- We do not mark this as a simp lemma because it breaks open `x`.
-- Nevertheless, it is useful in `SheafOfFunctions`.
/-
**TopologicalSpace.Opens.infLELeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.Opens`。
形式化陈述：infLELeft_apply (U V : Opens X) (x) : (infLELeft U V) x = ⟨x.1, (@inf_le_l
eft _ _ U V : _ <= _) x.2⟩
参数：U V : Opens X；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem infLELeft_apply (U V : Opens X) (x) :
    (infLELeft U V) x = ⟨x.1, (@inf_le_left _ _ U V : _ ≤ _) x.2⟩ :=
  rfl

@[simp]
/-
**TopologicalSpace.Opens.infLELeft_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `Topologic
alSpace.Opens`。
形式化陈述：infLELeft_apply_mk (U V : Opens X) (x) (m) : (infLELeft U V) ⟨x, m⟩ = ⟨x, 
(@inf_le_left _ _ U V : _ <= _) m⟩
参数：U V : Opens X；x；m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem infLELeft_apply_mk (U V : Opens X) (x) (m) :
    (infLELeft U V) ⟨x, m⟩ = ⟨x, (@inf_le_left _ _ U V : _ ≤ _) m⟩ :=
  rfl

@[simp]
/-
**TopologicalSpace.Opens.leSupr_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.Opens`。
形式化陈述：leSupr_apply_mk {ι : Type*} (U : ι -> Opens X) (i : ι) (x) (m) : (leSupr U
 i) ⟨x, m⟩ = ⟨x, (le_iSup U i :) m⟩
参数：U : ι -> Opens X；i : ι；x；m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leSupr_apply_mk {ι : Type*} (U : ι → Opens X) (i : ι) (x) (m) :
    (leSupr U i) ⟨x, m⟩ = ⟨x, (le_iSup U i :) m⟩ :=
  rfl

/-- The functor from open sets in `X` to `TopCat`,
realising each open set as a topological space itself.
-/
/-
**TopologicalSpace.Opens.toTopCat** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：toTopCat (X : TopCat.{u}) : Opens X ⥤ TopCat where obj U
参数：X : TopCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from open sets in `X` to `TopCat`,
realising each open set as a topological space itself.
-/
def toTopCat (X : TopCat.{u}) : Opens X ⥤ TopCat where
  obj U := TopCat.of U
  map i := TopCat.ofHom ⟨fun x ↦ ⟨x.1, i.le x.2⟩,
    IsEmbedding.subtypeVal.continuous_iff.2 continuous_induced_dom⟩

@[simp]
/-
**TopologicalSpace.Opens.toTopCat_map** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpac
e.Opens`。
形式化陈述：toTopCat_map (X : TopCat.{u}) {U V : Opens X} {f : U ⟶ V} {x} {h} : ((toTo
pCat X).map f) ⟨x, h⟩ = ⟨x, f.le h⟩
参数：X : TopCat.{u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toTopCat_map (X : TopCat.{u}) {U V : Opens X} {f : U ⟶ V} {x} {h} :
    ((toTopCat X).map f) ⟨x, h⟩ = ⟨x, f.le h⟩ :=
  rfl

/-- The inclusion map from an open subset to the whole space, as a morphism in `TopCat`.
-/
@[simps! -fullyApplied]
/-
**TopologicalSpace.Opens.inclusion'** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.
Opens`。
形式化陈述：inclusion' {X : TopCat.{u}} (U : Opens X) : (toTopCat X).obj U ⟶ X
参数：U : Opens X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map from an open subset to the whole space, as a morphism in `TopC
at`.
-/
def inclusion' {X : TopCat.{u}} (U : Opens X) : (toTopCat X).obj U ⟶ X :=
  TopCat.ofHom
  { toFun := _
    continuous_toFun := continuous_subtype_val }

@[simp]
/-
**TopologicalSpace.Opens.coe_inclusion'** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.Opens`。
形式化陈述：coe_inclusion' {X : TopCat.{u}} {U : Opens X} : (inclusion' U : U -> X) = 
Subtype.val
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inclusion' {X : TopCat.{u}} {U : Opens X} :
    (inclusion' U : U → X) = Subtype.val := rfl
/-
**TopologicalSpace.Opens.isOpenEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.Opens`。
形式化陈述：isOpenEmbedding {X : TopCat.{u}} (U : Opens X) : IsOpenEmbedding (inclusio
n' U)
参数：U : Opens X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
-/
theorem isOpenEmbedding {X : TopCat.{u}} (U : Opens X) : IsOpenEmbedding (inclusion' U) :=
  U.2.isOpenEmbedding_subtypeVal

/-- The inclusion of the top open subset (i.e. the whole space) is an isomorphism.
-/
/-
**TopologicalSpace.Opens.inclusionTopIso** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalS
pace.Opens`。
形式化陈述：inclusionTopIso (X : TopCat.{u}) : (toTopCat X).obj ⊤ ≅ X where hom
参数：X : TopCat.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
The inclusion of the top open subset (i.e. the whole space) is an isomorphism.
-/
def inclusionTopIso (X : TopCat.{u}) : (toTopCat X).obj ⊤ ≅ X where
  hom := inclusion' ⊤
  inv := TopCat.ofHom ⟨fun x => ⟨x, trivial⟩, continuous_def.2 fun _ ⟨_, hS, hSU⟩ => hSU ▸ hS⟩

/-- The FrameHom sending an open in `Y` to its preimage in `X` -/
@[simps]
/-
**TopologicalSpace.Opens._root_.TopCat.Hom.frameHom** 是 Mathlib 中的一个定义，位于命名空间 `T
opologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The FrameHom sending an open in `Y` to its preimage in `X`
-/
def _root_.TopCat.Hom.frameHom (f : X ⟶ Y) : FrameHom (Opens Y) (Opens X) where
  toFun U := ⟨f ⁻¹' (U : Set Y), U.isOpen.preimage f.hom.continuous⟩
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' _ := by ext; simp

/-- `Opens.map f` gives the functor from open sets in Y to open set in X,
given by taking preimages under f. -/
/-
**TopologicalSpace.Opens.map** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Opens`。
形式化陈述：map (f : X ⟶ Y) : Opens Y ⥤ Opens X
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Opens.map f` gives the functor from open sets in Y to open set in X,
given by taking preimages under f.
-/
def map (f : X ⟶ Y) : Opens Y ⥤ Opens X :=
  (OrderHomClass.toOrderHom f.frameHom).toFunctor
/-
**TopologicalSpace.Opens.map_def** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：map_def (f : X ⟶ Y) : map f = { obj U
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_def (f : X ⟶ Y) : map f =
  { obj U := ⟨f ⁻¹' (U : Set Y), U.isOpen.preimage f.hom.continuous⟩
    map i := ⟨⟨fun _ h => i.le h⟩⟩ } := rfl

@[simp]
/-
**TopologicalSpace.Opens.map_coe** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：map_coe (f : X ⟶ Y) (U : Opens Y) : ((map f).obj U : Set X) = f ⁻¹' (U : S
et Y)
参数：f : X ⟶ Y；U : Opens Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_coe (f : X ⟶ Y) (U : Opens Y) : ((map f).obj U : Set X) = f ⁻¹' (U : Set Y) :=
  rfl

@[simp]
/-
**TopologicalSpace.Opens.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：mem_map {f : X ⟶ Y} {U : Opens Y} {x : X} : x in (map f).obj U ↔ f.hom x i
n U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map {f : X ⟶ Y} {U : Opens Y} {x : X} :
    x ∈ (map f).obj U ↔ f.hom x ∈ U := .rfl

@[simp]
/-
**TopologicalSpace.Opens.map_obj** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：map_obj (f : X ⟶ Y) (U) (p) : (map f).obj ⟨U, p⟩ = ⟨f ⁻¹' U, p.preimage f.
hom.continuous⟩
参数：f : X ⟶ Y；U；p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_obj (f : X ⟶ Y) (U) (p) : (map f).obj ⟨U, p⟩ = ⟨f ⁻¹' U, p.preimage f.hom.continuous⟩ :=
  rfl

@[simp]
/-
**TopologicalSpace.Opens.map_homOfLE** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace
.Opens`。
形式化陈述：map_homOfLE (f : X ⟶ Y) {U V : Opens Y} (e : U <= V) : (TopologicalSpace.O
pens.map f).map (homOfLE e) = homOfLE (show (Opens.map f).obj U <= (Opens.map f)
.obj V from fun _ hx => e hx)
参数：f : X ⟶ Y；e : U <= V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_homOfLE (f : X ⟶ Y) {U V : Opens Y} (e : U ≤ V) :
    (TopologicalSpace.Opens.map f).map (homOfLE e) =
      homOfLE (show (Opens.map f).obj U ≤ (Opens.map f).obj V from fun _ hx ↦ e hx) :=
  rfl

@[simp]
/-
**TopologicalSpace.Opens.map_id_obj** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Opens`。
形式化陈述：map_id_obj (U : Opens X) : (map (𝟙 X)).obj U = U
参数：U : Opens X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_id_obj (U : Opens X) : (map (𝟙 X)).obj U = U :=
  let ⟨_, _⟩ := U
  rfl

@[simp]
/-
**TopologicalSpace.Opens.map_id_obj'** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace
.Opens`。
形式化陈述：map_id_obj' (U) (p) : (map (𝟙 X)).obj ⟨U, p⟩ = ⟨U, p⟩
参数：U；p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_id_obj' (U) (p) : (map (𝟙 X)).obj ⟨U, p⟩ = ⟨U, p⟩ :=
  rfl
/-
**TopologicalSpace.Opens.map_id_obj_unop** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.Opens`。
形式化陈述：map_id_obj_unop (U : (Opens X)ᵒᵖ) : (map (𝟙 X)).obj (unop U) = unop U
参数：U : (Opens X)ᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.map_id_obj`：map_id_obj (U : Opens X) : (map (𝟙 X)
).obj U = U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_id_obj_unop (U : (Opens X)ᵒᵖ) : (map (𝟙 X)).obj (unop U) = unop U := by
  simp
/-
**TopologicalSpace.Opens.op_map_id_obj** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpa
ce.Opens`。
形式化陈述：op_map_id_obj (U : (Opens X)ᵒᵖ) : (map (𝟙 X)).op.obj U = U
参数：U : (Opens X)ᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.map_id_obj`：map_id_obj (U : Opens X) : (map (𝟙 X)
).obj U = U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem op_map_id_obj (U : (Opens X)ᵒᵖ) : (map (𝟙 X)).op.obj U = U := by simp

@[simp]
/-
**TopologicalSpace.Opens.map_top** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：map_top (f : X ⟶ Y) : (Opens.map f).obj ⊤ = ⊤
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_top (f : X ⟶ Y) : (Opens.map f).obj ⊤ = ⊤ := rfl

/-- The inclusion `U ⟶ (map f).obj ⊤` as a morphism in the category of open sets.
-/
/-
**TopologicalSpace.Opens.leMapTop** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：leMapTop (f : X ⟶ Y) (U : Opens X) : U ⟶ (map f).obj ⊤
参数：f : X ⟶ Y；U : Opens X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `U ⟶ (map f).obj ⊤` as a morphism in the category of open sets.
-/
noncomputable def leMapTop (f : X ⟶ Y) (U : Opens X) : U ⟶ (map f).obj ⊤ :=
  leTop U

@[simp]
/-
**TopologicalSpace.Opens.map_comp_obj** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpac
e.Opens`。
形式化陈述：map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (map (f ≫ g)).obj U = (map f).o
bj ((map g).obj U)
参数：f : X ⟶ Y；g : Y ⟶ Z；U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (map (f ≫ g)).obj U = (map f).obj ((map g).obj U) :=
  rfl

@[simp]
/-
**TopologicalSpace.Opens.map_comp_obj'** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpa
ce.Opens`。
形式化陈述：map_comp_obj' (f : X ⟶ Y) (g : Y ⟶ Z) (U) (p) : (map (f ≫ g)).obj ⟨U, p⟩ =
 (map f).obj ((map g).obj ⟨U, p⟩)
参数：f : X ⟶ Y；g : Y ⟶ Z；U；p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_obj' (f : X ⟶ Y) (g : Y ⟶ Z) (U) (p) :
    (map (f ≫ g)).obj ⟨U, p⟩ = (map f).obj ((map g).obj ⟨U, p⟩) :=
  rfl

@[simp]
/-
**TopologicalSpace.Opens.map_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpac
e.Opens`。
形式化陈述：map_comp_map (f : X ⟶ Y) (g : Y ⟶ Z) {U V} (i : U ⟶ V) : (map (f ≫ g)).map
 i = (map f).map ((map g).map i)
参数：f : X ⟶ Y；g : Y ⟶ Z；i : U ⟶ V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_map (f : X ⟶ Y) (g : Y ⟶ Z) {U V} (i : U ⟶ V) :
    (map (f ≫ g)).map i = (map f).map ((map g).map i) :=
  rfl

@[simp]
/-
**TopologicalSpace.Opens.map_comp_obj_unop** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace.Opens`。
形式化陈述：map_comp_obj_unop (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (map (f ≫ g)).obj (unop U)
 = (map f).obj ((map g).obj (unop U))
参数：f : X ⟶ Y；g : Y ⟶ Z；U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_obj_unop (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (map (f ≫ g)).obj (unop U) = (map f).obj ((map g).obj (unop U)) :=
  rfl

@[simp]
/-
**TopologicalSpace.Opens.op_map_comp_obj** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.Opens`。
形式化陈述：op_map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (map (f ≫ g)).op.obj U = (ma
p f).op.obj ((map g).op.obj U)
参数：f : X ⟶ Y；g : Y ⟶ Z；U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (map (f ≫ g)).op.obj U = (map f).op.obj ((map g).op.obj U) :=
  rfl
/-
**TopologicalSpace.Opens.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：map_iSup (f : X ⟶ Y) {ι : Type*} (U : ι -> Opens Y) : (map f).obj (iSup U)
 = iSup ((map f).obj ∘ U)
参数：f : X ⟶ Y；U : ι -> Opens Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_iSup (f : X ⟶ Y) {ι : Type*} (U : ι → Opens Y) :
    (map f).obj (iSup U) = iSup ((map f).obj ∘ U) := by
  ext
  simp

section

variable (X)

/-- The functor `Opens X ⥤ Opens X` given by taking preimages under the identity function
is naturally isomorphic to the identity functor.
-/
@[simps]
/-
**TopologicalSpace.Opens.mapId** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Opens
`。
形式化陈述：mapId : map (𝟙 X) ≅ 𝟭 (Opens X) where hom
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.map_id_obj`：map_id_obj (U : Opens X) : (map (𝟙 X)
).obj U = U

--- 原说明 ---
The functor `Opens X ⥤ Opens X` given by taking preimages under the identity fun
ction
is naturally isomorphic to the identity functor.
-/
def mapId : map (𝟙 X) ≅ 𝟭 (Opens X) where
  hom := { app := fun U => eqToHom (map_id_obj U) }
  inv := { app := fun U => eqToHom (map_id_obj U).symm }
/-
**TopologicalSpace.Opens.map_id_eq** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.O
pens`。
形式化陈述：map_id_eq : map (𝟙 X) = 𝟭 (Opens X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_id_eq : map (𝟙 X) = 𝟭 (Opens X) := by
  rfl

end

/-- The natural isomorphism between taking preimages under `f ≫ g`, and the composite
of taking preimages under `g`, then preimages under `f`.
-/
@[simps]
/-
**TopologicalSpace.Opens.mapComp** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：mapComp (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f where hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.map_comp_obj`：map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z
) (U) : (map (f ≫ g)).obj U = (map f).obj ((map g).obj U)

--- 原说明 ---
The natural isomorphism between taking preimages under `f ≫ g`, and the composit
e
of taking preimages under `g`, then preimages under `f`.
-/
def mapComp (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f where
  hom := { app := fun U => eqToHom (map_comp_obj f g U) }
  inv := { app := fun U => eqToHom (map_comp_obj f g U).symm }
/-
**TopologicalSpace.Opens.map_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace
.Opens`。
形式化陈述：map_comp_eq (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map g ⋙ map f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_eq (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map g ⋙ map f :=
  rfl

-- We could make `f g` implicit here, but it's nice to be able to see when
-- they are the identity (often!)
/-- If two continuous maps `f g : X ⟶ Y` are equal,
then the functors `Opens Y ⥤ Opens X` they induce are isomorphic.
-/
/-
**TopologicalSpace.Opens.mapIso** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Open
s`。
形式化陈述：mapIso (f g : X ⟶ Y) (h : f = g) : map f ≅ map g
参数：f g : X ⟶ Y；h : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two continuous maps `f g : X ⟶ Y` are equal,
then the functors `Opens Y ⥤ Opens X` they induce are isomorphic.
-/
def mapIso (f g : X ⟶ Y) (h : f = g) : map f ≅ map g :=
  NatIso.ofComponents fun U => eqToIso (by rw [congr_arg map h])
/-
**TopologicalSpace.Opens.map_eq** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Open
s`。
形式化陈述：map_eq (f g : X ⟶ Y) (h : f = g) : map f = map g
参数：f g : X ⟶ Y；h : f = g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_eq (f g : X ⟶ Y) (h : f = g) : map f = map g := by
  subst h
  rfl

@[simp]
/-
**TopologicalSpace.Opens.mapIso_refl** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace
.Opens`。
形式化陈述：mapIso_refl (f : X ⟶ Y) (h) : mapIso f f h = Iso.refl (map _)
参数：f : X ⟶ Y；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapIso_refl (f : X ⟶ Y) (h) : mapIso f f h = Iso.refl (map _) :=
  rfl

@[simp]
/-
**TopologicalSpace.Opens.mapIso_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.Opens`。
形式化陈述：mapIso_hom_app (f g : X ⟶ Y) (h : f = g) (U : Opens Y) : (mapIso f g h).ho
m.app U = eqToHom (by rw [h])
参数：f g : X ⟶ Y；h : f = g；U : Opens Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapIso_hom_app (f g : X ⟶ Y) (h : f = g) (U : Opens Y) :
    (mapIso f g h).hom.app U = eqToHom (by rw [h]) :=
  rfl

@[simp]
/-
**TopologicalSpace.Opens.mapIso_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.Opens`。
形式化陈述：mapIso_inv_app (f g : X ⟶ Y) (h : f = g) (U : Opens Y) : (mapIso f g h).in
v.app U = eqToHom (by rw [h])
参数：f g : X ⟶ Y；h : f = g；U : Opens Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapIso_inv_app (f g : X ⟶ Y) (h : f = g) (U : Opens Y) :
    (mapIso f g h).inv.app U = eqToHom (by rw [h]) :=
  rfl

/-- A homeomorphism of spaces gives an equivalence of categories of open sets. -/
/-
**TopologicalSpace.Opens.mapMapIso** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.O
pens`。
形式化陈述：mapMapIso {X Y : TopCat.{u}} (H : X ≅ Y) : Opens Y ≌ Opens X
参数：H : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homeomorphism of spaces gives an equivalence of categories of open sets.
-/
def mapMapIso {X Y : TopCat.{u}} (H : X ≅ Y) : Opens Y ≌ Opens X :=
  (TopCat.homeoOfIso H).opensCongr.equivalence.symm

@[simp]
/-
**TopologicalSpace.Opens.mapMapIso_functor** 是 Mathlib 中的一个引理，位于命名空间 `Topologica
lSpace.Opens`。
形式化陈述：mapMapIso_functor {X Y : TopCat.{u}} (H : X ≅ Y) : (mapMapIso H).functor =
 map H.hom
参数：H : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapMapIso_functor {X Y : TopCat.{u}} (H : X ≅ Y) :
    (mapMapIso H).functor = map H.hom := rfl

@[simp]
/-
**TopologicalSpace.Opens.mapMapIso_inverse** 是 Mathlib 中的一个引理，位于命名空间 `Topologica
lSpace.Opens`。
形式化陈述：mapMapIso_inverse {X Y : TopCat.{u}} (H : X ≅ Y) : (mapMapIso H).inverse =
 map H.inv
参数：H : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapMapIso_inverse {X Y : TopCat.{u}} (H : X ≅ Y) :
    (mapMapIso H).inverse = map H.inv := rfl

@[simp]
/-
**TopologicalSpace.Opens.mapMapIso_unitIso** 是 Mathlib 中的一个引理，位于命名空间 `Topologica
lSpace.Opens`。
形式化陈述：mapMapIso_unitIso {X Y : TopCat.{u}} (H : X ≅ Y) : (mapMapIso H).unitIso =
 NatIso.ofComponents (fun U => eqToIso (by cat_disch)) (by cat_disch)
参数：H : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapMapIso_unitIso {X Y : TopCat.{u}} (H : X ≅ Y) :
    (mapMapIso H).unitIso = NatIso.ofComponents (fun U ↦ eqToIso (by cat_disch))
    (by cat_disch) := rfl

@[simp]
/-
**TopologicalSpace.Opens.mapMapIso_counitIso** 是 Mathlib 中的一个引理，位于命名空间 `Topologi
calSpace.Opens`。
形式化陈述：mapMapIso_counitIso {X Y : TopCat.{u}} (H : X ≅ Y) : (mapMapIso H).counitI
so = NatIso.ofComponents (fun U => eqToIso (by cat_disch)) (by cat_disch)
参数：H : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapMapIso_counitIso {X Y : TopCat.{u}} (H : X ≅ Y) :
    (mapMapIso H).counitIso = NatIso.ofComponents (fun U ↦ eqToIso (by cat_disch))
    (by cat_disch) := rfl

end TopologicalSpace.Opens

/-- If `f : X ⟶ Y` is a map of topological spaces and `U ⊆ V` are open subsets of `X` whose
images are open, this is the morphism `f'' U ⟶ f'' Y` in `Opens Y`. Useful for applications
to presheaves when we don't want to suppose that `f` is an open map.
-/
/-
**IsOpenMap.functorMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsOpenMap.functorMap {X Y : TopCat.{u}} {f : X ⟶ Y} {U V : Opens X} (HU : 
IsOpen (f '' U)) (HV : IsOpen (f '' V)) (le : U <= V) : (⟨_, HU⟩ : Opens Y) ⟶ ⟨_
, HV⟩
参数：HU : IsOpen (f '' U)；HV : IsOpen (f '' V)；le : U <= V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X ⟶ Y` is a map of topological spaces and `U ⊆ V` are open subsets of `X
` whose
images are open, this is the morphism `f'' U ⟶ f'' Y` in `Opens Y`. Useful for a
pplications
to presheaves when we don't want to suppose that `f` is an open map.
-/
def IsOpenMap.functorMap {X Y : TopCat.{u}} {f : X ⟶ Y} {U V : Opens X}
     (HU : IsOpen (f '' U)) (HV : IsOpen (f '' V)) (le : U ≤ V) :
     (⟨_, HU⟩ : Opens Y) ⟶ ⟨_, HV⟩ := ⟨⟨Set.image_mono le⟩⟩

/-- An open map `f : X ⟶ Y` induces a functor `Opens X ⥤ Opens Y`.
-/
@[simps obj_coe]
/-
**IsOpenMap.functor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsOpenMap.functor {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f) : Open
s X ⥤ Opens Y where obj U
参数：hf : IsOpenMap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open map `f : X ⟶ Y` induces a functor `Opens X ⥤ Opens Y`.
-/
def IsOpenMap.functor {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f) : Opens X ⥤ Opens Y where
  obj U := ⟨f '' (U : Set X), hf (U : Set X) U.2⟩
  map {U V} h := IsOpenMap.functorMap (hf _ U.2) (hf _ V.2) h.down.down

/-- An open map `f : X ⟶ Y` induces an adjunction between `Opens X` and `Opens Y`.
-/
/-
**IsOpenMap.adjunction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsOpenMap.adjunction {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f) : h
f.functor ⊣ Opens.map f where unit
参数：hf : IsOpenMap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open map `f : X ⟶ Y` induces an adjunction between `Opens X` and `Opens Y`.
-/
def IsOpenMap.adjunction {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f) :
    hf.functor ⊣ Opens.map f where
  unit := { app := fun _ => homOfLE fun x hxU => ⟨x, hxU, rfl⟩ }
  counit := { app := fun _ => homOfLE fun _ ⟨_, hfxV, hxy⟩ => hxy ▸ hfxV }
/-
**IsOpenMap.functorFullOfMono** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsOpenMap.functorFullOfMono {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap
 f) [H : Mono f] : hf.functor.Full where map_surjective i
参数：hf : IsOpenMap f。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopCat.mono_iff_injective`：mono_iff_injective {X Y : TopCat.{u}} (f : X 
⟶ Y) : Mono f ↔ Function.Injective f
-/
instance IsOpenMap.functorFullOfMono {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f)
    [H : Mono f] : hf.functor.Full where
  map_surjective i :=
    ⟨homOfLE fun x hx => by
      obtain ⟨y, hy, eq⟩ := i.le ⟨x, hx, rfl⟩
      exact (TopCat.mono_iff_injective f).mp H eq ▸ hy, rfl⟩
/-
**IsOpenMap.functor_faithful** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap ⇑(CategoryTheory.ConcreteCate
gory.hom f)), hf.functor.Faithful
参数：hf : IsOpenMap ⇑(CategoryTheory.ConcreteCategory.hom f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance IsOpenMap.functor_faithful {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f) :
    hf.functor.Faithful where

/-- An open embedding `f : X ⟶ Y` induces a functor `Opens X ⥤ Opens Y`.
We define `IsOpenEmbedding.functor` as `IsOpenEmbedding.isOpenMap.functor`, so it won't
default to `IsInducing.functor` (which is equal but not defeq).
-/
/-
**Topology.IsOpenEmbedding.functor** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.functor {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOp
enEmbedding f)
参数：hf : IsOpenEmbedding f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open embedding `f : X ⟶ Y` induces a functor `Opens X ⥤ Opens Y`.
We define `IsOpenEmbedding.functor` as `IsOpenEmbedding.isOpenMap.functor`, so i
t won't
default to `IsInducing.functor` (which is equal but not defeq).
-/
abbrev Topology.IsOpenEmbedding.functor {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenEmbedding f) :=
    hf.isOpenMap.functor
/-
**Topology.IsOpenEmbedding.functor_obj_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.functor_obj_injective {X Y : TopCat.{u}} {f : X ⟶
 Y} (hf : IsOpenEmbedding f) : Function.Injective hf.functor.obj
参数：hf : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_injective`：image_injective : Injective (image f) ↔ Injective f
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma Topology.IsOpenEmbedding.functor_obj_injective {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : IsOpenEmbedding f) : Function.Injective hf.functor.obj :=
  fun _ _ e ↦ Opens.ext (Set.image_injective.mpr hf.injective (congr_arg (↑· : Opens Y → Set Y) e))
/-
**Topology.IsOpenEmbedding.functor_obj_iInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.functor_obj_iInf {X Y : TopCat.{u}} (f : X ⟶ Y) (
hf : Topology.IsOpenEmbedding f) {ι : Type*} [Nonempty ι] [Finite ι] (g : ι -> T
opologicalSpace.Opens X) : hf.functor.obj (⨅ i, g i) = ⨅ i, hf.functor.obj (g i)
参数：f : X ⟶ Y；hf : Topology.IsOpenEmbedding f；g : ι -> TopologicalSpace.Opens X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOpenMap.coe_functor_obj`：∀ {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap 
⇑(CategoryTheory.ConcreteCategory.hom f)) (U : TopologicalSpace.Opens ↑X),   ↑(h
f.functor.obj U…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用引理 `TopologicalSpace.Opens.coe_iInf`：coe_iInf {ι : Type*} [Finite ι] (U : ι 
-> TopologicalSpace.Opens α) : (((⨅ i, U i) : Opens α) : Set α) = ⋂ i, U i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
-/
lemma Topology.IsOpenEmbedding.functor_obj_iInf {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : Topology.IsOpenEmbedding f) {ι : Type*} [Nonempty ι] [Finite ι]
    (g : ι → TopologicalSpace.Opens X) :
    hf.functor.obj (⨅ i, g i) = ⨅ i, hf.functor.obj (g i) := by
  ext : 1
  simp only [IsOpenMap.coe_functor_obj, TopologicalSpace.Opens.coe_iInf]
  rw [Set.InjOn.image_iInter_eq]
  exact hf.injective.injOn

namespace Topology.IsInducing

/-- Given an inducing map `X ⟶ Y` and some `U : Opens X`, this is the union of all open sets
whose preimage is `U`. This is right adjoint to `Opens.map`. -/
@[nolint unusedArguments]
/-
**Topology.IsInducing.functorObj** 是 Mathlib 中的一个定义，位于命名空间 `Topology.IsInducing`
。
形式化陈述：functorObj {X Y : TopCat.{u}} {f : X ⟶ Y} (_ : IsInducing f) (U : Opens X)
 : Opens Y
参数：_ : IsInducing f；U : Opens X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an inducing map `X ⟶ Y` and some `U : Opens X`, this is the union of all o
pen sets
whose preimage is `U`. This is right adjoint to `Opens.map`.
-/
def functorObj {X Y : TopCat.{u}} {f : X ⟶ Y} (_ : IsInducing f) (U : Opens X) : Opens Y :=
  sSup { s : Opens Y | (Opens.map f).obj s = U }
/-
**Topology.IsInducing.map_functorObj** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsInduc
ing`。
形式化陈述：map_functorObj {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) (U : Ope
ns X) : (Opens.map f).obj (hf.functorObj U) = U
参数：hf : IsInducing f；U : Opens X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.isOpen_iff`：isOpen_iff (hf : IsInducing f) {s : Set 
X} : IsOpen s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.Opens.mem_sSup`：mem_sSup {Us : Set (Opens α)} {x : α} :
 x in sSup Us ↔ exists u in Us, x in u
-/
lemma map_functorObj {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f)
    (U : Opens X) :
    (Opens.map f).obj (hf.functorObj U) = U := by
  apply le_antisymm
  · rintro x ⟨_, ⟨s, rfl⟩, _, ⟨rfl : _ = U, rfl⟩, hx : f x ∈ s⟩; exact hx
  · intro x hx
    obtain ⟨U, hU⟩ := U
    obtain ⟨t, ht, rfl⟩ := hf.isOpen_iff.mp hU
    exact Opens.mem_sSup.mpr ⟨⟨_, ht⟩, rfl, hx⟩
/-
**Topology.IsInducing.mem_functorObj_iff** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsI
nducing`。
形式化陈述：mem_functorObj_iff {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) (U :
 Opens X) {x : X} : f x in hf.functorObj U ↔ x in U
参数：hf : IsInducing f；U : Opens X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsInducing.map_functorObj`：map_functorObj {X Y : TopCat.{u}} {f
 : X ⟶ Y} (hf : IsInducing f) (U : Opens X) : (Opens.map f).obj (hf.functorObj U
) = U
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_functorObj_iff {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) (U : Opens X)
    {x : X} : f x ∈ hf.functorObj U ↔ x ∈ U := by
  conv_rhs => rw [← hf.map_functorObj U]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**Topology.IsInducing.le_functorObj_iff** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsIn
ducing`。
形式化陈述：le_functorObj_iff {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) {U : 
Opens X} {V : Opens Y} : V <= hf.functorObj U ↔ (Opens.map f).obj V <= U
参数：hf : IsInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.isOpen_iff`：isOpen_iff (hf : IsInducing f) {s : Set 
X} : IsOpen s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用引理 `Topology.IsInducing.mem_functorObj_iff`：mem_functorObj_iff {X Y : TopCat
.{u}} {f : X ⟶ Y} (hf : IsInducing f) (U : Opens X) {x : X} : f x in hf.functorO
bj U ↔ x in U
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.Opens.mem_sSup`：mem_sSup {Us : Set (Opens α)} {x : α} :
 x in sSup Us ↔ exists u in Us, x in u
· 使用定理 `IsOpen.union`：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s
₁ union s₂)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_right`：union_eq_right {s t : Set α} : s union t = t ↔ s sub
seteq t
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
-/
lemma le_functorObj_iff {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) {U : Opens X}
    {V : Opens Y} : V ≤ hf.functorObj U ↔ (Opens.map f).obj V ≤ U := by
  obtain ⟨U, hU⟩ := U
  obtain ⟨t, ht, rfl⟩ := hf.isOpen_iff.mp hU
  constructor
  · exact fun i x hx ↦ (hf.mem_functorObj_iff ((Opens.map f).obj ⟨t, ht⟩)).mp (i hx)
  · intro h x hx
    refine Opens.mem_sSup.mpr ⟨⟨_, V.2.union ht⟩, Opens.ext ?_, Set.mem_union_left t hx⟩
    dsimp
    rwa [Set.union_eq_right]

/-- An inducing map `f : X ⟶ Y` induces a Galois insertion between `Opens Y` and `Opens X`. -/
/-
**Topology.IsInducing.opensGI** 是 Mathlib 中的一个定义，位于命名空间 `Topology.IsInducing`。
形式化陈述：opensGI {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) : GaloisInserti
on (Opens.map f).obj hf.functorObj
参数：hf : IsInducing f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inducing map `f : X ⟶ Y` induces a Galois insertion between `Opens Y` and `Op
ens X`.
-/
def opensGI {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) :
    GaloisInsertion (Opens.map f).obj hf.functorObj :=
  ⟨_, fun _ _ ↦ hf.le_functorObj_iff.symm, fun U ↦ (hf.map_functorObj U).ge, fun _ _ ↦ rfl⟩

/-- An inducing map `f : X ⟶ Y` induces a functor `Opens X ⥤ Opens Y`. -/
@[simps]
/-
**Topology.IsInducing.functor** 是 Mathlib 中的一个定义，位于命名空间 `Topology.IsInducing`。
形式化陈述：functor {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) : Opens X ⥤ Ope
ns Y where obj
参数：hf : IsInducing f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inducing map `f : X ⟶ Y` induces a functor `Opens X ⥤ Opens Y`.
-/
def functor {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) :
    Opens X ⥤ Opens Y where
  obj := hf.functorObj
  map {U V} h := homOfLE (hf.le_functorObj_iff.mpr ((hf.map_functorObj U).trans_le h.le))

/-- An inducing map `f : X ⟶ Y` induces an adjunction between `Opens Y` and `Opens X`. -/
/-
**Topology.IsInducing.adjunction** 是 Mathlib 中的一个定义，位于命名空间 `Topology.IsInducing`
。
形式化陈述：adjunction {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) : Opens.map 
f ⊣ hf.functor
参数：hf : IsInducing f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inducing map `f : X ⟶ Y` induces an adjunction between `Opens Y` and `Opens X
`.
-/
def adjunction {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsInducing f) :
    Opens.map f ⊣ hf.functor :=
  hf.opensGI.gc.adjunction

end Topology.IsInducing

namespace TopologicalSpace.Opens

open TopologicalSpace

@[simp]
/-
**TopologicalSpace.Opens.isOpenEmbedding_obj_top** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logicalSpace.Opens`。
形式化陈述：isOpenEmbedding_obj_top {X : TopCat.{u}} (U : Opens X) : U.isOpenEmbedding
.functor.obj ⊤ = U
参数：U : Opens X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem isOpenEmbedding_obj_top {X : TopCat.{u}} (U : Opens X) :
    U.isOpenEmbedding.functor.obj ⊤ = U := by
  ext1
  exact Set.image_univ.trans Subtype.range_coe

@[simp]
/-
**TopologicalSpace.Opens.inclusion'_map_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gicalSpace.Opens`。
形式化陈述：∀ {X : TopCat} (U : TopologicalSpace.Opens ↑X), (TopologicalSpace.Opens.ma
p U.inclusion').obj U = ⊤
参数：U : TopologicalSpace.Opens ↑X；TopologicalSpace.Opens.map U.inclusion'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
-/
theorem inclusion'_map_eq_top {X : TopCat.{u}} (U : Opens X) :
    (Opens.map U.inclusion').obj U = ⊤ := by
  ext1
  exact Subtype.coe_preimage_self _

@[simp]
/-
**TopologicalSpace.Opens.adjunction_counit_app_self** 是 Mathlib 中的一个定理，位于命名空间 `T
opologicalSpace.Opens`。
形式化陈述：adjunction_counit_app_self {X : TopCat.{u}} (U : Opens X) : U.isOpenEmbedd
ing.isOpenMap.adjunction.counit.app U = eqToHom (by simp)
参数：U : Opens X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
-/
theorem adjunction_counit_app_self {X : TopCat.{u}} (U : Opens X) :
    U.isOpenEmbedding.isOpenMap.adjunction.counit.app U = eqToHom (by simp) := Subsingleton.elim _ _
/-
**TopologicalSpace.Opens.inclusion'_top_functor** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogicalSpace.Opens`。
形式化陈述：∀ (X : TopCat), ⋯.functor = TopologicalSpace.Opens.map (TopologicalSpace.O
pens.inclusionTopIso X).inv
参数：X : TopCat；TopologicalSpace.Opens.inclusionTopIso X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `trivial`：True
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem inclusion'_top_functor (X : TopCat) :
    (@Opens.isOpenEmbedding X ⊤).functor = map (inclusionTopIso X).inv := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro U
    ext x
    exact ⟨fun ⟨⟨_, _⟩, h, rfl⟩ => h, fun h => ⟨⟨x, trivial⟩, h, rfl⟩⟩
  · subsingleton
/-
**TopologicalSpace.Opens.functor_obj_map_obj** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace.Opens`。
形式化陈述：functor_obj_map_obj {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f) (U :
 Opens Y) : hf.functor.obj ((Opens.map f).obj U) = hf.functor.obj ⊤ ⊓ U
参数：hf : IsOpenMap f；U : Opens Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `trivial`：True
-/
theorem functor_obj_map_obj {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f) (U : Opens Y) :
    hf.functor.obj ((Opens.map f).obj U) = hf.functor.obj ⊤ ⊓ U := by
  ext
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, trivial, rfl⟩, hx⟩
  · rintro ⟨⟨x, -, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩
/-
**TopologicalSpace.Opens.set_range_inclusion'** 是 Mathlib 中的一个引理，位于命名空间 `Topolog
icalSpace.Opens`。
形式化陈述：set_range_inclusion' {X : TopCat.{u}} (U : Opens X) : Set.range (inclusion
' U) = (U : Set X)
参数：U : Opens X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
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
/-
**TopologicalSpace.Opens.functor_map_eq_inf** 是 Mathlib 中的一个定理，位于命名空间 `Topologic
alSpace.Opens`。
形式化陈述：functor_map_eq_inf {X : TopCat.{u}} (U V : Opens X) : U.isOpenEmbedding.fu
nctor.obj ((Opens.map U.inclusion').obj V) = V ⊓ U
参数：U V : Opens X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpenMap.coe_functor_obj`：∀ {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap 
⇑(CategoryTheory.ConcreteCategory.hom f)) (U : TopologicalSpace.Opens ↑X),   ↑(h
f.functor.obj U…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用引理 `TopologicalSpace.Opens.set_range_inclusion'`：set_range_inclusion' {X : T
opCat.{u}} (U : Opens X) : Set.range (inclusion' U) = (U : Set X)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem functor_map_eq_inf {X : TopCat.{u}} (U V : Opens X) :
    U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) = V ⊓ U := by
  ext1
  simp only [IsOpenMap.coe_functor_obj, map_coe, coe_inf,
    Set.image_preimage_eq_inter_range, set_range_inclusion' U]
/-
**TopologicalSpace.Opens.map_functor_eq'** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.Opens`。
形式化陈述：map_functor_eq' {X U : TopCat.{u}} (f : U ⟶ X) (hf : IsOpenEmbedding f) (V
) : ((Opens.map f).obj <| hf.functor.obj V) = V
参数：f : U ⟶ X；hf : IsOpenEmbedding f；V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
-/
theorem map_functor_eq' {X U : TopCat.{u}} (f : U ⟶ X) (hf : IsOpenEmbedding f) (V) :
    ((Opens.map f).obj <| hf.functor.obj V) = V :=
  Opens.ext <| Set.preimage_image_eq _ hf.injective

@[simp]
/-
**TopologicalSpace.Opens.map_functor_eq** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.Opens`。
形式化陈述：map_functor_eq {X : TopCat.{u}} {U : Opens X} (V : Opens U) : ((Opens.map 
U.inclusion').obj <| U.isOpenEmbedding.functor.obj V) = V
参数：V : Opens U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.map_functor_eq'`：map_functor_eq' {X U : TopCat.{u
}} (f : U ⟶ X) (hf : IsOpenEmbedding f) (V) : ((Opens.map f).obj <| hf.functor.o
bj V) = V
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
-/
theorem map_functor_eq {X : TopCat.{u}} {U : Opens X} (V : Opens U) :
    ((Opens.map U.inclusion').obj <| U.isOpenEmbedding.functor.obj V) = V :=
  TopologicalSpace.Opens.map_functor_eq' _ U.isOpenEmbedding V

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**TopologicalSpace.Opens.adjunction_counit_map_functor** 是 Mathlib 中的一个定理，位于命名空间
 `TopologicalSpace.Opens`。
形式化陈述：adjunction_counit_map_functor {X : TopCat.{u}} {U : Opens X} (V : Opens U)
 : U.isOpenEmbedding.isOpenMap.adjunction.counit.app (U.isOpenEmbedding.functor.
obj V) = eqToHom (by dsimp; rw [map_functor_eq V])
参数：V : Opens U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
-/
theorem adjunction_counit_map_functor {X : TopCat.{u}} {U : Opens X} (V : Opens U) :
    U.isOpenEmbedding.isOpenMap.adjunction.counit.app (U.isOpenEmbedding.functor.obj V) =
      eqToHom (by dsimp; rw [map_functor_eq V]) := by
  subsingleton

open Limits in
/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
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

