/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Data.Set.Subsingleton

/-!
# The category of open neighborhoods of a point

Given an object `X` of the category `TopCat` of topological spaces and a point `x : X`, this file
builds the type `OpenNhds x` of open neighborhoods of `x` in `X` and endows it with the partial
order given by inclusion and the corresponding category structure (as a full subcategory of the
poset category `Set X`). This is used in `Topology.Sheaves.Stalks` to build the stalk of a sheaf
at `x` as a limit over `OpenNhds x`.

## Main declarations

Besides `OpenNhds`, the main constructions here are:

* `inclusion (x : X)`: the obvious functor `OpenNhds x ⥤ Opens X`
* `functorNhds`: An open map `f : X ⟶ Y` induces a functor `OpenNhds x ⥤ OpenNhds (f x)`
* `adjunctionNhds`: An open map `f : X ⟶ Y` induces an adjunction between `OpenNhds x` and
                    `OpenNhds (f x)`.
-/

@[expose] public section


open CategoryTheory TopologicalSpace Opposite Topology

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

namespace TopologicalSpace

/--
Definition of `OpenNhds` / `OpenNhds` 的定义

English:
definition OpenNhds
  signature: (x : X)
  body: { U : Opens X // x in U }

中文:
定义 OpenNhds
  签名: (x : X)
  定义体: { U : Opens X // x in U }
-/
def OpenNhds (x : X) : Type u := { U : Opens X // x in U }

namespace OpenNhds
variable {x : X} {U V W : OpenNhds x}

/--
Instance `partialOrder` / 实例 `partialOrder`

English:
instance partialOrder
  signature: (x : X)
  body: inferInstanceAs (PartialOrder { U : Opens X // x in U })

中文:
实例 partialOrder
  签名: (x : X)
  定义体: inferInstanceAs (PartialOrder { U : Opens X // x in U })

Depends on / 依赖: PartialOrder
-/
instance partialOrder (x : X) : PartialOrder (OpenNhds x) :=
  inferInstanceAs (PartialOrder { U : Opens X // x in U })

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: (U V : OpenNhds x)
  statement: U <= V ↔ U.1 <= V.1
  proof: Iff.rfl

中文:
定理 le_def
  条件: (U V : OpenNhds x)
  结论: U <= V ↔ U.1 <= V.1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def (U V : OpenNhds x) : U <= V ↔ U.1 <= V.1 := Iff.rfl

instance (x : X) : Lattice (OpenNhds x) :=
  { inf := fun U V => ⟨U.1 ⊓ V.1, ⟨U.2, V.2⟩⟩
    le_inf := fun U V W => @le_inf _ _ U.1.1 V.1.1 W.1.1
    inf_le_left := fun U V => @inf_le_left _ _ U.1.1 V.1.1
    inf_le_right := fun U V => @inf_le_right _ _ U.1.1 V.1.1
    sup := fun U V => ⟨U.1 ⊔ V.1, Set.mem_union_left V.1.1 U.2⟩
    sup_le := fun U V W => @sup_le _ _ U.1.1 V.1.1 W.1.1
    le_sup_left := fun U V => @le_sup_left _ _ U.1.1 V.1.1
    le_sup_right := fun U V => @le_sup_right _ _ U.1.1 V.1.1 }

set_option backward.isDefEq.respectTransparency.types false in
instance (x : X) : OrderTop (OpenNhds x) where
  top := ⟨⊤, trivial⟩
  le_top x := by
    cases x
    simp [le_def]

set_option backward.isDefEq.respectTransparency.types false in
instance (x : X) : Inhabited (OpenNhds x) :=
  ⟨⊤⟩

/--
Instance `opensNhds.instFunLike` / 实例 `opensNhds.instFunLike`

English:
instance opensNhds.instFunLike
  signature: : FunLike (U ⟶ V) U.1 V.1 where
  body: Set.inclusion f.le
  coe_injective := by rintro ⟨⟨_⟩⟩ _ _; congr!

中文:
实例 opensNhds.instFunLike
  签名: : FunLike (U ⟶ V) U.1 V.1 where
  定义体: Set.inclusion f.le
  coe_injective := by rintro ⟨⟨_⟩⟩ _ _; congr!

Depends on / 依赖: Set.inclusion, f.le, inclusion
-/
instance opensNhds.instFunLike : FunLike (U ⟶ V) U.1 V.1 where
  coe f := Set.inclusion f.le
  coe_injective := by rintro ⟨⟨_⟩⟩ _ _; congr!

/--
lemma `apply_mk` / 引理 `apply_mk`

English:
lemma apply_mk
  given: (f : U ⟶ V) (y : X) (hy)
  statement: f ⟨y, hy⟩ = ⟨y, f.le hy⟩
  proof: rfl

中文:
引理 apply_mk
  条件: (f : U ⟶ V) (y : X) (hy)
  结论: f ⟨y, hy⟩ = ⟨y, f.le hy⟩
  证明: rfl
-/
@[simp] lemma apply_mk (f : U ⟶ V) (y : X) (hy) : f ⟨y, hy⟩ = ⟨y, f.le hy⟩ := rfl

/--
lemma `val_apply` / 引理 `val_apply`

English:
lemma val_apply
  given: (f : U ⟶ V) (y : U.1)
  statement: (f y : X) = y
  proof: rfl

中文:
引理 val_apply
  条件: (f : U ⟶ V) (y : U.1)
  结论: (f y : X) = y
  证明: rfl
-/
@[simp] lemma val_apply (f : U ⟶ V) (y : U.1) : (f y : X) = y := rfl

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
  given: (f : U ⟶ U) (y : U.1)
  statement: f y = y
  proof: rfl

中文:
引理 id_apply
  条件: (f : U ⟶ U) (y : U.1)
  结论: f y = y
  证明: rfl
-/
lemma id_apply (f : U ⟶ U) (y : U.1) : f y = y := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: (f : U ⟶ V) (g : V ⟶ W) (x : U.1)
  statement: (f ≫ g) x = g (f x)
  proof: rfl

中文:
引理 comp_apply
  条件: (f : U ⟶ V) (g : V ⟶ W) (x : U.1)
  结论: (f ≫ g) x = g (f x)
  证明: rfl
-/
@[simp] lemma comp_apply (f : U ⟶ V) (g : V ⟶ W) (x : U.1) : (f ≫ g) x = g (f x) := rfl

/--
Definition of `infLELeft` / `infLELeft` 的定义

English:
definition infLELeft
  signature: {x : X} (U V : OpenNhds x)
  body: homOfLE inf_le_left

中文:
定义 infLELeft
  签名: {x : X} (U V : OpenNhds x)
  定义体: homOfLE inf_le_left

Depends on / 依赖: homOfLE, inf_le_left
-/
def infLELeft {x : X} (U V : OpenNhds x) : U ⊓ V ⟶ U :=
  homOfLE inf_le_left

/--
Definition of `infLERight` / `infLERight` 的定义

English:
definition infLERight
  signature: {x : X} (U V : OpenNhds x)
  body: homOfLE inf_le_right

中文:
定义 infLERight
  签名: {x : X} (U V : OpenNhds x)
  定义体: homOfLE inf_le_right

Depends on / 依赖: homOfLE, inf_le_right
-/
def infLERight {x : X} (U V : OpenNhds x) : U ⊓ V ⟶ V :=
  homOfLE inf_le_right

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: (x : X)
  body: (Subtype.mono_coe _).functor

@[simp]

中文:
定义 inclusion
  签名: (x : X)
  定义体: (Subtype.mono_coe _).functor

@[simp]

Depends on / 依赖: Subtype, Subtype.mono_coe, functor, mono_coe
-/
def inclusion (x : X) : OpenNhds x ⥤ Opens X :=
  (Subtype.mono_coe _).functor

@[simp]
/--
theorem `inclusion_obj` / 定理 `inclusion_obj`

English:
theorem inclusion_obj
  given: (x : X) (U) (p)
  statement: (inclusion x).obj ⟨U, p⟩ = U
  proof: rfl

中文:
定理 inclusion_obj
  条件: (x : X) (U) (p)
  结论: (inclusion x).obj ⟨U, p⟩ = U
  证明: rfl
-/
theorem inclusion_obj (x : X) (U) (p) : (inclusion x).obj ⟨U, p⟩ = U :=
  rfl

/--
theorem `isOpenEmbedding` / 定理 `isOpenEmbedding`

English:
theorem isOpenEmbedding
  given: {x : X} (U : OpenNhds x)
  statement: IsOpenEmbedding U.1.inclusion'
  proof: U.1.isOpenEmbedding

中文:
定理 isOpenEmbedding
  条件: {x : X} (U : OpenNhds x)
  结论: IsOpenEmbedding U.1.inclusion'
  证明: U.1.isOpenEmbedding

Depends on / 依赖: isOpenEmbedding
-/
theorem isOpenEmbedding {x : X} (U : OpenNhds x) : IsOpenEmbedding U.1.inclusion' :=
  U.1.isOpenEmbedding

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (x : X)
  body: ⟨(Opens.map f).obj U.1, U.2⟩
  map i := (Opens.map f).map i

@[simp]

中文:
定义 map
  签名: (x : X)
  定义体: ⟨(Opens.map f).obj U.1, U.2⟩
  map i := (Opens.map f).map i

@[simp]

Depends on / 依赖: Opens.map
-/
def map (x : X) : OpenNhds (f x) ⥤ OpenNhds x where
  obj U := ⟨(Opens.map f).obj U.1, U.2⟩
  map i := (Opens.map f).map i

@[simp]
/--
theorem `map_obj` / 定理 `map_obj`

English:
theorem map_obj
  given: (x : X) (U) (q)
  statement: (map f x).obj ⟨U, q⟩ = ⟨(Opens.map f).obj U, q⟩
  proof: rfl

@[simp]

中文:
定理 map_obj
  条件: (x : X) (U) (q)
  结论: (map f x).obj ⟨U, q⟩ = ⟨(Opens.map f).obj U, q⟩
  证明: rfl

@[simp]
-/
theorem map_obj (x : X) (U) (q) : (map f x).obj ⟨U, q⟩ = ⟨(Opens.map f).obj U, q⟩ :=
  rfl

@[simp]
/--
theorem `map_id_obj` / 定理 `map_id_obj`

English:
theorem map_id_obj
  given: (x : X) (U)
  statement: (map (𝟙 X) x).obj U = U
  proof: rfl

@[simp]

中文:
定理 map_id_obj
  条件: (x : X) (U)
  结论: (map (𝟙 X) x).obj U = U
  证明: rfl

@[simp]
-/
theorem map_id_obj (x : X) (U) : (map (𝟙 X) x).obj U = U := rfl

@[simp]
/--
theorem `map_id_obj'` / 定理 `map_id_obj'`

English:
theorem map_id_obj'
  given: (x : X) (U) (p) (q)
  statement: (map (𝟙 X) x).obj ⟨⟨U, p⟩, q⟩ = ⟨⟨U, p⟩, q⟩
  proof: rfl

中文:
定理 map_id_obj'
  条件: (x : X) (U) (p) (q)
  结论: (map (𝟙 X) x).obj ⟨⟨U, p⟩, q⟩ = ⟨⟨U, p⟩, q⟩
  证明: rfl
-/
theorem map_id_obj' (x : X) (U) (p) (q) : (map (𝟙 X) x).obj ⟨⟨U, p⟩, q⟩ = ⟨⟨U, p⟩, q⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `map_id_obj_unop` / 定理 `map_id_obj_unop`

English:
theorem map_id_obj_unop
  given: (x : X) (U : (OpenNhds x)ᵒᵖ)
  statement: (map (𝟙 X) x).obj (unop U) = unop U
  proof: by
  simp

中文:
定理 map_id_obj_unop
  条件: (x : X) (U : (OpenNhds x)ᵒᵖ)
  结论: (map (𝟙 X) x).obj (unop U) = unop U
  证明: by
  simp
-/
theorem map_id_obj_unop (x : X) (U : (OpenNhds x)ᵒᵖ) : (map (𝟙 X) x).obj (unop U) = unop U := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `op_map_id_obj` / 定理 `op_map_id_obj`

English:
theorem op_map_id_obj
  given: (x : X) (U : (OpenNhds x)ᵒᵖ)
  statement: (map (𝟙 X) x).op.obj U = U
  proof: by simp

中文:
定理 op_map_id_obj
  条件: (x : X) (U : (OpenNhds x)ᵒᵖ)
  结论: (map (𝟙 X) x).op.obj U = U
  证明: by simp
-/
theorem op_map_id_obj (x : X) (U : (OpenNhds x)ᵒᵖ) : (map (𝟙 X) x).op.obj U = U := by simp

/--
Definition of `inclusionMapIso` / `inclusionMapIso` 的定义

English:
definition inclusionMapIso
  signature: (x : X)
  body: NatIso.ofComponents fun U => { hom := 𝟙 _, inv := 𝟙 _ }

@[simp]

中文:
定义 inclusionMapIso
  签名: (x : X)
  定义体: NatIso.ofComponents fun U => { hom := 𝟙 _, inv := 𝟙 _ }

@[simp]

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def inclusionMapIso (x : X) : inclusion (f x) ⋙ Opens.map f ≅ map f x ⋙ inclusion x :=
  NatIso.ofComponents fun U => { hom := 𝟙 _, inv := 𝟙 _ }

@[simp]
/--
theorem `inclusionMapIso_hom` / 定理 `inclusionMapIso_hom`

English:
theorem inclusionMapIso_hom
  given: (x : X)
  statement: (inclusionMapIso f x).hom = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 inclusionMapIso_hom
  条件: (x : X)
  结论: (inclusionMapIso f x).hom = 𝟙 _
  证明: rfl

@[simp]
-/
theorem inclusionMapIso_hom (x : X) : (inclusionMapIso f x).hom = 𝟙 _ :=
  rfl

@[simp]
/--
theorem `inclusionMapIso_inv` / 定理 `inclusionMapIso_inv`

English:
theorem inclusionMapIso_inv
  given: (x : X)
  statement: (inclusionMapIso f x).inv = 𝟙 _
  proof: rfl

中文:
定理 inclusionMapIso_inv
  条件: (x : X)
  结论: (inclusionMapIso f x).inv = 𝟙 _
  证明: rfl
-/
theorem inclusionMapIso_inv (x : X) : (inclusionMapIso f x).inv = 𝟙 _ :=
  rfl

end OpenNhds

end TopologicalSpace

namespace IsOpenMap

open TopologicalSpace

variable {f}

/-- An open map `f : X ⟶ Y` induces a functor `OpenNhds x ⥤ OpenNhds (f x)`. -/
@[simps]
/--
Definition of `functorNhds` / `functorNhds` 的定义

English:
definition functorNhds
  signature: (h : IsOpenMap f) (x : X)
  body: ⟨h.functor.obj U.1, ⟨x, U.2, rfl⟩⟩
  map i := h.functor.map i

中文:
定义 functorNhds
  签名: (h : IsOpenMap f) (x : X)
  定义体: ⟨h.functor.obj U.1, ⟨x, U.2, rfl⟩⟩
  map i := h.functor.map i

Depends on / 依赖: functor, h.functor.obj
-/
def functorNhds (h : IsOpenMap f) (x : X) : OpenNhds x ⥤ OpenNhds (f x) where
  obj U := ⟨h.functor.obj U.1, ⟨x, U.2, rfl⟩⟩
  map i := h.functor.map i

/--
Definition of `adjunctionNhds` / `adjunctionNhds` 的定义

English:
definition adjunctionNhds
  signature: (h : IsOpenMap f) (x : X)
  body: { app := fun _ => homOfLE fun x hxU => ⟨x, hxU, rfl⟩ }
  counit := { app := fun _ => homOfLE fun _ ⟨_, hfxV, hxy⟩ => hxy ▸ hfxV }

中文:
定义 adjunctionNhds
  签名: (h : IsOpenMap f) (x : X)
  定义体: { app := fun _ => homOfLE fun x hxU => ⟨x, hxU, rfl⟩ }
  counit := { app := fun _ => homOfLE fun _ ⟨_, hfxV, hxy⟩ => hxy ▸ hfxV }

Depends on / 依赖: homOfLE
-/
def adjunctionNhds (h : IsOpenMap f) (x : X) : IsOpenMap.functorNhds h x ⊣ OpenNhds.map f x where
  unit := { app := fun _ => homOfLE fun x hxU => ⟨x, hxU, rfl⟩ }
  counit := { app := fun _ => homOfLE fun _ ⟨_, hfxV, hxy⟩ => hxy ▸ hfxV }

end IsOpenMap

section

variable {f}

/--
Definition of `Topology.IsOpenEmbedding.functorNhds` / `Topology.IsOpenEmbedding.functorNhds` 的定义

English:
abbreviation Topology.IsOpenEmbedding.functorNhds
  signature: (h : Topology.IsOpenEmbedding f) (x : X)
  body: h.isOpenMap.functorNhds x

中文:
缩写 Topology.IsOpenEmbedding.functorNhds
  签名: (h : Topology.IsOpenEmbedding f) (x : X)
  定义体: h.isOpenMap.functorNhds x

Depends on / 依赖: functorNhds, h.isOpenMap.functorNhds, isOpenMap
-/
abbrev Topology.IsOpenEmbedding.functorNhds (h : Topology.IsOpenEmbedding f) (x : X) :=
    h.isOpenMap.functorNhds x

/--
Definition of `Topology.IsOpenEmbedding.adjunctionNhds` / `Topology.IsOpenEmbedding.adjunctionNhds` 的定义

English:
abbreviation Topology.IsOpenEmbedding.adjunctionNhds
  signature: (h : Topology.IsOpenEmbedding f) (x : X)
  body: h.isOpenMap.adjunctionNhds x

中文:
缩写 Topology.IsOpenEmbedding.adjunctionNhds
  签名: (h : Topology.IsOpenEmbedding f) (x : X)
  定义体: h.isOpenMap.adjunctionNhds x

Depends on / 依赖: adjunctionNhds, h.isOpenMap.adjunctionNhds, isOpenMap
-/
abbrev Topology.IsOpenEmbedding.adjunctionNhds (h : Topology.IsOpenEmbedding f) (x : X) :=
  h.isOpenMap.adjunctionNhds x

end

namespace Topology.IsInducing

open TopologicalSpace

variable {f}

/-- An inducing map `f : X ⟶ Y` induces a functor `OpenNhds x ⥤ OpenNhds (f x)`. -/
@[simps]
/--
Definition of `functorNhds` / `functorNhds` 的定义

English:
definition functorNhds
  signature: (h : IsInducing f) (x : X)
  body: ⟨h.functor.obj U.1, (h.mem_functorObj_iff U.1).mpr U.2⟩
  map := h.functor.map

中文:
定义 functorNhds
  签名: (h : IsInducing f) (x : X)
  定义体: ⟨h.functor.obj U.1, (h.mem_functorObj_iff U.1).mpr U.2⟩
  map := h.functor.map

Depends on / 依赖: functor, h.functor.obj, h.mem_functorObj_iff, mem_functorObj_iff
-/
def functorNhds (h : IsInducing f) (x : X) :
    OpenNhds x ⥤ OpenNhds (f x) where
  obj U := ⟨h.functor.obj U.1, (h.mem_functorObj_iff U.1).mpr U.2⟩
  map := h.functor.map

/--
Definition of `adjunctionNhds` / `adjunctionNhds` 的定义

English:
definition adjunctionNhds
  signature: (h : IsInducing f) (x : X)
  body: { app := fun U => homOfLE (h.adjunction.unit.app U.1).le }
  counit := { app := fun U => homOfLE (h.adjunction.counit.app U.1).le }

中文:
定义 adjunctionNhds
  签名: (h : IsInducing f) (x : X)
  定义体: { app := fun U => homOfLE (h.adjunction.unit.app U.1).le }
  counit := { app := fun U => homOfLE (h.adjunction.counit.app U.1).le }

Depends on / 依赖: adjunction, h.adjunction.unit.app, homOfLE
-/
def adjunctionNhds (h : IsInducing f) (x : X) :
    OpenNhds.map f x ⊣ h.functorNhds x where
  unit := { app := fun U => homOfLE (h.adjunction.unit.app U.1).le }
  counit := { app := fun U => homOfLE (h.adjunction.counit.app U.1).le }

end Topology.IsInducing
