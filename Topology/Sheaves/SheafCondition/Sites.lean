/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!

# Coverings and sieves; from sheaves on sites and sheaves on spaces

In this file, we connect coverings in a topological space to sieves in the associated Grothendieck
topology, in preparation of connecting the sheaf condition on sites to the various sheaf conditions
on spaces.

We also specialize results about sheaves on sites to sheaves on spaces; we show that the inclusion
functor from a topological basis to `TopologicalSpace.Opens` is cover dense, that open maps
induce cover-preserving functors, and that open embeddings induce continuous functors.

-/

@[expose] public section


noncomputable section

open CategoryTheory TopologicalSpace Topology

universe w v u

namespace TopCat.Presheaf

variable {X : TopCat.{w}}

/--
Definition of `coveringOfPresieve` / `coveringOfPresieve` 的定义

English:
definition coveringOfPresieve
  signature: (U : Opens X) (R : Presieve U)
  body: fun f => f.1

@[simp]

中文:
定义 coveringOfPresieve
  签名: (U : Opens X) (R : Presieve U)
  定义体: fun f => f.1

@[simp]
-/
def coveringOfPresieve (U : Opens X) (R : Presieve U) : (Σ V, { f : V ⟶ U // R f }) -> Opens X :=
  fun f => f.1

@[simp]
/--
theorem `coveringOfPresieve_apply` / 定理 `coveringOfPresieve_apply`

English:
theorem coveringOfPresieve_apply
  given: (U : Opens X) (R : Presieve U) (f : Σ V, { f : V ⟶ U // R f })
  proof: rfl

中文:
定理 coveringOfPresieve_apply
  条件: (U : Opens X) (R : Presieve U) (f : Σ V, { f : V ⟶ U // R f })
  证明: rfl
-/
theorem coveringOfPresieve_apply (U : Opens X) (R : Presieve U) (f : Σ V, { f : V ⟶ U // R f }) :
    coveringOfPresieve U R f = f.1 := rfl

namespace coveringOfPresieve

variable (U : Opens X) (R : Presieve U)

/--
theorem `iSup_eq_of_mem_grothendieck` / 定理 `iSup_eq_of_mem_grothendieck`

English:
theorem iSup_eq_of_mem_grothendieck
  given: (hR : Sieve.generate R in Opens.grothendieckTopology X U)
  proof: by
  apply le_antisymm
  · refine iSup_le ?_
    intro f
    exact f.2.1.le
  intro x hxU
  rw [Opens.mem_iSup]
  obtain ⟨V, iVU, ⟨W, iVW, iWU, hiWU, -⟩, hxV⟩ := hR x hxU
  exact ⟨⟨W, ⟨iWU, hiWU⟩⟩, iVW.le hxV⟩

中文:
定理 iSup_eq_of_mem_grothendieck
  条件: (hR : 筛.generate R in Opens.grothendieckTopology X U)
  证明: by
  apply le_antisymm
  · refine iSup_le ?_
    intro f
    exact f.2.1.le
  intro x hxU
  rw [Opens.mem_iSup]
  obtain ⟨V, iVU, ⟨W, iVW, iWU, hiWU, -⟩, hxV⟩ := hR x hxU
  exact ⟨⟨W, ⟨iWU, hiWU⟩⟩, iVW.le hxV⟩

Depends on / 依赖: Opens.mem_iSup, iSup_le, iVW.le, le_antisymm, mem_iSup
-/
theorem iSup_eq_of_mem_grothendieck (hR : Sieve.generate R in Opens.grothendieckTopology X U) :
    iSup (coveringOfPresieve U R) = U := by
  apply le_antisymm
  · refine iSup_le ?_
    intro f
    exact f.2.1.le
  intro x hxU
  rw [Opens.mem_iSup]
  obtain ⟨V, iVU, ⟨W, iVW, iWU, hiWU, -⟩, hxV⟩ := hR x hxU
  exact ⟨⟨W, ⟨iWU, hiWU⟩⟩, iVW.le hxV⟩

end coveringOfPresieve

/--
Definition of `presieveOfCoveringAux` / `presieveOfCoveringAux` 的定义

English:
definition presieveOfCoveringAux
  signature: {ι : Type v} (U : ι -> Opens X) (Y : Opens X)
  body: fun V _ => exists i, V = U i

中文:
定义 presieveOfCoveringAux
  签名: {ι : 类型v} (U : ι -> Opens X) (Y : Opens X)
  定义体: fun V _ => exists i, V = U i
-/
def presieveOfCoveringAux {ι : Type v} (U : ι -> Opens X) (Y : Opens X) : Presieve Y :=
  fun V _ => exists i, V = U i

/--
Definition of `presieveOfCovering` / `presieveOfCovering` 的定义

English:
definition presieveOfCovering
  signature: {ι : Type v} (U : ι -> Opens X)
  body: presieveOfCoveringAux U (iSup U)

中文:
定义 presieveOfCovering
  签名: {ι : 类型v} (U : ι -> Opens X)
  定义体: presieveOfCoveringAux U (iSup U)

Depends on / 依赖: presieveOfCoveringAux
-/
def presieveOfCovering {ι : Type v} (U : ι -> Opens X) : Presieve (iSup U) :=
  presieveOfCoveringAux U (iSup U)

/-- Given a presieve `R` on `Y`, if we take its associated family of opens via `coveringOfPresieve`
(which may not cover `Y` if `R` is not covering), and take the presieve on `Y` associated to the
family of opens via `presieveOfCoveringAux`, then we get back the original presieve `R`. -/
@[simp]
/--
theorem `covering_presieve_eq_self` / 定理 `covering_presieve_eq_self`

English:
theorem covering_presieve_eq_self
  given: {Y : Opens X} (R : Presieve Y)
  proof: by
  funext Z
  ext f
  exact ⟨fun ⟨⟨_, f', h⟩, rfl⟩ => by rwa [Subsingleton.elim f f'], fun h => ⟨⟨Z, f, h⟩, rfl⟩⟩

中文:
定理 covering_presieve_eq_self
  条件: {Y : Opens X} (R : Presieve Y)
  证明: by
  funext Z
  ext f
  exact ⟨fun ⟨⟨_, f', h⟩, rfl⟩ => by rwa [Subsingleton.elim f f'], fun h => ⟨⟨Z, f, h⟩, rfl⟩⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem covering_presieve_eq_self {Y : Opens X} (R : Presieve Y) :
    presieveOfCoveringAux (coveringOfPresieve Y R) Y = R := by
  funext Z
  ext f
  exact ⟨fun ⟨⟨_, f', h⟩, rfl⟩ => by rwa [Subsingleton.elim f f'], fun h => ⟨⟨Z, f, h⟩, rfl⟩⟩

namespace presieveOfCovering

variable {ι : Type v} (U : ι -> Opens X)

/--
theorem `mem_grothendieckTopology` / 定理 `mem_grothendieckTopology`

English:
theorem mem_grothendieckTopology
  proof: by
  intro x hx
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  exact ⟨U i, Opens.leSupr U i, ⟨U i, 𝟙 _, Opens.leSupr U i, ⟨i, rfl⟩, Category.id_comp _⟩, hxi⟩

中文:
定理 mem_grothendieckTopology
  证明: by
  intro x hx
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  exact ⟨U i, Opens.leSupr U i, ⟨U i, 𝟙 _, Opens.leSupr U i, ⟨i, rfl⟩, Category.id_comp _⟩, hxi⟩

Depends on / 依赖: Category, Category.id_comp, Opens.leSupr, Opens.mem_iSup.mp, id_comp, leSupr, mem_iSup
-/
theorem mem_grothendieckTopology :
    Sieve.generate (presieveOfCovering U) in Opens.grothendieckTopology X (iSup U) := by
  intro x hx
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  exact ⟨U i, Opens.leSupr U i, ⟨U i, 𝟙 _, Opens.leSupr U i, ⟨i, rfl⟩, Category.id_comp _⟩, hxi⟩

/--
Definition of `homOfIndex` / `homOfIndex` 的定义

English:
definition homOfIndex
  signature: (i : ι)
  body: ⟨U i, Opens.leSupr U i, i, rfl⟩

中文:
定义 homOfIndex
  签名: (i : ι)
  定义体: ⟨U i, Opens.leSupr U i, i, rfl⟩

Depends on / 依赖: Opens.leSupr, leSupr
-/
def homOfIndex (i : ι) : Σ V, { f : V ⟶ iSup U // presieveOfCovering U f } :=
  ⟨U i, Opens.leSupr U i, i, rfl⟩

/--
Definition of `indexOfHom` / `indexOfHom` 的定义

English:
definition indexOfHom
  signature: (f : Σ V, { f : V ⟶ iSup U // presieveOfCovering U f })
  body: f.2.2.choose

中文:
定义 indexOfHom
  签名: (f : Σ V, { f : V ⟶ iSup U // presieveOfCovering U f })
  定义体: f.2.2.choose
-/
def indexOfHom (f : Σ V, { f : V ⟶ iSup U // presieveOfCovering U f }) : ι :=
  f.2.2.choose

/--
theorem `indexOfHom_spec` / 定理 `indexOfHom_spec`

English:
theorem indexOfHom_spec
  given: (f : Σ V, { f : V ⟶ iSup U // presieveOfCovering U f })
  proof: f.2.2.choose_spec

中文:
定理 indexOfHom_spec
  条件: (f : Σ V, { f : V ⟶ iSup U // presieveOfCovering U f })
  证明: f.2.2.choose_spec

Depends on / 依赖: choose_spec
-/
theorem indexOfHom_spec (f : Σ V, { f : V ⟶ iSup U // presieveOfCovering U f }) :
    f.1 = U (indexOfHom U f) :=
  f.2.2.choose_spec

end presieveOfCovering

end TopCat.Presheaf

namespace TopCat.Opens

variable {X : TopCat.{w}} {ι : Type*}

/--
theorem `coverDense_iff_isBasis` / 定理 `coverDense_iff_isBasis`

English:
theorem coverDense_iff_isBasis
  given: [Category* ι] (B : ι ⥤ Opens X)
  proof: by
  rw [Opens.isBasis_iff_nbhd]
  constructor
  · intro hd U x hx; rcases hd.1 U x hx with ⟨V, f, ⟨i, f₁, f₂, _⟩, hV⟩
    exact ⟨B.obj i, ⟨i, rfl⟩, f₁.le hV, f₂.le⟩
  intro hb; constructor; intro U x hx; rcases hb hx with ⟨_, ⟨i, rfl⟩, hx, hi⟩
  exact ⟨B.obj i, ⟨⟨hi⟩⟩, ⟨⟨i, 𝟙 _, ⟨⟨hi⟩⟩, rfl⟩⟩, hx⟩

中文:
定理 coverDense_iff_isBasis
  条件: [范畴* ι] (B : ι ⥤ Opens X)
  证明: by
  rw [Opens.isBasis_iff_nbhd]
  constructor
  · intro hd U x hx; rcases hd.1 U x hx with ⟨V, f, ⟨i, f₁, f₂, _⟩, hV⟩
    exact ⟨B.obj i, ⟨i, rfl⟩, f₁.le hV, f₂.le⟩
  intro hb; constructor; intro U x hx; rcases hb hx with ⟨_, ⟨i, rfl⟩, hx, hi⟩
  exact ⟨B.obj i, ⟨⟨hi⟩⟩, ⟨⟨i, 𝟙 _, ⟨⟨hi⟩⟩, rfl⟩⟩, hx⟩

Depends on / 依赖: B.obj, Opens.isBasis_iff_nbhd, isBasis_iff_nbhd
-/
theorem coverDense_iff_isBasis [Category* ι] (B : ι ⥤ Opens X) :
    B.IsCoverDense (Opens.grothendieckTopology X) ↔ Opens.IsBasis (Set.range B.obj) := by
  rw [Opens.isBasis_iff_nbhd]
  constructor
  · intro hd U x hx; rcases hd.1 U x hx with ⟨V, f, ⟨i, f₁, f₂, _⟩, hV⟩
    exact ⟨B.obj i, ⟨i, rfl⟩, f₁.le hV, f₂.le⟩
  intro hb; constructor; intro U x hx; rcases hb hx with ⟨_, ⟨i, rfl⟩, hx, hi⟩
  exact ⟨B.obj i, ⟨⟨hi⟩⟩, ⟨⟨i, 𝟙 _, ⟨⟨hi⟩⟩, rfl⟩⟩, hx⟩

/--
theorem `coverDense_inducedFunctor` / 定理 `coverDense_inducedFunctor`

English:
theorem coverDense_inducedFunctor
  given: {B : ι -> Opens X} (h : Opens.IsBasis (Set.range B))
  proof: (coverDense_iff_isBasis _).2 h

中文:
定理 coverDense_inducedFunctor
  条件: {B : ι -> Opens X} (h : Opens.是基 (集合.range B))
  证明: (coverDense_iff_isBasis _).2 h

Depends on / 依赖: coverDense_iff_isBasis
-/
theorem coverDense_inducedFunctor {B : ι -> Opens X} (h : Opens.IsBasis (Set.range B)) :
    (inducedFunctor B).IsCoverDense (Opens.grothendieckTopology X) :=
  (coverDense_iff_isBasis _).2 h

end TopCat.Opens

section IsOpenEmbedding

open TopCat.Presheaf Opposite

variable {C : Type u} [Category.{v} C]
variable {X Y : TopCat.{w}} {f : X ⟶ Y} {F : Y.Presheaf C}

/--
theorem `Topology.IsOpenEmbedding.compatiblePreserving` / 定理 `Topology.IsOpenEmbedding.compatiblePreserving`

English:
theorem Topology.IsOpenEmbedding.compatiblePreserving
  given: (hf : IsOpenEmbedding f)
  proof: by
  have : Mono f := (TopCat.mono_iff_injective f).mpr hf.injective
  apply compatiblePreservingOfDownwardsClosed
  intro U V i
refine ⟨(Opens.map f).obj V, eqToIso Opens.ext Set.image_preimage_eq_of_subset fun x h => ?_⟩
  obtain ⟨_, _, rfl⟩ := i.le h
  exact ⟨_, rfl⟩

中文:
定理 拓扑.是开嵌入.compatiblePreserving
  条件: (hf : 是开嵌入 f)
  证明: by
  have : Mono f := (TopCat.mono_iff_injective f).mpr hf.injective
  apply compatiblePreservingOfDownwardsClosed
  intro U V i
refine ⟨(Opens.map f).obj V, eqToIso Opens.ext Set.image_preimage_eq_of_subset fun x h => ?_⟩
  obtain ⟨_, _, rfl⟩ := i.le h
  exact ⟨_, rfl⟩

Depends on / 依赖: Opens.ext, Opens.map, Set.image_preimage_eq_of_subset, TopCat, TopCat.mono_iff_injective, compatiblePreservingOfDownwardsClosed, eqToIso, hf.injective, i.le, image_preimage_eq_of_subset, injective, mono_iff_injective
-/
theorem Topology.IsOpenEmbedding.compatiblePreserving (hf : IsOpenEmbedding f) :
    CompatiblePreserving (Opens.grothendieckTopology Y) hf.functor := by
  have : Mono f := (TopCat.mono_iff_injective f).mpr hf.injective
  apply compatiblePreservingOfDownwardsClosed
  intro U V i
refine ⟨(Opens.map f).obj V, eqToIso Opens.ext Set.image_preimage_eq_of_subset fun x h => ?_⟩
  obtain ⟨_, _, rfl⟩ := i.le h
  exact ⟨_, rfl⟩

/--
theorem `IsOpenMap.coverPreserving` / 定理 `IsOpenMap.coverPreserving`

English:
theorem IsOpenMap.coverPreserving
  given: (hf : IsOpenMap f)
  proof: by
  constructor
  rintro U S hU _ ⟨x, hx, rfl⟩
  obtain ⟨V, i, hV, hxV⟩ := hU x hx
  exact ⟨_, hf.functor.map i, ⟨_, i, 𝟙 _, hV, rfl⟩, Set.mem_image_of_mem f hxV⟩

中文:
定理 是开映射.coverPreserving
  条件: (hf : 是开映射 f)
  证明: by
  constructor
  rintro U S hU _ ⟨x, hx, rfl⟩
  obtain ⟨V, i, hV, hxV⟩ := hU x hx
  exact ⟨_, hf.functor.map i, ⟨_, i, 𝟙 _, hV, rfl⟩, Set.mem_image_of_mem f hxV⟩

Depends on / 依赖: Set.mem_image_of_mem, functor, hf.functor.map, mem_image_of_mem
-/
theorem IsOpenMap.coverPreserving (hf : IsOpenMap f) :
    CoverPreserving (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) hf.functor := by
  constructor
  rintro U S hU _ ⟨x, hx, rfl⟩
  obtain ⟨V, i, hV, hxV⟩ := hU x hx
  exact ⟨_, hf.functor.map i, ⟨_, i, 𝟙 _, hV, rfl⟩, Set.mem_image_of_mem f hxV⟩


/--
lemma `Topology.IsOpenEmbedding.functor_isContinuous` / 引理 `Topology.IsOpenEmbedding.functor_isContinuous`

English:
lemma Topology.IsOpenEmbedding.functor_isContinuous
  given: (h : IsOpenEmbedding f)
  proof: by
  apply Functor.isContinuous_of_coverPreserving
  · exact h.compatiblePreserving
  · exact h.isOpenMap.coverPreserving

中文:
引理 拓扑.是开嵌入.functor_isContinuous
  条件: (h : 是开嵌入 f)
  证明: by
  apply Functor.isContinuous_of_coverPreserving
  · exact h.compatiblePreserving
  · exact h.isOpenMap.coverPreserving

Depends on / 依赖: Functor, Functor.isContinuous_of_coverPreserving, compatiblePreserving, coverPreserving, h.compatiblePreserving, h.isOpenMap.coverPreserving, isContinuous_of_coverPreserving, isOpenMap
-/
lemma Topology.IsOpenEmbedding.functor_isContinuous (h : IsOpenEmbedding f) :
    h.functor.IsContinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) := by
  apply Functor.isContinuous_of_coverPreserving
  · exact h.compatiblePreserving
  · exact h.isOpenMap.coverPreserving

/--
theorem `TopCat.Presheaf.isSheaf_of_isOpenEmbedding` / 定理 `TopCat.Presheaf.isSheaf_of_isOpenEmbedding`

English:
theorem TopCat.Presheaf.isSheaf_of_isOpenEmbedding
  given: (h : IsOpenEmbedding f) (hF : F.IsSheaf)
  proof: by
  have := h.functor_isContinuous
  exact Functor.op_comp_isSheaf _ _ _ ⟨_, hF⟩

中文:
定理 顶元素范畴.预层.isSheaf_of_isOpenEmbedding
  条件: (h : 是开嵌入 f) (hF : F.是层)
  证明: by
  have := h.functor_isContinuous
  exact Functor.op_comp_isSheaf _ _ _ ⟨_, hF⟩

Depends on / 依赖: Functor, Functor.op_comp_isSheaf, functor_isContinuous, h.functor_isContinuous, op_comp_isSheaf
-/
theorem TopCat.Presheaf.isSheaf_of_isOpenEmbedding (h : IsOpenEmbedding f) (hF : F.IsSheaf) :
    IsSheaf (h.functor.op ⋙ F) := by
  have := h.functor_isContinuous
  exact Functor.op_comp_isSheaf _ _ _ ⟨_, hF⟩

/-- The restriction functor of a sheaf to an open subspace. -/
@[simps!]
/--
Definition of `TopologicalSpace.Opens.sheafRestrict` / `TopologicalSpace.Opens.sheafRestrict` 的定义

English:
definition TopologicalSpace.Opens.sheafRestrict
  signature: (U : Opens X)
  body: haveI H : IsOpenEmbedding (TopCat.Hom.hom (TopCat.ofHom ⟨_, continuous_subtype_val⟩)) :=
    U.isOpenEmbedding
  haveI := H.functor_isContinuous
  H.isOpenMap.functor.sheafPushforwardContinuous C _ _

中文:
定义 拓扑空间.Opens.sheafRestrict
  签名: (U : Opens X)
  定义体: haveI H : IsOpenEmbedding (TopCat.Hom.hom (TopCat.ofHom ⟨_, continuous_subtype_val⟩)) :=
    U.isOpenEmbedding
  haveI := H.functor_isContinuous
  H.isOpenMap.functor.sheafPushforwardContinuous C _ _

Depends on / 依赖: H.functor_isContinuous, H.isOpenMap.functor.sheafPushforwardContinuous, IsOpenEmbedding, TopCat, TopCat.Hom.hom, TopCat.ofHom, U.isOpenEmbedding, continuous_subtype_val, functor, functor_isContinuous, isOpenEmbedding, isOpenMap, sheafPushforwardContinuous
-/
def TopologicalSpace.Opens.sheafRestrict (U : Opens X) :
    Sheaf (Opens.grothendieckTopology X) C ⥤ Sheaf (Opens.grothendieckTopology U) C :=
  haveI H : IsOpenEmbedding (TopCat.Hom.hom (TopCat.ofHom ⟨_, continuous_subtype_val⟩)) :=
    U.isOpenEmbedding
  haveI := H.functor_isContinuous
  H.isOpenMap.functor.sheafPushforwardContinuous C _ _

variable (f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RepresentablyFlat (Opens.map f)
  body: by
  constructor
  intro U
  refine @IsCofiltered.mk _ _ ?_ ?_
  · constructor
    · intro V W
exact ⟨⟨⟨PUnit.unit⟩, V.right ⊓ W.right, homOfLE le_inf V.hom.le W.hom.le⟩,
        StructuredArrow.homMk (homOfLE inf_le_left),
        StructuredArrow.homMk (homOfLE inf_le_right), trivial⟩
    · exact fun _ _ _ _ => ⟨_, 𝟙 _, by simp [eq_iff_true_of_subsingleton]⟩
· exact ⟨StructuredArrow.mk show U ⟶ (Opens.map f).obj ⊤ from homOfLE le_top⟩

中文:
实例 :
  签名: RepresentablyFlat (Opens.map f)
  定义体: by
  constructor
  intro U
  refine @IsCofiltered.mk _ _ ?_ ?_
  · constructor
    · intro V W
exact ⟨⟨⟨PUnit.unit⟩, V.right ⊓ W.right, homOfLE le_inf V.hom.le W.hom.le⟩,
        StructuredArrow.homMk (homOfLE inf_le_left),
        StructuredArrow.homMk (homOfLE inf_le_right), trivial⟩
    · exact fun _ _ _ _ => ⟨_, 𝟙 _, by simp [eq_iff_true_of_subsingleton]⟩
· exact ⟨StructuredArrow.mk show U ⟶ (Opens.map f).obj ⊤ from homOfLE le_top⟩

Depends on / 依赖: IsCofiltered, IsCofiltered.mk, Opens.map, PUnit.unit, StructuredArrow, StructuredArrow.homMk, StructuredArrow.mk, V.hom.le, V.right, W.hom.le, W.right, eq_iff_true_of_subsingleton, homOfLE, inf_le_left, inf_le_right, le_inf, le_top
-/
instance : RepresentablyFlat (Opens.map f) := by
  constructor
  intro U
  refine @IsCofiltered.mk _ _ ?_ ?_
  · constructor
    · intro V W
exact ⟨⟨⟨PUnit.unit⟩, V.right ⊓ W.right, homOfLE le_inf V.hom.le W.hom.le⟩,
        StructuredArrow.homMk (homOfLE inf_le_left),
        StructuredArrow.homMk (homOfLE inf_le_right), trivial⟩
    · exact fun _ _ _ _ => ⟨_, 𝟙 _, by simp [eq_iff_true_of_subsingleton]⟩
· exact ⟨StructuredArrow.mk show U ⟶ (Opens.map f).obj ⊤ from homOfLE le_top⟩

/--
theorem `compatiblePreserving_opens_map` / 定理 `compatiblePreserving_opens_map`

English:
theorem compatiblePreserving_opens_map
  proof: compatiblePreservingOfFlat _ _

中文:
定理 compatiblePreserving_opens_map
  证明: compatiblePreservingOfFlat _ _

Depends on / 依赖: compatiblePreservingOfFlat
-/
theorem compatiblePreserving_opens_map :
    CompatiblePreserving (Opens.grothendieckTopology X) (Opens.map f) :=
  compatiblePreservingOfFlat _ _

/--
theorem `coverPreserving_opens_map` / 定理 `coverPreserving_opens_map`

English:
theorem coverPreserving_opens_map
  statement: CoverPreserving (Opens.grothendieckTopology Y)
  proof: by
  constructor
  intro U S hS x hx
  obtain ⟨V, i, hi, hxV⟩ := hS (f x) hx
  exact ⟨_, (Opens.map f).map i, ⟨_, _, 𝟙 _, hi, Subsingleton.elim _ _⟩, hxV⟩

中文:
定理 coverPreserving_opens_map
  结论: 余verPreserving (Opens.grothendieckTopology Y)
  证明: by
  constructor
  intro U S hS x hx
  obtain ⟨V, i, hi, hxV⟩ := hS (f x) hx
  exact ⟨_, (Opens.map f).map i, ⟨_, _, 𝟙 _, hi, Subsingleton.elim _ _⟩, hxV⟩

Depends on / 依赖: Opens.map, Subsingleton, Subsingleton.elim
-/
theorem coverPreserving_opens_map : CoverPreserving (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology X) (Opens.map f) := by
  constructor
  intro U S hS x hx
  obtain ⟨V, i, hi, hxV⟩ := hS (f x) hx
  exact ⟨_, (Opens.map f).map i, ⟨_, _, 𝟙 _, hi, Subsingleton.elim _ _⟩, hxV⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Opens.map f).IsContinuous (Opens.grothendieckTopology Y)
  body: by
  apply Functor.isContinuous_of_coverPreserving
  · exact compatiblePreserving_opens_map f
  · exact coverPreserving_opens_map f

中文:
实例 :
  签名: (Opens.map f).是连续 (Opens.grothendieckTopology Y)
  定义体: by
  apply Functor.isContinuous_of_coverPreserving
  · exact compatiblePreserving_opens_map f
  · exact coverPreserving_opens_map f

Depends on / 依赖: Functor, Functor.isContinuous_of_coverPreserving, compatiblePreserving_opens_map, coverPreserving_opens_map, isContinuous_of_coverPreserving
-/
instance : (Opens.map f).IsContinuous (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology X) := by
  apply Functor.isContinuous_of_coverPreserving
  · exact compatiblePreserving_opens_map f
  · exact coverPreserving_opens_map f

end IsOpenEmbedding

namespace TopCat.Sheaf

open TopCat Opposite

variable {C : Type u} [Category.{v} C]
variable {X : TopCat.{w}} {ι : Type*} {B : ι -> Opens X}
variable (F : X.Presheaf C) (F' : Sheaf C X)

/--
Definition of `isTerminalOfEmpty` / `isTerminalOfEmpty` 的定义

English:
definition isTerminalOfEmpty
  signature: (F : Sheaf C X)
  body: F.isTerminalOfBotCover ⊥ (fun _ h => h.elim)

中文:
定义 isTerminalOfEmpty
  签名: (F : 层 C X)
  定义体: F.isTerminalOfBotCover ⊥ (fun _ h => h.elim)

Depends on / 依赖: F.isTerminalOfBotCover, h.elim, isTerminalOfBotCover
-/
def isTerminalOfEmpty (F : Sheaf C X) : Limits.IsTerminal (F.obj.obj (op ⊥)) :=
  F.isTerminalOfBotCover ⊥ (fun _ h => h.elim)

/--
Definition of `isTerminalOfEqEmpty` / `isTerminalOfEqEmpty` 的定义

English:
definition isTerminalOfEqEmpty
  signature: (F : X.Sheaf C) {U : Opens X} (h : U = ⊥)
  body: by
  convert! F.isTerminalOfEmpty

中文:
定义 isTerminalOfEqEmpty
  签名: (F : X.层 C) {U : Opens X} (h : U = ⊥)
  定义体: by
  convert! F.isTerminalOfEmpty

Depends on / 依赖: F.isTerminalOfEmpty, convert, isTerminalOfEmpty
-/
def isTerminalOfEqEmpty (F : X.Sheaf C) {U : Opens X} (h : U = ⊥) :
    Limits.IsTerminal (F.obj.obj (op U)) := by
  convert! F.isTerminalOfEmpty

/--
Definition of `restrictHomEquivHom` / `restrictHomEquivHom` 的定义

English:
definition restrictHomEquivHom
  signature: (h : Opens.IsBasis (Set.range B))
  body: @Functor.IsCoverDense.restrictHomEquivHom _ _ _ _ _ _ _ _
    (Opens.coverDense_inducedFunctor h) _ F F'

@[simp]

中文:
定义 restrictHomEquivHom
  签名: (h : Opens.是基 (集合.range B))
  定义体: @Functor.IsCoverDense.restrictHomEquivHom _ _ _ _ _ _ _ _
    (Opens.coverDense_inducedFunctor h) _ F F'

@[simp]

Depends on / 依赖: Functor, Functor.IsCoverDense.restrictHomEquivHom, IsCoverDense, Opens.coverDense_inducedFunctor, coverDense_inducedFunctor, restrictHomEquivHom
-/
def restrictHomEquivHom (h : Opens.IsBasis (Set.range B)) :
    ((inducedFunctor B).op ⋙ F ⟶ (inducedFunctor B).op ⋙ F'.1) ≃ (F ⟶ F'.1) :=
  @Functor.IsCoverDense.restrictHomEquivHom _ _ _ _ _ _ _ _
    (Opens.coverDense_inducedFunctor h) _ F F'

@[simp]
/--
theorem `extend_hom_app` / 定理 `extend_hom_app`

English:
theorem extend_hom_app
  statement: (h : Opens.IsBasis (Set.range B))
  proof: by
  nth_rw 2 [← (restrictHomEquivHom F F' h).left_inv α]
  rfl

中文:
定理 extend_hom_app
  结论: (h : Opens.是基 (集合.range B))
  证明: by
  nth_rw 2 [← (restrictHomEquivHom F F' h).left_inv α]
  rfl

Depends on / 依赖: left_inv, nth_rw, restrictHomEquivHom
-/
theorem extend_hom_app (h : Opens.IsBasis (Set.range B))
    (α : (inducedFunctor B).op ⋙ F ⟶ (inducedFunctor B).op ⋙ F'.1) (i : ι) :
    (restrictHomEquivHom F F' h α).app (op (B i)) = α.app (op i) := by
  nth_rw 2 [← (restrictHomEquivHom F F' h).left_inv α]
  rfl

/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: (h : Opens.IsBasis (Set.range B))
  proof: by
  apply (restrictHomEquivHom F F' h).symm.injective
  ext i
  exact he i.unop

中文:
定理 hom_ext
  结论: (h : Opens.是基 (集合.range B))
  证明: by
  apply (restrictHomEquivHom F F' h).symm.injective
  ext i
  exact he i.unop

Depends on / 依赖: i.unop, injective, restrictHomEquivHom, symm.injective
-/
theorem hom_ext (h : Opens.IsBasis (Set.range B))
    {α β : F ⟶ F'.1} (he : forall i, α.app (op (B i)) = β.app (op (B i))) : α = β := by
  apply (restrictHomEquivHom F F' h).symm.injective
  ext i
  exact he i.unop

/--
theorem `isIso_iff_isIso_basis` / 定理 `isIso_iff_isIso_basis`

English:
theorem isIso_iff_isIso_basis
  statement: {F G : Sheaf C X} (h : Opens.IsBasis (Set.range B))
  proof: by
  have : (inducedFunctor B).IsCoverDense (Opens.grothendieckTopology X) :=
    Opens.coverDense_inducedFunctor h
  refine Functor.IsCoverDense.iso_of_restrict_iso (G := inducedFunctor B) _ ?_
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun _ => hi _

中文:
定理 isIso_iff_isIso_basis
  结论: {F G : 层 C X} (h : Opens.是基 (集合.range B))
  证明: by
  have : (inducedFunctor B).IsCoverDense (Opens.grothendieckTopology X) :=
    Opens.coverDense_inducedFunctor h
  refine Functor.IsCoverDense.iso_of_restrict_iso (G := inducedFunctor B) _ ?_
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun _ => hi _

Depends on / 依赖: Functor, Functor.IsCoverDense.iso_of_restrict_iso, IsCoverDense, NatTrans, NatTrans.isIso_iff_isIso_app, Opens.coverDense_inducedFunctor, Opens.grothendieckTopology, coverDense_inducedFunctor, grothendieckTopology, inducedFunctor, isIso_iff_isIso_app, iso_of_restrict_iso
-/
theorem isIso_iff_isIso_basis {F G : Sheaf C X} (h : Opens.IsBasis (Set.range B))
    {φ : F ⟶ G} (hi : forall i, IsIso (φ.hom.app (op (B i)))) :
    IsIso φ := by
  have : (inducedFunctor B).IsCoverDense (Opens.grothendieckTopology X) :=
    Opens.coverDense_inducedFunctor h
  refine Functor.IsCoverDense.iso_of_restrict_iso (G := inducedFunctor B) _ ?_
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun _ => hi _

end TopCat.Sheaf

namespace TopologicalSpace.Opens

instance {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (F : Opens X ⥤ Opens Y) (G : Opens Y ⥤ Opens Z)
    [Functor.IsContinuous F (Opens.grothendieckTopology _) (Opens.grothendieckTopology _)]
    [Functor.IsContinuous G (Opens.grothendieckTopology _) (Opens.grothendieckTopology _)] :
    Functor.IsContinuous (F ⋙ G) (Opens.grothendieckTopology _)
      (Opens.grothendieckTopology _) :=
  Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology _) _

end TopologicalSpace.Opens
