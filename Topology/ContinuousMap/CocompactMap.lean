/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Cocompact continuous maps

The type of *cocompact continuous maps* are those which tend to the cocompact filter on the
codomain along the cocompact filter on the domain. When the domain and codomain are Hausdorff, this
is equivalent to many other conditions, including that preimages of compact sets are compact. -/

@[expose] public section


universe u v w

open Filter Set

/-! ### Cocompact continuous maps -/


/--
Definition of `CocompactMap` / `CocompactMap` 的定义

English:
structure CocompactMap
  parameters: (α : Type u) (β : Type v) [TopologicalSpace α] [TopologicalSpace β]
  extends: ContinuousMap α β
  axioms and operations (1):
    - cocompact_tendsto' : Tendsto toFun (cocompact α) (cocompact β)

中文:
结构 CocompactMap
  参数: (α : 类型u) (β : 类型v) [TopologicalSpace α] [TopologicalSpace β]
  继承: ContinuousMap α β
  公理与运算 (1 个):
    - cocompact_tendsto' : Tendsto toFun (cocompact α) (cocompact β)
-/
structure CocompactMap (α : Type u) (β : Type v) [TopologicalSpace α] [TopologicalSpace β] :
    Type max u v
    extends ContinuousMap α β where
  /-- The cocompact filter on `α` tends to the cocompact filter on `β` under the function -/
  cocompact_tendsto' : Tendsto toFun (cocompact α) (cocompact β)

section

/--
Definition of `CocompactMapClass` / `CocompactMapClass` 的定义

English:
class CocompactMapClass
  parameters: (F : Type*) (α β : outParam Type*) [TopologicalSpace α]
  extends: ContinuousMapClass F α β
  axioms and operations (1):
    - cocompact_tendsto((f : F)) : Tendsto f (cocompact α) (cocompact β)

中文:
类 CocompactMapClass
  参数: (F : 类型) (α β : outParam 类型) [TopologicalSpace α]
  继承: ContinuousMapClass F α β
  公理与运算 (1 个):
    - cocompact_tendsto((f : F)) : Tendsto f (cocompact α) (cocompact β)
-/
class CocompactMapClass (F : Type*) (α β : outParam Type*) [TopologicalSpace α]
  [TopologicalSpace β] [FunLike F α β] : Prop extends ContinuousMapClass F α β where
  /-- The cocompact filter on `α` tends to the cocompact filter on `β` under the function -/
  cocompact_tendsto (f : F) : Tendsto f (cocompact α) (cocompact β)

end

namespace CocompactMapClass

variable {F α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
variable [FunLike F α β] [CocompactMapClass F α β]

/-- Turn an element of a type `F` satisfying `CocompactMapClass F α β` into an actual
`CocompactMap`. This is declared as the default coercion from `F` to `CocompactMap α β`. -/
@[coe]
/--
Definition of `toCocompactMap` / `toCocompactMap` 的定义

English:
definition toCocompactMap
  signature: (f : F)
  body: { (f : C(α, β)) with
    cocompact_tendsto' := cocompact_tendsto f }

中文:
定义 toCocompactMap
  签名: (f : F)
  定义体: { (f : C(α, β)) with
    cocompact_tendsto' := cocompact_tendsto f }

Depends on / 依赖: cocompact_tendsto
-/
def toCocompactMap (f : F) : CocompactMap α β :=
  { (f : C(α, β)) with
    cocompact_tendsto' := cocompact_tendsto f }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC F (CocompactMap α β)
  body: ⟨toCocompactMap⟩

中文:
实例 :
  签名: CoeTC F (CocompactMap α β)
  定义体: ⟨toCocompactMap⟩

Depends on / 依赖: toCocompactMap
-/
instance : CoeTC F (CocompactMap α β) :=
  ⟨toCocompactMap⟩

end CocompactMapClass

export CocompactMapClass (cocompact_tendsto)

namespace CocompactMap

section Basics

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (CocompactMap α β) α β
  body: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

中文:
实例 :
  签名: FunLike (CocompactMap α β) α β
  定义体: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

Depends on / 依赖: f.toFun
-/
instance : FunLike (CocompactMap α β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CocompactMapClass (CocompactMap α β) α β
  body: f.continuous_toFun
  cocompact_tendsto f := f.cocompact_tendsto'

@[simp]

中文:
实例 :
  签名: CocompactMapClass (CocompactMap α β) α β
  定义体: f.continuous_toFun
  cocompact_tendsto f := f.cocompact_tendsto'

@[simp]

Depends on / 依赖: continuous_toFun, f.continuous_toFun
-/
instance : CocompactMapClass (CocompactMap α β) α β where
  map_continuous f := f.continuous_toFun
  cocompact_tendsto f := f.cocompact_tendsto'

@[simp]
/--
theorem `coe_toContinuousMap` / 定理 `coe_toContinuousMap`

English:
theorem coe_toContinuousMap
  given: {f : CocompactMap α β}
  statement: (f.toContinuousMap : α -> β) = f
  proof: rfl

@[ext]

中文:
定理 coe_toContinuousMap
  条件: {f : CocompactMap α β}
  结论: (f.toContinuousMap : α -> β) = f
  证明: rfl

@[ext]
-/
theorem coe_toContinuousMap {f : CocompactMap α β} : (f.toContinuousMap : α -> β) = f :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : CocompactMap α β} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {f g : CocompactMap α β} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : CocompactMap α β} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : CocompactMap α β) (f' : α -> β) (h : f' = f)
  body: f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  cocompact_tendsto' := by
    simp_rw [h]
    exact f.cocompact_tendsto'

@[simp]

中文:
定义 copy
  签名: (f : CocompactMap α β) (f' : α -> β) (h : f' = f)
  定义体: f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  cocompact_tendsto' := by
    simp_rw [h]
    exact f.cocompact_tendsto'

@[simp]
-/
protected def copy (f : CocompactMap α β) (f' : α -> β) (h : f' = f) : CocompactMap α β where
  toFun := f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  cocompact_tendsto' := by
    simp_rw [h]
    exact f.cocompact_tendsto'

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : CocompactMap α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : CocompactMap α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : CocompactMap α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : CocompactMap α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

@[simp]

中文:
定理 copy_eq
  条件: (f : CocompactMap α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : CocompactMap α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : C(α, β)) (h : Tendsto f (cocompact α) (cocompact β))
  proof: rfl

中文:
定理 coe_mk
  条件: (f : C(α, β)) (h : Tendsto f (cocompact α) (cocompact β))
  证明: rfl
-/
theorem coe_mk (f : C(α, β)) (h : Tendsto f (cocompact α) (cocompact β)) :
    ⇑(⟨f, h⟩ : CocompactMap α β) = f :=
  rfl

section

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : CocompactMap α α
  body: ⟨ContinuousMap.id _, tendsto_id⟩

@[simp, norm_cast]

中文:
定义 id
  签名: : CocompactMap α α
  定义体: ⟨ContinuousMap.id _, tendsto_id⟩

@[simp, norm_cast]
-/
protected def id : CocompactMap α α :=
  ⟨ContinuousMap.id _, tendsto_id⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(CocompactMap.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(CocompactMap.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(CocompactMap.id α) = id :=
  rfl

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (CocompactMap α α)
  body: ⟨CocompactMap.id α⟩

中文:
实例 :
  签名: Inhabited (CocompactMap α α)
  定义体: ⟨CocompactMap.id α⟩

Depends on / 依赖: CocompactMap, CocompactMap.id
-/
instance : Inhabited (CocompactMap α α) :=
  ⟨CocompactMap.id α⟩

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : CocompactMap β γ) (g : CocompactMap α β)
  body: ⟨f.toContinuousMap.comp g, (cocompact_tendsto f).comp (cocompact_tendsto g)⟩

@[simp]

中文:
定义 comp
  签名: (f : CocompactMap β γ) (g : CocompactMap α β)
  定义体: ⟨f.toContinuousMap.comp g, (cocompact_tendsto f).comp (cocompact_tendsto g)⟩

@[simp]

Depends on / 依赖: cocompact_tendsto, f.toContinuousMap.comp, toContinuousMap
-/
def comp (f : CocompactMap β γ) (g : CocompactMap α β) : CocompactMap α γ :=
  ⟨f.toContinuousMap.comp g, (cocompact_tendsto f).comp (cocompact_tendsto g)⟩

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : CocompactMap β γ) (g : CocompactMap α β)
  statement: ⇑(comp f g) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : CocompactMap β γ) (g : CocompactMap α β)
  结论: ⇑(comp f g) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : CocompactMap β γ) (g : CocompactMap α β) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : CocompactMap β γ) (g : CocompactMap α β) (a : α)
  statement: comp f g a = f (g a)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : CocompactMap β γ) (g : CocompactMap α β) (a : α)
  结论: comp f g a = f (g a)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : CocompactMap β γ) (g : CocompactMap α β) (a : α) : comp f g a = f (g a) :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : CocompactMap γ δ) (g : CocompactMap β γ) (h : CocompactMap α β)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : CocompactMap γ δ) (g : CocompactMap β γ) (h : CocompactMap α β)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : CocompactMap γ δ) (g : CocompactMap β γ) (h : CocompactMap α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : CocompactMap α β)
  statement: (CocompactMap.id _).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : CocompactMap α β)
  结论: (CocompactMap.id _).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : CocompactMap α β) : (CocompactMap.id _).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : CocompactMap α β)
  statement: f.comp (CocompactMap.id _) = f
  proof: ext fun _ => rfl

中文:
定理 comp_id
  条件: (f : CocompactMap α β)
  结论: f.comp (CocompactMap.id _) = f
  证明: ext fun _ => rfl
-/
theorem comp_id (f : CocompactMap α β) : f.comp (CocompactMap.id _) = f :=
  ext fun _ => rfl

/--
theorem `tendsto_of_forall_preimage` / 定理 `tendsto_of_forall_preimage`

English:
theorem tendsto_of_forall_preimage
  given: {f : α -> β} (h : forall s, IsCompact s -> IsCompact (f ⁻¹' s))
  proof: fun s hs =>
  match mem_cocompact.mp hs with
  | ⟨t, ht, hts⟩ =>
    mem_map.mpr (mem_cocompact.mpr ⟨f ⁻¹' t, h t ht, by simpa using preimage_mono hts⟩)

中文:
定理 tendsto_of_forall_preimage
  条件: {f : α -> β} (h : 对任意 s, IsCompact s -> IsCompact (f ⁻¹' s))
  证明: fun s hs =>
  match mem_cocompact.mp hs with
  | ⟨t, ht, hts⟩ =>
    mem_map.mpr (mem_cocompact.mpr ⟨f ⁻¹' t, h t ht, by simpa using preimage_mono hts⟩)
-/
theorem tendsto_of_forall_preimage {f : α -> β} (h : forall s, IsCompact s -> IsCompact (f ⁻¹' s)) :
    Tendsto f (cocompact α) (cocompact β) := fun s hs =>
  match mem_cocompact.mp hs with
  | ⟨t, ht, hts⟩ =>
    mem_map.mpr (mem_cocompact.mpr ⟨f ⁻¹' t, h t ht, by simpa using preimage_mono hts⟩)

/--
theorem `isCompact_preimage_of_isClosed` / 定理 `isCompact_preimage_of_isClosed`

English:
theorem isCompact_preimage_of_isClosed
  statement: (f : CocompactMap α β)
  proof: by
  obtain ⟨t, ht, hts⟩ :=
    mem_cocompact'.mp
      (by
        simpa only [preimage_image_preimage, preimage_compl] using
          mem_map.mp
            (cocompact_tendsto f <|
              mem_cocompact.mpr ⟨s, hs, compl_subset_compl.mpr (image_preimage_subset f _)⟩))
  exact
    ht.of_isCl

中文:
定理 isCompact_preimage_of_isClosed
  结论: (f : CocompactMap α β)
  证明: by
  obtain ⟨t, ht, hts⟩ :=
    mem_cocompact'.mp
      (by
        simpa only [preimage_image_preimage, preimage_compl] using
          mem_map.mp
            (cocompact_tendsto f <|
              mem_cocompact.mpr ⟨s, hs, compl_subset_compl.mpr (image_preimage_subset f _)⟩))
  exact
    ht.of_isCl

Depends on / 依赖: cocompact_tendsto, compl_subset_compl, compl_subset_compl.mpr, ht.of_isClosed_subset, image_preimage_subset, map_continuous, mem_cocompact, mem_cocompact.mpr, mem_map, mem_map.mp, of_isClosed_subset, preimage, preimage_compl, preimage_image_preimage, s.preimage
-/
theorem isCompact_preimage_of_isClosed (f : CocompactMap α β)
    ⦃s : Set β⦄ (hs : IsCompact s) (h's : IsClosed s) :
    IsCompact (f ⁻¹' s) := by
  obtain ⟨t, ht, hts⟩ :=
    mem_cocompact'.mp
      (by
        simpa only [preimage_image_preimage, preimage_compl] using
          mem_map.mp
            (cocompact_tendsto f <|
              mem_cocompact.mpr ⟨s, hs, compl_subset_compl.mpr (image_preimage_subset f _)⟩))
  exact
    ht.of_isClosed_subset (h's.preimage <| map_continuous f) (by simpa using hts)

/--
theorem `isCompact_preimage` / 定理 `isCompact_preimage`

English:
theorem isCompact_preimage
  given: [T2Space β] (f : CocompactMap α β) ⦃s
  statement: Set β⦄ (hs : IsCompact s) :
  proof: isCompact_preimage_of_isClosed f hs hs.isClosed

中文:
定理 isCompact_preimage
  条件: [T2Space β] (f : CocompactMap α β) ⦃s
  结论: Set β⦄ (hs : IsCompact s) :
  证明: isCompact_preimage_of_isClosed f hs hs.isClosed

Depends on / 依赖: hs.isClosed, isClosed, isCompact_preimage_of_isClosed
-/
theorem isCompact_preimage [T2Space β] (f : CocompactMap α β) ⦃s : Set β⦄ (hs : IsCompact s) :
    IsCompact (f ⁻¹' s) :=
  isCompact_preimage_of_isClosed f hs hs.isClosed

end Basics

end CocompactMap

/-- A homeomorphism is a cocompact map. -/
@[simps]
/--
Definition of `Homeomorph.toCocompactMap` / `Homeomorph.toCocompactMap` 的定义

English:
definition Homeomorph.toCocompactMap
  signature: {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
  body: f
  continuous_toFun := f.continuous
  cocompact_tendsto' := by
    refine CocompactMap.tendsto_of_forall_preimage fun K hK => ?_
    have := f.toEquiv.image_symm_eq_preimage K
    simp only [coe_toEquiv] at this
    rw [← this]
    exact hK.image f.symm.continuous

中文:
定义 Homeomorph.toCocompactMap
  签名: {α β : 类型} [TopologicalSpace α] [TopologicalSpace β]
  定义体: f
  continuous_toFun := f.continuous
  cocompact_tendsto' := by
    refine CocompactMap.tendsto_of_forall_preimage fun K hK => ?_
    have := f.toEquiv.image_symm_eq_preimage K
    simp only [coe_toEquiv] at this
    rw [← this]
    exact hK.image f.symm.continuous
-/
def Homeomorph.toCocompactMap {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (f : α ≃ₜ β) : CocompactMap α β where
  toFun := f
  continuous_toFun := f.continuous
  cocompact_tendsto' := by
    refine CocompactMap.tendsto_of_forall_preimage fun K hK => ?_
    have := f.toEquiv.image_symm_eq_preimage K
    simp only [coe_toEquiv] at this
    rw [← this]
    exact hK.image f.symm.continuous
