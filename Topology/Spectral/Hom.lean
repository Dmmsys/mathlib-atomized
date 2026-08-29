/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Spectral maps

This file defines spectral maps. A map is spectral when it's continuous and the preimage of a
compact open set is compact open.

## Main declarations

* `IsSpectralMap`: Predicate for a map to be spectral.
* `SpectralMap`: Bundled spectral maps.
* `SpectralMapClass`: Typeclass for a type to be a type of spectral maps.

## TODO

Once we have `SpectralSpace`, `IsSpectralMap` should move to `Mathlib/Topology/Spectral/Basic.lean`.
-/

@[expose] public section


open Function OrderDual

variable {F α β γ δ : Type*}

section Unbundled

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {f : α -> β} {s : Set β}

/-- A function between topological spaces is spectral if it is continuous and the preimage of every
compact open set is compact open. -/
@[stacks 005A, stacks 08YG]
/--
Definition of `IsSpectralMap` / `IsSpectralMap` 的定义

English:
structure IsSpectralMap
  parameters: (f : α -> β)
  extends: Continuous f
  axioms and operations (1):
    - isCompact_preimage_of_isOpen(⦃s) : Set β⦄ : IsOpen s -> IsCompact s -> IsCompact (f ⁻¹' s)

中文:
结构 是谱映射
  参数: (f : α -> β)
  继承: 连续 f
  公理与运算 (1 个):
    - isCompact_preimage_of_isOpen(⦃s) : 集合 β⦄ : 是开集 s -> 是紧集 s -> 是紧集 (f ⁻¹' s)
-/
structure IsSpectralMap (f : α -> β) : Prop extends Continuous f where
  /-- A function between topological spaces is spectral if it is continuous and the preimage of
  every compact open set is compact open. -/
  isCompact_preimage_of_isOpen ⦃s : Set β⦄ : IsOpen s -> IsCompact s -> IsCompact (f ⁻¹' s)

/--
theorem `IsCompact.preimage_of_isOpen` / 定理 `IsCompact.preimage_of_isOpen`

English:
theorem IsCompact.preimage_of_isOpen
  given: (hf : IsSpectralMap f) (h₀ : IsCompact s) (h₁ : IsOpen s)
  proof: hf.isCompact_preimage_of_isOpen h₁ h₀

中文:
定理 是紧集.preimage_of_isOpen
  条件: (hf : 是谱映射 f) (h₀ : 是紧集 s) (h₁ : 是开集 s)
  证明: hf.isCompact_preimage_of_isOpen h₁ h₀

Depends on / 依赖: hf.isCompact_preimage_of_isOpen, isCompact_preimage_of_isOpen
-/
theorem IsCompact.preimage_of_isOpen (hf : IsSpectralMap f) (h₀ : IsCompact s) (h₁ : IsOpen s) :
    IsCompact (f ⁻¹' s) :=
  hf.isCompact_preimage_of_isOpen h₁ h₀

/--
theorem `IsSpectralMap.continuous` / 定理 `IsSpectralMap.continuous`

English:
theorem IsSpectralMap.continuous
  given: {f : α -> β} (hf : IsSpectralMap f)
  statement: Continuous f
  proof: hf.toContinuous

中文:
定理 是谱映射.continuous
  条件: {f : α -> β} (hf : 是谱映射 f)
  结论: 连续 f
  证明: hf.toContinuous

Depends on / 依赖: hf.toContinuous, toContinuous
-/
theorem IsSpectralMap.continuous {f : α -> β} (hf : IsSpectralMap f) : Continuous f :=
  hf.toContinuous

/--
theorem `isSpectralMap_id` / 定理 `isSpectralMap_id`

English:
theorem isSpectralMap_id
  statement: IsSpectralMap (@id α)
  proof: ⟨continuous_id, fun _s _ => id⟩

@[stacks 005B]

中文:
定理 isSpectralMap_id
  结论: 是谱映射 (@id α)
  证明: ⟨continuous_id, fun _s _ => id⟩

@[stacks 005B]

Depends on / 依赖: continuous_id
-/
theorem isSpectralMap_id : IsSpectralMap (@id α) :=
  ⟨continuous_id, fun _s _ => id⟩

@[stacks 005B]
/--
theorem `IsSpectralMap.comp` / 定理 `IsSpectralMap.comp`

English:
theorem IsSpectralMap.comp
  given: {f : β -> γ} {g : α -> β} (hf : IsSpectralMap f) (hg : IsSpectralMap g)
  proof: ⟨hf.continuous.comp hg.continuous, fun _s hs₀ hs₁ =>
    ((hs₁.preimage_of_isOpen hf hs₀).preimage_of_isOpen hg) (hs₀.preimage hf.continuous)⟩

中文:
定理 是谱映射.comp
  条件: {f : β -> γ} {g : α -> β} (hf : 是谱映射 f) (hg : 是谱映射 g)
  证明: ⟨hf.continuous.comp hg.continuous, fun _s hs₀ hs₁ =>
    ((hs₁.preimage_of_isOpen hf hs₀).preimage_of_isOpen hg) (hs₀.preimage hf.continuous)⟩

Depends on / 依赖: continuous, hf.continuous, hf.continuous.comp, hg.continuous, preimage, preimage_of_isOpen
-/
theorem IsSpectralMap.comp {f : β -> γ} {g : α -> β} (hf : IsSpectralMap f) (hg : IsSpectralMap g) :
    IsSpectralMap (f ∘ g) :=
  ⟨hf.continuous.comp hg.continuous, fun _s hs₀ hs₁ =>
    ((hs₁.preimage_of_isOpen hf hs₀).preimage_of_isOpen hg) (hs₀.preimage hf.continuous)⟩

/--
theorem `IsProperMap.isSpectralMap` / 定理 `IsProperMap.isSpectralMap`

English:
theorem IsProperMap.isSpectralMap
  given: {f : α -> β} (hf : IsProperMap f)
  statement: IsSpectralMap f
  proof: ⟨hf.toContinuous, fun _ _ => hf.isCompact_preimage⟩

中文:
定理 是真映射.isSpectralMap
  条件: {f : α -> β} (hf : 是真映射 f)
  结论: 是谱映射 f
  证明: ⟨hf.toContinuous, fun _ _ => hf.isCompact_preimage⟩

Depends on / 依赖: hf.isCompact_preimage, hf.toContinuous, isCompact_preimage, toContinuous
-/
theorem IsProperMap.isSpectralMap {f : α -> β} (hf : IsProperMap f) : IsSpectralMap f :=
  ⟨hf.toContinuous, fun _ _ => hf.isCompact_preimage⟩

end Unbundled

/--
Definition of `SpectralMap` / `SpectralMap` 的定义

English:
structure SpectralMap
  parameters: (α β : Type*) [TopologicalSpace α] [TopologicalSpace β]
  axioms and operations (2):
    - toFun : α -> β
    - spectral' : IsSpectralMap toFun

中文:
结构 谱映射
  参数: (α β : 类型) [拓扑空间 α] [拓扑空间 β]
  公理与运算 (2 个):
    - toFun : α -> β
    - spectral' : 是谱映射 toFun
-/
structure SpectralMap (α β : Type*) [TopologicalSpace α] [TopologicalSpace β] where
  /-- function between topological spaces -/
  toFun : α -> β
  /-- proof that `toFun` is a spectral map -/
  spectral' : IsSpectralMap toFun

section

/--
Definition of `SpectralMapClass` / `SpectralMapClass` 的定义

English:
class SpectralMapClass
  parameters: (F α β : Type*) [TopologicalSpace α] [TopologicalSpace β]
  axioms and operations (1):
    - map_spectral((f : F)) : IsSpectralMap f

中文:
类 谱映射类
  参数: (F α β : 类型) [拓扑空间 α] [拓扑空间 β]
  公理与运算 (1 个):
    - map_spectral((f : F)) : 是谱映射 f
-/
class SpectralMapClass (F α β : Type*) [TopologicalSpace α] [TopologicalSpace β]
    [FunLike F α β] : Prop where
  /-- statement that `F` is a type of spectral maps -/
  map_spectral (f : F) : IsSpectralMap f

end

export SpectralMapClass (map_spectral)

attribute [simp] map_spectral

-- See note [lower instance priority]
instance (priority := 100) SpectralMapClass.toContinuousMapClass [TopologicalSpace α]
    [TopologicalSpace β] [FunLike F α β] [SpectralMapClass F α β] : ContinuousMapClass F α β :=
  { ‹SpectralMapClass F α β› with map_continuous := fun f => (map_spectral f).continuous }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [TopologicalSpace β] [FunLike F α β] [SpectralMapClass F α β] :
  body: ⟨fun f => ⟨_, map_spectral f⟩⟩

中文:
实例 [拓扑空间
  签名: α] [拓扑空间 β] [函数状 F α β] [谱映射类 F α β] :
  定义体: ⟨fun f => ⟨_, map_spectral f⟩⟩

Depends on / 依赖: map_spectral
-/
instance [TopologicalSpace α] [TopologicalSpace β] [FunLike F α β] [SpectralMapClass F α β] :
    CoeTC F (SpectralMap α β) :=
  ⟨fun f => ⟨_, map_spectral f⟩⟩

/-! ### Spectral maps -/


namespace SpectralMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

/--
Definition of `toContinuousMap` / `toContinuousMap` 的定义

English:
definition toContinuousMap
  signature: (f : SpectralMap α β)
  body: ⟨_, f.spectral'.continuous⟩

中文:
定义 toContinuousMap
  签名: (f : 谱映射 α β)
  定义体: ⟨_, f.spectral'.continuous⟩

Depends on / 依赖: continuous, f.spectral, spectral
-/
def toContinuousMap (f : SpectralMap α β) : ContinuousMap α β :=
  ⟨_, f.spectral'.continuous⟩

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (SpectralMap α β) α β where
  body: SpectralMap.toFun
  coe_injective f g h := by cases f; cases g; congr

中文:
实例 instFunLike
  签名: : 函数状 (谱映射 α β) α β where
  定义体: SpectralMap.toFun
  coe_injective f g h := by cases f; cases g; congr

Depends on / 依赖: SpectralMap, SpectralMap.toFun
-/
instance instFunLike : FunLike (SpectralMap α β) α β where
  coe := SpectralMap.toFun
  coe_injective f g h := by cases f; cases g; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SpectralMapClass (SpectralMap α β) α β
  body: f.spectral'

@[simp]

中文:
实例 :
  签名: 谱映射类 (谱映射 α β) α β
  定义体: f.spectral'

@[simp]

Depends on / 依赖: f.spectral, spectral
-/
instance : SpectralMapClass (SpectralMap α β) α β where
  map_spectral f := f.spectral'

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {f : SpectralMap α β}
  statement: f.toFun = (f : α -> β)
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe
  条件: {f : 谱映射 α β}
  结论: f.toFun = (f : α -> β)
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe {f : SpectralMap α β} : f.toFun = (f : α -> β) :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : SpectralMap α β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : 谱映射 α β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : SpectralMap α β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : SpectralMap α β) (f' : α -> β) (h : f' = f)
  body: ⟨f', h.symm.subst f.spectral'⟩

@[simp]

中文:
定义 copy
  签名: (f : 谱映射 α β) (f' : α -> β) (h : f' = f)
  定义体: ⟨f', h.symm.subst f.spectral'⟩

@[simp]
-/
protected def copy (f : SpectralMap α β) (f' : α -> β) (h : f' = f) : SpectralMap α β :=
  ⟨f', h.symm.subst f.spectral'⟩

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : SpectralMap α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : 谱映射 α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : SpectralMap α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : SpectralMap α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : 谱映射 α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : SpectralMap α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : SpectralMap α α
  body: ⟨id, isSpectralMap_id⟩

中文:
定义 id
  签名: : 谱映射 α α
  定义体: ⟨id, isSpectralMap_id⟩
-/
protected def id : SpectralMap α α :=
  ⟨id, isSpectralMap_id⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (SpectralMap α α)
  body: ⟨SpectralMap.id α⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 可居 (谱映射 α α)
  定义体: ⟨SpectralMap.id α⟩

@[simp, norm_cast]

Depends on / 依赖: SpectralMap, SpectralMap.id
-/
instance : Inhabited (SpectralMap α α) :=
  ⟨SpectralMap.id α⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(SpectralMap.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(谱映射.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(SpectralMap.id α) = id :=
  rfl

variable {α}

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: SpectralMap.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: 谱映射.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : SpectralMap.id α a = a :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : SpectralMap β γ) (g : SpectralMap α β)
  body: ⟨f.toContinuousMap.comp g.toContinuousMap, f.spectral'.comp g.spectral'⟩

@[simp]

中文:
定义 comp
  签名: (f : 谱映射 β γ) (g : 谱映射 α β)
  定义体: ⟨f.toContinuousMap.comp g.toContinuousMap, f.spectral'.comp g.spectral'⟩

@[simp]

Depends on / 依赖: f.spectral, f.toContinuousMap.comp, g.spectral, g.toContinuousMap, spectral, toContinuousMap
-/
def comp (f : SpectralMap β γ) (g : SpectralMap α β) : SpectralMap α γ :=
  ⟨f.toContinuousMap.comp g.toContinuousMap, f.spectral'.comp g.spectral'⟩

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : SpectralMap β γ) (g : SpectralMap α β)
  statement: (f.comp g : α -> γ) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : 谱映射 β γ) (g : 谱映射 α β)
  结论: (f.comp g : α -> γ) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : SpectralMap β γ) (g : SpectralMap α β) : (f.comp g : α -> γ) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : SpectralMap β γ) (g : SpectralMap α β) (a : α)
  statement: (f.comp g) a = f (g a)
  proof: rfl

中文:
定理 comp_apply
  条件: (f : 谱映射 β γ) (g : 谱映射 α β) (a : α)
  结论: (f.comp g) a = f (g a)
  证明: rfl
-/
theorem comp_apply (f : SpectralMap β γ) (g : SpectralMap α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

/--
theorem `coe_comp_continuousMap` / 定理 `coe_comp_continuousMap`

English:
theorem coe_comp_continuousMap
  given: (f : SpectralMap β γ) (g : SpectralMap α β)
  proof: rfl

@[simp]

中文:
定理 coe_comp_continuousMap
  条件: (f : 谱映射 β γ) (g : 谱映射 α β)
  证明: rfl

@[simp]
-/
theorem coe_comp_continuousMap (f : SpectralMap β γ) (g : SpectralMap α β) :
    f ∘ g = (f : ContinuousMap β γ) ∘ (g : ContinuousMap α β) :=
  rfl

@[simp]
/--
theorem `coe_comp_continuousMap'` / 定理 `coe_comp_continuousMap'`

English:
theorem coe_comp_continuousMap'
  given: (f : SpectralMap β γ) (g : SpectralMap α β)
  proof: rfl

@[simp]

中文:
定理 coe_comp_continuousMap'
  条件: (f : 谱映射 β γ) (g : 谱映射 α β)
  证明: rfl

@[simp]
-/
theorem coe_comp_continuousMap' (f : SpectralMap β γ) (g : SpectralMap α β) :
    (f.comp g : ContinuousMap α γ) = (f : ContinuousMap β γ).comp g :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : SpectralMap γ δ) (g : SpectralMap β γ) (h : SpectralMap α β)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : 谱映射 γ δ) (g : 谱映射 β γ) (h : 谱映射 α β)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : SpectralMap γ δ) (g : SpectralMap β γ) (h : SpectralMap α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : SpectralMap α β)
  statement: f.comp (SpectralMap.id α) = f
  proof: ext fun _a => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : 谱映射 α β)
  结论: f.comp (谱映射.id α) = f
  证明: ext fun _a => rfl

@[simp]
-/
theorem comp_id (f : SpectralMap α β) : f.comp (SpectralMap.id α) = f :=
  ext fun _a => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : SpectralMap α β)
  statement: (SpectralMap.id β).comp f = f
  proof: ext fun _a => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : 谱映射 α β)
  结论: (谱映射.id β).comp f = f
  证明: ext fun _a => rfl

@[simp]
-/
theorem id_comp (f : SpectralMap α β) : (SpectralMap.id β).comp f = f :=
  ext fun _a => rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : SpectralMap β γ} {f : SpectralMap α β} (hf : Surjective f)
  proof: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h,
   fun a => of_eq (congrFun (congrArg comp a) f)⟩

@[simp]

中文:
定理 cancel_right
  条件: {g₁ g₂ : 谱映射 β γ} {f : 谱映射 α β} (hf : 满射 f)
  证明: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h,
   fun a => of_eq (congrFun (congrArg comp a) f)⟩

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, hf.forall, of_eq
-/
theorem cancel_right {g₁ g₂ : SpectralMap β γ} {f : SpectralMap α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h,
   fun a => of_eq (congrFun (congrArg comp a) f)⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : SpectralMap β γ} {f₁ f₂ : SpectralMap α β} (hg : Injective g)
  proof: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: {g : 谱映射 β γ} {f₁ f₂ : 谱映射 α β} (hg : 单射 g)
  证明: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: comp_apply, congr_arg
-/
theorem cancel_left {g : SpectralMap β γ} {f₁ f₂ : SpectralMap α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end SpectralMap
