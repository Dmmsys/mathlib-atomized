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

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {f : α → β} {s : Set β}

/-- A function between topological spaces is spectral if it is continuous and the preimage of every
compact open set is compact open. -/
@[stacks 005A, stacks 08YG]
/-
**IsSpectralMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [TopologicalSpace α] → [TopologicalSpace
 β] → (α → β) → Prop
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function between topological spaces is spectral if it is continuous and the pr
eimage of every
compact open set is compact open.
-/
structure IsSpectralMap (f : α → β) : Prop extends Continuous f where
  /-- A function between topological spaces is spectral if it is continuous and the preimage of
  every compact open set is compact open. -/
  isCompact_preimage_of_isOpen ⦃s : Set β⦄ : IsOpen s → IsCompact s → IsCompact (f ⁻¹' s)
/-
**IsCompact.preimage_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.preimage_of_isOpen (hf : IsSpectralMap f) (h₀ : IsCompact s) (h₁
 : IsOpen s) : IsCompact (f ⁻¹' s)
参数：hf : IsSpectralMap f；h₀ : IsCompact s；h₁ : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSpectralMap.isCompact_preimage_of_isOpen`：∀ {α : Type u_2} {β : Type u
_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β},   IsS
pectralMap f → ∀ ⦃s : Set β⦄, Is…
-/
theorem IsCompact.preimage_of_isOpen (hf : IsSpectralMap f) (h₀ : IsCompact s) (h₁ : IsOpen s) :
    IsCompact (f ⁻¹' s) :=
  hf.isCompact_preimage_of_isOpen h₁ h₀
/-
**IsSpectralMap.continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSpectralMap.continuous {f : α -> β} (hf : IsSpectralMap f) : Continuous 
f
参数：hf : IsSpectralMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSpectralMap.toContinuous`：∀ {α : Type u_2} {β : Type u_3} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β},   IsSpectralMap f → C
ontinuous f
-/
theorem IsSpectralMap.continuous {f : α → β} (hf : IsSpectralMap f) : Continuous f :=
  hf.toContinuous
/-
**isSpectralMap_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSpectralMap_id : IsSpectralMap (@id α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem isSpectralMap_id : IsSpectralMap (@id α) :=
  ⟨continuous_id, fun _s _ => id⟩

@[stacks 005B]
/-
**IsSpectralMap.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSpectralMap.comp {f : β -> γ} {g : α -> β} (hf : IsSpectralMap f) (hg : 
IsSpectralMap g) : IsSpectralMap (f ∘ g)
参数：hf : IsSpectralMap f；hg : IsSpectralMap g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `IsSpectralMap.continuous`：IsSpectralMap.continuous {f : α -> β} (hf : Is
SpectralMap f) : Continuous f
· 使用定理 `IsCompact.preimage_of_isOpen`：IsCompact.preimage_of_isOpen (hf : IsSpect
ralMap f) (h₀ : IsCompact s) (h₁ : IsOpen s) : IsCompact (f ⁻¹' s)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
-/
theorem IsSpectralMap.comp {f : β → γ} {g : α → β} (hf : IsSpectralMap f) (hg : IsSpectralMap g) :
    IsSpectralMap (f ∘ g) :=
  ⟨hf.continuous.comp hg.continuous, fun _s hs₀ hs₁ =>
    ((hs₁.preimage_of_isOpen hf hs₀).preimage_of_isOpen hg) (hs₀.preimage hf.continuous)⟩
/-
**IsProperMap.isSpectralMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsProperMap.isSpectralMap {f : α -> β} (hf : IsProperMap f) : IsSpectralMa
p f
参数：hf : IsProperMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsProperMap.toContinuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsProperMap f → Conti
nuous f
· 使用引理 `IsProperMap.isCompact_preimage`：IsProperMap.isCompact_preimage (h : IsPr
operMap f) {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K)
-/
theorem IsProperMap.isSpectralMap {f : α → β} (hf : IsProperMap f) : IsSpectralMap f :=
  ⟨hf.toContinuous, fun _ _ ↦ hf.isCompact_preimage⟩

end Unbundled

/-- The type of spectral maps from `α` to `β`. -/
/-
**SpectralMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [TopologicalSpace α] → [TopologicalSpace
 β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of spectral maps from `α` to `β`.
-/
structure SpectralMap (α β : Type*) [TopologicalSpace α] [TopologicalSpace β] where
  /-- function between topological spaces -/
  toFun : α → β
  /-- proof that `toFun` is a spectral map -/
  spectral' : IsSpectralMap toFun

section

/-- `SpectralMapClass F α β` states that `F` is a type of spectral maps.

You should extend this class when you extend `SpectralMap`. -/
/-
**SpectralMapClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) → (α : Type u_7) → (β : Type u_8) → [TopologicalSpace α] → 
[TopologicalSpace β] → [FunLike F α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SpectralMapClass F α β` states that `F` is a type of spectral maps.

You should extend this class when you extend `SpectralMap`.
-/
class SpectralMapClass (F α β : Type*) [TopologicalSpace α] [TopologicalSpace β]
    [FunLike F α β] : Prop where
  /-- statement that `F` is a type of spectral maps -/
  map_spectral (f : F) : IsSpectralMap f

end

export SpectralMapClass (map_spectral)

attribute [simp] map_spectral

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SpectralMapClass.toContinuousMapClass [TopologicalSpace α]
    [TopologicalSpace β] [FunLike F α β] [SpectralMapClass F α β] : ContinuousMapClass F α β :=
  { ‹SpectralMapClass F α β› with map_continuous := fun f => (map_spectral f).continuous }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] [TopologicalSpace β] [FunLike F α β] [SpectralMapClass F α β] :
    CoeTC F (SpectralMap α β) :=
  ⟨fun f => ⟨_, map_spectral f⟩⟩

/-! ### Spectral maps -/


namespace SpectralMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

/-- Reinterpret a `SpectralMap` as a `ContinuousMap`. -/
/-
**SpectralMap.toContinuousMap** 是 Mathlib 中的一个定义，位于命名空间 `SpectralMap`。
形式化陈述：toContinuousMap (f : SpectralMap α β) : ContinuousMap α β
参数：f : SpectralMap α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a `SpectralMap` as a `ContinuousMap`.
-/
def toContinuousMap (f : SpectralMap α β) : ContinuousMap α β :=
  ⟨_, f.spectral'.continuous⟩
/-
**SpectralMap.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `SpectralMap`。
形式化陈述：instFunLike : FunLike (SpectralMap α β) α β where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (SpectralMap α β) α β where
  coe := SpectralMap.toFun
  coe_injective f g h := by cases f; cases g; congr
/-
**SpectralMap.** 是 Mathlib 中的一个实例，位于命名空间 `SpectralMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SpectralMapClass (SpectralMap α β) α β where
  map_spectral f := f.spectral'

@[simp]
/-
**SpectralMap.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `SpectralMap`。
形式化陈述：toFun_eq_coe {f : SpectralMap α β} : f.toFun = (f : α -> β)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {f : SpectralMap α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
/-
**SpectralMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `SpectralMap`。
形式化陈述：ext {f g : SpectralMap α β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : SpectralMap α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `SpectralMap` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**SpectralMap.copy** 是 Mathlib 中的一个定义，位于命名空间 `SpectralMap`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : TopologicalSpace α] →     
  [inst_1 : TopologicalSpace β] → (f : SpectralMap α β) → (f' : α → β) → f' = ⇑f
 → SpectralMap α β
参数：f : SpectralMap α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `SpectralMap` with a new `toFun` equal to the old one. Useful to fix d
efinitional
equalities.
-/
protected def copy (f : SpectralMap α β) (f' : α → β) (h : f' = f) : SpectralMap α β :=
  ⟨f', h.symm.subst f.spectral'⟩

@[simp]
/-
**SpectralMap.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `SpectralMap`。
形式化陈述：coe_copy (f : SpectralMap α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h)
 = f'
参数：f : SpectralMap α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : SpectralMap α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**SpectralMap.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `SpectralMap`。
形式化陈述：copy_eq (f : SpectralMap α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : SpectralMap α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : SpectralMap α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `SpectralMap`. -/
/-
**SpectralMap.id** 是 Mathlib 中的一个定义，位于命名空间 `SpectralMap`。
形式化陈述：(α : Type u_2) → [inst : TopologicalSpace α] → SpectralMap α α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isSpectralMap_id`：isSpectralMap_id : IsSpectralMap (@id α)

--- 原说明 ---
`id` as a `SpectralMap`.
-/
protected def id : SpectralMap α α :=
  ⟨id, isSpectralMap_id⟩
/-
**SpectralMap.** 是 Mathlib 中的一个实例，位于命名空间 `SpectralMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (SpectralMap α α) :=
  ⟨SpectralMap.id α⟩

@[simp, norm_cast]
/-
**SpectralMap.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `SpectralMap`。
形式化陈述：coe_id : ⇑(SpectralMap.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(SpectralMap.id α) = id :=
  rfl

variable {α}

@[simp]
/-
**SpectralMap.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `SpectralMap`。
形式化陈述：id_apply (a : α) : SpectralMap.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : SpectralMap.id α a = a :=
  rfl

/-- Composition of `SpectralMap`s as a `SpectralMap`. -/
/-
**SpectralMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `SpectralMap`。
形式化陈述：comp (f : SpectralMap β γ) (g : SpectralMap α β) : SpectralMap α γ
参数：f : SpectralMap β γ；g : SpectralMap α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `SpectralMap`s as a `SpectralMap`.
-/
def comp (f : SpectralMap β γ) (g : SpectralMap α β) : SpectralMap α γ :=
  ⟨f.toContinuousMap.comp g.toContinuousMap, f.spectral'.comp g.spectral'⟩

@[simp]
/-
**SpectralMap.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `SpectralMap`。
形式化陈述：coe_comp (f : SpectralMap β γ) (g : SpectralMap α β) : (f.comp g : α -> γ)
 = f ∘ g
参数：f : SpectralMap β γ；g : SpectralMap α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : SpectralMap β γ) (g : SpectralMap α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
/-
**SpectralMap.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `SpectralMap`。
形式化陈述：comp_apply (f : SpectralMap β γ) (g : SpectralMap α β) (a : α) : (f.comp g
) a = f (g a)
参数：f : SpectralMap β γ；g : SpectralMap α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : SpectralMap β γ) (g : SpectralMap α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
/-
**SpectralMap.coe_comp_continuousMap** 是 Mathlib 中的一个定理，位于命名空间 `SpectralMap`。
形式化陈述：coe_comp_continuousMap (f : SpectralMap β γ) (g : SpectralMap α β) : f ∘ g
 = (f : ContinuousMap β γ) ∘ (g : ContinuousMap α β)
参数：f : SpectralMap β γ；g : SpectralMap α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp_continuousMap (f : SpectralMap β γ) (g : SpectralMap α β) :
    f ∘ g = (f : ContinuousMap β γ) ∘ (g : ContinuousMap α β) :=
  rfl

@[simp]
/-
**SpectralMap.coe_comp_continuousMap'** 是 Mathlib 中的一个定理，位于命名空间 `SpectralMap`。
形式化陈述：coe_comp_continuousMap' (f : SpectralMap β γ) (g : SpectralMap α β) : (f.c
omp g : ContinuousMap α γ) = (f : ContinuousMap β γ).comp g
参数：f : SpectralMap β γ；g : SpectralMap α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SpectralMapClass.toContinuousMapClass`：∀ {F : Type u_1} {α : Type u_2} {
β : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_
2 : FunLike F α β] [Spectra…
· 使用定理 `SpectralMap.instSpectralMapClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: TopologicalSpace α] [inst_1 : TopologicalSpace β],   SpectralMapClass (Spectra
lMap α β) α β
-/
theorem coe_comp_continuousMap' (f : SpectralMap β γ) (g : SpectralMap α β) :
    (f.comp g : ContinuousMap α γ) = (f : ContinuousMap β γ).comp g :=
  rfl

@[simp]
/-
**SpectralMap.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `SpectralMap`。
形式化陈述：comp_assoc (f : SpectralMap γ δ) (g : SpectralMap β γ) (h : SpectralMap α 
β) : (f.comp g).comp h = f.comp (g.comp h)
参数：f : SpectralMap γ δ；g : SpectralMap β γ；h : SpectralMap α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : SpectralMap γ δ) (g : SpectralMap β γ) (h : SpectralMap α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**SpectralMap.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `SpectralMap`。
形式化陈述：comp_id (f : SpectralMap α β) : f.comp (SpectralMap.id α) = f
参数：f : SpectralMap α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SpectralMap.ext`：ext {f g : SpectralMap α β} (h : forall a, f a = g a) :
 f = g
-/
theorem comp_id (f : SpectralMap α β) : f.comp (SpectralMap.id α) = f :=
  ext fun _a => rfl

@[simp]
/-
**SpectralMap.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `SpectralMap`。
形式化陈述：id_comp (f : SpectralMap α β) : (SpectralMap.id β).comp f = f
参数：f : SpectralMap α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SpectralMap.ext`：ext {f g : SpectralMap α β} (h : forall a, f a = g a) :
 f = g
-/
theorem id_comp (f : SpectralMap α β) : (SpectralMap.id β).comp f = f :=
  ext fun _a => rfl

@[simp]
/-
**SpectralMap.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `SpectralMap`。
形式化陈述：cancel_right {g₁ g₂ : SpectralMap β γ} {f : SpectralMap α β} (hf : Surject
ive f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SpectralMap.ext`：ext {f g : SpectralMap α β} (h : forall a, f a = g a) :
 f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `of_eq`：of_eq {α} {a b c : α} (_ : (a : α) = c) (_ : b = c) : a = b
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem cancel_right {g₁ g₂ : SpectralMap β γ} {f : SpectralMap α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h,
   fun a => of_eq (congrFun (congrArg comp a) f)⟩

@[simp]
/-
**SpectralMap.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `SpectralMap`。
形式化陈述：cancel_left {g : SpectralMap β γ} {f₁ f₂ : SpectralMap α β} (hg : Injectiv
e g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SpectralMap.ext`：ext {f g : SpectralMap α β} (h : forall a, f a = g a) :
 f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SpectralMap.comp_apply`：comp_apply (f : SpectralMap β γ) (g : SpectralMa
p α β) (a : α) : (f.comp g) a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : SpectralMap β γ} {f₁ f₂ : SpectralMap α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end SpectralMap

