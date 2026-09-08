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


/-- A *cocompact continuous map* is a continuous function between topological spaces which
tends to the cocompact filter along the cocompact filter. Functions for which preimages of compact
sets are compact always satisfy this property, and the converse holds for cocompact continuous maps
when the codomain is Hausdorff (see `CocompactMap.tendsto_of_forall_preimage` and
`CocompactMap.isCompact_preimage`).

Cocompact maps thus generalise proper maps, with which they correspond when the codomain is
Hausdorff. -/
/-
**CocompactMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → (β : Type v) → [TopologicalSpace α] → [TopologicalSpace β] 
→ Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *cocompact continuous map* is a continuous function between topological spaces
 which
tends to the cocompact filter along the cocompact filter. Functions for which pr
eimages of compact
sets are compact always satisfy this property, and the converse holds for cocomp
act continuous maps
when the codomain is Hausdorff (see `CocompactMap.tendsto_of_forall_preimage` an
d
`CocompactMap.isCompact_preimage`).

Cocompact maps thus generalise proper maps, with which they correspond when the 
codomain is
Hausdorff.
-/
structure CocompactMap (α : Type u) (β : Type v) [TopologicalSpace α] [TopologicalSpace β] :
    Type max u v
    extends ContinuousMap α β where
  /-- The cocompact filter on `α` tends to the cocompact filter on `β` under the function -/
  cocompact_tendsto' : Tendsto toFun (cocompact α) (cocompact β)

section

/-- `CocompactMapClass F α β` states that `F` is a type of cocompact continuous maps.

You should also extend this typeclass when you extend `CocompactMap`. -/
/-
**CocompactMapClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (α : outParam (Type u_2)) →     (β : outParam (Type u_3
)) → [TopologicalSpace α] → [TopologicalSpace β] → [FunLike F α β] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CocompactMapClass F α β` states that `F` is a type of cocompact continuous maps
.

You should also extend this typeclass when you extend `CocompactMap`.
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
/-
**CocompactMapClass.toCocompactMap** 是 Mathlib 中的一个定义，位于命名空间 `CocompactMapClass`
。
形式化陈述：toCocompactMap (f : F) : CocompactMap α β
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CocompactMapClass.toContinuousMapClass`：∀ {F : Type u_1} {α : outParam (
Type u_2)} {β : outParam (Type u_3)} {inst : TopologicalSpace α}   {inst_1 : Top
ologicalSpace β} {inst_2 : F…
· 使用定理 `CocompactMapClass.cocompact_tendsto`：∀ {F : Type u_1} {α : outParam (Typ
e u_2)} {β : outParam (Type u_3)} {inst : TopologicalSpace α}   {inst_1 : Topolo
gicalSpace β} {inst_2 : F…

--- 原说明 ---
Turn an element of a type `F` satisfying `CocompactMapClass F α β` into an actua
l
`CocompactMap`. This is declared as the default coercion from `F` to `CocompactM
ap α β`.
-/
def toCocompactMap (f : F) : CocompactMap α β :=
  { (f : C(α, β)) with
    cocompact_tendsto' := cocompact_tendsto f }
/-
**CocompactMapClass.** 是 Mathlib 中的一个实例，位于命名空间 `CocompactMapClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeTC F (CocompactMap α β) :=
  ⟨toCocompactMap⟩

end CocompactMapClass

export CocompactMapClass (cocompact_tendsto)

namespace CocompactMap

section Basics

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

/-
**CocompactMap.** 是 Mathlib 中的一个实例，位于命名空间 `CocompactMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (CocompactMap α β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
/-
**CocompactMap.** 是 Mathlib 中的一个实例，位于命名空间 `CocompactMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CocompactMapClass (CocompactMap α β) α β where
  map_continuous f := f.continuous_toFun
  cocompact_tendsto f := f.cocompact_tendsto'

@[simp]
/-
**CocompactMap.coe_toContinuousMap** 是 Mathlib 中的一个定理，位于命名空间 `CocompactMap`。
形式化陈述：coe_toContinuousMap {f : CocompactMap α β} : (f.toContinuousMap : α -> β) 
= f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousMap {f : CocompactMap α β} : (f.toContinuousMap : α → β) = f :=
  rfl

@[ext]
/-
**CocompactMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `CocompactMap`。
形式化陈述：ext {f g : CocompactMap α β} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : CocompactMap α β} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `CocompactMap` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
/-
**CocompactMap.copy** 是 Mathlib 中的一个定义，位于命名空间 `CocompactMap`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : TopologicalSpace α] →     
  [inst_1 : TopologicalSpace β] → (f : CocompactMap α β) → (f' : α → β) → f' = ⇑
f → CocompactMap α β
参数：f : CocompactMap α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `CocompactMap` with a new `toFun` equal to the old one. Useful
to fix definitional equalities.
-/
protected def copy (f : CocompactMap α β) (f' : α → β) (h : f' = f) : CocompactMap α β where
  toFun := f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  cocompact_tendsto' := by
    simp_rw [h]
    exact f.cocompact_tendsto'

@[simp]
/-
**CocompactMap.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `CocompactMap`。
形式化陈述：coe_copy (f : CocompactMap α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h
) = f'
参数：f : CocompactMap α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : CocompactMap α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**CocompactMap.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `CocompactMap`。
形式化陈述：copy_eq (f : CocompactMap α β) (f' : α -> β) (h : f' = f) : f.copy f' h = 
f
参数：f : CocompactMap α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : CocompactMap α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
/-
**CocompactMap.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `CocompactMap`。
形式化陈述：coe_mk (f : C(α, β)) (h : Tendsto f (cocompact α) (cocompact β)) : ⇑(⟨f, h
⟩ : CocompactMap α β) = f
参数：f : C(α, β)；h : Tendsto f (cocompact α) (cocompact β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : C(α, β)) (h : Tendsto f (cocompact α) (cocompact β)) :
    ⇑(⟨f, h⟩ : CocompactMap α β) = f :=
  rfl

section

variable (α)

/-- The identity as a cocompact continuous map. -/
/-
**CocompactMap.id** 是 Mathlib 中的一个定义，位于命名空间 `CocompactMap`。
形式化陈述：(α : Type u_1) → [inst : TopologicalSpace α] → CocompactMap α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity as a cocompact continuous map.
-/
protected def id : CocompactMap α α :=
  ⟨ContinuousMap.id _, tendsto_id⟩

@[simp, norm_cast]
/-
**CocompactMap.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `CocompactMap`。
形式化陈述：coe_id : ⇑(CocompactMap.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(CocompactMap.id α) = id :=
  rfl

end

/-
**CocompactMap.** 是 Mathlib 中的一个实例，位于命名空间 `CocompactMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (CocompactMap α α) :=
  ⟨CocompactMap.id α⟩

/-- The composition of cocompact continuous maps, as a cocompact continuous map. -/
/-
**CocompactMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `CocompactMap`。
形式化陈述：comp (f : CocompactMap β γ) (g : CocompactMap α β) : CocompactMap α γ
参数：f : CocompactMap β γ；g : CocompactMap α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of cocompact continuous maps, as a cocompact continuous map.
-/
def comp (f : CocompactMap β γ) (g : CocompactMap α β) : CocompactMap α γ :=
  ⟨f.toContinuousMap.comp g, (cocompact_tendsto f).comp (cocompact_tendsto g)⟩

@[simp]
/-
**CocompactMap.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `CocompactMap`。
形式化陈述：coe_comp (f : CocompactMap β γ) (g : CocompactMap α β) : ⇑(comp f g) = f ∘
 g
参数：f : CocompactMap β γ；g : CocompactMap α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : CocompactMap β γ) (g : CocompactMap α β) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
/-
**CocompactMap.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `CocompactMap`。
形式化陈述：comp_apply (f : CocompactMap β γ) (g : CocompactMap α β) (a : α) : comp f 
g a = f (g a)
参数：f : CocompactMap β γ；g : CocompactMap α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : CocompactMap β γ) (g : CocompactMap α β) (a : α) : comp f g a = f (g a) :=
  rfl

@[simp]
/-
**CocompactMap.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CocompactMap`。
形式化陈述：comp_assoc (f : CocompactMap γ δ) (g : CocompactMap β γ) (h : CocompactMap
 α β) : (f.comp g).comp h = f.comp (g.comp h)
参数：f : CocompactMap γ δ；g : CocompactMap β γ；h : CocompactMap α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : CocompactMap γ δ) (g : CocompactMap β γ) (h : CocompactMap α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**CocompactMap.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `CocompactMap`。
形式化陈述：id_comp (f : CocompactMap α β) : (CocompactMap.id _).comp f = f
参数：f : CocompactMap α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CocompactMap.ext`：ext {f g : CocompactMap α β} (h : forall x, f x = g x)
 : f = g
-/
theorem id_comp (f : CocompactMap α β) : (CocompactMap.id _).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**CocompactMap.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `CocompactMap`。
形式化陈述：comp_id (f : CocompactMap α β) : f.comp (CocompactMap.id _) = f
参数：f : CocompactMap α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CocompactMap.ext`：ext {f g : CocompactMap α β} (h : forall x, f x = g x)
 : f = g
-/
theorem comp_id (f : CocompactMap α β) : f.comp (CocompactMap.id _) = f :=
  ext fun _ => rfl
/-
**CocompactMap.tendsto_of_forall_preimage** 是 Mathlib 中的一个定理，位于命名空间 `CocompactMa
p`。
形式化陈述：tendsto_of_forall_preimage {f : α -> β} (h : forall s, IsCompact s -> IsCo
mpact (f ⁻¹' s)) : Tendsto f (cocompact α) (cocompact β)
参数：h : forall s, IsCompact s -> IsCompact (f ⁻¹' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_cocompact`：mem_cocompact : s in cocompact X ↔ exists t, IsCom
pact t ∧ tᶜ subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem tendsto_of_forall_preimage {f : α → β} (h : ∀ s, IsCompact s → IsCompact (f ⁻¹' s)) :
    Tendsto f (cocompact α) (cocompact β) := fun s hs =>
  match mem_cocompact.mp hs with
  | ⟨t, ht, hts⟩ =>
    mem_map.mpr (mem_cocompact.mpr ⟨f ⁻¹' t, h t ht, by simpa using preimage_mono hts⟩)

/-- Preimages of compact closed sets are compact under a cocompact continuous map. -/
/-
**CocompactMap.isCompact_preimage_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Cocompa
ctMap`。
形式化陈述：isCompact_preimage_of_isClosed (f : CocompactMap α β) ⦃s : Set β⦄ (hs : Is
Compact s) (h's : IsClosed s) : IsCompact (f ⁻¹' s)
参数：f : CocompactMap α β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_cocompact'`：mem_cocompact' : s in cocompact X ↔ exists t, IsC
ompact t ∧ sᶜ subseteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_image_preimage`：preimage_image_preimage {f : α -> β} {s : S
et β} : f ⁻¹' f '' f ⁻¹' s = f ⁻¹' s
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `CocompactMapClass.cocompact_tendsto`：∀ {F : Type u_1} {α : outParam (Typ
e u_2)} {β : outParam (Type u_3)} {inst : TopologicalSpace α}   {inst_1 : Topolo
gicalSpace β} {inst_2 : F…
· 使用定理 `CocompactMap.instCocompactMapClass`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace α] [inst_1 : TopologicalSpace β],   CocompactMapClass (Coco
mpactMap α β) α β
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_cocompact`：mem_cocompact : s in cocompact X ↔ exists t, IsCom
pact t ∧ tᶜ subseteq s
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `CocompactMapClass.toContinuousMapClass`：∀ {F : Type u_1} {α : outParam (
Type u_2)} {β : outParam (Type u_3)} {inst : TopologicalSpace α}   {inst_1 : Top
ologicalSpace β} {inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x

--- 原说明 ---
Preimages of compact closed sets are compact under a cocompact continuous map.
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

/-- If the codomain is Hausdorff, preimages of compact sets are compact under a cocompact
continuous map. -/
/-
**CocompactMap.isCompact_preimage** 是 Mathlib 中的一个定理，位于命名空间 `CocompactMap`。
形式化陈述：isCompact_preimage [T2Space β] (f : CocompactMap α β) ⦃s : Set β⦄ (hs : Is
Compact s) : IsCompact (f ⁻¹' s)
参数：f : CocompactMap α β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CocompactMap.isCompact_preimage_of_isClosed`：isCompact_preimage_of_isClo
sed (f : CocompactMap α β) ⦃s : Set β⦄ (hs : IsCompact s) (h's : IsClosed s) : I
sCompact (f ⁻¹' s)
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s

--- 原说明 ---
If the codomain is Hausdorff, preimages of compact sets are compact under a coco
mpact
continuous map.
-/
theorem isCompact_preimage [T2Space β] (f : CocompactMap α β) ⦃s : Set β⦄ (hs : IsCompact s) :
    IsCompact (f ⁻¹' s) :=
  isCompact_preimage_of_isClosed f hs hs.isClosed

end Basics

end CocompactMap

/-- A homeomorphism is a cocompact map. -/
@[simps]
/-
**Homeomorph.toCocompactMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Homeomorph.toCocompactMap {α β : Type*} [TopologicalSpace α] [TopologicalS
pace β] (f : α ≃ₜ β) : CocompactMap α β where toFun
参数：f : α ≃ₜ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h

--- 原说明 ---
A homeomorphism is a cocompact map.
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
