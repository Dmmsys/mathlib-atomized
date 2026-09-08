/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.PartialHomeomorph.Basic
/-!
# Partial homeomorphisms: basic theory


## Main definitions

* `OpenPartialHomeomorph.refl`: the identity open partial homeomorphism
* `Topology.IsOpenEmbedding.toOpenPartialHomeomorph`: construct an open partial homeomorphism from
  an open embedding
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace OpenPartialHomeomorph

/-- The identity on the whole space as an open partial homeomorphism. -/
@[simps! (attr := mfld_simps) -fullyApplied apply, simps! -isSimp source target]
/-
**OpenPartialHomeomorph.refl** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：(X : Type u_7) → [inst : TopologicalSpace X] → OpenPartialHomeomorph X X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity on the whole space as an open partial homeomorphism.
-/
protected def refl (X : Type*) [TopologicalSpace X] : OpenPartialHomeomorph X X :=
  (Homeomorph.refl X).toOpenPartialHomeomorph

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.refl_partialEquiv** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartial
Homeomorph`。
形式化陈述：refl_partialEquiv : (OpenPartialHomeomorph.refl X).toPartialEquiv = Partia
lEquiv.refl X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_partialEquiv : (OpenPartialHomeomorph.refl X).toPartialEquiv = PartialEquiv.refl X :=
  rfl

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomor
ph`。
形式化陈述：refl_symm : (OpenPartialHomeomorph.refl X).symm = OpenPartialHomeomorph.re
fl X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm : (OpenPartialHomeomorph.refl X).symm = OpenPartialHomeomorph.refl X :=
  rfl

variable (e : OpenPartialHomeomorph X Y)
/-
**OpenPartialHomeomorph.source_preimage_target** 是 Mathlib 中的一个定理，位于命名空间 `OpenPa
rtialHomeomorph`。
形式化陈述：source_preimage_target : e.source subseteq e ⁻¹' e.target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y
), Set.MapsTo (↑e)…
-/
theorem source_preimage_target : e.source ⊆ e ⁻¹' e.target :=
  e.mapsTo
/-
**OpenPartialHomeomorph.image_eq_target_inter_inv_preimage** 是 Mathlib 中的一个定理，位于
命名空间 `OpenPartialHomeomorph`。
形式化陈述：image_eq_target_inter_inv_preimage {s : Set X} (h : s subseteq e.source) :
 e '' s = e.target inter e.symm ⁻¹' s
参数：h : s subseteq e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_eq_target_inter_inv_preimage`：image_eq_target_inter_i
nv_preimage {s : Set α} (h : s subseteq e.source) : e '' s = e.target inter e.sy
mm ⁻¹' s
-/
theorem image_eq_target_inter_inv_preimage {s : Set X} (h : s ⊆ e.source) :
    e '' s = e.target ∩ e.symm ⁻¹' s :=
  e.toPartialEquiv.image_eq_target_inter_inv_preimage h
/-
**OpenPartialHomeomorph.image_source_inter_eq'** 是 Mathlib 中的一个定理，位于命名空间 `OpenPa
rtialHomeomorph`。
形式化陈述：image_source_inter_eq' (s : Set X) : e '' (e.source inter s) = e.target in
ter e.symm ⁻¹' s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_source_inter_eq'`：image_source_inter_eq' (s : Set α) 
: e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
-/
theorem image_source_inter_eq' (s : Set X) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s :=
  e.toPartialEquiv.image_source_inter_eq' s
/-
**OpenPartialHomeomorph.image_source_inter_eq** 是 Mathlib 中的一个定理，位于命名空间 `OpenPar
tialHomeomorph`。
形式化陈述：image_source_inter_eq (s : Set X) : e '' (e.source inter s) = e.target int
er e.symm ⁻¹' (e.source inter s)
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_source_inter_eq`：image_source_inter_eq (s : Set α) : 
e '' (e.source inter s) = e.target inter e.symm ⁻¹' (e.source inter s)
-/
theorem image_source_inter_eq (s : Set X) :
    e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) :=
  e.toPartialEquiv.image_source_inter_eq s
/-
**OpenPartialHomeomorph.symm_image_eq_source_inter_preimage** 是 Mathlib 中的一个定理，位
于命名空间 `OpenPartialHomeomorph`。
形式化陈述：symm_image_eq_source_inter_preimage {s : Set Y} (h : s subseteq e.target) 
: e.symm '' s = e.source inter e ⁻¹' s
参数：h : s subseteq e.target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.image_eq_target_inter_inv_preimage`：image_eq_targe
t_inter_inv_preimage {s : Set X} (h : s subseteq e.source) : e '' s = e.target i
nter e.symm ⁻¹' s
-/
theorem symm_image_eq_source_inter_preimage {s : Set Y} (h : s ⊆ e.target) :
    e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h
/-
**OpenPartialHomeomorph.symm_image_target_inter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Op
enPartialHomeomorph`。
形式化陈述：symm_image_target_inter_eq (s : Set Y) : e.symm '' (e.target inter s) = e.
source inter e ⁻¹' (e.target inter s)
参数：s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.image_source_inter_eq`：image_source_inter_eq (s : 
Set X) : e '' (e.source inter s) = e.target inter e.symm ⁻¹' (e.source inter s)
-/
theorem symm_image_target_inter_eq (s : Set Y) :
    e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _
/-
**OpenPartialHomeomorph.source_inter_preimage_inv_preimage** 是 Mathlib 中的一个定理，位于
命名空间 `OpenPartialHomeomorph`。
形式化陈述：source_inter_preimage_inv_preimage (s : Set X) : e.source inter e ⁻¹' e.sy
mm ⁻¹' s = e.source inter s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.source_inter_preimage_inv_preimage`：source_inter_preimage_i
nv_preimage (s : Set α) : e.source inter e ⁻¹' e.symm ⁻¹' s = e.source inter s
-/
theorem source_inter_preimage_inv_preimage (s : Set X) :
    e.source ∩ e ⁻¹' e.symm ⁻¹' s = e.source ∩ s :=
  e.toPartialEquiv.source_inter_preimage_inv_preimage s
/-
**OpenPartialHomeomorph.target_inter_inv_preimage_preimage** 是 Mathlib 中的一个定理，位于
命名空间 `OpenPartialHomeomorph`。
形式化陈述：target_inter_inv_preimage_preimage (s : Set Y) : e.target inter e.symm ⁻¹'
 e ⁻¹' s = e.target inter s
参数：s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.source_inter_preimage_inv_preimage`：source_inter_p
reimage_inv_preimage (s : Set X) : e.source inter e ⁻¹' e.symm ⁻¹' s = e.source 
inter s
-/
theorem target_inter_inv_preimage_preimage (s : Set Y) :
    e.target ∩ e.symm ⁻¹' e ⁻¹' s = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _
/-
**OpenPartialHomeomorph.source_inter_preimage_target_inter** 是 Mathlib 中的一个定理，位于
命名空间 `OpenPartialHomeomorph`。
形式化陈述：source_inter_preimage_target_inter (s : Set Y) : e.source inter e ⁻¹' (e.t
arget inter s) = e.source inter e ⁻¹' s
参数：s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.source_inter_preimage_target_inter`：source_inter_preimage_t
arget_inter (s : Set β) : e.source inter e ⁻¹' (e.target inter s) = e.source int
er e ⁻¹' s
-/
theorem source_inter_preimage_target_inter (s : Set Y) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.toPartialEquiv.source_inter_preimage_target_inter s
/-
**OpenPartialHomeomorph.image_source_eq_target** 是 Mathlib 中的一个定理，位于命名空间 `OpenPa
rtialHomeomorph`。
形式化陈述：image_source_eq_target : e '' e.source = e.target
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
-/
theorem image_source_eq_target : e '' e.source = e.target :=
  e.toPartialEquiv.image_source_eq_target
/-
**OpenPartialHomeomorph.symm_image_target_eq_source** 是 Mathlib 中的一个定理，位于命名空间 `O
penPartialHomeomorph`。
形式化陈述：symm_image_target_eq_source : e.symm '' e.target = e.source
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.image_source_eq_target`：image_source_eq_target : e
 '' e.source = e.target
-/
theorem symm_image_target_eq_source : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target
/-
**OpenPartialHomeomorph.isOpen_inter_preimage** 是 Mathlib 中的一个定理，位于命名空间 `OpenPar
tialHomeomorph`。
形式化陈述：isOpen_inter_preimage {s : Set Y} (hs : IsOpen s) : IsOpen (e.source inter
 e ⁻¹' s)
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.isOpen_inter_preimage`：ContinuousOn.isOpen_inter_preimage {
t : Set β} (hf : ContinuousOn f s) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s i
nter f ⁻¹' t)
· 使用定理 `OpenPartialHomeomorph.continuousOn`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y), ContinuousOn (↑…
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
theorem isOpen_inter_preimage {s : Set Y} (hs : IsOpen s) : IsOpen (e.source ∩ e ⁻¹' s) :=
  e.continuousOn.isOpen_inter_preimage e.open_source hs
/-
**OpenPartialHomeomorph.isOpen_inter_preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 `Op
enPartialHomeomorph`。
形式化陈述：isOpen_inter_preimage_symm {s : Set X} (hs : IsOpen s) : IsOpen (e.target 
inter e.symm ⁻¹' s)
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.isOpen_inter_preimage`：ContinuousOn.isOpen_inter_preimage {
t : Set β} (hf : ContinuousOn f s) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s i
nter f ⁻¹' t)
· 使用定理 `OpenPartialHomeomorph.continuousOn`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y), ContinuousOn (↑…
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
theorem isOpen_inter_preimage_symm {s : Set X} (hs : IsOpen s) : IsOpen (e.target ∩ e.symm ⁻¹' s) :=
  e.symm.continuousOn.isOpen_inter_preimage e.open_target hs

/-- An open partial homeomorphism is an open map on its source:
  the image of an open subset of the source is open. -/
/-
**OpenPartialHomeomorph.isOpen_image_of_subset_source** 是 Mathlib 中的一个引理，位于命名空间 
`OpenPartialHomeomorph`。
形式化陈述：isOpen_image_of_subset_source {s : Set X} (hs : IsOpen s) (hse : s subsete
q e.source) : IsOpen (e '' s)
参数：hs : IsOpen s；hse : s subseteq e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.image_eq_target_inter_inv_preimage`：image_eq_targe
t_inter_inv_preimage {s : Set X} (h : s subseteq e.source) : e '' s = e.target i
nter e.symm ⁻¹' s
· 使用定理 `ContinuousOn.isOpen_inter_preimage`：ContinuousOn.isOpen_inter_preimage {
t : Set β} (hf : ContinuousOn f s) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s i
nter f ⁻¹' t)
· 使用定理 `PartialHomeomorph.continuousOn_invFun`：∀ {X : Type u_7} {Y : Type u_8} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeom
orph X Y), ContinuousOn sel…
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…

--- 原说明 ---
An open partial homeomorphism is an open map on its source:
  the image of an open subset of the source is open.
-/
lemma isOpen_image_of_subset_source {s : Set X} (hs : IsOpen s) (hse : s ⊆ e.source) :
    IsOpen (e '' s) := by
  rw [(image_eq_target_inter_inv_preimage (e := e) hse)]
  exact e.continuousOn_invFun.isOpen_inter_preimage e.open_target hs

/-- The image of the restriction of an open set to the source is open. -/
/-
**OpenPartialHomeomorph.isOpen_image_source_inter** 是 Mathlib 中的一个定理，位于命名空间 `Ope
nPartialHomeomorph`。
形式化陈述：isOpen_image_source_inter {s : Set X} (hs : IsOpen s) : IsOpen (e '' (e.so
urce inter s))
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OpenPartialHomeomorph.isOpen_image_of_subset_source`：isOpen_image_of_sub
set_source {s : Set X} (hs : IsOpen s) (hse : s subseteq e.source) : IsOpen (e '
' s)
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s

--- 原说明 ---
The image of the restriction of an open set to the source is open.
-/
theorem isOpen_image_source_inter {s : Set X} (hs : IsOpen s) :
    IsOpen (e '' (e.source ∩ s)) :=
  e.isOpen_image_of_subset_source (e.open_source.inter hs) inter_subset_left

/-- The inverse of an open partial homeomorphism `e` is an open map on `e.target`. -/
/-
**OpenPartialHomeomorph.isOpen_image_symm_of_subset_target** 是 Mathlib 中的一个引理，位于
命名空间 `OpenPartialHomeomorph`。
形式化陈述：isOpen_image_symm_of_subset_target {t : Set Y} (ht : IsOpen t) (hte : t su
bseteq e.target) : IsOpen (e.symm '' t)
参数：ht : IsOpen t；hte : t subseteq e.target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OpenPartialHomeomorph.isOpen_image_of_subset_source`：isOpen_image_of_sub
set_source {s : Set X} (hs : IsOpen s) (hse : s subseteq e.source) : IsOpen (e '
' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.symm_source`：symm_source : e.symm.source = e.targe
t

--- 原说明 ---
The inverse of an open partial homeomorphism `e` is an open map on `e.target`.
-/
lemma isOpen_image_symm_of_subset_target {t : Set Y} (ht : IsOpen t) (hte : t ⊆ e.target) :
    IsOpen (e.symm '' t) :=
  isOpen_image_of_subset_source e.symm ht (e.symm_source ▸ hte)
/-
**OpenPartialHomeomorph.isOpen_symm_image_iff_of_subset_target** 是 Mathlib 中的一个引
理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：isOpen_symm_image_iff_of_subset_target {t : Set Y} (hs : t subseteq e.targ
et) : IsOpen (e.symm '' t) ↔ IsOpen t
参数：hs : t subseteq e.target。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.symm_image_eq_source_inter_preimage`：symm_image_eq
_source_inter_preimage {s : Set Y} (h : s subseteq e.target) : e.symm '' s = e.s
ource inter e ⁻¹' s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.image_symm_image_of_subset_target`：image_symm_image_of_subs
et_target {s : Set β} (h : s subseteq e.target) : e '' e.symm '' s = s
· 使用引理 `OpenPartialHomeomorph.isOpen_image_of_subset_source`：isOpen_image_of_sub
set_source {s : Set X} (hs : IsOpen s) (hse : s subseteq e.source) : IsOpen (e '
' s)
-/
lemma isOpen_symm_image_iff_of_subset_target {t : Set Y} (hs : t ⊆ e.target) :
    IsOpen (e.symm '' t) ↔ IsOpen t := by
  refine ⟨fun h ↦ ?_, fun h ↦ e.symm.isOpen_image_of_subset_source h hs⟩
  have hs' : e.symm '' t ⊆ e.source := by
    rw [e.symm_image_eq_source_inter_preimage hs]
    apply Set.inter_subset_left
  rw [← e.image_symm_image_of_subset_target hs]
  exact e.isOpen_image_of_subset_source h hs'
/-
**OpenPartialHomeomorph.isOpen_image_iff_of_subset_source** 是 Mathlib 中的一个定理，位于命
名空间 `OpenPartialHomeomorph`。
形式化陈述：isOpen_image_iff_of_subset_source {s : Set X} (hs : s subseteq e.source) :
 IsOpen (e '' s) ↔ IsOpen s
参数：hs : s subseteq e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `OpenPartialHomeomorph.isOpen_symm_image_iff_of_subset_target`：isOpen_sym
m_image_iff_of_subset_target {t : Set Y} (hs : t subseteq e.target) : IsOpen (e.
symm '' t) ↔ IsOpen t
· 使用定理 `OpenPartialHomeomorph.symm_symm`：∀ {X : Type u_1} {Y : Type u_3} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph 
X Y), e.symm.symm = e
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_image_iff_of_subset_source {s : Set X} (hs : s ⊆ e.source) :
    IsOpen (e '' s) ↔ IsOpen s := by
  rw [← e.symm.isOpen_symm_image_iff_of_subset_target hs, e.symm_symm]

/-- A `PartialEquiv` which is continuous on its source and has open forward map (on its source)
and open source is an `OpenPartialHomeomorph`. -/
@[simps! toPartialHomeomorph]
/-
**OpenPartialHomeomorph.ofContinuousOpenRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.sou
rce) (ho : IsOpenMap (e.source.domRestrict e)) (hs : IsOpen e.source) : OpenPart
ialHomeomorph X Y where toPartialHomeomorph
参数：e : PartialEquiv X Y；hc : ContinuousOn e e.source；ho : IsOpenMap (e.source.do
mRestrict e)；hs : IsOpen e.source。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `PartialEquiv` which is continuous on its source and has open forward map (on 
its source)
and open source is an `OpenPartialHomeomorph`.
-/
def ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.domRestrict e)) (hs : IsOpen e.source) :
    OpenPartialHomeomorph X Y where
  toPartialHomeomorph := PartialHomeomorph.ofContinuousOpenRestrict e hc ho
  open_source := hs
  open_target := by simpa [e.image_source_eq_target] using ho.isOpen_range

@[simp]
/-
**OpenPartialHomeomorph.coe_ofContinuousOpenRestrict** 是 Mathlib 中的一个定理，位于命名空间 `
OpenPartialHomeomorph`。
形式化陈述：coe_ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e
.source) (ho : IsOpenMap (e.source.domRestrict e)) (hs : IsOpen e.source) : ⇑(of
ContinuousOpenRestrict e hc ho hs) = e
参数：e : PartialEquiv X Y；hc : ContinuousOn e e.source；ho : IsOpenMap (e.source.do
mRestrict e)；hs : IsOpen e.source。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.domRestrict e)) (hs : IsOpen e.source) :
    ⇑(ofContinuousOpenRestrict e hc ho hs) = e :=
  rfl

@[simp]
/-
**OpenPartialHomeomorph.coe_ofContinuousOpenRestrict_symm** 是 Mathlib 中的一个定理，位于命
名空间 `OpenPartialHomeomorph`。
形式化陈述：coe_ofContinuousOpenRestrict_symm (e : PartialEquiv X Y) (hc : ContinuousO
n e e.source) (ho : IsOpenMap (e.source.domRestrict e)) (hs : IsOpen e.source) :
 ⇑(ofContinuousOpenRestrict e hc ho hs).symm = e.symm
参数：e : PartialEquiv X Y；hc : ContinuousOn e e.source；ho : IsOpenMap (e.source.do
mRestrict e)；hs : IsOpen e.source。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofContinuousOpenRestrict_symm (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.domRestrict e)) (hs : IsOpen e.source) :
    ⇑(ofContinuousOpenRestrict e hc ho hs).symm = e.symm :=
  rfl

/-- A `PartialEquiv` which is continuous on its source and has open forward map (on its source) and
open source is an `OpenPartialHomeomorph`. -/
@[simps! toPartialHomeomorph]
/-
**OpenPartialHomeomorph.ofContinuousOpen** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialH
omeomorph`。
形式化陈述：ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source) (ho
 : IsOpenMap e) (hs : IsOpen e.source) : OpenPartialHomeomorph X Y
参数：e : PartialEquiv X Y；hc : ContinuousOn e e.source；ho : IsOpenMap e；hs : IsOpe
n e.source。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `PartialEquiv` which is continuous on its source and has open forward map (on 
its source) and
open source is an `OpenPartialHomeomorph`.
-/
def ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
    (hs : IsOpen e.source) : OpenPartialHomeomorph X Y :=
  ofContinuousOpenRestrict e hc (ho.domRestrict hs) hs

@[simp]
/-
**OpenPartialHomeomorph.coe_ofContinuousOpen** 是 Mathlib 中的一个定理，位于命名空间 `OpenPart
ialHomeomorph`。
形式化陈述：coe_ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
 (ho : IsOpenMap e) (hs : IsOpen e.source) : ⇑(ofContinuousOpen e hc ho hs) = e
参数：e : PartialEquiv X Y；hc : ContinuousOn e e.source；ho : IsOpenMap e；hs : IsOpe
n e.source。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap e) (hs : IsOpen e.source) :
    ⇑(ofContinuousOpen e hc ho hs) = e :=
  rfl

@[simp]
/-
**OpenPartialHomeomorph.coe_ofContinuousOpen_symm** 是 Mathlib 中的一个定理，位于命名空间 `Ope
nPartialHomeomorph`。
形式化陈述：coe_ofContinuousOpen_symm (e : PartialEquiv X Y) (hc : ContinuousOn e e.so
urce) (ho : IsOpenMap e) (hs : IsOpen e.source) : ⇑(ofContinuousOpen e hc ho hs)
.symm = e.symm
参数：e : PartialEquiv X Y；hc : ContinuousOn e e.source；ho : IsOpenMap e；hs : IsOpe
n e.source。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofContinuousOpen_symm (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap e) (hs : IsOpen e.source) :
    ⇑(ofContinuousOpen e hc ho hs).symm = e.symm :=
  rfl

/-- The homeomorphism obtained by restricting an `OpenPartialHomeomorph` to a subset of the source.
-/
@[simps!]
/-
**OpenPartialHomeomorph.homeomorphOfImageSubsetSource** 是 Mathlib 中的一个定义，位于命名空间 
`OpenPartialHomeomorph`。
形式化陈述：homeomorphOfImageSubsetSource {s : Set X} {t : Set Y} (hs : s subseteq e.s
ource) (ht : e '' s = t) : s ≃ₜ t
参数：hs : s subseteq e.source；ht : e '' s = t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homeomorphism obtained by restricting an `OpenPartialHomeomorph` to a subset
 of the source.
-/
def homeomorphOfImageSubsetSource {s : Set X} {t : Set Y} (hs : s ⊆ e.source) (ht : e '' s = t) :
    s ≃ₜ t :=
  e.toPartialHomeomorph.homeomorphOfImageSubsetSource hs ht

/-- An open partial homeomorphism defines a homeomorphism between its source and target. -/
@[simps!]
/-
**OpenPartialHomeomorph.toHomeomorphSourceTarget** 是 Mathlib 中的一个定义，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：toHomeomorphSourceTarget : e.source ≃ₜ e.target
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.image_source_eq_target`：image_source_eq_target : e
 '' e.source = e.target

--- 原说明 ---
An open partial homeomorphism defines a homeomorphism between its source and tar
get.
-/
def toHomeomorphSourceTarget : e.source ≃ₜ e.target :=
  e.homeomorphOfImageSubsetSource subset_rfl e.image_source_eq_target
/-
**OpenPartialHomeomorph.secondCountableTopology_source** 是 Mathlib 中的一个定理，位于命名空间
 `OpenPartialHomeomorph`。
形式化陈述：secondCountableTopology_source [SecondCountableTopology Y] : SecondCountab
leTopology e.source
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.secondCountableTopology`：∀ {X : Type u_1} {Y : Type u_2} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [SecondCountableTopology Y
]   (h : X ≃ₜ Y), Second…
· 使用定理 `TopologicalSpace.Subtype.secondCountableTopology`：∀ {α : Type u} [t : To
pologicalSpace α] (s : Set α) [SecondCountableTopology α], SecondCountableTopolo
gy ↑s
-/
theorem secondCountableTopology_source [SecondCountableTopology Y] :
    SecondCountableTopology e.source :=
  e.toHomeomorphSourceTarget.secondCountableTopology
/-
**OpenPartialHomeomorph.nhds_eq_comap_inf_principal** 是 Mathlib 中的一个定理，位于命名空间 `O
penPartialHomeomorph`。
形式化陈述：nhds_eq_comap_inf_principal {x} (hx : x in e.source) : 𝓝 x = comap e (𝓝 (e
 x)) ⊓ 𝓟 e.source
参数：hx : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpen.nhdsWithin_eq`：IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOp
en s) (ha : a in s) : 𝓝[s] a = 𝓝 a
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `map_nhds_subtype_val`：map_nhds_subtype_val {s : Set X} (x : s) : map ((↑
) : s -> X) (𝓝 x) = 𝓝[s] ↑x
· 使用定理 `Filter.map_comap_setCoe_val`：map_comap_setCoe_val (f : Filter β) (s : Se
t β) : (f.comap ((↑) : s -> β)).map (↑) = f ⊓ 𝓟 s
· 使用定理 `Homeomorph.nhds_eq_comap`：nhds_eq_comap (h : X ≃ₜ Y) (x : X) : 𝓝 x = com
ap h (𝓝 (h x))
· 使用定理 `nhds_subtype_eq_comap`：nhds_subtype_eq_comap {x : X} {h : p x} : 𝓝 (⟨x, 
h⟩ : Subtype p) = comap (↑) (𝓝 x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.toHomeomorphSourceTarget_apply_coe`：∀ {X : Type u_
1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e
 : OpenPartialHomeomorph X Y) (a : ↑e.source),…
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhds_eq_comap_inf_principal {x} (hx : x ∈ e.source) :
    𝓝 x = comap e (𝓝 (e x)) ⊓ 𝓟 e.source := by
  lift x to e.source using hx
  rw [← e.open_source.nhdsWithin_eq x.2, ← map_nhds_subtype_val, ← map_comap_setCoe_val,
    e.toHomeomorphSourceTarget.nhds_eq_comap, nhds_subtype_eq_comap]
  simp only [Function.comp_def, toHomeomorphSourceTarget_apply_coe, comap_comap]

/-- If an open partial homeomorphism has source and target equal to univ, then it induces a
homeomorphism between the whole spaces, expressed in this definition. -/
@[simps! (attr := mfld_simps) -fullyApplied apply symm_apply]
-- TODO: add a `PartialEquiv` version
/-
**OpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv** 是 Mathlib 中的一个定
义，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：toHomeomorphOfSourceEqUnivTargetEqUniv (h : e.source = (univ : Set X)) (h'
 : e.target = univ) : X ≃ₜ Y
参数：h : e.source = (univ : Set X)；h' : e.target = univ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toHomeomorphOfSourceEqUnivTargetEqUniv (h : e.source = (univ : Set X)) (h' : e.target = univ) :
    X ≃ₜ Y :=
  e.toPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv h h'
/-
**OpenPartialHomeomorph.isOpenEmbedding_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：isOpenEmbedding_restrict : IsOpenEmbedding (e.source.domRestrict e) where 
toIsEmbedding
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.isEmbedding_restrict`：isEmbedding_restrict : IsEmbeddi
ng (e.source.domRestrict e.toFun)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_domRestrict`：range_domRestrict (f : α -> β) (s : Set α) : Set.
range (s.domRestrict f) = f '' s
· 使用定理 `OpenPartialHomeomorph.image_source_eq_target`：image_source_eq_target : e
 '' e.source = e.target
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
theorem isOpenEmbedding_restrict : IsOpenEmbedding (e.source.domRestrict e) where
  toIsEmbedding := e.isEmbedding_restrict
  isOpen_range := by
    rw [range_domRestrict, image_source_eq_target]
    exact e.open_target

/-- An open partial homeomorphism whose source is all of `X` defines an open embedding of `X` into
`Y`. The converse is also true; see `IsOpenEmbedding.toOpenPartialHomeomorph`. -/
/-
**OpenPartialHomeomorph.isOpenEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHo
meomorph`。
形式化陈述：isOpenEmbedding (h : e.source = Set.univ) : IsOpenEmbedding e
参数：h : e.source = Set.univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type
 u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologica
lSpace Y] [inst_2 :…
· 使用定理 `OpenPartialHomeomorph.isOpenEmbedding_restrict`：isOpenEmbedding_restrict
 : IsOpenEmbedding (e.source.domRestrict e) where toIsEmbedding
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h

--- 原说明 ---
An open partial homeomorphism whose source is all of `X` defines an open embeddi
ng of `X` into
`Y`. The converse is also true; see `IsOpenEmbedding.toOpenPartialHomeomorph`.
-/
theorem isOpenEmbedding (h : e.source = Set.univ) : IsOpenEmbedding e :=
  e.isOpenEmbedding_restrict.comp
    ((Homeomorph.setCongr h).trans <| Homeomorph.Set.univ X).symm.isOpenEmbedding

@[deprecated (since := "2026-07-17")] alias to_isOpenEmbedding := isOpenEmbedding

end OpenPartialHomeomorph

/-!
## Open embeddings
-/
namespace Topology.IsOpenEmbedding

variable (f : X → Y) (h : IsOpenEmbedding f)

/-- An open embedding of `X` into `Y`, with `X` nonempty, defines an open partial homeomorphism
whose source is all of `X`. The converse is also true; see
`OpenPartialHomeomorph.isOpenEmbedding`. -/
@[simps! (attr := mfld_simps) -fullyApplied apply source target]
/-
**Topology.IsOpenEmbedding.toOpenPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `To
pology.IsOpenEmbedding`。
形式化陈述：toOpenPartialHomeomorph [Nonempty X] : OpenPartialHomeomorph X Y
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ

--- 原说明 ---
An open embedding of `X` into `Y`, with `X` nonempty, defines an open partial ho
meomorphism
whose source is all of `X`. The converse is also true; see
`OpenPartialHomeomorph.isOpenEmbedding`.
-/
noncomputable def toOpenPartialHomeomorph [Nonempty X] : OpenPartialHomeomorph X Y :=
  OpenPartialHomeomorph.ofContinuousOpen (h.isEmbedding.injective.injOn.toPartialEquiv f univ)
    h.continuous.continuousOn h.isOpenMap isOpen_univ

variable [Nonempty X]
/-
**Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv** 是 Mathlib 中的一个引理，位
于命名空间 `Topology.IsOpenEmbedding`。
形式化陈述：toOpenPartialHomeomorph_left_inv {x : X} : (h.toOpenPartialHomeomorph f).s
ymm (f x) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply`：∀ {X : Type u_1}
 {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : X
 → Y)   (h : Topology.IsOpenEmbedding f) [in…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
lemma toOpenPartialHomeomorph_left_inv {x : X} : (h.toOpenPartialHomeomorph f).symm (f x) = x := by
  rw [← congr_fun (h.toOpenPartialHomeomorph_apply f), OpenPartialHomeomorph.left_inv]
  exact Set.mem_univ _
/-
**Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv** 是 Mathlib 中的一个引理，
位于命名空间 `Topology.IsOpenEmbedding`。
形式化陈述：toOpenPartialHomeomorph_right_inv {x : Y} (hx : x in Set.range f) : f ((h.
toOpenPartialHomeomorph f).symm x) = x
参数：hx : x in Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply`：∀ {X : Type u_1}
 {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : X
 → Y)   (h : Topology.IsOpenEmbedding f) [in…
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target`：∀ {X : Type u_1
} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : 
X → Y)   (h : Topology.IsOpenEmbedding f) [in…
-/
lemma toOpenPartialHomeomorph_right_inv {x : Y} (hx : x ∈ Set.range f) :
    f ((h.toOpenPartialHomeomorph f).symm x) = x := by
  rw [← congr_fun (h.toOpenPartialHomeomorph_apply f), OpenPartialHomeomorph.right_inv]
  rwa [toOpenPartialHomeomorph_target]

end Topology.IsOpenEmbedding

/-! inclusion of an open set in a topological space -/
namespace TopologicalSpace.Opens

/- `Nonempty s` is not a type class argument because `s`, being a subset, rarely comes with a type
class instance. Then we'd have to manually provide the instance every time we use the following
lemmas, tediously using `haveI := ...` or `@foobar _ _ _ ...`. -/
variable (s : Opens X) (hs : Nonempty s)

/-- The inclusion of an open subset `s` of a space `X` into `X` is an open partial homeomorphism
from the subtype `s` to `X`. -/
/-
**TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe** 是 Mathlib 中的一个定义，位于命名
空间 `TopologicalSpace.Opens`。
形式化陈述：openPartialHomeomorphSubtypeCoe : OpenPartialHomeomorph s X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of an open subset `s` of a space `X` into `X` is an open partial h
omeomorphism
from the subtype `s` to `X`.
-/
noncomputable def openPartialHomeomorphSubtypeCoe : OpenPartialHomeomorph s X :=
  IsOpenEmbedding.toOpenPartialHomeomorph _ s.2.isOpenEmbedding_subtypeVal

@[simp, mfld_simps]
/-
**TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe** 是 Mathlib 中的一个定理，
位于命名空间 `TopologicalSpace.Opens`。
形式化陈述：openPartialHomeomorphSubtypeCoe_coe : (s.openPartialHomeomorphSubtypeCoe h
s : s -> X) = (↑)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem openPartialHomeomorphSubtypeCoe_coe :
    (s.openPartialHomeomorphSubtypeCoe hs : s → X) = (↑) :=
  rfl

@[simp, mfld_simps]
/-
**TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source** 是 Mathlib 中的一个
定理，位于命名空间 `TopologicalSpace.Opens`。
形式化陈述：openPartialHomeomorphSubtypeCoe_source : (s.openPartialHomeomorphSubtypeCo
e hs).source = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem openPartialHomeomorphSubtypeCoe_source :
    (s.openPartialHomeomorphSubtypeCoe hs).source = Set.univ :=
  rfl

@[simp, mfld_simps]
/-
**TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target** 是 Mathlib 中的一个
定理，位于命名空间 `TopologicalSpace.Opens`。
形式化陈述：openPartialHomeomorphSubtypeCoe_target : (s.openPartialHomeomorphSubtypeCo
e hs).target = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target`：∀ {X : Type u_1
} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : 
X → Y)   (h : Topology.IsOpenEmbedding f) [in…
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem openPartialHomeomorphSubtypeCoe_target :
    (s.openPartialHomeomorphSubtypeCoe hs).target = s := by
  simp [openPartialHomeomorphSubtypeCoe]

end TopologicalSpace.Opens

