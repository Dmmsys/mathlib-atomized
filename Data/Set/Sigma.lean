/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.BooleanAlgebra

/-!
# Sets in sigma types

This file defines `Set.sigma`, the indexed sum of sets.
-/

@[expose] public section

namespace Set

variable {ι ι' : Type*} {α : ι → Type*} {s s₁ s₂ : Set ι} {t t₁ t₂ : ∀ i, Set (α i)}
  {u : Set (Σ i, α i)} {x : Σ i, α i} {i j : ι} {a : α i}

@[simp]
/-
**Set.range_sigmaMk** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_sigmaMk (i : ι) : range (Sigma.mk i : α i -> Sigma α) = Sigma.fst ⁻¹
' {i}
参数：i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_sigmaMk (i : ι) : range (Sigma.mk i : α i → Sigma α) = Sigma.fst ⁻¹' {i} := by grind
/-
**Set.preimage_image_sigmaMk_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_image_sigmaMk_of_ne (h : i != j) (s : Set (α j)) : Sigma.mk i ⁻¹'
 Sigma.mk j '' s = ∅
参数：h : i != j；s : Set (α j)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_image_sigmaMk_of_ne (h : i ≠ j) (s : Set (α j)) :
    Sigma.mk i ⁻¹' Sigma.mk j '' s = ∅ := by grind
/-
**Set.image_sigmaMk_preimage_sigmaMap_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_sigmaMk_preimage_sigmaMap_subset {β : ι' -> Type*} (f : ι -> ι') (g 
: forall i, α i -> β (f i)) (i : ι) (s : Set (β (f i))) : Sigma.mk i '' g i ⁻¹' 
s subseteq Sigma.map f g ⁻¹' Sigma.mk (f i) '' s
参数：f : ι -> ι'；g : forall i, α i -> β (f i)；i : ι；s : Set (β (f i))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem image_sigmaMk_preimage_sigmaMap_subset {β : ι' → Type*} (f : ι → ι')
    (g : ∀ i, α i → β (f i)) (i : ι) (s : Set (β (f i))) :
    Sigma.mk i '' g i ⁻¹' s ⊆ Sigma.map f g ⁻¹' Sigma.mk (f i) '' s :=
  image_subset_iff.2 fun x hx ↦ ⟨g i x, hx, rfl⟩
/-
**Set.image_sigmaMk_preimage_sigmaMap** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_sigmaMk_preimage_sigmaMap {β : ι' -> Type*} {f : ι -> ι'} (hf : Func
tion.Injective f) (g : forall i, α i -> β (f i)) (i : ι) (s : Set (β (f i))) : S
igma.mk i '' g i ⁻¹' s = Sigma.map f g ⁻¹' Sigma.mk (f i) '' s
参数：hf : Function.Injective f；g : forall i, α i -> β (f i)；i : ι；s : Set (β (f i)
)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.image_sigmaMk_preimage_sigmaMap_subset`：image_sigmaMk_preimage_sigma
Map_subset {β : ι' -> Type*} (f : ι -> ι') (g : forall i, α i -> β (f i)) (i : ι
) (s : Set (β (f i))) : Sigma.mk…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
-/
theorem image_sigmaMk_preimage_sigmaMap {β : ι' → Type*} {f : ι → ι'} (hf : Function.Injective f)
    (g : ∀ i, α i → β (f i)) (i : ι) (s : Set (β (f i))) :
    Sigma.mk i '' g i ⁻¹' s = Sigma.map f g ⁻¹' Sigma.mk (f i) '' s := by
  refine (image_sigmaMk_preimage_sigmaMap_subset f g i s).antisymm ?_
  rintro ⟨j, x⟩ ⟨y, hys, hxy⟩
  simp only [hf.eq_iff, Sigma.map, Sigma.ext_iff] at hxy
  grind

/-- Indexed sum of sets. `s.sigma t` is the set of dependent pairs `⟨i, a⟩` such that `i ∈ s` and
`a ∈ t i`. -/
/-
**Set.sigma** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{ι : Type u_1} → {α : ι → Type u_3} → Set ι → ((i : ι) → Set (α i)) → Set 
((i : ι) × α i)
参数：(i : ι) → Set (α i)；(i : ι) × α i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Indexed sum of sets. `s.sigma t` is the set of dependent pairs `⟨i, a⟩` such tha
t `i ∈ s` and
`a ∈ t i`.
-/
protected def sigma (s : Set ι) (t : ∀ i, Set (α i)) : Set (Σ i, α i) := {x | x.1 ∈ s ∧ x.2 ∈ t x.1}
/-
**Set.mem_sigma_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} {s : Set ι} {t : (i : ι) → Set (α i)} 
{x : (i : ι) × α i},   x ∈ s.sigma t ↔ x.fst ∈ s ∧ x.snd ∈ t x.fst
参数：i : ι；α i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, grind =] theorem mem_sigma_iff : x ∈ s.sigma t ↔ x.1 ∈ s ∧ x.2 ∈ t x.1 := Iff.rfl
/-
**Set.mk_sigma_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_sigma_iff : (⟨i, a⟩ : Σ i, α i) in s.sigma t ↔ i in s ∧ a in t i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_sigma_iff : (⟨i, a⟩ : Σ i, α i) ∈ s.sigma t ↔ i ∈ s ∧ a ∈ t i := Iff.rfl
/-
**Set.mk_mem_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_mem_sigma (hi : i in s) (ha : a in t i) : (⟨i, a⟩ : Σ i, α i) in s.sigm
a t
参数：hi : i in s；ha : a in t i。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_mem_sigma (hi : i ∈ s) (ha : a ∈ t i) : (⟨i, a⟩ : Σ i, α i) ∈ s.sigma t := ⟨hi, ha⟩
/-
**Set.sigma_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigma_mono (hs : s₁ subseteq s₂) (ht : forall i, t₁ i subseteq t₂ i) : s₁.
sigma t₁ subseteq s₂.sigma t₂
参数：hs : s₁ subseteq s₂；ht : forall i, t₁ i subseteq t₂ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sigma_mono (hs : s₁ ⊆ s₂) (ht : ∀ i, t₁ i ⊆ t₂ i) : s₁.sigma t₁ ⊆ s₂.sigma t₂ := fun _ hx ↦
  ⟨hs hx.1, ht _ hx.2⟩
/-
**Set.sigma_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigma_subset_iff : s.sigma t subseteq u ↔ forall ⦃i⦄, i in s -> forall ⦃a⦄
, a in t i -> (⟨i, a⟩ : Σ i, α i) in u
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigma_subset_iff :
    s.sigma t ⊆ u ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃a⦄, a ∈ t i → (⟨i, a⟩ : Σ i, α i) ∈ u := by grind
/-
**Set.forall_sigma_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：forall_sigma_iff {p : (Σ i, α i) -> Prop} : (forall x in s.sigma t, p x) ↔
 forall ⦃i⦄, i in s -> forall ⦃a⦄, a in t i -> p ⟨i, a⟩
参数：Σ i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_sigma_iff {p : (Σ i, α i) → Prop} :
    (∀ x ∈ s.sigma t, p x) ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃a⦄, a ∈ t i → p ⟨i, a⟩ := by grind
/-
**Set.exists_sigma_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_sigma_iff {p : (Σ i, α i) -> Prop} : (exists x in s.sigma t, p x) ↔
 exists i in s, exists a in t i, p ⟨i, a⟩
参数：Σ i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_sigma_iff {p : (Σ i, α i) → Prop} :
    (∃ x ∈ s.sigma t, p x) ↔ ∃ i ∈ s, ∃ a ∈ t i, p ⟨i, a⟩ := by grind
/-
**Set.sigma_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} {s : Set ι}, (s.sigma fun i => ∅) = ∅
参数：s.sigma fun i => ∅。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem sigma_empty : s.sigma (fun i ↦ (∅ : Set (α i))) = ∅ := by grind
/-
**Set.empty_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} {t : (i : ι) → Set (α i)}, ∅.sigma t =
 ∅
参数：i : ι；α i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem empty_sigma : (∅ : Set ι).sigma t = ∅ := by grind
/-
**Set.univ_sigma_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_sigma_univ : (@univ ι).sigma (fun _ => @univ (α i)) = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem univ_sigma_univ : (@univ ι).sigma (fun _ ↦ @univ (α i)) = univ := by grind

@[simp]
/-
**Set.sigma_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigma_univ : s.sigma (fun _ => univ : forall i, Set (α i)) = Sigma.fst ⁻¹'
 s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigma_univ : s.sigma (fun _ ↦ univ : ∀ i, Set (α i)) = Sigma.fst ⁻¹' s := by grind
/-
**Set.univ_sigma_preimage_mk** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} (s : Set ((i : ι) × α i)), (Set.univ.s
igma fun i => Sigma.mk i ⁻¹' s) = s
参数：s : Set ((i : ι) × α i)；Set.univ.sigma fun i => Sigma.mk i ⁻¹' s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem univ_sigma_preimage_mk (s : Set (Σ i, α i)) :
    (univ : Set ι).sigma (fun i ↦ Sigma.mk i ⁻¹' s) = s := by grind

@[simp]
/-
**Set.singleton_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_sigma : ({i} : Set ι).sigma t = Sigma.mk i '' t i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleton_sigma : ({i} : Set ι).sigma t = Sigma.mk i '' t i := by grind

@[simp]
/-
**Set.sigma_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigma_singleton {a : forall i, α i} : s.sigma (fun i => ({a i} : Set (α i)
)) = (fun i => Sigma.mk i <| a i) '' s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigma_singleton {a : ∀ i, α i} :
    s.sigma (fun i ↦ ({a i} : Set (α i))) = (fun i ↦ Sigma.mk i <| a i) '' s := by grind
/-
**Set.singleton_sigma_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_sigma_singleton {a : forall i, α i} : (({i} : Set ι).sigma fun i
 => ({a i} : Set (α i))) = {⟨i, a i⟩}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleton_sigma_singleton {a : ∀ i, α i} :
    (({i} : Set ι).sigma fun i ↦ ({a i} : Set (α i))) = {⟨i, a i⟩} := by grind

@[simp]
/-
**Set.union_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_sigma : (s₁ union s₂).sigma t = s₁.sigma t union s₂.sigma t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_sigma : (s₁ ∪ s₂).sigma t = s₁.sigma t ∪ s₂.sigma t := by grind

@[simp]
/-
**Set.sigma_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigma_union : s.sigma (fun i => t₁ i union t₂ i) = s.sigma t₁ union s.sigm
a t₂
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigma_union : s.sigma (fun i ↦ t₁ i ∪ t₂ i) = s.sigma t₁ ∪ s.sigma t₂ := by grind
/-
**Set.sigma_inter_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigma_inter_sigma : s₁.sigma t₁ inter s₂.sigma t₂ = (s₁ inter s₂).sigma fu
n i => t₁ i inter t₂ i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigma_inter_sigma : s₁.sigma t₁ ∩ s₂.sigma t₂ = (s₁ ∩ s₂).sigma fun i ↦ t₁ i ∩ t₂ i := by
  grind

variable {β : Type*} [CompleteLattice β]
/-
**Set._root_.biSup_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.biSup_sigma (s : Set ι) (t : ∀ i, Set (α i)) (f : Sigma α → β) :
    ⨆ ij ∈ s.sigma t, f ij = ⨆ (i ∈ s) (j ∈ t i), f ⟨i, j⟩ :=
  eq_of_forall_ge_iff fun _ ↦ ⟨by simp_all, by simp_all⟩
/-
**Set._root_.biSup_sigma'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.biSup_sigma' (s : Set ι) (t : ∀ i, Set (α i)) (f : ∀ i, α i → β) :
    ⨆ (i ∈ s) (j ∈ t i), f i j = ⨆ ij ∈ s.sigma t, f ij.fst ij.snd :=
  Eq.symm (biSup_sigma _ _ _)
/-
**Set._root_.biInf_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.biInf_sigma (s : Set ι) (t : ∀ i, Set (α i)) (f : Sigma α → β) :
    ⨅ ij ∈ s.sigma t, f ij = ⨅ (i ∈ s) (j ∈ t i), f ⟨i, j⟩ :=
  biSup_sigma (β := βᵒᵈ) _ _ _
/-
**Set._root_.biInf_sigma'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.biInf_sigma' (s : Set ι) (t : ∀ i, Set (α i)) (f : ∀ i, α i → β) :
    ⨅ (i ∈ s) (j ∈ t i), f i j = ⨅ ij ∈ s.sigma t, f ij.fst ij.snd :=
  Eq.symm (biInf_sigma _ _ _)

variable {β : Type*}
/-
**Set.biUnion_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_sigma (s : Set ι) (t : forall i, Set (α i)) (f : Sigma α -> Set β)
 : ⋃ ij in s.sigma t, f ij = ⋃ i in s, ⋃ j in t i, f ⟨i, j⟩
参数：s : Set ι；t : forall i, Set (α i)；f : Sigma α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_sigma`：∀ {ι : Type u_1} {α : ι → Type u_3} {β : Type u_4} [inst : 
CompleteLattice β] (s : Set ι) (t : (i : ι) → Set (α i))   (f : Sigma α → β), ⨆ 
i…
-/
theorem biUnion_sigma (s : Set ι) (t : ∀ i, Set (α i)) (f : Sigma α → Set β) :
    ⋃ ij ∈ s.sigma t, f ij = ⋃ i ∈ s, ⋃ j ∈ t i, f ⟨i, j⟩ :=
  biSup_sigma _ _ _
/-
**Set.biUnion_sigma'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_sigma' (s : Set ι) (t : forall i, Set (α i)) (f : forall i, α i ->
 Set β) : ⋃ i in s, ⋃ j in t i, f i j = ⋃ ij in s.sigma t, f ij.fst ij.snd
参数：s : Set ι；t : forall i, Set (α i)；f : forall i, α i -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_sigma'`：∀ {ι : Type u_1} {α : ι → Type u_3} {β : Type u_4} [inst :
 CompleteLattice β] (s : Set ι) (t : (i : ι) → Set (α i))   (f : (i : ι) → α i →
 β…
-/
theorem biUnion_sigma' (s : Set ι) (t : ∀ i, Set (α i)) (f : ∀ i, α i → Set β) :
    ⋃ i ∈ s, ⋃ j ∈ t i, f i j = ⋃ ij ∈ s.sigma t, f ij.fst ij.snd :=
  biSup_sigma' _ _ _
/-
**Set.biInter_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_sigma (s : Set ι) (t : forall i, Set (α i)) (f : Sigma α -> Set β)
 : ⋂ ij in s.sigma t, f ij = ⋂ i in s, ⋂ j in t i, f ⟨i, j⟩
参数：s : Set ι；t : forall i, Set (α i)；f : Sigma α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biInf_sigma`：∀ {ι : Type u_1} {α : ι → Type u_3} {β : Type u_4} [inst : 
CompleteLattice β] (s : Set ι) (t : (i : ι) → Set (α i))   (f : Sigma α → β), ⨅ 
i…
-/
theorem biInter_sigma (s : Set ι) (t : ∀ i, Set (α i)) (f : Sigma α → Set β) :
    ⋂ ij ∈ s.sigma t, f ij = ⋂ i ∈ s, ⋂ j ∈ t i, f ⟨i, j⟩ :=
  biInf_sigma _ _ _
/-
**Set.biInter_sigma'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_sigma' (s : Set ι) (t : forall i, Set (α i)) (f : forall i, α i ->
 Set β) : ⋂ i in s, ⋂ j in t i, f i j = ⋂ ij in s.sigma t, f ij.fst ij.snd
参数：s : Set ι；t : forall i, Set (α i)；f : forall i, α i -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biInf_sigma'`：∀ {ι : Type u_1} {α : ι → Type u_3} {β : Type u_4} [inst :
 CompleteLattice β] (s : Set ι) (t : (i : ι) → Set (α i))   (f : (i : ι) → α i →
 β…
-/
theorem biInter_sigma' (s : Set ι) (t : ∀ i, Set (α i)) (f : ∀ i, α i → Set β) :
    ⋂ i ∈ s, ⋂ j ∈ t i, f i j = ⋂ ij ∈ s.sigma t, f ij.fst ij.snd :=
  biInf_sigma' _ _ _

variable {β : ι → Type*}
/-
**Set.insert_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_sigma : (insert i s).sigma t = Sigma.mk i '' t i union s.sigma t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_sigma : (insert i s).sigma t = Sigma.mk i '' t i ∪ s.sigma t := by grind
/-
**Set.sigma_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigma_insert {a : forall i, α i} : s.sigma (fun i => insert (a i) (t i)) =
 (fun i => ⟨i, a i⟩) '' s union s.sigma t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigma_insert {a : ∀ i, α i} :
    s.sigma (fun i ↦ insert (a i) (t i)) = (fun i ↦ ⟨i, a i⟩) '' s ∪ s.sigma t := by grind
/-
**Set.sigma_preimage_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigma_preimage_eq {f : ι' -> ι} {g : forall i, β i -> α i} : (f ⁻¹' s).sig
ma (fun i => g (f i) ⁻¹' t (f i)) = (fun p : Σ i, β (f i) => Sigma.mk _ (g _ p.2
)) ⁻¹' s.sigma t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigma_preimage_eq {f : ι' → ι} {g : ∀ i, β i → α i} :
    (f ⁻¹' s).sigma (fun i ↦ g (f i) ⁻¹' t (f i)) =
      (fun p : Σ i, β (f i) ↦ Sigma.mk _ (g _ p.2)) ⁻¹' s.sigma t := rfl
/-
**Set.sigma_preimage_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigma_preimage_left {f : ι' -> ι} : ((f ⁻¹' s).sigma fun i => t (f i)) = (
fun p : Σ i, α (f i) => Sigma.mk _ p.2) ⁻¹' s.sigma t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigma_preimage_left {f : ι' → ι} :
    ((f ⁻¹' s).sigma fun i ↦ t (f i)) = (fun p : Σ i, α (f i) ↦ Sigma.mk _ p.2) ⁻¹' s.sigma t :=
  rfl
/-
**Set.sigma_preimage_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigma_preimage_right {g : forall i, β i -> α i} : (s.sigma fun i => g i ⁻¹
' t i) = (fun p : Σ i, β i => Sigma.mk p.1 (g _ p.2)) ⁻¹' s.sigma t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigma_preimage_right {g : ∀ i, β i → α i} :
    (s.sigma fun i ↦ g i ⁻¹' t i) = (fun p : Σ i, β i ↦ Sigma.mk p.1 (g _ p.2)) ⁻¹' s.sigma t :=
  rfl
/-
**Set.preimage_sigmaMap_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_sigmaMap_sigma {α' : ι' -> Type*} (f : ι -> ι') (g : forall i, α 
i -> α' (f i)) (s : Set ι') (t : forall i, Set (α' i)) : Sigma.map f g ⁻¹' s.sig
ma t = (f ⁻¹' s).sigma fun i => g i ⁻¹' t (f i)
参数：f : ι -> ι'；g : forall i, α i -> α' (f i)；s : Set ι'；t : forall i, Set (α' i)
。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_sigmaMap_sigma {α' : ι' → Type*} (f : ι → ι') (g : ∀ i, α i → α' (f i))
    (s : Set ι') (t : ∀ i, Set (α' i)) :
    Sigma.map f g ⁻¹' s.sigma t = (f ⁻¹' s).sigma fun i ↦ g i ⁻¹' t (f i) := rfl

@[simp]
/-
**Set.mk_preimage_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_preimage_sigma (hi : i in s) : Sigma.mk i ⁻¹' s.sigma t = t i
参数：hi : i in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_preimage_sigma (hi : i ∈ s) : Sigma.mk i ⁻¹' s.sigma t = t i := by grind

@[simp]
/-
**Set.mk_preimage_sigma_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_preimage_sigma_eq_empty (hi : i ∉ s) : Sigma.mk i ⁻¹' s.sigma t = ∅
参数：hi : i ∉ s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_preimage_sigma_eq_empty (hi : i ∉ s) : Sigma.mk i ⁻¹' s.sigma t = ∅ := by grind
/-
**Set.mk_preimage_sigma_eq_if** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_preimage_sigma_eq_if [DecidablePred (· in s)] : Sigma.mk i ⁻¹' s.sigma 
t = if i in s then t i else ∅
参数：· in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_preimage_sigma_eq_if [DecidablePred (· ∈ s)] :
    Sigma.mk i ⁻¹' s.sigma t = if i ∈ s then t i else ∅ := by grind
/-
**Set.mk_preimage_sigma_fn_eq_if** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_preimage_sigma_fn_eq_if {β : Type*} [DecidablePred (· in s)] (g : β -> 
α i) : (fun b => Sigma.mk i (g b)) ⁻¹' s.sigma t = if i in s then g ⁻¹' t i else
 ∅
参数：· in s；g : β -> α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_preimage_sigma_fn_eq_if {β : Type*} [DecidablePred (· ∈ s)] (g : β → α i) :
    (fun b ↦ Sigma.mk i (g b)) ⁻¹' s.sigma t = if i ∈ s then g ⁻¹' t i else ∅ := by grind
/-
**Set.sigma_univ_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigma_univ_range_eq {f : forall i, α i -> β i} : (univ : Set ι).sigma (fun
 i => range (f i)) = range fun x : Σ i, α i => ⟨x.1, f _ x.2⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem sigma_univ_range_eq {f : ∀ i, α i → β i} :
    (univ : Set ι).sigma (fun i ↦ range (f i)) = range fun x : Σ i, α i ↦ ⟨x.1, f _ x.2⟩ :=
  ext <| by simp [range, Sigma.forall]
/-
**Set.Nonempty.sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} {s : Set ι} {t : (i : ι) → Set (α i)},
   s.Nonempty → (∀ (i : ι), (t i).Nonempty) → (s.sigma t).Nonempty
参数：i : ι；α i；∀ (i : ι), (t i).Nonempty；s.sigma t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Nonempty.sigma :
    s.Nonempty → (∀ i, (t i).Nonempty) → (s.sigma t).Nonempty := fun ⟨i, hi⟩ h ↦
  let ⟨a, ha⟩ := h i
  ⟨⟨i, a⟩, hi, ha⟩
/-
**Set.Nonempty.sigma_fst** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} {s : Set ι} {t : (i : ι) → Set (α i)},
 (s.sigma t).Nonempty → s.Nonempty
参数：i : ι；α i；s.sigma t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Nonempty.sigma_fst : (s.sigma t).Nonempty → s.Nonempty := fun ⟨x, hx⟩ ↦ ⟨x.1, hx.1⟩
/-
**Set.Nonempty.sigma_snd** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_3} {s : Set ι} {t : (i : ι) → Set (α i)},
   (s.sigma t).Nonempty → ∃ i ∈ s, (t i).Nonempty
参数：i : ι；α i；s.sigma t；t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Nonempty.sigma_snd : (s.sigma t).Nonempty → ∃ i ∈ s, (t i).Nonempty :=
  fun ⟨x, hx⟩ ↦ ⟨x.1, hx.1, x.2, hx.2⟩
/-
**Set.sigma_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigma_nonempty_iff : (s.sigma t).Nonempty ↔ exists i in s, (t i).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.sigma_snd`：∀ {ι : Type u_1} {α : ι → Type u_3} {s : Set ι} 
{t : (i : ι) → Set (α i)},   (s.sigma t).Nonempty → ∃ i ∈ s, (t i).Nonempty
-/
theorem sigma_nonempty_iff : (s.sigma t).Nonempty ↔ ∃ i ∈ s, (t i).Nonempty :=
  ⟨Nonempty.sigma_snd, fun ⟨i, hi, a, ha⟩ ↦ ⟨⟨i, a⟩, hi, ha⟩⟩
/-
**Set.sigma_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigma_eq_empty_iff : s.sigma t = ∅ ↔ forall i in s, t i = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.sigma_nonempty_iff`：sigma_nonempty_iff : (s.sigma t).Nonempty ↔ exis
ts i in s, (t i).Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sigma_eq_empty_iff : s.sigma t = ∅ ↔ ∀ i ∈ s, t i = ∅ :=
  not_nonempty_iff_eq_empty.symm.trans <|
    sigma_nonempty_iff.not.trans <| by
      simp only [not_nonempty_iff_eq_empty, not_and, not_exists]
/-
**Set.image_sigmaMk_subset_sigma_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_sigmaMk_subset_sigma_left {a : forall i, α i} (ha : forall i, a i in
 t i) : (fun i => Sigma.mk i (a i)) '' s subseteq s.sigma t
参数：ha : forall i, a i in t i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem image_sigmaMk_subset_sigma_left {a : ∀ i, α i} (ha : ∀ i, a i ∈ t i) :
    (fun i ↦ Sigma.mk i (a i)) '' s ⊆ s.sigma t :=
  image_subset_iff.2 fun _ hi ↦ ⟨hi, ha _⟩
/-
**Set.image_sigmaMk_subset_sigma_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_sigmaMk_subset_sigma_right (hi : i in s) : Sigma.mk i '' t i subsete
q s.sigma t
参数：hi : i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem image_sigmaMk_subset_sigma_right (hi : i ∈ s) : Sigma.mk i '' t i ⊆ s.sigma t :=
  image_subset_iff.2 fun _ ↦ And.intro hi
/-
**Set.sigma_subset_preimage_fst** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigma_subset_preimage_fst (s : Set ι) (t : forall i, Set (α i)) : s.sigma 
t subseteq Sigma.fst ⁻¹' s
参数：s : Set ι；t : forall i, Set (α i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem sigma_subset_preimage_fst (s : Set ι) (t : ∀ i, Set (α i)) : s.sigma t ⊆ Sigma.fst ⁻¹' s :=
  fun _ ↦ And.left
/-
**Set.fst_image_sigma_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：fst_image_sigma_subset (s : Set ι) (t : forall i, Set (α i)) : Sigma.fst '
' s.sigma t subseteq s
参数：s : Set ι；t : forall i, Set (α i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem fst_image_sigma_subset (s : Set ι) (t : ∀ i, Set (α i)) : Sigma.fst '' s.sigma t ⊆ s :=
  image_subset_iff.2 fun _ ↦ And.left
/-
**Set.image_sigma_eq_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_sigma_eq_iUnion {γ : Type*} (f : (Σ i, α i) -> γ) : f '' (s.sigma t)
 = ⋃ i in s, (f ∘ Sigma.mk i) '' t i
参数：f : (Σ i, α i) -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma image_sigma_eq_iUnion {γ : Type*} (f : (Σ i, α i) → γ) :
    f '' (s.sigma t) = ⋃ i ∈ s, (f ∘ Sigma.mk i) '' t i := by
  aesop
/-
**Set.fst_image_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：fst_image_sigma (s : Set ι) (ht : forall i, (t i).Nonempty) : Sigma.fst ''
 s.sigma t = s
参数：s : Set ι；ht : forall i, (t i).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.fst_image_sigma_subset`：fst_image_sigma_subset (s : Set ι) (t : fora
ll i, Set (α i)) : Sigma.fst '' s.sigma t subseteq s
-/
theorem fst_image_sigma (s : Set ι) (ht : ∀ i, (t i).Nonempty) : Sigma.fst '' s.sigma t = s :=
  (fst_image_sigma_subset _ _).antisymm fun i hi ↦
    let ⟨a, ha⟩ := ht i
    ⟨⟨i, a⟩, ⟨hi, ha⟩, rfl⟩
/-
**Set.sigma_sdiff_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sigma_sdiff_sigma : s₁.sigma t₁ \ s₂.sigma t₂ = s₁.sigma (t₁ \ t₂) union (
s₁ \ s₂).sigma t₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
theorem sigma_sdiff_sigma : s₁.sigma t₁ \ s₂.sigma t₂ = s₁.sigma (t₁ \ t₂) ∪ (s₁ \ s₂).sigma t₁ :=
  ext fun x ↦ by
    by_cases h₁ : x.1 ∈ s₁ <;> by_cases h₂ : x.2 ∈ t₁ x.1 <;> simp [*, ← imp_iff_or_not]

@[deprecated (since := "2026-06-03")] alias sigma_diff_sigma := sigma_sdiff_sigma
/-
**Set.sigma_eq_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sigma_eq_biUnion : s.sigma t = ⋃ i in s, Sigma.mk i '' t i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma sigma_eq_biUnion : s.sigma t = ⋃ i ∈ s, Sigma.mk i '' t i := by
  aesop
/-
**Set.uncurry_preimage_sigma_pi** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uncurry_preimage_sigma_pi {β : (i : ι) -> α i -> Type*} (s : Set ι) (t : (
i : ι) -> Set (α i)) (u : (p : (i : ι) × α i) -> Set (β p.1 p.2)) : Sigma.uncurr
y ⁻¹' (s.sigma t).pi u = s.pi (fun i => (t i).pi fun j => u ⟨i, j⟩)
参数：i : ι；s : Set ι；t : (i : ι) -> Set (α i)；u : (p : (i : ι) × α i) -> Set (β p.
1 p.2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma uncurry_preimage_sigma_pi {β : (i : ι) → α i → Type*} (s : Set ι) (t : (i : ι) → Set (α i))
    (u : (p : (i : ι) × α i) → Set (β p.1 p.2)) :
    Sigma.uncurry ⁻¹' (s.sigma t).pi u = s.pi (fun i ↦ (t i).pi fun j ↦ u ⟨i, j⟩) := by
  ext x
  simp only [mem_preimage, mem_pi, mem_sigma_iff, and_imp]
  exact ⟨fun h i hi j hj ↦ h ⟨i, j⟩ hi hj, fun h p hp1 hp2 ↦ h p.1 hp1 p.2 hp2⟩

end Set

