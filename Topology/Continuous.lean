/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
module

public import Mathlib.Topology.ClusterPt

/-!
# Continuity in topological spaces

For topological spaces `X` and `Y`, a function `f : X → Y` and a point `x : X`,
`ContinuousAt f x` means `f` is continuous at `x`, and global continuity is
`Continuous f`. There is also a version of continuity `PContinuous` for
partially defined functions.

## Tags

continuity, continuous function
-/

@[expose] public section

open Set Filter Topology

variable {X Y Z : Type*}

open TopologicalSpace

-- The curly braces are intentional, so this definition works well with simp
-- when topologies are not those provided by instances.
/-
**continuous_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_def {_ : TopologicalSpace X} {_ : TopologicalSpace Y} {f : X ->
 Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
-/
theorem continuous_def {_ : TopologicalSpace X} {_ : TopologicalSpace Y} {f : X → Y} :
    Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  ⟨fun hf => hf.1, fun h => ⟨h⟩⟩

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {f : X → Y} {s : Set X} {x : X} {y : Y}
/-
**IsOpen.preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : IsOpen t) : IsOpen (f
 ⁻¹' t)
参数：hf : Continuous f；h : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
-/
theorem IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : IsOpen t) :
    IsOpen (f ⁻¹' t) :=
  hf.isOpen_preimage t h
/-
**Equiv.continuous_symm_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Equiv.continuous_symm_iff (e : X ≃ Y) : Continuous e.symm ↔ IsOpenMap e
参数：e : X ≃ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Equiv.continuous_symm_iff (e : X ≃ Y) : Continuous e.symm ↔ IsOpenMap e := by
  simp_rw [continuous_def, ← Equiv.image_eq_preimage_symm, IsOpenMap]
/-
**Equiv.isOpenMap_symm_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Equiv.isOpenMap_symm_iff (e : X ≃ Y) : IsOpenMap e.symm ↔ Continuous e
参数：e : X ≃ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Equiv.isOpenMap_symm_iff (e : X ≃ Y) : IsOpenMap e.symm ↔ Continuous e := by
  simp_rw [← Equiv.continuous_symm_iff, Equiv.symm_symm]
/-
**continuous_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_congr {g : X -> Y} (h : forall x, f x = g x) : Continuous f ↔ C
ontinuous g
参数：h : forall x, f x = g x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem continuous_congr {g : X → Y} (h : ∀ x, f x = g x) :
    Continuous f ↔ Continuous g :=
  .of_eq <| congrArg _ <| funext h
/-
**Continuous.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.congr {g : X -> Y} (h : Continuous f) (h' : forall x, f x = g x
) : Continuous g
参数：h : Continuous f；h' : forall x, f x = g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_congr`：continuous_congr {g : X -> Y} (h : forall x, f x = g x
) : Continuous f ↔ Continuous g
-/
theorem Continuous.congr {g : X → Y} (h : Continuous f) (h' : ∀ x, f x = g x) : Continuous g :=
  continuous_congr h' |>.mp h
/-
**ContinuousAt.tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.tendsto (h : ContinuousAt f x) : Tendsto f (𝓝 x) (𝓝 (f x))
参数：h : ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContinuousAt.tendsto (h : ContinuousAt f x) :
    Tendsto f (𝓝 x) (𝓝 (f x)) :=
  h
/-
**continuousAt_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_def : ContinuousAt f x ↔ forall A in 𝓝 (f x), f ⁻¹' A in 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousAt_def : ContinuousAt f x ↔ ∀ A ∈ 𝓝 (f x), f ⁻¹' A ∈ 𝓝 x :=
  Iff.rfl
/-
**continuousAt_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_congr {g : X -> Y} (h : f =ᶠ[𝓝 x] g) : ContinuousAt f x ↔ Con
tinuousAt g x
参数：h : f =ᶠ[𝓝 x] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousAt_congr {g : X → Y} (h : f =ᶠ[𝓝 x] g) :
    ContinuousAt f x ↔ ContinuousAt g x := by
  simp only [ContinuousAt, tendsto_congr' h, h.eq_of_nhds]
/-
**ContinuousAt.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.congr {g : X -> Y} (hf : ContinuousAt f x) (h : f =ᶠ[𝓝 x] g) 
: ContinuousAt g x
参数：hf : ContinuousAt f x；h : f =ᶠ[𝓝 x] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousAt_congr`：continuousAt_congr {g : X -> Y} (h : f =ᶠ[𝓝 x] g) : 
ContinuousAt f x ↔ ContinuousAt g x
-/
theorem ContinuousAt.congr {g : X → Y} (hf : ContinuousAt f x) (h : f =ᶠ[𝓝 x] g) :
    ContinuousAt g x :=
  (continuousAt_congr h).1 hf
/-
**ContinuousAt.preimage_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.preimage_mem_nhds {t : Set Y} (h : ContinuousAt f x) (ht : t 
in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
参数：h : ContinuousAt f x；ht : t in 𝓝 (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContinuousAt.preimage_mem_nhds {t : Set Y} (h : ContinuousAt f x)
    (ht : t ∈ 𝓝 (f x)) : f ⁻¹' t ∈ 𝓝 x :=
  h ht

/-- If `f x ∈ s ∈ 𝓝 (f x)` for continuous `f`, then `f y ∈ s` near `x`.

This is essentially `Filter.Tendsto.eventually_mem`, but infers in more cases when applied. -/
/-
**ContinuousAt.eventually_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.eventually_mem {f : X -> Y} {x : X} (hf : ContinuousAt f x) {
s : Set Y} (hs : s in 𝓝 (f x)) : forallᶠ y in 𝓝 x, f y in s
参数：hf : ContinuousAt f x；hs : s in 𝓝 (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f x ∈ s ∈ 𝓝 (f x)` for continuous `f`, then `f y ∈ s` near `x`.

This is essentially `Filter.Tendsto.eventually_mem`, but infers in more cases wh
en applied.
-/
theorem ContinuousAt.eventually_mem {f : X → Y} {x : X} (hf : ContinuousAt f x) {s : Set Y}
    (hs : s ∈ 𝓝 (f x)) : ∀ᶠ y in 𝓝 x, f y ∈ s :=
  hf hs

/-- If a function `f` tends to somewhere other than `𝓝 (f x)` at `x`,
then `f` is not continuous at `x`
-/
/-
**not_continuousAt_of_tendsto** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_continuousAt_of_tendsto {f : X -> Y} {l₁ : Filter X} {l₂ : Filter Y} {
x : X} (hf : Tendsto f l₁ l₂) [l₁.NeBot] (hl₁ : l₁ <= 𝓝 x) (hl₂ : Disjoint (𝓝 (f
 x)) l₂) : ¬ ContinuousAt f x
参数：hf : Tendsto f l₁ l₂；hl₁ : l₁ <= 𝓝 x；hl₂ : Disjoint (𝓝 (f x)) l₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.not_tendsto`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{a : Filter α} {b₁ b₂ : Filter β},   Filter.Tendsto f a b₁ → ∀ [a.NeBot], Disjoi
nt b₁ b₂ → ¬Filt…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z

--- 原说明 ---
If a function `f` tends to somewhere other than `𝓝 (f x)` at `x`,
then `f` is not continuous at `x`
-/
lemma not_continuousAt_of_tendsto {f : X → Y} {l₁ : Filter X} {l₂ : Filter Y} {x : X}
    (hf : Tendsto f l₁ l₂) [l₁.NeBot] (hl₁ : l₁ ≤ 𝓝 x) (hl₂ : Disjoint (𝓝 (f x)) l₂) :
    ¬ ContinuousAt f x := fun cont ↦
  (cont.mono_left hl₁).not_tendsto hl₂ hf
/-
**ClusterPt.map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ClusterPt.map {lx : Filter X} {ly : Filter Y} (H : ClusterPt x lx) (hfc : 
ContinuousAt f x) (hf : Tendsto f lx ly) : ClusterPt (f x) ly
参数：H : ClusterPt x lx；hfc : ContinuousAt f x；hf : Tendsto f lx ly。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `Filter.NeBot.map`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α}, f.NeBo
t → ∀ (m : α → β), (Filter.map m f).NeBot
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
-/
theorem ClusterPt.map {lx : Filter X} {ly : Filter Y} (H : ClusterPt x lx)
    (hfc : ContinuousAt f x) (hf : Tendsto f lx ly) : ClusterPt (f x) ly :=
  (NeBot.map H f).mono <| hfc.tendsto.inf hf

/-- See also `interior_preimage_subset_preimage_interior`. -/
/-
**preimage_interior_subset_interior_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preimage_interior_subset_interior_preimage {t : Set Y} (hf : Continuous f)
 : f ⁻¹' interior t subseteq interior (f ⁻¹' t)
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)

--- 原说明 ---
See also `interior_preimage_subset_preimage_interior`.
-/
theorem preimage_interior_subset_interior_preimage {t : Set Y} (hf : Continuous f) :
    f ⁻¹' interior t ⊆ interior (f ⁻¹' t) :=
  interior_maximal (preimage_mono interior_subset) (isOpen_interior.preimage hf)
/-
**continuous_iff_preimage_interior_subset_interior_preimage** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：continuous_iff_preimage_interior_subset_interior_preimage : Continuous f ↔
 forall s, f ⁻¹' (interior s) subseteq interior (f ⁻¹' s) where mp h s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `preimage_interior_subset_interior_preimage`：preimage_interior_subset_int
erior_preimage {t : Set Y} (hf : Continuous f) : f ⁻¹' interior t subseteq inter
ior (f ⁻¹' t)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `subset_interior_iff_isOpen`：subset_interior_iff_isOpen : s subseteq inte
rior s ↔ IsOpen s
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
-/
theorem continuous_iff_preimage_interior_subset_interior_preimage :
    Continuous f ↔ ∀ s, f ⁻¹' (interior s) ⊆ interior (f ⁻¹' s) where
  mp h s := preimage_interior_subset_interior_preimage h
  mpr h := ⟨fun s hs ↦ subset_interior_iff_isOpen.mp <| by grw [← h, hs.interior_eq]⟩

@[continuity]
/-
**continuous_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_id : Continuous (fun x ↦ x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
-/
theorem continuous_id : Continuous (id : X → X) :=
  continuous_def.2 fun _ => id

-- This is needed due to reducibility issues with the `continuity` tactic.
@[continuity, fun_prop]
/-
**continuous_id'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_id' : Continuous (fun (x : X) => x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_id' : Continuous (fun (x : X) => x) := continuous_id
/-
**Continuous.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : Continuous f) : Con
tinuous (g ∘ f)
参数：hg : Continuous g；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
-/
theorem Continuous.comp {g : Y → Z} (hg : Continuous g) (hf : Continuous f) :
    Continuous (g ∘ f) :=
  continuous_def.2 fun _ h => (h.preimage hg).preimage hf

-- This is needed due to reducibility issues with the `continuity` tactic.
@[continuity, fun_prop]
/-
**Continuous.comp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf : Continuous f) : Co
ntinuous (fun x => g (f x))
参数：hg : Continuous g；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
-/
theorem Continuous.comp' {g : Y → Z} (hg : Continuous g) (hf : Continuous f) :
    Continuous (fun x => g (f x)) := hg.comp hf

@[fun_prop]
/-
**Continuous.iterate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.iterate {f : X -> X} (h : Continuous f) (n : Nat) : Continuous 
f^[n]
参数：h : Continuous f；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
-/
theorem Continuous.iterate {f : X → X} (h : Continuous f) (n : ℕ) : Continuous f^[n] :=
  Nat.recOn n continuous_id fun _ ihn => ihn.comp h

nonrec theorem ContinuousAt.comp {g : Y → Z} (hg : ContinuousAt g (f x))
    (hf : ContinuousAt f x) : ContinuousAt (g ∘ f) x :=
  hg.comp hf

@[fun_prop]
/-
**ContinuousAt.comp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.comp' {g : Y -> Z} {x : X} (hg : ContinuousAt g (f x)) (hf : 
ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x
参数：hg : ContinuousAt g (f x)；hf : ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
-/
theorem ContinuousAt.comp' {g : Y → Z} {x : X} (hg : ContinuousAt g (f x))
    (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x := ContinuousAt.comp hg hf

/-- See note [comp_of_eq lemmas] -/
/-
**ContinuousAt.comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.comp_of_eq {g : Y -> Z} (hg : ContinuousAt g y) (hf : Continu
ousAt f x) (hy : f x = y) : ContinuousAt (g ∘ f) x
参数：hg : ContinuousAt g y；hf : ContinuousAt f x；hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …

--- 原说明 ---
See note [comp_of_eq lemmas]
-/
theorem ContinuousAt.comp_of_eq {g : Y → Z} (hg : ContinuousAt g y)
    (hf : ContinuousAt f x) (hy : f x = y) : ContinuousAt (g ∘ f) x := by subst hy; exact hg.comp hf
/-
**Continuous.tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.tendsto (hf : Continuous f) (x) : Tendsto f (𝓝 x) (𝓝 (f x))
参数：hf : Continuous f；x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem Continuous.tendsto (hf : Continuous f) (x) : Tendsto f (𝓝 x) (𝓝 (f x)) :=
  ((nhds_basis_opens x).tendsto_iff <| nhds_basis_opens <| f x).2 fun t ⟨hxt, ht⟩ =>
    ⟨f ⁻¹' t, ⟨hxt, ht.preimage hf⟩, Subset.rfl⟩

/-- A version of `Continuous.tendsto` that allows one to specify a simpler form of the limit.
E.g., one can write `continuous_exp.tendsto' 0 1 exp_zero`. -/
/-
**Continuous.tendsto'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.tendsto' (hf : Continuous f) (x : X) (y : Y) (h : f x = y) : Te
ndsto f (𝓝 x) (𝓝 y)
参数：hf : Continuous f；x : X；y : Y；h : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))

--- 原说明 ---
A version of `Continuous.tendsto` that allows one to specify a simpler form of t
he limit.
E.g., one can write `continuous_exp.tendsto' 0 1 exp_zero`.
-/
theorem Continuous.tendsto' (hf : Continuous f) (x : X) (y : Y) (h : f x = y) :
    Tendsto f (𝓝 x) (𝓝 y) :=
  h ▸ hf.tendsto x

@[fun_prop]
/-
**Continuous.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.continuousAt (h : Continuous f) : ContinuousAt f x
参数：h : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
-/
theorem Continuous.continuousAt (h : Continuous f) : ContinuousAt f x :=
  h.tendsto x
/-
**continuous_iff_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_iff_continuousAt : Continuous f ↔ forall x, ContinuousAt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem continuous_iff_continuousAt : Continuous f ↔ ∀ x, ContinuousAt f x :=
  ⟨Continuous.tendsto, fun hf => continuous_def.2 fun _U hU => isOpen_iff_mem_nhds.2 fun x hx =>
    hf x <| hU.mem_nhds hx⟩

@[fun_prop]
/-
**continuousAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_const : ContinuousAt (fun _ : X => y) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem continuousAt_const : ContinuousAt (fun _ : X => y) x :=
  tendsto_const_nhds

@[continuity, fun_prop]
/-
**continuous_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_const (y : Y) : Continuous (fun x ↦ y)
参数：y : Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
-/
theorem continuous_const : Continuous fun _ : X => y :=
  continuous_iff_continuousAt.mpr fun _ => continuousAt_const
/-
**Filter.EventuallyEq.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.continuousAt (h : f =ᶠ[𝓝 x] fun _ => y) : ContinuousAt
 f x
参数：h : f =ᶠ[𝓝 x] fun _ => y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousAt_congr`：continuousAt_congr {g : X -> Y} (h : f =ᶠ[𝓝 x] g) : 
ContinuousAt f x ↔ ContinuousAt g x
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem Filter.EventuallyEq.continuousAt (h : f =ᶠ[𝓝 x] fun _ => y) :
    ContinuousAt f x :=
  (continuousAt_congr h).2 tendsto_const_nhds
/-
**continuous_of_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_of_const (h : forall x y, f x = f y) : Continuous f
参数：h : forall x y, f x = f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Filter.EventuallyEq.continuousAt`：Filter.EventuallyEq.continuousAt (h : 
f =ᶠ[𝓝 x] fun _ => y) : ContinuousAt f x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem continuous_of_const (h : ∀ x y, f x = f y) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x =>
    Filter.EventuallyEq.continuousAt <| Eventually.of_forall fun y => h y x
/-
**continuousAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_id : ContinuousAt id x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuousAt_id : ContinuousAt id x :=
  continuous_id.continuousAt

@[fun_prop]
/-
**continuousAt_id'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
参数：y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
-/
theorem continuousAt_id' (y) : ContinuousAt (fun x : X => x) y := continuousAt_id
/-
**ContinuousAt.iterate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.iterate {f : X -> X} (hf : ContinuousAt f x) (hx : f x = x) (
n : Nat) : ContinuousAt f^[n] x
参数：hf : ContinuousAt f x；hx : f x = x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
· 使用定理 `ContinuousAt.comp_of_eq`：ContinuousAt.comp_of_eq {g : Y -> Z} (hg : Cont
inuousAt g y) (hf : ContinuousAt f x) (hy : f x = y) : ContinuousAt (g ∘ f) x
-/
theorem ContinuousAt.iterate {f : X → X} (hf : ContinuousAt f x) (hx : f x = x) (n : ℕ) :
    ContinuousAt f^[n] x :=
  Nat.recOn n continuousAt_id fun _n ihn ↦ ihn.comp_of_eq hf hx
/-
**continuous_iff_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_iff_isClosed : Continuous f ↔ forall s, IsClosed s -> IsClosed 
(f ⁻¹' s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
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
theorem continuous_iff_isClosed : Continuous f ↔ ∀ s, IsClosed s → IsClosed (f ⁻¹' s) :=
  continuous_def.trans <| compl_surjective.forall.trans <| by
    simp only [isOpen_compl_iff, preimage_compl]
/-
**IsClosed.preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h : IsClosed t) : IsClo
sed (f ⁻¹' t)
参数：hf : Continuous f；h : IsClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_iff_isClosed`：continuous_iff_isClosed : Continuous f ↔ forall
 s, IsClosed s -> IsClosed (f ⁻¹' s)
-/
theorem IsClosed.preimage (hf : Continuous f) {t : Set Y} (h : IsClosed t) :
    IsClosed (f ⁻¹' t) :=
  continuous_iff_isClosed.mp hf t h
/-
**mem_closure_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_image (hf : ContinuousAt f x) (hx : x in closure s) : f x in c
losure (f '' s)
参数：hf : ContinuousAt f x；hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_closure_of_frequently_of_tendsto`：mem_closure_of_frequently_of_tends
to {f : α -> X} {b : Filter α} (h : existsᶠ x in b, f x in s) (hf : Tendsto f b 
(𝓝 x)) : x in closure s
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_frequently`：mem_closure_iff_frequently : x in closure s 
↔ existsᶠ x in 𝓝 x, x in s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem mem_closure_image (hf : ContinuousAt f x)
    (hx : x ∈ closure s) : f x ∈ closure (f '' s) :=
  mem_closure_of_frequently_of_tendsto
    ((mem_closure_iff_frequently.1 hx).mono fun _ => mem_image_of_mem _) hf
/-
**Continuous.closure_preimage_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.closure_preimage_subset (hf : Continuous f) (t : Set Y) : closu
re (f ⁻¹' t) subseteq f ⁻¹' closure t
参数：hf : Continuous f；t : Set Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Continuous.closure_preimage_subset (hf : Continuous f) (t : Set Y) :
    closure (f ⁻¹' t) ⊆ f ⁻¹' closure t := by
  rw [← (isClosed_closure.preimage hf).closure_eq]
  exact closure_mono (preimage_mono subset_closure)
/-
**Continuous.frontier_preimage_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.frontier_preimage_subset (hf : Continuous f) (t : Set Y) : fron
tier (f ⁻¹' t) subseteq f ⁻¹' frontier t
参数：hf : Continuous f；t : Set Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sdiff_subset_sdiff`：sdiff_subset_sdiff {s₁ s₂ t₁ t₂ : Set α} : s₁ su
bseteq s₂ -> t₂ subseteq t₁ -> s₁ \ t₁ subseteq s₂ \ t₂
· 使用定理 `Continuous.closure_preimage_subset`：Continuous.closure_preimage_subset (
hf : Continuous f) (t : Set Y) : closure (f ⁻¹' t) subseteq f ⁻¹' closure t
· 使用定理 `preimage_interior_subset_interior_preimage`：preimage_interior_subset_int
erior_preimage {t : Set Y} (hf : Continuous f) : f ⁻¹' interior t subseteq inter
ior (f ⁻¹' t)
-/
theorem Continuous.frontier_preimage_subset (hf : Continuous f) (t : Set Y) :
    frontier (f ⁻¹' t) ⊆ f ⁻¹' frontier t :=
  sdiff_subset_sdiff (hf.closure_preimage_subset t) (preimage_interior_subset_interior_preimage hf)

/-- If a continuous map `f` maps `s` to `t`, then it maps `closure s` to `closure t`. -/
/-
**Set.MapsTo.closure** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y} {s : Set X}   {t : Set Y}, Set.MapsTo f s t → Contin
uous f → Set.MapsTo f (closure s) (closure t)
参数：closure s；closure t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ClusterPt.map`：ClusterPt.map {lx : Filter X} {ly : Filter Y} (H : Cluste
rPt x lx) (hfc : ContinuousAt f x) (hf : Tendsto f lx ly) : ClusterPt (f x) ly
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_principal_principal`：tendsto_principal_principal {f : α -
> β} {s : Set α} {t : Set β} : Tendsto f (𝓟 s) (𝓟 t) ↔ forall a in s, f a in t

--- 原说明 ---
If a continuous map `f` maps `s` to `t`, then it maps `closure s` to `closure t`
.
-/
protected theorem Set.MapsTo.closure {t : Set Y} (h : MapsTo f s t)
    (hc : Continuous f) : MapsTo f (closure s) (closure t) := by
  simp only [MapsTo, mem_closure_iff_clusterPt]
  exact fun x hx => hx.map hc.continuousAt (tendsto_principal_principal.2 h)

/-- See also `IsClosedMap.closure_image_eq_of_continuous`. -/
/-
**image_closure_subset_closure_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_closure_subset_closure_image (h : Continuous f) : f '' closure s sub
seteq closure (f '' s)
参数：h : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `Set.MapsTo.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X}   {t : Set Y}, Set
.MapsTo …
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)

--- 原说明 ---
See also `IsClosedMap.closure_image_eq_of_continuous`.
-/
theorem image_closure_subset_closure_image (h : Continuous f) :
    f '' closure s ⊆ closure (f '' s) :=
  ((mapsTo_image f s).closure h).image_subset
/-
**closure_image_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_image_closure (h : Continuous f) : closure (f '' closure s) = clos
ure (f '' s)
参数：h : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem closure_image_closure (h : Continuous f) :
    closure (f '' closure s) = closure (f '' s) :=
  Subset.antisymm
    (closure_minimal (image_closure_subset_closure_image h) isClosed_closure)
    (closure_mono <| image_mono subset_closure)
/-
**closure_subset_preimage_closure_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_subset_preimage_closure_image (h : Continuous f) : closure s subse
teq f ⁻¹' closure (f '' s)
参数：h : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X}   {t : Set Y}, Set
.MapsTo …
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem closure_subset_preimage_closure_image (h : Continuous f) :
    closure s ⊆ f ⁻¹' closure (f '' s) :=
  (mapsTo_image _ _).closure h
/-
**nonempty_preimage_closure_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonempty_preimage_closure_image (h : Continuous f) (t : Set X) (ht : t.Non
empty) : (f ⁻¹' (closure (f '' t))).Nonempty
参数：h : Continuous f；t : Set X；ht : t.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `closure_subset_preimage_closure_image`：closure_subset_preimage_closure_i
mage (h : Continuous f) : closure s subseteq f ⁻¹' closure (f '' s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `closure_nonempty_iff`：closure_nonempty_iff : (closure s).Nonempty ↔ s.No
nempty
-/
lemma nonempty_preimage_closure_image (h : Continuous f) (t : Set X) (ht : t.Nonempty) :
    (f ⁻¹' (closure (f '' t))).Nonempty :=
  (Nonempty.mono (closure_subset_preimage_closure_image h (s := t)) (closure_nonempty_iff.mpr ht))
/-
**continuous_iff_image_closure_subset_closure_image** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：continuous_iff_image_closure_subset_closure_image : Continuous f ↔ forall 
s, f '' closure s subseteq closure (f '' s) where mp h s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_isClosed`：continuous_iff_isClosed : Continuous f ↔ forall
 s, IsClosed s -> IsClosed (f ⁻¹' s)
· 使用定理 `isClosed_of_closure_subset`：isClosed_of_closure_subset (h : closure s su
bseteq s) : IsClosed s
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `IsClosed.closure_subset`：IsClosed.closure_subset (hs : IsClosed s) : clo
sure s subseteq s
-/
theorem continuous_iff_image_closure_subset_closure_image :
    Continuous f ↔ ∀ s, f '' closure s ⊆ closure (f '' s) where
  mp h s := image_closure_subset_closure_image h
  mpr h := continuous_iff_isClosed.mpr fun s hs ↦ isClosed_of_closure_subset <| by
    grw [image_subset_iff.mp <| h <| f ⁻¹' s, image_preimage_subset, hs.closure_subset]
/-
**map_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mem_closure {t : Set Y} (hf : Continuous f) (hx : x in closure s) (ht 
: MapsTo f s t) : f x in closure t
参数：hf : Continuous f；hx : x in closure s；ht : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X}   {t : Set Y}, Set
.MapsTo …
-/
theorem map_mem_closure {t : Set Y} (hf : Continuous f)
    (hx : x ∈ closure s) (ht : MapsTo f s t) : f x ∈ closure t :=
  ht.closure hf hx

/-- If a continuous map `f` maps `s` to a closed set `t`, then it maps `closure s` to `t`. -/
/-
**Set.MapsTo.closure_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.MapsTo.closure_left {t : Set Y} (h : MapsTo f s t) (hc : Continuous f)
 (ht : IsClosed t) : MapsTo f (closure s) t
参数：h : MapsTo f s t；hc : Continuous f；ht : IsClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X}   {t : Set Y}, Set
.MapsTo …
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x

--- 原说明 ---
If a continuous map `f` maps `s` to a closed set `t`, then it maps `closure s` t
o `t`.
-/
theorem Set.MapsTo.closure_left {t : Set Y} (h : MapsTo f s t)
    (hc : Continuous f) (ht : IsClosed t) : MapsTo f (closure s) t :=
  ht.closure_eq ▸ h.closure hc
/-
**Filter.Tendsto.lift'_closure** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y},   Continuous f →     ∀ {l : Filter X} {l' : Filter 
Y}, Filter.Tendsto f l l' → Filter.Tendsto f (l.lift' closure) (l'.lift' closure
)
参数：l.lift' closure；l'.lift' closure。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.tendsto_lift'`：tendsto_lift' {m : γ -> β} {l : Filter γ} : Tendst
o m l (f.lift' h) ↔ forall s in f, forallᶠ a in l, m a in h s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.mem_lift'`：mem_lift' {t : Set α} (ht : t in f) : h t in f.lift' h
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.MapsTo.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X}   {t : Set Y}, Set
.MapsTo …
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
-/
theorem Filter.Tendsto.lift'_closure (hf : Continuous f) {l l'} (h : Tendsto f l l') :
    Tendsto f (l.lift' closure) (l'.lift' closure) :=
  tendsto_lift'.2 fun s hs ↦ by
    filter_upwards [mem_lift' (h hs)] using (mapsTo_preimage _ _).closure hf
/-
**tendsto_lift'_closure_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y},   Continuous f → ∀ (x : X), Filter.Tendsto f ((nhds
 x).lift' closure) ((nhds (f x)).lift' closure)
参数：x : X；(nhds x).lift' closure；(nhds (f x)).lift' closure。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.lift'_closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f →   
  ∀ {l : Filter X}…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
-/
theorem tendsto_lift'_closure_nhds (hf : Continuous f) (x : X) :
    Tendsto f ((𝓝 x).lift' closure) ((𝓝 (f x)).lift' closure) :=
  (hf.tendsto x).lift'_closure hf

/-!
### Function with dense range
-/

section DenseRange

variable {α ι : Type*} (f : α → X) (g : X → Y)
variable {f : α → X} {s : Set X}

/-- A surjective map has dense range. -/
/-
**Function.Surjective.denseRange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.denseRange (hf : Function.Surjective f) : DenseRange f
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x

--- 原说明 ---
A surjective map has dense range.
-/
theorem Function.Surjective.denseRange (hf : Function.Surjective f) : DenseRange f := fun x => by
  simp [hf.range_eq]
/-
**denseRange_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：denseRange_id : DenseRange (id : X -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
-/
theorem denseRange_id : DenseRange (id : X → X) :=
  Function.Surjective.denseRange Function.surjective_id
/-
**denseRange_iff_closure_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：denseRange_iff_closure_range : DenseRange f ↔ closure (range f) = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ
-/
theorem denseRange_iff_closure_range : DenseRange f ↔ closure (range f) = univ :=
  dense_iff_closure_eq
/-
**DenseRange.closure_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.closure_range (h : DenseRange f) : closure (range f) = univ
参数：h : DenseRange f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
-/
theorem DenseRange.closure_range (h : DenseRange f) : closure (range f) = univ :=
  h.closure_eq

@[simp]
/-
**denseRange_subtype_val** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：denseRange_subtype_val {p : X -> Prop} : DenseRange (@Subtype.val _ p) ↔ D
ense {x | p x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma denseRange_subtype_val {p : X → Prop} : DenseRange (@Subtype.val _ p) ↔ Dense {x | p x} := by
  simp [DenseRange]
/-
**Dense.denseRange_val** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.denseRange_val (h : Dense s) : DenseRange ((↑) : s -> X)
参数：h : Dense s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `denseRange_subtype_val`：denseRange_subtype_val {p : X -> Prop} : DenseRa
nge (@Subtype.val _ p) ↔ Dense {x | p x}
-/
theorem Dense.denseRange_val (h : Dense s) : DenseRange ((↑) : s → X) :=
  denseRange_subtype_val.2 h
/-
**Continuous.range_subset_closure_image_dense** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.range_subset_closure_image_dense {f : X -> Y} (hf : Continuous 
f) (hs : Dense s) : range f subseteq closure (f '' s)
参数：hf : Continuous f；hs : Dense s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
-/
theorem Continuous.range_subset_closure_image_dense {f : X → Y} (hf : Continuous f)
    (hs : Dense s) : range f ⊆ closure (f '' s) := by
  rw [← image_univ, ← hs.closure_eq]
  exact image_closure_subset_closure_image hf

/-- The image of a dense set under a continuous map with dense range is a dense set. -/
/-
**DenseRange.dense_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.dense_image {f : X -> Y} (hf' : DenseRange f) (hf : Continuous 
f) (hs : Dense s) : Dense (f '' s)
参数：hf' : DenseRange f；hf : Continuous f；hs : Dense s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.of_closure`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense (closure s) → Dense s
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `Continuous.range_subset_closure_image_dense`：Continuous.range_subset_clo
sure_image_dense {f : X -> Y} (hf : Continuous f) (hs : Dense s) : range f subse
teq closure (f '' s)

--- 原说明 ---
The image of a dense set under a continuous map with dense range is a dense set.
-/
theorem DenseRange.dense_image {f : X → Y} (hf' : DenseRange f) (hf : Continuous f)
    (hs : Dense s) : Dense (f '' s) :=
  (hf'.mono <| hf.range_subset_closure_image_dense hs).of_closure

/-- If `f` has dense range and `s` is an open set in the codomain of `f`, then the image of the
preimage of `s` under `f` is dense in `s`. -/
/-
**DenseRange.subset_closure_image_preimage_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：DenseRange.subset_closure_image_preimage_of_isOpen (hf : DenseRange f) (hs
 : IsOpen s) : s subseteq closure (f '' f ⁻¹' s)
参数：hf : DenseRange f；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Dense.open_subset_closure_inter`：Dense.open_subset_closure_inter (hs : D
ense s) (ht : IsOpen t) : t subseteq closure (t inter s)

--- 原说明 ---
If `f` has dense range and `s` is an open set in the codomain of `f`, then the i
mage of the
preimage of `s` under `f` is dense in `s`.
-/
theorem DenseRange.subset_closure_image_preimage_of_isOpen (hf : DenseRange f) (hs : IsOpen s) :
    s ⊆ closure (f '' f ⁻¹' s) := by
  rw [image_preimage_eq_inter_range]
  exact hf.open_subset_closure_inter hs

/-- If a continuous map with dense range maps a dense set to a subset of `t`, then `t` is a dense
set. -/
/-
**DenseRange.dense_of_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.dense_of_mapsTo {f : X -> Y} (hf' : DenseRange f) (hf : Continu
ous f) (hs : Dense s) {t : Set Y} (ht : MapsTo f s t) : Dense t
参数：hf' : DenseRange f；hf : Continuous f；hs : Dense s；ht : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `DenseRange.dense_image`：DenseRange.dense_image {f : X -> Y} (hf' : Dense
Range f) (hf : Continuous f) (hs : Dense s) : Dense (f '' s)

--- 原说明 ---
If a continuous map with dense range maps a dense set to a subset of `t`, then `
t` is a dense
set.
-/
theorem DenseRange.dense_of_mapsTo {f : X → Y} (hf' : DenseRange f) (hf : Continuous f)
    (hs : Dense s) {t : Set Y} (ht : MapsTo f s t) : Dense t :=
  (hf'.dense_image hf hs).mono ht.image_subset

/-- Composition of a continuous map with dense range and a function with dense range has dense
range. -/
/-
**DenseRange.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.comp {g : Y -> Z} {f : α -> Y} (hg : DenseRange g) (hf : DenseR
ange f) (cg : Continuous g) : DenseRange (g ∘ f)
参数：hg : DenseRange g；hf : DenseRange f；cg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DenseRange.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] {α : Type u_
1} (f : α → X), DenseRange f = Dense (Set.range f)
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `DenseRange.dense_image`：DenseRange.dense_image {f : X -> Y} (hf' : Dense
Range f) (hf : Continuous f) (hs : Dense s) : Dense (f '' s)

--- 原说明 ---
Composition of a continuous map with dense range and a function with dense range
 has dense
range.
-/
theorem DenseRange.comp {g : Y → Z} {f : α → Y} (hg : DenseRange g) (hf : DenseRange f)
    (cg : Continuous g) : DenseRange (g ∘ f) := by
  rw [DenseRange, range_comp]
  exact hg.dense_image cg hf

nonrec theorem DenseRange.nonempty_iff (hf : DenseRange f) : Nonempty α ↔ Nonempty X :=
  range_nonempty_iff_nonempty.symm.trans hf.nonempty_iff
/-
**DenseRange.nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.nonempty [h : Nonempty X] (hf : DenseRange f) : Nonempty α
参数：hf : DenseRange f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DenseRange.nonempty_iff`：∀ {X : Type u_1} [inst : TopologicalSpace X] {α
 : Type u_4} {f : α → X}, DenseRange f → (Nonempty α ↔ Nonempty X)
-/
theorem DenseRange.nonempty [h : Nonempty X] (hf : DenseRange f) : Nonempty α :=
  hf.nonempty_iff.mpr h

/-- Given a function `f : X → Y` with dense range and `y : Y`, returns some `x : X`. -/
/-
**DenseRange.some** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DenseRange.some (hf : DenseRange f) (x : X) : α
参数：hf : DenseRange f；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f : X → Y` with dense range and `y : Y`, returns some `x : X`.
-/
noncomputable def DenseRange.some (hf : DenseRange f) (x : X) : α :=
  Classical.choice <| hf.nonempty_iff.mpr ⟨x⟩

nonrec theorem DenseRange.exists_mem_open (hf : DenseRange f) (ho : IsOpen s) (hs : s.Nonempty) :
    ∃ a, f a ∈ s :=
  exists_range_iff.1 <| hf.exists_mem_open ho hs
/-
**DenseRange.mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.mem_nhds (h : DenseRange f) (hs : s in 𝓝 x) : exists a, f a in 
s
参数：h : DenseRange f；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.exists_mem_open`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 {α : Type u_4} {f : α → X} {s : Set X},   DenseRange f → IsOpen s → s.Nonempty 
→ ∃ a, f a ∈ s
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem DenseRange.mem_nhds (h : DenseRange f) (hs : s ∈ 𝓝 x) :
    ∃ a, f a ∈ s :=
  let ⟨a, ha⟩ := h.exists_mem_open isOpen_interior ⟨x, mem_interior_iff_mem_nhds.2 hs⟩
  ⟨a, interior_subset ha⟩

end DenseRange

library_note «continuity lemma statement» /--
The library contains many lemmas stating that functions/operations are continuous. There are many
ways to formulate the continuity of operations. Some are more convenient than others.
Note: for the most part this note also applies to other properties
(`Measurable`, `Differentiable`, `ContinuousOn`, ...).

### The traditional way
As an example, let's look at addition `(+) : M → M → M`. We can state that this is continuous
in different definitionally equal ways (omitting some typing information)
* `Continuous (fun p ↦ p.1 + p.2)`;
* `Continuous (Function.uncurry (+))`;
* `Continuous ↿(+)`. (`↿` is notation for recursively uncurrying a function)

However, lemmas with this conclusion are not nice to use in practice because
1. They confuse the elaborator. The following example fails, because of limitations in the
  elaboration process.
  ```
  variable {M : Type*} [Add M] [TopologicalSpace M] [ContinuousAdd M]
  example : Continuous (fun x : M ↦ x + x) :=
    continuous_add.comp _

  -- This example used to fail, but would be accepted if you wrote is as
  -- `continuous_add.comp (continuous_id.prodMk continuous_id :)`.
  example : Continuous (fun x : M ↦ x + x) :=
    continuous_add.comp (continuous_id.prodMk continuous_id)
  ```

2. If the operation has more than 2 arguments, they are impractical to use, because in your
  application the arguments in the domain might be in a different order or associated differently.

### The convenient way

A much more convenient way to write continuity lemmas is like `Continuous.add`:
```
Continuous.add {f g : X → M} (hf : Continuous f) (hg : Continuous g) :
  Continuous (f + g)
```
The conclusion can be `Continuous (fun x ↦ f x + g x)`, which is definitionally equal.
This has the following advantages
* It supports projection notation, so is shorter to write.
* `Continuous.add _ _` is recognized correctly by the elaborator and gives useful new goals.
* It works generally, since the domain is a variable.
  (Having a domain `Y × Z` would be less convenient in general.)

As an example for a unary operation, we have `Continuous.neg`.
```
Continuous.neg {f : X → G} (hf : Continuous f) : Continuous (-f)
```
For unary functions, the elaborator is not confused when applying the traditional lemma
(like `continuous_neg`), but it's still convenient to have the short version available (compare
`hf.neg.neg.neg` with `continuous_neg.comp <| continuous_neg.comp <| continuous_neg.comp hf`).

As a harder example, consider an operation of the following type:
```
def strans {x : F} (γ γ' : Path x x) (t₀ : I) : Path x x
```
The precise definition is not important, only its type.
The correct continuity principle for this operation is something like this:
```
{f : X → F} {γ γ' : ∀ x, Path (f x) (f x)} {t₀ s : X → I}
  (hγ : Continuous ↿γ) (hγ' : Continuous ↿γ')
  (ht : Continuous t₀) (hs : Continuous s) :
  Continuous (fun x ↦ strans (γ x) (γ' x) (t x) (s x))
```
Note that *all* arguments of `strans` are indexed over `X`, even the basepoint `x`, and the last
argument `s` that arises since `Path x x` has a coercion to `I → F`. The paths `γ` and `γ'` (which
are unary functions from `I`) become binary functions in the continuity lemma.

### Summary
* Make sure that your continuity lemmas are stated in the most general way, and in a convenient
  form. That means that:
  - The conclusion has a variable `X` as domain (not something like `Y × Z`);
  - Wherever possible, all point arguments `c : Y` are replaced by functions `c : X → Y`;
  - All `n`-ary function arguments are replaced by `n+1`-ary functions
    (`f : Y → Z` becomes `f : X → Y → Z`);
  - All (relevant) arguments have continuity assumptions, and perhaps there are additional
    assumptions needed to make the operation continuous;
  - The function in the conclusion is fully applied.
* These remarks are mostly about the format of the *conclusion* of a continuity lemma.
  In assumptions it's fine to state that a function with more than 1 argument is continuous using
  `↿` or `Function.uncurry`.

### Functions with discontinuities

In some cases, you want to work with discontinuous functions, and in certain expressions they are
still continuous. For example, consider the fractional part of a number, `Int.fract : ℝ → ℝ`.
In this case, you want to add conditions to when a function involving `fract` is continuous, so you
get something like this: (assumption `hf` could be weakened, but the important thing is the shape
of the conclusion)
```
lemma ContinuousOn.comp_fract {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → ℝ → Y} {g : X → ℝ} (hf : Continuous ↿f) (hg : Continuous g) (h : ∀ s, f s 0 = f s 1) :
    Continuous (fun x ↦ f x (fract (g x)))
```
With `ContinuousAt` you can be even more precise about what to prove in case of discontinuities,
see e.g. `ContinuousAt.comp_div_cases`.
-/

library_note «comp_of_eq lemmas» /--
Lean's elaborator has trouble elaborating applications of lemmas that state that the composition of
two functions satisfy some property at a point, like `ContinuousAt.comp` / `ContDiffAt.comp` and
`ContMDiffWithinAt.comp`. The reason is that a lemma like this looks like
`ContinuousAt g (f x) → ContinuousAt f x → ContinuousAt (g ∘ f) x`.
Since Lean's elaborator elaborates the arguments from left-to-right, when you write `hg.comp hf`,
the elaborator will try to figure out *both* `f` and `g` from the type of `hg`. It tries to figure
out `f` just from the point where `g` is continuous. For example, if `hg : ContinuousAt g (a, x)`
then the elaborator will assign `f` to the function `Prod.mk a`, since in that case `f x = (a, x)`.
This is undesirable in most cases where `f` is not a variable. There are some ways to work around
this, for example by giving `f` explicitly, or to force Lean to elaborate `hf` before elaborating
`hg`, but this is annoying.
Another better solution is to reformulate composition lemmas to have the following shape
`ContinuousAt g y → ContinuousAt f x → f x = y → ContinuousAt (g ∘ f) x`.
This is even useful if the proof of `f x = y` is `rfl`.
The reason that this works better is because the type of `hg` doesn't mention `f`.
Only after elaborating the two `ContinuousAt` arguments, Lean will try to unify `f x` with `y`,
which is often easy after having chosen the correct functions for `f` and `g`.
Here is an example that shows the difference:
```
example [TopologicalSpace X] [TopologicalSpace Y] {x₀ : X} (f : X → X → Y)
    (hf : ContinuousAt (Function.uncurry f) (x₀, x₀)) :
    ContinuousAt (fun x ↦ f x x) x₀ :=
  -- hf.comp (continuousAt_id.prod continuousAt_id) -- type mismatch
  -- hf.comp_of_eq (continuousAt_id.prod continuousAt_id) rfl -- works
```
-/

