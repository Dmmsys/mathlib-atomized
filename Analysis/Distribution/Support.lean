/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Distribution.Distribution

/-! # Support of distributions

We define the support of a distribution, `dsupport u`, as the intersection of all closed sets for
which `u` vanishes on the complement.
For this we also define a predicate `IsVanishingOn` that asserts that a map `f : F → V` vanishes on
`s : Set α` if for all `u : F` with `tsupport u ⊆ s` it follows that `f u = 0`.

These definitions work independently of a specific class of distributions (classical, tempered, or
compactly supported) and all basic properties are proved in an abstract setting using `FunLike`.

## Main definitions
* `IsVanishingOn`: A distribution vanishes on a set if it acts trivially on all test functions
  supported in that subset.
* `dsupport`: The support of a distribution is the intersection of all closed sets for which that
  distribution vanishes on the complement of the set.

## Main statements
* `dsupport_delta`: The support of the delta distribution is a single point. Available for tempered
  and classical distributions.

-/

@[expose] public noncomputable section

variable {ι α β 𝕜 E F F₁ F₂ R V : Type*}

open scoped Topology

namespace Distribution

section IsVanishingOn

variable [FunLike F α β] [TopologicalSpace α] [Zero β]

variable {f g : F → V} {s s₁ s₂ : Set α}

/-! ### Vanishing of distributions -/

section Zero

variable [Zero V]

/-- A distribution `f` vanishes on a set `s` if it vanishes for all test functions `u` with
`tsupport u ⊆ s`.

To make this definition work for all types of distributions, we define it for any function from
a `FunLike` type to a type with zero. -/
@[fun_prop]
/-
**Distribution.IsVanishingOn** 是 Mathlib 中的一个定义，位于命名空间 `Distribution`。
形式化陈述：IsVanishingOn (f : F -> V) (s : Set α) : Prop
参数：f : F -> V；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A distribution `f` vanishes on a set `s` if it vanishes for all test functions `
u` with
`tsupport u ⊆ s`.

To make this definition work for all types of distributions, we define it for an
y function from
a `FunLike` type to a type with zero.
-/
def IsVanishingOn (f : F → V) (s : Set α) : Prop :=
    ∀ (u : F), tsupport u ⊆ s → f u = 0

@[gcongr]
/-
**Distribution.IsVanishingOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Distribution.IsVani
shingOn`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {F : Type u_6} {V : Type u_10} [inst : Fun
Like F α β] [inst_1 : TopologicalSpace α]   [inst_2 : Zero β] {f : F → V} [inst_
3 : Zero V] ⦃s₁ s₂ : Set α⦄,   s₂ ⊆ s₁ → Distribution.IsVanishingOn f s₁ → Distr
ibution.IsVanishingOn f s₂
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem IsVanishingOn.mono ⦃s₁ s₂ : Set α⦄ (hs : s₂ ⊆ s₁) (hf : IsVanishingOn f s₁) :
    IsVanishingOn f s₂ :=
  (hf · <| ·.trans hs)
/-
**Distribution.not_isVanishingOn_mono** 是 Mathlib 中的一个定理，位于命名空间 `Distribution`。
形式化陈述：not_isVanishingOn_mono ⦃s₁ s₂ : Set α⦄ (hs : s₁ subseteq s₂) (hf : ¬ IsVan
ishingOn f s₁) : ¬ IsVanishingOn f s₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Distribution.IsVanishingOn.mono`：∀ {α : Type u_2} {β : Type u_3} {F : Ty
pe u_6} {V : Type u_10} [inst : FunLike F α β] [inst_1 : TopologicalSpace α]   [
inst_2 : Zero β] {f :…
-/
theorem not_isVanishingOn_mono ⦃s₁ s₂ : Set α⦄ (hs : s₁ ⊆ s₂) (hf : ¬ IsVanishingOn f s₁) :
    ¬ IsVanishingOn f s₂ :=
  (hf <| ·.mono hs)
/-
**Distribution.not_isVanishingOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Distribution`。
形式化陈述：not_isVanishingOn_iff : ¬ IsVanishingOn f s ↔ exists u : F, tsupport u sub
seteq s ∧ f u != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_isVanishingOn_iff :
    ¬ IsVanishingOn f s ↔ ∃ u : F, tsupport u ⊆ s ∧ f u ≠ 0 := by
  simp [IsVanishingOn]

end Zero

end IsVanishingOn

section dsupport

/-! ### Support -/

section Zero

variable [FunLike F α β] [TopologicalSpace α] [Zero β] [Zero V]

variable {f g : F → V} {s s₁ s₂ : Set α}

/-- The distributional support of `f` is the intersection of all closed sets `s` such that `f`
vanishes on the complement of `s`.

To make this definition work for all types of distributions, we define it for any function from
a `FunLike` type to a type with zero. -/
/-
**Distribution.dsupport** 是 Mathlib 中的一个定义，位于命名空间 `Distribution`。
形式化陈述：dsupport (f : F -> V) : Set α
参数：f : F -> V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distributional support of `f` is the intersection of all closed sets `s` suc
h that `f`
vanishes on the complement of `s`.

To make this definition work for all types of distributions, we define it for an
y function from
a `FunLike` type to a type with zero.
-/
def dsupport (f : F → V) : Set α := ⋂₀ { s | IsVanishingOn f sᶜ ∧ IsClosed s}
/-
**Distribution.mem_dsupport_iff** 是 Mathlib 中的一个定理，位于命名空间 `Distribution`。
形式化陈述：mem_dsupport_iff (x : α) : x in dsupport f ↔ forall (s : Set α), IsVanishi
ngOn f sᶜ -> IsClosed s -> x in s
参数：x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_dsupport_iff (x : α) :
    x ∈ dsupport f ↔ ∀ (s : Set α), IsVanishingOn f sᶜ → IsClosed s → x ∈ s := by
  simp [dsupport]

/-- The complement of the support is the largest open set on which `f` vanishes. -/
/-
**Distribution.dsupport_compl_eq** 是 Mathlib 中的一个定理，位于命名空间 `Distribution`。
形式化陈述：dsupport_compl_eq : (dsupport f)ᶜ = ⋃₀ { a | IsVanishingOn f a ∧ IsOpen a 
}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_sInter`：compl_sInter (S : Set (Set α)) : (⋂₀ S)ᶜ = ⋃₀ (compl '
' S)
· 使用定理 `Set.compl_image_ofPred`：compl_image_ofPred {p : Set α -> Prop} : compl '
' { s | p s } = { s | p sᶜ }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The complement of the support is the largest open set on which `f` vanishes.
-/
theorem dsupport_compl_eq : (dsupport f)ᶜ = ⋃₀ { a | IsVanishingOn f a ∧ IsOpen a } := by
  simp [dsupport, Set.compl_sInter, Set.compl_image_ofPred]

@[simp high]
/-
**Distribution.notMem_dsupport_iff** 是 Mathlib 中的一个定理，位于命名空间 `Distribution`。
形式化陈述：notMem_dsupport_iff (x : α) : x ∉ (dsupport f) ↔ exists (s : Set α), IsVan
ishingOn f s ∧ IsOpen s ∧ x in s
参数：x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Distribution.dsupport_compl_eq`：dsupport_compl_eq : (dsupport f)ᶜ = ⋃₀ {
 a | IsVanishingOn f a ∧ IsOpen a }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem notMem_dsupport_iff (x : α) :
    x ∉ (dsupport f) ↔ ∃ (s : Set α), IsVanishingOn f s ∧ IsOpen s ∧ x ∈ s := by
  simp [← Set.mem_compl_iff, dsupport_compl_eq, Set.mem_sUnion, and_assoc]
/-
**Distribution.mem_dsupport_iff_not_isVanishingOn** 是 Mathlib 中的一个定理，位于命名空间 `Dis
tribution`。
形式化陈述：mem_dsupport_iff_not_isVanishingOn (x : α) : x in dsupport f ↔ forall s, x
 in s -> IsOpen s -> ¬ IsVanishingOn f s
参数：x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_dsupport_iff_not_isVanishingOn (x : α) :
    x ∈ dsupport f ↔ ∀ s, x ∈ s → IsOpen s → ¬ IsVanishingOn f s := by
  grind only [notMem_dsupport_iff]
/-
**Distribution.mem_dsupport_iff_forall_exists_ne** 是 Mathlib 中的一个定理，位于命名空间 `Dist
ribution`。
形式化陈述：mem_dsupport_iff_forall_exists_ne (x : α) : x in dsupport f ↔ forall s, x 
in s -> IsOpen s -> exists u : F, tsupport u subseteq s ∧ f u != 0
参数：x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_dsupport_iff_forall_exists_ne (x : α) :
    x ∈ dsupport f ↔ ∀ s, x ∈ s → IsOpen s → ∃ u : F, tsupport u ⊆ s ∧ f u ≠ 0 := by
  simp_rw [mem_dsupport_iff_not_isVanishingOn, not_isVanishingOn_iff]
/-
**Distribution.mem_dsupport_iff_frequently** 是 Mathlib 中的一个定理，位于命名空间 `Distributi
on`。
形式化陈述：mem_dsupport_iff_frequently {x : α} : x in dsupport f ↔ existsᶠ u in (𝓝 x)
.smallSets, ¬ IsVanishingOn f u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.frequently_smallSets`：∀ {α : Type u_4} {ι : Sort u_5} {p
 : ι → Prop} {l : Filter α} {s : ι → Set α} {q : Set α → Prop} {hl : l.HasBasis 
p s},   (∀ ⦃s t : Set α⦄, …
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `Distribution.not_isVanishingOn_mono`：not_isVanishingOn_mono ⦃s₁ s₂ : Set
 α⦄ (hs : s₁ subseteq s₂) (hf : ¬ IsVanishingOn f s₁) : ¬ IsVanishingOn f s₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Distribution.mem_dsupport_iff_not_isVanishingOn`：mem_dsupport_iff_not_is
VanishingOn (x : α) : x in dsupport f ↔ forall s, x in s -> IsOpen s -> ¬ IsVani
shingOn f s
-/
theorem mem_dsupport_iff_frequently {x : α} :
    x ∈ dsupport f ↔ ∃ᶠ u in (𝓝 x).smallSets, ¬ IsVanishingOn f u := by
  rw [nhds_basis_opens x |>.frequently_smallSets not_isVanishingOn_mono]
  simpa using mem_dsupport_iff_not_isVanishingOn x
/-
**Distribution._root_.Filter.HasBasis.mem_dsupport** 是 Mathlib 中的一个定理，位于命名空间 `Di
stribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.HasBasis.mem_dsupport {ι : Sort*} {p : ι → Prop}
    {s : ι → Set α} {x : α} (hl : (𝓝 x).HasBasis p s) :
    x ∈ dsupport f ↔ ∀ (i : ι), p i → ¬ IsVanishingOn f (s i) := by
  rw [mem_dsupport_iff_frequently]
  exact hl.frequently_smallSets not_isVanishingOn_mono
/-
**Distribution.notMem_dsupport_iff_eventually** 是 Mathlib 中的一个定理，位于命名空间 `Distrib
ution`。
形式化陈述：notMem_dsupport_iff_eventually {x : α} : x ∉ dsupport f ↔ forallᶠ u in (𝓝 
x).smallSets, IsVanishingOn f u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem notMem_dsupport_iff_eventually {x : α} :
    x ∉ dsupport f ↔ ∀ᶠ u in (𝓝 x).smallSets, IsVanishingOn f u := by
  simp [mem_dsupport_iff_frequently]
/-
**Distribution._root_.Filter.HasBasis.notMem_dsupport** 是 Mathlib 中的一个定理，位于命名空间 
`Distribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.HasBasis.notMem_dsupport {ι : Sort*} {p : ι → Prop}
    {s : ι → Set α} {x : α} (hl : (𝓝 x).HasBasis p s) :
    x ∉ dsupport f ↔ ∃ i, p i ∧ IsVanishingOn f (s i) := by
  simp [hl.mem_dsupport]

@[gcongr only]
/-
**Distribution.dsupport_subset_dsupport** 是 Mathlib 中的一个定理，位于命名空间 `Distribution`
。
形式化陈述：dsupport_subset_dsupport (h : forall (s : Set α) (_ : IsOpen s), IsVanishi
ngOn g s -> IsVanishingOn f s) : dsupport f subseteq dsupport g
参数：h : forall (s : Set α) (_ : IsOpen s), IsVanishingOn g s -> IsVanishingOn f s
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sInter_mono`：∀ {α : Type u_1} {S T : Set (Set α)}, S ⊆ T → ⋂₀ T ⊆ ⋂₀
 S
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
-/
theorem dsupport_subset_dsupport
    (h : ∀ (s : Set α) (_ : IsOpen s), IsVanishingOn g s → IsVanishingOn f s) :
    dsupport f ⊆ dsupport g :=
  Set.sInter_mono fun s ⟨g_van, s_cl⟩ ↦ ⟨h sᶜ s_cl.isOpen_compl g_van, s_cl⟩

@[grind .]
/-
**Distribution.isClosed_dsupport** 是 Mathlib 中的一个定理，位于命名空间 `Distribution`。
形式化陈述：isClosed_dsupport : IsClosed (dsupport f)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isClosed_dsupport : IsClosed (dsupport f) := by
  grind [dsupport, isClosed_sInter]
/-
**Distribution.IsVanishingOn.disjoint_dsupport** 是 Mathlib 中的一个定理，位于命名空间 `Distri
bution.IsVanishingOn`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {F : Type u_6} {V : Type u_10} [inst : Fun
Like F α β] [inst_1 : TopologicalSpace α]   [inst_2 : Zero β] [inst_3 : Zero V] 
{f : F → V} {s : Set α},   Distribution.IsVanishingOn f s → IsOpen s → Disjoint 
s (Distribution.dsupport f)
参数：Distribution.dsupport f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.subset_compl_iff_disjoint_right`：subset_compl_iff_disjoint_right : s
 subseteq tᶜ ↔ Disjoint s t
· 使用定理 `Distribution.dsupport_compl_eq`：dsupport_compl_eq : (dsupport f)ᶜ = ⋃₀ {
 a | IsVanishingOn f a ∧ IsOpen a }
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
-/
theorem IsVanishingOn.disjoint_dsupport (h : IsVanishingOn f s) (s_open : IsOpen s) :
    Disjoint s (dsupport f) := by
  rw [← Set.subset_compl_iff_disjoint_right, dsupport_compl_eq]
  exact Set.subset_sUnion_of_mem ⟨h, s_open⟩

end Zero

end dsupport

section normed

variable [FunLike F α β] [PseudoMetricSpace α] [Zero β] [Zero V]

variable {f : F → V}

/-- The complement of the support is given by all *bounded* open sets on which `f` vanishes. -/
/-
**Distribution.compl_dsupport_eq_sUnion_isBounded** 是 Mathlib 中的一个定理，位于命名空间 `Dis
tribution`。
形式化陈述：compl_dsupport_eq_sUnion_isBounded : (dsupport f)ᶜ = ⋃₀ { a | IsVanishingO
n f a ∧ IsOpen a ∧ Bornology.IsBounded a }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b

--- 原说明 ---
The complement of the support is given by all *bounded* open sets on which `f` v
anishes.
-/
theorem compl_dsupport_eq_sUnion_isBounded :
    (dsupport f)ᶜ = ⋃₀ { a | IsVanishingOn f a ∧ IsOpen a ∧ Bornology.IsBounded a } := by
  ext x
  grind [(Metric.hasBasis_nhds_isOpen_isBounded x).notMem_dsupport]

end normed

/-! ## Tempered distributions -/

open SchwartzMap Distribution TemperedDistribution

namespace TemperedDistribution

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℂ F]

variable {f : 𝓢'(E, F)} {s : Set E}

namespace IsVanishingOn

open scoped Topology

@[fun_prop]
/-
**Distribution.TemperedDistribution.IsVanishingOn.smulLeftCLM** 是 Mathlib 中的一个定理
，位于命名空间 `Distribution.TemperedDistribution.IsVanishingOn`。
形式化陈述：smulLeftCLM (hf : IsVanishingOn f s) {g : E -> Complex} (hg : g.HasTempera
teGrowth) : IsVanishingOn (smulLeftCLM F g f) s
参数：hf : IsVanishingOn f s；hg : g.HasTemperateGrowth。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.smulLeftCLM_apply`：smulLeftCLM_apply {g : E -> 𝕜} (hg : g.Ha
sTemperateGrowth) (f : 𝓢(E, F)) : smulLeftCLM F g f = fun x => g x • f x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `tsupport_smul_subset_right`：tsupport_smul_subset_right {M α} [Zero α] [S
MulZeroClass M α] (f : X -> M) (g : X -> α) : (tsupport fun x => f x • g x) subs
eteq tsupport g
-/
theorem smulLeftCLM (hf : IsVanishingOn f s) {g : E → ℂ} (hg : g.HasTemperateGrowth) :
    IsVanishingOn (smulLeftCLM F g f) s := by
  intro u hu
  apply hf ((SchwartzMap.smulLeftCLM ℂ g) u)
  rw [SchwartzMap.smulLeftCLM_apply hg]
  exact (tsupport_smul_subset_right g u).trans hu

@[deprecated (since := "2026-07-01")] alias _root_.Distribution.IsVanishingOn.smulLeftCLM :=
  Distribution.TemperedDistribution.IsVanishingOn.smulLeftCLM

open LineDeriv

@[fun_prop]
/-
**Distribution.TemperedDistribution.IsVanishingOn.lineDerivOp** 是 Mathlib 中的一个定理
，位于命名空间 `Distribution.TemperedDistribution.IsVanishingOn`。
形式化陈述：lineDerivOp (hf : IsVanishingOn f s) (m : E) : IsVanishingOn (∂_{m} f : 𝓢'
(E, F)) s
参数：hf : IsVanishingOn f s；m : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `tsupport_fderiv_apply_subset`：tsupport_fderiv_apply_subset (v : E) : tsu
pport (fderiv 𝕜 f · v) subseteq tsupport f
-/
theorem lineDerivOp (hf : IsVanishingOn f s) (m : E) :
    IsVanishingOn (∂_{m} f : 𝓢'(E, F)) s := by
  intro u hu
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg, neg_eq_zero]
  exact hf (∂_{m} u) <| (tsupport_fderiv_apply_subset ℝ m).trans hu

@[fun_prop]
/-
**Distribution.TemperedDistribution.IsVanishingOn.iteratedLineDerivOp** 是 Mathli
b 中的一个定理，位于命名空间 `Distribution.TemperedDistribution.IsVanishingOn`。
形式化陈述：iteratedLineDerivOp {n : Nat} (hf : IsVanishingOn f s) (m : Fin n -> E) : 
IsVanishingOn (∂^{m} f : 𝓢'(E, F)) s
参数：hf : IsVanishingOn f s；m : Fin n -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Distribution.TemperedDistribution.IsVanishingOn.lineDerivOp`：lineDerivOp
 (hf : IsVanishingOn f s) (m : E) : IsVanishingOn (∂_{m} f : 𝓢'(E, F)) s
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem iteratedLineDerivOp {n : ℕ} (hf : IsVanishingOn f s) (m : Fin n → E) :
    IsVanishingOn (∂^{m} f : 𝓢'(E, F)) s := by
  induction n with
  | zero =>
    exact hf
  | succ n IH =>
    exact lineDerivOp (IH <| Fin.tail m) (m 0)

@[fun_prop]
/-
**Distribution.TemperedDistribution.IsVanishingOn._root_.TemperedDistribution.is
VanishingOn_delta** 是 Mathlib 中的一个定理，位于命名空间 `Distribution.TemperedDistribution.I
sVanishingOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.TemperedDistribution.isVanishingOn_delta (x : E) :
    IsVanishingOn (TemperedDistribution.delta x) {x}ᶜ := by
  intro u hu
  rw [Set.subset_compl_singleton_iff] at hu
  apply image_eq_zero_of_notMem_tsupport hu

end IsVanishingOn

section Support

/-
**Distribution.TemperedDistribution.dsupport_smulLeftCLM_subset** 是 Mathlib 中的一个
定理，位于命名空间 `Distribution.TemperedDistribution`。
形式化陈述：dsupport_smulLeftCLM_subset {g : E -> Complex} (hg : g.HasTemperateGrowth)
 : dsupport (smulLeftCLM F g f) subseteq dsupport f
参数：hg : g.HasTemperateGrowth。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Distribution.dsupport_subset_dsupport`：dsupport_subset_dsupport (h : for
all (s : Set α) (_ : IsOpen s), IsVanishingOn g s -> IsVanishingOn f s) : dsuppo
rt f subseteq dsupport g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Distribution.TemperedDistribution.IsVanishingOn.smulLeftCLM`：smulLeftCLM
 (hf : IsVanishingOn f s) {g : E -> Complex} (hg : g.HasTemperateGrowth) : IsVan
ishingOn (smulLeftCLM F g f) s
-/
theorem dsupport_smulLeftCLM_subset {g : E → ℂ} (hg : g.HasTemperateGrowth) :
    dsupport (smulLeftCLM F g f) ⊆ dsupport f := by
  gcongr; fun_prop

@[deprecated (since := "2026-07-01")] alias _root_.Distribution.dsupport_smulLeftCLM_subset :=
  Distribution.TemperedDistribution.dsupport_smulLeftCLM_subset

open LineDeriv
/-
**Distribution.TemperedDistribution.dsupport_lineDerivOp_subset** 是 Mathlib 中的一个
定理，位于命名空间 `Distribution.TemperedDistribution`。
形式化陈述：dsupport_lineDerivOp_subset (m : E) : dsupport (∂_{m} f : 𝓢'(E, F)) subset
eq dsupport f
参数：m : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Distribution.dsupport_subset_dsupport`：dsupport_subset_dsupport (h : for
all (s : Set α) (_ : IsOpen s), IsVanishingOn g s -> IsVanishingOn f s) : dsuppo
rt f subseteq dsupport g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Distribution.TemperedDistribution.IsVanishingOn.lineDerivOp`：lineDerivOp
 (hf : IsVanishingOn f s) (m : E) : IsVanishingOn (∂_{m} f : 𝓢'(E, F)) s
-/
theorem dsupport_lineDerivOp_subset (m : E) : dsupport (∂_{m} f : 𝓢'(E, F)) ⊆ dsupport f := by
  gcongr; fun_prop
/-
**Distribution.TemperedDistribution.dsupport_iteratedLineDerivOp_subset** 是 Math
lib 中的一个定理，位于命名空间 `Distribution.TemperedDistribution`。
形式化陈述：dsupport_iteratedLineDerivOp_subset {n : Nat} (m : Fin n -> E) : dsupport 
(∂^{m} f : 𝓢'(E, F)) subseteq dsupport f
参数：m : Fin n -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Distribution.dsupport_subset_dsupport`：dsupport_subset_dsupport (h : for
all (s : Set α) (_ : IsOpen s), IsVanishingOn g s -> IsVanishingOn f s) : dsuppo
rt f subseteq dsupport g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Distribution.TemperedDistribution.IsVanishingOn.iteratedLineDerivOp`：ite
ratedLineDerivOp {n : Nat} (hf : IsVanishingOn f s) (m : Fin n -> E) : IsVanishi
ngOn (∂^{m} f : 𝓢'(E, F)) s
-/
theorem dsupport_iteratedLineDerivOp_subset {n : ℕ} (m : Fin n → E) :
    dsupport (∂^{m} f : 𝓢'(E, F)) ⊆ dsupport f := by
  gcongr; fun_prop
/-
**Distribution.TemperedDistribution.dsupport_delta** 是 Mathlib 中的一个定理，位于命名空间 `Di
stribution.TemperedDistribution`。
形式化陈述：dsupport_delta [FiniteDimensional Real E] (x : E) : dsupport (TemperedDist
ribution.delta x) = {x}
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Distribution.mem_dsupport_iff`：mem_dsupport_iff (x : α) : x in dsupport 
f ↔ forall (s : Set α), IsVanishingOn f sᶜ -> IsClosed s -> x in s
· 使用定理 `TemperedDistribution.isVanishingOn_delta`：∀ {E : Type u_5} [inst : Norme
dAddCommGroup E] [inst_1 : NormedSpace ℝ E] (x : E),   Distribution.IsVanishingO
n ⇑(TemperedDistribution.delta…
· 使用定理 `T1Space.t1`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T1Space X
] (x : X), IsClosed {x}
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Distribution.mem_dsupport_iff_forall_exists_ne`：mem_dsupport_iff_forall_
exists_ne (x : α) : x in dsupport f ↔ forall s, x in s -> IsOpen s -> exists u :
 F, tsupport u subseteq s ∧ f u != 0
· 使用定理 `exists_contDiff_tsupport_subset`：exists_contDiff_tsupport_subset {s : Se
t E} {x : E} {n : Nat∞} (hs : s in 𝓝 x) : exists f : E -> Real, tsupport f subse
teq s ∧ HasCompactSup…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.mem_nhds_iff`：∀ {X : Type u} [inst : TopologicalSpace X] {x : X} 
{s : Set X}, IsOpen s → (s ∈ nhds x ↔ x ∈ s)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `tsupport_comp_subset`：∀ {X : Type u_1} {α : Type u_2} {β : Type u_4} [in
st : Zero α] [inst_1 : TopologicalSpace X] [inst_2 : Zero β]   {g : α → β}, g 0 
= 0 → ∀ (f…
· 使用定理 `HasCompactSupport.comp_left`：∀ {α : Type u_2} {β : Type u_4} {γ : Type u
_5} [inst : TopologicalSpace α] [inst_1 : Zero β] [inst_2 : Zero γ]   {g : β → γ
} {f : α → β}, Ha…
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `ContinuousLinearMap.contDiff`：ContinuousLinearMap.contDiff (f : E ->L[𝕜]
 F) : ContDiff 𝕜 n f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HasCompactSupport.toSchwartzMap_toFun`：∀ {E : Type u_5} {F : Type u_6} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommG
roup F]   [inst_3 : NormedS…
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem dsupport_delta [FiniteDimensional ℝ E] (x : E) :
    dsupport (TemperedDistribution.delta x) = {x} := by
  apply subset_antisymm
  · intro x' hx'
    rw [mem_dsupport_iff] at hx'
    exact hx' {x} (isVanishingOn_delta x) (T1Space.t1 x)
  rintro x rfl
  rw [mem_dsupport_iff_forall_exists_ne]
  intro s hx hs
  obtain ⟨u, h₁, h₂, h₃, -, h₄⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) ((IsOpen.mem_nhds_iff hs).mpr hx)
  have h₁' : tsupport (Complex.ofRealCLM ∘ u) ⊆ s := (tsupport_comp_subset rfl _).trans h₁
  have h₂' : HasCompactSupport (Complex.ofRealCLM ∘ u) := h₂.comp_left rfl
  use h₂'.toSchwartzMap (Complex.ofRealCLM.contDiff.comp h₃)
  exact ⟨h₁', by simp [h₄]⟩

end Support

end TemperedDistribution

/-! ## Classical distributions -/

open TopologicalSpace Distributions

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  {n : ℕ∞}

variable {f : 𝓓'(Ω, F)} {s : Set E}

namespace IsVanishingOn

open scoped Topology

open LineDeriv

@[fun_prop]
/-
**Distribution.IsVanishingOn.lineDerivOp** 是 Mathlib 中的一个定理，位于命名空间 `Distribution
.IsVanishingOn`。
形式化陈述：lineDerivOp (hf : IsVanishingOn f s) (m : E) : IsVanishingOn (∂_{m} f : 𝓓'
(Ω, F)) s
参数：hf : IsVanishingOn f s；m : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Distribution.lineDerivOp_apply_apply`：lineDerivOp_apply_apply (f : 𝓓'(Ω,
 F)) (g : 𝓓(Ω, Real)) (m : E) : ∂_{m} f g = f (- ∂_{m} g)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `tsupport_fderiv_apply_subset`：tsupport_fderiv_apply_subset (v : E) : tsu
pport (fderiv 𝕜 f · v) subseteq tsupport f
-/
theorem lineDerivOp (hf : IsVanishingOn f s) (m : E) :
    IsVanishingOn (∂_{m} f : 𝓓'(Ω, F)) s := by
  intro u hu
  simp only [Distribution.lineDerivOp_apply_apply, map_neg, neg_eq_zero]
  exact hf (∂_{m} u) <| (tsupport_fderiv_apply_subset ℝ m).trans hu

@[fun_prop]
/-
**Distribution.IsVanishingOn.iteratedLineDerivOp** 是 Mathlib 中的一个定理，位于命名空间 `Dist
ribution.IsVanishingOn`。
形式化陈述：iteratedLineDerivOp {n : Nat} (hf : IsVanishingOn f s) (m : Fin n -> E) : 
IsVanishingOn (∂^{m} f : 𝓓'(Ω, F)) s
参数：hf : IsVanishingOn f s；m : Fin n -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Distribution.IsVanishingOn.lineDerivOp`：lineDerivOp (hf : IsVanishingOn 
f s) (m : E) : IsVanishingOn (∂_{m} f : 𝓓'(Ω, F)) s
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem iteratedLineDerivOp {n : ℕ} (hf : IsVanishingOn f s) (m : Fin n → E) :
    IsVanishingOn (∂^{m} f : 𝓓'(Ω, F)) s := by
  induction n with
  | zero =>
    exact hf
  | succ n IH =>
    exact lineDerivOp (IH <| Fin.tail m) (m 0)

@[fun_prop]
/-
**Distribution.IsVanishingOn._root_.Distribution.isVanishingOn_delta** 是 Mathlib
 中的一个定理，位于命名空间 `Distribution.IsVanishingOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Distribution.isVanishingOn_delta (x : E) :
    IsVanishingOn (Distribution.delta x : 𝓓'^{n}(Ω, ℝ)) {x}ᶜ := by
  intro u hu
  rw [Set.subset_compl_singleton_iff] at hu
  apply image_eq_zero_of_notMem_tsupport hu

end IsVanishingOn

section Support

open LineDeriv

/-
**Distribution.dsupport_lineDerivOp_subset** 是 Mathlib 中的一个定理，位于命名空间 `Distributi
on`。
形式化陈述：dsupport_lineDerivOp_subset (m : E) : dsupport (∂_{m} f : 𝓓'(Ω, F)) subset
eq dsupport f
参数：m : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Distribution.dsupport_subset_dsupport`：dsupport_subset_dsupport (h : for
all (s : Set α) (_ : IsOpen s), IsVanishingOn g s -> IsVanishingOn f s) : dsuppo
rt f subseteq dsupport g
· 使用定理 `Distribution.IsVanishingOn.lineDerivOp`：lineDerivOp (hf : IsVanishingOn 
f s) (m : E) : IsVanishingOn (∂_{m} f : 𝓓'(Ω, F)) s
-/
theorem dsupport_lineDerivOp_subset (m : E) : dsupport (∂_{m} f : 𝓓'(Ω, F)) ⊆ dsupport f := by
  gcongr; fun_prop
/-
**Distribution.dsupport_iteratedLineDerivOp_subset** 是 Mathlib 中的一个定理，位于命名空间 `Di
stribution`。
形式化陈述：dsupport_iteratedLineDerivOp_subset {n : Nat} (m : Fin n -> E) : dsupport 
(∂^{m} f : 𝓓'(Ω, F)) subseteq dsupport f
参数：m : Fin n -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Distribution.dsupport_subset_dsupport`：dsupport_subset_dsupport (h : for
all (s : Set α) (_ : IsOpen s), IsVanishingOn g s -> IsVanishingOn f s) : dsuppo
rt f subseteq dsupport g
· 使用定理 `Distribution.IsVanishingOn.iteratedLineDerivOp`：iteratedLineDerivOp {n :
 Nat} (hf : IsVanishingOn f s) (m : Fin n -> E) : IsVanishingOn (∂^{m} f : 𝓓'(Ω,
 F)) s
-/
theorem dsupport_iteratedLineDerivOp_subset {n : ℕ} (m : Fin n → E) :
    dsupport (∂^{m} f : 𝓓'(Ω, F)) ⊆ dsupport f := by
  gcongr; fun_prop
/-
**Distribution.dsupport_delta** 是 Mathlib 中的一个定理，位于命名空间 `Distribution`。
形式化陈述：dsupport_delta [FiniteDimensional Real E] (x : E) (hx : x in Ω) : dsupport
 (Distribution.delta x : 𝓓'^{n}(Ω, Real)) = {x}
参数：x : E；hx : x in Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Distribution.mem_dsupport_iff`：mem_dsupport_iff (x : α) : x in dsupport 
f ↔ forall (s : Set α), IsVanishingOn f sᶜ -> IsClosed s -> x in s
· 使用定理 `Distribution.isVanishingOn_delta`：∀ {E : Type u_11} [inst : NormedAddCom
mGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {n : ℕ∞}   (
x : E), Distribution.I…
· 使用定理 `T1Space.t1`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T1Space X
] (x : X), IsClosed {x}
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Distribution.mem_dsupport_iff_forall_exists_ne`：mem_dsupport_iff_forall_
exists_ne (x : α) : x in dsupport f ↔ forall s, x in s -> IsOpen s -> exists u :
 F, tsupport u subseteq s ∧ f u != 0
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
· 使用定理 `exists_contDiff_tsupport_subset`：exists_contDiff_tsupport_subset {s : Se
t E} {x : E} {n : Nat∞} (hs : s in 𝓝 x) : exists f : E -> Real, tsupport f subse
teq s ∧ HasCompactSup…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.mem_nhds_iff`：∀ {X : Type u} [inst : TopologicalSpace X] {x : X} 
{s : Set X}, IsOpen s → (s ∈ nhds x ↔ x ∈ s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Distribution.delta_apply`：delta_apply (x : E) (f : 𝓓^{n}(Ω, Real)) : del
ta x f = f x
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem dsupport_delta [FiniteDimensional ℝ E] (x : E) (hx : x ∈ Ω) :
    dsupport (Distribution.delta x : 𝓓'^{n}(Ω, ℝ)) = {x} := by
  apply subset_antisymm
  · intro x' hx'
    rw [mem_dsupport_iff] at hx'
    exact hx' {x} (isVanishingOn_delta x) (T1Space.t1 x)
  rintro x rfl
  rw [mem_dsupport_iff_forall_exists_ne]
  intro s hxs hs
  set t := s ∩ Ω
  have ht : IsOpen t := hs.inter Ω.isOpen
  have htx : x ∈ t := Set.mem_inter hxs hx
  obtain ⟨u, h₁, h₂, h₃, -, h₄⟩ :=
    exists_contDiff_tsupport_subset (n := n) ((IsOpen.mem_nhds_iff ht).mpr htx)
  exact ⟨⟨u, h₃, h₂, by aesop⟩, ⟨by aesop, by simp [h₄]⟩⟩

end Support

end Distribution

