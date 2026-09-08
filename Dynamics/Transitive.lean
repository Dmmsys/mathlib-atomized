/-
Copyright (c) 2025 Daniel Figueroa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Figueroa
-/
module

public import Mathlib.Dynamics.Minimal

/-!
# Topologically transitive monoid actions

In this file we define an action of a monoid `M` on a topological space `α` to be
*topologically transitive* if for any pair of nonempty open sets `U` and `V` in `α` there exists an
`m : M` such that `(m • U) ∩ V` is nonempty. We also provide an additive version of this definition
and prove basic facts about topologically transitive actions.

## Tags

group action, topologically transitive
-/

public section


open scoped Pointwise

/-- An action of an additive monoid `M` on a topological space `α` is called
*topologically transitive* if for any pair of nonempty open sets `U` and `V` in `α` there exists an
`m : M` such that `(m +ᵥ U) ∩ V` is nonempty. -/
/-
**AddAction.IsTopologicallyTransitive** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddAction`。
形式化陈述：(M : Type u_1) → (α : Type u_2) → [inst : AddMonoid M] → [TopologicalSpace
 α] → [AddAction M α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An action of an additive monoid `M` on a topological space `α` is called
*topologically transitive* if for any pair of nonempty open sets `U` and `V` in 
`α` there exists an
`m : M` such that `(m +ᵥ U) ∩ V` is nonempty.
-/
class AddAction.IsTopologicallyTransitive (M α : Type*) [AddMonoid M] [TopologicalSpace α]
    [AddAction M α] : Prop where
  exists_vadd_inter : ∀ {U V : Set α}, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
    ∃ m : M, ((m +ᵥ U) ∩ V).Nonempty

/-- An action of a monoid `M` on a topological space `α` is called *topologically transitive* if for
any pair of nonempty open sets `U` and `V` in `α` there exists an `m : M` such that `(m • U) ∩ V` is
nonempty. -/
@[to_additive]
/-
**MulAction.IsTopologicallyTransitive** 是 Mathlib 中的一个归纳类型，位于命名空间 `MulAction`。
形式化陈述：(M : Type u_1) → (α : Type u_2) → [inst : Monoid M] → [TopologicalSpace α]
 → [MulAction M α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An action of a monoid `M` on a topological space `α` is called *topologically tr
ansitive* if for
any pair of nonempty open sets `U` and `V` in `α` there exists an `m : M` such t
hat `(m • U) ∩ V` is
nonempty.
-/
class MulAction.IsTopologicallyTransitive (M α : Type*) [Monoid M] [TopologicalSpace α]
    [MulAction M α] : Prop where
  exists_smul_inter : ∀ {U V : Set α}, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
    ∃ m : M, ((m • U) ∩ V).Nonempty

open MulAction Set

variable (M : Type*) {α : Type*} [TopologicalSpace α] [Monoid M] [MulAction M α]

section IsTopologicallyTransitive

@[to_additive]
/-
**MulAction.isTopologicallyTransitive_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulAction.isTopologicallyTransitive_iff : IsTopologicallyTransitive M α ↔ 
forall {U V : Set α}, IsOpen U -> U.Nonempty -> IsOpen V -> V.Nonempty -> exists
 m : M, ((m • U) inter V).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsTopologicallyTransitive.exists_smul_inter`：∀ {M : Type u_1} 
{α : Type u_2} {inst : Monoid M} {inst_1 : TopologicalSpace α} {inst_2 : MulActi
on M α}   [self : MulAction.IsTopologically…
-/
theorem MulAction.isTopologicallyTransitive_iff :
    IsTopologicallyTransitive M α ↔ ∀ {U V : Set α}, IsOpen U → U.Nonempty → IsOpen V →
    V.Nonempty → ∃ m : M, ((m • U) ∩ V).Nonempty := ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

/-- An action of a monoid `M` on `α` is topologically transitive if and only if for any nonempty
open subset `U` of `α` the union over the elements of `M` of images of `U` is dense in `α`. -/
@[to_additive /-- An action of an additive monoid `M` on `α` is topologically transitive if and only
if for any nonempty open subset `U` of `α` the union over the elements of `M` of images of `U` is
dense in `α`. -/]
/-
**MulAction.isTopologicallyTransitive_iff_dense_iUnion** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：MulAction.isTopologicallyTransitive_iff_dense_iUnion : IsTopologicallyTran
sitive M α ↔ forall {U : Set α}, IsOpen U -> U.Nonempty -> Dense (⋃ m : M, m • U
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
-/
theorem MulAction.isTopologicallyTransitive_iff_dense_iUnion :
    IsTopologicallyTransitive M α ↔
    ∀ {U : Set α}, IsOpen U → U.Nonempty → Dense (⋃ m : M, m • U) := by
  simp only [isTopologicallyTransitive_iff, inter_comm, dense_iff_inter_open, inter_iUnion,
    nonempty_iUnion]
  exact ⟨fun h _ h₁ h₂ _ h₃ h₄ ↦ h h₁ h₂ h₃ h₄, fun h _ _ h₁ h₂ h₃ h₄ ↦ h h₁ h₂ _ h₃ h₄⟩

/-- An action of a monoid `M` on `α` is topologically transitive if and only if for any nonempty
open subset `U` of `α` the union of the preimages of `U` over the elements of `M` is dense in `α`.
-/
@[to_additive /-- An action of an additive monoid `M` on `α` is topologically transitive if and only
if for any nonempty open subset `U` of `α` the union of the preimages of `U` over the elements of
`M` is dense in `α`. -/]
/-
**MulAction.isTopologicallyTransitive_iff_dense_iUnion_preimage** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：MulAction.isTopologicallyTransitive_iff_dense_iUnion_preimage : IsTopologi
callyTransitive M α ↔ forall {U : Set α}, IsOpen U -> U.Nonempty -> Dense (⋃ m :
 M, (m • ·) ⁻¹' U)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulAction.IsTopologicallyTransitive.exists_smul_inter`：∀ {M : Type u_1} 
{α : Type u_2} {inst : Monoid M} {inst_1 : TopologicalSpace α} {inst_2 : MulActi
on M α}   [self : MulAction.IsTopologically…
-/
theorem MulAction.isTopologicallyTransitive_iff_dense_iUnion_preimage :
    IsTopologicallyTransitive M α ↔
    ∀ {U : Set α}, IsOpen U → U.Nonempty → Dense (⋃ m : M, (m • ·) ⁻¹' U) := by
  simp only [dense_iff_inter_open, inter_iUnion, nonempty_iUnion, ← image_inter_nonempty_iff]
  exact ⟨fun h _ h₁ h₂ _ h₃ h₄ ↦ h.1 h₃ h₄ h₁ h₂, fun h ↦ ⟨fun h₁ h₂ h₃ h₄ ↦ h h₃ h₄ _ h₁ h₂⟩⟩

@[to_additive]
/-
**IsOpen.dense_iUnion_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.dense_iUnion_smul [h : IsTopologicallyTransitive M α] {U : Set α} (
hUo : IsOpen U) (hUne : U.Nonempty) : Dense (⋃ m : M, m • U)
参数：hUo : IsOpen U；hUne : U.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulAction.isTopologicallyTransitive_iff_dense_iUnion`：MulAction.isTopolo
gicallyTransitive_iff_dense_iUnion : IsTopologicallyTransitive M α ↔ forall {U :
 Set α}, IsOpen U -> U.Nonempty -> Dense (…
-/
theorem IsOpen.dense_iUnion_smul [h : IsTopologicallyTransitive M α] {U : Set α}
    (hUo : IsOpen U) (hUne : U.Nonempty) : Dense (⋃ m : M, m • U) :=
  (isTopologicallyTransitive_iff_dense_iUnion M).mp h hUo hUne

@[to_additive]
/-
**IsOpen.dense_iUnion_preimage_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.dense_iUnion_preimage_smul [h : IsTopologicallyTransitive M α] {U :
 Set α} (hUo : IsOpen U) (hUne : U.Nonempty) : Dense (⋃ m : M, (m • ·) ⁻¹' U)
参数：hUo : IsOpen U；hUne : U.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulAction.isTopologicallyTransitive_iff_dense_iUnion_preimage`：MulAction
.isTopologicallyTransitive_iff_dense_iUnion_preimage : IsTopologicallyTransitive
 M α ↔ forall {U : Set α}, IsOpen U -> U.Nonempty -…
-/
theorem IsOpen.dense_iUnion_preimage_smul [h : IsTopologicallyTransitive M α]
    {U : Set α} (hUo : IsOpen U) (hUne : U.Nonempty) : Dense (⋃ m : M, (m • ·) ⁻¹' U) :=
  (isTopologicallyTransitive_iff_dense_iUnion_preimage M).mp h hUo hUne

/-- Let `M` be a monoid with a topologically transitive action on `α`. If `U` is a nonempty open
subset of `α` and `(m • ·) ⁻¹' U ⊆ U` for all `m : M` then `U` is dense in `α`. -/
@[to_additive /-- Let `M` be an additive monoid with a topologically transitive action on `α`. If
`U` is a nonempty open subset of `α` and `(m +ᵥ ·) ⁻¹' U ⊆ U` for all `m : M` then `U` is dense in
`α`. -/]
/-
**IsOpen.dense_of_preimage_smul_invariant** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.dense_of_preimage_smul_invariant [IsTopologicallyTransitive M α] {U
 : Set α} (hUo : IsOpen U) (hUne : U.Nonempty) (hUinv : forall m : M, (m • ·) ⁻¹
' U subseteq U) : Dense U
参数：hUo : IsOpen U；hUne : U.Nonempty；hUinv : forall m : M, (m • ·) ⁻¹' U subseteq
 U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `IsOpen.dense_iUnion_preimage_smul`：IsOpen.dense_iUnion_preimage_smul [h 
: IsTopologicallyTransitive M α] {U : Set α} (hUo : IsOpen U) (hUne : U.Nonempty
) : Dense (⋃ m : M, (m …
-/
theorem IsOpen.dense_of_preimage_smul_invariant [IsTopologicallyTransitive M α] {U : Set α}
    (hUo : IsOpen U) (hUne : U.Nonempty) (hUinv : ∀ m : M, (m • ·) ⁻¹' U ⊆ U) : Dense U :=
  .mono (by simpa only [iUnion_subset_iff]) (hUo.dense_iUnion_preimage_smul M hUne)

/-- An action of a monoid `M` on `α` that is continuous in the second argument is topologically
transitive if and only if any nonempty open subset `U` of `α` with `(m • ·) ⁻¹' U ⊆ U` for all
`m : M` is dense in `α`. -/
@[to_additive /-- An action of an additive monoid `M` on `α` that is continuous in the second
argument is topologically transitive if and only if any nonempty open subset `U` of `α` with
`(m +ᵥ ·) ⁻¹' U ⊆ U` for all `m : M` is dense in `α`. -/]
/-
**MulAction.isTopologicallyTransitive_iff_dense_of_preimage_invariant** 是 Mathli
b 中的一个定理，位于命名空间 ``。
形式化陈述：MulAction.isTopologicallyTransitive_iff_dense_of_preimage_invariant [h : C
ontinuousConstSMul M α] : IsTopologicallyTransitive M α ↔ forall {U : Set α}, Is
Open U -> U.Nonempty -> (forall m : M, (m • ·) ⁻¹' U subseteq U) -> Dense U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.dense_of_preimage_smul_invariant`：IsOpen.dense_of_preimage_smul_i
nvariant [IsTopologicallyTransitive M α] {U : Set α} (hUo : IsOpen U) (hUne : U.
Nonempty) (hUinv : forall m :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulAction.isTopologicallyTransitive_iff_dense_iUnion_preimage`：MulAction
.isTopologicallyTransitive_iff_dense_iUnion_preimage : IsTopologicallyTransitive
 M α ↔ forall {U : Set α}, IsOpen U -> U.Nonempty -…
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
· 使用定理 `Set.nonempty_iUnion`：nonempty_iUnion : (⋃ i, s i).Nonempty ↔ exists i, (
s i).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
-/
theorem MulAction.isTopologicallyTransitive_iff_dense_of_preimage_invariant
    [h : ContinuousConstSMul M α] : IsTopologicallyTransitive M α ↔
    ∀ {U : Set α}, IsOpen U → U.Nonempty → (∀ m : M, (m • ·) ⁻¹' U ⊆ U) → Dense U := by
  refine ⟨fun _ _ h₀ h₁ h₂ ↦ h₀.dense_of_preimage_smul_invariant M h₁ h₂, fun h₄ ↦ ?_⟩
  refine (isTopologicallyTransitive_iff_dense_iUnion_preimage M).mpr ?_
  refine fun hU _ ↦ h₄ (isOpen_iUnion fun a ↦ hU.preimage (h.1 a)) ?_ fun b _ ↦ ?_
  · exact nonempty_iUnion.mpr ⟨1, by simpa only [one_smul]⟩
  · simp only [preimage_iUnion, mem_iUnion, mem_preimage, smul_smul, forall_exists_index]
    exact fun c hc ↦ ⟨c * b, hc⟩

@[to_additive]
/-
**MulAction.isTopologicallyTransitive_of_isMinimal** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulAction.isTopologicallyTransitive_of_isMinimal [IsMinimal M α] : IsTopol
ogicallyTransitive M α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulAction.isTopologicallyTransitive_iff_dense_iUnion_preimage`：MulAction
.isTopologicallyTransitive_iff_dense_iUnion_preimage : IsTopologicallyTransitive
 M α ↔ forall {U : Set α}, IsOpen U -> U.Nonempty -…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.iUnion_preimage_smul`：IsOpen.iUnion_preimage_smul [IsMinimal M α]
 {U : Set α} (hUo : IsOpen U) (hne : U.Nonempty) : ⋃ c : M, (c • ·) ⁻¹' U = univ
-/
instance MulAction.isTopologicallyTransitive_of_isMinimal [IsMinimal M α] :
    IsTopologicallyTransitive M α := by
  refine (isTopologicallyTransitive_iff_dense_iUnion_preimage M).mpr fun h hn ↦ ?_
  simp only [h.iUnion_preimage_smul M hn, dense_univ]

end IsTopologicallyTransitive

