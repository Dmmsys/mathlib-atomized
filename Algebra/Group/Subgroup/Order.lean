/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subsemigroup.Operations
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Basic
public import Mathlib.Order.Atoms

/-!
# Facts about ordered structures and ordered instances on subgroups
-/

public section

open Subgroup

@[to_additive (attr := simp)]
/-
**mabs_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mabs_mem_iff {S G} [Group G] [LinearOrder G] {_ : SetLike S G} [InvMemClas
s S G] {H : S} {x : G} : |x|ₘ in H ↔ x in H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mabs_choice`：∀ {α : Type u_1} [inst : Group α] [inst_1 : LinearOrder α] 
(x : α), |x|ₘ = x ∨ |x|ₘ = x⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mabs_mem_iff {S G} [Group G] [LinearOrder G] {_ : SetLike S G}
    [InvMemClass S G] {H : S} {x : G} : |x|ₘ ∈ H ↔ x ∈ H := by
  cases mabs_choice x <;> simp [*]

section ModularLattice

variable {C : Type*} [CommGroup C]

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsModularLattice (Subgroup C) :=
  ⟨fun {x} y z xz a ha => by
    rw [mem_inf, mem_sup] at ha
    rcases ha with ⟨⟨b, hb, c, hc, rfl⟩, haz⟩
    rw [mem_sup]
    exact ⟨b, hb, c, mem_inf.2 ⟨hc, (mul_mem_cancel_left (xz hb)).1 haz⟩, rfl⟩⟩

end ModularLattice

section Coatom
namespace Subgroup

variable {G : Type*} [Group G] (H : Subgroup G)

/-- In a group that satisfies the normalizer condition, every maximal subgroup is normal -/
/-
**Subgroup.NormalizerCondition.normal_of_coatom** 是 Mathlib 中的一个定理，位于命名空间 `Subgr
oup.NormalizerCondition`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), NormalizerCondition G 
→ IsCoatom H → H.Normal
参数：H : Subgroup G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.normalizer_eq_top_iff`：normalizer_eq_top_iff : normalizer (H : 
Set G) = ⊤ ↔ H.Normal
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
In a group that satisfies the normalizer condition, every maximal subgroup is no
rmal
-/
theorem NormalizerCondition.normal_of_coatom (hnc : NormalizerCondition G) (hmax : IsCoatom H) :
    H.Normal :=
  normalizer_eq_top_iff.mp (hmax.2 _ (hnc H (lt_top_iff_ne_top.mpr hmax.1)))

@[simp]
/-
**Subgroup.isCoatom_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：isCoatom_comap {H : Type*} [Group H] (f : G ≃* H) {K : Subgroup H} : IsCoa
tom (Subgroup.comap (f : G ->* H) K) ↔ IsCoatom K
参数：f : G ≃* H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isCoatom_iff`：isCoatom_iff [OrderTop α] [OrderTop β] (f : α ≃o 
β) (a : α) : IsCoatom (f a) ↔ IsCoatom a
-/
theorem isCoatom_comap {H : Type*} [Group H] (f : G ≃* H) {K : Subgroup H} :
    IsCoatom (Subgroup.comap (f : G →* H) K) ↔ IsCoatom K :=
  OrderIso.isCoatom_iff (f.comapSubgroup) K

@[simp]
/-
**Subgroup.isCoatom_map** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：isCoatom_map (f : G ≃* H) {K : Subgroup G} : IsCoatom (Subgroup.map (f : G
 ->* H) K) ↔ IsCoatom K
参数：f : G ≃* H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isCoatom_iff`：isCoatom_iff [OrderTop α] [OrderTop β] (f : α ≃o 
β) (a : α) : IsCoatom (f a) ↔ IsCoatom a
-/
theorem isCoatom_map (f : G ≃* H) {K : Subgroup G} :
    IsCoatom (Subgroup.map (f : G →* H) K) ↔ IsCoatom K :=
  OrderIso.isCoatom_iff (f.mapSubgroup) K
/-
**Subgroup.isCoatom_comap_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：isCoatom_comap_of_surjective {H : Type*} [Group H] {φ : G ->* H} (hφ : Fun
ction.Surjective φ) {M : Subgroup H} (hM : IsCoatom M) : IsCoatom (M.comap φ)
参数：hφ : Function.Surjective φ；hM : IsCoatom M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.comap_top`：comap_top (f : G ->* N) : (⊤ : Subgroup N).comap f =
 ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `Subgroup.comap_injective`：comap_injective {f : G ->* N} (h : Function.Su
rjective f) : Function.Injective (comap f)
· 使用定理 `Subgroup.comap_map_eq_self`：comap_map_eq_self {f : G ->* N} {H : Subgrou
p G} (h : f.ker <= H) : comap f (map f H) = H
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subgroup.ker_le_comap`：ker_le_comap (H : Subgroup N) : f.ker <= comap f 
H
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Subgroup.comap_lt_comap_of_surjective`：comap_lt_comap_of_surjective {f :
 G ->* N} {K L : Subgroup N} (hf : Function.Surjective f) : K.comap f < L.comap 
f ↔ K < L
-/
lemma isCoatom_comap_of_surjective
    {H : Type*} [Group H] {φ : G →* H} (hφ : Function.Surjective φ)
    {M : Subgroup H} (hM : IsCoatom M) : IsCoatom (M.comap φ) := by
  refine And.imp (fun hM ↦ ?_) (fun hM ↦ ?_) hM
  · rwa [← (comap_injective hφ).ne_iff, comap_top] at hM
  · intro K hK
    specialize hM (K.map φ)
    rw [← comap_lt_comap_of_surjective hφ, ← (comap_injective hφ).eq_iff] at hM
    rw [comap_map_eq_self ((M.ker_le_comap φ).trans hK.le), comap_top] at hM
    exact hM hK

end Subgroup
end Coatom

namespace Subgroup

variable {G : Type*}

/-- A subgroup of an ordered group is an ordered group. -/
@[to_additive
/-- An additive subgroup of an additive ordered group is an additive ordered group. -/]
/-
**Subgroup.toIsOrderedMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：toIsOrderedMonoid [CommGroup G] [Preorder G] [IsOrderedMonoid G] (H : Subg
roup G) : IsOrderedMonoid H
参数：H : Subgroup G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Injective.isOrderedMonoid`：Function.Injective.isOrderedMonoid [
IsOrderedMonoid α] [CommMonoid β] [Preorder β] (f : β -> α) (mul : forall x y, f
 (x * y) = f x * f y) (l…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
instance toIsOrderedMonoid [CommGroup G] [Preorder G] [IsOrderedMonoid G] (H : Subgroup G) :
    IsOrderedMonoid H :=
  Function.Injective.isOrderedMonoid Subtype.val (fun _ _ => rfl) .rfl

end Subgroup

@[to_additive]
/-
**Subsemigroup.strictMono_topEquiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subsemigroup.strictMono_topEquiv {G : Type*} [CommMonoid G] [Preorder G] :
 StrictMono (topEquiv (M
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Subsemigroup.strictMono_topEquiv {G : Type*} [CommMonoid G] [Preorder G] :
    StrictMono (topEquiv (M := G)) := fun _ _ ↦ id

@[to_additive]
/-
**MulEquiv.strictMono_subsemigroupCongr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulEquiv.strictMono_subsemigroupCongr {G : Type*} [CommMonoid G] [Preorder
 G] {S T : Subsemigroup G} (h : S = T) : StrictMono (subsemigroupCongr h)
参数：h : S = T。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MulEquiv.strictMono_subsemigroupCongr {G : Type*}
    [CommMonoid G] [Preorder G] {S T : Subsemigroup G}
    (h : S = T) : StrictMono (subsemigroupCongr h) := fun _ _ ↦ id

@[to_additive]
/-
**MulEquiv.strictMono_symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulEquiv.strictMono_symm {G G' : Type*} [CommMonoid G] [LinearOrder G] [Co
mmMonoid G'] [Preorder G'] {e : G ≃* G'} (he : StrictMono e) : StrictMono e.symm
参数：he : StrictMono e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma MulEquiv.strictMono_symm {G G' : Type*} [CommMonoid G] [LinearOrder G]
    [CommMonoid G'] [Preorder G'] {e : G ≃* G'} (he : StrictMono e) : StrictMono e.symm := by
  intro
  simp [← he.lt_iff_lt]
