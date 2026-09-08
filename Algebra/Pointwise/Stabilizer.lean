/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Stabilizer of a set under a pointwise action

This file characterises the stabilizer of a set/finset under the pointwise action of a group.
-/

public section

open Function MulOpposite Set
open scoped Pointwise

namespace MulAction
variable {G H α : Type*}

/-! ### Stabilizer of a set -/

section Set
section Group
variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

@[to_additive (attr := simp)]
/-
**MulAction.stabilizer_empty** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_empty : stabilizer G (∅ : Set α) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.coe_eq_univ`：coe_eq_univ {H : Subgroup G} : (H : Set G) = Set.u
niv ↔ H = ⊤
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Set.smul_set_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {a
 : α}, a • ∅ = ∅
-/
lemma stabilizer_empty : stabilizer G (∅ : Set α) = ⊤ :=
  Subgroup.coe_eq_univ.1 <| eq_univ_of_forall fun _a ↦ smul_set_empty

@[to_additive (attr := simp)]
/-
**MulAction.stabilizer_univ** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_univ : stabilizer G (Set.univ : Set α) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.smul_set_univ`：smul_set_univ : a • (univ : Set β) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma stabilizer_univ : stabilizer G (Set.univ : Set α) = ⊤ := by
  ext
  simp

@[to_additive (attr := simp)]
/-
**MulAction.stabilizer_singleton** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_singleton (b : α) : stabilizer G ({b} : Set α) = stabilizer G b
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.smul_set_singleton`：smul_set_singleton : a • ({b} : Set β) = {a • b}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma stabilizer_singleton (b : α) : stabilizer G ({b} : Set α) = stabilizer G b := by ext; simp

@[to_additive]
/-
**MulAction.mem_stabilizer_set** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：mem_stabilizer_set {s : Set α} : a in stabilizer G s ↔ forall b, a • b in 
s ↔ b in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.forall_congr'`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β →
 Prop} (e : α ≃ β),   (∀ (b : β), p (e.symm b) ↔ q b) → ((∀ (a : α), p a) ↔ ∀ (b
 : β), q …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulAction.toPerm_symm_apply`：∀ {α : Type u_5} {β : Type u_6} [inst : Gro
up α] [inst_1 : MulAction α β] (a : α) (x : β),   (Equiv.symm (MulAction.toPerm 
a)) x = a⁻¹ • x
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma mem_stabilizer_set {s : Set α} : a ∈ stabilizer G s ↔ ∀ b, a • b ∈ s ↔ b ∈ s := by
  refine mem_stabilizer_iff.trans ⟨fun h b ↦ ?_, fun h ↦ ?_⟩
  · rw [← (smul_mem_smul_set_iff : a • b ∈ _ ↔ _), h]
  simp_rw [Set.ext_iff, mem_smul_set_iff_inv_smul_mem]
  exact ((MulAction.toPerm a).forall_congr' <| by simp [Iff.comm]).1 h

@[to_additive]
/-
**MulAction.map_stabilizer_le** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：map_stabilizer_le (f : G ->* H) (s : Set G) : (stabilizer G s).map f <= st
abilizer H (f '' s)
参数：f : G ->* H；s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.image_smul_distrib`：image_smul_distrib [Mul α] [Mul β] [FunLike F α 
β] [MulHomClass F α β] (f : F) (a : α) (s : Set α) : f '' (a • s) = f a • f '' s
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
lemma map_stabilizer_le (f : G →* H) (s : Set G) :
    (stabilizer G s).map f ≤ stabilizer H (f '' s) := by
  rintro a
  simp only [Subgroup.mem_map, mem_stabilizer_iff, forall_exists_index, and_imp]
  rintro a ha rfl
  rw [← image_smul_distrib, ha]

@[to_additive (attr := simp)]
/-
**MulAction.stabilizer_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_mul_self (s : Set G) : (stabilizer G s : Set G) * s = s
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma stabilizer_mul_self (s : Set G) : (stabilizer G s : Set G) * s = s := by
  ext
  refine ⟨?_, fun h ↦ ⟨_, (stabilizer G s).one_mem, _, h, one_mul _⟩⟩
  rintro ⟨a, ha, b, hb, rfl⟩
  rw [← mem_stabilizer_iff.1 ha]
  exact smul_mem_smul_set hb

@[to_additive]
/-
**MulAction.stabilizer_inf_stabilizer_le_stabilizer_apply** 是 Mathlib 中的一个引理，位于命
名空间 `MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stabilizer_inf_stabilizer_le_stabilizer_apply₂ {f : Set α → Set α → Set α}
    (hf : ∀ a : G, a • f s t = f (a • s) (a • t)) :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (f s t) := by aesop (add simp [SetLike.le_def])

@[to_additive]
/-
**MulAction.stabilizer_inf_stabilizer_le_stabilizer_union** 是 Mathlib 中的一个引理，位于命
名空间 `MulAction`。
形式化陈述：stabilizer_inf_stabilizer_le_stabilizer_union : stabilizer G s ⊓ stabilize
r G t <= stabilizer G (s union t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.stabilizer_inf_stabilizer_le_stabilizer_apply₂`：stabilizer_inf
_stabilizer_le_stabilizer_apply₂ {f : Set α -> Set α -> Set α} (hf : forall a : 
G, a • f s t = f (a • s) (a • t)) : stabilizer…
· 使用引理 `Set.smul_set_union`：smul_set_union : a • (t₁ union t₂) = a • t₁ union a 
• t₂
-/
lemma stabilizer_inf_stabilizer_le_stabilizer_union :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (s ∪ t) :=
  stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ ↦ smul_set_union

@[to_additive]
/-
**MulAction.stabilizer_inf_stabilizer_le_stabilizer_inter** 是 Mathlib 中的一个引理，位于命
名空间 `MulAction`。
形式化陈述：stabilizer_inf_stabilizer_le_stabilizer_inter : stabilizer G s ⊓ stabilize
r G t <= stabilizer G (s inter t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.stabilizer_inf_stabilizer_le_stabilizer_apply₂`：stabilizer_inf
_stabilizer_le_stabilizer_apply₂ {f : Set α -> Set α -> Set α} (hf : forall a : 
G, a • f s t = f (a • s) (a • t)) : stabilizer…
· 使用定理 `Set.smul_set_inter`：smul_set_inter : a • (s inter t) = a • s inter a • t
-/
lemma stabilizer_inf_stabilizer_le_stabilizer_inter :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (s ∩ t) :=
  stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ ↦ smul_set_inter

@[to_additive]
/-
**MulAction.stabilizer_inf_stabilizer_le_stabilizer_sdiff** 是 Mathlib 中的一个引理，位于命
名空间 `MulAction`。
形式化陈述：stabilizer_inf_stabilizer_le_stabilizer_sdiff : stabilizer G s ⊓ stabilize
r G t <= stabilizer G (s \ t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.stabilizer_inf_stabilizer_le_stabilizer_apply₂`：stabilizer_inf
_stabilizer_le_stabilizer_apply₂ {f : Set α -> Set α -> Set α} (hf : forall a : 
G, a • f s t = f (a • s) (a • t)) : stabilizer…
· 使用定理 `Set.smul_set_sdiff`：smul_set_sdiff : a • (s \ t) = a • s \ a • t
-/
lemma stabilizer_inf_stabilizer_le_stabilizer_sdiff :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (s \ t) :=
  stabilizer_inf_stabilizer_le_stabilizer_apply₂ fun _ ↦ smul_set_sdiff

@[to_additive]
/-
**MulAction.stabilizer_union_eq_left** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_union_eq_left (hdisj : Disjoint s t) (hstab : stabilizer G s <=
 stabilizer G t) (hstab_union : stabilizer G (s union t) <= stabilizer G t) : st
abilizer G (s union t) = stabilizer G s
参数：hdisj : Disjoint s t；hstab : stabilizer G s <= stabilizer G t；hstab_union : s
tabilizer G (s union t) <= stabilizer G t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `MulAction.stabilizer_inf_stabilizer_le_stabilizer_sdiff`：stabilizer_inf_
stabilizer_le_stabilizer_sdiff : stabilizer G s ⊓ stabilizer G t <= stabilizer G
 (s \ t)
· 使用定理 `Set.union_sdiff_cancel_right`：union_sdiff_cancel_right {s t : Set α} (h 
: s inter t subseteq ∅) : (s union t) \ t = s
· 使用引理 `MulAction.stabilizer_inf_stabilizer_le_stabilizer_union`：stabilizer_inf_
stabilizer_le_stabilizer_union : stabilizer G s ⊓ stabilizer G t <= stabilizer G
 (s union t)
-/
lemma stabilizer_union_eq_left (hdisj : Disjoint s t) (hstab : stabilizer G s ≤ stabilizer G t)
    (hstab_union : stabilizer G (s ∪ t) ≤ stabilizer G t) :
    stabilizer G (s ∪ t) = stabilizer G s := by
  refine le_antisymm ?_ ?_
  · calc
      stabilizer G (s ∪ t)
        ≤ stabilizer G (s ∪ t) ⊓ stabilizer G t := by simpa
      _ ≤ stabilizer G ((s ∪ t) \ t) := stabilizer_inf_stabilizer_le_stabilizer_sdiff
      _ = stabilizer G s := by rw [union_sdiff_cancel_right]; simpa [← disjoint_iff_inter_eq_empty]
  · calc
      stabilizer G s
        ≤ stabilizer G s ⊓ stabilizer G t := by simpa
      _ ≤ stabilizer G (s ∪ t) := stabilizer_inf_stabilizer_le_stabilizer_union

@[to_additive]
/-
**MulAction.stabilizer_union_eq_right** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_union_eq_right (hdisj : Disjoint s t) (hstab : stabilizer G t <
= stabilizer G s) (hstab_union : stabilizer G (s union t) <= stabilizer G s) : s
tabilizer G (s union t) = stabilizer G t
参数：hdisj : Disjoint s t；hstab : stabilizer G t <= stabilizer G s；hstab_union : s
tabilizer G (s union t) <= stabilizer G s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用引理 `MulAction.stabilizer_union_eq_left`：stabilizer_union_eq_left (hdisj : Di
sjoint s t) (hstab : stabilizer G s <= stabilizer G t) (hstab_union : stabilizer
 G (s union t) <= stabil…
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
-/
lemma stabilizer_union_eq_right (hdisj : Disjoint s t) (hstab : stabilizer G t ≤ stabilizer G s)
    (hstab_union : stabilizer G (s ∪ t) ≤ stabilizer G s) :
    stabilizer G (s ∪ t) = stabilizer G t := by
  rw [union_comm, stabilizer_union_eq_left hdisj.symm hstab (union_comm .. ▸ hstab_union)]

variable {s : Set G}

open scoped RightActions in
@[to_additive]
/-
**MulAction.op_smul_set_stabilizer_subset** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：op_smul_set_stabilizer_subset (ha : a in s) : (stabilizer G s : Set G) <• 
a subseteq s
参数：ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.smul_set_subset_iff`：smul_set_subset_iff : a • s subseteq t ↔ forall
 ⦃b⦄, b in s -> a • b in t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
lemma op_smul_set_stabilizer_subset (ha : a ∈ s) : (stabilizer G s : Set G) <• a ⊆ s :=
  smul_set_subset_iff.2 fun b hb ↦ by rw [← hb]; exact smul_mem_smul_set ha

@[to_additive]
/-
**MulAction.stabilizer_subset_div_right** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_subset_div_right (ha : a in s) : ↑(stabilizer G s) subseteq s /
 {a}
参数：ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MulAction.mem_stabilizer_set`：mem_stabilizer_set {s : Set α} : a in stab
ilizer G s ↔ forall b, a • b in s ↔ b in s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `mul_div_cancel_right`：mul_div_cancel_right (a b : G) : a * b / b = a
-/
lemma stabilizer_subset_div_right (ha : a ∈ s) : ↑(stabilizer G s) ⊆ s / {a} := fun b hb ↦
  ⟨_, by rwa [← smul_eq_mul, mem_stabilizer_set.1 hb], _, mem_singleton _, mul_div_cancel_right _ _⟩

@[to_additive]
/-
**MulAction.stabilizer_finite** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_finite (hs₀ : s.Nonempty) (hs : s.Finite) : (stabilizer G s : S
et G).Finite
参数：hs₀ : s.Nonempty；hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.div`：∀ {α : Type u_2} [inst : Div α] {s t : Set α}, s.Finite 
→ t.Finite → (s / t).Finite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用引理 `MulAction.stabilizer_subset_div_right`：stabilizer_subset_div_right (ha :
 a in s) : ↑(stabilizer G s) subseteq s / {a}
-/
lemma stabilizer_finite (hs₀ : s.Nonempty) (hs : s.Finite) : (stabilizer G s : Set G).Finite := by
  obtain ⟨a, ha⟩ := hs₀
  exact (hs.div <| finite_singleton _).subset <| stabilizer_subset_div_right ha

end Group

section CommGroup
variable [CommGroup G] {s t : Set G} {a : G}

@[to_additive]
/-
**MulAction.smul_set_stabilizer_subset** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：smul_set_stabilizer_subset (ha : a in s) : a • (stabilizer G s : Set G) su
bseteq s
参数：ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用引理 `MulAction.op_smul_set_stabilizer_subset`：op_smul_set_stabilizer_subset (
ha : a in s) : (stabilizer G s : Set G) <• a subseteq s
-/
lemma smul_set_stabilizer_subset (ha : a ∈ s) : a • (stabilizer G s : Set G) ⊆ s := by
  simpa using op_smul_set_stabilizer_subset ha

end CommGroup
end Set

variable [Group G] [Group H] [MulAction G α] {a : G}

/-! ### Stabilizer of a subgroup -/

section Subgroup

-- TODO: Is there a lemma that could unify the following three very similar lemmas?

@[to_additive (attr := simp)]
/-
**MulAction.stabilizer_subgroup** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_subgroup (s : Subgroup G) : stabilizer G (s : Set G) = s
参数：s : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `Subgroup.mul_mem_cancel_left`：∀ {G : Type u_1} [inst : Group G] (H : Sub
group G) {x y : G}, x ∈ H → (x * y ∈ H ↔ y ∈ H)
-/
lemma stabilizer_subgroup (s : Subgroup G) : stabilizer G (s : Set G) = s := by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  refine fun a ↦ ⟨fun h ↦ ?_, fun ha b ↦ s.mul_mem_cancel_left ha⟩
  simpa only [smul_eq_mul, SetLike.mem_coe, mul_one] using (h 1).2 s.one_mem

@[to_additive (attr := simp)]
/-
**MulAction.stabilizer_op_subgroup** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_op_subgroup (s : Subgroup G) : stabilizer Gᵐᵒᵖ (s : Set G) = s.
op
参数：s : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `Subgroup.mul_mem_cancel_right`：∀ {G : Type u_1} [inst : Group G] (H : Su
bgroup G) {x y : G}, x ∈ H → (y * x ∈ H ↔ y ∈ H)
-/
lemma stabilizer_op_subgroup (s : Subgroup G) : stabilizer Gᵐᵒᵖ (s : Set G) = s.op := by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  simp only [smul_eq_mul_unop, SetLike.mem_coe, Subgroup.mem_op, «forall», unop_op]
  refine fun a ↦ ⟨fun h ↦ ?_, fun ha b ↦ s.mul_mem_cancel_right ha⟩
  simpa only [op_smul_eq_mul, SetLike.mem_coe, one_mul] using (h 1).2 s.one_mem

@[to_additive (attr := simp)]
/-
**MulAction.stabilizer_subgroup_op** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_subgroup_op (s : Subgroup Gᵐᵒᵖ) : stabilizer G (s : Set Gᵐᵒᵖ) =
 s.unop
参数：s : Subgroup Gᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Subgroup.mul_mem_cancel_right`：∀ {G : Type u_1} [inst : Group G] (H : Su
bgroup G) {x y : G}, x ∈ H → (y * x ∈ H ↔ y ∈ H)
-/
lemma stabilizer_subgroup_op (s : Subgroup Gᵐᵒᵖ) : stabilizer G (s : Set Gᵐᵒᵖ) = s.unop := by
  simp_rw [SetLike.ext_iff, mem_stabilizer_set]
  refine fun a ↦ ⟨fun h ↦ ?_, fun ha b ↦ s.mul_mem_cancel_right ha⟩
  have : 1 * MulOpposite.op a ∈ s := (h 1).2 s.one_mem
  simpa only [op_smul_eq_mul, SetLike.mem_coe, one_mul] using! this

end Subgroup

/-! ### Stabilizer of a finset -/

section Finset
variable [DecidableEq α]

@[to_additive (attr := simp, norm_cast)]
/-
**MulAction.stabilizer_coe_finset** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_coe_finset (s : Finset α) : stabilizer G (s : Set α) = stabiliz
er G s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma stabilizer_coe_finset (s : Finset α) : stabilizer G (s : Set α) = stabilizer G s := by
  ext; simp [← Finset.coe_inj]

@[to_additive (attr := simp)]
/-
**MulAction.stabilizer_finset_empty** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_finset_empty : stabilizer G (∅ : Finset α) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.coe_eq_univ`：coe_eq_univ {H : Subgroup G} : (H : Set G) = Set.u
niv ↔ H = ⊤
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用引理 `Finset.smul_finset_empty`：smul_finset_empty (a : α) : a • (∅ : Finset β)
 = ∅
-/
lemma stabilizer_finset_empty : stabilizer G (∅ : Finset α) = ⊤ :=
  Subgroup.coe_eq_univ.1 <| eq_univ_of_forall Finset.smul_finset_empty

@[to_additive (attr := simp)]
/-
**MulAction.stabilizer_finset_univ** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_finset_univ [Fintype α] : stabilizer G (Finset.univ : Finset α)
 = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.smul_finset_univ`：smul_finset_univ [Fintype β] : a • (univ : Fins
et β) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma stabilizer_finset_univ [Fintype α] : stabilizer G (Finset.univ : Finset α) = ⊤ := by
  ext
  simp

@[to_additive (attr := simp)]
/-
**MulAction.stabilizer_finset_singleton** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_finset_singleton (b : α) : stabilizer G ({b} : Finset α) = stab
ilizer G b
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.smul_finset_singleton`：smul_finset_singleton (b : β) : a • ({b} :
 Finset β) = {a • b}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma stabilizer_finset_singleton (b : α) : stabilizer G ({b} : Finset α) = stabilizer G b := by
  ext; simp

@[to_additive]
/-
**MulAction.mem_stabilizer_finset** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：mem_stabilizer_finset {s : Finset α} : a in stabilizer G s ↔ forall b, a •
 b in s ↔ b in s
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_stabilizer_finset {s : Finset α} : a ∈ stabilizer G s ↔ ∀ b, a • b ∈ s ↔ b ∈ s := by
  simp_rw [← stabilizer_coe_finset, mem_stabilizer_set, Finset.mem_coe]

@[to_additive]
/-
**MulAction.mem_stabilizer_finset_iff_subset_smul_finset** 是 Mathlib 中的一个引理，位于命名
空间 `MulAction`。
形式化陈述：mem_stabilizer_finset_iff_subset_smul_finset {s : Finset α} : a in stabili
zer G s ↔ s subseteq a • s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `Finset.subset_iff_eq_of_card_le`：subset_iff_eq_of_card_le (h : #t <= #s)
 : s subseteq t ↔ s = t
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.card_smul_finset`：card_smul_finset (a : α) (s : Finset β) : (a • 
s).card = s.card
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_stabilizer_finset_iff_subset_smul_finset {s : Finset α} :
    a ∈ stabilizer G s ↔ s ⊆ a • s := by
  rw [mem_stabilizer_iff, Finset.subset_iff_eq_of_card_le (Finset.card_smul_finset _ _).le, eq_comm]

@[to_additive]
/-
**MulAction.mem_stabilizer_finset_iff_smul_finset_subset** 是 Mathlib 中的一个引理，位于命名
空间 `MulAction`。
形式化陈述：mem_stabilizer_finset_iff_smul_finset_subset {s : Finset α} : a in stabili
zer G s ↔ a • s subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `Finset.subset_iff_eq_of_card_le`：subset_iff_eq_of_card_le (h : #t <= #s)
 : s subseteq t ↔ s = t
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Finset.card_smul_finset`：card_smul_finset (a : α) (s : Finset β) : (a • 
s).card = s.card
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_stabilizer_finset_iff_smul_finset_subset {s : Finset α} :
    a ∈ stabilizer G s ↔ a • s ⊆ s := by
  rw [mem_stabilizer_iff, Finset.subset_iff_eq_of_card_le (Finset.card_smul_finset _ _).ge]

@[to_additive]
/-
**MulAction.mem_stabilizer_finset'** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：mem_stabilizer_finset' {s : Finset α} : a in stabilizer G s ↔ forall ⦃b⦄, 
b in s -> a • b in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.inv_mem_iff`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G)
 {x : G}, x⁻¹ ∈ H ↔ x ∈ H
· 使用引理 `MulAction.mem_stabilizer_finset_iff_subset_smul_finset`：mem_stabilizer_f
inset_iff_subset_smul_finset {s : Finset α} : a in stabilizer G s ↔ s subseteq a
 • s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_stabilizer_finset' {s : Finset α} : a ∈ stabilizer G s ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  rw [← Subgroup.inv_mem_iff, mem_stabilizer_finset_iff_subset_smul_finset]
  simp_rw [← Finset.mem_inv_smul_finset_iff, Finset.subset_iff]

end Finset

/-! ### Stabilizer of a finite set -/

variable {s : Set α}

@[to_additive]
/-
**MulAction.mem_stabilizer_set_iff_subset_smul_set** 是 Mathlib 中的一个引理，位于命名空间 `Mu
lAction`。
形式化陈述：mem_stabilizer_set_iff_subset_smul_set {s : Set α} (hs : s.Finite) : a in 
stabilizer G s ↔ s subseteq a • s
参数：hs : s.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MulAction.stabilizer_coe_finset`：stabilizer_coe_finset (s : Finset α) : 
stabilizer G (s : Set α) = stabilizer G s
· 使用引理 `MulAction.mem_stabilizer_finset_iff_subset_smul_finset`：mem_stabilizer_f
inset_iff_subset_smul_finset {s : Finset α} : a in stabilizer G s ↔ s subseteq a
 • s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_stabilizer_set_iff_subset_smul_set {s : Set α} (hs : s.Finite) :
    a ∈ stabilizer G s ↔ s ⊆ a • s := by
  lift s to Finset α using hs
  classical
  rw [stabilizer_coe_finset, mem_stabilizer_finset_iff_subset_smul_finset, ← Finset.coe_smul_finset,
    Finset.coe_subset]

@[to_additive]
/-
**MulAction.mem_stabilizer_set_iff_smul_set_subset** 是 Mathlib 中的一个引理，位于命名空间 `Mu
lAction`。
形式化陈述：mem_stabilizer_set_iff_smul_set_subset {s : Set α} (hs : s.Finite) : a in 
stabilizer G s ↔ a • s subseteq s
参数：hs : s.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MulAction.stabilizer_coe_finset`：stabilizer_coe_finset (s : Finset α) : 
stabilizer G (s : Set α) = stabilizer G s
· 使用引理 `MulAction.mem_stabilizer_finset_iff_smul_finset_subset`：mem_stabilizer_f
inset_iff_smul_finset_subset {s : Finset α} : a in stabilizer G s ↔ a • s subset
eq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_stabilizer_set_iff_smul_set_subset {s : Set α} (hs : s.Finite) :
    a ∈ stabilizer G s ↔ a • s ⊆ s := by
  lift s to Finset α using hs
  classical
  rw [stabilizer_coe_finset, mem_stabilizer_finset_iff_smul_finset_subset, ← Finset.coe_smul_finset,
    Finset.coe_subset]

@[to_additive]
/-
**MulAction.mem_stabilizer_set'** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：mem_stabilizer_set' {s : Set α} (hs : s.Finite) : a in stabilizer G s ↔ fo
rall ⦃b⦄, b in s -> a • b in s
参数：hs : s.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MulAction.stabilizer_coe_finset`：stabilizer_coe_finset (s : Finset α) : 
stabilizer G (s : Set α) = stabilizer G s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_stabilizer_set' {s : Set α} (hs : s.Finite) :
    a ∈ stabilizer G s ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  lift s to Finset α using hs
  classical simp [-mem_stabilizer_iff, mem_stabilizer_finset']

end MulAction

/-! ### Stabilizer in a commutative group -/

namespace MulAction
variable {G : Type*} [CommGroup G] (s : Set G)

@[to_additive (attr := simp)]
/-
**MulAction.mul_stabilizer_self** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：mul_stabilizer_self : s * stabilizer G s = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `MulAction.stabilizer_mul_self`：stabilizer_mul_self (s : Set G) : (stabil
izer G s : Set G) * s = s
-/
lemma mul_stabilizer_self : s * stabilizer G s = s := by rw [mul_comm, stabilizer_mul_self]

local notation "Q" => G ⧸ stabilizer G s
local notation "q" => ((↑) : G → Q)

@[to_additive]
/-
**MulAction.stabilizer_image_coe_quotient** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_image_coe_quotient : stabilizer Q (q '' s) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用定理 `QuotientGroup.induction_on`：induction_on {C : α ⧸ s -> Prop} (x : α ⧸ s)
 (H : forall z, C (QuotientGroup.mk z)) : C x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.image_smul_distrib`：image_smul_distrib [Mul α] [Mul β] [FunLike F α 
β] [MulHomClass F α β] (f : F) (a : α) (s : Set α) : f '' (a • s) = f a • f '' s
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `MulAction.stabilizer_mul_self`：stabilizer_mul_self (s : Set G) : (stabil
izer G s : Set G) * s = s
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `QuotientGroup.image_coe_inj`：image_coe_inj {s t : Set G} : ((↑) : G -> Q
) '' s = ((↑) : G -> Q) '' t ↔ ↑N * s = N * t
-/
lemma stabilizer_image_coe_quotient : stabilizer Q (q '' s) = ⊥ := by
  ext a
  induction a using QuotientGroup.induction_on with | _ a
  simp only [mem_stabilizer_iff, Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  have : q a • q '' s = q '' (a • s) :=
    (image_smul_distrib (QuotientGroup.mk' <| stabilizer G s) _ _).symm
  rw [this]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  rwa [QuotientGroup.image_coe_inj, mul_smul_comm, stabilizer_mul_self] at h

end MulAction

