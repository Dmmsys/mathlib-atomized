/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.FiniteIndexNormalSubgroup

/-!
# Residually Finite Groups

In this file we define residually finite groups and prove some basic properties.

## Main definitions

- `Group.ResiduallyFinite G`: A group `G` is residually finite if the intersection of all
  finite index normal subgroups is trivial.

-/

@[expose] public section

/-- An additive group `G` is residually finite if the intersection of all finite index normal
additive subgroups is trivial. -/
/-
**AddGroup.ResiduallyFinite** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddGroup`。
形式化陈述：(G : Type u_1) → [AddGroup G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive group `G` is residually finite if the intersection of all finite ind
ex normal
additive subgroups is trivial.
-/
class AddGroup.ResiduallyFinite (G : Type*) [AddGroup G] : Prop where
  iInf_eq_bot : ⨅ H : FiniteIndexNormalAddSubgroup G, H.toAddSubgroup = ⊥

namespace Group

/-- A group `G` is residually finite if the intersection of all finite index normal subgroups is
trivial. -/
/-
**Group.ResiduallyFinite** 是 Mathlib 中的一个归纳类型，位于命名空间 `Group`。
形式化陈述：(G : Type u_1) → [Group G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A group `G` is residually finite if the intersection of all finite index normal 
subgroups is
trivial.
-/
class ResiduallyFinite (G : Type*) [Group G] : Prop where
  iInf_eq_bot : ⨅ H : FiniteIndexNormalSubgroup G, H.toSubgroup = ⊥

attribute [to_additive existing] ResiduallyFinite

variable {G G' : Type*} [Group G] [Group G']

@[to_additive]
/-
**Group.residuallyFinite_def** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：residuallyFinite_def : ResiduallyFinite G ↔ ⨅ H : FiniteIndexNormalSubgrou
p G, H.toSubgroup = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.ResiduallyFinite.iInf_eq_bot`：∀ {G : Type u_1} {inst : Group G} [s
elf : Group.ResiduallyFinite G], ⨅ H, H.toSubgroup = ⊥
-/
theorem residuallyFinite_def :
    ResiduallyFinite G ↔ ⨅ H : FiniteIndexNormalSubgroup G, H.toSubgroup = ⊥ :=
  ⟨fun h ↦ h.iInf_eq_bot, fun h ↦ ⟨h⟩⟩

@[to_additive]
/-
**Group.residuallyFinite_iff_forall_finiteIndexNormalSubgroup** 是 Mathlib 中的一个定理
，位于命名空间 `Group`。
形式化陈述：residuallyFinite_iff_forall_finiteIndexNormalSubgroup : ResiduallyFinite G
 ↔ forall g : G, (forall H : FiniteIndexNormalSubgroup G, g in H) -> g = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem residuallyFinite_iff_forall_finiteIndexNormalSubgroup :
    ResiduallyFinite G ↔ ∀ g : G, (∀ H : FiniteIndexNormalSubgroup G, g ∈ H) → g = 1 := by
  simp_rw [residuallyFinite_def, Subgroup.eq_bot_iff_forall, Subgroup.mem_iInf,
    FiniteIndexNormalSubgroup.mem_toSubgroup_iff]

@[to_additive]
/-
**Group.eq_one_iff_forall_finiteIndexNormalSubroup** 是 Mathlib 中的一个定理，位于命名空间 `Gr
oup`。
形式化陈述：eq_one_iff_forall_finiteIndexNormalSubroup [ResiduallyFinite G] (g : G) (h
g : forall H : FiniteIndexNormalSubgroup G, g in H) : g = 1
参数：g : G；hg : forall H : FiniteIndexNormalSubgroup G, g in H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Group.residuallyFinite_iff_forall_finiteIndexNormalSubgroup`：residuallyF
inite_iff_forall_finiteIndexNormalSubgroup : ResiduallyFinite G ↔ forall g : G, 
(forall H : FiniteIndexNormalSubgroup G, g in H) …
-/
theorem eq_one_iff_forall_finiteIndexNormalSubroup [ResiduallyFinite G]
    (g : G) (hg : ∀ H : FiniteIndexNormalSubgroup G, g ∈ H) : g = 1 :=
  residuallyFinite_iff_forall_finiteIndexNormalSubgroup.mp ‹_› g hg

@[to_additive]
/-
**Group.residuallyFinite_iff_exists_finiteIndexNormalSubgroup** 是 Mathlib 中的一个定理
，位于命名空间 `Group`。
形式化陈述：residuallyFinite_iff_exists_finiteIndexNormalSubgroup : ResiduallyFinite G
 ↔ forall g : G, g != 1 -> exists H : FiniteIndexNormalSubgroup G, g ∉ H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem residuallyFinite_iff_exists_finiteIndexNormalSubgroup :
    ResiduallyFinite G ↔ ∀ g : G, g ≠ 1 → ∃ H : FiniteIndexNormalSubgroup G, g ∉ H := by
  simp_rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup, ← not_forall, not_imp_not]

@[to_additive]
/-
**Group.exists_finiteIndexNormalSubgroup_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Group
`。
形式化陈述：exists_finiteIndexNormalSubgroup_notMem [ResiduallyFinite G] (g : G) (hg :
 g != 1) : exists H : FiniteIndexNormalSubgroup G, g ∉ H
参数：g : G；hg : g != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Group.residuallyFinite_iff_exists_finiteIndexNormalSubgroup`：residuallyF
inite_iff_exists_finiteIndexNormalSubgroup : ResiduallyFinite G ↔ forall g : G, 
g != 1 -> exists H : FiniteIndexNormalSubgroup G,…
-/
theorem exists_finiteIndexNormalSubgroup_notMem [ResiduallyFinite G] (g : G) (hg : g ≠ 1) :
    ∃ H : FiniteIndexNormalSubgroup G, g ∉ H :=
  residuallyFinite_iff_exists_finiteIndexNormalSubgroup.mp ‹_› g hg

@[to_additive]
/-
**Group.residuallyFinite_iff_forall_finiteIndex** 是 Mathlib 中的一个定理，位于命名空间 `Group
`。
形式化陈述：residuallyFinite_iff_forall_finiteIndex : ResiduallyFinite G ↔ forall g : 
G, (forall (H : Subgroup G) [H.FiniteIndex], g in H) -> g = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Group.residuallyFinite_iff_forall_finiteIndexNormalSubgroup`：residuallyF
inite_iff_forall_finiteIndexNormalSubgroup : ResiduallyFinite G ↔ forall g : G, 
(forall H : FiniteIndexNormalSubgroup G, g in H) …
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `FiniteIndexNormalSubgroup.instFiniteIndex`：∀ {G : Type u_1} [inst : Grou
p G] (H : FiniteIndexNormalSubgroup G), H.FiniteIndex
· 使用定理 `Subgroup.normalCore_le`：normalCore_le (H : Subgroup G) : H.normalCore <=
 H
-/
theorem residuallyFinite_iff_forall_finiteIndex :
    ResiduallyFinite G ↔ ∀ g : G, (∀ (H : Subgroup G) [H.FiniteIndex], g ∈ H) → g = 1 := by
  rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  exact forall_congr' fun g ↦ ⟨fun h hg ↦ h fun H ↦ hg H,
    fun h hg ↦ h fun H hH ↦ H.normalCore_le (hg (.ofSubgroup H.normalCore))⟩

@[to_additive]
/-
**Group.residuallyFinite_iff_exists_finiteIndex** 是 Mathlib 中的一个定理，位于命名空间 `Group
`。
形式化陈述：residuallyFinite_iff_exists_finiteIndex : ResiduallyFinite G ↔ forall g : 
G, g != 1 -> exists (H : Subgroup G), H.FiniteIndex ∧ g ∉ H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem residuallyFinite_iff_exists_finiteIndex :
    ResiduallyFinite G ↔ ∀ g : G, g ≠ 1 → ∃ (H : Subgroup G), H.FiniteIndex ∧ g ∉ H := by
  simp_rw [residuallyFinite_iff_forall_finiteIndex, ← Classical.not_imp, ← not_forall,
    not_imp_not]

/-- If `G` is residually finite, for every pair of distinct elements `g`, `h` there exists a finite
index normal subgroup `H` such that `g` and `h` differ in the quotient `G ⧸ H`. -/
@[to_additive]
/-
**Group.exists_finiteIndexNormalSubgroup_of_residuallyFinite** 是 Mathlib 中的一个定理，
位于命名空间 `Group`。
形式化陈述：exists_finiteIndexNormalSubgroup_of_residuallyFinite [ResiduallyFinite G] 
(g h : G) (hgh : g != h) : exists H : FiniteIndexNormalSubgroup G, (g : G ⧸ H.to
Subgroup) != ↑h
参数：g h : G；hgh : g != h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.exists_finiteIndexNormalSubgroup_notMem`：exists_finiteIndexNormalS
ubgroup_notMem [ResiduallyFinite G] (g : G) (hg : g != 1) : exists H : FiniteInd
exNormalSubgroup G, g ∉ H
· 使用引理 `eq_of_inv_mul_eq_one`：eq_of_inv_mul_eq_one (h : a⁻¹ * b = 1) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If `G` is residually finite, for every pair of distinct elements `g`, `h` there 
exists a finite
index normal subgroup `H` such that `g` and `h` differ in the quotient `G ⧸ H`.
-/
theorem exists_finiteIndexNormalSubgroup_of_residuallyFinite [ResiduallyFinite G] (g h : G)
    (hgh : g ≠ h) : ∃ H : FiniteIndexNormalSubgroup G, (g : G ⧸ H.toSubgroup) ≠ ↑h := by
  obtain ⟨H, hH⟩ :=
    exists_finiteIndexNormalSubgroup_notMem (g⁻¹ * h) fun h ↦ hgh <| eq_of_inv_mul_eq_one h
  exact ⟨H, by simpa [QuotientGroup.eq]⟩

/-- `G` is residually finite if for every element `g` not equal to `1` there exists a group
homomorphism `f` to a finite group `H` such that `f g ≠ 1`. -/
@[to_additive]
/-
**Group.residuallyFinite_of_forall_exists_finite_monoidHom.** 是 Mathlib 中的一个定理，位
于命名空间 `Group`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G` is residually finite if for every element `g` not equal to `1` there exists 
a group
homomorphism `f` to a finite group `H` such that `f g ≠ 1`.
-/
theorem residuallyFinite_of_forall_exists_finite_monoidHom.{u}
    (h : ∀ g : G, g ≠ 1 → ∃ (H : Type u) (_ : Group H) (_ : Finite H) (f : G →* H), f g ≠ 1) :
    ResiduallyFinite G := by
  rw [residuallyFinite_iff_exists_finiteIndex]
  intro g hg
  obtain ⟨_, _, _, f, hf⟩ := h g hg
  exact ⟨f.ker, Subgroup.finiteIndex_ker f, by simpa using hf⟩

@[to_additive]
/-
**Group.** 是 Mathlib 中的一个实例，位于命名空间 `Group`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite G] : ResiduallyFinite G :=
  residuallyFinite_iff_forall_finiteIndex.mpr fun _ hg ↦ hg ⊥

@[to_additive]
/-
**Group.** 是 Mathlib 中的一个实例，位于命名空间 `Group`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ResiduallyFinite G] {H : Subgroup G} : ResiduallyFinite H := by
  rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  intro g hg
  ext
  exact eq_one_iff_forall_finiteIndexNormalSubroup g.1 fun K ↦ hg (K.comap H.subtype)

@[to_additive]
/-
**Group.** 是 Mathlib 中的一个实例，位于命名空间 `Group`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ResiduallyFinite G] [ResiduallyFinite G'] : ResiduallyFinite (G × G') := by
  rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  intro g hg
  ext
  · exact eq_one_iff_forall_finiteIndexNormalSubroup g.1 fun K ↦ hg (K.comap (MonoidHom.fst G G'))
  · exact eq_one_iff_forall_finiteIndexNormalSubroup g.2 fun K ↦ hg (K.comap (MonoidHom.snd G G'))

end Group

