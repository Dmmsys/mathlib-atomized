/-
Copyright (c) 2026 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Inna Capdeboscq, Damiano Testa
-/
module

public import Mathlib.GroupTheory.Nilpotent

/-!
# Perfect groups

A group `G` is perfect if it equals its commutator subgroup, that is `⁅G, G⁆ = G`.

Among the basic results, we show that
* a nontrivial perfect group is not solvable (`IsPerfect.not_isSolvable`);
* an abelian perfect group is trivial (`IsPerfect.subsingleton_of_isMulCommutative`).

## Main Definition

* `Group.IsPerfect`: a group `G` is *perfect* if it equals its own commutator,
  that is `⁅⊤, ⊤⁆ = ⊤`, where `⊤` is the full subgroup `G`.

## Main Theorems

* `IsPerfect.map`: The image of a perfect group under a monoid homomorphism is perfect.
* `IsPerfect.instQuotientSubgroup`: The quotient of a perfect group by a normal subgroup is perfect.
* `IsPerfect.ofSurjective`: The image of a perfect group under a surjective monoid
  homomorphism is perfect.
-/

@[expose] public section

namespace Group
open Subgroup

variable {G G' : Type*} [Group G] [Group G'] {H K : Subgroup G} (f : G →* G')

variable (G) in
/-- A group `G` is perfect if `G` equals its commutator subgroup `⁅G, G⁆`. -/
/-
**Group.IsPerfect** 是 Mathlib 中的一个归纳类型，位于命名空间 `Group`。
形式化陈述：(G : Type u_1) → [Group G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A group `G` is perfect if `G` equals its commutator subgroup `⁅G, G⁆`.
-/
class IsPerfect where
  /-- The commutator of the group `G` with itself is the whole group `G`. -/
  commutator_eq_top : commutator G = (⊤ : Subgroup G)

attribute [simp] IsPerfect.commutator_eq_top
/-
**Group.isPerfect_def** 是 Mathlib 中的一个引理，位于命名空间 `Group`。
形式化陈述：isPerfect_def : IsPerfect G ↔ commutator G = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.IsPerfect.commutator_eq_top`：∀ {G : Type u_1} {inst : Group G} [se
lf : Group.IsPerfect G], commutator G = ⊤
-/
lemma isPerfect_def : IsPerfect G ↔ commutator G = ⊤ :=
  ⟨fun h ↦ h.commutator_eq_top, fun h ↦ ⟨h⟩⟩
/-
**Group._root_.Subgroup.isPerfect_iff** 是 Mathlib 中的一个引理，位于命名空间 `Group`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Subgroup.isPerfect_iff : IsPerfect H ↔ ⁅H, H⁆ = H := by
  rw [Group.isPerfect_def, ← map_subtype_inj,
    map_subtype_commutator, ← MonoidHom.range_eq_map, range_subtype]
/-
**Group._root_.Subgroup.commutator_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Group`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Subgroup.commutator_eq_self [hH : IsPerfect H] : ⁅H, H⁆ = H :=
  isPerfect_iff.mp hH

namespace IsPerfect

/-
**Group.IsPerfect.mem_commutator** 是 Mathlib 中的一个引理，位于命名空间 `Group.IsPerfect`。
形式化陈述：mem_commutator [hP : IsPerfect G] {g : G} : g in commutator G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Group.IsPerfect.commutator_eq_top`：∀ {G : Type u_1} {inst : Group G} [se
lf : Group.IsPerfect G], commutator G = ⊤
-/
lemma mem_commutator [hP : IsPerfect G] {g : G} : g ∈ commutator G := by
  simp

/-- The trivial group is perfect. -/
/-
**Group.IsPerfect.** 是 Mathlib 中的一个实例，位于命名空间 `Group.IsPerfect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial group is perfect.
-/
instance [Subsingleton G] : IsPerfect G where
  commutator_eq_top := Subsingleton.elim _ _
/-
**Group.IsPerfect.top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Group.IsPerfect`。
形式化陈述：top_iff : IsPerfect (⊤ : Subgroup G) ↔ IsPerfect G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Group.isPerfect_def`：isPerfect_def : IsPerfect G ↔ commutator G = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.map_subtype_inj`：map_subtype_inj {H : Subgroup G} {K L : Subgro
up H} : K.map H.subtype = L.map H.subtype ↔ K = L
· 使用引理 `Subgroup.map_subtype_commutator`：Subgroup.map_subtype_commutator (H : Su
bgroup G) : (_root_.commutator H).map H.subtype = ⁅H, H⁆
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Subgroup.subtype_range`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用引理 `commutator_def`：commutator_def : commutator G = ⁅(⊤ : Subgroup G), ⊤⁆
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem top_iff : IsPerfect (⊤ : Subgroup G) ↔ IsPerfect G := by
  rw [isPerfect_def, isPerfect_def, ← map_subtype_inj,
    map_subtype_commutator, ← MonoidHom.range_eq_map, subtype_range, commutator_def]
/-
**Group.IsPerfect.** 是 Mathlib 中的一个实例，位于命名空间 `Group.IsPerfect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsPerfect G] : IsPerfect (⊤ : Subgroup G) :=
  top_iff.mpr inferInstance

variable (G) in
/-
**Group.IsPerfect.not_isSolvable** 是 Mathlib 中的一个引理，位于命名空间 `Group.IsPerfect`。
形式化陈述：not_isSolvable [Nontrivial G] [IsPerfect G] : ¬ IsSolvable G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Group.IsSolvable.commutator_lt_top_of_nontrivial`：∀ (G : Type u_1) [inst
 : Group G] [hG : Group.IsSolvable G] [Nontrivial G], commutator G < ⊤
· 使用定理 `Group.IsPerfect.commutator_eq_top`：∀ {G : Type u_1} {inst : Group G} [se
lf : Group.IsPerfect G], commutator G = ⊤
-/
lemma not_isSolvable [Nontrivial G] [IsPerfect G] : ¬ IsSolvable G := by
  intro h
  exact (h.commutator_lt_top_of_nontrivial G).ne commutator_eq_top

variable (G) in
/-
**Group.IsPerfect.not_isNilpotent** 是 Mathlib 中的一个引理，位于命名空间 `Group.IsPerfect`。
形式化陈述：not_isNilpotent [Nontrivial G] [IsPerfect G] : ¬ IsNilpotent G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Group.IsPerfect.not_isSolvable`：not_isSolvable [Nontrivial G] [IsPerfect
 G] : ¬ IsSolvable G
· 使用定理 `IsNilpotent.to_isSolvable`：∀ {G : Type u_1} [inst : Group G] [h : Group.
IsNilpotent G], Group.IsSolvable G
-/
lemma not_isNilpotent [Nontrivial G] [IsPerfect G] : ¬ IsNilpotent G :=
  fun _ ↦ (not_isSolvable G) IsNilpotent.to_isSolvable

open scoped IsMulCommutative in
variable (G) in
/-
**Group.IsPerfect.not_isMulCommutative** 是 Mathlib 中的一个引理，位于命名空间 `Group.IsPerfec
t`。
形式化陈述：not_isMulCommutative [Nontrivial G] [IsPerfect G] : ¬ IsMulCommutative G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Group.IsPerfect.not_isSolvable`：not_isSolvable [Nontrivial G] [IsPerfect
 G] : ¬ IsSolvable G
· 使用定理 `IsNilpotent.to_isSolvable`：∀ {G : Type u_1} [inst : Group G] [h : Group.
IsNilpotent G], Group.IsSolvable G
· 使用定理 `CommGroup.isNilpotent`：∀ {G : Type u_2} [inst : CommGroup G], Group.IsNi
lpotent G
-/
lemma not_isMulCommutative [Nontrivial G] [IsPerfect G] : ¬ IsMulCommutative G :=
  fun _ ↦ (not_isSolvable G) inferInstance
/-
**Group.IsPerfect.subsingleton_of_isMulCommutative** 是 Mathlib 中的一个实例，位于命名空间 `Gr
oup.IsPerfect`。
形式化陈述：subsingleton_of_isMulCommutative [hG : IsPerfect G] [h_comm : IsMulCommuta
tive G] : Subsingleton G
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `Group.IsPerfect.not_isMulCommutative`：not_isMulCommutative [Nontrivial G
] [IsPerfect G] : ¬ IsMulCommutative G
-/
instance subsingleton_of_isMulCommutative
    [hG : IsPerfect G] [h_comm : IsMulCommutative G] : Subsingleton G := by
  by_contra! h_not_subsingleton
  exact not_isMulCommutative G h_comm
/-
**Group.IsPerfect.map** 是 Mathlib 中的一个定理，位于命名空间 `Group.IsPerfect`。
形式化陈述：∀ {G : Type u_1} {G' : Type u_2} [inst : Group G] [inst_1 : Group G'] {H :
 Subgroup G} (f : G →* G')   [Group.IsPerfect ↥H], Group.IsPerfect ↥(Subgroup.ma
p f H)
参数：f : G →* G'；Subgroup.map f H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.isPerfect_iff`：∀ {G : Type u_1} [inst : Group G] {H : Subgroup 
G}, Group.IsPerfect ↥H ↔ ⁅H, H⁆ = H
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.map_commutator`：map_commutator (f : G ->* G') : map f ⁅H₁, H₂⁆ 
= ⁅map f H₁, map f H₂⁆
· 使用定理 `Subgroup.commutator_eq_self`：∀ {G : Type u_1} [inst : Group G] {H : Subg
roup G} [hH : Group.IsPerfect ↥H], ⁅H, H⁆ = H
-/
protected lemma map [IsPerfect H] : IsPerfect (H.map f) := by
  rw [isPerfect_iff, ← map_commutator, commutator_eq_self]
/-
**Group.IsPerfect.range** 是 Mathlib 中的一个定理，位于命名空间 `Group.IsPerfect`。
形式化陈述：∀ {G : Type u_1} {G' : Type u_2} [inst : Group G] [inst_1 : Group G'] (f :
 G →* G') [Group.IsPerfect G],   Group.IsPerfect ↥f.range
参数：f : G →* G'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Group.IsPerfect.map`：∀ {G : Type u_1} {G' : Type u_2} [inst : Group G] [
inst_1 : Group G'] {H : Subgroup G} (f : G →* G')   [Group.IsPerfect ↥H], Group.
IsPerfect…
· 使用定理 `Group.IsPerfect.instSubtypeMemSubgroupTop`：∀ {G : Type u_1} [inst : Grou
p G] [Group.IsPerfect G], Group.IsPerfect ↥⊤
-/
protected lemma range [IsPerfect G] : IsPerfect f.range := by
  rw [MonoidHom.range_eq_map]
  exact IsPerfect.map _

variable {f} in
/-
**Group.IsPerfect.ofSurjective** 是 Mathlib 中的一个引理，位于命名空间 `Group.IsPerfect`。
形式化陈述：ofSurjective [IsPerfect G] (hf : Function.Surjective f) : IsPerfect G'
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Group.IsPerfect.top_iff`：top_iff : IsPerfect (⊤ : Subgroup G) ↔ IsPerfec
t G
· 使用定理 `MonoidHom.range_eq_top_of_surjective`：range_eq_top_of_surjective {N} [Gr
oup N] (f : G ->* N) (hf : Function.Surjective f) : f.range = (⊤ : Subgroup N)
· 使用定理 `Group.IsPerfect.range`：∀ {G : Type u_1} {G' : Type u_2} [inst : Group G]
 [inst_1 : Group G'] (f : G →* G') [Group.IsPerfect G],   Group.IsPerfect ↥f.ran
ge
-/
lemma ofSurjective [IsPerfect G] (hf : Function.Surjective f) : IsPerfect G' := by
  rw [← top_iff, ← MonoidHom.range_eq_top_of_surjective f hf]
  exact IsPerfect.range f
/-
**Group.IsPerfect.instQuotientSubgroup** 是 Mathlib 中的一个实例，位于命名空间 `Group.IsPerfec
t`。
形式化陈述：instQuotientSubgroup [H.Normal] [IsPerfect G] : IsPerfect (G ⧸ H)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Group.IsPerfect.ofSurjective`：ofSurjective [IsPerfect G] (hf : Function.
Surjective f) : IsPerfect G'
· 使用定理 `QuotientGroup.mk'_surjective`：∀ {G : Type u_1} [inst : Group G] (N : Sub
group G) [nN : N.Normal], Function.Surjective ⇑(QuotientGroup.mk' N)
-/
instance instQuotientSubgroup [H.Normal] [IsPerfect G] : IsPerfect (G ⧸ H) :=
  ofSurjective (QuotientGroup.mk'_surjective H)

variable (G) in
@[simp]
/-
**Group.IsPerfect.derivedSeries_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Group.IsPerfec
t`。
形式化陈述：derivedSeries_eq_top [IsPerfect G] (n : Nat) : derivedSeries G n = ⊤
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem derivedSeries_eq_top [IsPerfect G] (n : ℕ) : derivedSeries G n = ⊤ := by
  match n with
  | 0 => simp
  | n + 1 =>
    rw [derivedSeries_succ, derivedSeries_eq_top, commutator_eq_self]

@[simp]
/-
**Group.IsPerfect.lowerCentralSeries_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Group.IsP
erfect`。
形式化陈述：lowerCentralSeries_eq_top (H : Subgroup G) [IsPerfect H] (n : Nat) : H.low
erCentralSeries n = H
参数：H : Subgroup G；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lowerCentralSeries_eq_top (H : Subgroup G) [IsPerfect H] (n : ℕ) :
    H.lowerCentralSeries n = H := by
  match n with
  | 0 => simp
  | n + 1 =>
    rw [Subgroup.lowerCentralSeries_succ, lowerCentralSeries_eq_top, commutator_eq_self]

variable (G) in
@[simp]
/-
**Group.IsPerfect.upperCentralSeries_eq_center** 是 Mathlib 中的一个定理，位于命名空间 `Group.
IsPerfect`。
形式化陈述：upperCentralSeries_eq_center [IsPerfect G] {n : Nat} (hn : n != 0) : Subgr
oup.upperCentralSeries G n = center G
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.upperCentralSeries_one`：upperCentralSeries_one : upperCentralSe
ries G 1 = center G
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Subgroup.upperCentralSeries.eq_ge_of_eq_succ`：∀ {G : Type u_1} [inst : G
roup G] {a b : ℕ},   a ≤ b →     Subgroup.upperCentralSeries G a = Subgroup.uppe
rCentralSeries G (a + 1) →       S…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Subgroup.upperCentralSeries_mono`：upperCentralSeries_mono : Monotone (up
perCentralSeries G)
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Subgroup.commutator_top_right_eq_bot_iff_le_center`：commutator_top_right
_eq_bot_iff_le_center : ⁅H, (⊤ : Subgroup G)⁆ = ⊥ ↔ H <= center G
· 使用定理 `Group.IsPerfect.commutator_eq_top`：∀ {G : Type u_1} {inst : Group G} [se
lf : Group.IsPerfect G], commutator G = ⊤
· 使用定理 `Subgroup.commutator_comm`：commutator_comm : ⁅H₁, H₂⁆ = ⁅H₂, H₁⁆
· 使用引理 `commutator_def`：commutator_def : commutator G = ⁅(⊤ : Subgroup G), ⊤⁆
· 使用定理 `Subgroup.commutator_upperCentralSeries_top_le`：commutator_upperCentralSe
ries_top_le (n : Nat) : ⁅upperCentralSeries G (n + 1), ⊤⁆ <= upperCentralSeries 
G n
· 使用定理 `Subgroup.commutator_commutator_eq_bot_of_rotate`：commutator_commutator_e
q_bot_of_rotate (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ = ⊥) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ = ⊥) : ⁅⁅H₁, H₂⁆,
 H₃⁆ = ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem upperCentralSeries_eq_center [IsPerfect G] {n : ℕ} (hn : n ≠ 0) :
    Subgroup.upperCentralSeries G n = center G := by
  rw [← Subgroup.upperCentralSeries_one, eq_comm]
  apply Subgroup.upperCentralSeries.eq_ge_of_eq_succ <| by lia
  apply le_antisymm <| Subgroup.upperCentralSeries_mono G one_le_two
  rw [Subgroup.upperCentralSeries_one, ← commutator_top_right_eq_bot_iff_le_center,
    ← commutator_eq_top, commutator_comm, commutator_def]
  suffices ⁅⁅Subgroup.upperCentralSeries G 2, ⊤⁆, ⊤⁆ = ⊥ from
    commutator_commutator_eq_bot_of_rotate (by simpa [commutator_comm]) this
  rw [commutator_top_right_eq_bot_iff_le_center, ← Subgroup.upperCentralSeries_one]
  apply commutator_upperCentralSeries_top_le

variable (G) in
/-- **Grün's lemma** -/
/-
**Group.IsPerfect.center_quotient_center_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Group
.IsPerfect`。
形式化陈述：center_quotient_center_eq_bot [IsPerfect G] : center (G ⧸ center G) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.upperCentralSeries_one`：upperCentralSeries_one : upperCentralSe
ries G 1 = center G
· 使用定理 `Subgroup.comap_eq_ker_of_surjective`：comap_eq_ker_of_surjective {f : G -
>* N} (hf : Surjective f) {H : Subgroup N} : H.comap f = f.ker ↔ H = ⊥
· 使用定理 `QuotientGroup.mk'_surjective`：∀ {G : Type u_1} [inst : Group G] (N : Sub
group G) [nN : N.Normal], Function.Surjective ⇑(QuotientGroup.mk' N)
· 使用定理 `QuotientGroup.ker_mk'`：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G 
->* G ⧸ N) = N
· 使用定理 `Subgroup.comap_upperCentralSeries_quotient_center`：comap_upperCentralSer
ies_quotient_center (n : Nat) : comap (mk' (center G)) (upperCentralSeries (G ⧸ 
center G) n) = upperCentralSeries G n.s…
· 使用定理 `Group.IsPerfect.upperCentralSeries_eq_center`：upperCentralSeries_eq_cent
er [IsPerfect G] {n : Nat} (hn : n != 0) : Subgroup.upperCentralSeries G n = cen
ter G

--- 原说明 ---
**Grün's lemma**
-/
theorem center_quotient_center_eq_bot [IsPerfect G] : center (G ⧸ center G) = ⊥ := by
  rw [← Subgroup.upperCentralSeries_one (G ⧸ center G),
    ← comap_eq_ker_of_surjective <| QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk',
    Subgroup.comap_upperCentralSeries_quotient_center, upperCentralSeries_eq_center G <| by lia]

end Group.IsPerfect

