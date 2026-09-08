/-
Copyright (c) 2021 Jordan Brown, Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Solvable Groups

In this file we introduce the notion of a solvable group. We define a solvable group as one whose
derived series is eventually trivial. This requires defining the commutator of two subgroups and
the derived series of a group.

## Main definitions

* `derivedSeries G n` : the `n`th term in the derived series of `G`, defined by iterating
    `general_commutator` starting with the top subgroup
* `IsSolvable G` : the group `G` is solvable
-/

@[expose] public section

open Subgroup

open scoped commutatorElement

variable {G G' : Type*} [Group G] [Group G'] {f : G →* G'}

section derivedSeries

variable (G)

/-- The derived series of the group `G`, obtained by starting from the subgroup `⊤` and repeatedly
  taking the commutator of the previous subgroup with itself for `n` times. -/
/-
**derivedSeries** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：(G : Type u_1) → [inst : Group G] → ℕ → Subgroup G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derived series of the group `G`, obtained by starting from the subgroup `⊤` 
and repeatedly
  taking the commutator of the previous subgroup with itself for `n` times.
-/
def derivedSeries : ℕ → Subgroup G
  | 0 => ⊤
  | n + 1 => ⁅derivedSeries n, derivedSeries n⁆

@[simp]
/-
**derivedSeries_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivedSeries_zero : derivedSeries G 0 = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem derivedSeries_zero : derivedSeries G 0 = ⊤ :=
  rfl

@[simp]
/-
**derivedSeries_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivedSeries_succ (n : Nat) : derivedSeries G (n + 1) = ⁅derivedSeries G 
n, derivedSeries G n⁆
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem derivedSeries_succ (n : ℕ) :
    derivedSeries G (n + 1) = ⁅derivedSeries G n, derivedSeries G n⁆ :=
  rfl
/-
**derivedSeries_normal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivedSeries_normal (n : Nat) : (derivedSeries G n).Normal
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_of_characteristic`：∀ {G : Type u_1} [inst : Group G] (H 
: Subgroup G) [h : H.Characteristic], H.Normal
-/
theorem derivedSeries_normal (n : ℕ) : (derivedSeries G n).Normal := by
  induction n with
  | zero => exact (⊤ : Subgroup G).normal_of_characteristic
  | succ n ih => exact Subgroup.commutator_normal (derivedSeries G n) (derivedSeries G n)

@[simp 1100]
/-
**derivedSeries_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivedSeries_one : derivedSeries G 1 = commutator G
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem derivedSeries_one : derivedSeries G 1 = commutator G :=
  rfl
/-
**derivedSeries_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivedSeries_antitone : Antitone (derivedSeries G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antitone_nat_of_succ_le`：antitone_nat_of_succ_le {f : Nat -> α} (hf : fo
rall n, f (n + 1) <= f n) : Antitone f
· 使用引理 `Subgroup.commutator_le_self`：Subgroup.commutator_le_self (H : Subgroup G
) : ⁅H, H⁆ <= H
-/
theorem derivedSeries_antitone : Antitone (derivedSeries G) :=
  antitone_nat_of_succ_le fun n => (derivedSeries G n).commutator_le_self
/-
**derivedSeries_characteristic** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：derivedSeries_characteristic (n : Nat) : (derivedSeries G n).Characteristi
c
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance derivedSeries_characteristic (n : ℕ) : (derivedSeries G n).Characteristic := by
  induction n with
  | zero => exact Subgroup.topCharacteristic
  | succ n _ => exact Subgroup.commutator_characteristic _ _

end derivedSeries

section CommutatorMap

section DerivedSeriesMap

variable (f) in
/-
**map_derivedSeries_le_derivedSeries** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_derivedSeries_le_derivedSeries (n : Nat) : (derivedSeries G n).map f <
= derivedSeries G' n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_commutator`：map_commutator (f : G ->* G') : map f ⁅H₁, H₂⁆ 
= ⁅map f H₁, map f H₂⁆
-/
theorem map_derivedSeries_le_derivedSeries (n : ℕ) :
    (derivedSeries G n).map f ≤ derivedSeries G' n := by
  induction n with
  | zero => exact le_top
  | succ n ih => simp only [derivedSeries_succ, map_commutator, commutator_mono, ih]
/-
**derivedSeries_le_map_derivedSeries** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivedSeries_le_map_derivedSeries (hf : Function.Surjective f) (n : Nat) 
: derivedSeries G' n <= (derivedSeries G n).map f
参数：hf : Function.Surjective f；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subgroup.map_top_of_surjective`：map_top_of_surjective (f : G ->* N) (h :
 Function.Surjective f) : Subgroup.map f ⊤ = ⊤
· 使用定理 `Subgroup.commutator_le_map_commutator`：commutator_le_map_commutator {f :
 G ->* G'} {K₁ K₂ : Subgroup G'} (h₁ : K₁ <= H₁.map f) (h₂ : K₂ <= H₂.map f) : ⁅
K₁, K₂⁆ <= ⁅H₁, H₂⁆.map f
-/
theorem derivedSeries_le_map_derivedSeries (hf : Function.Surjective f) (n : ℕ) :
    derivedSeries G' n ≤ (derivedSeries G n).map f := by
  induction n with
  | zero => exact (map_top_of_surjective f hf).ge
  | succ n ih => exact commutator_le_map_commutator ih ih
/-
**map_derivedSeries_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_derivedSeries_eq (hf : Function.Surjective f) (n : Nat) : (derivedSeri
es G n).map f = derivedSeries G' n
参数：hf : Function.Surjective f；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `map_derivedSeries_le_derivedSeries`：map_derivedSeries_le_derivedSeries (
n : Nat) : (derivedSeries G n).map f <= derivedSeries G' n
· 使用定理 `derivedSeries_le_map_derivedSeries`：derivedSeries_le_map_derivedSeries (
hf : Function.Surjective f) (n : Nat) : derivedSeries G' n <= (derivedSeries G n
).map f
-/
theorem map_derivedSeries_eq (hf : Function.Surjective f) (n : ℕ) :
    (derivedSeries G n).map f = derivedSeries G' n :=
  le_antisymm (map_derivedSeries_le_derivedSeries f n) (derivedSeries_le_map_derivedSeries hf n)

end DerivedSeriesMap

end CommutatorMap

section Solvable

variable (G)

namespace Group

/-- A group `G` is solvable if its derived series is eventually trivial. We use this definition
  because it's the most convenient one to work with. -/
@[mk_iff isSolvable_def, wikidata Q759832]
/-
**Group.IsSolvable** 是 Mathlib 中的一个归纳类型，位于命名空间 `Group`。
形式化陈述：(G : Type u_1) → [Group G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A group `G` is solvable if its derived series is eventually trivial. We use this
 definition
  because it's the most convenient one to work with.
-/
class IsSolvable : Prop where
  /-- A group `G` is solvable if its derived series is eventually trivial. -/
  solvable : ∃ n : ℕ, derivedSeries G n = ⊥

@[deprecated (since := "2026-07-16")]
alias _root_.IsSolvable := Group.IsSolvable

@[deprecated (since := "2026-07-17")]
alias _root_.isSolvable_def := Group.isSolvable_def
/-
**Group.** 是 Mathlib 中的一个实例，位于命名空间 `Group`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {G : Type*} [CommGroup G] : IsSolvable G :=
  ⟨⟨1, le_bot_iff.mp (Abelianization.commutator_subset_ker (MonoidHom.id G))⟩⟩
/-
**Group.isSolvable_of_comm** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：isSolvable_of_comm {G : Type*} [hG : Group G] (h : forall a b : G, a * b =
 b * a) : IsSolvable G
参数：h : forall a b : G, a * b = b * a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.instIsSolvable`：∀ {G : Type u_3} [inst : CommGroup G], Group.IsSol
vable G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isSolvable_of_comm {G : Type*} [hG : Group G] (h : ∀ a b : G, a * b = b * a) :
    IsSolvable G := by
  let hG' : CommGroup G := { hG with mul_comm := h }
  cases hG
  infer_instance

@[deprecated (since := "2026-07-16")]
alias _root_.isSolvable_of_comm := Group.isSolvable_of_comm
/-
**Group.isSolvable_of_top_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：isSolvable_of_top_eq_bot (h : (⊤ : Subgroup G) = ⊥) : IsSolvable G
参数：h : (⊤ : Subgroup G) = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isSolvable_of_top_eq_bot (h : (⊤ : Subgroup G) = ⊥) : IsSolvable G :=
  ⟨⟨0, h⟩⟩

@[deprecated (since := "2026-07-16")]
alias _root_.isSolvable_of_top_eq_bot := Group.isSolvable_of_top_eq_bot
/-
**Group.** 是 Mathlib 中的一个实例，位于命名空间 `Group`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [Subsingleton G] : IsSolvable G :=
  isSolvable_of_top_eq_bot G (by simp [eq_iff_true_of_subsingleton])

variable {G}
/-
**Group.isSolvable_of_ker_le_range** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：isSolvable_of_ker_le_range {G' G'' : Type*} [Group G'] [Group G''] (f : G'
 ->* G) (g : G ->* G'') (hfg : g.ker <= f.range) [hG' : IsSolvable G'] [hG'' : I
sSolvable G''] : IsSolvable G
参数：f : G' ->* G；g : G ->* G''；hfg : g.ker <= f.range。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subgroup.map_eq_bot_iff`：map_eq_bot_iff {f : G ->* N} : H.map f = ⊥ ↔ H 
<= f.ker
· 使用定理 `map_derivedSeries_le_derivedSeries`：map_derivedSeries_le_derivedSeries (
n : Nat) : (derivedSeries G n).map f <= derivedSeries G' n
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Subgroup.commutator_le_map_commutator`：commutator_le_map_commutator {f :
 G ->* G'} {K₁ K₂ : Subgroup G'} (h₁ : K₁ <= H₁.map f) (h₂ : K₂ <= H₂.map f) : ⁅
K₁, K₂⁆ <= ⁅H₁, H₂⁆.map f
· 使用定理 `Subgroup.map_bot`：map_bot (f : G ->* N) : (⊥ : Subgroup G).map f = ⊥
-/
theorem isSolvable_of_ker_le_range {G' G'' : Type*} [Group G'] [Group G''] (f : G' →* G)
    (g : G →* G'') (hfg : g.ker ≤ f.range) [hG' : IsSolvable G'] [hG'' : IsSolvable G''] :
    IsSolvable G := by
  obtain ⟨n, hn⟩ := id hG''
  obtain ⟨m, hm⟩ := id hG'
  refine ⟨⟨n + m, le_bot_iff.mp (Subgroup.map_bot f ▸ hm ▸ ?_)⟩⟩
  clear hm
  induction m with
  | zero =>
    exact f.range_eq_map ▸ ((derivedSeries G n).map_eq_bot_iff.mp
      (le_bot_iff.mp ((map_derivedSeries_le_derivedSeries g n).trans hn.le))).trans hfg
  | succ m hm => exact commutator_le_map_commutator hm hm

@[deprecated (since := "2026-07-16")]
alias _root_.solvable_of_ker_le_range := isSolvable_of_ker_le_range
/-
**Group.isSolvable_of_isSolvable_injective** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：isSolvable_of_isSolvable_injective (hf : Function.Injective f) [IsSolvable
 G'] : IsSolvable G
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.isSolvable_of_ker_le_range`：isSolvable_of_ker_le_range {G' G'' : T
ype*} [Group G'] [Group G''] (f : G' ->* G) (g : G ->* G'') (hfg : g.ker <= f.ra
nge) [hG' : IsSolvable…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.ker_eq_bot`：ker_eq_bot (f : G ->* M) (hf : Function.Injective 
f) : f.ker = ⊥
-/
theorem isSolvable_of_isSolvable_injective (hf : Function.Injective f) [IsSolvable G'] :
    IsSolvable G :=
  isSolvable_of_ker_le_range (1 : G' →* G) f ((f.ker_eq_bot hf).symm ▸ bot_le)

@[deprecated (since := "2026-07-16")]
alias _root_.solvable_of_solvable_injective := isSolvable_of_isSolvable_injective
/-
**Group.** 是 Mathlib 中的一个实例，位于命名空间 `Group`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (H : Subgroup G) [IsSolvable G] : IsSolvable H :=
  isSolvable_of_isSolvable_injective H.subtype_injective
/-
**Group.isSolvable_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：isSolvable_of_surjective (hf : Function.Surjective f) [IsSolvable G] : IsS
olvable G'
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.isSolvable_of_ker_le_range`：isSolvable_of_ker_le_range {G' G'' : T
ype*} [Group G'] [Group G''] (f : G' ->* G) (g : G ->* G'') (hfg : g.ker <= f.ra
nge) [hG' : IsSolvable…
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.range_eq_top_of_surjective`：range_eq_top_of_surjective {N} [Gr
oup N] (f : G ->* N) (hf : Function.Surjective f) : f.range = (⊤ : Subgroup N)
-/
theorem isSolvable_of_surjective (hf : Function.Surjective f) [IsSolvable G] : IsSolvable G' :=
  isSolvable_of_ker_le_range f (1 : G' →* G) (f.range_eq_top_of_surjective hf ▸ le_top)

@[deprecated (since := "2026-07-16")]
alias _root_.solvable_of_surjective := isSolvable_of_surjective
/-
**Group.** 是 Mathlib 中的一个实例，位于命名空间 `Group`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (H : Subgroup G) [H.Normal] [IsSolvable G] :
    IsSolvable (G ⧸ H) :=
  isSolvable_of_surjective (QuotientGroup.mk'_surjective H)
/-
**Group.isSolvable_iff_subgroup_quotient** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：isSolvable_iff_subgroup_quotient (H : Subgroup G) [H.Normal] : IsSolvable 
G ↔ IsSolvable H ∧ IsSolvable (G ⧸ H)
参数：H : Subgroup G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.instIsSolvableSubtypeMemSubgroup`：∀ {G : Type u_1} [inst : Group G
] (H : Subgroup G) [Group.IsSolvable G], Group.IsSolvable ↥H
· 使用定理 `Group.instIsSolvableQuotientSubgroup`：∀ {G : Type u_1} [inst : Group G] 
(H : Subgroup G) [inst_1 : H.Normal] [Group.IsSolvable G], Group.IsSolvable (G ⧸
 H)
· 使用定理 `Group.isSolvable_of_ker_le_range`：isSolvable_of_ker_le_range {G' G'' : T
ype*} [Group G'] [Group G''] (f : G' ->* G) (g : G ->* G'') (hfg : g.ker <= f.ra
nge) [hG' : IsSolvable…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.ker_mk'`：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G 
->* G ⧸ N) = N
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
-/
theorem isSolvable_iff_subgroup_quotient (H : Subgroup G) [H.Normal] :
    IsSolvable G ↔ IsSolvable H ∧ IsSolvable (G ⧸ H) :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦
    isSolvable_of_ker_le_range H.subtype (QuotientGroup.mk' H) (by simp)⟩
/-
**Group.** 是 Mathlib 中的一个实例，位于命名空间 `Group`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G' : Type*} [Group G'] [IsSolvable G] [IsSolvable G'] :
    IsSolvable (G × G') :=
  isSolvable_of_ker_le_range (MonoidHom.inl G G') (MonoidHom.snd G G') fun x hx =>
    ⟨x.1, Prod.ext rfl hx.symm⟩

variable (G) in
/-
**Group.IsSolvable.commutator_lt_top_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Gr
oup.IsSolvable`。
形式化陈述：∀ (G : Type u_1) [inst : Group G] [hG : Group.IsSolvable G] [Nontrivial G]
, commutator G < ⊤
参数：G : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `derivedSeries_zero`：derivedSeries_zero : derivedSeries G 0 = ⊤
· 使用定理 `derivedSeries_succ`：derivedSeries_succ (n : Nat) : derivedSeries G (n + 
1) = ⁅derivedSeries G n, derivedSeries G n⁆
· 使用定理 `top_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : BoundedOrde
r α] [Nontrivial α], ⊤ ≠ ⊥
· 使用定理 `Subgroup.instNontrivial`：∀ {G : Type u_1} [inst : Group G] [Nontrivial G
], Nontrivial (Subgroup G)
-/
theorem IsSolvable.commutator_lt_top_of_nontrivial [hG : IsSolvable G] [Nontrivial G] :
    commutator G < ⊤ := by
  rw [lt_top_iff_ne_top]
  obtain ⟨n, hn⟩ := hG
  contrapose! hn
  refine ne_of_eq_of_ne ?_ top_ne_bot
  induction n with
  | zero => exact derivedSeries_zero G
  | succ n h => rwa [derivedSeries_succ, h]

@[deprecated (since := "2026-07-16")]
alias _root_.IsSolvable.commutator_lt_top_of_nontrivial :=
  Group.IsSolvable.commutator_lt_top_of_nontrivial
/-
**Group.IsSolvable.commutator_lt_of_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Group.IsSo
lvable`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] [Group.IsSolvable G] {H : Subgroup G}, H
 ≠ ⊥ → ⁅H, H⁆ < H
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Subgroup.map_commutator`：map_commutator (f : G ->* G') : map f ⁅H₁, H₂⁆ 
= ⁅map f H₁, map f H₂⁆
· 使用定理 `Subgroup.map_subtype_lt_map_subtype`：map_subtype_lt_map_subtype {G' : Su
bgroup G} {H K : Subgroup G'} : H.map G'.subtype < K.map G'.subtype ↔ H < K
· 使用定理 `Group.IsSolvable.commutator_lt_top_of_nontrivial`：∀ (G : Type u_1) [inst
 : Group G] [hG : Group.IsSolvable G] [Nontrivial G], commutator G < ⊤
· 使用定理 `Group.instIsSolvableSubtypeMemSubgroup`：∀ {G : Type u_1} [inst : Group G
] (H : Subgroup G) [Group.IsSolvable G], Group.IsSolvable ↥H
· 使用定理 `Subgroup.nontrivial_iff_ne_bot`：nontrivial_iff_ne_bot (H : Subgroup G) :
 Nontrivial H ↔ H != ⊥
-/
theorem IsSolvable.commutator_lt_of_ne_bot [IsSolvable G] {H : Subgroup G} (hH : H ≠ ⊥) :
    ⁅H, H⁆ < H := by
  rw [← nontrivial_iff_ne_bot] at hH
  rw [← H.range_subtype, MonoidHom.range_eq_map, ← map_commutator, map_subtype_lt_map_subtype]
  exact commutator_lt_top_of_nontrivial H

@[deprecated (since := "2026-07-16")]
alias _root_.IsSolvable.commutator_lt_of_ne_bot := Group.IsSolvable.commutator_lt_of_ne_bot
/-
**Group.isSolvable_iff_commutator_lt** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：isSolvable_iff_commutator_lt [WellFoundedLT (Subgroup G)] : IsSolvable G ↔
 forall H : Subgroup G, H != ⊥ -> ⁅H, H⁆ < H
参数：Subgroup G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.IsSolvable.commutator_lt_of_ne_bot`：∀ {G : Type u_1} [inst : Group
 G] [Group.IsSolvable G] {H : Subgroup G}, H ≠ ⊥ → ⁅H, H⁆ < H
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Group.instIsSolvableOfSubsingleton`：∀ (G : Type u_1) [inst : Group G] [S
ubsingleton G], Group.IsSolvable G
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_subtype_inj`：map_subtype_inj {H : Subgroup G} {K L : Subgro
up H} : K.map H.subtype = L.map H.subtype ↔ K = L
· 使用定理 `Subgroup.map_bot`：map_bot (f : G ->* N) : (⊥ : Subgroup G).map f = ⊥
· 使用定理 `derivedSeries_succ`：derivedSeries_succ (n : Nat) : derivedSeries G (n + 
1) = ⁅derivedSeries G n, derivedSeries G n⁆
· 使用定理 `derivedSeries_zero`：derivedSeries_zero : derivedSeries G 0 = ⊤
· 使用定理 `Subgroup.map_commutator`：map_commutator (f : G ->* G') : map f ⁅H₁, H₂⁆ 
= ⁅map f H₁, map f H₂⁆
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用定理 `Group.isSolvable_of_surjective`：isSolvable_of_surjective (hf : Function.
Surjective f) [IsSolvable G] : IsSolvable G'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
-/
theorem isSolvable_iff_commutator_lt [WellFoundedLT (Subgroup G)] :
    IsSolvable G ↔ ∀ H : Subgroup G, H ≠ ⊥ → ⁅H, H⁆ < H := by
  refine ⟨fun _ _ ↦ IsSolvable.commutator_lt_of_ne_bot, fun h ↦ ?_⟩
  suffices h : IsSolvable (⊤ : Subgroup G) from
    isSolvable_of_surjective (MonoidHom.range_eq_top.mp (range_subtype ⊤))
  induction (⊤ : Subgroup G) using WellFoundedLT.induction with | ind H hH
  rcases eq_or_ne H ⊥ with rfl | h'
  · infer_instance
  · obtain ⟨n, hn⟩ := hH ⁅H, H⁆ (h H h')
    use n + 1
    rw [← map_subtype_inj, Subgroup.map_bot] at hn ⊢
    rw [← hn]
    clear hn
    induction n with
    | zero =>
      rw [derivedSeries_succ, derivedSeries_zero, derivedSeries_zero, map_commutator,
        ← MonoidHom.range_eq_map, ← MonoidHom.range_eq_map, range_subtype, range_subtype]
    | succ n ih => rw [derivedSeries_succ, map_commutator, ih, derivedSeries_succ, map_commutator]

@[deprecated (since := "2026-07-16")]
alias _root_.isSolvable_iff_commutator_lt := Group.isSolvable_iff_commutator_lt

end Group

end Solvable

section IsSimpleGroup

variable [IsSimpleGroup G]

/-
**IsSimpleGroup.derivedSeries_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSimpleGroup.derivedSeries_succ {n : Nat} : derivedSeries G n.succ = comm
utator G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivedSeries_one`：derivedSeries_one : derivedSeries G 1 = commutator G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivedSeries_succ`：derivedSeries_succ (n : Nat) : derivedSeries G (n + 
1) = ⁅derivedSeries G n, derivedSeries G n⁆
· 使用定理 `commutator.eq_1`：∀ (G : Type u_1) [inst : Group G], commutator G = ⁅⊤, ⊤
⁆
· 使用定理 `Subgroup.Normal.eq_bot_or_eq_top`：Subgroup.Normal.eq_bot_or_eq_top [IsSi
mpleGroup G] {H : Subgroup G} (Hn : H.Normal) : H = ⊥ ∨ H = ⊤
· 使用定理 `Subgroup.commutator_bot_left`：commutator_bot_left : ⁅(⊥ : Subgroup G), H
₁⁆ = ⊥
-/
theorem IsSimpleGroup.derivedSeries_succ {n : ℕ} : derivedSeries G n.succ = commutator G := by
  induction n with
  | zero => exact derivedSeries_one G
  | succ n ih =>
    rw [_root_.derivedSeries_succ, ih, _root_.commutator]
    rcases (commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with h | h
    · rw [h, commutator_bot_left]
    · rwa [h]
/-
**IsSimpleGroup.comm_iff_isSolvable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSimpleGroup.comm_iff_isSolvable : (forall a b : G, a * b = b * a) ↔ Grou
p.IsSolvable G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.isSolvable_of_comm`：isSolvable_of_comm {G : Type*} [hG : Group G] 
(h : forall a b : G, a * b = b * a) : IsSolvable G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_bot`：mem_bot {x : G} : x in (⊥ : Subgroup G) ↔ x = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.mem_top`：mem_top (x : G) : x in (⊤ : Subgroup G)
· 使用定理 `mul_inv_eq_one`：mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsSimpleGroup.derivedSeries_succ`：IsSimpleGroup.derivedSeries_succ {n : 
Nat} : derivedSeries G n.succ = commutator G
· 使用引理 `commutator_eq_closure`：commutator_eq_closure : commutator G = Subgroup.c
losure (commutatorSet G)
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
-/
theorem IsSimpleGroup.comm_iff_isSolvable : (∀ a b : G, a * b = b * a) ↔ Group.IsSolvable G :=
  ⟨Group.isSolvable_of_comm, fun ⟨⟨n, hn⟩⟩ => by
    cases n
    · intro a b
      refine (mem_bot.1 ?_).trans (mem_bot.1 ?_).symm <;>
        · rw [← hn]
          exact mem_top _
    · rw [IsSimpleGroup.derivedSeries_succ] at hn
      intro a b
      rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← mem_bot, ← hn, commutator_eq_closure]
      exact subset_closure ⟨a, b, rfl⟩⟩

end IsSimpleGroup

section PermNotSolvable

/-
**not_isSolvable_of_mem_derivedSeries** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isSolvable_of_mem_derivedSeries {g : G} (h1 : g != 1) (h2 : forall n :
 Nat, g in derivedSeries G n) : ¬Group.IsSolvable G
参数：h1 : g != 1；h2 : forall n : Nat, g in derivedSeries G n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Group.isSolvable_def`：∀ (G : Type u_1) [inst : Group G], Group.IsSolvabl
e G ↔ ∃ n, derivedSeries G n = ⊥
· 使用定理 `not_exists_of_forall_not`：∀ {α : Sort u_1} {p : α → Prop}, (∀ (x : α), ¬
p x) → ¬∃ x, p x
· 使用定理 `Subgroup.mem_bot`：mem_bot {x : G} : x in (⊥ : Subgroup G) ↔ x = 1
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem not_isSolvable_of_mem_derivedSeries {g : G} (h1 : g ≠ 1)
    (h2 : ∀ n : ℕ, g ∈ derivedSeries G n) : ¬Group.IsSolvable G :=
  mt (Group.isSolvable_def _).mp
    (not_exists_of_forall_not fun n h =>
      h1 (Subgroup.mem_bot.mp ((congr_arg (g ∈ ·) h).mp (h2 n))))

@[deprecated (since := "2026-07-16")]
alias not_solvable_of_mem_derivedSeries := not_isSolvable_of_mem_derivedSeries
/-
**Equiv.Perm.not_isSolvable_fin_5** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.not_isSolvable_fin_5 : ¬Group.IsSolvable (Equiv.Perm (Fin 5))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `not_isSolvable_of_mem_derivedSeries`：not_isSolvable_of_mem_derivedSeries
 {g : G} (h1 : g != 1) (h2 : forall n : Nat, g in derivedSeries G n) : ¬Group.Is
Solvable G
· 使用定理 `Subgroup.mem_top`：mem_top (x : G) : x in (⊤ : Subgroup G)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.Normal.mem_comm_iff`：mem_comm_iff (nH : H.Normal) {a b : G} : a
 * b in H ↔ b * a in H
· 使用定理 `derivedSeries_normal`：derivedSeries_normal (n : Nat) : (derivedSeries G 
n).Normal
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `Subgroup.commutator_mem_commutator`：commutator_mem_commutator (h₁ : g₁ i
n H₁) (h₂ : g₂ in H₂) : ⁅g₁, g₂⁆ in ⁅H₁, H₂⁆
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
-/
theorem Equiv.Perm.not_isSolvable_fin_5 : ¬Group.IsSolvable (Equiv.Perm (Fin 5)) := by
  let x : Equiv.Perm (Fin 5) := ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide, by decide⟩
  let y : Equiv.Perm (Fin 5) := ⟨![3, 4, 2, 0, 1], ![3, 4, 2, 0, 1], by decide, by decide⟩
  let z : Equiv.Perm (Fin 5) := ⟨![0, 3, 2, 1, 4], ![0, 3, 2, 1, 4], by decide, by decide⟩
  have key : x = z * ⁅x, y * x * y⁻¹⁆ * z⁻¹ := by unfold x y z; decide
  refine not_isSolvable_of_mem_derivedSeries (show x ≠ 1 by decide) fun n => ?_
  induction n with
  | zero => exact mem_top x
  | succ n ih =>
    rw [key, (derivedSeries_normal _ _).mem_comm_iff, inv_mul_cancel_left]
    exact commutator_mem_commutator ih ((derivedSeries_normal _ _).conj_mem _ ih _)

@[deprecated (since := "2026-07-16")]
alias Equiv.Perm.fin_5_not_solvable := Equiv.Perm.not_isSolvable_fin_5
/-
**Equiv.Perm.not_isSolvable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.not_isSolvable (X : Type*) (hX : 5 <= Cardinal.mk X) : ¬Group.I
sSolvable (Equiv.Perm X)
参数：X : Type*；hX : 5 <= Cardinal.mk X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_mk_le`：lift_mk_le {α : Type v} {β : Type w} : lift.{max u 
w} #α <= lift.{max u v} #β ↔ Nonempty (α ↪ β)
· 使用定理 `Cardinal.mk_fin`：mk_fin (n : Nat) : #(Fin n) = n
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Equiv.Perm.not_isSolvable_fin_5`：Equiv.Perm.not_isSolvable_fin_5 : ¬Grou
p.IsSolvable (Equiv.Perm (Fin 5))
· 使用定理 `Group.isSolvable_of_isSolvable_injective`：isSolvable_of_isSolvable_injec
tive (hf : Function.Injective f) [IsSolvable G'] : IsSolvable G
· 使用定理 `Equiv.Perm.viaEmbeddingHom_injective`：viaEmbeddingHom_injective : Functi
on.Injective (viaEmbeddingHom ι)
-/
theorem Equiv.Perm.not_isSolvable (X : Type*) (hX : 5 ≤ Cardinal.mk X) :
    ¬Group.IsSolvable (Equiv.Perm X) := by
  intro h
  have key : Nonempty (Fin 5 ↪ X) := by
    rwa [← Cardinal.lift_mk_le, Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_id]
  exact
    Equiv.Perm.not_isSolvable_fin_5 (Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Nonempty.some key)))

@[deprecated (since := "2026-07-16")]
alias Equiv.Perm.not_solvable := Equiv.Perm.not_isSolvable

end PermNotSolvable

