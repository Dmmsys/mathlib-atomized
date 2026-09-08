/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Commensurability for subgroups

Two subgroups `H` and `K` of a group `G` are commensurable if `H ∩ K` has finite index in both `H`
and `K`.

This file defines commensurability for subgroups of a group `G`. It goes on to prove that
commensurability defines an equivalence relation on subgroups of `G` and finally defines the
commensurator of a subgroup `H` of `G`, which is the elements `g` of `G` such that `gHg⁻¹` is
commensurable with `H`.

## Main definitions

* `Commensurable H K`: the statement that the subgroups `H` and `K` of `G` are commensurable.
* `commensurator H`: the commensurator of a subgroup `H` of `G`.

## Implementation details

We define the commensurator of a subgroup `H` of `G` by first defining it as a subgroup of
`(conjAct G)`, which we call `commensurator'` and then taking the pre-image under
the map `G → (conjAct G)` to obtain our commensurator as a subgroup of `G`.

We define `Commensurable` both for additive and multiplicative groups (in the `AddSubgroup` and
`Subgroup` namespaces respectively); but `Commensurator` is not additivized, since it is not an
interesting concept for abelian groups, and it would be unusual to write a non-abelian group
additively.
-/

@[expose] public section

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Equivalence of `K / (H ⊓ K)` with `gKg⁻¹/ (gHg⁻¹ ⊓ gKg⁻¹)` -/
/-
**Subgroup.quotConjEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subgroup.quotConjEquiv (H K : Subgroup G) (g : ConjAct G) : K ⧸ H.subgroup
Of K ≃ (g • K : Subgroup G) ⧸ (g • H).subgroupOf (g • K)
参数：H K : Subgroup G；g : ConjAct G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence of `K / (H ⊓ K)` with `gKg⁻¹/ (gHg⁻¹ ⊓ gKg⁻¹)`
-/
def Subgroup.quotConjEquiv (H K : Subgroup G) (g : ConjAct G) :
    K ⧸ H.subgroupOf K ≃ (g • K : Subgroup G) ⧸ (g • H).subgroupOf (g • K) :=
  Quotient.congr (K.equivSMul g).toEquiv fun a b ↦ by
    dsimp
    rw [← Quotient.eq'', ← Quotient.eq'', QuotientGroup.eq, QuotientGroup.eq,
      mem_subgroupOf, mem_subgroupOf, ← map_inv, ← map_mul, equivSMul_apply_coe]
    exact smul_mem_pointwise_smul_iff.symm

/-- Two subgroups `H K` of `G` are commensurable if `H ⊓ K` has finite index in both `H` and `K`. -/
@[to_additive /-- Two subgroups `H K` of `G` are commensurable if `H ⊓ K` has finite index in both
`H` and `K`. -/]
/-
**Subgroup.Commensurable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subgroup.Commensurable (H K : Subgroup G) : Prop
参数：H K : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Subgroup.Commensurable (H K : Subgroup G) : Prop :=
  H.relIndex K ≠ 0 ∧ K.relIndex H ≠ 0

namespace Subgroup.Commensurable

@[to_additive (attr := refl)]
/-
**Subgroup.Commensurable.refl** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Commensurable`
。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), H.Commensurable H
参数：H : Subgroup G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.relIndex_self`：relIndex_self : H.relIndex H = 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
protected theorem refl (H : Subgroup G) : Commensurable H H := by simp [Commensurable]

@[to_additive]
/-
**Subgroup.Commensurable.comm** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Commensurable`
。
形式化陈述：comm {H K : Subgroup G} : Commensurable H K ↔ Commensurable K H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem comm {H K : Subgroup G} : Commensurable H K ↔ Commensurable K H := and_comm

@[to_additive (attr := symm)]
/-
**Subgroup.Commensurable.symm** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Commensurable`
。
形式化陈述：symm {H K : Subgroup G} : Commensurable H K -> Commensurable K H
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
-/
theorem symm {H K : Subgroup G} : Commensurable H K → Commensurable K H := And.symm

@[to_additive (attr := trans)]
/-
**Subgroup.Commensurable.trans** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Commensurable
`。
形式化陈述：trans {H K L : Subgroup G} (hhk : Commensurable H K) (hkl : Commensurable 
K L) : Commensurable H L
参数：hhk : Commensurable H K；hkl : Commensurable K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.relIndex_ne_zero_trans`：relIndex_ne_zero_trans (hHK : H.relInde
x K != 0) (hKL : K.relIndex L != 0) : H.relIndex L != 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem trans {H K L : Subgroup G} (hhk : Commensurable H K) (hkl : Commensurable K L) :
    Commensurable H L :=
  ⟨Subgroup.relIndex_ne_zero_trans hhk.1 hkl.1, Subgroup.relIndex_ne_zero_trans hkl.2 hhk.2⟩

@[to_additive]
/-
**Subgroup.Commensurable.equivalence** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Commens
urable`。
形式化陈述：equivalence : Equivalence (@Commensurable G _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Commensurable.refl`：∀ {G : Type u_1} [inst : Group G] (H : Subg
roup G), H.Commensurable H
· 使用定理 `Subgroup.Commensurable.symm`：symm {H K : Subgroup G} : Commensurable H K
 -> Commensurable K H
· 使用定理 `Subgroup.Commensurable.trans`：trans {H K L : Subgroup G} (hhk : Commensu
rable H K) (hkl : Commensurable K L) : Commensurable H L
-/
theorem equivalence : Equivalence (@Commensurable G _) :=
  ⟨Commensurable.refl, fun h => Commensurable.symm h, fun h₁ h₂ => Commensurable.trans h₁ h₂⟩
/-
**Subgroup.Commensurable.commensurable_conj** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.
Commensurable`。
形式化陈述：commensurable_conj {H K : Subgroup G} (g : ConjAct G) : Commensurable H K 
↔ Commensurable (g • H) (g • K)
参数：g : ConjAct G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Eq.congr_left`：∀ {α : Sort u_1} {x y z : α}, x = y → (x = z ↔ y = z)
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem commensurable_conj {H K : Subgroup G} (g : ConjAct G) :
    Commensurable H K ↔ Commensurable (g • H) (g • K) :=
  and_congr (not_iff_not.mpr (Eq.congr_left (Nat.card_congr (quotConjEquiv H K g))))
    (not_iff_not.mpr (Eq.congr_left (Nat.card_congr (quotConjEquiv K H g))))

/-- Alias for the forward direction of `commensurable_conj` to allow dot-notation -/
/-
**Subgroup.Commensurable.conj** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Commensurable`
。
形式化陈述：conj {H K : Subgroup G} (h : Commensurable H K) (g : ConjAct G) : Commensu
rable (g • H) (g • K)
参数：h : Commensurable H K；g : ConjAct G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.Commensurable.commensurable_conj`：commensurable_conj {H K : Sub
group G} (g : ConjAct G) : Commensurable H K ↔ Commensurable (g • H) (g • K)

--- 原说明 ---
Alias for the forward direction of `commensurable_conj` to allow dot-notation
-/
theorem conj {H K : Subgroup G} (h : Commensurable H K) (g : ConjAct G) :
    Commensurable (g • H) (g • K) :=
  (commensurable_conj g).mp h
/-
**Subgroup.Commensurable.commensurable_inv** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.C
ommensurable`。
形式化陈述：commensurable_inv (H : Subgroup G) (g : ConjAct G) : Commensurable (g • H)
 H ↔ Commensurable H (g⁻¹ • H)
参数：H : Subgroup G；g : ConjAct G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.Commensurable.commensurable_conj`：commensurable_conj {H K : Sub
group G} (g : ConjAct G) : Commensurable H K ↔ Commensurable (g • H) (g • K)
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem commensurable_inv (H : Subgroup G) (g : ConjAct G) :
    Commensurable (g • H) H ↔ Commensurable H (g⁻¹ • H) := by rw [commensurable_conj, inv_smul_smul]

/-- For `H` a subgroup of `G`, this is the subgroup of all elements `g : conjAut G`
such that `Commensurable (g • H) H` -/
/-
**Subgroup.Commensurable.commensurator'** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup.Comm
ensurable`。
形式化陈述：commensurator' (H : Subgroup G) : Subgroup (ConjAct G) where carrier
参数：H : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `H` a subgroup of `G`, this is the subgroup of all elements `g : conjAut G`
such that `Commensurable (g • H) H`
-/
def commensurator' (H : Subgroup G) : Subgroup (ConjAct G) where
  carrier := { g : ConjAct G | Commensurable (g • H) H }
  one_mem' := by rw [Set.mem_ofPred_eq, one_smul]
  mul_mem' ha hb := by
    rw [Set.mem_ofPred_eq, mul_smul]
    exact trans ((commensurable_conj _).mp hb) ha
  inv_mem' _ := by rwa [Set.mem_ofPred_eq, comm, ← commensurable_inv]

/-- For `H` a subgroup of `G`, this is the subgroup of all elements `g : G`
such that `Commensurable (g H g⁻¹) H` -/
/-
**Subgroup.Commensurable.commensurator** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup.Comme
nsurable`。
形式化陈述：commensurator (H : Subgroup G) : Subgroup G
参数：H : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `H` a subgroup of `G`, this is the subgroup of all elements `g : G`
such that `Commensurable (g H g⁻¹) H`
-/
def commensurator (H : Subgroup G) : Subgroup G :=
  (commensurator' H).comap ConjAct.toConjAct.toMonoidHom

@[simp]
/-
**Subgroup.Commensurable.commensurator'_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgr
oup.Commensurable`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) (g : ConjAct G),   g ∈ 
Subgroup.Commensurable.commensurator' H ↔ (g • H).Commensurable H
参数：H : Subgroup G；g : ConjAct G；g • H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem commensurator'_mem_iff (H : Subgroup G) (g : ConjAct G) :
    g ∈ commensurator' H ↔ Commensurable (g • H) H := Iff.rfl

@[simp]
/-
**Subgroup.Commensurable.commensurator_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgro
up.Commensurable`。
形式化陈述：commensurator_mem_iff (H : Subgroup G) (g : G) : g in commensurator H ↔ Co
mmensurable (ConjAct.toConjAct g • H) H
参数：H : Subgroup G；g : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem commensurator_mem_iff (H : Subgroup G) (g : G) :
    g ∈ commensurator H ↔ Commensurable (ConjAct.toConjAct g • H) H := Iff.rfl
/-
**Subgroup.Commensurable.eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Commensurable`。
形式化陈述：eq {H K : Subgroup G} (hk : Commensurable H K) : commensurator H = commens
urator K
参数：hk : Commensurable H K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.Commensurable.commensurable_conj`：commensurable_conj {H K : Sub
group G} (g : ConjAct G) : Commensurable H K ↔ Commensurable (g • H) (g • K)
· 使用定理 `Subgroup.Commensurable.trans`：trans {H K L : Subgroup G} (hhk : Commensu
rable H K) (hkl : Commensurable K L) : Commensurable H L
· 使用定理 `Subgroup.Commensurable.symm`：symm {H K : Subgroup G} : Commensurable H K
 -> Commensurable K H
-/
theorem eq {H K : Subgroup G} (hk : Commensurable H K) : commensurator H = commensurator K :=
  Subgroup.ext fun x =>
    let hx := (commensurable_conj x).1 hk
    ⟨fun h => hx.symm.trans (h.trans hk), fun h => hx.trans (h.trans hk.symm)⟩

end Subgroup.Commensurable

