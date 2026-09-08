/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Nilpotent
public import Mathlib.Algebra.Lie.Normalizer

/-!
# Cartan subalgebras

Cartan subalgebras are one of the most important concepts in Lie theory. We define them here.
The standard example is the set of diagonal matrices in the Lie algebra of matrices.

## Main definitions

  * `LieSubmodule.IsUcsLimit`
  * `LieSubalgebra.IsCartanSubalgebra`
  * `LieSubalgebra.isCartanSubalgebra_iff_isUcsLimit`

## Tags

lie subalgebra, normalizer, idealizer, cartan subalgebra
-/

@[expose] public section


universe u v w w₁ w₂

variable {R : Type u} {L : Type v}
variable [CommRing R] [LieRing L] [LieAlgebra R L] (H : LieSubalgebra R L)

/-- Given a Lie module `M` of a Lie algebra `L`, `LieSubmodule.IsUcsLimit` is the proposition
that a Lie submodule `N ⊆ M` is the limiting value for the upper central series.

This is a characteristic property of Cartan subalgebras with the roles of `L`, `M`, `N` played by
`H`, `L`, `H`, respectively. See `LieSubalgebra.isCartanSubalgebra_iff_isUcsLimit`. -/
/-
**LieSubmodule.IsUcsLimit** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LieSubmodule.IsUcsLimit {M : Type*} [AddCommGroup M] [Module R M] [LieRing
Module L M] [LieModule R L M] (N : LieSubmodule R L M) : Prop
参数：N : LieSubmodule R L M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Lie module `M` of a Lie algebra `L`, `LieSubmodule.IsUcsLimit` is the pr
oposition
that a Lie submodule `N ⊆ M` is the limiting value for the upper central series.

This is a characteristic property of Cartan subalgebras with the roles of `L`, `
M`, `N` played by
`H`, `L`, `H`, respectively. See `LieSubalgebra.isCartanSubalgebra_iff_isUcsLimi
t`.
-/
def LieSubmodule.IsUcsLimit {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M]
    [LieModule R L M] (N : LieSubmodule R L M) : Prop :=
  ∃ k, ∀ l, k ≤ l → (⊥ : LieSubmodule R L M).ucs l = N

namespace LieSubalgebra

/-- A Cartan subalgebra is a nilpotent, self-normalizing subalgebra.

A _splitting_ Cartan subalgebra can be defined by mixing in `LieModule.IsTriangularizable R H L`. -/
/-
**LieSubalgebra.IsCartanSubalgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieSubalgebra`。
形式化陈述：{R : Type u} →   {L : Type v} → [inst : CommRing R] → [inst_1 : LieRing L]
 → [inst_2 : LieAlgebra R L] → LieSubalgebra R L → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Cartan subalgebra is a nilpotent, self-normalizing subalgebra.

A _splitting_ Cartan subalgebra can be defined by mixing in `LieModule.IsTriangu
larizable R H L`.
-/
class IsCartanSubalgebra : Prop where
  nilpotent : LieRing.IsNilpotent H
  self_normalizing : H.normalizer = H
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [H.IsCartanSubalgebra] : LieRing.IsNilpotent H :=
  IsCartanSubalgebra.nilpotent

@[simp]
/-
**LieSubalgebra.normalizer_eq_self_of_isCartanSubalgebra** 是 Mathlib 中的一个定理，位于命名
空间 `LieSubalgebra`。
形式化陈述：normalizer_eq_self_of_isCartanSubalgebra (H : LieSubalgebra R L) [H.IsCart
anSubalgebra] : H.toLieSubmodule.normalizer = H.toLieSubmodule
参数：H : LieSubalgebra R L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubalgebra.coe_normalizer_eq_normalizer`：coe_normalizer_eq_normalizer
 : (H.toLieSubmodule.normalizer : Submodule R L) = H.normalizer
· 使用定理 `LieSubalgebra.IsCartanSubalgebra.self_normalizing`：∀ {R : Type u} {L : T
ype v} {inst : CommRing R} {inst_1 : LieRing L} {inst_2 : LieAlgebra R L} {H : L
ieSubalgebra R L}   [self : H.IsCartanS…
· 使用定理 `LieSubalgebra.coe_toLieSubmodule`：coe_toLieSubmodule : (K.toLieSubmodule
 : Submodule R L) = K
-/
theorem normalizer_eq_self_of_isCartanSubalgebra (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    H.toLieSubmodule.normalizer = H.toLieSubmodule := by
  rw [← LieSubmodule.toSubmodule_inj, coe_normalizer_eq_normalizer,
    IsCartanSubalgebra.self_normalizing, coe_toLieSubmodule]

@[simp]
/-
**LieSubalgebra.ucs_eq_self_of_isCartanSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `Lie
Subalgebra`。
形式化陈述：ucs_eq_self_of_isCartanSubalgebra (H : LieSubalgebra R L) [H.IsCartanSubal
gebra] (k : Nat) : H.toLieSubmodule.ucs k = H.toLieSubmodule
参数：H : LieSubalgebra R L；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.ucs_succ`：ucs_succ (k : Nat) : N.ucs (k + 1) = (N.ucs k).no
rmalizer
· 使用定理 `LieSubmodule.normalizer.congr_simp`：∀ {R : Type u_1} {L : Type u_2} {M :
 Type u_3} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   
[inst_3 : AddCommGroup M…
· 使用定理 `LieSubalgebra.normalizer_eq_self_of_isCartanSubalgebra`：normalizer_eq_se
lf_of_isCartanSubalgebra (H : LieSubalgebra R L) [H.IsCartanSubalgebra] : H.toLi
eSubmodule.normalizer = H.toLieSubmodule
-/
theorem ucs_eq_self_of_isCartanSubalgebra (H : LieSubalgebra R L) [H.IsCartanSubalgebra] (k : ℕ) :
    H.toLieSubmodule.ucs k = H.toLieSubmodule := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih]
/-
**LieSubalgebra.isCartanSubalgebra_iff_isUcsLimit** 是 Mathlib 中的一个定理，位于命名空间 `Lie
Subalgebra`。
形式化陈述：isCartanSubalgebra_iff_isUcsLimit : H.IsCartanSubalgebra ↔ H.toLieSubmodul
e.IsUcsLimit
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LieSubmodule.isNilpotent_iff_exists_self_le_ucs`：isNilpotent_iff_exists_
self_le_ucs : LieModule.IsNilpotent L N ↔ exists k, N <= (⊥ : LieSubmodule R L M
).ucs k
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LieSubmodule.ucs_le_of_normalizer_eq_self`：ucs_le_of_normalizer_eq_self 
(h : N₁.normalizer = N₁) (k : Nat) : (⊥ : LieSubmodule R L M).ucs k <= N₁
· 使用定理 `LieSubalgebra.normalizer_eq_self_of_isCartanSubalgebra`：normalizer_eq_se
lf_of_isCartanSubalgebra (H : LieSubalgebra R L) [H.IsCartanSubalgebra] : H.toLi
eSubmodule.normalizer = H.toLieSubmodule
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `LieSubmodule.ucs_add`：ucs_add (k l : Nat) : N.ucs (k + l) = (N.ucs l).uc
s k
· 使用定理 `LieSubalgebra.ucs_eq_self_of_isCartanSubalgebra`：ucs_eq_self_of_isCartan
Subalgebra (H : LieSubalgebra R L) [H.IsCartanSubalgebra] (k : Nat) : H.toLieSub
module.ucs k = H.toLieSubmodule
· 使用定理 `LieSubmodule.isNilpotent_iff_exists_lcs_eq_bot`：∀ {R : Type u} {L : Type
 v} {M : Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L]   [inst_3 : AddCommGroup M] [ins…
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `LieSubmodule.lcs_le_iff`：lcs_le_iff (k : Nat) : N₁.lcs k <= N₂ ↔ N₁ <= N
₂.ucs k
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `LieSubalgebra.toSubmodule_inj`：toSubmodule_inj (L₁' L₂' : LieSubalgebra 
R L) : (L₁' : Submodule R L) = (L₂' : Submodule R L) ↔ L₁' = L₂'
· 使用定理 `LieSubalgebra.coe_normalizer_eq_normalizer`：coe_normalizer_eq_normalizer
 : (H.toLieSubmodule.normalizer : Submodule R L) = H.normalizer
· 使用定理 `LieSubmodule.ucs_succ`：ucs_succ (k : Nat) : N.ucs (k + 1) = (N.ucs k).no
rmalizer
· 使用定理 `LieSubalgebra.coe_toLieSubmodule`：coe_toLieSubmodule : (K.toLieSubmodule
 : Submodule R L) = K
-/
theorem isCartanSubalgebra_iff_isUcsLimit : H.IsCartanSubalgebra ↔ H.toLieSubmodule.IsUcsLimit := by
  constructor
  · intro h
    have h₁ : LieRing.IsNilpotent H := by infer_instance
    obtain ⟨k, hk⟩ := H.toLieSubmodule.isNilpotent_iff_exists_self_le_ucs.mp h₁
    replace hk : H.toLieSubmodule = LieSubmodule.ucs k ⊥ :=
      le_antisymm hk
        (LieSubmodule.ucs_le_of_normalizer_eq_self H.normalizer_eq_self_of_isCartanSubalgebra k)
    refine ⟨k, fun l hl => ?_⟩
    rw [← Nat.sub_add_cancel hl, LieSubmodule.ucs_add, ← hk,
      LieSubalgebra.ucs_eq_self_of_isCartanSubalgebra]
  · rintro ⟨k, hk⟩
    exact
      { nilpotent := by
          dsimp only [LieRing.IsNilpotent]
          -- The instance for the second `H` in the goal is `lieRingSelfModule`
          -- but `rw` expects it to be `H.toLieSubmodule.instLieRingModuleSubtypeMem`,
          -- and these are not reducibly defeq.
          erw [H.toLieSubmodule.isNilpotent_iff_exists_lcs_eq_bot]
          use k
          rw [_root_.eq_bot_iff, LieSubmodule.lcs_le_iff, hk k (le_refl k)]
        self_normalizing := by
          have hk' := hk (k + 1) k.le_succ
          rw [LieSubmodule.ucs_succ, hk k (le_refl k)] at hk'
          rw [← LieSubalgebra.toSubmodule_inj, ← LieSubalgebra.coe_normalizer_eq_normalizer,
            hk', LieSubalgebra.coe_toLieSubmodule] }
/-
**LieSubalgebra.ne_bot_of_isCartanSubalgebra** 是 Mathlib 中的一个引理，位于命名空间 `LieSubal
gebra`。
形式化陈述：ne_bot_of_isCartanSubalgebra [Nontrivial L] (H : LieSubalgebra R L) [H.IsC
artanSubalgebra] : H != ⊥
参数：H : LieSubalgebra R L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
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
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LieSubalgebra.IsCartanSubalgebra.self_normalizing`：∀ {R : Type u} {L : T
ype v} {inst : CommRing R} {inst_1 : LieRing L} {inst_2 : LieAlgebra R L} {H : L
ieSubalgebra R L}   [self : H.IsCartanS…
-/
lemma ne_bot_of_isCartanSubalgebra [Nontrivial L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    H ≠ ⊥ := by
  intro e
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have : x ∈ H.normalizer := by simp [LieSubalgebra.mem_normalizer_iff, e]
  exact hx (by rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing, e] at this)
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 500) [Nontrivial L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    Nontrivial H := by
  refine (subsingleton_or_nontrivial H).elim (fun inst ↦ False.elim ?_) id
  apply ne_bot_of_isCartanSubalgebra H
  rw [eq_bot_iff]
  exact fun x hx ↦ congr_arg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : H) 0)

end LieSubalgebra

@[simp]
/-
**LieIdeal.normalizer_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieIdeal.normalizer_eq_top {R : Type u} {L : Type v} [CommRing R] [LieRing
 L] [LieAlgebra R L] (I : LieIdeal R L) : (I : LieSubalgebra R L).normalizer = ⊤
参数：I : LieIdeal R L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.ext`：ext (L₁' L₂' : LieSubalgebra R L) (h : forall x, x in
 L₁' ↔ x in L₂') : L₁' = L₂'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
-/
theorem LieIdeal.normalizer_eq_top {R : Type u} {L : Type v} [CommRing R] [LieRing L]
    [LieAlgebra R L] (I : LieIdeal R L) : (I : LieSubalgebra R L).normalizer = ⊤ := by
  ext x
  simpa only [LieSubalgebra.mem_normalizer_iff, LieSubalgebra.mem_top, iff_true] using!
    fun y hy => I.lie_mem hy

open LieIdeal

/-- A nilpotent Lie algebra is its own Cartan subalgebra. -/
/-
**LieAlgebra.top_isCartanSubalgebra_of_nilpotent** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LieAlgebra.top_isCartanSubalgebra_of_nilpotent [LieRing.IsNilpotent L] : L
ieSubalgebra.IsCartanSubalgebra (⊤ : LieSubalgebra R L) where nilpotent
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsNilpotentSubtypeMemLieSubalgebraTop`：∀ {R : Type u} {L : Type v} [
inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [h : LieRing
.IsNilpotent L], LieRing.IsNilp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieIdeal.top_toLieSubalgebra`：top_toLieSubalgebra : ((⊤ : LieIdeal R L) 
: LieSubalgebra R L) = ⊤
· 使用定理 `LieIdeal.normalizer_eq_top`：LieIdeal.normalizer_eq_top {R : Type u} {L :
 Type v} [CommRing R] [LieRing L] [LieAlgebra R L] (I : LieIdeal R L) : (I : Lie
Subalgebra R L).…

--- 原说明 ---
A nilpotent Lie algebra is its own Cartan subalgebra.
-/
instance LieAlgebra.top_isCartanSubalgebra_of_nilpotent [LieRing.IsNilpotent L] :
    LieSubalgebra.IsCartanSubalgebra (⊤ : LieSubalgebra R L) where
  nilpotent := inferInstance
  self_normalizing := by rw [← top_toLieSubalgebra, normalizer_eq_top, top_toLieSubalgebra]
