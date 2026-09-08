/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Solvable
public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.Algebra.Lie.Normalizer
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Nilpotent Lie algebras

Like groups, Lie algebras admit a natural concept of nilpotency. More generally, any Lie module
carries a natural concept of nilpotency. We define these here via the lower central series.

## Main definitions

  * `LieModule.lowerCentralSeries`
  * `LieModule.IsNilpotent`
  * `LieModule.maxNilpotentSubmodule`
  * `LieAlgebra.maxNilpotentIdeal`

## Tags

lie algebra, lower central series, nilpotent, max nilpotent ideal
-/

@[expose] public section

universe u v w w₁ w₂

section NilpotentModules

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M]
variable (k : ℕ) (N : LieSubmodule R L M)

namespace LieSubmodule

/-- A generalisation of the lower central series. The zeroth term is a specified Lie submodule of
a Lie module. In the case when we specify the top ideal `⊤` of the Lie algebra, regarded as a Lie
module over itself, we get the usual lower central series of a Lie algebra.

It can be more convenient to work with this generalisation when considering the lower central series
of a Lie submodule, regarded as a Lie module in its own right, since it provides a type-theoretic
expression of the fact that the terms of the Lie submodule's lower central series are also Lie
submodules of the enclosing Lie module.

See also `LieSubmodule.lowerCentralSeries_eq_lcs_comap` and
`LieSubmodule.lowerCentralSeries_map_eq_lcs` below, as well as `LieSubmodule.ucs`. -/
/-
**LieSubmodule.lcs** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule`。
形式化陈述：lcs : LieSubmodule R L M -> LieSubmodule R L M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A generalisation of the lower central series. The zeroth term is a specified Lie
 submodule of
a Lie module. In the case when we specify the top ideal `⊤` of the Lie algebra, 
regarded as a Lie
module over itself, we get the usual lower central series of a Lie algebra.

It can be more convenient to work with this generalisation when considering the 
lower central series
of a Lie submodule, regarded as a Lie module in its own right, since it provides
 a type-theoretic
expression of the fact that the terms of the Lie submodule's lower central serie
s are also Lie
submodules of the enclosing Lie module.

See also `LieSubmodule.lowerCentralSeries_eq_lcs_comap` and
`LieSubmodule.lowerCentralSeries_map_eq_lcs` below, as well as `LieSubmodule.ucs
`.
-/
def lcs : LieSubmodule R L M → LieSubmodule R L M :=
  (fun N => ⁅(⊤ : LieIdeal R L), N⁆)^[k]

@[simp]
/-
**LieSubmodule.lcs_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lcs_zero (N : LieSubmodule R L M) : N.lcs 0 = N
参数：N : LieSubmodule R L M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lcs_zero (N : LieSubmodule R L M) : N.lcs 0 = N :=
  rfl

@[simp]
/-
**LieSubmodule.lcs_succ** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lcs_succ : N.lcs (k + 1) = ⁅(⊤ : LieIdeal R L), N.lcs k⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
-/
theorem lcs_succ : N.lcs (k + 1) = ⁅(⊤ : LieIdeal R L), N.lcs k⁆ :=
  Function.iterate_succ_apply' (fun N' => ⁅⊤, N'⁆) k N

@[simp]
/-
**LieSubmodule.lcs_sup** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmodule`。
形式化陈述：lcs_sup {N₁ N₂ : LieSubmodule R L M} {k : Nat} : (N₁ ⊔ N₂).lcs k = N₁.lcs 
k ⊔ N₂.lcs k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.lcs_succ`：lcs_succ : N.lcs (k + 1) = ⁅(⊤ : LieIdeal R L), N
.lcs k⁆
· 使用定理 `LieSubmodule.lie_sup`：lie_sup : ⁅I, N ⊔ N'⁆ = ⁅I, N⁆ ⊔ ⁅I, N'⁆
-/
lemma lcs_sup {N₁ N₂ : LieSubmodule R L M} {k : ℕ} :
    (N₁ ⊔ N₂).lcs k = N₁.lcs k ⊔ N₂.lcs k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [LieSubmodule.lcs_succ, ih, LieSubmodule.lie_sup]

end LieSubmodule

namespace LieModule

variable (R L M)

/-- The lower central series of Lie submodules of a Lie module. -/
/-
**LieModule.lowerCentralSeries** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：lowerCentralSeries : LieSubmodule R L M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lower central series of Lie submodules of a Lie module.
-/
def lowerCentralSeries : LieSubmodule R L M :=
  (⊤ : LieSubmodule R L M).lcs k

@[simp]
/-
**LieModule.lowerCentralSeries_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：lowerCentralSeries_zero : lowerCentralSeries R L M 0 = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lowerCentralSeries_zero : lowerCentralSeries R L M 0 = ⊤ :=
  rfl

@[simp]
/-
**LieModule.lowerCentralSeries_succ** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：lowerCentralSeries_succ : lowerCentralSeries R L M (k + 1) = ⁅(⊤ : LieIdea
l R L), lowerCentralSeries R L M k⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.lcs_succ`：lcs_succ : N.lcs (k + 1) = ⁅(⊤ : LieIdeal R L), N
.lcs k⁆
-/
theorem lowerCentralSeries_succ :
    lowerCentralSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆ :=
  (⊤ : LieSubmodule R L M).lcs_succ k
/-
**LieModule.coe_lowerCentralSeries_eq_int_aux** 是 Mathlib 中的一个定理，位于命名空间 `LieModu
le`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem coe_lowerCentralSeries_eq_int_aux (R₁ R₂ L M : Type*)
    [CommRing R₁] [CommRing R₂] [AddCommGroup M]
    [LieRing L] [LieAlgebra R₁ L] [LieAlgebra R₂ L] [Module R₁ M] [Module R₂ M] [LieRingModule L M]
    [LieModule R₁ L M] (k : ℕ) :
    let I := lowerCentralSeries R₂ L M k; let S : Set M := {⁅a, b⁆ | (a : L) (b ∈ I)}
    (Submodule.span R₁ S : Set M) ≤ (Submodule.span R₂ S : Set M) := by
  intro I S x hx
  simp only [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.closure_induction with
  | zero => exact Submodule.zero_mem _
  | add y z hy₁ hz₁ hy₂ hz₂ => exact Submodule.add_mem _ hy₂ hz₂
  | smul_mem c y hy =>
      obtain ⟨a, b, hb, rfl⟩ := hy
      rw [← smul_lie]
      exact Submodule.subset_span ⟨c • a, b, hb, rfl⟩
/-
**LieModule.coe_lowerCentralSeries_eq_int** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：coe_lowerCentralSeries_eq_int [LieModule R L M] (k : Nat) : (lowerCentralS
eries R L M k : Set M) = (lowerCentralSeries Int L M k : Set M)
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.coe_toSubmodule`：coe_toSubmodule : ((N : Submodule R M) : S
et M) = N
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span'`：lieIdeal_oper_eq_linear_span
' [LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅x, n⁆ | (x
 in I) (n in N) }
· 使用定理 `instLieModuleInt`：∀ {L : Type v} {M : Type w} [inst : LieRing L] [inst_1
 : AddCommGroup M] [inst_2 : LieRingModule L M], LieModule ℤ L M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `_private.Mathlib.Algebra.Lie.Nilpotent.0.LieModule.coe_lowerCentralSerie
s_eq_int_aux`：∀ (R₁ : Type u_1) (R₂ : Type u_2) (L : Type u_3) (M : Type u_4) [i
nst : CommRing R₁] [inst_1 : CommRing R₂]   [inst_2 : AddCommGroup M] [ins…
-/
theorem coe_lowerCentralSeries_eq_int [LieModule R L M] (k : ℕ) :
    (lowerCentralSeries R L M k : Set M) = (lowerCentralSeries ℤ L M k : Set M) := by
  rw [← LieSubmodule.coe_toSubmodule, ← LieSubmodule.coe_toSubmodule]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [lowerCentralSeries_succ, lowerCentralSeries_succ]
    rw [LieSubmodule.lieIdeal_oper_eq_linear_span', LieSubmodule.lieIdeal_oper_eq_linear_span']
    rw [Set.ext_iff] at ih
    simp only [SetLike.mem_coe, LieSubmodule.mem_toSubmodule] at ih
    simp only [LieSubmodule.mem_top, ih, true_and]
    apply le_antisymm
    · exact coe_lowerCentralSeries_eq_int_aux _ _ L M k
    · simp only [← ih]
      exact coe_lowerCentralSeries_eq_int_aux _ _ L M k

end LieModule

namespace LieSubmodule

open LieModule

/-
**LieSubmodule.lcs_le_self** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lcs_le_self : N.lcs k <= N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.lcs_succ`：lcs_succ : N.lcs (k + 1) = ⁅(⊤ : LieIdeal R L), N
.lcs k⁆
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LieSubmodule.mono_lie_right`：mono_lie_right (h : N <= N') : ⁅I, N⁆ <= ⁅I
, N'⁆
· 使用定理 `LieSubmodule.lie_le_right`：lie_le_right : ⁅I, N⁆ <= N
-/
theorem lcs_le_self : N.lcs k ≤ N := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [lcs_succ]
    exact (LieSubmodule.mono_lie_right ⊤ ih).trans (N.lie_le_right ⊤)

variable [LieModule R L M]
/-
**LieSubmodule.lowerCentralSeries_eq_lcs_comap** 是 Mathlib 中的一个定理，位于命名空间 `LieSub
module`。
形式化陈述：lowerCentralSeries_eq_lcs_comap : lowerCentralSeries R L N k = (N.lcs k).c
omap N.incl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.comap_incl_self`：comap_incl_self : comap N.incl N = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `LieSubmodule.lcs_succ`：lcs_succ : N.lcs (k + 1) = ⁅(⊤ : LieIdeal R L), N
.lcs k⁆
· 使用定理 `LieSubmodule.range_incl`：range_incl : N.incl.range = N
· 使用定理 `LieSubmodule.lcs_le_self`：lcs_le_self : N.lcs k <= N
· 使用定理 `LieSubmodule.comap_bracket_eq`：comap_bracket_eq [LieModule R L M] (hf₁ :
 f.ker = ⊥) (hf₂ : N₂ <= f.range) : comap f ⁅I, N₂⁆ = ⁅I, comap f N₂⁆
· 使用定理 `LieSubmodule.ker_incl`：ker_incl : N.incl.ker = ⊥
-/
theorem lowerCentralSeries_eq_lcs_comap : lowerCentralSeries R L N k = (N.lcs k).comap N.incl := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [lcs_succ, lowerCentralSeries_succ] at ih ⊢
    have : N.lcs k ≤ N.incl.range := by
      rw [N.range_incl]
      apply lcs_le_self
    rw [ih, LieSubmodule.comap_bracket_eq _ N.incl _ N.ker_incl this]
/-
**LieSubmodule.lowerCentralSeries_map_eq_lcs** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmo
dule`。
形式化陈述：lowerCentralSeries_map_eq_lcs : (lowerCentralSeries R L N k).map N.incl = 
N.lcs k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.lowerCentralSeries_eq_lcs_comap`：lowerCentralSeries_eq_lcs_
comap : lowerCentralSeries R L N k = (N.lcs k).comap N.incl
· 使用定理 `LieSubmodule.map_comap_incl`：map_comap_incl : map N.incl (comap N.incl N
') = N ⊓ N'
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `LieSubmodule.lcs_le_self`：lcs_le_self : N.lcs k <= N
-/
theorem lowerCentralSeries_map_eq_lcs : (lowerCentralSeries R L N k).map N.incl = N.lcs k := by
  rw [lowerCentralSeries_eq_lcs_comap, LieSubmodule.map_comap_incl, inf_eq_right]
  apply lcs_le_self
/-
**LieSubmodule.lowerCentralSeries_eq_bot_iff_lcs_eq_bot** 是 Mathlib 中的一个定理，位于命名空
间 `LieSubmodule`。
形式化陈述：lowerCentralSeries_eq_bot_iff_lcs_eq_bot : lowerCentralSeries R L N k = ⊥ 
↔ lcs k N = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.lowerCentralSeries_map_eq_lcs`：lowerCentralSeries_map_eq_lc
s : (lowerCentralSeries R L N k).map N.incl = N.lcs k
· 使用定理 `LieModuleHom.le_ker_iff_map`：le_ker_iff_map (M' : LieSubmodule R L M) : 
M' <= f.ker ↔ LieSubmodule.map f M' = ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LieSubmodule.ker_incl`：ker_incl : N.incl.ker = ⊥
· 使用定理 `LieSubmodule.lowerCentralSeries_eq_lcs_comap`：lowerCentralSeries_eq_lcs_
comap : lowerCentralSeries R L N k = (N.lcs k).comap N.incl
· 使用定理 `LieSubmodule.comap_incl_eq_bot`：comap_incl_eq_bot : N₂.comap N.incl = ⊥ 
↔ N ⊓ N₂ = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lowerCentralSeries_eq_bot_iff_lcs_eq_bot :
    lowerCentralSeries R L N k = ⊥ ↔ lcs k N = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← N.lowerCentralSeries_map_eq_lcs, ← LieModuleHom.le_ker_iff_map]
    simpa
  · rw [N.lowerCentralSeries_eq_lcs_comap, comap_incl_eq_bot]
    simp [h]

end LieSubmodule

namespace LieModule

variable {M₂ : Type w₁} [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]
variable (R L M)

/-
**LieModule.antitone_lowerCentralSeries** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：antitone_lowerCentralSeries : Antitone lowerCentralSeries R L M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `Nat.of_le_succ`：∀ {m n : ℕ}, m ≤ n.succ → m ≤ n ∨ m = n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LieSubmodule.mono_lie_right`：mono_lie_right (h : N <= N') : ⁅I, N⁆ <= ⁅I
, N'⁆
· 使用定理 `LieSubmodule.lie_le_right`：lie_le_right : ⁅I, N⁆ <= N
-/
theorem antitone_lowerCentralSeries : Antitone <| lowerCentralSeries R L M := by
  intro l k
  induction k generalizing l with
  | zero => exact fun h ↦ (Nat.le_zero.mp h).symm ▸ le_rfl
  | succ k ih =>
    intro h
    rcases Nat.of_le_succ h with (hk | hk)
    · rw [lowerCentralSeries_succ]
      exact (LieSubmodule.mono_lie_right ⊤ (ih hk)).trans (LieSubmodule.lie_le_right _ _)
    · exact hk.symm ▸ le_rfl
/-
**LieModule.eventually_iInf_lowerCentralSeries_eq** 是 Mathlib 中的一个定理，位于命名空间 `Lie
Module`。
形式化陈述：eventually_iInf_lowerCentralSeries_eq [IsArtinian R M] : forallᶠ l in Filt
er.atTop, ⨅ k, lowerCentralSeries R L M k = lowerCentralSeries R L M l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.wellFoundedLT_of_isArtinian`：wellFoundedLT_of_isArtinian [I
sArtinian R M] : WellFoundedLT (LieSubmodule R L M)
· 使用定理 `LieModule.antitone_lowerCentralSeries`：antitone_lowerCentralSeries : Ant
itone lowerCentralSeries R L M
· 使用定理 `WellFoundedGT.monotone_chain_condition`：WellFoundedGT.monotone_chain_con
dition [PartialOrder α] [h : WellFoundedGT α] (a : Nat ->o α) : exists n, forall
 m, n <= m -> a n = a m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem eventually_iInf_lowerCentralSeries_eq [IsArtinian R M] :
    ∀ᶠ l in Filter.atTop, ⨅ k, lowerCentralSeries R L M k = lowerCentralSeries R L M l := by
  have h_wf : WellFoundedGT (LieSubmodule R L M)ᵒᵈ :=
    LieSubmodule.wellFoundedLT_of_isArtinian R L M
  obtain ⟨n, hn : ∀ m, n ≤ m → lowerCentralSeries R L M n = lowerCentralSeries R L M m⟩ :=
    h_wf.monotone_chain_condition ⟨_, antitone_lowerCentralSeries R L M⟩
  refine Filter.eventually_atTop.mpr ⟨n, fun l hl ↦ le_antisymm (iInf_le _ _) (le_iInf fun m ↦ ?_)⟩
  rcases le_or_gt l m with h | h
  · rw [← hn _ hl, ← hn _ (hl.trans h)]
  · exact antitone_lowerCentralSeries R L M (le_of_lt h)
/-
**LieModule.trivial_iff_lower_central_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieModul
e`。
形式化陈述：trivial_iff_lower_central_eq_bot : IsTrivial L M ↔ lowerCentralSeries R L 
M 1 = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `LieSubmodule.trivial_lie_oper_zero`：LieSubmodule.trivial_lie_oper_zero [
LieModule.IsTrivial L M] : ⁅I, N⁆ = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LieSubmodule.eq_bot_iff`：∀ {R : Type u} {L : Type v} {M : Type w} [inst 
: CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.
Module R M] […
· 使用定理 `LieSubmodule.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem trivial_iff_lower_central_eq_bot : IsTrivial L M ↔ lowerCentralSeries R L M 1 = ⊥ := by
  constructor <;> intro h
  · simp
  · rw [LieSubmodule.eq_bot_iff] at h; apply IsTrivial.mk; intro x m; apply h
    apply LieSubmodule.subset_lieSpan
    simp only [Subtype.exists, LieSubmodule.mem_top, exists_prop, true_and, Set.mem_ofPred]
    exact ⟨x, m, rfl⟩

section
variable [LieModule R L M]

/-
**LieModule.iterate_toEnd_mem_lowerCentralSeries** 是 Mathlib 中的一个定理，位于命名空间 `LieM
odule`。
形式化陈述：iterate_toEnd_mem_lowerCentralSeries (x : L) (m : M) (k : Nat) : (toEnd R 
L M x)^[k] m in lowerCentralSeries R L M k
参数：x : L；m : M；k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `LieSubmodule.lie_mem_lie`：lie_mem_lie {x : L} {m : M} (hx : x in I) (hm 
: m in N) : ⁅x, m⁆ in ⁅I, N⁆
· 使用定理 `LieSubmodule.mem_top`：mem_top (x : M) : x in (⊤ : LieSubmodule R L M)
-/
theorem iterate_toEnd_mem_lowerCentralSeries (x : L) (m : M) (k : ℕ) :
    (toEnd R L M x)^[k] m ∈ lowerCentralSeries R L M k := by
  induction k with
  | zero => simp only [Function.iterate_zero, lowerCentralSeries_zero, LieSubmodule.mem_top]
  | succ k ih =>
    simp only [lowerCentralSeries_succ, Function.comp_apply, Function.iterate_succ',
      toEnd_apply_apply]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) ih
/-
**LieModule.iterate_toEnd_mem_lowerCentralSeries** 是 Mathlib 中的一个定理，位于命名空间 `LieM
odule`。
形式化陈述：iterate_toEnd_mem_lowerCentralSeries (x : L) (m : M) (k : Nat) : (toEnd R 
L M x)^[k] m in lowerCentralSeries R L M k
参数：x : L；m : M；k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `LieSubmodule.lie_mem_lie`：lie_mem_lie {x : L} {m : M} (hx : x in I) (hm 
: m in N) : ⁅x, m⁆ in ⁅I, N⁆
· 使用定理 `LieSubmodule.mem_top`：mem_top (x : M) : x in (⊤ : LieSubmodule R L M)
-/
theorem iterate_toEnd_mem_lowerCentralSeries₂ (x y : L) (m : M) (k : ℕ) :
    (toEnd R L M x ∘ₗ toEnd R L M y)^[k] m ∈
      lowerCentralSeries R L M (2 * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : 2 * k.succ = (2 * k + 1) + 1 := rfl
    simp only [lowerCentralSeries_succ, Function.comp_apply, Function.iterate_succ', hk,
      toEnd_apply_apply, LinearMap.coe_comp, toEnd_apply_apply]
    refine LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) ?_
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top y) ih

variable {R L M}
/-
**LieModule.map_lowerCentralSeries_le** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：map_lowerCentralSeries_le (f : M ->ₗ⁅R,L⁆ M₂) : (lowerCentralSeries R L M 
k).map f <= lowerCentralSeries R L M₂ k
参数：f : M ->ₗ⁅R,L⁆ M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `LieSubmodule.map_bracket_eq`：map_bracket_eq [LieModule R L M] : map f ⁅I
, N⁆ = ⁅I, map f N⁆
· 使用定理 `LieSubmodule.mono_lie_right`：mono_lie_right (h : N <= N') : ⁅I, N⁆ <= ⁅I
, N'⁆
-/
theorem map_lowerCentralSeries_le (f : M →ₗ⁅R,L⁆ M₂) :
    (lowerCentralSeries R L M k).map f ≤ lowerCentralSeries R L M₂ k := by
  induction k with
  | zero => simp only [lowerCentralSeries_zero, le_top]
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.map_bracket_eq]
    exact LieSubmodule.mono_lie_right ⊤ ih
/-
**LieModule.map_lowerCentralSeries_eq** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：map_lowerCentralSeries_eq {f : M ->ₗ⁅R,L⁆ M₂} (hf : Function.Surjective f)
 : (lowerCentralSeries R L M k).map f = lowerCentralSeries R L M₂ k
参数：hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LieModule.map_lowerCentralSeries_le`：map_lowerCentralSeries_le (f : M ->
ₗ⁅R,L⁆ M₂) : (lowerCentralSeries R L M k).map f <= lowerCentralSeries R L M₂ k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.lowerCentralSeries_zero`：lowerCentralSeries_zero : lowerCentra
lSeries R L M 0 = ⊤
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `LieModuleHom.map_top`：map_top : LieSubmodule.map f ⊤ = f.range
· 使用定理 `LieModuleHom.range_eq_top`：range_eq_top : f.range = ⊤ ↔ Function.Surject
ive f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LieSubmodule.map_bracket_eq`：map_bracket_eq [LieModule R L M] : map f ⁅I
, N⁆ = ⁅I, map f N⁆
· 使用定理 `LieSubmodule.mono_lie_right`：mono_lie_right (h : N <= N') : ⁅I, N⁆ <= ⁅I
, N'⁆
-/
lemma map_lowerCentralSeries_eq {f : M →ₗ⁅R,L⁆ M₂} (hf : Function.Surjective f) :
    (lowerCentralSeries R L M k).map f = lowerCentralSeries R L M₂ k := by
  apply le_antisymm (map_lowerCentralSeries_le k f)
  induction k with
  | zero =>
    rwa [lowerCentralSeries_zero, lowerCentralSeries_zero, top_le_iff, f.map_top,
      f.range_eq_top]
  | succ =>
    simp only [lowerCentralSeries_succ, LieSubmodule.map_bracket_eq]
    apply LieSubmodule.mono_lie_right
    assumption

end

open LieAlgebra

/-
**LieModule.derivedSeries_le_lowerCentralSeries** 是 Mathlib 中的一个定理，位于命名空间 `LieMo
dule`。
形式化陈述：derivedSeries_le_lowerCentralSeries (k : Nat) : derivedSeries R L k <= low
erCentralSeries R L L k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.derivedSeries_def`：derivedSeries_def (k : Nat) : derivedSerie
s R L k = derivedSeriesOfIdeal R L k ⊤
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_zero`：derivedSeriesOfIdeal_zero : derive
dSeriesOfIdeal R L 0 I = I
· 使用定理 `LieModule.lowerCentralSeries_zero`：lowerCentralSeries_zero : lowerCentra
lSeries R L M 0 = ⊤
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_succ`：derivedSeriesOfIdeal_succ (k : Nat
) : derivedSeriesOfIdeal R L (k + 1) I = ⁅derivedSeriesOfIdeal R L k I, derivedS
eriesOfIdeal R L k I⁆
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `LieSubmodule.mono_lie`：mono_lie (h₁ : I <= J) (h₂ : N <= N') : ⁅I, N⁆ <=
 ⁅J, N'⁆
-/
theorem derivedSeries_le_lowerCentralSeries (k : ℕ) :
    derivedSeries R L k ≤ lowerCentralSeries R L L k := by
  induction k with
  | zero => rw [derivedSeries_def, derivedSeriesOfIdeal_zero, lowerCentralSeries_zero]
  | succ k h =>
    have h' : derivedSeries R L k ≤ ⊤ := by simp only [le_top]
    rw [derivedSeries_def, derivedSeriesOfIdeal_succ, lowerCentralSeries_succ]
    exact LieSubmodule.mono_lie h' h

/-- A Lie module is nilpotent if its lower central series reaches 0 (in a finite number of
steps). -/
@[mk_iff isNilpotent_iff_int]
/-
**LieModule.IsNilpotent** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieModule`。
形式化陈述：(L : Type v) → (M : Type w) → [inst : LieRing L] → [inst_1 : AddCommGroup 
M] → [LieRingModule L M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie module is nilpotent if its lower central series reaches 0 (in a finite num
ber of
steps).
-/
class IsNilpotent : Prop where
  mk_int ::
  nilpotent_int : ∃ k, lowerCentralSeries ℤ L M k = ⊥

section

variable [LieModule R L M]

/-- See also `LieModule.isNilpotent_iff_exists_ucs_eq_top`. -/
/-
**LieModule.isNilpotent_iff** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：isNilpotent_iff : IsNilpotent L M ↔ exists k, lowerCentralSeries R L M k =
 ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.coe_lowerCentralSeries_eq_int`：coe_lowerCentralSeries_eq_int [
LieModule R L M] (k : Nat) : (lowerCentralSeries R L M k : Set M) = (lowerCentra
lSeries Int L M k : Set M)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
See also `LieModule.isNilpotent_iff_exists_ucs_eq_top`.
-/
lemma isNilpotent_iff :
    IsNilpotent L M ↔ ∃ k, lowerCentralSeries R L M k = ⊥ := by
  simp [isNilpotent_iff_int, SetLike.ext'_iff, coe_lowerCentralSeries_eq_int R L M]
/-
**LieModule.IsNilpotent.nilpotent** 是 Mathlib 中的一个定理，位于命名空间 `LieModule.IsNilpote
nt`。
形式化陈述：∀ (R : Type u) (L : Type v) (M : Type w) [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _root_.M
odule R M] [inst_5 : LieRingModule L M] [LieModule R L M]   [LieModule.IsNilpote
nt L M], ∃ k, LieModule.lowerCentralSeries R L M k = ⊥
参数：R : Type u；L : Type v；M : Type w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LieModule.isNilpotent_iff`：isNilpotent_iff : IsNilpotent L M ↔ exists k,
 lowerCentralSeries R L M k = ⊥
-/
lemma IsNilpotent.nilpotent [IsNilpotent L M] : ∃ k, lowerCentralSeries R L M k = ⊥ :=
  (isNilpotent_iff R L M).mp ‹_›

variable {R L} in
/-
**LieModule.IsNilpotent.mk** 是 Mathlib 中的一个定理，位于命名空间 `LieModule.IsNilpotent`。
形式化陈述：∀ {R : Type u} {L : Type v} (M : Type w) [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _root_.M
odule R M] [inst_5 : LieRingModule L M] [LieModule R L M] {k : ℕ},   LieModule.l
owerCentralSeries R L M k = ⊥ → LieModule.IsNilpotent L M
参数：M : Type w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LieModule.isNilpotent_iff`：isNilpotent_iff : IsNilpotent L M ↔ exists k,
 lowerCentralSeries R L M k = ⊥
-/
lemma IsNilpotent.mk {k : ℕ} (h : lowerCentralSeries R L M k = ⊥) : IsNilpotent L M :=
  (isNilpotent_iff R L M).mpr ⟨k, h⟩
/-
**LieModule.iInf_lowerCentralSeries_eq_bot_of_isNilpotent** 是 Mathlib 中的一个定理，位于命
名空间 `LieModule`。
形式化陈述：∀ (R : Type u) (L : Type v) (M : Type w) [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _root_.M
odule R M] [inst_5 : LieRingModule L M] [LieModule R L M]   [LieModule.IsNilpote
nt L M], ⨅ k, LieModule.lowerCentralSeries R L M k = ⊥
参数：R : Type u；L : Type v；M : Type w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.IsNilpotent.nilpotent`：∀ (R : Type u) (L : Type v) (M : Type w
) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 :
 AddCommGroup M] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
@[simp] lemma iInf_lowerCentralSeries_eq_bot_of_isNilpotent [IsNilpotent L M] :
    ⨅ k, lowerCentralSeries R L M k = ⊥ := by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M
  rw [eq_bot_iff, ← hk]
  exact iInf_le _ _

end

section
variable {R L M}
variable [LieModule R L M]

/-
**LieModule._root_.LieSubmodule.isNilpotent_iff_exists_lcs_eq_bot** 是 Mathlib 中的
一个定理，位于命名空间 `LieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LieSubmodule.isNilpotent_iff_exists_lcs_eq_bot (N : LieSubmodule R L M) :
    LieModule.IsNilpotent L N ↔ ∃ k, N.lcs k = ⊥ := by
  rw [isNilpotent_iff R L N]
  refine exists_congr fun k => ?_
  rw [N.lowerCentralSeries_eq_lcs_comap k, LieSubmodule.comap_incl_eq_bot,
    inf_eq_right.mpr (N.lcs_le_self k)]

variable (R L M)
/-
**LieModule.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) trivialIsNilpotent [IsTrivial L M] : IsNilpotent L M :=
  ⟨by use 1; simp⟩
/-
**LieModule.instIsNilpotentSup** 是 Mathlib 中的一个实例，位于命名空间 `LieModule`。
形式化陈述：instIsNilpotentSup (M₁ M₂ : LieSubmodule R L M) [IsNilpotent L M₁] [IsNilp
otent L M₂] : IsNilpotent L (M₁ ⊔ M₂ : LieSubmodule R L M)
参数：M₁ M₂ : LieSubmodule R L M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LieModule.IsNilpotent.nilpotent`：∀ (R : Type u) (L : Type v) (M : Type w
) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 :
 AddCommGroup M] [ins…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.antitone_lowerCentralSeries`：antitone_lowerCentralSeries : Ant
itone lowerCentralSeries R L M
· 使用定理 `Nat.le_max_left`：∀ (a b : ℕ), a ≤ max a b
· 使用定理 `Nat.le_max_right`：∀ (a b : ℕ), b ≤ max a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LieModule.isNilpotent_iff`：isNilpotent_iff : IsNilpotent L M ↔ exists k,
 lowerCentralSeries R L M k = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieSubmodule.lowerCentralSeries_eq_lcs_comap`：lowerCentralSeries_eq_lcs_
comap : lowerCentralSeries R L N k = (N.lcs k).comap N.incl
· 使用引理 `LieSubmodule.lcs_sup`：lcs_sup {N₁ N₂ : LieSubmodule R L M} {k : Nat} : (
N₁ ⊔ N₂).lcs k = N₁.lcs k ⊔ N₂.lcs k
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieSubmodule.lowerCentralSeries_eq_bot_iff_lcs_eq_bot`：lowerCentralSerie
s_eq_bot_iff_lcs_eq_bot : lowerCentralSeries R L N k = ⊥ ↔ lcs k N = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instIsNilpotentSup (M₁ M₂ : LieSubmodule R L M) [IsNilpotent L M₁] [IsNilpotent L M₂] :
    IsNilpotent L (M₁ ⊔ M₂ : LieSubmodule R L M) := by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M₁
  obtain ⟨l, hl⟩ := IsNilpotent.nilpotent R L M₂
  let lcs_eq_bot {m n} (N : LieSubmodule R L M) (le : m ≤ n) (hn : lowerCentralSeries R L N m = ⊥) :
    lowerCentralSeries R L N n = ⊥ := by
    simpa [hn] using antitone_lowerCentralSeries R L N le
  have h₁ : lowerCentralSeries R L M₁ (k ⊔ l) = ⊥ := lcs_eq_bot M₁ (Nat.le_max_left k l) hk
  have h₂ : lowerCentralSeries R L M₂ (k ⊔ l) = ⊥ := lcs_eq_bot M₂ (Nat.le_max_right k l) hl
  refine (isNilpotent_iff R L (M₁ + M₂)).mpr ⟨k ⊔ l, ?_⟩
  simp [LieSubmodule.add_eq_sup, (M₁ ⊔ M₂).lowerCentralSeries_eq_lcs_comap, LieSubmodule.lcs_sup,
    (M₁.lowerCentralSeries_eq_bot_iff_lcs_eq_bot (k ⊔ l)).1 h₁,
    (M₂.lowerCentralSeries_eq_bot_iff_lcs_eq_bot (k ⊔ l)).1 h₂, LieSubmodule.comap_incl_eq_bot]
/-
**LieModule.exists_forall_pow_toEnd_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieModule
`。
形式化陈述：exists_forall_pow_toEnd_eq_zero [IsNilpotent L M] : exists k : Nat, forall
 x : L, toEnd R L M x ^ k = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.IsNilpotent.nilpotent`：∀ (R : Type u) (L : Type v) (M : Type w
) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 :
 AddCommGroup M] [ins…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.pow_apply`：pow_apply (f : End R M) (n : Nat) (m : M) : (f ^ n
) m = f^[n] m
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.mem_bot`：mem_bot (x : M) : x in (⊥ : LieSubmodule R L M) ↔ 
x = 0
· 使用定理 `LieModule.iterate_toEnd_mem_lowerCentralSeries`：iterate_toEnd_mem_lowerC
entralSeries (x : L) (m : M) (k : Nat) : (toEnd R L M x)^[k] m in lowerCentralSe
ries R L M k
-/
theorem exists_forall_pow_toEnd_eq_zero [IsNilpotent L M] :
    ∃ k : ℕ, ∀ x : L, toEnd R L M x ^ k = 0 := by
  obtain ⟨k, hM⟩ := IsNilpotent.nilpotent R L M
  use k
  intro x; ext m
  rw [Module.End.pow_apply, LinearMap.zero_apply, ← @LieSubmodule.mem_bot R L M, ← hM]
  exact iterate_toEnd_mem_lowerCentralSeries R L M x m k
/-
**LieModule.isNilpotent_toEnd_of_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 `LieModul
e`。
形式化陈述：isNilpotent_toEnd_of_isNilpotent [IsNilpotent L M] (x : L) : _root_.IsNilp
otent (toEnd R L M x)
参数：x : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.exists_forall_pow_toEnd_eq_zero`：exists_forall_pow_toEnd_eq_ze
ro [IsNilpotent L M] : exists k : Nat, forall x : L, toEnd R L M x ^ k = 0
-/
theorem isNilpotent_toEnd_of_isNilpotent [IsNilpotent L M] (x : L) :
    _root_.IsNilpotent (toEnd R L M x) := by
  change ∃ k, toEnd R L M x ^ k = 0
  have := exists_forall_pow_toEnd_eq_zero R L M
  tauto
/-
**LieModule.isNilpotent_toEnd_of_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 `LieModul
e`。
形式化陈述：isNilpotent_toEnd_of_isNilpotent [IsNilpotent L M] (x : L) : _root_.IsNilp
otent (toEnd R L M x)
参数：x : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.exists_forall_pow_toEnd_eq_zero`：exists_forall_pow_toEnd_eq_ze
ro [IsNilpotent L M] : exists k : Nat, forall x : L, toEnd R L M x ^ k = 0
-/
theorem isNilpotent_toEnd_of_isNilpotent₂ [IsNilpotent L M] (x y : L) :
    _root_.IsNilpotent (toEnd R L M x ∘ₗ toEnd R L M y) := by
  obtain ⟨k, hM⟩ := IsNilpotent.nilpotent R L M
  replace hM : lowerCentralSeries R L M (2 * k) = ⊥ := by
    rw [eq_bot_iff, ← hM]; exact antitone_lowerCentralSeries R L M (by lia)
  use k
  ext m
  rw [Module.End.pow_apply, LinearMap.zero_apply, ← LieSubmodule.mem_bot (R := R) (L := L), ← hM]
  exact iterate_toEnd_mem_lowerCentralSeries₂ R L M x y m k
/-
**LieModule.maxGenEigenSpace_toEnd_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ (R : Type u) (L : Type v) (M : Type w) [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _root_.M
odule R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [LieModule.
IsNilpotent L M] (x : L), ((LieModule.toEnd R L M) x).maxGenEigenspace 0 = ⊤
参数：R : Type u；L : Type v；M : Type w；x : L；(LieModule.toEnd R L M) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `LieModule.exists_forall_pow_toEnd_eq_zero`：exists_forall_pow_toEnd_eq_ze
ro [IsNilpotent L M] : exists k : Nat, forall x : L, toEnd R L M x ^ k = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma maxGenEigenSpace_toEnd_eq_top [IsNilpotent L M] (x : L) :
    ((toEnd R L M x).maxGenEigenspace 0) = ⊤ := by
  ext m
  simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, Submodule.mem_top,
    iff_true]
  obtain ⟨k, hk⟩ := exists_forall_pow_toEnd_eq_zero R L M
  exact ⟨k, by simp [hk x]⟩

/-- If the quotient of a Lie module `M` by a Lie submodule on which the Lie algebra acts trivially
is nilpotent then `M` is nilpotent.

This is essentially the Lie module equivalent of the fact that a central
extension of nilpotent Lie algebras is nilpotent. See `LieAlgebra.nilpotent_of_nilpotent_quotient`
below for the corresponding result for Lie algebras. -/
/-
**LieModule.nilpotentOfNilpotentQuotient** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：nilpotentOfNilpotentQuotient {N : LieSubmodule R L M} (h₁ : N <= maxTrivSu
bmodule R L M) (h₂ : IsNilpotent L (M ⧸ N)) : IsNilpotent L M
参数：h₁ : N <= maxTrivSubmodule R L M；h₂ : IsNilpotent L (M ⧸ N)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.isNilpotent_iff`：isNilpotent_iff : IsNilpotent L M ↔ exists k,
 lowerCentralSeries R L M k = ⊥
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.Quotient.map_mk'_eq_bot_le`：∀ {R : Type u} {L : Type v} {M 
: Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [
inst_3 : _root_.Module R M] […
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `LieModule.map_lowerCentralSeries_le`：map_lowerCentralSeries_le (f : M ->
ₗ⁅R,L⁆ M₂) : (lowerCentralSeries R L M k).map f <= lowerCentralSeries R L M₂ k
· 使用定理 `LieSubmodule.mono_lie_right`：mono_lie_right (h : N <= N') : ⁅I, N⁆ <= ⁅I
, N'⁆
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LieModule.ideal_oper_maxTrivSubmodule_eq_bot`：ideal_oper_maxTrivSubmodul
e_eq_bot (I : LieIdeal R L) : ⁅I, maxTrivSubmodule R L M⁆ = ⊥

--- 原说明 ---
If the quotient of a Lie module `M` by a Lie submodule on which the Lie algebra 
acts trivially
is nilpotent then `M` is nilpotent.

This is essentially the Lie module equivalent of the fact that a central
extension of nilpotent Lie algebras is nilpotent. See `LieAlgebra.nilpotent_of_n
ilpotent_quotient`
below for the corresponding result for Lie algebras.
-/
theorem nilpotentOfNilpotentQuotient {N : LieSubmodule R L M} (h₁ : N ≤ maxTrivSubmodule R L M)
    (h₂ : IsNilpotent L (M ⧸ N)) : IsNilpotent L M := by
  rw [isNilpotent_iff R L] at h₂ ⊢
  obtain ⟨k, hk⟩ := h₂
  use k + 1
  simp only [lowerCentralSeries_succ]
  suffices lowerCentralSeries R L M k ≤ N by
    replace this := LieSubmodule.mono_lie_right ⊤ (le_trans this h₁)
    rwa [ideal_oper_maxTrivSubmodule_eq_bot, le_bot_iff] at this
  rw [← LieSubmodule.Quotient.map_mk'_eq_bot_le, ← le_bot_iff, ← hk]
  exact map_lowerCentralSeries_le k (LieSubmodule.Quotient.mk' N)
/-
**LieModule.isNilpotent_quotient_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：isNilpotent_quotient_iff : IsNilpotent L (M ⧸ N) ↔ exists k, lowerCentralS
eries R L M k <= N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.isNilpotent_iff`：isNilpotent_iff : IsNilpotent L M ↔ exists k,
 lowerCentralSeries R L M k = ⊥
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.Quotient.map_mk'_eq_bot_le`：∀ {R : Type u} {L : Type v} {M 
: Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [
inst_3 : _root_.Module R M] […
· 使用引理 `LieModule.map_lowerCentralSeries_eq`：map_lowerCentralSeries_eq {f : M ->
ₗ⁅R,L⁆ M₂} (hf : Function.Surjective f) : (lowerCentralSeries R L M k).map f = l
owerCentralSeries R L M₂ …
· 使用定理 `LieSubmodule.Quotient.surjective_mk'`：surjective_mk' : Function.Surjecti
ve (mk' N)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isNilpotent_quotient_iff :
    IsNilpotent L (M ⧸ N) ↔ ∃ k, lowerCentralSeries R L M k ≤ N := by
  rw [isNilpotent_iff R L]
  refine exists_congr fun k ↦ ?_
  rw [← LieSubmodule.Quotient.map_mk'_eq_bot_le, map_lowerCentralSeries_eq k
    (LieSubmodule.Quotient.surjective_mk' N)]
/-
**LieModule.iInf_lcs_le_of_isNilpotent_quot** 是 Mathlib 中的一个定理，位于命名空间 `LieModule
`。
形式化陈述：iInf_lcs_le_of_isNilpotent_quot (h : IsNilpotent L (M ⧸ N)) : ⨅ k, lowerCe
ntralSeries R L M k <= N
参数：h : IsNilpotent L (M ⧸ N)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieModule.isNilpotent_quotient_iff`：isNilpotent_quotient_iff : IsNilpote
nt L (M ⧸ N) ↔ exists k, lowerCentralSeries R L M k <= N
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
-/
theorem iInf_lcs_le_of_isNilpotent_quot (h : IsNilpotent L (M ⧸ N)) :
    ⨅ k, lowerCentralSeries R L M k ≤ N := by
  obtain ⟨k, hk⟩ := (isNilpotent_quotient_iff R L M N).mp h
  exact iInf_le_of_le k hk

end

/-- Given a nilpotent Lie module `M` with lower central series `M = C₀ ≥ C₁ ≥ ⋯ ≥ Cₖ = ⊥`, this is
the natural number `k` (the number of inclusions).

For a non-nilpotent module, we use the junk value 0. -/
/-
**LieModule.nilpotencyLength** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：nilpotencyLength : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a nilpotent Lie module `M` with lower central series `M = C₀ ≥ C₁ ≥ ⋯ ≥ Cₖ
 = ⊥`, this is
the natural number `k` (the number of inclusions).

For a non-nilpotent module, we use the junk value 0.
-/
noncomputable def nilpotencyLength : ℕ :=
  sInf {k | lowerCentralSeries ℤ L M k = ⊥}

@[simp]
/-
**LieModule.nilpotencyLength_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：nilpotencyLength_eq_zero_iff [IsNilpotent L M] : nilpotencyLength L M = 0 
↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.IsNilpotent.nilpotent`：∀ (R : Type u) (L : Type v) (M : Type w
) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 :
 AddCommGroup M] [ins…
· 使用定理 `instLieModuleInt`：∀ {L : Type v} {M : Type w} [inst : LieRing L] [inst_1
 : AddCommGroup M] [inst_2 : LieRingModule L M], LieModule ℤ L M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.subsingleton_iff`：subsingleton_iff : Subsingleton (LieSubmo
dule R L M) ↔ Subsingleton M
· 使用定理 `subsingleton_iff_bot_eq_top`：subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ 
: α) ↔ Subsingleton α
· 使用定理 `LieModule.lowerCentralSeries_zero`：lowerCentralSeries_zero : lowerCentra
lSeries R L M 0 = ⊤
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.sInf_mem`：sInf_mem {s : Set Nat} (h : s.Nonempty) : sInf s in s
· 使用定理 `Nat.sInf_eq_zero`：sInf_eq_zero {s : Set Nat} : sInf s = 0 ↔ 0 in s ∨ s =
 ∅
-/
theorem nilpotencyLength_eq_zero_iff [IsNilpotent L M] :
    nilpotencyLength L M = 0 ↔ Subsingleton M := by
  let s := {k | lowerCentralSeries ℤ L M k = ⊥}
  have hs : s.Nonempty := by
    obtain ⟨k, hk⟩ := IsNilpotent.nilpotent ℤ L M
    exact ⟨k, hk⟩
  change sInf s = 0 ↔ _
  rw [← LieSubmodule.subsingleton_iff ℤ L M, ← subsingleton_iff_bot_eq_top, ←
    lowerCentralSeries_zero, @eq_comm (LieSubmodule ℤ L M)]
  refine ⟨fun h => h ▸ Nat.sInf_mem hs, fun h => ?_⟩
  rw [Nat.sInf_eq_zero]
  exact Or.inl h

section

variable [LieModule R L M]

/-
**LieModule.nilpotencyLength_eq_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：nilpotencyLength_eq_succ_iff (k : Nat) : nilpotencyLength L M = k + 1 ↔ lo
werCentralSeries R L M (k + 1) = ⊥ ∧ lowerCentralSeries R L M k != ⊥
参数：k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.coe_lowerCentralSeries_eq_int`：coe_lowerCentralSeries_eq_int [
LieModule R L M] (k : Nat) : (lowerCentralSeries R L M k : Set M) = (lowerCentra
lSeries Int L M k : Set M)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `LieModule.antitone_lowerCentralSeries`：antitone_lowerCentralSeries : Ant
itone lowerCentralSeries R L M
· 使用定理 `Nat.sInf_upward_closed_eq_succ_iff`：sInf_upward_closed_eq_succ_iff {s : 
Set Nat} (hs : forall k₁ k₂ : Nat, k₁ <= k₂ -> k₁ in s -> k₂ in s) (k : Nat) : s
Inf s = k + 1 ↔ k + 1 in…
-/
theorem nilpotencyLength_eq_succ_iff (k : ℕ) :
    nilpotencyLength L M = k + 1 ↔
      lowerCentralSeries R L M (k + 1) = ⊥ ∧ lowerCentralSeries R L M k ≠ ⊥ := by
  have aux (k : ℕ) : lowerCentralSeries R L M k = ⊥ ↔ lowerCentralSeries ℤ L M k = ⊥ := by
    simp [SetLike.ext'_iff, coe_lowerCentralSeries_eq_int R L M]
  let s := {k | lowerCentralSeries ℤ L M k = ⊥}
  rw [aux, ne_eq, aux]
  change sInf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s
  have hs : ∀ k₁ k₂, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s := by
    rintro k₁ k₂ h₁₂ (h₁ : lowerCentralSeries ℤ L M k₁ = ⊥)
    exact eq_bot_iff.mpr (h₁ ▸ antitone_lowerCentralSeries ℤ L M h₁₂)
  exact Nat.sInf_upward_closed_eq_succ_iff hs k

@[simp]
/-
**LieModule.nilpotencyLength_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：nilpotencyLength_eq_one_iff [Nontrivial M] : nilpotencyLength L M = 1 ↔ Is
Trivial L M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.nilpotencyLength_eq_succ_iff`：nilpotencyLength_eq_succ_iff (k 
: Nat) : nilpotencyLength L M = k + 1 ↔ lowerCentralSeries R L M (k + 1) = ⊥ ∧ l
owerCentralSeries R L M k !=…
· 使用定理 `instLieModuleInt`：∀ {L : Type v} {M : Type w} [inst : LieRing L] [inst_1
 : AddCommGroup M] [inst_2 : LieRingModule L M], LieModule ℤ L M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieModule.trivial_iff_lower_central_eq_bot`：trivial_iff_lower_central_eq
_bot : IsTrivial L M ↔ lowerCentralSeries R L M 1 = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieSubmodule.instNontrivial`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _ro
ot_.Module R M] […
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nilpotencyLength_eq_one_iff [Nontrivial M] :
    nilpotencyLength L M = 1 ↔ IsTrivial L M := by
  rw [nilpotencyLength_eq_succ_iff ℤ, ← trivial_iff_lower_central_eq_bot]
  simp
/-
**LieModule.isTrivial_of_nilpotencyLength_le_one** 是 Mathlib 中的一个定理，位于命名空间 `LieM
odule`。
形式化陈述：isTrivial_of_nilpotencyLength_le_one [IsNilpotent L M] (h : nilpotencyLeng
th L M <= 1) : IsTrivial L M
参数：h : nilpotencyLength L M <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_one_iff_eq_zero_or_eq_one`：∀ {n : ℕ}, n ≤ 1 ↔ n = 0 ∨ n = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.nilpotencyLength_eq_zero_iff`：nilpotencyLength_eq_zero_iff [Is
Nilpotent L M] : nilpotencyLength L M = 0 ↔ Subsingleton M
· 使用定理 `LieModule.nilpotencyLength_eq_one_iff`：nilpotencyLength_eq_one_iff [Nont
rivial M] : nilpotencyLength L M = 1 ↔ IsTrivial L M
-/
theorem isTrivial_of_nilpotencyLength_le_one [IsNilpotent L M] (h : nilpotencyLength L M ≤ 1) :
    IsTrivial L M := by
  nontriviality M
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h | h
  · rw [nilpotencyLength_eq_zero_iff] at h; infer_instance
  · rwa [nilpotencyLength_eq_one_iff] at h

end

/-- Given a non-trivial nilpotent Lie module `M` with lower central series
`M = C₀ ≥ C₁ ≥ ⋯ ≥ Cₖ = ⊥`, this is the `k-1`th term in the lower central series (the last
non-trivial term).

For a trivial or non-nilpotent module, this is the bottom submodule, `⊥`. -/
/-
**LieModule.lowerCentralSeriesLast** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：lowerCentralSeriesLast : LieSubmodule R L M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a non-trivial nilpotent Lie module `M` with lower central series
`M = C₀ ≥ C₁ ≥ ⋯ ≥ Cₖ = ⊥`, this is the `k-1`th term in the lower central series
 (the last
non-trivial term).

For a trivial or non-nilpotent module, this is the bottom submodule, `⊥`.
-/
noncomputable def lowerCentralSeriesLast : LieSubmodule R L M :=
  match nilpotencyLength L M with
  | 0 => ⊥
  | k + 1 => lowerCentralSeries R L M k
/-
**LieModule.lowerCentralSeriesLast_le_max_triv** 是 Mathlib 中的一个定理，位于命名空间 `LieMod
ule`。
形式化陈述：lowerCentralSeriesLast_le_max_triv [LieModule R L M] : lowerCentralSeriesL
ast R L M <= maxTrivSubmodule R L M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.lowerCentralSeriesLast.eq_1`：∀ (R : Type u) (L : Type v) (M : 
Type w) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [in
st_3 : AddCommGroup M] [ins…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `LieModule.le_max_triv_iff_bracket_eq_bot`：le_max_triv_iff_bracket_eq_bot
 {N : LieSubmodule R L M} : N <= maxTrivSubmodule R L M ↔ ⁅(⊤ : LieIdeal R L), N
⁆ = ⊥
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `LieModule.nilpotencyLength_eq_succ_iff`：nilpotencyLength_eq_succ_iff (k 
: Nat) : nilpotencyLength L M = k + 1 ↔ lowerCentralSeries R L M (k + 1) = ⊥ ∧ l
owerCentralSeries R L M k !=…
-/
theorem lowerCentralSeriesLast_le_max_triv [LieModule R L M] :
    lowerCentralSeriesLast R L M ≤ maxTrivSubmodule R L M := by
  rw [lowerCentralSeriesLast]
  rcases h : nilpotencyLength L M with - | k
  · exact bot_le
  · rw [le_max_triv_iff_bracket_eq_bot]
    rw [nilpotencyLength_eq_succ_iff R, lowerCentralSeries_succ] at h
    exact h.1
/-
**LieModule.nontrivial_lowerCentralSeriesLast** 是 Mathlib 中的一个定理，位于命名空间 `LieModu
le`。
形式化陈述：nontrivial_lowerCentralSeriesLast [LieModule R L M] [Nontrivial M] [IsNilp
otent L M] : Nontrivial (lowerCentralSeriesLast R L M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.nontrivial_iff_ne_bot`：nontrivial_iff_ne_bot {N : LieSubmod
ule R L M} : Nontrivial N ↔ N != ⊥
· 使用定理 `LieModule.lowerCentralSeriesLast.eq_1`：∀ (R : Type u) (L : Type v) (M : 
Type w) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [in
st_3 : AddCommGroup M] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
· 使用定理 `LieModule.nilpotencyLength_eq_zero_iff`：nilpotencyLength_eq_zero_iff [Is
Nilpotent L M] : nilpotencyLength L M = 0 ↔ Subsingleton M
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LieModule.nilpotencyLength_eq_succ_iff`：nilpotencyLength_eq_succ_iff (k 
: Nat) : nilpotencyLength L M = k + 1 ↔ lowerCentralSeries R L M (k + 1) = ⊥ ∧ l
owerCentralSeries R L M k !=…
-/
theorem nontrivial_lowerCentralSeriesLast [LieModule R L M] [Nontrivial M] [IsNilpotent L M] :
    Nontrivial (lowerCentralSeriesLast R L M) := by
  rw [LieSubmodule.nontrivial_iff_ne_bot, lowerCentralSeriesLast]
  cases h : nilpotencyLength L M
  · rw [nilpotencyLength_eq_zero_iff, ← not_nontrivial_iff_subsingleton] at h
    contradiction
  · rw [nilpotencyLength_eq_succ_iff R] at h
    exact h.2
/-
**LieModule.lowerCentralSeriesLast_le_of_not_isTrivial** 是 Mathlib 中的一个定理，位于命名空间
 `LieModule`。
形式化陈述：lowerCentralSeriesLast_le_of_not_isTrivial [IsNilpotent L M] (h : ¬ IsTriv
ial L M) : lowerCentralSeriesLast R L M <= lowerCentralSeries R L M 1
参数：h : ¬ IsTrivial L M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.lowerCentralSeriesLast.eq_1`：∀ (R : Type u) (L : Type v) (M : 
Type w) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [in
st_3 : AddCommGroup M] [ins…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LieModule.isTrivial_of_nilpotencyLength_le_one`：isTrivial_of_nilpotencyL
ength_le_one [IsNilpotent L M] (h : nilpotencyLength L M <= 1) : IsTrivial L M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `LieModule.antitone_lowerCentralSeries`：antitone_lowerCentralSeries : Ant
itone lowerCentralSeries R L M
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
-/
theorem lowerCentralSeriesLast_le_of_not_isTrivial [IsNilpotent L M] (h : ¬ IsTrivial L M) :
    lowerCentralSeriesLast R L M ≤ lowerCentralSeries R L M 1 := by
  rw [lowerCentralSeriesLast]
  replace h : 1 < nilpotencyLength L M := by
    by_contra contra
    have := isTrivial_of_nilpotencyLength_le_one L M (not_lt.mp contra)
    contradiction
  rcases hk : nilpotencyLength L M with - | k <;> rw [hk] at h
  · contradiction
  · exact antitone_lowerCentralSeries _ _ _ (Nat.le_of_lt_succ h)

variable [LieModule R L M]
attribute [local instance 100] LieRing.ofAssociativeRing

/-- For a nilpotent Lie module `M` of a Lie algebra `L`, the first term in the lower central series
of `M` contains a non-zero element on which `L` acts trivially unless the entire action is trivial.

Taking `M = L`, this provides a useful characterisation of Abelian-ness for nilpotent Lie
algebras. -/
/-
**LieModule.disjoint_lowerCentralSeries_maxTrivSubmodule_iff** 是 Mathlib 中的一个引理，
位于命名空间 `LieModule`。
形式化陈述：disjoint_lowerCentralSeries_maxTrivSubmodule_iff [IsNilpotent L M] : Disjo
int (lowerCentralSeries R L M 1) (maxTrivSubmodule R L M) ↔ IsTrivial L M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `LieModule.lowerCentralSeriesLast_le_of_not_isTrivial`：lowerCentralSeries
Last_le_of_not_isTrivial [IsNilpotent L M] (h : ¬ IsTrivial L M) : lowerCentralS
eriesLast R L M <= lowerCentralSeries R L …
· 使用定理 `LieModule.lowerCentralSeriesLast_le_max_triv`：lowerCentralSeriesLast_le_
max_triv [LieModule R L M] : lowerCentralSeriesLast R L M <= maxTrivSubmodule R 
L M
· 使用定理 `not_nontrivial`：not_nontrivial (α) [Subsingleton α] : ¬Nontrivial α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `LieModule.nontrivial_lowerCentralSeriesLast`：nontrivial_lowerCentralSeri
esLast [LieModule R L M] [Nontrivial M] [IsNilpotent L M] : Nontrivial (lowerCen
tralSeriesLast R L M)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `LieSubmodule.trivial_lie_oper_zero`：LieSubmodule.trivial_lie_oper_zero [
LieModule.IsTrivial L M] : ⁅I, N⁆ = ⊥

--- 原说明 ---
For a nilpotent Lie module `M` of a Lie algebra `L`, the first term in the lower
 central series
of `M` contains a non-zero element on which `L` acts trivially unless the entire
 action is trivial.

Taking `M = L`, this provides a useful characterisation of Abelian-ness for nilp
otent Lie
algebras.
-/
lemma disjoint_lowerCentralSeries_maxTrivSubmodule_iff [IsNilpotent L M] :
    Disjoint (lowerCentralSeries R L M 1) (maxTrivSubmodule R L M) ↔ IsTrivial L M := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp⟩
  nontriviality M
  by_contra contra
  have : lowerCentralSeriesLast R L M ≤ lowerCentralSeries R L M 1 ⊓ maxTrivSubmodule R L M :=
    le_inf_iff.mpr ⟨lowerCentralSeriesLast_le_of_not_isTrivial R L M contra,
      lowerCentralSeriesLast_le_max_triv R L M⟩
  suffices ¬ Nontrivial (lowerCentralSeriesLast R L M) by
    exact this (nontrivial_lowerCentralSeriesLast R L M)
  rw [h.eq_bot, le_bot_iff] at this
  exact this ▸ not_nontrivial _
/-
**LieModule.nontrivial_max_triv_of_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 `LieMod
ule`。
形式化陈述：nontrivial_max_triv_of_isNilpotent [Nontrivial M] [IsNilpotent L M] : Nont
rivial (maxTrivSubmodule R L M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nontrivial_mono`：nontrivial_mono {α : Type*} {s t : Set α} (hst : s 
subseteq t) (hs : Nontrivial s) : Nontrivial t
· 使用定理 `LieModule.lowerCentralSeriesLast_le_max_triv`：lowerCentralSeriesLast_le_
max_triv [LieModule R L M] : lowerCentralSeriesLast R L M <= maxTrivSubmodule R 
L M
· 使用定理 `LieModule.nontrivial_lowerCentralSeriesLast`：nontrivial_lowerCentralSeri
esLast [LieModule R L M] [Nontrivial M] [IsNilpotent L M] : Nontrivial (lowerCen
tralSeriesLast R L M)
-/
theorem nontrivial_max_triv_of_isNilpotent [Nontrivial M] [IsNilpotent L M] :
    Nontrivial (maxTrivSubmodule R L M) :=
  Set.nontrivial_mono (lowerCentralSeriesLast_le_max_triv R L M)
    (nontrivial_lowerCentralSeriesLast R L M)

@[simp]
/-
**LieModule.coe_lcs_range_toEnd_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：coe_lcs_range_toEnd_eq (k : Nat) : (lowerCentralSeries R (toEnd R L M).ran
ge M k : Submodule R M) = lowerCentralSeries R L M k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span'`：lieIdeal_oper_eq_linear_span
' [LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅x, n⁆ | (x
 in I) (n in N) }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.mem_toSubmodule`：mem_toSubmodule {x : M} : x in (N : Submod
ule R M) ↔ x in N
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
-/
theorem coe_lcs_range_toEnd_eq (k : ℕ) :
    (lowerCentralSeries R (toEnd R L M).range M k : Submodule R M) =
      lowerCentralSeries R L M k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', ←
      (lowerCentralSeries R (toEnd R L M).range M k).mem_toSubmodule, ih]
    simp

@[simp]
/-
**LieModule.isNilpotent_range_toEnd_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：isNilpotent_range_toEnd_iff : IsNilpotent (toEnd R L M).range M ↔ IsNilpot
ent L M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.isNilpotent_iff`：isNilpotent_iff : IsNilpotent L M ↔ exists k,
 lowerCentralSeries R L M k = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.coe_lcs_range_toEnd_eq`：coe_lcs_range_toEnd_eq (k : Nat) : (lo
werCentralSeries R (toEnd R L M).range M k : Submodule R M) = lowerCentralSeries
 R L M k
-/
theorem isNilpotent_range_toEnd_iff :
    IsNilpotent (toEnd R L M).range M ↔ IsNilpotent L M := by
  simp only [isNilpotent_iff R _ M]
  constructor <;> rintro ⟨k, hk⟩ <;> use k <;>
      rw [← LieSubmodule.toSubmodule_inj] at hk ⊢ <;>
    simpa using hk

end LieModule

namespace LieSubmodule

variable {N₁ N₂ : LieSubmodule R L M}
variable [LieModule R L M]

/-- The upper (aka ascending) central series.

See also `LieSubmodule.lcs`. -/
/-
**LieSubmodule.ucs** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule`。
形式化陈述：ucs (k : Nat) : LieSubmodule R L M -> LieSubmodule R L M
参数：k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The upper (aka ascending) central series.

See also `LieSubmodule.lcs`.
-/
def ucs (k : ℕ) : LieSubmodule R L M → LieSubmodule R L M :=
  normalizer^[k]

@[simp]
/-
**LieSubmodule.ucs_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：ucs_zero : N.ucs 0 = N
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ucs_zero : N.ucs 0 = N :=
  rfl

@[simp]
/-
**LieSubmodule.ucs_succ** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：ucs_succ (k : Nat) : N.ucs (k + 1) = (N.ucs k).normalizer
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
-/
theorem ucs_succ (k : ℕ) : N.ucs (k + 1) = (N.ucs k).normalizer :=
  Function.iterate_succ_apply' normalizer k N
/-
**LieSubmodule.ucs_add** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：ucs_add (k l : Nat) : N.ucs (k + l) = (N.ucs l).ucs k
参数：k l : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
-/
theorem ucs_add (k l : ℕ) : N.ucs (k + l) = (N.ucs l).ucs k :=
  Function.iterate_add_apply normalizer k l N

@[gcongr, mono]
/-
**LieSubmodule.ucs_mono** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：ucs_mono (k : Nat) (h : N₁ <= N₂) : N₁.ucs k <= N₂.ucs k
参数：k : Nat；h : N₁ <= N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.ucs_succ`：ucs_succ (k : Nat) : N.ucs (k + 1) = (N.ucs k).no
rmalizer
· 使用定理 `LieSubmodule.normalizer_mono`：normalizer_mono (h : N₁ <= N₂) : normalize
r N₁ <= normalizer N₂
-/
theorem ucs_mono (k : ℕ) (h : N₁ ≤ N₂) : N₁.ucs k ≤ N₂.ucs k := by
  induction k with
  | zero => simpa
  | succ k ih =>
    simp only [ucs_succ]
    gcongr
/-
**LieSubmodule.ucs_eq_self_of_normalizer_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `LieS
ubmodule`。
形式化陈述：ucs_eq_self_of_normalizer_eq_self (h : N₁.normalizer = N₁) (k : Nat) : N₁.
ucs k = N₁
参数：h : N₁.normalizer = N₁；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.ucs_succ`：ucs_succ (k : Nat) : N.ucs (k + 1) = (N.ucs k).no
rmalizer
-/
theorem ucs_eq_self_of_normalizer_eq_self (h : N₁.normalizer = N₁) (k : ℕ) : N₁.ucs k = N₁ := by
  induction k with
  | zero => simp
  | succ k ih => rwa [ucs_succ, ih]

/-- If a Lie module `M` contains a self-normalizing Lie submodule `N`, then all terms of the upper
central series of `M` are contained in `N`.

An important instance of this situation arises from a Cartan subalgebra `H ⊆ L` with the roles of
`L`, `M`, `N` played by `H`, `L`, `H`, respectively. -/
/-
**LieSubmodule.ucs_le_of_normalizer_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmod
ule`。
形式化陈述：ucs_le_of_normalizer_eq_self (h : N₁.normalizer = N₁) (k : Nat) : (⊥ : Lie
Submodule R L M).ucs k <= N₁
参数：h : N₁.normalizer = N₁；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.ucs_eq_self_of_normalizer_eq_self`：ucs_eq_self_of_normalize
r_eq_self (h : N₁.normalizer = N₁) (k : Nat) : N₁.ucs k = N₁
· 使用定理 `LieSubmodule.ucs_mono`：ucs_mono (k : Nat) (h : N₁ <= N₂) : N₁.ucs k <= N
₂.ucs k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
If a Lie module `M` contains a self-normalizing Lie submodule `N`, then all term
s of the upper
central series of `M` are contained in `N`.

An important instance of this situation arises from a Cartan subalgebra `H ⊆ L` 
with the roles of
`L`, `M`, `N` played by `H`, `L`, `H`, respectively.
-/
theorem ucs_le_of_normalizer_eq_self (h : N₁.normalizer = N₁) (k : ℕ) :
    (⊥ : LieSubmodule R L M).ucs k ≤ N₁ := by
  rw [← ucs_eq_self_of_normalizer_eq_self h k]
  gcongr
  simp
/-
**LieSubmodule.lcs_add_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lcs_add_le_iff (l k : Nat) : N₁.lcs (l + k) <= N₂ ↔ N₁.lcs l <= N₂.ucs k
参数：l k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `_private.Mathlib.Algebra.Lie.Nilpotent.0.LieSubmodule.lcs_add_le_iff._ab
el_1_2`：∀ (k l : ℕ), l + (k + 1) = l + 1 + k
· 使用定理 `LieSubmodule.ucs_succ`：ucs_succ (k : Nat) : N.ucs (k + 1) = (N.ucs k).no
rmalizer
· 使用定理 `LieSubmodule.lcs_succ`：lcs_succ : N.lcs (k + 1) = ⁅(⊤ : LieIdeal R L), N
.lcs k⁆
· 使用定理 `LieSubmodule.top_lie_le_iff_le_normalizer`：top_lie_le_iff_le_normalizer 
(N' : LieSubmodule R L M) : ⁅(⊤ : LieIdeal R L), N⁆ <= N' ↔ N <= N'.normalizer
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lcs_add_le_iff (l k : ℕ) : N₁.lcs (l + k) ≤ N₂ ↔ N₁.lcs l ≤ N₂.ucs k := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    rw [(by abel : l + (k + 1) = l + 1 + k), ih, ucs_succ, lcs_succ, top_lie_le_iff_le_normalizer]
/-
**LieSubmodule.lcs_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lcs_le_iff (k : Nat) : N₁.lcs k <= N₂ ↔ N₁ <= N₂.ucs k
参数：k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LieSubmodule.lcs_add_le_iff`：lcs_add_le_iff (l k : Nat) : N₁.lcs (l + k)
 <= N₂ ↔ N₁.lcs l <= N₂.ucs k
-/
theorem lcs_le_iff (k : ℕ) : N₁.lcs k ≤ N₂ ↔ N₁ ≤ N₂.ucs k := by
  convert! lcs_add_le_iff (R := R) (L := L) (M := M) 0 k
  rw [zero_add]
/-
**LieSubmodule.gc_lcs_ucs** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：gc_lcs_ucs (k : Nat) : GaloisConnection (fun N : LieSubmodule R L M => N.l
cs k) fun N : LieSubmodule R L M => N.ucs k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.lcs_le_iff`：lcs_le_iff (k : Nat) : N₁.lcs k <= N₂ ↔ N₁ <= N
₂.ucs k
-/
theorem gc_lcs_ucs (k : ℕ) :
    GaloisConnection (fun N : LieSubmodule R L M => N.lcs k) fun N : LieSubmodule R L M =>
      N.ucs k :=
  fun _ _ => lcs_le_iff k
/-
**LieSubmodule.ucs_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：ucs_eq_top_iff (k : Nat) : N.ucs k = ⊤ ↔ LieModule.lowerCentralSeries R L 
M k <= N
参数：k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.lcs_le_iff`：lcs_le_iff (k : Nat) : N₁.lcs k <= N₂ ↔ N₁ <= N
₂.ucs k
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ucs_eq_top_iff (k : ℕ) : N.ucs k = ⊤ ↔ LieModule.lowerCentralSeries R L M k ≤ N := by
  rw [eq_top_iff, ← lcs_le_iff]; rfl

variable (R) in
/-
**LieSubmodule._root_.LieModule.isNilpotent_iff_exists_ucs_eq_top** 是 Mathlib 中的
一个定理，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LieModule.isNilpotent_iff_exists_ucs_eq_top :
    LieModule.IsNilpotent L M ↔ ∃ k, (⊥ : LieSubmodule R L M).ucs k = ⊤ := by
  rw [LieModule.isNilpotent_iff R]; exact exists_congr fun k => by simp [ucs_eq_top_iff]
/-
**LieSubmodule.ucs_comap_incl** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：ucs_comap_incl (k : Nat) : ((⊥ : LieSubmodule R L M).ucs k).comap N.incl =
 (⊥ : LieSubmodule R L N).ucs k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LieSubmodule.ker_incl`：ker_incl : N.incl.ker = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.ucs_succ`：ucs_succ (k : Nat) : N.ucs (k + 1) = (N.ucs k).no
rmalizer
· 使用定理 `LieSubmodule.comap_normalizer`：comap_normalizer (f : M' ->ₗ⁅R,L⁆ M) : N.
normalizer.comap f = (N.comap f).normalizer
· 使用定理 `LieSubmodule.normalizer.congr_simp`：∀ {R : Type u_1} {L : Type u_2} {M :
 Type u_3} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   
[inst_3 : AddCommGroup M…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ucs_comap_incl (k : ℕ) :
    ((⊥ : LieSubmodule R L M).ucs k).comap N.incl = (⊥ : LieSubmodule R L N).ucs k := by
  induction k with
  | zero => exact N.ker_incl
  | succ k ih => simp [← ih]
/-
**LieSubmodule.isNilpotent_iff_exists_self_le_ucs** 是 Mathlib 中的一个定理，位于命名空间 `Lie
Submodule`。
形式化陈述：isNilpotent_iff_exists_self_le_ucs : LieModule.IsNilpotent L N ↔ exists k,
 N <= (⊥ : LieSubmodule R L M).ucs k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.isNilpotent_iff_exists_ucs_eq_top`：∀ (R : Type u) {L : Type v}
 {M : Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]
   [inst_3 : AddCommGroup M] [ins…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isNilpotent_iff_exists_self_le_ucs :
    LieModule.IsNilpotent L N ↔ ∃ k, N ≤ (⊥ : LieSubmodule R L M).ucs k := by
  simp_rw [LieModule.isNilpotent_iff_exists_ucs_eq_top R, ← ucs_comap_incl, comap_incl_eq_top]
/-
**LieSubmodule.ucs_bot_one** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：ucs_bot_one : (⊥ : LieSubmodule R L M).ucs 1 = LieModule.maxTrivSubmodule 
R L M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.ucs_succ`：ucs_succ (k : Nat) : N.ucs (k + 1) = (N.ucs k).no
rmalizer
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ucs_bot_one : (⊥ : LieSubmodule R L M).ucs 1 = LieModule.maxTrivSubmodule R L M := by
  simp [LieSubmodule.normalizer_bot_eq_maxTrivSubmodule]

end LieSubmodule

section Morphisms

open LieModule Function

variable [LieModule R L M]
variable {L₂ M₂ : Type*} [LieRing L₂] [LieAlgebra R L₂]
variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L₂ M₂]
variable {f : L →ₗ⁅R⁆ L₂} {g : M →ₗ[R] M₂}
variable (hfg : ∀ x m, ⁅f x, g m⁆ = g ⁅x, m⁆)

include hfg in
/-
**lieModule_lcs_map_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lieModule_lcs_map_le (k : Nat) : (lowerCentralSeries R L M k : Submodule R
 M).map g <= lowerCentralSeries R L₂ M₂ k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span'`：lieIdeal_oper_eq_linear_span
' [LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅x, n⁆ | (x
 in I) (n in N) }
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.lie_mem_lie`：lie_mem_lie {x : L} {m : M} (hx : x in I) (hm 
: m in N) : ⁅x, m⁆ in ⁅I, N⁆
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
-/
theorem lieModule_lcs_map_le (k : ℕ) :
    (lowerCentralSeries R L M k : Submodule R M).map g ≤ lowerCentralSeries R L₂ M₂ k := by
  induction k with
  | zero =>
    simp [Submodule.map_top]
  | succ k ih =>
    rw [lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', Submodule.map_span,
      Submodule.span_le]
    rintro m₂ ⟨m, ⟨x, n, m_n, ⟨h₁, h₂⟩⟩, rfl⟩
    simp only [lowerCentralSeries_succ, SetLike.mem_coe, LieSubmodule.mem_toSubmodule]
    have : ∃ y : L₂, ∃ n : lowerCentralSeries R L₂ M₂ k, ⁅y, n⁆ = g m := by
      use f x, ⟨g m_n, ih (Submodule.mem_map_of_mem h₁)⟩
      simp [hfg x m_n, h₂]
    obtain ⟨y, n, hn⟩ := this
    rw [← hn]
    apply LieSubmodule.lie_mem_lie
    · simp
    · exact SetLike.coe_mem n

variable [LieModule R L₂ M₂] (hg_inj : Injective g)

include hg_inj hfg in
/-
**Function.Injective.lieModuleIsNilpotent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.lieModuleIsNilpotent [IsNilpotent L₂ M₂] : IsNilpotent 
L M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.IsNilpotent.nilpotent`：∀ (R : Type u) (L : Type v) (M : Type w
) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 :
 AddCommGroup M] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.isNilpotent_iff`：isNilpotent_iff : IsNilpotent L M ↔ exists k,
 lowerCentralSeries R L M k = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `lieModule_lcs_map_le`：lieModule_lcs_map_le (k : Nat) : (lowerCentralSeri
es R L M k : Submodule R M).map g <= lowerCentralSeries R L₂ M₂ k
-/
theorem Function.Injective.lieModuleIsNilpotent [IsNilpotent L₂ M₂] : IsNilpotent L M := by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L₂ M₂
  rw [isNilpotent_iff R]
  use k
  rw [← LieSubmodule.toSubmodule_inj] at hk ⊢
  apply Submodule.map_injective_of_injective hg_inj
  simpa [hk] using lieModule_lcs_map_le hfg k

variable (hf_surj : Surjective f) (hg_surj : Surjective g)

include hf_surj hg_surj hfg in
/-
**Function.Surjective.lieModule_lcs_map_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.lieModule_lcs_map_eq (k : Nat) : (lowerCentralSeries R
 L M k : Submodule R M).map g = lowerCentralSeries R L₂ M₂ k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `lieModule_lcs_map_le`：lieModule_lcs_map_le (k : Nat) : (lowerCentralSeri
es R L M k : Submodule R M).map g <= lowerCentralSeries R L₂ M₂ k
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span'`：lieIdeal_oper_eq_linear_span
' [LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅x, n⁆ | (x
 in I) (n in N) }
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
-/
theorem Function.Surjective.lieModule_lcs_map_eq (k : ℕ) :
    (lowerCentralSeries R L M k : Submodule R M).map g = lowerCentralSeries R L₂ M₂ k := by
  refine le_antisymm (lieModule_lcs_map_le hfg k) ?_
  induction k with
  | zero => simpa [LinearMap.range_eq_top]
  | succ k ih =>
    suffices
      {m | ∃ (x : L₂) (n : _), n ∈ lowerCentralSeries R L M k ∧ ⁅x, g n⁆ = m} ⊆
        g '' {m | ∃ (x : L) (n : _), n ∈ lowerCentralSeries R L M k ∧ ⁅x, n⁆ = m} by
      simp only [← LieSubmodule.mem_toSubmodule] at this
      simp_rw [lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span',
        Submodule.map_span, LieSubmodule.mem_top, true_and, ← LieSubmodule.mem_toSubmodule]
      refine Submodule.span_mono (Set.Subset.trans ?_ this)
      rintro m₁ ⟨x, n, hn, rfl⟩
      obtain ⟨n', hn', rfl⟩ := ih hn
      exact ⟨x, n', hn', rfl⟩
    rintro m₂ ⟨x, n, hn, rfl⟩
    obtain ⟨y, rfl⟩ := hf_surj x
    exact ⟨⁅y, n⁆, ⟨y, n, hn, rfl⟩, (hfg y n).symm⟩

include hf_surj hg_surj hfg in
/-
**Function.Surjective.lieModuleIsNilpotent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.lieModuleIsNilpotent [IsNilpotent L M] : IsNilpotent L
₂ M₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.IsNilpotent.nilpotent`：∀ (R : Type u) (L : Type v) (M : Type w
) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 :
 AddCommGroup M] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.isNilpotent_iff`：isNilpotent_iff : IsNilpotent L M ↔ exists k,
 lowerCentralSeries R L M k = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Surjective.lieModule_lcs_map_eq`：Function.Surjective.lieModule_
lcs_map_eq (k : Nat) : (lowerCentralSeries R L M k : Submodule R M).map g = lowe
rCentralSeries R L₂ M₂ k
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Function.Surjective.lieModuleIsNilpotent [IsNilpotent L M] : IsNilpotent L₂ M₂ := by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M
  rw [isNilpotent_iff R]
  use k
  rw [← LieSubmodule.toSubmodule_inj] at hk ⊢
  simp [← hf_surj.lieModule_lcs_map_eq hfg hg_surj k, hk]
/-
**Equiv.lieModule_isNilpotent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.lieModule_isNilpotent_iff (f : L ≃ₗ⁅R⁆ L₂) (g : M ≃ₗ[R] M₂) (hfg : f
orall x m, ⁅f x, g m⁆ = g ⁅x, m⁆) : IsNilpotent L M ↔ IsNilpotent L₂ M₂
参数：f : L ≃ₗ⁅R⁆ L₂；g : M ≃ₗ[R] M₂；hfg : forall x m, ⁅f x, g m⁆ = g ⁅x, m⁆。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Function.Surjective.lieModuleIsNilpotent`：Function.Surjective.lieModuleI
sNilpotent [IsNilpotent L M] : IsNilpotent L₂ M₂
· 使用定理 `LieEquiv.surjective`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [inst : 
CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieRing L₂]   [inst_3 : LieAlgebra R
 L₁] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `LieEquiv.coe_toLieHom`：coe_toLieHom (e : L₁ ≃ₗ⁅R⁆ L₂) : ⇑(e : L₁ ->ₗ⁅R⁆ 
L₂) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `LieEquiv.apply_symm_apply`：apply_symm_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : forall x
, e (e.symm x) = x
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem Equiv.lieModule_isNilpotent_iff (f : L ≃ₗ⁅R⁆ L₂) (g : M ≃ₗ[R] M₂)
    (hfg : ∀ x m, ⁅f x, g m⁆ = g ⁅x, m⁆) : IsNilpotent L M ↔ IsNilpotent L₂ M₂ := by
  constructor <;> intro h
  · have hg : Surjective (g : M →ₗ[R] M₂) := g.surjective
    exact f.surjective.lieModuleIsNilpotent hfg hg
  · have hg : Surjective (g.symm : M₂ →ₗ[R] M) := g.symm.surjective
    refine f.symm.surjective.lieModuleIsNilpotent (fun x m => ?_) hg
    rw [LinearEquiv.coe_coe, LieEquiv.coe_toLieHom, ← g.symm_apply_apply ⁅f.symm x, g.symm m⁆, ←
      hfg, f.apply_symm_apply, g.apply_symm_apply]

@[simp]
/-
**LieModule.isNilpotent_of_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieModule.isNilpotent_of_top_iff : IsNilpotent (⊤ : LieSubalgebra R L) M ↔
 IsNilpotent L M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.lieModule_isNilpotent_iff`：Equiv.lieModule_isNilpotent_iff (f : L 
≃ₗ⁅R⁆ L₂) (g : M ≃ₗ[R] M₂) (hfg : forall x m, ⁅f x, g m⁆ = g ⁅x, m⁆) : IsNilpote
nt L M ↔ IsNilpotent …
-/
theorem LieModule.isNilpotent_of_top_iff :
    IsNilpotent (⊤ : LieSubalgebra R L) M ↔ IsNilpotent L M :=
  Equiv.lieModule_isNilpotent_iff LieSubalgebra.topEquiv (1 : M ≃ₗ[R] M) fun _ _ => rfl
/-
**LieModule.isNilpotent_of_top_iff'** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _root_.M
odule R M] [inst_5 : LieRingModule L M] [LieModule R L M],   LieModule.IsNilpote
nt L ↥⊤ ↔ LieModule.IsNilpotent L M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.lieModule_isNilpotent_iff`：Equiv.lieModule_isNilpotent_iff (f : L 
≃ₗ⁅R⁆ L₂) (g : M ≃ₗ[R] M₂) (hfg : forall x m, ⁅f x, g m⁆ = g ⁅x, m⁆) : IsNilpote
nt L M ↔ IsNilpotent …
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
@[simp] lemma LieModule.isNilpotent_of_top_iff' :
    IsNilpotent L {x // x ∈ (⊤ : LieSubmodule R L M)} ↔ IsNilpotent L M :=
  Equiv.lieModule_isNilpotent_iff 1 (LinearEquiv.ofTop ⊤ rfl) fun _ _ ↦ rfl

end Morphisms

namespace LieModule

variable (R L M)
variable [LieModule R L M]

/-
**LieModule.isNilpotent_of_le** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：isNilpotent_of_le (M₁ M₂ : LieSubmodule R L M) (h₁ : M₁ <= M₂) [IsNilpoten
t L M₂] : IsNilpotent L M₁
参数：M₁ M₂ : LieSubmodule R L M；h₁ : M₁ <= M₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Function.Injective.lieModuleIsNilpotent`：Function.Injective.lieModuleIsN
ilpotent [IsNilpotent L₂ M₂] : IsNilpotent L M
· 使用定理 `Submodule.inclusion_injective`：inclusion_injective (h : p <= p') : Funct
ion.Injective (inclusion h)
-/
theorem isNilpotent_of_le (M₁ M₂ : LieSubmodule R L M) (h₁ : M₁ ≤ M₂) [IsNilpotent L M₂] :
    IsNilpotent L M₁ := by
  let f : L →ₗ⁅R⁆ L := LieHom.id
  let g : M₁ →ₗ[R] M₂ := Submodule.inclusion h₁
  have hfg : ∀ x m, ⁅f x, g m⁆ = g ⁅x, m⁆ := by aesop
  exact (Submodule.inclusion_injective h₁).lieModuleIsNilpotent hfg

/-- The max nilpotent submodule is the `sSup` of all nilpotent submodules. -/
/-
**LieModule.maxNilpotentSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：maxNilpotentSubmodule
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […

--- 原说明 ---
The max nilpotent submodule is the `sSup` of all nilpotent submodules.
-/
def maxNilpotentSubmodule :=
  sSup { N : LieSubmodule R L M | IsNilpotent L N }

-- TODO: should infer_instance be considered normalising?
set_option linter.flexible false in
/-
**LieModule.instMaxNilpotentSubmoduleIsNilpotent** 是 Mathlib 中的一个实例，位于命名空间 `LieM
odule`。
形式化陈述：instMaxNilpotentSubmoduleIsNilpotent [IsNoetherian R M] : IsNilpotent L (m
axNilpotentSubmodule R L M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteLattice.WellFoundedGT.isSupClosedCompact`：∀ (α : Type u_2) [inst
 : CompleteLattice α], WellFoundedGT α → CompleteLattice.IsSupClosedCompact α
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LieModule.trivialIsNilpotent`：∀ (L : Type v) (M : Type w) [inst : LieRin
g L] [inst_1 : AddCommGroup M] [inst_2 : LieRingModule L M]   [LieModule.IsTrivi
al L M], LieModule…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
instance instMaxNilpotentSubmoduleIsNilpotent [IsNoetherian R M] :
    IsNilpotent L (maxNilpotentSubmodule R L M) := by
  have hwf := CompleteLattice.WellFoundedGT.isSupClosedCompact (LieSubmodule R L M) inferInstance
  refine hwf { N : LieSubmodule R L M | IsNilpotent L N } ⟨⊥, ?_⟩ fun N₁ h₁ N₂ h₂ => ?_ <;>
  simp_all <;> infer_instance
/-
**LieModule.isNilpotent_iff_le_maxNilpotentSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `
LieModule`。
形式化陈述：isNilpotent_iff_le_maxNilpotentSubmodule [IsNoetherian R M] (N : LieSubmod
ule R L M) : IsNilpotent L N ↔ N <= maxNilpotentSubmodule R L M
参数：N : LieSubmodule R L M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `LieModule.isNilpotent_of_le`：isNilpotent_of_le (M₁ M₂ : LieSubmodule R L
 M) (h₁ : M₁ <= M₂) [IsNilpotent L M₂] : IsNilpotent L M₁
-/
theorem isNilpotent_iff_le_maxNilpotentSubmodule [IsNoetherian R M] (N : LieSubmodule R L M) :
    IsNilpotent L N ↔ N ≤ maxNilpotentSubmodule R L M :=
  ⟨fun h ↦ le_sSup h, fun h ↦ isNilpotent_of_le R L M N (maxNilpotentSubmodule R L M) h⟩
/-
**LieModule.maxNilpotentSubmodule_eq_top_of_isNilpotent** 是 Mathlib 中的一个定理，位于命名空
间 `LieModule`。
形式化陈述：∀ (R : Type u) (L : Type v) (M : Type w) [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _root_.M
odule R M] [inst_5 : LieRingModule L M] [LieModule R L M]   [LieModule.IsNilpote
nt L M], LieModule.maxNilpotentSubmodule R L M = ⊤
参数：R : Type u；L : Type v；M : Type w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
@[simp] lemma maxNilpotentSubmodule_eq_top_of_isNilpotent [LieModule.IsNilpotent L M] :
    maxNilpotentSubmodule R L M = ⊤ := by
  rw [eq_top_iff]
  apply le_sSup
  simpa

end LieModule

end NilpotentModules

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) LieAlgebra.isSolvable_of_isNilpotent (L : Type v)
    [LieRing L] [hL : LieModule.IsNilpotent L L] :
    LieAlgebra.IsSolvable L := by
  obtain ⟨k, h⟩ : ∃ k, LieModule.lowerCentralSeries ℤ L L k = ⊥ := hL.nilpotent_int
  use k; rw [← le_bot_iff] at h ⊢
  exact le_trans (LieModule.derivedSeries_le_lowerCentralSeries ℤ L k) h

section NilpotentAlgebras

variable (R : Type u) (L : Type v) (L' : Type w)
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

/-- We say a Lie ring is nilpotent when it is nilpotent as a Lie module over itself via the
adjoint representation. -/
/-
**LieRing.IsNilpotent** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LieRing.IsNilpotent (L : Type v) [LieRing L] : Prop
参数：L : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say a Lie ring is nilpotent when it is nilpotent as a Lie module over itself 
via the
adjoint representation.
-/
abbrev LieRing.IsNilpotent (L : Type v) [LieRing L] : Prop :=
  LieModule.IsNilpotent L L

open LieRing
/-
**LieAlgebra.nilpotent_ad_of_nilpotent_algebra** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieAlgebra.nilpotent_ad_of_nilpotent_algebra [IsNilpotent L] : exists k : 
Nat, forall x : L, ad R L x ^ k = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.exists_forall_pow_toEnd_eq_zero`：exists_forall_pow_toEnd_eq_ze
ro [IsNilpotent L M] : exists k : Nat, forall x : L, toEnd R L M x ^ k = 0
-/
theorem LieAlgebra.nilpotent_ad_of_nilpotent_algebra [IsNilpotent L] :
    ∃ k : ℕ, ∀ x : L, ad R L x ^ k = 0 :=
  LieModule.exists_forall_pow_toEnd_eq_zero R L L

-- TODO Generalise the below to Lie modules if / when we define morphisms, equivs of Lie modules
-- covering a Lie algebra morphism of (possibly different) Lie algebras.
variable {R L L'}

open LieModule (lowerCentralSeries)

/-- Given an ideal `I` of a Lie algebra `L`, the lower central series of `L ⧸ I` is the same
whether we regard `L ⧸ I` as an `L` module or an `L ⧸ I` module.

TODO: This result obviously generalises but the generalisation requires the missing definition of
morphisms between Lie modules over different Lie algebras. -/
-- Porting note: added `LieSubmodule.toSubmodule` in the statement
/-
**coe_lowerCentralSeries_ideal_quot_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_lowerCentralSeries_ideal_quot_eq {I : LieIdeal R L} (k : Nat) : LieSub
module.toSubmodule (lowerCentralSeries R L (L ⧸ I) k) = LieSubmodule.toSubmodule
 (lowerCentralSeries R (L ⧸ I) (L ⧸ I) k)
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span`：lieIdeal_oper_eq_linear_span 
[LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅(x : L), (n 
: M)⁆ | (x : I) (n : N) }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LieSubmodule.mem_top`：mem_top (x : M) : x in (⊤ : LieSubmodule R L M)
· 使用定理 `LieSubmodule.mem_toSubmodule`：mem_toSubmodule {x : M} : x in (N : Submod
ule R M) ↔ x in N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coe_lowerCentralSeries_ideal_quot_eq {I : LieIdeal R L} (k : ℕ) :
    LieSubmodule.toSubmodule (lowerCentralSeries R L (L ⧸ I) k) =
      LieSubmodule.toSubmodule (lowerCentralSeries R (L ⧸ I) (L ⧸ I) k) := by
  induction k with
  | zero =>
    simp only [LieModule.lowerCentralSeries_zero, LieSubmodule.top_toSubmodule]
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
    congr
    ext x
    constructor
    · rintro ⟨⟨y, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩
      rw [← LieSubmodule.mem_toSubmodule, ih, LieSubmodule.mem_toSubmodule] at hz
      exact ⟨⟨LieSubmodule.Quotient.mk y, LieSubmodule.mem_top _⟩, ⟨z, hz⟩, rfl⟩
    · rintro ⟨⟨⟨y⟩, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩
      rw [← LieSubmodule.mem_toSubmodule, ← ih, LieSubmodule.mem_toSubmodule] at hz
      exact ⟨⟨y, LieSubmodule.mem_top _⟩, ⟨z, hz⟩, rfl⟩

/-- Note that the below inequality can be strict. For example the ideal of strictly-upper-triangular
2x2 matrices inside the Lie algebra of upper-triangular 2x2 matrices with `k = 1`. -/
-- Porting note: added `LieSubmodule.toSubmodule` in the statement
/-
**LieModule.coe_lowerCentralSeries_ideal_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieModule.coe_lowerCentralSeries_ideal_le {I : LieIdeal R L} (k : Nat) : L
ieSubmodule.toSubmodule (lowerCentralSeries R I I k) <= lowerCentralSeries R L I
 k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span`：lieIdeal_oper_eq_linear_span 
[LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅(x : L), (n 
: M)⁆ | (x : I) (n : N) }
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `LieSubmodule.mem_top`：mem_top (x : M) : x in (⊤ : LieSubmodule R L M)
-/
theorem LieModule.coe_lowerCentralSeries_ideal_le {I : LieIdeal R L} (k : ℕ) :
    LieSubmodule.toSubmodule (lowerCentralSeries R I I k) ≤ lowerCentralSeries R L I k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
    apply Submodule.span_mono
    rintro x ⟨⟨y, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩
    exact ⟨⟨y.val, LieSubmodule.mem_top _⟩, ⟨z, ih hz⟩, rfl⟩

/-- A central extension of nilpotent Lie algebras is nilpotent. -/
/-
**LieAlgebra.nilpotent_of_nilpotent_quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieAlgebra.nilpotent_of_nilpotent_quotient {I : LieIdeal R L} (h₁ : I <= c
enter R L) (h₂ : IsNilpotent (L ⧸ I)) : IsNilpotent L
参数：h₁ : I <= center R L；h₂ : IsNilpotent (L ⧸ I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.isNilpotent_iff`：isNilpotent_iff : IsNilpotent L M ↔ exists k,
 lowerCentralSeries R L M k = ⊥
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coe_lowerCentralSeries_ideal_quot_eq`：coe_lowerCentralSeries_ideal_quot_
eq {I : LieIdeal R L} (k : Nat) : LieSubmodule.toSubmodule (lowerCentralSeries R
 L (L ⧸ I) k) = LieSubmodu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LieModule.nilpotentOfNilpotentQuotient`：nilpotentOfNilpotentQuotient {N 
: LieSubmodule R L M} (h₁ : N <= maxTrivSubmodule R L M) (h₂ : IsNilpotent L (M 
⧸ N)) : IsNilpotent L M

--- 原说明 ---
A central extension of nilpotent Lie algebras is nilpotent.
-/
theorem LieAlgebra.nilpotent_of_nilpotent_quotient {I : LieIdeal R L} (h₁ : I ≤ center R L)
    (h₂ : IsNilpotent (L ⧸ I)) : IsNilpotent L := by
  suffices LieModule.IsNilpotent L (L ⧸ I) by
    exact LieModule.nilpotentOfNilpotentQuotient R L L h₁ this
  simp only [LieRing.IsNilpotent, LieModule.isNilpotent_iff R] at h₂ ⊢
  peel h₂ with k hk
  simp [← LieSubmodule.toSubmodule_inj, coe_lowerCentralSeries_ideal_quot_eq, hk]
/-
**LieAlgebra.non_trivial_center_of_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieAlgebra.non_trivial_center_of_isNilpotent [Nontrivial L] [IsNilpotent L
] : Nontrivial center R L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.nontrivial_max_triv_of_isNilpotent`：nontrivial_max_triv_of_isN
ilpotent [Nontrivial M] [IsNilpotent L M] : Nontrivial (maxTrivSubmodule R L M)
-/
theorem LieAlgebra.non_trivial_center_of_isNilpotent [Nontrivial L] [IsNilpotent L] :
    Nontrivial <| center R L :=
  LieModule.nontrivial_max_triv_of_isNilpotent R L L
/-
**LieIdeal.map_lowerCentralSeries_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieIdeal.map_lowerCentralSeries_le (k : Nat) {f : L ->ₗ⁅R⁆ L'} : LieIdeal.
map f (lowerCentralSeries R L L k) <= lowerCentralSeries R L' L' k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LieIdeal.map_bracket_le`：map_bracket_le {I₁ I₂ : LieIdeal R L} : map f ⁅
I₁, I₂⁆ <= ⁅map f I₁, map f I₂⁆
· 使用定理 `LieSubmodule.mono_lie`：mono_lie (h₁ : I <= J) (h₂ : N <= N') : ⁅I, N⁆ <=
 ⁅J, N'⁆
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem LieIdeal.map_lowerCentralSeries_le (k : ℕ) {f : L →ₗ⁅R⁆ L'} :
    LieIdeal.map f (lowerCentralSeries R L L k) ≤ lowerCentralSeries R L' L' k := by
  induction k with
  | zero => simp only [LieModule.lowerCentralSeries_zero, le_top]
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ]
    exact le_trans (LieIdeal.map_bracket_le f) (LieSubmodule.mono_lie le_top ih)
/-
**LieIdeal.lowerCentralSeries_map_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieIdeal.lowerCentralSeries_map_eq (k : Nat) {f : L ->ₗ⁅R⁆ L'} (h : Functi
on.Surjective f) : LieIdeal.map f (lowerCentralSeries R L L k) = lowerCentralSer
ies R L' L' k
参数：k : Nat；h : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieHom.idealRange_eq_map`：idealRange_eq_map : f.idealRange = LieIdeal.ma
p f ⊤
· 使用定理 `LieHom.idealRange_eq_top_of_surjective`：idealRange_eq_top_of_surjective 
(h : Function.Surjective f) : f.idealRange = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `LieIdeal.map_bracket_eq`：map_bracket_eq {I₁ I₂ : LieIdeal R L} (h : Func
tion.Surjective f) : map f ⁅I₁, I₂⁆ = ⁅map f I₁, map f I₂⁆
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LieIdeal.lowerCentralSeries_map_eq (k : ℕ) {f : L →ₗ⁅R⁆ L'} (h : Function.Surjective f) :
    LieIdeal.map f (lowerCentralSeries R L L k) = lowerCentralSeries R L' L' k := by
  have h' : (⊤ : LieIdeal R L).map f = ⊤ := by
    rw [← f.idealRange_eq_map]
    exact f.idealRange_eq_top_of_surjective h
  induction k with
  | zero => simp only [LieModule.lowerCentralSeries_zero]; exact h'
  | succ k ih => simp only [LieModule.lowerCentralSeries_succ, LieIdeal.map_bracket_eq f h, ih, h']
/-
**Function.Injective.lieAlgebra_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.lieAlgebra_isNilpotent [h₁ : IsNilpotent L'] {f : L ->ₗ
⁅R⁆ L'} (h₂ : Function.Injective f) : IsNilpotent L
参数：h₂ : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieRing.IsNilpotent.eq_1`：∀ (L : Type v) [inst : LieRing L], LieRing.IsN
ilpotent L = LieModule.IsNilpotent L L
· 使用引理 `LieModule.isNilpotent_iff`：isNilpotent_iff : IsNilpotent L M ↔ exists k,
 lowerCentralSeries R L M k = ⊥
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `LieIdeal.bot_of_map_eq_bot`：bot_of_map_eq_bot {I : LieIdeal R L} (h₁ : F
unction.Injective f) (h₂ : I.map f = ⊥) : I = ⊥
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieIdeal.map_lowerCentralSeries_le`：LieIdeal.map_lowerCentralSeries_le (
k : Nat) {f : L ->ₗ⁅R⁆ L'} : LieIdeal.map f (lowerCentralSeries R L L k) <= lowe
rCentralSeries R L' L' k
-/
theorem Function.Injective.lieAlgebra_isNilpotent [h₁ : IsNilpotent L'] {f : L →ₗ⁅R⁆ L'}
    (h₂ : Function.Injective f) : IsNilpotent L := by
  rw [LieRing.IsNilpotent, LieModule.isNilpotent_iff R] at h₁ ⊢
  peel h₁ with k hk
  apply LieIdeal.bot_of_map_eq_bot h₂; rw [eq_bot_iff, ← hk]
  apply LieIdeal.map_lowerCentralSeries_le
/-
**Function.Surjective.lieAlgebra_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.lieAlgebra_isNilpotent [h₁ : IsNilpotent L] {f : L ->ₗ
⁅R⁆ L'} (h₂ : Function.Surjective f) : IsNilpotent L'
参数：h₂ : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieRing.IsNilpotent.eq_1`：∀ (L : Type v) [inst : LieRing L], LieRing.IsN
ilpotent L = LieModule.IsNilpotent L L
· 使用引理 `LieModule.isNilpotent_iff`：isNilpotent_iff : IsNilpotent L M ↔ exists k,
 lowerCentralSeries R L M k = ⊥
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieIdeal.lowerCentralSeries_map_eq`：LieIdeal.lowerCentralSeries_map_eq (
k : Nat) {f : L ->ₗ⁅R⁆ L'} (h : Function.Surjective f) : LieIdeal.map f (lowerCe
ntralSeries R L L k) = l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem Function.Surjective.lieAlgebra_isNilpotent [h₁ : IsNilpotent L] {f : L →ₗ⁅R⁆ L'}
    (h₂ : Function.Surjective f) : IsNilpotent L' := by
  rw [LieRing.IsNilpotent, LieModule.isNilpotent_iff R] at h₁ ⊢
  peel h₁ with k hk
  rw [← LieIdeal.lowerCentralSeries_map_eq k h₂, hk]
  simp only [LieIdeal.map_eq_bot_iff, bot_le]
/-
**LieEquiv.nilpotent_iff_equiv_nilpotent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieEquiv.nilpotent_iff_equiv_nilpotent (e : L ≃ₗ⁅R⁆ L') : IsNilpotent L ↔ 
IsNilpotent L'
参数：e : L ≃ₗ⁅R⁆ L'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.lieAlgebra_isNilpotent`：Function.Injective.lieAlgebra
_isNilpotent [h₁ : IsNilpotent L'] {f : L ->ₗ⁅R⁆ L'} (h₂ : Function.Injective f)
 : IsNilpotent L
· 使用定理 `LieEquiv.injective`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [inst : C
ommRing R] [inst_1 : LieRing L₁] [inst_2 : LieRing L₂]   [inst_3 : LieAlgebra R 
L₁] [ins…
-/
theorem LieEquiv.nilpotent_iff_equiv_nilpotent (e : L ≃ₗ⁅R⁆ L') :
    IsNilpotent L ↔ IsNilpotent L' := by
  constructor <;> intro h
  · exact e.symm.injective.lieAlgebra_isNilpotent
  · exact e.injective.lieAlgebra_isNilpotent
/-
**LieHom.isNilpotent_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieHom.isNilpotent_range [IsNilpotent L] (f : L ->ₗ⁅R⁆ L') : IsNilpotent f
.range
参数：f : L ->ₗ⁅R⁆ L'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.lieAlgebra_isNilpotent`：Function.Surjective.lieAlgeb
ra_isNilpotent [h₁ : IsNilpotent L] {f : L ->ₗ⁅R⁆ L'} (h₂ : Function.Surjective 
f) : IsNilpotent L'
· 使用定理 `LieHom.surjective_rangeRestrict`：surjective_rangeRestrict : Function.Sur
jective f.rangeRestrict
-/
theorem LieHom.isNilpotent_range [IsNilpotent L] (f : L →ₗ⁅R⁆ L') : IsNilpotent f.range :=
  f.surjective_rangeRestrict.lieAlgebra_isNilpotent

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Note that this result is not quite a special case of
`LieModule.isNilpotent_range_toEnd_iff` which concerns nilpotency of the
`(ad R L).range`-module `L`, whereas this result concerns nilpotency of the `(ad R L).range`-module
`(ad R L).range`. -/
@[simp]
/-
**LieAlgebra.isNilpotent_range_ad_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieAlgebra.isNilpotent_range_ad_iff : IsNilpotent (ad R L).range ↔ IsNilpo
tent L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.self_module_ker_eq_center`：self_module_ker_eq_center : LieMod
ule.ker R L L = center R L
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LieAlgebra.nilpotent_of_nilpotent_quotient`：LieAlgebra.nilpotent_of_nilp
otent_quotient {I : LieIdeal R L} (h₁ : I <= center R L) (h₂ : IsNilpotent (L ⧸ 
I)) : IsNilpotent L
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieEquiv.nilpotent_iff_equiv_nilpotent`：LieEquiv.nilpotent_iff_equiv_nil
potent (e : L ≃ₗ⁅R⁆ L') : IsNilpotent L ↔ IsNilpotent L'
· 使用定理 `LieHom.isNilpotent_range`：LieHom.isNilpotent_range [IsNilpotent L] (f : 
L ->ₗ⁅R⁆ L') : IsNilpotent f.range

--- 原说明 ---
Note that this result is not quite a special case of
`LieModule.isNilpotent_range_toEnd_iff` which concerns nilpotency of the
`(ad R L).range`-module `L`, whereas this result concerns nilpotency of the `(ad
 R L).range`-module
`(ad R L).range`.
-/
theorem LieAlgebra.isNilpotent_range_ad_iff : IsNilpotent (ad R L).range ↔ IsNilpotent L := by
  refine ⟨fun h => ?_, ?_⟩
  · have : (ad R L).ker = center R L := by simp
    exact
      LieAlgebra.nilpotent_of_nilpotent_quotient (le_of_eq this)
        ((ad R L).quotKerEquivRange.nilpotent_iff_equiv_nilpotent.mpr h)
  · intro h
    exact (ad R L).isNilpotent_range
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : LieRing.IsNilpotent L] : LieRing.IsNilpotent (⊤ : LieSubalgebra R L) :=
  LieSubalgebra.topEquiv.nilpotent_iff_equiv_nilpotent.mpr h

end NilpotentAlgebras

namespace LieIdeal

open LieModule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (I : LieIdeal R L)
variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M]
variable (k : ℕ)

/-- Given a Lie module `M` over a Lie algebra `L` together with an ideal `I` of `L`, this is the
lower central series of `M` as an `I`-module. The advantage of using this definition instead of
`LieModule.lowerCentralSeries R I M` is that its terms are Lie submodules of `M` as an
`L`-module, rather than just as an `I`-module.

See also `LieIdeal.coe_lcs_eq`. -/
/-
**LieIdeal.lcs** 是 Mathlib 中的一个定义，位于命名空间 `LieIdeal`。
形式化陈述：lcs : LieSubmodule R L M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Lie module `M` over a Lie algebra `L` together with an ideal `I` of `L`,
 this is the
lower central series of `M` as an `I`-module. The advantage of using this defini
tion instead of
`LieModule.lowerCentralSeries R I M` is that its terms are Lie submodules of `M`
 as an
`L`-module, rather than just as an `I`-module.

See also `LieIdeal.coe_lcs_eq`.
-/
def lcs : LieSubmodule R L M :=
  (fun N => ⁅I, N⁆)^[k] ⊤

@[simp]
/-
**LieIdeal.lcs_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：lcs_zero : I.lcs M 0 = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lcs_zero : I.lcs M 0 = ⊤ :=
  rfl

@[simp]
/-
**LieIdeal.lcs_succ** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：lcs_succ : I.lcs M (k + 1) = ⁅I, I.lcs M k⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
-/
theorem lcs_succ : I.lcs M (k + 1) = ⁅I, I.lcs M k⁆ :=
  Function.iterate_succ_apply' (fun N => ⁅I, N⁆) k ⊤
/-
**LieIdeal.lcs_top** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：lcs_top : (⊤ : LieIdeal R L).lcs M k = lowerCentralSeries R L M k
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lcs_top : (⊤ : LieIdeal R L).lcs M k = lowerCentralSeries R L M k :=
  rfl

set_option backward.isDefEq.respectTransparency false in
-- Porting note: added `LieSubmodule.toSubmodule` in the statement
/-
**LieIdeal.coe_lcs_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：coe_lcs_eq [LieModule R L M] : LieSubmodule.toSubmodule (I.lcs M k) = lowe
rCentralSeries R I M k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieIdeal.lcs_succ`：lcs_succ : I.lcs M (k + 1) = ⁅I, I.lcs M k⁆
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span'`：lieIdeal_oper_eq_linear_span
' [LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅x, n⁆ | (x
 in I) (n in N) }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.mem_toSubmodule`：mem_toSubmodule {x : M} : x in (N : Submod
ule R M) ↔ x in N
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LieSubalgebra.coe_bracket_of_module`：coe_bracket_of_module (x : L') (m :
 M) : ⁅x, m⁆ = ⁅(x : L), m⁆
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
theorem coe_lcs_eq [LieModule R L M] :
    LieSubmodule.toSubmodule (I.lcs M k) = lowerCentralSeries R I M k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp_rw [lowerCentralSeries_succ, lcs_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', ←
      (I.lcs M k).mem_toSubmodule, ih, LieSubmodule.mem_toSubmodule, LieSubmodule.mem_top,
      true_and, (I : LieSubalgebra R L).coe_bracket_of_module]
    simp
/-
**LieIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `LieIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsNilpotent L I] : LieRing.IsNilpotent I := by
  let f : I →ₗ⁅R⁆ L := I.incl
  let g : I →ₗ⁅R⁆ I := LieHom.id
  have hfg : ∀ x m, ⁅f x, g m⁆ = g ⁅x, m⁆ := by aesop
  exact Function.injective_id.lieModuleIsNilpotent hfg

end LieIdeal

section ExtendScalars

open LieModule TensorProduct

variable (R A L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [CommRing A] [Algebra R A]

@[simp]
/-
**LieSubmodule.lowerCentralSeries_tensor_eq_baseChange** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：LieSubmodule.lowerCentralSeries_tensor_eq_baseChange (k : Nat) : lowerCent
ralSeries A (A otimes[R] L) (A otimes[R] M) k = (lowerCentralSeries R L M k).bas
eChange A
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieSubmodule.baseChange_top`：baseChange_top : (⊤ : LieSubmodule R L M).b
aseChange A = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用引理 `LieSubmodule.lie_baseChange`：lie_baseChange {I : LieIdeal R L} {N : LieS
ubmodule R L M} : ⁅I, N⁆.baseChange A = ⁅I.baseChange A, N.baseChange A⁆
-/
lemma LieSubmodule.lowerCentralSeries_tensor_eq_baseChange (k : ℕ) :
    lowerCentralSeries A (A ⊗[R] L) (A ⊗[R] M) k =
    (lowerCentralSeries R L M k).baseChange A := by
  induction k with
  | zero => simp
  | succ k ih => simp only [lowerCentralSeries_succ, ih, ← baseChange_top, lie_baseChange]
/-
**LieModule.instIsNilpotentTensor** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LieModule.instIsNilpotentTensor [IsNilpotent L M] : IsNilpotent (A otimes[
R] L) (A otimes[R] M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.IsNilpotent.nilpotent`：∀ (R : Type u) (L : Type v) (M : Type w
) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 :
 AddCommGroup M] [ins…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.isNilpotent_iff`：isNilpotent_iff : IsNilpotent L M ↔ exists k,
 lowerCentralSeries R L M k = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LieSubmodule.lowerCentralSeries_tensor_eq_baseChange`：LieSubmodule.lower
CentralSeries_tensor_eq_baseChange (k : Nat) : lowerCentralSeries A (A otimes[R]
 L) (A otimes[R] M) k = (lowerCentralSerie…
· 使用引理 `LieSubmodule.baseChange_bot`：baseChange_bot : (⊥ : LieSubmodule R L M).b
aseChange A = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance LieModule.instIsNilpotentTensor [IsNilpotent L M] :
    IsNilpotent (A ⊗[R] L) (A ⊗[R] M) := by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M
  rw [isNilpotent_iff A]
  exact ⟨k, by simp [hk]⟩

end ExtendScalars

namespace LieAlgebra

open LieModule

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The max nilpotent ideal of a Lie algebra. It is defined as the max nilpotent Lie submodule of
`L` under the adjoint action. -/
/-
**LieAlgebra.maxNilpotentIdeal** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra`。
形式化陈述：maxNilpotentIdeal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The max nilpotent ideal of a Lie algebra. It is defined as the max nilpotent Lie
 submodule of
`L` under the adjoint action.
-/
def maxNilpotentIdeal := maxNilpotentSubmodule R L L
/-
**LieAlgebra.maxNilpotentIdealIsNilpotent** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`
。
形式化陈述：maxNilpotentIdealIsNilpotent [IsNoetherian R L] : IsNilpotent L (maxNilpot
entIdeal R L)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance maxNilpotentIdealIsNilpotent [IsNoetherian R L] :
    IsNilpotent L (maxNilpotentIdeal R L) :=
  instMaxNilpotentSubmoduleIsNilpotent R L L
/-
**LieAlgebra.LieIdeal.isNilpotent_iff_le_maxNilpotentIdeal** 是 Mathlib 中的一个定理，位于
命名空间 `LieAlgebra.LieIdeal`。
形式化陈述：∀ (R : Type u) (L : Type v) [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] [IsNoetherian R L]   (I : LieIdeal R L), LieModule.IsNilpot
ent L ↥I ↔ I ≤ LieAlgebra.maxNilpotentIdeal R L
参数：R : Type u；L : Type v；I : LieIdeal R L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.isNilpotent_iff_le_maxNilpotentSubmodule`：isNilpotent_iff_le_m
axNilpotentSubmodule [IsNoetherian R M] (N : LieSubmodule R L M) : IsNilpotent L
 N ↔ N <= maxNilpotentSubmodule R L M
-/
theorem LieIdeal.isNilpotent_iff_le_maxNilpotentIdeal [IsNoetherian R L] (I : LieIdeal R L) :
    IsNilpotent L I ↔ I ≤ maxNilpotentIdeal R L :=
  isNilpotent_iff_le_maxNilpotentSubmodule R L L I
/-
**LieAlgebra.center_le_maxNilpotentIdeal** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：center_le_maxNilpotentIdeal : center R L <= maxNilpotentIdeal R L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LieModule.trivialIsNilpotent`：∀ (L : Type v) (M : Type w) [inst : LieRin
g L] [inst_1 : AddCommGroup M] [inst_2 : LieRingModule L M]   [LieModule.IsTrivi
al L M], LieModule…
· 使用定理 `LieModule.instIsTrivialSubtypeMemLieSubmoduleMaxTrivSubmodule`：∀ (R : Ty
pe u) (L : Type v) (M : Type w) [inst : CommRing R] [inst_1 : LieRing L] [inst_2
 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [ins…
-/
theorem center_le_maxNilpotentIdeal : center R L ≤ maxNilpotentIdeal R L :=
  le_sSup (trivialIsNilpotent L (center R L))
/-
**LieAlgebra.maxNilpotentIdeal_le_radical** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`
。
形式化陈述：maxNilpotentIdeal_le_radical : maxNilpotentIdeal R L <= radical R L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LieAlgebra.isSolvable_of_isNilpotent`：∀ (L : Type v) [inst : LieRing L] 
[hL : LieModule.IsNilpotent L L], LieAlgebra.IsSolvable L
· 使用定理 `LieIdeal.instIsNilpotentSubtypeMemOfIsNilpotent`：∀ {R : Type u_1} {L : T
ype u_2} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (I :
 LieIdeal R L)   [LieModule.IsNilpote…
-/
theorem maxNilpotentIdeal_le_radical : maxNilpotentIdeal R L ≤ radical R L :=
  sSup_le_sSup fun I (_ : IsNilpotent L I) ↦ isSolvable_of_isNilpotent I
/-
**LieAlgebra.maxNilpotentIdeal_eq_top_of_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 `
LieAlgebra`。
形式化陈述：∀ (R : Type u) (L : Type v) [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] [LieRing.IsNilpotent L],   LieAlgebra.maxNilpotentIdeal R L
 = ⊤
参数：R : Type u；L : Type v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.maxNilpotentSubmodule_eq_top_of_isNilpotent`：∀ (R : Type u) (L
 : Type v) (M : Type w) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAl
gebra R L]   [inst_3 : AddCommGroup M] [ins…
-/
@[simp] lemma maxNilpotentIdeal_eq_top_of_isNilpotent [LieRing.IsNilpotent L] :
    maxNilpotentIdeal R L = ⊤ :=
  maxNilpotentSubmodule_eq_top_of_isNilpotent R L L

end LieAlgebra

