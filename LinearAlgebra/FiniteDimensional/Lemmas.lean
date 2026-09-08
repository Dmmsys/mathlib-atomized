/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.IntervalCases

/-!
# Finite-dimensional vector spaces

This file contains some further development of finite-dimensional vector spaces, their dimensions,
and linear maps on such spaces.

Definitions are in `Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
and results that require fewer imports are in `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`.
-/

@[expose] public section

assert_not_exists Monoid.exponent Module.IsTorsion


universe u v v'

open Cardinal Submodule Module Function

variable {K : Type u} {V : Type v}

namespace Submodule

open IsNoetherian Module

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The dimension of a strict submodule is strictly bounded by the dimension of the ambient
space.

See also `Submodule.length_lt`. -/
/-
**Submodule.finrank_lt** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：finrank_lt [FiniteDimensional K V] {s : Submodule K V} (h : s != ⊤) : finr
ank K s < finrank K V
参数：h : s != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.finrank_quotient_add_finrank`：Submodule.finrank_quotient_add_f
inrank [Module.Finite R M] (N : Submodule R M) : finrank R (M ⧸ N) + finrank R N
 = finrank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.lt_add_of_pos_right`：∀ {k n : ℕ}, 0 < k → n < n + k
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Submodule.Quotient.nontrivial_iff`：∀ {R : Type u_1} {M : Type u_2} [inst
 : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submodu
le R M}, Nontrivial (M …

--- 原说明 ---
The dimension of a strict submodule is strictly bounded by the dimension of the 
ambient
space.

See also `Submodule.length_lt`.
-/
theorem finrank_lt [FiniteDimensional K V] {s : Submodule K V} (h : s ≠ ⊤) :
    finrank K s < finrank K V := by
  rw [← s.finrank_quotient_add_finrank, add_comm]
  rw [← Quotient.nontrivial_iff] at h
  exact Nat.lt_add_of_pos_right finrank_pos

/-- The sum of the dimensions of s + t and s ∩ t is the sum of the dimensions of s and t -/
/-
**Submodule.finrank_sup_add_finrank_inf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：finrank_sup_add_finrank_inf_eq (s t : Submodule K V) [FiniteDimensional K 
s] [FiniteDimensional K t] : finrank K ↑(s ⊔ t) + finrank K ↑(s ⊓ t) = finrank K
 ↑s + finrank K ↑t
参数：s t : Submodule K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.rank_sup_add_rank_inf_eq`：Submodule.rank_sup_add_rank_inf_eq (
s t : Submodule R M) : Module.rank R (s ⊔ t : Submodule R M) + Module.rank R (s 
⊓ t : Submodule R M) = M…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K

--- 原说明 ---
The sum of the dimensions of s + t and s ∩ t is the sum of the dimensions of s a
nd t
-/
theorem finrank_sup_add_finrank_inf_eq (s t : Submodule K V) [FiniteDimensional K s]
    [FiniteDimensional K t] :
    finrank K ↑(s ⊔ t) + finrank K ↑(s ⊓ t) = finrank K ↑s + finrank K ↑t := by
  have key : Module.rank K ↑(s ⊔ t) + Module.rank K ↑(s ⊓ t) = Module.rank K s + Module.rank K t :=
    rank_sup_add_rank_inf_eq s t
  repeat rw [← finrank_eq_rank] at key
  norm_cast at key
/-
**Submodule.finrank_add_le_finrank_add_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule`。
形式化陈述：finrank_add_le_finrank_add_finrank (s t : Submodule K V) [FiniteDimensiona
l K s] [FiniteDimensional K t] : finrank K (s ⊔ t : Submodule K V) <= finrank K 
s + finrank K t
参数：s t : Submodule K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.finrank_sup_add_finrank_inf_eq`：finrank_sup_add_finrank_inf_eq
 (s t : Submodule K V) [FiniteDimensional K s] [FiniteDimensional K t] : finrank
 K ↑(s ⊔ t) + finrank K ↑(s ⊓ …
· 使用定理 `self_le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] (a b : α), a ≤ a + b
-/
theorem finrank_add_le_finrank_add_finrank (s t : Submodule K V) [FiniteDimensional K s]
    [FiniteDimensional K t] : finrank K (s ⊔ t : Submodule K V) ≤ finrank K s + finrank K t := by
  rw [← finrank_sup_add_finrank_inf_eq]
  exact self_le_add_right _ _
/-
**Submodule.finrank_add_finrank_le_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule`。
形式化陈述：finrank_add_finrank_le_of_disjoint [FiniteDimensional K V] {s t : Submodul
e K V} (hdisjoint : Disjoint s t) : finrank K s + finrank K t <= finrank K V
参数：hdisjoint : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.finrank_sup_add_finrank_inf_eq`：finrank_sup_add_finrank_inf_eq
 (s t : Submodule K V) [FiniteDimensional K s] [FiniteDimensional K t] : finrank
 K ↑(s ⊔ t) + finrank K ↑(s ⊓ …
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `finrank_bot`：finrank_bot : finrank R (⊥ : Submodule R M) = 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Submodule.finrank_le`：Submodule.finrank_le [Module.Finite R M] (s : Subm
odule R M) : finrank R s <= finrank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
-/
theorem finrank_add_finrank_le_of_disjoint [FiniteDimensional K V]
    {s t : Submodule K V} (hdisjoint : Disjoint s t) :
    finrank K s + finrank K t ≤ finrank K V := by
  rw [← Submodule.finrank_sup_add_finrank_inf_eq s t, hdisjoint.eq_bot, finrank_bot, add_zero]
  exact Submodule.finrank_le _
/-
**Submodule.eq_top_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：eq_top_of_disjoint [FiniteDimensional K V] (s t : Submodule K V) (hdim : f
inrank K V <= finrank K s + finrank K t) (hdisjoint : Disjoint s t) : s ⊔ t = ⊤
参数：s t : Submodule K V；hdim : finrank K V <= finrank K s + finrank K t；hdisjoint
 : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `finrank_bot`：finrank_bot : finrank R (⊥ : Submodule R M) = 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Submodule.eq_top_of_finrank_eq`：∀ {K : Type u} {V : Type v} [inst : Divi
sionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [FiniteDime
nsional K V] {S : Su…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.finrank_add_finrank_le_of_disjoint`：finrank_add_finrank_le_of_
disjoint [FiniteDimensional K V] {s t : Submodule K V} (hdisjoint : Disjoint s t
) : finrank K s + finrank K t <= f…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Submodule.finrank_sup_add_finrank_inf_eq`：finrank_sup_add_finrank_inf_eq
 (s t : Submodule K V) [FiniteDimensional K s] [FiniteDimensional K t] : finrank
 K ↑(s ⊔ t) + finrank K ↑(s ⊓ …
-/
theorem eq_top_of_disjoint [FiniteDimensional K V] (s t : Submodule K V)
    (hdim : finrank K V ≤ finrank K s + finrank K t) (hdisjoint : Disjoint s t) : s ⊔ t = ⊤ := by
  have h_finrank_inf : finrank K ↑(s ⊓ t) = 0 := by
    rw [disjoint_iff_inf_le, le_bot_iff] at hdisjoint
    rw [hdisjoint, finrank_bot]
  apply eq_top_of_finrank_eq
  replace hdim : finrank K V = finrank K s + finrank K t :=
    le_antisymm hdim (finrank_add_finrank_le_of_disjoint hdisjoint)
  rw [hdim]
  convert! s.finrank_sup_add_finrank_inf_eq t
  rw [h_finrank_inf, add_zero]
/-
**Submodule.isCompl_iff_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isCompl_iff_disjoint [FiniteDimensional K V] (s t : Submodule K V) (hdim :
 finrank K V <= finrank K s + finrank K t) : IsCompl s t ↔ Disjoint s t
参数：s t : Submodule K V；hdim : finrank K V <= finrank K s + finrank K t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Submodule.eq_top_of_disjoint`：eq_top_of_disjoint [FiniteDimensional K V]
 (s t : Submodule K V) (hdim : finrank K V <= finrank K s + finrank K t) (hdisjo
int : Disjoint s t…
-/
theorem isCompl_iff_disjoint [FiniteDimensional K V] (s t : Submodule K V)
    (hdim : finrank K V ≤ finrank K s + finrank K t) :
    IsCompl s t ↔ Disjoint s t :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, codisjoint_iff.mpr <| eq_top_of_disjoint s t hdim h⟩⟩
/-
**Submodule.sup_span_singleton_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：sup_span_singleton_eq_top_iff [Module.Finite K V] {W : Submodule K V} {v :
 V} (hv : v ∉ W) : W ⊔ span K {v} = ⊤ ↔ finrank K (V ⧸ W) = 1
参数：hv : v ∉ W。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Submodule.finrank_sup_add_finrank_inf_eq`：finrank_sup_add_finrank_inf_eq
 (s t : Submodule K V) [FiniteDimensional K s] [FiniteDimensional K t] : finrank
 K ↑(s ⊔ t) + finrank K ↑(s ⊓ …
· 使用引理 `Submodule.finrank_quotient_add_finrank`：Submodule.finrank_quotient_add_f
inrank [Module.Finite R M] (N : Submodule R M) : finrank R (M ⧸ N) + finrank R N
 = finrank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
· 使用定理 `finrank_bot`：finrank_bot : finrank R (⊥ : Submodule R M) = 0
· 使用定理 `finrank_span_singleton`：finrank_span_singleton {v : V} (hv : v != 0) : f
inrank K (K ∙ v) = 1
· 使用定理 `Submodule.eq_top_of_disjoint`：eq_top_of_disjoint [FiniteDimensional K V]
 (s t : Submodule K V) (hdim : finrank K V <= finrank K s + finrank K t) (hdisjo
int : Disjoint s t…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
（共 36 条，此处仅展示前 30 条）
-/
theorem sup_span_singleton_eq_top_iff [Module.Finite K V] {W : Submodule K V} {v : V} (hv : v ∉ W) :
    W ⊔ span K {v} = ⊤ ↔ finrank K (V ⧸ W) = 1 := by
  refine ⟨fun hW ↦ ?_, fun hW ↦ ?_⟩
  · suffices W ⊓ span K {v} = ⊥ by
      have hv₀ : v ≠ 0 := by aesop
      have aux := finrank_sup_add_finrank_inf_eq W (span K {v})
      rw [hW, finrank_span_singleton hv₀, this, finrank_bot, finrank_top,
        ← finrank_quotient_add_finrank W] at aux
      lia
    refine (Submodule.eq_bot_iff _).mpr fun w hw ↦ ?_
    obtain ⟨ht, t, rfl⟩ : w ∈ W ∧ ∃ t : K, t • v = w := by simpa [mem_span_singleton] using hw
    rcases eq_or_ne t 0 with rfl | ht₀; · simp
    rw [Submodule.smul_mem_iff _ ht₀] at ht
    contradiction
  · apply Submodule.eq_top_of_disjoint
    · rw [← W.finrank_quotient_add_finrank, add_comm, add_le_add_iff_left, hW]
      aesop
    · exact Submodule.disjoint_span_singleton_of_notMem hv
/-
**Submodule.finrank_sup_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：finrank_sup_span_singleton [Module.Finite K V] {p : Submodule K V} {v : V}
 (hv : v ∉ p) : finrank K (p ⊔ Submodule.span K {v} : Submodule K V) = finrank K
 p + 1
参数：hv : v ∉ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_left_inj`：∀ {m k n : ℕ}, m + n = k + n ↔ m = k
· 使用定理 `Submodule.finrank_sup_add_finrank_inf_eq`：finrank_sup_add_finrank_inf_eq
 (s t : Submodule K V) [FiniteDimensional K s] [FiniteDimensional K t] : finrank
 K ↑(s ⊔ t) + finrank K ↑(s ⊓ …
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.add_left_cancel_iff`：∀ {m k n : ℕ}, n + m = n + k ↔ m = k
· 使用定理 `finrank_span_singleton`：finrank_span_singleton {v : V} (hv : v != 0) : f
inrank K (K ∙ v) = 1
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Nat.left_eq_add`：∀ {a b : ℕ}, a = a + b ↔ b = 0
· 使用定理 `Submodule.finrank_eq_zero`：Submodule.finrank_eq_zero [StrongRankConditio
n R] {S : Submodule R M} [Module.Finite R S] : finrank R S = 0 ↔ S = ⊥
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Submodule.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem finrank_sup_span_singleton [Module.Finite K V] {p : Submodule K V} {v : V} (hv : v ∉ p) :
    finrank K (p ⊔ Submodule.span K {v} : Submodule K V) = finrank K p + 1 := by
  rw [← Nat.add_left_inj, finrank_sup_add_finrank_inf_eq, add_assoc,
    Nat.add_left_cancel_iff, finrank_span_singleton (by aesop),
    Nat.left_eq_add, Submodule.finrank_eq_zero, eq_bot_iff]
  intro x
  simp only [mem_inf, mem_span_singleton]
  rintro ⟨hx, ⟨a, hx'⟩⟩
  rw [← hx'] at hx
  suffices a = 0 by simp [← hx', this]
  contrapose hv
  simpa [smul_mem_iff p hv] using hx
/-
**Submodule.eq_top_iff_finrank_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：eq_top_iff_finrank_eq [Module.Finite K V] {W : Submodule K V} : W = ⊤ ↔ fi
nrank K W = finrank K V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
· 使用定理 `Submodule.eq_of_le_of_finrank_eq`：eq_of_le_of_finrank_eq {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₁ = finrank 
K S₂) : S₁ = S₂
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem eq_top_iff_finrank_eq [Module.Finite K V] {W : Submodule K V} :
    W = ⊤ ↔ finrank K W = finrank K V := by
  refine ⟨fun h ↦ by rw [h, finrank_top], fun h ↦ ?_⟩
  apply eq_of_le_of_finrank_eq le_top
  rw [finrank_top, h]

end DivisionRing

end Submodule

namespace FiniteDimensional

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

variable [FiniteDimensional K V] [FiniteDimensional K V₂]

/-- Given isomorphic subspaces `p q` of vector spaces `V` and `V₁` respectively,
  `p.quotient` is isomorphic to `q.quotient`. -/
/-
**FiniteDimensional.LinearEquiv.quotEquivOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Fini
teDimensional.LinearEquiv`。
形式化陈述：{K : Type u} →   {V : Type v} →     [inst : DivisionRing K] →       [inst_
1 : AddCommGroup V] →         [inst_2 : _root_.Module K V] →           {V₂ : Typ
e v'} →             [inst_3 : AddCommGroup V₂] →               [inst_4 : _root_.
Module K V₂] →                 [FiniteDimensional K V] →                   [Fini
teDimensional K V₂] →                     {p : Subspace K V} → {q : Subspace K V
₂} → (↥p ≃ₗ[K] ↥q) → (V ≃ₗ[K] V₂) → (V ⧸ p) ≃ₗ[K] V₂ ⧸ q
参数：↥p ≃ₗ[K] ↥q；V ≃ₗ[K] V₂；V ⧸ p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given isomorphic subspaces `p q` of vector spaces `V` and `V₁` respectively,
  `p.quotient` is isomorphic to `q.quotient`.
-/
noncomputable def LinearEquiv.quotEquivOfEquiv {p : Subspace K V} {q : Subspace K V₂}
    (f₁ : p ≃ₗ[K] q) (f₂ : V ≃ₗ[K] V₂) : (V ⧸ p) ≃ₗ[K] V₂ ⧸ q :=
  LinearEquiv.ofFinrankEq _ _
    (by
      rw [← @add_right_cancel_iff _ _ _ (finrank K p), Submodule.finrank_quotient_add_finrank,
        LinearEquiv.finrank_eq f₁, Submodule.finrank_quotient_add_finrank,
        LinearEquiv.finrank_eq f₂])

-- TODO: generalize to the case where one of `p` and `q` is finite-dimensional.
/-- Given the subspaces `p q`, if `p.quotient ≃ₗ[K] q`, then `q.quotient ≃ₗ[K] p` -/
/-
**FiniteDimensional.LinearEquiv.quotEquivOfQuotEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
FiniteDimensional.LinearEquiv`。
形式化陈述：{K : Type u} →   {V : Type v} →     [inst : DivisionRing K] →       [inst_
1 : AddCommGroup V] →         [inst_2 : _root_.Module K V] →           [FiniteDi
mensional K V] → {p q : Subspace K V} → ((V ⧸ p) ≃ₗ[K] ↥q) → (V ⧸ q) ≃ₗ[K] ↥p
参数：(V ⧸ p) ≃ₗ[K] ↥q；V ⧸ q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the subspaces `p q`, if `p.quotient ≃ₗ[K] q`, then `q.quotient ≃ₗ[K] p`
-/
noncomputable def LinearEquiv.quotEquivOfQuotEquiv {p q : Subspace K V} (f : (V ⧸ p) ≃ₗ[K] q) :
    (V ⧸ q) ≃ₗ[K] p :=
  LinearEquiv.ofFinrankEq _ _ <| by
    rw [← add_right_cancel_iff, Submodule.finrank_quotient_add_finrank, ← LinearEquiv.finrank_eq f,
      add_comm, Submodule.finrank_quotient_add_finrank]

end DivisionRing

end FiniteDimensional

namespace LinearMap

open Module

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/-- rank-nullity theorem : the dimensions of the kernel and the range of a linear map add up to
the dimension of the source space. -/
/-
**LinearMap.finrank_range_add_finrank_ker** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：finrank_range_add_finrank_ker [FiniteDimensional K V] (f : V ->ₗ[K] V₂) : 
finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V
参数：f : V ->ₗ[K] V₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用引理 `Submodule.finrank_quotient_add_finrank`：Submodule.finrank_quotient_add_f
inrank [Module.Finite R M] (N : Submodule R M) : finrank R (M ⧸ N) + finrank R N
 = finrank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K

--- 原说明 ---
rank-nullity theorem : the dimensions of the kernel and the range of a linear ma
p add up to
the dimension of the source space.
-/
theorem finrank_range_add_finrank_ker [FiniteDimensional K V] (f : V →ₗ[K] V₂) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V := by
  rw [← f.quotKerEquivRange.finrank_eq]
  exact Submodule.finrank_quotient_add_finrank _
/-
**LinearMap.ker_ne_bot_of_finrank_lt** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：ker_ne_bot_of_finrank_lt [FiniteDimensional K V] [FiniteDimensional K V₂] 
{f : V ->ₗ[K] V₂} (h : finrank K V₂ < finrank K V) : LinearMap.ker f != ⊥
参数：h : finrank K V₂ < finrank K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.finrank_range_add_finrank_ker`：finrank_range_add_finrank_ker [
FiniteDimensional K V] (f : V ->ₗ[K] V₂) : finrank K (LinearMap.range f) + finra
nk K (LinearMap.ker f) = finr…
· 使用定理 `Submodule.finrank_le`：Submodule.finrank_le [Module.Finite R M] (s : Subm
odule R M) : finrank R s <= finrank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Submodule.one_le_finrank_iff`：Submodule.one_le_finrank_iff [StrongRankCo
ndition R] {S : Submodule R M} [Module.Finite R S] : 1 <= finrank R S ↔ S != ⊥
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
-/
lemma ker_ne_bot_of_finrank_lt [FiniteDimensional K V] [FiniteDimensional K V₂] {f : V →ₗ[K] V₂}
    (h : finrank K V₂ < finrank K V) :
    LinearMap.ker f ≠ ⊥ := by
  have h₁ := f.finrank_range_add_finrank_ker
  have h₂ : finrank K (LinearMap.range f) ≤ finrank K V₂ := (LinearMap.range f).finrank_le
  suffices 0 < finrank K (LinearMap.ker f) from Submodule.one_le_finrank_iff.mp this
  lia

end DivisionRing

end LinearMap

open Module

namespace LinearMap

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/-
**LinearMap.injective_iff_surjective_of_finrank_eq_finrank** 是 Mathlib 中的一个定理，位于
命名空间 `LinearMap`。
形式化陈述：injective_iff_surjective_of_finrank_eq_finrank [FiniteDimensional K V] [Fi
niteDimensional K V₂] (H : finrank K V = finrank K V₂) {f : V ->ₗ[K] V₂} : Funct
ion.Injective f ↔ Function.Surjective f
参数：H : finrank K V = finrank K V₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.finrank_range_add_finrank_ker`：finrank_range_add_finrank_ker [
FiniteDimensional K V] (f : V ->ₗ[K] V₂) : finrank K (LinearMap.range f) + finra
nk K (LinearMap.ker f) = finr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Submodule.eq_top_of_finrank_eq`：∀ {K : Type u} {V : Type v} [inst : Divi
sionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [FiniteDime
nsional K V] {S : Su…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `finrank_bot`：finrank_bot : finrank R (⊥ : Submodule R M) = 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.finrank_eq_zero`：Submodule.finrank_eq_zero [StrongRankConditio
n R] {S : Submodule R M} [Module.Finite R S] : finrank R S = 0 ↔ S = ⊥
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
-/
theorem injective_iff_surjective_of_finrank_eq_finrank [FiniteDimensional K V]
    [FiniteDimensional K V₂] (H : finrank K V = finrank K V₂) {f : V →ₗ[K] V₂} :
    Function.Injective f ↔ Function.Surjective f := by
  have := finrank_range_add_finrank_ker f
  rw [← ker_eq_bot, ← range_eq_top]; refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, finrank_bot, add_zero, H] at this
    exact eq_top_of_finrank_eq this
  · rw [h, finrank_top, H] at this
    exact Submodule.finrank_eq_zero.1 (add_right_injective _ this)
/-
**LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank** 是 Mathlib 中的一个定理
，位于命名空间 `LinearMap`。
形式化陈述：ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank [FiniteDimensional K V] 
[FiniteDimensional K V₂] (H : finrank K V = finrank K V₂) {f : V ->ₗ[K] V₂} : Li
nearMap.ker f = ⊥ ↔ LinearMap.range f = ⊤
参数：H : finrank K V = finrank K V₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`：injective_iff_
surjective_of_finrank_eq_finrank [FiniteDimensional K V] [FiniteDimensional K V₂
] (H : finrank K V = finrank K V₂) {f : V ->ₗ[…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank [FiniteDimensional K V]
    [FiniteDimensional K V₂] (H : finrank K V = finrank K V₂) {f : V →ₗ[K] V₂} :
    LinearMap.ker f = ⊥ ↔ LinearMap.range f = ⊤ := by
  rw [range_eq_top, ker_eq_bot, injective_iff_surjective_of_finrank_eq_finrank H]

/-- Given a linear map `f` between two vector spaces with the same dimension, if
`ker f = ⊥` then `linearEquivOfInjective` is the induced isomorphism
between the two vector spaces. -/
/-
**LinearMap.linearEquivOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：linearEquivOfInjective [FiniteDimensional K V] [FiniteDimensional K V₂] (f
 : V ->ₗ[K] V₂) (hf : Injective f) (hdim : finrank K V = finrank K V₂) : V ≃ₗ[K]
 V₂
参数：f : V ->ₗ[K] V₂；hf : Injective f；hdim : finrank K V = finrank K V₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a linear map `f` between two vector spaces with the same dimension, if
`ker f = ⊥` then `linearEquivOfInjective` is the induced isomorphism
between the two vector spaces.
-/
noncomputable def linearEquivOfInjective [FiniteDimensional K V] [FiniteDimensional K V₂]
    (f : V →ₗ[K] V₂) (hf : Injective f) (hdim : finrank K V = finrank K V₂) : V ≃ₗ[K] V₂ :=
  LinearEquiv.ofBijective f
    ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf⟩

@[simp]
/-
**LinearMap.linearEquivOfInjective_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：linearEquivOfInjective_apply [FiniteDimensional K V] [FiniteDimensional K 
V₂] {f : V ->ₗ[K] V₂} (hf : Injective f) (hdim : finrank K V = finrank K V₂) (x 
: V) : f.linearEquivOfInjective hf hdim x = f x
参数：hf : Injective f；hdim : finrank K V = finrank K V₂；x : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linearEquivOfInjective_apply [FiniteDimensional K V] [FiniteDimensional K V₂]
    {f : V →ₗ[K] V₂} (hf : Injective f) (hdim : finrank K V = finrank K V₂) (x : V) :
    f.linearEquivOfInjective hf hdim x = f x :=
  rfl

end LinearMap

namespace Submodule

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/-
**Submodule.finrank_lt_finrank_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：finrank_lt_finrank_of_lt {s t : Submodule K V} [FiniteDimensional K t] (hs
t : s < t) : finrank K s < finrank K t
参数：hst : s < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Submodule.finrank_lt`：finrank_lt [FiniteDimensional K V] {s : Submodule 
K V} (h : s != ⊤) : finrank K s < finrank K V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem finrank_lt_finrank_of_lt {s t : Submodule K V} [FiniteDimensional K t] (hst : s < t) :
    finrank K s < finrank K t :=
  (comapSubtypeEquivOfLe hst.le).finrank_eq.symm.trans_lt <|
    finrank_lt <| by simp [not_le_of_gt hst]
/-
**Submodule.finrank_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：finrank_strictMono [FiniteDimensional K V] : StrictMono fun s : Submodule 
K V => finrank K s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.finrank_lt_finrank_of_lt`：finrank_lt_finrank_of_lt {s t : Subm
odule K V} [FiniteDimensional K t] (hst : s < t) : finrank K s < finrank K t
-/
theorem finrank_strictMono [FiniteDimensional K V] :
    StrictMono fun s : Submodule K V => finrank K s := fun _ _ => finrank_lt_finrank_of_lt
/-
**Submodule.finrank_add_eq_of_isCompl** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：finrank_add_eq_of_isCompl [FiniteDimensional K V] {U W : Submodule K V} (h
 : IsCompl U W) : finrank K U + finrank K W = finrank K V
参数：h : IsCompl U W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.finrank_sup_add_finrank_inf_eq`：finrank_sup_add_finrank_inf_eq
 (s t : Submodule K V) [FiniteDimensional K s] [FiniteDimensional K t] : finrank
 K ↑(s ⊔ t) + finrank K ↑(s ⊓ …
· 使用定理 `Codisjoint.eq_top`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → a ⊔ b = ⊤
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `finrank_bot`：finrank_bot : finrank R (⊥ : Submodule R M) = 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
-/
theorem finrank_add_eq_of_isCompl [FiniteDimensional K V] {U W : Submodule K V} (h : IsCompl U W) :
    finrank K U + finrank K W = finrank K V := by
  rw [← finrank_sup_add_finrank_inf_eq, h.codisjoint.eq_top, h.disjoint.eq_bot, finrank_bot,
    add_zero]
  exact finrank_top _ _

end DivisionRing

end Submodule

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

section Basis
variable {ι : Type*} [Fintype ι]

/-
**LinearIndependent.span_eq_top_of_card_eq_finrank'** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：LinearIndependent.span_eq_top_of_card_eq_finrank' [FiniteDimensional K V] 
{b : ι -> V} (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finra
nk K V) : span K (Set.range b) = ⊤
参数：lin_ind : LinearIndependent K b；card_eq : Fintype.card ι = finrank K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Submodule.finrank_lt`：finrank_lt [FiniteDimensional K V] {s : Submodule 
K V} (h : s != ⊤) : finrank K s < finrank K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finrank_span_eq_card`：finrank_span_eq_card [Nontrivial R] {ι : Type*} [F
intype ι] {b : ι -> M} (hb : LinearIndependent R b) : finrank R (span R (Set.ran
ge b)) = F…
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
-/
theorem LinearIndependent.span_eq_top_of_card_eq_finrank' [FiniteDimensional K V] {b : ι → V}
    (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) :
    span K (Set.range b) = ⊤ := by
  by_contra ne_top
  rw [← finrank_span_eq_card lin_ind] at card_eq
  exact ne_of_lt (Submodule.finrank_lt ne_top) card_eq
/-
**LinearIndependent.span_eq_top_of_card_eq_finrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.span_eq_top_of_card_eq_finrank [Nonempty ι] {b : ι -> V}
 (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) : sp
an K (Set.range b) = ⊤
参数：lin_ind : LinearIndependent K b；card_eq : Fintype.card ι = finrank K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.of_finrank_pos`：of_finrank_pos (h : 0 < finrank K V) :
 FiniteDimensional K V
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `LinearIndependent.span_eq_top_of_card_eq_finrank'`：LinearIndependent.spa
n_eq_top_of_card_eq_finrank' [FiniteDimensional K V] {b : ι -> V} (lin_ind : Lin
earIndependent K b) (card_eq : Fintype.…
-/
theorem LinearIndependent.span_eq_top_of_card_eq_finrank [Nonempty ι]
    {b : ι → V} (lin_ind : LinearIndependent K b)
    (card_eq : Fintype.card ι = finrank K V) : span K (Set.range b) = ⊤ :=
  have : FiniteDimensional K V := .of_finrank_pos <| card_eq ▸ Fintype.card_pos
  lin_ind.span_eq_top_of_card_eq_finrank' card_eq

/-- A linear independent family of `finrank K V` vectors forms a basis. -/
@[simps! repr_apply]
/-
**basisOfLinearIndependentOfCardEqFinrank'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：basisOfLinearIndependentOfCardEqFinrank' [FiniteDimensional K V] (b : ι ->
 V) (hb : LinearIndependent K b) (hι : Fintype.card ι = finrank K V) : Basis ι K
 V
参数：b : ι -> V；hb : LinearIndependent K b；hι : Fintype.card ι = finrank K V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear independent family of `finrank K V` vectors forms a basis.
-/
noncomputable def basisOfLinearIndependentOfCardEqFinrank'
    [FiniteDimensional K V] (b : ι → V) (hb : LinearIndependent K b)
    (hι : Fintype.card ι = finrank K V) : Basis ι K V :=
  .mk hb (hb.span_eq_top_of_card_eq_finrank' hι).ge

@[simp]
/-
**coe_basisOfLinearIndependentOfCardEqFinrank'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coe_basisOfLinearIndependentOfCardEqFinrank' [FiniteDimensional K V] (b : 
ι -> V) (hb hι) : ⇑(basisOfLinearIndependentOfCardEqFinrank' (K
参数：b : ι -> V；hb hι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
-/
lemma coe_basisOfLinearIndependentOfCardEqFinrank' [FiniteDimensional K V] (b : ι → V) (hb hι) :
    ⇑(basisOfLinearIndependentOfCardEqFinrank' (K := K) b hb hι) = b := Basis.coe_mk ..

/-- A linear independent family of `finrank K V` vectors forms a basis. -/
@[simps! repr_apply]
/-
**basisOfLinearIndependentOfCardEqFinrank** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：basisOfLinearIndependentOfCardEqFinrank [Nonempty ι] {b : ι -> V} (lin_ind
 : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) : Basis ι K V
参数：lin_ind : LinearIndependent K b；card_eq : Fintype.card ι = finrank K V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear independent family of `finrank K V` vectors forms a basis.
-/
noncomputable def basisOfLinearIndependentOfCardEqFinrank [Nonempty ι]
    {b : ι → V} (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) :
    Basis ι K V :=
  Basis.mk lin_ind <| (lin_ind.span_eq_top_of_card_eq_finrank card_eq).ge

@[simp]
/-
**coe_basisOfLinearIndependentOfCardEqFinrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_basisOfLinearIndependentOfCardEqFinrank [Nonempty ι] {b : ι -> V} (lin
_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) : ⇑(basis
OfLinearIndependentOfCardEqFinrank lin_ind card_eq) = b
参数：lin_ind : LinearIndependent K b；card_eq : Fintype.card ι = finrank K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
-/
theorem coe_basisOfLinearIndependentOfCardEqFinrank [Nonempty ι]
    {b : ι → V} (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) :
    ⇑(basisOfLinearIndependentOfCardEqFinrank lin_ind card_eq) = b := Basis.coe_mk ..

/-- In a vector space `ι → K`, a linear independent family indexed by `ι` is a basis. -/
/-
**basisOfPiSpaceOfLinearIndependent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：basisOfPiSpaceOfLinearIndependent [Decidable (Nonempty ι)] {b : ι -> (ι ->
 K)} (hb : LinearIndependent K b) : Basis ι K (ι -> K)
参数：Nonempty ι；ι -> K；hb : LinearIndependent K b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a vector space `ι → K`, a linear independent family indexed by `ι` is a basis
.
-/
noncomputable def basisOfPiSpaceOfLinearIndependent
    [Decidable (Nonempty ι)] {b : ι → (ι → K)} (hb : LinearIndependent K b) : Basis ι K (ι → K) :=
  if hι : Nonempty ι then
    basisOfLinearIndependentOfCardEqFinrank hb (Module.finrank_fintype_fun_eq_card K).symm
  else
    have : IsEmpty ι := not_nonempty_iff.mp hι
    Basis.empty _

open scoped Classical in
@[simp]
/-
**coe_basisOfPiSpaceOfLinearIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_basisOfPiSpaceOfLinearIndependent {b : ι -> (ι -> K)} (hb : LinearInde
pendent K b) : ⇑(basisOfPiSpaceOfLinearIndependent hb) = b
参数：ι -> K；hb : LinearIndependent K b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `coe_basisOfLinearIndependentOfCardEqFinrank`：coe_basisOfLinearIndependen
tOfCardEqFinrank [Nonempty ι] {b : ι -> V} (lin_ind : LinearIndependent K b) (ca
rd_eq : Fintype.card ι = finrank …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `basisOfPiSpaceOfLinearIndependent.eq_1`：∀ {K : Type u} [inst : DivisionR
ing K] {ι : Type u_1} [inst_1 : Fintype ι] [inst_2 : Decidable (Nonempty ι)]   {
b : ι → ι → K} (hb : LinearI…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
-/
theorem coe_basisOfPiSpaceOfLinearIndependent
    {b : ι → (ι → K)} (hb : LinearIndependent K b) :
    ⇑(basisOfPiSpaceOfLinearIndependent hb) = b := by
  by_cases hι : Nonempty ι
  · simp [hι, basisOfPiSpaceOfLinearIndependent]
  · rw [basisOfPiSpaceOfLinearIndependent, dif_neg hι]
    ext i
    exact ((not_nonempty_iff.mp hι).false i).elim

/-- A linear independent finset of `finrank K V`-many vectors forms a basis. -/
@[simps! repr_apply]
/-
**finsetBasisOfLinearIndependentOfCardEqFinrank** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finsetBasisOfLinearIndependentOfCardEqFinrank {s : Finset V} (hs : s.Nonem
pty) (lin_ind : LinearIndependent K ((↑) : s -> V)) (card_eq : s.card = finrank 
K V) : Basis s K V
参数：hs : s.Nonempty；lin_ind : LinearIndependent K ((↑) : s -> V)；card_eq : s.card
 = finrank K V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear independent finset of `finrank K V`-many vectors forms a basis.
-/
noncomputable def finsetBasisOfLinearIndependentOfCardEqFinrank {s : Finset V} (hs : s.Nonempty)
    (lin_ind : LinearIndependent K ((↑) : s → V)) (card_eq : s.card = finrank K V) : Basis s K V :=
  haveI : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  basisOfLinearIndependentOfCardEqFinrank lin_ind (_root_.trans (Fintype.card_coe _) card_eq)

@[simp]
/-
**coe_finsetBasisOfLinearIndependentOfCardEqFinrank** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：coe_finsetBasisOfLinearIndependentOfCardEqFinrank {s : Finset V} (hs : s.N
onempty) (lin_ind : LinearIndependent K ((↑) : s -> V)) (card_eq : s.card = finr
ank K V) : ⇑(finsetBasisOfLinearIndependentOfCardEqFinrank hs lin_ind card_eq) =
 ((↑) : s -> V)
参数：hs : s.Nonempty；lin_ind : LinearIndependent K ((↑) : s -> V)；card_eq : s.card
 = finrank K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coe_basisOfLinearIndependentOfCardEqFinrank`：coe_basisOfLinearIndependen
tOfCardEqFinrank [Nonempty ι] {b : ι -> V} (lin_ind : LinearIndependent K b) (ca
rd_eq : Fintype.card ι = finrank …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_finsetBasisOfLinearIndependentOfCardEqFinrank {s : Finset V} (hs : s.Nonempty)
    (lin_ind : LinearIndependent K ((↑) : s → V)) (card_eq : s.card = finrank K V) :
    ⇑(finsetBasisOfLinearIndependentOfCardEqFinrank hs lin_ind card_eq) = ((↑) : s → V) := by
  have : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  simp [finsetBasisOfLinearIndependentOfCardEqFinrank]

/-- A linear independent set of `finrank K V`-many vectors forms a basis. -/
@[simps! repr_apply]
/-
**setBasisOfLinearIndependentOfCardEqFinrank** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：setBasisOfLinearIndependentOfCardEqFinrank {s : Set V} [Nonempty s] [Finty
pe s] (lin_ind : LinearIndependent K ((↑) : s -> V)) (card_eq : s.toFinset.card 
= finrank K V) : Basis s K V
参数：lin_ind : LinearIndependent K ((↑) : s -> V)；card_eq : s.toFinset.card = finr
ank K V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear independent set of `finrank K V`-many vectors forms a basis.
-/
noncomputable def setBasisOfLinearIndependentOfCardEqFinrank {s : Set V} [Nonempty s] [Fintype s]
    (lin_ind : LinearIndependent K ((↑) : s → V)) (card_eq : s.toFinset.card = finrank K V) :
    Basis s K V :=
  basisOfLinearIndependentOfCardEqFinrank lin_ind (_root_.trans s.toFinset_card.symm card_eq)

@[simp]
/-
**coe_setBasisOfLinearIndependentOfCardEqFinrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_setBasisOfLinearIndependentOfCardEqFinrank {s : Set V} [Nonempty s] [F
intype s] (lin_ind : LinearIndependent K ((↑) : s -> V)) (card_eq : s.toFinset.c
ard = finrank K V) : ⇑(setBasisOfLinearIndependentOfCardEqFinrank lin_ind card_e
q) = ((↑) : s -> V)
参数：lin_ind : LinearIndependent K ((↑) : s -> V)；card_eq : s.toFinset.card = finr
ank K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coe_basisOfLinearIndependentOfCardEqFinrank`：coe_basisOfLinearIndependen
tOfCardEqFinrank [Nonempty ι] {b : ι -> V} (lin_ind : LinearIndependent K b) (ca
rd_eq : Fintype.card ι = finrank …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_setBasisOfLinearIndependentOfCardEqFinrank {s : Set V} [Nonempty s] [Fintype s]
    (lin_ind : LinearIndependent K ((↑) : s → V)) (card_eq : s.toFinset.card = finrank K V) :
    ⇑(setBasisOfLinearIndependentOfCardEqFinrank lin_ind card_eq) = ((↑) : s → V) := by
  simp [setBasisOfLinearIndependentOfCardEqFinrank]

end Basis

/-!
We now give characterisations of `finrank K V = 1` and `finrank K V ≤ 1`.
-/

section finrank_eq_one

/-- Any `K`-algebra module that is 1-dimensional over `K` is simple. -/
/-
**is_simple_module_of_finrank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：is_simple_module_of_finrank_eq_one {A} [Semiring A] [Module A V] [SMul K A
] [IsScalarTower K A V] (h : finrank K V = 1) : IsSimpleOrder (Submodule A V)
参数：h : finrank K V = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.nontrivial_of_finrank_eq_succ`：Module.nontrivial_of_finrank_eq_su
cc {n : Nat} (hn : finrank R M = n.succ) : Nontrivial M
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Submodule.instNontrivial`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial M], 
Nontrivial (Su…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.restrictScalars_inj`：restrictScalars_inj {V₁ V₂ : Submodule R 
M} : restrictScalars S V₁ = restrictScalars S V₂ ↔ V₁ = V₂
· 使用定理 `FiniteDimensional.of_finrank_eq_succ`：of_finrank_eq_succ {n : Nat} (hn :
 finrank K V = n.succ) : FiniteDimensional K V
· 使用定理 `Submodule.eq_top_of_finrank_eq`：∀ {K : Type u} {V : Type v} [inst : Divi
sionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [FiniteDime
nsional K V] {S : Su…
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Submodule.finrank_le`：Submodule.finrank_le [Module.Finite R M] (s : Subm
odule R M) : finrank R s <= finrank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `finrank_bot`：finrank_bot : finrank R (⊥ : Submodule R M) = 0
· 使用定理 `Submodule.finrank_strictMono`：finrank_strictMono [FiniteDimensional K V]
 : StrictMono fun s : Submodule K V => finrank K s
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a

--- 原说明 ---
Any `K`-algebra module that is 1-dimensional over `K` is simple.
-/
theorem is_simple_module_of_finrank_eq_one {A} [Semiring A] [Module A V] [SMul K A]
    [IsScalarTower K A V] (h : finrank K V = 1) : IsSimpleOrder (Submodule A V) := by
  have := nontrivial_of_finrank_eq_succ h
  refine ⟨fun S => or_iff_not_imp_left.2 fun hn => ?_⟩
  rw [← restrictScalars_inj K] at hn ⊢
  have : FiniteDimensional _ _ := .of_finrank_eq_succ h
  refine eq_top_of_finrank_eq ((Submodule.finrank_le _).antisymm ?_)
  simpa only [h, finrank_bot] using! Submodule.finrank_strictMono (Ne.bot_lt hn)

end finrank_eq_one

end DivisionRing

section SubalgebraRank

open Module

variable {F E : Type*} [Field F] [Ring E] [Algebra F E]

/-
**Subalgebra.isSimpleOrder_of_finrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.isSimpleOrder_of_finrank (hr : finrank F E = 2) : IsSimpleOrder
 (Subalgebra F E)
参数：hr : finrank F E = 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.nontrivial_of_finrank_pos`：Module.nontrivial_of_finrank_pos (h : 
0 < finrank R M) : Nontrivial M
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subalgebra.bot_eq_top_iff_finrank_eq_one`：bot_eq_top_iff_finrank_eq_one 
[Nontrivial E] [Module.Free F E] : (⊥ : Subalgebra F E) = ⊤ ↔ finrank F E = 1
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `FiniteDimensional.of_finrank_eq_succ`：of_finrank_eq_succ {n : Nat} (hn :
 finrank K V = n.succ) : FiniteDimensional K V
· 使用定理 `Submodule.finrank_le`：Submodule.finrank_le [Module.Finite R M] (s : Subm
odule R M) : finrank R s <= finrank R M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.finrank_pos_iff`：Module.finrank_pos_iff [IsDomain R] [IsTorsionFr
ee R M] : 0 < finrank R M ↔ Nontrivial M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.toSubmodule_eq_top`：toSubmodule_eq_top {S : Subalgebra R A} : Su
balgebra.toSubmodule S = ⊤ ↔ S = ⊤
· 使用定理 `Submodule.eq_top_of_finrank_eq`：∀ {K : Type u} {V : Type v} [inst : Divi
sionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [FiniteDime
nsional K V] {S : Su…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Mathlib.Tactic.IntervalCases.of_le_right`：of_le_right [LE α] (h : (a : α
) <= b) (eq : b = b') : a <= b'
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 35 条，此处仅展示前 30 条）
-/
theorem Subalgebra.isSimpleOrder_of_finrank (hr : finrank F E = 2) :
    IsSimpleOrder (Subalgebra F E) :=
  let i := nontrivial_of_finrank_pos (zero_lt_two.trans_eq hr.symm)
  { toNontrivial :=
      ⟨⟨⊥, ⊤, fun h => by cases hr.symm.trans (Subalgebra.bot_eq_top_iff_finrank_eq_one.1 h)⟩⟩
    eq_bot_or_eq_top := by
      intro S
      have : FiniteDimensional F E := .of_finrank_eq_succ hr
      have : FiniteDimensional F S :=
        FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule S)
      have : finrank F S ≤ 2 := hr ▸ S.toSubmodule.finrank_le
      have : 0 < finrank F S := finrank_pos_iff.mpr inferInstance
      interval_cases h : finrank F { x // x ∈ S }
      · left
        exact Subalgebra.eq_bot_of_finrank_one h
      · right
        rw [← hr] at h
        rw [← Algebra.toSubmodule_eq_top]
        exact eq_top_of_finrank_eq h }

end SubalgebraRank

namespace Module

namespace End

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-
**Module.End.exists_ker_pow_eq_ker_pow_succ** 是 Mathlib 中的一个定理，位于命名空间 `Module.En
d`。
形式化陈述：exists_ker_pow_eq_ker_pow_succ [FiniteDimensional K V] (f : End K V) : exi
sts k : Nat, k <= finrank K V ∧ LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.suc
c)
参数：f : End K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `LinearMap.ker_le_ker_comp`：ker_le_ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ 
->ₛₗ[τ₂₃] M₃) : ker f <= ker (g.comp f : M ->ₛₗ[τ₁₃] M₃)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Nat.le_of_succ_le_succ`：∀ {n m : ℕ}, n.succ ≤ m.succ → n ≤ m
· 使用定理 `Submodule.finrank_lt_finrank_of_lt`：finrank_lt_finrank_of_lt {s t : Subm
odule K V} [FiniteDimensional K t] (hst : s < t) : finrank K s < finrank K t
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `Nat.le_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n ≤ m
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.finrank_le`：Submodule.finrank_le [Module.Finite R M] (s : Subm
odule R M) : finrank R s <= finrank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Nat.not_succ_le_self`：∀ (n : ℕ), ¬n.succ ≤ n
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
-/
theorem exists_ker_pow_eq_ker_pow_succ [FiniteDimensional K V] (f : End K V) :
    ∃ k : ℕ, k ≤ finrank K V ∧ LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.succ) := by
  by_contra h_contra
  simp_rw [not_exists, not_and] at h_contra
  have h_le_ker_pow : ∀ n : ℕ, n ≤ (finrank K V).succ →
      n ≤ finrank K (LinearMap.ker (f ^ n)) := by
    intro n hn
    induction n with
    | zero => exact zero_le
    | succ n ih =>
      have h_ker_lt_ker : LinearMap.ker (f ^ n) < LinearMap.ker (f ^ n.succ) := by
        refine lt_of_le_of_ne ?_ (h_contra n (Nat.le_of_succ_le_succ hn))
        rw [pow_succ']
        apply LinearMap.ker_le_ker_comp
      have h_finrank_lt_finrank :
          finrank K (LinearMap.ker (f ^ n)) < finrank K (LinearMap.ker (f ^ n.succ)) := by
        apply Submodule.finrank_lt_finrank_of_lt h_ker_lt_ker
      calc
        n.succ ≤ (finrank K ↑(LinearMap.ker (f ^ n))).succ :=
          Nat.succ_le_succ (ih (Nat.le_of_succ_le hn))
        _ ≤ finrank K ↑(LinearMap.ker (f ^ n.succ)) := Nat.succ_le_of_lt h_finrank_lt_finrank
  have h_any_n_lt : ∀ n, n ≤ (finrank K V).succ → n ≤ finrank K V := fun n hn =>
    (h_le_ker_pow n hn).trans (Submodule.finrank_le _)
  exact Nat.not_succ_le_self _ (h_any_n_lt (finrank K V).succ (finrank K V).succ.le_refl)
/-
**Module.End.ker_pow_eq_ker_pow_finrank_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Module.
End`。
形式化陈述：ker_pow_eq_ker_pow_finrank_of_le [FiniteDimensional K V] {f : End K V} {m 
: Nat} (hm : finrank K V <= m) : LinearMap.ker (f ^ m) = LinearMap.ker (f ^ finr
ank K V)
参数：hm : finrank K V <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.exists_ker_pow_eq_ker_pow_succ`：exists_ker_pow_eq_ker_pow_suc
c [FiniteDimensional K V] (f : End K V) : exists k : Nat, k <= finrank K V ∧ Lin
earMap.ker (f ^ k) = LinearMap.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Module.End.ker_pow_constant`：∀ {K : Type u} {V : Type v} [inst : Divisio
nRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   {f : Module.En
d K V} {k : ℕ},  …
-/
theorem ker_pow_eq_ker_pow_finrank_of_le [FiniteDimensional K V] {f : End K V} {m : ℕ}
    (hm : finrank K V ≤ m) : LinearMap.ker (f ^ m) = LinearMap.ker (f ^ finrank K V) := by
  obtain ⟨k, h_k_le, hk⟩ :
    ∃ k, k ≤ finrank K V ∧ LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.succ) :=
    exists_ker_pow_eq_ker_pow_succ f
  calc
    LinearMap.ker (f ^ m) = LinearMap.ker (f ^ (k + (m - k))) := by
      rw [add_tsub_cancel_of_le (h_k_le.trans hm)]
    _ = LinearMap.ker (f ^ k) := by rw [ker_pow_constant hk _]
    _ = LinearMap.ker (f ^ (k + (finrank K V - k))) := ker_pow_constant hk (finrank K V - k)
    _ = LinearMap.ker (f ^ finrank K V) := by rw [add_tsub_cancel_of_le h_k_le]
/-
**Module.End.ker_pow_le_ker_pow_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：ker_pow_le_ker_pow_finrank [FiniteDimensional K V] (f : End K V) (m : Nat)
 : LinearMap.ker (f ^ m) <= LinearMap.ker (f ^ finrank K V)
参数：f : End K V；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `LinearMap.ker_le_ker_comp`：ker_le_ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ 
->ₛₗ[τ₂₃] M₃) : ker f <= ker (g.comp f : M ->ₛₗ[τ₁₃] M₃)
· 使用定理 `Module.End.ker_pow_eq_ker_pow_finrank_of_le`：ker_pow_eq_ker_pow_finrank_
of_le [FiniteDimensional K V] {f : End K V} {m : Nat} (hm : finrank K V <= m) : 
LinearMap.ker (f ^ m) = LinearMap…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem ker_pow_le_ker_pow_finrank [FiniteDimensional K V] (f : End K V) (m : ℕ) :
    LinearMap.ker (f ^ m) ≤ LinearMap.ker (f ^ finrank K V) := by
  by_cases! h_cases : m < finrank K V
  · rw [← add_tsub_cancel_of_le h_cases.le, add_comm, pow_add]
    apply LinearMap.ker_le_ker_comp
  · rw [ker_pow_eq_ker_pow_finrank_of_le h_cases]

end End

end Module

namespace Submodule

section DivisionRing

variable {W : Type v'} [DivisionRing K] [AddCommGroup W] [AddCommGroup V] [Module K V] [Module K W]
  {f : V →ₗ[K] W}

/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : Submodule K W) [FiniteDimensional K p] [FiniteDimensional K f.ker] :
    FiniteDimensional K (comap f p) := by
  grw [FiniteDimensional, ← rank_lt_aleph0_iff, ← lift_lt, f.lift_rank_comap_le p, lift_aleph0]
  apply add_lt_aleph0 <;> rwa [lift_lt_aleph0, rank_lt_aleph0_iff]
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : Submodule K V) [FiniteDimensional K (V ⧸ p)] [FiniteDimensional K (W ⧸ f.range)] :
    FiniteDimensional K (W ⧸ map f p) := by
  grw [FiniteDimensional, ← rank_lt_aleph0_iff, ← lift_lt, f.lift_rank_quot_map_le p, lift_aleph0]
  apply add_lt_aleph0 <;> rwa [lift_lt_aleph0, rank_lt_aleph0_iff]

end DivisionRing

end Submodule

