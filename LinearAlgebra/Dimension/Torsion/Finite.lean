/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Results relating rank and torsion.

-/

public section

/-- A torsion module has rank zero. -/
/-
**Module.IsTorsion.rank_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.IsTorsion.rank_eq_zero {R M : Type*} [Semiring R] [AddCommMonoid M]
 [Module R M] [Nontrivial R] (h : IsTorsion R M) : Module.rank R M = 0
参数：h : IsTorsion R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.one_le_rank_iff`：Module.one_le_rank_iff : 1 <= Module.rank R M ↔ 
exists f : R ->ₗ[R] M, Injective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.one_le_iff_ne_zero`：∀ {c : Cardinal.{u_1}}, 1 ≤ c ↔ c ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
A torsion module has rank zero.
-/
theorem Module.IsTorsion.rank_eq_zero {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Nontrivial R] (h : IsTorsion R M) : Module.rank R M = 0 := by
  by_contra! h'
  obtain ⟨f, hf⟩ := by rwa [← Cardinal.one_le_iff_ne_zero, one_le_rank_iff] at h'
  simpa [← map_smul, zero_notMem_nonZeroDivisors, hf] using @h (f 1)
/-
**Module.IsTorsion.finrank_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.IsTorsion.finrank_eq_zero {R M : Type*} [Semiring R] [AddCommMonoid
 M] [Module R M] [Nontrivial R] (h : IsTorsion R M) : finrank R M = 0
参数：h : IsTorsion R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_eq_zero_of_rank_eq_zero`：Module.finrank_eq_zero_of_rank_e
q_zero (h : Module.rank R M = 0) : finrank R M = 0
· 使用定理 `Module.IsTorsion.rank_eq_zero`：Module.IsTorsion.rank_eq_zero {R M : Type
*} [Semiring R] [AddCommMonoid M] [Module R M] [Nontrivial R] (h : IsTorsion R M
) : Module.rank R M…
-/
theorem Module.IsTorsion.finrank_eq_zero {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Nontrivial R] (h : IsTorsion R M) : finrank R M = 0 :=
  finrank_eq_zero_of_rank_eq_zero h.rank_eq_zero

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
/-
**Module.rank_eq_zero_iff_isTorsion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.rank_eq_zero_iff_isTorsion : Module.rank R M = 0 ↔ Module.IsTorsion
 R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Module.rank_eq_zero_iff_isTorsion : Module.rank R M = 0 ↔ Module.IsTorsion R M := by
  simp [IsTorsion, rank_eq_zero_iff]

@[deprecated (since := "2026-07-14")] alias
rank_eq_zero_iff_isTorsion := Module.rank_eq_zero_iff_isTorsion

/-- The `StrongRankCondition` is automatic. See `commRing_strongRankCondition`. -/
/-
**Module.finrank_eq_zero_iff_isTorsion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_eq_zero_iff_isTorsion [StrongRankCondition R] [Module.Finit
e R M] : finrank R M = 0 ↔ Module.IsTorsion R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.rank_eq_zero_iff_isTorsion`：Module.rank_eq_zero_iff_isTorsion : M
odule.rank R M = 0 ↔ Module.IsTorsion R M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The `StrongRankCondition` is automatic. See `commRing_strongRankCondition`.
-/
theorem Module.finrank_eq_zero_iff_isTorsion [StrongRankCondition R] [Module.Finite R M] :
    finrank R M = 0 ↔ Module.IsTorsion R M := by
  simp [← rank_eq_zero_iff_isTorsion (R := R), ← finrank_eq_rank]
