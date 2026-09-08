/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.SetTheory.Cardinal.Finsupp

/-!
# Rank of free modules

## Main result
- `Module.nonempty_linearEquiv_iff_lift_rank_eq`:
  Two free modules are isomorphic iff they have the same dimension.
- `Module.finBasis`:
  An arbitrary basis of a finite free module indexed by `Fin n` given `finrank R M = n`.

-/

@[expose] public section


noncomputable section

universe u v v' w

open Cardinal Basis Submodule Function Set Module

section Tower

variable (F : Type u) (K : Type v) (A : Type w)
variable [Semiring F] [Semiring K] [AddCommMonoid A]
variable [Module F K] [Module K A] [Module F A] [IsScalarTower F K A]
variable [StrongRankCondition F] [StrongRankCondition K] [Module.Free F K] [Module.Free K A]

/-- Tower law: if `A` is a `K`-module and `K` is an extension of `F` then
$\operatorname{rank}_F(A) = \operatorname{rank}_F(K) * \operatorname{rank}_K(A)$.

The universe polymorphic version of `rank_mul_rank` below. -/
/-
**lift_rank_mul_lift_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_rank_mul_lift_rank : Cardinal.lift.{w} (Module.rank F K) * Cardinal.l
ift.{v} (Module.rank K A) = Cardinal.lift.{v} (Module.rank F A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Module.Basis.mk_eq_rank`：mk_eq_rank (v : Basis ι R M) : Cardinal.lift.{v
} #ι = Cardinal.lift.{w} (Module.rank R M)
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.mk_prod`：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v
, u} #α * lift.{u, v} #β
· 使用定理 `Cardinal.lift_mul`：lift_mul (a b : Cardinal.{u}) : lift.{v} (a * b) = li
ft.{v} a * lift.{v} b
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a

--- 原说明 ---
Tower law: if `A` is a `K`-module and `K` is an extension of `F` then
$\operatorname{rank}_F(A) = \operatorname{rank}_F(K) * \operatorname{rank}_K(A)$
.

The universe polymorphic version of `rank_mul_rank` below.
-/
theorem lift_rank_mul_lift_rank :
    Cardinal.lift.{w} (Module.rank F K) * Cardinal.lift.{v} (Module.rank K A) =
      Cardinal.lift.{v} (Module.rank F A) := by
  let b := Module.Free.chooseBasis F K
  let c := Module.Free.chooseBasis K A
  rw [← (Module.rank F K).lift_id, ← b.mk_eq_rank, ← (Module.rank K A).lift_id, ← c.mk_eq_rank,
    ← lift_umax.{w, v}, ← (b.smulTower c).mk_eq_rank, mk_prod, lift_mul, lift_lift, lift_lift,
    lift_lift, lift_lift, lift_umax.{v, w}]

/-- Tower law: if `A` is a `K`-module and `K` is an extension of `F` then
$\operatorname{rank}_F(A) = \operatorname{rank}_F(K) * \operatorname{rank}_K(A)$.

This is a simpler version of `lift_rank_mul_lift_rank` with `K` and `A` in the same universe. -/
@[stacks 09G9]
/-
**rank_mul_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_mul_rank (A : Type v) [AddCommMonoid A] [Module K A] [Module F A] [Is
ScalarTower F K A] [Module.Free K A] : Module.rank F K * Module.rank K A = Modul
e.rank F A
参数：A : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `lift_rank_mul_lift_rank`：lift_rank_mul_lift_rank : Cardinal.lift.{w} (Mo
dule.rank F K) * Cardinal.lift.{v} (Module.rank K A) = Cardinal.lift.{v} (Module
.rank F A)

--- 原说明 ---
Tower law: if `A` is a `K`-module and `K` is an extension of `F` then
$\operatorname{rank}_F(A) = \operatorname{rank}_F(K) * \operatorname{rank}_K(A)$
.

This is a simpler version of `lift_rank_mul_lift_rank` with `K` and `A` in the s
ame universe.
-/
theorem rank_mul_rank (A : Type v) [AddCommMonoid A]
    [Module K A] [Module F A] [IsScalarTower F K A] [Module.Free K A] :
    Module.rank F K * Module.rank K A = Module.rank F A := by
  convert! lift_rank_mul_lift_rank F K A <;> rw [lift_id]

/-- Tower law: if `A` is a `K`-module and `K` is an extension of `F` then
$\operatorname{rank}_F(A) = \operatorname{rank}_F(K) * \operatorname{rank}_K(A)$.

See `Module.finrank_mul_finrank'` for a variant over a tower of domains that assumes the rings are
module-finite rather than the modules being free. -/
/-
**Module.finrank_mul_finrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_mul_finrank : finrank F K * finrank K A = finrank F A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `Cardinal.toNat_mul`：toNat_mul (x y : Cardinal) : toNat (x * y) = toNat x
 * toNat y
· 使用定理 `lift_rank_mul_lift_rank`：lift_rank_mul_lift_rank : Cardinal.lift.{w} (Mo
dule.rank F K) * Cardinal.lift.{v} (Module.rank K A) = Cardinal.lift.{v} (Module
.rank F A)

--- 原说明 ---
Tower law: if `A` is a `K`-module and `K` is an extension of `F` then
$\operatorname{rank}_F(A) = \operatorname{rank}_F(K) * \operatorname{rank}_K(A)$
.

See `Module.finrank_mul_finrank'` for a variant over a tower of domains that ass
umes the rings are
module-finite rather than the modules being free.
-/
theorem Module.finrank_mul_finrank : finrank F K * finrank K A = finrank F A := by
  simp_rw [finrank]
  rw [← toNat_lift.{w} (Module.rank F K), ← toNat_lift.{v} (Module.rank K A), ← toNat_mul,
    lift_rank_mul_lift_rank, toNat_lift]
/-
**Module.finrank_dvd_finrank_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_dvd_finrank_left : Module.finrank K A ∣ Module.finrank F A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.intro_left`：Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
-/
theorem Module.finrank_dvd_finrank_left :
    Module.finrank K A ∣ Module.finrank F A :=
  Dvd.intro_left (finrank F K) (finrank_mul_finrank ..)
/-
**Module.finrank_dvd_finrank_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_dvd_finrank_right : Module.finrank F K ∣ Module.finrank F A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
-/
theorem Module.finrank_dvd_finrank_right :
    Module.finrank F K ∣ Module.finrank F A :=
  Dvd.intro (finrank K A) (finrank_mul_finrank ..)
/-
**Module.finrank_div_finrank_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_div_finrank_cancel_right (h : Module.finrank K A != 0) : Mo
dule.finrank F A / Module.finrank K A = Module.finrank F K
参数：h : Module.finrank K A != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.div_eq_of_eq_mul_left`：∀ {n m k : ℕ}, 0 < n → m = k * n → m / n = k
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
-/
theorem Module.finrank_div_finrank_cancel_right (h : Module.finrank K A ≠ 0) :
    Module.finrank F A / Module.finrank K A = Module.finrank F K :=
  Nat.div_eq_of_eq_mul_left h.bot_lt (finrank_mul_finrank ..).symm
/-
**Module.finrank_div_finrank_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_div_finrank_cancel_left (h : Module.finrank F K != 0) : Mod
ule.finrank F A / Module.finrank F K = Module.finrank K A
参数：h : Module.finrank F K != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.div_eq_of_eq_mul_right`：∀ {n m k : ℕ}, 0 < n → m = n * k → m / n = k
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
-/
theorem Module.finrank_div_finrank_cancel_left (h : Module.finrank F K ≠ 0) :
    Module.finrank F A / Module.finrank F K = Module.finrank K A :=
  Nat.div_eq_of_eq_mul_right h.bot_lt (finrank_mul_finrank ..).symm
/-
**Module.finrank_div_finrank_cancel_right_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：Module.finrank_div_finrank_cancel_right_of_nontrivial [Nontrivial A] [Modu
le.Finite K A] : Module.finrank F A / Module.finrank K A = Module.finrank F K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_div_finrank_cancel_right`：Module.finrank_div_finrank_canc
el_right (h : Module.finrank K A != 0) : Module.finrank F A / Module.finrank K A
 = Module.finrank F K
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.finrank_pos_iff_of_free`：finrank_pos_iff_of_free [Module.Free R M
] [Module.Finite R M] : 0 < Module.finrank R M ↔ Nontrivial M
-/
theorem Module.finrank_div_finrank_cancel_right_of_nontrivial [Nontrivial A] [Module.Finite K A] :
    Module.finrank F A / Module.finrank K A = Module.finrank F K :=
  finrank_div_finrank_cancel_right F K A ((finrank_pos_iff_of_free ..).mpr ‹_›).ne'
/-
**Module.finrank_div_finrank_cancel_left_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Module.finrank_div_finrank_cancel_left_of_nontrivial [Nontrivial K] [Modul
e.Finite F K] : Module.finrank F A / Module.finrank F K = Module.finrank K A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_div_finrank_cancel_left`：Module.finrank_div_finrank_cance
l_left (h : Module.finrank F K != 0) : Module.finrank F A / Module.finrank F K =
 Module.finrank K A
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.finrank_pos_iff_of_free`：finrank_pos_iff_of_free [Module.Free R M
] [Module.Finite R M] : 0 < Module.finrank R M ↔ Nontrivial M
-/
theorem Module.finrank_div_finrank_cancel_left_of_nontrivial [Nontrivial K] [Module.Finite F K] :
    Module.finrank F A / Module.finrank F K = Module.finrank K A :=
  finrank_div_finrank_cancel_left F K A ((finrank_pos_iff_of_free ..).mpr ‹_›).ne'

end Tower

variable {R : Type u} {S : Type*} {M M₁ : Type v} {M' : Type v'}
variable [Semiring R]
variable [AddCommMonoid M] [Module R M] [Module.Free R M]
variable [AddCommMonoid M'] [Module R M'] [Module.Free R M']
variable [AddCommMonoid M₁] [Module R M₁] [Module.Free R M₁]

namespace Module.Free

variable {N : Type v} [AddCommMonoid N] [Module R N]
variable {N' : Type v'} [AddCommMonoid N'] [Module R N']

/-
**Module.Free.exists_linearMap_injective_of_linearIndependent_of_lift_rank_le** 
是 Mathlib 中的一个定理，位于命名空间 `Module.Free`。
形式化陈述：exists_linearMap_injective_of_linearIndependent_of_lift_rank_le {ι : Type 
w} {v : ι -> N'} (hv : LinearIndependent R v) (cnd : Cardinal.lift.{w} (Module.r
ank R M) <= Cardinal.lift.{v} #ι) : exists f : M ->ₗ[R] N', Function.Injective f
参数：hv : LinearIndependent R v；cnd : Cardinal.lift.{w} (Module.rank R M) <= Cardi
nal.lift.{v} #ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Module.nontrivial`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZer
o R] [Nontrivial M] [inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
· 使用定理 `Module.Free.exists_set`：∀ (R : Type u) (M : Type v) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Free R M], ∃ S
, Nonempty (…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `LinearIndependent.cardinal_le_rank`：cardinal_le_rank {ι : Type v} {v : ι
 -> M} (hv : LinearIndependent R v) : #ι <= Module.rank R M
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
· 使用定理 `Module.Basis.injective_constr_of_linearIndependent`：injective_constr_of_
linearIndependent [Semiring R₂] [Module R₂ M'] [SMulCommClass R R₂ M'] {v : ι ->
 M'} (hv : LinearIndependent R v) : Inje…
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
-/
theorem exists_linearMap_injective_of_linearIndependent_of_lift_rank_le
    {ι : Type w} {v : ι → N'} (hv : LinearIndependent R v)
    (cnd : Cardinal.lift.{w} (Module.rank R M) ≤ Cardinal.lift.{v} #ι) :
    ∃ f : M →ₗ[R] N', Function.Injective f := by
  nontriviality M
  have := Module.nontrivial R M
  rcases Module.Free.exists_set R M with ⟨_, ⟨B⟩⟩
  replace cnd := (Cardinal.lift_le.2 B.linearIndependent.cardinal_le_rank).trans cnd
  rw [Cardinal.lift_mk_le'] at cnd
  rcases cnd with ⟨i, hi⟩
  refine ⟨B.constr ℕ (v ∘ i), B.injective_constr_of_linearIndependent (hv.comp _ hi)⟩
/-
**Module.Free.exists_linearMap_injective_of_linearIndependent_of_rank_le** 是 Mat
hlib 中的一个定理，位于命名空间 `Module.Free`。
形式化陈述：exists_linearMap_injective_of_linearIndependent_of_rank_le {ι : Type v} {v
 : ι -> N} (hv : LinearIndependent R v) (cnd : Module.rank R M <= #ι) : exists f
 : M ->ₗ[R] N, Function.Injective f
参数：hv : LinearIndependent R v；cnd : Module.rank R M <= #ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_linearMap_injective_of_linearIndependent_of_lift_rank
_le`：exists_linearMap_injective_of_linearIndependent_of_lift_rank_le {ι : Type w
} {v : ι -> N'} (hv : LinearIndependent R v) (cnd : Cardinal.lift…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem exists_linearMap_injective_of_linearIndependent_of_rank_le
    {ι : Type v} {v : ι → N} (hv : LinearIndependent R v) (cnd : Module.rank R M ≤ #ι) :
    ∃ f : M →ₗ[R] N, Function.Injective f :=
  exists_linearMap_injective_of_linearIndependent_of_lift_rank_le hv (by simpa using cnd)
/-
**Module.Free.exists_linearMap_injective_of_lift_rank_lt** 是 Mathlib 中的一个定理，位于命名
空间 `Module.Free`。
形式化陈述：exists_linearMap_injective_of_lift_rank_lt (cnd : Cardinal.lift.{v'} (Modu
le.rank R M) < Cardinal.lift.{v} (Module.rank R N')) : exists f : M ->ₗ[R] N', F
unction.Injective f
参数：cnd : Cardinal.lift.{v'} (Module.rank R M) < Cardinal.lift.{v} (Module.rank R
 N')。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.exists_set_linearIndependent_of_lt_lift_rank`：exists_set_linearIn
dependent_of_lt_lift_rank {c : Cardinal.{w}} (h : Cardinal.lift.{v} c < Cardinal
.lift.{w} (Module.rank R M)) : exists s :…
· 使用定理 `Module.Free.exists_linearMap_injective_of_linearIndependent_of_lift_rank
_le`：exists_linearMap_injective_of_linearIndependent_of_lift_rank_le {ι : Type w
} {v : ι -> N'} (hv : LinearIndependent R v) (cnd : Cardinal.lift…
· 使用定理 `LinearIndepOn.linearIndependent`：LinearIndepOn.linearIndependent {s : Se
t ι} (h : LinearIndepOn R v s) : LinearIndependent R (fun x : s => v x)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_linearMap_injective_of_lift_rank_lt
    (cnd : Cardinal.lift.{v'} (Module.rank R M) < Cardinal.lift.{v} (Module.rank R N')) :
    ∃ f : M →ₗ[R] N', Function.Injective f := by
  rcases exists_set_linearIndependent_of_lt_lift_rank cnd with ⟨s, hs, hs₂⟩
  exact exists_linearMap_injective_of_linearIndependent_of_lift_rank_le
    hs₂.linearIndependent hs.symm.le
/-
**Module.Free.exists_linearMap_injective_of_rank_lt** 是 Mathlib 中的一个定理，位于命名空间 `M
odule.Free`。
形式化陈述：exists_linearMap_injective_of_rank_lt (cnd : Module.rank R M < Module.rank
 R N) : exists f : M ->ₗ[R] N, Function.Injective f
参数：cnd : Module.rank R M < Module.rank R N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_linearMap_injective_of_lift_rank_lt`：exists_linearMap
_injective_of_lift_rank_lt (cnd : Cardinal.lift.{v'} (Module.rank R M) < Cardina
l.lift.{v} (Module.rank R N')) : exists f : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem exists_linearMap_injective_of_rank_lt (cnd : Module.rank R M < Module.rank R N) :
    ∃ f : M →ₗ[R] N, Function.Injective f :=
  exists_linearMap_injective_of_lift_rank_lt (by simpa using cnd)

end Module.Free

section StrongRankCondition

variable [StrongRankCondition R]

namespace Module.Free

variable (R M)

/-- The rank of a free module `M` over `R` is the cardinality of `ChooseBasisIndex R M`. -/
/-
**Module.Free.rank_eq_card_chooseBasisIndex** 是 Mathlib 中的一个定理，位于命名空间 `Module.Fr
ee`。
形式化陈述：rank_eq_card_chooseBasisIndex : Module.rank R M = #(ChooseBasisIndex R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M

--- 原说明 ---
The rank of a free module `M` over `R` is the cardinality of `ChooseBasisIndex R
 M`.
-/
theorem rank_eq_card_chooseBasisIndex : Module.rank R M = #(ChooseBasisIndex R M) :=
  (chooseBasis R M).mk_eq_rank''.symm

/-- The `finrank` of a free module `M` over `R` is the cardinality of `ChooseBasisIndex R M`. -/
/-
**Module.Free._root_.Module.finrank_eq_card_chooseBasisIndex** 是 Mathlib 中的一个定理，
位于命名空间 `Module.Free`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `finrank` of a free module `M` over `R` is the cardinality of `ChooseBasisIn
dex R M`.
-/
theorem _root_.Module.finrank_eq_card_chooseBasisIndex [Module.Finite R M] :
    finrank R M = Fintype.card (ChooseBasisIndex R M) := by
  simp [finrank, rank_eq_card_chooseBasisIndex]

/-- The rank of a free module `M` over an infinite scalar ring `R` is the cardinality of `M`
whenever `#R < #M`. -/
/-
**Module.Free.rank_eq_mk_of_infinite_lt** 是 Mathlib 中的一个引理，位于命名空间 `Module.Free`。
形式化陈述：rank_eq_mk_of_infinite_lt [Infinite R] (h_lt : lift.{v} #R < lift.{u} #M) 
: Module.rank R M = #M
参数：h_lt : lift.{v} #R < lift.{u} #M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.infinite_iff`：infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ <= #α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `max_eq_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b =
 c ↔ a = c ∧ b ≤ a ∨ b = c ∧ a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_finsupp_lift_of_infinite'`：mk_finsupp_lift_of_infinite' (α :
 Type u) (β : Type v) [Nonempty α] [Zero β] [Infinite β] : #(α ->₀ β) = max (lif
t.{v} #α) (lift.{u} #β)
· 使用定理 `Module.Free.instNonemptyChooseBasisIndexOfNontrivial`：∀ (R : Type u) (M 
: Type v) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module
 R M]   [inst_3 : Module.Free R M] [Nontri…
· 使用定理 `Infinite.instNontrivial`：∀ (α : Type u_4) [Infinite α], Nontrivial α
· 使用定理 `Cardinal.lift_max`：lift_max {a b : Cardinal} : lift.{u, v} (max a b) = m
ax (lift.{u, v} a) (lift.{u, v} b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `not_and_of_not_left`：∀ {a : Prop} (b : Prop), ¬a → ¬(a ∧ b)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}

--- 原说明 ---
The rank of a free module `M` over an infinite scalar ring `R` is the cardinalit
y of `M`
whenever `#R < #M`.
-/
lemma rank_eq_mk_of_infinite_lt [Infinite R] (h_lt : lift.{v} #R < lift.{u} #M) :
    Module.rank R M = #M := by
  have : Infinite M := infinite_iff.mpr <| lift_le.mp <| le_trans (by simp) h_lt.le
  have h : lift #M = lift #(ChooseBasisIndex R M →₀ R) := lift_mk_eq'.mpr ⟨(chooseBasis R M).repr⟩
  simp only [mk_finsupp_lift_of_infinite', ← rank_eq_card_chooseBasisIndex, lift_max,
    lift_lift] at h
  refine lift_inj.mp ((max_eq_iff.mp h.symm).resolve_right <| not_and_of_not_left _ ?_).left
  exact (lift_umax.{v, u}.symm ▸ h_lt).ne

end Module.Free

open Module.Free

open Cardinal

/-
**lift_rank_le_iff_exists_linearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_rank_le_iff_exists_linearMap : Cardinal.lift.{v'} (Module.rank R M) <
= Cardinal.lift.{v} (Module.rank R M') ↔ exists f : M ->ₗ[R] M', Function.Inject
ive f where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_set`：∀ (R : Type u) (M : Type v) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Free R M], ∃ S
, Nonempty (…
· 使用定理 `Module.Free.exists_linearMap_injective_of_linearIndependent_of_lift_rank
_le`：exists_linearMap_injective_of_linearIndependent_of_lift_rank_le {ι : Type w
} {v : ι -> N'} (hv : LinearIndependent R v) (cnd : Cardinal.lift…
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `LinearMap.lift_rank_le_of_injective`：LinearMap.lift_rank_le_of_injective
 (f : M ->ₗ[R] M') (i : Injective f) : Cardinal.lift.{v'} (Module.rank R M) <= C
ardinal.lift.{v} (Module.…
-/
theorem lift_rank_le_iff_exists_linearMap :
    Cardinal.lift.{v'} (Module.rank R M) ≤ Cardinal.lift.{v} (Module.rank R M') ↔
    ∃ f : M →ₗ[R] M', Function.Injective f where
  mp h := by
    rcases Module.Free.exists_set R M' with ⟨_, ⟨B⟩⟩
    exact exists_linearMap_injective_of_linearIndependent_of_lift_rank_le B.linearIndependent
      (B.mk_eq_rank''.symm ▸ h)
  mpr := fun ⟨f, hf⟩ ↦ LinearMap.lift_rank_le_of_injective f hf
/-
**rank_le_iff_exists_linearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_le_iff_exists_linearMap : Module.rank R M <= Module.rank R M₁ ↔ exist
s f : M ->ₗ[R] M₁, Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rank_le_iff_exists_linearMap :
    Module.rank R M ≤ Module.rank R M₁ ↔ ∃ f : M →ₗ[R] M₁, Function.Injective f := by
  simp [← lift_rank_le_iff_exists_linearMap]
/-
**finrank_le_iff_exists_linearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_le_iff_exists_linearMap [Module.Finite R M] [Module.Finite R M'] :
 finrank R M <= finrank R M' ↔ exists f : M ->ₗ[R] M', Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem finrank_le_iff_exists_linearMap [Module.Finite R M] [Module.Finite R M'] :
    finrank R M ≤ finrank R M' ↔ ∃ f : M →ₗ[R] M', Function.Injective f := by
  simp [← lift_rank_le_iff_exists_linearMap, ← finrank_eq_rank]

/-- Two vector spaces are isomorphic if they have the same dimension. -/
/-
**nonempty_linearEquiv_of_lift_rank_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_linearEquiv_of_lift_rank_eq (cnd : Cardinal.lift.{v'} (Module.ran
k R M) = Cardinal.lift.{v} (Module.rank R M')) : Nonempty (M ≃ₗ[R] M')
参数：cnd : Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R
 M')。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_mk_eq`：lift_mk_eq {α : Type u} {β : Type v} : lift.{max v 
w} #α = lift.{max u w} #β ↔ Nonempty (α ≃ β)

--- 原说明 ---
Two vector spaces are isomorphic if they have the same dimension.
-/
theorem nonempty_linearEquiv_of_lift_rank_eq
    (cnd : Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')) :
    Nonempty (M ≃ₗ[R] M') := by
  obtain ⟨⟨α, B⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  obtain ⟨⟨β, B'⟩⟩ := Module.Free.exists_basis (R := R) (M := M')
  have : Cardinal.lift.{v', v} #α = Cardinal.lift.{v, v'} #β := by
    rw [B.mk_eq_rank'', cnd, B'.mk_eq_rank'']
  exact (Cardinal.lift_mk_eq.{v, v', 0}.1 this).map (B.equiv B')

/-- Two vector spaces are isomorphic if they have the same dimension. -/
/-
**nonempty_linearEquiv_of_rank_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_linearEquiv_of_rank_eq (cond : Module.rank R M = Module.rank R M₁
) : Nonempty (M ≃ₗ[R] M₁)
参数：cond : Module.rank R M = Module.rank R M₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_linearEquiv_of_lift_rank_eq`：nonempty_linearEquiv_of_lift_rank_
eq (cnd : Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank 
R M')) : Nonempty (M ≃ₗ[R]…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
Two vector spaces are isomorphic if they have the same dimension.
-/
theorem nonempty_linearEquiv_of_rank_eq (cond : Module.rank R M = Module.rank R M₁) :
    Nonempty (M ≃ₗ[R] M₁) :=
  nonempty_linearEquiv_of_lift_rank_eq <| congr_arg _ cond

section

variable (M M' M₁)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
/-
**LinearEquiv.ofLiftRankEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearEquiv.ofLiftRankEq (cond : Cardinal.lift.{v'} (Module.rank R M) = Ca
rdinal.lift.{v} (Module.rank R M')) : M ≃ₗ[R] M'
参数：cond : Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank 
R M')。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_linearEquiv_of_lift_rank_eq`：nonempty_linearEquiv_of_lift_rank_
eq (cnd : Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank 
R M')) : Nonempty (M ≃ₗ[R]…

--- 原说明 ---
Two vector spaces are isomorphic if they have the same dimension.
-/
def LinearEquiv.ofLiftRankEq
    (cond : Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')) :
    M ≃ₗ[R] M' :=
  Classical.choice (nonempty_linearEquiv_of_lift_rank_eq cond)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
/-
**LinearEquiv.ofRankEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearEquiv.ofRankEq (cond : Module.rank R M = Module.rank R M₁) : M ≃ₗ[R]
 M₁
参数：cond : Module.rank R M = Module.rank R M₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_linearEquiv_of_rank_eq`：nonempty_linearEquiv_of_rank_eq (cond :
 Module.rank R M = Module.rank R M₁) : Nonempty (M ≃ₗ[R] M₁)

--- 原说明 ---
Two vector spaces are isomorphic if they have the same dimension.
-/
def LinearEquiv.ofRankEq (cond : Module.rank R M = Module.rank R M₁) : M ≃ₗ[R] M₁ :=
  Classical.choice (nonempty_linearEquiv_of_rank_eq cond)

end

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
/-
**Module.nonempty_linearEquiv_iff_lift_rank_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.nonempty_linearEquiv_iff_lift_rank_eq : Nonempty (M ≃ₗ[R] M') ↔ Car
dinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.lift_rank_eq`：LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') : Ca
rdinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')
· 使用定理 `nonempty_linearEquiv_of_lift_rank_eq`：nonempty_linearEquiv_of_lift_rank_
eq (cnd : Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank 
R M')) : Nonempty (M ≃ₗ[R]…

--- 原说明 ---
Two vector spaces are isomorphic if and only if they have the same dimension.
-/
theorem Module.nonempty_linearEquiv_iff_lift_rank_eq : Nonempty (M ≃ₗ[R] M') ↔
    Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M') :=
  ⟨fun ⟨h⟩ => LinearEquiv.lift_rank_eq h, fun h => nonempty_linearEquiv_of_lift_rank_eq h⟩

@[deprecated (since := "2026-06-30")]
alias LinearEquiv.nonempty_equiv_iff_lift_rank_eq := Module.nonempty_linearEquiv_iff_lift_rank_eq

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
/-
**Module.nonempty_linearEquiv_iff_rank_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.nonempty_linearEquiv_iff_rank_eq : Nonempty (M ≃ₗ[R] M₁) ↔ Module.r
ank R M = Module.rank R M₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用定理 `nonempty_linearEquiv_of_rank_eq`：nonempty_linearEquiv_of_rank_eq (cond :
 Module.rank R M = Module.rank R M₁) : Nonempty (M ≃ₗ[R] M₁)

--- 原说明 ---
Two vector spaces are isomorphic if and only if they have the same dimension.
-/
theorem Module.nonempty_linearEquiv_iff_rank_eq :
    Nonempty (M ≃ₗ[R] M₁) ↔ Module.rank R M = Module.rank R M₁ :=
  ⟨fun ⟨h⟩ => LinearEquiv.rank_eq h, fun h => nonempty_linearEquiv_of_rank_eq h⟩

@[deprecated (since := "2026-06-30")]
alias LinearEquiv.nonempty_equiv_iff_rank_eq := Module.nonempty_linearEquiv_iff_rank_eq

/-- Two finite and free modules are isomorphic if they have the same (finite) rank. -/
/-
**FiniteDimensional.nonempty_linearEquiv_of_finrank_eq** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：FiniteDimensional.nonempty_linearEquiv_of_finrank_eq [Module.Finite R M] [
Module.Finite R M'] (cond : finrank R M = finrank R M') : Nonempty (M ≃ₗ[R] M')
参数：cond : finrank R M = finrank R M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_linearEquiv_of_lift_rank_eq`：nonempty_linearEquiv_of_lift_rank_
eq (cnd : Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank 
R M')) : Nonempty (M ≃ₗ[R]…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two finite and free modules are isomorphic if they have the same (finite) rank.
-/
theorem FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    [Module.Finite R M] [Module.Finite R M'] (cond : finrank R M = finrank R M') :
    Nonempty (M ≃ₗ[R] M') :=
  nonempty_linearEquiv_of_lift_rank_eq <| by simp only [← finrank_eq_rank, cond, lift_natCast]

/-- Two finite and free modules are isomorphic if and only if they have the same (finite) rank. -/
/-
**FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq [Module.Finite R M] 
[Module.Finite R M'] : Nonempty (M ≃ₗ[R] M') ↔ finrank R M = finrank R M'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `FiniteDimensional.nonempty_linearEquiv_of_finrank_eq`：FiniteDimensional.
nonempty_linearEquiv_of_finrank_eq [Module.Finite R M] [Module.Finite R M'] (con
d : finrank R M = finrank R M') : Nonempty…

--- 原说明 ---
Two finite and free modules are isomorphic if and only if they have the same (fi
nite) rank.
-/
theorem FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq [Module.Finite R M]
    [Module.Finite R M'] : Nonempty (M ≃ₗ[R] M') ↔ finrank R M = finrank R M' :=
  ⟨fun ⟨h⟩ => h.finrank_eq, fun h => nonempty_linearEquiv_of_finrank_eq h⟩

variable (M M') in
/-- Two finite and free modules are isomorphic if they have the same (finite) rank. -/
/-
**LinearEquiv.ofFinrankEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearEquiv.ofFinrankEq [Module.Finite R M] [Module.Finite R M'] (cond : f
inrank R M = finrank R M') : M ≃ₗ[R] M'
参数：cond : finrank R M = finrank R M'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.nonempty_linearEquiv_of_finrank_eq`：FiniteDimensional.
nonempty_linearEquiv_of_finrank_eq [Module.Finite R M] [Module.Finite R M'] (con
d : finrank R M = finrank R M') : Nonempty…

--- 原说明 ---
Two finite and free modules are isomorphic if they have the same (finite) rank.
-/
noncomputable def LinearEquiv.ofFinrankEq [Module.Finite R M] [Module.Finite R M']
    (cond : finrank R M = finrank R M') : M ≃ₗ[R] M' :=
  Classical.choice <| FiniteDimensional.nonempty_linearEquiv_of_finrank_eq cond

namespace Module

/-- A free module of rank zero is trivial. -/
/-
**Module.subsingleton_of_rank_zero** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：subsingleton_of_rank_zero (h : Module.rank R M = 0) : Subsingleton M
参数：h : Module.rank R M = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_eq_zero_iff`：mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty 
α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M

--- 原说明 ---
A free module of rank zero is trivial.
-/
lemma subsingleton_of_rank_zero (h : Module.rank R M = 0) : Subsingleton M := by
  rw [← Basis.mk_eq_rank'' (Module.Free.chooseBasis R M), Cardinal.mk_eq_zero_iff] at h
  exact (Module.Free.chooseBasis R M).repr.subsingleton

/-- See `rank_lt_aleph0` for the inverse direction without `Module.Free R M`. -/
/-
**Module.rank_lt_aleph0_iff** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：rank_lt_aleph0_iff : Module.rank R M < ℵ₀ ↔ Module.Finite R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Free.rank_eq_card_chooseBasisIndex`：rank_eq_card_chooseBasisIndex
 : Module.rank R M = #(ChooseBasisIndex R M)
· 使用引理 `Cardinal.mk_lt_aleph0_iff`：mk_lt_aleph0_iff : #α < ℵ₀ ↔ Finite α
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
See `rank_lt_aleph0` for the inverse direction without `Module.Free R M`.
-/
lemma rank_lt_aleph0_iff : Module.rank R M < ℵ₀ ↔ Module.Finite R M := by
  rw [Free.rank_eq_card_chooseBasisIndex, mk_lt_aleph0_iff]
  exact ⟨fun h ↦ Finite.of_basis (Free.chooseBasis R M),
    fun I ↦ Finite.of_fintype (Free.ChooseBasisIndex R M)⟩
/-
**Module.finrank_of_not_finite** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_of_not_finite (h : ¬Module.Finite R M) : finrank R M = 0
参数：h : ¬Module.Finite R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
· 使用引理 `Cardinal.toNat_eq_zero`：toNat_eq_zero : toNat c = 0 ↔ c = 0 ∨ ℵ₀ <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用引理 `Module.rank_lt_aleph0_iff`：rank_lt_aleph0_iff : Module.rank R M < ℵ₀ ↔ M
odule.Finite R M
-/
theorem finrank_of_not_finite (h : ¬Module.Finite R M) : finrank R M = 0 := by
  rw [finrank, toNat_eq_zero, ← not_lt, Module.rank_lt_aleph0_iff]
  exact .inr h
/-
**Module.finite_of_finrank_pos** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finite_of_finrank_pos (h : 0 < finrank R M) : Module.Finite R M
参数：h : 0 < finrank R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_of_not_finite`：finrank_of_not_finite (h : ¬Module.Finite 
R M) : finrank R M = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem finite_of_finrank_pos (h : 0 < finrank R M) : Module.Finite R M := by
  contrapose h
  simp [finrank_of_not_finite h]
/-
**Module.finite_of_finrank_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finite_of_finrank_eq_succ {n : Nat} (hn : finrank R M = n.succ) : Module.F
inite R M
参数：hn : finrank R M = n.succ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finite_of_finrank_pos`：finite_of_finrank_pos (h : 0 < finrank R M
) : Module.Finite R M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
theorem finite_of_finrank_eq_succ {n : ℕ} (hn : finrank R M = n.succ) : Module.Finite R M :=
  finite_of_finrank_pos <| by rw [hn]; exact n.succ_pos
/-
**Module.finite_iff_of_rank_eq_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finite_iff_of_rank_eq_nsmul {W} [AddCommMonoid W] [Module R W] [Module.Fre
e R W] {n : Nat} (hn : n != 0) (hVW : Module.rank R M = n • Module.rank R W) : M
odule.Finite R M ↔ Module.Finite R W
参数：hn : n != 0；hVW : Module.rank R M = n • Module.rank R W。
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
· 使用定理 `Cardinal.nsmul_lt_aleph0_iff_of_ne_zero`：nsmul_lt_aleph0_iff_of_ne_zero 
{n : Nat} {a : Cardinal} (h : n != 0) : n • a < ℵ₀ ↔ a < ℵ₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem finite_iff_of_rank_eq_nsmul {W} [AddCommMonoid W] [Module R W] [Module.Free R W] {n : ℕ}
    (hn : n ≠ 0) (hVW : Module.rank R M = n • Module.rank R W) :
    Module.Finite R M ↔ Module.Finite R W := by
  simp only [← rank_lt_aleph0_iff, hVW, nsmul_lt_aleph0_iff_of_ne_zero hn]

variable (R S M) in
omit [Module.Free R M] in
/-- Also see `Module.finrank_top_le_finrank_of_isScalarTower`
for a version with different typeclass constraints. -/
/-
**Module.finrank_top_le_finrank_of_isScalarTower_of_free** 是 Mathlib 中的一个引理，位于命名
空间 `Module`。
形式化陈述：finrank_top_le_finrank_of_isScalarTower_of_free [Semiring S] [StrongRankCo
ndition S] [Module S M] [Module R S] [FaithfulSMul R S] [Module.Finite R S] [IsS
calarTower R S S] [IsScalarTower R S M] [Module.Free S M] : finrank S M <= finra
nk R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.trans`：∀ {R : Type u_6} (A : Type u_7) (M : Type u_8) [ins
t : Semiring R] [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : A
ddCommMon…
· 使用引理 `Module.finrank_top_le_finrank_of_isScalarTower`：Module.finrank_top_le_fi
nrank_of_isScalarTower [Module.Finite R M] [Semiring S] [Module S M] [Module R S
] [IsScalarTower R S S] [FaithfulSMu…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Cardinal.toNat_eq_zero`：toNat_eq_zero : toNat c = 0 ↔ c = 0 ∨ ℵ₀ <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用引理 `Module.rank_lt_aleph0_iff`：rank_lt_aleph0_iff : Module.rank R M < ℵ₀ ↔ M
odule.Finite R M
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
Also see `Module.finrank_top_le_finrank_of_isScalarTower`
for a version with different typeclass constraints.
-/
lemma finrank_top_le_finrank_of_isScalarTower_of_free [Semiring S] [StrongRankCondition S]
    [Module S M] [Module R S] [FaithfulSMul R S] [Module.Finite R S]
    [IsScalarTower R S S] [IsScalarTower R S M] [Module.Free S M] :
    finrank S M ≤ finrank R M := by
  by_cases H : Module.Finite S M
  · have := Module.Finite.trans (R := R) S M
    exact finrank_top_le_finrank_of_isScalarTower R S M
  · rw [finrank, Cardinal.toNat_eq_zero.mpr (.inr _)]
    · exact zero_le
    · rwa [← not_lt, Module.rank_lt_aleph0_iff]

variable (R) in
/-- Also see `Module.finrank_bot_le_finrank_of_isScalarTower`
for a version with different typeclass constraints. -/
/-
**Module.finrank_bot_le_finrank_of_isScalarTower_of_free** 是 Mathlib 中的一个引理，位于命名
空间 `Module`。
形式化陈述：finrank_bot_le_finrank_of_isScalarTower_of_free (S T : Type*) [Semiring S]
 [Semiring T] [Module R T] [Module S T] [Module R S] [IsScalarTower R S T] [IsSc
alarTower S T T] [FaithfulSMul S T] [Module.Finite S T] [Module.Free R S] : finr
ank R S <= finrank R T
参数：S T : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.trans`：∀ {R : Type u_6} (A : Type u_7) (M : Type u_8) [ins
t : Semiring R] [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : A
ddCommMon…
· 使用引理 `Module.finrank_bot_le_finrank_of_isScalarTower`：Module.finrank_bot_le_fi
nrank_of_isScalarTower (S T : Type*) [Semiring S] [Semiring T] [Module R T] [Mod
ule S T] [Module R S] [IsScalarTower…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Cardinal.toNat_eq_zero`：toNat_eq_zero : toNat c = 0 ↔ c = 0 ∨ ℵ₀ <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用引理 `Module.rank_lt_aleph0_iff`：rank_lt_aleph0_iff : Module.rank R M < ℵ₀ ↔ M
odule.Finite R M
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
Also see `Module.finrank_bot_le_finrank_of_isScalarTower`
for a version with different typeclass constraints.
-/
lemma finrank_bot_le_finrank_of_isScalarTower_of_free (S T : Type*) [Semiring S] [Semiring T]
    [Module R T] [Module S T] [Module R S] [IsScalarTower R S T]
    [IsScalarTower S T T] [FaithfulSMul S T] [Module.Finite S T] [Module.Free R S] :
    finrank R S ≤ finrank R T := by
  by_cases H : Module.Finite R S
  · have := Module.Finite.trans (R := R) S T
    exact finrank_bot_le_finrank_of_isScalarTower R S T
  · rw [finrank, Cardinal.toNat_eq_zero.mpr (.inr _)]
    · exact zero_le
    · rwa [← not_lt, Module.rank_lt_aleph0_iff]
/-
**Module.nonempty_linearEquiv_iff_rank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Module`
。
形式化陈述：nonempty_linearEquiv_iff_rank_eq_one : Nonempty (R ≃ₗ[R] M) ↔ Module.rank 
R M = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nonempty_linearEquiv_iff_rank_eq_one :
    Nonempty (R ≃ₗ[R] M) ↔ Module.rank R M = 1 := by
  simp [nonempty_linearEquiv_iff_lift_rank_eq, eq_comm]

/-- See also `finrank_eq_one_iff` -/
/-
**Module.nonempty_linearEquiv_iff_finrank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Modu
le`。
形式化陈述：nonempty_linearEquiv_iff_finrank_eq_one : Nonempty (R ≃ₗ[R] M) ↔ finrank R
 M = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
See also `finrank_eq_one_iff`
-/
theorem nonempty_linearEquiv_iff_finrank_eq_one :
    Nonempty (R ≃ₗ[R] M) ↔ finrank R M = 1 := by
  simp [nonempty_linearEquiv_iff_rank_eq_one, finrank]

alias ⟨_, nonempty_linearEquiv_of_finrank_eq_one⟩ := nonempty_linearEquiv_iff_finrank_eq_one
/-
**Module.nonempty_algEquiv_iff_finrank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Module`
。
形式化陈述：nonempty_algEquiv_iff_finrank_eq_one {R S : Type*} [CommSemiring R] [Stron
gRankCondition R] [Semiring S] [Algebra R S] [Free R S] : Nonempty (R ≃ₐ[R] S) ↔
 finrank R S = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.nonempty_linearEquiv_iff_finrank_eq_one`：nonempty_linearEquiv_iff
_finrank_eq_one : Nonempty (R ≃ₗ[R] M) ↔ finrank R M = 1
· 使用定理 `bijective_algebraMap_of_linearEquiv`：bijective_algebraMap_of_linearEquiv
 (b : F ≃ₗ[F] E) : Bijective (algebraMap F E)
-/
theorem nonempty_algEquiv_iff_finrank_eq_one
    {R S : Type*} [CommSemiring R] [StrongRankCondition R] [Semiring S] [Algebra R S]
    [Free R S] : Nonempty (R ≃ₐ[R] S) ↔ finrank R S = 1 := by
  rw [← nonempty_linearEquiv_iff_finrank_eq_one]
  exact ⟨fun ⟨e⟩ ↦ ⟨e⟩, fun ⟨e⟩ ↦
    ⟨.ofBijective (Algebra.ofId R S) (bijective_algebraMap_of_linearEquiv e)⟩⟩

variable (R M)

/-- A finite rank free module has a basis indexed by `Fin (finrank R M)`. -/
/-
**Module.finBasis** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：finBasis [Module.Finite R M] : Basis (Fin (finrank R M)) R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite rank free module has a basis indexed by `Fin (finrank R M)`.
-/
noncomputable def finBasis [Module.Finite R M] :
    Basis (Fin (finrank R M)) R M :=
  (Module.Free.chooseBasis R M).reindex (Fintype.equivFinOfCardEq
    (finrank_eq_card_chooseBasisIndex R M).symm)

/-- A rank `n` free module has a basis indexed by `Fin n`. -/
/-
**Module.finBasisOfFinrankEq** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：finBasisOfFinrankEq [Module.Finite R M] {n : Nat} (hn : finrank R M = n) :
 Basis (Fin n) R M
参数：hn : finrank R M = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A rank `n` free module has a basis indexed by `Fin n`.
-/
noncomputable def finBasisOfFinrankEq [Module.Finite R M] {n : ℕ} (hn : finrank R M = n) :
    Basis (Fin n) R M := (finBasis R M).reindex (finCongr hn)

variable {R M}

/-- A free module with rank 1 has a basis with one element. -/
/-
**Module.basisUnique** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：basisUnique (ι : Type*) [Unique ι] (h : finrank R M = 1) : Basis ι R M
参数：ι : Type*；h : finrank R M = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A free module with rank 1 has a basis with one element.
-/
noncomputable def basisUnique (ι : Type*) [Unique ι]
    (h : finrank R M = 1) :
    Basis ι R M :=
  haveI : Module.Finite R M :=
    Module.finite_of_finrank_pos (_root_.zero_lt_one.trans_le h.symm.le)
  (finBasisOfFinrankEq R M h).reindex (Equiv.ofUnique _ _)

/-- If a finite module of `finrank 1` has a basis, then this basis has a unique element. -/
/-
**Module.Basis.nonempty_unique_index_of_finrank_eq_one** 是 Mathlib 中的一个定理，位于命名空间
 `Module.Basis`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst_1 : AddCommMonoid M]
 [inst_2 : _root_.Module R M]   [Module.Free R M] [StrongRankCondition R] {ι : T
ype u_2} (b : Module.Basis ι R M),   Module.finrank R M = 1 → Nonempty (Unique ι
)
参数：b : Module.Basis ι R M；Unique ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `Module.finite_of_finrank_pos`：finite_of_finrank_pos (h : 0 < finrank R M
) : Module.Finite R M
· 使用定理 `Nat.lt_of_sub_eq_succ`：∀ {m n l : ℕ}, m - n = l.succ → n < m
· 使用引理 `Module.Finite.finite_basis`：finite_basis [Nontrivial R] {ι} [Module.Fini
te R M] (b : Basis ι R M) : _root_.Finite ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_one_iff_nonempty_unique`：card_eq_one_iff_nonempty_unique
 : card α = 1 ↔ Nonempty (Unique α)
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι

--- 原说明 ---
If a finite module of `finrank 1` has a basis, then this basis has a unique elem
ent.
-/
theorem Basis.nonempty_unique_index_of_finrank_eq_one
    {ι : Type*} (b : Module.Basis ι R M) (d1 : Module.finrank R M = 1) :
    Nonempty (Unique ι) := by
  -- why isn't this an instance?
  have : Nontrivial R := nontrivial_of_invariantBasisNumber R
  have : Module.Finite R M :=
    Module.finite_of_finrank_pos (Nat.lt_of_sub_eq_succ d1)
  have : Finite ι := Module.Finite.finite_basis b
  have : Fintype ι := Fintype.ofFinite ι
  rwa [Module.finrank_eq_card_basis b, Fintype.card_eq_one_iff_nonempty_unique] at d1

@[simp]
/-
**Module.basisUnique_repr_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：basisUnique_repr_eq_zero_iff {ι : Type*} [Unique ι] {h : finrank R M = 1} 
{v : M} {i : ι} : (basisUnique ι h).repr v i = 0 ↔ v = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.map_eq_zero_iff`：map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Finsupp.zero_apply`：zero_apply {a : α} : (0 : α ->₀ M) a = 0
-/
theorem basisUnique_repr_eq_zero_iff {ι : Type*} [Unique ι]
    {h : finrank R M = 1} {v : M} {i : ι} :
    (basisUnique ι h).repr v i = 0 ↔ v = 0 :=
  ⟨fun hv =>
    (basisUnique ι h).repr.map_eq_zero_iff.mp (Finsupp.ext fun j => Subsingleton.elim i j ▸ hv),
    fun hv => by rw [hv, map_zero, Finsupp.zero_apply]⟩

omit [StrongRankCondition R] in
/-
**Module._root_.OrzechProperty.bijective_of_surjective_of_finrank_le** 是 Mathlib
 中的一个定理，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.OrzechProperty.bijective_of_surjective_of_finrank_le
    [OrzechProperty R] [Module.Finite R M] [Module.Finite R M']
    (f : M →ₗ[R] M') (hf : Function.Surjective f) (h : Module.finrank R M ≤ Module.finrank R M') :
    Function.Bijective f := by
  cases subsingleton_or_nontrivial R
  -- TODO : figure out how to make `nontriviality` work here nicely
  · have := Module.subsingleton R M
    exact ⟨Function.injective_of_subsingleton f, hf⟩
  rcases finrank_le_iff_exists_linearMap.mp h with ⟨_, hi⟩
  exact OrzechProperty.bijective_of_surjective_of_injective _ _ hi hf

variable {R : Type*} [CommSemiring R] [StrongRankCondition R]
    {M : Type*} [AddCommMonoid M] [Module R M] [Module.Free R M]

set_option backward.isDefEq.respectTransparency false in
/-
**Module._root_.LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one** 是 Mathlib 
中的一个定理，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
    (d1 : Module.finrank R M = 1) (u : M →ₗ[R] M) :
    ∃! c : R, u = c • LinearMap.id := by
  let e := (nonempty_linearEquiv_of_finrank_eq_one d1).some
  set c := e.symm (u (e 1)) with hc
  suffices u = c • LinearMap.id by
    use c
    simp only [this, true_and]
    intro d hcd
    rw [LinearMap.ext_iff] at hcd
    simpa using (LinearEquiv.congr_arg (e := e.symm) (hcd (e 1))).symm
  ext x
  have (x : M) : x = (e.symm x) • (e 1) := by simp [← LinearEquiv.map_smul]
  rw [this x]
  simp only [hc, map_smul, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  rw [← this]

/-- Endomorphisms of a free module of rank one are homotheties. -/
@[simps apply]
/-
**Module._root_.LinearEquiv.smul_id_of_finrank_eq_one** 是 Mathlib 中的一个定义，位于命名空间 
`Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Endomorphisms of a free module of rank one are homotheties.
-/
noncomputable def _root_.LinearEquiv.smul_id_of_finrank_eq_one (d1 : Module.finrank R M = 1) :
    R ≃ₗ[R] (M →ₗ[R] M) where
  toFun := fun c ↦ c • LinearMap.id
  map_add' c d := by ext; simp [add_smul]
  map_smul' c d := by ext; simp [mul_smul]
  invFun u := (u.existsUnique_eq_smul_id_of_finrank_eq_one d1).choose
  left_inv c := by
    simp [← (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one d1 _).choose_spec.2 c]
  right_inv u := ((u.existsUnique_eq_smul_id_of_finrank_eq_one d1).choose_spec.1).symm

end Module

end StrongRankCondition

namespace Algebra

/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (R S : Type*) [CommSemiring R] [StrongRankCondition R] [Semiring S]
    [Algebra R S] [IsQuadraticExtension R S] :
    Module.Finite R S := finite_of_finrank_eq_succ <| IsQuadraticExtension.finrank_eq_two R S

end Algebra

