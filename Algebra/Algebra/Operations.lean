/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.Module.Submodule.Finsupp
public import Mathlib.Algebra.Ring.NonZeroDivisors
public import Mathlib.Algebra.Ring.Submonoid.Pointwise
public import Mathlib.Data.Set.Semiring
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Pointwise

/-!
# Multiplication and division of submodules of an algebra.

An interface for multiplication and division of sub-R-modules of an R-algebra A is developed.

## Main definitions

Let `R` be a commutative ring (or semiring) and let `A` be an `R`-algebra.

* `1 : Submodule R A`   : the R-submodule R of the R-algebra A
* `Mul (Submodule R A)` : multiplication of two sub-R-modules M and N of A is defined to be
                              the smallest submodule containing all the products `m * n`.
* `Div (Submodule R A)` : `I / J` is defined to be the submodule consisting of all `a : A` such
                              that `a • J ⊆ I`

It is proved that `Submodule R A` is a semiring, and also an algebra over `Set A`.

Additionally, in the `Pointwise` scope we promote `Submodule.pointwiseDistribMulAction` to a
`MulSemiringAction` as `Submodule.pointwiseMulSemiringAction`.

When `R` is not necessarily commutative, and `A` is merely an `R`-module with a ring structure
such that `IsScalarTower R A A` holds (equivalent to the data of a ring homomorphism `R →+* A`
by `ringHomEquivModuleIsScalarTower`), we can still define `1 : Submodule R A` and
`Mul (Submodule R A)`, but `1` is only a left identity, not necessarily a right one.

## Tags

multiplication of submodules, division of submodules, submodule semiring
-/

@[expose] public section


universe uι u v

open Algebra Set MulOpposite

open scoped Pointwise

namespace SubMulAction

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

/-
**SubMulAction.algebraMap_mem** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：algebraMap_mem (r : R) : algebraMap R A r in (1 : SubMulAction R A)
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
-/
theorem algebraMap_mem (r : R) : algebraMap R A r ∈ (1 : SubMulAction R A) :=
  ⟨r, (algebraMap_eq_smul_one r).symm⟩
/-
**SubMulAction.mem_one'** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：mem_one' {x : A} : x in (1 : SubMulAction R A) ↔ exists y, algebraMap R A 
y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_one' {x : A} : x ∈ (1 : SubMulAction R A) ↔ ∃ y, algebraMap R A y = x :=
  exists_congr fun r => by rw [algebraMap_eq_smul_one]

end SubMulAction

namespace Submodule

section Module

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

-- TODO: Why is this in a file about `Algebra`?
-- TODO: potentially change this back to `LinearMap.range (Algebra.linearMap R A)`
-- once a version of `Algebra` without the `commutes'` field is introduced.
-- See issue https://github.com/leanprover-community/mathlib4/issues/18110.
/-- `1 : Submodule R A` is the submodule `R ∙ 1` of `A`.
-/
/-
**Submodule.one** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：one : One (Submodule R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`1 : Submodule R A` is the submodule `R ∙ 1` of `A`.
-/
instance one : One (Submodule R A) :=
  ⟨LinearMap.range (LinearMap.toSpanSingleton R A 1)⟩
/-
**Submodule.one_eq_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：one_eq_span : (1 : Submodule R A) = R ∙ 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.span_singleton_eq_range`：span_singleton_eq_range (x : M) : R ∙
 x = range (toSpanSingleton R M x)
-/
theorem one_eq_span : (1 : Submodule R A) = R ∙ 1 :=
  (LinearMap.span_singleton_eq_range _ _ _).symm
/-
**Submodule.le_one_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：le_one_toAddSubmonoid : 1 <= (1 : Submodule R A).toAddSubmonoid
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
-/
theorem le_one_toAddSubmonoid : 1 ≤ (1 : Submodule R A).toAddSubmonoid := by
  rintro x ⟨n, rfl⟩
  exact ⟨n, show (n : R) • (1 : A) = n by rw [Nat.cast_smul_eq_nsmul, nsmul_one]⟩

@[simp]
/-
**Submodule.toSubMulAction_one** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toSubMulAction_one : (1 : Submodule R A).toSubMulAction = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.one_eq_span`：one_eq_span : (1 : Submodule R A) = R ∙ 1
· 使用定理 `SubMulAction.mem_one`：mem_one {x : M} : x in (1 : SubMulAction R M) ↔ ex
ists r : R, r • (1 : M) = x
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
-/
theorem toSubMulAction_one : (1 : Submodule R A).toSubMulAction = 1 :=
  SetLike.ext fun _ ↦ by rw [one_eq_span, SubMulAction.mem_one]; exact mem_span_singleton
/-
**Submodule.one_eq_span_one_set** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：one_eq_span_one_set : (1 : Submodule R A) = span R 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.one_eq_span`：one_eq_span : (1 : Submodule R A) = R ∙ 1
-/
theorem one_eq_span_one_set : (1 : Submodule R A) = span R 1 :=
  one_eq_span

@[simp]
/-
**Submodule.one_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：one_le {P : Submodule R A} : (1 : Submodule R A) <= P ↔ (1 : A) in P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.one_eq_span`：one_eq_span : (1 : Submodule R A) = R ∙ 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem one_le {P : Submodule R A} : (1 : Submodule R A) ≤ P ↔ (1 : A) ∈ P := by
  simp [one_eq_span]
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoidWithOne (Submodule R A) where
  add_comm := sup_comm

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul (Submodule R A) (Submodule R M) where
  smul A' M' :=
  { __ := A'.toAddSubmonoid • M'.toAddSubmonoid
    smul_mem' := fun r m hm ↦ AddSubmonoid.smul_induction_on hm
      (fun a ha m hm ↦ by rw [← smul_assoc]; exact AddSubmonoid.smul_mem_smul (A'.smul_mem r ha) hm)
      fun m₁ m₂ h₁ h₂ ↦ by rw [smul_add]; exact (A'.1 • M'.1).add_mem h₁ h₂ }

section

variable {I J : Submodule R A} {N P : Submodule R M}

/-
**Submodule.smul_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_toAddSubmonoid : (I • N).toAddSubmonoid = I.toAddSubmonoid • N.toAddS
ubmonoid
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_toAddSubmonoid : (I • N).toAddSubmonoid = I.toAddSubmonoid • N.toAddSubmonoid := rfl
/-
**Submodule.smul_mem_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_mem_smul {r} {n} (hr : r in I) (hn : n in N) : r • n in I • N
参数：hr : r in I；hn : n in N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AddSubmonoid.smul_mem_smul`：smul_mem_smul (hm : m in M) (hn : n in N) : 
m • n in M • N
-/
theorem smul_mem_smul {r} {n} (hr : r ∈ I) (hn : n ∈ N) : r • n ∈ I • N :=
  AddSubmonoid.smul_mem_smul hr hn
/-
**Submodule.smul_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_le : I • N <= P ↔ forall r in I, forall n in N, r • n in P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AddSubmonoid.smul_le`：smul_le : M • N <= P ↔ forall m in M, forall n in 
N, m • n in P
-/
theorem smul_le : I • N ≤ P ↔ ∀ r ∈ I, ∀ n ∈ N, r • n ∈ P :=
  AddSubmonoid.smul_le

@[simp, norm_cast]
/-
**Submodule.coe_set_smul** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：coe_set_smul : (I : Set A) • N = I • N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.set_smul_eq_of_le`：set_smul_eq_of_le (p : Submodule R M) (clos
ed_under_smul : forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in N -> r • n in p) (le : p 
<= s • N) : s • N…
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.smul_le`：smul_le : I • N <= P ↔ forall r in I, forall n in N, 
r • n in P
· 使用引理 `Submodule.mem_set_smul_of_mem_mem`：mem_set_smul_of_mem_mem {r : S} {m : 
M} (mem1 : r in s) (mem2 : m in N) : r • m in s • N
-/
lemma coe_set_smul : (I : Set A) • N = I • N :=
  set_smul_eq_of_le _ _ _
    (fun _ _ hr hx ↦ smul_mem_smul hr hx)
    (smul_le.mpr fun _ hr _ hx ↦ mem_set_smul_of_mem_mem hr hx)

@[elab_as_elim]
/-
**Submodule.smul_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_induction_on {p : M -> Prop} {x} (H : x in I • N) (smul : forall r in
 I, forall n in N, p (r • n)) (add : forall x y, p x -> p y -> p (x + y)) : p x
参数：H : x in I • N；smul : forall r in I, forall n in N, p (r • n)；add : forall x 
y, p x -> p y -> p (x + y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.smul_induction_on`：∀ {R : Type u_2} {A : Type u_3} [inst : 
AddMonoid R] [inst_1 : AddMonoid A] [inst_2 : DistribSMul R A]   {M : AddSubmono
id R} {N : AddSubmon…
-/
theorem smul_induction_on {p : M → Prop} {x} (H : x ∈ I • N) (smul : ∀ r ∈ I, ∀ n ∈ N, p (r • n))
    (add : ∀ x y, p x → p y → p (x + y)) : p x :=
  AddSubmonoid.smul_induction_on H smul add

/-- Dependent version of `Submodule.smul_induction_on`. -/
@[elab_as_elim]
/-
**Submodule.smul_induction_on'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_induction_on' {x : M} (hx : x in I • N) {p : forall x, x in I • N -> 
Prop} (smul : forall (r : A) (hr : r in I) (n : M) (hn : n in N), p (r • n) (smu
l_mem_smul hr hn)) (add : forall x hx y hy, p x hx -> p y hy -> p (x + y) (add_m
em ‹_› ‹_›)) : p x hx
参数：hx : x in I • N；smul : forall (r : A) (hr : r in I) (n : M) (hn : n in N), p 
(r • n) (smul_mem_smul hr hn)；add : forall x hx y hy, p x hx -> p y hy -> p (x +
 y) (add_mem ‹_› ‹_›)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Submodule.smul_induction_on`：smul_induction_on {p : M -> Prop} {x} (H : 
x in I • N) (smul : forall r in I, forall n in N, p (r • n)) (add : forall x y, 
p x -> p y -> p (…

--- 原说明 ---
Dependent version of `Submodule.smul_induction_on`.
-/
theorem smul_induction_on' {x : M} (hx : x ∈ I • N) {p : ∀ x, x ∈ I • N → Prop}
    (smul : ∀ (r : A) (hr : r ∈ I) (n : M) (hn : n ∈ N), p (r • n) (smul_mem_smul hr hn))
    (add : ∀ x hx y hy, p x hx → p y hy → p (x + y) (add_mem ‹_› ‹_›)) : p x hx := by
  refine Exists.elim ?_ fun (h : x ∈ I • N) (H : p x h) ↦ H
  exact smul_induction_on hx (fun a ha x hx ↦ ⟨_, smul _ ha _ hx⟩)
    fun x y ⟨_, hx⟩ ⟨_, hy⟩ ↦ ⟨_, add _ _ _ _ hx hy⟩
/-
**Submodule.smul_mono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_mono (hij : I <= J) (hnp : N <= P) : I • N <= J • P
参数：hij : I <= J；hnp : N <= P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AddSubmonoid.smul_le_smul`：smul_le_smul (h : M <= M') (hnp : N <= P) : M
 • N <= M' • P
-/
theorem smul_mono (hij : I ≤ J) (hnp : N ≤ P) : I • N ≤ J • P :=
  AddSubmonoid.smul_le_smul hij hnp
/-
**Submodule.smul_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_mono_left (h : I <= J) : I • N <= J • N
参数：h : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_mono`：smul_mono (hij : I <= J) (hnp : N <= P) : I • N <= 
J • P
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem smul_mono_left (h : I ≤ J) : I • N ≤ J • N :=
  smul_mono h le_rfl
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CovariantClass (Submodule R A) (Submodule R M) HSMul.hSMul LE.le :=
  ⟨fun _ _ => smul_mono le_rfl⟩

variable (I J N P)

@[simp]
/-
**Submodule.smul_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_bot : I • (⊥ : Submodule R M) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.toAddSubmonoid_injective`：toAddSubmonoid_injective : Injective
 (toAddSubmonoid : Submodule R M -> AddSubmonoid M)
· 使用引理 `AddSubmonoid.addSubmonoid_smul_bot`：addSubmonoid_smul_bot (S : AddSubmon
oid R) : S • (⊥ : AddSubmonoid A) = ⊥
-/
theorem smul_bot : I • (⊥ : Submodule R M) = ⊥ :=
  toAddSubmonoid_injective <| AddSubmonoid.addSubmonoid_smul_bot _

@[simp]
/-
**Submodule.bot_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：bot_smul : (⊥ : Submodule R A) • N = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.smul_le`：smul_le : I • N <= P ↔ forall r in I, forall n in N, 
r • n in P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem bot_smul : (⊥ : Submodule R A) • N = ⊥ :=
  le_bot_iff.mp <| smul_le.mpr <| by rintro _ rfl _ _; rw [zero_smul]; exact zero_mem _
/-
**Submodule.smul_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_sup : I • (N ⊔ P) = I • N ⊔ I • P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.toAddSubmonoid_injective`：toAddSubmonoid_injective : Injective
 (toAddSubmonoid : Submodule R M -> AddSubmonoid M)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.sup_toAddSubmonoid`：sup_toAddSubmonoid : (p ⊔ p').toAddSubmono
id = p.toAddSubmonoid ⊔ p'.toAddSubmonoid
· 使用引理 `AddSubmonoid.addSubmonoid_smul_sup`：addSubmonoid_smul_sup : M • (N ⊔ P) 
= M • N ⊔ M • P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_sup : I • (N ⊔ P) = I • N ⊔ I • P :=
  toAddSubmonoid_injective <| by
    simp only [smul_toAddSubmonoid, sup_toAddSubmonoid, AddSubmonoid.addSubmonoid_smul_sup]
/-
**Submodule.sup_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：sup_smul : (I ⊔ J) • N = I • N ⊔ J • N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.smul_le`：smul_le : I • N <= P ↔ forall r in I, forall n in N, 
r • n in P
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Submodule.add_mem_sup`：add_mem_sup {S T : Submodule R M} {s t : M} (hs :
 s in S) (ht : t in T) : s + t in S ⊔ T
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Submodule.smul_mono_left`：smul_mono_left (h : I <= J) : I • N <= J • N
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem sup_smul : (I ⊔ J) • N = I • N ⊔ J • N :=
  le_antisymm (smul_le.mpr fun mn hmn p hp ↦ by
    obtain ⟨m, hm, n, hn, rfl⟩ := mem_sup.mp hmn
    rw [add_smul]; exact add_mem_sup (smul_mem_smul hm hp) <| smul_mem_smul hn hp)
    (sup_le (smul_mono_left le_sup_left) <| smul_mono_left le_sup_right)
/-
**Submodule.smul_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst_1 : Semiring A] [ins
t_2 : _root_.Module R A] {M : Type u_1}   [inst_3 : AddCommMonoid M] [inst_4 : _
root_.Module R M] [inst_5 : _root_.Module A M] [inst_6 : IsScalarTower R A M]   
{B : Type u_2} [inst_7 : Semiring B] [inst_8 : _root_.Module R B] [inst_9 : _roo
t_.Module A B]   [inst_10 : _root_.Module B M] [inst_11 : IsScalarTower R A B] [
inst_12 : IsScalarTower R B M] [IsScalarTower A B M]   (I : Submodule R A) (J : 
Submodule R B) (N : Submodule R M), (I • J) • N = I • J • N
参数：I : Submodule R A；J : Submodule R B；N : Submodule R M；I • J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.smul_le`：smul_le : I • N <= P ↔ forall r in I, forall n in N, 
r • n in P
· 使用定理 `Submodule.smul_induction_on`：smul_induction_on {p : M -> Prop} {x} (H : 
x in I • N) (smul : forall r in I, forall n in N, p (r • n)) (add : forall x y, 
p x -> p y -> p (…
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
-/
protected theorem smul_assoc {B} [Semiring B] [Module R B] [Module A B] [Module B M]
    [IsScalarTower R A B] [IsScalarTower R B M] [IsScalarTower A B M]
    (I : Submodule R A) (J : Submodule R B) (N : Submodule R M) :
    (I • J) • N = I • J • N :=
  le_antisymm
    (smul_le.2 fun _ hrsij t htn ↦ smul_induction_on hrsij
      (fun r hr s hs ↦ smul_assoc r s t ▸ smul_mem_smul hr (smul_mem_smul hs htn))
      fun x y ↦ (add_smul x y t).symm ▸ add_mem)
    (smul_le.2 fun r hr _ hsn ↦ smul_induction_on hsn
      (fun j hj n hn ↦ (smul_assoc r j n).symm ▸ smul_mem_smul (smul_mem_smul hr hj) hn)
      fun m₁ m₂ ↦ (smul_add r m₁ m₂) ▸ add_mem)
/-
**Submodule.smul_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_iSup {ι : Sort*} {I : Submodule R A} {t : ι -> Submodule R M} : I • (
⨆ i, t i) = ⨆ i, I • t i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.toAddSubmonoid_injective`：toAddSubmonoid_injective : Injective
 (toAddSubmonoid : Submodule R M -> AddSubmonoid M)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.iSup_toAddSubmonoid`：iSup_toAddSubmonoid {ι : Sort*} (p : ι ->
 Submodule R M) : (⨆ i, p i).toAddSubmonoid = ⨆ i, (p i).toAddSubmonoid
· 使用引理 `AddSubmonoid.smul_iSup`：smul_iSup (T : AddSubmonoid R) (S : ι -> AddSubm
onoid A) : (T • ⨆ i, S i) = ⨆ i, T • S i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_iSup {ι : Sort*} {I : Submodule R A} {t : ι → Submodule R M} :
    I • (⨆ i, t i) = ⨆ i, I • t i :=
  toAddSubmonoid_injective <| by
    simp only [smul_toAddSubmonoid, iSup_toAddSubmonoid, AddSubmonoid.smul_iSup]
/-
**Submodule.iSup_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：iSup_smul {ι : Sort*} {t : ι -> Submodule R A} {N : Submodule R M} : (⨆ i,
 t i) • N = ⨆ i, t i • N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.smul_le`：smul_le : I • N <= P ↔ forall r in I, forall n in N, 
r • n in P
· 使用定理 `Submodule.iSup_induction`：iSup_induction {ι : Sort*} (p : ι -> Submodule
 R M) {motive : M -> Prop} {x : M} (hx : x in ⨆ i, p i) (mem : forall (i), foral
l x in p i, mo…
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Submodule.smul_mono_left`：smul_mono_left (h : I <= J) : I • N <= J • N
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem iSup_smul {ι : Sort*} {t : ι → Submodule R A} {N : Submodule R M} :
    (⨆ i, t i) • N = ⨆ i, t i • N :=
  le_antisymm (smul_le.mpr fun t ht s hs ↦ iSup_induction _ (motive := (· • s ∈ _)) ht
    (fun i t ht ↦ mem_iSup_of_mem i <| smul_mem_smul ht hs)
    (by simp_rw [zero_smul]; apply zero_mem) fun x y ↦ by simp_rw [add_smul]; apply add_mem)
    (iSup_le fun i ↦ Submodule.smul_mono_left <| le_iSup _ i)
/-
**Submodule.one_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst_1 : Semiring A] [ins
t_2 : _root_.Module R A] {M : Type u_1}   [inst_3 : AddCommMonoid M] [inst_4 : _
root_.Module R M] [inst_5 : _root_.Module A M] [inst_6 : IsScalarTower R A M]   
(N : Submodule R M), 1 • N = N
参数：N : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.smul_le`：smul_le : I • N <= P ↔ forall r in I, forall n in N, 
r • n in P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.one_le`：one_le {P : Submodule R A} : (1 : Submodule R A) <= P 
↔ (1 : A) in P
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
protected theorem one_smul : (1 : Submodule R A) • N = N := by
  refine le_antisymm (smul_le.mpr fun r hr m hm ↦ ?_) fun m hm ↦ ?_
  · obtain ⟨r, rfl⟩ := hr
    rw [LinearMap.toSpanSingleton_apply, smul_one_smul]; exact N.smul_mem r hm
  · rw [← one_smul A m]; exact smul_mem_smul (one_le.mp le_rfl) hm
/-
**Submodule.smul_subset_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_subset_smul : (↑I : Set A) • (↑N : Set M) subseteq (↑(I • N) : Set M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AddSubmonoid.smul_subset_smul`：smul_subset_smul : (↑M : Set R) • (↑N : S
et A) subseteq (↑(M • N) : Set A)
-/
theorem smul_subset_smul : (↑I : Set A) • (↑N : Set M) ⊆ (↑(I • N) : Set M) :=
  AddSubmonoid.smul_subset_smul

end

variable [IsScalarTower R A A]

/-- Multiplication of sub-R-modules of an R-module A that is also a semiring. The submodule `M * N`
consists of finite sums of elements `m * n` for `m ∈ M` and `n ∈ N`. -/
/-
**Submodule.mul** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：mul : Mul (Submodule R A) where mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication of sub-R-modules of an R-module A that is also a semiring. The su
bmodule `M * N`
consists of finite sums of elements `m * n` for `m ∈ M` and `n ∈ N`.
-/
instance mul : Mul (Submodule R A) where
  mul := (· • ·)

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}
/-
**Submodule.mul_mem_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mul_mem_mul (hm : m in M) (hn : n in N) : m * n in M * N
参数：hm : m in M；hn : n in N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
-/
theorem mul_mem_mul (hm : m ∈ M) (hn : n ∈ N) : m * n ∈ M * N :=
  smul_mem_smul hm hn
/-
**Submodule.mul_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mul_le : M * N <= P ↔ forall m in M, forall n in N, m * n in P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_le`：smul_le : I • N <= P ↔ forall r in I, forall n in N, 
r • n in P
-/
theorem mul_le : M * N ≤ P ↔ ∀ m ∈ M, ∀ n ∈ N, m * n ∈ P :=
  smul_le
/-
**Submodule.mul_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mul_toAddSubmonoid (M N : Submodule R A) : (M * N).toAddSubmonoid = M.toAd
dSubmonoid * N.toAddSubmonoid
参数：M N : Submodule R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_toAddSubmonoid (M N : Submodule R A) :
    (M * N).toAddSubmonoid = M.toAddSubmonoid * N.toAddSubmonoid := rfl

@[elab_as_elim]
/-
**Submodule.mul_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst_1 : Semiring A] [ins
t_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] {M N : Submodule R A} 
{C : A → Prop} {r : A},   r ∈ M * N → (∀ m ∈ M, ∀ n ∈ N, C (m * n)) → (∀ (x y : 
A), C x → C y → C (x + y)) → C r
参数：∀ m ∈ M, ∀ n ∈ N, C (m * n)；∀ (x y : A), C x → C y → C (x + y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_induction_on`：smul_induction_on {p : M -> Prop} {x} (H : 
x in I • N) (smul : forall r in I, forall n in N, p (r • n)) (add : forall x y, 
p x -> p y -> p (…
-/
protected theorem mul_induction_on {C : A → Prop} {r : A} (hr : r ∈ M * N)
    (hm : ∀ m ∈ M, ∀ n ∈ N, C (m * n)) (ha : ∀ x y, C x → C y → C (x + y)) : C r :=
  smul_induction_on hr hm ha

/-- A dependent version of `mul_induction_on`. -/
@[elab_as_elim]
/-
**Submodule.mul_induction_on'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst_1 : Semiring A] [ins
t_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] {M N : Submodule R A} 
{C : (r : A) → r ∈ M * N → Prop},   (∀ (m : A) (hm : m ∈ M) (n : A) (hn : n ∈ N)
, C (m * n) ⋯) →     (∀ (x : A) (hx : x ∈ M * N) (y : A) (hy : y ∈ M * N), C x h
x → C y hy → C (x + y) ⋯) →       ∀ {r : A} (hr : r ∈ M * N), C r hr
参数：r : A；∀ (m : A) (hm : m ∈ M) (n : A) (hn : n ∈ N), C (m * n) ⋯；∀ (x : A) (hx 
: x ∈ M * N) (y : A) (hy : y ∈ M * N), C x hx → C y hy → C (x + y) ⋯；hr : r ∈ M 
* N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Submodule.smul_induction_on'`：smul_induction_on' {x : M} (hx : x in I • 
N) {p : forall x, x in I • N -> Prop} (smul : forall (r : A) (hr : r in I) (n : 
M) (hn : n in N), …

--- 原说明 ---
A dependent version of `mul_induction_on`.
-/
protected theorem mul_induction_on' {C : ∀ r, r ∈ M * N → Prop}
    (mem_mul_mem : ∀ m (hm : m ∈ M) n (hn : n ∈ N), C (m * n) (mul_mem_mul hm hn))
    (add : ∀ x hx y hy, C x hx → C y hy → C (x + y) (add_mem hx hy)) {r : A} (hr : r ∈ M * N) :
    C r hr :=
  smul_induction_on' hr mem_mul_mem add

variable (M)

@[simp]
/-
**Submodule.mul_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mul_bot : M * ⊥ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_bot`：smul_bot : I • (⊥ : Submodule R M) = ⊥
-/
theorem mul_bot : M * ⊥ = ⊥ :=
  smul_bot _

@[simp]
/-
**Submodule.bot_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：bot_mul : ⊥ * M = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.bot_smul`：bot_smul : (⊥ : Submodule R A) • N = ⊥
-/
theorem bot_mul : ⊥ * M = ⊥ :=
  bot_smul _

@[simp]
/-
**Submodule.mul_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mul_eq_bot [NoZeroDivisors A] {M N : Submodule R A} : M * N = ⊥ ↔ M = ⊥ ∨ 
N = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
· 使用定理 `Submodule.bot_mul`：bot_mul : ⊥ * M = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mul_bot`：mul_bot : M * ⊥ = ⊥
-/
theorem mul_eq_bot [NoZeroDivisors A] {M N : Submodule R A} :
    M * N = ⊥ ↔ M = ⊥ ∨ N = ⊥ :=
  ⟨fun hmn =>
    or_iff_not_imp_left.mpr fun M_ne_bot =>
      N.eq_bot_iff.mpr fun n hn =>
        let ⟨m, hm, ne0⟩ := M.ne_bot_iff.mp M_ne_bot
        Or.resolve_left (mul_eq_zero.mp ((M * N).eq_bot_iff.mp hmn _ (mul_mem_mul hm hn))) ne0,
    fun h => by obtain rfl | rfl := h; exacts [bot_mul _, mul_bot _]⟩
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoZeroDivisors A] : NoZeroDivisors (Submodule R A) where
  eq_zero_or_eq_zero_of_mul_eq_zero := mul_eq_bot.1
/-
**Submodule.one_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst_1 : Semiring A] [ins
t_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (M : Submodule R A), 1
 * M = M
参数：M : Submodule R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.one_smul`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [ins
t_1 : Semiring A] [inst_2 : _root_.Module R A] {M : Type u_1}   [inst_3 : AddCom
mMonoid …
-/
protected theorem one_mul : (1 : Submodule R A) * M = M :=
  Submodule.one_smul _

variable {M}
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulLeftMono (Submodule R A) where
  elim _M _N _P hNP := smul_mono_right _ hNP
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulRightMono (Submodule R A) where
  elim _ _ _ := smul_mono_left
/-
**Submodule.mul_comm_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mul_comm_of_commute (h : forall m in M, forall n in N, Commute m n) : M * 
N = N * M
参数：h : forall m in M, forall n in N, Commute m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.toAddSubmonoid_injective`：toAddSubmonoid_injective : Injective
 (toAddSubmonoid : Submodule R M -> AddSubmonoid M)
· 使用引理 `AddSubmonoid.mul_comm_of_commute`：mul_comm_of_commute (h : forall m in M
, forall n in N, Commute m n) : M * N = N * M
-/
theorem mul_comm_of_commute (h : ∀ m ∈ M, ∀ n ∈ N, Commute m n) : M * N = N * M :=
  toAddSubmonoid_injective <| AddSubmonoid.mul_comm_of_commute h

variable (M N P)
/-
**Submodule.mul_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mul_sup : M * (N ⊔ P) = M * N ⊔ M * P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_sup`：smul_sup : I • (N ⊔ P) = I • N ⊔ I • P
-/
theorem mul_sup : M * (N ⊔ P) = M * N ⊔ M * P :=
  smul_sup _ _ _
/-
**Submodule.sup_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：sup_mul : (M ⊔ N) * P = M * P ⊔ N * P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.sup_smul`：sup_smul : (I ⊔ J) • N = I • N ⊔ J • N
-/
theorem sup_mul : (M ⊔ N) * P = M * P ⊔ N * P :=
  sup_smul _ _ _
/-
**Submodule.mul_subset_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mul_subset_mul : (↑M : Set A) * (↑N : Set A) subseteq (↑(M * N) : Set A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_subset_smul`：smul_subset_smul : (↑I : Set A) • (↑N : Set 
M) subseteq (↑(I • N) : Set M)
-/
theorem mul_subset_mul : (↑M : Set A) * (↑N : Set A) ⊆ (↑(M * N) : Set A) :=
  smul_subset_smul _ _
/-
**Submodule.restrictScalars_mul** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_mul {A B C} [Semiring A] [Semiring B] [Semiring C] [SMul A
 B] [Module A C] [Module B C] [IsScalarTower A C C] [IsScalarTower B C C] [IsSca
larTower A B C] {I J : Submodule B C} : (I * J).restrictScalars A = I.restrictSc
alars A * J.restrictScalars A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalars_mul {A B C} [Semiring A] [Semiring B] [Semiring C]
    [SMul A B] [Module A C] [Module B C] [IsScalarTower A C C] [IsScalarTower B C C]
    [IsScalarTower A B C] {I J : Submodule B C} :
    (I * J).restrictScalars A = I.restrictScalars A * J.restrictScalars A :=
  rfl

variable {ι : Sort uι}
/-
**Submodule.iSup_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：iSup_mul (s : ι -> Submodule R A) (t : Submodule R A) : (⨆ i, s i) * t = ⨆
 i, s i * t
参数：s : ι -> Submodule R A；t : Submodule R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.iSup_smul`：iSup_smul {ι : Sort*} {t : ι -> Submodule R A} {N :
 Submodule R M} : (⨆ i, t i) • N = ⨆ i, t i • N
-/
theorem iSup_mul (s : ι → Submodule R A) (t : Submodule R A) : (⨆ i, s i) * t = ⨆ i, s i * t :=
  iSup_smul
/-
**Submodule.mul_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mul_iSup (t : Submodule R A) (s : ι -> Submodule R A) : (t * ⨆ i, s i) = ⨆
 i, t * s i
参数：t : Submodule R A；s : ι -> Submodule R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_iSup`：smul_iSup {ι : Sort*} {I : Submodule R A} {t : ι ->
 Submodule R M} : I • (⨆ i, t i) = ⨆ i, I • t i
-/
theorem mul_iSup (t : Submodule R A) (s : ι → Submodule R A) : (t * ⨆ i, s i) = ⨆ i, t * s i :=
  smul_iSup

/-- Sub-`R`-modules of an `R`-module form an idempotent semiring. -/
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sub-`R`-modules of an `R`-module form an idempotent semiring.
-/
instance : NonUnitalSemiring (Submodule R A) where
  __ := toAddSubmonoid_injective.semigroup _ mul_toAddSubmonoid
  zero_mul := bot_mul
  mul_zero := mul_bot
  left_distrib := mul_sup
  right_distrib := sup_mul
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (Submodule R A) ℕ where
  pow s n := npowRec n s
/-
**Submodule.mul_top_eq_top_of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mul_top_eq_top_of_mul_eq_one (h : N * P = 1) : N * ⊤ = ⊤
参数：h : N * P = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.one_mul`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst
_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (
M : Sub…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Submodule.smul_mono`：smul_mono (hij : I <= J) (hnp : N <= P) : I • N <= 
J • P
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem mul_top_eq_top_of_mul_eq_one (h : N * P = 1) : N * ⊤ = ⊤ :=
  top_unique <| by
    conv_lhs => rw [← Submodule.one_mul ⊤, ← h, mul_assoc]
    exact smul_mono le_rfl le_top
/-
**Submodule.pow_eq_npowRec** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：pow_eq_npowRec {n : Nat} : M ^ n = npowRec n M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_eq_npowRec {n : ℕ} : M ^ n = npowRec n M := rfl
/-
**Submodule.pow_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst_1 : Semiring A] [ins
t_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (M : Submodule R A), M
 ^ 0 = 1
参数：M : Submodule R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem pow_zero : M ^ 0 = 1 := rfl
/-
**Submodule.pow_succ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst_1 : Semiring A] [ins
t_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (M : Submodule R A) {n
 : ℕ}, M ^ (n + 1) = M ^ n * M
参数：M : Submodule R A；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem pow_succ {n : ℕ} : M ^ (n + 1) = M ^ n * M := rfl
/-
**Submodule.pow_add** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst_1 : Semiring A] [ins
t_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (M : Submodule R A) {m
 n : ℕ}, n ≠ 0 → M ^ (m + n) = M ^ m * M ^ n
参数：M : Submodule R A；m + n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `npowRec_add`：∀ {M : Type u} [inst : One M] [inst_1 : Semigroup M] (m n :
 ℕ),   n ≠ 0 → ∀ (a : M), 1 * a = a → npowRec (m + n) a = npowRec m a * npowRec 
n…
· 使用定理 `Submodule.one_mul`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst
_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (
M : Sub…
-/
protected theorem pow_add {m n : ℕ} (h : n ≠ 0) : M ^ (m + n) = M ^ m * M ^ n :=
  npowRec_add m n h _ M.one_mul
/-
**Submodule.pow_one** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst_1 : Semiring A] [ins
t_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (M : Submodule R A), M
 ^ 1 = M
参数：M : Submodule R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.pow_succ`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [ins
t_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] 
(M : Sub…
· 使用定理 `Submodule.pow_zero`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [ins
t_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] 
(M : Sub…
· 使用定理 `Submodule.one_mul`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst
_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (
M : Sub…
-/
protected theorem pow_one : M ^ 1 = M := by
  rw [Submodule.pow_succ, Submodule.pow_zero, Submodule.one_mul]

/-- `Submodule.pow_succ` with the right-hand side commuted. -/
/-
**Submodule.pow_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst_1 : Semiring A] [ins
t_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (M : Submodule R A) {n
 : ℕ}, n ≠ 0 → M ^ (n + 1) = M * M ^ n
参数：M : Submodule R A；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Submodule.pow_add`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst
_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (
M : Sub…
· 使用定理 `Submodule.pow_one`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst
_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (
M : Sub…

--- 原说明 ---
`Submodule.pow_succ` with the right-hand side commuted.
-/
protected theorem pow_succ' {n : ℕ} (h : n ≠ 0) : M ^ (n + 1) = M * M ^ n := by
  rw [add_comm, M.pow_add h, Submodule.pow_one]

@[simp]
/-
**Submodule.bot_pow** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst_1 : Semiring A] [ins
t_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] {n : ℕ}, n ≠ 0 → ⊥ ^ n
 = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_pow : ∀ {n : ℕ}, n ≠ 0 → (⊥ : Submodule R A) ^ n = ⊥
  | 1, _ => Submodule.pow_one _
  | n + 2, _ => by rw [Submodule.pow_succ, bot_pow n.succ_ne_zero, bot_mul]
/-
**Submodule.pow_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：pow_toAddSubmonoid {n : Nat} (h : n != 0) : (M ^ n).toAddSubmonoid = M.toA
ddSubmonoid ^ n
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.pow_succ`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [ins
t_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] 
(M : Sub…
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Submodule.mul_toAddSubmonoid`：mul_toAddSubmonoid (M N : Submodule R A) :
 (M * N).toAddSubmonoid = M.toAddSubmonoid * N.toAddSubmonoid
· 使用定理 `Submodule.pow_zero`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [ins
t_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] 
(M : Sub…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.one_mul`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst
_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (
M : Sub…
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
-/
theorem pow_toAddSubmonoid {n : ℕ} (h : n ≠ 0) : (M ^ n).toAddSubmonoid = M.toAddSubmonoid ^ n := by
  induction n with
  | zero => exact (h rfl).elim
  | succ n ih =>
    rw [Submodule.pow_succ, pow_succ, mul_toAddSubmonoid]
    cases n with
    | zero => rw [Submodule.pow_zero, pow_zero, one_mul, ← mul_toAddSubmonoid, Submodule.one_mul]
    | succ n => rw [ih n.succ_ne_zero]
/-
**Submodule.le_pow_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：le_pow_toAddSubmonoid {n : Nat} : M.toAddSubmonoid ^ n <= (M ^ n).toAddSub
monoid
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.pow_zero`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [ins
t_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] 
(M : Sub…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Submodule.le_one_toAddSubmonoid`：le_one_toAddSubmonoid : 1 <= (1 : Submo
dule R A).toAddSubmonoid
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Submodule.pow_toAddSubmonoid`：pow_toAddSubmonoid {n : Nat} (h : n != 0) 
: (M ^ n).toAddSubmonoid = M.toAddSubmonoid ^ n
-/
theorem le_pow_toAddSubmonoid {n : ℕ} : M.toAddSubmonoid ^ n ≤ (M ^ n).toAddSubmonoid := by
  obtain rfl | hn := Decidable.eq_or_ne n 0
  · rw [Submodule.pow_zero, pow_zero]
    exact le_one_toAddSubmonoid
  · exact (pow_toAddSubmonoid M hn).ge
/-
**Submodule.pow_subset_pow** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：pow_subset_pow {n : Nat} : (↑M : Set A) ^ n subseteq ↑(M ^ n : Submodule R
 A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用引理 `AddSubmonoid.pow_subset_pow`：pow_subset_pow {s : AddSubmonoid R} {n : Na
t} : (↑s : Set R) ^ n subseteq ↑(s ^ n)
· 使用定理 `Submodule.le_pow_toAddSubmonoid`：le_pow_toAddSubmonoid {n : Nat} : M.toA
ddSubmonoid ^ n <= (M ^ n).toAddSubmonoid
-/
theorem pow_subset_pow {n : ℕ} : (↑M : Set A) ^ n ⊆ ↑(M ^ n : Submodule R A) :=
  trans AddSubmonoid.pow_subset_pow (le_pow_toAddSubmonoid M)
/-
**Submodule.pow_mem_pow** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：pow_mem_pow {x : A} (hx : x in M) (n : Nat) : x ^ n in M ^ n
参数：hx : x in M；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.pow_subset_pow`：pow_subset_pow {n : Nat} : (↑M : Set A) ^ n su
bseteq ↑(M ^ n : Submodule R A)
· 使用定理 `Set.pow_mem_pow`：∀ {α : Type u_2} [inst : Monoid α] {s : Set α} {a : α} 
{n : ℕ}, a ∈ s → a ^ n ∈ s ^ n
-/
theorem pow_mem_pow {x : A} (hx : x ∈ M) (n : ℕ) : x ^ n ∈ M ^ n :=
  pow_subset_pow _ <| Set.pow_mem_pow hx
/-
**Submodule.restrictScalars_pow** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_pow {A B C : Type*} [Semiring A] [Semiring B] [Semiring C]
 [SMul A B] [Module A C] [Module B C] [IsScalarTower A C C] [IsScalarTower B C C
] [IsScalarTower A B C] {I : Submodule B C} : forall {n : Nat}, (hn : n != 0) ->
 (I ^ n).restrictScalars A = I.restrictScalars A ^ n | 1, _ => by simp [Submodul
e.pow_one] | n + 2, _ => by simp [Submodule.pow_succ (n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalars_pow {A B C : Type*} [Semiring A] [Semiring B]
    [Semiring C] [SMul A B] [Module A C] [Module B C]
    [IsScalarTower A C C] [IsScalarTower B C C] [IsScalarTower A B C]
    {I : Submodule B C} :
    ∀ {n : ℕ}, (hn : n ≠ 0) → (I ^ n).restrictScalars A = I.restrictScalars A ^ n
  | 1, _ => by simp [Submodule.pow_one]
  | n + 2, _ => by
    simp [Submodule.pow_succ (n := n + 1), restrictScalars_mul, restrictScalars_pow n.succ_ne_zero]
/-
**Submodule.instIsReduced** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：instIsReduced [IsReduced A] : IsReduced (Submodule R A) where eq_zero M hM
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.zero_eq_bot`：zero_eq_bot : (0 : Submodule R M) = ⊥
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.pow_mem_pow`：pow_mem_pow {x : A} (hx : x in M) (n : Nat) : x ^
 n in M ^ n
-/
instance instIsReduced [IsReduced A] : IsReduced (Submodule R A) where
  eq_zero M hM := by
    rw [Submodule.zero_eq_bot, Submodule.eq_bot_iff]
    rintro m hm
    obtain ⟨n, hn⟩ := hM
    exact eq_zero_of_pow_eq_zero <| (M ^ n).eq_bot_iff.mp hn _ (pow_mem_pow M hm n)
/-
**Submodule.pow_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：pow_eq_bot [IsReduced A] {M : Submodule R A} {n : Nat} (hn : n != 0) : M ^
 n = ⊥ ↔ M = ⊥
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.bot_pow`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst
_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] {
n : ℕ},…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pow_eq_bot [IsReduced A] {M : Submodule R A} {n : ℕ} (hn : n ≠ 0) :
    M ^ n = ⊥ ↔ M = ⊥ := by refine ⟨eq_zero_of_pow_eq_zero, by aesop⟩

end Module

variable {ι : Sort uι}
variable {R : Type u} [CommSemiring R]

section AlgebraSemiring

variable {A : Type v} [Semiring A] [Algebra R A]
variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

/-
**Submodule.one_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：one_eq_range : (1 : Submodule R A) = LinearMap.range (Algebra.linearMap R 
A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.one_eq_span`：one_eq_span : (1 : Submodule R A) = R ∙ 1
· 使用定理 `LinearMap.span_singleton_eq_range`：span_singleton_eq_range (x : M) : R ∙
 x = range (toSpanSingleton R M x)
· 使用定理 `LinearMap.toSpanSingleton_one_eq_algebraLinearMap`：toSpanSingleton_one_e
q_algebraLinearMap : toSpanSingleton R A 1 = Algebra.linearMap R A
-/
theorem one_eq_range : (1 : Submodule R A) = LinearMap.range (Algebra.linearMap R A) := by
  rw [one_eq_span, LinearMap.span_singleton_eq_range,
    LinearMap.toSpanSingleton_one_eq_algebraLinearMap]
/-
**Submodule.algebraMap_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：algebraMap_mem (r : R) : algebraMap R A r in (1 : Submodule R A)
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.one_eq_range`：one_eq_range : (1 : Submodule R A) = LinearMap.r
ange (Algebra.linearMap R A)
-/
theorem algebraMap_mem (r : R) : algebraMap R A r ∈ (1 : Submodule R A) := by
  simp [one_eq_range]

@[simp]
/-
**Submodule.mem_one** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y, algebraMap R A y = 
x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.one_eq_range`：one_eq_range : (1 : Submodule R A) = LinearMap.r
ange (Algebra.linearMap R A)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_one {x : A} : x ∈ (1 : Submodule R A) ↔ ∃ y, algebraMap R A y = x := by
  simp [one_eq_range]
/-
**Submodule.smul_one_eq_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_one_eq_span (x : A) : x • (1 : Submodule R A) = span R {x}
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.one_eq_span`：one_eq_span : (1 : Submodule R A) = R ∙ 1
· 使用定理 `Submodule.smul_span`：smul_span (a : α) (s : Set M) : a • span R s = span
 R (a • s)
· 使用引理 `Set.smul_set_singleton`：smul_set_singleton : a • ({b} : Set β) = {a • b}
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem smul_one_eq_span (x : A) : x • (1 : Submodule R A) = span R {x} := by
  rw [one_eq_span, smul_span, smul_set_singleton, smul_eq_mul, mul_one]
/-
**Submodule.span_singleton_algebraMap_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：span_singleton_algebraMap_of_isUnit {r : R} (h : IsUnit r) : span R {algeb
raMap R A r} = 1
参数：h : IsUnit r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.one_eq_span`：one_eq_span : (1 : Submodule R A) = R ∙ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_singleton_smul_eq`：span_singleton_smul_eq {r : R} (hr : I
sUnit r) (x : M) : R ∙ r • x = R ∙ x
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
-/
theorem span_singleton_algebraMap_of_isUnit {r : R} (h : IsUnit r) :
    span R {algebraMap R A r} = 1 := by
  conv_rhs => rw [one_eq_span, ← span_singleton_smul_eq h, ← algebraMap_eq_smul_one]
/-
**Submodule.map_one** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [inst_1 : Semiring A] 
[inst_2 : Algebra R A] {A' : Type u_1}   [inst_3 : Semiring A'] [inst_4 : Algebr
a R A'] (f : A →ₐ[R] A'), Submodule.map f.toLinearMap 1 = 1
参数：f : A →ₐ[R] A'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
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
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem map_one {A'} [Semiring A'] [Algebra R A'] (f : A →ₐ[R] A') :
    map f.toLinearMap (1 : Submodule R A) = 1 := by
  ext
  simp

@[simp]
/-
**Submodule.map_op_one** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_op_one : map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) (1 : 
Submodule R A) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_op_one :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (1 : Submodule R A) = 1 := by
  ext x
  induction x
  simp

@[simp]
/-
**Submodule.comap_op_one** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_op_one : comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) (
1 : Submodule R Aᵐᵒᵖ) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_op_one :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (1 : Submodule R Aᵐᵒᵖ) = 1 := by
  ext
  simp

@[simp]
/-
**Submodule.map_unop_one** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_unop_one : map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A
) (1 : Submodule R Aᵐᵒᵖ) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.comap_equiv_eq_map_symm`：comap_equiv_eq_map_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R₂ M₂) : K.comap (e : M ->ₛₗ[τ₁₂] M₂) = K.map (e.symm : M₂
 ->ₛₗ[τ₂₁] M)
· 使用定理 `Submodule.comap_op_one`：comap_op_one : comap (↑(opLinearEquiv R : A ≃ₗ[R
] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) (1 : Submodule R Aᵐᵒᵖ) = 1
-/
theorem map_unop_one :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (1 : Submodule R Aᵐᵒᵖ) = 1 := by
  rw [← comap_equiv_eq_map_symm, comap_op_one]

@[simp]
/-
**Submodule.comap_unop_one** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_unop_one : comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[
R] A) (1 : Submodule R A) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R M) : K.map (e : M ->ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ -
>ₛₗ[τ₂₁] M)
· 使用定理 `Submodule.map_op_one`：map_op_one : map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ
) : A ->ₗ[R] Aᵐᵒᵖ) (1 : Submodule R A) = 1
-/
theorem comap_unop_one :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (1 : Submodule R A) = 1 := by
  rw [← map_equiv_eq_comap_symm, map_op_one]
/-
**Submodule.mul_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_eq_map₂ : M * N = map₂ (LinearMap.mul R A) M N :=
  le_antisymm (mul_le.mpr fun _m hm _n ↦ apply_mem_map₂ _ hm)
    (map₂_le.mpr fun _m hm _n ↦ mul_mem_mul hm)

variable (R M N)
/-
**Submodule.span_mul_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_mul_span : span R S * span R T = span R (S * T)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mul_eq_map₂`：mul_eq_map₂ : M * N = map₂ (LinearMap.mul R A) M 
N
· 使用定理 `Submodule.map₂_span_span`：map₂_span_span (f : M ->ₗ[R] N ->ₗ[R] P) (s : 
Set M) (t : Set N) : map₂ f (span R s) (span R t) = span R (Set.image2 (fun m n 
=> f m n) s t)
-/
theorem span_mul_span : span R S * span R T = span R (S * T) := by
  rw [mul_eq_map₂]; apply map₂_span_span
/-
**Submodule.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：mul_def : M * N = span R (M * N : Set A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.span_coe_eq_restrictScalars`：span_coe_eq_restrictScalars [Semi
ring S] [SMul S R] [Module S M] [IsScalarTower S R M] : span S (p : Set M) = p.r
estrictScalars S
· 使用定理 `Submodule.restrictScalars_self`：restrictScalars_self (V : Submodule R M)
 : V.restrictScalars R = V
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_def : M * N = span R (M * N : Set A) := by simp [← span_mul_span]

variable {R} (P Q)
/-
**Submodule.mul_one** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (M : Submodule R A),   M * 1 = M
参数：M : Submodule R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.one_eq_span`：one_eq_span : (1 : Submodule R A) = R ∙ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_eq`：span_eq : span R (p : Set M) = p
· 使用定理 `Submodule.span_mul_span`：span_mul_span : span R S * span R T = span R (S
 * T)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.mul_singleton`：mul_singleton : s * {b} = (· * b) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `Submodule.span_coe_eq_restrictScalars`：span_coe_eq_restrictScalars [Semi
ring S] [SMul S R] [Module S M] [IsScalarTower S R M] : span S (p : Set M) = p.r
estrictScalars S
· 使用定理 `Submodule.restrictScalars_self`：restrictScalars_self (V : Submodule R M)
 : V.restrictScalars R = V
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem mul_one : M * 1 = M := by
  conv_lhs => rw [one_eq_span, ← span_eq M]
  rw [span_mul_span]
  simp
/-
**Submodule.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (M N : Submodule R A)   {A' : Type u_1} [inst_3 : Semirin
g A'] [inst_4 : Algebra R A'] (f : A →ₐ[R] A'),   Submodule.map f.toLinearMap (M
 * N) = Submodule.map f.toLinearMap M * Submodule.map f.toLinearMap N
参数：M N : Submodule R A；f : A →ₐ[R] A'；M * N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mul_eq_map₂`：mul_eq_map₂ : M * N = map₂ (LinearMap.mul R A) M 
N
· 使用定理 `Submodule.map_iSup`：map_iSup {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> 
Submodule R M) : map f (⨆ i, p i) = ⨆ i, map f (p i)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgHom.toLinearMap_apply`：toLinearMap_apply (p : A) : φ.toLinearMap p = 
φ p
-/
protected theorem map_mul {A'} [Semiring A'] [Algebra R A'] (f : A →ₐ[R] A') :
    map f.toLinearMap (M * N) = map f.toLinearMap M * map f.toLinearMap N :=
  calc
    map f.toLinearMap (M * N) = ⨆ i : M, (N.map (LinearMap.mul R A i)).map f.toLinearMap := by
      rw [mul_eq_map₂]; apply map_iSup
    _ = map f.toLinearMap M * map f.toLinearMap N := by
      rw [mul_eq_map₂]
      apply congr_arg sSup
      ext S
      constructor <;> rintro ⟨y, hy⟩
      · use ⟨f y, mem_map.mpr ⟨y.1, y.2, rfl⟩⟩
        refine Eq.trans ?_ hy
        ext
        simp
      · obtain ⟨y', hy', fy_eq⟩ := mem_map.mp y.2
        use ⟨y', hy'⟩
        refine Eq.trans ?_ hy
        rw [f.toLinearMap_apply] at fy_eq
        ext
        simp [fy_eq]
/-
**Submodule.map_op_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_op_mul : map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) (M * 
N) = map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) N * map (↑(opLinear
Equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mul_le`：mul_le : M * N <= P ↔ forall m in M, forall n in N, m 
* n in P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_comap`：mem_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂
} : x in comap f p ↔ f x in p
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Submodule.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R M) : K.map (e : M ->ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ -
>ₛₗ[τ₂₁] M)
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
· 使用定理 `Submodule.mem_map_equiv`：mem_map_equiv {e : M ≃ₛₗ[τ₁₂] M₂} {x : M₂} : x 
in p.map (e : M ->ₛₗ[τ₁₂] M₂) ↔ e.symm x in p
-/
theorem map_op_mul :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (M * N) =
      map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) N *
        map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) M := by
  apply le_antisymm
  · simp_rw [map_le_iff_le_comap]
    refine mul_le.2 fun m hm n hn => ?_
    rw [mem_comap, map_equiv_eq_comap_symm, map_equiv_eq_comap_symm]
    change op n * op m ∈ _
    exact mul_mem_mul hn hm
  · refine mul_le.2 (MulOpposite.rec' fun m hm => MulOpposite.rec' fun n hn => ?_)
    rw [Submodule.mem_map_equiv] at hm hn ⊢
    exact mul_mem_mul hn hm
/-
**Submodule.comap_unop_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_unop_mul : comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[
R] A) (M * N) = comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) N
 * comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map_op_mul`：map_op_mul : map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ
) : A ->ₗ[R] Aᵐᵒᵖ) (M * N) = map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] A
ᵐᵒᵖ) N * m…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_unop_mul :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (M * N) =
      comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) N *
        comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) M := by
  simp_rw [← map_equiv_eq_comap_symm, map_op_mul]
/-
**Submodule.map_unop_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_unop_mul (M N : Submodule R Aᵐᵒᵖ) : map (↑(opLinearEquiv R : A ≃ₗ[R] A
ᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) (M * N) = map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm
 : Aᵐᵒᵖ ->ₗ[R] A) N * map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] 
A) M
参数：M N : Submodule R Aᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_comp`：map_comp [RingHomSurjective σ₂₃] [RingHomSurjective 
σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.com
p f : M …
· 使用定理 `Submodule.map_op_mul`：map_op_mul : map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ
) : A ->ₗ[R] Aᵐᵒᵖ) (M * N) = map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] A
ᵐᵒᵖ) N * m…
· 使用定理 `LinearEquiv.comp_coe`：comp_coe (f : M₁ ≃ₛₗ[σ₁₂] M₂) (f' : M₂ ≃ₛₗ[σ₂₃] M₃
) : (f' : M₂ ->ₛₗ[σ₂₃] M₃).comp (f : M₁ ->ₛₗ[σ₁₂] M₂) = (f.trans f' : M₁ ≃ₛₗ[σ₁₃
] M₃)
· 使用定理 `LinearEquiv.symm_trans_self`：symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.sy
mm.trans f = LinearEquiv.refl R₂ M₂
· 使用定理 `LinearEquiv.refl_toLinearMap`：refl_toLinearMap [Module R M] : (LinearEqu
iv.refl R M : M ->ₗ[R] M) = LinearMap.id
· 使用定理 `Submodule.map_id`：map_id : map (LinearMap.id : M ->ₗ[R] M) p = p
-/
theorem map_unop_mul (M N : Submodule R Aᵐᵒᵖ) :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (M * N) =
      map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) N *
        map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) M :=
  have : Function.Injective (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) :=
    LinearEquiv.injective _
  map_injective_of_injective this <| by
    rw [← map_comp, map_op_mul, ← map_comp, ← map_comp, LinearEquiv.comp_coe,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, map_id, map_id, map_id]
/-
**Submodule.comap_op_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_op_mul (M N : Submodule R Aᵐᵒᵖ) : comap (↑(opLinearEquiv R : A ≃ₗ[R]
 Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) (M * N) = comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A -
>ₗ[R] Aᵐᵒᵖ) N * comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) M
参数：M N : Submodule R Aᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.comap_equiv_eq_map_symm`：comap_equiv_eq_map_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R₂ M₂) : K.comap (e : M ->ₛₗ[τ₁₂] M₂) = K.map (e.symm : M₂
 ->ₛₗ[τ₂₁] M)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map_unop_mul`：map_unop_mul (M N : Submodule R Aᵐᵒᵖ) : map (↑(o
pLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) (M * N) = map (↑(opLinearEq
uiv R : A ≃ₗ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_op_mul (M N : Submodule R Aᵐᵒᵖ) :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (M * N) =
      comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) N *
        comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) M := by
  simp_rw [comap_equiv_eq_map_symm, map_unop_mul]

section
variable {α : Type*} [Monoid α] [DistribMulAction α A] [SMulCommClass α R A]

/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsScalarTower α A A] : IsScalarTower α (Submodule R A) (Submodule R A) where
  smul_assoc a S T := by
    rw [← S.span_eq, ← T.span_eq, smul_span, smul_eq_mul, smul_eq_mul, span_mul_span, span_mul_span,
      smul_span, smul_mul_assoc]
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass α A A] : SMulCommClass α (Submodule R A) (Submodule R A) where
  smul_comm a S T := by
    rw [← S.span_eq, ← T.span_eq, smul_span, smul_eq_mul, smul_eq_mul, span_mul_span, span_mul_span,
      smul_span, mul_smul_comm]
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass A α A] : SMulCommClass (Submodule R A) α (Submodule R A) :=
  have := SMulCommClass.symm A α A; .symm ..

end

section

open scoped Pointwise

/-- `Submodule.pointwiseNeg` distributes over multiplication.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/-
**Submodule.hasDistribPointwiseNeg** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u} →   [inst : CommSemiring R] → {A : Type u_1} → [inst_1 : Ring
 A] → [inst_2 : Algebra R A] → HasDistribNeg (Submodule R A)
参数：Submodule R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Submodule.pointwiseNeg` distributes over multiplication.

This is available as an instance in the `Pointwise` locale.
-/
protected def hasDistribPointwiseNeg {A} [Ring A] [Algebra R A] : HasDistribNeg (Submodule R A) :=
  toAddSubmonoid_injective.hasDistribNeg _ neg_toAddSubmonoid mul_toAddSubmonoid

scoped[Pointwise] attribute [instance] Submodule.hasDistribPointwiseNeg

end

section DecidableEq

/-
**Submodule.mem_span_mul_finite_of_mem_span_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：mem_span_mul_finite_of_mem_span_mul {R A} [Semiring R] [AddCommMonoid A] [
Mul A] [Module R A] {S : Set A} {S' : Set A} {x : A} (hx : x in span R (S * S'))
 : exists T T' : Finset A, ↑T subseteq S ∧ ↑T' subseteq S' ∧ x in span R (T * T'
 : Set A)
参数：hx : x in span R (S * S')。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_span_finite_of_mem_span`：mem_span_finite_of_mem_span {S : 
Set M} {x : M} (hx : x in span R S) : exists T : Finset M, ↑T subseteq S ∧ x in 
span R (T : Set M)
· 使用定理 `Finset.subset_mul`：subset_mul {s t : Set α} : ↑u subseteq s * t -> exist
s s' t' : Finset α, ↑s' subseteq s ∧ ↑t' subseteq t ∧ u subseteq s' * t'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
-/
theorem mem_span_mul_finite_of_mem_span_mul {R A} [Semiring R] [AddCommMonoid A] [Mul A]
    [Module R A] {S : Set A} {S' : Set A} {x : A} (hx : x ∈ span R (S * S')) :
    ∃ T T' : Finset A, ↑T ⊆ S ∧ ↑T' ⊆ S' ∧ x ∈ span R (T * T' : Set A) := by
  classical
  obtain ⟨U, h, hU⟩ := mem_span_finite_of_mem_span hx
  obtain ⟨T, T', hS, hS', h⟩ := Finset.subset_mul h
  use T, T', hS, hS'
  have h' : (U : Set A) ⊆ T * T' := by assumption_mod_cast
  have h'' := span_mono h' hU
  assumption

end DecidableEq

/-
**Submodule.mul_eq_span_mul_set** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mul_eq_span_mul_set (s t : Submodule R A) : s * t = span R ((s : Set A) * 
(t : Set A))
参数：s t : Submodule R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mul_eq_map₂`：mul_eq_map₂ : M * N = map₂ (LinearMap.mul R A) M 
N
· 使用定理 `Submodule.map₂_eq_span_image2`：map₂_eq_span_image2 (f : M ->ₗ[R] N ->ₗ[R
] P) (p : Submodule R M) (q : Submodule R N) : map₂ f p q = span R (Set.image2 (
fun m n => f m n) (…
-/
theorem mul_eq_span_mul_set (s t : Submodule R A) : s * t = span R ((s : Set A) * (t : Set A)) := by
  rw [mul_eq_map₂]; exact map₂_eq_span_image2 _ s t
/-
**Submodule.mem_span_mul_finite_of_mem_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：mem_span_mul_finite_of_mem_mul {P Q : Submodule R A} {x : A} (hx : x in P 
* Q) : exists T T' : Finset A, (T : Set A) subseteq P ∧ (T' : Set A) subseteq Q 
∧ x in span R (T * T' : Set A)
参数：hx : x in P * Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.mem_span_mul_finite_of_mem_span_mul`：mem_span_mul_finite_of_me
m_span_mul {R A} [Semiring R] [AddCommMonoid A] [Mul A] [Module R A] {S : Set A}
 {S' : Set A} {x : A} (hx : x in sp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_mul_span`：span_mul_span : span R S * span R T = span R (S
 * T)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_eq`：span_eq : span R (p : Set M) = p
-/
theorem mem_span_mul_finite_of_mem_mul {P Q : Submodule R A} {x : A} (hx : x ∈ P * Q) :
    ∃ T T' : Finset A, (T : Set A) ⊆ P ∧ (T' : Set A) ⊆ Q ∧ x ∈ span R (T * T' : Set A) :=
  Submodule.mem_span_mul_finite_of_mem_span_mul
    (by rwa [← Submodule.span_eq P, ← Submodule.span_eq Q, Submodule.span_mul_span] at hx)

variable {M N P}
/-
**Submodule.mem_span_singleton_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_span_singleton_mul {x y : A} : x in span R {y} * P ↔ exists z in P, y 
* z = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mul_eq_map₂`：mul_eq_map₂ : M * N = map₂ (LinearMap.mul R A) M 
N
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Submodule.map₂_span_singleton_eq_map`：map₂_span_singleton_eq_map (f : M 
->ₗ[R] N ->ₗ[R] P) (m : M) : map₂ f (span R {m}) = map (f m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_span_singleton_mul {x y : A} : x ∈ span R {y} * P ↔ ∃ z ∈ P, y * z = x := by
  simp_rw [mul_eq_map₂, map₂_span_singleton_eq_map, mem_map, LinearMap.mul_apply_apply]
/-
**Submodule.mem_mul_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_mul_span_singleton {x y : A} : x in P * span R {y} ↔ exists z in P, z 
* y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mul_eq_map₂`：mul_eq_map₂ : M * N = map₂ (LinearMap.mul R A) M 
N
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Submodule.map₂_span_singleton_eq_map_flip`：map₂_span_singleton_eq_map_fl
ip (f : M ->ₗ[R] N ->ₗ[R] P) (s : Submodule R M) (n : N) : map₂ f s (span R {n})
 = map (f.flip n) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_mul_span_singleton {x y : A} : x ∈ P * span R {y} ↔ ∃ z ∈ P, z * y = x := by
  simp_rw [mul_eq_map₂, map₂_span_singleton_eq_map_flip, mem_map, LinearMap.flip_apply,
    LinearMap.mul_apply_apply]
/-
**Submodule.span_singleton_mul** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：span_singleton_mul {x : A} {p : Submodule R A} : Submodule.span R {x} * p 
= x • p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Submodule.mem_span_singleton_mul`：mem_span_singleton_mul {x y : A} : x i
n span R {y} * P ↔ exists z in P, y * z = x
-/
lemma span_singleton_mul {x : A} {p : Submodule R A} :
    Submodule.span R {x} * p = x • p := ext fun _ ↦ mem_span_singleton_mul
/-
**Submodule.mem_smul_iff_inv_mul_mem** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：mem_smul_iff_inv_mul_mem {S} [DivisionSemiring S] [Algebra R S] {x : S} {p
 : Submodule R S} {y : S} (hx : x != 0) : y in x • p ↔ x⁻¹ * y in p
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DistribSMul.toLinearMap_apply`：∀ (R : Type u_1) {S : Type u_3} (M : Type
 u_4) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : Distr…
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mem_smul_iff_inv_mul_mem {S} [DivisionSemiring S] [Algebra R S] {x : S} {p : Submodule R S}
    {y : S} (hx : x ≠ 0) : y ∈ x • p ↔ x⁻¹ * y ∈ p := by
  constructor
  · rintro ⟨a, ha : a ∈ p, rfl⟩; simpa [inv_mul_cancel_left₀ hx]
  · exact fun h ↦ ⟨_, h, by simp [mul_inv_cancel_left₀ hx]⟩
/-
**Submodule.mul_mem_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：mul_mem_smul_iff {S} [Ring S] [Algebra R S] {x : S} {p : Submodule R S} {y
 : S} (hx : x in nonZeroDivisors S) : x * y in x • p ↔ y in p
参数：hx : x in nonZeroDivisors S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `mul_cancel_left_mem_nonZeroDivisors`：mul_cancel_left_mem_nonZeroDivisors
 (hr : r in R⁰) : r * x = r * y ↔ x = y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mul_mem_smul_iff {S} [Ring S] [Algebra R S] {x : S} {p : Submodule R S} {y : S}
    (hx : x ∈ nonZeroDivisors S) :
    x * y ∈ x • p ↔ y ∈ p := by
  simp [mem_smul_pointwise_iff_exists, mul_cancel_left_mem_nonZeroDivisors hx]

variable (M N) in
/-
**Submodule.mul_smul_mul_eq_smul_mul_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mul_smul_mul_eq_smul_mul_smul (x y : R) : (x * y) • (M * N) = (x • M) * (y
 • N)
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_smul_mul_comm`：mul_smul_mul_comm [Mul α] [Mul β] [SMul α β] [IsScala
rTower α β β] [IsScalarTower α α β] [SMulCommClass α β β] (a b : α) (c d : β) : 
(a * b)…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.instIsScalarTower`：∀ {R : Type u} [inst : CommSemiring R] {A :
 Type v} [inst_1 : Semiring A] [inst_2 : Algebra R A] {α : Type u_1}   [inst_3 :
 Monoid α] [inst_…
· 使用定理 `Submodule.instSMulCommClass`：∀ {R : Type u} [inst : CommSemiring R] {A :
 Type v} [inst_1 : Semiring A] [inst_2 : Algebra R A] {α : Type u_1}   [inst_3 :
 Monoid α] [inst_…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem mul_smul_mul_eq_smul_mul_smul (x y : R) : (x * y) • (M * N) = (x • M) * (y • N) :=
  mul_smul_mul_comm x y M N

/-- Sub-R-modules of an R-algebra form an idempotent semiring. -/
/-
**Submodule.idemSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：idemSemiring : IdemSemiring (Submodule R A) where one_mul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.mul_one`：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [
inst_1 : Semiring A] [inst_2 : Algebra R A] (M : Submodule R A),   M * 1 = M

--- 原说明 ---
Sub-R-modules of an R-algebra form an idempotent semiring.
-/
instance idemSemiring : IdemSemiring (Submodule R A) where
  one_mul := Submodule.one_mul
  mul_one := Submodule.mul_one
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedRing (Submodule R A) where

variable (M)
/-
**Submodule.span_pow** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (s : Set A) (n : ℕ),   Submodule.span R s ^ n = Submodule
.span R (s ^ n)
参数：s : Set A；n : ℕ；s ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem span_pow (s : Set A) : ∀ n : ℕ, span R s ^ n = span R (s ^ n)
  | 0 => by rw [pow_zero, pow_zero, one_eq_span_one_set]
  | n + 1 => by rw [pow_succ, pow_succ, span_pow s n, span_mul_span]
/-
**Submodule.pow_eq_span_pow_set** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：pow_eq_span_pow_set (n : Nat) : M ^ n = span R ((M : Set A) ^ n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_pow`：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (s : Set A) (n : ℕ),   Submodule.sp
an R s ^…
· 使用定理 `Submodule.span_eq`：span_eq : span R (p : Set M) = p
-/
theorem pow_eq_span_pow_set (n : ℕ) : M ^ n = span R ((M : Set A) ^ n) := by
  rw [← span_pow, span_eq]
/-
**Submodule.top_mul_eq_top_of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：top_mul_eq_top_of_mul_eq_one (h : N * P = 1) : ⊤ * P = ⊤
参数：h : N * P = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Submodule.smul_mono_left`：smul_mono_left (h : I <= J) : I • N <= J • N
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem top_mul_eq_top_of_mul_eq_one (h : N * P = 1) : ⊤ * P = ⊤ :=
  top_unique <| by
    conv_lhs => rw [← mul_one ⊤, ← h, ← mul_assoc]
    exact smul_mono_left le_top

/-- Dependent version of `Submodule.pow_induction_on_left`. -/
@[elab_as_elim]
/-
**Submodule.pow_induction_on_left'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (M : Submodule R A)   {C : (n : ℕ) → (x : A) → x ∈ M ^ n 
→ Prop},   (∀ (r : R), C 0 ((algebraMap R A) r) ⋯) →     (∀ (x y : A) (i : ℕ) (h
x : x ∈ M ^ i) (hy : y ∈ M ^ i), C i x hx → C i y hy → C i (x + y) ⋯) →       (∀
 (m : A) (hm : m ∈ M) (i : ℕ) (x : A) (hx : x ∈ M ^ i), C i x hx → C i.succ (m *
 x) ⋯) →         ∀ {n : ℕ} {x : A} (hx : x ∈ M ^ n), C n x hx
参数：M : Submodule R A；n : ℕ；x : A；∀ (r : R), C 0 ((algebraMap R A) r) ⋯；∀ (x y : 
A) (i : ℕ) (hx : x ∈ M ^ i) (hy : y ∈ M ^ i), C i x hx → C i y hy → C i (x + y) 
⋯；∀ (m : A) (hm : m ∈ M) (i : ℕ) (x : A) (hx : x ∈ M ^ i), C i x hx → C i.succ (
m * x) ⋯；hx : x ∈ M ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.algebraMap_mem`：algebraMap_mem (r : R) : algebraMap R A r in (
1 : Submodule R A)
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_one`：mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y
, algebraMap R A y = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Submodule.mul_induction_on'`：∀ {R : Type u} [inst : Semiring R] {A : Typ
e v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTowe
r R A A] {M N : S…

--- 原说明 ---
Dependent version of `Submodule.pow_induction_on_left`.
-/
protected theorem pow_induction_on_left' {C : ∀ (n : ℕ) (x), x ∈ M ^ n → Prop}
    (algebraMap : ∀ r : R, C 0 (algebraMap _ _ r) (algebraMap_mem r))
    (add : ∀ x y i hx hy, C i x hx → C i y hy → C i (x + y) (add_mem ‹_› ‹_›))
    (mem_mul : ∀ m (hm : m ∈ M), ∀ (i x hx), C i x hx → C i.succ (m * x)
      ((pow_succ' M i).symm ▸ (mul_mem_mul hm hx)))
    {n : ℕ} {x : A}
    (hx : x ∈ M ^ n) : C n x hx := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero] at hx
    obtain ⟨r, rfl⟩ := mem_one.mp hx
    exact algebraMap r
  | succ n n_ih =>
    revert hx
    simp_rw [pow_succ']
    exact fun hx ↦ Submodule.mul_induction_on' (fun m hm x ih => mem_mul _ hm _ _ _ (n_ih ih))
      (fun x hx y hy Cx Cy => add _ _ _ _ _ Cx Cy) hx

/-- Dependent version of `Submodule.pow_induction_on_right`. -/
@[elab_as_elim]
/-
**Submodule.pow_induction_on_right'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (M : Submodule R A)   {C : (n : ℕ) → (x : A) → x ∈ M ^ n 
→ Prop},   (∀ (r : R), C 0 ((algebraMap R A) r) ⋯) →     (∀ (x y : A) (i : ℕ) (h
x : x ∈ M ^ i) (hy : y ∈ M ^ i), C i x hx → C i y hy → C i (x + y) ⋯) →       (∀
 (i : ℕ) (x : A) (hx : x ∈ M ^ i), C i x hx → ∀ (m : A) (hm : m ∈ M), C i.succ (
x * m) ⋯) →         ∀ {n : ℕ} {x : A} (hx : x ∈ M ^ n), C n x hx
参数：M : Submodule R A；n : ℕ；x : A；∀ (r : R), C 0 ((algebraMap R A) r) ⋯；∀ (x y : 
A) (i : ℕ) (hx : x ∈ M ^ i) (hy : y ∈ M ^ i), C i x hx → C i y hy → C i (x + y) 
⋯；∀ (i : ℕ) (x : A) (hx : x ∈ M ^ i), C i x hx → ∀ (m : A) (hm : m ∈ M), C i.suc
c (x * m) ⋯；hx : x ∈ M ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.algebraMap_mem`：algebraMap_mem (r : R) : algebraMap R A r in (
1 : Submodule R A)
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_one`：mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y
, algebraMap R A y = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Submodule.mul_induction_on'`：∀ {R : Type u} [inst : Semiring R] {A : Typ
e v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTowe
r R A A] {M N : S…

--- 原说明 ---
Dependent version of `Submodule.pow_induction_on_right`.
-/
protected theorem pow_induction_on_right' {C : ∀ (n : ℕ) (x), x ∈ M ^ n → Prop}
    (algebraMap : ∀ r : R, C 0 (algebraMap _ _ r) (algebraMap_mem r))
    (add : ∀ x y i hx hy, C i x hx → C i y hy → C i (x + y) (add_mem ‹_› ‹_›))
    (mul_mem :
      ∀ i x hx, C i x hx →
        ∀ m (hm : m ∈ M), C i.succ (x * m) (mul_mem_mul hx hm))
    {n : ℕ} {x : A} (hx : x ∈ M ^ n) : C n x hx := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero] at hx
    obtain ⟨r, rfl⟩ := mem_one.mp hx
    exact algebraMap r
  | succ n n_ih =>
    revert hx
    simp_rw [pow_succ]
    exact fun hx ↦ Submodule.mul_induction_on' (fun m hm x ih => mul_mem _ _ hm (n_ih _) _ ih)
      (fun x hx y hy Cx Cy => add _ _ _ _ _ Cx Cy) hx

/-- To show a property on elements of `M ^ n` holds, it suffices to show that it holds for scalars,
is closed under addition, and holds for `m * x` where `m ∈ M` and it holds for `x` -/
@[elab_as_elim]
/-
**Submodule.pow_induction_on_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (M : Submodule R A)   {C : A → Prop},   (∀ (r : R), C ((a
lgebraMap R A) r)) →     (∀ (x y : A), C x → C y → C (x + y)) → (∀ m ∈ M, ∀ (x :
 A), C x → C (m * x)) → ∀ {x : A} {n : ℕ}, x ∈ M ^ n → C x
参数：M : Submodule R A；∀ (r : R), C ((algebraMap R A) r)；∀ (x y : A), C x → C y → 
C (x + y)；∀ m ∈ M, ∀ (x : A), C x → C (m * x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.pow_induction_on_left'`：∀ {R : Type u} [inst : CommSemiring R]
 {A : Type v} [inst_1 : Semiring A] [inst_2 : Algebra R A] (M : Submodule R A)  
 {C : (n : ℕ) → (x : A…

--- 原说明 ---
To show a property on elements of `M ^ n` holds, it suffices to show that it hol
ds for scalars,
is closed under addition, and holds for `m * x` where `m ∈ M` and it holds for `
x`
-/
protected theorem pow_induction_on_left {C : A → Prop} (hr : ∀ r : R, C (algebraMap _ _ r))
    (hadd : ∀ x y, C x → C y → C (x + y)) (hmul : ∀ m ∈ M, ∀ (x), C x → C (m * x)) {x : A} {n : ℕ}
    (hx : x ∈ M ^ n) : C x :=
  Submodule.pow_induction_on_left' M (C := fun _ a _ => C a) hr
    (fun x y _i _hx _hy => hadd x y)
    (fun _m hm _i _x _hx => hmul _ hm _) hx

/-- To show a property on elements of `M ^ n` holds, it suffices to show that it holds for scalars,
is closed under addition, and holds for `x * m` where `m ∈ M` and it holds for `x` -/
@[elab_as_elim]
/-
**Submodule.pow_induction_on_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (M : Submodule R A)   {C : A → Prop},   (∀ (r : R), C ((a
lgebraMap R A) r)) →     (∀ (x y : A), C x → C y → C (x + y)) → (∀ (x : A), C x 
→ ∀ m ∈ M, C (x * m)) → ∀ {x : A} {n : ℕ}, x ∈ M ^ n → C x
参数：M : Submodule R A；∀ (r : R), C ((algebraMap R A) r)；∀ (x y : A), C x → C y → 
C (x + y)；∀ (x : A), C x → ∀ m ∈ M, C (x * m)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.pow_induction_on_right'`：∀ {R : Type u} [inst : CommSemiring R
] {A : Type v} [inst_1 : Semiring A] [inst_2 : Algebra R A] (M : Submodule R A) 
  {C : (n : ℕ) → (x : A…

--- 原说明 ---
To show a property on elements of `M ^ n` holds, it suffices to show that it hol
ds for scalars,
is closed under addition, and holds for `x * m` where `m ∈ M` and it holds for `
x`
-/
protected theorem pow_induction_on_right {C : A → Prop} (hr : ∀ r : R, C (algebraMap _ _ r))
    (hadd : ∀ x y, C x → C y → C (x + y)) (hmul : ∀ x, C x → ∀ m ∈ M, C (x * m)) {x : A} {n : ℕ}
    (hx : x ∈ M ^ n) : C x :=
  Submodule.pow_induction_on_right' (M := M) (C := fun _ a _ => C a) hr
    (fun x y _i _hx _hy => hadd x y)
    (fun _i _x _hx => hmul _) hx

/-- `Submonoid.map` as a `RingHom`, when applied to an `AlgHom`. -/
@[simps]
/-
**Submodule.mapHom** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：mapHom {A'} [Semiring A'] [Algebra R A'] (f : A ->ₐ[R] A') : Submodule R A
 ->+* Submodule R A' where toFun
参数：f : A ->ₐ[R] A'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_one`：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [
inst_1 : Semiring A] [inst_2 : Algebra R A] {A' : Type u_1}   [inst_3 : Semiring
 A'] [i…
· 使用定理 `Submodule.map_mul`：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [
inst_1 : Semiring A] [inst_2 : Algebra R A] (M N : Submodule R A)   {A' : Type u
_1} [in…

--- 原说明 ---
`Submonoid.map` as a `RingHom`, when applied to an `AlgHom`.
-/
def mapHom {A'} [Semiring A'] [Algebra R A'] (f : A →ₐ[R] A') :
    Submodule R A →+* Submodule R A' where
  toFun := map f.toLinearMap
  map_zero' := Submodule.map_bot _
  map_add' := (Submodule.map_sup · · _)
  map_one' := Submodule.map_one _
  map_mul' := (Submodule.map_mul · · _)
/-
**Submodule.mapHom_id** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mapHom_id : mapHom (.id R A) = .id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Submodule.map_id`：map_id : map (LinearMap.id : M ->ₗ[R] M) p = p
-/
theorem mapHom_id : mapHom (.id R A) = .id _ := RingHom.ext map_id

/-- The ring of submodules of the opposite algebra is isomorphic to the opposite ring of
submodules. -/
@[simps apply symm_apply]
/-
**Submodule.equivOpposite** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：equivOpposite : Submodule R Aᵐᵒᵖ ≃+* (Submodule R A)ᵐᵒᵖ where toFun p
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
The ring of submodules of the opposite algebra is isomorphic to the opposite rin
g of
submodules.
-/
def equivOpposite : Submodule R Aᵐᵒᵖ ≃+* (Submodule R A)ᵐᵒᵖ where
  toFun p := op <| p.comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ)
  invFun p := p.unop.comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A)
  left_inv _ := SetLike.coe_injective <| rfl
  right_inv _ := unop_injective <| SetLike.coe_injective rfl
  map_add' p q := by simp [comap_equiv_eq_map_symm, ← op_add]
  map_mul' _ _ := congr_arg op <| comap_op_mul _ _
/-
**Submodule.map_pow** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (M : Submodule R A)   {A' : Type u_1} [inst_3 : Semiring 
A'] [inst_4 : Algebra R A'] (f : A →ₐ[R] A') (n : ℕ),   Submodule.map f.toLinear
Map (M ^ n) = Submodule.map f.toLinearMap M ^ n
参数：M : Submodule R A；f : A →ₐ[R] A'；n : ℕ；M ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
protected theorem map_pow {A'} [Semiring A'] [Algebra R A'] (f : A →ₐ[R] A') (n : ℕ) :
    map f.toLinearMap (M ^ n) = map f.toLinearMap M ^ n :=
  map_pow (mapHom f) M n
/-
**Submodule.comap_unop_pow** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_unop_pow (n : Nat) : comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm :
 Aᵐᵒᵖ ->ₗ[R] A) (M ^ n) = comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ -
>ₗ[R] A) M ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.map_pow`：∀ {R : Type u_4} {S : Type u_5} [inst : Semiring R] [
inst_1 : Semiring S] (f : R ≃+* S) (a : R) (n : ℕ),   f (a ^ n) = f a ^ n
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem comap_unop_pow (n : ℕ) :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (M ^ n) =
      comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) M ^ n :=
  (equivOpposite : Submodule R Aᵐᵒᵖ ≃+* _).symm.map_pow (op M) n
/-
**Submodule.comap_op_pow** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_op_pow (n : Nat) (M : Submodule R Aᵐᵒᵖ) : comap (↑(opLinearEquiv R :
 A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) (M ^ n) = comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒ
ᵖ) : A ->ₗ[R] Aᵐᵒᵖ) M ^ n
参数：n : Nat；M : Submodule R Aᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingEquiv.map_pow`：∀ {R : Type u_4} {S : Type u_5} [inst : Semiring R] [
inst_1 : Semiring S] (f : R ≃+* S) (a : R) (n : ℕ),   f (a ^ n) = f a ^ n
-/
theorem comap_op_pow (n : ℕ) (M : Submodule R Aᵐᵒᵖ) :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (M ^ n) =
      comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) M ^ n :=
  op_injective <| (equivOpposite : Submodule R Aᵐᵒᵖ ≃+* _).map_pow M n
/-
**Submodule.map_op_pow** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_op_pow (n : Nat) : map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] A
ᵐᵒᵖ) (M ^ n) = map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) M ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Submodule.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R M) : K.map (e : M ->ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ -
>ₛₗ[τ₂₁] M)
· 使用定理 `Submodule.comap_unop_pow`：comap_unop_pow (n : Nat) : comap (↑(opLinearEq
uiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) (M ^ n) = comap (↑(opLinearEquiv R :
 A ≃ₗ[R] Aᵐᵒᵖ)…
-/
theorem map_op_pow (n : ℕ) :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (M ^ n) =
      map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) M ^ n := by
  rw [map_equiv_eq_comap_symm, map_equiv_eq_comap_symm, comap_unop_pow]
/-
**Submodule.map_unop_pow** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_unop_pow (n : Nat) (M : Submodule R Aᵐᵒᵖ) : map (↑(opLinearEquiv R : A
 ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) (M ^ n) = map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐ
ᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) M ^ n
参数：n : Nat；M : Submodule R Aᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.comap_equiv_eq_map_symm`：comap_equiv_eq_map_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R₂ M₂) : K.comap (e : M ->ₛₗ[τ₁₂] M₂) = K.map (e.symm : M₂
 ->ₛₗ[τ₂₁] M)
· 使用定理 `Submodule.comap_op_pow`：comap_op_pow (n : Nat) (M : Submodule R Aᵐᵒᵖ) : 
comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) (M ^ n) = comap (↑(opL
inearEquiv R…
-/
theorem map_unop_pow (n : ℕ) (M : Submodule R Aᵐᵒᵖ) :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (M ^ n) =
      map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) M ^ n := by
  rw [← comap_equiv_eq_map_symm, ← comap_equiv_eq_map_symm, comap_op_pow]

/-- `span` is a semiring homomorphism (recall multiplication is pointwise multiplication of subsets
on either side). -/
@[simps]
/-
**Submodule.span.ringHom** 是 Mathlib 中的一个定义，位于命名空间 `Submodule.span`。
形式化陈述：{R : Type u} →   [inst : CommSemiring R] →     {A : Type v} → [inst_1 : Se
miring A] → [inst_2 : Algebra R A] → SetSemiring A →+* Submodule R A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`span` is a semiring homomorphism (recall multiplication is pointwise multiplica
tion of subsets
on either side).
-/
noncomputable def span.ringHom : SetSemiring A →+* Submodule R A where
  toFun s := Submodule.span R (SetSemiring.down s)
  map_zero' := span_empty
  map_one' := one_eq_span.symm
  map_add' := span_union
  map_mul' s t := by simp_rw [SetSemiring.down_mul, span_mul_span]

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- `(span R {·})` as a `MonoidWithZeroHom`. -/
/-
**Submodule.spanSingleton** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：spanSingleton : A ->*₀ Submodule R A where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(span R {·})` as a `MonoidWithZeroHom`.
-/
noncomputable def spanSingleton : A →*₀ Submodule R A where
  __ := Submodule.span.ringHom.toMonoidHom.comp SetSemiring.singletonMonoidHom
  map_zero' := by simp [SetSemiring.singletonMonoidHom]
/-
**Submodule.spanSingleton_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (x : A),   (Submodule.spanSingleton R) x = R ∙ x
参数：x : A；Submodule.spanSingleton R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma spanSingleton_apply (x : A) : spanSingleton R x = Submodule.span R {x} := rfl

section FaithfulSMul

variable [FaithfulSMul R A]

/-
**Submodule.span_singleton_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_singleton_eq_one_iff {x : A} : span R {x} = 1 ↔ exists r : Rˣ, x = al
gebraMap R A r where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_one`：mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y
, algebraMap R A y = x
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `Submodule.algebraMap_mem`：algebraMap_mem (r : R) : algebraMap R A r in (
1 : Submodule R A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submodule.span_singleton_algebraMap_of_isUnit`：span_singleton_algebraMap
_of_isUnit {r : R} (h : IsUnit r) : span R {algebraMap R A r} = 1
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem span_singleton_eq_one_iff {x : A} : span R {x} = 1 ↔ ∃ r : Rˣ, x = algebraMap R A r where
  mp h := by
    obtain ⟨r, rfl⟩ := mem_one.mp (h ▸ mem_span_singleton_self x)
    have ⟨r', eq⟩ := mem_span_singleton.mp (h ▸ algebraMap_mem 1)
    rw [Algebra.smul_def, ← map_mul, (FaithfulSMul.algebraMap_injective R A).eq_iff] at eq
    exact ⟨.mkOfMulEqOne _ _ (mul_comm _ r ▸ eq), rfl⟩
  mpr := by rintro ⟨r, rfl⟩; exact span_singleton_algebraMap_of_isUnit r.isUnit
/-
**Submodule.mker_spanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mker_spanSingleton : MonoidHom.mker (Submodule.spanSingleton R) = (IsUnit.
submonoid R).map (algebraMap R A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Submodule.span_singleton_eq_one_iff`：span_singleton_eq_one_iff {x : A} :
 span R {x} = 1 ↔ exists r : Rˣ, x = algebraMap R A r where mp h
-/
theorem mker_spanSingleton :
    MonoidHom.mker (Submodule.spanSingleton R) = (IsUnit.submonoid R).map (algebraMap R A) := by
  ext; simp_rw [Submonoid.mem_map, IsUnit.mem_submonoid_iff, IsUnit, existsAndEq, true_and, eq_comm]
  exact span_singleton_eq_one_iff

/-- Exactness of the sequence `1 → Rˣ → Aˣ → (Submodule R A)ˣ → Pic R → Pic A` at `Aˣ`.
See Exercise I.3.7(iv) in [Weibel2013] or Theorem 2.4 in [RobertsSingh1993]. -/
/- Note: `assert_not_exists Submodule.hasQuotient` in `Mathlib.RingTheory.Ideal.Operations`
forbids importing `Function.MulExact` into this file. -/
/-
**Submodule.ker_unitsMap_spanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ker_unitsMap_spanSingleton : (Units.map (Submodule.spanSingleton R).toMono
idHom).ker = (Units.map (algebraMap R A).toMonoidHom).range
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.span_singleton_eq_one_iff`：span_singleton_eq_one_iff {x : A} :
 span R {x} = 1 ↔ exists r : Rˣ, x = algebraMap R A r where mp h

--- 原说明 ---
Note: `assert_not_exists Submodule.hasQuotient` in `Mathlib.RingTheory.Ideal.Ope
rations`
forbids importing `Function.MulExact` into this file.
-/
theorem ker_unitsMap_spanSingleton :
    (Units.map (Submodule.spanSingleton R).toMonoidHom).ker =
    (Units.map (algebraMap R A).toMonoidHom).range := by
  ext; simpa [Units.ext_iff, eq_comm] using span_singleton_eq_one_iff

end FaithfulSMul

section

variable {α : Type*} [Monoid α] [MulSemiringAction α A] [SMulCommClass α R A]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.

This is a stronger version of `Submodule.pointwiseDistribMulAction`. -/
@[instance_reducible]
/-
**Submodule.pointwiseMulSemiringAction** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u} →   [inst : CommSemiring R] →     {A : Type v} →       [inst_
1 : Semiring A] →         [inst_2 : Algebra R A] →           {α : Type u_1} →   
          [inst_3 : Monoid α] →               [inst_4 : MulSemiringAction α A] →
 [SMulCommClass α R A] → MulSemiringAction α (Submodule R A)
参数：Submodule R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.

This is a stronger version of `Submodule.pointwiseDistribMulAction`.
-/
protected def pointwiseMulSemiringAction : MulSemiringAction α (Submodule R A) where
  __ := Submodule.pointwiseDistribMulAction
  smul_mul r x y := Submodule.map_mul x y <| MulSemiringAction.toAlgHom R A r
  smul_one r := Submodule.map_one <| MulSemiringAction.toAlgHom R A r

scoped[Pointwise] attribute [instance] Submodule.pointwiseMulSemiringAction

end

end AlgebraSemiring

section AlgebraCommSemiring

variable {A : Type v} [CommSemiring A] [Algebra R A]
variable {M N : Submodule R A} {m n : A}

/-
**Submodule.mul_mem_mul_rev** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mul_mem_mul_rev (hm : m in M) (hn : n in N) : n * m in M * N
参数：hm : m in M；hn : n in N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mul_mem_mul_rev (hm : m ∈ M) (hn : n ∈ N) : n * m ∈ M * N :=
  mul_comm m n ▸ mul_mem_mul hm hn

variable (M N)
/-
**Submodule.mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [inst_1 : CommSemiring
 A] [inst_2 : Algebra R A]   (M N : Submodule R A), M * N = N * M
参数：M N : Submodule R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mul_le`：mul_le : M * N <= P ↔ forall m in M, forall n in N, m 
* n in P
· 使用定理 `Submodule.mul_mem_mul_rev`：mul_mem_mul_rev (hm : m in M) (hn : n in N) :
 n * m in M * N
-/
protected theorem mul_comm : M * N = N * M :=
  le_antisymm (mul_le.2 fun _r hrm _s hsn => mul_mem_mul_rev hsn hrm)
    (mul_le.2 fun _r hrn _s hsm => mul_mem_mul_rev hsm hrn)

/-- Sub-R-modules of an R-algebra A form a semiring. -/
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sub-R-modules of an R-algebra A form a semiring.
-/
instance : IdemCommSemiring (Submodule R A) :=
  { Submodule.idemSemiring with mul_comm := Submodule.mul_comm }
/-
**Submodule.prod_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prod_span {ι : Type*} (s : Finset ι) (M : ι -> Set A) : (∏ i in s, Submodu
le.span R (M i)) = Submodule.span R (∏ i in s, M i)
参数：s : Finset ι；M : ι -> Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.one_eq_span`：one_eq_span : (1 : Submodule R A) = R ∙ 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.span_mul_span`：span_mul_span : span R S * span R T = span R (S
 * T)
-/
theorem prod_span {ι : Type*} (s : Finset ι) (M : ι → Set A) :
    (∏ i ∈ s, Submodule.span R (M i)) = Submodule.span R (∏ i ∈ s, M i) := by
  let := Classical.decEq ι
  refine Finset.induction_on s ?_ ?_
  · simp [one_eq_span, Set.singleton_one]
  · intro _ _ H ih
    rw [Finset.prod_insert H, Finset.prod_insert H, ih, span_mul_span]
/-
**Submodule.prod_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prod_span_singleton {ι : Type*} (s : Finset ι) (x : ι -> A) : (∏ i in s, s
pan R ({x i} : Set A)) = span R {∏ i in s, x i}
参数：s : Finset ι；x : ι -> A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.prod_span`：prod_span {ι : Type*} (s : Finset ι) (M : ι -> Set 
A) : (∏ i in s, Submodule.span R (M i)) = Submodule.span R (∏ i in s, M i)
· 使用定理 `Set.finsetProd_singleton`：finsetProd_singleton {M ι : Type*} [CommMonoid
 M] (s : Finset ι) (I : ι -> M) : ∏ i in s, ({I i} : Set M) = {∏ i in s, I i}
-/
theorem prod_span_singleton {ι : Type*} (s : Finset ι) (x : ι → A) :
    (∏ i ∈ s, span R ({x i} : Set A)) = span R {∏ i ∈ s, x i} := by
  rw [prod_span, Set.finsetProd_singleton]

variable (R A)

/-- R-submodules of the R-algebra A are a module over `Set A`. -/
/-
**Submodule.moduleSet** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：moduleSet : Module (SetSemiring A) (Submodule R A) where smul s P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
R-submodules of the R-algebra A are a module over `Set A`.
-/
noncomputable instance moduleSet : Module (SetSemiring A) (Submodule R A) where
  smul s P := span R (SetSemiring.down s) * P
  smul_add _ _ _ := mul_add _ _ _
  add_smul s t P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_add, span_union, sup_mul, add_eq_sup]
  mul_smul s t P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_mul, ← mul_assoc, span_mul_span]
  one_smul P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_one, ← one_eq_span_one_set, one_mul]
  zero_smul P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_zero, span_empty, bot_mul, bot_eq_zero]
  smul_zero _ := mul_bot _

variable {R A}
/-
**Submodule.setSemiring_smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：setSemiring_smul_def (s : SetSemiring A) (P : Submodule R A) : s • P = spa
n R (SetSemiring.down (α
参数：s : SetSemiring A；P : Submodule R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem setSemiring_smul_def (s : SetSemiring A) (P : Submodule R A) :
    s • P = span R (SetSemiring.down (α := A) s) * P :=
  rfl
/-
**Submodule.smul_le_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_le_smul {s t : SetSemiring A} {M N : Submodule R A} (h₁ : SetSemiring
.down (α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Submodule.instMulLeftMono`：∀ {R : Type u} [inst : Semiring R] {A : Type 
v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower 
R A A], MulLeft…
· 使用定理 `Submodule.instMulRightMono`：∀ {R : Type u} [inst : Semiring R] {A : Type
 v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower
 R A A], MulRigh…
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
-/
theorem smul_le_smul {s t : SetSemiring A} {M N : Submodule R A}
    (h₁ : SetSemiring.down (α := A) s ⊆ SetSemiring.down (α := A) t)
    (h₂ : M ≤ N) : s • M ≤ t • N :=
  mul_le_mul' (span_mono h₁) h₂
/-
**Submodule.singleton_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：singleton_smul (a : A) (M : Submodule R A) : Set.up ({a} : Set A) • M = M.
map (LinearMap.mulLeft R a)
参数：a : A；M : Submodule R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_eq`：span_eq : span R (p : Set M) = p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.setSemiring_smul_def`：setSemiring_smul_def (s : SetSemiring A)
 (P : Submodule R A) : s • P = span R (SetSemiring.down (α
· 使用定理 `SetSemiring.down_up`：∀ {α : Type u_1} (s : Set α), SetSemiring.down (Set
.up s) = s
· 使用定理 `Submodule.span_mul_span`：span_mul_span : span R S * span R T = span R (S
 * T)
· 使用定理 `Set.singleton_mul`：singleton_mul : {a} * t = (a * ·) '' t
-/
theorem singleton_smul (a : A) (M : Submodule R A) :
    Set.up ({a} : Set A) • M = M.map (LinearMap.mulLeft R a) := by
  conv_lhs => rw [← span_eq M]
  rw [setSemiring_smul_def, SetSemiring.down_up, span_mul_span, singleton_mul]
  exact (map (LinearMap.mulLeft R a) M).span_eq

section Quotient

/-- The elements of `I / J` are the `x` such that `x • J ⊆ I`.

In fact, we define `x ∈ I / J` to be `∀ y ∈ J, x * y ∈ I` (see `mem_div_iff_forall_mul_mem`),
which is equivalent to `x • J ⊆ I` (see `mem_div_iff_smul_subset`), but nicer to use in proofs.

This is the general form of the ideal quotient, traditionally written $I : J$.
-/
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The elements of `I / J` are the `x` such that `x • J ⊆ I`.

In fact, we define `x ∈ I / J` to be `∀ y ∈ J, x * y ∈ I` (see `mem_div_iff_fora
ll_mul_mem`),
which is equivalent to `x • J ⊆ I` (see `mem_div_iff_smul_subset`), but nicer to
 use in proofs.

This is the general form of the ideal quotient, traditionally written $I : J$.
-/
instance : Div (Submodule R A) :=
  ⟨fun I J =>
    { carrier := { x | ∀ y ∈ J, x * y ∈ I }
      zero_mem' := fun y _ => by
        rw [zero_mul]
        apply Submodule.zero_mem
      add_mem' := fun ha hb y hy => by
        rw [add_mul]
        exact Submodule.add_mem _ (ha _ hy) (hb _ hy)
      smul_mem' := fun r x hx y hy => by
        rw [Algebra.smul_mul_assoc]
        exact Submodule.smul_mem _ _ (hx _ hy) }⟩
/-
**Submodule.mem_div_iff_forall_mul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_div_iff_forall_mul_mem {x : A} {I J : Submodule R A} : x in I / J ↔ fo
rall y in J, x * y in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.refl`：∀ (a : Prop), a ↔ a
-/
theorem mem_div_iff_forall_mul_mem {x : A} {I J : Submodule R A} : x ∈ I / J ↔ ∀ y ∈ J, x * y ∈ I :=
  Iff.refl _
/-
**Submodule.mem_div_iff_smul_subset** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_div_iff_smul_subset {x : A} {I J : Submodule R A} : x in I / J ↔ x • (
J : Set A) subseteq I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem mem_div_iff_smul_subset {x : A} {I J : Submodule R A} : x ∈ I / J ↔ x • (J : Set A) ⊆ I :=
  ⟨fun h y ⟨y', hy', xy'_eq_y⟩ => by rw [← xy'_eq_y]; exact h _ hy',
    fun h _ hy => h (Set.smul_mem_smul_set hy)⟩
/-
**Submodule.le_div_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：le_div_iff {I J K : Submodule R A} : I <= J / K ↔ forall x in I, forall z 
in K, x * z in J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.refl`：∀ (a : Prop), a ↔ a
-/
theorem le_div_iff {I J K : Submodule R A} : I ≤ J / K ↔ ∀ x ∈ I, ∀ z ∈ K, x * z ∈ J :=
  Iff.refl _
/-
**Submodule.le_div_iff_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：le_div_iff_mul_le {I J K : Submodule R A} : I <= J / K ↔ I * K <= J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.le_div_iff`：le_div_iff {I J K : Submodule R A} : I <= J / K ↔ 
forall x in I, forall z in K, x * z in J
· 使用定理 `Submodule.mul_le`：mul_le : M * N <= P ↔ forall m in M, forall n in N, m 
* n in P
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_div_iff_mul_le {I J K : Submodule R A} : I ≤ J / K ↔ I * K ≤ J := by
  rw [le_div_iff, mul_le]
/-
**Submodule.one_le_one_div** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：one_le_one_div {I : Submodule R A} : 1 <= 1 / I ↔ I <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.le_div_iff_mul_le`：le_div_iff_mul_le {I J K : Submodule R A} :
 I <= J / K ↔ I * K <= J
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_le_one_div {I : Submodule R A} : 1 ≤ 1 / I ↔ I ≤ 1 := by
  rw [le_div_iff_mul_le, one_mul]

@[simp]
/-
**Submodule.one_mem_div** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：one_mem_div {I J : Submodule R A} : 1 in I / J ↔ J <= I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.one_le`：one_le {P : Submodule R A} : (1 : Submodule R A) <= P 
↔ (1 : A) in P
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.le_div_iff_mul_le`：le_div_iff_mul_le {I J K : Submodule R A} :
 I <= J / K ↔ I * K <= J
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_mem_div {I J : Submodule R A} : 1 ∈ I / J ↔ J ≤ I := by
  rw [← one_le, le_div_iff_mul_le, one_mul]
/-
**Submodule.le_self_mul_one_div** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：le_self_mul_one_div {I : Submodule R A} (hI : I <= 1) : I <= I * (1 / I)
参数：hI : I <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `Submodule.instMulLeftMono`：∀ {R : Type u} [inst : Semiring R] {A : Type 
v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower 
R A A], MulLeft…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.one_le_one_div`：one_le_one_div {I : Submodule R A} : 1 <= 1 / 
I ↔ I <= 1
-/
theorem le_self_mul_one_div {I : Submodule R A} (hI : I ≤ 1) : I ≤ I * (1 / I) := by
  simpa using mul_le_mul_right (one_le_one_div.mpr hI) _
/-
**Submodule.mul_one_div_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mul_one_div_le_one {I : Submodule R A} : I * (1 / I) <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mul_le`：mul_le : M * N <= P ↔ forall m in M, forall n in N, m 
* n in P
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submodule.mem_div_iff_forall_mul_mem`：mem_div_iff_forall_mul_mem {x : A}
 {I J : Submodule R A} : x in I / J ↔ forall y in J, x * y in I
-/
theorem mul_one_div_le_one {I : Submodule R A} : I * (1 / I) ≤ 1 := by
  rw [Submodule.mul_le]
  intro m hm n hn
  rw [Submodule.mem_div_iff_forall_mul_mem] at hn
  rw [mul_comm]
  exact hn m hm

@[simp]
/-
**Submodule.map_div** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [inst_1 : CommSemiring
 A] [inst_2 : Algebra R A] {B : Type u_1}   [inst_3 : CommSemiring B] [inst_4 : 
Algebra R B] (I J : Submodule R A) (h : A ≃ₐ[R] B),   Submodule.map h.toLinearMa
p (I / J) = Submodule.map h.toLinearMap I / Submodule.map h.toLinearMap J
参数：I J : Submodule R A；h : A ≃ₐ[R] B；I / J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
-/
protected theorem map_div {B : Type*} [CommSemiring B] [Algebra R B] (I J : Submodule R A)
    (h : A ≃ₐ[R] B) : (I / J).map h.toLinearMap = I.map h.toLinearMap / J.map h.toLinearMap := by
  ext x
  simp only [mem_map, mem_div_iff_forall_mul_mem, AlgEquiv.toLinearMap_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨x * y, hx _ hy, map_mul h x y⟩
  · rintro hx
    refine ⟨h.symm x, fun z hz => ?_, h.apply_symm_apply x⟩
    obtain ⟨xz, xz_mem, hxz⟩ := hx (h z) ⟨z, hz, rfl⟩
    convert! xz_mem
    apply h.injective
    rw [map_mul, h.apply_symm_apply, hxz]

end Quotient

end AlgebraCommSemiring

/-
**Submodule.restrictScalars_image_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_image_smul_eq {S M : Type*} [CommSemiring S] [Algebra S R]
 [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower S R M] (s : Set S) (
N : Submodule R M) : (algebraMap S R '' s • N).restrictScalars S = s • N.restric
tScalars S
参数：s : Set S；N : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Submodule.set_smul_inductionOn`：set_smul_inductionOn {motive : (x : M) -
> (_ : x in s • N) -> Prop} (x : M) (hx : x in s • N) (smul₀ : forall ⦃r : S⦄ ⦃n
 : M⦄ (mem₁ : r in s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.restrictScalars_mem`：restrictScalars_mem (V : Submodule R M) (
m : M) : m in V.restrictScalars S ↔ m in V
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用引理 `Submodule.mem_set_smul_of_mem_mem`：mem_set_smul_of_mem_mem {r : S} {m : 
M} (mem1 : r in s) (mem2 : m in N) : r • m in s • N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Submodule.mem_set_smul`：mem_set_smul (x : M) [SMulCommClass R R N] : x i
n sR • N ↔ exists (c : R ->₀ N), (c.support : Set R) subseteq sR ∧ x = c.sum fun
 r m => r • …
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AddSubmonoidClass.coe_finsetSum`：∀ {B : Type u_3} {S : B} {ι : Type u_4}
 {M : Type u_5} [inst : AddCommMonoid M] [inst_1 : SetLike B M]   [inst_2 : AddS
ubmonoidClass B M] (f…
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Submodule.coe_mem`：coe_mem (x : p) : (x : M) in p
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用引理 `Submodule.set_smul_le`：set_smul_le (p : Submodule R M) (closed_under_smu
l : forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in N -> r • n in p) : s • N <= p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem restrictScalars_image_smul_eq {S M : Type*}
    [CommSemiring S] [Algebra S R]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower S R M]
    (s : Set S) (N : Submodule R M) :
    (algebraMap S R '' s • N).restrictScalars S = s • N.restrictScalars S := by
  refine le_antisymm (fun x x_in ↦ ?_) (set_smul_le _ _ _ fun r x r_in x_in ↦ ?_)
  · rw [restrictScalars_mem] at x_in
    refine set_smul_inductionOn x x_in ?_ ?_ (fun _ _ _ _ h h' ↦ add_mem h h') (zero_mem _)
    · rintro _ x ⟨r, r_in, rfl⟩ x_in
      rw [algebraMap_smul]
      exact mem_set_smul_of_mem_mem r_in x_in
    · intro r y h h'
      obtain ⟨c, c_supp, hc⟩ := (mem_set_smul ..).mp <| smul_mem _ r h
      simp only [hc, Finsupp.sum, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
      refine sum_mem fun u u_in ↦ ?_
      obtain ⟨u, u_in', rfl⟩ := c_supp (Finset.mem_coe.mpr u_in)
      rw [algebraMap_smul]
      exact mem_set_smul_of_mem_mem u_in' (coe_mem (c ((algebraMap S R) u)))
  · rw [restrictScalars_mem, ← algebraMap_smul R r]
    exact mem_set_smul_of_mem_mem (Set.mem_image_of_mem _ r_in) x_in

end Submodule

