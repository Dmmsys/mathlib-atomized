/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yaël Dillies
-/
module

public import Mathlib.Data.List.Iterate
public import Mathlib.Data.Set.Pairwise.List
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.Tactic.Group

/-!
# Cycle factors of a permutation

Let `β` be a `Fintype` and `f : Equiv.Perm β`.

* `Equiv.Perm.cycleOf`: `f.cycleOf x` is the cycle of `f` that `x` belongs to.
* `Equiv.Perm.cycleFactors`: `f.cycleFactors` is a list of disjoint cyclic permutations
  that multiply to `f`.
-/

@[expose] public section

open Equiv Function Finset

variable {ι α β : Type*}

namespace Equiv.Perm

/-!
### `cycleOf`
-/

section CycleOf

variable {f g : Perm α} {x y : α}

/-- `f.cycleOf x` is the cycle of the permutation `f` to which `x` belongs. -/
/-
**Equiv.Perm.cycleOf** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleOf (f : Perm α) [DecidableRel f.SameCycle] (x : α) : Perm α
参数：f : Perm α；x : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.sameCycle_apply_right`：sameCycle_apply_right : SameCycle f x 
(f y) ↔ SameCycle f x y

--- 原说明 ---
`f.cycleOf x` is the cycle of the permutation `f` to which `x` belongs.
-/
def cycleOf (f : Perm α) [DecidableRel f.SameCycle] (x : α) : Perm α :=
  ofSubtype (subtypePerm f fun _ => sameCycle_apply_right : Perm { y // SameCycle f x y })
/-
**Equiv.Perm.cycleOf_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleOf_apply (f : Perm α) [DecidableRel f.SameCycle] (x y : α) : cycleOf 
f x y = if SameCycle f x y then f y else y
参数：f : Perm α；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.sameCycle_apply_right`：sameCycle_apply_right : SameCycle f x 
(f y) ↔ SameCycle f x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_mem`：ofSubtype_apply_of_mem (f : Perm (Sub
type p)) (ha : p a) : ofSubtype f a = f ⟨a, ha⟩
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_not_mem`：ofSubtype_apply_of_not_mem (f : P
erm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a
-/
theorem cycleOf_apply (f : Perm α) [DecidableRel f.SameCycle] (x y : α) :
    cycleOf f x y = if SameCycle f x y then f y else y := by
  dsimp only [cycleOf]
  split_ifs with h
  · apply ofSubtype_apply_of_mem
    exact h
  · apply ofSubtype_apply_of_not_mem
    exact h
/-
**Equiv.Perm.cycleOf_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleOf_inv (f : Perm α) [DecidableRel f.SameCycle] (x : α) : (cycleOf f x
)⁻¹ = cycleOf f⁻¹ x
参数：f : Perm α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.inv_eq_iff_eq`：inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x =
 y ↔ x = f y
· 使用定理 `Equiv.Perm.cycleOf_apply`：cycleOf_apply (f : Perm α) [DecidableRel f.Sam
eCycle] (x y : α) : cycleOf f x y = if SameCycle f x y then f y else y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem cycleOf_inv (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
    (cycleOf f x)⁻¹ = cycleOf f⁻¹ x :=
  Equiv.ext fun y => by
    rw [inv_eq_iff_eq, cycleOf_apply, cycleOf_apply]
    split_ifs <;> simp_all [sameCycle_inv, sameCycle_symm_apply_right]

@[simp]
/-
**Equiv.Perm.cycleOf_pow_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleOf_pow_apply_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) : f
orall n : Nat, (cycleOf f x ^ n) x = (f ^ n) x
参数：f : Perm α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `Equiv.Perm.cycleOf_apply`：cycleOf_apply (f : Perm α) [DecidableRel f.Sam
eCycle] (x y : α) : cycleOf f x y = if SameCycle f x y then f y else y
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem cycleOf_pow_apply_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
    ∀ n : ℕ, (cycleOf f x ^ n) x = (f ^ n) x := by
  intro n
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ', mul_apply, cycleOf_apply, hn, if_pos, pow_succ', mul_apply]
    exact ⟨n, rfl⟩

@[simp]
/-
**Equiv.Perm.cycleOf_zpow_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleOf_zpow_apply_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) : 
forall n : Int, (cycleOf f x ^ n) x = (f ^ n) x
参数：f : Perm α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.cycleOf_pow_apply_self`：cycleOf_pow_apply_self (f : Perm α) [
DecidableRel f.SameCycle] (x : α) : forall n : Nat, (cycleOf f x ^ n) x = (f ^ n
) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Equiv.Perm.cycleOf_inv`：cycleOf_inv (f : Perm α) [DecidableRel f.SameCyc
le] (x : α) : (cycleOf f x)⁻¹ = cycleOf f⁻¹ x
-/
theorem cycleOf_zpow_apply_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
    ∀ n : ℤ, (cycleOf f x ^ n) x = (f ^ n) x := by
  intro z
  cases z with
  | ofNat z => exact cycleOf_pow_apply_self f x z
  | negSucc z =>
    rw [zpow_negSucc, ← inv_pow, cycleOf_inv, zpow_negSucc, ← inv_pow, cycleOf_pow_apply_self]
/-
**Equiv.Perm.SameCycle.cycleOf_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.SameC
ycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α} [inst : DecidableRel f.SameC
ycle], f.SameCycle x y → (f.cycleOf x) y = f y
参数：f.cycleOf x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_mem`：ofSubtype_apply_of_mem (f : Perm (Sub
type p)) (ha : p a) : ofSubtype f a = f ⟨a, ha⟩
· 使用定理 `Equiv.Perm.sameCycle_apply_right`：sameCycle_apply_right : SameCycle f x 
(f y) ↔ SameCycle f x y
-/
theorem SameCycle.cycleOf_apply [DecidableRel f.SameCycle] :
    SameCycle f x y → cycleOf f x y = f y :=
  ofSubtype_apply_of_mem _
/-
**Equiv.Perm.cycleOf_apply_of_not_sameCycle** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m`。
形式化陈述：cycleOf_apply_of_not_sameCycle [DecidableRel f.SameCycle] : ¬SameCycle f x
 y -> cycleOf f x y = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_not_mem`：ofSubtype_apply_of_not_mem (f : P
erm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a
· 使用定理 `Equiv.Perm.sameCycle_apply_right`：sameCycle_apply_right : SameCycle f x 
(f y) ↔ SameCycle f x y
-/
theorem cycleOf_apply_of_not_sameCycle [DecidableRel f.SameCycle] :
    ¬SameCycle f x y → cycleOf f x y = y :=
  ofSubtype_apply_of_not_mem _
/-
**Equiv.Perm.SameCycle.cycleOf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.SameCycl
e`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α} [inst : DecidableRel f.SameC
ycle],   f.SameCycle x y → f.cycleOf x = f.cycleOf y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleOf_apply`：cycleOf_apply (f : Perm α) [DecidableRel f.Sam
eCycle] (x y : α) : cycleOf f x y = if SameCycle f x y then f y else y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.SameCycle.cycleOf_apply`：∀ {α : Type u_2} {f : Equiv.Perm α} 
{x y : α} [inst : DecidableRel f.SameCycle], f.SameCycle x y → (f.cycleOf x) y =
 f y
· 使用定理 `Equiv.Perm.SameCycle.trans`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y z :
 α}, f.SameCycle x y → f.SameCycle y z → f.SameCycle x z
· 使用定理 `Equiv.Perm.SameCycle.symm`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α}
, f.SameCycle x y → f.SameCycle y x
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Equiv.Perm.cycleOf_apply_of_not_sameCycle`：cycleOf_apply_of_not_sameCycl
e [DecidableRel f.SameCycle] : ¬SameCycle f x y -> cycleOf f x y = y
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem SameCycle.cycleOf_eq [DecidableRel f.SameCycle] (h : SameCycle f x y) :
    cycleOf f x = cycleOf f y := by
  ext z
  rw [Equiv.Perm.cycleOf_apply]
  split_ifs with hz
  · exact (h.symm.trans hz).cycleOf_apply.symm
  · exact (cycleOf_apply_of_not_sameCycle (mt h.trans hz)).symm

@[simp]
/-
**Equiv.Perm.cycleOf_apply_apply_zpow_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
`。
形式化陈述：cycleOf_apply_apply_zpow_self (f : Perm α) [DecidableRel f.SameCycle] (x :
 α) (k : Int) : cycleOf f x ((f ^ k) x) = (f ^ (k + 1) : Perm α) x
参数：f : Perm α；x : α；k : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.SameCycle.cycleOf_apply`：∀ {α : Type u_2} {f : Equiv.Perm α} 
{x y : α} [inst : DecidableRel f.SameCycle], f.SameCycle x y → (f.cycleOf x) y =
 f y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
-/
theorem cycleOf_apply_apply_zpow_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) (k : ℤ) :
    cycleOf f x ((f ^ k) x) = (f ^ (k + 1) : Perm α) x := by
  rw [SameCycle.cycleOf_apply]
  · rw [add_comm, zpow_add, zpow_one, mul_apply]
  · exact ⟨k, rfl⟩

@[simp]
/-
**Equiv.Perm.cycleOf_apply_apply_pow_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`
。
形式化陈述：cycleOf_apply_apply_pow_self (f : Perm α) [DecidableRel f.SameCycle] (x : 
α) (k : Nat) : cycleOf f x ((f ^ k) x) = (f ^ (k + 1) : Perm α) x
参数：f : Perm α；x : α；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.cycleOf_apply_apply_zpow_self`：cycleOf_apply_apply_zpow_self 
(f : Perm α) [DecidableRel f.SameCycle] (x : α) (k : Int) : cycleOf f x ((f ^ k)
 x) = (f ^ (k + 1) : Perm α) x
-/
theorem cycleOf_apply_apply_pow_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) (k : ℕ) :
    cycleOf f x ((f ^ k) x) = (f ^ (k + 1) : Perm α) x := by
  convert! cycleOf_apply_apply_zpow_self f x k using 1

@[simp]
/-
**Equiv.Perm.cycleOf_apply_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleOf_apply_apply_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
 cycleOf f x (f x) = f (f x)
参数：f : Perm α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.cycleOf_apply_apply_pow_self`：cycleOf_apply_apply_pow_self (f
 : Perm α) [DecidableRel f.SameCycle] (x : α) (k : Nat) : cycleOf f x ((f ^ k) x
) = (f ^ (k + 1) : Perm α) x
-/
theorem cycleOf_apply_apply_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
    cycleOf f x (f x) = f (f x) := by
  convert! cycleOf_apply_apply_pow_self f x 1 using 1

@[simp]
/-
**Equiv.Perm.cycleOf_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleOf_apply_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) : cycle
Of f x x = f x
参数：f : Perm α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.cycleOf_apply`：∀ {α : Type u_2} {f : Equiv.Perm α} 
{x y : α} [inst : DecidableRel f.SameCycle], f.SameCycle x y → (f.cycleOf x) y =
 f y
· 使用定理 `Equiv.Perm.SameCycle.rfl`：∀ {α : Type u_2} {f : Equiv.Perm α} {x : α}, f
.SameCycle x x
-/
theorem cycleOf_apply_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) : cycleOf f x x = f x :=
  SameCycle.rfl.cycleOf_apply
/-
**Equiv.Perm.IsCycle.cycleOf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x : α} [inst : DecidableRel f.SameCyc
le], f.IsCycle → f x ≠ x → f.cycleOf x = f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.SameCycle.cycleOf_apply`：∀ {α : Type u_2} {f : Equiv.Perm α} 
{x y : α} [inst : DecidableRel f.SameCycle], f.SameCycle x y → (f.cycleOf x) y =
 f y
· 使用定理 `Equiv.Perm.cycleOf_apply_of_not_sameCycle`：cycleOf_apply_of_not_sameCycl
e [DecidableRel f.SameCycle] : ¬SameCycle f x y -> cycleOf f x y = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.isCycle_iff_sameCycle`：isCycle_iff_sameCycle (hx : f x != x) 
: IsCycle f ↔ forall {y}, SameCycle f x y ↔ f y != y
-/
theorem IsCycle.cycleOf_eq [DecidableRel f.SameCycle]
    (hf : IsCycle f) (hx : f x ≠ x) : cycleOf f x = f :=
  Equiv.ext fun y =>
    if h : SameCycle f x y then by rw [h.cycleOf_apply]
    else by
      rw [cycleOf_apply_of_not_sameCycle h,
        Classical.not_not.1 (mt ((isCycle_iff_sameCycle hx).1 hf).2 h)]

@[simp]
/-
**Equiv.Perm.cycleOf_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleOf_eq_one_iff (f : Perm α) [DecidableRel f.SameCycle] : cycleOf f x =
 1 ↔ f x = x
参数：f : Perm α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Equiv.Perm.cycleOf_apply`：cycleOf_apply (f : Perm α) [DecidableRel f.Sam
eCycle] (x y : α) : cycleOf f x y = if SameCycle f x y then f y else y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Equiv.Perm.SameCycle.refl`：∀ {α : Type u_2} (f : Equiv.Perm α) (x : α), 
f.SameCycle x x
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Equiv.Perm.SameCycle.apply_eq_self_iff`：∀ {α : Type u_2} {f : Equiv.Perm
 α} {x y : α}, f.SameCycle x y → (f x = x ↔ f y = y)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.iff_iff_and_or_not_and_not`：∀ {a b : Prop} [Decidable b], (a ↔
 b) ↔ a ∧ b ∨ ¬a ∧ ¬b
-/
theorem cycleOf_eq_one_iff (f : Perm α) [DecidableRel f.SameCycle] : cycleOf f x = 1 ↔ f x = x := by
  simp_rw [Perm.ext_iff, cycleOf_apply, one_apply]
  refine ⟨fun h => (if_pos (SameCycle.refl f x)).symm.trans (h x), fun h y => ?_⟩
  by_cases hy : f y = y
  · rw [hy, ite_self]
  · exact if_neg (mt SameCycle.apply_eq_self_iff (by tauto))

@[simp]
/-
**Equiv.Perm.cycleOf_self_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleOf_self_apply (f : Perm α) [DecidableRel f.SameCycle] (x : α) : cycle
Of f (f x) = cycleOf f x
参数：f : Perm α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.cycleOf_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {x 
y : α} [inst : DecidableRel f.SameCycle],   f.SameCycle x y → f.cycleOf x = f.cy
cleOf y
· 使用定理 `Equiv.Perm.SameCycle.symm`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α}
, f.SameCycle x y → f.SameCycle y x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.sameCycle_apply_right`：sameCycle_apply_right : SameCycle f x 
(f y) ↔ SameCycle f x y
· 使用定理 `Equiv.Perm.SameCycle.rfl`：∀ {α : Type u_2} {f : Equiv.Perm α} {x : α}, f
.SameCycle x x
-/
theorem cycleOf_self_apply (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
    cycleOf f (f x) = cycleOf f x :=
  (sameCycle_apply_right.2 SameCycle.rfl).symm.cycleOf_eq

@[simp]
/-
**Equiv.Perm.cycleOf_self_apply_pow** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleOf_self_apply_pow (f : Perm α) [DecidableRel f.SameCycle] (n : Nat) (
x : α) : cycleOf f ((f ^ n) x) = cycleOf f x
参数：f : Perm α；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.cycleOf_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {x 
y : α} [inst : DecidableRel f.SameCycle],   f.SameCycle x y → f.cycleOf x = f.cy
cleOf y
· 使用定理 `Equiv.Perm.SameCycle.pow_left`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y 
: α} {n : ℕ}, f.SameCycle x y → f.SameCycle ((f ^ n) x) y
· 使用定理 `Equiv.Perm.SameCycle.rfl`：∀ {α : Type u_2} {f : Equiv.Perm α} {x : α}, f
.SameCycle x x
-/
theorem cycleOf_self_apply_pow (f : Perm α) [DecidableRel f.SameCycle] (n : ℕ) (x : α) :
    cycleOf f ((f ^ n) x) = cycleOf f x :=
  SameCycle.rfl.pow_left.cycleOf_eq

@[simp]
/-
**Equiv.Perm.cycleOf_self_apply_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleOf_self_apply_zpow (f : Perm α) [DecidableRel f.SameCycle] (n : Int) 
(x : α) : cycleOf f ((f ^ n) x) = cycleOf f x
参数：f : Perm α；n : Int；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.cycleOf_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {x 
y : α} [inst : DecidableRel f.SameCycle],   f.SameCycle x y → f.cycleOf x = f.cy
cleOf y
· 使用定理 `Equiv.Perm.SameCycle.zpow_left`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y
 : α} {n : ℤ}, f.SameCycle x y → f.SameCycle ((f ^ n) x) y
· 使用定理 `Equiv.Perm.SameCycle.rfl`：∀ {α : Type u_2} {f : Equiv.Perm α} {x : α}, f
.SameCycle x x
-/
theorem cycleOf_self_apply_zpow (f : Perm α) [DecidableRel f.SameCycle] (n : ℤ) (x : α) :
    cycleOf f ((f ^ n) x) = cycleOf f x :=
  SameCycle.rfl.zpow_left.cycleOf_eq
/-
**Equiv.Perm.IsCycle.cycleOf** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x : α} [inst : DecidableRel f.SameCyc
le] [inst_1 : DecidableEq α],   f.IsCycle → f.cycleOf x = if f x = x then 1 else
 f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Equiv.Perm.cycleOf_eq_one_iff`：cycleOf_eq_one_iff (f : Perm α) [Decidabl
eRel f.SameCycle] : cycleOf f x = 1 ↔ f x = x
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Equiv.Perm.IsCycle.cycleOf_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {x : 
α} [inst : DecidableRel f.SameCycle], f.IsCycle → f x ≠ x → f.cycleOf x = f
-/
protected theorem IsCycle.cycleOf [DecidableRel f.SameCycle] [DecidableEq α]
    (hf : IsCycle f) : cycleOf f x = if f x = x then 1 else f := by
  by_cases hx : f x = x
  · rwa [if_pos hx, cycleOf_eq_one_iff]
  · rwa [if_neg hx, hf.cycleOf_eq]
/-
**Equiv.Perm.cycleOf_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleOf_one [DecidableRel (1 : Perm α).SameCycle] (x : α) : cycleOf 1 x = 
1
参数：1 : Perm α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.cycleOf_eq_one_iff`：cycleOf_eq_one_iff (f : Perm α) [Decidabl
eRel f.SameCycle] : cycleOf f x = 1 ↔ f x = x
-/
theorem cycleOf_one [DecidableRel (1 : Perm α).SameCycle] (x : α) :
    cycleOf 1 x = 1 := (cycleOf_eq_one_iff 1).mpr rfl
/-
**Equiv.Perm.isCycle_cycleOf** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCycle_cycleOf (f : Perm α) [DecidableRel f.SameCycle] (hx : f x != x) : 
IsCycle (cycleOf f x)
参数：f : Perm α；hx : f x != x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.SameCycle.cycleOf_apply`：∀ {α : Type u_2} {f : Equiv.Perm α} 
{x y : α} [inst : DecidableRel f.SameCycle], f.SameCycle x y → (f.cycleOf x) y =
 f y
· 使用定理 `Equiv.Perm.SameCycle.rfl`：∀ {α : Type u_2} {f : Equiv.Perm α} {x : α}, f
.SameCycle x x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.isCycle_iff_sameCycle`：isCycle_iff_sameCycle (hx : f x != x) 
: IsCycle f ↔ forall {y}, SameCycle f x y ↔ f y != y
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Equiv.Perm.SameCycle.apply_eq_self_iff`：∀ {α : Type u_2} {f : Equiv.Perm
 α} {x y : α}, f.SameCycle x y → (f x = x ↔ f y = y)
· 使用定理 `Equiv.Perm.cycleOf_zpow_apply_self`：cycleOf_zpow_apply_self (f : Perm α)
 [DecidableRel f.SameCycle] (x : α) : forall n : Int, (cycleOf f x ^ n) x = (f ^
 n) x
· 使用定理 `Equiv.Perm.cycleOf_apply_of_not_sameCycle`：cycleOf_apply_of_not_sameCycl
e [DecidableRel f.SameCycle] : ¬SameCycle f x y -> cycleOf f x y = y
-/
theorem isCycle_cycleOf (f : Perm α) [DecidableRel f.SameCycle] (hx : f x ≠ x) :
    IsCycle (cycleOf f x) :=
  have : cycleOf f x x ≠ x := by rwa [SameCycle.rfl.cycleOf_apply]
  (isCycle_iff_sameCycle this).2 @fun y =>
    ⟨fun h => mt h.apply_eq_self_iff.2 this, fun h =>
      if hxy : SameCycle f x y then
        let ⟨i, hi⟩ := hxy
        ⟨i, by rw [cycleOf_zpow_apply_self, hi]⟩
      else by
        rw [cycleOf_apply_of_not_sameCycle hxy] at h
        exact (h rfl).elim⟩
/-
**Equiv.Perm.pow_mod_orderOf_cycleOf_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
`。
形式化陈述：pow_mod_orderOf_cycleOf_apply (f : Perm α) [DecidableRel f.SameCycle] (n :
 Nat) (x : α) : (f ^ (n % orderOf (cycleOf f x))) x = (f ^ n) x
参数：f : Perm α；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.cycleOf_pow_apply_self`：cycleOf_pow_apply_self (f : Perm α) [
DecidableRel f.SameCycle] (x : α) : forall n : Nat, (cycleOf f x ^ n) x = (f ^ n
) x
· 使用引理 `pow_mod_orderOf`：pow_mod_orderOf (x : G) (n : Nat) : x ^ (n % orderOf x)
 = x ^ n
-/
theorem pow_mod_orderOf_cycleOf_apply (f : Perm α) [DecidableRel f.SameCycle] (n : ℕ) (x : α) :
    (f ^ (n % orderOf (cycleOf f x))) x = (f ^ n) x := by
  rw [← cycleOf_pow_apply_self f, ← cycleOf_pow_apply_self f, pow_mod_orderOf]
/-
**Equiv.Perm.cycleOf_mul_of_apply_right_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv
.Perm`。
形式化陈述：cycleOf_mul_of_apply_right_eq_self [DecidableRel f.SameCycle] [DecidableRe
l (f * g).SameCycle] (h : Commute f g) (x : α) (hx : g x = x) : (f * g).cycleOf 
x = f.cycleOf x
参数：f * g；h : Commute f g；x : α；hx : g x = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleOf_apply_apply_zpow_self`：cycleOf_apply_apply_zpow_self 
(f : Perm α) [DecidableRel f.SameCycle] (x : α) (k : Int) : cycleOf f x ((f ^ k)
 x) = (f ^ (k + 1) : Perm α) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Commute.mul_zpow`：∀ {G : Type u_1} [inst : DivisionMonoid G] {a b : G}, 
Commute a b → ∀ (n : ℤ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self`：∀ {α : Type u_1} {f : Eq
uiv.Perm α} {x : α}, f x = x → ∀ (n : ℤ), (f ^ n) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.cycleOf_apply_of_not_sameCycle`：cycleOf_apply_of_not_sameCycl
e [DecidableRel f.SameCycle] : ¬SameCycle f x y -> cycleOf f x y = y
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
-/
theorem cycleOf_mul_of_apply_right_eq_self [DecidableRel f.SameCycle]
    [DecidableRel (f * g).SameCycle]
    (h : Commute f g) (x : α) (hx : g x = x) : (f * g).cycleOf x = f.cycleOf x := by
  ext y
  by_cases hxy : (f * g).SameCycle x y
  · obtain ⟨z, rfl⟩ := hxy
    rw [cycleOf_apply_apply_zpow_self]
    simp [h.mul_zpow, zpow_apply_eq_self_of_apply_eq_self hx]
  · rw [cycleOf_apply_of_not_sameCycle hxy, cycleOf_apply_of_not_sameCycle]
    contrapose hxy
    obtain ⟨z, rfl⟩ := hxy
    refine ⟨z, ?_⟩
    simp [h.mul_zpow, zpow_apply_eq_self_of_apply_eq_self hx]
/-
**Equiv.Perm.Disjoint.cycleOf_mul_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.
Disjoint`。
形式化陈述：∀ {α : Type u_2} {f g : Equiv.Perm α} [inst : DecidableRel f.SameCycle] [i
nst_1 : DecidableRel g.SameCycle]   [inst_2 : DecidableRel (f * g).SameCycle], f
.Disjoint g → ∀ (x : α), (f * g).cycleOf x = f.cycleOf x * g.cycleOf x
参数：f * g；x : α；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.disjoint_iff_eq_or_eq`：disjoint_iff_eq_or_eq : Disjoint f g ↔
 forall x : α, f x = x ∨ g x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleOf.congr_simp`：∀ {α : Type u_2} (f f_1 : Equiv.Perm α), 
  f = f_1 →     ∀ {inst : DecidableRel f.SameCycle} [inst_1 : DecidableRel f_1.S
ameCycle] (x x_1 : …
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `Equiv.Perm.cycleOf_mul_of_apply_right_eq_self`：cycleOf_mul_of_apply_righ
t_eq_self [DecidableRel f.SameCycle] [DecidableRel (f * g).SameCycle] (h : Commu
te f g) (x : α) (hx : g x = x) : (f…
· 使用定理 `Equiv.Perm.Disjoint.symm`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Disjo
int g → g.Disjoint f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
-/
theorem Disjoint.cycleOf_mul_distrib [DecidableRel f.SameCycle] [DecidableRel g.SameCycle]
    [DecidableRel (f * g).SameCycle] (h : f.Disjoint g) (x : α) :
    (f * g).cycleOf x = f.cycleOf x * g.cycleOf x := by
  classical
  rcases (disjoint_iff_eq_or_eq.mp h) x with hfx | hgx
  · simp [h.commute.eq, cycleOf_mul_of_apply_right_eq_self h.symm.commute, hfx]
  · simp [cycleOf_mul_of_apply_right_eq_self h.commute, hgx]
/-
**Equiv.Perm.mem_support_cycleOf_iff_aux** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mem_support_cycleOf_iff_aux [DecidableRel f.SameCycle] [DecidableEq α] [Fintype α] :
    y ∈ support (f.cycleOf x) ↔ SameCycle f x y ∧ x ∈ support f := by
  by_cases hx : f x = x
  · rw [(cycleOf_eq_one_iff _).mpr hx]
    simp [hx]
  · rw [mem_support, cycleOf_apply]
    split_ifs with hy
    · simp only [hx, hy, Ne, not_false_iff, and_self_iff, mem_support]
      rcases hy with ⟨k, rfl⟩
      rw [← notMem_support]
      simpa using hx
    · simpa [hx] using hy
/-
**Equiv.Perm.mem_support_cycleOf_iff'_aux** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mem_support_cycleOf_iff'_aux (hx : f x ≠ x)
    [DecidableRel f.SameCycle] [DecidableEq α] [Fintype α] :
    y ∈ support (f.cycleOf x) ↔ SameCycle f x y := by
  rw [mem_support_cycleOf_iff_aux, and_iff_left (mem_support.2 hx)]

/-- `x` is in the support of `f` iff `Equiv.Perm.cycle_of f x` is a cycle. -/
/-
**Equiv.Perm.isCycle_cycleOf_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCycle_cycleOf_iff (f : Perm α) [DecidableRel f.SameCycle] : IsCycle (cyc
leOf f x) ↔ f x != x
参数：f : Perm α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.cycleOf_eq_one_iff`：cycleOf_eq_one_iff (f : Perm α) [Decidabl
eRel f.SameCycle] : cycleOf f x = 1 ↔ f x = x
· 使用定理 `Equiv.Perm.IsCycle.ne_one`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycl
e → f ≠ 1
· 使用定理 `Equiv.Perm.isCycle_cycleOf`：isCycle_cycleOf (f : Perm α) [DecidableRel f
.SameCycle] (hx : f x != x) : IsCycle (cycleOf f x)

--- 原说明 ---
`x` is in the support of `f` iff `Equiv.Perm.cycle_of f x` is a cycle.
-/
theorem isCycle_cycleOf_iff (f : Perm α) [DecidableRel f.SameCycle] :
    IsCycle (cycleOf f x) ↔ f x ≠ x := by
  refine ⟨fun hx => ?_, f.isCycle_cycleOf⟩
  rw [Ne, ← cycleOf_eq_one_iff f]
  exact hx.ne_one
/-
**Equiv.Perm.isCycleOn_support_cycleOf_aux** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem isCycleOn_support_cycleOf_aux [DecidableEq α] [Fintype α] (f : Perm α)
    [DecidableRel f.SameCycle] (x : α) : f.IsCycleOn (f.cycleOf x).support :=
  ⟨f.bijOn <| by
    refine fun _ ↦
        ⟨fun h ↦ mem_support_cycleOf_iff_aux.2 ?_, fun h ↦ mem_support_cycleOf_iff_aux.2 ?_⟩
    · exact ⟨sameCycle_apply_right.1 (mem_support_cycleOf_iff_aux.1 h).1,
      (mem_support_cycleOf_iff_aux.1 h).2⟩
    · exact ⟨sameCycle_apply_right.2 (mem_support_cycleOf_iff_aux.1 h).1,
      (mem_support_cycleOf_iff_aux.1 h).2⟩,
    fun a ha b hb ↦ by
      rw [mem_coe, mem_support_cycleOf_iff_aux] at ha hb
      exact ha.1.symm.trans hb.1⟩
/-
**Equiv.Perm.SameCycle.exists_pow_eq_of_mem_support_aux** 是 Mathlib 中的一个定理，位于命名空
间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem SameCycle.exists_pow_eq_of_mem_support_aux {f} [DecidableEq α] [Fintype α]
    [DecidableRel f.SameCycle] (h : SameCycle f x y) (hx : x ∈ f.support) :
    ∃ i < #(f.cycleOf x).support, (f ^ i) x = y := by
  rw [mem_support] at hx
  exact Equiv.Perm.IsCycleOn.exists_pow_eq (b := y) (f.isCycleOn_support_cycleOf_aux x)
    (by rw [mem_support_cycleOf_iff'_aux hx]) (by rwa [mem_support_cycleOf_iff'_aux hx])
/-
**Equiv.Perm.instDecidableRelSameCycle** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm`。
形式化陈述：instDecidableRelSameCycle [DecidableEq α] [Fintype α] (f : Perm α) : Decid
ableRel (SameCycle f)
参数：f : Perm α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
instance instDecidableRelSameCycle [DecidableEq α] [Fintype α] (f : Perm α) :
    DecidableRel (SameCycle f) := fun x y =>
  decidable_of_iff (y ∈ List.iterate f x (Fintype.card α)) <| by
    simp only [List.mem_iterate, iterate_eq_pow, eq_comm (a := y)]
    constructor
    · rintro ⟨n, _, hn⟩
      exact ⟨n, hn⟩
    · intro hxy
      by_cases hx : x ∈ f.support
      case pos =>
        -- we can't invoke the aux lemmas above without obtaining the decidable instance we are
        -- already building; but now we've left the data, so we can do this non-constructively
        -- without sacrificing computability.
        let _inst (f : Perm α) : DecidableRel (SameCycle f) := Classical.decRel _
        rcases hxy.exists_pow_eq_of_mem_support_aux hx with ⟨i, hixy, hi⟩
        refine ⟨i, lt_of_lt_of_le hixy (card_le_univ _), hi⟩
      case neg =>
        have : Nonempty α := ⟨x⟩
        rw [notMem_support] at hx
        exact ⟨0, Fintype.card_pos, hxy.eq_of_left hx⟩

@[simp]
/-
**Equiv.Perm.two_le_card_support_cycleOf_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Pe
rm`。
形式化陈述：two_le_card_support_cycleOf_iff [DecidableEq α] [Fintype α] : 2 <= #(cycle
Of f x).support ↔ f x != x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.cycleOf_eq_one_iff`：cycleOf_eq_one_iff (f : Perm α) [Decidabl
eRel f.SameCycle] : cycleOf f x = 1 ↔ f x = x
· 使用定理 `Equiv.Perm.support_one`：support_one : (1 : Perm α).support = ∅
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Equiv.Perm.IsCycle.two_le_card_support`：∀ {α : Type u_2} {f : Equiv.Perm
 α} [inst : DecidableEq α] [inst_1 : Fintype α], f.IsCycle → 2 ≤ f.support.card
· 使用定理 `Equiv.Perm.isCycle_cycleOf`：isCycle_cycleOf (f : Perm α) [DecidableRel f
.SameCycle] (hx : f x != x) : IsCycle (cycleOf f x)
-/
theorem two_le_card_support_cycleOf_iff [DecidableEq α] [Fintype α] :
    2 ≤ #(cycleOf f x).support ↔ f x ≠ x := by
  refine ⟨fun h => ?_, fun h => by simpa using (isCycle_cycleOf _ h).two_le_card_support⟩
  contrapose! h
  rw [← cycleOf_eq_one_iff] at h
  simp [h]
/-
**Equiv.Perm.support_cycleOf_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x : α} [inst : DecidableEq α] [inst_1
 : Fintype α],   (f.cycleOf x).support.Nonempty ↔ f x ≠ x
参数：f.cycleOf x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.two_le_card_support_cycleOf_iff`：two_le_card_support_cycleOf_
iff [DecidableEq α] [Fintype α] : 2 <= #(cycleOf f x).support ↔ f x != x
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Equiv.Perm.card_support_ne_one`：card_support_ne_one (f : Perm α) : #f.su
pport != 1
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
@[simp] lemma support_cycleOf_nonempty [DecidableEq α] [Fintype α] :
    (cycleOf f x).support.Nonempty ↔ f x ≠ x := by
  rw [← two_le_card_support_cycleOf_iff, ← card_pos, ← Nat.succ_le_iff]
  exact ⟨fun h => Or.resolve_left h.eq_or_lt (card_support_ne_one _).symm, zero_lt_two.trans_le⟩
/-
**Equiv.Perm.mem_support_cycleOf_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_support_cycleOf_iff [DecidableEq α] [Fintype α] : y in support (f.cycl
eOf x) ↔ SameCycle f x y ∧ x in support f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.GroupTheory.Perm.Cycle.Factors.0.Equiv.Perm.mem_support
_cycleOf_iff_aux`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α} [inst : Decidabl
eRel f.SameCycle] [inst_1 : DecidableEq α]   [inst_2 : Fintype α], y ∈ (f.cycl…
-/
theorem mem_support_cycleOf_iff [DecidableEq α] [Fintype α] :
    y ∈ support (f.cycleOf x) ↔ SameCycle f x y ∧ x ∈ support f :=
  mem_support_cycleOf_iff_aux
/-
**Equiv.Perm.mem_support_cycleOf_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_support_cycleOf_iff' (hx : f x != x) [DecidableEq α] [Fintype α] : y i
n support (f.cycleOf x) ↔ SameCycle f x y
参数：hx : f x != x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.GroupTheory.Perm.Cycle.Factors.0.Equiv.Perm.mem_support
_cycleOf_iff'_aux`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α},   f x ≠ x →   
  ∀ [inst : DecidableRel f.SameCycle] [inst_1 : DecidableEq α] [inst_2 : Fintyp…
-/
theorem mem_support_cycleOf_iff' (hx : f x ≠ x) [DecidableEq α] [Fintype α] :
    y ∈ support (f.cycleOf x) ↔ SameCycle f x y :=
  mem_support_cycleOf_iff'_aux hx
/-
**Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `
Equiv.Perm`。
形式化陈述：sameCycle_iff_cycleOf_eq_of_mem_support [DecidableEq α] [Fintype α] {g : P
erm α} {x y : α} (hx : x in g.support) (hy : y in g.support) : g.SameCycle x y ↔
 g.cycleOf x = g.cycleOf y
参数：hx : x in g.support；hy : y in g.support。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.cycleOf_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {x 
y : α} [inst : DecidableRel f.SameCycle],   f.SameCycle x y → f.cycleOf x = f.cy
cleOf y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.mem_support_cycleOf_iff'`：mem_support_cycleOf_iff' (hx : f x 
!= x) [DecidableEq α] [Fintype α] : y in support (f.cycleOf x) ↔ SameCycle f x y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.Perm.SameCycle.refl`：∀ {α : Type u_2} (f : Equiv.Perm α) (x : α), 
f.SameCycle x x
-/
theorem sameCycle_iff_cycleOf_eq_of_mem_support [DecidableEq α] [Fintype α]
    {g : Perm α} {x y : α} (hx : x ∈ g.support) (hy : y ∈ g.support) :
    g.SameCycle x y ↔ g.cycleOf x = g.cycleOf y := by
  refine ⟨SameCycle.cycleOf_eq, fun h ↦ ?_⟩
  rw [← mem_support_cycleOf_iff' (mem_support.mp hx), h,
    mem_support_cycleOf_iff' (mem_support.mp hy)]
/-
**Equiv.Perm.support_cycleOf_eq_nil_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_cycleOf_eq_nil_iff [DecidableEq α] [Fintype α] : (f.cycleOf x).sup
port = ∅ ↔ x ∉ f.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_cycleOf_eq_nil_iff [DecidableEq α] [Fintype α] :
    (f.cycleOf x).support = ∅ ↔ x ∉ f.support := by simp
/-
**Equiv.Perm.isCycleOn_support_cycleOf** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCycleOn_support_cycleOf [DecidableEq α] [Fintype α] (f : Perm α) (x : α)
 : f.IsCycleOn (f.cycleOf x).support
参数：f : Perm α；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.GroupTheory.Perm.Cycle.Factors.0.Equiv.Perm.isCycleOn_s
upport_cycleOf_aux`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Fintype α]
 (f : Equiv.Perm α) [inst_2 : DecidableRel f.SameCycle]   (x : α), f.IsCycleOn ↑
…
-/
theorem isCycleOn_support_cycleOf [DecidableEq α] [Fintype α] (f : Perm α) (x : α) :
    f.IsCycleOn (f.cycleOf x).support :=
  isCycleOn_support_cycleOf_aux f x
/-
**Equiv.Perm.SameCycle.exists_pow_eq_of_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `E
quiv.Perm.SameCycle`。
形式化陈述：∀ {α : Type u_2} {x y : α} {f : Equiv.Perm α} [inst : DecidableEq α] [inst
_1 : Fintype α],   f.SameCycle x y → x ∈ f.support → ∃ i < (f.cycleOf x).support
.card, (f ^ i) x = y
参数：f.cycleOf x；f ^ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.GroupTheory.Perm.Cycle.Factors.0.Equiv.Perm.SameCycle.e
xists_pow_eq_of_mem_support_aux`：∀ {α : Type u_2} {x y : α} {f : Equiv.Perm α} [
inst : DecidableEq α] [inst_1 : Fintype α]   [inst_2 : DecidableRel f.SameCycle]
, f.SameCycle…
-/
theorem SameCycle.exists_pow_eq_of_mem_support {f} [DecidableEq α] [Fintype α] (h : SameCycle f x y)
    (hx : x ∈ f.support) : ∃ i < #(f.cycleOf x).support, (f ^ i) x = y :=
  h.exists_pow_eq_of_mem_support_aux hx
/-
**Equiv.Perm.support_cycleOf_le** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_cycleOf_le [DecidableEq α] [Fintype α] (f : Perm α) (x : α) : supp
ort (f.cycleOf x) <= support f
参数：f : Perm α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Equiv.Perm.cycleOf_apply`：cycleOf_apply (f : Perm α) [DecidableRel f.Sam
eCycle] (x y : α) : cycleOf f x y = if SameCycle f x y then f y else y
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem support_cycleOf_le [DecidableEq α] [Fintype α] (f : Perm α) (x : α) :
    support (f.cycleOf x) ≤ support f := by
  intro y hy
  rw [mem_support, cycleOf_apply] at hy
  split_ifs at hy
  · exact mem_support.mpr hy
  · exact absurd rfl hy
/-
**Equiv.Perm.SameCycle.mem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Sam
eCycle`。
形式化陈述：∀ {α : Type u_2} {x y : α} {f : Equiv.Perm α} [inst : DecidableEq α] [inst
_1 : Fintype α],   f.SameCycle x y → (x ∈ f.support ↔ y ∈ f.support)
参数：x ∈ f.support ↔ y ∈ f.support。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.support_cycleOf_le`：support_cycleOf_le [DecidableEq α] [Finty
pe α] (f : Perm α) (x : α) : support (f.cycleOf x) <= support f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.mem_support_cycleOf_iff`：mem_support_cycleOf_iff [DecidableEq
 α] [Fintype α] : y in support (f.cycleOf x) ↔ SameCycle f x y ∧ x in support f
· 使用定理 `Equiv.Perm.SameCycle.symm`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α}
, f.SameCycle x y → f.SameCycle y x
-/
theorem SameCycle.mem_support_iff {f} [DecidableEq α] [Fintype α] (h : SameCycle f x y) :
    x ∈ support f ↔ y ∈ support f :=
  ⟨fun hx => support_cycleOf_le f x (mem_support_cycleOf_iff.mpr ⟨h, hx⟩), fun hy =>
    support_cycleOf_le f y (mem_support_cycleOf_iff.mpr ⟨h.symm, hy⟩)⟩
/-
**Equiv.Perm.pow_mod_card_support_cycleOf_self_apply** 是 Mathlib 中的一个定理，位于命名空间 `
Equiv.Perm`。
形式化陈述：pow_mod_card_support_cycleOf_self_apply [DecidableEq α] [Fintype α] (f : P
erm α) (n : Nat) (x : α) : (f ^ (n % #(f.cycleOf x).support)) x = (f ^ n) x
参数：f : Perm α；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.pow_apply_eq_self_of_apply_eq_self`：∀ {α : Type u_1} {f : Equ
iv.Perm α} {x : α}, f x = x → ∀ (n : ℕ), (f ^ n) x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.cycleOf_pow_apply_self`：cycleOf_pow_apply_self (f : Perm α) [
DecidableRel f.SameCycle] (x : α) : forall n : Nat, (cycleOf f x ^ n) x = (f ^ n
) x
· 使用定理 `Equiv.Perm.IsCycle.orderOf`：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : 
DecidableEq α] [inst_1 : Fintype α], f.IsCycle → orderOf f = f.support.card
· 使用定理 `Equiv.Perm.isCycle_cycleOf`：isCycle_cycleOf (f : Perm α) [DecidableRel f
.SameCycle] (hx : f x != x) : IsCycle (cycleOf f x)
· 使用引理 `pow_mod_orderOf`：pow_mod_orderOf (x : G) (n : Nat) : x ^ (n % orderOf x)
 = x ^ n
-/
theorem pow_mod_card_support_cycleOf_self_apply [DecidableEq α] [Fintype α]
    (f : Perm α) (n : ℕ) (x : α) : (f ^ (n % #(f.cycleOf x).support)) x = (f ^ n) x := by
  by_cases hx : f x = x
  · rw [pow_apply_eq_self_of_apply_eq_self hx, pow_apply_eq_self_of_apply_eq_self hx]
  · rw [← cycleOf_pow_apply_self, ← cycleOf_pow_apply_self f, ← (isCycle_cycleOf f hx).orderOf,
      pow_mod_orderOf]
/-
**Equiv.Perm.SameCycle.exists_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.SameC
ycle`。
形式化陈述：∀ {α : Type u_2} {x y : α} [inst : DecidableEq α] [inst_1 : Fintype α] (f 
: Equiv.Perm α),   f.SameCycle x y → ∃ i, 0 < i ∧ i ≤ (f.cycleOf x).support.card
 + 1 ∧ (f ^ i) x = y
参数：f : Equiv.Perm α；f.cycleOf x；f ^ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.exists_pow_eq_of_mem_support`：∀ {α : Type u_2} {x y
 : α} {f : Equiv.Perm α} [inst : DecidableEq α] [inst_1 : Fintype α],   f.SameCy
cle x y → x ∈ f.support → ∃ i < (f.cycl…
· 使用定理 `self_le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] (a b : α), a ≤ a + b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.IsCycle.orderOf`：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : 
DecidableEq α] [inst_1 : Fintype α], f.IsCycle → orderOf f = f.support.card
· 使用定理 `Equiv.Perm.isCycle_cycleOf`：isCycle_cycleOf (f : Perm α) [DecidableRel f
.SameCycle] (hx : f x != x) : IsCycle (cycleOf f x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.Perm.cycleOf_pow_apply_self`：cycleOf_pow_apply_self (f : Perm α) [
DecidableRel f.SameCycle] (x : α) : forall n : Nat, (cycleOf f x ^ n) x = (f ^ n
) x
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `Equiv.Perm.one_apply`：one_apply (x) : (1 : Perm α) x = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `Equiv.Perm.pow_apply_eq_self_of_apply_eq_self`：∀ {α : Type u_1} {f : Equ
iv.Perm α} {x : α}, f x = x → ∀ (n : ℕ), (f ^ n) x = x
（共 32 条，此处仅展示前 30 条）
-/
theorem SameCycle.exists_pow_eq [DecidableEq α] [Fintype α] (f : Perm α) (h : SameCycle f x y) :
    ∃ i : ℕ, 0 < i ∧ i ≤ #(f.cycleOf x).support + 1 ∧ (f ^ i) x = y := by
  by_cases hx : x ∈ f.support
  · obtain ⟨k, hk, hk'⟩ := h.exists_pow_eq_of_mem_support hx
    rcases k with - | k
    · refine ⟨#(f.cycleOf x).support, hk, self_le_add_right _ _, ?_⟩
      simp only [pow_zero, coe_one, id_eq] at hk'
      subst hk'
      rw [← (isCycle_cycleOf _ <| mem_support.1 hx).orderOf, ← cycleOf_pow_apply_self,
        pow_orderOf_eq_one, one_apply]
    · exact ⟨k + 1, by simp, Nat.le_succ_of_le hk.le, hk'⟩
  · refine ⟨1, zero_lt_one, by simp, ?_⟩
    obtain ⟨k, rfl⟩ := h
    rw [notMem_support] at hx
    rw [pow_apply_eq_self_of_apply_eq_self hx, zpow_apply_eq_self_of_apply_eq_self hx]
/-
**Equiv.Perm.zpow_eq_zpow_on_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：zpow_eq_zpow_on_iff [DecidableEq α] [Fintype α] (g : Perm α) {m n : Int} {
x : α} (hx : g x != x) : (g ^ m) x = (g ^ n) x ↔ m % #(g.cycleOf x).support = n 
% #(g.cycleOf x).support
参数：g : Perm α；hx : g x != x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.emod_eq_emod_iff_emod_sub_eq_zero`：∀ {m n k : ℤ}, m % n = k % n ↔ (m
 - k) % n = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.sub_add_cancel`：∀ (a b : ℤ), a - b + b = a
· 使用定理 `Int.add_comm`：∀ (a b : ℤ), a + b = b + a
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Int.dvd_iff_emod_eq_zero`：∀ {a b : ℤ}, a ∣ b ↔ b % a = 0
· 使用定理 `Equiv.Perm.cycleOf_zpow_apply_self`：cycleOf_zpow_apply_self (f : Perm α)
 [DecidableRel f.SameCycle] (x : α) : forall n : Int, (cycleOf f x ^ n) x = (f ^
 n) x
· 使用定理 `Equiv.Perm.cycle_zpow_mem_support_iff`：cycle_zpow_mem_support_iff {g : P
erm α} (hg : g.IsCycle) {n : Int} {x : α} (hx : g x != x) : (g ^ n) x = x ↔ n % 
#g.support = 0
· 使用定理 `Equiv.Perm.isCycle_cycleOf`：isCycle_cycleOf (f : Perm α) [DecidableRel f
.SameCycle] (hx : f x != x) : IsCycle (cycleOf f x)
· 使用定理 `Equiv.Perm.cycleOf_apply_self`：cycleOf_apply_self (f : Perm α) [Decidabl
eRel f.SameCycle] (x : α) : cycleOf f x x = f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zpow_eq_zpow_on_iff [DecidableEq α] [Fintype α]
    (g : Perm α) {m n : ℤ} {x : α} (hx : g x ≠ x) :
    (g ^ m) x = (g ^ n) x ↔ m % #(g.cycleOf x).support = n % #(g.cycleOf x).support := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  conv_lhs => rw [← Int.sub_add_cancel m n, Int.add_comm, zpow_add]
  simp only [coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [← Int.dvd_iff_emod_eq_zero]
  rw [← cycleOf_zpow_apply_self g x, cycle_zpow_mem_support_iff]
  · rw [← Int.dvd_iff_emod_eq_zero]
  · exact isCycle_cycleOf g hx
  · simp only [cycleOf_apply_self]; exact hx

end CycleOf


/-!
### `cycleFactors`
-/

section cycleFactors

open scoped List in
/-- Given a list `l : List α` and a permutation `f : Perm α` whose nonfixed points are all in `l`,
  recursively factors `f` into cycles. -/
/-
**Equiv.Perm.cycleFactorsAux** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleFactorsAux [DecidableEq α] [Fintype α] (l : List α) (f : Perm α) (h :
 forall {x}, f x != x -> x in l) : { pl : List (Perm α) // pl.prod = f ∧ (forall
 g in pl, IsCycle g) ∧ pl.Pairwise Disjoint }
参数：l : List α；f : Perm α；h : forall {x}, f x != x -> x in l。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a list `l : List α` and a permutation `f : Perm α` whose nonfixed points a
re all in `l`,
  recursively factors `f` into cycles.
-/
def cycleFactorsAux [DecidableEq α] [Fintype α]
    (l : List α) (f : Perm α) (h : ∀ {x}, f x ≠ x → x ∈ l) :
    { pl : List (Perm α) // pl.prod = f ∧ (∀ g ∈ pl, IsCycle g) ∧ pl.Pairwise Disjoint } :=
  go l f h (fun _ => rfl)
where
  /-- The auxiliary of `cycleFactorsAux`. This functions separates cycles from `f` instead of `g`
  to prevent the process of a cycle gets complex. -/
  go (l : List α) (g : Perm α) (hg : ∀ {x}, g x ≠ x → x ∈ l)
    (hfg : ∀ {x}, g x ≠ x → cycleOf f x = cycleOf g x) :
    { pl : List (Perm α) // pl.prod = g ∧ (∀ g' ∈ pl, IsCycle g') ∧ pl.Pairwise Disjoint } :=
  match l with
  | [] => ⟨[], by
      { simp only [imp_false, List.Pairwise.nil, List.not_mem_nil, forall_const, and_true,
          forall_prop_of_false, Classical.not_not, not_false_iff, List.prod_nil] at *
        ext
        simp [*]}⟩
  | x :: l =>
    if hx : g x = x then go l g (by
        intro y hy; exact List.mem_of_ne_of_mem (fun h => hy (by rwa [h])) (hg hy)) hfg
    else
      let ⟨m, hm⟩ :=
        go l ((cycleOf f x)⁻¹ * g) (by
            rw [hfg hx]
            intro y hy
            exact List.mem_of_ne_of_mem
              (fun h : y = x => by
                rw [h, mul_apply, Ne, inv_eq_iff_eq, cycleOf_apply_self] at hy
                exact hy rfl)
              (hg fun h : g y = y => by
                rw [mul_apply, h, Ne, inv_eq_iff_eq, cycleOf_apply] at hy
                split_ifs at hy <;> tauto))
          (by
            rw [hfg hx]
            intro y hy
            simp [symm_apply_eq, cycleOf_apply, eq_comm (a := g y)] at hy
            rw [hfg (Ne.symm hy.right), ← mul_inv_eq_one (a := g.cycleOf y), cycleOf_inv]
            simp_rw [mul_inv_rev]
            rw [inv_inv, cycleOf_mul_of_apply_right_eq_self, ← cycleOf_inv, mul_inv_eq_one]
            · rw [Commute.inv_left_iff, commute_iff_eq]
              ext z; by_cases hz : SameCycle g x z
              · simp [cycleOf_apply, hz]
              · simp [cycleOf_apply_of_not_sameCycle, hz]
            · exact cycleOf_apply_of_not_sameCycle hy.left)
      ⟨cycleOf f x :: m, by
        obtain ⟨hm₁, hm₂, hm₃⟩ := hm
        rw [hfg hx] at hm₁ ⊢
        rw [List.pairwise_cons]
        refine ⟨?_, fun g' hg' ↦ ?_, fun g' hg' y ↦ ?_, hm₃⟩
        · simp [List.prod_cons, hm₁]
        · exact ((List.mem_cons).1 hg').elim (fun hg' => hg'.symm ▸ isCycle_cycleOf _ hx) (hm₂ g')
        by_contra! ⟨hgy, hg'y⟩
        have hxy : SameCycle g x y := not_imp_comm.1 cycleOf_apply_of_not_sameCycle hgy
        have hg'm : g' :: m.erase g' ~ m := List.cons_perm_iff_perm_erase.2 ⟨hg', .refl _⟩
        have : ∀ h ∈ m.erase g', Disjoint g' h :=
          (List.pairwise_cons.1 ((hg'm.pairwise_iff Disjoint.symm).2 hm₃)).1
        refine hg'y <| (disjoint_prod_right _ this y).resolve_right ?_
        have hsc : SameCycle g⁻¹ x (g y) := by rwa [sameCycle_inv, sameCycle_apply_right]
        rw [disjoint_prod_perm hm₃ hg'm.symm, List.prod_cons, ← eq_inv_mul_iff_mul_eq] at hm₁
        simpa [hm₁, cycleOf_inv, hsc.cycleOf_apply, eq_symm_apply, eq_comm] using hg'y⟩
/-
**Equiv.Perm.mem_list_cycles_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_list_cycles_iff {α : Type*} [Finite α] {l : List (Perm α)} (h1 : foral
l σ : Perm α, σ in l -> σ.IsCycle) (h2 : l.Pairwise Disjoint) {σ : Perm α} : σ i
n l ↔ σ.IsCycle ∧ forall a, σ a != a -> σ a = l.prod a
参数：Perm α；h1 : forall σ : Perm α, σ in l -> σ.IsCycle；h2 : l.Pairwise Disjoint。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Equiv.Perm.eq_on_support_mem_disjoint`：eq_on_support_mem_disjoint {l : L
ist (Perm α)} (h : f in l) (hl : l.Pairwise Disjoint) : forall x in f.support, f
 x = l.prod x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.exists_mem_support_of_mem_support_prod`：exists_mem_support_of
_mem_support_prod {l : List (Perm α)} {x : α} (hx : x in l.prod.support) : exist
s f : Perm α, f in l ∧ x in f.support
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_of_mem_inter_left`：mem_of_mem_inter_left {a : α} {s₁ s₂ : Fin
set α} (h : a in s₁ inter s₂) : a in s₁
· 使用定理 `Finset.mem_of_mem_inter_right`：mem_of_mem_inter_right {a : α} {s₁ s₂ : F
inset α} (h : a in s₁ inter s₂) : a in s₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Equiv.Perm.IsCycle.eq_on_support_inter_nonempty_congr`：∀ {α : Type u_2} 
{f g : Equiv.Perm α} {x : α} [inst : DecidableEq α] [inst_1 : Fintype α],   f.Is
Cycle → g.IsCycle → (∀ x ∈ f.support ∩ g.su…
· 使用定理 `Finset.mem_inter_of_mem`：mem_inter_of_mem {a : α} {s₁ s₂ : Finset α} : a
 in s₁ -> a in s₂ -> a in s₁ inter s₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mem_list_cycles_iff {α : Type*} [Finite α] {l : List (Perm α)}
    (h1 : ∀ σ : Perm α, σ ∈ l → σ.IsCycle) (h2 : l.Pairwise Disjoint) {σ : Perm α} :
    σ ∈ l ↔ σ.IsCycle ∧ ∀ a, σ a ≠ a → σ a = l.prod a := by
  suffices σ.IsCycle → (σ ∈ l ↔ ∀ a, σ a ≠ a → σ a = l.prod a) by
    exact ⟨fun hσ => ⟨h1 σ hσ, (this (h1 σ hσ)).mp hσ⟩, fun hσ => (this hσ.1).mpr hσ.2⟩
  intro h3
  classical
    cases nonempty_fintype α
    constructor
    · intro h a ha
      exact eq_on_support_mem_disjoint h h2 _ (mem_support.mpr ha)
    · intro h
      have hσl : σ.support ⊆ l.prod.support := by
        intro x hx
        rw [mem_support] at hx
        rwa [mem_support, ← h _ hx]
      obtain ⟨a, ha, -⟩ := id h3
      rw [← mem_support] at ha
      obtain ⟨τ, hτ, hτa⟩ := exists_mem_support_of_mem_support_prod (hσl ha)
      have hτl : ∀ x ∈ τ.support, τ x = l.prod x := eq_on_support_mem_disjoint hτ h2
      have key : ∀ x ∈ σ.support ∩ τ.support, σ x = τ x := by
        intro x hx
        rw [h x (mem_support.mp (mem_of_mem_inter_left hx)), hτl x (mem_of_mem_inter_right hx)]
      convert! hτ
      refine h3.eq_on_support_inter_nonempty_congr (h1 _ hτ) key ?_ ha
      exact key a (mem_inter_of_mem ha hτa)

open scoped List in
/-
**Equiv.Perm.list_cycles_perm_list_cycles** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`
。
形式化陈述：list_cycles_perm_list_cycles {α : Type*} [Finite α] {l₁ l₂ : List (Perm α)
} (h₀ : l₁.prod = l₂.prod) (h₁l₁ : forall σ : Perm α, σ in l₁ -> σ.IsCycle) (h₁l
₂ : forall σ : Perm α, σ in l₂ -> σ.IsCycle) (h₂l₁ : l₁.Pairwise Disjoint) (h₂l₂
 : l₂.Pairwise Disjoint) : l₁ ~ l₂
参数：Perm α；h₀ : l₁.prod = l₂.prod；h₁l₁ : forall σ : Perm α, σ in l₁ -> σ.IsCycle；
h₁l₂ : forall σ : Perm α, σ in l₂ -> σ.IsCycle；h₂l₁ : l₁.Pairwise Disjoint；h₂l₂ 
: l₂.Pairwise Disjoint。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.perm_ext_iff_of_nodup`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Nodup 
→ l₂.Nodup → (l₁.Perm l₂ ↔ ∀ (a : α), a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `Equiv.Perm.nodup_of_pairwise_disjoint_cycles`：nodup_of_pairwise_disjoint
_cycles {l : List (Perm β)} (h1 : forall f in l, IsCycle f) (h2 : l.Pairwise Dis
joint) : l.Nodup
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.mem_list_cycles_iff`：mem_list_cycles_iff {α : Type*} [Finite 
α] {l : List (Perm α)} (h1 : forall σ : Perm α, σ in l -> σ.IsCycle) (h2 : l.Pai
rwise Disjoint) {σ :…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem list_cycles_perm_list_cycles {α : Type*} [Finite α] {l₁ l₂ : List (Perm α)}
    (h₀ : l₁.prod = l₂.prod) (h₁l₁ : ∀ σ : Perm α, σ ∈ l₁ → σ.IsCycle)
    (h₁l₂ : ∀ σ : Perm α, σ ∈ l₂ → σ.IsCycle) (h₂l₁ : l₁.Pairwise Disjoint)
    (h₂l₂ : l₂.Pairwise Disjoint) : l₁ ~ l₂ := by
  refine
    (List.perm_ext_iff_of_nodup (nodup_of_pairwise_disjoint_cycles h₁l₁ h₂l₁)
          (nodup_of_pairwise_disjoint_cycles h₁l₂ h₂l₂)).mpr
      fun σ => ?_
  by_cases hσ : σ.IsCycle
  · obtain _ := not_forall.mp (mt ext hσ.ne_one)
    rw [mem_list_cycles_iff h₁l₁ h₂l₁, mem_list_cycles_iff h₁l₂ h₂l₂, h₀]
  · exact iff_of_false (mt (h₁l₁ σ) hσ) (mt (h₁l₂ σ) hσ)

/-- Factors a permutation `f` into a list of disjoint cyclic permutations that multiply to `f`. -/
/-
**Equiv.Perm.cycleFactors** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleFactors [Fintype α] [LinearOrder α] (f : Perm α) : { l : List (Perm α
) // l.prod = f ∧ (forall g in l, IsCycle g) ∧ l.Pairwise Disjoint }
参数：f : Perm α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Factors a permutation `f` into a list of disjoint cyclic permutations that multi
ply to `f`.
-/
def cycleFactors [Fintype α] [LinearOrder α] (f : Perm α) :
    { l : List (Perm α) // l.prod = f ∧ (∀ g ∈ l, IsCycle g) ∧ l.Pairwise Disjoint } :=
  cycleFactorsAux (sort (α := α) univ) f (fun {_ _} ↦ (mem_sort _).2 (mem_univ _))

/-- Factors a permutation `f` into a list of disjoint cyclic permutations that multiply to `f`,
  without a linear order. -/
/-
**Equiv.Perm.truncCycleFactors** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：truncCycleFactors [DecidableEq α] [Fintype α] (f : Perm α) : Trunc { l : L
ist (Perm α) // l.prod = f ∧ (forall g in l, IsCycle g) ∧ l.Pairwise Disjoint }
参数：f : Perm α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Factors a permutation `f` into a list of disjoint cyclic permutations that multi
ply to `f`,
  without a linear order.
-/
def truncCycleFactors [DecidableEq α] [Fintype α] (f : Perm α) :
    Trunc { l : List (Perm α) // l.prod = f ∧ (∀ g ∈ l, IsCycle g) ∧ l.Pairwise Disjoint } :=
  Quotient.recOnSubsingleton (@univ α _).1 (fun l h => Trunc.mk (cycleFactorsAux l f (h _)))
    (show ∀ x, f x ≠ x → x ∈ (@univ α _).1 from fun _ _ => mem_univ _)

section CycleFactorsFinset

variable [DecidableEq α] [Fintype α] (f : Perm α)

/-- Factors a permutation `f` into a `Finset` of disjoint cyclic permutations that multiply to `f`.
-/
/-
**Equiv.Perm.cycleFactorsFinset** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleFactorsFinset : Finset (Perm α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Factors a permutation `f` into a `Finset` of disjoint cyclic permutations that m
ultiply to `f`.
-/
def cycleFactorsFinset : Finset (Perm α) :=
  (truncCycleFactors f).lift
    (fun l : { l : List (Perm α) // l.prod = f ∧ (∀ g ∈ l, IsCycle g) ∧ l.Pairwise Disjoint } =>
      ⟨↑l.val, nodup_of_pairwise_disjoint (fun h1 => not_isCycle_one <| l.2.2.1 _ h1) l.2.2.2⟩)
    fun ⟨_, hl⟩ ⟨_, hl'⟩ =>
    Finset.eq_of_veq <| Multiset.coe_eq_coe.mpr <|
      list_cycles_perm_list_cycles (hl'.left.symm ▸ hl.left) hl.right.left hl'.right.left
        hl.right.right hl'.right.right

set_option backward.isDefEq.respectTransparency false in
open scoped List in
/-
**Equiv.Perm.cycleFactorsFinset_eq_list_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Equi
v.Perm`。
形式化陈述：cycleFactorsFinset_eq_list_toFinset {σ : Perm α} {l : List (Perm α)} (hn :
 l.Nodup) : σ.cycleFactorsFinset = l.toFinset ↔ (forall f : Perm α, f in l -> f.
IsCycle) ∧ l.Pairwise Disjoint ∧ l.prod = σ
参数：Perm α；hn : l.Nodup。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Trunc.exists_rep`：exists_rep (q : Trunc α) : exists a : α, mk a = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleFactorsFinset.eq_1`：∀ {α : Type u_2} [inst : DecidableEq
 α] [inst_1 : Fintype α] (f : Equiv.Perm α),   f.cycleFactorsFinset = Trunc.lift
 (fun l => { val := ↑↑l,…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Trunc.lift_mk`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (c : ∀ (a b :
 α), f a = f b) (a : α), Trunc.lift f c (Trunc.mk a) = f a
· 使用定理 `Multiset.toFinset_eq`：toFinset_eq {s : Multiset α} (n : Nodup s) : Finse
t.mk s n = s.toFinset
· 使用定理 `List.toFinset_coe`：toFinset_coe (l : List α) : (l : Multiset α).toFinset
 = l.toFinset
· 使用定理 `Equiv.Perm.nodup_of_pairwise_disjoint_cycles`：nodup_of_pairwise_disjoint
_cycles {l : List (Perm β)} (h1 : forall f in l, IsCycle f) (h2 : l.Pairwise Dis
joint) : l.Nodup
· 使用定理 `List.perm_of_nodup_nodup_toFinset_eq`：perm_of_nodup_nodup_toFinset_eq (h
l : Nodup l) (hl' : Nodup l') (h : l.toFinset = l'.toFinset) : l ~ l'
· 使用定理 `List.Perm.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁ ⊆ l
₂
· 使用定理 `List.Perm.pairwise_iff`：∀ {α : Type u_1} {R : α → α → Prop},   (∀ {x y :
 α}, R x y → R y x) → ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → (List.Pairwise R l₁ ↔ Lis
t.Pairwise R…
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `Equiv.Perm.Disjoint.stdSymm`：∀ {α : Type u_1}, Std.Symm Equiv.Perm.Disjo
int
· 使用定理 `List.Perm.prod_eq'`：∀ {M : Type u_4} [inst : Monoid M] {l₁ l₂ : List M},
 l₁.Perm l₂ → List.Pairwise Commute l₁ → l₁.prod = l₂.prod
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `List.toFinset_eq_of_perm`：toFinset_eq_of_perm (l l' : List α) (h : l ~ l
') : l.toFinset = l'.toFinset
· 使用定理 `Equiv.Perm.list_cycles_perm_list_cycles`：list_cycles_perm_list_cycles {α
 : Type*} [Finite α] {l₁ l₂ : List (Perm α)} (h₀ : l₁.prod = l₂.prod) (h₁l₁ : fo
rall σ : Perm α, σ in l₁ -> σ…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem cycleFactorsFinset_eq_list_toFinset {σ : Perm α} {l : List (Perm α)} (hn : l.Nodup) :
    σ.cycleFactorsFinset = l.toFinset ↔
      (∀ f : Perm α, f ∈ l → f.IsCycle) ∧ l.Pairwise Disjoint ∧ l.prod = σ := by
  obtain ⟨⟨l', hp', hc', hd'⟩, hl⟩ := Trunc.exists_rep σ.truncCycleFactors
  have ht : cycleFactorsFinset σ = l'.toFinset := by
    rw [cycleFactorsFinset, ← hl, Trunc.lift_mk, Multiset.toFinset_eq, List.toFinset_coe]
  rw [ht]
  constructor
  · intro h
    have hn' : l'.Nodup := nodup_of_pairwise_disjoint_cycles hc' hd'
    have hperm : l ~ l' := List.perm_of_nodup_nodup_toFinset_eq hn hn' h.symm
    refine ⟨?_, ?_, ?_⟩
    · exact fun _ h => hc' _ (hperm.subset h)
    · rwa [hperm.pairwise_iff symm]
    · rw [← hp', hperm.symm.prod_eq']
      exact hd'.imp Disjoint.commute
  · rintro ⟨hc, hd, hp⟩
    refine List.toFinset_eq_of_perm _ _ ?_
    refine list_cycles_perm_list_cycles ?_ hc' hc hd' hd
    rw [hp, hp']

set_option backward.isDefEq.respectTransparency false in
/-
**Equiv.Perm.cycleFactorsFinset_eq_finset** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`
。
形式化陈述：cycleFactorsFinset_eq_finset {σ : Perm α} {s : Finset (Perm α)} : σ.cycleF
actorsFinset = s ↔ (forall f : Perm α, f in s -> f.IsCycle) ∧ exists h : (s : Se
t (Perm α)).Pairwise Disjoint, s.noncommProd id (h.mono' fun _ _ => Disjoint.com
mute) = σ
参数：Perm α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `Finset.exists_list_nodup_eq`：exists_list_nodup_eq [DecidableEq α] (s : F
inset α) : exists l : List α, l.Nodup ∧ l.toFinset = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.noncommProd_congr`：noncommProd_congr {s₁ s₂ : Finset α} {f g : α 
-> β} (h₁ : s₁ = s₂) (h₂ : forall x in s₂, f x = g x) (comm) : noncommProd s₁ f 
comm = noncomm…
· 使用定理 `Finset.noncommProd_toFinset`：noncommProd_toFinset [DecidableEq α] (l : L
ist α) (f : α -> β) (comm) (hl : l.Nodup) : noncommProd l.toFinset f comm = (l.m
ap f).prod
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun'`：∀ {α : Type u_1}, (List.map fun a => a) = id
· 使用定理 `List.coe_toFinset`：coe_toFinset (l : List α) : (l.toFinset : Set α) = { 
a | a in l }
· 使用定理 `Equiv.Perm.Disjoint.stdSymm`：∀ {α : Type u_1}, Std.Symm Equiv.Perm.Disjo
int
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cycleFactorsFinset_eq_finset {σ : Perm α} {s : Finset (Perm α)} :
    σ.cycleFactorsFinset = s ↔
      (∀ f : Perm α, f ∈ s → f.IsCycle) ∧
        ∃ h : (s : Set (Perm α)).Pairwise Disjoint,
          s.noncommProd id (h.mono' fun _ _ => Disjoint.commute) = σ := by
  obtain ⟨l, hl, rfl⟩ := s.exists_list_nodup_eq
  simp [cycleFactorsFinset_eq_list_toFinset, hl]
/-
**Equiv.Perm.cycleFactorsFinset_pairwise_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Equ
iv.Perm`。
形式化陈述：cycleFactorsFinset_pairwise_disjoint : (cycleFactorsFinset f : Set (Perm α
)).Pairwise Disjoint
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.cycleFactorsFinset_eq_finset`：cycleFactorsFinset_eq_finset {σ
 : Perm α} {s : Finset (Perm α)} : σ.cycleFactorsFinset = s ↔ (forall f : Perm α
, f in s -> f.IsCycle) ∧ exis…
-/
theorem cycleFactorsFinset_pairwise_disjoint :
    (cycleFactorsFinset f : Set (Perm α)).Pairwise Disjoint :=
  (cycleFactorsFinset_eq_finset.mp rfl).2.choose

/-- Two cycles of a permutation commute. -/
/-
**Equiv.Perm.cycleFactorsFinset_mem_commute** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m`。
形式化陈述：cycleFactorsFinset_mem_commute : (cycleFactorsFinset f : Set (Perm α)).Pai
rwise Commute
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `Equiv.Perm.cycleFactorsFinset_pairwise_disjoint`：cycleFactorsFinset_pair
wise_disjoint : (cycleFactorsFinset f : Set (Perm α)).Pairwise Disjoint

--- 原说明 ---
Two cycles of a permutation commute.
-/
theorem cycleFactorsFinset_mem_commute : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute :=
  (cycleFactorsFinset_pairwise_disjoint _).mono' fun _ _ => Disjoint.commute

/-- Two cycles of a permutation commute. -/
/-
**Equiv.Perm.cycleFactorsFinset_mem_commute'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Pe
rm`。
形式化陈述：cycleFactorsFinset_mem_commute' {g1 g2 : Perm α} (h1 : g1 in f.cycleFactor
sFinset) (h2 : g2 in f.cycleFactorsFinset) : Commute g1 g2
参数：h1 : g1 in f.cycleFactorsFinset；h2 : g2 in f.cycleFactorsFinset。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
· 使用定理 `Equiv.Perm.cycleFactorsFinset_mem_commute`：cycleFactorsFinset_mem_commut
e : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute

--- 原说明 ---
Two cycles of a permutation commute.
-/
theorem cycleFactorsFinset_mem_commute' {g1 g2 : Perm α}
    (h1 : g1 ∈ f.cycleFactorsFinset) (h2 : g2 ∈ f.cycleFactorsFinset) :
    Commute g1 g2 := by
  rcases eq_or_ne g1 g2 with rfl | h
  · apply Commute.refl
  · exact Equiv.Perm.cycleFactorsFinset_mem_commute f h1 h2 h

/-- The product of cycle factors is equal to the original `f : perm α`. -/
/-
**Equiv.Perm.cycleFactorsFinset_noncommProd** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m`。
形式化陈述：cycleFactorsFinset_noncommProd (comm : (cycleFactorsFinset f : Set (Perm α
)).Pairwise Commute
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.cycleFactorsFinset_eq_finset`：cycleFactorsFinset_eq_finset {σ
 : Perm α} {s : Finset (Perm α)} : σ.cycleFactorsFinset = s ↔ (forall f : Perm α
, f in s -> f.IsCycle) ∧ exis…

--- 原说明 ---
The product of cycle factors is equal to the original `f : perm α`.
-/
theorem cycleFactorsFinset_noncommProd
    (comm : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute :=
      cycleFactorsFinset_mem_commute f) :
    f.cycleFactorsFinset.noncommProd id comm = f :=
  (cycleFactorsFinset_eq_finset.mp rfl).2.choose_spec
/-
**Equiv.Perm.mem_cycleFactorsFinset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_cycleFactorsFinset_iff {f p : Perm α} : p in cycleFactorsFinset f ↔ p.
IsCycle ∧ forall a in p.support, p a = f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_list_nodup_eq`：exists_list_nodup_eq [DecidableEq α] (s : F
inset α) : exists l : List α, l.Nodup ∧ l.toFinset = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Equiv.Perm.cycleFactorsFinset_eq_list_toFinset`：cycleFactorsFinset_eq_li
st_toFinset {σ : Perm α} {l : List (Perm α)} (hn : l.Nodup) : σ.cycleFactorsFins
et = l.toFinset ↔ (forall f : Perm α…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Equiv.Perm.mem_list_cycles_iff`：mem_list_cycles_iff {α : Type*} [Finite 
α] {l : List (Perm α)} (h1 : forall σ : Perm α, σ in l -> σ.IsCycle) (h2 : l.Pai
rwise Disjoint) {σ :…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem mem_cycleFactorsFinset_iff {f p : Perm α} :
    p ∈ cycleFactorsFinset f ↔ p.IsCycle ∧ ∀ a ∈ p.support, p a = f a := by
  obtain ⟨l, hl, hl'⟩ := f.cycleFactorsFinset.exists_list_nodup_eq
  rw [← hl']
  rw [eq_comm, cycleFactorsFinset_eq_list_toFinset hl] at hl'
  simpa [List.mem_toFinset, Ne, ← hl'.right.right] using
    mem_list_cycles_iff hl'.left hl'.right.left
/-
**Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv
.Perm`。
形式化陈述：cycleOf_mem_cycleFactorsFinset_iff {f : Perm α} {x : α} : cycleOf f x in c
ycleFactorsFinset f ↔ x in f.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_iff`：mem_cycleFactorsFinset_iff {f p :
 Perm α} : p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = 
f a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.cycleOf_eq_one_iff`：cycleOf_eq_one_iff (f : Perm α) [Decidabl
eRel f.SameCycle] : cycleOf f x = 1 ↔ f x = x
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Equiv.Perm.isCycle_cycleOf`：isCycle_cycleOf (f : Perm α) [DecidableRel f
.SameCycle] (hx : f x != x) : IsCycle (cycleOf f x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.Perm.cycleOf_apply`：cycleOf_apply (f : Perm α) [DecidableRel f.Sam
eCycle] (x y : α) : cycleOf f x y = if SameCycle f x y then f y else y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Equiv.Perm.cycleOf_apply_of_not_sameCycle`：cycleOf_apply_of_not_sameCycl
e [DecidableRel f.SameCycle] : ¬SameCycle f x y -> cycleOf f x y = y
-/
theorem cycleOf_mem_cycleFactorsFinset_iff {f : Perm α} {x : α} :
    cycleOf f x ∈ cycleFactorsFinset f ↔ x ∈ f.support := by
  rw [mem_cycleFactorsFinset_iff]
  constructor
  · rintro ⟨hc, _⟩
    contrapose hc
    rw [notMem_support, ← cycleOf_eq_one_iff] at hc
    simp [hc]
  · intro hx
    refine ⟨isCycle_cycleOf _ (mem_support.mp hx), ?_⟩
    intro y hy
    rw [mem_support] at hy
    rw [cycleOf_apply]
    split_ifs with H
    · rfl
    · rw [cycleOf_apply_of_not_sameCycle H] at hy
      contradiction
/-
**Equiv.Perm.cycleOf_ne_one_iff_mem_cycleFactorsFinset** 是 Mathlib 中的一个引理，位于命名空间
 `Equiv.Perm`。
形式化陈述：cycleOf_ne_one_iff_mem_cycleFactorsFinset {g : Equiv.Perm α} {x : α} : g.c
ycleOf x != 1 ↔ g.cycleOf x in g.cycleFactorsFinset
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff`：cycleOf_mem_cycleFactorsF
inset_iff {f : Perm α} {x : α} : cycleOf f x in cycleFactorsFinset f ↔ x in f.su
pport
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Equiv.Perm.cycleOf_eq_one_iff`：cycleOf_eq_one_iff (f : Perm α) [Decidabl
eRel f.SameCycle] : cycleOf f x = 1 ↔ f x = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma cycleOf_ne_one_iff_mem_cycleFactorsFinset {g : Equiv.Perm α} {x : α} :
    g.cycleOf x ≠ 1 ↔ g.cycleOf x ∈ g.cycleFactorsFinset := by
  rw [cycleOf_mem_cycleFactorsFinset_iff, mem_support, ne_eq, cycleOf_eq_one_iff]
/-
**Equiv.Perm.mem_cycleFactorsFinset_support_le** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.
Perm`。
形式化陈述：mem_cycleFactorsFinset_support_le {p f : Perm α} (h : p in cycleFactorsFin
set f) : p.support <= f.support
参数：h : p in cycleFactorsFinset f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_iff`：mem_cycleFactorsFinset_iff {f p :
 Perm α} : p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = 
f a
-/
theorem mem_cycleFactorsFinset_support_le {p f : Perm α} (h : p ∈ cycleFactorsFinset f) :
    p.support ≤ f.support := by
  rw [mem_cycleFactorsFinset_iff] at h
  intro x hx
  rwa [mem_support, ← h.right x hx, ← mem_support]
/-
**Equiv.Perm.support_zpowers_of_mem_cycleFactorsFinset_le** 是 Mathlib 中的一个引理，位于命
名空间 `Equiv.Perm`。
形式化陈述：support_zpowers_of_mem_cycleFactorsFinset_le {g : Perm α} {c : g.cycleFact
orsFinset} (v : Subgroup.zpowers (c : Perm α)) : (v : Perm α).support <= g.suppo
rt
参数：v : Subgroup.zpowers (c : Perm α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Equiv.Perm.support_zpow_le`：support_zpow_le (σ : Perm α) (n : Int) : (σ 
^ n).support <= σ.support
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_support_le`：mem_cycleFactorsFinset_sup
port_le {p f : Perm α} (h : p in cycleFactorsFinset f) : p.support <= f.support
-/
lemma support_zpowers_of_mem_cycleFactorsFinset_le {g : Perm α}
    {c : g.cycleFactorsFinset} (v : Subgroup.zpowers (c : Perm α)) :
    (v : Perm α).support ≤ g.support := by
  obtain ⟨m, hm⟩ := v.prop
  simp only [← hm]
  exact le_trans (support_zpow_le _ _) (mem_cycleFactorsFinset_support_le c.prop)
/-
**Equiv.Perm.pairwise_disjoint_of_mem_zpowers** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.P
erm`。
形式化陈述：pairwise_disjoint_of_mem_zpowers : Pairwise fun (i j : f.cycleFactorsFinse
t) => forall (x y : Perm α), x in Subgroup.zpowers ↑i -> y in Subgroup.zpowers ↑
j -> Disjoint x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.Disjoint.zpow_disjoint_zpow`：∀ {α : Type u_1} {σ τ : Equiv.Pe
rm α}, σ.Disjoint τ → ∀ (m n : ℤ), (σ ^ m).Disjoint (τ ^ n)
· 使用定理 `Equiv.Perm.cycleFactorsFinset_pairwise_disjoint`：cycleFactorsFinset_pair
wise_disjoint : (cycleFactorsFinset f : Set (Perm α)).Pairwise Disjoint
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
-/
theorem pairwise_disjoint_of_mem_zpowers :
    Pairwise fun (i j : f.cycleFactorsFinset) ↦
      ∀ (x y : Perm α), x ∈ Subgroup.zpowers ↑i → y ∈ Subgroup.zpowers ↑j → Disjoint x y :=
  fun c d hcd ↦ fun x y hx hy ↦ by
  obtain ⟨m, hm⟩ := hx; obtain ⟨n, hn⟩ := hy
  simp only [← hm, ← hn]
  apply Disjoint.zpow_disjoint_zpow
  exact f.cycleFactorsFinset_pairwise_disjoint c.prop d.prop (Subtype.coe_ne_coe.mpr hcd)
/-
**Equiv.Perm.pairwise_commute_of_mem_zpowers** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.Pe
rm`。
形式化陈述：pairwise_commute_of_mem_zpowers : Pairwise fun (i j : f.cycleFactorsFinset
) => forall (x y : Perm α), x in Subgroup.zpowers ↑i -> y in Subgroup.zpowers ↑j
 -> Commute x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `Equiv.Perm.pairwise_disjoint_of_mem_zpowers`：pairwise_disjoint_of_mem_zp
owers : Pairwise fun (i j : f.cycleFactorsFinset) => forall (x y : Perm α), x in
 Subgroup.zpowers ↑i -> y in Subg…
· 使用定理 `forall₂_imp`：forall₂_imp {p q : forall a, β a -> Prop} (h : forall a b, 
p a b -> q a b) : (forall a b, p a b) -> forall a b, q a b
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
-/
lemma pairwise_commute_of_mem_zpowers :
    Pairwise fun (i j : f.cycleFactorsFinset) ↦
      ∀ (x y : Perm α), x ∈ Subgroup.zpowers ↑i → y ∈ Subgroup.zpowers ↑j → Commute x y :=
  f.pairwise_disjoint_of_mem_zpowers.mono
    (fun _ _ ↦ forall₂_imp (fun _ _ h hx hy ↦ (h hx hy).commute))
/-
**Equiv.Perm.disjoint_ofSubtype_noncommPiCoprod** 是 Mathlib 中的一个引理，位于命名空间 `Equiv
.Perm`。
形式化陈述：disjoint_ofSubtype_noncommPiCoprod (u : Perm (Function.fixedPoints f)) (v 
: (c : { x // x in f.cycleFactorsFinset }) -> (Subgroup.zpowers (c : Perm α))) :
 Disjoint (ofSubtype u) ((Subgroup.noncommPiCoprod f.pairwise_commute_of_mem_zpo
wers) v)
参数：u : Perm (Function.fixedPoints f)；v : (c : { x // x in f.cycleFactorsFinset }
) -> (Subgroup.zpowers (c : Perm α))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.noncommProd_induction`：noncommProd_induction (s : Finset α) (f : 
α -> β) (comm) (p : β -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit
 : p 1) (base : fo…
· 使用引理 `Equiv.Perm.pairwise_commute_of_mem_zpowers`：pairwise_commute_of_mem_zpow
ers : Pairwise fun (i j : f.cycleFactorsFinset) => forall (x y : Perm α), x in S
ubgroup.zpowers ↑i -> y in Subgr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.Perm.Disjoint.mul_right`：∀ {α : Type u_1} {f g h : Equiv.Perm α}, 
f.Disjoint g → f.Disjoint h → f.Disjoint (g * h)
· 使用定理 `Equiv.Perm.disjoint_one_right`：disjoint_one_right (f : Perm α) : Disjoin
t f 1
· 使用定理 `Equiv.Perm.Disjoint.mono`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_
1 : Fintype α] {f g x y : Equiv.Perm α},   f.Disjoint g → x.support ⊆ f.support 
→ y.support ⊆ …
· 使用引理 `Equiv.Perm.disjoint_ofSubtype_of_memFixedPoints_self`：disjoint_ofSubtype
_of_memFixedPoints_self {g : Perm α} (u : Perm (Function.fixedPoints g)) : Disjo
int (ofSubtype u) g
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `Equiv.Perm.support_zpowers_of_mem_cycleFactorsFinset_le`：support_zpowers
_of_mem_cycleFactorsFinset_le {g : Perm α} {c : g.cycleFactorsFinset} (v : Subgr
oup.zpowers (c : Perm α)) : (v : Perm α).supp…
-/
lemma disjoint_ofSubtype_noncommPiCoprod (u : Perm (Function.fixedPoints f))
    (v : (c : { x // x ∈ f.cycleFactorsFinset }) → (Subgroup.zpowers (c : Perm α))) :
    Disjoint (ofSubtype u) ((Subgroup.noncommPiCoprod f.pairwise_commute_of_mem_zpowers) v) := by
  apply Finset.noncommProd_induction
  · intro a _ b _ h
    apply f.pairwise_commute_of_mem_zpowers h <;> simp only [Subgroup.coe_subtype, SetLike.coe_mem]
  · intro x y
    exact Disjoint.mul_right
  · exact disjoint_one_right _
  · intro c _
    simp only [Subgroup.coe_subtype]
    exact Disjoint.mono (disjoint_ofSubtype_of_memFixedPoints_self u)
      le_rfl (support_zpowers_of_mem_cycleFactorsFinset_le (v c))
/-
**Equiv.Perm.commute_ofSubtype_noncommPiCoprod** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.
Perm`。
形式化陈述：commute_ofSubtype_noncommPiCoprod (u : Perm (Function.fixedPoints f)) (v :
 (c : { x // x in f.cycleFactorsFinset }) -> (Subgroup.zpowers (c : Perm α))) : 
Commute (ofSubtype u) ((Subgroup.noncommPiCoprod f.pairwise_commute_of_mem_zpowe
rs) v)
参数：u : Perm (Function.fixedPoints f)；v : (c : { x // x in f.cycleFactorsFinset }
) -> (Subgroup.zpowers (c : Perm α))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用引理 `Equiv.Perm.pairwise_commute_of_mem_zpowers`：pairwise_commute_of_mem_zpow
ers : Pairwise fun (i j : f.cycleFactorsFinset) => forall (x y : Perm α), x in S
ubgroup.zpowers ↑i -> y in Subgr…
· 使用引理 `Equiv.Perm.disjoint_ofSubtype_noncommPiCoprod`：disjoint_ofSubtype_noncom
mPiCoprod (u : Perm (Function.fixedPoints f)) (v : (c : { x // x in f.cycleFacto
rsFinset }) -> (Subgroup.zpowers (c…
-/
lemma commute_ofSubtype_noncommPiCoprod (u : Perm (Function.fixedPoints f))
    (v : (c : { x // x ∈ f.cycleFactorsFinset }) → (Subgroup.zpowers (c : Perm α))) :
    Commute (ofSubtype u) ((Subgroup.noncommPiCoprod f.pairwise_commute_of_mem_zpowers) v) :=
  Disjoint.commute (f.disjoint_ofSubtype_noncommPiCoprod u v)
/-
**Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset** 是 Mathlib 中
的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_support_iff_mem_support_of_mem_cycleFactorsFinset {g : Equiv.Perm α} {
x : α} : x in g.support ↔ exists c in g.cycleFactorsFinset, x in c.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff`：cycleOf_mem_cycleFactorsF
inset_iff {f : Perm α} {x : α} : cycleOf f x in cycleFactorsFinset f ↔ x in f.su
pport
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.mem_support_cycleOf_iff`：mem_support_cycleOf_iff [DecidableEq
 α] [Fintype α] : y in support (f.cycleOf x) ↔ SameCycle f x y ∧ x in support f
· 使用定理 `Equiv.Perm.SameCycle.refl`：∀ {α : Type u_2} (f : Equiv.Perm α) (x : α), 
f.SameCycle x x
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_support_le`：mem_cycleFactorsFinset_sup
port_le {p f : Perm α} (h : p in cycleFactorsFinset f) : p.support <= f.support
-/
theorem mem_support_iff_mem_support_of_mem_cycleFactorsFinset {g : Equiv.Perm α} {x : α} :
    x ∈ g.support ↔ ∃ c ∈ g.cycleFactorsFinset, x ∈ c.support := by
  constructor
  · intro h
    use g.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr h
    rw [mem_support_cycleOf_iff]
    exact ⟨SameCycle.refl g x, h⟩
  · rintro ⟨c, hc, hx⟩
    exact mem_cycleFactorsFinset_support_le hc hx

set_option backward.isDefEq.respectTransparency.types false in
/-
**Equiv.Perm.cycleFactorsFinset_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Pe
rm`。
形式化陈述：cycleFactorsFinset_eq_empty_iff {f : Perm α} : cycleFactorsFinset f = ∅ ↔ 
f = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.noncommProd_congr`：noncommProd_congr {s₁ s₂ : Finset α} {f g : α 
-> β} (h₁ : s₁ = s₂) (h₂ : forall x in s₂, f x = g x) (comm) : noncommProd s₁ f 
comm = noncomm…
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem cycleFactorsFinset_eq_empty_iff {f : Perm α} : cycleFactorsFinset f = ∅ ↔ f = 1 := by
  simpa [cycleFactorsFinset_eq_finset] using eq_comm

@[simp]
/-
**Equiv.Perm.cycleFactorsFinset_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleFactorsFinset_one : cycleFactorsFinset (1 : Perm α) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cycleFactorsFinset_one : cycleFactorsFinset (1 : Perm α) = ∅ := by
  simp [cycleFactorsFinset_eq_empty_iff]

@[simp]
/-
**Equiv.Perm.cycleFactorsFinset_eq_singleton_self_iff** 是 Mathlib 中的一个定理，位于命名空间 
`Equiv.Perm`。
形式化陈述：cycleFactorsFinset_eq_singleton_self_iff {f : Perm α} : f.cycleFactorsFins
et = {f} ↔ f.IsCycle
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.noncommProd_congr`：noncommProd_congr {s₁ s₂ : Finset α} {f g : α 
-> β} (h₁ : s₁ = s₂) (h₂ : forall x in s₂, f x = g x) (comm) : noncommProd s₁ f 
comm = noncomm…
· 使用定理 `Finset.noncommProd_singleton`：noncommProd_singleton (a : α) (f : α -> β)
 : noncommProd ({a} : Finset α) f (by norm_cast exact Set.pairwise_singleton _ _
) = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cycleFactorsFinset_eq_singleton_self_iff {f : Perm α} :
    f.cycleFactorsFinset = {f} ↔ f.IsCycle := by simp [cycleFactorsFinset_eq_finset]
/-
**Equiv.Perm.IsCycle.cycleFactorsFinset_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `
Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Fintype α] {f : Equiv.Pe
rm α}, f.IsCycle → f.cycleFactorsFinset = {f}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.cycleFactorsFinset_eq_singleton_self_iff`：cycleFactorsFinset_
eq_singleton_self_iff {f : Perm α} : f.cycleFactorsFinset = {f} ↔ f.IsCycle
-/
theorem IsCycle.cycleFactorsFinset_eq_singleton {f : Perm α} (hf : IsCycle f) :
    f.cycleFactorsFinset = {f} :=
  cycleFactorsFinset_eq_singleton_self_iff.mpr hf
/-
**Equiv.Perm.cycleFactorsFinset_eq_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equi
v.Perm`。
形式化陈述：cycleFactorsFinset_eq_singleton_iff {f g : Perm α} : f.cycleFactorsFinset 
= {g} ↔ f.IsCycle ∧ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleFactorsFinset_eq_finset`：cycleFactorsFinset_eq_finset {σ
 : Perm α} {s : Finset (Perm α)} : σ.cycleFactorsFinset = s ↔ (forall f : Perm α
, f in s -> f.IsCycle) ∧ exis…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.noncommProd_congr`：noncommProd_congr {s₁ s₂ : Finset α} {f g : α 
-> β} (h₁ : s₁ = s₂) (h₂ : forall x in s₂, f x = g x) (comm) : noncommProd s₁ f 
comm = noncomm…
· 使用定理 `Finset.noncommProd_singleton`：noncommProd_singleton (a : α) (f : α -> β)
 : noncommProd ({a} : Finset α) f (by norm_cast exact Set.pairwise_singleton _ _
) = f a
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem cycleFactorsFinset_eq_singleton_iff {f g : Perm α} :
    f.cycleFactorsFinset = {g} ↔ f.IsCycle ∧ f = g := by
  suffices f = g → (g.IsCycle ↔ f.IsCycle) by
    rw [cycleFactorsFinset_eq_finset]
    simpa [eq_comm]
  rintro rfl
  exact Iff.rfl

/-- Two permutations `f g : Perm α` have the same cycle factors iff they are the same. -/
/-
**Equiv.Perm.cycleFactorsFinset_injective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`
。
形式化陈述：cycleFactorsFinset_injective : Function.Injective (@cycleFactorsFinset α _
 _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.cycleFactorsFinset_mem_commute`：cycleFactorsFinset_mem_commut
e : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.cycleFactorsFinset_noncommProd`：cycleFactorsFinset_noncommPro
d (comm : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.noncommProd_congr`：noncommProd_congr {s₁ s₂ : Finset α} {f g : α 
-> β} (h₁ : s₁ = s₂) (h₂ : forall x in s₂, f x = g x) (comm) : noncommProd s₁ f 
comm = noncomm…

--- 原说明 ---
Two permutations `f g : Perm α` have the same cycle factors iff they are the sam
e.
-/
theorem cycleFactorsFinset_injective : Function.Injective (@cycleFactorsFinset α _ _) := by
  intro f g h
  rw [← cycleFactorsFinset_noncommProd f]
  simpa [h] using cycleFactorsFinset_noncommProd g
/-
**Equiv.Perm.Disjoint.disjoint_cycleFactorsFinset** 是 Mathlib 中的一个定理，位于命名空间 `Equ
iv.Perm.Disjoint`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Fintype α] {f g : Equiv.
Perm α},   f.Disjoint g → Disjoint f.cycleFactorsFinset g.cycleFactorsFinset
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Equiv.Perm.disjoint_iff_disjoint_support`：disjoint_iff_disjoint_support 
: Disjoint f g ↔ _root_.Disjoint f.support g.support
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem Disjoint.disjoint_cycleFactorsFinset {f g : Perm α} (h : Disjoint f g) :
    _root_.Disjoint (cycleFactorsFinset f) (cycleFactorsFinset g) := by
  rw [disjoint_iff_disjoint_support] at h
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [mem_cycleFactorsFinset_iff, mem_support] at hx hy
  obtain ⟨⟨⟨a, ha, -⟩, hf⟩, -, hg⟩ := hx, hy
  have := h.le_bot (by simp [ha, ← hf a ha, ← hg a ha] : a ∈ f.support ∩ g.support)
  tauto
/-
**Equiv.Perm.Disjoint.cycleFactorsFinset_mul_eq_union** 是 Mathlib 中的一个定理，位于命名空间 
`Equiv.Perm.Disjoint`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Fintype α] {f g : Equiv.
Perm α},   f.Disjoint g → (f * g).cycleFactorsFinset = f.cycleFactorsFinset ∪ g.
cycleFactorsFinset
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleFactorsFinset_eq_finset`：cycleFactorsFinset_eq_finset {σ
 : Perm α} {s : Finset (Perm α)} : σ.cycleFactorsFinset = s ↔ (forall f : Perm α
, f in s -> f.IsCycle) ∧ exis…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Set.pairwise_union_of_symm`：pairwise_union_of_symm [Std.Symm r] : (s uni
on t).Pairwise r ↔ s.Pairwise r ∧ t.Pairwise r ∧ forall a in s, forall b in t, a
 != b -> r a b
· 使用定理 `Equiv.Perm.Disjoint.stdSymm`：∀ {α : Type u_1}, Std.Symm Equiv.Perm.Disjo
int
· 使用定理 `Equiv.Perm.cycleFactorsFinset_pairwise_disjoint`：cycleFactorsFinset_pair
wise_disjoint : (cycleFactorsFinset f : Set (Perm α)).Pairwise Disjoint
· 使用定理 `Equiv.Perm.Disjoint.mono`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_
1 : Fintype α] {f g x y : Equiv.Perm α},   f.Disjoint g → x.support ⊆ f.support 
→ y.support ⊆ …
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_support_le`：mem_cycleFactorsFinset_sup
port_le {p f : Perm α} (h : p in cycleFactorsFinset f) : p.support <= f.support
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.noncommProd_union_of_disjoint`：noncommProd_union_of_disjoint [Dec
idableEq α] {s t : Finset α} (h : Disjoint s t) (f : α -> β) (comm : Set.Pairwis
e ↑(s union t) (Commute on…
· 使用定理 `Equiv.Perm.Disjoint.disjoint_cycleFactorsFinset`：∀ {α : Type u_2} [inst 
: DecidableEq α] [inst_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g → Dis
joint f.cycleFactorsFinset g.cycleFac…
· 使用定理 `Equiv.Perm.cycleFactorsFinset_mem_commute`：cycleFactorsFinset_mem_commut
e : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute
· 使用定理 `Equiv.Perm.cycleFactorsFinset_noncommProd`：cycleFactorsFinset_noncommPro
d (comm : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute
-/
theorem Disjoint.cycleFactorsFinset_mul_eq_union {f g : Perm α} (h : Disjoint f g) :
    cycleFactorsFinset (f * g) = cycleFactorsFinset f ∪ cycleFactorsFinset g := by
  rw [cycleFactorsFinset_eq_finset]
  refine ⟨?_, ?_, ?_⟩
  · simp [or_imp, mem_cycleFactorsFinset_iff, forall_comm]
  · rw [coe_union, Set.pairwise_union_of_symm]
    exact
      ⟨cycleFactorsFinset_pairwise_disjoint _, cycleFactorsFinset_pairwise_disjoint _,
        fun x hx y hy _ =>
        h.mono (mem_cycleFactorsFinset_support_le hx) (mem_cycleFactorsFinset_support_le hy)⟩
  · rw [noncommProd_union_of_disjoint h.disjoint_cycleFactorsFinset]
    rw [cycleFactorsFinset_noncommProd, cycleFactorsFinset_noncommProd]
/-
**Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset** 是 Mathlib 中的一个定理，位于命名空
间 `Equiv.Perm`。
形式化陈述：disjoint_mul_inv_of_mem_cycleFactorsFinset {f g : Perm α} (h : f in cycleF
actorsFinset g) : Disjoint (g * f⁻¹) f
参数：h : f in cycleFactorsFinset g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_iff`：mem_cycleFactorsFinset_iff {f p :
 Perm α} : p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = 
f a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem disjoint_mul_inv_of_mem_cycleFactorsFinset {f g : Perm α} (h : f ∈ cycleFactorsFinset g) :
    Disjoint (g * f⁻¹) f := by
  rw [mem_cycleFactorsFinset_iff] at h
  intro x
  by_cases hx : f x = x
  · exact Or.inr hx
  left
  rw [mul_apply, ← h.right _ (by simpa [eq_symm_apply])]
  simp

/-- If c is a cycle, a ∈ c.support and c is a cycle of f, then `c = f.cycleOf a` -/
/-
**Equiv.Perm.cycle_is_cycleOf** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycle_is_cycleOf {f c : Equiv.Perm α} {a : α} (ha : a in c.support) (hc : 
c in f.cycleFactorsFinset) : c = f.cycleOf a
参数：ha : a in c.support；hc : c in f.cycleFactorsFinset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.Disjoint.symm`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Disjo
int g → g.Disjoint f
· 使用定理 `Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset`：disjoint_mul_inv_
of_mem_cycleFactorsFinset {f g : Perm α} (h : f in cycleFactorsFinset g) : Disjo
int (g * f⁻¹) f
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.cycleOf_mul_of_apply_right_eq_self`：cycleOf_mul_of_apply_righ
t_eq_self [DecidableRel f.SameCycle] [DecidableRel (f * g).SameCycle] (h : Commu
te f g) (x : α) (hx : g x = x) : (f…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Equiv.Perm.Disjoint.disjoint_support`：∀ {α : Type u_1} [inst : Decidable
Eq α] [inst_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g → Disjoint f.sup
port g.support
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.Perm.cycleOf.congr_simp`：∀ {α : Type u_2} (f f_1 : Equiv.Perm α), 
  f = f_1 →     ∀ {inst : DecidableRel f.SameCycle} [inst_1 : DecidableRel f_1.S
ameCycle] (x x_1 : …
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `Equiv.Perm.IsCycle.cycleOf_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {x : 
α} [inst : DecidableRel f.SameCycle], f.IsCycle → f x ≠ x → f.cycleOf x = f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_iff`：mem_cycleFactorsFinset_iff {f p :
 Perm α} : p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = 
f a
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x

--- 原说明 ---
If c is a cycle, a ∈ c.support and c is a cycle of f, then `c = f.cycleOf a`
-/
theorem cycle_is_cycleOf {f c : Equiv.Perm α} {a : α} (ha : a ∈ c.support)
    (hc : c ∈ f.cycleFactorsFinset) : c = f.cycleOf a := by
  suffices f.cycleOf a = c.cycleOf a by
    rw [this]
    apply symm
    exact
      Equiv.Perm.IsCycle.cycleOf_eq (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).left
        (Equiv.Perm.mem_support.mp ha)
  let hfc := (Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc).symm
  let hfc2 := Perm.Disjoint.commute hfc
  rw [← Equiv.Perm.cycleOf_mul_of_apply_right_eq_self hfc2]
  · simp only [hfc2.eq, inv_mul_cancel_right]
  -- `a` is in the support of `c`, hence it is not in the support of `g c⁻¹`
  exact
    Equiv.Perm.notMem_support.mp
      (Finset.disjoint_left.mp (Equiv.Perm.Disjoint.disjoint_support hfc) ha)
/-
**Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset** 是 Mathlib 中的一个定理，位于命名
空间 `Equiv.Perm`。
形式化陈述：isCycleOn_support_of_mem_cycleFactorsFinset {g c : Equiv.Perm α} (hc : c i
n g.cycleFactorsFinset) : IsCycleOn g c.support
参数：hc : c in g.cycleFactorsFinset。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.IsCycle.nonempty_support`：∀ {α : Type u_2} [inst : Fintype α]
 [inst_1 : DecidableEq α] {g : Equiv.Perm α}, g.IsCycle → g.support.Nonempty
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_iff`：mem_cycleFactorsFinset_iff {f p :
 Perm α} : p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = 
f a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycle_is_cycleOf`：cycle_is_cycleOf {f c : Equiv.Perm α} {a : 
α} (ha : a in c.support) (hc : c in f.cycleFactorsFinset) : c = f.cycleOf a
· 使用定理 `Equiv.Perm.isCycleOn_support_cycleOf`：isCycleOn_support_cycleOf [Decidab
leEq α] [Fintype α] (f : Perm α) (x : α) : f.IsCycleOn (f.cycleOf x).support
-/
theorem isCycleOn_support_of_mem_cycleFactorsFinset {g c : Equiv.Perm α}
    (hc : c ∈ g.cycleFactorsFinset) :
    IsCycleOn g c.support := by
  obtain ⟨x, hx⟩ := IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp hc).1
  rw [cycle_is_cycleOf hx hc]
  exact isCycleOn_support_cycleOf g x
/-
**Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff** 是 Mathlib 中的一个定理，位于命名空间 
`Equiv.Perm`。
形式化陈述：eq_cycleOf_of_mem_cycleFactorsFinset_iff (g c : Perm α) (hc : c in g.cycle
FactorsFinset) (x : α) : c = g.cycleOf x ↔ x in c.support
参数：g c : Perm α；hc : c in g.cycleFactorsFinset；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.Perm.cycleOf_apply_self`：cycleOf_apply_self (f : Perm α) [Decidabl
eRel f.SameCycle] (x : α) : cycleOf f x x = f x
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.cycleOf_eq_one_iff`：cycleOf_eq_one_iff (f : Perm α) [Decidabl
eRel f.SameCycle] : cycleOf f x = 1 ↔ f x = x
· 使用定理 `Equiv.Perm.IsCycle.ne_one`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycl
e → f ≠ 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_iff`：mem_cycleFactorsFinset_iff {f p :
 Perm α} : p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = 
f a
· 使用定理 `Equiv.Perm.cycle_is_cycleOf`：cycle_is_cycleOf {f c : Equiv.Perm α} {a : 
α} (ha : a in c.support) (hc : c in f.cycleFactorsFinset) : c = f.cycleOf a
-/
theorem eq_cycleOf_of_mem_cycleFactorsFinset_iff
    (g c : Perm α) (hc : c ∈ g.cycleFactorsFinset) (x : α) :
    c = g.cycleOf x ↔ x ∈ c.support := by
  refine ⟨?_, (cycle_is_cycleOf · hc)⟩
  rintro rfl
  rw [mem_support, cycleOf_apply_self, ne_eq, ← cycleOf_eq_one_iff]
  exact (mem_cycleFactorsFinset_iff.mp hc).left.ne_one
/-
**Equiv.Perm.zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff** 是 Mathlib 中的
一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff {g : Perm α} {x : α} 
{m : Int} {c : g.cycleFactorsFinset} : (g ^ m) x in (c : Perm α).support ↔ x in 
(c : Perm α).support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff`：eq_cycleOf_of_mem_c
ycleFactorsFinset_iff (g c : Perm α) (hc : c in g.cycleFactorsFinset) (x : α) : 
c = g.cycleOf x ↔ x in c.support
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Equiv.Perm.cycleOf_self_apply_zpow`：cycleOf_self_apply_zpow (f : Perm α)
 [DecidableRel f.SameCycle] (n : Int) (x : α) : cycleOf f ((f ^ n) x) = cycleOf 
f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff {g : Perm α}
    {x : α} {m : ℤ} {c : g.cycleFactorsFinset} :
    (g ^ m) x ∈ (c : Perm α).support ↔ x ∈ (c : Perm α).support := by
  rw [← g.eq_cycleOf_of_mem_cycleFactorsFinset_iff _ c.prop, cycleOf_self_apply_zpow,
    eq_cycleOf_of_mem_cycleFactorsFinset_iff _ _ c.prop]

/-- A permutation `c` is a cycle of `g` iff `k * c * k⁻¹` is a cycle of `k * g * k⁻¹` -/
/-
**Equiv.Perm.mem_cycleFactorsFinset_conj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_cycleFactorsFinset_conj (g k c : Perm α) : k * c * k⁻¹ in (k * g * k⁻¹
).cycleFactorsFinset ↔ c in g.cycleFactorsFinset
参数：g k c : Perm α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `Equiv.Perm.IsCycle.conj`：∀ {α : Type u_2} {f g : Equiv.Perm α}, f.IsCycl
e → (g * f * g⁻¹).IsCycle
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.support_conj`：support_conj : (σ * τ * σ⁻¹).support = τ.suppor
t.map σ.toEmbedding
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.Group._zpow_trick_one'`：_zpow_trick_one' {G : Type*} [Gro
up G] (a b : G) (n : Int) : a * b ^ n * b = a * b ^ (n + 1)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A permutation `c` is a cycle of `g` iff `k * c * k⁻¹` is a cycle of `k * g * k⁻¹
`
-/
theorem mem_cycleFactorsFinset_conj (g k c : Perm α) :
    k * c * k⁻¹ ∈ (k * g * k⁻¹).cycleFactorsFinset ↔ c ∈ g.cycleFactorsFinset := by
  suffices imp_lemma : ∀ {g k c : Perm α},
      c ∈ g.cycleFactorsFinset → k * c * k⁻¹ ∈ (k * g * k⁻¹).cycleFactorsFinset by
    refine ⟨fun h ↦ ?_, imp_lemma⟩
    have aux : ∀ h : Perm α, h = k⁻¹ * (k * h * k⁻¹) * k := fun _ ↦ by group
    rw [aux g, aux c]
    exact imp_lemma h
  intro g k c
  simp only [mem_cycleFactorsFinset_iff]
  apply And.imp IsCycle.conj
  intro hc a ha
  simp only [coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
  apply hc
  simp_all

/-- If a permutation commutes with every cycle of `g`, then it commutes with `g`

NB. The converse is false. Commuting with every cycle of `g` means that we belong
to the kernel of the action of `Equiv.Perm α` on `g.cycleFactorsFinset` -/
/-
**Equiv.Perm.commute_of_mem_cycleFactorsFinset_commute** 是 Mathlib 中的一个定理，位于命名空间
 `Equiv.Perm`。
形式化陈述：commute_of_mem_cycleFactorsFinset_commute (k g : Perm α) (hk : forall c in
 g.cycleFactorsFinset, Commute k c) : Commute k g
参数：k g : Perm α；hk : forall c in g.cycleFactorsFinset, Commute k c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.cycleFactorsFinset_mem_commute`：cycleFactorsFinset_mem_commut
e : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.cycleFactorsFinset_noncommProd`：cycleFactorsFinset_noncommPro
d (comm : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute
· 使用定理 `Finset.noncommProd_commute`：noncommProd_commute (s : Finset α) (f : α ->
 β) (comm) (y : β) (h : forall x in s, Commute y (f x)) : Commute y (s.noncommPr
od f comm)

--- 原说明 ---
If a permutation commutes with every cycle of `g`, then it commutes with `g`

NB. The converse is false. Commuting with every cycle of `g` means that we belon
g
to the kernel of the action of `Equiv.Perm α` on `g.cycleFactorsFinset`
-/
theorem commute_of_mem_cycleFactorsFinset_commute (k g : Perm α)
    (hk : ∀ c ∈ g.cycleFactorsFinset, Commute k c) :
    Commute k g := by
  rw [← cycleFactorsFinset_noncommProd g (cycleFactorsFinset_mem_commute g)]
  apply Finset.noncommProd_commute
  simpa only [id_eq] using hk

/-- The cycles of a permutation commute with it -/
/-
**Equiv.Perm.self_mem_cycle_factors_commute** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m`。
形式化陈述：self_mem_cycle_factors_commute {g c : Perm α} (hc : c in g.cycleFactorsFin
set) : Commute c g
参数：hc : c in g.cycleFactorsFinset。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.commute_of_mem_cycleFactorsFinset_commute`：commute_of_mem_cyc
leFactorsFinset_commute (k g : Perm α) (hk : forall c in g.cycleFactorsFinset, C
ommute k c) : Commute k g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
· 使用定理 `Equiv.Perm.cycleFactorsFinset_mem_commute`：cycleFactorsFinset_mem_commut
e : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute

--- 原说明 ---
The cycles of a permutation commute with it
-/
theorem self_mem_cycle_factors_commute {g c : Perm α}
    (hc : c ∈ g.cycleFactorsFinset) : Commute c g := by
  apply commute_of_mem_cycleFactorsFinset_commute
  intro c' hc'
  by_cases hcc' : c = c'
  · rw [hcc']
  · apply g.cycleFactorsFinset_mem_commute hc hc'; exact hcc'

/-- If `c` and `d` are cycles of `g`, then `d` stabilizes the support of `c` -/
/-
**Equiv.Perm.mem_support_cycle_of_cycle** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_support_cycle_of_cycle {g d c : Perm α} (hc : c in g.cycleFactorsFinse
t) (hd : d in g.cycleFactorsFinset) : forall x : α, d x in c.support ↔ x in c.su
pport
参数：hc : c in g.cycleFactorsFinset；hd : d in g.cycleFactorsFinset。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EmbeddingLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : F) {x y : α} : f x =
 f y ↔ x = y
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Equiv.Perm.cycleFactorsFinset_mem_commute`：cycleFactorsFinset_mem_commut
e : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute

--- 原说明 ---
If `c` and `d` are cycles of `g`, then `d` stabilizes the support of `c`
-/
theorem mem_support_cycle_of_cycle {g d c : Perm α}
    (hc : c ∈ g.cycleFactorsFinset) (hd : d ∈ g.cycleFactorsFinset) :
    ∀ x : α, d x ∈ c.support ↔ x ∈ c.support := by
  intro x
  simp only [mem_support, not_iff_not]
  by_cases h : c = d
  · rw [← h, EmbeddingLike.apply_eq_iff_eq]
  · rw [← Perm.mul_apply,
      Commute.eq (cycleFactorsFinset_mem_commute g hc hd h),
      mul_apply, EmbeddingLike.apply_eq_iff_eq]

/-- If a permutation is a cycle of `g`, then its support is invariant under `g`. -/
/-
**Equiv.Perm.mem_cycleFactorsFinset_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m`。
形式化陈述：mem_cycleFactorsFinset_support {g c : Perm α} (hc : c in g.cycleFactorsFin
set) (a : α) : g a in c.support ↔ a in c.support
参数：hc : c in g.cycleFactorsFinset；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.mem_support_iff_of_commute`：mem_support_iff_of_commute {g c :
 Perm α} (hgc : Commute g c) (x : α) : g x in c.support ↔ x in c.support
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Equiv.Perm.self_mem_cycle_factors_commute`：self_mem_cycle_factors_commut
e {g c : Perm α} (hc : c in g.cycleFactorsFinset) : Commute c g

--- 原说明 ---
If a permutation is a cycle of `g`, then its support is invariant under `g`.
-/
theorem mem_cycleFactorsFinset_support {g c : Perm α} (hc : c ∈ g.cycleFactorsFinset) (a : α) :
    g a ∈ c.support ↔ a ∈ c.support :=
  mem_support_iff_of_commute (self_mem_cycle_factors_commute hc).symm a

end CycleFactorsFinset

@[elab_as_elim]
/-
**Equiv.Perm.cycle_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycle_induction_on [Finite β] (P : Perm β -> Prop) (σ : Perm β) (base_one 
: P 1) (base_cycles : forall σ : Perm β, σ.IsCycle -> P σ) (induction_disjoint :
 forall σ τ : Perm β, Disjoint σ τ -> IsCycle σ -> P σ -> P τ -> P (σ * τ)) : P 
σ
参数：P : Perm β -> Prop；σ : Perm β；base_one : P 1；base_cycles : forall σ : Perm β,
 σ.IsCycle -> P σ；induction_disjoint : forall σ τ : Perm β, Disjoint σ τ -> IsCy
cle σ -> P σ -> P τ -> P (σ * τ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `Equiv.Perm.disjoint_prod_right`：disjoint_prod_right (l : List (Perm α)) 
(h : forall g in l, Disjoint f g) : Disjoint f l.prod
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.pairwise_cons`：∀ {α : Type u} {R : α → α → Prop} {a : α} {l : List 
α},   List.Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ List.Pairwise R l
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `List.Pairwise.of_cons`：∀ {α : Type u_1} {a : α} {l : List α} {R : α → α 
→ Prop}, List.Pairwise R (a :: l) → List.Pairwise R l
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem cycle_induction_on [Finite β] (P : Perm β → Prop) (σ : Perm β) (base_one : P 1)
    (base_cycles : ∀ σ : Perm β, σ.IsCycle → P σ)
    (induction_disjoint : ∀ σ τ : Perm β,
      Disjoint σ τ → IsCycle σ → P σ → P τ → P (σ * τ)) : P σ := by
  cases nonempty_fintype β
  suffices ∀ l : List (Perm β),
      (∀ τ : Perm β, τ ∈ l → τ.IsCycle) → l.Pairwise Disjoint → P l.prod by
    classical
      let x := σ.truncCycleFactors.out
      exact (congr_arg P x.2.1).mp (this x.1 x.2.2.1 x.2.2.2)
  intro l
  induction l with
  | nil => exact fun _ _ => base_one
  | cons σ l ih =>
    intro h1 h2
    rw [List.prod_cons]
    exact
      induction_disjoint σ l.prod (disjoint_prod_right _ (List.pairwise_cons.mp h2).1)
        (h1 _ List.mem_cons_self) (base_cycles σ (h1 σ List.mem_cons_self))
        (ih (fun τ hτ => h1 τ (List.mem_cons_of_mem σ hτ)) h2.of_cons)
/-
**Equiv.Perm.cycleFactorsFinset_mul_inv_mem_eq_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `
Equiv.Perm`。
形式化陈述：cycleFactorsFinset_mul_inv_mem_eq_sdiff [DecidableEq α] [Fintype α] {f g :
 Perm α} (h : f in cycleFactorsFinset g) : cycleFactorsFinset (g * f⁻¹) = cycleF
actorsFinset g \ {f}
参数：h : f in cycleFactorsFinset g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.cycle_induction_on`：cycle_induction_on [Finite β] (P : Perm β
 -> Prop) (σ : Perm β) (base_one : P 1) (base_cycles : forall σ : Perm β, σ.IsCy
cle -> P σ) (induct…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleFactorsFinset_one`：cycleFactorsFinset_one : cycleFactors
Finset (1 : Perm α) = ∅
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.empty_sdiff`：empty_sdiff (s : Finset α) : ∅ \ s = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.cycleFactorsFinset_eq_singleton_self_iff`：cycleFactorsFinset_
eq_singleton_self_iff {f : Perm α} : f.cycleFactorsFinset = {f} ↔ f.IsCycle
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.Disjoint.cycleFactorsFinset_mul_eq_union`：∀ {α : Type u_2} [i
nst : DecidableEq α] [inst_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g →
 (f * g).cycleFactorsFinset = f.cycleFact…
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用定理 `Finset.union_sdiff_distrib`：union_sdiff_distrib (s₁ s₂ t : Finset α) : (
s₁ union s₂) \ t = s₁ \ t union s₂ \ t
· 使用定理 `Finset.sdiff_singleton_eq_erase`：sdiff_singleton_eq_erase (a : α) (s : F
inset α) : s \ {a} = s.erase a
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Equiv.Perm.Disjoint.disjoint_cycleFactorsFinset`：∀ {α : Type u_2} [inst 
: DecidableEq α] [inst_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g → Dis
joint f.cycleFactorsFinset g.cycleFac…
· 使用定理 `Finset.mem_inter_of_mem`：mem_inter_of_mem {a : α} {s₁ s₂ : Finset α} : a
 in s₁ -> a in s₂ -> a in s₁ inter s₂
（共 39 条，此处仅展示前 30 条）
-/
theorem cycleFactorsFinset_mul_inv_mem_eq_sdiff [DecidableEq α] [Fintype α] {f g : Perm α}
    (h : f ∈ cycleFactorsFinset g) : cycleFactorsFinset (g * f⁻¹) = cycleFactorsFinset g \ {f} := by
  revert f
  refine
    cycle_induction_on (P := fun {g : Perm α} ↦
      ∀ {f}, (f ∈ cycleFactorsFinset g)
        → cycleFactorsFinset (g * f⁻¹) = cycleFactorsFinset g \ {f}) _ ?_ ?_ ?_
  · simp
  · intro σ hσ f hf
    simp only [cycleFactorsFinset_eq_singleton_self_iff.mpr hσ, mem_singleton] at hf ⊢
    simp [hf]
  · intro σ τ hd _ hσ hτ f
    simp_rw [hd.cycleFactorsFinset_mul_eq_union, mem_union]
    -- if only `wlog` could work here...
    rintro (hf | hf)
    · rw [hd.commute.eq, union_comm, union_sdiff_distrib, sdiff_singleton_eq_erase,
        erase_eq_of_notMem, mul_assoc, Disjoint.cycleFactorsFinset_mul_eq_union, hσ hf]
      · rw [mem_cycleFactorsFinset_iff] at hf
        intro x
        rcases hd.symm x with hx | hx
        · exact Or.inl hx
        · refine Or.inr ?_
          by_cases hfx : f x = x
          · rw [← hfx]
            simpa [hx] using hfx.symm
          · rw [mul_apply]
            rw [← hf.right _ (mem_support.mpr hfx)] at hx
            contradiction
      · exact fun H =>
        notMem_empty _ (hd.disjoint_cycleFactorsFinset.le_bot (mem_inter_of_mem hf H))
    · rw [union_sdiff_distrib, sdiff_singleton_eq_erase, erase_eq_of_notMem, mul_assoc,
        Disjoint.cycleFactorsFinset_mul_eq_union, hτ hf]
      · rw [mem_cycleFactorsFinset_iff] at hf
        intro x
        rcases hd x with hx | hx
        · exact Or.inl hx
        · refine Or.inr ?_
          by_cases hfx : f x = x
          · rw [← hfx]
            simpa [hx] using hfx.symm
          · rw [mul_apply]
            rw [← hf.right _ (mem_support.mpr hfx)] at hx
            contradiction
      · exact fun H =>
        notMem_empty _ (hd.disjoint_cycleFactorsFinset.le_bot (mem_inter_of_mem H hf))
/-
**Equiv.Perm.IsCycle.forall_commute_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Is
Cycle`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Fintype α] (g z : Equiv.
Perm α),   (∀ c ∈ g.cycleFactorsFinset, Commute z c) ↔     ∀ c ∈ g.cycleFactorsF
inset,       ∃ (hc : ∀ (x : α), z x ∈ c.support ↔ x ∈ c.support), Equiv.Perm.ofS
ubtype (z.subtypePerm hc) ∈ Subgroup.zpowers c
参数：g z : Equiv.Perm α；∀ c ∈ g.cycleFactorsFinset, Commute z c；hc : ∀ (x : α), z 
x ∈ c.support ↔ x ∈ c.support；z.subtypePerm hc。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `imp_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a → b ↔ a → c)
· 使用定理 `Equiv.Perm.IsCycle.commute_iff`：∀ {α : Type u_2} [inst : Fintype α] [ins
t_1 : DecidableEq α] {g c : Equiv.Perm α},   c.IsCycle →     (Commute g c ↔     
  ∃ (hc' : ∀ (x : α)…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_iff`：mem_cycleFactorsFinset_iff {f p :
 Perm α} : p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = 
f a
-/
theorem IsCycle.forall_commute_iff [DecidableEq α] [Fintype α] (g z : Perm α) :
    (∀ c ∈ g.cycleFactorsFinset, Commute z c) ↔
      ∀ c ∈ g.cycleFactorsFinset,
      ∃ (hc : ∀ x : α, z x ∈ c.support ↔ x ∈ c.support),
        ofSubtype (subtypePerm z hc) ∈ Subgroup.zpowers c := by
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro hc
  exact IsCycle.commute_iff (mem_cycleFactorsFinset_iff.mp hc).1

/-- A permutation restricted to the support of a cycle factor is that cycle factor -/
/-
**Equiv.Perm.subtypePerm_on_cycleFactorsFinset** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.
Perm`。
形式化陈述：subtypePerm_on_cycleFactorsFinset [DecidableEq α] [Fintype α] {g c : Perm 
α} (hc : c in g.cycleFactorsFinset) : g.subtypePerm (mem_cycleFactorsFinset_supp
ort hc) = c.subtypePermOfSupport
参数：hc : c in g.cycleFactorsFinset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_support`：mem_cycleFactorsFinset_suppor
t {g c : Perm α} (hc : c in g.cycleFactorsFinset) (a : α) : g a in c.support ↔ a
 in c.support
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_iff`：mem_cycleFactorsFinset_iff {f p :
 Perm α} : p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = 
f a

--- 原说明 ---
A permutation restricted to the support of a cycle factor is that cycle factor
-/
theorem subtypePerm_on_cycleFactorsFinset [DecidableEq α] [Fintype α]
    {g c : Perm α} (hc : c ∈ g.cycleFactorsFinset) :
    g.subtypePerm (mem_cycleFactorsFinset_support hc) = c.subtypePermOfSupport := by
  ext ⟨x, hx⟩
  simp only [subtypePerm_apply, Subtype.coe_mk, subtypePermOfSupport]
  exact ((mem_cycleFactorsFinset_iff.mp hc).2 x hx).symm
/-
**Equiv.Perm.commute_iff_of_mem_cycleFactorsFinset** 是 Mathlib 中的一个定理，位于命名空间 `Eq
uiv.Perm`。
形式化陈述：commute_iff_of_mem_cycleFactorsFinset [DecidableEq α] [Fintype α] {g k c :
 Equiv.Perm α} (hc : c in g.cycleFactorsFinset) : Commute k c ↔ exists hc' : for
all x : α, k x in c.support ↔ x in c.support, k.subtypePerm hc' in Subgroup.zpow
ers (g.subtypePerm (mem_cycleFactorsFinset_support hc))
参数：hc : c in g.cycleFactorsFinset。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_support`：mem_cycleFactorsFinset_suppor
t {g c : Perm α} (hc : c in g.cycleFactorsFinset) (a : α) : g a in c.support ↔ a
 in c.support
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.IsCycle.commute_iff'`：∀ {α : Type u_2} [inst : Fintype α] [in
st_1 : DecidableEq α] {g c : Equiv.Perm α},   c.IsCycle →     (Commute g c ↔    
   ∃ (hc' : ∀ (x : α)…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_iff`：mem_cycleFactorsFinset_iff {f p :
 Perm α} : p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = 
f a
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.Perm.subtypePerm_on_cycleFactorsFinset`：subtypePerm_on_cycleFactor
sFinset [DecidableEq α] [Fintype α] {g c : Perm α} (hc : c in g.cycleFactorsFins
et) : g.subtypePerm (mem_cycleFact…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem commute_iff_of_mem_cycleFactorsFinset [DecidableEq α] [Fintype α] {g k c : Equiv.Perm α}
    (hc : c ∈ g.cycleFactorsFinset) :
    Commute k c ↔
      ∃ hc' : ∀ x : α, k x ∈ c.support ↔ x ∈ c.support,
        k.subtypePerm hc' ∈ Subgroup.zpowers
          (g.subtypePerm (mem_cycleFactorsFinset_support hc)) := by
  rw [IsCycle.commute_iff' (mem_cycleFactorsFinset_iff.mp hc).1]
  apply exists_congr
  intro hc'
  simp only [Subgroup.mem_zpowers_iff]
  apply exists_congr
  intro n
  rw [Equiv.Perm.subtypePerm_on_cycleFactorsFinset hc]

end cycleFactors

end Perm

end Equiv

