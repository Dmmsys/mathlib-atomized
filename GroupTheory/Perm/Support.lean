/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.NoncommProd
public import Mathlib.Data.Fintype.Card

/-!
# support of a permutation

## Main definitions

In the following, `f g : Equiv.Perm α`.

* `Equiv.Perm.Disjoint`: two permutations `f` and `g` are `Disjoint` if every element is fixed
  either by `f`, or by `g`.
  Equivalently, `f` and `g` are `Disjoint` iff their `support` are disjoint.
* `Equiv.Perm.IsSwap`: `f = swap x y` for `x ≠ y`.
* `Equiv.Perm.support`: the elements `x : α` that are not fixed by `f`.

Assume `α` is a Fintype:
* `Equiv.Perm.fixed_point_card_lt_of_ne_one f` says that `f` has
  strictly less than `Fintype.card α - 1` fixed points, unless `f = 1`.
  (Equivalently, `f.support` has at least 2 elements.)

-/

@[expose] public section


open Equiv Finset Function

namespace Equiv.Perm

variable {α : Type*}

section Disjoint

/-- Two permutations `f` and `g` are `Disjoint` if their supports are disjoint, i.e.,
every element is fixed either by `f`, or by `g`. -/
/-
**Equiv.Perm.Disjoint** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：Disjoint (f g : Perm α)
参数：f g : Perm α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two permutations `f` and `g` are `Disjoint` if their supports are disjoint, i.e.
,
every element is fixed either by `f`, or by `g`.
-/
def Disjoint (f g : Perm α) :=
  ∀ x, f x = x ∨ g x = x

variable {f g h : Perm α}

@[symm]
/-
**Equiv.Perm.Disjoint.symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Disjoint`。
形式化陈述：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Disjoint g → g.Disjoint f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem Disjoint.symm : Disjoint f g → Disjoint g f := by simp only [Disjoint, or_comm, imp_self]
/-
**Equiv.Perm.Disjoint.stdSymm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Disjoint`。
形式化陈述：∀ {α : Type u_1}, Std.Symm Equiv.Perm.Disjoint
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.Disjoint.symm`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Disjo
int g → g.Disjoint f
-/
instance Disjoint.stdSymm : Std.Symm (α := Perm α) Disjoint where
  symm _ _ := Disjoint.symm

@[deprecated (since := "2026-06-10")] alias Disjoint.symmetric := Disjoint.stdSymm
/-
**Equiv.Perm.disjoint_comm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：disjoint_comm : Disjoint f g ↔ Disjoint g f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.Disjoint.symm`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Disjo
int g → g.Disjoint f
-/
theorem disjoint_comm : Disjoint f g ↔ Disjoint g f :=
  ⟨Disjoint.symm, Disjoint.symm⟩
/-
**Equiv.Perm.Disjoint.commute** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Disjoint`。
形式化陈述：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Disjoint g → Commute f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem Disjoint.commute (h : Disjoint f g) : Commute f g :=
  Equiv.ext fun x =>
    (h x).elim
      (fun hf =>
        (h (g x)).elim (fun hg => by simp [mul_apply, hf, hg]) fun hg => by
          simp [mul_apply, hf, g.injective hg])
      fun hg =>
      (h (f x)).elim (fun hf => by simp [mul_apply, f.injective hf, hg]) fun hf => by
        simp [mul_apply, hf, hg]

@[simp]
/-
**Equiv.Perm.disjoint_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：disjoint_one_left (f : Perm α) : Disjoint 1 f
参数：f : Perm α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_one_left (f : Perm α) : Disjoint 1 f := fun _ => Or.inl rfl

@[simp]
/-
**Equiv.Perm.disjoint_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：disjoint_one_right (f : Perm α) : Disjoint f 1
参数：f : Perm α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_one_right (f : Perm α) : Disjoint f 1 := fun _ => Or.inr rfl
/-
**Equiv.Perm.disjoint_iff_eq_or_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：disjoint_iff_eq_or_eq : Disjoint f g ↔ forall x : α, f x = x ∨ g x = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_iff_eq_or_eq : Disjoint f g ↔ ∀ x : α, f x = x ∨ g x = x :=
  Iff.rfl

@[simp]
/-
**Equiv.Perm.disjoint_refl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：disjoint_refl_iff : Disjoint f f ↔ f = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.disjoint_one_left`：disjoint_one_left (f : Perm α) : Disjoint 
1 f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem disjoint_refl_iff : Disjoint f f ↔ f = 1 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ disjoint_one_left 1⟩
  ext x
  rcases h x with hx | hx <;> simp [hx]
/-
**Equiv.Perm.Disjoint.inv_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Disjoint`。
形式化陈述：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Disjoint g → f⁻¹.Disjoint g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.inv_eq_iff_eq`：inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x =
 y ↔ x = f y
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem Disjoint.inv_left (h : Disjoint f g) : Disjoint f⁻¹ g := by
  intro x
  rw [inv_eq_iff_eq, eq_comm]
  exact h x
/-
**Equiv.Perm.Disjoint.inv_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Disjoint`。
形式化陈述：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Disjoint g → f.Disjoint g⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.Disjoint.symm`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Disjo
int g → g.Disjoint f
· 使用定理 `Equiv.Perm.Disjoint.inv_left`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.D
isjoint g → f⁻¹.Disjoint g
-/
theorem Disjoint.inv_right (h : Disjoint f g) : Disjoint f g⁻¹ :=
  h.symm.inv_left.symm

@[simp]
/-
**Equiv.Perm.disjoint_inv_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：disjoint_inv_left_iff : Disjoint f⁻¹ g ↔ Disjoint f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.Disjoint.inv_left`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.D
isjoint g → f⁻¹.Disjoint g
-/
theorem disjoint_inv_left_iff : Disjoint f⁻¹ g ↔ Disjoint f g := by
  refine ⟨fun h => ?_, Disjoint.inv_left⟩
  convert! h.inv_left

@[simp]
/-
**Equiv.Perm.disjoint_inv_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：disjoint_inv_right_iff : Disjoint f g⁻¹ ↔ Disjoint f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.disjoint_comm`：disjoint_comm : Disjoint f g ↔ Disjoint g f
· 使用定理 `Equiv.Perm.disjoint_inv_left_iff`：disjoint_inv_left_iff : Disjoint f⁻¹ g
 ↔ Disjoint f g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_inv_right_iff : Disjoint f g⁻¹ ↔ Disjoint f g := by
  rw [disjoint_comm, disjoint_inv_left_iff, disjoint_comm]
/-
**Equiv.Perm.Disjoint.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Disjoint`。
形式化陈述：∀ {α : Type u_1} {f g h : Equiv.Perm α}, f.Disjoint h → g.Disjoint h → (f 
* g).Disjoint h
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem Disjoint.mul_left (H1 : Disjoint f h) (H2 : Disjoint g h) : Disjoint (f * g) h := fun x =>
  by cases H1 x <;> cases H2 x <;> simp [*]
/-
**Equiv.Perm.Disjoint.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Disjoint`。
形式化陈述：∀ {α : Type u_1} {f g h : Equiv.Perm α}, f.Disjoint g → f.Disjoint h → f.D
isjoint (g * h)
参数：g * h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.disjoint_comm`：disjoint_comm : Disjoint f g ↔ Disjoint g f
· 使用定理 `Equiv.Perm.Disjoint.mul_left`：∀ {α : Type u_1} {f g h : Equiv.Perm α}, f
.Disjoint h → g.Disjoint h → (f * g).Disjoint h
· 使用定理 `Equiv.Perm.Disjoint.symm`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Disjo
int g → g.Disjoint f
-/
theorem Disjoint.mul_right (H1 : Disjoint f g) (H2 : Disjoint f h) : Disjoint f (g * h) := by
  rw [disjoint_comm]
  exact H1.symm.mul_left H2.symm

@[simp]
/-
**Equiv.Perm.disjoint_conj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：disjoint_conj (h : Perm α) : Disjoint (h * f * h⁻¹) (h * g * h⁻¹) ↔ Disjoi
nt f g
参数：h : Perm α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.forall_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∀ (a : α), p a) ↔ ∀ (b : β),
 q b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_conj (h : Perm α) : Disjoint (h * f * h⁻¹) (h * g * h⁻¹) ↔ Disjoint f g :=
  (h⁻¹).forall_congr fun {_} ↦ by simp only [mul_apply, eq_inv_iff_eq]
/-
**Equiv.Perm.Disjoint.conj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Disjoint`。
形式化陈述：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Disjoint g → ∀ (h : Equiv.Perm α)
, (h * f * h⁻¹).Disjoint (h * g * h⁻¹)
参数：h : Equiv.Perm α；h * f * h⁻¹；h * g * h⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.disjoint_conj`：disjoint_conj (h : Perm α) : Disjoint (h * f *
 h⁻¹) (h * g * h⁻¹) ↔ Disjoint f g
-/
theorem Disjoint.conj (H : Disjoint f g) (h : Perm α) : Disjoint (h * f * h⁻¹) (h * g * h⁻¹) :=
  (disjoint_conj h).2 H
/-
**Equiv.Perm.disjoint_prod_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：disjoint_prod_right (l : List (Perm α)) (h : forall g in l, Disjoint f g) 
: Disjoint f l.prod
参数：l : List (Perm α)；h : forall g in l, Disjoint f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.disjoint_one_right`：disjoint_one_right (f : Perm α) : Disjoin
t f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `Equiv.Perm.Disjoint.mul_right`：∀ {α : Type u_1} {f g h : Equiv.Perm α}, 
f.Disjoint g → f.Disjoint h → f.Disjoint (g * h)
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
-/
theorem disjoint_prod_right (l : List (Perm α)) (h : ∀ g ∈ l, Disjoint f g) :
    Disjoint f l.prod := by
  induction l with
  | nil => exact disjoint_one_right _
  | cons g l ih =>
    rw [List.prod_cons]
    exact (h _ List.mem_cons_self).mul_right (ih fun g hg => h g (List.mem_cons_of_mem _ hg))
/-
**Equiv.Perm.disjoint_noncommProd_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：disjoint_noncommProd_right {ι : Type*} {k : ι -> Perm α} {s : Finset ι} (h
s : Set.Pairwise s fun i j => Commute (k i) (k j)) (hg : forall i in s, g.Disjoi
nt (k i)) : Disjoint g (s.noncommProd k (hs))
参数：hs : Set.Pairwise s fun i j => Commute (k i) (k j)；hg : forall i in s, g.Disj
oint (k i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.noncommProd_induction`：noncommProd_induction (s : Finset α) (f : 
α -> β) (comm) (p : β -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit
 : p 1) (base : fo…
· 使用定理 `Equiv.Perm.Disjoint.mul_right`：∀ {α : Type u_1} {f g h : Equiv.Perm α}, 
f.Disjoint g → f.Disjoint h → f.Disjoint (g * h)
· 使用定理 `Equiv.Perm.disjoint_one_right`：disjoint_one_right (f : Perm α) : Disjoin
t f 1
-/
theorem disjoint_noncommProd_right {ι : Type*} {k : ι → Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j ↦ Commute (k i) (k j))
    (hg : ∀ i ∈ s, g.Disjoint (k i)) :
    Disjoint g (s.noncommProd k (hs)) :=
  noncommProd_induction s k hs g.Disjoint (fun _ _ ↦ Disjoint.mul_right) (disjoint_one_right g) hg

open scoped List in
/-
**Equiv.Perm.disjoint_prod_perm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：disjoint_prod_perm {l₁ l₂ : List (Perm α)} (hl : l₁.Pairwise Disjoint) (hp
 : l₁ ~ l₂) : l₁.prod = l₂.prod
参数：Perm α；hl : l₁.Pairwise Disjoint；hp : l₁ ~ l₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.prod_eq'`：∀ {M : Type u_4} [inst : Monoid M] {l₁ l₂ : List M},
 l₁.Perm l₂ → List.Pairwise Commute l₁ → l₁.prod = l₂.prod
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
-/
theorem disjoint_prod_perm {l₁ l₂ : List (Perm α)} (hl : l₁.Pairwise Disjoint) (hp : l₁ ~ l₂) :
    l₁.prod = l₂.prod :=
  hp.prod_eq' <| hl.imp Disjoint.commute
/-
**Equiv.Perm.nodup_of_pairwise_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：nodup_of_pairwise_disjoint {l : List (Perm α)} (h1 : (1 : Perm α) ∉ l) (h2
 : l.Pairwise Disjoint) : l.Nodup
参数：Perm α；h1 : (1 : Perm α) ∉ l；h2 : l.Pairwise Disjoint。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nodup_of_pairwise_disjoint {l : List (Perm α)} (h1 : (1 : Perm α) ∉ l)
    (h2 : l.Pairwise Disjoint) : l.Nodup := by
  grind [List.Pairwise.imp_of_mem, disjoint_refl_iff]
/-
**Equiv.Perm.pow_apply_eq_self_of_apply_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv
.Perm`。
形式化陈述：∀ {α : Type u_1} {f : Equiv.Perm α} {x : α}, f x = x → ∀ (n : ℕ), (f ^ n) 
x = x
参数：n : ℕ；f ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) : ∀ n : ℕ, (f ^ n) x = x
  | 0 => rfl
  | n + 1 => by rw [pow_succ, mul_apply, hfx, pow_apply_eq_self_of_apply_eq_self hfx n]
/-
**Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Equi
v.Perm`。
形式化陈述：∀ {α : Type u_1} {f : Equiv.Perm α} {x : α}, f x = x → ∀ (n : ℤ), (f ^ n) 
x = x
参数：n : ℤ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.pow_apply_eq_self_of_apply_eq_self`：∀ {α : Type u_1} {f : Equ
iv.Perm α} {x : α}, f x = x → ∀ (n : ℕ), (f ^ n) x = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Equiv.Perm.inv_eq_iff_eq`：inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x =
 y ↔ x = f y
-/
theorem zpow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) : ∀ n : ℤ, (f ^ n) x = x
  | (n : ℕ) => pow_apply_eq_self_of_apply_eq_self hfx n
  | Int.negSucc n => by rw [zpow_negSucc, inv_eq_iff_eq, pow_apply_eq_self_of_apply_eq_self hfx]
/-
**Equiv.Perm.pow_apply_eq_of_apply_apply_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Equi
v.Perm`。
形式化陈述：∀ {α : Type u_1} {f : Equiv.Perm α} {x : α}, f (f x) = x → ∀ (n : ℕ), (f ^
 n) x = x ∨ (f ^ n) x = f x
参数：f x；n : ℕ；f ^ n；f ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) :
    ∀ n : ℕ, (f ^ n) x = x ∨ (f ^ n) x = f x
  | 0 => Or.inl rfl
  | n + 1 =>
    (pow_apply_eq_of_apply_apply_eq_self hffx n).elim
      (fun h => Or.inr (by rw [pow_succ', mul_apply, h]))
      fun h => Or.inl (by rw [pow_succ', mul_apply, h, hffx])
/-
**Equiv.Perm.zpow_apply_eq_of_apply_apply_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Equ
iv.Perm`。
形式化陈述：∀ {α : Type u_1} {f : Equiv.Perm α} {x : α}, f (f x) = x → ∀ (i : ℤ), (f ^
 i) x = x ∨ (f ^ i) x = f x
参数：f x；i : ℤ；f ^ i；f ^ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.pow_apply_eq_of_apply_apply_eq_self`：∀ {α : Type u_1} {f : Eq
uiv.Perm α} {x : α}, f (f x) = x → ∀ (n : ℕ), (f ^ n) x = x ∨ (f ^ n) x = f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Equiv.Perm.inv_eq_iff_eq`：inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x =
 y ↔ x = f y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
-/
theorem zpow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) :
    ∀ i : ℤ, (f ^ i) x = x ∨ (f ^ i) x = f x
  | (n : ℕ) => pow_apply_eq_of_apply_apply_eq_self hffx n
  | Int.negSucc n => by
    rw [zpow_negSucc, inv_eq_iff_eq, ← f.injective.eq_iff, ← mul_apply, ← pow_succ', eq_comm,
      inv_eq_iff_eq, ← mul_apply, ← pow_succ, @eq_comm _ x, or_comm]
    exact pow_apply_eq_of_apply_apply_eq_self hffx _
/-
**Equiv.Perm.Disjoint.mul_apply_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Dis
joint`。
形式化陈述：∀ {α : Type u_1} {σ τ : Equiv.Perm α}, σ.Disjoint τ → ∀ {a : α}, (σ * τ) a
 = a ↔ σ a = a ∧ τ a = a
参数：σ * τ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Disjoint.mul_apply_eq_iff {σ τ : Perm α} (hστ : Disjoint σ τ) {a : α} :
    (σ * τ) a = a ↔ σ a = a ∧ τ a = a := by
  refine ⟨fun h => ?_, fun h => by rw [mul_apply, h.2, h.1]⟩
  rcases hστ a with hσ | hτ
  · exact ⟨hσ, σ.injective (h.trans hσ.symm)⟩
  · exact ⟨(congr_arg σ hτ).symm.trans h, hτ⟩
/-
**Equiv.Perm.Disjoint.mul_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Disjo
int`。
形式化陈述：∀ {α : Type u_1} {σ τ : Equiv.Perm α}, σ.Disjoint τ → (σ * τ = 1 ↔ σ = 1 ∧
 τ = 1)
参数：σ * τ = 1 ↔ σ = 1 ∧ τ = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Equiv.Perm.Disjoint.mul_apply_eq_iff`：∀ {α : Type u_1} {σ τ : Equiv.Perm
 α}, σ.Disjoint τ → ∀ {a : α}, (σ * τ) a = a ↔ σ a = a ∧ τ a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Disjoint.mul_eq_one_iff {σ τ : Perm α} (hστ : Disjoint σ τ) :
    σ * τ = 1 ↔ σ = 1 ∧ τ = 1 := by
  simp_rw [Perm.ext_iff, one_apply, hστ.mul_apply_eq_iff, forall_and]
/-
**Equiv.Perm.Disjoint.zpow_disjoint_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.D
isjoint`。
形式化陈述：∀ {α : Type u_1} {σ τ : Equiv.Perm α}, σ.Disjoint τ → ∀ (m n : ℤ), (σ ^ m)
.Disjoint (τ ^ n)
参数：m n : ℤ；σ ^ m；τ ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self`：∀ {α : Type u_1} {f : Eq
uiv.Perm α} {x : α}, f x = x → ∀ (n : ℤ), (f ^ n) x = x
-/
theorem Disjoint.zpow_disjoint_zpow {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : ℤ) :
    Disjoint (σ ^ m) (τ ^ n) := fun x =>
  Or.imp (fun h => zpow_apply_eq_self_of_apply_eq_self h m)
    (fun h => zpow_apply_eq_self_of_apply_eq_self h n) (hστ x)
/-
**Equiv.Perm.Disjoint.pow_disjoint_pow** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Dis
joint`。
形式化陈述：∀ {α : Type u_1} {σ τ : Equiv.Perm α}, σ.Disjoint τ → ∀ (m n : ℕ), (σ ^ m)
.Disjoint (τ ^ n)
参数：m n : ℕ；σ ^ m；τ ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.Disjoint.zpow_disjoint_zpow`：∀ {α : Type u_1} {σ τ : Equiv.Pe
rm α}, σ.Disjoint τ → ∀ (m n : ℤ), (σ ^ m).Disjoint (τ ^ n)
-/
theorem Disjoint.pow_disjoint_pow {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : ℕ) :
    Disjoint (σ ^ m) (τ ^ n) :=
  hστ.zpow_disjoint_zpow m n

end Disjoint

section IsSwap

variable [DecidableEq α]

/-- `f.IsSwap` indicates that the permutation `f` is a transposition of two elements. -/
/-
**Equiv.Perm.IsSwap** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：IsSwap (f : Perm α) : Prop
参数：f : Perm α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f.IsSwap` indicates that the permutation `f` is a transposition of two elements
.
-/
def IsSwap (f : Perm α) : Prop :=
  ∃ x y, x ≠ y ∧ f = swap x y

@[simp]
/-
**Equiv.Perm.ofSubtype_swap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：ofSubtype_swap_eq {p : α -> Prop} [DecidablePred p] (x y : Subtype p) : of
Subtype (Equiv.swap x y) = Equiv.swap ↑x ↑y
参数：x y : Subtype p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSubtype_swap_eq {p : α → Prop} [DecidablePred p] (x y : Subtype p) :
    ofSubtype (Equiv.swap x y) = Equiv.swap ↑x ↑y := by
  grind [ofSubtype_apply_of_mem, ofSubtype_apply_of_not_mem]
/-
**Equiv.Perm.IsSwap.of_subtype_isSwap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsSw
ap`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {p : α → Prop} [inst_1 : Decidable
Pred p] {f : Equiv.Perm (Subtype p)},   f.IsSwap → (Equiv.Perm.ofSubtype f).IsSw
ap
参数：Subtype p；Equiv.Perm.ofSubtype f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Equiv.Perm.ofSubtype_swap_eq`：ofSubtype_swap_eq {p : α -> Prop} [Decidab
lePred p] (x y : Subtype p) : ofSubtype (Equiv.swap x y) = Equiv.swap ↑x ↑y
-/
theorem IsSwap.of_subtype_isSwap {p : α → Prop} [DecidablePred p] {f : Perm (Subtype p)}
    (h : f.IsSwap) : (ofSubtype f).IsSwap :=
  let ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := h
  ⟨x, y, by
    simp only [Ne, Subtype.ext_iff] at hxy
    exact hxy.1, by
    rw [hxy.2, ofSubtype_swap_eq]⟩
/-
**Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self** 是 Mathlib 中的一个定理，位于命名空间 `Equi
v.Perm`。
形式化陈述：ne_and_ne_of_swap_mul_apply_ne_self {f : Perm α} {x y : α} (hy : (swap x (
f x) * f) y != y) : f y != y ∧ y != x
参数：hy : (swap x (f x) * f) y != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem ne_and_ne_of_swap_mul_apply_ne_self {f : Perm α} {x y : α} (hy : (swap x (f x) * f) y ≠ y) :
    f y ≠ y ∧ y ≠ x := by
  simp only [swap_apply_def, mul_apply, f.injective.eq_iff] at *
  grind

end IsSwap

section support

section Set

variable (p q : Perm α)

/-
**Equiv.Perm.set_support_symm_eq** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.Perm`。
形式化陈述：set_support_symm_eq : {x | p.symm x != x} = {x | p x != x}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma set_support_symm_eq : {x | p.symm x ≠ x} = {x | p x ≠ x} := by
  ext; simp [eq_symm_apply, eq_comm]
/-
**Equiv.Perm.set_support_apply_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：set_support_apply_mem {p : Perm α} {a : α} : p a in { x | p x != x } ↔ a i
n { x | p x != x }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem set_support_apply_mem {p : Perm α} {a : α} :
    p a ∈ { x | p x ≠ x } ↔ a ∈ { x | p x ≠ x } := by simp
/-
**Equiv.Perm.set_support_zpow_subset** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：set_support_zpow_subset (n : Int) : { x | (p ^ n) x != x } subseteq { x | 
p x != x }
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self`：∀ {α : Type u_1} {f : Eq
uiv.Perm α} {x : α}, f x = x → ∀ (n : ℤ), (f ^ n) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem set_support_zpow_subset (n : ℤ) : { x | (p ^ n) x ≠ x } ⊆ { x | p x ≠ x } := by
  intro x
  simp only [Set.mem_ofPred_eq, Ne]
  intro hx H
  simp [zpow_apply_eq_self_of_apply_eq_self H] at hx
/-
**Equiv.Perm.set_support_mul_subset** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：set_support_mul_subset : { x | (p * q) x != x } subseteq { x | p x != x } 
union { x | q x != x }
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem set_support_mul_subset : { x | (p * q) x ≠ x } ⊆ { x | p x ≠ x } ∪ { x | q x ≠ x } := by
  simp only [coe_mul]
  grind

end Set

@[simp]
/-
**Equiv.Perm.apply_pow_apply_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：apply_pow_apply_eq_iff (f : Perm α) (n : Nat) {x : α} : f ((f ^ n) x) = (f
 ^ n) x ↔ f x = x
参数：f : Perm α；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `Commute.self_pow`：self_pow (a : M) (n : Nat) : Commute a (a ^ n)
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem apply_pow_apply_eq_iff (f : Perm α) (n : ℕ) {x : α} :
    f ((f ^ n) x) = (f ^ n) x ↔ f x = x := by
  rw [← mul_apply, Commute.self_pow f, mul_apply, apply_eq_iff_eq]

@[simp]
/-
**Equiv.Perm.apply_zpow_apply_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：apply_zpow_apply_eq_iff (f : Perm α) (n : Int) {x : α} : f ((f ^ n) x) = (
f ^ n) x ↔ f x = x
参数：f : Perm α；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `Commute.self_zpow`：Commute.self_zpow (A : M) (n : Int) : Commute A (A ^ 
n)
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem apply_zpow_apply_eq_iff (f : Perm α) (n : ℤ) {x : α} :
    f ((f ^ n) x) = (f ^ n) x ↔ f x = x := by
  rw [← mul_apply, Commute.self_zpow f, mul_apply, apply_eq_iff_eq]

variable [DecidableEq α] [Fintype α] {f g : Perm α}

/-- The `Finset` of nonfixed points of a permutation. -/
/-
**Equiv.Perm.support** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：support (f : Perm α) : Finset α
参数：f : Perm α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Finset` of nonfixed points of a permutation.
-/
def support (f : Perm α) : Finset α := {x | f x ≠ x}

@[simp]
/-
**Equiv.Perm.mem_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_support {x : α} : x in f.support ↔ f x != x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.support.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1
 : Fintype α] (f : Equiv.Perm α), f.support = {x | f x ≠ x}
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_support {x : α} : x ∈ f.support ↔ f x ≠ x := by
  rw [support, mem_filter, and_iff_right (mem_univ x)]
/-
**Equiv.Perm.notMem_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：notMem_support {x : α} : x ∉ f.support ↔ f x = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem notMem_support {x : α} : x ∉ f.support ↔ f x = x := by simp
/-
**Equiv.Perm.coe_support_eq_set_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：coe_support_eq_set_support (f : Perm α) : (f.support : Set α) = { x | f x 
!= x }
参数：f : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_support_eq_set_support (f : Perm α) : (f.support : Set α) = { x | f x ≠ x } := by
  ext
  simp

@[simp]
/-
**Equiv.Perm.support_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_eq_empty_iff {σ : Perm α} : σ.support = ∅ ↔ σ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_eq_empty_iff {σ : Perm α} : σ.support = ∅ ↔ σ = 1 := by
  simp_rw [Finset.ext_iff, mem_support, Finset.notMem_empty, iff_false, not_not,
    Equiv.Perm.ext_iff, one_apply]

@[simp]
/-
**Equiv.Perm.support_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_one : (1 : Perm α).support = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.support_eq_empty_iff`：support_eq_empty_iff {σ : Perm α} : σ.s
upport = ∅ ↔ σ = 1
-/
theorem support_one : (1 : Perm α).support = ∅ := by rw [support_eq_empty_iff]

@[simp]
/-
**Equiv.Perm.support_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_refl : support (Equiv.refl α) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.support_one`：support_one : (1 : Perm α).support = ∅
-/
theorem support_refl : support (Equiv.refl α) = ∅ :=
  support_one
/-
**Equiv.Perm.support_congr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_congr (h : f.support subseteq g.support) (h' : forall x in g.suppo
rt, f x = g x) : f = g
参数：h : f.support subseteq g.support；h' : forall x in g.support, f x = g x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_congr (h : f.support ⊆ g.support) (h' : ∀ x ∈ g.support, f x = g x) : f = g := by
  grind [notMem_support]

/-- If g and c commute, then g stabilizes the support of c -/
/-
**Equiv.Perm.mem_support_iff_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_support_iff_of_commute {g c : Perm α} (hgc : Commute g c) (x : α) : g 
x in c.support ↔ x in c.support
参数：hgc : Commute g c；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If g and c commute, then g stabilizes the support of c
-/
theorem mem_support_iff_of_commute {g c : Perm α} (hgc : Commute g c) (x : α) :
    g x ∈ c.support ↔ x ∈ c.support := by
  simp only [mem_support, not_iff_not, ← mul_apply]
  rw [← hgc, mul_apply, Equiv.apply_eq_iff_eq]
/-
**Equiv.Perm.support_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_mul_le (f g : Perm α) : (f * g).support <= f.support ⊔ g.support
参数：f g : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
-/
theorem support_mul_le (f g : Perm α) : (f * g).support ≤ f.support ⊔ g.support := fun x => by
  simp only [sup_eq_union]
  rw [mem_union, mem_support, mem_support, mem_support, mul_apply, ← not_and_or, not_imp_not]
  rintro ⟨hf, hg⟩
  rw [hg, hf]
/-
**Equiv.Perm.exists_mem_support_of_mem_support_prod** 是 Mathlib 中的一个定理，位于命名空间 `E
quiv.Perm`。
形式化陈述：exists_mem_support_of_mem_support_prod {l : List (Perm α)} {x : α} (hx : x
 in l.prod.support) : exists f : Perm α, f in l ∧ x in f.support
参数：Perm α；hx : x in l.prod.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem exists_mem_support_of_mem_support_prod {l : List (Perm α)} {x : α}
    (hx : x ∈ l.prod.support) : ∃ f : Perm α, f ∈ l ∧ x ∈ f.support := by
  contrapose! hx
  simp_rw [mem_support, not_not] at hx ⊢
  induction l with
  | nil => rfl
  | cons f l ih =>
    rw [List.prod_cons, mul_apply, ih, hx]
    · simp only [List.mem_cons, true_or]
    grind
/-
**Equiv.Perm.support_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_pow_le (σ : Perm α) (n : Nat) : (σ ^ n).support <= σ.support
参数：σ : Perm α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.pow_apply_eq_self_of_apply_eq_self`：∀ {α : Type u_1} {f : Equ
iv.Perm α} {x : α}, f x = x → ∀ (n : ℕ), (f ^ n) x = x
-/
theorem support_pow_le (σ : Perm α) (n : ℕ) : (σ ^ n).support ≤ σ.support := fun _ h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (pow_apply_eq_self_of_apply_eq_self h2 n)

@[simp]
/-
**Equiv.Perm.support_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_inv (σ : Perm α) : support σ⁻¹ = σ.support
参数：σ : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.Perm.inv_eq_iff_eq`：inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x =
 y ↔ x = f y
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem support_inv (σ : Perm α) : support σ⁻¹ = σ.support := by
  simp_rw [Finset.ext_iff, mem_support, not_iff_not, inv_eq_iff_eq.trans eq_comm, imp_true_iff]
/-
**Equiv.Perm.apply_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：apply_mem_support {x : α} : f x in f.support ↔ x in f.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem apply_mem_support {x : α} : f x ∈ f.support ↔ x ∈ f.support := by
  rw [mem_support, mem_support, Ne, Ne, apply_eq_iff_eq]

/-- The support of a permutation is invariant -/
/-
**Equiv.Perm.isInvariant_of_support_le** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isInvariant_of_support_le {c : Perm α} {s : Finset α} (hcs : c.support <= 
s) (x : α) : c x in s ↔ x in s
参数：hcs : c.support <= s；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.apply_mem_support`：apply_mem_support {x : α} : f x in f.suppo
rt ↔ x in f.support
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The support of a permutation is invariant
-/
theorem isInvariant_of_support_le {c : Perm α} {s : Finset α} (hcs : c.support ≤ s) (x : α) :
    c x ∈ s ↔ x ∈ s := by
  by_cases hx' : x ∈ c.support
  · simp only [hcs hx', hcs (apply_mem_support.mpr hx')]
  · rw [notMem_support.mp hx']

/-- A permutation c is the extension of a restriction of g to s
  iff its support is contained in s and its restriction is that of g -/
/-
**Equiv.Perm.ofSubtype_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.Perm`。
形式化陈述：ofSubtype_eq_iff {g c : Equiv.Perm α} {s : Finset α} (hg : forall x, g x i
n s ↔ x in s) : ofSubtype (g.subtypePerm hg) = c ↔ c.support <= s ∧ forall (hc' 
: forall x, c x in s ↔ x in s), c.subtypePerm hc' = g.subtypePerm hg
参数：hg : forall x, g x in s ↔ x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_not_mem`：ofSubtype_apply_of_not_mem (f : P
erm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_mem`：ofSubtype_apply_of_mem (f : Perm (Sub
type p)) (ha : p a) : ofSubtype f a = f ⟨a, ha⟩
· 使用定理 `Equiv.Perm.subtypePerm_apply`：subtypePerm_apply (f : Perm α) (h : forall
 x, p (f x) ↔ p x) (x : { x // p x }) : subtypePerm f h x = ⟨f x, (h _).2 x.2⟩
· 使用定理 `Equiv.Perm.isInvariant_of_support_le`：isInvariant_of_support_le {c : Per
m α} {s : Finset α} (hcs : c.support <= s) (x : α) : c x in s ↔ x in s
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用定理 `Finset.notMem_mono`：notMem_mono {s t : Finset α} (h : s subseteq t) {a :
 α} : a ∉ t -> a ∉ s

--- 原说明 ---
A permutation c is the extension of a restriction of g to s
  iff its support is contained in s and its restriction is that of g
-/
lemma ofSubtype_eq_iff {g c : Equiv.Perm α} {s : Finset α}
    (hg : ∀ x, g x ∈ s ↔ x ∈ s) :
    ofSubtype (g.subtypePerm hg) = c ↔
      c.support ≤ s ∧
      ∀ (hc' : ∀ x, c x ∈ s ↔ x ∈ s), c.subtypePerm hc' = g.subtypePerm hg := by
  simp only [Equiv.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  constructor
  · intro h
    constructor
    · intro a ha
      by_contra ha'
      rw [mem_support, ← h a, ofSubtype_apply_of_not_mem (p := (· ∈ s)) _ ha'] at ha
      exact ha rfl
    · intro _ a ha
      rw [← h a, ofSubtype_apply_of_mem (p := (· ∈ s)) _ ha, subtypePerm_apply]
  · rintro ⟨hc, h⟩ a
    specialize h (isInvariant_of_support_le hc)
    by_cases ha : a ∈ s
    · rw [h a ha, ofSubtype_apply_of_mem (p := (· ∈ s)) _ ha, subtypePerm_apply]
    · rw [ofSubtype_apply_of_not_mem (p := (· ∈ s)) _ ha, eq_comm, ← notMem_support]
      exact Finset.notMem_mono hc ha
/-
**Equiv.Perm.support_ofSubtype** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_ofSubtype {p : α -> Prop} [DecidablePred p] (u : Perm (Subtype p))
 : (ofSubtype u).support = u.support.map (Function.Embedding.subtype p)
参数：u : Perm (Subtype p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_prop_of_true`：∀ {p : Prop} {q : p → Prop} (h : p), (∀ (h' : p), q
 h') ↔ q h
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_mem`：ofSubtype_apply_of_mem (f : Perm (Sub
type p)) (ha : p a) : ofSubtype f a = f ⟨a, ha⟩
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_prop_of_false`：∀ {p : Prop} {q : p → Prop}, ¬p → ((∀ (h' : p), q 
h') ↔ True)
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_not_mem`：ofSubtype_apply_of_not_mem (f : P
erm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem support_ofSubtype {p : α → Prop} [DecidablePred p] (u : Perm (Subtype p)) :
    (ofSubtype u).support = u.support.map (Function.Embedding.subtype p) := by
  ext x
  simp only [mem_support, ne_eq, Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists,
    exists_and_right, exists_eq_right, not_iff_comm, not_exists, not_not]
  by_cases hx : p x
  · simp only [forall_prop_of_true hx, ofSubtype_apply_of_mem u hx, ← Subtype.coe_inj]
  · simp only [forall_prop_of_false hx, ofSubtype_apply_of_not_mem u hx]
/-
**Equiv.Perm.mem_support_ofSubtype** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_support_ofSubtype {p : α -> Prop} [DecidablePred p] (x : α) (u : Perm 
(Subtype p)) : x in (ofSubtype u).support ↔ exists (hx : p x), ⟨x, hx⟩ in u.supp
ort
参数：x : α；u : Perm (Subtype p)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.support_ofSubtype`：support_ofSubtype {p : α -> Prop} [Decidab
lePred p] (u : Perm (Subtype p)) : (ofSubtype u).support = u.support.map (Functi
on.Embedding.subty…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_support_ofSubtype {p : α → Prop} [DecidablePred p] (x : α) (u : Perm (Subtype p)) :
    x ∈ (ofSubtype u).support ↔ ∃ (hx : p x), ⟨x, hx⟩ ∈ u.support := by
  simp [support_ofSubtype]
/-
**Equiv.Perm.mem_support_of_mem_noncommProd_support** 是 Mathlib 中的一个定理，位于命名空间 `E
quiv.Perm`。
形式化陈述：mem_support_of_mem_noncommProd_support {α β : Type*} [DecidableEq β] [Fint
ype β] {s : Finset α} {f : α -> Perm β} {comm : (s : Set α).Pairwise (Commute on
 f)} {x : β} (hx : x in (s.noncommProd f comm).support) : exists a in s, x in (f
 a).support
参数：s : Set α；Commute on f；hx : x in (s.noncommProd f comm).support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Equiv.Perm.support_one`：support_one : (1 : Perm α).support = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.noncommProd_insert_of_notMem`：noncommProd_insert_of_notMem [Decid
ableEq α] (s : Finset α) (a : α) (f : α -> β) (comm) (ha : a ∉ s) : noncommProd 
(insert a s) f comm = f a…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finset.mem_of_subset`：mem_of_subset {s₁ s₂ : Finset α} {a : α} : s₁ subs
eteq s₂ -> a in s₁ -> a in s₂
· 使用定理 `Equiv.Perm.support_mul_le`：support_mul_le (f g : Perm α) : (f * g).suppo
rt <= f.support ⊔ g.support
· 使用定理 `Finset.sup_eq_union`：sup_eq_union {s t : Finset α} : s ⊔ t = s union t
· 使用定理 `Finset.notMem_union`：notMem_union : a ∉ s union t ↔ a ∉ s ∧ a ∉ t
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
-/
theorem mem_support_of_mem_noncommProd_support {α β : Type*} [DecidableEq β] [Fintype β]
    {s : Finset α} {f : α → Perm β}
    {comm : (s : Set α).Pairwise (Commute on f)} {x : β} (hx : x ∈ (s.noncommProd f comm).support) :
    ∃ a ∈ s, x ∈ (f a).support := by
  contrapose! hx
  classical
  revert hx comm s
  apply Finset.induction
  · simp
  · intro a s ha ih comm hs
    rw [Finset.noncommProd_insert_of_notMem s a f comm ha]
    apply mt (Finset.mem_of_subset (support_mul_le _ _))
    rw [Finset.sup_eq_union, Finset.notMem_union]
    exact ⟨hs a (s.mem_insert_self a), ih (fun a ha ↦ hs a (Finset.mem_insert_of_mem ha))⟩
/-
**Equiv.Perm.pow_apply_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：pow_apply_mem_support {n : Nat} {x : α} : (f ^ n) x in f.support ↔ x in f.
support
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
theorem pow_apply_mem_support {n : ℕ} {x : α} : (f ^ n) x ∈ f.support ↔ x ∈ f.support := by
  simp only [mem_support, ne_eq, apply_pow_apply_eq_iff]
/-
**Equiv.Perm.zpow_apply_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：zpow_apply_mem_support {n : Int} {x : α} : (f ^ n) x in f.support ↔ x in f
.support
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
theorem zpow_apply_mem_support {n : ℤ} {x : α} : (f ^ n) x ∈ f.support ↔ x ∈ f.support := by
  simp only [mem_support, ne_eq, apply_zpow_apply_eq_iff]
/-
**Equiv.Perm.pow_eq_on_of_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：pow_eq_on_of_mem_support (h : forall x in f.support inter g.support, f x =
 g x) (k : Nat) : forall x in f.support inter g.support, (f ^ k) x = (g ^ k) x
参数：h : forall x in f.support inter g.support, f x = g x；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `Finset.mem_inter`：mem_inter {a : α} {s₁ s₂ : Finset α} : a in s₁ inter s
₂ ↔ a in s₁ ∧ a in s₂
· 使用定理 `Equiv.Perm.apply_mem_support`：apply_mem_support {x : α} : f x in f.suppo
rt ↔ x in f.support
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pow_eq_on_of_mem_support (h : ∀ x ∈ f.support ∩ g.support, f x = g x) (k : ℕ) :
    ∀ x ∈ f.support ∩ g.support, (f ^ k) x = (g ^ k) x := by
  induction k with
  | zero => simp
  | succ k hk =>
    intro x hx
    rw [pow_succ, mul_apply, pow_succ, mul_apply, h _ hx, hk]
    rwa [mem_inter, apply_mem_support, ← h _ hx, apply_mem_support, ← mem_inter]
/-
**Equiv.Perm.disjoint_iff_disjoint_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
`。
形式化陈述：disjoint_iff_disjoint_support : Disjoint f g ↔ _root_.Disjoint f.support g
.support
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
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_iff_disjoint_support : Disjoint f g ↔ _root_.Disjoint f.support g.support := by
  simp [disjoint_iff_eq_or_eq, disjoint_iff, disjoint_iff, Finset.ext_iff,
    imp_iff_not_or]
/-
**Equiv.Perm.Disjoint.disjoint_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Dis
joint`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Fintype α] {f g : Equiv.
Perm α},   f.Disjoint g → Disjoint f.support g.support
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.disjoint_iff_disjoint_support`：disjoint_iff_disjoint_support 
: Disjoint f g ↔ _root_.Disjoint f.support g.support
-/
theorem Disjoint.disjoint_support (h : Disjoint f g) : _root_.Disjoint f.support g.support :=
  disjoint_iff_disjoint_support.1 h
/-
**Equiv.Perm.Disjoint.support_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Disjoint
`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Fintype α] {f g : Equiv.
Perm α},   f.Disjoint g → (f * g).support = f.support ∪ g.support
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Equiv.Perm.support_mul_le`：support_mul_le (f g : Perm α) : (f * g).suppo
rt <= f.support ⊔ g.support
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem Disjoint.support_mul (h : Disjoint f g) : (f * g).support = f.support ∪ g.support := by
  refine le_antisymm (support_mul_le _ _) fun a => ?_
  rw [mem_union, mem_support, mem_support, mem_support, mul_apply, ← not_and_or, not_imp_not]
  exact
    (h a).elim (fun hf h => ⟨hf, f.apply_eq_iff_eq.mp (h.trans hf.symm)⟩) fun hg h =>
      ⟨(congr_arg f hg).symm.trans h, hg⟩
/-
**Equiv.Perm.support_prod_of_pairwise_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.
Perm`。
形式化陈述：support_prod_of_pairwise_disjoint (l : List (Perm α)) (h : l.Pairwise Disj
oint) : l.prod.support = (l.map support).foldr (· ⊔ ·) ⊥
参数：l : List (Perm α)；h : l.Pairwise Disjoint。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.support_one`：support_one : (1 : Perm α).support = ∅
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.disjoint_prod_right`：disjoint_prod_right (l : List (Perm α)) 
(h : forall g in l, Disjoint f g) : Disjoint f l.prod
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.pairwise_cons`：∀ {α : Type u} {R : α → α → Prop} {a : α} {l : List 
α},   List.Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ List.Pairwise R l
· 使用定理 `Equiv.Perm.Disjoint.support_mul`：∀ {α : Type u_1} [inst : DecidableEq α]
 [inst_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g → (f * g).support = f
.support ∪ g.support
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
-/
theorem support_prod_of_pairwise_disjoint (l : List (Perm α)) (h : l.Pairwise Disjoint) :
    l.prod.support = (l.map support).foldr (· ⊔ ·) ⊥ := by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    rw [List.pairwise_cons] at h
    have : Disjoint hd tl.prod := disjoint_prod_right _ h.left
    simp [this.support_mul, hl h.right]
/-
**Equiv.Perm.support_noncommProd** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_noncommProd {ι : Type*} {k : ι -> Perm α} {s : Finset ι} (hs : Set
.Pairwise s fun i j => Disjoint (k i) (k j)) : (s.noncommProd k (hs.imp (fun _ _
 => Perm.Disjoint.commute))).support = s.biUnion fun i => (k i).support
参数：hs : Set.Pairwise s fun i j => Disjoint (k i) (k j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `Set.Pairwise.imp`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, s.P
airwise r → (∀ ⦃a b : α⦄, r a b → p a b) → s.Pairwise p
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.support_one`：support_one : (1 : Perm α).support = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.noncommProd_insert_of_notMem`：noncommProd_insert_of_notMem [Decid
ableEq α] (s : Finset α) (a : α) (f : α -> β) (comm) (ha : a ∉ s) : noncommProd 
(insert a s) f comm = f a…
· 使用引理 `Finset.biUnion_insert`：biUnion_insert [DecidableEq α] {a : α} : (insert 
a s).biUnion t = t a union s.biUnion t
· 使用定理 `Equiv.Perm.Disjoint.support_mul`：∀ {α : Type u_1} [inst : DecidableEq α]
 [inst_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g → (f * g).support = f
.support ∪ g.support
· 使用定理 `Equiv.Perm.disjoint_noncommProd_right`：disjoint_noncommProd_right {ι : T
ype*} {k : ι -> Perm α} {s : Finset ι} (hs : Set.Pairwise s fun i j => Commute (
k i) (k j)) (hg : forall i …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
-/
theorem support_noncommProd {ι : Type*} {k : ι → Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j ↦ Disjoint (k i) (k j)) :
    (s.noncommProd k (hs.imp (fun _ _ ↦ Perm.Disjoint.commute))).support =
      s.biUnion fun i ↦ (k i).support := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j ↦ Disjoint (k i) (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi, Finset.biUnion_insert]
    rw [Equiv.Perm.Disjoint.support_mul, hrec hs']
    apply disjoint_noncommProd_right
    intro j hj
    apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or]
/-
**Equiv.Perm.support_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_prod_le (l : List (Perm α)) : l.prod.support <= (l.map support).fo
ldr (· ⊔ ·) ⊥
参数：l : List (Perm α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.support_one`：support_one : (1 : Perm α).support = ∅
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.foldr_cons`：∀ {α : Type u} {β : Type v} {a : α} {l : List α} {f : α
 → β → β} {b : β},   List.foldr f b (a :: l) = f a (List.foldr f b l)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Equiv.Perm.support_mul_le`：support_mul_le (f g : Perm α) : (f * g).suppo
rt <= f.support ⊔ g.support
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem support_prod_le (l : List (Perm α)) : l.prod.support ≤ (l.map support).foldr (· ⊔ ·) ⊥ := by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    rw [List.prod_cons, List.map_cons, List.foldr_cons]
    refine (support_mul_le hd tl.prod).trans ?_
    exact sup_le_sup le_rfl hl
/-
**Equiv.Perm.support_zpow_le** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_zpow_le (σ : Perm α) (n : Int) : (σ ^ n).support <= σ.support
参数：σ : Perm α；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self`：∀ {α : Type u_1} {f : Eq
uiv.Perm α} {x : α}, f x = x → ∀ (n : ℤ), (f ^ n) x = x
-/
theorem support_zpow_le (σ : Perm α) (n : ℤ) : (σ ^ n).support ≤ σ.support := fun _ h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (zpow_apply_eq_self_of_apply_eq_self h2 n)

@[simp]
/-
**Equiv.Perm.support_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_swap {x y : α} (h : x != y) : support (swap x y) = {x, y}
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_swap {x y : α} (h : x ≠ y) : support (swap x y) = {x, y} := by
  grind [support]
/-
**Equiv.Perm.support_swap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_swap_iff (x y : α) : support (swap x y) = {x, y} ↔ x != y
参数：x y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.swap_self`：swap_self (a : α) : swap a a = Equiv.refl _
· 使用定理 `Equiv.Perm.support_refl`：support_refl : support (Equiv.refl α) = ∅
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Equiv.Perm.support_swap`：support_swap {x y : α} (h : x != y) : support (
swap x y) = {x, y}
-/
theorem support_swap_iff (x y : α) : support (swap x y) = {x, y} ↔ x ≠ y := by
  refine ⟨fun h => ?_, fun h => support_swap h⟩
  rintro rfl
  simp [Finset.ext_iff] at h
/-
**Equiv.Perm.support_swap_mul_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_swap_mul_swap {x y z : α} (h : List.Nodup [x, y, z]) : support (sw
ap x y * swap y z) = {x, y, z}
参数：h : List.Nodup [x, y, z]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.support_swap`：support_swap {x y : α} (h : x != y) : support (
swap x y) = {x, y}
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.union_insert`：union_insert (a : α) (s t : Finset α) : s union ins
ert a t = insert a (s union t)
· 使用定理 `Finset.insert_union`：insert_union (a : α) (s t : Finset α) : insert a s 
union t = insert a (s union t)
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Equiv.Perm.support_mul_le`：support_mul_le (f g : Perm α) : (f * g).suppo
rt <= f.support ⊔ g.support
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
-/
theorem support_swap_mul_swap {x y z : α} (h : List.Nodup [x, y, z]) :
    support (swap x y * swap y z) = {x, y, z} := by
  simp only [List.not_mem_nil, and_true, List.mem_cons, not_false_iff, List.nodup_cons,
    and_self_iff, List.nodup_nil] at h
  push Not at h
  apply le_antisymm
  · convert! support_mul_le (swap x y) (swap y z) using 1
    rw [support_swap h.left.left, support_swap h.right.left]
    simp [-Finset.union_singleton]
  · intro
    simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl | rfl | _) <;>
      simp [swap_apply_of_ne_of_ne, h.left.left, h.left.left.symm, h.left.right.symm,
        h.left.right.left.symm, h.right.left.symm]
/-
**Equiv.Perm.support_swap_mul_ge_support_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.
Perm`。
形式化陈述：support_swap_mul_ge_support_sdiff (f : Perm α) (x y : α) : f.support \ {x,
 y} <= (swap x y * f).support
参数：f : Perm α；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `Equiv.swap_apply_eq_iff`：swap_apply_eq_iff {x y z w : α} : swap x y z = 
w ↔ z = swap x y w
-/
theorem support_swap_mul_ge_support_sdiff (f : Perm α) (x y : α) :
    f.support \ {x, y} ≤ (swap x y * f).support := by
  intro
  simp only [and_imp, Perm.coe_mul, Function.comp_apply, Ne, mem_support, mem_insert, mem_sdiff,
    mem_singleton]
  push Not
  rintro ha ⟨hx, hy⟩ H
  rw [swap_apply_eq_iff, swap_apply_of_ne_of_ne hx hy] at H
  exact ha H

@[deprecated (since := "2026-06-03")]
alias support_swap_mul_ge_support_diff := support_swap_mul_ge_support_sdiff
/-
**Equiv.Perm.support_swap_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_swap_mul_eq (f : Perm α) (x : α) (h : f (f x) != x) : (swap x (f x
) * f).support = f.support \ {x}
参数：f : Perm α；x : α；h : f (f x) != x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.swap_self`：swap_self (a : α) : swap a a = Equiv.refl _
· 使用定理 `Equiv.trans_refl`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.trans (Equi
v.refl β) = e
· 使用定理 `Finset.sdiff_singleton_eq_erase`：sdiff_singleton_eq_erase (a : α) (s : F
inset α) : s \ {a} = s.erase a
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem support_swap_mul_eq (f : Perm α) (x : α) (h : f (f x) ≠ x) :
    (swap x (f x) * f).support = f.support \ {x} := by
  by_cases hx : f x = x
  · simp [hx, sdiff_singleton_eq_erase, notMem_support.mpr hx, erase_eq_of_notMem, pull_end]
  ext z
  by_cases hzx : z = x
  · simp [hzx]
  by_cases hzf : z = f x
  · simp [hzf, hx, h, swap_apply_of_ne_of_ne]
  by_cases hzfx : f z = x
  · simp [Ne.symm hzx, hzx, Ne.symm hzf, hzfx]
  · simp [hzx, hzfx, f.injective.ne hzx, swap_apply_of_ne_of_ne]
/-
**Equiv.Perm.mem_support_swap_mul_imp_mem_support_ne** 是 Mathlib 中的一个定理，位于命名空间 `
Equiv.Perm`。
形式化陈述：mem_support_swap_mul_imp_mem_support_ne {x y : α} (hy : y in support (swap
 x (f x) * f)) : y in support f ∧ y != x
参数：hy : y in support (swap x (f x) * f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem mem_support_swap_mul_imp_mem_support_ne {x y : α} (hy : y ∈ support (swap x (f x) * f)) :
    y ∈ support f ∧ y ≠ x := by
  simp only [mem_support, swap_apply_def, mul_apply, f.injective.eq_iff] at *
  grind

omit [Fintype α] in
/-
**Equiv.Perm.disjoint_swap_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：disjoint_swap_swap {x y z t : α} (h : [x, y, z, t].Nodup) : Disjoint (swap
 x y) (swap z t)
参数：h : [x, y, z, t].Nodup。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_swap_swap {x y z t : α} (h : [x, y, z, t].Nodup) :
    Disjoint (swap x y) (swap z t) := by
  intro; grind
/-
**Equiv.Perm.Disjoint.mem_imp** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Disjoint`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Fintype α] {f g : Equiv.
Perm α},   f.Disjoint g → ∀ {x : α}, x ∈ f.support → x ∉ g.support
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Equiv.Perm.Disjoint.disjoint_support`：∀ {α : Type u_1} [inst : Decidable
Eq α] [inst_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g → Disjoint f.sup
port g.support
-/
theorem Disjoint.mem_imp (h : Disjoint f g) {x : α} (hx : x ∈ f.support) : x ∉ g.support :=
  disjoint_left.mp h.disjoint_support hx
/-
**Equiv.Perm.eq_on_support_mem_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：eq_on_support_mem_disjoint {l : List (Perm α)} (h : f in l) (hl : l.Pairwi
se Disjoint) : forall x in f.support, f x = l.prod x
参数：Perm α；h : f in l；hl : l.Pairwise Disjoint。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用定理 `Equiv.Perm.Disjoint.mem_imp`：∀ {α : Type u_1} [inst : DecidableEq α] [in
st_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g → ∀ {x : α}, x ∈ f.suppor
t → x ∉ g.support
· 使用定理 `Equiv.Perm.disjoint_prod_right`：disjoint_prod_right (l : List (Perm α)) 
(h : forall g in l, Disjoint f g) : Disjoint f l.prod
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.pairwise_cons`：∀ {α : Type u} {R : α → α → Prop} {a : α} {l : List 
α},   List.Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ List.Pairwise R l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Equiv.Perm.Disjoint.symm`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Disjo
int g → g.Disjoint f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
-/
theorem eq_on_support_mem_disjoint {l : List (Perm α)} (h : f ∈ l) (hl : l.Pairwise Disjoint) :
    ∀ x ∈ f.support, f x = l.prod x := by
  induction l with
  | nil => simp at h
  | cons hd tl IH =>
    intro x hx
    rw [List.pairwise_cons] at hl
    rw [List.mem_cons] at h
    rcases h with (rfl | h)
    · rw [List.prod_cons, mul_apply,
        notMem_support.mp ((disjoint_prod_right tl hl.left).mem_imp hx)]
    · rw [List.prod_cons, mul_apply, ← IH h hl.right _ hx, eq_comm, ← notMem_support]
      refine (hl.left _ h).symm.mem_imp ?_
      simpa using hx
/-
**Equiv.Perm.Disjoint.mono** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Disjoint`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Fintype α] {f g x y : Eq
uiv.Perm α},   f.Disjoint g → x.support ⊆ f.support → y.support ⊆ g.support → x.
Disjoint y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.disjoint_iff_disjoint_support`：disjoint_iff_disjoint_support 
: Disjoint f g ↔ _root_.Disjoint f.support g.support
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
-/
theorem Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.support ≤ f.support)
    (hg : y.support ≤ g.support) : Disjoint x y := by
  rw [disjoint_iff_disjoint_support] at h ⊢
  exact h.mono hf hg
/-
**Equiv.Perm.support_le_prod_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_le_prod_of_mem {l : List (Perm α)} (h : f in l) (hl : l.Pairwise D
isjoint) : f.support <= l.prod.support
参数：Perm α；h : f in l；hl : l.Pairwise Disjoint。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.eq_on_support_mem_disjoint`：eq_on_support_mem_disjoint {l : L
ist (Perm α)} (h : f in l) (hl : l.Pairwise Disjoint) : forall x in f.support, f
 x = l.prod x
-/
theorem support_le_prod_of_mem {l : List (Perm α)} (h : f ∈ l) (hl : l.Pairwise Disjoint) :
    f.support ≤ l.prod.support := by
  intro x hx
  rwa [mem_support, ← eq_on_support_mem_disjoint h hl _ hx, ← mem_support]

section ExtendDomain

variable {β : Type*} [DecidableEq β] [Fintype β] {p : β → Prop} [DecidablePred p]

@[simp]
/-
**Equiv.Perm.support_extend_domain** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_extend_domain (f : α ≃ Subtype p) {g : Perm α} : support (g.extend
Domain f) = g.support.map f.asEmbedding
参数：f : α ≃ Subtype p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.Perm.extendDomain_apply_subtype`：∀ {α' : Type u_9} {β' : Type u_10
} (e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype
 p)   {b : β'} (h : p b), (…
· 使用定理 `Equiv.Perm.extendDomain_apply_not_subtype`：∀ {α' : Type u_9} {β' : Type 
u_10} (e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Sub
type p)   {b : β'}, ¬p b → (e.e…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem support_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    support (g.extendDomain f) = g.support.map f.asEmbedding := by
  ext b
  simp only [mem_map, Ne,
    mem_support]
  by_cases pb : p b
  · rw [extendDomain_apply_subtype _ _ pb]
    grind [asEmbedding_apply]
  · rw [extendDomain_apply_not_subtype _ _ pb]
    simp only [not_exists, false_iff, not_and, not_true]
    rintro a _ rfl
    exact pb (Subtype.prop _)
/-
**Equiv.Perm.card_support_extend_domain** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_support_extend_domain (f : α ≃ Subtype p) {g : Perm α} : #(g.extendDo
main f).support = #g.support
参数：f : α ≃ Subtype p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.support_extend_domain`：support_extend_domain (f : α ≃ Subtype
 p) {g : Perm α} : support (g.extendDomain f) = g.support.map f.asEmbedding
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_support_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    #(g.extendDomain f).support = #g.support := by simp

end ExtendDomain

section Card

/-
**Equiv.Perm.card_support_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_support_eq_zero {f : Perm α} : #f.support = 0 ↔ f = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `Equiv.Perm.support_eq_empty_iff`：support_eq_empty_iff {σ : Perm α} : σ.s
upport = ∅ ↔ σ = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem card_support_eq_zero {f : Perm α} : #f.support = 0 ↔ f = 1 := by
  rw [Finset.card_eq_zero, support_eq_empty_iff]
/-
**Equiv.Perm.one_lt_card_support_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
`。
形式化陈述：one_lt_card_support_of_ne_one {f : Perm α} (h : f != 1) : 1 < #f.support
参数：h : f != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `or_self_iff`：∀ {a : Prop}, a ∨ a ↔ a
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
-/
theorem one_lt_card_support_of_ne_one {f : Perm α} (h : f ≠ 1) : 1 < #f.support := by
  simp_rw [one_lt_card_iff, mem_support, ← not_or]
  contrapose! h
  ext a
  specialize h (f a) a
  rwa [apply_eq_iff_eq, or_self_iff, or_self_iff] at h
/-
**Equiv.Perm.card_support_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_support_ne_one (f : Perm α) : #f.support != 1
参数：f : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.card_support_eq_zero`：card_support_eq_zero {f : Perm α} : #f.
support = 0 ↔ f = 1
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Equiv.Perm.one_lt_card_support_of_ne_one`：one_lt_card_support_of_ne_one 
{f : Perm α} (h : f != 1) : 1 < #f.support
-/
theorem card_support_ne_one (f : Perm α) : #f.support ≠ 1 := by
  by_cases h : f = 1
  · exact ne_of_eq_of_ne (card_support_eq_zero.mpr h) zero_ne_one
  · exact ne_of_gt (one_lt_card_support_of_ne_one h)

@[simp]
/-
**Equiv.Perm.card_support_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_support_le_one {f : Perm α} : #f.support <= 1 ↔ f = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `Equiv.Perm.card_support_eq_zero`：card_support_eq_zero {f : Perm α} : #f.
support = 0 ↔ f = 1
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `imp_iff_right`：∀ {b a : Prop}, a → (a → b ↔ b)
· 使用定理 `Equiv.Perm.card_support_ne_one`：card_support_ne_one (f : Perm α) : #f.su
pport != 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem card_support_le_one {f : Perm α} : #f.support ≤ 1 ↔ f = 1 := by
  rw [le_iff_lt_or_eq, Nat.lt_succ_iff, Nat.le_zero, card_support_eq_zero, or_iff_not_imp_right,
    imp_iff_right f.card_support_ne_one]
/-
**Equiv.Perm.two_le_card_support_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
`。
形式化陈述：two_le_card_support_of_ne_one {f : Perm α} (h : f != 1) : 2 <= #f.support
参数：h : f != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.one_lt_card_support_of_ne_one`：one_lt_card_support_of_ne_one 
{f : Perm α} (h : f != 1) : 1 < #f.support
-/
theorem two_le_card_support_of_ne_one {f : Perm α} (h : f ≠ 1) : 2 ≤ #f.support :=
  one_lt_card_support_of_ne_one h
/-
**Equiv.Perm.card_support_swap_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_support_swap_mul {f : Perm α} {x : α} (hx : f x != x) : #(swap x (f x
) * f).support < #f.support
参数：hx : f x != x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Equiv.Perm.mem_support_swap_mul_imp_mem_support_ne`：mem_support_swap_mul
_imp_mem_support_ne {x y : α} (hy : y in support (swap x (f x) * f)) : y in supp
ort f ∧ y != x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem card_support_swap_mul {f : Perm α} {x : α} (hx : f x ≠ x) :
    #(swap x (f x) * f).support < #f.support :=
  Finset.card_lt_card
    ⟨fun _ hz => (mem_support_swap_mul_imp_mem_support_ne hz).left, fun h =>
      absurd (h (mem_support.2 hx)) (mt mem_support.1 (by simp))⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Equiv.Perm.card_support_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_support_swap {x y : α} (hxy : x != y) : #(swap x y).support = 2
参数：hxy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.nodup_cons`：nodup_cons {a : α} {s : Multiset α} : Nodup (a ::ₘ 
s) ↔ a ∉ s ∧ Nodup s
· 使用定理 `Equiv.Perm.support_swap`：support_swap {x y : α} (h : x != y) : support (
swap x y) = {x, y}
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem card_support_swap {x y : α} (hxy : x ≠ y) : #(swap x y).support = 2 :=
  show #(swap x y).support = #⟨x ::ₘ y ::ₘ 0, by simp [hxy]⟩ from
    congr_arg card <| by simp [support_swap hxy, *, Finset.ext_iff]

@[simp]
/-
**Equiv.Perm.card_support_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_support_eq_two {f : Perm α} : #f.support = 2 ↔ IsSwap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_eq_succ`：card_eq_succ : #s = n + 1 ↔ exists a t, a ∉ t ∧ ins
ert a t = s ∧ #t = n
· 使用定理 `Finset.card_eq_one`：card_eq_one : #s = 1 ↔ exists a, s = {a}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `Equiv.Perm.card_support_swap`：card_support_swap {x y : α} (hxy : x != y)
 : #(swap x y).support = 2
-/
theorem card_support_eq_two {f : Perm α} : #f.support = 2 ↔ IsSwap f := by
  constructor <;> intro h
  · obtain ⟨x, t, hmem, hins, ht⟩ := card_eq_succ.1 h
    obtain ⟨y, rfl⟩ := card_eq_one.1 ht
    rw [mem_singleton] at hmem
    refine ⟨x, y, hmem, ?_⟩
    ext a
    have key : ∀ b, f b ≠ b ↔ _ := fun b => by rw [← mem_support, ← hins, mem_insert, mem_singleton]
    by_cases ha : f a = a
    · have ha' := not_or.mp (mt (key a).mpr (not_not.mpr ha))
      rw [ha, swap_apply_of_ne_of_ne ha'.1 ha'.2]
    · have ha' := (key (f a)).mp (mt f.apply_eq_iff_eq.mp ha)
      obtain rfl | rfl := (key a).mp ha
      · rw [Or.resolve_left ha' ha, swap_apply_left]
      · rw [Or.resolve_right ha' ha, swap_apply_right]
  · obtain ⟨x, y, hxy, rfl⟩ := h
    exact card_support_swap hxy
/-
**Equiv.Perm.Disjoint.card_support_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Dis
joint`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Fintype α] {f g : Equiv.
Perm α},   f.Disjoint g → (f * g).support.card = f.support.card + g.support.card
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Equiv.Perm.Disjoint.disjoint_support`：∀ {α : Type u_1} [inst : Decidable
Eq α] [inst_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g → Disjoint f.sup
port g.support
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.Disjoint.support_mul`：∀ {α : Type u_1} [inst : DecidableEq α]
 [inst_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g → (f * g).support = f
.support ∪ g.support
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Disjoint.card_support_mul (h : Disjoint f g) :
    #(f * g).support = #f.support + #g.support := by
  rw [← Finset.card_union_of_disjoint]
  · congr
    ext
    simp [h.support_mul]
  · simpa using h.disjoint_support
/-
**Equiv.Perm.card_support_prod_list_of_pairwise_disjoint** 是 Mathlib 中的一个定理，位于命名
空间 `Equiv.Perm`。
形式化陈述：card_support_prod_list_of_pairwise_disjoint {l : List (Perm α)} (h : l.Pai
rwise Disjoint) : #l.prod.support = (l.map (card ∘ support)).sum
参数：Perm α；h : l.Pairwise Disjoint。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.card_support_eq_zero`：card_support_eq_zero {f : Perm α} : #f.
support = 0 ↔ f = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.pairwise_cons`：∀ {α : Type u} {R : α → α → Prop} {a : α} {l : List 
α},   List.Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ List.Pairwise R l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.sum_cons`：∀ {α : Type u} [inst : Add α] [inst_1 : Zero α] {a : α} {
l : List α}, (a :: l).sum = a + l.sum
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.Disjoint.card_support_mul`：∀ {α : Type u_1} [inst : Decidable
Eq α] [inst_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g → (f * g).suppor
t.card = f.support.card + …
· 使用定理 `Equiv.Perm.disjoint_prod_right`：disjoint_prod_right (l : List (Perm α)) 
(h : forall g in l, Disjoint f g) : Disjoint f l.prod
-/
theorem card_support_prod_list_of_pairwise_disjoint {l : List (Perm α)} (h : l.Pairwise Disjoint) :
    #l.prod.support = (l.map (card ∘ support)).sum := by
  induction l with
  | nil => exact card_support_eq_zero.mpr rfl
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.1 h
    rw [List.prod_cons, List.map_cons, List.sum_cons, ← ih ht]
    exact (disjoint_prod_right _ ha).card_support_mul

end Card

end support

@[simp]
/-
**Equiv.Perm.support_subtypePerm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_subtypePerm [DecidableEq α] {s : Finset α} (f : Perm α) (h) : (f.s
ubtypePerm h : Perm s).support = ({x | f x != x} : Finset s)
参数：f : Perm α；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_subtypePerm [DecidableEq α] {s : Finset α} (f : Perm α) (h) :
    (f.subtypePerm h : Perm s).support = ({x | f x ≠ x} : Finset s) := by
  ext; simp [Subtype.ext_iff]

end Equiv.Perm

section FixedPoints

namespace Equiv.Perm
/-!
### Fixed points
-/

variable {α : Type*}

/-
**Equiv.Perm.fixed_point_card_lt_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
`。
形式化陈述：fixed_point_card_lt_of_ne_one [DecidableEq α] [Fintype α] {σ : Perm α} (h 
: σ != 1) : #{x | σ x = x} < Fintype.card α - 1
参数：h : σ != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_sub_iff_add_lt`：∀ {a b c : ℕ}, a < c - b ↔ a + b < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_sub_iff_add_lt'`：∀ {a b c : ℕ}, a < c - b ↔ b + a < c
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Finset.compl_filter`：compl_filter (p : α -> Prop) [DecidablePred p] [for
all x, Decidable ¬p x] : (univ.filter p)ᶜ = univ.filter fun x => ¬p x
· 使用定理 `Equiv.Perm.one_lt_card_support_of_ne_one`：one_lt_card_support_of_ne_one 
{f : Perm α} (h : f != 1) : 1 < #f.support
-/
theorem fixed_point_card_lt_of_ne_one [DecidableEq α] [Fintype α] {σ : Perm α} (h : σ ≠ 1) :
    #{x | σ x = x} < Fintype.card α - 1 := by
  rw [Nat.lt_sub_iff_add_lt, ← Nat.lt_sub_iff_add_lt', ← Finset.card_compl, Finset.compl_filter]
  exact one_lt_card_support_of_ne_one h

end Equiv.Perm

end FixedPoints

section Conjugation

namespace Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α] {σ τ : Perm α}

@[simp]
/-
**Equiv.Perm.support_conj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：support_conj : (σ * τ * σ⁻¹).support = τ.support.map σ.toEmbedding
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_conj : (σ * τ * σ⁻¹).support = τ.support.map σ.toEmbedding := by
  ext
  simp only [mem_map_equiv, Perm.coe_mul, Function.comp_apply, Ne, Perm.mem_support,
    Equiv.eq_symm_apply, inv_def]
/-
**Equiv.Perm.card_support_conj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_support_conj : #(σ * τ * σ⁻¹).support = #τ.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.support_conj`：support_conj : (σ * τ * σ⁻¹).support = τ.suppor
t.map σ.toEmbedding
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_support_conj : #(σ * τ * σ⁻¹).support = #τ.support := by simp

end Equiv.Perm

end Conjugation

