/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Support
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.RingTheory.HahnSeries.Basic
public import Mathlib.Tactic.FastInstance

/-!
# Additive properties of Hahn series

If `Γ` is ordered and `R` has zero, then `R⟦Γ⟧` consists of formal series over `Γ` with coefficients
in `R`, whose supports are partially well-ordered. With further structure on `R` and `Γ`, we can add
further structure on `R⟦Γ⟧`.  When `R` has an addition operation, `R⟦Γ⟧` also has addition by adding
coefficients.

## Main Definitions
* If `R` is a (commutative) additive monoid or group, then so is `R⟦Γ⟧`.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

@[expose] public section


open Finset Function

noncomputable section

variable {Γ Γ' R S U V α : Type*}

namespace HahnSeries

section SMulZeroClass

variable [PartialOrder Γ] {V : Type*} [Zero V] [SMulZeroClass R V]

/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul R V⟦Γ⟧ :=
  ⟨fun r x =>
    { coeff := r • x.coeff
      isPWO_support' := x.isPWO_support.mono (Function.support_const_smul_subset ..) }⟩
/-
**HahnSeries.support_smul_subset** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_smul_subset (r : R) (x : HahnSeries Γ V) : (r • x).support subsete
q x.support
参数：r : R；x : HahnSeries Γ V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.support_const_smul_subset`：support_const_smul_subset [Zero M] [
SMulZeroClass R M] (a : R) (f : α -> M) : support (a • f) subseteq support f
-/
theorem support_smul_subset (r : R) (x : HahnSeries Γ V) : (r • x).support ⊆ x.support :=
  Function.support_const_smul_subset ..

@[simp]
/-
**HahnSeries.coeff_smul'** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_smul' (r : R) (x : V⟦Γ⟧) : (r • x).coeff = r • x.coeff
参数：r : R；x : V⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_smul' (r : R) (x : V⟦Γ⟧) : (r • x).coeff = r • x.coeff :=
  rfl

@[simp]
/-
**HahnSeries.coeff_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_smul {r : R} {x : V⟦Γ⟧} {a : Γ} : (r • x).coeff a = r • x.coeff a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_smul {r : R} {x : V⟦Γ⟧} {a : Γ} : (r • x).coeff a = r • x.coeff a :=
  rfl
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulZeroClass R V⟦Γ⟧ where
  smul_zero _ := by
    ext
    simp only [coeff_smul, coeff_zero, smul_zero]
/-
**HahnSeries.orderTop_smul_not_lt** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_smul_not_lt (r : R) (x : V⟦Γ⟧) : ¬ (r • x).orderTop < x.orderTop
参数：r : R；x : V⟦Γ⟧。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `not_top_lt`：not_top_lt : ¬⊤ < a
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用引理 `right_ne_zero_of_smul`：right_ne_zero_of_smul {a : M} {b : A} : a • b != 
0 -> b != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `Set.IsWF.min_of_subset_not_lt_min`：∀ {α : Type u_2} [inst : Preorder α] 
{s t : Set α} {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF} {htn : t.Nonempty},
   s ⊆ t → ¬hs.min hsn …
· 使用引理 `Function.support_smul_subset_right`：support_smul_subset_right [Zero M] [
SMulZeroClass R M] (f : α -> R) (g : α -> M) : support (f • g) subseteq support 
g
-/
theorem orderTop_smul_not_lt (r : R) (x : V⟦Γ⟧) : ¬ (r • x).orderTop < x.orderTop := by
  by_cases hrx : r • x = 0
  · rw [hrx, orderTop_zero]
    exact not_top_lt
  · simp only [orderTop_of_ne_zero hrx, orderTop_of_ne_zero <| right_ne_zero_of_smul hrx,
      WithTop.coe_lt_coe]
    exact Set.IsWF.min_of_subset_not_lt_min (Function.support_smul_subset_right ..)
/-
**HahnSeries.orderTop_le_orderTop_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_le_orderTop_smul {Γ} [LinearOrder Γ] (r : R) (x : V⟦Γ⟧) : x.order
Top <= (r • x).orderTop
参数：r : R；x : V⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `HahnSeries.orderTop_smul_not_lt`：orderTop_smul_not_lt (r : R) (x : V⟦Γ⟧)
 : ¬ (r • x).orderTop < x.orderTop
-/
theorem orderTop_le_orderTop_smul {Γ} [LinearOrder Γ] (r : R) (x : V⟦Γ⟧) :
    x.orderTop ≤ (r • x).orderTop :=
  le_of_not_gt <| orderTop_smul_not_lt r x
/-
**HahnSeries.order_smul_not_lt** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：order_smul_not_lt [Zero Γ] (r : R) (x : V⟦Γ⟧) (h : r • x != 0) : ¬ (r • x)
.order < x.order
参数：r : R；x : V⟦Γ⟧；h : r • x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `right_ne_zero_of_smul`：right_ne_zero_of_smul {a : M} {b : A} : a • b != 
0 -> b != 0
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false`：¬False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Set.IsWF.min_of_subset_not_lt_min`：∀ {α : Type u_2} [inst : Preorder α] 
{s t : Set α} {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF} {htn : t.Nonempty},
   s ⊆ t → ¬hs.min hsn …
· 使用引理 `Function.support_smul_subset_right`：support_smul_subset_right [Zero M] [
SMulZeroClass R M] (f : α -> R) (g : α -> M) : support (f • g) subseteq support 
g
-/
theorem order_smul_not_lt [Zero Γ] (r : R) (x : V⟦Γ⟧) (h : r • x ≠ 0) :
    ¬ (r • x).order < x.order := by
  have hx : x ≠ 0 := right_ne_zero_of_smul h
  simp_all only [order, dite_false]
  exact Set.IsWF.min_of_subset_not_lt_min (Function.support_smul_subset_right ..)
/-
**HahnSeries.le_order_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：le_order_smul {Γ} [Zero Γ] [LinearOrder Γ] (r : R) (x : V⟦Γ⟧) (h : r • x !
= 0) : x.order <= (r • x).order
参数：r : R；x : V⟦Γ⟧；h : r • x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `HahnSeries.order_smul_not_lt`：order_smul_not_lt [Zero Γ] (r : R) (x : V⟦
Γ⟧) (h : r • x != 0) : ¬ (r • x).order < x.order
-/
theorem le_order_smul {Γ} [Zero Γ] [LinearOrder Γ] (r : R) (x : V⟦Γ⟧) (h : r • x ≠ 0) :
    x.order ≤ (r • x).order :=
  le_of_not_gt (order_smul_not_lt r x h)
/-
**HahnSeries.truncLT_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：truncLT_smul [DecidableLT Γ] (c : Γ) (r : R) (x : V⟦Γ⟧) : truncLT c (r • x
) = r • truncLT c x
参数：c : Γ；r : R；x : V⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem truncLT_smul [DecidableLT Γ] (c : Γ) (r : R) (x : V⟦Γ⟧) :
    truncLT c (r • x) = r • truncLT c x := by ext; simp

end SMulZeroClass

section Addition

variable [PartialOrder Γ]

section AddMonoid

variable [AddMonoid R]

/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add R⟦Γ⟧ where
  add x y :=
    { coeff := x.coeff + y.coeff
      isPWO_support' := (x.isPWO_support.union y.isPWO_support).mono (Function.support_add ..) }
/-
**HahnSeries.support_add_subset** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_add_subset (x y : R⟦Γ⟧) : (x + y).support subseteq x.support union
 y.support
参数：x y : R⟦Γ⟧。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.support_add`：∀ {α : Type u_1} {M : Type u_2} [inst : AddZeroCla
ss M] (f g : α → M),   (Function.support fun x => f x + g x) ⊆ Function.support 
f ∪ Functi…
-/
theorem support_add_subset (x y : R⟦Γ⟧) : (x + y).support ⊆ x.support ∪ y.support :=
  Function.support_add ..

@[simp]
/-
**HahnSeries.coeff_add'** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_add' (x y : R⟦Γ⟧) : (x + y).coeff = x.coeff + y.coeff
参数：x y : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_add' (x y : R⟦Γ⟧) : (x + y).coeff = x.coeff + y.coeff :=
  rfl
/-
**HahnSeries.coeff_add** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_add {x y : R⟦Γ⟧} {a : Γ} : (x + y).coeff a = x.coeff a + y.coeff a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_add {x y : R⟦Γ⟧} {a : Γ} : (x + y).coeff a = x.coeff a + y.coeff a :=
  rfl
/-
**HahnSeries.single_add** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} [inst : PartialOrder Γ] [inst_1 : AddMonoi
d R] (a : Γ) (r s : R),   (HahnSeries.single a) (r + s) = (HahnSeries.single a) 
r + (HahnSeries.single a) s
参数：a : Γ；r s : R；HahnSeries.single a；r + s；HahnSeries.single a；HahnSeries.single
 a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `Pi.single_add`：∀ {I : Type u} {f : I → Type v} [inst : DecidableEq I] [i
nst_1 : (i : I) → AddZeroClass (f i)] (i : I) (x y : f i),   Pi.single i (x + y)
 = …
-/
@[simp] theorem single_add (a : Γ) (r s : R) : single a (r + s) = single a r + single a s := by
  classical
  ext : 1; exact Pi.single_add (f := fun _ => R) a r s
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMonoid R⟦Γ⟧ := fast_instance%
  coeff_injective.addMonoid _
    coeff_zero' coeff_add' (fun _ _ => coeff_smul' _ _)
/-
**HahnSeries.coeff_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_nsmul {x : R⟦Γ⟧} {n : Nat} : (n • x).coeff = n • x.coeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.coeff_smul'`：coeff_smul' (r : R) (x : V⟦Γ⟧) : (r • x).coeff =
 r • x.coeff
-/
theorem coeff_nsmul {x : R⟦Γ⟧} {n : ℕ} : (n • x).coeff = n • x.coeff := coeff_smul' _ _

@[simp]
/-
**HahnSeries.map_add** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4} [inst : PartialOrder Γ] [in
st_1 : AddMonoid R] [inst_2 : AddMonoid S]   (f : R →+ S) {x y : HahnSeries Γ R}
, (x + y).map f = x.map f + y.map f
参数：f : R →+ S；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.map_coeff`：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4} [in
st : PartialOrder Γ] [inst_1 : Zero R] [inst_2 : Zero S]   (x : HahnSeries Γ R) 
{F : Type …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_add [AddMonoid S] (f : R →+ S) {x y : R⟦Γ⟧} :
    ((x + y).map f : S⟦Γ⟧) = x.map f + y.map f := by
  ext; simp
/--
`addOppositeEquiv` is an additive monoid isomorphism between
Hahn series over `Γ` with coefficients in the opposite additive monoid `Rᵃᵒᵖ`
and the additive opposite of Hahn series over `Γ` with coefficients `R`.
-/
@[simps -isSimp]
/-
**HahnSeries.addOppositeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：addOppositeEquiv : Rᵃᵒᵖ⟦Γ⟧ ≃+ R⟦Γ⟧ᵃᵒᵖ where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`addOppositeEquiv` is an additive monoid isomorphism between
Hahn series over `Γ` with coefficients in the opposite additive monoid `Rᵃᵒᵖ`
and the additive opposite of Hahn series over `Γ` with coefficients `R`.
-/
def addOppositeEquiv : Rᵃᵒᵖ⟦Γ⟧ ≃+ R⟦Γ⟧ᵃᵒᵖ where
  toFun x := .op ⟨fun a ↦ (x.coeff a).unop, by convert! x.isPWO_support; ext; simp⟩
  invFun x := ⟨fun a ↦ .op (x.unop.coeff a), by convert! x.unop.isPWO_support; ext; simp⟩
  left_inv x := by simp
  right_inv x := by
    apply AddOpposite.unop_injective
    simp
  map_add' x y := by
    apply AddOpposite.unop_injective
    ext
    simp

@[simp]
/-
**HahnSeries.addOppositeEquiv_support** 是 Mathlib 中的一个引理，位于命名空间 `HahnSeries`。
形式化陈述：addOppositeEquiv_support (x : Rᵃᵒᵖ⟦Γ⟧) : (addOppositeEquiv x).unop.support
 = x.support
参数：x : Rᵃᵒᵖ⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.addOppositeEquiv_apply`：∀ {Γ : Type u_1} {R : Type u_3} [inst
 : PartialOrder Γ] [inst_1 : AddMonoid R] (x : HahnSeries Γ Rᵃᵒᵖ),   HahnSeries.
addOppositeEquiv x = Ad…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma addOppositeEquiv_support (x : Rᵃᵒᵖ⟦Γ⟧) :
    (addOppositeEquiv x).unop.support = x.support := by
  ext
  simp [addOppositeEquiv_apply]

@[simp]
/-
**HahnSeries.addOppositeEquiv_symm_support** 是 Mathlib 中的一个引理，位于命名空间 `HahnSeries
`。
形式化陈述：addOppositeEquiv_symm_support (x : R⟦Γ⟧ᵃᵒᵖ) : (addOppositeEquiv.symm x).su
pport = x.unop.support
参数：x : R⟦Γ⟧ᵃᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HahnSeries.addOppositeEquiv_support`：addOppositeEquiv_support (x : Rᵃᵒᵖ⟦
Γ⟧) : (addOppositeEquiv x).unop.support = x.support
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
-/
lemma addOppositeEquiv_symm_support (x : R⟦Γ⟧ᵃᵒᵖ) :
    (addOppositeEquiv.symm x).support = x.unop.support := by
  rw [← addOppositeEquiv_support, AddEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**HahnSeries.addOppositeEquiv_orderTop** 是 Mathlib 中的一个引理，位于命名空间 `HahnSeries`。
形式化陈述：addOppositeEquiv_orderTop (x : Rᵃᵒᵖ⟦Γ⟧) : (addOppositeEquiv x).unop.orderT
op = x.orderTop
参数：x : Rᵃᵒᵖ⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用引理 `HahnSeries.addOppositeEquiv_support`：addOppositeEquiv_support (x : Rᵃᵒᵖ⟦
Γ⟧) : (addOppositeEquiv x).unop.support = x.support
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Set.IsWF.min.congr_simp`：∀ {α : Type u_2} [inst : Preorder α] {s s_1 : S
et α} (e_s : s = s_1) (hs : s.IsWF) (hn : s.Nonempty),   hs.min hn = ⋯.min ⋯
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.addOppositeEquiv_apply`：∀ {Γ : Type u_1} {R : Type u_3} [inst
 : PartialOrder Γ] [inst_1 : AddMonoid R] (x : HahnSeries Γ Rᵃᵒᵖ),   HahnSeries.
addOppositeEquiv x = Ad…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma addOppositeEquiv_orderTop (x : Rᵃᵒᵖ⟦Γ⟧) :
    (addOppositeEquiv x).unop.orderTop = x.orderTop := by
  classical
  simp only [orderTop,
    addOppositeEquiv_support]
  simp only [addOppositeEquiv_apply, AddOpposite.unop_op, mk_eq_zero]
  simp_rw [HahnSeries.ext_iff, funext_iff]
  simp only [Pi.zero_apply, AddOpposite.unop_eq_zero_iff, coeff_zero]

@[simp]
/-
**HahnSeries.addOppositeEquiv_symm_orderTop** 是 Mathlib 中的一个引理，位于命名空间 `HahnSerie
s`。
形式化陈述：addOppositeEquiv_symm_orderTop (x : R⟦Γ⟧ᵃᵒᵖ) : (addOppositeEquiv.symm x).o
rderTop = x.unop.orderTop
参数：x : R⟦Γ⟧ᵃᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HahnSeries.addOppositeEquiv_orderTop`：addOppositeEquiv_orderTop (x : Rᵃᵒ
ᵖ⟦Γ⟧) : (addOppositeEquiv x).unop.orderTop = x.orderTop
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
-/
lemma addOppositeEquiv_symm_orderTop (x : R⟦Γ⟧ᵃᵒᵖ) :
    (addOppositeEquiv.symm x).orderTop = x.unop.orderTop := by
  rw [← addOppositeEquiv_orderTop, AddEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**HahnSeries.addOppositeEquiv_leadingCoeff** 是 Mathlib 中的一个引理，位于命名空间 `HahnSeries
`。
形式化陈述：addOppositeEquiv_leadingCoeff (x : Rᵃᵒᵖ⟦Γ⟧) : (addOppositeEquiv x).unop.le
adingCoeff = x.leadingCoeff.unop
参数：x : Rᵃᵒᵖ⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `HahnSeries.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R⟦Γ⟧
) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `HahnSeries.orderTop_ne_top`：orderTop_ne_top : orderTop x != ⊤ ↔ x != 0
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `HahnSeries.addOppositeEquiv_orderTop`：addOppositeEquiv_orderTop (x : Rᵃᵒ
ᵖ⟦Γ⟧) : (addOppositeEquiv x).unop.orderTop = x.orderTop
· 使用定理 `HahnSeries.leadingCoeff_of_ne_zero`：leadingCoeff_of_ne_zero {x : R⟦Γ⟧} (
hx : x != 0) : x.leadingCoeff = x.coeff (x.orderTop.untop <| orderTop_ne_top.2 h
x)
· 使用定理 `WithTop.untop.congr_simp`：∀ {α : Type u_1} (x x_1 : WithTop α) (e_x : x 
= x_1) (a : x ≠ ⊤), x.untop a = x_1.untop ⋯
-/
lemma addOppositeEquiv_leadingCoeff (x : Rᵃᵒᵖ⟦Γ⟧) :
    (addOppositeEquiv x).unop.leadingCoeff = x.leadingCoeff.unop := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  simp only [ne_eq, AddOpposite.unop_eq_zero_iff, EmbeddingLike.map_eq_zero_iff, hx,
    not_false_eq_true, leadingCoeff_of_ne_zero, addOppositeEquiv_orderTop]
  simp [addOppositeEquiv]

@[simp]
/-
**HahnSeries.addOppositeEquiv_symm_leadingCoeff** 是 Mathlib 中的一个引理，位于命名空间 `HahnS
eries`。
形式化陈述：addOppositeEquiv_symm_leadingCoeff (x : R⟦Γ⟧ᵃᵒᵖ) : (addOppositeEquiv.symm 
x).leadingCoeff = .op x.unop.leadingCoeff
参数：x : R⟦Γ⟧ᵃᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddOpposite.unop_injective`：∀ {α : Type u_1}, Function.Injective AddOppo
site.unop
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HahnSeries.addOppositeEquiv_leadingCoeff`：addOppositeEquiv_leadingCoeff 
(x : Rᵃᵒᵖ⟦Γ⟧) : (addOppositeEquiv x).unop.leadingCoeff = x.leadingCoeff.unop
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
· 使用定理 `AddOpposite.unop_op`：∀ {α : Type u_1} (x : α), AddOpposite.unop (AddOppo
site.op x) = x
-/
lemma addOppositeEquiv_symm_leadingCoeff (x : R⟦Γ⟧ᵃᵒᵖ) :
    (addOppositeEquiv.symm x).leadingCoeff = .op x.unop.leadingCoeff := by
  apply AddOpposite.unop_injective
  rw [← addOppositeEquiv_leadingCoeff, AddEquiv.apply_symm_apply, AddOpposite.unop_op]
/-
**HahnSeries.min_le_min_add** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：∀ {R : Type u_3} [inst : AddMonoid R] {Γ : Type u_8} [inst_1 : LinearOrder
 Γ] {x y : HahnSeries Γ R} (hx : x ≠ 0)   (hy : y ≠ 0) (hxy : x + y ≠ 0), min (⋯
.min ⋯) (⋯.min ⋯) ≤ ⋯.min ⋯
参数：hx : x ≠ 0；hy : y ≠ 0；hxy : x + y ≠ 0；⋯.min ⋯；⋯.min ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `Set.IsWF.union`：∀ {α : Type u_2} [inst : Preorder α] {s t : Set α}, s.Is
WF → t.IsWF → (s ∪ t).IsWF
· 使用定理 `Set.union_nonempty`：union_nonempty : (s union t).Nonempty ↔ s.Nonempty ∨
 t.Nonempty
· 使用定理 `Or.intro_left`：∀ {a : Prop} (b : Prop), a → a ∨ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.IsWF.min_union`：∀ {α : Type u_2} [inst : LinearOrder α] {s t : Set α
} (hs : s.IsWF) (hsn : s.Nonempty) (ht : t.IsWF) (htn : t.Nonempty),   ⋯.min ⋯ =
 min (hs…
· 使用定理 `Set.IsWF.min_le_min_of_subset`：∀ {α : Type u_2} [inst : LinearOrder α] {
s t : Set α} {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF} {htn : t.Nonempty}, 
  s ⊆ t → ht.min ht…
· 使用定理 `HahnSeries.support_add_subset`：support_add_subset (x y : R⟦Γ⟧) : (x + y)
.support subseteq x.support union y.support
-/
protected theorem min_le_min_add {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} (hx : x ≠ 0)
    (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (Set.IsWF.min x.isWF_support (support_nonempty_iff.2 hx))
      (Set.IsWF.min y.isWF_support (support_nonempty_iff.2 hy)) ≤
      Set.IsWF.min (x + y).isWF_support (support_nonempty_iff.2 hxy) := by
  rw [← Set.IsWF.min_union]
  exact Set.IsWF.min_le_min_of_subset (support_add_subset (x := x) (y := y))
/-
**HahnSeries.min_orderTop_le_orderTop_add** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`
。
形式化陈述：min_orderTop_le_orderTop_add {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} : min x.orde
rTop y.orderTop <= (x + y).orderTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_min`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), ↑(mi
n a b) = min ↑a ↑b
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `HahnSeries.min_le_min_add`：∀ {R : Type u_3} [inst : AddMonoid R] {Γ : Ty
pe u_8} [inst_1 : LinearOrder Γ] {x y : HahnSeries Γ R} (hx : x ≠ 0)   (hy : y ≠
 0) (hxy : x + …
-/
theorem min_orderTop_le_orderTop_add {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} :
    min x.orderTop y.orderTop ≤ (x + y).orderTop := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  by_cases hxy : x + y = 0; · simp [hxy]
  rw [orderTop_of_ne_zero hx, orderTop_of_ne_zero hy, orderTop_of_ne_zero hxy, ← WithTop.coe_min,
    WithTop.coe_le_coe]
  exact HahnSeries.min_le_min_add hx hy hxy
/-
**HahnSeries.min_order_le_order_add** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：min_order_le_order_add {Γ} [Zero Γ] [LinearOrder Γ] {x y : R⟦Γ⟧} (hxy : x 
+ y != 0) : min x.order y.order <= (x + y).order
参数：hxy : x + y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.order_zero`：order_zero : order (0 : R⟦Γ⟧) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `HahnSeries.order_of_ne`：order_of_ne {x : R⟦Γ⟧} (hx : x != 0) : order x =
 x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `HahnSeries.min_le_min_add`：∀ {R : Type u_3} [inst : AddMonoid R] {Γ : Ty
pe u_8} [inst_1 : LinearOrder Γ] {x y : HahnSeries Γ R} (hx : x ≠ 0)   (hy : y ≠
 0) (hxy : x + …
-/
theorem min_order_le_order_add {Γ} [Zero Γ] [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : x + y ≠ 0) : min x.order y.order ≤ (x + y).order := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [order_of_ne hx, order_of_ne hy, order_of_ne hxy]
  exact HahnSeries.min_le_min_add hx hy hxy
/-
**HahnSeries.orderTop_add_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_add_eq_left {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} (hxy : x.orderTop < 
y.orderTop) : (x + y).orderTop = x.orderTop
参数：hxy : x.orderTop < y.orderTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `HahnSeries.orderTop_ne_top`：orderTop_ne_top : orderTop x != ⊤ ↔ x != 0
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.coeff_add`：coeff_add {x y : R⟦Γ⟧} {a : Γ} : (x + y).coeff a =
 x.coeff a + y.coeff a
· 使用定理 `HahnSeries.coeff_eq_zero_of_lt_orderTop`：coeff_eq_zero_of_lt_orderTop {x
 : R⟦Γ⟧} {i : Γ} (hi : i < x.orderTop) : x.coeff i = 0
· 使用定理 `lt_of_eq_of_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < 
c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `HahnSeries.coeff_orderTop_ne`：coeff_orderTop_ne {x : R⟦Γ⟧} {g : Γ} (hg :
 x.orderTop = g) : x.coeff g != 0
· 使用定理 `HahnSeries.orderTop_le_of_coeff_ne_zero`：orderTop_le_of_coeff_ne_zero {Γ
} [LinearOrder Γ] {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0) : x.orderTop <= g
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `min_eq_left_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a 
< b → min a b = a
· 使用定理 `HahnSeries.min_orderTop_le_orderTop_add`：min_orderTop_le_orderTop_add {Γ
} [LinearOrder Γ] {x y : R⟦Γ⟧} : min x.orderTop y.orderTop <= (x + y).orderTop
-/
theorem orderTop_add_eq_left {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : x.orderTop < y.orderTop) : (x + y).orderTop = x.orderTop := by
  have hx : x ≠ 0 := orderTop_ne_top.1 hxy.ne_top
  let g : Γ := Set.IsWF.min x.isWF_support (support_nonempty_iff.2 hx)
  have hcxyne : (x + y).coeff g ≠ 0 := by
    rw [coeff_add, coeff_eq_zero_of_lt_orderTop (lt_of_eq_of_lt (orderTop_of_ne_zero hx).symm hxy),
      add_zero]
    exact coeff_orderTop_ne (orderTop_of_ne_zero hx)
  have hxyx : (x + y).orderTop ≤ x.orderTop := by
    rw [orderTop_of_ne_zero hx]
    exact orderTop_le_of_coeff_ne_zero hcxyne
  exact le_antisymm hxyx (le_of_eq_of_le (min_eq_left_of_lt hxy).symm min_orderTop_le_orderTop_add)
/-
**HahnSeries.orderTop_add_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_add_eq_right {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} (hxy : y.orderTop <
 x.orderTop) : (x + y).orderTop = y.orderTop
参数：hxy : y.orderTop < x.orderTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HahnSeries.addOppositeEquiv_symm_orderTop`：addOppositeEquiv_symm_orderTo
p (x : R⟦Γ⟧ᵃᵒᵖ) : (addOppositeEquiv.symm x).orderTop = x.unop.orderTop
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `HahnSeries.orderTop_add_eq_left`：orderTop_add_eq_left {Γ} [LinearOrder Γ
] {x y : R⟦Γ⟧} (hxy : x.orderTop < y.orderTop) : (x + y).orderTop = x.orderTop
-/
theorem orderTop_add_eq_right {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : y.orderTop < x.orderTop) : (x + y).orderTop = y.orderTop := by
  simpa [← map_add, ← AddOpposite.op_add, hxy] using orderTop_add_eq_left
    (x := addOppositeEquiv.symm (.op y))
    (y := addOppositeEquiv.symm (.op x))
/-
**HahnSeries.leadingCoeff_add_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_add_eq_left {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} (hxy : x.orderTo
p < y.orderTop) : (x + y).leadingCoeff = x.leadingCoeff
参数：hxy : x.orderTop < y.orderTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `HahnSeries.orderTop_ne_top`：orderTop_ne_top : orderTop x != ⊤ ↔ x != 0
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `HahnSeries.orderTop_add_eq_left`：orderTop_add_eq_left {Γ} [LinearOrder Γ
] {x y : R⟦Γ⟧} (hxy : x.orderTop < y.orderTop) : (x + y).orderTop = x.orderTop
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.orderTop_eq_top`：∀ {Γ : Type u_1} {R : Type u_3} [inst : Part
ialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R}, x.orderTop = ⊤ ↔ x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.leadingCoeff_of_ne_zero`：leadingCoeff_of_ne_zero {x : R⟦Γ⟧} (
hx : x != 0) : x.leadingCoeff = x.coeff (x.orderTop.untop <| orderTop_ne_top.2 h
x)
· 使用定理 `WithTop.untop.congr_simp`：∀ {α : Type u_1} (x x_1 : WithTop α) (e_x : x 
= x_1) (a : x ≠ ⊤), x.untop a = x_1.untop ⋯
· 使用定理 `HahnSeries.coeff_eq_zero_of_lt_orderTop`：coeff_eq_zero_of_lt_orderTop {x
 : R⟦Γ⟧} {i : Γ} (hi : i < x.orderTop) : x.coeff i = 0
· 使用定理 `WithTop.coe_untop`：∀ {α : Type u_1} (x : WithTop α) (hx : x ≠ ⊤), ↑(x.un
top hx) = x
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem leadingCoeff_add_eq_left {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : x.orderTop < y.orderTop) : (x + y).leadingCoeff = x.leadingCoeff := by
  have hx : x ≠ 0 := orderTop_ne_top.1 hxy.ne_top
  have ho : (x + y).orderTop = x.orderTop := orderTop_add_eq_left hxy
  by_cases h : x + y = 0
  · rw [h, orderTop_zero] at ho
    rw [h, orderTop_eq_top.mp ho.symm]
  · simp_rw [leadingCoeff_of_ne_zero h, leadingCoeff_of_ne_zero hx, ho, coeff_add]
    rw [coeff_eq_zero_of_lt_orderTop (x := y) (by simpa using hxy), add_zero]
/-
**HahnSeries.leadingCoeff_add_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_add_eq_right {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} (hxy : y.orderT
op < x.orderTop) : (x + y).leadingCoeff = y.leadingCoeff
参数：hxy : y.orderTop < x.orderTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HahnSeries.addOppositeEquiv_symm_orderTop`：addOppositeEquiv_symm_orderTo
p (x : R⟦Γ⟧ᵃᵒᵖ) : (addOppositeEquiv.symm x).orderTop = x.unop.orderTop
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用引理 `HahnSeries.addOppositeEquiv_symm_leadingCoeff`：addOppositeEquiv_symm_lea
dingCoeff (x : R⟦Γ⟧ᵃᵒᵖ) : (addOppositeEquiv.symm x).leadingCoeff = .op x.unop.le
adingCoeff
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `HahnSeries.leadingCoeff_add_eq_left`：leadingCoeff_add_eq_left {Γ} [Linea
rOrder Γ] {x y : R⟦Γ⟧} (hxy : x.orderTop < y.orderTop) : (x + y).leadingCoeff = 
x.leadingCoeff
-/
theorem leadingCoeff_add_eq_right {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : y.orderTop < x.orderTop) : (x + y).leadingCoeff = y.leadingCoeff := by
  simpa [← map_add, ← AddOpposite.op_add, hxy] using leadingCoeff_add_eq_left
    (x := addOppositeEquiv.symm (.op y))
    (y := addOppositeEquiv.symm (.op x))
/-
**HahnSeries.ne_zero_of_eq_add_single** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：ne_zero_of_eq_add_single [Zero Γ] {x y : R⟦Γ⟧} (hxy : x = y + single x.ord
er x.leadingCoeff) (hy : y != 0) : x != 0
参数：hxy : x = y + single x.order x.leadingCoeff；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.order_zero`：order_zero : order (0 : R⟦Γ⟧) = 0
· 使用定理 `HahnSeries.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R⟦Γ⟧
) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem ne_zero_of_eq_add_single [Zero Γ] {x y : R⟦Γ⟧}
    (hxy : x = y + single x.order x.leadingCoeff) (hy : y ≠ 0) : x ≠ 0 := by
  by_contra h
  simp only [h, order_zero, leadingCoeff_zero, map_zero, add_zero] at hxy
  exact hy hxy.symm
/-
**HahnSeries.coeff_order_of_eq_add_single** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`
。
形式化陈述：coeff_order_of_eq_add_single {R} [AddCancelCommMonoid R] [Zero Γ] {x y : R
⟦Γ⟧} (hxy : x = y + single x.order x.leadingCoeff) : y.coeff x.order = 0
参数：hxy : x = y + single x.order x.leadingCoeff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.coeff_single_same`：coeff_single_same (a : Γ) (r : R) : (singl
e a r).coeff a = r
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem coeff_order_of_eq_add_single {R} [AddCancelCommMonoid R] [Zero Γ] {x y : R⟦Γ⟧}
    (hxy : x = y + single x.order x.leadingCoeff) : y.coeff x.order = 0 := by
  simpa [← leadingCoeff_eq] using congr(($hxy).coeff x.order)
/-
**HahnSeries.order_lt_order_of_eq_add_single** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeri
es`。
形式化陈述：order_lt_order_of_eq_add_single {R} {Γ} [LinearOrder Γ] [Zero Γ] [AddCance
lCommMonoid R] {x y : R⟦Γ⟧} (hxy : x = y + single x.order x.leadingCoeff) (hy : 
y != 0) : x.order < y.order
参数：hxy : x = y + single x.order x.leadingCoeff；hy : y != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.single_ne_zero`：single_ne_zero (h : r != 0) : single a r != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.leadingCoeff_ne_zero`：leadingCoeff_ne_zero {x : R⟦Γ⟧} : x.lea
dingCoeff != 0 ↔ x != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.single_eq_zero`：single_eq_zero : single a (0 : R) = 0
· 使用定理 `HahnSeries.coeff_order_of_eq_add_single`：coeff_order_of_eq_add_single {R
} [AddCancelCommMonoid R] [Zero Γ] {x y : R⟦Γ⟧} (hxy : x = y + single x.order x.
leadingCoeff) : y.coeff x.ord…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.leadingCoeff_eq`：leadingCoeff_eq {x : R⟦Γ⟧} : x.leadingCoeff 
= x.coeff x.order
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `HahnSeries.ne_zero_of_eq_add_single`：ne_zero_of_eq_add_single [Zero Γ] {
x y : R⟦Γ⟧} (hxy : x = y + single x.order x.leadingCoeff) (hy : y != 0) : x != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Set.IsWF.min_le_min_of_subset`：∀ {α : Type u_2} [inst : LinearOrder α] {
s t : Set α} {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF} {htn : t.Nonempty}, 
  s ⊆ t → ht.min ht…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `HahnSeries.coeff_order_eq_zero`：coeff_order_eq_zero {x : R⟦Γ⟧} : x.coeff
 x.order = 0 ↔ x = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `HahnSeries.coeff_single_of_ne`：coeff_single_of_ne (h : b != a) : (single
 a r).coeff b = 0
· 使用定理 `HahnSeries.coeff_add`：coeff_add {x y : R⟦Γ⟧} {a : Γ} : (x + y).coeff a =
 x.coeff a + y.coeff a
-/
theorem order_lt_order_of_eq_add_single {R} {Γ} [LinearOrder Γ] [Zero Γ] [AddCancelCommMonoid R]
    {x y : R⟦Γ⟧} (hxy : x = y + single x.order x.leadingCoeff) (hy : y ≠ 0) :
    x.order < y.order := by
  have : x.order ≠ y.order := by
    intro h
    have hyne : single y.order y.leadingCoeff ≠ 0 := single_ne_zero <| leadingCoeff_ne_zero.mpr hy
    rw [leadingCoeff_eq, ← h, coeff_order_of_eq_add_single hxy, single_eq_zero] at hyne
    exact hyne rfl
  refine lt_of_le_of_ne ?_ this
  simp only [order, ne_zero_of_eq_add_single hxy hy, ↓reduceDIte, hy]
  refine Set.IsWF.min_le_min_of_subset fun g hg ↦ ?_
  obtain rfl | hgx := eq_or_ne g x.order
  · simpa using coeff_order_eq_zero.not.2 <| ne_zero_of_eq_add_single hxy hy
  · have : x.coeff g = (y + (single x.order) x.leadingCoeff).coeff g := by rw [← hxy]
    rw [coeff_add, coeff_single_of_ne hgx, add_zero] at this
    simpa [this] using hg

/-- `single` as an additive monoid/group homomorphism -/
@[simps!]
/-
**HahnSeries.single.addMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries.single`。
形式化陈述：{Γ : Type u_1} → {R : Type u_3} → [inst : PartialOrder Γ] → [inst_1 : AddM
onoid R] → Γ → R →+ HahnSeries Γ R
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.single_add`：∀ {Γ : Type u_1} {R : Type u_3} [inst : PartialOr
der Γ] [inst_1 : AddMonoid R] (a : Γ) (r s : R),   (HahnSeries.single a) (r + s)
 = (HahnSer…

--- 原说明 ---
`single` as an additive monoid/group homomorphism
-/
def single.addMonoidHom (a : Γ) : R →+ R⟦Γ⟧ :=
  { single a with
    map_add' := single_add _ }

/-- `coeff g` as an additive monoid/group homomorphism -/
@[simps]
/-
**HahnSeries.coeff.addMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries.coeff`。
形式化陈述：{Γ : Type u_1} → {R : Type u_3} → [inst : PartialOrder Γ] → [inst_1 : AddM
onoid R] → Γ → HahnSeries Γ R →+ R
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.coeff_add`：coeff_add {x y : R⟦Γ⟧} {a : Γ} : (x + y).coeff a =
 x.coeff a + y.coeff a

--- 原说明 ---
`coeff g` as an additive monoid/group homomorphism
-/
def coeff.addMonoidHom (g : Γ) : R⟦Γ⟧ →+ R where
  toFun f := f.coeff g
  map_zero' := coeff_zero
  map_add' _ _ := coeff_add

section Domain

variable [PartialOrder Γ']

/-
**HahnSeries.embDomain_add** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：embDomain_add (f : Γ ↪o Γ') (x y : R⟦Γ⟧) : embDomain f (x + y) = embDomain
 f x + embDomain f y
参数：f : Γ ↪o Γ'；x y : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.embDomain_coeff`：embDomain_coeff {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {a 
: Γ} : (embDomain f x).coeff (f a) = x.coeff a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HahnSeries.embDomain_of_notMem_range`：embDomain_of_notMem_range {f : Γ ↪
o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ Set.range f) : (embDomain f x).coeff b = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem embDomain_add (f : Γ ↪o Γ') (x y : R⟦Γ⟧) :
    embDomain f (x + y) = embDomain f x + embDomain f y := by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [embDomain_of_notMem_range hg]

end Domain

/-
**HahnSeries.truncLT_add** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：truncLT_add [DecidableLT Γ] (c : Γ) (x y : R⟦Γ⟧) : truncLT c (x + y) = tru
ncLT c x + truncLT c y
参数：c : Γ；x y : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem truncLT_add [DecidableLT Γ] (c : Γ) (x y : R⟦Γ⟧) :
    truncLT c (x + y) = truncLT c x + truncLT c y := by
  ext i
  by_cases h : i < c <;> simp [h]

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid R]

/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid R⟦Γ⟧ where
  add_comm x y := by
    ext
    apply add_comm

@[simp]
/-
**HahnSeries.coeff_sum** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_sum {s : Finset α} {x : α -> R⟦Γ⟧} (g : Γ) : (∑ i in s, x i).coeff g
 = ∑ i in s, (x i).coeff g
参数：g : Γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `HahnSeries.coeff_add`：coeff_add {x y : R⟦Γ⟧} {a : Γ} : (x + y).coeff a =
 x.coeff a + y.coeff a
-/
theorem coeff_sum {s : Finset α} {x : α → R⟦Γ⟧} (g : Γ) :
    (∑ i ∈ s, x i).coeff g = ∑ i ∈ s, (x i).coeff g :=
  cons_induction rfl (fun i s his hsum => by rw [sum_cons, sum_cons, coeff_add, hsum]) s

end AddCommMonoid

section NegZeroClass

variable [NegZeroClass R]

/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg R⟦Γ⟧ where
  neg x := x.map (-ZeroHom.id _)
/-
**HahnSeries.support_neg_subset** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_neg_subset (x : R⟦Γ⟧) : (-x).support subseteq x.support
参数：x : R⟦Γ⟧。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.support_map_subset`：support_map_subset [Zero S] (x : R⟦Γ⟧) (f
 : ZeroHom R S) : (x.map f).support subseteq x.support
-/
theorem support_neg_subset (x : R⟦Γ⟧) : (-x).support ⊆ x.support :=
  support_map_subset ..

@[simp]
/-
**HahnSeries.coeff_neg'** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_neg' (x : R⟦Γ⟧) : (-x).coeff = -x.coeff
参数：x : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_neg' (x : R⟦Γ⟧) : (-x).coeff = -x.coeff :=
  rfl
/-
**HahnSeries.coeff_neg** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_neg {x : R⟦Γ⟧} {a : Γ} : (-x).coeff a = -x.coeff a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_neg {x : R⟦Γ⟧} {a : Γ} : (-x).coeff a = -x.coeff a :=
  rfl

end NegZeroClass

section AddGroup

variable [AddGroup R]

/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub R⟦Γ⟧ where
  sub x y :=
    { coeff := x.coeff - y.coeff
      isPWO_support' := (x.isPWO_support.union y.isPWO_support).mono (Function.support_sub ..) }
/-
**HahnSeries.support_sub_subset** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_sub_subset (x y : R⟦Γ⟧) : (x - y).support subseteq x.support union
 y.support
参数：x y : R⟦Γ⟧。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.support_sub`：∀ {α : Type u_1} {G : Type u_3} [inst : Subtractio
nMonoid G] (f g : α → G),   (Function.support fun x => f x - g x) ⊆ Function.sup
port f ∪ F…
-/
theorem support_sub_subset (x y : R⟦Γ⟧) : (x - y).support ⊆ x.support ∪ y.support :=
  Function.support_sub ..

@[simp]
/-
**HahnSeries.coeff_sub'** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_sub' (x y : R⟦Γ⟧) : (x - y).coeff = x.coeff - y.coeff
参数：x y : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_sub' (x y : R⟦Γ⟧) : (x - y).coeff = x.coeff - y.coeff :=
  rfl
/-
**HahnSeries.coeff_sub** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_sub {x y : R⟦Γ⟧} {a : Γ} : (x - y).coeff a = x.coeff a - y.coeff a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_sub {x y : R⟦Γ⟧} {a : Γ} : (x - y).coeff a = x.coeff a - y.coeff a :=
  rfl
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddGroup R⟦Γ⟧ := fast_instance%
  coeff_injective.addGroup _
    coeff_zero' coeff_add' coeff_neg' coeff_sub'
    (fun _ _ => coeff_smul' _ _) (fun _ _ => coeff_smul' _ _)

@[simp]
/-
**HahnSeries.single_sub** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：single_sub (a : Γ) (r s : R) : single a (r - s) = single a r - single a s
参数：a : Γ；r s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem single_sub (a : Γ) (r s : R) : single a (r - s) = single a r - single a s :=
  map_sub (single.addMonoidHom a) _ _

@[simp]
/-
**HahnSeries.single_neg** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：single_neg (a : Γ) (r : R) : single a (-r) = -single a r
参数：a : Γ；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem single_neg (a : Γ) (r : R) : single a (-r) = -single a r :=
  map_neg (single.addMonoidHom a) _

@[simp]
/-
**HahnSeries.support_neg** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_neg {x : R⟦Γ⟧} : (-x).support = x.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_neg {x : R⟦Γ⟧} : (-x).support = x.support := by
  ext
  simp

@[simp]
/-
**HahnSeries.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4} [inst : PartialOrder Γ] [in
st_1 : AddGroup R] [inst_2 : AddGroup S]   (f : R →+ S) {x : HahnSeries Γ R}, (-
x).map f = -x.map f
参数：f : R →+ S；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.map_coeff`：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4} [in
st : PartialOrder Γ] [inst_1 : Zero R] [inst_2 : Zero S]   (x : HahnSeries Γ R) 
{F : Type …
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_neg [AddGroup S] (f : R →+ S) {x : R⟦Γ⟧} :
    ((-x).map f : S⟦Γ⟧) = -x.map f := by
  ext; simp

@[simp]
/-
**HahnSeries.orderTop_neg** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_neg {x : R⟦Γ⟧} : (-x).orderTop = x.orderTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.support_neg`：support_neg {x : R⟦Γ⟧} : (-x).support = x.suppor
t
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Set.IsWF.min.congr_simp`：∀ {α : Type u_2} [inst : Preorder α] {s s_1 : S
et α} (e_s : s = s_1) (hs : s.IsWF) (hn : s.Nonempty),   hs.min hn = ⋯.min ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem orderTop_neg {x : R⟦Γ⟧} : (-x).orderTop = x.orderTop := by
  classical simp only [orderTop, support_neg, neg_eq_zero]

@[simp]
/-
**HahnSeries.order_neg** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：order_neg [Zero Γ] {f : R⟦Γ⟧} : (-f).order = f.order
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `HahnSeries.support_neg`：support_neg {x : R⟦Γ⟧} : (-x).support = x.suppor
t
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Set.IsWF.min.congr_simp`：∀ {α : Type u_2} [inst : Preorder α] {s s_1 : S
et α} (e_s : s = s_1) (hs : s.IsWF) (hn : s.Nonempty),   hs.min hn = ⋯.min ⋯
-/
theorem order_neg [Zero Γ] {f : R⟦Γ⟧} : (-f).order = f.order := by
  classical
  by_cases hf : f = 0
  · simp only [hf, neg_zero]
  simp only [order, support_neg, neg_eq_zero]
/-
**HahnSeries.leadingCoeff_neg** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_neg {x : R⟦Γ⟧} : (-x).leadingCoeff = -x.leadingCoeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `HahnSeries.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R⟦Γ⟧
) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `HahnSeries.orderTop_ne_top`：orderTop_ne_top : orderTop x != ⊤ ↔ x != 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `HahnSeries.orderTop_neg`：orderTop_neg {x : R⟦Γ⟧} : (-x).orderTop = x.ord
erTop
· 使用定理 `HahnSeries.leadingCoeff_of_ne_zero`：leadingCoeff_of_ne_zero {x : R⟦Γ⟧} (
hx : x != 0) : x.leadingCoeff = x.coeff (x.orderTop.untop <| orderTop_ne_top.2 h
x)
· 使用定理 `WithTop.untop.congr_simp`：∀ {α : Type u_1} (x x_1 : WithTop α) (e_x : x 
= x_1) (a : x ≠ ⊤), x.untop a = x_1.untop ⋯
-/
theorem leadingCoeff_neg {x : R⟦Γ⟧} : (-x).leadingCoeff = -x.leadingCoeff := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [leadingCoeff_of_ne_zero, *]

@[simp]
/-
**HahnSeries.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4} [inst : PartialOrder Γ] [in
st_1 : AddGroup R] [inst_2 : AddGroup S]   (f : R →+ S) {x y : HahnSeries Γ R}, 
(x - y).map f = x.map f - y.map f
参数：f : R →+ S；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.map_coeff`：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4} [in
st : PartialOrder Γ] [inst_1 : Zero R] [inst_2 : Zero S]   (x : HahnSeries Γ R) 
{F : Type …
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_sub [AddGroup S] (f : R →+ S) {x y : R⟦Γ⟧} :
    ((x - y).map f : S⟦Γ⟧) = x.map f - y.map f := by
  ext; simp
/-
**HahnSeries.min_orderTop_le_orderTop_sub** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`
。
形式化陈述：min_orderTop_le_orderTop_sub {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} : min x.orde
rTop y.orderTop <= (x - y).orderTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.orderTop_neg`：orderTop_neg {x : R⟦Γ⟧} : (-x).orderTop = x.ord
erTop
· 使用定理 `HahnSeries.min_orderTop_le_orderTop_add`：min_orderTop_le_orderTop_add {Γ
} [LinearOrder Γ] {x y : R⟦Γ⟧} : min x.orderTop y.orderTop <= (x + y).orderTop
-/
theorem min_orderTop_le_orderTop_sub {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} :
    min x.orderTop y.orderTop ≤ (x - y).orderTop := by
  rw [sub_eq_add_neg, ← orderTop_neg (x := y)]
  exact min_orderTop_le_orderTop_add
/-
**HahnSeries.orderTop_sub** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_sub {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} (hxy : x.orderTop < y.orderT
op) : (x - y).orderTop = x.orderTop
参数：hxy : x.orderTop < y.orderTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `HahnSeries.orderTop_add_eq_left`：orderTop_add_eq_left {Γ} [LinearOrder Γ
] {x y : R⟦Γ⟧} (hxy : x.orderTop < y.orderTop) : (x + y).orderTop = x.orderTop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.orderTop_neg`：orderTop_neg {x : R⟦Γ⟧} : (-x).orderTop = x.ord
erTop
-/
theorem orderTop_sub {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : x.orderTop < y.orderTop) : (x - y).orderTop = x.orderTop := by
  rw [sub_eq_add_neg]
  rw [← orderTop_neg (x := y)] at hxy
  exact orderTop_add_eq_left hxy
/-
**HahnSeries.leadingCoeff_sub** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_sub {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} (hxy : x.orderTop < y.or
derTop) : (x - y).leadingCoeff = x.leadingCoeff
参数：hxy : x.orderTop < y.orderTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `HahnSeries.leadingCoeff_add_eq_left`：leadingCoeff_add_eq_left {Γ} [Linea
rOrder Γ] {x y : R⟦Γ⟧} (hxy : x.orderTop < y.orderTop) : (x + y).leadingCoeff = 
x.leadingCoeff
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.orderTop_neg`：orderTop_neg {x : R⟦Γ⟧} : (-x).orderTop = x.ord
erTop
-/
theorem leadingCoeff_sub {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : x.orderTop < y.orderTop) : (x - y).leadingCoeff = x.leadingCoeff := by
  rw [sub_eq_add_neg]
  rw [← orderTop_neg (x := y)] at hxy
  exact leadingCoeff_add_eq_left hxy
/-
**HahnSeries.orderTop_sub_ne** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_sub_ne {x y : R⟦Γ⟧} {g : Γ} (hxg : x.orderTop = g) (hyg : y.order
Top = g) (hxyc : x.leadingCoeff = y.leadingCoeff) : (x - y).orderTop != g
参数：hxg : x.orderTop = g；hyg : y.orderTop = g；hxyc : x.leadingCoeff = y.leadingCo
eff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.orderTop_ne_of_coeff_eq_zero`：orderTop_ne_of_coeff_eq_zero {x
 : R⟦Γ⟧} {i : Γ} (hx : x.coeff i = 0) : x.orderTop != i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `HahnSeries.coeff_sub`：coeff_sub {x y : R⟦Γ⟧} {a : Γ} : (x - y).coeff a =
 x.coeff a - y.coeff a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `HahnSeries.orderTop_ne_top`：orderTop_ne_top : orderTop x != ⊤ ↔ x != 0
· 使用定理 `HahnSeries.leadingCoeff_of_ne_zero`：leadingCoeff_of_ne_zero {x : R⟦Γ⟧} (
hx : x != 0) : x.leadingCoeff = x.coeff (x.orderTop.untop <| orderTop_ne_top.2 h
x)
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `HahnSeries.untop_orderTop_of_ne_zero`：untop_orderTop_of_ne_zero {x : R⟦Γ
⟧} (hx : x != 0) : WithTop.untop x.orderTop (orderTop_ne_top.2 hx) = x.isWF_supp
ort.min (support_nonempty_…
· 使用定理 `WithTop.coe_eq_coe`：∀ {α : Type u_1} {a b : α}, ↑a = ↑b ↔ a = b
· 使用定理 `HahnSeries.orderTop_of_ne_zero`：orderTop_of_ne_zero (hx : x != 0) : orde
rTop x = x.isWF_support.min (support_nonempty_iff.2 hx)
-/
theorem orderTop_sub_ne {x y : R⟦Γ⟧} {g : Γ}
    (hxg : x.orderTop = g) (hyg : y.orderTop = g) (hxyc : x.leadingCoeff = y.leadingCoeff) :
    (x - y).orderTop ≠ g := by
  refine orderTop_ne_of_coeff_eq_zero ?_
  have hx : x ≠ 0 := fun h ↦ by simp_all [orderTop_zero, WithTop.top_ne_coe]
  rw [orderTop_of_ne_zero hx, WithTop.coe_eq_coe] at hxg
  have hy : y ≠ 0 := fun h ↦ by simp_all [orderTop_zero, WithTop.top_ne_coe]
  rw [orderTop_of_ne_zero hy, WithTop.coe_eq_coe] at hyg
  simp only [leadingCoeff_of_ne_zero hx, leadingCoeff_of_ne_zero hy, untop_orderTop_of_ne_zero hx,
    untop_orderTop_of_ne_zero hy, hxg, hyg] at hxyc
  rwa [coeff_sub, sub_eq_zero]
/-
**HahnSeries.le_orderTop_of_leadingCoeff_eq** 是 Mathlib 中的一个定理，位于命名空间 `HahnSerie
s`。
形式化陈述：le_orderTop_of_leadingCoeff_eq {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} {g : Γ} (h
xg : x.orderTop = g) (hyg : y.orderTop = g) (hxyc : x.leadingCoeff = y.leadingCo
eff) : g < (x - y).orderTop
参数：hxg : x.orderTop = g；hyg : y.orderTop = g；hxyc : x.leadingCoeff = y.leadingCo
eff。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
· 使用定理 `HahnSeries.min_orderTop_le_orderTop_sub`：min_orderTop_le_orderTop_sub {Γ
} [LinearOrder Γ] {x y : R⟦Γ⟧} : min x.orderTop y.orderTop <= (x - y).orderTop
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `HahnSeries.orderTop_sub_ne`：orderTop_sub_ne {x y : R⟦Γ⟧} {g : Γ} (hxg : 
x.orderTop = g) (hyg : y.orderTop = g) (hxyc : x.leadingCoeff = y.leadingCoeff) 
: (x - y).orderT…
-/
theorem le_orderTop_of_leadingCoeff_eq {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} {g : Γ}
    (hxg : x.orderTop = g) (hyg : y.orderTop = g) (hxyc : x.leadingCoeff = y.leadingCoeff) :
    g < (x - y).orderTop :=
  lt_of_le_of_ne (le_of_eq_of_le (by rw [hxg, hyg, inf_idem]) min_orderTop_le_orderTop_sub)
    (orderTop_sub_ne hxg hyg hxyc).symm

end AddGroup

/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommGroup R] : AddCommGroup R⟦Γ⟧ where

end Addition

section DistribMulAction

variable [PartialOrder Γ] {V : Type*} [Monoid R] [AddMonoid V] [DistribMulAction R V]

/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribMulAction R V⟦Γ⟧ where
  one_smul _ := by
    ext
    simp
  smul_zero _ := by
    ext
    simp
  smul_add _ _ _ := by
    ext
    simp [smul_add]
  mul_smul _ _ _ := by
    ext
    simp [mul_smul]

variable {S : Type*} [Monoid S] [DistribMulAction S V]
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R S] [IsScalarTower R S V] : IsScalarTower R S V⟦Γ⟧ :=
  ⟨fun r s a => by
    ext
    simp⟩
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass R S V] : SMulCommClass R S V⟦Γ⟧ :=
  ⟨fun r s a => by
    ext
    simp [smul_comm]⟩

end DistribMulAction

section Module

variable [PartialOrder Γ] [Semiring R] [AddCommMonoid V] [Module R V]

/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R V⟦Γ⟧ where
  zero_smul _ := by
    ext
    simp
  add_smul _ _ _ := by
    ext
    simp [add_smul]

/-- `single` as a linear map -/
@[simps]
/-
**HahnSeries.single.linearMap** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries.single`。
形式化陈述：{Γ : Type u_1} →   {R : Type u_3} →     {V : Type u_6} →       [inst : Par
tialOrder Γ] →         [inst_1 : Semiring R] → [inst_2 : AddCommMonoid V] → [ins
t_3 : _root_.Module R V] → Γ → V →ₗ[R] HahnSeries Γ V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`single` as a linear map
-/
def single.linearMap (a : Γ) : V →ₗ[R] V⟦Γ⟧ :=
  { single.addMonoidHom a with
    map_smul' := fun r s => by
      ext b
      by_cases h : b = a <;> simp [h] }

/-- `coeff g` as a linear map -/
@[simps]
/-
**HahnSeries.coeff.linearMap** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries.coeff`。
形式化陈述：{Γ : Type u_1} →   {R : Type u_3} →     {V : Type u_6} →       [inst : Par
tialOrder Γ] →         [inst_1 : Semiring R] → [inst_2 : AddCommMonoid V] → [ins
t_3 : _root_.Module R V] → Γ → HahnSeries Γ V →ₗ[R] V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`coeff g` as a linear map
-/
def coeff.linearMap (g : Γ) : V⟦Γ⟧ →ₗ[R] V :=
  { coeff.addMonoidHom g with map_smul' := fun _ _ => rfl }

@[simp]
/-
**HahnSeries.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：∀ {Γ : Type u_1} {R : Type u_3} {U : Type u_5} {V : Type u_6} [inst : Part
ialOrder Γ] [inst_1 : Semiring R]   [inst_2 : AddCommMonoid V] [inst_3 : _root_.
Module R V] [inst_4 : AddCommMonoid U] [inst_5 : _root_.Module R U]   (f : U →ₗ[
R] V) {r : R} {x : HahnSeries Γ U}, (r • x).map f = r • x.map f
参数：f : U →ₗ[R] V；r • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.map_coeff`：∀ {Γ : Type u_1} {R : Type u_3} {S : Type u_4} [in
st : PartialOrder Γ] [inst_1 : Zero R] [inst_2 : Zero S]   (x : HahnSeries Γ R) 
{F : Type …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_smul [AddCommMonoid U] [Module R U] (f : U →ₗ[R] V) {r : R} {x : U⟦Γ⟧} :
    (r • x).map f = r • (x.map f : V⟦Γ⟧) := by
  ext; simp

section Finsupp

variable (R) in
/-- `ofFinsupp` as a linear map. -/
/-
**HahnSeries.ofFinsuppLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：ofFinsuppLinearMap : (Γ ->₀ V) ->ₗ[R] V⟦Γ⟧ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofFinsupp` as a linear map.
-/
def ofFinsuppLinearMap : (Γ →₀ V) →ₗ[R] V⟦Γ⟧ where
  toFun := ofFinsupp
  map_add' _ _ := by
    ext
    simp
  map_smul' _ _ := by
    ext
    simp

variable (R) in
@[simp]
/-
**HahnSeries.coeff_ofFinsuppLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_ofFinsuppLinearMap (f : Γ ->₀ V) (a : Γ) : (ofFinsuppLinearMap R f).
coeff a = f a
参数：f : Γ ->₀ V；a : Γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_ofFinsuppLinearMap (f : Γ →₀ V) (a : Γ) :
    (ofFinsuppLinearMap R f).coeff a = f a := rfl

end Finsupp

section Domain

variable [PartialOrder Γ']

/-
**HahnSeries.embDomain_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：embDomain_smul (f : Γ ↪o Γ') (r : R) (x : R⟦Γ⟧) : embDomain f (r • x) = r 
• embDomain f x
参数：f : Γ ↪o Γ'；r : R；x : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.embDomain_coeff`：embDomain_coeff {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {a 
: Γ} : (embDomain f x).coeff (f a) = x.coeff a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HahnSeries.embDomain_of_notMem_range`：embDomain_of_notMem_range {f : Γ ↪
o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ Set.range f) : (embDomain f x).coeff b = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem embDomain_smul (f : Γ ↪o Γ') (r : R) (x : R⟦Γ⟧) :
    embDomain f (r • x) = r • embDomain f x := by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [embDomain_of_notMem_range hg]

/-- Extending the domain of Hahn series is a linear map. -/
@[simps]
/-
**HahnSeries.embDomainLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：embDomainLinearMap (f : Γ ↪o Γ') : R⟦Γ⟧ ->ₗ[R] R⟦Γ'⟧ where toFun
参数：f : Γ ↪o Γ'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.embDomain_smul`：embDomain_smul (f : Γ ↪o Γ') (r : R) (x : R⟦Γ
⟧) : embDomain f (r • x) = r • embDomain f x

--- 原说明 ---
Extending the domain of Hahn series is a linear map.
-/
def embDomainLinearMap (f : Γ ↪o Γ') : R⟦Γ⟧ →ₗ[R] R⟦Γ'⟧ where
  toFun := embDomain f
  map_add' := embDomain_add f
  map_smul' := embDomain_smul f

end Domain

variable (R) in
/-- `HahnSeries.truncLT` as a linear map. -/
/-
**HahnSeries.truncLTLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：truncLTLinearMap [DecidableLT Γ] (c : Γ) : V⟦Γ⟧ ->ₗ[R] V⟦Γ⟧ where toFun
参数：c : Γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HahnSeries.truncLT` as a linear map.
-/
def truncLTLinearMap [DecidableLT Γ] (c : Γ) : V⟦Γ⟧ →ₗ[R] V⟦Γ⟧ where
  toFun := truncLT c
  map_add' := truncLT_add c
  map_smul' := truncLT_smul c

variable (R) in
@[simp]
/-
**HahnSeries.coe_truncLTLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coe_truncLTLinearMap [DecidableLT Γ] (c : Γ) : (truncLTLinearMap R c : V⟦Γ
⟧ -> V⟦Γ⟧) = truncLT c
参数：c : Γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_truncLTLinearMap [DecidableLT Γ] (c : Γ) :
    (truncLTLinearMap R c : V⟦Γ⟧ → V⟦Γ⟧) = truncLT c := by rfl

end Module

end HahnSeries

