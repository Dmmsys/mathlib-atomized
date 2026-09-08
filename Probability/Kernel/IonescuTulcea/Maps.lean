/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.Order.Restriction

/-! # Auxiliary maps for Ionescu-Tulcea theorem

This file contains auxiliary maps which are used to prove the Ionescu-Tulcea theorem.
-/

@[expose] public section

open Finset Preorder

section Definitions

section LinearOrder

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [DecidableLE ι] {X : ι → Type*}

/-- Gluing `Ioc a b` and `Ioc b c` into `Ioc a c`. -/
/-
**IocProdIoc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IocProdIoc (a b c : ι) (x : (Π i : Ioc a b, X i) × (Π i : Ioc b c, X i)) (
i : Ioc a c) : X i
参数：a b c : ι；x : (Π i : Ioc a b, X i) × (Π i : Ioc b c, X i)；i : Ioc a c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Gluing `Ioc a b` and `Ioc b c` into `Ioc a c`.
-/
def IocProdIoc (a b c : ι) (x : (Π i : Ioc a b, X i) × (Π i : Ioc b c, X i)) (i : Ioc a c) : X i :=
  if h : i ≤ b
    then x.1 ⟨i, mem_Ioc.2 ⟨(mem_Ioc.1 i.2).1, h⟩⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, (mem_Ioc.1 i.2).2⟩⟩

@[fun_prop]
/-
**measurable_IocProdIoc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_IocProdIoc [forall i, MeasurableSpace (X i)] {a b c : ι} : Meas
urable (IocProdIoc (X
参数：X i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Measurable.eval`：Measurable.eval {a : δ} {g : α -> forall a, X a} (hg : 
Measurable g) : Measurable fun x => g x a
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
lemma measurable_IocProdIoc [∀ i, MeasurableSpace (X i)] {a b c : ι} :
    Measurable (IocProdIoc (X := X) a b c) := by
  refine measurable_pi_lambda _ (fun i ↦ ?_)
  by_cases h : i ≤ b
  · simpa [IocProdIoc, h] using measurable_fst.eval
  · simpa [IocProdIoc, h] using measurable_snd.eval

variable [LocallyFiniteOrderBot ι]

/-- Gluing `Iic a` and `Ioc a b` into `Iic b`. If `b < a`, this is just a projection on the first
coordinate followed by a restriction, see `IicProdIoc_le`. -/
/-
**IicProdIoc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IicProdIoc (a b : ι) (x : (Π i : Iic a, X i) × (Π i : Ioc a b, X i)) (i : 
Iic b) : X i
参数：a b : ι；x : (Π i : Iic a, X i) × (Π i : Ioc a b, X i)；i : Iic b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Gluing `Iic a` and `Ioc a b` into `Iic b`. If `b < a`, this is just a projection
 on the first
coordinate followed by a restriction, see `IicProdIoc_le`.
-/
def IicProdIoc (a b : ι) (x : (Π i : Iic a, X i) × (Π i : Ioc a b, X i)) (i : Iic b) : X i :=
  if h : i ≤ a
    then x.1 ⟨i, mem_Iic.2 h⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩

/-- When `IicProdIoc` is only partially applied (i.e. `IicProdIoc a b x` but not
`IicProdIoc a b x i`) `simp [IicProdIoc]` won't unfold the definition.
This lemma allows to unfold it by writing `simp [IicProdIoc_def]`. -/
/-
**IicProdIoc_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IicProdIoc_def (a b : ι) : IicProdIoc (X
参数：a b : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `IicProdIoc` is only partially applied (i.e. `IicProdIoc a b x` but not
`IicProdIoc a b x i`) `simp [IicProdIoc]` won't unfold the definition.
This lemma allows to unfold it by writing `simp [IicProdIoc_def]`.
-/
lemma IicProdIoc_def (a b : ι) :
    IicProdIoc (X := X) a b = fun x i ↦ if h : i.1 ≤ a then x.1 ⟨i, mem_Iic.2 h⟩
      else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩ := rfl
/-
**frestrictLe** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma frestrictLe₂_comp_IicProdIoc {a b : ι} (hab : a ≤ b) :
    (frestrictLe₂ hab) ∘ (IicProdIoc (X := X) a b) = Prod.fst := by
  ext x i
  simp [IicProdIoc, mem_Iic.1 i.2]
/-
**restrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrict₂_comp_IicProdIoc (a b : ι) :
    (restrict₂ Ioc_subset_Iic_self) ∘ (IicProdIoc (X := X) a b) = Prod.snd := by
  ext x i
  simp [IicProdIoc, not_le.2 (mem_Ioc.1 i.2).1]

@[simp]
/-
**IicProdIoc_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IicProdIoc_self (a : ι) : IicProdIoc (X
参数：a : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IicProdIoc_self (a : ι) : IicProdIoc (X := X) a a = Prod.fst := by
  ext x i
  simp [IicProdIoc, mem_Iic.1 i.2]
/-
**IicProdIoc_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IicProdIoc_le {a b : ι} (hba : b <= a) : IicProdIoc (X
参数：hba : b <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IicProdIoc_le {a b : ι} (hba : b ≤ a) :
    IicProdIoc (X := X) a b = (frestrictLe₂ hba) ∘ Prod.fst := by
  ext x i
  simp [IicProdIoc, (mem_Iic.1 i.2).trans hba]
/-
**IicProdIoc_comp_restrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IicProdIoc_comp_restrict₂ {a b : ι} :
    (restrict₂ Ioc_subset_Iic_self) ∘ (IicProdIoc (X := X) a b) = Prod.snd := by
  ext x i
  simp [IicProdIoc, not_le.2 (mem_Ioc.1 i.2).1]

variable [∀ i, MeasurableSpace (X i)]

@[fun_prop]
/-
**measurable_IicProdIoc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_IicProdIoc {m n : ι} : Measurable (IicProdIoc (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Measurable.eval`：Measurable.eval {a : δ} {g : α -> forall a, X a} (hg : 
Measurable g) : Measurable fun x => g x a
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
lemma measurable_IicProdIoc {m n : ι} : Measurable (IicProdIoc (X := X) m n) := by
  refine measurable_pi_lambda _ (fun i ↦ ?_)
  by_cases h : i ≤ m
  · simpa [IicProdIoc, h] using measurable_fst.eval
  · simpa [IicProdIoc, h] using measurable_snd.eval

namespace MeasurableEquiv

set_option backward.isDefEq.respectTransparency false in
/-- Gluing `Iic a` and `Ioc a b` into `Iic b`. This version requires `a ≤ b` to get a measurable
equivalence. -/
/-
**MeasurableEquiv.IicProdIoc** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：IicProdIoc {a b : ι} (hab : a <= b) : ((Π i : Iic a, X i) × (Π i : Ioc a b
, X i)) ≃ᵐ Π i : Iic b, X i where toFun x i
参数：hab : a <= b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Gluing `Iic a` and `Ioc a b` into `Iic b`. This version requires `a ≤ b` to get 
a measurable
equivalence.
-/
def IicProdIoc {a b : ι} (hab : a ≤ b) :
    ((Π i : Iic a, X i) × (Π i : Ioc a b, X i)) ≃ᵐ Π i : Iic b, X i where
  toFun x i := if h : i ≤ a then x.1 ⟨i, mem_Iic.2 h⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩
  invFun x := ⟨fun i ↦ x ⟨i.1, Iic_subset_Iic.2 hab i.2⟩, fun i ↦ x ⟨i.1, Ioc_subset_Iic_self i.2⟩⟩
  left_inv := fun x ↦ by
    ext i
    · simp [mem_Iic.1 i.2]
    · simp [not_le.2 (mem_Ioc.1 i.2).1]
  right_inv := fun x ↦ funext fun i ↦ by
    by_cases hi : i.1 ≤ a <;> simp [hi]
  measurable_toFun := by
    refine measurable_pi_lambda _ (fun x ↦ ?_)
    by_cases h : x ≤ a
    · simpa [h] using measurable_fst.eval
    · simpa [h] using measurable_snd.eval
/-
**MeasurableEquiv.coe_IicProdIoc** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv`。
形式化陈述：coe_IicProdIoc {a b : ι} (hab : a <= b) : ⇑(IicProdIoc (X
参数：hab : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_IicProdIoc {a b : ι} (hab : a ≤ b) :
    ⇑(IicProdIoc (X := X) hab) = _root_.IicProdIoc a b := rfl
/-
**MeasurableEquiv.coe_IicProdIoc_symm** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv
`。
形式化陈述：coe_IicProdIoc_symm {a b : ι} (hab : a <= b) : ⇑(IicProdIoc (X
参数：hab : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_IicProdIoc_symm {a b : ι} (hab : a ≤ b) :
    ⇑(IicProdIoc (X := X) hab).symm =
    fun x ↦ (frestrictLe₂ hab x, restrict₂ Ioc_subset_Iic_self x) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Gluing `Iic a` and `Ioi a` into `ℕ`, version as a measurable equivalence
on dependent functions. -/
/-
**MeasurableEquiv.IicProdIoi** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：IicProdIoi (a : ι) : ((Π i : Iic a, X i) × (Π i : Set.Ioi a, X i)) ≃ᵐ (Π n
, X n) where toFun
参数：a : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Gluing `Iic a` and `Ioi a` into `ℕ`, version as a measurable equivalence
on dependent functions.
-/
def IicProdIoi (a : ι) :
    ((Π i : Iic a, X i) × (Π i : Set.Ioi a, X i)) ≃ᵐ (Π n, X n) where
  toFun := fun x i ↦ if hi : i ≤ a
    then x.1 ⟨i, mem_Iic.2 hi⟩
    else x.2 ⟨i, Set.mem_Ioi.2 (not_le.1 hi)⟩
  invFun := fun x ↦ (fun i ↦ x i, fun i ↦ x i)
  left_inv := fun x ↦ by
    ext i
    · simp [mem_Iic.1 i.2]
    · simp [not_le.2 <| Set.mem_Ioi.1 i.2]
  right_inv := fun x ↦ by simp
  measurable_toFun := by
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    by_cases hi : i ≤ a <;> simp only [Equiv.coe_fn_mk, hi, ↓reduceDIte]
    · exact measurable_fst.eval
    · exact measurable_snd.eval

end MeasurableEquiv

end LinearOrder

section Nat

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

set_option backward.isDefEq.respectTransparency false in
/-- Identifying `{a + 1}` with `Ioc a (a + 1)`, as a measurable equiv on dependent functions. -/
/-
**MeasurableEquiv.piSingleton** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MeasurableEquiv.piSingleton (a : Nat) : X (a + 1) ≃ᵐ Π i : Ioc a (a + 1), 
X i where toFun x i
参数：a : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identifying `{a + 1}` with `Ioc a (a + 1)`, as a measurable equiv on dependent f
unctions.
-/
def MeasurableEquiv.piSingleton (a : ℕ) : X (a + 1) ≃ᵐ Π i : Ioc a (a + 1), X i where
  toFun x i := (Nat.mem_Ioc_succ.1 i.2).symm ▸ x
  invFun x := x ⟨a + 1, right_mem_Ioc.2 a.lt_succ_self⟩
  left_inv := fun x ↦ by simp
  right_inv := fun x ↦ funext fun i ↦ by cases Nat.mem_Ioc_succ' i; rfl
  measurable_toFun := by
    simp_rw [eqRec_eq_cast]
    refine measurable_pi_lambda _ (fun i ↦ (MeasurableEquiv.cast _ ?_).measurable)
    cases Nat.mem_Ioc_succ' i; rfl

end Nat

end Definitions

section Lemmas

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [DecidableLE ι] {X : ι → Type*}

/-
**_root_.IocProdIoc_preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：_root_.IocProdIoc_preimage {a b c : ι} (hab : a <= b) (hbc : b <= c) (s : 
(i : Ioc a c) -> Set (X i)) : IocProdIoc a b c ⁻¹' (Set.univ.pi s) = (Set.univ.p
i <| restrict₂ (π
参数：hab : a <= b；hbc : b <= c；s : (i : Ioc a c) -> Set (X i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IocProdIoc_preimage {a b c : ι} (hab : a ≤ b) (hbc : b ≤ c)
    (s : (i : Ioc a c) → Set (X i)) :
    IocProdIoc a b c ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi <| restrict₂ (π := (fun n ↦ Set (X n))) (Ioc_subset_Ioc_right hbc) s) ×ˢ
        (Set.univ.pi <| restrict₂ (π := (fun n ↦ Set (X n))) (Ioc_subset_Ioc_left hab) s) := by
  ext x
  simp
  grind [IocProdIoc]

variable [LocallyFiniteOrderBot ι]
/-
**_root_.IicProdIoc_preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：_root_.IicProdIoc_preimage {a b : ι} (hab : a <= b) (s : (i : Iic b) -> Se
t (X i)) : IicProdIoc a b ⁻¹' (Set.univ.pi s) = (Set.univ.pi <| frestrictLe₂ (π
参数：hab : a <= b；s : (i : Iic b) -> Set (X i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IicProdIoc_preimage {a b : ι} (hab : a ≤ b) (s : (i : Iic b) → Set (X i)) :
    IicProdIoc a b ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi <| frestrictLe₂ (π := (fun n ↦ Set (X n))) hab s) ×ˢ
        (Set.univ.pi <| restrict₂ (π := (fun n ↦ Set (X n))) Ioc_subset_Iic_self s) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, IicProdIoc_def, forall_const,
    Subtype.forall, mem_Iic, Set.mem_prod, frestrictLe₂_apply, restrict₂, mem_Ioc]
  refine ⟨fun h ↦ ⟨fun i hi ↦ ?_, fun i ⟨hi1, hi2⟩ ↦ ?_⟩, fun ⟨h1, h2⟩ i hi ↦ ?_⟩
  · convert! h i (hi.trans hab)
    rw [dif_pos hi]
  · convert! h i hi2
    rw [dif_neg (not_le.2 hi1)]
  · split_ifs with hi3
    · exact h1 i hi3
    · exact h2 i ⟨not_le.1 hi3, hi⟩

end Lemmas

