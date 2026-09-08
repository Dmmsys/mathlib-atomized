/-
Copyright (c) 2018 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Data.Nat.Find
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Basic properties of holors

Holors are indexed collections of tensor coefficients. Confusingly,
they are often called tensors in physics and in the neural network
community.

A holor is simply a multidimensional array of values. The size of a
holor is specified by a `List ℕ`, whose length is called the dimension
of the holor.

The tensor product of `x₁ : Holor α ds₁` and `x₂ : Holor α ds₂` is the
holor given by `(x₁ ⊗ x₂) (i₁ ++ i₂) = x₁ i₁ * x₂ i₂`. A holor is "of
rank at most 1" if it is a tensor product of one-dimensional holors.
The CP rank of a holor `x` is the smallest N such that `x` is the sum
of N holors of rank at most 1.

Based on the tensor library found in <https://www.isa-afp.org/entries/Deep_Learning.html>

## References

* <https://en.wikipedia.org/wiki/Tensor_rank_decomposition>
-/

@[expose] public section


universe u

open List

/-- `HolorIndex ds` is the type of valid index tuples used to identify an entry of a holor
of dimensions `ds`. -/
/-
**HolorIndex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HolorIndex (ds : List Nat) : Type
参数：ds : List Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HolorIndex ds` is the type of valid index tuples used to identify an entry of a
 holor
of dimensions `ds`.
-/
def HolorIndex (ds : List ℕ) : Type :=
  { is : List ℕ // Forall₂ (· < ·) is ds }

namespace HolorIndex

variable {ds₁ ds₂ ds₃ : List ℕ}

/-- Take the first elements of a `HolorIndex`. -/
/-
**HolorIndex.take** 是 Mathlib 中的一个定义，位于命名空间 `HolorIndex`。
形式化陈述：{ds₂ ds₁ : List ℕ} → HolorIndex (ds₁ ++ ds₂) → HolorIndex ds₁
参数：ds₁ ++ ds₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Take the first elements of a `HolorIndex`.
-/
def take : ∀ {ds₁ : List ℕ}, HolorIndex (ds₁ ++ ds₂) → HolorIndex ds₁
  | ds, is => ⟨List.take (length ds) is.1, forall₂_take_append is.1 ds ds₂ is.2⟩

/-- Drop the first elements of a `HolorIndex`. -/
/-
**HolorIndex.drop** 是 Mathlib 中的一个定义，位于命名空间 `HolorIndex`。
形式化陈述：{ds₂ ds₁ : List ℕ} → HolorIndex (ds₁ ++ ds₂) → HolorIndex ds₂
参数：ds₁ ++ ds₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Drop the first elements of a `HolorIndex`.
-/
def drop : ∀ {ds₁ : List ℕ}, HolorIndex (ds₁ ++ ds₂) → HolorIndex ds₂
  | ds, is => ⟨List.drop (length ds) is.1, forall₂_drop_append is.1 ds ds₂ is.2⟩
/-
**HolorIndex.cast_type** 是 Mathlib 中的一个定理，位于命名空间 `HolorIndex`。
形式化陈述：cast_type (is : List Nat) (eq : ds₁ = ds₂) (h : Forall₂ (· < ·) is ds₁) : 
(cast (congr_arg HolorIndex eq) ⟨is, h⟩).val = is
参数：is : List Nat；eq : ds₁ = ds₂；h : Forall₂ (· < ·) is ds₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cast_type (is : List ℕ) (eq : ds₁ = ds₂) (h : Forall₂ (· < ·) is ds₁) :
    (cast (congr_arg HolorIndex eq) ⟨is, h⟩).val = is := by subst eq; rfl

/-- Right associator for `HolorIndex` -/
/-
**HolorIndex.assocRight** 是 Mathlib 中的一个定义，位于命名空间 `HolorIndex`。
形式化陈述：assocRight : HolorIndex (ds₁ ++ ds₂ ++ ds₃) -> HolorIndex (ds₁ ++ (ds₂ ++ 
ds₃))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right associator for `HolorIndex`
-/
def assocRight : HolorIndex (ds₁ ++ ds₂ ++ ds₃) → HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) :=
  cast (congr_arg HolorIndex (append_assoc ds₁ ds₂ ds₃))

/-- Left associator for `HolorIndex` -/
/-
**HolorIndex.assocLeft** 是 Mathlib 中的一个定义，位于命名空间 `HolorIndex`。
形式化陈述：assocLeft : HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) -> HolorIndex (ds₁ ++ ds₂ ++ 
ds₃)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left associator for `HolorIndex`
-/
def assocLeft : HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) → HolorIndex (ds₁ ++ ds₂ ++ ds₃) :=
  cast (congr_arg HolorIndex (append_assoc ds₁ ds₂ ds₃).symm)
/-
**HolorIndex.take_take** 是 Mathlib 中的一个定理，位于命名空间 `HolorIndex`。
形式化陈述：∀ {ds₁ ds₂ ds₃ : List ℕ} (t : HolorIndex (ds₁ ++ ds₂ ++ ds₃)), t.assocRigh
t.take = t.take.take
参数：t : HolorIndex (ds₁ ++ ds₂ ++ ds₃)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HolorIndex.cast_type`：cast_type (is : List Nat) (eq : ds₁ = ds₂) (h : Fo
rall₂ (· < ·) is ds₁) : (cast (congr_arg HolorIndex eq) ⟨is, h⟩).val = is
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `List.take_take`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.take i (Li
st.take j l) = List.take (min i j) l
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
-/
theorem take_take : ∀ t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.take = t.take.take
  | ⟨is, h⟩ =>
    Subtype.ext <| by
      simp [assocRight, take, cast_type, List.take_take, Nat.le_add_right]
/-
**HolorIndex.drop_take** 是 Mathlib 中的一个定理，位于命名空间 `HolorIndex`。
形式化陈述：∀ {ds₁ ds₂ ds₃ : List ℕ} (t : HolorIndex (ds₁ ++ ds₂ ++ ds₃)), t.assocRigh
t.drop.take = t.take.drop
参数：t : HolorIndex (ds₁ ++ ds₂ ++ ds₃)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HolorIndex.cast_type`：cast_type (is : List Nat) (eq : ds₁ = ds₂) (h : Fo
rall₂ (· < ·) is ds₁) : (cast (congr_arg HolorIndex eq) ⟨is, h⟩).val = is
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `List.drop_take`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.drop i (Li
st.take j l) = List.take (j - i) (List.drop i l)
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
-/
theorem drop_take : ∀ t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.drop.take = t.take.drop
  | ⟨is, h⟩ => Subtype.ext (by simp [assocRight, take, drop, cast_type, List.drop_take])
/-
**HolorIndex.drop_drop** 是 Mathlib 中的一个定理，位于命名空间 `HolorIndex`。
形式化陈述：∀ {ds₁ ds₂ ds₃ : List ℕ} (t : HolorIndex (ds₁ ++ ds₂ ++ ds₃)), t.assocRigh
t.drop.drop = t.drop
参数：t : HolorIndex (ds₁ ++ ds₂ ++ ds₃)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HolorIndex.cast_type`：cast_type (is : List Nat) (eq : ds₁ = ds₂) (h : Fo
rall₂ (· < ·) is ds₁) : (cast (congr_arg HolorIndex eq) ⟨is, h⟩).val = is
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `List.drop_drop`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.drop i (Li
st.drop j l) = List.drop (j + i) l
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
-/
theorem drop_drop : ∀ t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.drop.drop = t.drop
  | ⟨is, h⟩ => Subtype.ext (by simp [assocRight, drop, cast_type, List.drop_drop])

end HolorIndex

/-- Holor (indexed collections of tensor coefficients) -/
/-
**Holor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Holor (α : Type u) (ds : List Nat)
参数：α : Type u；ds : List Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Holor (indexed collections of tensor coefficients)
-/
def Holor (α : Type u) (ds : List ℕ) :=
  HolorIndex ds → α

namespace Holor

variable {α : Type} {d : ℕ} {ds : List ℕ} {ds₁ : List ℕ} {ds₂ : List ℕ} {ds₃ : List ℕ}

/-
**Holor.** 是 Mathlib 中的一个实例，位于命名空间 `Holor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (Holor α ds) :=
  ⟨fun _ => default⟩
/-
**Holor.** 是 Mathlib 中的一个实例，位于命名空间 `Holor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero α] : Zero (Holor α ds) :=
  ⟨fun _ => 0⟩
/-
**Holor.** 是 Mathlib 中的一个实例，位于命名空间 `Holor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add α] : Add (Holor α ds) :=
  ⟨fun x y t => x t + y t⟩
/-
**Holor.** 是 Mathlib 中的一个实例，位于命名空间 `Holor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Neg α] : Neg (Holor α ds) :=
  ⟨fun a t => -a t⟩
/-
**Holor.** 是 Mathlib 中的一个实例，位于命名空间 `Holor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddSemigroup α] : AddSemigroup (Holor α ds) :=
  inferInstanceAs <| AddSemigroup (HolorIndex ds → α)
/-
**Holor.** 是 Mathlib 中的一个实例，位于命名空间 `Holor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommSemigroup α] : AddCommSemigroup (Holor α ds) :=
  inferInstanceAs <| AddCommSemigroup (HolorIndex ds → α)
/-
**Holor.** 是 Mathlib 中的一个实例，位于命名空间 `Holor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid α] : AddMonoid (Holor α ds) :=
  inferInstanceAs <| AddMonoid (HolorIndex ds → α)
/-
**Holor.** 是 Mathlib 中的一个实例，位于命名空间 `Holor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMonoid α] : AddCommMonoid (Holor α ds) :=
  inferInstanceAs <| AddCommMonoid (HolorIndex ds → α)
/-
**Holor.** 是 Mathlib 中的一个实例，位于命名空间 `Holor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroup α] : AddGroup (Holor α ds) :=
  inferInstanceAs <| AddGroup (HolorIndex ds → α)
/-
**Holor.** 是 Mathlib 中的一个实例，位于命名空间 `Holor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommGroup α] : AddCommGroup (Holor α ds) :=
  inferInstanceAs <| AddCommGroup (HolorIndex ds → α)

-- scalar product
/-
**Holor.** 是 Mathlib 中的一个实例，位于命名空间 `Holor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] : SMul α (Holor α ds) :=
  ⟨fun a x => fun t => a * x t⟩
/-
**Holor.** 是 Mathlib 中的一个实例，位于命名空间 `Holor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring α] : Module α (Holor α ds) :=
  inferInstanceAs <| Module α (HolorIndex ds → α)

/-- The tensor product of two holors. -/
/-
**Holor.mul** 是 Mathlib 中的一个定义，位于命名空间 `Holor`。
形式化陈述：mul [Mul α] (x : Holor α ds₁) (y : Holor α ds₂) : Holor α (ds₁ ++ ds₂)
参数：x : Holor α ds₁；y : Holor α ds₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two holors.
-/
def mul [Mul α] (x : Holor α ds₁) (y : Holor α ds₂) : Holor α (ds₁ ++ ds₂) := fun t =>
  x t.take * y t.drop

local infixl:70 " ⊗ " => mul
/-
**Holor.cast_type** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：cast_type (eq : ds₁ = ds₂) (a : Holor α ds₁) : cast (congr_arg (Holor α) e
q) a = fun t => a (cast (congr_arg HolorIndex eq.symm) t)
参数：eq : ds₁ = ds₂；a : Holor α ds₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cast_type (eq : ds₁ = ds₂) (a : Holor α ds₁) :
    cast (congr_arg (Holor α) eq) a = fun t => a (cast (congr_arg HolorIndex eq.symm) t) := by
  subst eq; rfl

/-- Right associator for `Holor` -/
/-
**Holor.assocRight** 是 Mathlib 中的一个定义，位于命名空间 `Holor`。
形式化陈述：assocRight : Holor α (ds₁ ++ ds₂ ++ ds₃) -> Holor α (ds₁ ++ (ds₂ ++ ds₃))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right associator for `Holor`
-/
def assocRight : Holor α (ds₁ ++ ds₂ ++ ds₃) → Holor α (ds₁ ++ (ds₂ ++ ds₃)) :=
  cast (congr_arg (Holor α) (append_assoc ds₁ ds₂ ds₃))

/-- Left associator for `Holor` -/
/-
**Holor.assocLeft** 是 Mathlib 中的一个定义，位于命名空间 `Holor`。
形式化陈述：assocLeft : Holor α (ds₁ ++ (ds₂ ++ ds₃)) -> Holor α (ds₁ ++ ds₂ ++ ds₃)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left associator for `Holor`
-/
def assocLeft : Holor α (ds₁ ++ (ds₂ ++ ds₃)) → Holor α (ds₁ ++ ds₂ ++ ds₃) :=
  cast (congr_arg (Holor α) (append_assoc ds₁ ds₂ ds₃).symm)

set_option backward.isDefEq.respectTransparency false in
/-
**Holor.mul_assoc0** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：mul_assoc0 [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α 
ds₃) : x otimes y otimes z = (x otimes (y otimes z)).assocLeft
参数：x : Holor α ds₁；y : Holor α ds₂；z : Holor α ds₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Holor.assocLeft.eq_1`：∀ {α : Type} {ds₁ ds₂ ds₃ : List ℕ}, Holor.assocLe
ft = cast ⋯
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HolorIndex.take_take`：∀ {ds₁ ds₂ ds₃ : List ℕ} (t : HolorIndex (ds₁ ++ d
s₂ ++ ds₃)), t.assocRight.take = t.take.take
· 使用定理 `HolorIndex.drop_take`：∀ {ds₁ ds₂ ds₃ : List ℕ} (t : HolorIndex (ds₁ ++ d
s₂ ++ ds₃)), t.assocRight.drop.take = t.take.drop
· 使用定理 `HolorIndex.drop_drop`：∀ {ds₁ ds₂ ds₃ : List ℕ} (t : HolorIndex (ds₁ ++ d
s₂ ++ ds₃)), t.assocRight.drop.drop = t.drop
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `Holor.cast_type`：cast_type (eq : ds₁ = ds₂) (a : Holor α ds₁) : cast (co
ngr_arg (Holor α) eq) a = fun t => a (cast (congr_arg HolorIndex eq.symm) t)
-/
theorem mul_assoc0 [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃) :
    x ⊗ y ⊗ z = (x ⊗ (y ⊗ z)).assocLeft :=
  funext fun t : HolorIndex (ds₁ ++ ds₂ ++ ds₃) => by
    rw [assocLeft]
    unfold mul
    rw [mul_assoc, ← HolorIndex.take_take, ← HolorIndex.drop_take, ← HolorIndex.drop_drop,
      cast_type]
    · rfl
    rw [append_assoc]
/-
**Holor.mul_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：mul_assoc [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α d
s₃) : mul (mul x y) z ≍ mul x (mul y z)
参数：x : Holor α ds₁；y : Holor α ds₂；z : Holor α ds₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Holor.mul_assoc0`：mul_assoc0 [Semigroup α] (x : Holor α ds₁) (y : Holor 
α ds₂) (z : Holor α ds₃) : x otimes y otimes z = (x otimes (y otimes z)).assocLe
ft
-/
theorem mul_assoc [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃) :
    mul (mul x y) z ≍ mul x (mul y z) := by simp [cast_heq, mul_assoc0, assocLeft]
/-
**Holor.mul_left_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：mul_left_distrib [Distrib α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holo
r α ds₂) : x otimes (y + z) = x otimes y + x otimes z
参数：x : Holor α ds₁；y : Holor α ds₂；z : Holor α ds₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
-/
theorem mul_left_distrib [Distrib α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₂) :
    x ⊗ (y + z) = x ⊗ y + x ⊗ z := funext fun t => left_distrib (x t.take) (y t.drop) (z t.drop)
/-
**Holor.mul_right_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：mul_right_distrib [Distrib α] (x : Holor α ds₁) (y : Holor α ds₁) (z : Hol
or α ds₂) : (x + y) otimes z = x otimes z + y otimes z
参数：x : Holor α ds₁；y : Holor α ds₁；z : Holor α ds₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
theorem mul_right_distrib [Distrib α] (x : Holor α ds₁) (y : Holor α ds₁) (z : Holor α ds₂) :
    (x + y) ⊗ z = x ⊗ z + y ⊗ z := funext fun t => add_mul (x t.take) (y t.take) (z t.drop)

@[simp]
nonrec theorem zero_mul {α : Type} [MulZeroClass α] (x : Holor α ds₂) : (0 : Holor α ds₁) ⊗ x = 0 :=
  funext fun t => zero_mul (x (HolorIndex.drop t))

@[simp]
nonrec theorem mul_zero {α : Type} [MulZeroClass α] (x : Holor α ds₁) : x ⊗ (0 : Holor α ds₂) = 0 :=
  funext fun t => mul_zero (x (HolorIndex.take t))

set_option backward.isDefEq.respectTransparency false in
/-
**Holor.mul_scalar_mul** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：mul_scalar_mul [Mul α] (x : Holor α []) (y : Holor α ds) : x otimes y = x 
⟨[], Forall₂.nil⟩ • y
参数：x : Holor α []；y : Holor α ds。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_scalar_mul [Mul α] (x : Holor α []) (y : Holor α ds) :
    x ⊗ y = x ⟨[], Forall₂.nil⟩ • y := by
  simp +unfoldPartialApp [mul, SMul.smul, HolorIndex.take, HolorIndex.drop,
    HSMul.hSMul]

-- holor slices
/-- A slice is a subholor consisting of all entries with initial index i. -/
/-
**Holor.slice** 是 Mathlib 中的一个定义，位于命名空间 `Holor`。
形式化陈述：slice (x : Holor α (d :: ds)) (i : Nat) (h : i < d) : Holor α ds
参数：x : Holor α (d :: ds)；i : Nat；h : i < d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A slice is a subholor consisting of all entries with initial index i.
-/
def slice (x : Holor α (d :: ds)) (i : ℕ) (h : i < d) : Holor α ds := fun is : HolorIndex ds =>
  x ⟨i :: is.1, Forall₂.cons h is.2⟩

/-- The 1-dimensional "unit" holor with 1 in the `j`th position. -/
/-
**Holor.unitVec** 是 Mathlib 中的一个定义，位于命名空间 `Holor`。
形式化陈述：unitVec [Monoid α] [AddMonoid α] (d : Nat) (j : Nat) : Holor α [d]
参数：d : Nat；j : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 1-dimensional "unit" holor with 1 in the `j`th position.
-/
def unitVec [Monoid α] [AddMonoid α] (d : ℕ) (j : ℕ) : Holor α [d] := fun ti =>
  if ti.1 = [j] then 1 else 0
/-
**Holor.holor_index_cons_decomp** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：∀ {d : ℕ} {ds : List ℕ} (p : HolorIndex (d :: ds) → Prop) (t : HolorIndex 
(d :: ds)),   (∀ (i : ℕ) (is : List ℕ) (h : ↑t = i :: is), p ⟨i :: is, ⋯⟩) → p t
参数：p : HolorIndex (d :: ds) → Prop；t : HolorIndex (d :: ds)；∀ (i : ℕ) (is : List
 ℕ) (h : ↑t = i :: is), p ⟨i :: is, ⋯⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.forall₂_nil_left_iff`：forall₂_nil_left_iff {l} : Forall₂ R nil l ↔ 
l = nil
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
-/
theorem holor_index_cons_decomp (p : HolorIndex (d :: ds) → Prop) :
    ∀ t : HolorIndex (d :: ds),
      (∀ i is, ∀ h : t.1 = i :: is, p ⟨i :: is, by rw [← h]; exact t.2⟩) → p t
  | ⟨[], hforall₂⟩, _ => absurd (forall₂_nil_left_iff.1 hforall₂) (cons_ne_nil d ds)
  | ⟨i :: is, _⟩, hp => hp i is rfl

/-- Two holors are equal if all their slices are equal. -/
/-
**Holor.slice_eq** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：slice_eq (x : Holor α (d :: ds)) (y : Holor α (d :: ds)) (h : slice x = sl
ice y) : x = y
参数：x : Holor α (d :: ds)；y : Holor α (d :: ds)；h : slice x = slice y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Holor.holor_index_cons_decomp`：∀ {d : ℕ} {ds : List ℕ} (p : HolorIndex (
d :: ds) → Prop) (t : HolorIndex (d :: ds)),   (∀ (i : ℕ) (is : List ℕ) (h : ↑t 
= i :: is), p ⟨i ::…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.forall₂_cons`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} {a
 : α} {b : β} {l₁ : List α} {l₂ : List β},   List.Forall₂ R (a :: l₁) (b :: l₂) 
↔ R a b…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2

--- 原说明 ---
Two holors are equal if all their slices are equal.
-/
theorem slice_eq (x : Holor α (d :: ds)) (y : Holor α (d :: ds)) (h : slice x = slice y) : x = y :=
  funext fun t : HolorIndex (d :: ds) =>
    holor_index_cons_decomp (fun t => x t = y t) t fun i is hiis =>
      have hiisdds : Forall₂ (· < ·) (i :: is) (d :: ds) := by rw [← hiis]; exact t.2
      have hid : i < d := (forall₂_cons.1 hiisdds).1
      have hisds : Forall₂ (· < ·) is ds := (forall₂_cons.1 hiisdds).2
      calc
        x ⟨i :: is, _⟩ = slice x i hid ⟨is, hisds⟩ := congr_arg x (Subtype.ext rfl)
        _ = slice y i hid ⟨is, hisds⟩ := by rw [h]
        _ = y ⟨i :: is, _⟩ := congr_arg y (Subtype.ext rfl)

set_option backward.isDefEq.respectTransparency false in
/-
**Holor.slice_unitVec_mul** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：slice_unitVec_mul [Semiring α] {i : Nat} {j : Nat} (hid : i < d) (x : Holo
r α ds) : slice (unitVec d j otimes x) i hid = if i = j then x else 0
参数：hid : i < d；x : Holor α ds。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.drop_succ_cons`：∀ {α : Type u} {a : α} {l : List α} {i : ℕ}, List.d
rop (i + 1) (a :: l) = List.drop i l
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem slice_unitVec_mul [Semiring α] {i : ℕ} {j : ℕ} (hid : i < d) (x : Holor α ds) :
    slice (unitVec d j ⊗ x) i hid = if i = j then x else 0 :=
  funext fun t : HolorIndex ds =>
    if h : i = j then by simp [slice, mul, HolorIndex.take, unitVec, HolorIndex.drop, h]
    else by simp [slice, mul, HolorIndex.take, unitVec, HolorIndex.drop, h]; rfl
/-
**Holor.slice_add** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：slice_add [Add α] (i : Nat) (hid : i < d) (x : Holor α (d :: ds)) (y : Hol
or α (d :: ds)) : slice x i hid + slice y i hid = slice (x + y) i hid
参数：i : Nat；hid : i < d；x : Holor α (d :: ds)；y : Holor α (d :: ds)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem slice_add [Add α] (i : ℕ) (hid : i < d) (x : Holor α (d :: ds)) (y : Holor α (d :: ds)) :
    slice x i hid + slice y i hid = slice (x + y) i hid :=
  funext fun t => by simp [slice, (· + ·), Add.add]
/-
**Holor.slice_zero** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：slice_zero [Zero α] (i : Nat) (hid : i < d) : slice (0 : Holor α (d :: ds)
) i hid = 0
参数：i : Nat；hid : i < d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem slice_zero [Zero α] (i : ℕ) (hid : i < d) : slice (0 : Holor α (d :: ds)) i hid = 0 :=
  rfl
/-
**Holor.slice_sum** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：slice_sum [AddCommMonoid α] {β : Type} (i : Nat) (hid : i < d) (s : Finset
 β) (f : β -> Holor α (d :: ds)) : (∑ x in s, slice (f x) i hid) = slice (∑ x in
 s, f x) i hid
参数：i : Nat；hid : i < d；s : Finset β；f : β -> Holor α (d :: ds)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Holor.slice_add`：slice_add [Add α] (i : Nat) (hid : i < d) (x : Holor α 
(d :: ds)) (y : Holor α (d :: ds)) : slice x i hid + slice y i hid = slice (x + 
y) i …
-/
theorem slice_sum [AddCommMonoid α] {β : Type} (i : ℕ) (hid : i < d) (s : Finset β)
    (f : β → Holor α (d :: ds)) : (∑ x ∈ s, slice (f x) i hid) = slice (∑ x ∈ s, f x) i hid := by
  let := Classical.decEq β
  refine Finset.induction_on s ?_ ?_
  · simp [slice_zero]
  · intro _ _ h_not_in ih
    rw [Finset.sum_insert h_not_in, ih, slice_add, Finset.sum_insert h_not_in]

set_option backward.isDefEq.respectTransparency false in
/-- The original holor can be recovered from its slices by multiplying with unit vectors and
summing up. -/
@[simp]
/-
**Holor.sum_unitVec_mul_slice** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：sum_unitVec_mul_slice [Semiring α] (x : Holor α (d :: ds)) : (∑ i in (Fins
et.range d).attach, unitVec d i otimes slice x i (Nat.succ_le_of_lt (Finset.mem_
range.1 i.prop))) = x
参数：x : Holor α (d :: ds)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Holor.slice_eq`：slice_eq (x : Holor α (d :: ds)) (y : Holor α (d :: ds))
 (h : slice x = slice y) : x = y
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Holor.slice_sum`：slice_sum [AddCommMonoid α] {β : Type} (i : Nat) (hid :
 i < d) (s : Finset β) (f : β -> Holor α (d :: ds)) : (∑ x in s, slice (f x) i h
id) =…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Holor.slice_unitVec_mul`：slice_unitVec_mul [Semiring α] {i : Nat} {j : N
at} (hid : i < d) (x : Holor α ds) : slice (unitVec d j otimes x) i hid = if i =
 j then x els…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.mem_attach`：mem_attach (s : Finset α) : forall x, x in s.attach
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a

--- 原说明 ---
The original holor can be recovered from its slices by multiplying with unit vec
tors and
summing up.
-/
theorem sum_unitVec_mul_slice [Semiring α] (x : Holor α (d :: ds)) :
    (∑ i ∈ (Finset.range d).attach,
        unitVec d i ⊗ slice x i (Nat.succ_le_of_lt (Finset.mem_range.1 i.prop))) =
      x := by
  apply slice_eq _ _ _
  ext i hid
  rw [← slice_sum]
  simp only [slice_unitVec_mul hid]
  rw [Finset.sum_eq_single (Subtype.mk i <| Finset.mem_range.2 hid)]
  · simp
  · intro (b : { x // x ∈ Finset.range d }) (_ : b ∈ (Finset.range d).attach) (hbi : b ≠ ⟨i, _⟩)
    have hbi' : i ≠ b := by simpa only [Ne, Subtype.ext_iff, Subtype.coe_mk] using hbi.symm
    simp [hbi']
  · intro (hid' : Subtype.mk i _ ∉ Finset.attach (Finset.range d))
    exfalso
    exact absurd (Finset.mem_attach _ _) hid'

-- CP rank
/-- `CPRankMax1 x` means `x` has CP rank at most 1, that is,
  it is the tensor product of 1-dimensional holors. -/
/-
**Holor.CPRankMax1** 是 Mathlib 中的一个归纳类型，位于命名空间 `Holor`。
形式化陈述：{α : Type} → [Mul α] → {ds : List ℕ} → Holor α ds → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CPRankMax1 x` means `x` has CP rank at most 1, that is,
  it is the tensor product of 1-dimensional holors.
-/
inductive CPRankMax1 [Mul α] : ∀ {ds}, Holor α ds → Prop
  | nil (x : Holor α []) : CPRankMax1 x
  | cons {d : ℕ} {ds : List ℕ} (x : Holor α [d]) (y : Holor α ds) :
    CPRankMax1 y → CPRankMax1 (x ⊗ y)

/-- `CPRankMax N x` means `x` has CP rank at most `N`, that is,
  it can be written as the sum of N holors of rank at most 1. -/
/-
**Holor.CPRankMax** 是 Mathlib 中的一个归纳类型，位于命名空间 `Holor`。
形式化陈述：{α : Type} → [Mul α] → [AddMonoid α] → ℕ → {ds : List ℕ} → Holor α ds → Pr
op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CPRankMax N x` means `x` has CP rank at most `N`, that is,
  it can be written as the sum of N holors of rank at most 1.
-/
inductive CPRankMax [Mul α] [AddMonoid α] : ℕ → ∀ {ds}, Holor α ds → Prop
  | zero {ds : List ℕ} : CPRankMax 0 (0 : Holor α ds)
  | succ (n : ℕ) {ds : List ℕ} (x : Holor α ds) (y : Holor α ds) :
    CPRankMax1 x → CPRankMax n y → CPRankMax (n + 1) (x + y)
/-
**Holor.cprankMax_nil** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：cprankMax_nil [Mul α] [AddMonoid α] (x : Holor α nil) : CPRankMax 1 x
参数：x : Holor α nil。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem cprankMax_nil [Mul α] [AddMonoid α] (x : Holor α nil) : CPRankMax 1 x := by
  have h := CPRankMax.succ 0 x 0 (CPRankMax1.nil x) CPRankMax.zero
  rwa [add_zero x, zero_add] at h
/-
**Holor.cprankMax_1** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：cprankMax_1 [Mul α] [AddMonoid α] {x : Holor α ds} (h : CPRankMax1 x) : CP
RankMax 1 x
参数：h : CPRankMax1 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem cprankMax_1 [Mul α] [AddMonoid α] {x : Holor α ds} (h : CPRankMax1 x) :
    CPRankMax 1 x := by
  have h' := CPRankMax.succ 0 x 0 h CPRankMax.zero
  rwa [zero_add, add_zero] at h'
/-
**Holor.cprankMax_add** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：∀ {α : Type} {ds : List ℕ} [inst : Mul α] [inst_1 : AddMonoid α] {m n : ℕ}
 {x y : Holor α ds},   Holor.CPRankMax m x → Holor.CPRankMax n y → Holor.CPRankM
ax (m + n) (x + y)
参数：m + n；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Holor.CPRankMax.brecOn`：∀ {α : Type} [inst : Mul α] [inst_1 : AddMonoid 
α]   {motive : (a : ℕ) → {ds : List ℕ} → (a_1 : Holor α ds) → Holor.CPRankMax a 
a_1 → Prop} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem cprankMax_add [Mul α] [AddMonoid α] :
    ∀ {m : ℕ} {n : ℕ} {x : Holor α ds} {y : Holor α ds},
      CPRankMax m x → CPRankMax n y → CPRankMax (m + n) (x + y)
  | 0, n, x, y, hx, hy => by
    match hx with
    | CPRankMax.zero => simp only [zero_add, hy]
  | m + 1, n, _, y, CPRankMax.succ _ x₁ x₂ hx₁ hx₂, hy => by
    suffices CPRankMax (m + n + 1) (x₁ + (x₂ + y)) by
      simpa only [add_comm, add_assoc, add_left_comm] using this
    apply CPRankMax.succ
    · assumption
    · exact cprankMax_add hx₂ hy

set_option backward.isDefEq.respectTransparency false in
/-
**Holor.cprankMax_mul** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：∀ {α : Type} {d : ℕ} {ds : List ℕ} [inst : NonUnitalNonAssocSemiring α] (n
 : ℕ) (x : Holor α [d]) (y : Holor α ds),   Holor.CPRankMax n y → Holor.CPRankMa
x n (x.mul y)
参数：n : ℕ；x : Holor α [d]；y : Holor α ds；x.mul y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Holor.CPRankMax.brecOn`：∀ {α : Type} [inst : Mul α] [inst_1 : AddMonoid 
α]   {motive : (a : ℕ) → {ds : List ℕ} → (a_1 : Holor α ds) → Holor.CPRankMax a 
a_1 → Prop} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Holor.mul_zero`：∀ {ds₁ ds₂ : List ℕ} {α : Type} [inst : MulZeroClass α] 
(x : Holor α ds₁), x.mul 0 = 0
· 使用定理 `Holor.mul_left_distrib`：mul_left_distrib [Distrib α] (x : Holor α ds₁) (
y : Holor α ds₂) (z : Holor α ds₂) : x otimes (y + z) = x otimes y + x otimes z
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Holor.cprankMax_add`：∀ {α : Type} {ds : List ℕ} [inst : Mul α] [inst_1 :
 AddMonoid α] {m n : ℕ} {x y : Holor α ds},   Holor.CPRankMax m x → Holor.CPRank
Max n y →…
· 使用定理 `Holor.cprankMax_1`：cprankMax_1 [Mul α] [AddMonoid α] {x : Holor α ds} (h
 : CPRankMax1 x) : CPRankMax 1 x
-/
theorem cprankMax_mul [NonUnitalNonAssocSemiring α] :
    ∀ (n : ℕ) (x : Holor α [d]) (y : Holor α ds), CPRankMax n y → CPRankMax n (x ⊗ y)
  | 0, x, _, CPRankMax.zero => by simp [mul_zero x, CPRankMax.zero]
  | n + 1, x, _, CPRankMax.succ _ y₁ y₂ hy₁ hy₂ => by
    rw [mul_left_distrib]
    rw [Nat.add_comm]
    apply cprankMax_add
    · exact cprankMax_1 (CPRankMax1.cons _ _ hy₁)
    · exact cprankMax_mul _ x y₂ hy₂
/-
**Holor.cprankMax_sum** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：cprankMax_sum [NonUnitalNonAssocSemiring α] {β} {n : Nat} (s : Finset β) (
f : β -> Holor α ds) : (forall x in s, CPRankMax n (f x)) -> CPRankMax (s.card *
 n) (∑ x in s, f x)
参数：s : Finset β；f : β -> Holor α ds。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_mul`：∀ (n : ℕ), 0 * n = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Nat.right_distrib`：∀ (n m k : ℕ), (n + m) * k = n * k + m * k
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Holor.cprankMax_add`：∀ {α : Type} {ds : List ℕ} [inst : Mul α] [inst_1 :
 AddMonoid α] {m n : ℕ} {x y : Holor α ds},   Holor.CPRankMax m x → Holor.CPRank
Max n y →…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
-/
theorem cprankMax_sum [NonUnitalNonAssocSemiring α] {β} {n : ℕ} (s : Finset β)
    (f : β → Holor α ds) : (∀ x ∈ s, CPRankMax n (f x)) → CPRankMax (s.card * n) (∑ x ∈ s, f x) :=
  letI := Classical.decEq β
  Finset.induction_on s (by simp [CPRankMax.zero])
    (by
      intro x s (h_x_notin_s : x ∉ s) ih h_cprank
      simp only [Finset.sum_insert h_x_notin_s, Finset.card_insert_of_notMem h_x_notin_s]
      rw [Nat.right_distrib]
      simp only [Nat.one_mul, Nat.add_comm]
      have ih' : CPRankMax (Finset.card s * n) (∑ x ∈ s, f x) := by grind
      exact cprankMax_add (h_cprank x (Finset.mem_insert_self x s)) ih')
/-
**Holor.cprankMax_upper_bound** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：cprankMax_upper_bound [Semiring α] : forall {ds}, forall x : Holor α ds, C
PRankMax ds.prod x | [], x => cprankMax_nil x | d :: ds, x => by have h_summands
 : forall i : { x // x in Finset.range d }, CPRankMax ds.prod (unitVec d i.1 oti
mes slice x i.1 (mem_range.1 i.2))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cprankMax_upper_bound [Semiring α] : ∀ {ds}, ∀ x : Holor α ds, CPRankMax ds.prod x
  | [], x => cprankMax_nil x
  | d :: ds, x => by
    have h_summands :
      ∀ i : { x // x ∈ Finset.range d },
        CPRankMax ds.prod (unitVec d i.1 ⊗ slice x i.1 (mem_range.1 i.2)) :=
      fun i => cprankMax_mul _ _ _ (cprankMax_upper_bound (slice x i.1 (mem_range.1 i.2)))
    have h_dds_prod : (List.cons d ds).prod = Finset.card (Finset.range d) * prod ds := by
      simp [Finset.card_range]
    have :
      CPRankMax (Finset.card (Finset.attach (Finset.range d)) * prod ds)
        (∑ i ∈ Finset.attach (Finset.range d),
          unitVec d i.val ⊗ slice x i.val (mem_range.1 i.2)) :=
      cprankMax_sum (Finset.range d).attach _ fun i _ => h_summands i
    have h_cprankMax_sum :
      CPRankMax (Finset.card (Finset.range d) * prod ds)
        (∑ i ∈ Finset.attach (Finset.range d),
          unitVec d i.val ⊗ slice x i.val (mem_range.1 i.2)) := by rwa [Finset.card_attach] at this
    rw [← sum_unitVec_mul_slice x]
    rw [h_dds_prod]
    exact h_cprankMax_sum

/-- The CP rank of a holor `x`: the smallest N such that
  `x` can be written as the sum of N holors of rank at most 1. -/
/-
**Holor.cprank** 是 Mathlib 中的一个定义，位于命名空间 `Holor`。
形式化陈述：cprank [Ring α] (x : Holor α ds) : Nat
参数：x : Holor α ds。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The CP rank of a holor `x`: the smallest N such that
  `x` can be written as the sum of N holors of rank at most 1.
-/
noncomputable def cprank [Ring α] (x : Holor α ds) : Nat :=
  @Nat.find (fun n => CPRankMax n x) (Classical.decPred _) ⟨ds.prod, cprankMax_upper_bound x⟩
/-
**Holor.cprank_upper_bound** 是 Mathlib 中的一个定理，位于命名空间 `Holor`。
形式化陈述：cprank_upper_bound [Ring α] : forall {ds}, forall x : Holor α ds, cprank x
 <= ds.prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
· 使用定理 `Holor.cprankMax_upper_bound`：cprankMax_upper_bound [Semiring α] : forall
 {ds}, forall x : Holor α ds, CPRankMax ds.prod x | [], x => cprankMax_nil x | d
 :: ds, x => by h…
-/
theorem cprank_upper_bound [Ring α] : ∀ {ds}, ∀ x : Holor α ds, cprank x ≤ ds.prod :=
  fun {ds} x =>
  letI := Classical.decPred fun n : ℕ => CPRankMax n x
  Nat.find_min' ⟨ds.prod, show (fun n => CPRankMax n x) ds.prod from cprankMax_upper_bound x⟩
    (cprankMax_upper_bound x)

end Holor

