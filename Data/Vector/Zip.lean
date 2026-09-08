/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Vector.Basic

/-!
# The `zipWith` operation on vectors.
-/

@[expose] public section

namespace List

namespace Vector

section ZipWith

variable {α β γ : Type*} {n : ℕ} (f : α → β → γ)

/-- Apply the function `f : α → β → γ` to each corresponding pair of elements from two vectors. -/
/-
**List.Vector.zipWith** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：zipWith : Vector α n -> Vector β n -> Vector γ n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply the function `f : α → β → γ` to each corresponding pair of elements from t
wo vectors.
-/
def zipWith : Vector α n → Vector β n → Vector γ n := fun x y => ⟨List.zipWith f x.1 y.1, by simp⟩

@[simp]
/-
**List.Vector.zipWith_toList** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：zipWith_toList (x : Vector α n) (y : Vector β n) : (Vector.zipWith f x y).
toList = List.zipWith f x.toList y.toList
参数：x : Vector α n；y : Vector β n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipWith_toList (x : Vector α n) (y : Vector β n) :
    (Vector.zipWith f x y).toList = List.zipWith f x.toList y.toList :=
  rfl

@[simp]
/-
**List.Vector.zipWith_get** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：zipWith_get (x : Vector α n) (y : Vector β n) (i) : (Vector.zipWith f x y)
.get i = f (x.get i) (y.get i)
参数：x : Vector α n；y : Vector β n；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.lt_length_left_of_zipWith`：∀ {α : Type u_1} {β : Type u_2} {γ : Typ
e u_3} {f : α → β → γ} {i : ℕ} {l : List α} {l' : List β},   i < (List.zipWith f
 l l').length → i < …
· 使用定理 `List.lt_length_right_of_zipWith`：∀ {α : Type u_1} {β : Type u_2} {γ : Ty
pe u_3} {f : α → β → γ} {i : ℕ} {l : List α} {l' : List β},   i < (List.zipWith 
f l l').length → i < …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_zipWith`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f 
: α → β → γ} {l : List α} {l' : List β} {i : ℕ}   {h : i < (List.zipWith f l l')
.length}, …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zipWith_get (x : Vector α n) (y : Vector β n) (i) :
    (Vector.zipWith f x y).get i = f (x.get i) (y.get i) := by
  dsimp only [Vector.zipWith, Vector.get]
  simp

@[simp]
/-
**List.Vector.zipWith_tail** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：zipWith_tail (x : Vector α n) (y : Vector β n) : (Vector.zipWith f x y).ta
il = Vector.zipWith f x.tail y.tail
参数：x : Vector α n；y : Vector β n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.ext`：∀ {α : Type u_1} {n : ℕ} {v w : List.Vector α n}, (∀ (m
 : Fin n), v.get m = w.get m) → v = w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.get_tail`：get_tail (x : Vector α n) (i) : x.tail.get i = x.g
et ⟨i.1 + 1, by lia⟩
· 使用定理 `List.Vector.zipWith_get`：zipWith_get (x : Vector α n) (y : Vector β n) (
i) : (Vector.zipWith f x y).get i = f (x.get i) (y.get i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zipWith_tail (x : Vector α n) (y : Vector β n) :
    (Vector.zipWith f x y).tail = Vector.zipWith f x.tail y.tail := by
  ext
  simp [get_tail]

@[to_additive]
/-
**List.Vector.prod_mul_prod_eq_prod_zipWith** 是 Mathlib 中的一个定理，位于命名空间 `List.Vect
or`。
形式化陈述：prod_mul_prod_eq_prod_zipWith [CommMonoid α] (x y : Vector α n) : x.toList
.prod * y.toList.prod = (Vector.zipWith (· * ·) x y).toList.prod
参数：x y : Vector α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.prod_mul_prod_eq_prod_zipWith_of_length_eq`：prod_mul_prod_eq_prod_z
ipWith_of_length_eq (l l' : List M) (h : l.length = l'.length) : l.prod * l'.pro
d = (zipWith (· * ·) l l').prod
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.Vector.toList_length`：toList_length (v : Vector α n) : (toList v).l
ength = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem prod_mul_prod_eq_prod_zipWith [CommMonoid α] (x y : Vector α n) :
    x.toList.prod * y.toList.prod = (Vector.zipWith (· * ·) x y).toList.prod :=
  List.prod_mul_prod_eq_prod_zipWith_of_length_eq x.toList y.toList
    ((toList_length x).trans (toList_length y).symm)

end ZipWith

end Vector

end List

