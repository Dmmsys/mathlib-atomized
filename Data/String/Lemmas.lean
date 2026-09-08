/-
Copyright (c) 2021 Chris Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Bailey
-/
module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.String.Defs

/-!
# Miscellaneous lemmas about strings
-/

public section

namespace String

/-
**String.congr_append** 是 Mathlib 中的一个引理，位于命名空间 `String`。
形式化陈述：congr_append (a b : String) : a ++ b = String.ofList (a.toList ++ b.toList
)
参数：a b : String。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `String.ofList_append`：∀ {l₁ l₂ : List Char}, String.ofList (l₁ ++ l₂) = 
String.ofList l₁ ++ String.ofList l₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `String.ofList_toList`：∀ {s : String}, String.ofList s.toList = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma congr_append (a b : String) : a ++ b = String.ofList (a.toList ++ b.toList) := by simp
/-
**String.length_replicate** 是 Mathlib 中的一个定理，位于命名空间 `String`。
形式化陈述：∀ (n : ℕ) (c : Char), (String.replicate n c).length = n
参数：n : ℕ；c : Char；String.replicate n c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `String.toList_ofList`：∀ {l : List Char}, (String.ofList l).toList = l
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma length_replicate (n : ℕ) (c : Char) : (replicate n c).length = n := by
  simp only [← length_toList, String.replicate, String.toList_ofList, List.length_replicate]
/-
**String.length_eq_list_length** 是 Mathlib 中的一个引理，位于命名空间 `String`。
形式化陈述：length_eq_list_length (l : List Char) : (String.ofList l).length = l.lengt
h
参数：l : List Char。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `String.length_ofList`：∀ {l : List Char}, (String.ofList l).length = l.le
ngth
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma length_eq_list_length (l : List Char) : (String.ofList l).length = l.length := by
  simp

/-- The length of the String returned by `String.leftpad n a c` is equal
  to the larger of `n` and `s.length` -/
/-
**String.length_leftpad** 是 Mathlib 中的一个定理，位于命名空间 `String`。
形式化陈述：∀ (n : ℕ) (c : Char) (s : String), (String.leftpad n c s).length = max n s
.length
参数：n : ℕ；c : Char；s : String；String.leftpad n c s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `String.length_toList`：∀ {s : String}, s.toList.length = s.length
· 使用定理 `String.ofList_append`：∀ {l₁ l₂ : List Char}, String.ofList (l₁ ++ l₂) = 
String.ofList l₁ ++ String.ofList l₂
· 使用定理 `String.ofList_toList`：∀ {s : String}, String.ofList s.toList = s
· 使用定理 `String.length_append`：∀ (s t : String), (s ++ t).length = s.length + t.l
ength
· 使用定理 `String.length_ofList`：∀ {l : List Char}, (String.ofList l).length = l.le
ngth
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
· 使用定理 `Nat.sub_add_eq_max`：∀ (a b : ℕ), a - b + b = max a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The length of the String returned by `String.leftpad n a c` is equal
  to the larger of `n` and `s.length`
-/
@[simp] lemma length_leftpad (n : ℕ) (c : Char) :
    ∀ (s : String), (leftpad n c s).length = max n s.length
  | s => by simp [leftpad, length_toList, Nat.sub_add_eq_max]
/-
**String.leftpad_prefix** 是 Mathlib 中的一个定理，位于命名空间 `String`。
形式化陈述：∀ (n : ℕ) (c : Char) (s : String), (String.replicate (n - s.length) c).IsP
refix (String.leftpad n c s)
参数：n : ℕ；c : Char；s : String；String.replicate (n - s.length) c；String.leftpad n 
c s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `String.toList_ofList`：∀ {l : List Char}, (String.ofList l).toList = l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `String.length_toList`：∀ {s : String}, s.toList.length = s.length
· 使用定理 `String.ofList_append`：∀ {l₁ l₂ : List Char}, String.ofList (l₁ ++ l₂) = 
String.ofList l₁ ++ String.ofList l₂
· 使用定理 `String.ofList_toList`：∀ {s : String}, String.ofList s.toList = s
· 使用定理 `String.toList_append`：∀ {s t : String}, (s ++ t).toList = s.toList ++ t.
toList
-/
lemma leftpad_prefix (n : ℕ) (c : Char) : ∀ s, IsPrefix (replicate (n - length s) c) (leftpad n c s)
  | s => by simp [leftpad, IsPrefix, replicate, length_toList]
/-
**String.leftpad_suffix** 是 Mathlib 中的一个定理，位于命名空间 `String`。
形式化陈述：∀ (n : ℕ) (c : Char) (s : String), s.IsSuffix (String.leftpad n c s)
参数：n : ℕ；c : Char；s : String；String.leftpad n c s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `String.ofList_append`：∀ {l₁ l₂ : List Char}, String.ofList (l₁ ++ l₂) = 
String.ofList l₁ ++ String.ofList l₂
· 使用定理 `String.ofList_toList`：∀ {s : String}, String.ofList s.toList = s
· 使用定理 `String.toList_append`：∀ {s t : String}, (s ++ t).toList = s.toList ++ t.
toList
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `String.toList_ofList`：∀ {l : List Char}, (String.ofList l).toList = l
-/
lemma leftpad_suffix (n : ℕ) (c : Char) : ∀ s, IsSuffix s (leftpad n c s)
  | s => by simp [leftpad, IsSuffix]

end String

