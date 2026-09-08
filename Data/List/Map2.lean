/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Data.List.Defs
public import Mathlib.Tactic.Common

/-!
# Map₂ Lemmas

This file contains additional lemmas about a number of list functions related to combining zipping
Lists together. In particular, we include lemmas about:

* `map₂Left'`
* `map₂Right'`
* `zipWith`
* `zipLeft'`
* `zipRight'`

-/

public section

assert_not_exists GroupWithZero
assert_not_exists Lattice
assert_not_exists Prod.swap_eq_iff_eq_swap
assert_not_exists Ring
assert_not_exists Set.range

open Function

open Nat hiding one_pos

namespace List

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {l₁ l₂ : List α}

/-! ### map₂Left' -/

section Map₂Left'

-- The definitional equalities for `map₂Left'` can already be used by the
-- simplifier because `map₂Left'` is marked `@[simp]`.
@[simp]
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂Left'_nil_right (f : α → Option β → γ) (as) :
    map₂Left' f as [] = (as.map fun a => f a none, []) := by cases as <;> rfl

end Map₂Left'

/-! ### map₂Right' -/

section Map₂Right'

variable (f : Option α → β → γ) (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂Right'_nil_left : map₂Right' f [] bs = (bs.map (f none), []) := by cases bs <;> rfl

@[simp]
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂Right'_nil_right : map₂Right' f as [] = ([], as) :=
  rfl

@[simp]
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂Right'_nil_cons : map₂Right' f [] (b :: bs) = (f none b :: bs.map (f none), []) :=
  rfl

@[simp]
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂Right'_cons_cons :
    map₂Right' f (a :: as) (b :: bs) =
      let r := map₂Right' f as bs
      (f (some a) b :: r.fst, r.snd) :=
  rfl

end Map₂Right'

/-! ### zipWith -/

/-
**List.nil_zipWith** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nil_zipWith (f : α -> β -> γ) (l : List β) : zipWith f [] l = []
参数：f : α -> β -> γ；l : List β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
### zipWith
-/
theorem nil_zipWith (f : α → β → γ) (l : List β) : zipWith f [] l = [] := by cases l <;> rfl
/-
**List.zipWith_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：zipWith_nil (f : α -> β -> γ) (l : List α) : zipWith f l [] = []
参数：f : α -> β -> γ；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zipWith_nil (f : α → β → γ) (l : List α) : zipWith f l [] = [] := by cases l <;> rfl

@[simp]
/-
**List.zipWith_flip** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (as : List α) (bs
 : List β),   List.zipWith (flip f) bs as = List.zipWith f as bs
参数：f : α → β → γ；as : List α；bs : List β；flip f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipWith_flip (f : α → β → γ) : ∀ as bs, zipWith (flip f) bs as = zipWith f as bs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    simp! [zipWith_flip]
    rfl


/-! ### zipLeft' -/

section ZipLeft'

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
/-
**List.zipLeft'_nil_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type v} (as : List α), as.zipLeft' [] = (List.map (fun
 a => (a, none)) as, [])
参数：as : List α；List.map (fun a => (a, none)) as, []。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.zipLeft'`：zipLeft'_nil_right : zipLeft' as ([] : List β) = (as.map 
fun a => (a, none), [])
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zipLeft'_nil_right : zipLeft' as ([] : List β) = (as.map fun a => (a, none), []) := by
  cases as <;> rfl

@[simp]
/-
**List.zipLeft'_nil_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type v} (bs : List β), [].zipLeft' bs = ([], bs)
参数：bs : List β；[], bs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.zipLeft'`：zipLeft'_nil_right : zipLeft' as ([] : List β) = (as.map 
fun a => (a, none), [])
-/
theorem zipLeft'_nil_left : zipLeft' ([] : List α) bs = ([], bs) :=
  rfl

@[simp]
/-
**List.zipLeft'_cons_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type v} (a : α) (as : List α),   (a :: as).zipLeft' []
 = ((a, none) :: List.map (fun a => (a, none)) as, [])
参数：a : α；as : List α；a :: as；(a, none) :: List.map (fun a => (a, none)) as, []。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.zipLeft'`：zipLeft'_nil_right : zipLeft' as ([] : List β) = (as.map 
fun a => (a, none), [])
-/
theorem zipLeft'_cons_nil :
    zipLeft' (a :: as) ([] : List β) = ((a, none) :: as.map fun a => (a, none), []) :=
  rfl

@[simp]
/-
**List.zipLeft'_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type v} (a : α) (as : List α) (b : β) (bs : List β),  
 (a :: as).zipLeft' (b :: bs) =     have r := as.zipLeft' bs;     ((a, some b) :
: r.1, r.2)
参数：a : α；as : List α；b : β；bs : List β；a :: as；b :: bs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.zipLeft'`：zipLeft'_nil_right : zipLeft' as ([] : List β) = (as.map 
fun a => (a, none), [])
-/
theorem zipLeft'_cons_cons :
    zipLeft' (a :: as) (b :: bs) =
      let r := zipLeft' as bs
      ((a, some b) :: r.fst, r.snd) :=
  rfl

end ZipLeft'

/-! ### zipRight' -/

section ZipRight'

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
/-
**List.zipRight'_nil_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type v} (bs : List β), [].zipRight' bs = (List.map (fu
n b => (none, b)) bs, [])
参数：bs : List β；List.map (fun b => (none, b)) bs, []。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.zipRight'`：zipRight'_nil_left : zipRight' ([] : List α) bs = (bs.ma
p fun b => (none, b), [])
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zipRight'_nil_left : zipRight' ([] : List α) bs = (bs.map fun b => (none, b), []) := by
  cases bs <;> rfl

@[simp]
/-
**List.zipRight'_nil_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type v} (as : List α), as.zipRight' [] = ([], as)
参数：as : List α；[], as。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.zipRight'`：zipRight'_nil_left : zipRight' ([] : List α) bs = (bs.ma
p fun b => (none, b), [])
-/
theorem zipRight'_nil_right : zipRight' as ([] : List β) = ([], as) :=
  rfl

@[simp]
/-
**List.zipRight'_nil_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type v} (b : β) (bs : List β),   [].zipRight' (b :: bs
) = ((none, b) :: List.map (fun b => (none, b)) bs, [])
参数：b : β；bs : List β；b :: bs；(none, b) :: List.map (fun b => (none, b)) bs, []。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.zipRight'`：zipRight'_nil_left : zipRight' ([] : List α) bs = (bs.ma
p fun b => (none, b), [])
-/
theorem zipRight'_nil_cons :
    zipRight' ([] : List α) (b :: bs) = ((none, b) :: bs.map fun b => (none, b), []) :=
  rfl

@[simp]
/-
**List.zipRight'_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type v} (a : α) (as : List α) (b : β) (bs : List β),  
 (a :: as).zipRight' (b :: bs) =     have r := as.zipRight' bs;     ((some a, b)
 :: r.1, r.2)
参数：a : α；as : List α；b : β；bs : List β；a :: as；b :: bs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.zipRight'`：zipRight'_nil_left : zipRight' ([] : List α) bs = (bs.ma
p fun b => (none, b), [])
-/
theorem zipRight'_cons_cons :
    zipRight' (a :: as) (b :: bs) =
      let r := zipRight' as bs
      ((some a, b) :: r.fst, r.snd) :=
  rfl

end ZipRight'

/-! ### map₂Left -/

section Map₂Left

variable (f : α → Option β → γ) (as : List α)

-- The definitional equalities for `map₂Left` can already be used by the
-- simplifier because `map₂Left` is marked `@[simp]`.
@[simp]
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂Left_nil_right : map₂Left f as [] = as.map fun a => f a none := by cases as <;> rfl
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂Left_eq_map₂Left' : ∀ as bs, map₂Left f as bs = (map₂Left' f as bs).fst
  | [], _ => by simp
  | a :: as, [] => by simp
  | a :: as, b :: bs => by simp [map₂Left_eq_map₂Left']
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂Left_eq_zipWith :
    ∀ as bs, length as ≤ length bs → map₂Left f as bs = zipWith (fun a b => f a (some b)) as bs
  | [], [], _ => by simp
  | [], _ :: _, _ => by simp
  | a :: as, [], h => by
    simp at h
  | a :: as, b :: bs, h => by
    simp only [length_cons, succ_le_succ_iff] at h
    simp [h, map₂Left_eq_zipWith]

end Map₂Left

/-! ### map₂Right -/

section Map₂Right

variable (f : Option α → β → γ) (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂Right_nil_left : map₂Right f [] bs = bs.map (f none) := by cases bs <;> rfl

@[simp]
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂Right_nil_right : map₂Right f as [] = [] :=
  rfl

@[simp]
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂Right_nil_cons : map₂Right f [] (b :: bs) = f none b :: bs.map (f none) :=
  rfl

@[simp]
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂Right_cons_cons :
    map₂Right f (a :: as) (b :: bs) = f (some a) b :: map₂Right f as bs :=
  rfl
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂Right_eq_map₂Right' : map₂Right f as bs = (map₂Right' f as bs).fst := by
  simp only [map₂Right, map₂Right', map₂Left_eq_map₂Left']
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂Right_eq_zipWith (h : length bs ≤ length as) :
    map₂Right f as bs = zipWith (fun a b => f (some a) b) as bs := by
  have : (fun a b => flip f a (some b)) = flip fun a b => f (some a) b := rfl
  simp only [map₂Right, map₂Left_eq_zipWith, zipWith_flip, *]

end Map₂Right

/-! ### zipLeft -/

section ZipLeft

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
/-
**List.zipLeft_nil_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：zipLeft_nil_right : zipLeft as ([] : List β) = as.map fun a => (a, none)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zipLeft_nil_right : zipLeft as ([] : List β) = as.map fun a => (a, none) := by
  cases as <;> rfl

@[simp]
/-
**List.zipLeft_nil_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：zipLeft_nil_left : zipLeft ([] : List α) bs = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipLeft_nil_left : zipLeft ([] : List α) bs = [] :=
  rfl

@[simp]
/-
**List.zipLeft_cons_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：zipLeft_cons_nil : zipLeft (a :: as) ([] : List β) = (a, none) :: as.map f
un a => (a, none)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipLeft_cons_nil :
    zipLeft (a :: as) ([] : List β) = (a, none) :: as.map fun a => (a, none) :=
  rfl

@[simp]
/-
**List.zipLeft_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：zipLeft_cons_cons : zipLeft (a :: as) (b :: bs) = (a, some b) :: zipLeft a
s bs
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipLeft_cons_cons : zipLeft (a :: as) (b :: bs) = (a, some b) :: zipLeft as bs :=
  rfl
/-
**List.zipLeft_eq_zipLeft'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：zipLeft_eq_zipLeft' (as : List α) (bs : List β) : zipLeft as bs = (zipLeft
' as bs).fst
参数：as : List α；bs : List β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.zipLeft'`：zipLeft'_nil_right : zipLeft' as ([] : List β) = (as.map 
fun a => (a, none), [])
-/
theorem zipLeft_eq_zipLeft' (as : List α) (bs : List β) : zipLeft as bs = (zipLeft' as bs).fst := by
  rw [zipLeft, zipLeft']
  cases as with
  | nil => rfl
  | cons _ atl =>
    cases bs with
    | nil => rfl
    | cons _ btl =>
      rw [zipWithLeft, zipWithLeft', cons_inj_right]
      exact zipLeft_eq_zipLeft' atl btl

end ZipLeft

/-! ### zipRight -/

section ZipRight

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
/-
**List.zipRight_nil_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：zipRight_nil_left : zipRight ([] : List α) bs = bs.map fun b => (none, b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zipRight_nil_left : zipRight ([] : List α) bs = bs.map fun b => (none, b) := by
  cases bs <;> rfl

@[simp]
/-
**List.zipRight_nil_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：zipRight_nil_right : zipRight as ([] : List β) = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipRight_nil_right : zipRight as ([] : List β) = [] :=
  rfl

@[simp]
/-
**List.zipRight_nil_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：zipRight_nil_cons : zipRight ([] : List α) (b :: bs) = (none, b) :: bs.map
 fun b => (none, b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipRight_nil_cons :
    zipRight ([] : List α) (b :: bs) = (none, b) :: bs.map fun b => (none, b) :=
  rfl

@[simp]
/-
**List.zipRight_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：zipRight_cons_cons : zipRight (a :: as) (b :: bs) = (some a, b) :: zipRigh
t as bs
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipRight_cons_cons : zipRight (a :: as) (b :: bs) = (some a, b) :: zipRight as bs :=
  rfl
/-
**List.zipRight_eq_zipRight'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：zipRight_eq_zipRight' : zipRight as bs = (zipRight' as bs).fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.zipRight'`：zipRight'_nil_left : zipRight' ([] : List α) bs = (bs.ma
p fun b => (none, b), [])
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.zipRight_nil_left`：zipRight_nil_left : zipRight ([] : List α) bs = 
bs.map fun b => (none, b)
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.zipRight'_nil_left`：∀ {α : Type u} {β : Type v} (bs : List β), [].z
ipRight' bs = (List.map (fun b => (none, b)) bs, [])
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem zipRight_eq_zipRight' : zipRight as bs = (zipRight' as bs).fst := by
  induction as generalizing bs <;> cases bs <;> simp [*]

end ZipRight

end List

