/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
module

public import Mathlib.Data.List.Forall2
public import Mathlib.Data.Nat.Basic

/-!
# zip & unzip

This file provides results about `List.zipWith`, `List.zip` and `List.unzip` (definitions are in
core Lean).
`zipWith f l₁ l₂` applies `f : α → β → γ` pointwise to a list `l₁ : List α` and `l₂ : List β`. It
applies, until one of the lists is exhausted. For example,
`zipWith f [0, 1, 2] [6.28, 31] = [f 0 6.28, f 1 31]`.
`zip` is `zipWith` applied to `Prod.mk`. For example,
`zip [a₁, a₂] [b₁, b₂, b₃] = [(a₁, b₁), (a₂, b₂)]`.
`unzip` undoes `zip`. For example, `unzip [(a₁, b₁), (a₂, b₂)] = ([a₁, a₂], [b₁, b₂])`.
-/

public section

-- Make sure we don't import algebra
assert_not_exists Monoid

universe u

open Nat

namespace List

variable {α : Type u} {β γ δ ε : Type*}

open Function in
/-
**List.rightInverse_unzip_zip** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rightInverse_unzip_zip : RightInverse (unzip : List (α × β) -> List α × Li
st β) (uncurry zip)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightInverse_unzip_zip :
    RightInverse (unzip : List (α × β) → List α × List β) (uncurry zip) := by
  grind [zip_unzip]

@[simp]
/-
**List.zip_swap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type u_1} (l₁ : List α) (l₂ : List β), List.map Prod.s
wap (l₁.zip l₂) = l₂.zip l₁
参数：l₁ : List α；l₂ : List β；l₁.zip l₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zip_swap : ∀ (l₁ : List α) (l₂ : List β), (zip l₁ l₂).map Prod.swap = zip l₂ l₁
  | [], _ => zip_nil_right.symm
  | l₁, [] => by rw [zip_nil_right]; rfl
  | a :: l₁, b :: l₂ => by
    simp only [zip_cons_cons, map_cons, zip_swap l₁ l₂, Prod.swap_prod_mk]
/-
**List.forall_zipWith** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type u_1} {γ : Type u_2} {f : α → β → γ} {p : γ → Prop
} {l₁ : List α} {l₂ : List β},   l₁.length = l₂.length → (List.Forall p (List.zi
pWith f l₁ l₂) ↔ List.Forall₂ (fun x y => p (f x y)) l₁ l₂)
参数：List.Forall p (List.zipWith f l₁ l₂) ↔ List.Forall₂ (fun x y => p (f x y)) l₁
 l₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_zipWith {f : α → β → γ} {p : γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, length l₁ = length l₂ →
      (Forall p (zipWith f l₁ l₂) ↔ Forall₂ (fun x y => p (f x y)) l₁ l₂)
  | [], [], _ => by simp
  | a :: l₁, b :: l₂, h => by
    simp only [length_cons, succ_inj] at h
    simp [forall_zipWith h]
/-
**List.unzip_swap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：unzip_swap (l : List (α × β)) : unzip (l.map Prod.swap) = (unzip l).swap
参数：l : List (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.unzip_eq_map`：∀ {α : Type u_1} {β : Type u_2} {l : List (α × β)}, l
.unzip = (List.map Prod.fst l, List.map Prod.snd l)
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
-/
theorem unzip_swap (l : List (α × β)) : unzip (l.map Prod.swap) = (unzip l).swap := by
  simp only [unzip_eq_map, map_map]
  rfl

@[congr]
/-
**List.zipWith_congr** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：zipWith_congr (f g : α -> β -> γ) (la : List α) (lb : List β) (h : List.Fo
rall₂ (fun a b => f a b = g a b) la lb) : zipWith f la lb = zipWith g la lb
参数：f g : α -> β -> γ；la : List α；lb : List β；h : List.Forall₂ (fun a b => f a b 
= g a b) la lb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
-/
theorem zipWith_congr (f g : α → β → γ) (la : List α) (lb : List β)
    (h : List.Forall₂ (fun a b => f a b = g a b) la lb) : zipWith f la lb = zipWith g la lb := by
  induction h with
  | nil => rfl
  | cons hfg _ ih => exact congr_arg₂ _ hfg ih
/-
**List.zipWith_zipWith_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type u_1} {γ : Type u_2} {δ : Type u_3} {ε : Type u_4}
 (f : δ → γ → ε) (g : α → β → δ) (la : List α)   (lb : List β) (lc : List γ),   
List.zipWith f (List.zipWith g la lb) lc = List.zipWith3 (fun a b c => f (g a b)
 c) la lb lc
参数：f : δ → γ → ε；g : α → β → δ；la : List α；lb : List β；lc : List γ；List.zipWith 
g la lb；fun a b c => f (g a b) c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipWith_zipWith_left (f : δ → γ → ε) (g : α → β → δ) :
    ∀ (la : List α) (lb : List β) (lc : List γ),
      zipWith f (zipWith g la lb) lc = zipWith3 (fun a b c => f (g a b) c) la lb lc
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | _ :: as, _ :: bs, _ :: cs => congr_arg (cons _) <| zipWith_zipWith_left f g as bs cs
/-
**List.zipWith_zipWith_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type u_1} {γ : Type u_2} {δ : Type u_3} {ε : Type u_4}
 (f : α → δ → ε) (g : β → γ → δ) (la : List α)   (lb : List β) (lc : List γ),   
List.zipWith f la (List.zipWith g lb lc) = List.zipWith3 (fun a b c => f a (g b 
c)) la lb lc
参数：f : α → δ → ε；g : β → γ → δ；la : List α；lb : List β；lc : List γ；List.zipWith 
g lb lc；fun a b c => f a (g b c)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipWith_zipWith_right (f : α → δ → ε) (g : β → γ → δ) :
    ∀ (la : List α) (lb : List β) (lc : List γ),
      zipWith f la (zipWith g lb lc) = zipWith3 (fun a b c => f a (g b c)) la lb lc
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | _ :: as, _ :: bs, _ :: cs => congr_arg (cons _) <| zipWith_zipWith_right f g as bs cs

@[simp]
/-
**List.zipWith3_same_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type u_1} {γ : Type u_2} (f : α → α → β → γ) (la : Lis
t α) (lb : List β),   List.zipWith3 f la la lb = List.zipWith (fun a b => f a a 
b) la lb
参数：f : α → α → β → γ；la : List α；lb : List β；fun a b => f a a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipWith3_same_left (f : α → α → β → γ) :
    ∀ (la : List α) (lb : List β), zipWith3 f la la lb = zipWith (fun a b => f a a b) la lb
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => congr_arg (cons _) <| zipWith3_same_left f as bs

@[simp]
/-
**List.zipWith3_same_mid** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type u_1} {γ : Type u_2} (f : α → β → α → γ) (la : Lis
t α) (lb : List β),   List.zipWith3 f la lb la = List.zipWith (fun a b => f a b 
a) la lb
参数：f : α → β → α → γ；la : List α；lb : List β；fun a b => f a b a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipWith3_same_mid (f : α → β → α → γ) :
    ∀ (la : List α) (lb : List β), zipWith3 f la lb la = zipWith (fun a b => f a b a) la lb
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => congr_arg (cons _) <| zipWith3_same_mid f as bs

@[simp]
/-
**List.zipWith3_same_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type u_1} {γ : Type u_2} (f : α → β → β → γ) (la : Lis
t α) (lb : List β),   List.zipWith3 f la lb lb = List.zipWith (fun a b => f a b 
b) la lb
参数：f : α → β → β → γ；la : List α；lb : List β；fun a b => f a b b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipWith3_same_right (f : α → β → β → γ) :
    ∀ (la : List α) (lb : List β), zipWith3 f la lb lb = zipWith (fun a b => f a b b) la lb
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => congr_arg (cons _) <| zipWith3_same_right f as bs
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : α → α → β) [IsSymmOp f] : IsSymmOp (zipWith f) :=
  ⟨fun _ _ => zipWith_comm_of_comm IsSymmOp.symm_op⟩

@[simp]
/-
**List.length_revzip** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_revzip (l : List α) : length (revzip l) = length l
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_zip`：∀ {α : Type u_1} {β : Type u_2} {l₁ : List α} {l₂ : Lis
t β}, (l₁.zip l₂).length = min l₁.length l₂.length
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_revzip (l : List α) : length (revzip l) = length l := by
  simp only [revzip, length_zip, length_reverse, min_self]

@[simp]
/-
**List.unzip_revzip** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：unzip_revzip (l : List α) : (revzip l).unzip = (l, l.reverse)
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.unzip_zip`：∀ {α : Type u_1} {β : Type u_2} {l₁ : List α} {l₂ : List
 β}, l₁.length = l₂.length → (l₁.zip l₂).unzip = (l₁, l₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
-/
theorem unzip_revzip (l : List α) : (revzip l).unzip = (l, l.reverse) :=
  unzip_zip length_reverse.symm

@[simp]
/-
**List.revzip_map_fst** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：revzip_map_fst (l : List α) : (revzip l).map Prod.fst = l
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.unzip_fst`：∀ {α : Type u_1} {β : Type u_2} {l : List (α × β)}, l.un
zip.1 = List.map Prod.fst l
· 使用定理 `List.unzip_revzip`：unzip_revzip (l : List α) : (revzip l).unzip = (l, l.
reverse)
-/
theorem revzip_map_fst (l : List α) : (revzip l).map Prod.fst = l := by
  rw [← unzip_fst, unzip_revzip]

@[simp]
/-
**List.revzip_map_snd** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：revzip_map_snd (l : List α) : (revzip l).map Prod.snd = l.reverse
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.unzip_snd`：∀ {α : Type u_1} {β : Type u_2} {l : List (α × β)}, l.un
zip.2 = List.map Prod.snd l
· 使用定理 `List.unzip_revzip`：unzip_revzip (l : List α) : (revzip l).unzip = (l, l.
reverse)
-/
theorem revzip_map_snd (l : List α) : (revzip l).map Prod.snd = l.reverse := by
  rw [← unzip_snd, unzip_revzip]
/-
**List.reverse_revzip** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reverse_revzip (l : List α) : reverse l.revzip = revzip l.reverse
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.zip_unzip`：∀ {α : Type u_1} {β : Type u_2} (l : List (α × β)), l.un
zip.1.zip l.unzip.2 = l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.unzip_eq_map`：∀ {α : Type u_1} {β : Type u_2} {l : List (α × β)}, l
.unzip = (List.map Prod.fst l, List.map Prod.snd l)
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `List.map_fst_zip`：∀ {α : Type u_1} {β : Type u_2} {l₁ : List α} {l₂ : Li
st β}, l₁.length ≤ l₂.length → List.map Prod.fst (l₁.zip l₂) = l₁
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `List.map_snd_zip`：∀ {α : Type u_1} {β : Type u_2} {l₁ : List α} {l₂ : Li
st β}, l₂.length ≤ l₁.length → List.map Prod.snd (l₁.zip l₂) = l₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reverse_revzip (l : List α) : reverse l.revzip = revzip l.reverse := by
  rw [← zip_unzip (revzip l).reverse]
  simp [unzip_eq_map, revzip, map_reverse, map_fst_zip, map_snd_zip]
/-
**List.revzip_swap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：revzip_swap (l : List α) : (revzip l).map Prod.swap = revzip l.reverse
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.zip_swap`：∀ {α : Type u} {β : Type u_1} (l₁ : List α) (l₂ : List β)
, List.map Prod.swap (l₁.zip l₂) = l₂.zip l₁
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem revzip_swap (l : List α) : (revzip l).map Prod.swap = revzip l.reverse := by simp [revzip]
/-
**List.mem_zip_inits_tails** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_zip_inits_tails {l : List α} {init tail : List α} : (init, tail) in zi
p l.inits l.tails ↔ init ++ tail = l
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
· 使用定理 `List.zip_nil_right`：∀ {α : Type u} {β : Type v} {l : List α}, l.zip [] =
 []
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `List.zip_map_left`：∀ {α : Type u_1} {γ : Type u_2} {β : Type u_3} {f : α
 → γ} {l₁ : List α} {l₂ : List β},   (List.map f l₁).zip l₂ = List.map (Prod.map
 f id) …
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `Prod.exists`：∀ {α : Type u_1} {β : Type u_2} {p : α × β → Prop}, (∃ x, p
 x) ↔ ∃ a b, p (a, b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem mem_zip_inits_tails {l : List α} {init tail : List α} :
    (init, tail) ∈ zip l.inits l.tails ↔ init ++ tail = l := by
  induction l generalizing init tail <;> simp_rw [tails, inits, zip_cons_cons]
  case nil => simp
  case cons hd tl ih =>
    constructor <;> rw [mem_cons, zip_map_left, mem_map, Prod.exists]
    · rintro (⟨rfl, rfl⟩ | ⟨_, _, h, rfl, rfl⟩)
      · simp
      · simp [ih.mp h]
    · rcases init with - | ⟨hd', tl'⟩
      · simp
      · intro h
        right
        use tl', tail
        simp_all

end List

