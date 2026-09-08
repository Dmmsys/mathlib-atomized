/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Order.Basic

/-!
# Sums and products from lists

This file provides basic results about `List.prod`, `List.sum`, which calculate the product and sum
of elements of a list and `List.alternatingProd`, `List.alternatingSum`, their alternating
counterparts.
-/

public section
assert_not_imported Mathlib.Algebra.Order.Group.Nat

variable {ι α β M N P G : Type*}

namespace List

section Monoid

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

open scoped Relator in
@[to_additive]
/-
**List.rel_prod** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rel_prod {R : M -> N -> Prop} (h : R 1 1) (hf : (R ⇒ R ⇒ R) (· * ·) (· * ·
)) : (Forall₂ R ⇒ R) prod prod
参数：h : R 1 1；hf : (R ⇒ R ⇒ R) (· * ·) (· * ·)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rel_foldr`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type
 u_4} {R : α → β → Prop} {P : γ → δ → Prop},   Relator.LiftFun (Relator.LiftFun 
R (R…
-/
theorem rel_prod {R : M → N → Prop} (h : R 1 1) (hf : (R ⇒ R ⇒ R) (· * ·) (· * ·)) :
    (Forall₂ R ⇒ R) prod prod :=
  rel_foldr hf h

@[to_additive]
/-
**List.prod_hom_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_hom_nonempty {l : List M} {F : Type*} [FunLike F M N] [MulHomClass F 
M N] (f : F) (hl : l != []) : (l.map f).prod = f l.prod
参数：f : F；hl : l != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem prod_hom_nonempty {l : List M} {F : Type*} [FunLike F M N] [MulHomClass F M N] (f : F)
    (hl : l ≠ []) : (l.map f).prod = f l.prod :=
  match l, hl with | x :: xs, hl => by induction xs generalizing x <;> simp_all

@[to_additive]
/-
**List.prod_hom** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_hom (l : List M) {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (
f : F) : (l.map f).prod = f l.prod
参数：l : List M；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `List.foldr_map`：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β : Type u_3} {f : α₁
 → α₂} {g : α₂ → β → β} {l : List α₁} {init : β},   List.foldr g init (List.map 
f l)…
· 使用定理 `List.foldr_hom`：∀ {β₁ : Type u_1} {β₂ : Type u_2} {α : Type u_3} (f : β₁
 → β₂) {g₁ : α → β₁ → β₁} {g₂ : α → β₂ → β₂} {l : List α}   {init : β₁}, (∀ (x :
 α) …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem prod_hom (l : List M) {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) :
    (l.map f).prod = f l.prod := by
  simp only [prod, foldr_map, ← map_one f]
  exact l.foldr_hom f (fun x y => (map_mul f x y).symm)

@[to_additive]
/-
**List.prod_hom** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_hom (l : List M) {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (
f : F) : (l.map f).prod = f l.prod
参数：l : List M；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `List.foldr_map`：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β : Type u_3} {f : α₁
 → α₂} {g : α₂ → β → β} {l : List α₁} {init : β},   List.foldr g init (List.map 
f l)…
· 使用定理 `List.foldr_hom`：∀ {β₁ : Type u_1} {β₂ : Type u_2} {α : Type u_3} (f : β₁
 → β₂) {g₁ : α → β₁ → β₁} {g₂ : α → β₂ → β₂} {l : List α}   {init : β₁}, (∀ (x :
 α) …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem prod_hom₂_nonempty {l : List ι} (f : M → N → P)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (f₁ : ι → M) (f₂ : ι → N) (hl : l ≠ []) :
    (l.map fun i => f (f₁ i) (f₂ i)).prod = f (l.map f₁).prod (l.map f₂).prod := by
  match l, hl with | x :: xs, hl => induction xs generalizing x <;> simp_all

@[to_additive]
/-
**List.prod_hom** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_hom (l : List M) {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (
f : F) : (l.map f).prod = f l.prod
参数：l : List M；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `List.foldr_map`：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β : Type u_3} {f : α₁
 → α₂} {g : α₂ → β → β} {l : List α₁} {init : β},   List.foldr g init (List.map 
f l)…
· 使用定理 `List.foldr_hom`：∀ {β₁ : Type u_1} {β₂ : Type u_2} {α : Type u_3} (f : β₁
 → β₂) {g₁ : α → β₁ → β₁} {g₂ : α → β₂ → β₂} {l : List α}   {init : β₁}, (∀ (x :
 α) …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem prod_hom₂ (l : List ι) (f : M → N → P) (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d)
    (hf' : f 1 1 = 1) (f₁ : ι → M) (f₂ : ι → N) :
    (l.map fun i => f (f₁ i) (f₂ i)).prod = f (l.map f₁).prod (l.map f₂).prod := by
  simp only [prod_eq_foldr, foldr_map]
  rw [← foldr_hom₂ l f _ _ ((fun x y => f (f₁ x) (f₂ x) * y)) _ _ (by simp [hf]), hf']

@[to_additive (attr := simp)]
/-
**List.prod_map_mul** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_map_mul {M : Type*} [CommMonoid M] {l : List ι} {f g : ι -> M} : (l.m
ap fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.prod_hom₂`：prod_hom₂ (l : List ι) (f : M -> N -> P) (hf : forall a 
b c d, f (a * b) (c * d) = f a c * f b d) (hf' : f 1 1 = 1) (f₁ : ι -> M) (f₂ : 
ι ->…
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem prod_map_mul {M : Type*} [CommMonoid M] {l : List ι} {f g : ι → M} :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod :=
  l.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _

@[to_additive]
/-
**List.prod_map_hom** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_map_hom (L : List ι) (f : ι -> M) {G : Type*} [FunLike G M N] [Monoid
HomClass G M N] (g : G) : (L.map (g ∘ f)).prod = g (L.map f).prod
参数：L : List ι；f : ι -> M；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.prod_hom`：prod_hom (l : List M) {F : Type*} [FunLike F M N] [Monoid
HomClass F M N] (f : F) : (l.map f).prod = f l.prod
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
-/
theorem prod_map_hom (L : List ι) (f : ι → M) {G : Type*} [FunLike G M N] [MonoidHomClass G M N]
    (g : G) :
    (L.map (g ∘ f)).prod = g (L.map f).prod := by rw [← prod_hom, map_map]

@[to_additive (attr := simp)]
/-
**List.prod_take_mul_prod_drop** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_take_mul_prod_drop (L : List M) (i : Nat) : (L.take i).prod * (L.drop
 i).prod = L.prod
参数：L : List M；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_take_mul_prod_drop (L : List M) (i : ℕ) :
    (L.take i).prod * (L.drop i).prod = L.prod := by
  simp [← prod_append]

@[to_additive (attr := simp)]
/-
**List.prod_take_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_take_succ (L : List M) (i : Nat) (p : i < L.length) : (L.take (i + 1)
).prod = (L.take i).prod * L[i]
参数：L : List M；i : Nat；p : i < L.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `List.take_concat_get'`：take_concat_get' (l : List α) (i : Nat) (h : i < 
l.length) : l.take i ++ [l[i]] = l.take (i + 1)
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_take_succ (L : List M) (i : ℕ) (p : i < L.length) :
    (L.take (i + 1)).prod = (L.take i).prod * L[i] := by
  rw [← take_concat_get' _ _ p, prod_append]
  simp

/-- A list with product not one must have positive length. -/
@[to_additive /-- A list with sum not zero must have positive length. -/]
/-
**List.length_pos_of_prod_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_pos_of_prod_ne_one (L : List M) (h : L.prod != 1) : 0 < L.length
参数：L : List M；h : L.prod != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
A list with product not one must have positive length.
-/
theorem length_pos_of_prod_ne_one (L : List M) (h : L.prod ≠ 1) : 0 < L.length := by
  cases L
  · simp at h
  · simp

/-- A list with product greater than one must have positive length. -/
@[to_additive length_pos_of_sum_pos /-- A list with positive sum must have positive length. -/]
/-
**List.length_pos_of_one_lt_prod** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_pos_of_one_lt_prod [Preorder M] (L : List M) (h : 1 < L.prod) : 0 <
 L.length
参数：L : List M；h : 1 < L.prod。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_pos_of_prod_ne_one`：length_pos_of_prod_ne_one (L : List M) (
h : L.prod != 1) : 0 < L.length
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
A list with product greater than one must have positive length.
-/
theorem length_pos_of_one_lt_prod [Preorder M] (L : List M) (h : 1 < L.prod) : 0 < L.length :=
  length_pos_of_prod_ne_one L h.ne'

/-- A list with product less than one must have positive length. -/
@[to_additive /-- A list with negative sum must have positive length. -/]
/-
**List.length_pos_of_prod_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_pos_of_prod_lt_one [Preorder M] (L : List M) (h : L.prod < 1) : 0 <
 L.length
参数：L : List M；h : L.prod < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_pos_of_prod_ne_one`：length_pos_of_prod_ne_one (L : List M) (
h : L.prod != 1) : 0 < L.length
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b

--- 原说明 ---
A list with product less than one must have positive length.
-/
theorem length_pos_of_prod_lt_one [Preorder M] (L : List M) (h : L.prod < 1) : 0 < L.length :=
  length_pos_of_prod_ne_one L h.ne

@[to_additive]
/-
**List.prod_set** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {M : Type u_4} [inst : Monoid M] (L : List M) (n : ℕ) (a : M),   (L.set 
n a).prod = ((List.take n L).prod * if n < L.length then a else 1) * (List.drop 
(n + 1) L).prod
参数：L : List M；n : ℕ；a : M；L.set n a；(List.take n L).prod * if n < L.length then 
a else 1；List.drop (n + 1) L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_set :
    ∀ (L : List M) (n : ℕ) (a : M),
      (L.set n a).prod =
        ((L.take n).prod * if n < L.length then a else 1) * (L.drop (n + 1)).prod
  | x :: xs, 0, a => by simp [set]
  | x :: xs, i + 1, a => by simp [set, prod_set xs i a, mul_assoc]
  | [], _, _ => by simp [set]

/-- We'd like to state this as `L.headI * L.tail.prod = L.prod`, but because `L.headI` relies on an
inhabited instance to return a garbage value on the empty list, this is not possible.
Instead, we write the statement in terms of `L[0]?.getD 1`.
-/
@[to_additive /-- We'd like to state this as `L.headI + L.tail.sum = L.sum`, but because `L.headI`
  relies on an inhabited instance to return a garbage value on the empty list, this is not possible.
  Instead, we write the statement in terms of `L[0]?.getD 0`. -/]
/-
**List.getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem?_zero_mul_tail_prod (l : List M) : l[0]?.getD 1 * l.tail.prod = l.
prod
参数：l : List M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getElem?_zero_mul_tail_prod (l : List M) : l[0]?.getD 1 * l.tail.prod = l.prod := by
  cases l <;> simp

/-- Same as `get?_zero_mul_tail_prod`, but avoiding the `List.headI` garbage complication by
  requiring the list to be nonempty. -/
@[to_additive /-- Same as `get?_zero_add_tail_sum`, but avoiding the `List.headI` garbage
  complication by requiring the list to be nonempty. -/]
/-
**List.headI_mul_tail_prod_of_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：headI_mul_tail_prod_of_ne_nil [Inhabited M] (l : List M) (h : l != []) : l
.headI * l.tail.prod = l.prod
参数：l : List M；h : l != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem headI_mul_tail_prod_of_ne_nil [Inhabited M] (l : List M) (h : l ≠ []) :
    l.headI * l.tail.prod = l.prod := by cases l <;> [contradiction; simp]

@[to_additive]
/-
**List._root_.Commute.list_prod_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Commute.list_prod_right (l : List M) (y : M) (h : ∀ x ∈ l, Commute y x) :
    Commute y l.prod := by
  induction l with
  | nil => simp
  | cons z l IH =>
    rw [List.forall_mem_cons] at h
    rw [List.prod_cons]
    exact Commute.mul_right h.1 (IH h.2)

@[to_additive]
/-
**List._root_.Commute.list_prod_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Commute.list_prod_left (l : List M) (y : M) (h : ∀ x ∈ l, Commute x y) :
    Commute l.prod y :=
  ((Commute.list_prod_right _ _) fun _ hx => (h _ hx).symm).symm
/-
**List.prod_range_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {M : Type u_4} [inst : Monoid M] (f : ℕ → M) (n : ℕ),   (List.map f (Lis
t.range n.succ)).prod = (List.map f (List.range n)).prod * f n
参数：f : ℕ → M；n : ℕ；List.map f (List.range n.succ)；List.map f (List.range n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.range_succ`：∀ {n : ℕ}, List.range n.succ = List.range n ++ [n]
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_singleton`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : α},
 List.map f [a] = [f a]
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `List.prod_nil`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α], [].prod =
 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
@[to_additive] lemma prod_range_succ (f : ℕ → M) (n : ℕ) :
    ((range n.succ).map f).prod = ((range n).map f).prod * f n := by
  rw [range_succ, map_append, map_singleton, prod_append, prod_cons, prod_nil, mul_one]

/-- A variant of `prod_range_succ` which pulls off the first term in the product rather than the
last. -/
@[to_additive /-- A variant of `sum_range_succ` which pulls off the first term in the sum rather
than the last. -/]
/-
**List.prod_range_succ'** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_range_succ' (f : Nat -> M) (n : Nat) : ((range n.succ).map f).prod = 
f 0 * ((range n).map fun i => f i.succ).prod
参数：f : Nat -> M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.range_succ_eq_map`：∀ {n : ℕ}, List.range (n + 1) = 0 :: List.map Na
t.succ (List.range n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_range_succ' (f : ℕ → M) (n : ℕ) :
    ((range n.succ).map f).prod = f 0 * ((range n).map fun i ↦ f i.succ).prod := by
  rw [range_succ_eq_map]
  simp [Function.comp_def]
/-
**List.prod_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {M : Type u_4} [inst : Monoid M] {l : List M}, (∀ x ∈ l, x = 1) → l.prod
 = 1
参数：∀ x ∈ l, x = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
@[to_additive] lemma prod_eq_one (hl : ∀ x ∈ l, x = 1) : l.prod = 1 := by
  induction l with
  | nil => rfl
  | cons i l hil =>
    rw [List.prod_cons, hil fun x hx ↦ hl _ (mem_cons_of_mem i hx),
      hl _ mem_cons_self, one_mul]
/-
**List.exists_mem_ne_one_of_prod_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {M : Type u_4} [inst : Monoid M] {l : List M}, l.prod ≠ 1 → ∃ x ∈ l, x ≠
 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `List.prod_eq_one`：∀ {M : Type u_4} [inst : Monoid M] {l : List M}, (∀ x 
∈ l, x = 1) → l.prod = 1
-/
@[to_additive] lemma exists_mem_ne_one_of_prod_ne_one (h : l.prod ≠ 1) :
    ∃ x ∈ l, x ≠ (1 : M) := by simpa only [not_forall, exists_prop] using mt prod_eq_one h

@[to_additive]
/-
**List.prod_erase_of_comm** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_erase_of_comm [DecidableEq M] (ha : a in l) (comm : forall x in l, fo
rall y in l, x * y = y * x) : a * (l.erase a).prod = l.prod
参数：ha : a in l；comm : forall x in l, forall y in l, x * y = y * x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.eq_or_ne_mem_of_mem`：∀ {α : Type u_1} {a b : α} {l : List α}, a ∈ b
 :: l → a = b ∨ a ≠ b ∧ a ∈ l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.erase_cons_head`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (a :
 α) (l : List α), (a :: l).erase a = l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.erase.eq_2`：∀ {α : Type u_1} [inst : BEq α] (x a : α) (as : List α)
,   (a :: as).erase x =     match a == x with     | true => as     | false => a 
:: as…
· 使用定理 `beq_false_of_ne`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a b : α}
, a ≠ b → (a == b) = false
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
-/
lemma prod_erase_of_comm [DecidableEq M] (ha : a ∈ l) (comm : ∀ x ∈ l, ∀ y ∈ l, x * y = y * x) :
    a * (l.erase a).prod = l.prod := by
  induction l with
  | nil => simp only [not_mem_nil] at ha
  | cons b l ih =>
    obtain rfl | ⟨ne, h⟩ := List.eq_or_ne_mem_of_mem ha
    · simp only [erase_cons_head, prod_cons]
    rw [List.erase, beq_false_of_ne ne.symm, List.prod_cons, List.prod_cons, ← mul_assoc,
      comm a ha b mem_cons_self, mul_assoc,
      ih h fun x hx y hy ↦ comm _ (List.mem_cons_of_mem b hx) _ (List.mem_cons_of_mem b hy)]

@[to_additive]
/-
**List.prod_map_eq_pow_single** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_map_eq_pow_single [DecidableEq α] {l : List α} (a : α) (f : α -> M) (
hf : forall a', a' != a -> a' in l -> f a' = 1) : (l.map f).prod = f a ^ l.count
 a
参数：a : α；f : α -> M；hf : forall a', a' != a -> a' in l -> f a' = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.prod_nil`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α], [].prod =
 1
· 使用定理 `List.count_nil`：∀ {α : Type u_1} [inst : BEq α] {a : α}, List.count a []
 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `List.count_cons`：∀ {α : Type u_1} [inst : BEq α] {a b : α} {l : List α},
   List.count a (b :: l) = List.count a l + if (b == a) = true then 1 else 0
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma prod_map_eq_pow_single [DecidableEq α] {l : List α} (a : α) (f : α → M)
    (hf : ∀ a', a' ≠ a → a' ∈ l → f a' = 1) : (l.map f).prod = f a ^ l.count a := by
  induction l generalizing a with
  | nil => rw [map_nil, prod_nil, count_nil, _root_.pow_zero]
  | cons a' as h =>
    specialize h a fun a' ha' hfa' => hf a' ha' (mem_cons_of_mem _ hfa')
    rw [List.map_cons, List.prod_cons, count_cons, h]
    simp only [beq_iff_eq]
    split_ifs with ha'
    · rw [ha', _root_.pow_succ']
    · rw [hf a' ha' mem_cons_self, one_mul, add_zero]

@[to_additive]
/-
**List.prod_eq_pow_single** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_eq_pow_single [DecidableEq M] (a : M) (h : forall a', a' != a -> a' i
n l -> a' = 1) : l.prod = a ^ l.count a
参数：a : M；h : forall a', a' != a -> a' in l -> a' = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_id`：∀ {α : Type u_1} (l : List α), List.map id l = l
· 使用引理 `List.prod_map_eq_pow_single`：prod_map_eq_pow_single [DecidableEq α] {l :
 List α} (a : α) (f : α -> M) (hf : forall a', a' != a -> a' in l -> f a' = 1) :
 (l.map f).prod =…
-/
lemma prod_eq_pow_single [DecidableEq M] (a : M) (h : ∀ a', a' ≠ a → a' ∈ l → a' = 1) :
    l.prod = a ^ l.count a :=
  _root_.trans (by rw [map_id]) (prod_map_eq_pow_single a id h)

@[to_additive (attr := simp)]
/-
**List.prod_insertIdx** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_insertIdx {i} (hlen : i <= l.length) (hcomm : forall a' in l.take i, 
Commute a a') : (l.insertIdx i a).prod = a * l.prod
参数：hlen : i <= l.length；hcomm : forall a' in l.take i, Commute a a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.exists_cons_of_length_pos`：∀ {α : Type u_1} {l : List α}, 0 < l.len
gth → ∃ h t, l = h :: t
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `List.mem_of_mem_tail`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l.tail 
→ a ∈ l
· 使用定理 `Commute.left_comm`：∀ {S : Type u_3} [inst : Semigroup S] {a b : S}, Comm
ute a b → ∀ (c : S), a * (b * c) = b * (a * c)
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `List.mem_of_mem_head?`：∀ {α : Type u_1} {l : List α} {a : α}, a ∈ l.head
? → a ∈ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem prod_insertIdx {i} (hlen : i ≤ l.length) (hcomm : ∀ a' ∈ l.take i, Commute a a') :
    (l.insertIdx i a).prod = a * l.prod := by
  induction i generalizing l
  case zero => rfl
  case succ i ih =>
    obtain ⟨hd, tl, rfl⟩ := exists_cons_of_length_pos (Nat.zero_lt_of_lt hlen)
    simp only [insertIdx_succ_cons, prod_cons,
      ih (Nat.le_of_lt_succ hlen) (fun a' a'_mem => hcomm a' (mem_of_mem_tail a'_mem))]
    exact Commute.left_comm (hcomm hd (mem_of_mem_head? rfl)).symm tl.prod

@[to_additive (attr := simp)]
/-
**List.mul_prod_eraseIdx** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mul_prod_eraseIdx {i} (hlen : i < l.length) (hcomm : forall a' in l.take i
, Commute l[i] a') : l[i] * (l.eraseIdx i).prod = l.prod
参数：hlen : i < l.length；hcomm : forall a' in l.take i, Commute l[i] a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.prod_insertIdx`：prod_insertIdx {i} (hlen : i <= l.length) (hcomm : 
forall a' in l.take i, Commute a a') : (l.insertIdx i a).prod = a * l.prod
· 使用定理 `List.take_eraseIdx_eq_take_of_le`：take_eraseIdx_eq_take_of_le (l : List 
α) i j (h : i <= j) : (l.eraseIdx j).take i = l.take i
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `List.insertIdx_eraseIdx_getElem`：insertIdx_eraseIdx_getElem {l : List α}
 {n : Nat} (hn : n < length l) : (l.eraseIdx n).insertIdx n l[n] = l
-/
theorem mul_prod_eraseIdx {i} (hlen : i < l.length) (hcomm : ∀ a' ∈ l.take i, Commute l[i] a') :
    l[i] * (l.eraseIdx i).prod = l.prod := by
  rw [← prod_insertIdx (by grind : i ≤ (l.eraseIdx i).length) (fun a' a'_mem =>
      hcomm a' (by rwa [take_eraseIdx_eq_take_of_le l i i (Nat.le_refl i)] at a'_mem)),
    insertIdx_eraseIdx_getElem hlen]

@[to_additive (attr := simp)]
/-
**List.prod_filter_bne_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_filter_bne_one [BEq M] [LawfulBEq M] (l : List M) : (l.filter (· != 1
)).prod = l.prod
参数：l : List M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_filter_bne_one [BEq M] [LawfulBEq M] (l : List M) :
    (l.filter (· != 1)).prod = l.prod := by
  classical induction l <;> grind

end Monoid

section CommMonoid
variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

@[to_additive (attr := simp)]
/-
**List.CommMonoid.prod_insertIdx** 是 Mathlib 中的一个定理，位于命名空间 `List.CommMonoid`。
形式化陈述：∀ {M : Type u_4} [inst : CommMonoid M] {a : M} {l : List M} {i : ℕ}, i ≤ l
.length → (l.insertIdx i a).prod = a * l.prod
参数：l.insertIdx i a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.prod_insertIdx`：prod_insertIdx {i} (hlen : i <= l.length) (hcomm : 
forall a' in l.take i, Commute a a') : (l.insertIdx i a).prod = a * l.prod
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem CommMonoid.prod_insertIdx {i} (h : i ≤ l.length) : (l.insertIdx i a).prod = a * l.prod :=
  List.prod_insertIdx h (fun a' _ ↦ Commute.all a a')

@[to_additive (attr := simp)]
/-
**List.CommMonoid.mul_prod_eraseIdx** 是 Mathlib 中的一个定理，位于命名空间 `List.CommMonoid`。
形式化陈述：∀ {M : Type u_4} [inst : CommMonoid M] {l : List M} {i : ℕ} (h : i < l.len
gth), l[i] * (l.eraseIdx i).prod = l.prod
参数：h : i < l.length；l.eraseIdx i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mul_prod_eraseIdx`：mul_prod_eraseIdx {i} (hlen : i < l.length) (hco
mm : forall a' in l.take i, Commute l[i] a') : l[i] * (l.eraseIdx i).prod = l.pr
od
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem CommMonoid.mul_prod_eraseIdx {i} (h : i < l.length) : l[i] * (l.eraseIdx i).prod = l.prod :=
  List.mul_prod_eraseIdx h (fun a' _ ↦ Commute.all l[i] a')

@[to_additive (attr := simp)]
/-
**List.prod_erase** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_erase [DecidableEq M] (ha : a in l) : a * (l.erase a).prod = l.prod
参数：ha : a in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.prod_erase_of_comm`：prod_erase_of_comm [DecidableEq M] (ha : a in l
) (comm : forall x in l, forall y in l, x * y = y * x) : a * (l.erase a).prod = 
l.prod
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma prod_erase [DecidableEq M] (ha : a ∈ l) : a * (l.erase a).prod = l.prod :=
  prod_erase_of_comm ha fun x _ y _ ↦ mul_comm x y

@[to_additive (attr := simp)]
/-
**List.prod_map_erase** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_map_erase [DecidableEq α] (f : α -> M) {a} : forall {l : List α}, a i
n l -> f a * ((l.erase a).map f).prod = (l.map f).prod | b :: l, h => by obtain 
rfl | ⟨ne, h⟩
参数：f : α -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prod_map_erase [DecidableEq α] (f : α → M) {a} :
    ∀ {l : List α}, a ∈ l → f a * ((l.erase a).map f).prod = (l.map f).prod
  | b :: l, h => by
    obtain rfl | ⟨ne, h⟩ := List.eq_or_ne_mem_of_mem h
    · simp only [map, erase_cons_head, prod_cons]
    · simp only [map, erase_cons_tail (not_beq_of_ne ne.symm), prod_cons, prod_map_erase _ h,
        mul_left_comm (f a) (f b)]
/-
**List.Perm.prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {M : Type u_4} [inst : CommMonoid M] {l₁ l₂ : List M}, l₁.Perm l₂ → l₁.p
rod = l₂.prod
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.foldr_op_eq`：∀ {α : Type u_1} {op : α → α → α} [IA : Std.Assoc
iative op] [IC : Std.Commutative op] {l₁ l₂ : List α} {a : α},   l₁.Perm l₂ → Li
st.foldr op…
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
-/
@[to_additive] lemma Perm.prod_eq (h : Perm l₁ l₂) : prod l₁ = prod l₂ := h.foldr_op_eq

attribute [to_additive existing] prod_reverse

@[to_additive]
/-
**List.prod_mul_prod_eq_prod_zipWith_mul_prod_drop** 是 Mathlib 中的一个定理，位于命名空间 `Li
st`。
形式化陈述：∀ {M : Type u_4} [inst : CommMonoid M] (l l' : List M),   l.prod * l'.prod
 =     (List.zipWith (fun x1 x2 => x1 * x2) l l').prod * (List.drop l'.length l)
.prod * (List.drop l.length l').prod
参数：l l' : List M；List.zipWith (fun x1 x2 => x1 * x2) l l'；List.drop l'.length l；
List.drop l.length l'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prod_mul_prod_eq_prod_zipWith_mul_prod_drop :
    ∀ l l' : List M,
      l.prod * l'.prod =
        (zipWith (· * ·) l l').prod * (l.drop l'.length).prod * (l'.drop l.length).prod
  | [], ys => by simp
  | xs, [] => by simp
  | x :: xs, y :: ys => by
    simp only [zipWith_cons_cons, prod_cons]
    conv =>
      lhs; rw [mul_assoc]; right; rw [mul_comm, mul_assoc]; right
      rw [mul_comm, prod_mul_prod_eq_prod_zipWith_mul_prod_drop xs ys]
    simp [mul_assoc]

@[to_additive]
/-
**List.prod_mul_prod_eq_prod_zipWith_of_length_eq** 是 Mathlib 中的一个引理，位于命名空间 `Lis
t`。
形式化陈述：prod_mul_prod_eq_prod_zipWith_of_length_eq (l l' : List M) (h : l.length =
 l'.length) : l.prod * l'.prod = (zipWith (· * ·) l l').prod
参数：l l' : List M；h : l.length = l'.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.prod_mul_prod_eq_prod_zipWith_mul_prod_drop`：∀ {M : Type u_4} [inst
 : CommMonoid M] (l l' : List M),   l.prod * l'.prod =     (List.zipWith (fun x1
 x2 => x1 * x2) l l').prod * (List.dro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.drop_length`：∀ {α : Type u_1} {l : List α}, List.drop l.length l = 
[]
· 使用定理 `List.prod_nil`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α], [].prod =
 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma prod_mul_prod_eq_prod_zipWith_of_length_eq (l l' : List M) (h : l.length = l'.length) :
    l.prod * l'.prod = (zipWith (· * ·) l l').prod := by
  apply (prod_mul_prod_eq_prod_zipWith_mul_prod_drop l l').trans
  rw [← h, drop_length, h, drop_length, prod_nil, mul_one, mul_one]

@[to_additive]
/-
**List.prod_map_ite** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_map_ite (p : α -> Prop) [DecidablePred p] (f g : α -> M) (l : List α)
 : (l.map fun a => if p a then f a else g a).prod = ((l.filter p).map f).prod * 
((l.filter fun a => ¬p a).map g).prod
参数：p : α -> Prop；f g : α -> M；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.filter_cons`：∀ {α : Type u_1} {x : α} {xs : List α} {p : α → Bool},
   List.filter p (x :: xs) = if p x = true then x :: List.filter p xs else List.
filter…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
-/
lemma prod_map_ite (p : α → Prop) [DecidablePred p] (f g : α → M) (l : List α) :
    (l.map fun a => if p a then f a else g a).prod =
      ((l.filter p).map f).prod * ((l.filter fun a ↦ ¬p a).map g).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, filter_cons, prod_cons] at ih ⊢
    rw [ih]
    clear ih
    by_cases hx : p x
    · simp only [hx, ↓reduceIte, decide_not, decide_true, map_cons, prod_cons, not_true_eq_false,
        decide_false, Bool.false_eq_true, mul_assoc]
    · simp only [hx, ↓reduceIte, decide_not, decide_false, Bool.false_eq_true, not_false_eq_true,
      decide_true, map_cons, prod_cons, mul_left_comm]

@[to_additive]
/-
**List.prod_map_filter_mul_prod_map_filter_not** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_map_filter_mul_prod_map_filter_not (p : α -> Prop) [DecidablePred p] 
(f : α -> M) (l : List α) : ((l.filter p).map f).prod * ((l.filter fun x => ¬p x
).map f).prod = (l.map f).prod
参数：p : α -> Prop；f : α -> M；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `List.prod_map_ite`：prod_map_ite (p : α -> Prop) [DecidablePred p] (f g :
 α -> M) (l : List α) : (l.map fun a => if p a then f a else g a).prod = ((l.fil
ter p).…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_map_filter_mul_prod_map_filter_not (p : α → Prop) [DecidablePred p] (f : α → M)
    (l : List α) :
    ((l.filter p).map f).prod * ((l.filter fun x => ¬p x).map f).prod = (l.map f).prod := by
  rw [← prod_map_ite]
  simp only [ite_self]

end CommMonoid

@[to_additive]
/-
**List.eq_of_prod_take_eq** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：eq_of_prod_take_eq [LeftCancelMonoid M] {L L' : List M} (h : L.length = L'
.length) (h' : forall i <= L.length, (L.take i).prod = (L'.take i).prod) : L = L
'
参数：h : L.length = L'.length；h' : forall i <= L.length, (L.take i).prod = (L'.tak
e i).prod。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_get`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁.length = l₂.length
 →     (∀ (n : ℕ) (h₁ : n < l₁.length) (h₂ : n < l₂.length), l₁.get ⟨n, h₁⟩ = l₂
.g…
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `List.prod_take_succ`：prod_take_succ (L : List M) (i : Nat) (p : i < L.le
ngth) : (L.take (i + 1)).prod = (L.take i).prod * L[i]
-/
lemma eq_of_prod_take_eq [LeftCancelMonoid M] {L L' : List M} (h : L.length = L'.length)
    (h' : ∀ i ≤ L.length, (L.take i).prod = (L'.take i).prod) : L = L' := by
  refine ext_get h fun i h₁ h₂ => ?_
  have : (L.take (i + 1)).prod = (L'.take (i + 1)).prod := h' _ (Nat.succ_le_of_lt h₁)
  rw [prod_take_succ L i h₁, prod_take_succ L' i h₂, h' i (Nat.le_of_lt h₁)] at this
  convert! mul_left_cancel this

section Group

variable [Group G]

/-- This is the `List.prod` version of `mul_inv_rev` -/
@[to_additive /-- This is the `List.sum` version of `add_neg_rev` -/]
/-
**List.prod_inv_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {G : Type u_7} [inst : Group G] (L : List G), L.prod⁻¹ = (List.map (fun 
x => x⁻¹) L).reverse.prod
参数：L : List G；List.map (fun x => x⁻¹) L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the `List.prod` version of `mul_inv_rev`
-/
theorem prod_inv_reverse : ∀ L : List G, L.prod⁻¹ = (L.map fun x => x⁻¹).reverse.prod
  | [] => by simp
  | x :: xs => by simp [prod_append, prod_inv_reverse xs]

/-- A non-commutative variant of `List.prod_reverse` -/
@[to_additive /-- A non-commutative variant of `List.sum_reverse` -/]
/-
**List.prod_reverse_noncomm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_reverse_noncomm : forall L : List G, L.reverse.prod = (L.map fun x =>
 x⁻¹).prod⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_inv_reverse`：∀ {G : Type u_7} [inst : Group G] (L : List G), L
.prod⁻¹ = (List.map (fun x => x⁻¹) L).reverse.prod
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Involutive.comp_self`：comp_self : f ∘ f = id
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun`：∀ {α : Type u_1}, List.map id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A non-commutative variant of `List.prod_reverse`
-/
theorem prod_reverse_noncomm : ∀ L : List G, L.reverse.prod = (L.map fun x => x⁻¹).prod⁻¹ := by
  simp [prod_inv_reverse]

/-- Counterpart to `List.prod_take_succ` when we have an inverse operation -/
@[to_additive (attr := simp)
  /-- Counterpart to `List.sum_take_succ` when we have a negation operation -/]
/-
**List.prod_drop_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {G : Type u_7} [inst : Group G] (L : List G) (i : ℕ) (p : i < L.length),
   (List.drop (i + 1) L).prod = L[i]⁻¹ * (List.drop i L).prod
参数：L : List G；i : ℕ；p : i < L.length；List.drop (i + 1) L；List.drop i L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_drop_succ :
    ∀ (L : List G) (i : ℕ) (p : i < L.length), (L.drop (i + 1)).prod = L[i]⁻¹ * (L.drop i).prod
  | [], _, p => False.elim (Nat.not_lt_zero _ p)
  | _ :: _, 0, _ => by simp
  | _ :: xs, i + 1, p => prod_drop_succ xs i (Nat.lt_of_succ_lt_succ p)

/-- Cancellation of a telescoping product. -/
@[to_additive /-- Cancellation of a telescoping sum. -/]
/-
**List.prod_range_div'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_range_div' (n : Nat) (f : Nat -> G) : ((range n).map fun k => f k / f
 (k + 1)).prod = f 0 / f n
参数：n : Nat；f : Nat -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.range_succ`：∀ {n : ℕ}, List.range n.succ = List.range n ++ [n]
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `div_mul_div_cancel`：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a
 / c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Cancellation of a telescoping product.
-/
theorem prod_range_div' (n : ℕ) (f : ℕ → G) :
    ((range n).map fun k ↦ f k / f (k + 1)).prod = f 0 / f n := by
  induction n with
  | zero => exact (div_self' (f 0)).symm
  | succ n h => simp [range_succ, prod_append, map_append, h]

end Group

section CommGroup

variable [CommGroup G]

/-- This is the `List.prod` version of `mul_inv` -/
@[to_additive /-- This is the `List.sum` version of `add_neg` -/]
/-
**List.prod_inv** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {K : Type u_8} [inst : DivisionCommMonoid K] (L : List K), L.prod⁻¹ = (L
ist.map (fun x => x⁻¹) L).prod
参数：L : List K；List.map (fun x => x⁻¹) L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the `List.prod` version of `mul_inv`
-/
theorem prod_inv {K : Type*} [DivisionCommMonoid K] :
    ∀ L : List K, L.prod⁻¹ = (L.map fun x => x⁻¹).prod
  | [] => by simp
  | x :: xs => by simp [mul_comm, prod_inv xs]

/-- Cancellation of a telescoping product. -/
@[to_additive /-- Cancellation of a telescoping sum. -/]
/-
**List.prod_range_div** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_range_div (n : Nat) (f : Nat -> G) : ((range n).map fun k => f (k + 1
) / f k).prod = f n / f 0
参数：n : Nat；f : Nat -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用定理 `List.prod_inv`：∀ {K : Type u_8} [inst : DivisionCommMonoid K] (L : List 
K), L.prod⁻¹ = (List.map (fun x => x⁻¹) L).prod
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.prod_range_div'`：prod_range_div' (n : Nat) (f : Nat -> G) : ((range
 n).map fun k => f k / f (k + 1)).prod = f 0 / f n

--- 原说明 ---
Cancellation of a telescoping product.
-/
theorem prod_range_div (n : ℕ) (f : ℕ → G) :
    ((range n).map fun k ↦ f (k + 1) / f k).prod = f n / f 0 := by
  have h : ((·⁻¹) ∘ fun k ↦ f (k + 1) / f k) = fun k ↦ f k / f (k + 1) := by ext; apply inv_div
  rw [← inv_inj, prod_inv, map_map, inv_div, h, prod_range_div']

/-- Alternative version of `List.prod_set` when the list is over a group -/
@[to_additive /-- Alternative version of `List.sum_set` when the list is over a group -/]
/-
**List.prod_set'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_set' (L : List G) (n : Nat) (a : G) : (L.set n a).prod = L.prod * if 
hn : n < L.length then L[n]⁻¹ * a else 1
参数：L : List G；n : Nat；a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.prod_set`：∀ {M : Type u_4} [inst : Monoid M] (L : List M) (n : ℕ) (
a : M),   (L.set n a).prod = ((List.take n L).prod * if n < L.length then a else
 1)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `List.prod_drop_succ`：∀ {G : Type u_7} [inst : Group G] (L : List G) (i :
 ℕ) (p : i < L.length),   (List.drop (i + 1) L).prod = L[i]⁻¹ * (List.drop i L).
prod
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.prod_take_mul_prod_drop`：prod_take_mul_prod_drop (L : List M) (i : 
Nat) : (L.take i).prod * (L.drop i).prod = L.prod
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.take_of_length_le`：∀ {α : Type u_1} {i : ℕ} {l : List α}, l.length 
≤ i → List.take i l = l
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `List.drop_eq_nil_of_le`：∀ {α : Type u} {as : List α} {i : ℕ}, as.length 
≤ i → List.drop i as = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Alternative version of `List.prod_set` when the list is over a group
-/
theorem prod_set' (L : List G) (n : ℕ) (a : G) :
    (L.set n a).prod = L.prod * if hn : n < L.length then L[n]⁻¹ * a else 1 := by
  refine (prod_set L n a).trans ?_
  split_ifs with hn
  · rw [mul_comm _ a, mul_assoc a, prod_drop_succ L n hn, mul_comm _ (drop n L).prod, ←
      mul_assoc (take n L).prod, prod_take_mul_prod_drop, mul_comm a, mul_assoc]
  · simp (disch := grind) [take_of_length_le, drop_eq_nil_of_le]

@[to_additive]
/-
**List.prod_map_ite_eq** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_map_ite_eq {A : Type*} [DecidableEq A] (l : List A) (f g : A -> G) (a
 : A) : (l.map fun x => if x = a then f x else g x).prod = (f a / g a) ^ (l.coun
t a) * (l.map g).prod
参数：l : List A；f g : A -> G；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.count_cons`：∀ {α : Type u_1} [inst : BEq α] {a b : α} {l : List α},
   List.count a (b :: l) = List.count a l + if (b == a) = true then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `beq_self_eq_true`：∀ {α : Type u_1} [inst : BEq α] [ReflBEq α] (a : α), (
a == a) = true
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `instEquivBEqOfLawfulBEq`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α], 
EquivBEq α
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma prod_map_ite_eq {A : Type*} [DecidableEq A] (l : List A) (f g : A → G) (a : A) :
    (l.map fun x => if x = a then f x else g x).prod
      = (f a / g a) ^ (l.count a) * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, prod_cons, count_cons] at ih ⊢
    rw [ih]
    clear ih
    by_cases hx : x = a
    · simp only [hx, ite_true, pow_add, pow_one, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
      mul_inv_cancel_left, beq_self_eq_true]
    · simp only [hx, ite_false, add_zero, mul_assoc, mul_comm (g x) _, beq_iff_eq]

end CommGroup

/-
**List.sum_const_nat** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sum_const_nat (m n : Nat) : sum (replicate m n) = m * n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sum_replicate`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ) (a : M
), (List.replicate n a).sum = n • a
-/
theorem sum_const_nat (m n : ℕ) : sum (replicate m n) = m * n :=
  sum_replicate m n

/-!
Several lemmas about sum/head/tail for `List ℕ`.
These are hard to generalize well, as they rely on the fact that `default ℕ = 0`.
If desired, we could add a class stating that `default = 0`.
-/

/-- This relies on `default ℕ = 0`. -/
/-
**List.headI_add_tail_sum** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：headI_add_tail_sum (L : List Nat) : L.headI + L.tail.sum = L.sum
参数：L : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
This relies on `default ℕ = 0`.
-/
theorem headI_add_tail_sum (L : List ℕ) : L.headI + L.tail.sum = L.sum := by
  cases L <;> simp

/-- This relies on `default ℕ = 0`. -/
/-
**List.headI_le_sum** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：headI_le_sum (L : List Nat) : L.headI <= L.sum
参数：L : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le.intro`：∀ {n m k : ℕ}, n + k = m → n ≤ m
· 使用定理 `List.headI_add_tail_sum`：headI_add_tail_sum (L : List Nat) : L.headI + L
.tail.sum = L.sum

--- 原说明 ---
This relies on `default ℕ = 0`.
-/
theorem headI_le_sum (L : List ℕ) : L.headI ≤ L.sum :=
  Nat.le.intro (headI_add_tail_sum L)

/-- This relies on `default ℕ = 0`. -/
/-
**List.tail_sum** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：tail_sum (L : List Nat) : L.tail.sum = L.sum - L.headI
参数：L : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.headI_add_tail_sum`：headI_add_tail_sum (L : List Nat) : L.headI + L
.tail.sum = L.sum
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n

--- 原说明 ---
This relies on `default ℕ = 0`.
-/
theorem tail_sum (L : List ℕ) : L.tail.sum = L.sum - L.headI := by
  rw [← headI_add_tail_sum L, add_comm, Nat.add_sub_cancel_right]

section Alternating

section

variable [One G] [Mul G] [Inv G]

@[to_additive (attr := simp)]
/-
**List.alternatingProd_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：alternatingProd_nil : alternatingProd ([] : List G) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem alternatingProd_nil : alternatingProd ([] : List G) = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**List.alternatingProd_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：alternatingProd_singleton (a : G) : alternatingProd [a] = a
参数：a : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem alternatingProd_singleton (a : G) : alternatingProd [a] = a :=
  rfl

@[to_additive]
/-
**List.alternatingProd_cons_cons'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：alternatingProd_cons_cons' (a b : G) (l : List G) : alternatingProd (a :: 
b :: l) = a * b⁻¹ * alternatingProd l
参数：a b : G；l : List G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem alternatingProd_cons_cons' (a b : G) (l : List G) :
    alternatingProd (a :: b :: l) = a * b⁻¹ * alternatingProd l :=
  rfl

end

@[to_additive]
/-
**List.alternatingProd_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：alternatingProd_cons_cons [DivInvMonoid G] (a b : G) (l : List G) : altern
atingProd (a :: b :: l) = a / b * alternatingProd l
参数：a b : G；l : List G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `List.alternatingProd_cons_cons'`：alternatingProd_cons_cons' (a b : G) (l
 : List G) : alternatingProd (a :: b :: l) = a * b⁻¹ * alternatingProd l
-/
theorem alternatingProd_cons_cons [DivInvMonoid G] (a b : G) (l : List G) :
    alternatingProd (a :: b :: l) = a / b * alternatingProd l := by
  rw [div_eq_mul_inv, alternatingProd_cons_cons']

variable [CommGroup G]

@[to_additive]
/-
**List.alternatingProd_cons'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {G : Type u_7} [inst : CommGroup G] (a : G) (l : List G), (a :: l).alter
natingProd = a * l.alternatingProd⁻¹
参数：a : G；l : List G；a :: l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem alternatingProd_cons' :
    ∀ (a : G) (l : List G), alternatingProd (a :: l) = a * (alternatingProd l)⁻¹
  | a, [] => by rw [alternatingProd_nil, inv_one, mul_one, alternatingProd_singleton]
  | a, b :: l => by
    rw [alternatingProd_cons_cons', alternatingProd_cons' b l, mul_inv, inv_inv, mul_assoc]

@[to_additive (attr := simp)]
/-
**List.alternatingProd_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：alternatingProd_cons (a : G) (l : List G) : alternatingProd (a :: l) = a /
 alternatingProd l
参数：a : G；l : List G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `List.alternatingProd_cons'`：∀ {G : Type u_7} [inst : CommGroup G] (a : G
) (l : List G), (a :: l).alternatingProd = a * l.alternatingProd⁻¹
-/
theorem alternatingProd_cons (a : G) (l : List G) :
    alternatingProd (a :: l) = a / alternatingProd l := by
  rw [div_eq_mul_inv, alternatingProd_cons']

end Alternating

/-
**List.sum_nat_mod** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：sum_nat_mod (l : List Nat) (n : Nat) : l.sum % n = (l.map (· % n)).sum % n
参数：l : List Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Nat.mod_add_mod`：∀ (m n k : ℕ), (m % n + k) % n = (m + k) % n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.add_mod_mod`：∀ (m n k : ℕ), (m + n % k) % k = (m + n) % k
-/
lemma sum_nat_mod (l : List ℕ) (n : ℕ) : l.sum % n = (l.map (· % n)).sum % n := by
  induction l with
  | nil => simp only [map_nil]
  | cons a l ih =>
    simpa only [map_cons, sum_cons, Nat.mod_add_mod, Nat.add_mod_mod] using congr((a + $ih) % n)
/-
**List.prod_nat_mod** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_nat_mod (l : List Nat) (n : Nat) : l.prod % n = (l.map (· % n)).prod 
% n
参数：l : List Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Nat.mod_mul_mod`：∀ (m n l : ℕ), m % l * n % l = m * n % l
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.mul_mod_mod`：∀ (m n l : ℕ), m * (n % l) % l = m * n % l
-/
lemma prod_nat_mod (l : List ℕ) (n : ℕ) : l.prod % n = (l.map (· % n)).prod % n := by
  induction l with
  | nil => simp only [map_nil]
  | cons a l ih =>
    simpa only [prod_cons, map_cons, Nat.mod_mul_mod, Nat.mul_mod_mod] using congr((a * $ih) % n)
/-
**List.sum_int_mod** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：sum_int_mod (l : List Int) (n : Int) : l.sum % n = (l.map (· % n)).sum % n
参数：l : List Int；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.add_emod`：∀ (a b n : ℤ), (a + b) % n = (a % n + b % n) % n
· 使用定理 `Int.emod_emod_of_dvd`：∀ (n : ℤ) {m k : ℤ}, m ∣ k → n % k % m = n % m
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
-/
lemma sum_int_mod (l : List ℤ) (n : ℤ) : l.sum % n = (l.map (· % n)).sum % n := by
  induction l <;> simp [Int.add_emod, *]
/-
**List.prod_int_mod** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_int_mod (l : List Int) (n : Int) : l.prod % n = (l.map (· % n)).prod 
% n
参数：l : List Int；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.mul_emod`：∀ (a b n : ℤ), a * b % n = a % n * (b % n) % n
· 使用定理 `Int.emod_emod_of_dvd`：∀ (n : ℤ) {m k : ℤ}, m ∣ k → n % k % m = n % m
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
-/
lemma prod_int_mod (l : List ℤ) (n : ℤ) : l.prod % n = (l.map (· % n)).prod % n := by
  induction l <;> simp [Int.mul_emod, *]

end List

section MonoidHom

variable [Monoid M] [Monoid N]

@[to_additive]
/-
**map_list_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) (
l : List M) : f l.prod = (l.map f).prod
参数：f : F；l : List M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.prod_hom`：prod_hom (l : List M) {F : Type*} [FunLike F M N] [Monoid
HomClass F M N] (f : F) : (l.map f).prod = f l.prod
-/
theorem map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) (l : List M) :
    f l.prod = (l.map f).prod :=
  (l.prod_hom f).symm

namespace MonoidHom

@[to_additive]
/-
**MonoidHom.map_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [inst_1 : Monoid N] (f :
 M →* N) (l : List M),   f l.prod = (List.map (⇑f) l).prod
参数：f : M →* N；l : List M；List.map (⇑f) l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
-/
protected theorem map_list_prod (f : M →* N) (l : List M) : f l.prod = (l.map f).prod :=
  map_list_prod f l

end MonoidHom

end MonoidHom

namespace List

/-
**List.prod_zpow** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_zpow {β : Type*} [DivisionCommMonoid β] {r : Int} {l : List β} : l.pr
od ^ r = (map (fun x => x ^ r) l).prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `mul_zpow`：∀ {α : Type u_1} [inst : DivisionCommMonoid α] (a b : α) (n : 
ℤ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
-/
theorem prod_zpow {β : Type*} [DivisionCommMonoid β] {r : ℤ} {l : List β} :
    l.prod ^ r = (map (fun x ↦ x ^ r) l).prod :=
  let fr : β →* β := ⟨⟨fun b ↦ b ^ r, one_zpow r⟩, (mul_zpow · · r)⟩
  map_list_prod fr l

/-- In a flatten, taking the first elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the flatten of the first `i` sublists. -/
/-
**List.take_sum_flatten** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：take_sum_flatten (L : List (List α)) (i : Nat) : L.flatten.take ((L.map le
ngth).take i).sum = (L.take i).flatten
参数：L : List (List α)；i : Nat。
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
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.take_length_add_append`：∀ {α : Type u_1} {l₁ l₂ : List α} (i : ℕ), 
List.take (l₁.length + i) (l₁ ++ l₂) = l₁ ++ List.take i l₂

--- 原说明 ---
In a flatten, taking the first elements up to an index which is the sum of the l
engths of the
first `i` sublists, is the same as taking the flatten of the first `i` sublists.
-/
lemma take_sum_flatten (L : List (List α)) (i : ℕ) :
    L.flatten.take ((L.map length).take i).sum = (L.take i).flatten := by
  induction L generalizing i
  · simp
  · cases i <;> simp [take_length_add_append, *]

/-- In a flatten, dropping all the elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join after dropping the first `i` sublists. -/
/-
**List.drop_sum_flatten** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：drop_sum_flatten (L : List (List α)) (i : Nat) : L.flatten.drop ((L.map le
ngth).take i).sum = (L.drop i).flatten
参数：L : List (List α)；i : Nat。
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
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.drop_length_add_append`：∀ {α : Type u_1} {l₁ l₂ : List α} (i : ℕ), 
List.drop (l₁.length + i) (l₁ ++ l₂) = List.drop i l₂
· 使用定理 `List.drop_succ_cons`：∀ {α : Type u} {a : α} {l : List α} {i : ℕ}, List.d
rop (i + 1) (a :: l) = List.drop i l

--- 原说明 ---
In a flatten, dropping all the elements up to an index which is the sum of the l
engths of the
first `i` sublists, is the same as taking the join after dropping the first `i` 
sublists.
-/
lemma drop_sum_flatten (L : List (List α)) (i : ℕ) :
    L.flatten.drop ((L.map length).take i).sum = (L.drop i).flatten := by
  induction L generalizing i
  · simp
  · cases i <;> simp [*]

end List


namespace List

/-- If all elements in a list are bounded below by `1`, then the length of the list is bounded
by the sum of the elements. -/
/-
**List.length_le_sum_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_le_sum_of_one_le (L : List Nat) (h : forall i in L, 1 <= i) : L.len
gth <= L.sum
参数：L : List Nat；h : forall i in L, 1 <= i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sum_cons`：∀ {α : Type u} [inst : Add α] [inst_1 : Zero α] {a : α} {
l : List α}, (a :: l).sum = a + l.sum
· 使用定理 `List.length.eq_2`：∀ {α : Type u_1} (head : α) (tail : List α), (head :: 
tail).length = tail.length + 1
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.add_le_add`：∀ {a b c d : ℕ}, a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l

--- 原说明 ---
If all elements in a list are bounded below by `1`, then the length of the list 
is bounded
by the sum of the elements.
-/
theorem length_le_sum_of_one_le (L : List ℕ) (h : ∀ i ∈ L, 1 ≤ i) : L.length ≤ L.sum := by
  induction L with
  | nil => simp
  | cons j L IH =>
    rw [sum_cons, length, add_comm]
    exact Nat.add_le_add (h _ mem_cons_self) (IH fun i hi => h i (mem_cons.2 (Or.inr hi)))

end List

