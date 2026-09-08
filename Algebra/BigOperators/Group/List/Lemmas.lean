/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.Flatten
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Range
public import Mathlib.Data.List.Rotate
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Algebra.Group.Opposite

/-!
# Sums and products from lists

This file provides further results about `List.prod`, `List.sum`,
which calculate the product and sum of elements of a list
and `List.alternatingProd`, `List.alternatingSum`, their alternating counterparts.
-/

public section
assert_not_imported Mathlib.Algebra.Order.Group.Nat

variable {ι α β M N P G : Type*}

namespace List

section Monoid

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

@[to_additive]
/-
**List.prod_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {M : Type u_4} [inst : Monoid M] {L : List M}, (∀ m ∈ L, IsUnit m) → IsU
nit L.prod
参数：∀ m ∈ L, IsUnit m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_isUnit : ∀ {L : List M}, (∀ m ∈ L, IsUnit m) → IsUnit L.prod
  | [], _ => by simp
  | h :: t, u => by
    simp only [List.prod_cons]
    exact IsUnit.mul (u h mem_cons_self) (prod_isUnit fun m mt => u m (mem_cons_of_mem h mt))

@[to_additive]
/-
**List.prod_isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_isUnit_iff {M : Type*} [CommMonoid M] {L : List M} : IsUnit L.prod ↔ 
forall m in L, IsUnit m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_mem_nil`：∀ {α : Type u_1} {a : α}, a ∉ []
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `List.eq_or_mem_of_mem_cons`：∀ {α : Type u_1} {a b : α} {l : List α}, a ∈
 b :: l → a = b ∨ a ∈ l
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.mul_iff`：mul_iff [Monoid M] [IsDedekindFiniteMonoid M] {x y : M} 
: IsUnit (x * y) ↔ IsUnit x ∧ IsUnit y
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.prod_isUnit`：∀ {M : Type u_4} [inst : Monoid M] {L : List M}, (∀ m 
∈ L, IsUnit m) → IsUnit L.prod
-/
theorem prod_isUnit_iff {M : Type*} [CommMonoid M] {L : List M} :
    IsUnit L.prod ↔ ∀ m ∈ L, IsUnit m := by
  refine ⟨fun h => ?_, prod_isUnit⟩
  induction L with
  | nil => exact fun m' h' => False.elim (not_mem_nil h')
  | cons m L ih =>
    rw [prod_cons, IsUnit.mul_iff] at h
    exact fun m' h' ↦ Or.elim (eq_or_mem_of_mem_cons h') (fun H => H.substr h.1) fun H => ih h.2 _ H

/-- If elements of a list commute with each other, then their product does not
depend on the order of elements. -/
@[to_additive /-- If elements of a list additively commute with each other, then their sum does not
depend on the order of elements. -/]
/-
**List.Perm.prod_eq'** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {M : Type u_4} [inst : Monoid M] {l₁ l₂ : List M}, l₁.Perm l₂ → List.Pai
rwise Commute l₁ → l₁.prod = l₂.prod
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Perm.foldr_eq'`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → β} {l₁
 l₂ : List α},   l₁.Perm l₂ →     (∀ x ∈ l₁, ∀ y ∈ l₁, ∀ (z : β), f y (f x z) = 
f x (f y …
· 使用定理 `List.Pairwise.forall_of_forall`：∀ {α : Type u_1} {R : α → α → Prop} {l :
 List α} [Std.Symm R],   (∀ x ∈ l, R x x) → List.Pairwise R l → ∀ ⦃x : α⦄, x ∈ l
 → ∀ ⦃y : α⦄, y ∈ l …
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
lemma Perm.prod_eq' (h : l₁ ~ l₂) (hc : l₁.Pairwise Commute) : l₁.prod = l₂.prod := by
  have : Std.Symm fun x y ↦ ∀ z : M, y * (x * z) = x * (y * z) := { symm x y h z := h z |>.symm }
  refine h.foldr_eq' (Pairwise.forall_of_forall (fun _ _ _ ↦ rfl) <| hc.imp fun {a b} h z ↦ ?_) 1
  rw [← mul_assoc, ← mul_assoc, h]

end Monoid

section Group

variable [Group G]

/-
**List.prod_rotate_eq_one_of_prod_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_rotate_eq_one_of_prod_eq_one : forall {l : List G} (_ : l.prod = 1) (
n : Nat), (l.rotate n).prod = 1 | [], _, _ => by simp | a :: l, hl, n => by have
 : n % List.length (a :: l) <= List.length (a :: l)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_nil`：rotate_nil (n : Nat) : ([] : List α).rotate n = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.rotate_mod`：rotate_mod (l : List α) (n : Nat) : l.rotate (n % l.len
gth) = l.rotate n
· 使用定理 `List.rotate_eq_drop_append_take`：rotate_eq_drop_append_take {l : List α}
 {n : Nat} : n <= l.length -> l.rotate n = l.drop n ++ l.take n
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `mul_eq_one_iff_inv_eq`：mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma prod_rotate_eq_one_of_prod_eq_one :
    ∀ {l : List G} (_ : l.prod = 1) (n : ℕ), (l.rotate n).prod = 1
  | [], _, _ => by simp
  | a :: l, hl, n => by
    have : n % List.length (a :: l) ≤ List.length (a :: l) := le_of_lt (Nat.mod_lt _ (by simp))
    rw [← List.take_append_drop (n % List.length (a :: l)) (a :: l)] at hl
    rw [← rotate_mod, rotate_eq_drop_append_take this, List.prod_append, mul_eq_one_iff_inv_eq,
      ← one_mul (List.prod _)⁻¹, ← hl, List.prod_append, mul_assoc, mul_inv_cancel, mul_one]

end Group

variable [DecidableEq α]

/-- Summing the count of `x` over a list filtered by some `p` is just `countP` applied to `p` -/
/-
**List.sum_map_count_dedup_filter_eq_countP** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sum_map_count_dedup_filter_eq_countP (p : α -> Bool) (l : List α) : ((l.de
dup.filter p).map fun x => l.count x).sum = l.countP p
参数：p : α -> Bool；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.countP_cons`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : List α}, 
  List.countP p (a :: l) = List.countP p l + if p a = true then 1 else 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.count_cons`：∀ {α : Type u_1} [inst : BEq α] {a b : α} {l : List α},
   List.count a (b :: l) = List.count a l + if (b == a) = true then 1 else 0
· 使用定理 `List.sum_map_add`：∀ {ι : Type u_1} {M : Type u_8} [inst : AddCommMonoid 
M] {l : List ι} {f g : ι → M},   (List.map (fun i => f i + g i) l).sum = (List.m
ap f l…
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.dedup_cons_of_mem`：dedup_cons_of_mem {a : α} {l : List α} (h : a in
 l) : dedup (a :: l) = dedup l
· 使用定理 `List.dedup_cons_of_notMem`：dedup_cons_of_notMem {a : α} {l : List α} (h 
: a ∉ l) : dedup (a :: l) = a :: dedup l
· 使用定理 `List.filter.eq_2`：∀ {α : Type u} (p : α → Bool) (a : α) (as : List α),  
 List.filter p (a :: as) =     match p a with     | true => a :: List.filter p a
s     …
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.count_eq_zero`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a : α
} {l : List α}, List.count a l = 0 ↔ a ∉ l
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `List.sum_map_eq_nsmul_single`：∀ {α : Type u_2} {M : Type u_4} [inst : Ad
dMonoid M] [inst_1 : DecidableEq α] {l : List α} (a : α) (f : α → M),   (∀ (a' :
 α), a' ≠ a → a' ∈…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.count_filter`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {p : α 
→ Bool} {a : α} {l : List α},   p a = true → List.count a (List.filter p l) = Li
st.coun…
· 使用定理 `List.count_dedup`：count_dedup (l : List α) (a : α) : l.dedup.count a = i
f a in l then 1 else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Summing the count of `x` over a list filtered by some `p` is just `countP` appli
ed to `p`
-/
theorem sum_map_count_dedup_filter_eq_countP (p : α → Bool) (l : List α) :
    ((l.dedup.filter p).map fun x => l.count x).sum = l.countP p := by
  induction l with
  | nil => simp
  | cons a as h =>
    simp_rw [List.countP_cons, List.count_cons, List.sum_map_add]
    congr 1
    · refine _root_.trans ?_ h
      by_cases ha : a ∈ as
      · simp [dedup_cons_of_mem ha]
      · simp only [dedup_cons_of_notMem ha, List.filter]
        match p a with
        | true => simp only [List.map_cons, List.sum_cons, List.count_eq_zero.2 ha, zero_add]
        | false => simp only
    · simp only [beq_iff_eq]
      by_cases hp : p a
      · refine _root_.trans (sum_map_eq_nsmul_single a _ fun _ h _ => by simp [h.symm]) ?_
        simp [hp, count_dedup]
      · exact _root_.trans (List.sum_eq_zero fun n hn => by grind) (by simp [hp])
/-
**List.sum_map_count_dedup_eq_length** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sum_map_count_dedup_eq_length (l : List α) : (l.dedup.map fun x => l.count
 x).sum = l.length
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `List.filter_true`：filter_true (l : List α) : filter (fun _ => true) l = 
l
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.countP_true`：∀ {α : Type u_1}, (List.countP fun x => true) = List.l
ength
· 使用定理 `List.sum_map_count_dedup_filter_eq_countP`：sum_map_count_dedup_filter_eq
_countP (p : α -> Bool) (l : List α) : ((l.dedup.filter p).map fun x => l.count 
x).sum = l.countP p
-/
theorem sum_map_count_dedup_eq_length (l : List α) :
    (l.dedup.map fun x => l.count x).sum = l.length := by
  simpa using sum_map_count_dedup_filter_eq_countP (fun _ => True) l

end List

namespace List

/-
**List.length_sigma** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：length_sigma {σ : α -> Type*} (l₁ : List α) (l₂ : forall a, List (σ a)) : 
length (l₁.sigma l₂) = (l₁.map fun a => length (l₂ a)).sum
参数：l₁ : List α；l₂ : forall a, List (σ a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma length_sigma {σ : α → Type*} (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    length (l₁.sigma l₂) = (l₁.map fun a ↦ length (l₂ a)).sum := by
  induction l₁ with
  | nil => rfl
  | cons x l₁ IH => simp only [sigma_cons, length_append, length_map, IH, map, sum_cons]
/-
**List.ranges_flatten** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ (l : List ℕ), l.ranges.flatten = List.range l.sum
参数：l : List ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ranges_flatten : ∀ (l : List ℕ), l.ranges.flatten = range l.sum
  | [] => rfl
  | a :: l => by simp [ranges, ← map_flatten, ranges_flatten, range_add]

/-- The members of `l.ranges` have no duplicates -/
/-
**List.ranges_nodup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ranges_nodup {l s : List Nat} (hs : s in ranges l) : s.Nodup
参数：hs : s in ranges l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.pairwise_flatten`：∀ {α : Type u_1} {R : α → α → Prop} {L : List (Li
st α)},   List.Pairwise R L.flatten ↔ (∀ l ∈ L, List.Pairwise R l) ∧ List.Pairwi
se (fun l₁ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ranges_flatten`：∀ (l : List ℕ), l.ranges.flatten = List.range l.sum
· 使用定理 `List.nodup_range`：∀ {n : ℕ}, (List.range n).Nodup

--- 原说明 ---
The members of `l.ranges` have no duplicates
-/
theorem ranges_nodup {l s : List ℕ} (hs : s ∈ ranges l) : s.Nodup :=
  (List.pairwise_flatten.mp <| by rw [ranges_flatten]; exact nodup_range).1 s hs

/-- Any entry of any member of `l.ranges` is strictly smaller than `l.sum`. -/
/-
**List.mem_mem_ranges_iff_lt_sum** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：mem_mem_ranges_iff_lt_sum (l : List Nat) {n : Nat} : (exists s in l.ranges
, n in s) ↔ n < l.sum
参数：l : List Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.mem_range`：∀ {m n : ℕ}, m ∈ List.range n ↔ m < n
· 使用定理 `List.ranges_flatten`：∀ (l : List ℕ), l.ranges.flatten = List.range l.sum
· 使用定理 `List.mem_flatten`：∀ {α : Type u_1} {a : α} {L : List (List α)}, a ∈ L.fl
atten ↔ ∃ l ∈ L, a ∈ l
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Any entry of any member of `l.ranges` is strictly smaller than `l.sum`.
-/
lemma mem_mem_ranges_iff_lt_sum (l : List ℕ) {n : ℕ} :
    (∃ s ∈ l.ranges, n ∈ s) ↔ n < l.sum := by
  rw [← mem_range, ← ranges_flatten, mem_flatten]

/-- In a flatten of sublists, taking the slice between the indices `A` and `B - 1` gives back the
original sublist of index `i` if `A` is the sum of the lengths of sublists of index `< i`, and
`B` is the sum of the lengths of sublists of index `≤ i`. -/
/-
**List.drop_take_succ_flatten_eq_getElem** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：drop_take_succ_flatten_eq_getElem (L : List (List α)) (i : Nat) (h : i < L
.length) : (L.flatten.take ((L.map length).take (i + 1)).sum).drop ((L.map lengt
h).take i).sum = L[i]
参数：L : List (List α)；i : Nat；h : i < L.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_take`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α} 
{i : ℕ},   List.map f (List.take i l) = List.take i (List.map f l)
· 使用定理 `List.take_take`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.take i (Li
st.take j l) = List.take (min i j) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.min_eq_left`：∀ {a b : ℕ}, a ≤ b → min a b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `List.take_sum_flatten`：take_sum_flatten (L : List (List α)) (i : Nat) : 
L.flatten.take ((L.map length).take i).sum = (L.take i).flatten
· 使用引理 `List.drop_sum_flatten`：drop_sum_flatten (L : List (List α)) (i : Nat) : 
L.flatten.drop ((L.map length).take i).sum = (L.drop i).flatten
· 使用定理 `List.drop_take_succ_eq_cons_getElem`：drop_take_succ_eq_cons_getElem (L :
 List α) (i : Nat) (h : i < L.length) : (L.take (i + 1)).drop i = [L[i]]
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as

--- 原说明 ---
In a flatten of sublists, taking the slice between the indices `A` and `B - 1` g
ives back the
original sublist of index `i` if `A` is the sum of the lengths of sublists of in
dex `< i`, and
`B` is the sum of the lengths of sublists of index `≤ i`.
-/
lemma drop_take_succ_flatten_eq_getElem (L : List (List α)) (i : Nat) (h : i < L.length) :
    (L.flatten.take ((L.map length).take (i + 1)).sum).drop ((L.map length).take i).sum = L[i] := by
  have : (L.map length).take i = ((L.take (i + 1)).map length).take i := by
    simp [map_take, take_take, Nat.min_eq_left]
  simp only [this, take_sum_flatten, drop_sum_flatten,
    drop_take_succ_eq_cons_getElem, h, flatten_nil, flatten_cons, append_nil]

end List


namespace List

/-- If a product of integers is `-1`, then at least one factor must be `-1`. -/
/-
**List.neg_one_mem_of_prod_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：neg_one_mem_of_prod_eq_neg_one {l : List Int} (h : l.prod = -1) : (-1 : In
t) in l
参数：h : l.prod = -1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.exists_mem_ne_one_of_prod_ne_one`：∀ {M : Type u_4} [inst : Monoid M
] {l : List M}, l.prod ≠ 1 → ∃ x ∈ l, x ≠ 1
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Int.isUnit_iff`：isUnit_iff : IsUnit u ↔ u = 1 ∨ u = -1
· 使用定理 `List.prod_isUnit_iff`：prod_isUnit_iff {M : Type*} [CommMonoid M] {L : Li
st M} : IsUnit L.prod ↔ forall m in L, IsUnit m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If a product of integers is `-1`, then at least one factor must be `-1`.
-/
theorem neg_one_mem_of_prod_eq_neg_one {l : List ℤ} (h : l.prod = -1) : (-1 : ℤ) ∈ l := by
  obtain ⟨x, h₁, h₂⟩ := exists_mem_ne_one_of_prod_ne_one (ne_of_eq_of_ne h (by decide))
  exact Or.resolve_left
    (Int.isUnit_iff.mp (prod_isUnit_iff.mp
      (h.symm ▸ ⟨⟨-1, -1, by decide, by decide⟩, rfl⟩ : IsUnit l.prod) x h₁)) h₂ ▸ h₁
/-
**List.dvd_prod** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dvd_prod [CommMonoid M] {a} {l : List M} (ha : a in l) : a ∣ l.prod
参数：ha : a in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.append_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ s t
, l = s ++ a :: t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem dvd_prod [CommMonoid M] {a} {l : List M} (ha : a ∈ l) : a ∣ l.prod := by
  let ⟨s, t, h⟩ := append_of_mem ha
  rw [h, prod_append, prod_cons, mul_left_comm]
  exact dvd_mul_right _ _
/-
**List.Sublist.prod_dvd_prod** 是 Mathlib 中的一个定理，位于命名空间 `List.Sublist`。
形式化陈述：∀ {M : Type u_4} [inst : CommMonoid M] {l₁ l₂ : List M}, l₁.Sublist l₂ → l
₁.prod ∣ l₂.prod
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.exists_perm_append`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.S
ublist l₂ → ∃ l, l₂.Perm (l₁ ++ l)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Perm.prod_eq`：∀ {M : Type u_4} [inst : CommMonoid M] {l₁ l₂ : List 
M}, l₁.Perm l₂ → l₁.prod = l₂.prod
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem Sublist.prod_dvd_prod [CommMonoid M] {l₁ l₂ : List M} (h : l₁ <+ l₂) :
    l₁.prod ∣ l₂.prod := by
  obtain ⟨l, hl⟩ := h.exists_perm_append
  rw [hl.prod_eq, prod_append]
  exact dvd_mul_right _ _

section Alternating

variable [CommGroup G]

@[to_additive]
/-
**List.alternatingProd_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {G : Type u_7} [inst : CommGroup G] (l₁ l₂ : List G),   (l₁ ++ l₂).alter
natingProd = l₁.alternatingProd * l₂.alternatingProd ^ (-1) ^ l₁.length
参数：l₁ l₂ : List G；l₁ ++ l₂；-1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem alternatingProd_append :
    ∀ l₁ l₂ : List G,
      alternatingProd (l₁ ++ l₂) = alternatingProd l₁ * alternatingProd l₂ ^ (-1 : ℤ) ^ length l₁
  | [], l₂ => by simp
  | a :: l₁, l₂ => by
    simp_rw [cons_append, alternatingProd_cons, alternatingProd_append, length_cons, pow_succ',
      Int.neg_mul, one_mul, zpow_neg, ← div_eq_mul_inv, div_div]

@[to_additive]
/-
**List.alternatingProd_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {G : Type u_7} [inst : CommGroup G] (l : List G),   l.reverse.alternatin
gProd = l.alternatingProd ^ (-1) ^ (l.length + 1)
参数：l : List G；-1；l.length + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem alternatingProd_reverse :
    ∀ l : List G, alternatingProd (reverse l) = alternatingProd l ^ (-1 : ℤ) ^ (length l + 1)
  | [] => by simp only [alternatingProd_nil, one_zpow, reverse_nil]
  | a :: l => by
    simp_rw [reverse_cons, alternatingProd_append, alternatingProd_reverse,
      alternatingProd_singleton, alternatingProd_cons, length_reverse, length, pow_succ',
      Int.neg_mul, one_mul, zpow_neg, inv_inv]
    rw [mul_comm, ← div_eq_mul_inv, div_zpow]

end Alternating

end List

open List

namespace MulOpposite
variable [Monoid M]

/-
**MulOpposite.op_list_prod** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：op_list_prod : forall l : List M, op l.prod = (l.map op).reverse.prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.reverse_cons'`：reverse_cons' (a : α) (l : List α) : reverse (a :: l
) = concat (reverse l) a
· 使用定理 `List.prod_concat`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 * x2
] {l :…
· 使用定理 `MulOpposite.op_mul`：∀ {α : Type u_1} [inst : Mul α] (x y : α), MulOpposi
te.op (x * y) = MulOpposite.op y * MulOpposite.op x
-/
lemma op_list_prod : ∀ l : List M, op l.prod = (l.map op).reverse.prod := by
  intro l; induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.prod_cons, List.map_cons, List.reverse_cons', List.prod_concat, op_mul, ih]
/-
**MulOpposite.unop_list_prod** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：unop_list_prod (l : List Mᵐᵒᵖ) : l.prod.unop = (l.map unop).reverse.prod
参数：l : List Mᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulOpposite.op_inj`：op_inj {x y : α} : op x = op y ↔ x = y
· 使用定理 `MulOpposite.op_unop`：op_unop (x : αᵐᵒᵖ) : op (unop x) = x
· 使用引理 `MulOpposite.op_list_prod`：op_list_prod : forall l : List M, op l.prod = 
(l.map op).reverse.prod
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `MulOpposite.op_comp_unop`：op_comp_unop : (op : α -> αᵐᵒᵖ) ∘ unop = id
· 使用定理 `List.map_id`：∀ {α : Type u_1} (l : List α), List.map id l = l
-/
lemma unop_list_prod (l : List Mᵐᵒᵖ) : l.prod.unop = (l.map unop).reverse.prod := by
  rw [← op_inj, op_unop, MulOpposite.op_list_prod, map_reverse, map_map, reverse_reverse,
    op_comp_unop, map_id]

end MulOpposite

section MonoidHom
variable [Monoid M] [Monoid N]

/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements. -/
/-
**unop_map_list_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：unop_map_list_prod {F : Type*} [FunLike F M Nᵐᵒᵖ] [MonoidHomClass F M Nᵐᵒᵖ
] (f : F) (l : List M) : (f l.prod).unop = (l.map (MulOpposite.unop ∘ f)).revers
e.prod
参数：f : F；l : List M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
· 使用引理 `MulOpposite.unop_list_prod`：unop_list_prod (l : List Mᵐᵒᵖ) : l.prod.unop
 = (l.map unop).reverse.prod
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l

--- 原说明 ---
A morphism into the opposite monoid acts on the product by acting on the reverse
d elements.
-/
lemma unop_map_list_prod {F : Type*} [FunLike F M Nᵐᵒᵖ] [MonoidHomClass F M Nᵐᵒᵖ]
    (f : F) (l : List M) :
    (f l.prod).unop = (l.map (MulOpposite.unop ∘ f)).reverse.prod := by
  rw [map_list_prod f l, MulOpposite.unop_list_prod, List.map_map]

end MonoidHom

