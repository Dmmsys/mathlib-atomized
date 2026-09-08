/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic

/-!
# Sums and products over multisets

In this file we define products and sums indexed by multisets. This is later used to define products
and sums indexed by finite sets.

## Main declarations

* `Multiset.prod`: `s.prod f` is the product of `f i` over all `i ∈ s`. Not to be mistaken with
  the Cartesian product `Multiset.product`.
* `Multiset.sum`: `s.sum f` is the sum of `f i` over all `i ∈ s`.
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {F ι κ G M N O : Type*}

namespace Multiset

section CommMonoid

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

@[to_additive (attr := simp)]
/-
**Multiset.prod_erase** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_erase [DecidableEq M] (h : a in s) : a * (s.erase a).prod = s.prod
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_toList`：coe_toList (s : Multiset α) : (s.toList : Multiset 
α) = s
· 使用定理 `Multiset.coe_erase`：coe_erase (l : List α) (a : α) : erase (l : Multiset
 α) a = l.erase a
· 使用定理 `Multiset.prod_coe`：prod_coe (l : List M) : prod ↑l = l.prod
· 使用引理 `List.prod_erase`：prod_erase [DecidableEq M] (ha : a in l) : a * (l.erase
 a).prod = l.prod
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_toList`：mem_toList {a : α} {s : Multiset α} : a in s.toList
 ↔ a in s
-/
theorem prod_erase [DecidableEq M] (h : a ∈ s) : a * (s.erase a).prod = s.prod := by
  rw [← s.coe_toList, coe_erase, prod_coe, prod_coe, List.prod_erase (mem_toList.2 h)]

@[to_additive (attr := simp)]
/-
**Multiset.prod_map_erase** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_map_erase [DecidableEq ι] {a : ι} (h : a in m) : f a * ((m.erase a).m
ap f).prod = (m.map f).prod
参数：h : a in m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_toList`：coe_toList (s : Multiset α) : (s.toList : Multiset 
α) = s
· 使用定理 `Multiset.coe_erase`：coe_erase (l : List α) (a : α) : erase (l : Multiset
 α) a = l.erase a
· 使用定理 `Multiset.map_coe`：∀ {α : Type u_1} {β : Type v} (f : α → β) (l : List α)
, Multiset.map f ↑l = ↑(List.map f l)
· 使用定理 `Multiset.prod_coe`：prod_coe (l : List M) : prod ↑l = l.prod
· 使用引理 `List.prod_map_erase`：prod_map_erase [DecidableEq α] (f : α -> M) {a} : f
orall {l : List α}, a in l -> f a * ((l.erase a).map f).prod = (l.map f).prod | 
b :: l, h…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_toList`：mem_toList {a : α} {s : Multiset α} : a in s.toList
 ↔ a in s
-/
theorem prod_map_erase [DecidableEq ι] {a : ι} (h : a ∈ m) :
    f a * ((m.erase a).map f).prod = (m.map f).prod := by
  rw [← m.coe_toList, coe_erase, map_coe, map_coe, prod_coe, prod_coe,
    List.prod_map_erase f (mem_toList.2 h)]

@[to_additive (attr := simp, grind =)]
/-
**Multiset.prod_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_add (s t : Multiset M) : prod (s + t) = prod s * prod t
参数：s t : Multiset M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_add (s t : Multiset M) : prod (s + t) = prod s * prod t :=
  Quotient.inductionOn₂ s t fun l₁ l₂ => by simp [List.prod_append]

@[to_additive]
/-
**Multiset.prod_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {M : Type u_5} [inst : CommMonoid M] (m : Multiset M) (n : ℕ), (n • m).p
rod = m.prod ^ n
参数：m : Multiset M；n : ℕ；n • m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_nsmul (m : Multiset M) : ∀ n : ℕ, (n • m).prod = m.prod ^ n
  | 0 => by
    rw [zero_nsmul, pow_zero]
    rfl
  | n + 1 => by rw [add_nsmul, one_nsmul, pow_add, pow_one, prod_add, prod_nsmul m n]

@[to_additive]
/-
**Multiset.prod_filter_mul_prod_filter_not** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_filter_mul_prod_filter_not (p) [DecidablePred p] : (s.filter p).prod 
* (s.filter (fun a => ¬ p a)).prod = s.prod
参数：p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.prod_add`：prod_add (s t : Multiset M) : prod (s + t) = prod s *
 prod t
· 使用定理 `Multiset.filter_add_not`：filter_add_not (s : Multiset α) : filter p s + 
filter (fun a => ¬p a) s = s
-/
theorem prod_filter_mul_prod_filter_not (p) [DecidablePred p] :
    (s.filter p).prod * (s.filter (fun a ↦ ¬ p a)).prod = s.prod := by
  rw [← prod_add, filter_add_not]

@[to_additive]
/-
**Multiset.prod_map_eq_pow_single** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_map_eq_pow_single [DecidableEq ι] (i : ι) (hf : forall i' != i, i' in
 m -> f i' = 1) : (m.map f).prod = f i ^ m.count i
参数：i : ι；hf : forall i' != i, i' in m -> f i' = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `List.prod_map_eq_pow_single`：prod_map_eq_pow_single [DecidableEq α] {l :
 List α} (a : α) (f : α -> M) (hf : forall a', a' != a -> a' in l -> f a' = 1) :
 (l.map f).prod =…
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_map_eq_pow_single [DecidableEq ι] (i : ι)
    (hf : ∀ i' ≠ i, i' ∈ m → f i' = 1) : (m.map f).prod = f i ^ m.count i := by
  induction m using Quotient.inductionOn
  simp [List.prod_map_eq_pow_single i f hf]

@[to_additive]
/-
**Multiset.prod_eq_pow_single** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_eq_pow_single [DecidableEq M] (a : M) (h : forall a' != a, a' in s ->
 a' = 1) : s.prod = a ^ s.count a
参数：a : M；h : forall a' != a, a' in s -> a' = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `List.prod_eq_pow_single`：prod_eq_pow_single [DecidableEq M] (a : M) (h :
 forall a', a' != a -> a' in l -> a' = 1) : l.prod = a ^ l.count a
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_eq_pow_single [DecidableEq M] (a : M) (h : ∀ a' ≠ a, a' ∈ s → a' = 1) :
    s.prod = a ^ s.count a := by
  induction s using Quotient.inductionOn; simp [List.prod_eq_pow_single a h]

@[to_additive]
/-
**Multiset.prod_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_eq_one (h : forall x in s, x = (1 : M)) : s.prod = 1
参数：h : forall x in s, x = (1 : M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_eq_one`：∀ {M : Type u_4} [inst : Monoid M] {l : List M}, (∀ x 
∈ l, x = 1) → l.prod = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_eq_one (h : ∀ x ∈ s, x = (1 : M)) : s.prod = 1 := by
  induction s using Quotient.inductionOn; simp [List.prod_eq_one h]

@[to_additive]
/-
**Multiset.prod_hom_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_hom_ne_zero {s : Multiset M} (hs : s != 0) {F : Type*} [FunLike F M N
] [MulHomClass F M N] (f : F) : (s.map f).prod = f s.prod
参数：hs : s != 0；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_hom_nonempty`：prod_hom_nonempty {l : List M} {F : Type*} [FunL
ike F M N] [MulHomClass F M N] (f : F) (hl : l != []) : (l.map f).prod = f l.pro
d
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_hom_ne_zero {s : Multiset M} (hs : s ≠ 0) {F : Type*} [FunLike F M N]
    [MulHomClass F M N] (f : F) :
    (s.map f).prod = f s.prod := by
  induction s using Quot.inductionOn; aesop (add simp List.prod_hom_nonempty)

@[to_additive]
/-
**Multiset.prod_hom** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_hom (s : Multiset M) {F : Type*} [FunLike F M N] [MonoidHomClass F M 
N] (f : F) : (s.map f).prod = f s.prod
参数：s : Multiset M；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_hom`：prod_hom (l : List M) {F : Type*} [FunLike F M N] [Monoid
HomClass F M N] (f : F) : (l.map f).prod = f l.prod
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_hom (s : Multiset M) {F : Type*} [FunLike F M N]
    [MonoidHomClass F M N] (f : F) :
    (s.map f).prod = f s.prod :=
  Quotient.inductionOn s fun l => by simp only [l.prod_hom f, quot_mk_to_coe, map_coe, prod_coe]

@[to_additive]
/-
**Multiset.prod_hom'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_hom' (s : Multiset ι) {F : Type*} [FunLike F M N] [MonoidHomClass F M
 N] (f : F) (g : ι -> M) : (s.map fun i => f <| g i).prod = f (s.map g).prod
参数：s : Multiset ι；f : F；g : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.prod_hom`：prod_hom (s : Multiset M) {F : Type*} [FunLike F M N]
 [MonoidHomClass F M N] (f : F) : (s.map f).prod = f s.prod
-/
theorem prod_hom' (s : Multiset ι) {F : Type*} [FunLike F M N]
    [MonoidHomClass F M N] (f : F)
    (g : ι → M) : (s.map fun i => f <| g i).prod = f (s.map g).prod := by
  convert! (s.map g).prod_hom f
  exact (map_map _ _ _).symm

@[to_additive]
/-
**Multiset.prod_hom** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_hom (s : Multiset M) {F : Type*} [FunLike F M N] [MonoidHomClass F M 
N] (f : F) : (s.map f).prod = f s.prod
参数：s : Multiset M；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_hom`：prod_hom (l : List M) {F : Type*} [FunLike F M N] [Monoid
HomClass F M N] (f : F) : (l.map f).prod = f l.prod
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_hom₂_ne_zero [CommMonoid O] {s : Multiset ι} (hs : s ≠ 0) (f : M → N → O)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (f₁ : ι → M) (f₂ : ι → N) :
    (s.map fun i => f (f₁ i) (f₂ i)).prod = f (s.map f₁).prod (s.map f₂).prod := by
  induction s using Quotient.inductionOn; aesop (add simp List.prod_hom₂_nonempty)

@[to_additive]
/-
**Multiset.prod_hom** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_hom (s : Multiset M) {F : Type*} [FunLike F M N] [MonoidHomClass F M 
N] (f : F) : (s.map f).prod = f s.prod
参数：s : Multiset M；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_hom`：prod_hom (l : List M) {F : Type*} [FunLike F M N] [Monoid
HomClass F M N] (f : F) : (l.map f).prod = f l.prod
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_hom₂ [CommMonoid O] (s : Multiset ι) (f : M → N → O)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (hf' : f 1 1 = 1) (f₁ : ι → M)
    (f₂ : ι → N) : (s.map fun i => f (f₁ i) (f₂ i)).prod = f (s.map f₁).prod (s.map f₂).prod :=
  Quotient.inductionOn s fun l => by
    simp only [l.prod_hom₂ f hf hf', quot_mk_to_coe, map_coe, prod_coe]

@[to_additive (attr := simp)]
/-
**Multiset.prod_map_mul** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_map_mul : (m.map fun i => f i * g i).prod = (m.map f).prod * (m.map g
).prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_hom₂`：prod_hom₂ [CommMonoid O] (s : Multiset ι) (f : M -> 
N -> O) (hf : forall a b c d, f (a * b) (c * d) = f a c * f b d) (hf' : f 1 1 = 
1) (f₁ :…
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem prod_map_mul : (m.map fun i => f i * g i).prod = (m.map f).prod * (m.map g).prod :=
  m.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _

@[to_additive]
/-
**Multiset.prod_map_pow** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_map_pow {n : Nat} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^ 
n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_hom'`：prod_hom' (s : Multiset ι) {F : Type*} [FunLike F M 
N] [MonoidHomClass F M N] (f : F) (g : ι -> M) : (s.map fun i => f <| g i).prod 
= f (s.m…
-/
theorem prod_map_pow {n : ℕ} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n :=
  m.prod_hom' (powMonoidHom n : M →* M) f

@[to_additive]
/-
**Multiset.prod_map_prod_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_map_prod_map (m : Multiset ι) (n : Multiset κ) {f : ι -> κ -> M} : pr
od (m.map fun a => prod <| n.map fun b => f a b) = prod (n.map fun b => prod <| 
m.map fun a => f a b)
参数：m : Multiset ι；n : Multiset κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.prod_map_mul`：prod_map_mul : (m.map fun i => f i * g i).prod = 
(m.map f).prod * (m.map g).prod
-/
theorem prod_map_prod_map (m : Multiset ι) (n : Multiset κ) {f : ι → κ → M} :
    prod (m.map fun a => prod <| n.map fun b => f a b) =
      prod (n.map fun b => prod <| m.map fun a => f a b) :=
  Multiset.induction_on m (by simp) fun a m ih => by simp [ih]
/-
**Multiset.prod_dvd_prod_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_dvd_prod_of_le (h : s <= t) : s.prod ∣ t.prod
参数：h : s <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `Multiset.instExistsAddOfLE`：∀ {α : Type u_1}, ExistsAddOfLE (Multiset α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_add`：prod_add (s t : Multiset M) : prod (s + t) = prod s *
 prod t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem prod_dvd_prod_of_le (h : s ≤ t) : s.prod ∣ t.prod := by
  obtain ⟨z, rfl⟩ := exists_add_of_le h
  simp only [prod_add, dvd_mul_right]

@[to_additive]
/-
**Multiset._root_.map_multiset_prod** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.map_multiset_prod [FunLike F M N] [MonoidHomClass F M N] (f : F) (s : Multiset M) :
    f s.prod = (s.map f).prod := (s.prod_hom f).symm

@[to_additive]
/-
**Multiset._root_.map_multiset_ne_zero_prod** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.map_multiset_ne_zero_prod [FunLike F M N] [MulHomClass F M N] (f : F)
    {s : Multiset M} (hs : s ≠ 0) :
    f s.prod = (s.map f).prod := (s.prod_hom_ne_zero hs f).symm

@[to_additive]
/-
**Multiset._root_.MonoidHom.map_multiset_prod** 是 Mathlib 中的一个引理，位于命名空间 `Multise
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.MonoidHom.map_multiset_prod (f : M →* N) (s : Multiset M) :
    f s.prod = (s.map f).prod := (s.prod_hom f).symm

@[to_additive]
/-
**Multiset._root_.MulHom.map_multiset_ne_zero_prod** 是 Mathlib 中的一个引理，位于命名空间 `Mu
ltiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.MulHom.map_multiset_ne_zero_prod (f : M →ₙ* N) (s : Multiset M)
    (hs : s ≠ 0) : f s.prod = (s.map f).prod := (s.prod_hom_ne_zero hs f).symm
/-
**Multiset.dvd_prod** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：dvd_prod : a in s -> a ∣ s.prod
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `List.dvd_prod`：dvd_prod [CommMonoid M] {a} {l : List M} (ha : a in l) : 
a ∣ l.prod
-/
lemma dvd_prod : a ∈ s → a ∣ s.prod :=
  Quotient.inductionOn s (fun l a h ↦ by simpa using List.dvd_prod h) a
/-
**Multiset.fst_prod** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {M : Type u_5} {N : Type u_6} [inst : CommMonoid M] [inst_1 : CommMonoid
 N] (s : Multiset (M × N)),   s.prod.1 = (Multiset.map Prod.fst s).prod
参数：s : Multiset (M × N)；Multiset.map Prod.fst s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_prod`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst 
: CommMonoid M] [inst_1 : CommMonoid N] [inst_2 : FunLike F M N]   [MonoidHomCla
ss F M …
-/
@[to_additive] lemma fst_prod (s : Multiset (M × N)) : s.prod.1 = (s.map Prod.fst).prod :=
  map_multiset_prod (MonoidHom.fst _ _) _
/-
**Multiset.snd_prod** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {M : Type u_5} {N : Type u_6} [inst : CommMonoid M] [inst_1 : CommMonoid
 N] (s : Multiset (M × N)),   s.prod.2 = (Multiset.map Prod.snd s).prod
参数：s : Multiset (M × N)；Multiset.map Prod.snd s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_prod`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst 
: CommMonoid M] [inst_1 : CommMonoid N] [inst_2 : FunLike F M N]   [MonoidHomCla
ss F M …
-/
@[to_additive] lemma snd_prod (s : Multiset (M × N)) : s.prod.2 = (s.map Prod.snd).prod :=
  map_multiset_prod (MonoidHom.snd _ _) _

end CommMonoid

/-
**Multiset.prod_dvd_prod_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_dvd_prod_of_dvd [CommMonoid N] {S : Multiset M} (g1 g2 : M -> N) (h :
 forall a in S, g1 a ∣ g2 a) : (Multiset.map g1 S).prod ∣ (Multiset.map g2 S).pr
od
参数：g1 g2 : M -> N；h : forall a in S, g1 a ∣ g2 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on'`：induction_on' {p : Multiset α -> Prop} (S : Mult
iset α) (h₁ : p 0) (h₂ : forall {a s}, a in S -> s subseteq S -> p s -> p (inser
t a s)) : p …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
-/
theorem prod_dvd_prod_of_dvd [CommMonoid N] {S : Multiset M} (g1 g2 : M → N)
    (h : ∀ a ∈ S, g1 a ∣ g2 a) : (Multiset.map g1 S).prod ∣ (Multiset.map g2 S).prod := by
  apply Multiset.induction_on' S
  · simp
  intro a T haS _ IH
  simp [mul_dvd_mul (h a haS) IH]

section AddCommMonoid

variable [AddCommMonoid M]

/-- `Multiset.sum`, the sum of the elements of a multiset, promoted to a morphism of
`AddCommMonoid`s. -/
/-
**Multiset.sumAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：sumAddMonoidHom : Multiset M ->+ M where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.sum_zero`：∀ {M : Type u_3} [inst : AddCommMonoid M], Multiset.s
um 0 = 0
· 使用定理 `Multiset.sum_add`：∀ {M : Type u_5} [inst : AddCommMonoid M] (s t : Multi
set M), (s + t).sum = s.sum + t.sum

--- 原说明 ---
`Multiset.sum`, the sum of the elements of a multiset, promoted to a morphism of
`AddCommMonoid`s.
-/
def sumAddMonoidHom : Multiset M →+ M where
  toFun := sum
  map_zero' := sum_zero
  map_add' := sum_add

@[simp]
/-
**Multiset.coe_sumAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_sumAddMonoidHom : (sumAddMonoidHom : Multiset M -> M) = sum
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sumAddMonoidHom : (sumAddMonoidHom : Multiset M → M) = sum :=
  rfl

end AddCommMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid G] {m : Multiset ι} {f g : ι → G}

@[to_additive]
/-
**Multiset.prod_map_inv'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_map_inv' (m : Multiset G) : (m.map Inv.inv).prod = m.prod⁻¹
参数：m : Multiset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_hom`：prod_hom (s : Multiset M) {F : Type*} [FunLike F M N]
 [MonoidHomClass F M N] (f : F) : (s.map f).prod = f s.prod
-/
theorem prod_map_inv' (m : Multiset G) : (m.map Inv.inv).prod = m.prod⁻¹ :=
  m.prod_hom (invMonoidHom : G →* G)

@[to_additive (attr := simp)]
/-
**Multiset.prod_map_inv** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_map_inv : (m.map fun i => (f i)⁻¹).prod = (m.map f).prod⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.prod_map_inv'`：prod_map_inv' (m : Multiset G) : (m.map Inv.inv)
.prod = m.prod⁻¹
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
theorem prod_map_inv : (m.map fun i => (f i)⁻¹).prod = (m.map f).prod⁻¹ := by
  rw [← (m.map f).prod_map_inv', map_map, Function.comp_def]

@[to_additive (attr := simp)]
/-
**Multiset.prod_map_div** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_map_div : (m.map fun i => f i / g i).prod = (m.map f).prod / (m.map g
).prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_hom₂`：prod_hom₂ [CommMonoid O] (s : Multiset ι) (f : M -> 
N -> O) (hf : forall a b c d, f (a * b) (c * d) = f a c * f b d) (hf' : f 1 1 = 
1) (f₁ :…
· 使用定理 `mul_div_mul_comm`：mul_div_mul_comm : a * b / (c * d) = a / c * (b / d)
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
theorem prod_map_div : (m.map fun i => f i / g i).prod = (m.map f).prod / (m.map g).prod :=
  m.prod_hom₂ (· / ·) mul_div_mul_comm (div_one _) _ _

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**Multiset.prod_map_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_map_zpow {n : Int} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^
 n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `zpowGroupHom_apply`：∀ {α : Type u_1} [inst : DivisionCommMonoid α] (n : 
ℤ) (x : α), (zpowGroupHom n) x = x ^ n
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.prod_hom`：prod_hom (s : Multiset M) {F : Type*} [FunLike F M N]
 [MonoidHomClass F M N] (f : F) : (s.map f).prod = f s.prod
-/
theorem prod_map_zpow {n : ℤ} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n := by
  convert! (m.map f).prod_hom (zpowGroupHom n : G →* G)
  simp only [map_map, Function.comp_apply, zpowGroupHom_apply]

end DivisionCommMonoid

@[simp]
/-
**Multiset.sum_map_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sum_map_singleton (s : Multiset M) : (s.map fun a => ({a} : Multiset M)).s
um = s
参数：s : Multiset M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem sum_map_singleton (s : Multiset M) : (s.map fun a => ({a} : Multiset M)).sum = s :=
  Multiset.induction_on s (by simp) (by simp)
/-
**Multiset.sum_nat_mod** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sum_nat_mod (s : Multiset Nat) (n : Nat) : s.sum % n = (s.map (· % n)).sum
 % n
参数：s : Multiset Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `Nat.add_mod`：∀ (a b n : ℕ), (a + b) % n = (a % n + b % n) % n
· 使用定理 `Nat.mod_mod_of_dvd`：∀ {c b : ℕ} (a : ℕ), c ∣ b → a % b % c = a % c
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
-/
theorem sum_nat_mod (s : Multiset ℕ) (n : ℕ) : s.sum % n = (s.map (· % n)).sum % n := by
  induction s using Multiset.induction <;> simp [Nat.add_mod, *]
/-
**Multiset.prod_nat_mod** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_nat_mod (s : Multiset Nat) (n : Nat) : s.prod % n = (s.map (· % n)).p
rod % n
参数：s : Multiset Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Nat.mul_mod`：∀ (a b n : ℕ), a * b % n = a % n * (b % n) % n
· 使用定理 `Nat.mod_mod_of_dvd`：∀ {c b : ℕ} (a : ℕ), c ∣ b → a % b % c = a % c
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
-/
theorem prod_nat_mod (s : Multiset ℕ) (n : ℕ) : s.prod % n = (s.map (· % n)).prod % n := by
  induction s using Multiset.induction <;> simp [Nat.mul_mod, *]
/-
**Multiset.sum_int_mod** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sum_int_mod (s : Multiset Int) (n : Int) : s.sum % n = (s.map (· % n)).sum
 % n
参数：s : Multiset Int；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `Int.add_emod`：∀ (a b n : ℤ), (a + b) % n = (a % n + b % n) % n
· 使用定理 `Int.emod_emod_of_dvd`：∀ (n : ℤ) {m k : ℤ}, m ∣ k → n % k % m = n % m
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
-/
theorem sum_int_mod (s : Multiset ℤ) (n : ℤ) : s.sum % n = (s.map (· % n)).sum % n := by
  induction s using Multiset.induction <;> simp [Int.add_emod, *]
/-
**Multiset.prod_int_mod** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_int_mod (s : Multiset Int) (n : Int) : s.prod % n = (s.map (· % n)).p
rod % n
参数：s : Multiset Int；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Int.mul_emod`：∀ (a b n : ℤ), a * b % n = a % n * (b % n) % n
· 使用定理 `Int.emod_emod_of_dvd`：∀ (n : ℤ) {m k : ℤ}, m ∣ k → n % k % m = n % m
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
-/
theorem prod_int_mod (s : Multiset ℤ) (n : ℤ) : s.prod % n = (s.map (· % n)).prod % n := by
  induction s using Multiset.induction <;> simp [Int.mul_emod, *]

section OrderedSub

/-
**Multiset.sum_map_tsub** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sum_map_tsub [AddCommMonoid M] [PartialOrder M] [ExistsAddOfLE M] [AddLeft
Mono M] [AddLeftReflectLE M] [Sub M] [OrderedSub M] (l : Multiset ι) {f g : ι ->
 M} (hfg : forall x in l, g x <= f x) : (l.map fun x => f x - g x).sum = (l.map 
f).sum - (l.map g).sum
参数：l : Multiset ι；hfg : forall x in l, g x <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_tsub_of_add_eq`：eq_tsub_of_add_eq (h : a + c = b) : a = b - c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.sum_map_add`：∀ {ι : Type u_2} {M : Type u_5} [inst : AddCommMon
oid M] {m : Multiset ι} {f g : ι → M},   (Multiset.map (fun i => f i + g i) m).s
um = (Mult…
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
-/
theorem sum_map_tsub [AddCommMonoid M] [PartialOrder M] [ExistsAddOfLE M]
    [AddLeftMono M] [AddLeftReflectLE M] [Sub M]
    [OrderedSub M] (l : Multiset ι) {f g : ι → M} (hfg : ∀ x ∈ l, g x ≤ f x) :
    (l.map fun x ↦ f x - g x).sum = (l.map f).sum - (l.map g).sum :=
  eq_tsub_of_add_eq <| by
    rw [← sum_map_add]
    congr 1
    exact map_congr rfl fun x hx => tsub_add_cancel_of_le <| hfg _ hx

end OrderedSub

/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} : IsAddTorsionFree (Multiset M) :=
  ⟨fun n hn x y h ↦ open scoped Classical in Multiset.ext' fun _ ↦
    (Nat.mul_right_inj hn).mp <| by simp only [← Multiset.count_nsmul, h]⟩

end Multiset

