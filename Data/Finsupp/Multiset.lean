/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Group.Finset
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Sym.Basic
public import Mathlib.Order.Preorder.Finsupp

/-!
# Equivalence between `Multiset` and `ℕ`-valued finitely supported functions

This defines `Finsupp.toMultiset` the equivalence between `α →₀ ℕ` and `Multiset α`, along
with `Multiset.toFinsupp` the reverse equivalence and `Finsupp.orderIsoMultiset` (the equivalence
promoted to an order isomorphism).

-/

@[expose] public section

open Finset

variable {α β ι : Type*}

namespace Finsupp

/-- Given `f : α →₀ ℕ`, `f.toMultiset` is the multiset with multiplicities given by the values of
`f` on the elements of `α`. We define this function as an `AddMonoidHom`.

Under the additional assumption of `[DecidableEq α]`, this is available as
`Multiset.toFinsupp : Multiset α ≃+ (α →₀ ℕ)`; the two declarations are separate as this assumption
is only needed for one direction. -/
/-
**Finsupp.toMultiset** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：toMultiset : (α ->₀ Nat) ->+ Multiset α where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : α →₀ ℕ`, `f.toMultiset` is the multiset with multiplicities given by 
the values of
`f` on the elements of `α`. We define this function as an `AddMonoidHom`.

Under the additional assumption of `[DecidableEq α]`, this is available as
`Multiset.toFinsupp : Multiset α ≃+ (α →₀ ℕ)`; the two declarations are separate
 as this assumption
is only needed for one direction.
-/
def toMultiset : (α →₀ ℕ) →+ Multiset α where
  toFun f := Finsupp.sum f fun a n => n • {a}
  -- Porting note: have to specify `h` or add a `dsimp only` before `sum_add_index'`.
  -- see also: https://github.com/leanprover-community/mathlib4/issues/12129
  map_add' _f _g := sum_add_index' (h := fun _ n => n • _)
    (fun _ ↦ zero_nsmul _) (fun _ ↦ add_nsmul _)
  map_zero' := sum_zero_index
/-
**Finsupp.toMultiset_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toMultiset_zero : toMultiset (0 : α ->₀ Nat) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMultiset_zero : toMultiset (0 : α →₀ ℕ) = 0 :=
  rfl
/-
**Finsupp.toMultiset_add** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toMultiset_add (m n : α ->₀ Nat) : toMultiset (m + n) = toMultiset m + toM
ultiset n
参数：m n : α ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b
-/
theorem toMultiset_add (m n : α →₀ ℕ) : toMultiset (m + n) = toMultiset m + toMultiset n :=
  toMultiset.map_add m n
/-
**Finsupp.toMultiset_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toMultiset_apply (f : α ->₀ Nat) : toMultiset f = f.sum fun a n => n • {a}
参数：f : α ->₀ Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMultiset_apply (f : α →₀ ℕ) : toMultiset f = f.sum fun a n => n • {a} :=
  rfl

@[simp]
/-
**Finsupp.toMultiset_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toMultiset_single (a : α) (n : Nat) : toMultiset (single a n) = n • {a}
参数：a : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.toMultiset_apply`：toMultiset_apply (f : α ->₀ Nat) : toMultiset 
f = f.sum fun a n => n • {a}
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
-/
theorem toMultiset_single (a : α) (n : ℕ) : toMultiset (single a n) = n • {a} := by
  rw [toMultiset_apply, sum_single_index]; apply zero_nsmul
/-
**Finsupp.toMultiset_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toMultiset_sum {f : ι -> α ->₀ Nat} (s : Finset ι) : Finsupp.toMultiset (∑
 i in s, f i) = ∑ i in s, Finsupp.toMultiset (f i)
参数：s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem toMultiset_sum {f : ι → α →₀ ℕ} (s : Finset ι) :
    Finsupp.toMultiset (∑ i ∈ s, f i) = ∑ i ∈ s, Finsupp.toMultiset (f i) :=
  map_sum Finsupp.toMultiset _ _
/-
**Finsupp.toMultiset_sum_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toMultiset_sum_single (s : Finset ι) (n : Nat) : Finsupp.toMultiset (∑ i i
n s, single i n) = n • s.val
参数：s : Finset ι；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.toMultiset_sum`：toMultiset_sum {f : ι -> α ->₀ Nat} (s : Finset 
ι) : Finsupp.toMultiset (∑ i in s, f i) = ∑ i in s, Finsupp.toMultiset (f i)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.toMultiset_single`：toMultiset_single (a : α) (n : Nat) : toMulti
set (single a n) = n • {a}
· 使用定理 `Finset.sum_nsmul`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid 
M] (s : Finset ι) (n : ℕ) (f : ι → M),   ∑ x ∈ s, n • f x = n • ∑ x ∈ s, f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_multiset_singleton`：sum_multiset_singleton (s : Finset ι) : ∑
 a in s, {a} = s.val
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMultiset_sum_single (s : Finset ι) (n : ℕ) :
    Finsupp.toMultiset (∑ i ∈ s, single i n) = n • s.val := by
  simp_rw [toMultiset_sum, Finsupp.toMultiset_single, Finset.sum_nsmul, sum_multiset_singleton]

@[simp]
/-
**Finsupp.card_toMultiset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：card_toMultiset (f : α ->₀ Nat) : Multiset.card (toMultiset f) = f.sum fun
 _ => id
参数：f : α ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_finsuppSum`：∀ {α : Type u_1} {ι : Type u_2} {M : Type u_8}
 [inst : Zero M] (f : ι →₀ M) (g : ι → M → Multiset α),   (f.sum g).card = f.sum
 fun i m => (g…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Multiset.card_nsmul`：card_nsmul (s : Multiset α) (n : Nat) : card (n • s
) = n * card s
· 使用定理 `Multiset.card_singleton`：card_singleton (a : α) : card ({a} : Multiset α
) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_toMultiset (f : α →₀ ℕ) : Multiset.card (toMultiset f) = f.sum fun _ => id := by
  simp [toMultiset_apply, Function.id_def]
/-
**Finsupp.toMultiset_map** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toMultiset_map (f : α ->₀ Nat) (g : α -> β) : f.toMultiset.map g = toMulti
set (f.mapDomain g)
参数：f : α ->₀ Nat；g : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.induction`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass 
M] {motive : (ι →₀ M) → Prop} (f : ι →₀ M),   motive 0 →     (∀ (a : ι) (b : M) 
(f : ι …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.toMultiset_zero`：toMultiset_zero : toMultiset (0 : α ->₀ Nat) = 
0
· 使用定理 `Multiset.map_zero`：map_zero (f : α -> β) : map f 0 = 0
· 使用定理 `Finsupp.mapDomain_zero`：mapDomain_zero {f : α -> β} : mapDomain f (0 : α
 ->₀ M) = (0 : β ->₀ M)
· 使用定理 `Finsupp.toMultiset_add`：toMultiset_add (m n : α ->₀ Nat) : toMultiset (m
 + n) = toMultiset m + toMultiset n
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Finsupp.mapDomain_add`：mapDomain_add {f : α -> β} : mapDomain f (v₁ + v₂
) = mapDomain f v₁ + mapDomain f v₂
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `Finsupp.toMultiset_single`：toMultiset_single (a : α) (n : Nat) : toMulti
set (single a n) = n • {a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Multiset.coe_mapAddMonoidHom`：coe_mapAddMonoidHom (f : α -> β) : (mapAdd
MonoidHom f : Multiset α -> Multiset β) = map f
· 使用定理 `AddMonoidHom.map_nsmul`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoi
d M] [inst_1 : AddMonoid N] (f : M →+ N) (n : ℕ) (a : M),   f (n • a) = n • f a
-/
theorem toMultiset_map (f : α →₀ ℕ) (g : α → β) :
    f.toMultiset.map g = toMultiset (f.mapDomain g) := by
  refine f.induction ?_ ?_
  · rw [toMultiset_zero, Multiset.map_zero, mapDomain_zero, toMultiset_zero]
  · intro a n f _ _ ih
    rw [toMultiset_add, Multiset.map_add, ih, mapDomain_add, mapDomain_single,
      toMultiset_single, toMultiset_add, toMultiset_single, ← Multiset.coe_mapAddMonoidHom,
      (Multiset.mapAddMonoidHom g).map_nsmul]
    rfl

@[to_additive (attr := simp)]
/-
**Finsupp.prod_toMultiset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_toMultiset [CommMonoid α] (f : α ->₀ Nat) : f.toMultiset.prod = f.pro
d fun a n => a ^ n
参数：f : α ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.induction`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass 
M] {motive : (ι →₀ M) → Prop} (f : ι →₀ M),   motive 0 →     (∀ (a : ι) (b : M) 
(f : ι …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.toMultiset_zero`：toMultiset_zero : toMultiset (0 : α ->₀ Nat) = 
0
· 使用定理 `Multiset.prod_zero`：prod_zero : @prod M _ 0 = 1
· 使用定理 `Finsupp.prod_zero_index`：prod_zero_index {h : α -> M -> N} : (0 : α ->₀ 
M).prod h = 1
· 使用定理 `Finsupp.toMultiset_add`：toMultiset_add (m n : α ->₀ Nat) : toMultiset (m
 + n) = toMultiset m + toMultiset n
· 使用定理 `Multiset.prod_add`：prod_add (s t : Multiset M) : prod (s + t) = prod s *
 prod t
· 使用定理 `Finsupp.toMultiset_single`：toMultiset_single (a : α) (n : Nat) : toMulti
set (single a n) = n • {a}
· 使用定理 `Multiset.prod_nsmul`：∀ {M : Type u_5} [inst : CommMonoid M] (m : Multise
t M) (n : ℕ), (n • m).prod = m.prod ^ n
· 使用定理 `Finsupp.prod_add_index'`：prod_add_index' [AddZeroClass M] [CommMonoid N]
 {f g : α ->₀ M} {h : α -> M -> N} (h_zero : forall a, h a 0 = 1) (h_add : foral
l a b₁ b₂, h …
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Finsupp.prod_single_index`：prod_single_index {a : α} {b : M} {h : α -> M
 -> N} (h_zero : h a 0 = 1) : (single a b).prod h = h a b
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
-/
theorem prod_toMultiset [CommMonoid α] (f : α →₀ ℕ) :
    f.toMultiset.prod = f.prod fun a n => a ^ n := by
  refine f.induction ?_ ?_
  · rw [toMultiset_zero, Multiset.prod_zero, Finsupp.prod_zero_index]
  · intro a n f _ _ ih
    rw [toMultiset_add, Multiset.prod_add, ih, toMultiset_single, Multiset.prod_nsmul,
      Finsupp.prod_add_index' pow_zero pow_add, Finsupp.prod_single_index, Multiset.prod_singleton]
    exact pow_zero a

@[simp]
/-
**Finsupp.toFinset_toMultiset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toFinset_toMultiset [DecidableEq α] (f : α ->₀ Nat) : f.toMultiset.toFinse
t = f.support
参数：f : α ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.induction`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass 
M] {motive : (ι →₀ M) → Prop} (f : ι →₀ M),   motive 0 →     (∀ (a : ι) (b : M) 
(f : ι …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.toMultiset_zero`：toMultiset_zero : toMultiset (0 : α ->₀ Nat) = 
0
· 使用定理 `Multiset.toFinset_zero`：toFinset_zero : toFinset (0 : Multiset α) = ∅
· 使用定理 `Finsupp.support_zero`：support_zero : (0 : α ->₀ M).support = ∅
· 使用定理 `Finsupp.toMultiset_add`：toMultiset_add (m n : α ->₀ Nat) : toMultiset (m
 + n) = toMultiset m + toMultiset n
· 使用定理 `Multiset.toFinset_add`：toFinset_add (s t : Multiset α) : (s + t).toFinse
t = s.toFinset union t.toFinset
· 使用定理 `Finsupp.toMultiset_single`：toMultiset_single (a : α) (n : Nat) : toMulti
set (single a n) = n • {a}
· 使用引理 `Finsupp.support_add_eq`：support_add_eq [DecidableEq ι] (h : Disjoint g₁.
support g₂.support) : (g₁ + g₂).support = g₁.support union g₂.support
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
· 使用定理 `Finset.disjoint_singleton_left`：disjoint_singleton_left : Disjoint (sing
leton a) s ↔ a ∉ s
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `Multiset.toFinset_nsmul`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Mu
ltiset α) (n : ℕ), n ≠ 0 → (n • s).toFinset = s.toFinset
· 使用定理 `Multiset.toFinset_singleton`：toFinset_singleton (a : α) : toFinset ({a} 
: Multiset α) = {a}
-/
theorem toFinset_toMultiset [DecidableEq α] (f : α →₀ ℕ) : f.toMultiset.toFinset = f.support := by
  refine f.induction ?_ ?_
  · rw [toMultiset_zero, Multiset.toFinset_zero, support_zero]
  · intro a n f ha hn ih
    rw [toMultiset_add, Multiset.toFinset_add, ih, toMultiset_single, support_add_eq,
      support_single _ hn, Multiset.toFinset_nsmul _ _ hn, Multiset.toFinset_singleton]
    refine Disjoint.mono_left support_single_subset ?_
    rwa [Finset.disjoint_singleton_left]

@[simp]
/-
**Finsupp.count_toMultiset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：count_toMultiset [DecidableEq α] (f : α ->₀ Nat) (a : α) : (toMultiset f).
count a = f a
参数：f : α ->₀ Nat；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.toMultiset_apply`：toMultiset_apply (f : α ->₀ Nat) : toMultiset 
f = f.sum fun a n => n • {a}
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Multiset.count_nsmul`：count_nsmul (a : α) (n s) : count a (n • s) = n * 
count a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.sum_eq_single`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M} (a : α)   {g : α → M → N}
, (∀ (b : α…
· 使用定理 `Multiset.count_singleton`：count_singleton (a b : α) : count a ({b} : Mul
tiset α) = if a = b then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Multiset.count_singleton_self`：count_singleton_self (a : α) : count a ({
a} : Multiset α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem count_toMultiset [DecidableEq α] (f : α →₀ ℕ) (a : α) : (toMultiset f).count a = f a :=
  calc
    (toMultiset f).count a = Finsupp.sum f (fun x n => (n • {x} : Multiset α).count a) := by
      rw [toMultiset_apply]; exact map_sum (Multiset.countAddMonoidHom a) _ f.support
    _ = f.sum fun x n => n * ({x} : Multiset α).count a := by simp only [Multiset.count_nsmul]
    _ = f a * ({a} : Multiset α).count a :=
      sum_eq_single _
        (fun a' _ H => by simp only [Multiset.count_singleton, if_false, H.symm, mul_zero])
        (fun _ => zero_mul _)
    _ = f a := by rw [Multiset.count_singleton_self, mul_one]
/-
**Finsupp.toMultiset_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toMultiset_sup [DecidableEq α] (f g : α ->₀ Nat) : toMultiset (f ⊔ g) = to
Multiset f union toMultiset g
参数：f g : α ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.count_union`：count_union (a : α) (s t : Multiset α) : count a (
s union t) = max (count a s) (count a t)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.count_toMultiset`：count_toMultiset [DecidableEq α] (f : α ->₀ Na
t) (a : α) : (toMultiset f).count a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMultiset_sup [DecidableEq α] (f g : α →₀ ℕ) :
    toMultiset (f ⊔ g) = toMultiset f ∪ toMultiset g := by
  ext
  simp_rw [Multiset.count_union, Finsupp.count_toMultiset, Finsupp.sup_apply]
/-
**Finsupp.toMultiset_inf** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toMultiset_inf [DecidableEq α] (f g : α ->₀ Nat) : toMultiset (f ⊓ g) = to
Multiset f inter toMultiset g
参数：f g : α ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.count_inter`：count_inter (a : α) (s t : Multiset α) : count a (
s inter t) = min (count a s) (count a t)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.count_toMultiset`：count_toMultiset [DecidableEq α] (f : α ->₀ Na
t) (a : α) : (toMultiset f).count a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMultiset_inf [DecidableEq α] (f g : α →₀ ℕ) :
    toMultiset (f ⊓ g) = toMultiset f ∩ toMultiset g := by
  ext
  simp_rw [Multiset.count_inter, Finsupp.count_toMultiset, Finsupp.inf_apply]

@[simp]
/-
**Finsupp.mem_toMultiset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_toMultiset (f : α ->₀ Nat) (i : α) : i in toMultiset f ↔ i in f.suppor
t
参数：f : α ->₀ Nat；i : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Multiset.count_ne_zero`：count_ne_zero {a : α} : count a s != 0 ↔ a in s
· 使用定理 `Finsupp.count_toMultiset`：count_toMultiset [DecidableEq α] (f : α ->₀ Na
t) (a : α) : (toMultiset f).count a = f a
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toMultiset (f : α →₀ ℕ) (i : α) : i ∈ toMultiset f ↔ i ∈ f.support := by
  classical
  rw [← Multiset.count_ne_zero, Finsupp.count_toMultiset, Finsupp.mem_support_iff]

end Finsupp

namespace Multiset

variable [DecidableEq α]

/-- Given a multiset `s`, `s.toFinsupp` returns the finitely supported function on `ℕ` given by
the multiplicities of the elements of `s`. -/
@[simps symm_apply]
/-
**Multiset.toFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：toFinsupp : Multiset α ≃+ (α ->₀ Nat) where toFun s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a multiset `s`, `s.toFinsupp` returns the finitely supported function on `
ℕ` given by
the multiplicities of the elements of `s`.
-/
noncomputable def toFinsupp : Multiset α ≃+ (α →₀ ℕ) where
  toFun s := ⟨s.toFinset, fun a => s.count a, fun a => by simp⟩
  invFun f := Finsupp.toMultiset f
  map_add' _ _ := Finsupp.ext fun _ => count_add _ _ _
  right_inv f :=
    Finsupp.ext fun a => by
      simp only [Finsupp.toMultiset_apply, Finsupp.sum, Multiset.count_sum',
        Multiset.count_singleton, mul_boole, Finsupp.coe_mk, Finsupp.mem_support_iff,
        Multiset.count_nsmul, Finset.sum_ite_eq, ite_not, ite_eq_right_iff]
      exact Eq.symm
  left_inv s := by simp only [Finsupp.toMultiset_apply, Finsupp.sum, Finsupp.coe_mk,
    Multiset.toFinset_sum_count_nsmul_eq]

@[simp]
/-
**Multiset.toFinsupp_support** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinsupp_support (s : Multiset α) : s.toFinsupp.support = s.toFinset
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_support (s : Multiset α) : s.toFinsupp.support = s.toFinset := rfl

@[simp]
/-
**Multiset.toFinsupp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinsupp_apply (s : Multiset α) (a : α) : toFinsupp s a = s.count a
参数：s : Multiset α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_apply (s : Multiset α) (a : α) : toFinsupp s a = s.count a := rfl
/-
**Multiset.toFinsupp_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinsupp_zero : toFinsupp (0 : Multiset α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
theorem toFinsupp_zero : toFinsupp (0 : Multiset α) = 0 := _root_.map_zero _
/-
**Multiset.toFinsupp_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinsupp_add (s t : Multiset α) : toFinsupp (s + t) = toFinsupp s + toFin
supp t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem toFinsupp_add (s t : Multiset α) : toFinsupp (s + t) = toFinsupp s + toFinsupp t :=
  _root_.map_add toFinsupp s t

@[simp]
/-
**Multiset.toFinsupp_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinsupp_singleton (a : α) : toFinsupp ({a} : Multiset α) = Finsupp.singl
e a 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.toFinsupp_apply`：toFinsupp_apply (s : Multiset α) (a : α) : toF
insupp s a = s.count a
· 使用定理 `Multiset.count_singleton`：count_singleton (a b : α) : count a ({b} : Mul
tiset α) = if a = b then 1 else 0
· 使用定理 `Finsupp.single_eq_pi_single`：single_eq_pi_single [DecidableEq α] (a : α)
 (b : M) : ⇑(single a b) = Pi.single a b
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
-/
theorem toFinsupp_singleton (a : α) : toFinsupp ({a} : Multiset α) = Finsupp.single a 1 := by
  ext; rw [toFinsupp_apply, count_singleton, Finsupp.single_eq_pi_single, Pi.single_apply]

@[simp]
/-
**Multiset.toFinsupp_toMultiset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinsupp_toMultiset (s : Multiset α) : Finsupp.toMultiset (toFinsupp s) =
 s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.symm_apply_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (x : M), e.symm (e x) = x
-/
theorem toFinsupp_toMultiset (s : Multiset α) : Finsupp.toMultiset (toFinsupp s) = s :=
  Multiset.toFinsupp.symm_apply_apply s
/-
**Multiset.toFinsupp_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinsupp_eq_iff {s : Multiset α} {f : α ->₀ Nat} : toFinsupp s = f ↔ s = 
Finsupp.toMultiset f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `AddEquiv.eq_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [
inst_1 : Add N] (e : M ≃+ N) {x : N} {y : M}, y = e.symm x ↔ e y = x
-/
theorem toFinsupp_eq_iff {s : Multiset α} {f : α →₀ ℕ} :
    toFinsupp s = f ↔ s = Finsupp.toMultiset f :=
  Multiset.toFinsupp.eq_symm_apply.symm
/-
**Multiset.toFinsupp_union** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinsupp_union (s t : Multiset α) : toFinsupp (s union t) = toFinsupp s ⊔
 toFinsupp t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.count_union`：count_union (a : α) (s t : Multiset α) : count a (
s union t) = max (count a s) (count a t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFinsupp_union (s t : Multiset α) : toFinsupp (s ∪ t) = toFinsupp s ⊔ toFinsupp t := by
  ext
  simp
/-
**Multiset.toFinsupp_inter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinsupp_inter (s t : Multiset α) : toFinsupp (s inter t) = toFinsupp s ⊓
 toFinsupp t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.count_inter`：count_inter (a : α) (s t : Multiset α) : count a (
s inter t) = min (count a s) (count a t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFinsupp_inter (s t : Multiset α) : toFinsupp (s ∩ t) = toFinsupp s ⊓ toFinsupp t := by
  ext
  simp

@[simp]
/-
**Multiset.toFinsupp_sum_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinsupp_sum_eq (s : Multiset α) : s.toFinsupp.sum (fun _ => id) = Multis
et.card s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.card_toMultiset`：card_toMultiset (f : α ->₀ Nat) : Multiset.card
 (toMultiset f) = f.sum fun _ => id
· 使用定理 `Multiset.toFinsupp_toMultiset`：toFinsupp_toMultiset (s : Multiset α) : F
insupp.toMultiset (toFinsupp s) = s
-/
theorem toFinsupp_sum_eq (s : Multiset α) : s.toFinsupp.sum (fun _ ↦ id) = Multiset.card s := by
  rw [← Finsupp.card_toMultiset, toFinsupp_toMultiset]

end Multiset

@[simp]
/-
**Finsupp.toMultiset_toFinsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finsupp.toMultiset_toFinsupp [DecidableEq α] (f : α ->₀ Nat) : Multiset.to
Finsupp (Finsupp.toMultiset f) = f
参数：f : α ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
-/
theorem Finsupp.toMultiset_toFinsupp [DecidableEq α] (f : α →₀ ℕ) :
    Multiset.toFinsupp (Finsupp.toMultiset f) = f :=
  Multiset.toFinsupp.apply_symm_apply _
/-
**Finsupp.toMultiset_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finsupp.toMultiset_eq_iff [DecidableEq α] {f : α ->₀ Nat} {s : Multiset α}
 : Finsupp.toMultiset f = s ↔ f = Multiset.toFinsupp s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.symm_apply_eq`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [
inst_1 : Add N] (e : M ≃+ N) {x : N} {y : M}, e.symm x = y ↔ x = e y
-/
theorem Finsupp.toMultiset_eq_iff [DecidableEq α] {f : α →₀ ℕ} {s : Multiset α} :
    Finsupp.toMultiset f = s ↔ f = Multiset.toFinsupp s :=
  Multiset.toFinsupp.symm_apply_eq

/-! ### As an order isomorphism -/

namespace Finsupp
/-- `Finsupp.toMultiset` as an order isomorphism. -/
/-
**Finsupp.orderIsoMultiset** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：orderIsoMultiset [DecidableEq ι] : (ι ->₀ Nat) ≃o Multiset ι where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp.toMultiset` as an order isomorphism.
-/
noncomputable def orderIsoMultiset [DecidableEq ι] : (ι →₀ ℕ) ≃o Multiset ι where
  toEquiv := Multiset.toFinsupp.symm.toEquiv
  map_rel_iff' {f g} := by simp [le_def, Multiset.le_iff_count]

@[simp]
/-
**Finsupp.coe_orderIsoMultiset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：coe_orderIsoMultiset [DecidableEq ι] : ⇑(@orderIsoMultiset ι _) = toMultis
et
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_orderIsoMultiset [DecidableEq ι] : ⇑(@orderIsoMultiset ι _) = toMultiset :=
  rfl

@[simp]
/-
**Finsupp.coe_orderIsoMultiset_symm** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：coe_orderIsoMultiset_symm [DecidableEq ι] : ⇑(@orderIsoMultiset ι).symm = 
Multiset.toFinsupp
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_orderIsoMultiset_symm [DecidableEq ι] :
    ⇑(@orderIsoMultiset ι).symm = Multiset.toFinsupp :=
  rfl
/-
**Finsupp.toMultiset_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toMultiset_strictMono : StrictMono (@toMultiset ι)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
-/
theorem toMultiset_strictMono : StrictMono (@toMultiset ι) := by
  classical exact (@orderIsoMultiset ι _).strictMono
/-
**Finsupp.sum_id_lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_id_lt_of_lt (m n : ι ->₀ Nat) (h : m < n) : (m.sum fun _ => id) < n.su
m fun _ => id
参数：m n : ι ->₀ Nat；h : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.card_toMultiset`：card_toMultiset (f : α ->₀ Nat) : Multiset.card
 (toMultiset f) = f.sum fun _ => id
· 使用定理 `Multiset.card_lt_card`：card_lt_card {s t : Multiset α} (h : s < t) : car
d s < card t
· 使用定理 `Finsupp.toMultiset_strictMono`：toMultiset_strictMono : StrictMono (@toMu
ltiset ι)
-/
theorem sum_id_lt_of_lt (m n : ι →₀ ℕ) (h : m < n) : (m.sum fun _ => id) < n.sum fun _ => id := by
  rw [← card_toMultiset, ← card_toMultiset]
  apply Multiset.card_lt_card
  exact toMultiset_strictMono h

variable (ι)

/-- The order on `ι →₀ ℕ` is well-founded. -/
/-
**Finsupp.lt_wf** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lt_wf : WellFounded (@LT.lt (ι ->₀ Nat) _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrelation.wf`：∀ {α : Sort u} {r q : α → α → Prop}, Subrelation q r → W
ellFounded r → WellFounded q
· 使用定理 `Finsupp.sum_id_lt_of_lt`：sum_id_lt_of_lt (m n : ι ->₀ Nat) (h : m < n) :
 (m.sum fun _ => id) < n.sum fun _ => id
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用定理 `WellFoundedRelation.wf`：∀ {α : Sort u} [self : WellFoundedRelation α], W
ellFounded WellFoundedRelation.rel

--- 原说明 ---
The order on `ι →₀ ℕ` is well-founded.
-/
theorem lt_wf : WellFounded (@LT.lt (ι →₀ ℕ) _) :=
  Subrelation.wf (sum_id_lt_of_lt _ _) <| InvImage.wf _ Nat.lt_wfRel.2

-- TODO: generalize to `[WellFoundedRelation α] → WellFoundedRelation (ι →₀ α)`
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellFoundedRelation (ι →₀ ℕ) where
  rel := (· < ·)
  wf := lt_wf _

end Finsupp

/-
**Multiset.toFinsupp_strictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.toFinsupp_strictMono [DecidableEq ι] : StrictMono (@Multiset.toFi
nsupp ι _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
-/
theorem Multiset.toFinsupp_strictMono [DecidableEq ι] : StrictMono (@Multiset.toFinsupp ι _) :=
  (@Finsupp.orderIsoMultiset ι).symm.strictMono

namespace Sym

variable (α)
variable [DecidableEq α] (n : ℕ)

/-- The `n`th symmetric power of a type `α` is naturally equivalent to the subtype of
finitely-supported maps `α →₀ ℕ` with total mass `n`.

See also `Sym.equivNatSumOfFintype` when `α` is finite. -/
/-
**Sym.equivNatSum** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：equivNatSum : Sym α n ≃ {P : α ->₀ Nat // P.sum (fun _ => id) = n}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th symmetric power of a type `α` is naturally equivalent to the subtype o
f
finitely-supported maps `α →₀ ℕ` with total mass `n`.

See also `Sym.equivNatSumOfFintype` when `α` is finite.
-/
noncomputable def equivNatSum :
    Sym α n ≃ {P : α →₀ ℕ // P.sum (fun _ ↦ id) = n} :=
  Multiset.toFinsupp.toEquiv.subtypeEquiv <| by simp
/-
**Sym.coe_equivNatSum_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：∀ (α : Type u_1) [inst : DecidableEq α] (n : ℕ) (s : Sym α n) (a : α),   ↑
((Sym.equivNatSum α n) s) a = Multiset.count a ↑s
参数：α : Type u_1；n : ℕ；s : Sym α n；a : α；(Sym.equivNatSum α n) s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_equivNatSum_apply_apply (s : Sym α n) (a : α) :
    (equivNatSum α n s : α →₀ ℕ) a = (s : Multiset α).count a :=
  rfl
/-
**Sym.coe_equivNatSum_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：∀ (α : Type u_1) [inst : DecidableEq α] (n : ℕ) (P : { P // (P.sum fun x =
> id) = n }),   ↑((Sym.equivNatSum α n).symm P) = Finsupp.toMultiset ↑P
参数：α : Type u_1；n : ℕ；P : { P // (P.sum fun x => id) = n }；(Sym.equivNatSum α n)
.symm P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma coe_equivNatSum_symm_apply (P : {P : α →₀ ℕ // P.sum (fun _ ↦ id) = n}) :
    ((equivNatSum α n).symm P : Multiset α) = Finsupp.toMultiset P :=
  rfl

/-- The `n`th symmetric power of a finite type `α` is naturally equivalent to the subtype of maps
`α → ℕ` with total mass `n`.

See also `Sym.equivNatSum` when `α` is not necessarily finite. -/
/-
**Sym.equivNatSumOfFintype** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：equivNatSumOfFintype [Fintype α] : Sym α n ≃ {P : α -> Nat // ∑ i, P i = n
}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The `n`th symmetric power of a finite type `α` is naturally equivalent to the su
btype of maps
`α → ℕ` with total mass `n`.

See also `Sym.equivNatSum` when `α` is not necessarily finite.
-/
noncomputable def equivNatSumOfFintype [Fintype α] :
    Sym α n ≃ {P : α → ℕ // ∑ i, P i = n} :=
  (equivNatSum α n).trans <| Finsupp.equivFunOnFinite.subtypeEquiv <| by simp [Finsupp.sum_fintype]
/-
**Sym.coe_equivNatSumOfFintype_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：∀ (α : Type u_1) [inst : DecidableEq α] (n : ℕ) [inst_1 : Fintype α] (s : 
Sym α n) (a : α),   ↑((Sym.equivNatSumOfFintype α n) s) a = Multiset.count a ↑s
参数：α : Type u_1；n : ℕ；s : Sym α n；a : α；(Sym.equivNatSumOfFintype α n) s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_equivNatSumOfFintype_apply_apply [Fintype α] (s : Sym α n) (a : α) :
    (equivNatSumOfFintype α n s : α → ℕ) a = (s : Multiset α).count a :=
  rfl
/-
**Sym.coe_equivNatSumOfFintype_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：∀ (α : Type u_1) [inst : DecidableEq α] (n : ℕ) [inst_1 : Fintype α] (P : 
{ P // ∑ i, P i = n }),   ↑((Sym.equivNatSumOfFintype α n).symm P) = ∑ a, ↑P a •
 {a}
参数：α : Type u_1；n : ℕ；P : { P // ∑ i, P i = n }；(Sym.equivNatSumOfFintype α n).s
ymm P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_sum`：count_sum [DecidableEq α] {m : Multiset β} {f : β ->
 Multiset α} {a : α} : count a (map f m).sum = sum (m.map fun b => count a <| f 
b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.count_toMultiset`：count_toMultiset [DecidableEq α] (f : α ->₀ Na
t) (a : α) : (toMultiset f).count a = f a
· 使用定理 `Finsupp.equivFunOnFinite_symm_apply_apply`：∀ {α : Type u_1} {M : Type u_
4} [inst : Zero M] [inst_1 : Finite α] (f : α → M) (a : α),   (Finsupp.equivFunO
nFinite.symm f) a = f a
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用引理 `Multiset.count_nsmul`：count_nsmul (a : α) (n s) : count a (n • s) = n * 
count a s
· 使用定理 `Multiset.count_singleton`：count_singleton (a b : α) : count a ({b} : Mul
tiset α) = if a = b then 1 else 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma coe_equivNatSumOfFintype_symm_apply [Fintype α] (P : {P : α → ℕ // ∑ i, P i = n}) :
    ((equivNatSumOfFintype α n).symm P : Multiset α) = ∑ a, ((P : α → ℕ) a) • {a} := by
  obtain ⟨P, hP⟩ := P
  change Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm P) = Multiset.sum _
  ext a
  rw [Multiset.count_sum]
  simp [Multiset.count_singleton]

end Sym

