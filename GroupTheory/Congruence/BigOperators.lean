/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.GroupTheory.Congruence.Basic

/-!
# Interactions between `∑, ∏` and `(Add)Con`

-/

public section

namespace Con

/-- Multiplicative congruence relations preserve product indexed by a list. -/
@[to_additive /-- Additive congruence relations preserve sum indexed by a list. -/]
/-
**Con.list_prod** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_2} [inst : MulOneClass M] (c : Con M) {l : Li
st ι} {f g : ι → M},   (∀ x ∈ l, c (f x) (g x)) → c (List.map f l).prod (List.ma
p g l).prod
参数：c : Con M；∀ x ∈ l, c (f x) (g x)；List.map f l；List.map g l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `Con.refl`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) (x : M), c x x
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `Con.mul`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {w x y z : M}, c w 
x → c y z → c (w * y) (x * z)

--- 原说明 ---
Multiplicative congruence relations preserve product indexed by a list.
-/
protected theorem list_prod {ι M : Type*} [MulOneClass M] (c : Con M) {l : List ι} {f g : ι → M}
    (h : ∀ x ∈ l, c (f x) (g x)) :
    c (l.map f).prod (l.map g).prod := by
  induction l with
  | nil =>
    simpa only [List.map_nil, List.prod_nil] using c.refl 1
  | cons x xs ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
    exact c.mul (h _ <| .head _) <| ih fun k hk ↦ h _ (.tail _ hk)

@[to_additive (attr := simp, norm_cast)]
/-
**Con.coe_listProd** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_2} [inst : MulOneClass M] (c : Con M) (l : Li
st ι) (f : ι → M),   ↑(List.map f l).prod = (List.map (fun i => ↑(f i)) l).prod
参数：c : Con M；l : List ι；f : ι → M；List.map f l；List.map (fun i => ↑(f i)) l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
-/
protected theorem coe_listProd {ι M : Type*} [MulOneClass M] (c : Con M)
    (l : List ι) (f : ι → M) :
    (↑(l.map f).prod : c.Quotient) = (l.map fun i => (f i : c.Quotient)).prod := by
  induction l with simp [*]

/-- Multiplicative congruence relations preserve product indexed by a multiset. -/
@[to_additive /-- Additive congruence relations preserve sum indexed by a multiset. -/]
/-
**Con.multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_2} [inst : CommMonoid M] (c : Con M) {s : Mul
tiset ι} {f g : ι → M},   (∀ x ∈ s, c (f x) (g x)) → c (Multiset.map f s).prod (
Multiset.map g s).prod
参数：c : Con M；∀ x ∈ s, c (f x) (g x)；Multiset.map f s；Multiset.map g s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.list_prod`：∀ {ι : Type u_1} {M : Type u_2} [inst : MulOneClass M] (c
 : Con M) {l : List ι} {f g : ι → M},   (∀ x ∈ l, c (f x) (g x)) → c (List.map f
 l)…

--- 原说明 ---
Multiplicative congruence relations preserve product indexed by a multiset.
-/
protected theorem multiset_prod {ι M : Type*} [CommMonoid M] (c : Con M) {s : Multiset ι}
    {f g : ι → M} (h : ∀ x ∈ s, c (f x) (g x)) :
    c (s.map f).prod (s.map g).prod := by
  rcases s; simpa using c.list_prod h

@[to_additive (attr := simp, norm_cast)]
/-
**Con.coe_multisetProd** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_2} [inst : CommMonoid M] (c : Con M) (s : Mul
tiset ι) (f : ι → M),   ↑(Multiset.map f s).prod = (Multiset.map (fun i => ↑(f i
)) s).prod
参数：c : Con M；s : Multiset ι；f : ι → M；Multiset.map f s；Multiset.map (fun i => ↑(
f i)) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `map_multiset_prod`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst 
: CommMonoid M] [inst_1 : CommMonoid N] [inst_2 : FunLike F M N]   [MonoidHomCla
ss F M …
-/
protected theorem coe_multisetProd {ι M : Type*} [CommMonoid M] (c : Con M)
    (s : Multiset ι) (f : ι → M) :
    (↑(s.map f).prod : c.Quotient) = (s.map fun i => (f i : c.Quotient)).prod := by
  simpa using map_multiset_prod c.mk' (s.map f)

/-- Multiplicative congruence relations preserve finite product. -/
@[to_additive /-- Additive congruence relations preserve finite sum. -/]
/-
**Con.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_2} [inst : CommMonoid M] (c : Con M) (s : Fin
set ι) {f g : ι → M},   (∀ i ∈ s, c (f i) (g i)) → c (s.prod f) (s.prod g)
参数：c : Con M；s : Finset ι；∀ i ∈ s, c (f i) (g i)；s.prod f；s.prod g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.multiset_prod`：∀ {ι : Type u_1} {M : Type u_2} [inst : CommMonoid M]
 (c : Con M) {s : Multiset ι} {f g : ι → M},   (∀ x ∈ s, c (f x) (g x)) → c (Mul
tiset.m…

--- 原说明 ---
Multiplicative congruence relations preserve finite product.
-/
protected theorem finsetProd {ι M : Type*} [CommMonoid M] (c : Con M) (s : Finset ι)
    {f g : ι → M} (h : ∀ i ∈ s, c (f i) (g i)) :
    c (s.prod f) (s.prod g) :=
  c.multiset_prod h

@[to_additive (attr := simp, norm_cast)]
/-
**Con.coe_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_2} [inst : CommMonoid M] (c : Con M) (s : Fin
set ι) (f : ι → M),   ↑(s.prod f) = ∏ i ∈ s, ↑(f i)
参数：c : Con M；s : Finset ι；f : ι → M；s.prod f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
protected theorem coe_finsetProd {ι M : Type*} [CommMonoid M] (c : Con M) (s : Finset ι)
    (f : ι → M) :
    (↑(s.prod f) : c.Quotient) = s.prod fun i => (f i : c.Quotient) :=
  map_prod c.mk' f s

@[to_additive]
/-
**Con.finsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {ι : Type u_1} {β : Type u_2} {M : Type u_3} [inst : CommMonoid M] [inst
_1 : Zero β] (c : Con M) (h h' : ι → β → M)   {f g : ι →₀ β},   (∀ (i : ι), c (h
 i 0) 1) →     (∀ (i : ι), c (h' i 0) 1) → (∀ (i : ι), c (h i (f i)) (h' i (g i)
)) → c (f.prod h) (g.prod h')
参数：c : Con M；h h' : ι → β → M；∀ (i : ι), c (h i 0) 1；∀ (i : ι), c (h' i 0) 1；∀ (
i : ι), c (h i (f i)) (h' i (g i))；f.prod h；g.prod h'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_finsuppProd`：map_finsuppProd [Zero M] [CommMonoid N] [CommMonoid P] 
{H : Type*} [FunLike H N P] [MonoidHomClass H N P] (h : H) (f : α ->₀ M) (g : α 
-> M …
· 使用定理 `Finsupp.prod_congr_of_eq_on_union`：prod_congr_of_eq_on_union [DecidableE
q α] {f1 f2 : α ->₀ M} {g1 g2 : α -> M -> N} (h : forall x in f1.support union f
2.support, g1 x (f1 x) …
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
protected theorem finsuppProd {ι : Type*} {β : Type*} {M : Type*}
    [CommMonoid M] [Zero β]
    (c : Con M) (h : ι → β → M) (h' : ι → β → M)
    {f g : ι →₀ β} (hf : ∀ i, c (h i 0) 1) (hf' : ∀ i, c (h' i 0) 1)
    (H : ∀ i, c (h i (f i)) (h' i (g i))) :
    c (f.prod h) (g.prod h') := by
  refine Quotient.exact (show c.mk' _ = c.mk' _ from ?_)
  rw [map_finsuppProd, map_finsuppProd]
  classical
  exact Finsupp.prod_congr_of_eq_on_union
    (fun _ _ => Quotient.sound <| H _)
    (fun _ _ => Quotient.sound <| hf _) (fun _ _ => Quotient.sound <| hf' _)

@[to_additive (attr := simp, norm_cast)]
/-
**Con.coe_finsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {ι : Type u_1} {β : Type u_2} {M : Type u_3} [inst : CommMonoid M] [inst
_1 : Zero β] (c : Con M) (h : ι → β → M)   (f : ι →₀ β), ↑(f.prod h) = f.prod fu
n i b => ↑(h i b)
参数：c : Con M；h : ι → β → M；f : ι →₀ β；f.prod h；h i b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finsuppProd`：map_finsuppProd [Zero M] [CommMonoid N] [CommMonoid P] 
{H : Type*} [FunLike H N P] [MonoidHomClass H N P] (h : H) (f : α ->₀ M) (g : α 
-> M …
-/
protected theorem coe_finsuppProd {ι : Type*} {β : Type*} {M : Type*}
    [CommMonoid M] [Zero β] (c : Con M) (h : ι → β → M) (f : ι →₀ β) :
    (↑(f.prod h) : c.Quotient) = f.prod fun i b => (h i b : c.Quotient) :=
  map_finsuppProd c.mk' f h

@[to_additive]
/-
**Con.dfinsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} {M : Type u_3} [inst : DecidableEq ι] 
[inst_1 : CommMonoid M]   [inst_2 : (i : ι) → Zero (β i)] [inst_3 : (i : ι) → (y
 : β i) → Decidable (y ≠ 0)] (c : Con M)   (h h' : (i : ι) → β i → M) {f g : Π₀ 
(i : ι), β i},   (∀ (i : ι), c (h i 0) 1) →     (∀ (i : ι), c (h' i 0) 1) → (∀ (
i : ι), c (h i (f i)) (h' i (g i))) → c (f.prod h) (g.prod h')
参数：i : ι；β i；i : ι；y : β i；y ≠ 0；c : Con M；h h' : (i : ι) → β i → M；i : ι；∀ (i :
 ι), c (h i 0) 1；∀ (i : ι), c (h' i 0) 1；∀ (i : ι), c (h i (f i)) (h' i (g i))；f
.prod h；g.prod h'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_dfinsuppProd`：∀ {ι : Type u} {β : ι → Type v} [inst : DecidableEq ι]
 {R : Type u_1} {S : Type u_2} {H : Type u_3}   [inst_1 : (i : ι) → Zero (β i)] 
[inst_…
· 使用定理 `DFinsupp.prod_congr_of_eq_on_union`：prod_congr_of_eq_on_union [forall i,
 Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)] [CommMonoid γ] {f1 f2 : 
Π₀ i, β i} {g1 g2 : (i :…
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
protected theorem dfinsuppProd {ι : Type*} {β : ι → Type*} {M : Type*}
    [DecidableEq ι] [CommMonoid M] [∀ i, Zero (β i)] [∀ i (y : β i), Decidable (y ≠ 0)]
    (c : Con M) (h : (i : ι) → β i → M) (h' : (i : ι) → β i → M)
    {f g : Π₀ i, β i} (hf : ∀ i, c (h i 0) 1) (hf' : ∀ i, c (h' i 0) 1)
    (H : ∀ i, c (h i (f i)) (h' i (g i))) :
    c (f.prod h) (g.prod h') := by
  refine Quotient.exact (show c.mk' _ = c.mk' _ from ?_)
  rw [map_dfinsuppProd, map_dfinsuppProd]
  exact DFinsupp.prod_congr_of_eq_on_union
    (fun _ _ => Quotient.sound <| H _)
    (fun _ _ => Quotient.sound <| hf _) (fun _ _ => Quotient.sound <| hf' _)

@[to_additive (attr := simp, norm_cast)]
/-
**Con.coe_dfinsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} {M : Type u_3} [inst : DecidableEq ι] 
[inst_1 : CommMonoid M]   [inst_2 : (i : ι) → Zero (β i)] [inst_3 : (i : ι) → (y
 : β i) → Decidable (y ≠ 0)] (c : Con M) (h : (i : ι) → β i → M)   (f : Π₀ (i : 
ι), β i), ↑(f.prod h) = f.prod fun i b => ↑(h i b)
参数：i : ι；β i；i : ι；y : β i；y ≠ 0；c : Con M；h : (i : ι) → β i → M；f : Π₀ (i : ι),
 β i；f.prod h；h i b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_dfinsuppProd`：∀ {ι : Type u} {β : ι → Type v} [inst : DecidableEq ι]
 {R : Type u_1} {S : Type u_2} {H : Type u_3}   [inst_1 : (i : ι) → Zero (β i)] 
[inst_…
-/
protected theorem coe_dfinsuppProd {ι : Type*} {β : ι → Type*} {M : Type*}
    [DecidableEq ι] [CommMonoid M] [∀ i, Zero (β i)] [∀ i (y : β i), Decidable (y ≠ 0)]
    (c : Con M) (h : (i : ι) → β i → M) (f : Π₀ i, β i) :
    (↑(f.prod h) : c.Quotient) = f.prod fun i b => (h i b : c.Quotient) :=
  map_dfinsuppProd c.mk' f h
/-
**Con._root_.AddCon.dfinsuppSumAddHom** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.AddCon.dfinsuppSumAddHom {ι : Type*} {β : ι → Type*} {M : Type*}
    [DecidableEq ι] [AddCommMonoid M] [∀ i, AddCommMonoid (β i)]
    (c : AddCon M) (h : (i : ι) → β i →+ M) (h' : (i : ι) → β i →+ M) {f g : Π₀ i, β i}
    (H : ∀ i, c (h i (f i)) (h' i (g i))) :
    c (f.sumAddHom h) (g.sumAddHom h') := by
  classical
  simp_rw [DFinsupp.sumAddHom_apply]
  exact c.dfinsuppSum _ _
    (bot_le (a := c) <| map_zero <| h ·) (bot_le (a := c) <| map_zero <| h' ·) H

@[simp, norm_cast]
/-
**Con._root_.AddCon.coe_dfinsuppSumAddHom** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.AddCon.coe_dfinsuppSumAddHom {ι : Type*} {β : ι → Type*} {M : Type*}
    [DecidableEq ι] [AddCommMonoid M] [∀ i, AddCommMonoid (β i)]
    (c : AddCon M) (h : (i : ι) → β i →+ M) (f : Π₀ i, β i) :
    (↑(f.sumAddHom h) : c.Quotient) = f.sumAddHom fun i => (AddCon.mk' c).comp (h i) := by
  classical
  simp_rw [← AddCon.coe_mk', DFinsupp.sumAddHom_apply, map_dfinsuppSum]
  rfl

@[deprecated (since := "2026-04-08")]
protected alias _root_.AddCon.finset_sum := AddCon.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
protected alias finset_prod := Con.finsetProd

end Con

