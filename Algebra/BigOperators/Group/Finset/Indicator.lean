/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Order.CompleteLattice.Finset

/-!
# Interaction of big operators with indicator functions
-/

public section

namespace Finset

variable {ι κ α β : Type*} [CommMonoid β]

open Set

/-- Consider a product of `g i (f i)` over a finset.  Suppose `g` is a function such as
`n ↦ (· ^ n)`, which maps a second argument of `1` to `1`. Then if `f` is replaced by the
corresponding multiplicative indicator function, the finset may be replaced by a possibly larger
finset without changing the value of the product. -/
@[to_additive /-- Consider a sum of `g i (f i)` over a finset.  Suppose `g` is a function such as
`n ↦ (n • ·)`, which maps a second argument of `0` to `0` (or a weighted sum of `f i * h i` or
`f i • h i`, where `f` gives the weights that are multiplied by some other function `h`). Then if
`f` is replaced by the corresponding indicator function, the finset may be replaced by a possibly
larger finset without changing the value of the sum. -/]
/-
**Finset.prod_mulIndicator_subset_of_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_mulIndicator_subset_of_eq_one [One α] (f : ι -> α) (g : ι -> α -> β) 
{s t : Finset ι} (h : s subseteq t) (hg : forall a, g a 1 = 1) : ∏ i in t, g i (
mulIndicator ↑s f i) = ∏ i in s, g i (f i)
参数：f : ι -> α；g : ι -> α -> β；h : s subseteq t；hg : forall a, g a 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
-/
lemma prod_mulIndicator_subset_of_eq_one [One α] (f : ι → α) (g : ι → α → β) {s t : Finset ι}
    (h : s ⊆ t) (hg : ∀ a, g a 1 = 1) :
    ∏ i ∈ t, g i (mulIndicator ↑s f i) = ∏ i ∈ s, g i (f i) := by
  calc
    _ = ∏ i ∈ s, g i (mulIndicator ↑s f i) := by rw [prod_subset h fun i _ hn ↦ by simp [hn, hg]]
    _ = _ := prod_congr rfl fun i hi ↦ congr_arg _ <| mulIndicator_of_mem hi f

/-- Taking the product of an indicator function over a possibly larger finset is the same as
taking the original function over the original finset. -/
@[to_additive /-- Summing an indicator function over a possibly larger `Finset` is the same as
summing the original function over the original finset. -/]
/-
**Finset.prod_mulIndicator_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_mulIndicator_subset (f : ι -> β) {s t : Finset ι} (h : s subseteq t) 
: ∏ i in t, mulIndicator (↑s) f i = ∏ i in s, f i
参数：f : ι -> β；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_mulIndicator_subset_of_eq_one`：prod_mulIndicator_subset_of_e
q_one [One α] (f : ι -> α) (g : ι -> α -> β) {s t : Finset ι} (h : s subseteq t)
 (hg : forall a, g a 1 = 1) : ∏…
-/
lemma prod_mulIndicator_subset (f : ι → β) {s t : Finset ι} (h : s ⊆ t) :
    ∏ i ∈ t, mulIndicator (↑s) f i = ∏ i ∈ s, f i :=
  prod_mulIndicator_subset_of_eq_one _ (fun _ ↦ id) h fun _ ↦ rfl

@[to_additive]
/-
**Finset.prod_mulIndicator_eq_prod_filter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_mulIndicator_eq_prod_filter (s : Finset ι) (f : ι -> κ -> β) (t : ι -
> Set κ) (g : ι -> κ) [DecidablePred fun i => g i in t i] : ∏ i in s, mulIndicat
or (t i) (f i) (g i) = ∏ i in s with g i in t i, f i (g i)
参数：s : Finset ι；f : ι -> κ -> β；t : ι -> Set κ；g : ι -> κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_filter_mul_prod_filter_not`：prod_filter_mul_prod_filter_not 
(s : Finset ι) (p : ι -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] (f
 : ι -> M) : (∏ x in s with …
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.prod_eq_one`：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s,
 f x = 1
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma prod_mulIndicator_eq_prod_filter (s : Finset ι) (f : ι → κ → β) (t : ι → Set κ) (g : ι → κ)
    [DecidablePred fun i ↦ g i ∈ t i] :
    ∏ i ∈ s, mulIndicator (t i) (f i) (g i) = ∏ i ∈ s with g i ∈ t i, f i (g i) := by
  refine (prod_filter_mul_prod_filter_not s (fun i ↦ g i ∈ t i) _).symm.trans <|
     Eq.trans (congr_arg₂ (· * ·) ?_ ?_) (mul_one _)
  · exact prod_congr rfl fun x hx ↦ mulIndicator_of_mem (mem_filter.1 hx).2 _
  · exact prod_eq_one fun x hx ↦ mulIndicator_of_notMem (mem_filter.1 hx).2 _

@[to_additive]
/-
**Finset.prod_mulIndicator_eq_prod_inter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_mulIndicator_eq_prod_inter [DecidableEq ι] (s t : Finset ι) (f : ι ->
 β) : ∏ i in s, (t : Set ι).mulIndicator f i = ∏ i in s inter t, f i
参数：s t : Finset ι；f : ι -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_mem_eq_inter`：filter_mem_eq_inter {s t : Finset α} [forall
 i, Decidable (i in t)] : (s.filter fun i => i in t) = s inter t
· 使用引理 `Finset.prod_mulIndicator_eq_prod_filter`：prod_mulIndicator_eq_prod_filte
r (s : Finset ι) (f : ι -> κ -> β) (t : ι -> Set κ) (g : ι -> κ) [DecidablePred 
fun i => g i in t i] : ∏ i in…
-/
lemma prod_mulIndicator_eq_prod_inter [DecidableEq ι] (s t : Finset ι) (f : ι → β) :
    ∏ i ∈ s, (t : Set ι).mulIndicator f i = ∏ i ∈ s ∩ t, f i := by
  rw [← filter_mem_eq_inter, prod_mulIndicator_eq_prod_filter]; rfl

@[to_additive]
/-
**Finset.mulIndicator_prod** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mulIndicator_prod (s : Finset ι) (t : Set κ) (f : ι -> κ -> β) : mulIndica
tor t (∏ i in s, f i) = ∏ i in s, mulIndicator t (f i)
参数：s : Finset ι；t : Set κ；f : ι -> κ -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
lemma mulIndicator_prod (s : Finset ι) (t : Set κ) (f : ι → κ → β) :
    mulIndicator t (∏ i ∈ s, f i) = ∏ i ∈ s, mulIndicator t (f i) :=
  map_prod (mulIndicatorHom _ _) _ _

@[to_additive]
/-
**Finset.mulIndicator_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mulIndicator_biUnion (s : Finset ι) (t : ι -> Set κ) {f : κ -> β} (hs : (s
 : Set ι).PairwiseDisjoint t) : mulIndicator (⋃ i in s, t i) f = fun a => ∏ i in
 s, mulIndicator (t i) f a
参数：s : Finset ι；t : ι -> Set κ；hs : (s : Set ι).PairwiseDisjoint t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用引理 `Set.mulIndicator_empty`：mulIndicator_empty (f : α -> M) : mulIndicator (
∅ : Set α) f = fun _ => 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.set_biUnion_insert`：set_biUnion_insert (a : α) (s : Finset α) (t 
: α -> Set β) : ⋃ x in insert a s, t x = t a union ⋃ x in s, t x
· 使用定理 `Set.mulIndicator_union_of_notMem_inter`：mulIndicator_union_of_notMem_int
er (h : a ∉ s inter t) (f : α -> M) : mulIndicator (s union t) f a = mulIndicato
r s f a * mulIndicator t f a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_iUnion₂_right`：disjoint_iUnion₂_right {s : Set α} {t : fora
ll i, κ i -> Set α} : Disjoint s (⋃ (i) (j), t i j) ↔ forall i j, Disjoint s (t 
i j)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.pairwiseDisjoint_insert_of_notMem`：pairwiseDisjoint_insert_of_notMem
 {i : ι} (hi : i ∉ s) : (insert i s).PairwiseDisjoint f ↔ s.PairwiseDisjoint f ∧
 forall j in s, Disjoint (f…
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finset.coe_cons`：coe_cons {a s h} : (@cons α a s h : Set α) = insert a (
s : Set α)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma mulIndicator_biUnion (s : Finset ι) (t : ι → Set κ) {f : κ → β}
    (hs : (s : Set ι).PairwiseDisjoint t) :
    mulIndicator (⋃ i ∈ s, t i) f = fun a ↦ ∏ i ∈ s, mulIndicator (t i) f a := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    ext j
    rw [coe_cons, Set.pairwiseDisjoint_insert_of_notMem (Finset.mem_coe.not.2 hi)] at hs
    classical
    rw [prod_cons, cons_eq_insert, set_biUnion_insert, mulIndicator_union_of_notMem_inter, ih hs.1]
    exact (Set.disjoint_iff.mp (Set.disjoint_iUnion₂_right.mpr hs.2) ·)

@[to_additive]
/-
**Finset.mulIndicator_biUnion_apply** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mulIndicator_biUnion_apply (s : Finset ι) (t : ι -> Set κ) {f : κ -> β} (h
 : (s : Set ι).PairwiseDisjoint t) (x : κ) : mulIndicator (⋃ i in s, t i) f x = 
∏ i in s, mulIndicator (t i) f x
参数：s : Finset ι；t : ι -> Set κ；h : (s : Set ι).PairwiseDisjoint t；x : κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mulIndicator_biUnion`：mulIndicator_biUnion (s : Finset ι) (t : ι 
-> Set κ) {f : κ -> β} (hs : (s : Set ι).PairwiseDisjoint t) : mulIndicator (⋃ i
 in s, t i) f = f…
-/
lemma mulIndicator_biUnion_apply (s : Finset ι) (t : ι → Set κ) {f : κ → β}
    (h : (s : Set ι).PairwiseDisjoint t) (x : κ) :
    mulIndicator (⋃ i ∈ s, t i) f x = ∏ i ∈ s, mulIndicator (t i) f x := by
  rw [mulIndicator_biUnion s t h]

end Finset

