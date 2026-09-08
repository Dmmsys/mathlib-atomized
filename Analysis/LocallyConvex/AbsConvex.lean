/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.Convex.TotallyBounded
public import Mathlib.Analysis.LocallyConvex.Bounded

/-!
# Absolutely convex sets

A set `s` in a commutative monoid `E` is called absolutely convex or disked if it is convex and
balanced. The importance of absolutely convex sets comes from the fact that every locally convex
topological vector space has a basis consisting of absolutely convex sets.

## Main definitions

* `absConvexHull`: the absolutely convex hull of a set `s` is the smallest absolutely convex set
  containing `s`;
* `closedAbsConvexHull`: the closed absolutely convex hull of a set `s` is the smallest absolutely
  convex set containing `s`;

## Main statements

* `absConvexHull_eq_convexHull_balancedHull`: when the locally convex space is a module, the
  absolutely convex hull of a set `s` equals the convex hull of the balanced hull of `s`;
* `convexHull_union_neg_eq_absConvexHull`: the convex hull of `s ∪ -s` is the absolutely convex hull
  of `s`;
* `closedAbsConvexHull_closure_eq_closedAbsConvexHull` : the closed absolutely convex hull of the
  closure of `s` equals the closed absolutely convex hull of `s`;

## Tags

disks, convex, balanced
-/

@[expose] public section

open NormedField Set

open NNReal Pointwise Topology

variable {𝕜 E : Type*}

section AbsolutelyConvex

variable (𝕜) [SeminormedRing 𝕜] [SMul 𝕜 E] [AddCommMonoid E] [PartialOrder 𝕜]

/-- A set is absolutely convex if it is balanced and convex. -/
/-
**AbsConvex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AbsConvex (s : Set E) : Prop
参数：s : Set E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is absolutely convex if it is balanced and convex.
-/
def AbsConvex (s : Set E) : Prop := Balanced 𝕜 s ∧ Convex 𝕜 s

variable {𝕜}
/-
**AbsConvex.empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AbsConvex.empty : AbsConvex 𝕜 (∅ : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `balanced_empty`：balanced_empty : Balanced 𝕜 (∅ : Set E)
· 使用定理 `convex_empty`：convex_empty : Convex 𝕜 (∅ : Set E)
-/
theorem AbsConvex.empty : AbsConvex 𝕜 (∅ : Set E) := ⟨balanced_empty, convex_empty⟩
/-
**AbsConvex.univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AbsConvex.univ : AbsConvex 𝕜 (univ : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `balanced_univ`：balanced_univ : Balanced 𝕜 (univ : Set E)
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
-/
theorem AbsConvex.univ : AbsConvex 𝕜 (univ : Set E) := ⟨balanced_univ, convex_univ⟩
/-
**AbsConvex.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AbsConvex.inter {s t : Set E} (hs : AbsConvex 𝕜 s) (ht : AbsConvex 𝕜 t) : 
AbsConvex 𝕜 (s inter t)
参数：hs : AbsConvex 𝕜 s；ht : AbsConvex 𝕜 t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Balanced.inter`：Balanced.inter (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) :
 Balanced 𝕜 (A inter B)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem AbsConvex.inter {s t : Set E} (hs : AbsConvex 𝕜 s) (ht : AbsConvex 𝕜 t) :
    AbsConvex 𝕜 (s ∩ t) := ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩
/-
**AbsConvex.sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AbsConvex.sInter {S : Set (Set E)} (h : forall s in S, AbsConvex 𝕜 s) : Ab
sConvex 𝕜 (⋂₀ S)
参数：Set E；h : forall s in S, AbsConvex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Balanced.sInter`：Balanced.sInter {S : Set (Set E)} (h : forall s in S, B
alanced 𝕜 s) : Balanced 𝕜 (⋂₀ S)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `convex_sInter`：convex_sInter {S : Set (Set E)} (h : forall s in S, Conve
x 𝕜 s) : Convex 𝕜 (⋂₀ S)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem AbsConvex.sInter {S : Set (Set E)} (h : ∀ s ∈ S, AbsConvex 𝕜 s) : AbsConvex 𝕜 (⋂₀ S) :=
  ⟨.sInter fun s hs => (h s hs).1, convex_sInter fun s hs => (h s hs).2⟩
/-
**AbsConvex.iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AbsConvex.iInter {ι : Sort*} {s : ι -> Set E} (h : forall i, AbsConvex 𝕜 (
s i)) : AbsConvex 𝕜 (⋂ i, s i)
参数：h : forall i, AbsConvex 𝕜 (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsConvex.sInter`：AbsConvex.sInter {S : Set (Set E)} (h : forall s in S,
 AbsConvex 𝕜 s) : AbsConvex 𝕜 (⋂₀ S)
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem AbsConvex.iInter {ι : Sort*} {s : ι → Set E} (h : ∀ i, AbsConvex 𝕜 (s i)) :
    AbsConvex 𝕜 (⋂ i, s i) :=
  sInter_range s ▸ AbsConvex.sInter <| forall_mem_range.2 h
/-
**AbsConvex.iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AbsConvex.iInter {ι : Sort*} {s : ι -> Set E} (h : forall i, AbsConvex 𝕜 (
s i)) : AbsConvex 𝕜 (⋂ i, s i)
参数：h : forall i, AbsConvex 𝕜 (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsConvex.sInter`：AbsConvex.sInter {S : Set (Set E)} (h : forall s in S,
 AbsConvex 𝕜 s) : AbsConvex 𝕜 (⋂₀ S)
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem AbsConvex.iInter₂ {ι : Sort*} {κ : ι → Sort*} {f : ∀ i, κ i → Set E}
    (h : ∀ i j, AbsConvex 𝕜 (f i j)) : AbsConvex 𝕜 (⋂ (i) (j), f i j) :=
  AbsConvex.iInter fun _ => (AbsConvex.iInter fun _ => h _ _)

variable (𝕜)

/-- The absolute convex hull of a set `s` is the minimal absolute convex set that includes `s`. -/
@[simps! isClosed]
/-
**absConvexHull** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：absConvexHull : ClosureOperator (Set E)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AbsConvex.sInter`：AbsConvex.sInter {S : Set (Set E)} (h : forall s in S,
 AbsConvex 𝕜 s) : AbsConvex 𝕜 (⋂₀ S)

--- 原说明 ---
The absolute convex hull of a set `s` is the minimal absolute convex set that in
cludes `s`.
-/
def absConvexHull : ClosureOperator (Set E) :=
  .ofCompletePred (AbsConvex 𝕜) fun _ ↦ .sInter

variable {𝕜} {s : Set E}
/-
**subset_absConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_absConvexHull : s subseteq absConvexHull 𝕜 s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.le_closure`：le_closure (x : α) : x <= c x
-/
theorem subset_absConvexHull : s ⊆ absConvexHull 𝕜 s :=
  (absConvexHull 𝕜).le_closure s
/-
**absConvex_absConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absConvex_absConvexHull : AbsConvex 𝕜 (absConvexHull 𝕜 s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.isClosed_closure`：∀ {α : Type u_1} [inst : Preorder α] (
c : ClosureOperator α) (x : α), c.IsClosed (c x)
-/
theorem absConvex_absConvexHull : AbsConvex 𝕜 (absConvexHull 𝕜 s) :=
  (absConvexHull 𝕜).isClosed_closure s
/-
**balanced_absConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balanced_absConvexHull : Balanced 𝕜 (absConvexHull 𝕜 s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `absConvex_absConvexHull`：absConvex_absConvexHull : AbsConvex 𝕜 (absConve
xHull 𝕜 s)
-/
theorem balanced_absConvexHull : Balanced 𝕜 (absConvexHull 𝕜 s) :=
  absConvex_absConvexHull.1
/-
**convex_absConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_absConvexHull : Convex 𝕜 (absConvexHull 𝕜 s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `absConvex_absConvexHull`：absConvex_absConvexHull : AbsConvex 𝕜 (absConve
xHull 𝕜 s)
-/
theorem convex_absConvexHull : Convex 𝕜 (absConvexHull 𝕜 s) :=
  absConvex_absConvexHull.2

set_option backward.isDefEq.respectTransparency false in
variable (𝕜 s) in
/-
**absConvexHull_eq_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absConvexHull_eq_iInter : absConvexHull 𝕜 s = ⋂ (t : Set E) (_ : s subsete
q t) (_ : AbsConvex 𝕜 t), t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbsConvex.sInter`：AbsConvex.sInter {S : Set (Set E)} (h : forall s in S,
 AbsConvex 𝕜 s) : AbsConvex 𝕜 (⋂₀ S)
· 使用定理 `ClosureOperator.ofCompletePred_apply`：∀ {α : Type u_1} [inst : CompleteL
attice α] (p : α → Prop) (hsinf : ∀ (s : Set α), (∀ a ∈ s, p a) → p (sInf s)) (a
 : α),   (ClosureOperator.…
· 使用定理 `Set.iInter_subtype`：iInter_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋂ x : { x // p x }, s x = ⋂ (x) (hx : p x), s ⟨x, hx⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_and`：iInter_and {p q : Prop} (s : p ∧ q -> Set α) : ⋂ h, s h 
= ⋂ (hp) (hq), s ⟨hp, hq⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem absConvexHull_eq_iInter :
    absConvexHull 𝕜 s = ⋂ (t : Set E) (_ : s ⊆ t) (_ : AbsConvex 𝕜 t), t := by
  simp [absConvexHull, iInter_subtype, iInter_and]

variable {t : Set E} {x : E}
/-
**mem_absConvexHull_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_absConvexHull_iff : x in absConvexHull 𝕜 s ↔ forall t, s subseteq t ->
 AbsConvex 𝕜 t -> x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `absConvexHull_eq_iInter`：absConvexHull_eq_iInter : absConvexHull 𝕜 s = ⋂
 (t : Set E) (_ : s subseteq t) (_ : AbsConvex 𝕜 t), t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_absConvexHull_iff : x ∈ absConvexHull 𝕜 s ↔ ∀ t, s ⊆ t → AbsConvex 𝕜 t → x ∈ t := by
  simp_rw [absConvexHull_eq_iInter, mem_iInter]
/-
**absConvexHull_min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absConvexHull_min : s subseteq t -> AbsConvex 𝕜 t -> absConvexHull 𝕜 s sub
seteq t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ClosureOperator.closure_min`：closure_min (hxy : x <= y) (hy : c.IsClosed
 y) : c x <= y
-/
theorem absConvexHull_min : s ⊆ t → AbsConvex 𝕜 t → absConvexHull 𝕜 s ⊆ t :=
  (absConvexHull 𝕜).closure_min
/-
**AbsConvex.absConvexHull_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AbsConvex.absConvexHull_subset_iff (ht : AbsConvex 𝕜 t) : absConvexHull 𝕜 
s subseteq t ↔ s subseteq t
参数：ht : AbsConvex 𝕜 t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.IsClosed.closure_le_iff`：∀ {α : Type u_1} [inst : Preord
er α] {c : ClosureOperator α} {x y : α}, c.IsClosed y → (c x ≤ y ↔ x ≤ y)
-/
theorem AbsConvex.absConvexHull_subset_iff (ht : AbsConvex 𝕜 t) : absConvexHull 𝕜 s ⊆ t ↔ s ⊆ t :=
  (show (absConvexHull 𝕜).IsClosed t from ht).closure_le_iff

@[mono, gcongr]
/-
**absConvexHull_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absConvexHull_mono (hst : s subseteq t) : absConvexHull 𝕜 s subseteq absCo
nvexHull 𝕜 t
参数：hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.monotone`：monotone : Monotone c
-/
theorem absConvexHull_mono (hst : s ⊆ t) : absConvexHull 𝕜 s ⊆ absConvexHull 𝕜 t :=
  (absConvexHull 𝕜).monotone hst
/-
**absConvexHull_eq_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：absConvexHull_eq_self : absConvexHull 𝕜 s = s ↔ AbsConvex 𝕜 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ClosureOperator.isClosed_iff`：∀ {α : Type u_1} [inst : Preorder α] (self
 : ClosureOperator α) {x : α}, self.IsClosed x ↔ self.toFun x = x
-/
lemma absConvexHull_eq_self : absConvexHull 𝕜 s = s ↔ AbsConvex 𝕜 s :=
  (absConvexHull 𝕜).isClosed_iff.symm

alias ⟨_, AbsConvex.absConvexHull_eq⟩ := absConvexHull_eq_self

@[simp]
/-
**absConvexHull_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absConvexHull_univ : absConvexHull 𝕜 (univ : Set E) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.closure_top`：closure_top : c ⊤ = ⊤
-/
theorem absConvexHull_univ : absConvexHull 𝕜 (univ : Set E) = univ :=
  ClosureOperator.closure_top (absConvexHull 𝕜)

@[simp]
/-
**absConvexHull_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absConvexHull_empty : absConvexHull 𝕜 (∅ : Set E) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsConvex.absConvexHull_eq`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semi
normedRing 𝕜] [inst_1 : SMul 𝕜 E] [inst_2 : AddCommMonoid E]   [inst_3 : Partial
Order 𝕜] {s : Se…
· 使用定理 `AbsConvex.empty`：AbsConvex.empty : AbsConvex 𝕜 (∅ : Set E)
-/
theorem absConvexHull_empty : absConvexHull 𝕜 (∅ : Set E) = ∅ :=
  AbsConvex.empty.absConvexHull_eq

@[simp]
/-
**absConvexHull_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absConvexHull_eq_empty : absConvexHull 𝕜 s = ∅ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `subset_absConvexHull`：subset_absConvexHull : s subseteq absConvexHull 𝕜 
s
· 使用定理 `absConvexHull_empty`：absConvexHull_empty : absConvexHull 𝕜 (∅ : Set E) =
 ∅
-/
theorem absConvexHull_eq_empty : absConvexHull 𝕜 s = ∅ ↔ s = ∅ := by
  constructor
  · intro h
    rw [← Set.subset_empty_iff, ← h]
    exact subset_absConvexHull
  · rintro rfl
    exact absConvexHull_empty

@[simp]
/-
**absConvexHull_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absConvexHull_nonempty : (absConvexHull 𝕜 s).Nonempty ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `absConvexHull_eq_empty`：absConvexHull_eq_empty : absConvexHull 𝕜 s = ∅ ↔
 s = ∅
-/
theorem absConvexHull_nonempty : (absConvexHull 𝕜 s).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, nonempty_iff_ne_empty, Ne, Ne]
  exact not_congr absConvexHull_eq_empty

protected alias ⟨_, Set.Nonempty.absConvexHull⟩ := absConvexHull_nonempty

variable [TopologicalSpace E]
/-
**absConvex_closed_sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absConvex_closed_sInter {S : Set (Set E)} (h : forall s in S, AbsConvex 𝕜 
s ∧ IsClosed s) : AbsConvex 𝕜 (⋂₀ S) ∧ IsClosed (⋂₀ S)
参数：Set E；h : forall s in S, AbsConvex 𝕜 s ∧ IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsConvex.sInter`：AbsConvex.sInter {S : Set (Set E)} (h : forall s in S,
 AbsConvex 𝕜 s) : AbsConvex 𝕜 (⋂₀ S)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isClosed_sInter`：isClosed_sInter {s : Set (Set X)} : (forall t in s, IsC
losed t) -> IsClosed (⋂₀ s)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem absConvex_closed_sInter {S : Set (Set E)} (h : ∀ s ∈ S, AbsConvex 𝕜 s ∧ IsClosed s) :
    AbsConvex 𝕜 (⋂₀ S) ∧ IsClosed (⋂₀ S) :=
  ⟨AbsConvex.sInter (fun s hs => (h s hs).1), isClosed_sInter fun _ hs => (h _ hs).2⟩

variable (𝕜) in
/-- The absolutely convex closed hull of a set `s` is the minimal absolutely convex closed set that
includes `s`. -/
@[simps! isClosed]
/-
**closedAbsConvexHull** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：closedAbsConvexHull : ClosureOperator (Set E)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `absConvex_closed_sInter`：absConvex_closed_sInter {S : Set (Set E)} (h : 
forall s in S, AbsConvex 𝕜 s ∧ IsClosed s) : AbsConvex 𝕜 (⋂₀ S) ∧ IsClosed (⋂₀ S
)

--- 原说明 ---
The absolutely convex closed hull of a set `s` is the minimal absolutely convex 
closed set that
includes `s`.
-/
def closedAbsConvexHull : ClosureOperator (Set E) :=
  .ofCompletePred (fun s => AbsConvex 𝕜 s ∧ IsClosed s) fun _ ↦ absConvex_closed_sInter
/-
**absConvex_convexClosedHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absConvex_convexClosedHull {s : Set E} : AbsConvex 𝕜 (closedAbsConvexHull 
𝕜 s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ClosureOperator.isClosed_closure`：∀ {α : Type u_1} [inst : Preorder α] (
c : ClosureOperator α) (x : α), c.IsClosed (c x)
-/
theorem absConvex_convexClosedHull {s : Set E} :
    AbsConvex 𝕜 (closedAbsConvexHull 𝕜 s) := ((closedAbsConvexHull 𝕜).isClosed_closure s).1
/-
**isClosed_closedAbsConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_closedAbsConvexHull {s : Set E} : IsClosed (closedAbsConvexHull 𝕜
 s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ClosureOperator.isClosed_closure`：∀ {α : Type u_1} [inst : Preorder α] (
c : ClosureOperator α) (x : α), c.IsClosed (c x)
-/
theorem isClosed_closedAbsConvexHull {s : Set E} :
    IsClosed (closedAbsConvexHull 𝕜 s) := ((closedAbsConvexHull 𝕜).isClosed_closure s).2
/-
**subset_closedAbsConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_closedAbsConvexHull {s : Set E} : s subseteq closedAbsConvexHull 𝕜 
s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.le_closure`：le_closure (x : α) : x <= c x
-/
theorem subset_closedAbsConvexHull {s : Set E} : s ⊆ closedAbsConvexHull 𝕜 s :=
  (closedAbsConvexHull 𝕜).le_closure s
/-
**closure_subset_closedAbsConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_subset_closedAbsConvexHull {s : Set E} : closure s subseteq closed
AbsConvexHull 𝕜 s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `subset_closedAbsConvexHull`：subset_closedAbsConvexHull {s : Set E} : s s
ubseteq closedAbsConvexHull 𝕜 s
· 使用定理 `isClosed_closedAbsConvexHull`：isClosed_closedAbsConvexHull {s : Set E} :
 IsClosed (closedAbsConvexHull 𝕜 s)
-/
theorem closure_subset_closedAbsConvexHull {s : Set E} : closure s ⊆ closedAbsConvexHull 𝕜 s :=
  closure_minimal subset_closedAbsConvexHull isClosed_closedAbsConvexHull
/-
**closedAbsConvexHull_min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closedAbsConvexHull_min {s t : Set E} (hst : s subseteq t) (h_conv : AbsCo
nvex 𝕜 t) (h_closed : IsClosed t) : closedAbsConvexHull 𝕜 s subseteq t
参数：hst : s subseteq t；h_conv : AbsConvex 𝕜 t；h_closed : IsClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ClosureOperator.closure_min`：closure_min (hxy : x <= y) (hy : c.IsClosed
 y) : c x <= y
-/
theorem closedAbsConvexHull_min {s t : Set E} (hst : s ⊆ t) (h_conv : AbsConvex 𝕜 t)
    (h_closed : IsClosed t) : closedAbsConvexHull 𝕜 s ⊆ t :=
  (closedAbsConvexHull 𝕜).closure_min hst ⟨h_conv, h_closed⟩
/-
**absConvexHull_subset_closedAbsConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absConvexHull_subset_closedAbsConvexHull {s : Set E} : (absConvexHull 𝕜) s
 subseteq (closedAbsConvexHull 𝕜) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `absConvexHull_min`：absConvexHull_min : s subseteq t -> AbsConvex 𝕜 t -> 
absConvexHull 𝕜 s subseteq t
· 使用定理 `subset_closedAbsConvexHull`：subset_closedAbsConvexHull {s : Set E} : s s
ubseteq closedAbsConvexHull 𝕜 s
· 使用定理 `absConvex_convexClosedHull`：absConvex_convexClosedHull {s : Set E} : Abs
Convex 𝕜 (closedAbsConvexHull 𝕜 s)
-/
theorem absConvexHull_subset_closedAbsConvexHull {s : Set E} :
    (absConvexHull 𝕜) s ⊆ (closedAbsConvexHull 𝕜) s :=
  absConvexHull_min subset_closedAbsConvexHull absConvex_convexClosedHull

@[simp]
/-
**closedAbsConvexHull_closure_eq_closedAbsConvexHull** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：closedAbsConvexHull_closure_eq_closedAbsConvexHull {s : Set E} : closedAbs
ConvexHull 𝕜 (closure s) = closedAbsConvexHull 𝕜 s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClosureOperator.idempotent`：idempotent (x : α) : c (c x) = c x
· 使用定理 `ClosureOperator.monotone`：monotone : Monotone c
· 使用定理 `closure_subset_closedAbsConvexHull`：closure_subset_closedAbsConvexHull {
s : Set E} : closure s subseteq closedAbsConvexHull 𝕜 s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem closedAbsConvexHull_closure_eq_closedAbsConvexHull {s : Set E} :
    closedAbsConvexHull 𝕜 (closure s) = closedAbsConvexHull 𝕜 s :=
  subset_antisymm (by simpa using ((closedAbsConvexHull 𝕜).monotone
      (closure_subset_closedAbsConvexHull (𝕜 := 𝕜) (E := E))))
    ((closedAbsConvexHull 𝕜).monotone subset_closure)

end AbsolutelyConvex

section NormedField

variable [NormedField 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-
**AbsConvex.closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AbsConvex.closure {s : Set E} (hs : AbsConvex 𝕜 s) : AbsConvex 𝕜 (closure 
s)
参数：hs : AbsConvex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Balanced.closure`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : NormedField 𝕜]
 [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   {A : Set E} [inst_3 : 
Topolo…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Convex.closure`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_1
 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [ins
t_4 …
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem AbsConvex.closure {s : Set E} (hs : AbsConvex 𝕜 s) : AbsConvex 𝕜 (closure s) :=
  ⟨Balanced.closure hs.1, Convex.closure hs.2⟩
/-
**closedAbsConvexHull_eq_closure_absConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closedAbsConvexHull_eq_closure_absConvexHull {s : Set E} : closedAbsConvex
Hull 𝕜 s = closure (absConvexHull 𝕜 s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `closedAbsConvexHull_min`：closedAbsConvexHull_min {s t : Set E} (hst : s 
subseteq t) (h_conv : AbsConvex 𝕜 t) (h_closed : IsClosed t) : closedAbsConvexHu
ll 𝕜 s subset…
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `subset_absConvexHull`：subset_absConvexHull : s subseteq absConvexHull 𝕜 
s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `AbsConvex.closure`：AbsConvex.closure {s : Set E} (hs : AbsConvex 𝕜 s) : 
AbsConvex 𝕜 (closure s)
· 使用定理 `absConvex_absConvexHull`：absConvex_absConvexHull : AbsConvex 𝕜 (absConve
xHull 𝕜 s)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `absConvexHull_subset_closedAbsConvexHull`：absConvexHull_subset_closedAbs
ConvexHull {s : Set E} : (absConvexHull 𝕜) s subseteq (closedAbsConvexHull 𝕜) s
· 使用定理 `isClosed_closedAbsConvexHull`：isClosed_closedAbsConvexHull {s : Set E} :
 IsClosed (closedAbsConvexHull 𝕜 s)
-/
theorem closedAbsConvexHull_eq_closure_absConvexHull {s : Set E} :
    closedAbsConvexHull 𝕜 s = closure (absConvexHull 𝕜 s) := subset_antisymm
  (closedAbsConvexHull_min (subset_trans (subset_absConvexHull) subset_closure)
    (AbsConvex.closure absConvex_absConvexHull) isClosed_closure)
  (closure_minimal absConvexHull_subset_closedAbsConvexHull isClosed_closedAbsConvexHull)

end NormedField

section

variable (𝕜) [NontriviallyNormedField 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

/-
**absConvexHull_add_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absConvexHull_add_subset {s t : Set E} : absConvexHull 𝕜 (s + t) subseteq 
absConvexHull 𝕜 s + absConvexHull 𝕜 t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `absConvexHull_min`：absConvexHull_min : s subseteq t -> AbsConvex 𝕜 t -> 
absConvexHull 𝕜 s subseteq t
· 使用定理 `Set.add_subset_add`：∀ {α : Type u_2} [inst : Add α] {s₁ s₂ t₁ t₂ : Set α
}, s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ + s₂ ⊆ t₁ + t₂
· 使用定理 `subset_absConvexHull`：subset_absConvexHull : s subseteq absConvexHull 𝕜 
s
· 使用定理 `Balanced.add`：Balanced.add (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t) : Bal
anced 𝕜 (s + t)
· 使用定理 `balanced_absConvexHull`：balanced_absConvexHull : Balanced 𝕜 (absConvexHu
ll 𝕜 s)
· 使用定理 `Convex.add`：Convex.add {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
 Convex 𝕜 (s + t)
· 使用定理 `convex_absConvexHull`：convex_absConvexHull : Convex 𝕜 (absConvexHull 𝕜 s
)
-/
theorem absConvexHull_add_subset {s t : Set E} :
    absConvexHull 𝕜 (s + t) ⊆ absConvexHull 𝕜 s + absConvexHull 𝕜 t :=
  absConvexHull_min (add_subset_add subset_absConvexHull subset_absConvexHull)
    ⟨Balanced.add balanced_absConvexHull balanced_absConvexHull,
      Convex.add convex_absConvexHull convex_absConvexHull⟩
/-
**absConvexHull_eq_convexHull_balancedHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absConvexHull_eq_convexHull_balancedHull {s : Set E} : absConvexHull 𝕜 s =
 convexHull 𝕜 (balancedHull 𝕜 s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `absConvexHull_min`：absConvexHull_min : s subseteq t -> AbsConvex 𝕜 t -> 
absConvexHull 𝕜 s subseteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `convexHull_mono`：convexHull_mono (hst : s subseteq t) : convexHull 𝕜 s s
ubseteq convexHull 𝕜 t
· 使用定理 `subset_balancedHull`：subset_balancedHull [NormOneClass 𝕜] {s : Set E} : 
s subseteq balancedHull 𝕜 s
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Balanced.convexHull`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nontriviall
yNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] {s : Se
t E} [ins…
· 使用定理 `balancedHull.balanced`：balancedHull.balanced (s : Set E) : Balanced 𝕜 (b
alancedHull 𝕜 s)
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `Balanced.balancedHull_subset_of_subset`：Balanced.balancedHull_subset_of_
subset (ht : Balanced 𝕜 t) (h : s subseteq t) : balancedHull 𝕜 s subseteq t
· 使用定理 `balanced_absConvexHull`：balanced_absConvexHull : Balanced 𝕜 (absConvexHu
ll 𝕜 s)
· 使用定理 `subset_absConvexHull`：subset_absConvexHull : s subseteq absConvexHull 𝕜 
s
· 使用定理 `convex_absConvexHull`：convex_absConvexHull : Convex 𝕜 (absConvexHull 𝕜 s
)
-/
theorem absConvexHull_eq_convexHull_balancedHull {s : Set E} :
    absConvexHull 𝕜 s = convexHull 𝕜 (balancedHull 𝕜 s) := le_antisymm
  (absConvexHull_min
    ((subset_convexHull 𝕜 s).trans (convexHull_mono (subset_balancedHull 𝕜)))
      ⟨Balanced.convexHull (balancedHull.balanced s), convex_convexHull ..⟩)
  (convexHull_min (balanced_absConvexHull.balancedHull_subset_of_subset subset_absConvexHull)
      convex_absConvexHull)

/-- In general, equality doesn't hold here - e.g. consider `s := {(-1, 1), (1, 1)}` in `ℝ²`. -/
/-
**balancedHull_convexHull_subset_absConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balancedHull_convexHull_subset_absConvexHull {s : Set E} : balancedHull 𝕜 
(convexHull 𝕜 s) subseteq absConvexHull 𝕜 s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Balanced.balancedHull_subset_of_subset`：Balanced.balancedHull_subset_of_
subset (ht : Balanced 𝕜 t) (h : s subseteq t) : balancedHull 𝕜 s subseteq t
· 使用定理 `balanced_absConvexHull`：balanced_absConvexHull : Balanced 𝕜 (absConvexHu
ll 𝕜 s)
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `subset_absConvexHull`：subset_absConvexHull : s subseteq absConvexHull 𝕜 
s
· 使用定理 `convex_absConvexHull`：convex_absConvexHull : Convex 𝕜 (absConvexHull 𝕜 s
)

--- 原说明 ---
In general, equality doesn't hold here - e.g. consider `s := {(-1, 1), (1, 1)}` 
in `ℝ²`.
-/
theorem balancedHull_convexHull_subset_absConvexHull {s : Set E} :
    balancedHull 𝕜 (convexHull 𝕜 s) ⊆ absConvexHull 𝕜 s :=
  balanced_absConvexHull.balancedHull_subset_of_subset
    (convexHull_min subset_absConvexHull convex_absConvexHull)

@[deprecated balancedHull_convexHull_subset_absConvexHull (since := "2026-05-23")]
alias balancedHull_convexHull_subseteq_absConvexHull := balancedHull_convexHull_subset_absConvexHull

variable [ZeroLEOneClass 𝕜] [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] [IsTopologicalAddGroup E]
/-
**IsOpen.absConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.absConvexHull {s : Set E} (hs : IsOpen s) (hzero : 0 in s) : IsOpen
 (absConvexHull 𝕜 s)
参数：hs : IsOpen s；hzero : 0 in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `absConvexHull_eq_convexHull_balancedHull`：absConvexHull_eq_convexHull_ba
lancedHull {s : Set E} : absConvexHull 𝕜 s = convexHull 𝕜 (balancedHull 𝕜 s)
· 使用定理 `IsOpen.convexHull`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [ins
t_1 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [
inst_4 …
· 使用定理 `IsOpen.balancedHull`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : NormedDivis
ionRing 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : To
pological…
-/
theorem IsOpen.absConvexHull {s : Set E} (hs : IsOpen s) (hzero : 0 ∈ s) :
    IsOpen (absConvexHull 𝕜 s) := by
  rw [absConvexHull_eq_convexHull_balancedHull]
  exact hs.balancedHull hzero |>.convexHull

end

section NontriviallyNormedField

variable (𝕜 E)
variable [NontriviallyNormedField 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [LocallyConvexSpace 𝕜 E] [ContinuousSMul 𝕜 E]

/-
**nhds_hasBasis_absConvex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_hasBasis_absConvex : (𝓝 (0 : E)).HasBasis (fun s : Set E => s in 𝓝 (0
 : E) ∧ AbsConvex 𝕜 s) id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `LocallyConvexSpace.convex_basis_zero`：LocallyConvexSpace.convex_basis_ze
ro [LocallyConvexSpace 𝕜 E] : (𝓝 0 : Filter E).HasBasis (fun s => s in (𝓝 0 : Fi
lter E) ∧ Convex 𝕜 s) id
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `balancedCore_mem_nhds_zero`：balancedCore_mem_nhds_zero (hU : U in 𝓝 (0 :
 E)) : balancedCore 𝕜 U in 𝓝 (0 : E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `Balanced.convexHull`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nontriviall
yNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] {s : Se
t E} [ins…
· 使用定理 `balancedCore_balanced`：balancedCore_balanced (s : Set E) : Balanced 𝕜 (b
alancedCore 𝕜 s)
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `balancedCore_subset`：balancedCore_subset (s : Set E) : balancedCore 𝕜 s 
subseteq s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
-/
theorem nhds_hasBasis_absConvex :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ 𝓝 (0 : E) ∧ AbsConvex 𝕜 s) id := by
  refine
    (LocallyConvexSpace.convex_basis_zero 𝕜 E).to_hasBasis (fun s hs => ?_) fun s hs =>
      ⟨s, ⟨hs.1, hs.2.2⟩, rfl.subset⟩
  refine ⟨convexHull 𝕜 (balancedCore 𝕜 s), ?_, convexHull_min (balancedCore_subset s) hs.2⟩
  refine ⟨Filter.mem_of_superset (balancedCore_mem_nhds_zero hs.1) (subset_convexHull 𝕜 _), ?_⟩
  refine ⟨(balancedCore_balanced s).convexHull, ?_⟩
  exact convex_convexHull 𝕜 (balancedCore 𝕜 s)

variable [IsTopologicalAddGroup E] [ZeroLEOneClass 𝕜]
/-
**nhds_hasBasis_absConvex_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_hasBasis_absConvex_open : (𝓝 (0 : E)).HasBasis (fun s => (0 : E) in s
 ∧ IsOpen s ∧ AbsConvex 𝕜 s) id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `nhds_hasBasis_absConvex`：nhds_hasBasis_absConvex : (𝓝 (0 : E)).HasBasis 
(fun s : Set E => s in 𝓝 (0 : E) ∧ AbsConvex 𝕜 s) id
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Balanced.interior`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : NormedField 𝕜
] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   {A : Set E} [inst_3 :
 Topolo…
· 使用定理 `Convex.interior`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_
1 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [in
st_4 …
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
-/
theorem nhds_hasBasis_absConvex_open :
    (𝓝 (0 : E)).HasBasis (fun s ↦ (0 : E) ∈ s ∧ IsOpen s ∧ AbsConvex 𝕜 s) id := by
  refine (nhds_hasBasis_absConvex 𝕜 E).to_hasBasis ?_ ?_
  · intro s ⟨hs_nhds, hs_balanced, hs_convex⟩
    refine ⟨interior s, ?_, interior_subset⟩
    exact
      ⟨mem_interior_iff_mem_nhds.mpr hs_nhds, isOpen_interior,
        hs_balanced.interior (mem_interior_iff_mem_nhds.mpr hs_nhds), hs_convex.interior⟩
  intro s ⟨hs_zero, hs_open, hs_balanced, hs_convex⟩
  exact ⟨s, ⟨hs_open.mem_nhds hs_zero, hs_balanced, hs_convex⟩, rfl.subset⟩
/-
**nhds_hasBasis_absConvex_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_hasBasis_absConvex_closed : (𝓝 (0 : E)).HasBasis (fun s => s in 𝓝 (0 
: E) ∧ IsClosed s ∧ AbsConvex 𝕜 s) id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `exists_open_nhds_zero_add_subset`：∀ {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : AddZeroClass M] [ContinuousAdd M] {U : Set M},   U ∈ nhds 0 → ∃
 V, IsOpen V ∧ 0 ∈ V ∧…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `nhds_hasBasis_absConvex_open`：nhds_hasBasis_absConvex_open : (𝓝 (0 : E))
.HasBasis (fun s => (0 : E) in s ∧ IsOpen s ∧ AbsConvex 𝕜 s) id
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `AbsConvex.closure`：AbsConvex.closure {s : Set E} (hs : AbsConvex 𝕜 s) : 
AbsConvex 𝕜 (closure s)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `closure_subset_add_self_of_mem_nhds_zero`：∀ {G : Type w} [inst : Topolog
icalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {U : Set G},   U ∈ 
nhds 0 → closure U ⊆ U + U
· 使用定理 `Set.add_subset_add`：∀ {α : Type u_2} [inst : Add α] {s₁ s₂ t₁ t₂ : Set α
}, s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ + s₂ ⊆ t₁ + t₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem nhds_hasBasis_absConvex_closed :
    (𝓝 (0 : E)).HasBasis (fun s ↦ s ∈ 𝓝 (0 : E) ∧ IsClosed s ∧ AbsConvex 𝕜 s) id := by
  refine (nhds_basis_opens 0).to_hasBasis ?_
    fun s ⟨hs_nhds, _, _⟩ ↦ ⟨interior s,
      by simp [interior_subset, mem_interior_iff_mem_nhds.mpr hs_nhds]⟩
  intro s ⟨hs_zero, hs_open⟩
  obtain ⟨W, hW_open, hW_zero, hW_add⟩ :=
    exists_open_nhds_zero_add_subset (hs_open.mem_nhds hs_zero)
  obtain ⟨V, ⟨hV_zero, hV_open, hV_abs⟩, hVW⟩ :=
    (nhds_hasBasis_absConvex_open 𝕜 E).mem_iff.mp (hW_open.mem_nhds hW_zero)
  exact ⟨closure V,
    ⟨Filter.mem_of_superset (hV_open.mem_nhds hV_zero) subset_closure, isClosed_closure,
     hV_abs.closure⟩,
    (closure_subset_add_self_of_mem_nhds_zero (hV_open.mem_nhds hV_zero)).trans
      ((add_subset_add hVW hVW).trans hW_add)⟩
/-
**exists_nhds_hasAntitoneBasis_absConvex_open_add_closure_subset** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：exists_nhds_hasAntitoneBasis_absConvex_open_add_closure_subset [FirstCount
ableTopology E] : exists x : Nat -> Set E, (𝓝 (0 : E)).HasAntitoneBasis x ∧ fora
ll n, IsOpen (x n) ∧ AbsConvex 𝕜 (x n) ∧ x (n + 1) + x (n + 1) subseteq x n ∧ cl
osure (x (n + 1)) subseteq x n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.exists_antitone_basis_nhds_zero`：∀ (G : Type w) [i
nst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] [First
CountableTopology G],   ∃ u, (nhds 0).HasAn…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `Filter.HasAntitoneBasis.toHasBasis`：∀ {α : Type u_1} {ι'' : Type u_6} [i
nst : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → l
.HasBasis (fun x => True…
· 使用定理 `trivial`：True
· 使用定理 `IsOpen.absConvexHull`：IsOpen.absConvexHull {s : Set E} (hs : IsOpen s) (
hzero : 0 in s) : IsOpen (absConvexHull 𝕜 s)
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `subset_absConvexHull`：subset_absConvexHull : s subseteq absConvexHull 𝕜 
s
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `nhds_hasBasis_absConvex`：nhds_hasBasis_absConvex : (𝓝 (0 : E)).HasBasis 
(fun s : Set E => s in 𝓝 (0 : E) ∧ AbsConvex 𝕜 s) id
· 使用定理 `Filter.HasAntitoneBasis.mem_iff`：∀ {α : Type u_1} {ι : Type u_4} [inst :
 Preorder ι] {l : Filter α} {s : ι → Set α},   l.HasAntitoneBasis s → ∀ {t : Set
 α}, t ∈ l ↔ ∃ i, s i…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `absConvexHull_min`：absConvexHull_min : s subseteq t -> AbsConvex 𝕜 t -> 
absConvexHull 𝕜 s subseteq t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `absConvexHull_mono`：absConvexHull_mono (hst : s subseteq t) : absConvexH
ull 𝕜 s subseteq absConvexHull 𝕜 t
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Filter.HasAntitoneBasis.antitone`：∀ {α : Type u_1} {ι'' : Type u_6} [ins
t : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → Ant
itone s
· 使用定理 `Filter.HasAntitoneBasis.subbasis_with_rel`：∀ {α : Type u_3} {f : Filter 
α} {s : ℕ → Set α},   f.HasAntitoneBasis s →     ∀ {r : ℕ → ℕ → Prop},       (∀ 
(m : ℕ), ∀ᶠ (n : ℕ) in Filter.a…
· 使用定理 `exists_open_nhds_zero_add_subset`：∀ {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : AddZeroClass M] [ContinuousAdd M] {U : Set M},   U ∈ nhds 0 → ∃
 V, IsOpen V ∧ 0 ∈ V ∧…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.add_subset_add`：∀ {α : Type u_2} [inst : Add α] {s₁ s₂ t₁ t₂ : Set α
}, s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ + s₂ ⊆ t₁ + t₂
· 使用定理 `absConvex_absConvexHull`：absConvex_absConvexHull : AbsConvex 𝕜 (absConve
xHull 𝕜 s)
（共 41 条，此处仅展示前 30 条）
-/
theorem exists_nhds_hasAntitoneBasis_absConvex_open_add_closure_subset [FirstCountableTopology E] :
    ∃ x : ℕ → Set E, (𝓝 (0 : E)).HasAntitoneBasis x ∧
      ∀ n, IsOpen (x n) ∧ AbsConvex 𝕜 (x n) ∧ x (n + 1) + x (n + 1) ⊆ x n ∧
        closure (x (n + 1)) ⊆ x n := by
  obtain ⟨u, hu_basis, -⟩ := IsTopologicalAddGroup.exists_antitone_basis_nhds_zero E
  have hu_zero (n : ℕ) : 0 ∈ interior (u n) :=
    mem_interior_iff_mem_nhds.mpr (hu_basis.mem_of_mem trivial)
  let v (n : ℕ) := absConvexHull 𝕜 (interior (u n))
  have hv_open (n : ℕ) : IsOpen (v n) := isOpen_interior.absConvexHull 𝕜 (hu_zero n)
  have hv_nhds (n : ℕ) : v n ∈ 𝓝 0 := (hv_open n).mem_nhds (subset_absConvexHull (hu_zero n))
  have hv_basis : (𝓝 0).HasAntitoneBasis v := by
    refine ⟨hu_basis.to_hasBasis ?_ ?_,
      fun _ _ hij ↦ absConvexHull_mono (interior_mono (hu_basis.antitone hij))⟩
    · intro n _
      obtain ⟨W, ⟨hW_nhds, hW_abs⟩, hWn⟩ :=
        (nhds_hasBasis_absConvex 𝕜 E).mem_iff.mp (hu_basis.mem_of_mem trivial)
      obtain ⟨m, hm⟩ := hu_basis.mem_iff.mp hW_nhds
      exact ⟨m, trivial, (absConvexHull_min (interior_subset.trans hm) hW_abs).trans hWn⟩
    · intro n _
      obtain ⟨m, hm⟩ := hu_basis.mem_iff.mp (isOpen_interior.mem_nhds (hu_zero n))
      exact ⟨m, trivial, hm.trans subset_absConvexHull⟩
  obtain ⟨φ, -, hφ_add, hφ_basis⟩ := hv_basis.subbasis_with_rel
    (r := fun i j ↦ v j + v j ⊆ v i) fun m ↦ by
      obtain ⟨W, hW_open, hW_zero, hW_add⟩ := exists_open_nhds_zero_add_subset (hv_nhds m)
      obtain ⟨N, hN⟩ := hv_basis.mem_iff.mp (hW_open.mem_nhds hW_zero)
      filter_upwards [Filter.eventually_ge_atTop N] with M hM
      exact (add_subset_add ((hv_basis.antitone hM).trans hN)
        ((hv_basis.antitone hM).trans hN)).trans hW_add
  exact ⟨v ∘ φ, hφ_basis, fun n ↦ ⟨hv_open (φ n), absConvex_absConvexHull, hφ_add (by simp),
    (closure_subset_add_self_of_mem_nhds_zero (hv_nhds (φ (n + 1)))).trans
        (hφ_add n.lt_succ_self)⟩⟩

end NontriviallyNormedField

section

variable [AddCommGroup E] [Module ℝ E]

/-
**balancedHull_subset_convexHull_union_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：balancedHull_subset_convexHull_union_neg {s : Set E} : balancedHull Real s
 subseteq convexHull Real (s union -s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_balancedHull_iff`：mem_balancedHull_iff : x in balancedHull 𝕜 s ↔ exi
sts r : 𝕜, ‖r‖ <= 1 ∧ x in r • s
· 使用定理 `segment_subset_convexHull`：segment_subset_convexHull (hx : x in s) (hy :
 y in s) : segment 𝕜 x y subseteq convexHull 𝕜 s
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `Set.mem_union_right`：mem_union_right {x : α} {b : Set α} (a : Set α) : x
 in b -> x in a union b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.neg_mem_neg`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s : Set α} {
a : α}, -a ∈ -s ↔ a ∈ s
· 使用定理 `neg_le_iff_add_nonneg'`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b : α}, -a ≤ b ↔ 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `neg_le_of_abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Lin
earOrder G] [IsOrderedAddMonoid G] {a b : G}, |a| ≤ b → -b ≤ a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_of_abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearO
rder G] [IsOrderedAddMonoid G] {a b : G}, |a| ≤ b → a ≤ b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 87 条，此处仅展示前 30 条）
-/
lemma balancedHull_subset_convexHull_union_neg {s : Set E} :
    balancedHull ℝ s ⊆ convexHull ℝ (s ∪ -s) := by
  intro a ha
  obtain ⟨r, hr, y, hy, rfl⟩ := mem_balancedHull_iff.1 ha
  apply segment_subset_convexHull (mem_union_left (-s) hy) (mem_union_right _ (neg_mem_neg.mpr hy))
  have : 0 ≤ 1 + r := neg_le_iff_add_nonneg'.mp (neg_le_of_abs_le hr)
  have : 0 ≤ 1 - r := sub_nonneg.2 (le_of_abs_le hr)
  refine ⟨(1 + r)/2, (1 - r)/2, by positivity, by positivity, by ring, ?_⟩
  rw [smul_neg, ← sub_eq_add_neg, ← sub_smul]
  ring_nf

@[simp]
/-
**convexHull_union_neg_eq_absConvexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_union_neg_eq_absConvexHull {s : Set E} : convexHull Real (s uni
on -s) = absConvexHull Real s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `absConvexHull_eq_convexHull_balancedHull`：absConvexHull_eq_convexHull_ba
lancedHull {s : Set E} : absConvexHull 𝕜 s = convexHull 𝕜 (balancedHull 𝕜 s)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `convexHull_mono`：convexHull_mono (hst : s subseteq t) : convexHull 𝕜 s s
ubseteq convexHull 𝕜 t
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `subset_balancedHull`：subset_balancedHull [NormOneClass 𝕜] {s : Set E} : 
s subseteq balancedHull 𝕜 s
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `mem_balancedHull_iff`：mem_balancedHull_iff : x in balancedHull 𝕜 s ↔ exi
sts r : 𝕜, ‖r‖ <= 1 ∧ x in r • s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用引理 `Set.neg_smul_set`：neg_smul_set : -a • t = -(a • t)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Convex.convexHull_eq`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜
] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module
 𝕜 E] {s :…
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用引理 `balancedHull_subset_convexHull_union_neg`：balancedHull_subset_convexHull
_union_neg {s : Set E} : balancedHull Real s subseteq convexHull Real (s union -
s)
-/
theorem convexHull_union_neg_eq_absConvexHull {s : Set E} :
    convexHull ℝ (s ∪ -s) = absConvexHull ℝ s := by
  rw [absConvexHull_eq_convexHull_balancedHull]
  exact le_antisymm (convexHull_mono (union_subset (subset_balancedHull ℝ)
    (fun _ _ => by rw [mem_balancedHull_iff]; use -1; simp_all)))
    (by
      rw [← Convex.convexHull_eq (convex_convexHull ℝ (s ∪ -s))]
      exact convexHull_mono balancedHull_subset_convexHull_union_neg)

variable (𝕜) {s : Set E}
variable [NontriviallyNormedField 𝕜] [PartialOrder 𝕜] [Module 𝕜 E] [SMulCommClass ℝ 𝕜 E]
variable [UniformSpace E] [IsUniformAddGroup E] [lcs : LocallyConvexSpace ℝ E] [ContinuousSMul ℝ E]

@[simp]
/-
**totallyBounded_absConvexHull** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：totallyBounded_absConvexHull : TotallyBounded (absConvexHull Real s) ↔ Tot
allyBounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma totallyBounded_absConvexHull : TotallyBounded (absConvexHull ℝ s) ↔ TotallyBounded s := by
  simp [← convexHull_union_neg_eq_absConvexHull]

protected alias ⟨_, TotallyBounded.absConvexHull⟩ := totallyBounded_absConvexHull

end

/-
**zero_mem_absConvexHull** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zero_mem_absConvexHull {s : Set E} [SeminormedRing 𝕜] [PartialOrder 𝕜] [Ad
dCommGroup E] [Module 𝕜 E] [Nonempty s] : 0 in absConvexHull 𝕜 s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Balanced.zero_mem`：Balanced.zero_mem (hs : Balanced 𝕜 s) (hs_nonempty : 
s.Nonempty) : (0 : E) in s
· 使用定理 `balanced_absConvexHull`：balanced_absConvexHull : Balanced 𝕜 (absConvexHu
ll 𝕜 s)
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `subset_absConvexHull`：subset_absConvexHull : s subseteq absConvexHull 𝕜 
s
· 使用定理 `Set.Nonempty.of_subtype`：∀ {α : Type u} {s : Set α} [Nonempty ↑s], s.Non
empty
-/
lemma zero_mem_absConvexHull {s : Set E} [SeminormedRing 𝕜] [PartialOrder 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Nonempty s] : 0 ∈ absConvexHull 𝕜 s :=
  balanced_absConvexHull.zero_mem (Nonempty.mono subset_absConvexHull Set.Nonempty.of_subtype)

/-- [Bourbaki, *Topological Vector Spaces*, III §1.6][bourbaki1987] -/
/-
**isCompact_closedAbsConvexHull_of_totallyBounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_closedAbsConvexHull_of_totallyBounded {E : Type*} [AddCommGroup 
E] [Module Real E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul Real E
] [LocallyConvexSpace Real E] [QuasiCompleteSpace Real E] {s : Set E} (ht : Tota
llyBounded s) : IsCompact (closedAbsConvexHull Real s)
参数：ht : TotallyBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closedAbsConvexHull_eq_closure_absConvexHull`：closedAbsConvexHull_eq_clo
sure_absConvexHull {s : Set E} : closedAbsConvexHull 𝕜 s = closure (absConvexHul
l 𝕜 s)
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `isCompact_closure_of_totallyBounded_quasiComplete`：isCompact_closure_of_
totallyBounded_quasiComplete {E : Type*} {𝕜 : Type*} [NormedField 𝕜] [AddCommGro
up E] [Module 𝕜 E] [UniformSpace E] [Is…
· 使用定理 `TotallyBounded.absConvexHull`：∀ {E : Type u_2} [inst : AddCommGroup E] [
inst_1 : _root_.Module ℝ E] {s : Set E} [inst_2 : UniformSpace E]   [IsUniformAd
dGroup E] [lcs : L…

--- 原说明 ---
[Bourbaki, *Topological Vector Spaces*, III §1.6][bourbaki1987]
-/
theorem isCompact_closedAbsConvexHull_of_totallyBounded {E : Type*} [AddCommGroup E] [Module ℝ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [QuasiCompleteSpace ℝ E] {s : Set E} (ht : TotallyBounded s) :
    IsCompact (closedAbsConvexHull ℝ s) := by
  rw [closedAbsConvexHull_eq_closure_absConvexHull]
  exact isCompact_closure_of_totallyBounded_quasiComplete (𝕜 := ℝ) ht.absConvexHull
