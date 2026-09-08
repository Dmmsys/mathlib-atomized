/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.WithTop
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.ENNReal.Inv

/-!
# Properties of big operators extended non-negative real numbers

In this file we prove elementary properties of sums and products on `ℝ≥0∞`, as well as how these
interact with the order structure on `ℝ≥0∞`.
-/

public section

open Set NNReal

namespace ENNReal

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

section OperationsAndInfty

variable {ι M : Type*} [Zero M]

@[simp, norm_cast]
/-
**ENNReal.ofNNReal_finsetSum** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofNNReal_finsetSum (s : Finset ι) (f : ι -> Real>=0) : ↑(∑ i in s, f i) = 
∑ i in s, ofNNReal (f i)
参数：s : Finset ι；f : ι -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
lemma ofNNReal_finsetSum (s : Finset ι) (f : ι → ℝ≥0) : ↑(∑ i ∈ s, f i) = ∑ i ∈ s, ofNNReal (f i) :=
  map_sum ofNNRealHom ..

@[deprecated (since := "2026-06-04")] alias coe_finsetSum := ofNNReal_finsetSum
@[deprecated (since := "2026-04-08")] alias coe_finset_sum := ofNNReal_finsetSum

@[simp, norm_cast]
/-
**ENNReal.ofNNReal_finsetProd** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofNNReal_finsetProd (s : Finset ι) (f : ι -> Real>=0) : ↑(∏ i in s, f i) =
 ∏ i in s, ofNNReal (f i)
参数：s : Finset ι；f : ι -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma ofNNReal_finsetProd (s : Finset ι) (f : ι → ℝ≥0) :
    ↑(∏ i ∈ s, f i) = ∏ i ∈ s, ofNNReal (f i) := map_prod ofNNRealHom f s

@[deprecated (since := "2026-06-04")] alias coe_finsetProd := ofNNReal_finsetProd
@[deprecated (since := "2026-04-08")] alias coe_finset_prod := ofNNReal_finsetProd

@[simp, norm_cast]
/-
**ENNReal.ofNNReal_finsuppSum** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofNNReal_finsuppSum (f : ι ->₀ M) (g : ι -> M -> Real>=0) : f.sum g = f.su
m (fun i m => ofNNReal (g i m))
参数：f : ι ->₀ M；g : ι -> M -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
lemma ofNNReal_finsuppSum (f : ι →₀ M) (g : ι → M → ℝ≥0) :
    f.sum g = f.sum (fun i m ↦ ofNNReal (g i m)) := map_finsuppSum ofNNRealHom ..

@[simp, norm_cast]
/-
**ENNReal.ofNNReal_finsuppProd** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofNNReal_finsuppProd (f : ι ->₀ M) (g : ι -> M -> Real>=0) : f.prod g = f.
prod (fun i m => ofNNReal (g i m))
参数：f : ι ->₀ M；g : ι -> M -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finsuppProd`：map_finsuppProd [Zero M] [CommMonoid N] [CommMonoid P] 
{H : Type*} [FunLike H N P] [MonoidHomClass H N P] (h : H) (f : α ->₀ M) (g : α 
-> M …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma ofNNReal_finsuppProd (f : ι →₀ M) (g : ι → M → ℝ≥0) :
    f.prod g = f.prod (fun i m ↦ ofNNReal (g i m)) := map_finsuppProd ofNNRealHom ..

@[simp]
/-
**ENNReal.toNNReal_prod** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_prod (s : Finset ι) (f : ι -> Real>=0∞) : (∏ i in s, f i).toNNRea
l = ∏ i in s, (f i).toNNReal
参数：s : Finset ι；f : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
theorem toNNReal_prod (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∏ i ∈ s, f i).toNNReal = ∏ i ∈ s, (f i).toNNReal :=
  map_prod toNNRealHom _ _

@[simp]
/-
**ENNReal.toReal_prod** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_prod (s : Finset ι) (f : ι -> Real>=0∞) : (∏ i in s, f i).toReal = 
∏ i in s, (f i).toReal
参数：s : Finset ι；f : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
theorem toReal_prod (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∏ i ∈ s, f i).toReal = ∏ i ∈ s, (f i).toReal :=
  map_prod toRealHom _ _
/-
**ENNReal.ofReal_prod_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_prod_of_nonneg {α : Type*} {s : Finset α} {f : α -> Real} (hf : for
all i, i in s -> 0 <= f i) : ENNReal.ofReal (∏ i in s, f i) = ∏ i in s, ENNReal.
ofReal (f i)
参数：hf : forall i, i in s -> 0 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_prod_of_nonneg`：∀ {ι : Type u_2} {s : Finset ι} {f : ι → ℝ
}, (∀ a ∈ s, 0 ≤ f a) → (∏ a ∈ s, f a).toNNReal = ∏ a ∈ s, (f a).toNNReal
-/
theorem ofReal_prod_of_nonneg {α : Type*} {s : Finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
    ENNReal.ofReal (∏ i ∈ s, f i) = ∏ i ∈ s, ENNReal.ofReal (f i) := by
  simp_rw [ENNReal.ofReal, ← ofNNReal_finsetProd, coe_inj]
  exact Real.toNNReal_prod_of_nonneg hf
/-
**ENNReal.iInf_sum** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：iInf_sum {ι α : Type*} {f : ι -> α -> Real>=0∞} {s : Finset α} [Nonempty ι
] (h : forall (t : Finset α) (i j : ι), exists k, forall a in t, f k a <= f i a 
∧ f k a <= f j a) : ⨅ i, ∑ a in s, f i a = ∑ a in s, ⨅ i, f i a
参数：h : forall (t : Finset α) (i j : ι), exists k, forall a in t, f k a <= f i a 
∧ f k a <= f j a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ciInf_const`：∀ {α : Type u_1} {ι : Sort u_4} [inst : ConditionallyComple
tePartialOrderInf α] [hι : Nonempty ι] {a : α}, ⨅ x, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.iInf_add_iInf`：iInf_add_iInf (h : forall i j, exists k, f k + g 
k <= f i + g j) : iInf f + iInf g = ⨅ a, f a + g a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.forall_mem_cons`：forall_mem_cons (h : a ∉ s) (p : α -> Prop) : (f
orall x, x in cons a s h -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem iInf_sum {ι α : Type*} {f : ι → α → ℝ≥0∞} {s : Finset α} [Nonempty ι]
    (h : ∀ (t : Finset α) (i j : ι), ∃ k, ∀ a ∈ t, f k a ≤ f i a ∧ f k a ≤ f j a) :
    ⨅ i, ∑ a ∈ s, f i a = ∑ a ∈ s, ⨅ i, f i a := by
  induction s using Finset.cons_induction_on with
  | empty => simp only [Finset.sum_empty, ciInf_const]
  | cons a s ha ih =>
    simp only [Finset.sum_cons, ← ih]
    refine (iInf_add_iInf fun i j => ?_).symm
    refine (h (Finset.cons a s ha) i j).imp fun k hk => ?_
    rw [Finset.forall_mem_cons] at hk
    exact add_le_add hk.1.1 (Finset.sum_le_sum fun a ha => (hk.2 a ha).2)

end OperationsAndInfty

section Sum

open Finset

variable {α : Type*} {s : Finset α} {f : α → ℝ≥0∞}

/-- A product of finite numbers is still finite. -/
/-
**ENNReal.prod_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：prod_ne_top (h : forall a in s, f a != ∞) : ∏ a in s, f a != ∞
参数：h : forall a in s, f a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.prod_ne_top`：prod_ne_top (h : forall i in s, f i != ⊤) : ∏ i in 
s, f i != ⊤
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal

--- 原说明 ---
A product of finite numbers is still finite.
-/
lemma prod_ne_top (h : ∀ a ∈ s, f a ≠ ∞) : ∏ a ∈ s, f a ≠ ∞ := WithTop.prod_ne_top h

/-- A product of finite numbers is still finite. -/
/-
**ENNReal.prod_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：prod_lt_top (h : forall a in s, f a < ∞) : ∏ a in s, f a < ∞
参数：h : forall a in s, f a < ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.prod_lt_top`：prod_lt_top [LT M₀] (h : forall i in s, f i < ⊤) : 
∏ i in s, f i < ⊤
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal

--- 原说明 ---
A product of finite numbers is still finite.
-/
lemma prod_lt_top (h : ∀ a ∈ s, f a < ∞) : ∏ a ∈ s, f a < ∞ := WithTop.prod_lt_top h

/-- A sum is infinite iff one of the summands is infinite. -/
/-
**ENNReal.sum_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {f : α → ENNReal}, ∑ x ∈ s, f x = ⊤ ↔ ∃ a 
∈ s, f a = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.sum_eq_top`：∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoi
d M] {s : Finset ι} {f : ι → WithTop M},   ∑ i ∈ s, f i = ⊤ ↔ ∃ i ∈ s, f i = ⊤

--- 原说明 ---
A sum is infinite iff one of the summands is infinite.
-/
@[simp] lemma sum_eq_top : ∑ x ∈ s, f x = ∞ ↔ ∃ a ∈ s, f a = ∞ := WithTop.sum_eq_top

/-- A sum is finite iff all summands are finite. -/
/-
**ENNReal.sum_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：sum_ne_top : ∑ a in s, f a != ∞ ↔ forall a in s, f a != ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.sum_ne_top`：sum_ne_top : ∑ i in s, f i != ⊤ ↔ forall i in s, f i
 != ⊤

--- 原说明 ---
A sum is finite iff all summands are finite.
-/
lemma sum_ne_top : ∑ a ∈ s, f a ≠ ∞ ↔ ∀ a ∈ s, f a ≠ ∞ := WithTop.sum_ne_top

/-- A sum is finite iff all summands are finite. -/
/-
**ENNReal.sum_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {f : α → ENNReal}, ∑ a ∈ s, f a < ⊤ ↔ ∀ a 
∈ s, f a < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.sum_lt_top`：∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoi
d M] {s : Finset ι} {f : ι → WithTop M} [inst_1 : LT M],   ∑ i ∈ s, f i < ⊤ ↔ ∀ 
i ∈ s, f…

--- 原说明 ---
A sum is finite iff all summands are finite.
-/
@[simp] lemma sum_lt_top : ∑ a ∈ s, f a < ∞ ↔ ∀ a ∈ s, f a < ∞ := WithTop.sum_lt_top
/-
**ENNReal.lt_top_of_sum_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lt_top_of_sum_ne_top {s : Finset α} {f : α -> Real>=0∞} (h : ∑ x in s, f x
 != ∞) {a : α} (ha : a in s) : f a < ∞
参数：h : ∑ x in s, f x != ∞；ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.sum_lt_top`：∀ {α : Type u_1} {s : Finset α} {f : α → ENNReal}, ∑
 a ∈ s, f a < ⊤ ↔ ∀ a ∈ s, f a < ⊤
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤

--- 原说明 ---
A sum is finite iff all summands are finite.
-/
theorem lt_top_of_sum_ne_top {s : Finset α} {f : α → ℝ≥0∞} (h : ∑ x ∈ s, f x ≠ ∞) {a : α}
    (ha : a ∈ s) : f a < ∞ :=
  sum_lt_top.1 h.lt_top a ha

/-- Seeing `ℝ≥0∞` as `ℝ≥0` does not change their sum, unless one of the `ℝ≥0∞` is
infinity -/
/-
**ENNReal.toNNReal_sum** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_sum {s : Finset α} {f : α -> Real>=0∞} (hf : forall a in s, f a !
= ∞) : ENNReal.toNNReal (∑ a in s, f a) = ∑ a in s, ENNReal.toNNReal (f a)
参数：hf : forall a in s, f a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENNReal.sum_ne_top`：sum_ne_top : ∑ a in s, f a != ∞ ↔ forall a in s, f a
 != ∞
· 使用引理 `ENNReal.ofNNReal_finsetSum`：ofNNReal_finsetSum (s : Finset ι) (f : ι -> 
Real>=0) : ↑(∑ i in s, f i) = ∑ i in s, ofNNReal (f i)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…

--- 原说明 ---
Seeing `ℝ≥0∞` as `ℝ≥0` does not change their sum, unless one of the `ℝ≥0∞` is
infinity
-/
theorem toNNReal_sum {s : Finset α} {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, f a ≠ ∞) :
    ENNReal.toNNReal (∑ a ∈ s, f a) = ∑ a ∈ s, ENNReal.toNNReal (f a) := by
  rw [← coe_inj, coe_toNNReal, ofNNReal_finsetSum, sum_congr rfl]
  · intro x hx
    exact (coe_toNNReal (hf x hx)).symm
  · exact sum_ne_top.2 hf

/-- seeing `ℝ≥0∞` as `Real` does not change their sum, unless one of the `ℝ≥0∞` is infinity -/
/-
**ENNReal.toReal_sum** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_sum {s : Finset α} {f : α -> Real>=0∞} (hf : forall a in s, f a != 
∞) : ENNReal.toReal (∑ a in s, f a) = ∑ a in s, ENNReal.toReal (f a)
参数：hf : forall a in s, f a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal.eq_1`：∀ (a : ENNReal), a.toReal = ↑a.toNNReal
· 使用定理 `ENNReal.toNNReal_sum`：toNNReal_sum {s : Finset α} {f : α -> Real>=0∞} (h
f : forall a in s, f a != ∞) : ENNReal.toNNReal (∑ a in s, f a) = ∑ a in s, ENNR
eal.toNNRe…
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)

--- 原说明 ---
seeing `ℝ≥0∞` as `Real` does not change their sum, unless one of the `ℝ≥0∞` is i
nfinity
-/
theorem toReal_sum {s : Finset α} {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, f a ≠ ∞) :
    ENNReal.toReal (∑ a ∈ s, f a) = ∑ a ∈ s, ENNReal.toReal (f a) := by
  rw [ENNReal.toReal, toNNReal_sum hf, NNReal.coe_sum]
  rfl
/-
**ENNReal.ofReal_sum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_sum_of_nonneg {s : Finset α} {f : α -> Real} (hf : forall i, i in s
 -> 0 <= f i) : ENNReal.ofReal (∑ i in s, f i) = ∑ i in s, ENNReal.ofReal (f i)
参数：hf : forall i, i in s -> 0 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_sum_of_nonneg`：∀ {ι : Type u_2} {s : Finset ι} {f : ι → ℝ}
, (∀ i ∈ s, 0 ≤ f i) → (∑ a ∈ s, f a).toNNReal = ∑ a ∈ s, (f a).toNNReal
-/
theorem ofReal_sum_of_nonneg {s : Finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
    ENNReal.ofReal (∑ i ∈ s, f i) = ∑ i ∈ s, ENNReal.ofReal (f i) := by
  simp_rw [ENNReal.ofReal, ← ofNNReal_finsetSum, coe_inj]
  exact Real.toNNReal_sum_of_nonneg hf
/-
**ENNReal.sum_lt_sum_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：sum_lt_sum_of_nonempty {s : Finset α} (hs : s.Nonempty) {f g : α -> Real>=
0∞} (Hlt : forall i in s, f i < g i) : ∑ i in s, f i < ∑ i in s, g i
参数：hs : s.Nonempty；Hlt : forall i in s, f i < g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `ENNReal.add_lt_add`：∀ {a b c d : ENNReal}, a < c → b < d → a + b < c + d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sum_lt_sum_of_nonempty {s : Finset α} (hs : s.Nonempty) {f g : α → ℝ≥0∞}
    (Hlt : ∀ i ∈ s, f i < g i) : ∑ i ∈ s, f i < ∑ i ∈ s, g i := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => simp [Hlt _ (Finset.mem_singleton_self _)]
  | cons _ _ _ _ ih =>
    simp only [Finset.sum_cons, forall_mem_cons] at Hlt ⊢
    exact ENNReal.add_lt_add Hlt.1 (ih Hlt.2)
/-
**ENNReal.exists_le_of_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：exists_le_of_sum_le {s : Finset α} (hs : s.Nonempty) {f g : α -> Real>=0∞}
 (Hle : ∑ i in s, f i <= ∑ i in s, g i) : exists i in s, f i <= g i
参数：hs : s.Nonempty；Hle : ∑ i in s, f i <= ∑ i in s, g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `ENNReal.sum_lt_sum_of_nonempty`：sum_lt_sum_of_nonempty {s : Finset α} (h
s : s.Nonempty) {f g : α -> Real>=0∞} (Hlt : forall i in s, f i < g i) : ∑ i in 
s, f i < ∑ i in s, g…
-/
theorem exists_le_of_sum_le {s : Finset α} (hs : s.Nonempty) {f g : α → ℝ≥0∞}
    (Hle : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i) : ∃ i ∈ s, f i ≤ g i := by
  contrapose! Hle
  apply ENNReal.sum_lt_sum_of_nonempty hs Hle

end Sum

section Inv

variable {ι : Type*} {f g : ι → ℝ≥0∞} {s : Finset ι}

/-
**ENNReal.prod_inv_distrib** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：prod_inv_distrib (hf : (s : Set ι).Pairwise fun i j => f i != 0 ∨ f j != ∞
) : (∏ i in s, f i)⁻¹ = ∏ i in s, (f i)⁻¹
参数：hf : (s : Set ι).Pairwise fun i j => f i != 0 ∨ f j != ∞。
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
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Finset.coe_cons`：coe_cons {a s h} : (@cons α a s h : Set α) = insert a (
s : Set α)
· 使用定理 `ENNReal.mul_inv`：∀ {a b : ENNReal}, a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊤ ∨ b ≠ 0 → (a *
 b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `not_or_of_imp`：not_or_of_imp : (a -> b) -> ¬a ∨ b
· 使用引理 `ENNReal.prod_ne_top`：prod_ne_top (h : forall a in s, f a != ∞) : ∏ a in 
s, f a != ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `imp_iff_not_or`：imp_iff_not_or : a -> b ↔ ¬a ∨ b
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
-/
lemma prod_inv_distrib (hf : (s : Set ι).Pairwise fun i j ↦ f i ≠ 0 ∨ f j ≠ ∞) :
    (∏ i ∈ s, f i)⁻¹ = ∏ i ∈ s, (f i)⁻¹ := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => ?_
  simp only [Finset.prod_cons, ← ih (hf.mono <| by simp)]
  refine ENNReal.mul_inv (not_or_of_imp fun hi₀ ↦ prod_ne_top fun j hj ↦ ?_)
    (not_or_of_imp fun hi₀ ↦ Finset.prod_ne_zero_iff.2 fun j hj ↦ ?_)
  · exact imp_iff_not_or.2 (hf (by simp) (by simp [hj]) <| .symm <| ne_of_mem_of_not_mem hj hi) hi₀
  · exact imp_iff_not_or.2 (hf (by simp [hj]) (by simp) <| ne_of_mem_of_not_mem hj hi).symm hi₀
/-
**ENNReal.prod_div_distrib** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：prod_div_distrib (hg : (s : Set ι).Pairwise fun i j => g i != 0 ∨ g j != ∞
) : (∏ i in s, f i / g i) = (∏ i in s, f i) / (∏ i in s, g i)
参数：hg : (s : Set ι).Pairwise fun i j => g i != 0 ∨ g j != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `ENNReal.prod_inv_distrib`：prod_inv_distrib (hf : (s : Set ι).Pairwise fu
n i j => f i != 0 ∨ f j != ∞) : (∏ i in s, f i)⁻¹ = ∏ i in s, (f i)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_div_distrib (hg : (s : Set ι).Pairwise fun i j ↦ g i ≠ 0 ∨ g j ≠ ∞) :
    (∏ i ∈ s, f i / g i) = (∏ i ∈ s, f i) / (∏ i ∈ s, g i) := by
  simp only [div_eq_mul_inv, prod_inv_distrib hg, ← Finset.prod_mul_distrib]
/-
**ENNReal.prod_div_distrib_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：prod_div_distrib_of_ne_top (hg : forall i in s, g i != ∞) : (∏ i in s, f i
 / g i) = (∏ i in s, f i) / (∏ i in s, g i)
参数：hg : forall i in s, g i != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.prod_div_distrib`：prod_div_distrib (hg : (s : Set ι).Pairwise fu
n i j => g i != 0 ∨ g j != ∞) : (∏ i in s, f i / g i) = (∏ i in s, f i) / (∏ i i
n s, g i)
-/
lemma prod_div_distrib_of_ne_top (hg : ∀ i ∈ s, g i ≠ ∞) :
    (∏ i ∈ s, f i / g i) = (∏ i ∈ s, f i) / (∏ i ∈ s, g i) :=
  prod_div_distrib (by grind [Set.Pairwise])
/-
**ENNReal.prod_div_distrib_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：prod_div_distrib_of_ne_zero (hg : forall i in s, g i != 0) : (∏ i in s, f 
i / g i) = (∏ i in s, f i) / (∏ i in s, g i)
参数：hg : forall i in s, g i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.prod_div_distrib`：prod_div_distrib (hg : (s : Set ι).Pairwise fu
n i j => g i != 0 ∨ g j != ∞) : (∏ i in s, f i / g i) = (∏ i in s, f i) / (∏ i i
n s, g i)
-/
lemma prod_div_distrib_of_ne_zero (hg : ∀ i ∈ s, g i ≠ 0) :
    (∏ i ∈ s, f i / g i) = (∏ i ∈ s, f i) / (∏ i ∈ s, g i) :=
  prod_div_distrib (by grind [Set.Pairwise])
/-
**ENNReal.finsetSum_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：finsetSum_iSup {α : Type*} {s : Finset α} {f : α -> ι -> Real>=0∞} (hf : f
orall i j, exists k, forall a, f a i <= f a k ∧ f a j <= f a k) : ∑ a in s, ⨆ i,
 f a i = ⨆ i, ∑ a in s, f a i
参数：hf : forall i j, exists k, forall a, f a i <= f a k ∧ f a j <= f a k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.iSup_zero`：∀ {ι : Sort u_1}, ⨆ x, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ENNReal.iSup_add_iSup`：iSup_add_iSup (h : forall i j, exists k, f i + g 
j <= f k + g k) : iSup f + iSup g = ⨆ i, f i + g i
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma finsetSum_iSup {α : Type*} {s : Finset α} {f : α → ι → ℝ≥0∞}
    (hf : ∀ i j, ∃ k, ∀ a, f a i ≤ f a k ∧ f a j ≤ f a k) :
    ∑ a ∈ s, ⨆ i, f a i = ⨆ i, ∑ a ∈ s, f a i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ihs =>
    simp_rw [Finset.sum_cons, ihs]
    refine iSup_add_iSup fun i j ↦ (hf i j).imp fun k hk ↦ ?_
    gcongr
    exacts [(hk a).1, (hk _).2]
/-
**ENNReal.finsetSum_iSup_of_monotone** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：finsetSum_iSup_of_monotone {α : Type*} [Preorder ι] [IsDirectedOrder ι] {s
 : Finset α} {f : α -> ι -> Real>=0∞} (hf : forall a, Monotone (f a)) : (∑ a in 
s, iSup (f a)) = ⨆ n, ∑ a in s, f a n
参数：hf : forall a, Monotone (f a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.finsetSum_iSup`：finsetSum_iSup {α : Type*} {s : Finset α} {f : α
 -> ι -> Real>=0∞} (hf : forall i j, exists k, forall a, f a i <= f a k ∧ f a j 
<= f a k) : …
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c
-/
lemma finsetSum_iSup_of_monotone {α : Type*} [Preorder ι] [IsDirectedOrder ι] {s : Finset α}
    {f : α → ι → ℝ≥0∞} (hf : ∀ a, Monotone (f a)) : (∑ a ∈ s, iSup (f a)) = ⨆ n, ∑ a ∈ s, f a n :=
  finsetSum_iSup fun i j ↦ (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ a ↦ ⟨hf a hi, hf a hj⟩

end Inv

end ENNReal

