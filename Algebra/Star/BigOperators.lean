/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Tactic.ContinuousFunctionalCalculus

/-! # Big-operators lemmas about `star` algebraic operations

These results are kept separate from `Algebra.Star.Basic` to avoid it needing to import `Finset`.
-/

public section


variable {R : Type*}

@[simp]
/-
**star_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_prod [CommMonoid R] [StarMul R] {α : Type*} (s : Finset α) (f : α -> 
R) : star (∏ x in s, f x) = ∏ x in s, star (f x)
参数：s : Finset α；f : α -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem star_prod [CommMonoid R] [StarMul R] {α : Type*} (s : Finset α) (f : α → R) :
    star (∏ x ∈ s, f x) = ∏ x ∈ s, star (f x) := map_prod (starMulAut : R ≃* R) _ _

@[simp]
/-
**star_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_sum [AddCommMonoid R] [StarAddMonoid R] {α : Type*} (s : Finset α) (f
 : α -> R) : star (∑ x in s, f x) = ∑ x in s, star (f x)
参数：s : Finset α；f : α -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem star_sum [AddCommMonoid R] [StarAddMonoid R] {α : Type*} (s : Finset α) (f : α → R) :
    star (∑ x ∈ s, f x) = ∑ x ∈ s, star (f x) := map_sum (starAddEquiv : R ≃+ R) _ _

@[aesop safe apply (rule_sets := [CStarAlgebra])]
/-
**isSelfAdjoint_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSelfAdjoint_sum {ι : Type*} [AddCommMonoid R] [StarAddMonoid R] (s : Fin
set ι) {x : ι -> R} (h : forall i in s, IsSelfAdjoint (x i)) : IsSelfAdjoint (∑ 
i in s, x i)
参数：s : Finset ι；h : forall i in s, IsSelfAdjoint (x i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_sum`：star_sum [AddCommMonoid R] [StarAddMonoid R] {α : Type*} (s : 
Finset α) (f : α -> R) : star (∑ x in s, f x) = ∑ x in s, star (f x)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
-/
theorem isSelfAdjoint_sum {ι : Type*} [AddCommMonoid R] [StarAddMonoid R] (s : Finset ι)
    {x : ι → R} (h : ∀ i ∈ s, IsSelfAdjoint (x i)) : IsSelfAdjoint (∑ i ∈ s, x i) := by
  simpa [IsSelfAdjoint, star_sum] using Finset.sum_congr rfl fun _ hi => h _ hi

@[simp]
/-
**star_finsuppSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_finsuppSum {ι : Type*} {M : Type*} [Zero M] [AddCommMonoid R] [StarAd
dMonoid R] (s : ι ->₀ M) (f : ι -> M -> R) : star (s.sum f) = s.sum (fun i m => 
star f i m)
参数：s : ι ->₀ M；f : ι -> M -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_sum`：star_sum [AddCommMonoid R] [StarAddMonoid R] {α : Type*} (s : 
Finset α) (f : α -> R) : star (∑ x in s, f x) = ∑ x in s, star (f x)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem star_finsuppSum {ι : Type*} {M : Type*} [Zero M] [AddCommMonoid R] [StarAddMonoid R]
    (s : ι →₀ M) (f : ι → M → R) : star (s.sum f) = s.sum (fun i m ↦ star f i m) := by
  simp [Finsupp.sum]

@[simp]
/-
**star_finsuppProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_finsuppProd {ι : Type*} {M : Type*} [Zero M] [CommMonoid R] [StarMul 
R] (s : ι ->₀ M) (f : ι -> M -> R) : star (s.prod f) = s.prod (fun i m => star f
 i m)
参数：s : ι ->₀ M；f : ι -> M -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_prod`：star_prod [CommMonoid R] [StarMul R] {α : Type*} (s : Finset 
α) (f : α -> R) : star (∏ x in s, f x) = ∏ x in s, star (f x)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem star_finsuppProd {ι : Type*} {M : Type*} [Zero M] [CommMonoid R] [StarMul R]
    (s : ι →₀ M) (f : ι → M → R) : star (s.prod f) = s.prod (fun i m ↦ star f i m) := by
  simp [Finsupp.prod]
