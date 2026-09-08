/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.NNRat.Defs

/-! # Casting lemmas for non-negative rational numbers involving sums and products
-/

public section

variable {α : Type*}

namespace NNRat

section DivisionSemiring

variable {K : Type*} [DivisionSemiring K] [CharZero K]

@[norm_cast]
/-
**NNRat.cast_listSum** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：cast_listSum (l : List Rat>=0) : (l.sum : K) = (l.map (↑)).sum
参数：l : List Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem cast_listSum (l : List ℚ≥0) : (l.sum : K) = (l.map (↑)).sum :=
  map_list_sum (castHom _) _

@[norm_cast]
/-
**NNRat.cast_listProd** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：cast_listProd (l : List Rat>=0) : (l.prod : K) = (l.map (↑)).prod
参数：l : List Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem cast_listProd (l : List ℚ≥0) : (l.prod : K) = (l.map (↑)).prod :=
  map_list_prod (castHom _) _

@[norm_cast]
/-
**NNRat.cast_multisetSum** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：cast_multisetSum (s : Multiset Rat>=0) : (s.sum : K) = (s.map (↑)).sum
参数：s : Multiset Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_sum`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst :
 AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : FunLike F M N] [AddMono
idHomC…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem cast_multisetSum (s : Multiset ℚ≥0) : (s.sum : K) = (s.map (↑)).sum :=
  map_multiset_sum (castHom _) _

@[norm_cast]
/-
**NNRat.cast_sum** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：cast_sum (s : Finset α) (f : α -> Rat>=0) : ↑(∑ a in s, f a) = ∑ a in s, (
f a : K)
参数：s : Finset α；f : α -> Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem cast_sum (s : Finset α) (f : α → ℚ≥0) : ↑(∑ a ∈ s, f a) = ∑ a ∈ s, (f a : K) :=
  map_sum (castHom _) _ _

end DivisionSemiring

section Semifield

variable {K : Type*} [Semifield K] [CharZero K]

@[norm_cast]
/-
**NNRat.cast_multisetProd** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：cast_multisetProd (s : Multiset Rat>=0) : (s.prod : K) = (s.map (↑)).prod
参数：s : Multiset Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_prod`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst 
: CommMonoid M] [inst_1 : CommMonoid N] [inst_2 : FunLike F M N]   [MonoidHomCla
ss F M …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem cast_multisetProd (s : Multiset ℚ≥0) : (s.prod : K) = (s.map (↑)).prod :=
  map_multiset_prod (castHom _) _

@[norm_cast]
/-
**NNRat.cast_prod** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：cast_prod (s : Finset α) (f : α -> Rat>=0) : ↑(∏ a in s, f a) = ∏ a in s, 
(f a : K)
参数：s : Finset α；f : α -> Rat>=0。
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
theorem cast_prod (s : Finset α) (f : α → ℚ≥0) : ↑(∏ a ∈ s, f a) = ∏ a ∈ s, (f a : K) :=
  map_prod (castHom _) _ _

end Semifield

section Rat

/-
**NNRat.toNNRat_sum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：toNNRat_sum_of_nonneg {s : Finset α} {f : α -> Rat} (hf : forall a, a in s
 -> 0 <= f a) : (∑ a in s, f a).toNNRat = ∑ a in s, (f a).toNNRat
参数：hf : forall a, a in s -> 0 <= f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.coe_inj`：coe_inj : (p : Rat) = q ↔ p = q
· 使用定理 `NNRat.cast_sum`：cast_sum (s : Finset α) (f : α -> Rat>=0) : ↑(∑ a in s, 
f a) = ∑ a in s, (f a : K)
· 使用定理 `Rat.coe_toNNRat`：∀ (q : ℚ), 0 ≤ q → ↑q.toNNRat = q
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
-/
theorem toNNRat_sum_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    (∑ a ∈ s, f a).toNNRat = ∑ a ∈ s, (f a).toNNRat := by
  rw [← coe_inj, cast_sum, Rat.coe_toNNRat _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs ↦ by rw [Rat.coe_toNNRat _ (hf x hxs)]
/-
**NNRat.toNNRat_prod_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：toNNRat_prod_of_nonneg {s : Finset α} {f : α -> Rat} (hf : forall a in s, 
0 <= f a) : (∏ a in s, f a).toNNRat = ∏ a in s, (f a).toNNRat
参数：hf : forall a in s, 0 <= f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.coe_inj`：coe_inj : (p : Rat) = q ↔ p = q
· 使用定理 `NNRat.cast_prod`：cast_prod (s : Finset α) (f : α -> Rat>=0) : ↑(∏ a in s
, f a) = ∏ a in s, (f a : K)
· 使用定理 `Rat.coe_toNNRat`：∀ (q : ℚ), 0 ≤ q → ↑q.toNNRat = q
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
theorem toNNRat_prod_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a ∈ s, 0 ≤ f a) :
    (∏ a ∈ s, f a).toNNRat = ∏ a ∈ s, (f a).toNNRat := by
  rw [← coe_inj, cast_prod, Rat.coe_toNNRat _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs ↦ by rw [Rat.coe_toNNRat _ (hf x hxs)]

end Rat

end NNRat

