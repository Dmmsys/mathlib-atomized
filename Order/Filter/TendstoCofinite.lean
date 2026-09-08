/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Bingyu Xia
-/
module

public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Data.Finsupp.Weight

/-!
# Functions tending to the cofinite filter

This file introduces the typeclass `Filter.TendstoCofinite`, which represents functions
`f : α → β` that tend to the cofinite filter along the cofinite filter. Functions of this class
are precisely the valid index transformations for renaming variables in multivariate power series.

## Main definitions

* `Filter.TendstoCofinite`: A typeclass for functions `f` satisfying
  `Filter.Tendsto f cofinite cofinite`. By `Filter.tendstoCofinite_iff_finite_preimage_singleton`,
  this is equivalent to `f` having finite fibers.
* `Filter.TendstoCofinite.mapDomain`: Given a function `v : α → M` into an `AddCommMonoid`,
  this is the pushforward function `β → M` defined by summing the values of `v` over the
  finite fibers of `f`.

## Main results

* `Filter.tendstoCofinite_iff_finite_preimage_singleton`: Characterizes `TendstoCofinite`
  as exactly those functions with finite fibers.
* Basic instances of `TendstoCofinite`.
* `Finsupp.mapDomain_tendstoCofinite`: Pushing forward finitely supported functions along
  a `TendstoCofinite` function preserves the `TendstoCofinite` property.

-/

@[expose] public section

variable {α β ι R M : Type*} (f : α → β) (g : β → ι) [AddCommMonoid M]

open Set Filter

namespace Filter

/-- The class of functions `f` such that `Tendsto f cofinite cofinite`, it is equivalent to
`f` having finite fibers, see `Filter.tendstoCofinite_iff_finite_preimage_singleton`. -/
/-
**Filter.TendstoCofinite** 是 Mathlib 中的一个归纳类型，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → Prop
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of functions `f` such that `Tendsto f cofinite cofinite`, it is equiva
lent to
`f` having finite fibers, see `Filter.tendstoCofinite_iff_finite_preimage_single
ton`.
-/
@[mk_iff] class TendstoCofinite (f : α → β) : Prop where
  tendsto_cofinite (f) : Tendsto f cofinite cofinite
/-
**Filter.TendstoCofinite.finite_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tends
toCofinite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β) [Filter.TendstoCofinite f] {s 
: Set β}, s.Finite → (f ⁻¹' s).Finite
参数：f : α → β；f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.TendstoCofinite.tendsto_cofinite`：∀ {α : Type u_1} {β : Type u_2}
 (f : α → β) [self : Filter.TendstoCofinite f],   Filter.Tendsto f Filter.cofini
te Filter.cofinite
-/
lemma TendstoCofinite.finite_preimage [TendstoCofinite f] {s : Set β} (hs : s.Finite) :
    Set.Finite (f ⁻¹' s) := by
  simpa [compl_eq_univ_sdiff] using TendstoCofinite.tendsto_cofinite f
    (show univ \ s ∈ cofinite by simpa [compl_eq_univ_sdiff])
/-
**Filter.TendstoCofinite.finite_preimage_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Fi
lter.TendstoCofinite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β) [Filter.TendstoCofinite f] (b 
: β), (f ⁻¹' {b}).Finite
参数：f : α → β；b : β；f ⁻¹' {b}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.TendstoCofinite.finite_preimage`：∀ {α : Type u_1} {β : Type u_2} 
(f : α → β) [Filter.TendstoCofinite f] {s : Set β}, s.Finite → (f ⁻¹' s).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma TendstoCofinite.finite_preimage_singleton [TendstoCofinite f] (b : β) :
    Set.Finite (f ⁻¹' {b}) := by simpa using TendstoCofinite.finite_preimage f (by simp)
/-
**Filter.tendstoCofinite_iff_finite_preimage_singleton** 是 Mathlib 中的一个定理，位于命名空间
 `Filter`。
形式化陈述：tendstoCofinite_iff_finite_preimage_singleton : TendstoCofinite f ↔ forall
 b : β, Set.Finite (f ⁻¹' {b})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.TendstoCofinite.finite_preimage_singleton`：∀ {α : Type u_1} {β : 
Type u_2} (f : α → β) [Filter.TendstoCofinite f] (b : β), (f ⁻¹' {b}).Finite
· 使用定理 `Filter.Tendsto.cofinite_of_finite_preimage_singleton`：Filter.Tendsto.cof
inite_of_finite_preimage_singleton {f : α -> β} (hf : forall b, Finite (f ⁻¹' {b
})) : Tendsto f cofinite cofinite
-/
theorem tendstoCofinite_iff_finite_preimage_singleton : TendstoCofinite f ↔
    ∀ b : β, Set.Finite (f ⁻¹' {b}) := ⟨fun _ ↦ TendstoCofinite.finite_preimage_singleton f,
  fun h ↦ ⟨Tendsto.cofinite_of_finite_preimage_singleton h⟩⟩

variable {f} in
/-
**Filter.tendstoCofinite_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendstoCofinite_of_injective (h : f.Injective) : TendstoCofinite f
参数：h : f.Injective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.tendsto_cofinite`：Function.Injective.tendsto_cofinite
 {f : α -> β} (hf : Injective f) : Tendsto f cofinite cofinite
-/
lemma tendstoCofinite_of_injective (h : f.Injective) : TendstoCofinite f := ⟨h.tendsto_cofinite⟩

@[instance]
/-
**Filter.tendstoCofinite_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendstoCofinite_of_finite [Finite α] : TendstoCofinite f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendstoCofinite_iff_finite_preimage_singleton`：tendstoCofinite_if
f_finite_preimage_singleton : TendstoCofinite f ↔ forall b : β, Set.Finite (f ⁻¹
' {b})
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
lemma tendstoCofinite_of_finite [Finite α] : TendstoCofinite f :=
  (tendstoCofinite_iff_finite_preimage_singleton f).mpr fun b ↦ Set.toFinite (f ⁻¹' {b})

namespace TendstoCofinite

@[instance]
/-
**Filter.TendstoCofinite.comp** 是 Mathlib 中的一个引理，位于命名空间 `Filter.TendstoCofinite`
。
形式化陈述：comp [TendstoCofinite g] [TendstoCofinite f] : TendstoCofinite (g ∘ f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendstoCofinite_iff_finite_preimage_singleton`：tendstoCofinite_if
f_finite_preimage_singleton : TendstoCofinite f ↔ forall b : β, Set.Finite (f ⁻¹
' {b})
· 使用定理 `Filter.TendstoCofinite.finite_preimage`：∀ {α : Type u_1} {β : Type u_2} 
(f : α → β) [Filter.TendstoCofinite f] {s : Set β}, s.Finite → (f ⁻¹' s).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma comp [TendstoCofinite g] [TendstoCofinite f] : TendstoCofinite (g ∘ f) :=
  (tendstoCofinite_iff_finite_preimage_singleton _).mpr (fun r ↦ by
    simpa using! TendstoCofinite.finite_preimage f (TendstoCofinite.finite_preimage g (by simp)))

@[instance]
/-
**Filter.TendstoCofinite.id** 是 Mathlib 中的一个引理，位于命名空间 `Filter.TendstoCofinite`。
形式化陈述：id : TendstoCofinite (id : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma id : TendstoCofinite (id : α → α) := by simp [tendstoCofinite_iff_finite_preimage_singleton]

@[instance]
/-
**Filter.TendstoCofinite.embedding** 是 Mathlib 中的一个引理，位于命名空间 `Filter.TendstoCofi
nite`。
形式化陈述：embedding (e : α ↪ β) : TendstoCofinite e
参数：e : α ↪ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.tendsto_cofinite`：Function.Injective.tendsto_cofinite
 {f : α -> β} (hf : Injective f) : Tendsto f cofinite cofinite
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
lemma embedding (e : α ↪ β) : TendstoCofinite e := ⟨e.injective.tendsto_cofinite⟩

@[instance]
/-
**Filter.TendstoCofinite.equiv** 是 Mathlib 中的一个引理，位于命名空间 `Filter.TendstoCofinite
`。
形式化陈述：equiv (e : α ≃ β) : TendstoCofinite e
参数：e : α ≃ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.tendsto_cofinite`：Function.Injective.tendsto_cofinite
 {f : α -> β} (hf : Injective f) : Tendsto f cofinite cofinite
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma equiv (e : α ≃ β) : TendstoCofinite e := ⟨e.injective.tendsto_cofinite⟩

variable [TendstoCofinite f]

/-- Given `f : α → β` with `Filter.TendstoCofinite f` and `v : α → M`,
`Filter.TendstoCofinite.mapDomain f v : β → M` is the function whose value at `b : β` is
the sum of `v x` over all `x` such that `f x = b`. -/
/-
**Filter.TendstoCofinite.mapDomain** 是 Mathlib 中的一个定义，位于命名空间 `Filter.TendstoCofi
nite`。
形式化陈述：mapDomain (v : α -> M) : β -> M
参数：v : α -> M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.TendstoCofinite.finite_preimage_singleton`：∀ {α : Type u_1} {β : 
Type u_2} (f : α → β) [Filter.TendstoCofinite f] (b : β), (f ⁻¹' {b}).Finite

--- 原说明 ---
Given `f : α → β` with `Filter.TendstoCofinite f` and `v : α → M`,
`Filter.TendstoCofinite.mapDomain f v : β → M` is the function whose value at `b
 : β` is
the sum of `v x` over all `x` such that `f x = b`.
-/
noncomputable def mapDomain (v : α → M) : β → M :=
  fun i ↦ (finite_preimage_singleton f i).toFinset.sum v

@[simp]
/-
**Filter.TendstoCofinite.mapDomain_add** 是 Mathlib 中的一个引理，位于命名空间 `Filter.Tendsto
Cofinite`。
形式化陈述：mapDomain_add (u v : α -> M) : mapDomain f (u + v) = mapDomain f u + mapDo
main f v
参数：u v : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.TendstoCofinite.finite_preimage_singleton`：∀ {α : Type u_1} {β : 
Type u_2} (f : α → β) [Filter.TendstoCofinite f] (b : β), (f ⁻¹' {b}).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomain_add (u v : α → M) : mapDomain f (u + v) = mapDomain f u + mapDomain f v := by
  ext; simp [mapDomain, Finset.sum_add_distrib]

@[simp]
/-
**Filter.TendstoCofinite.mapDomain_smul** 是 Mathlib 中的一个引理，位于命名空间 `Filter.Tendst
oCofinite`。
形式化陈述：mapDomain_smul [DistribSMul R M] (r : R) (v : α -> M) : mapDomain f (r • v
) = r • (mapDomain f v)
参数：r : R；v : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.TendstoCofinite.finite_preimage_singleton`：∀ {α : Type u_1} {β : 
Type u_2} (f : α → β) [Filter.TendstoCofinite f] (b : β), (f ⁻¹' {b}).Finite
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomain_smul [DistribSMul R M] (r : R) (v : α → M) :
    mapDomain f (r • v) = r • (mapDomain f v) := by ext; simp [mapDomain, Finset.smul_sum]
/-
**Filter.TendstoCofinite.mapDomain_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Ten
dstoCofinite`。
形式化陈述：mapDomain_eq_zero (v : α -> M) {i : β} (h' : i ∉ Set.range f) : mapDomain 
f v i = 0
参数：v : α -> M；h' : i ∉ Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.TendstoCofinite.finite_preimage_singleton`：∀ {α : Type u_1} {β : 
Type u_2} (f : α → β) [Filter.TendstoCofinite f] (b : β), (f ⁻¹' {b}).Finite
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_singleton_eq_empty`：preimage_singleton_eq_empty {f : α -> β
} {y : β} : f ⁻¹' {y} = ∅ ↔ y ∉ range f
· 使用定理 `Set.toFinset_empty`：toFinset_empty [Fintype (∅ : Set α)] : (∅ : Set α).t
oFinset = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapDomain_eq_zero (v : α → M) {i : β} (h' : i ∉ Set.range f) : mapDomain f v i = 0 := by
  rw [← Set.preimage_singleton_eq_empty] at h'
  simp [mapDomain, Set.Finite.toFinset, h']

end TendstoCofinite

end Filter

@[instance]
/-
**Finsupp.mapDomain_tendstoCofinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finsupp.mapDomain_tendstoCofinite [TendstoCofinite f] : TendstoCofinite (m
apDomain (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendstoCofinite_iff_finite_preimage_singleton`：tendstoCofinite_if
f_finite_preimage_singleton : TendstoCofinite f ↔ forall b : β, Set.Finite (f ⁻¹
' {b})
· 使用定理 `Filter.TendstoCofinite.finite_preimage_singleton`：∀ {α : Type u_1} {β : 
Type u_2} (f : α → β) [Filter.TendstoCofinite f] (b : β), (f ⁻¹' {b}).Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Finsupp.finite_of_degree_le`：finite_of_degree_le [Finite σ] (n : Nat) : 
{f : σ ->₀ Nat | degree f <= n}.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.degree_mapDomain`：degree_mapDomain {τ : Type*} (f : σ -> τ) [Add
CommMonoid M] (x : σ ->₀ M) : degree (x.mapDomain f) = degree x
· 使用定理 `Finsupp.degree_comapDomain_le_of_canonicallyOrderedAdd`：degree_comapDoma
in_le_of_canonicallyOrderedAdd {τ : Type*} {f : σ -> τ} [AddCommMonoid M] [Parti
alOrder M] [CanonicallyOrderedAdd M] {x : τ …
· 使用引理 `Finsupp.embDomain_comapDomain`：embDomain_comapDomain {f : α ↪ β} {g : β 
->₀ M} (hg : ↑g.support subseteq Set.range f) : embDomain f (comapDomain f g f.i
njective.injOn) = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_finsetSum`：∀ {α : Type u_1} {ι : Type u_2} {N : Type u_10} [
inst : AddCommMonoid N] (S : Finset ι) (f : ι → α →₀ N),   ⇑(∑ i ∈ S, f i) = ∑ i
 ∈ S, ⇑(f i…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 33 条，此处仅展示前 30 条）
-/
theorem Finsupp.mapDomain_tendstoCofinite [TendstoCofinite f] :
    TendstoCofinite (mapDomain (M := ℕ) f) := by
  classical
  refine (tendstoCofinite_iff_finite_preimage_singleton _).mpr fun x ↦ ?_
  let s := Finset.sup x.support (fun t ↦ (TendstoCofinite.finite_preimage_singleton f t).toFinset)
  let e : s ↪ α := Function.Embedding.subtype (fun u ↦ u ∈ s)
  refine Set.Finite.subset (Set.Finite.image (embDomain e) <| finite_of_degree_le (degree x)) ?_
  simp only [Set.subset_def, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image,
    Set.mem_ofPred_eq]
  refine fun y hy ↦ ⟨y.comapDomain e e.injective.injOn, ?_, embDomain_comapDomain ?_⟩
  · rw [← hy, degree_mapDomain]
    exact degree_comapDomain_le_of_canonicallyOrderedAdd ..
  · suffices y.support ⊆ s by simpa [e]
    simpa [← hy, mapDomain, sum, Finset.subset_iff, single_apply, s] using
      fun i hi ↦ ⟨i, by simp [hi]⟩
