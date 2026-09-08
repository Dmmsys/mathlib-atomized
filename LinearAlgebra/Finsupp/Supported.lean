/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# `Finsupp`s supported on a given submodule

* `Finsupp.restrictDom`: `Finsupp.filter` as a linear map to `Finsupp.supported s`;
  `Finsupp.supported R R s` and codomain `Submodule.span R (v '' s)`;
* `Finsupp.supportedEquivFinsupp`: a linear equivalence between the functions `α →₀ M` supported
  on `s` and the functions `s →₀ M`;
* `Finsupp.domLCongr`: a `LinearEquiv` version of `Finsupp.domCongr`;
* `Finsupp.congr`: if the sets `s` and `t` are equivalent, then `supported M R s` is equivalent to
  `supported M R t`;

## Tags

function with finite support, module, linear algebra
-/

@[expose] public section

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

variable (M R)

/-- `Finsupp.supported M R s` is the `R`-submodule of all `p : α →₀ M` such that `p.support ⊆ s`. -/
/-
**Finsupp.supported** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：supported (s : Set α) : Submodule R (α ->₀ M) where carrier
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp.supported M R s` is the `R`-submodule of all `p : α →₀ M` such that `p.
support ⊆ s`.
-/
def supported (s : Set α) : Submodule R (α →₀ M) where
  carrier := { p | ↑p.support ⊆ s }
  add_mem' {p q} hp hq := by
    classical
    refine Subset.trans (Subset.trans (Finset.coe_subset.2 support_add) ?_) (union_subset hp hq)
    rw [Finset.coe_union]
  zero_mem' := by
    simp only [subset_def, Finset.mem_coe, Set.mem_ofPred_eq, mem_support_iff, zero_apply]
    intro h ha
    exact (ha rfl).elim
  smul_mem' _ _ hp := Subset.trans (Finset.coe_subset.2 support_smul) hp

variable {M}
/-
**Finsupp.mem_supported** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_supported {s : Set α} (p : α ->₀ M) : p in supported M R s ↔ ↑p.suppor
t subseteq s
参数：p : α ->₀ M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_supported {s : Set α} (p : α →₀ M) : p ∈ supported M R s ↔ ↑p.support ⊆ s :=
  Iff.rfl
/-
**Finsupp.mem_supported'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_supported' {s : Set α} (p : α ->₀ M) : p in supported M R s ↔ forall x
 ∉ s, p x = 0
参数：p : α ->₀ M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_supported' {s : Set α} (p : α →₀ M) :
    p ∈ supported M R s ↔ ∀ x ∉ s, p x = 0 := by
  simp [mem_supported, Set.subset_def, not_imp_comm]
/-
**Finsupp.mem_supported_support** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_supported_support (p : α ->₀ M) : p in Finsupp.supported M R (p.suppor
t : Set α)
参数：p : α ->₀ M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mem_supported`：mem_supported {s : Set α} (p : α ->₀ M) : p in su
pported M R s ↔ ↑p.support subseteq s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mem_supported_support (p : α →₀ M) : p ∈ Finsupp.supported M R (p.support : Set α) := by
  rw [Finsupp.mem_supported]
/-
**Finsupp.single_mem_supported** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_mem_supported {s : Set α} {a : α} (b : M) (h : a in s) : single a b
 in supported M R s
参数：b : M；h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_set_iff`：singleton_subset_set_iff {s : Set α} {a
 : α} : ↑({a} : Finset α) subseteq s ↔ a in s
-/
theorem single_mem_supported {s : Set α} {a : α} (b : M) (h : a ∈ s) :
    single a b ∈ supported M R s :=
  Set.Subset.trans support_single_subset (Finset.singleton_subset_set_iff.2 h)
/-
**Finsupp.supported_eq_span_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：supported_eq_span_single (s : Set α) : supported R R s = span R ((fun i =>
 single i 1) '' s)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_eq_of_le`：span_eq_of_le (h₁ : s subseteq p) (h₂ : p <= sp
an R s) : span R s = p
· 使用定理 `Finsupp.single_mem_supported`：single_mem_supported {s : Set α} {a : α} (
b : M) (h : a in s) : single a b in supported M R s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_single`：sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum s
ingle = f
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem supported_eq_span_single (s : Set α) :
    supported R R s = span R ((fun i => single i 1) '' s) := by
  refine (span_eq_of_le _ ?_ (SetLike.le_def.2 fun l hl => ?_)).symm
  · rintro _ ⟨_, hp, rfl⟩
    exact single_mem_supported R 1 hp
  · rw [← l.sum_single]
    refine sum_mem fun i il => ?_
    rw [show single i (l i) = l i • single i 1 by simp]
    exact smul_mem _ (l i) (subset_span (mem_image_of_mem _ (hl il)))
/-
**Finsupp.single_mem_span_single** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：single_mem_span_single [Nontrivial R] {a : α} {s : Set α} : single a 1 in 
Submodule.span R ((single · (1 : R)) '' s) ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
· 使用定理 `Finsupp.mem_supported`：mem_supported {s : Set α} (p : α ->₀ M) : p in su
pported M R s ↔ ↑p.support subseteq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.supported_eq_span_single`：supported_eq_span_single (s : Set α) :
 supported R R s = span R ((fun i => single i 1) '' s)
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma single_mem_span_single [Nontrivial R] {a : α} {s : Set α} :
    single a 1 ∈ Submodule.span R ((single · (1 : R)) '' s) ↔ a ∈ s := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span <| Set.mem_image_of_mem _ h⟩
  rw [← Finsupp.supported_eq_span_single, Finsupp.mem_supported,
    Finsupp.support_single _ (one_ne_zero' R)] at h
  simpa using h
/-
**Finsupp.span_le_supported_biUnion_support** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：span_le_supported_biUnion_support (s : Set (α ->₀ M)) : span R s <= suppor
ted M R (⋃ x in s, x.support)
参数：s : Set (α ->₀ M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
-/
theorem span_le_supported_biUnion_support (s : Set (α →₀ M)) :
    span R s ≤ supported M R (⋃ x ∈ s, x.support) :=
  span_le.mpr fun _ h ↦ subset_biUnion_of_mem h (u := (SetLike.coe ·.support))

variable (M)

/-- Interpret `Finsupp.filter s` as a linear map from `α →₀ M` to `supported M R s`. -/
/-
**Finsupp.restrictDom** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：restrictDom (s : Set α) [DecidablePred (· in s)] : (α ->₀ M) ->ₗ[R] suppor
ted M R s
参数：s : Set α；· in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret `Finsupp.filter s` as a linear map from `α →₀ M` to `supported M R s`.
-/
def restrictDom (s : Set α) [DecidablePred (· ∈ s)] : (α →₀ M) →ₗ[R] supported M R s :=
  LinearMap.codRestrict _
    { toFun := filter (· ∈ s)
      map_add' := fun _ _ => filter_add
      map_smul' := fun _ _ => filter_smul } fun l =>
    (mem_supported' _ _).2 fun _ => filter_apply_neg (· ∈ s) l

variable {M R}

section

@[simp]
/-
**Finsupp.restrictDom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：restrictDom_apply (s : Set α) (l : α ->₀ M) [DecidablePred (· in s)] : (re
strictDom M R s l : α ->₀ M) = Finsupp.filter (· in s) l
参数：s : Set α；l : α ->₀ M；· in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictDom_apply (s : Set α) (l : α →₀ M) [DecidablePred (· ∈ s)] :
    (restrictDom M R s l : α →₀ M) = Finsupp.filter (· ∈ s) l := rfl

end

/-
**Finsupp.restrictDom_comp_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：restrictDom_comp_subtype (s : Set α) [DecidablePred (· in s)] : (restrictD
om M R s).comp (Submodule.subtype _) = LinearMap.id
参数：s : Set α；· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.filter_apply_pos`：filter_apply_pos {a : α} (h : p a) : f.filter 
p a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.filter_apply_neg`：filter_apply_neg {a : α} (h : ¬p a) : f.filter
 p a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_supported'`：mem_supported' {s : Set α} (p : α ->₀ M) : p in 
supported M R s ↔ forall x ∉ s, p x = 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem restrictDom_comp_subtype (s : Set α) [DecidablePred (· ∈ s)] :
    (restrictDom M R s).comp (Submodule.subtype _) = LinearMap.id := by
  ext l a
  by_cases h : a ∈ s
  · simp [h]
  simpa [h] using ((mem_supported' R l.1).1 l.2 a h).symm
/-
**Finsupp.range_restrictDom** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：range_restrictDom (s : Set α) [DecidablePred (· in s)] : LinearMap.range (
restrictDom M R s) = ⊤
参数：s : Set α；· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Finsupp.restrictDom_comp_subtype`：restrictDom_comp_subtype (s : Set α) [
DecidablePred (· in s)] : (restrictDom M R s).comp (Submodule.subtype _) = Linea
rMap.id
-/
theorem range_restrictDom (s : Set α) [DecidablePred (· ∈ s)] :
    LinearMap.range (restrictDom M R s) = ⊤ :=
  range_eq_top.2 <|
    Function.RightInverse.surjective <| LinearMap.congr_fun (restrictDom_comp_subtype s)
/-
**Finsupp.supported_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：supported_mono {s t : Set α} (st : s subseteq t) : supported M R s <= supp
orted M R t
参数：st : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
-/
theorem supported_mono {s t : Set α} (st : s ⊆ t) : supported M R s ≤ supported M R t := fun _ h =>
  Set.Subset.trans h st

@[simp]
/-
**Finsupp.supported_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：supported_empty : supported M R (∅ : Set α) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem supported_empty : supported M R (∅ : Set α) = ⊥ :=
  eq_bot_iff.2 fun l h => (Submodule.mem_bot R).2 <| by ext; simp_all [mem_supported']

@[simp]
/-
**Finsupp.supported_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：supported_univ : supported M R (Set.univ : Set α) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem supported_univ : supported M R (Set.univ : Set α) = ⊤ :=
  eq_top_iff.2 fun _ _ => Set.subset_univ _
/-
**Finsupp.supported_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：supported_iUnion {δ : Type*} (s : δ -> Set α) : supported M R (⋃ i, s i) =
 ⨆ i, supported M R (s i)
参数：s : δ -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_le_iff_comap`：range_le_iff_comap [RingHomSurjective τ₁₂]
 {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R₂ M₂} : range f <= p ↔ comap f p = ⊤
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Finsupp.induction`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass 
M] {motive : (ι →₀ M) → Prop} (f : ι →₀ M),   motive 0 →     (∀ (a : ι) (b : M) 
(f : ι …
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.filter_single_of_pos`：filter_single_of_pos {a : α} {b : M} (h : 
p a) : (single a b).filter p = single a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Finsupp.single_mem_supported`：single_mem_supported {s : Set α} {a : α} (
b : M) (h : a in s) : single a b in supported M R s
· 使用定理 `Finsupp.filter_single_of_neg`：filter_single_of_neg {a : α} {b : M} (h : 
¬p a) : (single a b).filter p = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Finsupp.range_restrictDom`：range_restrictDom (s : Set α) [DecidablePred 
(· in s)] : LinearMap.range (restrictDom M R s) = ⊤
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Finsupp.supported_mono`：supported_mono {s t : Set α} (st : s subseteq t)
 : supported M R s <= supported M R t
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
-/
theorem supported_iUnion {δ : Type*} (s : δ → Set α) :
    supported M R (⋃ i, s i) = ⨆ i, supported M R (s i) := by
  refine le_antisymm ?_ (iSup_le fun i => supported_mono <| Set.subset_iUnion _ _)
  have := Classical.decPred fun x => x ∈ ⋃ i, s i
  suffices
    LinearMap.range ((Submodule.subtype _).comp (restrictDom M R (⋃ i, s i))) ≤
      ⨆ i, supported M R (s i) by
    rwa [LinearMap.range_comp, range_restrictDom, Submodule.map_top, range_subtype] at this
  rw [range_le_iff_comap, eq_top_iff]
  rintro l ⟨⟩
  induction l using Finsupp.induction with
  | zero => exact zero_mem _
  | single_add x a l _ _ ih =>
    refine add_mem ?_ ih
    by_cases h : ∃ i, x ∈ s i
    · simp only [mem_comap, coe_comp, coe_subtype, Function.comp_apply, restrictDom_apply,
        mem_iUnion, h, filter_single_of_pos]
      obtain ⟨i, hi⟩ := h
      exact le_iSup (fun i => supported M R (s i)) i (single_mem_supported R _ hi)
    · simp [h]
/-
**Finsupp.supported_union** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：supported_union (s t : Set α) : supported M R (s union t) = supported M R 
s ⊔ supported M R t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `Finsupp.supported_iUnion`：supported_iUnion {δ : Type*} (s : δ -> Set α) 
: supported M R (⋃ i, s i) = ⨆ i, supported M R (s i)
· 使用定理 `iSup_bool_eq`：iSup_bool_eq {f : Bool -> α} : ⨆ b : Bool, f b = f true ⊔ 
f false
· 使用定理 `cond_true`：∀ {α : Sort u_1} (a b : α), (bif true then a else b) = a
· 使用定理 `cond_false`：∀ {α : Sort u_1} (a b : α), (bif false then a else b) = b
-/
theorem supported_union (s t : Set α) :
    supported M R (s ∪ t) = supported M R s ⊔ supported M R t := by
  rw [Set.union_eq_iUnion, supported_iUnion, iSup_bool_eq, cond_true, cond_false]
/-
**Finsupp.supported_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：supported_iInter {ι : Type*} (s : ι -> Set α) : supported M R (⋂ i, s i) =
 ⨅ i, supported M R (s i)
参数：s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem supported_iInter {ι : Type*} (s : ι → Set α) :
    supported M R (⋂ i, s i) = ⨅ i, supported M R (s i) :=
  Submodule.ext fun x => by simp [mem_supported, subset_iInter_iff]
/-
**Finsupp.supported_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：supported_inter (s t : Set α) : supported M R (s inter t) = supported M R 
s ⊓ supported M R t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_eq_iInter`：inter_eq_iInter {s₁ s₂ : Set α} : s₁ inter s₂ = ⋂ b
 : Bool, cond b s₁ s₂
· 使用定理 `Finsupp.supported_iInter`：supported_iInter {ι : Type*} (s : ι -> Set α) 
: supported M R (⋂ i, s i) = ⨅ i, supported M R (s i)
· 使用定理 `iInf_bool_eq`：∀ {α : Type u_1} [inst : CompleteLattice α] {f : Bool → α}
, ⨅ b, f b = f true ⊓ f false
-/
theorem supported_inter (s t : Set α) :
    supported M R (s ∩ t) = supported M R s ⊓ supported M R t := by
  rw [Set.inter_eq_iInter, supported_iInter, iInf_bool_eq]; rfl
/-
**Finsupp.disjoint_supported_supported** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：disjoint_supported_supported {s t : Set α} (h : Disjoint s t) : Disjoint (
supported M R s) (supported M R t)
参数：h : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.supported_inter`：supported_inter (s t : Set α) : supported M R (
s inter t) = supported M R s ⊓ supported M R t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Finsupp.supported_empty`：supported_empty : supported M R (∅ : Set α) = ⊥
-/
theorem disjoint_supported_supported {s t : Set α} (h : Disjoint s t) :
    Disjoint (supported M R s) (supported M R t) :=
  disjoint_iff.2 <| by rw [← supported_inter, disjoint_iff_inter_eq_empty.1 h, supported_empty]
/-
**Finsupp.disjoint_supported_supported_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：disjoint_supported_supported_iff [Nontrivial M] {s t : Set α} : Disjoint (
supported M R s) (supported M R t) ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Finsupp.single_mem_supported`：single_mem_supported {s : Set α} {a : α} (
b : M) (h : a in s) : single a b in supported M R s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_zero`：single_eq_zero : single a b = 0 ↔ b = 0
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Finsupp.disjoint_supported_supported`：disjoint_supported_supported {s t 
: Set α} (h : Disjoint s t) : Disjoint (supported M R s) (supported M R t)
-/
theorem disjoint_supported_supported_iff [Nontrivial M] {s t : Set α} :
    Disjoint (supported M R s) (supported M R t) ↔ Disjoint s t := by
  refine ⟨fun h => Set.disjoint_left.mpr fun x hx1 hx2 => ?_, disjoint_supported_supported⟩
  rcases exists_ne (0 : M) with ⟨y, hy⟩
  have := h.le_bot ⟨single_mem_supported R y hx1, single_mem_supported R y hx2⟩
  rw [mem_bot, single_eq_zero] at this
  exact hy this
/-
**Finsupp.codisjoint_supported_supported** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：codisjoint_supported_supported {s t : Set α} (h : Codisjoint s t) : Codisj
oint (supported M R s) (supported M R t)
参数：h : Codisjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.supported_union`：supported_union (s t : Set α) : supported M R (
s union t) = supported M R s ⊔ supported M R t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.supported_univ`：supported_univ : supported M R (Set.univ : Set α
) = ⊤
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma codisjoint_supported_supported {s t : Set α} (h : Codisjoint s t) :
    Codisjoint (supported M R s) (supported M R t) := by
  rw [codisjoint_iff, eq_top_iff, ← supported_union,
    show s ∪ t = .univ from codisjoint_iff.mp h, supported_univ]
/-
**Finsupp.codisjoint_supported_supported_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`
。
形式化陈述：codisjoint_supported_supported_iff [Nontrivial M] {s t : Set α} : Codisjoi
nt (supported M R s) (supported M R t) ↔ Codisjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.supported_union`：supported_union (s t : Set α) : supported M R (
s union t) = supported M R s ⊔ supported M R t
· 使用引理 `Finsupp.codisjoint_supported_supported`：codisjoint_supported_supported {
s t : Set α} (h : Codisjoint s t) : Codisjoint (supported M R s) (supported M R 
t)
-/
lemma codisjoint_supported_supported_iff [Nontrivial M] {s t : Set α} :
    Codisjoint (supported M R s) (supported M R t) ↔ Codisjoint s t := by
  refine ⟨fun h ↦ codisjoint_iff.mpr (eq_top_iff.mpr fun a ↦ ?_), codisjoint_supported_supported⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  rw [codisjoint_iff, ← supported_union, eq_top_iff'] at h
  simpa [Finsupp.mem_supported, Finsupp.support_single _ hx] using h (Finsupp.single a x)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Interpret `Finsupp.restrictSupportEquiv` as a linear equivalence between
`supported M R s` and `s →₀ M`. -/
/-
**Finsupp.supportedEquivFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：{α : Type u_1} →   {M : Type u_2} →     {R : Type u_5} →       [inst : Sem
iring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.Modul
e R M] → (s : Set α) → ↥(Finsupp.supported M R s) ≃ₗ[R] ↑s →₀ M
参数：s : Set α；Finsupp.supported M R s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret `Finsupp.restrictSupportEquiv` as a linear equivalence between
`supported M R s` and `s →₀ M`.
-/
@[simps!] def supportedEquivFinsupp (s : Set α) : supported M R s ≃ₗ[R] s →₀ M := by
  let F : supported M R s ≃ (s →₀ M) := restrictSupportEquiv s M
  refine F.toLinearEquiv ?_
  have :
    (F : supported M R s → ↥s →₀ M) =
      (lsubtypeDomain s : (α →₀ M) →ₗ[R] s →₀ M).comp (Submodule.subtype (supported M R s)) :=
    rfl
  rw [this]
  exact LinearMap.isLinear _
/-
**Finsupp.supportedEquivFinsupp_symm_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finsup
p`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {R : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (s : Set α) [inst_3 : Decidab
lePred fun x => x ∈ s] (f : ↑s →₀ M),   ↑((Finsupp.supportedEquivFinsupp s).symm
 f) = f.extendDomain
参数：s : Set α；f : ↑s →₀ M；(Finsupp.supportedEquivFinsupp s).symm f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Finsupp.restrictSupportEquiv_symm_apply_coe`：∀ {α : Type u_1} (s : Set α
) (M : Type u_12) [inst : AddCommMonoid M] [inst_1 : DecidablePred fun x => x ∈ 
s]   (f : ↑s →₀ M), ↑((Finsupp.re…
-/
@[simp] theorem supportedEquivFinsupp_symm_apply_coe (s : Set α) [DecidablePred (· ∈ s)]
    (f : s →₀ M) : (supportedEquivFinsupp (R := R) s).symm f = f.extendDomain := by
  convert! restrictSupportEquiv_symm_apply_coe ..
/-
**Finsupp.supportedEquivFinsupp_symm_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {R : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (s : Set α) (i : ↑s) (a : M),
   ↑((Finsupp.supportedEquivFinsupp s).symm fun₀ | i => a) = fun₀ | ↑i => a
参数：s : Set α；i : ↑s；a : M；(Finsupp.supportedEquivFinsupp s).symm fun₀ | i => a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.supportedEquivFinsupp_symm_apply_coe`：∀ {α : Type u_1} {M : Type
 u_2} {R : Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : 
_root_.Module R M] (s : Set α) [in…
· 使用定理 `Finsupp.extendDomain_single`：extendDomain_single (a : Subtype P) (m : M)
 : (single a m).extendDomain = single a.val m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem supportedEquivFinsupp_symm_single (s : Set α) (i : s) (a : M) :
    ((supportedEquivFinsupp (R := R) s).symm (single i a) : α →₀ M) = single ↑i a := by
  classical simp

section LMapDomain

variable {α' : Type*} {α'' : Type*} (M R)

/-
**Finsupp.supported_comap_lmapDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：supported_comap_lmapDomain (f : α -> α') (s : Set α') : supported M R (f ⁻
¹' s) <= (supported M R s).comap (lmapDomain M R f)
参数：f : α -> α'；s : Set α'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Finsupp.mapDomain_support`：mapDomain_support [DecidableEq β] {f : α -> β
} {s : α ->₀ M} : (s.mapDomain f).support subseteq s.support.image f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem supported_comap_lmapDomain (f : α → α') (s : Set α') :
    supported M R (f ⁻¹' s) ≤ (supported M R s).comap (lmapDomain M R f) := by
  classical
  intro l (hl : (l.support : Set α) ⊆ f ⁻¹' s)
  change ↑(mapDomain f l).support ⊆ s
  rw [← Set.image_subset_iff, ← Finset.coe_image] at hl
  exact Set.Subset.trans mapDomain_support hl
/-
**Finsupp.lmapDomain_supported** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lmapDomain_supported (f : α -> α') (s : Set α) : (supported M R s).map (lm
apDomain M R f) = supported M R (f '' s)
参数：f : α -> α'；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `Finsupp.supported_empty`：supported_empty : supported M R (∅ : Set α) = ⊥
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Finsupp.supported_mono`：supported_mono {s t : Set α} (st : s subseteq t)
 : supported M R s <= supported M R t
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
· 使用定理 `Finsupp.supported_comap_lmapDomain`：supported_comap_lmapDomain (f : α ->
 α') (s : Set α') : supported M R (f ⁻¹' s) <= (supported M R s).comap (lmapDoma
in M R f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finsupp.mapDomain_support`：mapDomain_support [DecidableEq β] {f : α -> β
} {s : α ->₀ M} : (s.mapDomain f).support subseteq s.support.image f
· 使用定理 `Function.invFunOn_mem`：invFunOn_mem (h : exists a in s, f a = b) : invFu
nOn f s b in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `Finsupp.lmapDomain_comp`：lmapDomain_comp (f : α -> α') (g : α' -> α'') :
 lmapDomain M R (g ∘ f) = (lmapDomain M R g).comp (lmapDomain M R f)
· 使用定理 `Finsupp.mapDomain_congr`：mapDomain_congr {f g : α -> β} (h : forall x in
 v.support, f x = g x) : v.mapDomain f = v.mapDomain g
· 使用定理 `Function.invFunOn_eq`：invFunOn_eq (h : exists a in s, f a = b) : f (invF
unOn f s b) = b
· 使用定理 `Finsupp.mapDomain_id`：mapDomain_id : mapDomain id v = v
-/
theorem lmapDomain_supported (f : α → α') (s : Set α) :
    (supported M R s).map (lmapDomain M R f) = supported M R (f '' s) := by
  classical
  cases isEmpty_or_nonempty α
  · simp [s.eq_empty_of_isEmpty]
  refine
    le_antisymm
      (map_le_iff_le_comap.2 <|
        le_trans (supported_mono <| Set.subset_preimage_image _ _)
          (supported_comap_lmapDomain M R _ _))
      ?_
  intro l hl
  refine ⟨(lmapDomain M R (Function.invFunOn f s) : (α' →₀ M) →ₗ[R] α →₀ M) l, fun x hx => ?_, ?_⟩
  · rcases Finset.mem_image.1 (mapDomain_support hx) with ⟨c, hc, rfl⟩
    exact Function.invFunOn_mem (by simpa using hl hc)
  · rw [← LinearMap.comp_apply, ← lmapDomain_comp]
    refine (mapDomain_congr fun c hc => ?_).trans mapDomain_id
    exact Function.invFunOn_eq (by simpa using hl hc)
/-
**Finsupp.lmapDomain_disjoint_ker** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lmapDomain_disjoint_ker (f : α -> α') {s : Set α} (H : forall a in s, fora
ll b in s, f a = f b -> a = b) : Disjoint (supported M R s) (ker (lmapDomain M R
 f))
参数：f : α -> α'；H : forall a in s, forall b in s, f a = f b -> a = b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Finsupp.mapDomain.eq_1`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [
inst : AddCommMonoid M] (f : α → β) (v : α →₀ M),   Finsupp.mapDomain f v = v.su
m fun a => F…
· 使用定理 `Finsupp.lmapDomain_apply`：lmapDomain_apply (f : α -> α') (l : α ->₀ M) :
 (lmapDomain M R f : (α ->₀ M) ->ₗ[R] α' ->₀ M) l = mapDomain f l
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Finsupp.sum_eq_single`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M} (a : α)   {g : α → M → N}
, (∀ (b : α…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
-/
theorem lmapDomain_disjoint_ker (f : α → α') {s : Set α}
    (H : ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b) :
    Disjoint (supported M R s) (ker (lmapDomain M R f)) := by
  rw [disjoint_iff_inf_le]
  rintro l ⟨h₁, h₂⟩
  rw [SetLike.mem_coe, mem_ker, lmapDomain_apply, mapDomain] at h₂
  simp only [mem_bot]; ext x
  have := Classical.decPred fun x => x ∈ s
  by_cases xs : x ∈ s
  · have : Finsupp.sum l (fun a => Finsupp.single (f a)) (f x) = 0 := by
      rw [h₂]
      rfl
    rw [Finsupp.sum_apply, Finsupp.sum_eq_single x, single_eq_same] at this
    · simpa
    · intro y hy xy
      simp only [SetLike.mem_coe, mem_supported, subset_def, mem_support_iff] at h₁
      simp [mt (H _ (h₁ _ hy) _ xs) xy]
    · simp +contextual
  · by_contra h
    exact xs (h₁ <| Finsupp.mem_support_iff.2 h)

end LMapDomain

/-- An equivalence of sets induces a linear equivalence of `Finsupp`s supported on those sets. -/
/-
**Finsupp.congr** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：congr {α' : Type*} (s : Set α) (t : Set α') (e : s ≃ t) : supported M R s 
≃ₗ[R] supported M R t
参数：s : Set α；t : Set α'；e : s ≃ t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of sets induces a linear equivalence of `Finsupp`s supported on t
hose sets.
-/
noncomputable def congr {α' : Type*} (s : Set α) (t : Set α') (e : s ≃ t) :
    supported M R s ≃ₗ[R] supported M R t := by
  haveI := Classical.decPred fun x => x ∈ s
  haveI := Classical.decPred fun x => x ∈ t
  exact Finsupp.supportedEquivFinsupp s ≪≫ₗ
    (Finsupp.domLCongr e ≪≫ₗ (Finsupp.supportedEquivFinsupp t).symm)

end Finsupp

