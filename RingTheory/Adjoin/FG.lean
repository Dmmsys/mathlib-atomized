/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Adjoining elements to form subalgebras

This file develops the basic theory of finitely-generated subalgebras.

## Definitions

* `FG (S : Subalgebra R A)` : A predicate saying that the subalgebra is finitely-generated
  as an A-algebra

## Tags

adjoin, algebra, finitely-generated algebra

-/

@[expose] public section


universe u v w

open Subsemiring Ring Submodule

open scoped Pointwise

namespace Algebra

variable {R : Type u} {A : Type v} {B : Type w} [CommSemiring R] [CommSemiring A] [Algebra R A]
  {s t : Set A}

/-
**Algebra.fg_trans** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：fg_trans (h1 : (adjoin R s).toSubmodule.FG) (h2 : (adjoin (adjoin R s) t).
toSubmodule.FG) : (adjoin R (s union t)).toSubmodule.FG
参数：h1 : (adjoin R s).toSubmodule.FG；h2 : (adjoin (adjoin R s) t).toSubmodule.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.fg_def`：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, 
S.Finite ∧ span R S = N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.mul`：∀ {α : Type u_2} [inst : Mul α] {s t : Set α}, s.Finite 
→ t.Finite → (s * t).Finite
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.mul_subset_iff`：mul_subset_iff : s * t subseteq u ↔ forall x in s, f
orall y in t, x * y in u
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.adjoin_union_eq_adjoin_adjoin`：adjoin_union_eq_adjoin_adjoin : a
djoin R (s union t) = (adjoin (adjoin R s) t).restrictScalars R
· 使用定理 `Finsupp.mem_span_image_iff_linearCombination`：mem_span_image_iff_linearC
ombination {s : Set α} {x : M} : x in span R (v '' s) ↔ exists l in supported R 
R s, linearCombination R v l = x
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Finsupp.sum_mul`：Finsupp.sum_mul (b : S) (s : α ->₀ R) {f : α -> R -> S}
 : s.sum f * b = s.sum fun a c => f a c * b
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
theorem fg_trans (h1 : (adjoin R s).toSubmodule.FG) (h2 : (adjoin (adjoin R s) t).toSubmodule.FG) :
    (adjoin R (s ∪ t)).toSubmodule.FG := by
  rcases fg_def.1 h1 with ⟨p, hp, hp'⟩
  rcases fg_def.1 h2 with ⟨q, hq, hq'⟩
  refine fg_def.2 ⟨p * q, hp.mul hq, le_antisymm ?_ ?_⟩
  · rw [span_le, Set.mul_subset_iff]
    intro x hx y hy
    change x * y ∈ adjoin R (s ∪ t)
    refine Subalgebra.mul_mem _ ?_ ?_
    · have : x ∈ Subalgebra.toSubmodule (adjoin R s) := by
        rw [← hp']
        exact subset_span hx
      exact adjoin_mono Set.subset_union_left this
    have : y ∈ Subalgebra.toSubmodule (adjoin (adjoin R s) t) := by
      rw [← hq']
      exact subset_span hy
    change y ∈ adjoin R (s ∪ t)
    rwa [adjoin_union_eq_adjoin_adjoin]
  · intro r hr
    change r ∈ adjoin R (s ∪ t) at hr
    rw [adjoin_union_eq_adjoin_adjoin] at hr
    change r ∈ Subalgebra.toSubmodule (adjoin (adjoin R s) t) at hr
    rw [← hq', ← Set.image_id q, Finsupp.mem_span_image_iff_linearCombination (adjoin R s)] at hr
    rcases hr with ⟨l, hlq, rfl⟩
    have := @Finsupp.linearCombination_apply A A (adjoin R s)
    rw [this, Finsupp.sum]
    refine sum_mem ?_
    intro z hz
    change (l z).1 * _ ∈ _
    have : (l z).1 ∈ Subalgebra.toSubmodule (adjoin R s) := (l z).2
    rw [← hp', ← Set.image_id p, Finsupp.mem_span_image_iff_linearCombination R] at this
    rcases this with ⟨l2, hlp, hl⟩
    have := @Finsupp.linearCombination_apply A A R
    rw [this] at hl
    rw [← hl, Finsupp.sum_mul]
    refine sum_mem ?_
    intro t ht
    change _ * _ ∈ _
    rw [smul_mul_assoc]
    refine smul_mem _ _ ?_
    exact subset_span ⟨t, hlp ht, z, hlq hz, rfl⟩

end Algebra

namespace Subalgebra

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- A subalgebra `S` is finitely generated if there exists `t : Finset A` such that
`Algebra.adjoin R t = S`. -/
/-
**Subalgebra.FG** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：FG (S : Subalgebra R A) : Prop
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subalgebra `S` is finitely generated if there exists `t : Finset A` such that
`Algebra.adjoin R t = S`.
-/
def FG (S : Subalgebra R A) : Prop :=
  ∃ t : Finset A, Algebra.adjoin R ↑t = S
/-
**Subalgebra.fg_adjoin_finset** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：fg_adjoin_finset (s : Finset A) : (Algebra.adjoin R (↑s : Set A)).FG
参数：s : Finset A。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fg_adjoin_finset (s : Finset A) : (Algebra.adjoin R (↑s : Set A)).FG :=
  ⟨s, rfl⟩
/-
**Subalgebra.fg_def** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：fg_def {S : Subalgebra R A} : S.FG ↔ exists t : Set A, Set.Finite t ∧ Alge
bra.adjoin R t = S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.exists_finite_iff_finset`：exists_finite_iff_finset {p : Set α -> Pro
p} : (exists s : Set α, s.Finite ∧ p s) ↔ exists s : Finset α, p ↑s
-/
theorem fg_def {S : Subalgebra R A} : S.FG ↔ ∃ t : Set A, Set.Finite t ∧ Algebra.adjoin R t = S :=
  Iff.symm Set.exists_finite_iff_finset
/-
**Subalgebra.fg_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：fg_bot : (⊥ : Subalgebra R A).FG
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_empty`：adjoin_empty : adjoin R (∅ : Set A) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
-/
theorem fg_bot : (⊥ : Subalgebra R A).FG :=
  ⟨∅, Finset.coe_empty ▸ Algebra.adjoin_empty R A⟩
/-
**Subalgebra.fg_of_fg_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：fg_of_fg_toSubmodule {S : Subalgebra R A} : S.toSubmodule.FG -> S.FG
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem fg_of_fg_toSubmodule {S : Subalgebra R A} : S.toSubmodule.FG → S.FG :=
  fun ⟨t, ht⟩ ↦ ⟨t, le_antisymm
    (Algebra.adjoin_le fun x hx ↦ show x ∈ Subalgebra.toSubmodule S from ht ▸ subset_span hx) <|
    show Subalgebra.toSubmodule S ≤ Subalgebra.toSubmodule (Algebra.adjoin R ↑t) from fun x hx ↦
      span_le.mpr (fun _ hx ↦ Algebra.subset_adjoin hx)
        (show x ∈ span R ↑t by
          rw [ht]
          exact hx)⟩
/-
**Subalgebra.fg_of_noetherian** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：fg_of_noetherian [IsNoetherian R A] (S : Subalgebra R A) : S.FG
参数：S : Subalgebra R A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.fg_of_fg_toSubmodule`：fg_of_fg_toSubmodule {S : Subalgebra R 
A} : S.toSubmodule.FG -> S.FG
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
-/
theorem fg_of_noetherian [IsNoetherian R A] (S : Subalgebra R A) : S.FG :=
  fg_of_fg_toSubmodule (IsNoetherian.noetherian (Subalgebra.toSubmodule S))
/-
**Subalgebra.fg_of_submodule_fg** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：fg_of_submodule_fg (h : (⊤ : Submodule R A).FG) : (⊤ : Subalgebra R A).FG
参数：h : (⊤ : Submodule R A).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.top_toSubmodule`：top_toSubmodule : Subalgebra.toSubmodule (⊤ : S
ubalgebra R A) = ⊤
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem fg_of_submodule_fg (h : (⊤ : Submodule R A).FG) : (⊤ : Subalgebra R A).FG :=
  let ⟨s, hs⟩ := h
  ⟨s, toSubmodule.injective <| by
    rw [Algebra.top_toSubmodule, eq_top_iff, ← hs, span_le]
    exact Algebra.subset_adjoin⟩
/-
**Subalgebra.FG.prod** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.FG`。
形式化陈述：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSemiring R] [inst_1 :
 Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] [inst_4 : Algebra R 
B] {S : Subalgebra R A} {T : Subalgebra R B}, S.FG → T.FG → (S.prod T).FG
参数：S.prod T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subalgebra.fg_def`：fg_def {S : Subalgebra R A} : S.FG ↔ exists t : Set A
, Set.Finite t ∧ Algebra.adjoin R t = S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Algebra.adjoin_inl_union_inr_eq_prod`：adjoin_inl_union_inr_eq_prod (s) (
t) : adjoin R (LinearMap.inl R A B '' (s union {1}) union LinearMap.inr R A B ''
 (t union {1})) = (adjoin …
-/
theorem FG.prod {S : Subalgebra R A} {T : Subalgebra R B} (hS : S.FG) (hT : T.FG) :
    (S.prod T).FG := by
  obtain ⟨s, hs⟩ := fg_def.1 hS
  obtain ⟨t, ht⟩ := fg_def.1 hT
  rw [← hs.2, ← ht.2]
  exact fg_def.2 ⟨LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1}),
    Set.Finite.union (Set.Finite.image _ (Set.Finite.union hs.1 (Set.finite_singleton _)))
      (Set.Finite.image _ (Set.Finite.union ht.1 (Set.finite_singleton _))),
    Algebra.adjoin_inl_union_inr_eq_prod R s t⟩

section

/-
**Subalgebra.FG.map** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.FG`。
形式化陈述：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSemiring R] [inst_1 :
 Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] [inst_4 : Algebra R 
B] {S : Subalgebra R A} (f : A →ₐ[R] B), S.FG → (Subalgebra.map f S).FG
参数：f : A →ₐ[R] B；Subalgebra.map f S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Algebra.adjoin_image`：adjoin_image (f : A ->ₐ[R] B) (s : Set A) : adjoin
 R (f '' s) = (adjoin R s).map f
-/
theorem FG.map {S : Subalgebra R A} (f : A →ₐ[R] B) (hs : S.FG) : (S.map f).FG := by
  let ⟨s, hs⟩ := hs
  classical
  exact ⟨s.image f, by rw [Finset.coe_image, Algebra.adjoin_image, hs]⟩

end

set_option backward.isDefEq.respectTransparency false in
/-
**Subalgebra.fg_of_fg_map** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：fg_of_fg_map (S : Subalgebra R A) (f : A ->ₐ[R] B) (hf : Function.Injectiv
e f) (hs : (S.map f).FG) : S.FG
参数：S : Subalgebra R A；f : A ->ₐ[R] B；hf : Function.Injective f；hs : (S.map f).FG
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.map_injective`：map_injective {f : A ->ₐ[R] B} (hf : Function.
Injective f) : Function.Injective (map f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_image`：adjoin_image (f : A ->ₐ[R] B) (s : Set A) : adjoin
 R (f '' s) = (adjoin R s).map f
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `Subalgebra.map_mono`：map_mono {S₁ S₂ : Subalgebra R A} {f : A ->ₐ[R] B} 
: S₁ <= S₂ -> S₁.map f <= S₂.map f
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem fg_of_fg_map (S : Subalgebra R A) (f : A →ₐ[R] B) (hf : Function.Injective f)
    (hs : (S.map f).FG) : S.FG :=
  let ⟨s, hs⟩ := hs
  ⟨s.preimage f fun _ _ _ _ h ↦ hf h,
    map_injective hf <| by
      rw [← Algebra.adjoin_image, Finset.coe_preimage, Set.image_preimage_eq_of_subset, hs]
      rw [← AlgHom.coe_range, ← Algebra.adjoin_le_iff, hs, ← Algebra.map_top]
      exact map_mono le_top⟩
/-
**Subalgebra.fg_top** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：fg_top (S : Subalgebra R A) : (⊤ : Subalgebra R S).FG ↔ S.FG
参数：S : Subalgebra R A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.range_val`：range_val : S.val.range = S
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `Subalgebra.FG.map`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B]
 [inst_…
· 使用定理 `Subalgebra.fg_of_fg_map`：fg_of_fg_map (S : Subalgebra R A) (f : A ->ₐ[R]
 B) (hf : Function.Injective f) (hs : (S.map f).FG) : S.FG
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
theorem fg_top (S : Subalgebra R A) : (⊤ : Subalgebra R S).FG ↔ S.FG :=
  ⟨fun h ↦ by
    rw [← S.range_val, ← Algebra.map_top]
    exact FG.map _ h, fun h ↦
    fg_of_fg_map _ S.val Subtype.val_injective <| by
      rw [Algebra.map_top, range_val]
      exact h⟩
/-
**Subalgebra.induction_on_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：induction_on_adjoin [IsNoetherian R A] (P : Subalgebra R A -> Prop) (base 
: P ⊥) (ih : forall (S : Subalgebra R A) (x : A), P S -> P (Algebra.adjoin R (in
sert x S))) (S : Subalgebra R A) : P S
参数：P : Subalgebra R A -> Prop；base : P ⊥；ih : forall (S : Subalgebra R A) (x : A
), P S -> P (Algebra.adjoin R (insert x S))；S : Subalgebra R A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.fg_of_noetherian`：fg_of_noetherian [IsNoetherian R A] (S : Su
balgebra R A) : S.FG
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Algebra.adjoin_empty`：adjoin_empty : adjoin R (∅ : Set A) = ⊥
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Algebra.adjoin_insert_adjoin`：adjoin_insert_adjoin (x : A) : adjoin R (i
nsert x ↑(adjoin R s)) = adjoin R (insert x s)
-/
theorem induction_on_adjoin [IsNoetherian R A] (P : Subalgebra R A → Prop) (base : P ⊥)
    (ih : ∀ (S : Subalgebra R A) (x : A), P S → P (Algebra.adjoin R (insert x S)))
    (S : Subalgebra R A) : P S := by
  classical
  obtain ⟨t, rfl⟩ := S.fg_of_noetherian
  refine Finset.induction_on t ?_ ?_
  · simpa using base
  intro x t _ h
  rw [Finset.coe_insert]
  simpa only [Algebra.adjoin_insert_adjoin] using ih _ x h
/-
**Subalgebra.FG.sup** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.FG`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A]   {S S' : Subalgebra R A}, S.FG → S'.FG → (S ⊔ S').FG
参数：S ⊔ S'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subalgebra.fg_def`：fg_def {S : Subalgebra R A} : S.FG ↔ exists t : Set A
, Set.Finite t ∧ Algebra.adjoin R t = S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_union`：adjoin_union (s t : Set A) : adjoin R (s union t) 
= adjoin R s ⊔ adjoin R t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem FG.sup {S S' : Subalgebra R A} (hS : Subalgebra.FG S) (hS' : Subalgebra.FG S') :
    Subalgebra.FG (S ⊔ S') :=
  let ⟨s, hs⟩ := Subalgebra.fg_def.1 hS
  let ⟨s', hs'⟩ := Subalgebra.fg_def.1 hS'
  fg_def.mpr ⟨s ∪ s', Set.Finite.union hs.1 hs'.1,
    (by rw [Algebra.adjoin_union, hs.2, hs'.2])⟩

end Subalgebra

section Semiring

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The image of a Noetherian R-algebra under an R-algebra map is a Noetherian ring. -/
/-
**AlgHom.isNoetherianRing_range** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AlgHom.isNoetherianRing_range (f : A ->ₐ[R] B) [IsNoetherianRing A] : IsNo
etherianRing f.range
参数：f : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a Noetherian R-algebra under an R-algebra map is a Noetherian ring.
-/
instance AlgHom.isNoetherianRing_range (f : A →ₐ[R] B) [IsNoetherianRing A] :
    IsNoetherianRing f.range :=
  _root_.isNoetherianRing_range f.toRingHom

end Semiring

section Ring

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-
**isNoetherianRing_of_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherianRing_of_fg {S : Subalgebra R A} (HS : S.FG) [IsNoetherianRing 
R] : IsNoetherianRing S
参数：HS : S.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_eq_range`：∀ (R : Type u) {S₁ : Type v} [inst : CommSemiri
ng R] [inst_1 : CommSemiring S₁] [inst_2 : Algebra R S₁] (s : Set S₁),   Algebra
.adjoin R s =…
-/
theorem isNoetherianRing_of_fg {S : Subalgebra R A} (HS : S.FG) [IsNoetherianRing R] :
    IsNoetherianRing S :=
  let ⟨t, ht⟩ := HS
  ht ▸ (Algebra.adjoin_eq_range R (↑t : Set A)).symm ▸ AlgHom.isNoetherianRing_range _
/-
**is_noetherian_subring_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：is_noetherian_subring_closure (s : Set R) (hs : s.Finite) : IsNoetherianRi
ng (Subring.closure s)
参数：s : Set R；hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherianRing_of_fg`：isNoetherianRing_of_fg {S : Subalgebra R A} (HS 
: S.FG) [IsNoetherianRing R] : IsNoetherianRing S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subalgebra.fg_def`：fg_def {S : Subalgebra R A} : S.FG ↔ exists t : Set A
, Set.Finite t ∧ Algebra.adjoin R t = S
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `AddGroup.instFGInt`：AddGroup.FG ℤ
· 使用定理 `Algebra.adjoin_int`：Algebra.adjoin_int {R : Type*} [Ring R] (s : Set R) 
: adjoin Int s = subalgebraOfSubring (Subring.closure s)
-/
theorem is_noetherian_subring_closure (s : Set R) (hs : s.Finite) :
    IsNoetherianRing (Subring.closure s) :=
  show IsNoetherianRing (subalgebraOfSubring (Subring.closure s)) from
    Algebra.adjoin_int s ▸ isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)

end Ring

