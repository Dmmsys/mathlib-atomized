/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Order.Nonneg.Module
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Basic results on finitely generated (sub)modules

This file contains the basic results on `Submodule.FG` and `Module.Finite` that do not need heavy
further imports.
-/

public section

assert_not_exists Module.Basis Ideal.radical Matrix Subalgebra

open Function (Surjective)

namespace Submodule

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

open Set

/-
**Submodule.fg_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_bot : (⊥ : Submodule R M).FG
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
-/
theorem fg_bot : (⊥ : Submodule R M).FG :=
  ⟨∅, by rw [Finset.coe_empty, span_empty]⟩
/-
**Submodule.fg_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_span {s : Set M} (hs : s.Finite) : FG (span R s)
参数：hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
-/
theorem fg_span {s : Set M} (hs : s.Finite) : FG (span R s) :=
  ⟨hs.toFinset, by rw [hs.coe_toFinset]⟩
/-
**Submodule.fg_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_span_singleton (x : M) : FG (R ∙ x)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.fg_span`：fg_span {s : Set M} (hs : s.Finite) : FG (span R s)
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
theorem fg_span_singleton (x : M) : FG (R ∙ x) :=
  fg_span (finite_singleton x)
/-
**Submodule.FG.sup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {N₁ N₂ : Submodule R M}, N₁.FG → N₂.FG → (N₁
 ⊔ N₂).FG
参数：N₁ ⊔ N₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.fg_def`：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, 
S.Finite ∧ span R S = N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_union`：span_union (s t : Set M) : span R (s union t) = sp
an R s ⊔ span R t
-/
theorem FG.sup {N₁ N₂ : Submodule R M} (hN₁ : N₁.FG) (hN₂ : N₂.FG) : (N₁ ⊔ N₂).FG :=
  let ⟨t₁, ht₁, span_t₁⟩ := fg_def.mp hN₁
  let ⟨t₂, ht₂, span_t₂⟩ := fg_def.mp hN₂
  fg_def.mpr ⟨t₁ ∪ t₂, ht₁.union ht₂, by rw [span_union, span_t₁, span_t₂]⟩
/-
**Submodule.fg_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_finset_sup {ι : Type*} (s : Finset ι) (N : ι -> Submodule R M) (h : for
all i in s, (N i).FG) : (s.sup N).FG
参数：s : Finset ι；N : ι -> Submodule R M；h : forall i in s, (N i).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_induction`：sup_induction {p : α -> Prop} (hb : p ⊥) (hp : for
all a₁, p a₁ -> forall a₂, p a₂ -> p (a₁ ⊔ a₂)) (hs : forall b in s, p (f b)) : 
p (s.sup f…
· 使用定理 `Submodule.fg_bot`：fg_bot : (⊥ : Submodule R M).FG
· 使用定理 `Submodule.FG.sup`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N₁ N₂ : Submodule R M},
 N₁.FG…
-/
theorem fg_finset_sup {ι : Type*} (s : Finset ι) (N : ι → Submodule R M) (h : ∀ i ∈ s, (N i).FG) :
    (s.sup N).FG :=
  Finset.sup_induction fg_bot (fun _ ha _ hb => ha.sup hb) h
/-
**Submodule.fg_biSup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_biSup {ι : Type*} (s : Finset ι) (N : ι -> Submodule R M) (h : forall i
 in s, (N i).FG) : (⨆ i in s, N i).FG
参数：s : Finset ι；N : ι -> Submodule R M；h : forall i in s, (N i).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `Submodule.fg_finset_sup`：fg_finset_sup {ι : Type*} (s : Finset ι) (N : ι
 -> Submodule R M) (h : forall i in s, (N i).FG) : (s.sup N).FG
-/
theorem fg_biSup {ι : Type*} (s : Finset ι) (N : ι → Submodule R M) (h : ∀ i ∈ s, (N i).FG) :
    (⨆ i ∈ s, N i).FG := by simpa only [Finset.sup_eq_iSup] using fg_finset_sup s N h
/-
**Submodule.fg_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_iSup {ι : Sort*} [Finite ι] (N : ι -> Submodule R M) (h : forall i, (N 
i).FG) : (iSup N).FG
参数：N : ι -> Submodule R M；h : forall i, (N i).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `instFinitePLift`：∀ {α : Sort u_1} [Finite α], Finite (PLift α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iSup_plift_down`：iSup_plift_down (f : ι -> α) : ⨆ i, f (PLift.down i) = 
⨆ i, f i
· 使用定理 `Submodule.fg_biSup`：fg_biSup {ι : Type*} (s : Finset ι) (N : ι -> Submod
ule R M) (h : forall i in s, (N i).FG) : (⨆ i in s, N i).FG
-/
theorem fg_iSup {ι : Sort*} [Finite ι] (N : ι → Submodule R M) (h : ∀ i, (N i).FG) :
    (iSup N).FG := by
  cases nonempty_fintype (PLift ι)
  simpa [iSup_plift_down] using fg_biSup Finset.univ (N ∘ PLift.down) fun i _ => h i.down
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup {P : Submodule R M // P.FG} where
  sup := fun P Q ↦ ⟨P.val ⊔ Q.val, Submodule.FG.sup P.property Q.property⟩
  le_sup_left := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_left
  le_sup_right := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_right
  sup_le := fun P Q R hPR hQR ↦ by
    rw [← Subtype.coe_le_coe] at hPR hQR ⊢
    exact sup_le hPR hQR
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited {P : Submodule R M // P.FG} where
  default := ⟨⊥, fg_bot⟩

section

variable {S P : Type*} [Semiring S] [AddCommMonoid P] [Module S P]
variable {σ : R →+* S} [RingHomSurjective σ] (f : M →ₛₗ[σ] P)

/-
**Submodule.fg_pi** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_pi {ι : Type*} {M : ι -> Type*} [Finite ι] [forall i, AddCommMonoid (M 
i)] [forall i, Module R (M i)] {p : forall i, Submodule R (M i)} (hsb : forall i
, (p i).FG) : (pi Set.univ p).FG
参数：M i；M i；M i；hsb : forall i, (p i).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_iUnion`：finite_iUnion [Finite ι] {f : ι -> Set α} (H : forall
 i, (f i).Finite) : (⋃ i, f i).Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_iUnion`：span_iUnion {ι} (s : ι -> Set M) : span R (⋃ i, s
 i) = ⨆ i, span R (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.iSup_map_single`：iSup_map_single [DecidableEq ι] [Finite ι] : 
⨆ i, map (LinearMap.single R φ i : φ i ->ₗ[R] (i : ι) -> φ i) (p i) = pi Set.uni
v p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem fg_pi {ι : Type*} {M : ι → Type*} [Finite ι] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] {p : ∀ i, Submodule R (M i)} (hsb : ∀ i, (p i).FG) :
    (pi Set.univ p).FG := by
  classical
    simp_rw [fg_def] at hsb ⊢
    choose t htf hts using hsb
    refine
      ⟨⋃ i, (LinearMap.single R _ i) '' t i, Set.finite_iUnion fun i => (htf i).image _, ?_⟩
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `span_image` into `span_image _`
    simp_rw [span_iUnion, span_image _, hts, iSup_map_single]
/-
**Submodule.FG.map** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type u_4} [inst_3 : Semi
ring S] [inst_4 : AddCommMonoid P] [inst_5 : _root_.Module S P]   {σ : R →+* S} 
[inst_6 : RingHomSurjective σ] (f : M →ₛₗ[σ] P) {N : Submodule R M}, N.FG → (Sub
module.map f N).FG
参数：f : M →ₛₗ[σ] P；Submodule.map f N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.fg_def`：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, 
S.Finite ∧ span R S = N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
-/
theorem FG.map {N : Submodule R M} (hs : N.FG) : (N.map f).FG :=
  let ⟨t, ht, span_t⟩ := fg_def.mp hs
  fg_def.mpr ⟨f '' t, ht.image _, by rw [span_image, span_t]⟩

/-- Maps from a finite module have a finite range. -/
/-
**Submodule.fg_range** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type u_4} [inst_3 : Semi
ring S] [inst_4 : AddCommMonoid P] [inst_5 : _root_.Module S P]   {σ : R →+* S} 
[inst_6 : RingHomSurjective σ] [Module.Finite R M] (f : M →ₛₗ[σ] P), f.range.FG
参数：f : M →ₛₗ[σ] P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…

--- 原说明 ---
Maps from a finite module have a finite range.
-/
@[simp] lemma fg_range [Module.Finite R M] (f : M →ₛₗ[σ] P) : f.range.FG := by
  rw [LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map f

set_option backward.isDefEq.respectTransparency false in
/-
**Submodule.fg_of_fg_map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_of_fg_map_injective (hf : Function.Injective f) {N : Submodule R M} (hf
n : (N.map f).FG) : N.FG
参数：hf : Function.Injective f；hfn : (N.map f).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_range`：coe_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] 
M₂) : (range f : Set M₂) = Set.range f
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.map_mono`：map_mono {f : M ->ₛₗ[σ₁₂] M₂} {p p' : Submodule R M}
 : p <= p' -> map f p <= map f p'
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem fg_of_fg_map_injective (hf : Function.Injective f) {N : Submodule R M}
    (hfn : (N.map f).FG) : N.FG :=
  let ⟨t, ht⟩ := hfn
  ⟨t.preimage f fun _ _ _ _ h => hf h,
    map_injective_of_injective hf <| by
      rw [map_span, Finset.coe_preimage, Set.image_preimage_eq_inter_range,
        Set.inter_eq_self_of_subset_left, ht]
      rw [← LinearMap.coe_range, ← span_le, ht, ← map_top]
      exact map_mono le_top⟩
/-
**Submodule.fg_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_map_iff (hf : Function.Injective f) {N : Submodule R M} : (N.map f).FG 
↔ N.FG
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.fg_of_fg_map_injective`：fg_of_fg_map_injective (hf : Function.
Injective f) {N : Submodule R M} (hfn : (N.map f).FG) : N.FG
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
-/
theorem fg_map_iff (hf : Function.Injective f) {N : Submodule R M} :
    (N.map f).FG ↔ N.FG :=
  ⟨(fg_of_fg_map_injective _ hf ·), (.map _)⟩

end

variable {P : Type*} [AddCommMonoid P] [Module R P]
variable {f : M →ₗ[R] P}

/-
**Submodule.fg_of_fg_map** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_of_fg_map {R M P : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCo
mmGroup P] [Module R P] (f : M ->ₗ[R] P) (hf : LinearMap.ker f = ⊥) {N : Submodu
le R M} (hfn : (N.map f).FG) : N.FG
参数：f : M ->ₗ[R] P；hf : LinearMap.ker f = ⊥；hfn : (N.map f).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.fg_of_fg_map_injective`：fg_of_fg_map_injective (hf : Function.
Injective f) {N : Submodule R M} (hfn : (N.map f).FG) : N.FG
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
-/
theorem fg_of_fg_map {R M P : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup P]
    [Module R P] (f : M →ₗ[R] P) (hf : LinearMap.ker f = ⊥) {N : Submodule R M}
    (hfn : (N.map f).FG) : N.FG :=
  fg_of_fg_map_injective f (LinearMap.ker_eq_bot.mp hf) hfn

/-- The top submodule of another submodule `N` is FG iff `N` is `FG`.

See also `Module.Finite.fg_top`. -/
/-
**Submodule.fg_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (N : Submodule R M), ⊤.FG ↔ N.FG
参数：N : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.fg_map_iff`：fg_map_iff (hf : Function.Injective f) {N : Submod
ule R M} : (N.map f).FG ↔ N.FG
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The top submodule of another submodule `N` is FG iff `N` is `FG`.

See also `Module.Finite.fg_top`.
-/
protected theorem fg_top (N : Submodule R M) : (⊤ : Submodule R N).FG ↔ N.FG := by
  rw [← fg_map_iff N.subtype Subtype.val_injective, map_top, range_subtype]

/-- See also `Module.Finite.equiv_iff`. -/
/-
**Submodule.fg_of_linearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_of_linearEquiv (e : M ≃ₗ[R] P) (h : (⊤ : Submodule R P).FG) : (⊤ : Subm
odule R M).FG
参数：e : M ≃ₗ[R] P；h : (⊤ : Submodule R P).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…

--- 原说明 ---
See also `Module.Finite.equiv_iff`.
-/
theorem fg_of_linearEquiv (e : M ≃ₗ[R] P) (h : (⊤ : Submodule R P).FG) : (⊤ : Submodule R M).FG :=
  e.symm.range ▸ map_top (e.symm : P →ₗ[R] M) ▸ h.map _
/-
**Submodule.fg_induction** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_induction {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {mo
tive : forall N : Submodule R M, N.FG -> Prop} (singleton : forall x : M, motive
 (R ∙ x) (fg_span_singleton _)) (sup : forall (N₁ N₂ : Submodule R M) (hN₁ : N₁.
FG) (hN₂ : N₂.FG), motive N₁ hN₁ -> motive N₂ hN₂ -> motive (N₁ ⊔ N₂) (hN₁.sup h
N₂)) (N : Submodule R M) (hN : N.FG) : motive N hN
参数：singleton : forall x : M, motive (R ∙ x) (fg_span_singleton _)；sup : forall (
N₁ N₂ : Submodule R M) (hN₁ : N₁.FG) (hN₂ : N₂.FG), motive N₁ hN₁ -> motive N₂ h
N₂ -> motive (N₁ ⊔ N₂) (hN₁.sup hN₂)；N : Submodule R M；hN : N.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.fg_span_singleton`：fg_span_singleton (x : M) : FG (R ∙ x)
· 使用定理 `Submodule.FG.sup`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N₁ N₂ : Submodule R M},
 N₁.FG…
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Submodule.span_insert`：span_insert (x) (s : Set M) : span R (insert x s)
 = R ∙ x ⊔ span R s
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem fg_induction {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {motive : ∀ N : Submodule R M, N.FG → Prop}
    (singleton : ∀ x : M, motive (R ∙ x) (fg_span_singleton _))
    (sup : ∀ (N₁ N₂ : Submodule R M) (hN₁ : N₁.FG) (hN₂ : N₂.FG),
      motive N₁ hN₁ → motive N₂ hN₂ → motive (N₁ ⊔ N₂) (hN₁.sup hN₂))
    (N : Submodule R M) (hN : N.FG) : motive N hN := by classical
  obtain ⟨s, rfl⟩ := hN
  induction s using Finset.induction with
  | empty => simpa using singleton 0
  | insert x s hxs ih =>
    simpa [span_insert, sup_comm] using
      sup (span R s) (R ∙ x) _ (fg_span_singleton _) ih (singleton x)
/-
**Submodule.fg_sup_span_induction** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_sup_span_induction {R M : Type*} [Semiring R] [AddCommMonoid M] [Module
 R M] {motive : forall N : Submodule R M, N.FG -> Prop} (bot : motive ⊥ fg_bot) 
(sup : forall (N : Submodule R M) (x : M) (hN : N.FG), motive N hN -> motive (N 
⊔ (R ∙ x)) (hN.sup <| fg_span_singleton x)) (N : Submodule R M) (hN : N.FG) : mo
tive N hN
参数：bot : motive ⊥ fg_bot；sup : forall (N : Submodule R M) (x : M) (hN : N.FG), m
otive N hN -> motive (N ⊔ (R ∙ x)) (hN.sup <| fg_span_singleton x)；N : Submodule
 R M；hN : N.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.fg_bot`：fg_bot : (⊥ : Submodule R M).FG
· 使用定理 `Submodule.FG.sup`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N₁ N₂ : Submodule R M},
 N₁.FG…
· 使用定理 `Submodule.fg_span_singleton`：fg_span_singleton (x : M) : FG (R ∙ x)
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Submodule.span_insert`：span_insert (x) (s : Set M) : span R (insert x s)
 = R ∙ x ⊔ span R s
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem fg_sup_span_induction {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {motive : ∀ N : Submodule R M, N.FG → Prop}
    (bot : motive ⊥ fg_bot)
    (sup : ∀ (N : Submodule R M) (x : M) (hN : N.FG),
      motive N hN → motive (N ⊔ (R ∙ x)) (hN.sup <| fg_span_singleton x))
    (N : Submodule R M) (hN : N.FG) : motive N hN := by classical
  obtain ⟨s, rfl⟩ := hN
  induction s using Finset.induction with
  | empty => simp [bot]
  | insert x s hxs ih => simpa [span_insert, sup_comm] using sup (span R s) x (by use s) ih

section RestrictScalars

variable {R A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M]
variable {S : Submodule A M}

/-
**Submodule.FG.restrictScalars_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e.FG`。
形式化陈述：∀ {R : Type u_4} {A : Type u_5} {M : Type u_6} [inst : Semiring A] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module A M] {S : Submodule A M} [inst_3 :
 CommSemiring R] [inst_4 : Algebra R A]   [inst_5 : _root_.Module R M] [inst_6 :
 IsScalarTower R A M],   S.FG → Function.Surjective ⇑(algebraMap R A) → (Submodu
le.restrictScalars R S).FG
参数：algebraMap R A；Submodule.restrictScalars R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.restrictScalars_span`：restrictScalars_span (hsur : Function.Su
rjective (algebraMap R A)) (X : Set M) : restrictScalars R (span A X) = span R X
-/
theorem FG.restrictScalars_of_surjective [CommSemiring R] [Algebra R A] [Module R M]
    [IsScalarTower R A M] (hS : S.FG) (h : Function.Surjective (algebraMap R A)) :
    (restrictScalars R S).FG := by
  obtain ⟨s, rfl⟩ := hS
  exact ⟨s, .symm <| restrictScalars_span R A h _⟩

@[deprecated (since := "2026-01-24")]
alias fg_restrictScalars := FG.restrictScalars_of_surjective
/-
**Submodule.FG.of_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {A : Type u_5} {M : Type u_6} [inst : Semiring A] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module A M]   {S : Submodule A M} (R : Type u_7) [inst_3 :
 Semiring R] [inst_4 : _root_.Module R M] [inst_5 : SMul R A]   [inst_6 : IsScal
arTower R A M], (Submodule.restrictScalars R S).FG → S.FG
参数：R : Type u_7；Submodule.restrictScalars R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.restrictScalars_injective`：restrictScalars_injective : Functio
n.Injective (restrictScalars S : Submodule R M -> Submodule S M)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.restrictScalars_le`：∀ (S : Type u_1) {R : Type u_2} {M : Type 
u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S]   [ins
t_3 : _root_.Modul…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_le_restrictScalars`：span_le_restrictScalars : span R s <=
 (span S s).restrictScalars R
-/
theorem FG.of_restrictScalars (R) [Semiring R] [Module R M] [SMul R A] [IsScalarTower R A M]
    (hS : (S.restrictScalars R).FG) : S.FG := by
  obtain ⟨s, e⟩ := hS
  refine ⟨s, restrictScalars_injective R _ _ (le_antisymm ?_ ?_)⟩
  · have := span_le.mp e.le
    rwa [restrictScalars_le, span_le]
  · rw [← e]
    exact span_le_restrictScalars ..

end RestrictScalars

/-
**Submodule.FG.stabilizes_of_iSup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {M' : Submodule R M}, M'.FG → ∀ (N : ℕ →o Su
bmodule R M), iSup ⇑N = M' → ∃ n, M' = N n
参数：N : ℕ →o Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_iSup_of_chain`：mem_iSup_of_chain (a : Nat ->o Submodule R 
M) (m : M) : (m in ⨆ k, a k) ↔ exists k, m in a k
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `OrderHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : Preorder α] 
[inst_1 : Preorder β] (self : α →o β), Monotone self.toFun
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.mem_attach`：mem_attach (s : Finset α) : forall x, x in s.attach
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem FG.stabilizes_of_iSup_eq {M' : Submodule R M} (hM' : M'.FG) (N : ℕ →o Submodule R M)
    (H : iSup N = M') : ∃ n, M' = N n := by
  obtain ⟨S, hS⟩ := hM'
  have (s : S) : ∃ n, (s : M) ∈ N n :=
    (mem_iSup_of_chain N s).mp (by simpa [H, ← hS] using subset_span s.prop)
  choose f hf using this
  use S.attach.sup f
  apply le_antisymm
  · rw [← hS, span_le]
    intro s hs
    exact N.monotone' (Finset.le_sup <| S.mem_attach ⟨s, hs⟩) (hf _)
  · rw [← H]
    exact le_iSup ..

/-- Finitely generated submodules are precisely compact elements in the submodule lattice. -/
/-
**Submodule.fg_iff_compact** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_iff_compact (s : Submodule R M) : s.FG ↔ IsCompactElement s
参数：s : Submodule R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_eq_iSup_of_singleton_spans`：span_eq_iSup_of_singleton_spa
ns (s : Set M) : span R s = ⨆ x in s, R ∙ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `CompleteLattice.isCompactElement_finsetSup`：isCompactElement_finsetSup {
α β : Type*} [CompleteLattice α] {f : β -> α} (s : Finset β) (h : forall x in s,
 IsCompactElement (f x)) : IsCom…
· 使用定理 `Submodule.singleton_span_isCompactElement`：singleton_span_isCompactEleme
nt (x : M) : IsCompactElement (span R {x} : Submodule R M)
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `iSup_image`：iSup_image {γ} {f : β -> γ} {g : γ -> α} {t : Set β} : ⨆ c i
n f '' t, g c = ⨆ b in t, g (f b)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Submodule.span_eq`：span_eq : span R (p : Set M) = p
· 使用定理 `CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup`：isCompac
tElement_iff_exists_le_sSup_of_le_sSup (k : α) : IsCompactElement k ↔ forall s :
 Set α, k <= sSup s -> exists t : Finset α, ↑t subse…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.sup_id_eq_sSup`：sup_id_eq_sSup [CompleteLattice α] (s : Finset α)
 : s.sup id = sSup s
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.subset_set_image_iff`：subset_set_image_iff [DecidableEq β] {s : S
et α} {t : Finset β} {f : α -> β} : ↑t subseteq f '' s ↔ exists s' : Finset α, ↑
s' subseteq s ∧ s…
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)

--- 原说明 ---
Finitely generated submodules are precisely compact elements in the submodule la
ttice.
-/
theorem fg_iff_compact (s : Submodule R M) : s.FG ↔ IsCompactElement s := by
  -- Introduce shorthand for span of an element
  let sp : M → Submodule R M := fun a => span R {a}
  -- Trivial rewrite lemma; a small hack since simp (only) & rw can't accomplish this smoothly.
  have supr_rw : ∀ t : Finset M, ⨆ x ∈ t, sp x = ⨆ x ∈ (↑t : Set M), sp x := fun t => by rfl
  constructor
  · rintro ⟨t, rfl⟩
    rw [span_eq_iSup_of_singleton_spans, ← supr_rw, ← t.sup_eq_iSup sp]
    apply CompleteLattice.isCompactElement_finsetSup
    exact fun n _ => singleton_span_isCompactElement n
  · intro h
    rw [CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup] at h
    -- s is the Sup of the spans of its elements.
    have sSup' : s = sSup (sp '' ↑s) := by
      rw [sSup_eq_iSup, iSup_image, ← span_eq_iSup_of_singleton_spans, eq_comm, span_eq]
    -- by h, s is then below (and equal to) the sup of the spans of finitely many elements.
    obtain ⟨u, ⟨huspan, husup⟩⟩ := h (sp '' ↑s) (le_of_eq sSup')
    have ssup : s = u.sup id := by
      suffices u.sup id ≤ s from le_antisymm husup this
      rw [sSup', Finset.sup_id_eq_sSup]
      exact sSup_le_sSup huspan
    obtain ⟨t, -, rfl⟩ := Finset.subset_set_image_iff.mp huspan
    rw [Finset.sup_image, Function.id_comp, Finset.sup_eq_iSup, supr_rw,
      ← span_eq_iSup_of_singleton_spans, eq_comm] at ssup
    exact ⟨t, ssup⟩

end Submodule

section ModuleAndAlgebra

variable (R A B M N : Type*)

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

namespace Finite

open Submodule Set

variable {R M N}

/-
**Module.Finite.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.Finite R M] : IsCoatomic (Submodule R M) :=
  CompleteLattice.coatomic_of_top_compact <| by rwa [← fg_iff_compact, ← finite_def]

-- See note [lower instance priority]
/-
**Module.Finite.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) of_finite [Finite M] : Module.Finite R M := by
  cases nonempty_fintype M
  exact ⟨⟨Finset.univ, by rw [Finset.coe_univ, span_univ]⟩⟩

section

variable {S} {P : Type*} [Semiring S] [AddCommMonoid P] [Module S P] {σ : R →+* S}

@[stacks 0519 "(3)"]
/-
**Module.Finite.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
形式化陈述：of_surjective [hM : Module.Finite R M] (f : M ->ₛₗ[σ] P) (hf : Surjective 
f) : Module.Finite S P
参数：f : M ->ₛₗ[σ] P；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finite_def`：finite_def {R M} [Semiring R] [AddCommMonoid M] [Modu
le R M] : Module.Finite R M ↔ (⊤ : Submodule R M).FG
· 使用定理 `Submodule.fg_def`：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, 
S.Finite ∧ span R S = N
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Submodule.image_span_subset_span`：image_span_subset_span (f : M ->ₛₗ[σ₁₂
] M₂) (s : Set M) : f '' span R s subseteq span R₂ (f '' s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
theorem of_surjective [hM : Module.Finite R M] (f : M →ₛₗ[σ] P) (hf : Surjective f) :
    Module.Finite S P := by
  rw [Module.finite_def, Submodule.fg_def] at hM ⊢
  obtain ⟨s, hsfin, hs⟩ := hM
  refine ⟨f '' s, hsfin.image f, eq_top_iff.mpr fun p _ ↦ ?_⟩
  exact image_span_subset_span f s (by simpa [hs] using hf p)
/-
**Module.Finite._root_.LinearMap.finite_iff_of_bijective** 是 Mathlib 中的一个定理，位于命名
空间 `Module.Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.finite_iff_of_bijective [RingHomSurjective σ]
    (f : M →ₛₗ[σ] P) (hf : Function.Bijective f) : Module.Finite R M ↔ Module.Finite S P :=
  ⟨fun _ ↦ of_surjective f hf.surjective, fun _ ↦ ⟨fg_of_fg_map_injective f hf.injective <| by
    rwa [Submodule.map_top, LinearMap.range_eq_top.mpr hf.surjective, ← Module.finite_def]⟩⟩

end

/-
**Module.Finite.quotient** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
形式化陈述：quotient (R) {A M} [Semiring R] [AddCommGroup M] [Ring A] [Module A M] [Mo
dule R M] [SMul R A] [IsScalarTower R A M] [Module.Finite R M] (N : Submodule A 
M) : Module.Finite R (M ⧸ N)
参数：R；N : Submodule A M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
-/
instance quotient (R) {A M} [Semiring R] [AddCommGroup M] [Ring A] [Module A M] [Module R M]
    [SMul R A] [IsScalarTower R A M] [Module.Finite R M] (N : Submodule A M) :
    Module.Finite R (M ⧸ N) :=
  Module.Finite.of_surjective (N.mkQ.restrictScalars R) N.mkQ_surjective

/-- The range of a linear map from a finite module is finite. -/
/-
**Module.Finite.range** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
形式化陈述：range [Module.Finite R M] (f : M ->ₗ[R] N) : Module.Finite R f.range
参数：f : M ->ₗ[R] N。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2

--- 原说明 ---
The range of a linear map from a finite module is finite.
-/
instance range [Module.Finite R M] (f : M →ₗ[R] N) : Module.Finite R f.range :=
  of_surjective (SemilinearMapClass.semilinearMap f).rangeRestrict
    fun ⟨_, y, hy⟩ => ⟨y, Subtype.ext hy⟩

/-- Pushforwards of finite submodules are finite. -/
/-
**Module.Finite.map** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
形式化陈述：map (p : Submodule R M) [Module.Finite R p] (f : M ->ₗ[R] N) : Module.Fini
te R (p.map f)
参数：p : Submodule R M；f : M ->ₗ[R] N。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2

--- 原说明 ---
Pushforwards of finite submodules are finite.
-/
instance map (p : Submodule R M) [Module.Finite R p] (f : M →ₗ[R] N) : Module.Finite R (p.map f) :=
  of_surjective (f.restrict fun _ ↦ mem_map_of_mem) fun ⟨_, _, hy, hy'⟩ ↦ ⟨⟨_, hy⟩, Subtype.ext hy'⟩
/-
**Module.Finite.pi** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
形式化陈述：pi {ι : Type*} {M : ι -> Type*} [_root_.Finite ι] [forall i, AddCommMonoid
 (M i)] [forall i, Module R (M i)] [h : forall i, Module.Finite R (M i)] : Modul
e.Finite R (forall i, M i)
参数：M i；M i；M i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.pi_top`：pi_top (s : Set ι) : (pi s fun i : ι => (⊤ : Submodule
 R (φ i))) = ⊤
· 使用定理 `Submodule.fg_pi`：fg_pi {ι : Type*} {M : ι -> Type*} [Finite ι] [forall i
, AddCommMonoid (M i)] [forall i, Module R (M i)] {p : forall i, Submodule R (M 
i)} (…
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
-/
instance pi {ι : Type*} {M : ι → Type*} [_root_.Finite ι] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] [h : ∀ i, Module.Finite R (M i)] : Module.Finite R (∀ i, M i) :=
  ⟨by
    rw [← pi_top]
    exact fg_pi fun i => (h i).fg_top⟩
/-
**Module.Finite.of_pi** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
形式化陈述：of_pi {ι : Type*} (M : ι -> Type*) [forall i, AddCommMonoid (M i)] [forall
 i, Module R (M i)] [Module.Finite R (forall i, M i)] (i : ι) : Module.Finite R 
(M i)
参数：M : ι -> Type*；M i；M i；forall i, M i；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `LinearMap.proj_surjective`：proj_surjective (i : ι) : Surjective (proj i 
: ((i : ι) -> φ i) ->ₗ[R] φ i)
-/
theorem of_pi {ι : Type*} (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [Module.Finite R (∀ i, M i)] (i : ι) : Module.Finite R (M i) :=
  of_surjective _ <| LinearMap.proj_surjective i
/-
**Module.Finite.pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
形式化陈述：pi_iff {ι : Type*} {M : ι -> Type*} [_root_.Finite ι] [forall i, AddCommMo
noid (M i)] [forall i, Module R (M i)] : Module.Finite R (forall i, M i) ↔ foral
l i, Module.Finite R (M i)
参数：M i；M i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_pi`：of_pi {ι : Type*} (M : ι -> Type*) [forall i, AddCo
mmMonoid (M i)] [forall i, Module R (M i)] [Module.Finite R (forall i, M i)] (i 
: ι) : Mo…
-/
theorem pi_iff {ι : Type*} {M : ι → Type*} [_root_.Finite ι] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] : Module.Finite R (∀ i, M i) ↔ ∀ i, Module.Finite R (M i) :=
  ⟨fun _ i => of_pi M i, fun _ => inferInstance⟩

variable (R)
/-
**Module.Finite._root_.Ideal.fg_top** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ideal.fg_top : (⊤ : Ideal R).FG :=
  ⟨{1}, by simpa only [Finset.coe_singleton] using Ideal.span_singleton_one⟩
/-
**Module.Finite.self** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
形式化陈述：self : Module.Finite R R
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.fg_top`：∀ (R : Type u_1) [inst : Semiring R], ⊤.FG
-/
instance self : Module.Finite R R := ⟨Ideal.fg_top R⟩

variable (M)
/-
**Module.Finite.of_restrictScalars_finite** 是 Mathlib 中的一个定理，位于命名空间 `Module.Fini
te`。
形式化陈述：of_restrictScalars_finite (R A M : Type*) [Semiring R] [Semiring A] [AddCo
mmMonoid M] [Module R M] [Module A M] [SMul R A] [IsScalarTower R A M] [hM : Mod
ule.Finite R M] : Module.Finite A M
参数：R A M : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finite_def`：finite_def {R M} [Semiring R] [AddCommMonoid M] [Modu
le R M] : Module.Finite R M ↔ (⊤ : Submodule R M).FG
· 使用定理 `Submodule.fg_def`：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, 
S.Finite ∧ span R S = N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Submodule.span_le_restrictScalars`：span_le_restrictScalars : span R s <=
 (span S s).restrictScalars R
-/
theorem of_restrictScalars_finite (R A M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M]
    [Module R M] [Module A M] [SMul R A] [IsScalarTower R A M] [hM : Module.Finite R M] :
    Module.Finite A M := by
  rw [finite_def, fg_def] at hM ⊢
  obtain ⟨S, hSfin, hSgen⟩ := hM
  refine ⟨S, hSfin, eq_top_iff.mpr ?_⟩
  have := span_le_restrictScalars R A S
  rwa [hSgen] at this

variable {R M}
/-
**Module.Finite.equiv** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
形式化陈述：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.Finite R N
参数：e : M ≃ₗ[R] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
-/
theorem equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.Finite R N :=
  of_surjective (e : M →ₗ[R] N) e.surjective
/-
**Module.Finite.equiv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
形式化陈述：equiv_iff (e : M ≃ₗ[R] N) : Module.Finite R M ↔ Module.Finite R N
参数：e : M ≃ₗ[R] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
-/
theorem equiv_iff (e : M ≃ₗ[R] N) : Module.Finite R M ↔ Module.Finite R N :=
  ⟨fun _ ↦ equiv e, fun _ ↦ equiv e.symm⟩
/-
**Module.Finite.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.Finite R M] : Module.Finite R Mᵐᵒᵖ := equiv (MulOpposite.opLinearEquiv R)
/-
**Module.Finite.ulift** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
形式化陈述：ulift [Module.Finite R M] : Module.Finite R (ULift M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
-/
instance ulift [Module.Finite R M] : Module.Finite R (ULift M) := equiv ULift.moduleEquiv.symm

universe u in
/-
**Module.Finite.shrink** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
形式化陈述：shrink [Module.Finite R M] [Small.{u} M] : Module.Finite R (Shrink.{u} M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
-/
instance shrink [Module.Finite R M] [Small.{u} M] : Module.Finite R (Shrink.{u} M) :=
  Module.Finite.equiv (Shrink.linearEquiv R M).symm

set_option linter.dupNamespace false in
@[deprecated (since := "2026-04-18")] alias Module.finite_shrink := shrink

/-- A submodule is finite as a module iff it is finitely generated. -/
/-
**Module.Finite.iff_fg** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
形式化陈述：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N.FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Module.finite_def`：finite_def {R M} [Semiring R] [AddCommMonoid M] [Modu
le R M] : Module.Finite R M ↔ (⊤ : Submodule R M).FG
· 使用定理 `Submodule.fg_top`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (N : Submodule R M), ⊤.F
G ↔ N.…

--- 原说明 ---
A submodule is finite as a module iff it is finitely generated.
-/
theorem iff_fg {N : Submodule R M} : Module.Finite R N ↔ N.FG := finite_def.trans N.fg_top

/-- A finitely-generated submodule is finite as a module. -/
alias ⟨_, of_fg⟩ := iff_fg

/-- A submodule that is finite as a module is finitely generated. -/
/-
**Module.Finite._root_.Submodule.FG.of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Module.
Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule that is finite as a module is finitely generated.
-/
theorem _root_.Submodule.FG.of_finite {N : Submodule R M} [Module.Finite R N] : N.FG :=
  iff_fg.mp ‹_›

variable (R M)
/-
**Module.Finite.bot** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
形式化陈述：bot : Module.Finite R (⊥ : Submodule R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `Submodule.fg_bot`：fg_bot : (⊥ : Submodule R M).FG
-/
instance bot : Module.Finite R (⊥ : Submodule R M) := .of_fg fg_bot
/-
**Module.Finite.top** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
形式化陈述：top [Module.Finite R M] : Module.Finite R (⊤ : Submodule R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
-/
instance top [Module.Finite R M] : Module.Finite R (⊤ : Submodule R M) := .of_fg fg_top
/-
**Module.Finite.top_left** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
形式化陈述：top_left [Module.Finite R M] : Module.Finite (⊤ : Subsemiring R) M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.instToRingHomRingEquiv`：∀ {R₁ : Type u_1} {R₂ : Type u
_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] (σ : R₁ ≃+* R₂), RingHomSurjecti
ve ↑σ
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
-/
instance top_left [Module.Finite R M] : Module.Finite (⊤ : Subsemiring R) M :=
  have : RingHomSurjective (Subsemiring.topEquiv (R := R)).symm.toRingHom :=
    RingHomSurjective.instToRingHomRingEquiv Subsemiring.topEquiv.symm
  of_surjective (σ := (Subsemiring.topEquiv (R := R)).symm.toRingHom)
      ⟨⟨id, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩ Function.surjective_id

variable {M}

/-- The submodule generated by a finite set is `R`-finite. -/
/-
**Module.Finite.span_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
形式化陈述：span_of_finite {A : Set M} (hA : Set.Finite A) : Module.Finite R (span R A
)
参数：hA : Set.Finite A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s

--- 原说明 ---
The submodule generated by a finite set is `R`-finite.
-/
theorem span_of_finite {A : Set M} (hA : Set.Finite A) : Module.Finite R (span R A) :=
  of_fg ⟨hA.toFinset, hA.coe_toFinset.symm ▸ rfl⟩

/-- The submodule generated by a single element is `R`-finite. -/
/-
**Module.Finite.span_singleton** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
形式化陈述：span_singleton (x : M) : Module.Finite R (R ∙ x)
参数：x : M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.span_of_finite`：span_of_finite {A : Set M} (hA : Set.Finit
e A) : Module.Finite R (span R A)
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite

--- 原说明 ---
The submodule generated by a single element is `R`-finite.
-/
instance span_singleton (x : M) : Module.Finite R (R ∙ x) :=
  span_of_finite R <| Set.finite_singleton _

/-- The submodule generated by a finset is `R`-finite. -/
/-
**Module.Finite.span_finset** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
形式化陈述：span_finset (s : Finset M) : Module.Finite R (span R (s : Set M))
参数：s : Finset M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…

--- 原说明 ---
The submodule generated by a finset is `R`-finite.
-/
instance span_finset (s : Finset M) : Module.Finite R (span R (s : Set M)) :=
  of_fg ⟨s, rfl⟩

variable {R}

section Algebra

/-
**Module.Finite.trans** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
形式化陈述：∀ {R : Type u_6} (A : Type u_7) (M : Type u_8) [inst : Semiring R] [inst_1
 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : AddCommMonoid M] [inst_4
 : _root_.Module R M] [inst_5 : _root_.Module A M] [IsScalarTower R A M]   [Modu
le.Finite R A] [Module.Finite A M], Module.Finite R M
参数：A : Type u_7；M : Type u_8。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.fg_def`：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, 
S.Finite ∧ span R S = N
· 使用定理 `Set.Finite.image2`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : S
et α} {t : Set β} (f : α → β → γ),   s.Finite → t.Finite → (Set.image2 f s t).Fi
nite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : 
Set α} {t : Set β}, Set.image2 (fun x1 x2 => x1 • x2) s t = s • t
· 使用定理 `Submodule.span_smul_of_span_eq_top`：span_smul_of_span_eq_top {s : Set S}
 (hs : span R s = ⊤) (t : Set A) : span R (s • t) = (span S t).restrictScalars R
· 使用定理 `Submodule.restrictScalars_top`：restrictScalars_top : restrictScalars S (
⊤ : Submodule R M) = ⊤
-/
theorem trans {R : Type*} (A M : Type*) [Semiring R] [Semiring A] [Module R A]
    [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M] :
    ∀ [Module.Finite R A] [Module.Finite A M], Module.Finite R M
  | ⟨⟨s, hs⟩⟩, ⟨⟨t, ht⟩⟩ =>
    ⟨fg_def.mpr
      ⟨image2 (· • ·) (↑s : Set A) (↑t : Set M),
        Finite.image2 _ s.finite_toSet t.finite_toSet,
        by rw [image2_smul, span_smul_of_span_eq_top hs (↑t : Set M), ht, restrictScalars_top]⟩⟩

/-- See also `Module.Finite.of_surjective` and `LinearMap.finite_iff_of_bijective`. -/
/-
**Module.Finite.of_equiv_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Module.Finite`。
形式化陈述：of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommSemiring A₁] [CommSemiring B₁] [
CommSemiring A₂] [Semiring B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) 
(e₂ : B₁ ≃+* B₂) (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (a
lgebraMap A₁ B₁)) [Module.Finite A₁ B₁] : Module.Finite A₂ B₂
参数：e₁ : A₁ ≃+* A₂；e₂ : B₁ ≃+* B₂；he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = Ring
Hom.comp ↑e₂ (algebraMap A₁ B₁)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RingEquiv.map_mul'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `RingEquiv.map_add'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Finite.of_restrictScalars_finite`：of_restrictScalars_finite (R A 
M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M] [Module R M] [Module A M]
 [SMul R A] [IsScalarTower R …
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N

--- 原说明 ---
See also `Module.Finite.of_surjective` and `LinearMap.finite_iff_of_bijective`.
-/
lemma of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommSemiring A₁] [CommSemiring B₁]
    [CommSemiring A₂] [Semiring B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂)
    (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁))
    [Module.Finite A₁ B₁] : Module.Finite A₂ B₂ := by
  let := e₁.toRingHom.toAlgebra
  let := ((algebraMap A₁ B₁).comp e₁.symm.toRingHom).toAlgebra
  have : IsScalarTower A₁ A₂ B₁ := IsScalarTower.of_algebraMap_eq
    (fun x ↦ by simp [RingHom.algebraMap_toAlgebra])
  let e : B₁ ≃ₐ[A₂] B₂ :=
    { e₂ with
      commutes' := fun r ↦ by
        simpa [RingHom.algebraMap_toAlgebra] using DFunLike.congr_fun he.symm (e₁.symm r) }
  have := of_restrictScalars_finite A₁ A₂ B₁
  exact equiv e.toLinearEquiv

end Algebra

end Finite

end Module

end ModuleAndAlgebra

namespace Submodule

open Module

variable {R V} [Ring R] [AddCommGroup V] [Module R V]

/-- The sup of two fg submodules is finite. Also see `Submodule.FG.sup`. -/
/-
**Submodule.finite_sup** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：finite_sup (S₁ S₂ : Submodule R V) [h₁ : Module.Finite R S₁] [h₂ : Module.
Finite R S₂] : Module.Finite R (S₁ ⊔ S₂ : Submodule R V)
参数：S₁ S₂ : Submodule R V。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `Submodule.FG.sup`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N₁ N₂ : Submodule R M},
 N₁.FG…

--- 原说明 ---
The sup of two fg submodules is finite. Also see `Submodule.FG.sup`.
-/
instance finite_sup (S₁ S₂ : Submodule R V) [h₁ : Module.Finite R S₁]
    [h₂ : Module.Finite R S₂] : Module.Finite R (S₁ ⊔ S₂ : Submodule R V) := by
  rw [Finite.iff_fg] at *
  exact .sup h₁ h₂

/-- The submodule generated by a finite supremum of finite-dimensional submodules is
finite-dimensional.

Note that strictly this only needs `∀ i ∈ s, FiniteDimensional K (S i)`, but that doesn't
work well with typeclass search. -/
/-
**Submodule.finite_finset_sup** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：finite_finset_sup {ι : Type*} (s : Finset ι) (S : ι -> Submodule R V) [for
all i, Module.Finite R (S i)] : Module.Finite R (s.sup S : Submodule R V)
参数：s : Finset ι；S : ι -> Submodule R V；S i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_induction`：sup_induction {p : α -> Prop} (hb : p ⊥) (hp : for
all a₁, p a₁ -> forall a₂, p a₂ -> p (a₁ ⊔ a₂)) (hs : forall b in s, p (f b)) : 
p (s.sup f…

--- 原说明 ---
The submodule generated by a finite supremum of finite-dimensional submodules is
finite-dimensional.

Note that strictly this only needs `∀ i ∈ s, FiniteDimensional K (S i)`, but tha
t doesn't
work well with typeclass search.
-/
instance finite_finset_sup {ι : Type*} (s : Finset ι) (S : ι → Submodule R V)
    [∀ i, Module.Finite R (S i)] : Module.Finite R (s.sup S : Submodule R V) := by
  refine s.sup_induction (f := S) (p := fun i => Module.Finite R ↑i) (Module.Finite.bot R V) ?_
    inferInstance
  intro S₁ hS₁ S₂ hS₂
  exact finite_sup S₁ S₂

section RestrictScalars

variable {R : Type*} [Semiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {A : Type*} [Semiring A] [Module R A] [Module A M] [IsScalarTower R A M]
variable {S : Submodule A M}

set_option backward.isDefEq.respectTransparency false in
/-
**Submodule.FG.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {M : Type u_2} [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {A : Type u_3} [inst_3 : Semiring A] [inst_4
 : _root_.Module R A] [inst_5 : _root_.Module A M]   [inst_6 : IsScalarTower R A
 M] {S : Submodule A M} [Module.Finite R A], S.FG → (Submodule.restrictScalars R
 S).FG
参数：Submodule.restrictScalars R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `Module.Finite.trans`：∀ {R : Type u_6} (A : Type u_7) (M : Type u_8) [ins
t : Semiring R] [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : A
ddCommMon…
-/
theorem FG.restrictScalars [Module.Finite R A] (hS : S.FG) : (S.restrictScalars R).FG := by
  rw [← Module.Finite.iff_fg] at *
  exact Module.Finite.trans A S

@[simp]
/-
**Submodule.FG.restrictScalars_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {M : Type u_2} [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {A : Type u_3} [inst_3 : Semiring A] [inst_4
 : _root_.Module R A] [inst_5 : _root_.Module A M]   [inst_6 : IsScalarTower R A
 M] {S : Submodule A M} [Module.Finite R A], (Submodule.restrictScalars R S).FG 
↔ S.FG
参数：Submodule.restrictScalars R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.FG.of_restrictScalars`：∀ {A : Type u_5} {M : Type u_6} [inst :
 Semiring A] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module A M]   {S : Subm
odule A M} (R : Type …
· 使用定理 `Submodule.FG.restrictScalars`：∀ {R : Type u_1} [inst : Semiring R] {M : 
Type u_2} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {A : Type u_
3} [inst_3 : Semir…
-/
theorem FG.restrictScalars_iff [Module.Finite R A] : (S.restrictScalars R).FG ↔ S.FG :=
  ⟨of_restrictScalars R, restrictScalars⟩

/-- If a ring `R` is finite over a subring `S` then the `R`-span of an FG `S`-submodule is FG. -/
/-
**Submodule.FG.span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {M : Type u_2} [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {A : Type u_3} [inst_3 : Semiring A] [inst_4
 : _root_.Module R A] [inst_5 : _root_.Module A M] [IsScalarTower R A M]   {S : 
Submodule R M}, S.FG → (Submodule.span A ↑S).FG
参数：Submodule.span A ↑S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_span_of_tower`：span_span_of_tower : span S (span R s : Se
t M) = span S s

--- 原说明 ---
If a ring `R` is finite over a subring `S` then the `R`-span of an FG `S`-submod
ule is FG.
-/
protected theorem FG.span {S : Submodule R M} (hS : S.FG) : (span A (S : Set M)).FG := by
  obtain ⟨t, ht⟩ := hS
  use t
  rw [← ht, Submodule.span_span_of_tower]

end RestrictScalars

end Submodule

namespace RingHom

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

namespace Finite

variable (A) in
/-
**RingHom.Finite.id** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Finite`。
形式化陈述：id : Finite (RingHom.id A)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id : Finite (RingHom.id A) :=
  Module.Finite.self A
/-
**RingHom.Finite.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Finite`。
形式化陈述：of_surjective (f : A ->+* B) (hf : Surjective f) : f.Finite
参数：f : A ->+* B；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
-/
theorem of_surjective (f : A →+* B) (hf : Surjective f) : f.Finite :=
  letI := f.toAlgebra
  Module.Finite.of_surjective (Algebra.linearMap A B) hf
/-
**RingHom.Finite._root_.RingEquiv.finite** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Fini
te`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.RingEquiv.finite (e : A ≃+* B) : e.toRingHom.Finite :=
  .of_surjective _ e.surjective
/-
**RingHom.Finite.** 是 Mathlib 中的一个实例，位于命名空间 `RingHom.Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (h : A ≃+* B) : letI := h.toRingHom.toAlgebra; Module.Finite A B :=
  h.finite
/-
**RingHom.Finite.comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Finite`。
形式化陈述：comp {g : B ->+* C} {f : A ->+* B} (hg : g.Finite) (hf : f.Finite) : (g.co
mp f).Finite
参数：hg : g.Finite；hf : f.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Module.Finite.trans`：∀ {R : Type u_6} (A : Type u_7) (M : Type u_8) [ins
t : Semiring R] [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : A
ddCommMon…
-/
theorem comp {g : B →+* C} {f : A →+* B} (hg : g.Finite) (hf : f.Finite) : (g.comp f).Finite := by
  algebraize [f, g, g.comp f]
  exact .trans B C
/-
**RingHom.Finite.of_comp_finite** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Finite`。
形式化陈述：of_comp_finite {f : A ->+* B} {g : B ->+* C} (h : (g.comp f).Finite) : g.F
inite
参数：h : (g.comp f).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Module.Finite.of_restrictScalars_finite`：of_restrictScalars_finite (R A 
M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M] [Module R M] [Module A M]
 [SMul R A] [IsScalarTower R …
-/
theorem of_comp_finite {f : A →+* B} {g : B →+* C} (h : (g.comp f).Finite) : g.Finite := by
  algebraize [f, g, g.comp f]
  exact .of_restrictScalars_finite A B C

end Finite

end RingHom

namespace AlgHom

variable {R A B C : Type*} [CommRing R]
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

namespace Finite

variable (R A)

/-
**AlgHom.Finite.id** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom.Finite`。
形式化陈述：id : Finite (AlgHom.id R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.Finite.id`：id : Finite (RingHom.id A)
-/
theorem id : Finite (AlgHom.id R A) :=
  RingHom.Finite.id A

variable {R A}
/-
**AlgHom.Finite.comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom.Finite`。
形式化陈述：comp {g : B ->ₐ[R] C} {f : A ->ₐ[R] B} (hg : g.Finite) (hf : f.Finite) : (
g.comp f).Finite
参数：hg : g.Finite；hf : f.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.Finite.comp`：comp {g : B ->+* C} {f : A ->+* B} (hg : g.Finite) 
(hf : f.Finite) : (g.comp f).Finite
-/
theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.Finite) (hf : f.Finite) : (g.comp f).Finite :=
  RingHom.Finite.comp hg hf
/-
**AlgHom.Finite.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom.Finite`。
形式化陈述：of_surjective (f : A ->ₐ[R] B) (hf : Surjective f) : f.Finite
参数：f : A ->ₐ[R] B；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.Finite.of_surjective`：of_surjective (f : A ->+* B) (hf : Surject
ive f) : f.Finite
-/
theorem of_surjective (f : A →ₐ[R] B) (hf : Surjective f) : f.Finite :=
  RingHom.Finite.of_surjective f.toRingHom hf
/-
**AlgHom.Finite.of_comp_finite** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom.Finite`。
形式化陈述：of_comp_finite {f : A ->ₐ[R] B} {g : B ->ₐ[R] C} (h : (g.comp f).Finite) :
 g.Finite
参数：h : (g.comp f).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.Finite.of_comp_finite`：of_comp_finite {f : A ->+* B} {g : B ->+*
 C} (h : (g.comp f).Finite) : g.Finite
-/
theorem of_comp_finite {f : A →ₐ[R] B} {g : B →ₐ[R] C} (h : (g.comp f).Finite) : g.Finite :=
  RingHom.Finite.of_comp_finite h

end Finite

end AlgHom

section Ring
variable {R E : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E]

local notation3 "R≥0" => {c : R // 0 ≤ c}

/-
**instModuleFiniteAux** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private instance instModuleFiniteAux : Module.Finite R≥0 R := by
  simp_rw [Module.finite_def, Submodule.fg_def, Submodule.eq_top_iff']
  refine ⟨{1, -1}, by simp, fun x ↦ ?_⟩
  obtain hx | hx := le_total 0 x
  · simpa using Submodule.smul_mem (M := R) (.span R≥0 {1, -1}) ⟨x, hx⟩ (x := 1)
      (Submodule.subset_span <| by simp)
  · simpa using Submodule.smul_mem (M := R) (.span R≥0 {1, -1}) ⟨-x, neg_nonneg.mpr hx⟩ (x := -1)
      (Submodule.subset_span <| by simp)

/-- If a module is finite over a linearly ordered ring, then it is also finite over the non-negative
scalars. -/
/-
**instModuleFinite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instModuleFinite [Module.Finite R E] : Module.Finite R>=0 E
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.trans`：∀ {R : Type u_6} (A : Type u_7) (M : Type u_8) [ins
t : Semiring R] [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : A
ddCommMon…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `_private.Mathlib.RingTheory.Finiteness.Basic.0.instModuleFiniteAux`：∀ {R
 : Type u_1} [inst : Ring R] [inst_1 : LinearOrder R] [inst_2 : IsOrderedRing R]
, Module.Finite { c // 0 ≤ c } R

--- 原说明 ---
If a module is finite over a linearly ordered ring, then it is also finite over 
the non-negative
scalars.
-/
instance instModuleFinite [Module.Finite R E] : Module.Finite R≥0 E := .trans R E

end Ring

