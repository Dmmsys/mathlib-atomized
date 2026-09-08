/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Finitely supported functions and spans

## Tags

function with finite support, module, linear algebra
-/

public section

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

@[simp]
/-
**Finsupp.ker_lsingle** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：ker_lsingle (a : α) : ker (lsingle a : M ->ₗ[R] α ->₀ M) = ⊥
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `Finsupp.single_injective`：single_injective (a : α) : Function.Injective 
(single a : M -> α ->₀ M)
-/
theorem ker_lsingle (a : α) : ker (lsingle a : M →ₗ[R] α →₀ M) = ⊥ :=
  ker_eq_bot_of_injective (single_injective a)
/-
**Finsupp.lsingle_range_le_ker_lapply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lsingle_range_le_ker_lapply (s t : Set α) (h : Disjoint s t) : ⨆ a in s, L
inearMap.range (lsingle a : M ->ₗ[R] α ->₀ M) <= ⨅ a in t, ker (lapply a : (α ->
₀ M) ->ₗ[R] M)
参数：s t : Set α；h : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_le_iff_comap`：range_le_iff_comap [RingHomSurjective τ₁₂]
 {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R₂ M₂} : range f <= p ↔ comap f p = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.comap_iInf`：comap_iInf {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι
 -> Submodule R₂ M₂) : comap f (⨅ i, p i) = ⨅ i, comap f (p i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
-/
theorem lsingle_range_le_ker_lapply (s t : Set α) (h : Disjoint s t) :
    ⨆ a ∈ s, LinearMap.range (lsingle a : M →ₗ[R] α →₀ M) ≤
      ⨅ a ∈ t, ker (lapply a : (α →₀ M) →ₗ[R] M) := by
  refine iSup_le fun a₁ => iSup_le fun h₁ => range_le_iff_comap.2 ?_
  simp only [(ker_comp _ _).symm, eq_top_iff, SetLike.le_def, mem_ker, comap_iInf, mem_iInf]
  intro b _ a₂ h₂
  have : a₂ ≠ a₁ := fun eq => h.le_bot ⟨h₁, eq.symm ▸ h₂⟩
  exact single_eq_of_ne this
/-
**Finsupp.iInf_ker_lapply_le_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：iInf_ker_lapply_le_bot : ⨅ a, ker (lapply a : (α ->₀ M) ->ₗ[R] M) <= ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem iInf_ker_lapply_le_bot : ⨅ a, ker (lapply a : (α →₀ M) →ₗ[R] M) ≤ ⊥ := by
  simp only [SetLike.le_def, mem_iInf, mem_ker, mem_bot, lapply_apply]
  exact fun a h => Finsupp.ext h
/-
**Finsupp.iSup_lsingle_range** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：iSup_lsingle_range : ⨆ a, LinearMap.range (lsingle a : M ->ₗ[R] α ->₀ M) =
 ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.sum_single`：sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum s
ingle = f
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
-/
theorem iSup_lsingle_range : ⨆ a, LinearMap.range (lsingle a : M →ₗ[R] α →₀ M) = ⊤ := by
  refine eq_top_iff.2 <| SetLike.le_def.2 fun f _ => ?_
  rw [← sum_single f]
  exact sum_mem fun a _ => Submodule.mem_iSup_of_mem a ⟨_, rfl⟩
/-
**Finsupp.disjoint_lsingle_lsingle** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：disjoint_lsingle_lsingle (s t : Set α) (hs : Disjoint s t) : Disjoint (⨆ a
 in s, LinearMap.range (lsingle a : M ->ₗ[R] α ->₀ M)) (⨆ a in t, LinearMap.rang
e (lsingle a : M ->ₗ[R] α ->₀ M))
参数：s t : Set α；hs : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Finsupp.lsingle_range_le_ker_lapply`：lsingle_range_le_ker_lapply (s t : 
Set α) (h : Disjoint s t) : ⨆ a in s, LinearMap.range (lsingle a : M ->ₗ[R] α ->
₀ M) <= ⨅ a in t, ker (la…
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `inf_le_of_right_le`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α}
, b ≤ c → a ⊓ b ≤ c
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `inf_le_of_left_le`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α},
 a ≤ c → a ⊓ b ≤ c
· 使用定理 `Finsupp.iInf_ker_lapply_le_bot`：iInf_ker_lapply_le_bot : ⨅ a, ker (lappl
y a : (α ->₀ M) ->ₗ[R] M) <= ⊥
-/
theorem disjoint_lsingle_lsingle (s t : Set α) (hs : Disjoint s t) :
    Disjoint (⨆ a ∈ s, LinearMap.range (lsingle a : M →ₗ[R] α →₀ M))
      (⨆ a ∈ t, LinearMap.range (lsingle a : M →ₗ[R] α →₀ M)) := by
  refine
    (Disjoint.mono
      (lsingle_range_le_ker_lapply s sᶜ disjoint_compl_right)
      (lsingle_range_le_ker_lapply t tᶜ disjoint_compl_right))
      ?_
  rw [disjoint_iff_inf_le]
  refine le_trans (le_iInf fun i => ?_) iInf_ker_lapply_le_bot
  classical
    by_cases his : i ∈ s
    · by_cases hit : i ∈ t
      · exact (hs.le_bot ⟨his, hit⟩).elim
      exact inf_le_of_right_le (iInf_le_of_le i <| iInf_le _ hit)
    exact inf_le_of_left_le (iInf_le_of_le i <| iInf_le _ his)
/-
**Finsupp.span_single_image** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：span_single_image (s : Set M) (a : α) : Submodule.span R (single a '' s) =
 (Submodule.span R s).map (lsingle a : M ->ₗ[R] α ->₀ M)
参数：s : Set M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
-/
theorem span_single_image (s : Set M) (a : α) :
    Submodule.span R (single a '' s) = (Submodule.span R s).map (lsingle a : M →ₗ[R] α →₀ M) := by
  rw [← span_image]; rfl
/-
**Finsupp.range_lmapDomain** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：range_lmapDomain {β : Type*} (u : α -> β) : LinearMap.range (lmapDomain R 
R u) = .span R (.range fun x => single (u x) 1)
参数：u : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Finsupp.induction_linear`：induction_linear {motive : (ι ->₀ M) -> Prop} 
(f : ι ->₀ M) (zero : motive 0) (add : forall f g : ι ->₀ M, motive f -> motive 
g -> motive (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain_zero`：mapDomain_zero {f : α -> β} : mapDomain f (0 : α
 ->₀ M) = (0 : β ->₀ M)
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `Finsupp.lmapDomain_apply`：lmapDomain_apply (f : α -> α') (l : α ->₀ M) :
 (lmapDomain M R f : (α ->₀ M) ->ₗ[R] α' ->₀ M) l = mapDomain f l
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.smul_single_one`：smul_single_one [MulZeroOneClass R] (a : α) (b 
: R) : b • single a (1 : R) = single a b
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_lmapDomain {β : Type*} (u : α → β) :
    LinearMap.range (lmapDomain R R u) = .span R (.range fun x ↦ single (u x) 1) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨x, rfl⟩
    induction x using induction_linear with
    | single i s =>
        rw [lmapDomain_apply, mapDomain_single, ← Finsupp.smul_single_one]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add f g hf hg =>
        rw [map_add]
        exact Submodule.add_mem _ hf hg
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    exact ⟨Finsupp.single i 1, by simp⟩
/-
**Finsupp.span_single_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：span_single_eq_top : span R {single i x | (i : α) (x : M)} = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
· 使用引理 `Finsupp.induction_linear`：induction_linear {motive : (ι ->₀ M) -> Prop} 
(f : ι ->₀ M) (zero : motive 0) (add : forall f g : ι ->₀ M, motive f -> motive 
g -> motive (f…
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Submodule.mem_span_of_mem`：mem_span_of_mem {s : Set M} {x : M} (hx : x i
n s) : x in span R s
-/
lemma span_single_eq_top : span R {single i x | (i : α) (x : M)} = ⊤ := by
  refine eq_top_iff'.mpr fun x ↦ ?_
  induction x using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem ..
  | add f g f_in g_in => exact add_mem f_in g_in
  | single a b => exact mem_span_of_mem ⟨a, b, rfl⟩

end Finsupp

open Finsupp

namespace Submodule

section Semiring

variable {R : Type*} {M : Type*} {N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-
**Submodule.exists_finset_of_mem_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：exists_finset_of_mem_iSup {ι : Sort _} (p : ι -> Submodule R M) {m : M} (h
m : m in ⨆ i, p i) : exists s : Finset ι, m in ⨆ i in s, p i
参数：p : ι -> Submodule R M；hm : m in ⨆ i, p i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteLattice.IsCompactElement.exists_finset_of_le_iSup`：∀ (α : Type u
_2) [inst : CompleteLattice α] {k : α},   IsCompactElement k → ∀ {ι : Type u_3} 
(f : ι → α), k ≤ ⨆ i, f i → ∃ s, k ≤ ⨆ i ∈ s, f…
· 使用定理 `Submodule.singleton_span_isCompactElement`：singleton_span_isCompactEleme
nt (x : M) : IsCompactElement (span R {x} : Submodule R M)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem exists_finset_of_mem_iSup {ι : Sort _} (p : ι → Submodule R M) {m : M}
    (hm : m ∈ ⨆ i, p i) : ∃ s : Finset ι, m ∈ ⨆ i ∈ s, p i := by
  have :=
    CompleteLattice.IsCompactElement.exists_finset_of_le_iSup (Submodule R M)
      (Submodule.singleton_span_isCompactElement m) p
  simp only [Submodule.span_singleton_le_iff_mem] at this
  exact this hm

/-- `Submodule.exists_finset_of_mem_iSup` as an `iff` -/
/-
**Submodule.mem_iSup_iff_exists_finset** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_iSup_iff_exists_finset {ι : Sort _} {p : ι -> Submodule R M} {m : M} :
 (m in ⨆ i, p i) ↔ exists s : Finset ι, m in ⨆ i in s, p i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_finset_of_mem_iSup`：exists_finset_of_mem_iSup {ι : Sort
 _} (p : ι -> Submodule R M) {m : M} (hm : m in ⨆ i, p i) : exists s : Finset ι,
 m in ⨆ i in s, p i
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `iSup_const_le`：iSup_const_le : ⨆ _ : ι, a <= a

--- 原说明 ---
`Submodule.exists_finset_of_mem_iSup` as an `iff`
-/
theorem mem_iSup_iff_exists_finset {ι : Sort _} {p : ι → Submodule R M} {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∃ s : Finset ι, m ∈ ⨆ i ∈ s, p i :=
  ⟨Submodule.exists_finset_of_mem_iSup p, fun ⟨_, hs⟩ =>
    iSup_mono (fun i => (iSup_const_le : _ ≤ p i)) hs⟩
/-
**Submodule.mem_sSup_iff_exists_finset** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_sSup_iff_exists_finset {S : Set (Submodule R M)} {m : M} : m in sSup S
 ↔ exists s : Finset (Submodule R M), ↑s subseteq S ∧ m in ⨆ i in s, i
参数：Submodule R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `Submodule.mem_iSup_iff_exists_finset`：mem_iSup_iff_exists_finset {ι : So
rt _} {p : ι -> Submodule R M} {m : M} : (m in ⨆ i, p i) ↔ exists s : Finset ι, 
m in ⨆ i in s, p i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iSup_exists`：iSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ x, f x 
= ⨆ (i) (h), f ⟨i, h⟩
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `iSup_and'`：iSup_and' {p q : Prop} {s : p -> q -> α} : ⨆ (h₁ : p) (h₂ : q
), s h₁ h₂ = ⨆ h : p ∧ q, s h.1 h.2
-/
theorem mem_sSup_iff_exists_finset {S : Set (Submodule R M)} {m : M} :
    m ∈ sSup S ↔ ∃ s : Finset (Submodule R M), ↑s ⊆ S ∧ m ∈ ⨆ i ∈ s, i := by
  rw [sSup_eq_iSup, iSup_subtype', Submodule.mem_iSup_iff_exists_finset]
  refine ⟨fun ⟨s, hs⟩ ↦ ⟨s.map (Function.Embedding.subtype (· ∈ S)), ?_, ?_⟩,
          fun ⟨s, hsS, hs⟩ ↦ ⟨s.preimage (↑) Subtype.coe_injective.injOn, ?_⟩⟩
  · simp
  · suffices m ∈ ⨆ (i) (hi : i ∈ S) (_ : ⟨i, hi⟩ ∈ s), i by simpa
    rwa [iSup_subtype']
  · have : ⨆ (i) (_ : i ∈ S ∧ i ∈ s), i = ⨆ (i) (_ : i ∈ s), i := by convert! rfl; grind
    simpa only [Finset.mem_preimage, iSup_subtype, iSup_and', this]

end Semiring

section CommSemiring

variable {R M N σ : Type*} [CommSemiring R] [AddCommMonoid M]
variable [AddCommMonoid N] [Module R M] [Module R N]

open scoped Pointwise in
/-
**Submodule.range_lsum_smul** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：range_lsum_smul (φ : M ->ₗ[R] N) (f : σ -> R) : (lsum (S
参数：φ : M ->ₗ[R] N；f : σ -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Submodule.set_smul_span`：set_smul_span (s : Set α) (t : Set M) : s • spa
n R t = span R (s • t)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma range_lsum_smul (φ : M →ₗ[R] N) (f : σ → R) :
    (lsum (S := R) (f · • φ)).range = Set.range f • φ.range := by
  simp_rw [range_eq_map, ← span_single_eq_top, ← span_univ, map_span, set_smul_span]
  congr 1
  aesop (add simp Set.mem_smul)

open scoped Pointwise in
/-
**Submodule.image_smul_top_eq_range_lsum** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：image_smul_top_eq_range_lsum (s : Set σ) (f : σ -> R) : (f '' s • ⊤ : Subm
odule R M) = (lsum (S
参数：s : Set σ；f : σ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `LinearMap.range_id`：range_id : range (LinearMap.id : M ->ₗ[R] M) = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.range_lsum_smul`：range_lsum_smul (φ : M ->ₗ[R] N) (f : σ -> R)
 : (lsum (S
-/
theorem image_smul_top_eq_range_lsum (s : Set σ) (f : σ → R) :
    (f '' s • ⊤ : Submodule R M) = (lsum (S := R) fun i : s ↦ f i • .id).range := by
  simpa [Set.range_comp] using (range_lsum_smul (.id (R := R) (M := M)) (f ∘ (↑) : s → R)).symm

open scoped Pointwise in
/-
**Submodule.smul_top_eq_range_lsum** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_top_eq_range_lsum (s : Set R) : (s • ⊤ : Submodule R M) = (lsum (S
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `Submodule.image_smul_top_eq_range_lsum`：image_smul_top_eq_range_lsum (s 
: Set σ) (f : σ -> R) : (f '' s • ⊤ : Submodule R M) = (lsum (S
-/
theorem smul_top_eq_range_lsum (s : Set R) :
    (s • ⊤ : Submodule R M) = (lsum (S := R) fun i : s ↦ i.val • .id).range := by
  simpa using image_smul_top_eq_range_lsum (M := M) s id

end CommSemiring

end Submodule

