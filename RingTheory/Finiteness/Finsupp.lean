/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness of (sub)modules and finitely supported functions

-/

public section

open Function (Surjective)
open Finsupp

namespace LinearMap

variable {R M N ι : Type*} (S : Type*) [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N] [Semiring S] [Module S N] [SMulCommClass R S N]

/-- The linear map from `Hom(M,N)^(ι)` to `Hom(M,N^(ι))`. This is the `Finsupp` version of
the forward direction of `LinearEquiv.linearMapPi`. -/
/-
**LinearMap.finsuppLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     {N : Type u_3} →       {ι : Type u
_4} →         (S : Type u_5) →           [inst : Semiring R] →             [inst
_1 : AddCommMonoid M] →               [inst_2 : AddCommMonoid N] →              
   [inst_3 : _root_.Module R M] →                   [inst_4 : _root_.Module R N]
 →                     [inst_5 : Semiring S] →                       [inst_6 : _
root_.Module S N] →                         [inst_7 : SMulCommClass R S N] → (ι 
→₀ M →ₗ[R] N) →ₗ[S] M →ₗ[R] ι →₀ N
参数：S : Type u_5；ι →₀ M →ₗ[R] N。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b

--- 原说明 ---
The linear map from `Hom(M,N)^(ι)` to `Hom(M,N^(ι))`. This is the `Finsupp` vers
ion of
the forward direction of `LinearEquiv.linearMapPi`.
-/
@[expose, simps!] noncomputable def finsuppLinearMap : (ι →₀ M →ₗ[R] N) →ₗ[S] M →ₗ[R] ι →₀ N :=
  have := SMulCommClass.symm
  LinearMap.flip
  { toFun := (Finsupp.mapRange.linearMap <| flip id ·)
    map_add' := fun _ _ ↦ by ext; simp
    map_smul' := fun _ _ ↦ by ext; simp }

variable (R M N ι)
/-
**LinearMap.finsuppLinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：finsuppLinearMap_injective : Function.Injective (finsuppLinearMap S : (ι -
>₀ M ->ₗ[R] N) -> M ->ₗ[R] ι ->₀ N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem finsuppLinearMap_injective :
    Function.Injective (finsuppLinearMap S : (ι →₀ M →ₗ[R] N) → M →ₗ[R] ι →₀ N) :=
  fun _ _ eq ↦ by ext i m; exact congr($eq m i)
/-
**LinearMap.finsuppLinearMap_bijective_of_moduleFinite** 是 Mathlib 中的一个定理，位于命名空间
 `LinearMap`。
形式化陈述：finsuppLinearMap_bijective_of_moduleFinite [Module.Finite R M] : Function.
Bijective (finsuppLinearMap S : (ι ->₀ M ->ₗ[R] N) -> M ->ₗ[R] ι ->₀ N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.finite_def`：finite_def {R M} [Semiring R] [AddCommMonoid M] [Modu
le R M] : Module.Finite R M ↔ (⊤ : Submodule R M).FG
· 使用定理 `LinearMap.finsuppLinearMap_injective`：finsuppLinearMap_injective : Funct
ion.Injective (finsuppLinearMap S : (ι ->₀ M ->ₗ[R] N) -> M ->ₗ[R] ι ->₀ N)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `LinearMap.ext_on`：ext_on {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (hv : span R
 s = ⊤) (h : Set.EqOn f g s) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem finsuppLinearMap_bijective_of_moduleFinite [Module.Finite R M] :
    Function.Bijective (finsuppLinearMap S : (ι →₀ M →ₗ[R] N) → M →ₗ[R] ι →₀ N) := by
  have ⟨s, span_s⟩ := Module.finite_def.mp ‹Module.Finite R M›
  classical refine ⟨finsuppLinearMap_injective ..,
    fun x ↦ ⟨.onFinset (s.sup fun m ↦ (x m).support) (lapply · ∘ₗ x) fun i h ↦ ?_, ?_⟩⟩
  · contrapose! h; exact LinearMap.ext_on span_s (by simpa using! h)
  · ext; rfl
/-
**LinearMap.finsuppLinearMap_bijective_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap`。
形式化陈述：finsuppLinearMap_bijective_of_finite [Finite ι] : Function.Bijective (fins
uppLinearMap S : (ι ->₀ M ->ₗ[R] N) -> M ->ₗ[R] ι ->₀ N) where left
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.finsuppLinearMap_injective`：finsuppLinearMap_injective : Funct
ion.Injective (finsuppLinearMap S : (ι ->₀ M ->ₗ[R] N) -> M ->ₗ[R] ι ->₀ N)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.finsuppLinearMap_apply_apply_apply`：∀ {R : Type u_1} {M : Type
 u_2} {N : Type u_3} {ι : Type u_4} (S : Type u_5) [inst : Semiring R]   [inst_1
 : AddCommMonoid M] [inst_2 : AddC…
· 使用定理 `Finsupp.equivFunOnFinite_symm_apply_apply`：∀ {α : Type u_1} {M : Type u_
4} [inst : Zero M] [inst_1 : Finite α] (f : α → M) (a : α),   (Finsupp.equivFunO
nFinite.symm f) a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsuppLinearMap_bijective_of_finite [Finite ι] :
    Function.Bijective (finsuppLinearMap S : (ι →₀ M →ₗ[R] N) → M →ₗ[R] ι →₀ N) where
  left := finsuppLinearMap_injective ..
  right x := ⟨equivFunOnFinite.symm fun i ↦ lapply i ∘ₗ x, by ext; simp⟩

end LinearMap

namespace Submodule

variable {R M N P : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P]

open Set

/-- If 0 → M' → M → M'' → 0 is exact and M' and M'' are
finitely generated then so is M. -/
/-
**Submodule.fg_of_fg_map_of_fg_inf_ker** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_of_fg_map_of_fg_inf_ker (f : M ->ₗ[R] P) {s : Submodule R M} (hs1 : (s.
map f).FG) (hs2 : (s ⊓ LinearMap.ker f).FG) : s.FG
参数：f : M ->ₗ[R] P；hs1 : (s.map f).FG；hs2 : (s ⊓ LinearMap.ker f).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Submodule.span_union`：span_union (s t : Set M) : span R (s union t) = sp
an R s ⊔ span R t
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Finsupp.mem_span_image_iff_linearCombination`：mem_span_image_iff_linearC
ombination {s : Set α} {x : M} : x in span R (v '' s) ↔ exists l in supported R 
R s, linearCombination R v l = x
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Finsupp.lmapDomain_supported`：lmapDomain_supported (f : α -> α') (s : Se
t α) : (supported M R s).map (lmapDomain M R f) = supported M R (f '' s)
· 使用定理 `Submodule.mem_inf`：mem_inf {p q : Submodule R M} {x : M} : x in p ⊓ q ↔ 
x in p ∧ x in q
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.lmapDomain_apply`：lmapDomain_apply (f : α -> α') (l : α ->₀ M) :
 (lmapDomain M R f : (α ->₀ M) ->ₗ[R] α' ->₀ M) l = mapDomain f l
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
If 0 → M' → M → M'' → 0 is exact and M' and M'' are
finitely generated then so is M.
-/
theorem fg_of_fg_map_of_fg_inf_ker (f : M →ₗ[R] P) {s : Submodule R M}
    (hs1 : (s.map f).FG)
    (hs2 : (s ⊓ LinearMap.ker f).FG) : s.FG := by
  have := Classical.decEq R
  have := Classical.decEq M
  have := Classical.decEq P
  obtain ⟨t1, ht1⟩ := hs1
  obtain ⟨t2, ht2⟩ := hs2
  have : ∀ y ∈ t1, ∃ x ∈ s, f x = y := by
    intro y hy
    have : y ∈ s.map f := by
      rw [← ht1]
      exact subset_span hy
    rcases mem_map.1 this with ⟨x, hx1, hx2⟩
    exact ⟨x, hx1, hx2⟩
  have : ∃ g : P → M, ∀ y ∈ t1, g y ∈ s ∧ f (g y) = y := by
    choose g hg1 hg2 using this
    exists fun y => if H : y ∈ t1 then g y H else 0
    intro y H
    constructor
    · simp only [dif_pos H]
      apply hg1
    · simp only [dif_pos H]
      apply hg2
  obtain ⟨g, hg⟩ := this
  clear this
  exists t1.image g ∪ t2
  rw [Finset.coe_union, span_union, Finset.coe_image]
  apply le_antisymm
  · refine sup_le (span_le.2 <| image_subset_iff.2 ?_) (span_le.2 ?_)
    · intro y hy
      exact (hg y hy).1
    · intro x hx
      have : x ∈ span R t2 := subset_span hx
      rw [ht2] at this
      exact this.1
  intro x hx
  have : f x ∈ s.map f := by
    rw [mem_map]
    exact ⟨x, hx, rfl⟩
  rw [← ht1, ← Set.image_id (t1 : Set P), Finsupp.mem_span_image_iff_linearCombination] at this
  rcases this with ⟨l, hl1, hl2⟩
  refine
    mem_sup.2
      ⟨(linearCombination R id).toFun ((lmapDomain R R g : (P →₀ R) → M →₀ R) l), ?_,
        x - linearCombination R id ((lmapDomain R R g : (P →₀ R) → M →₀ R) l), ?_,
        add_sub_cancel _ _⟩
  · rw [← Set.image_id (g '' ↑t1), Finsupp.mem_span_image_iff_linearCombination]
    refine ⟨_, ?_, rfl⟩
    have : Inhabited P := ⟨0⟩
    rw [← Finsupp.lmapDomain_supported _ _ g, mem_map]
    refine ⟨l, hl1, ?_⟩
    rfl
  rw [ht2, mem_inf]
  constructor
  · apply s.sub_mem hx
    rw [Finsupp.linearCombination_apply, Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index]
    · refine s.sum_mem ?_
      intro y hy
      exact s.smul_mem _ (hg y (hl1 hy)).1
    · exact zero_smul _
    · exact fun _ _ _ => add_smul _ _ _
  · rw [LinearMap.mem_ker, f.map_sub, ← hl2]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.lmapDomain_apply]
    rw [Finsupp.sum_mapDomain_index, Finsupp.sum, Finsupp.sum, map_sum]
    · rw [sub_eq_zero]
      refine Finset.sum_congr rfl fun y hy => ?_
      unfold id
      rw [f.map_smul, (hg y (hl1 hy)).2]
    · exact zero_smul _
    · exact fun _ _ _ => add_smul _ _ _

/-- The kernel of the composition of two linear maps is finitely generated if both kernels are and
the first morphism is surjective. -/
/-
**Submodule.fg_ker_comp** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_ker_comp (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (hf1 : (LinearMap.ker f).FG)
 (hf2 : (LinearMap.ker g).FG) (hsur : Function.Surjective f) : (LinearMap.ker (g
.comp f)).FG
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] P；hf1 : (LinearMap.ker f).FG；hf2 : (LinearMap.ker
 g).FG；hsur : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `Submodule.fg_of_fg_map_of_fg_inf_ker`：fg_of_fg_map_of_fg_inf_ker (f : M 
->ₗ[R] P) {s : Submodule R M} (hs1 : (s.map f).FG) (hs2 : (s ⊓ LinearMap.ker f).
FG) : s.FG
· 使用定理 `Submodule.map_comap_eq`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} 
{M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `Submodule.comap_mono`：comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule 
R₂ M₂} : q <= q' -> comap f q <= comap f q'
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a

--- 原说明 ---
The kernel of the composition of two linear maps is finitely generated if both k
ernels are and
the first morphism is surjective.
-/
theorem fg_ker_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf1 : (LinearMap.ker f).FG) (hf2 : (LinearMap.ker g).FG)
    (hsur : Function.Surjective f) : (LinearMap.ker (g.comp f)).FG := by
  rw [LinearMap.ker_comp]
  apply fg_of_fg_map_of_fg_inf_ker f
  · rwa [Submodule.map_comap_eq, LinearMap.range_eq_top.2 hsur, top_inf_eq]
  · rwa [inf_of_le_right (show (LinearMap.ker f) ≤
      (LinearMap.ker g).comap f from comap_mono bot_le)]

/-- If $M → N → P → 0$ is exact and $M$ and $P$ are finitely generated then so is $N$.

This is the `Module.Finite` version of `Submodule.fg_of_fg_map_of_fg_inf_ker`. -/
@[stacks 0519 "(1)"]
/-
**Submodule._root_.Module.Finite.of_exact** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If $M → N → P → 0$ is exact and $M$ and $P$ are finitely generated then so is $N
$.

This is the `Module.Finite` version of `Submodule.fg_of_fg_map_of_fg_inf_ker`.
-/
lemma _root_.Module.Finite.of_exact {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h_exact : Function.Exact f g) (h_surj : Function.Surjective g)
    [Module.Finite R M] [Module.Finite R P] : Module.Finite R N := by
  refine ⟨(⊤ : Submodule R _).fg_of_fg_map_of_fg_inf_ker g ?_ ?_⟩
  · rw [← LinearMap.range_eq_top] at h_surj
    rw [Submodule.map_top, h_surj]
    exact Module.Finite.fg_top
  · simp [LinearMap.exact_iff.1 h_exact]
/-
**Submodule._root_.Module.Finite.of_submodule_quotient** 是 Mathlib 中的一个定理，位于命名空间
 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Module.Finite.of_submodule_quotient (N : Submodule R M) [Module.Finite R N]
    [Module.Finite R (M ⧸ N)] : Module.Finite R M :=
  .of_exact (LinearMap.exact_subtype_mkQ N) (Quotient.mk_surjective _)

end Submodule

section

variable {R V} [Semiring R] [AddCommMonoid V] [Module R V]

/-
**Module.Finite.finsupp** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.Finite.finsupp {ι : Type*} [_root_.Finite ι] [Module.Finite R V] : 
Module.Finite R (ι ->₀ V)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
-/
instance Module.Finite.finsupp {ι : Type*} [_root_.Finite ι] [Module.Finite R V] :
    Module.Finite R (ι →₀ V) :=
  Module.Finite.equiv (Finsupp.linearEquivFunOnFinite R V ι).symm

end

namespace AddMonoidAlgebra
variable {M R S : Type*} [Finite M] [Semiring R] [Semiring S] [Module R S] [Module.Finite R S]

/-
**AddMonoidAlgebra.moduleFinite** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：moduleFinite : Module.Finite R S[M]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
-/
instance moduleFinite : Module.Finite R S[M] := .equiv <| .symm <| coeffLinearEquiv _

end AddMonoidAlgebra

namespace MonoidAlgebra
variable {M R S : Type*} [Finite M] [Semiring R] [Semiring S] [Module R S] [Module.Finite R S]

/-
**MonoidAlgebra.moduleFinite** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
形式化陈述：moduleFinite : Module.Finite R S[M]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
-/
instance moduleFinite : Module.Finite R S[M] := .equiv <| .symm <| coeffLinearEquiv _

end MonoidAlgebra

namespace FreeAbelianGroup
variable {σ : Type*} [Finite σ]

/-
**FreeAbelianGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeAbelianGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Finite ℤ (FreeAbelianGroup σ) :=
  .of_surjective _ (FreeAbelianGroup.equivFinsupp σ).toIntLinearEquiv.symm.surjective
/-
**FreeAbelianGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeAbelianGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMonoid.FG (FreeAbelianGroup σ) := by
  rw [← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]; infer_instance

end FreeAbelianGroup

