/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Defs
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Basic properties of tangent cones and sets with unique differentiability property

In this file we prove basic lemmas about `tangentConeAt`, `UniqueDiffWithinAt`,
and `UniqueDiffOn`.
-/

public section

open Filter Set Metric
open scoped Topology Pointwise

variable {𝕜 E : Type*}

section SMul

variable [AddCommGroup E] [SMul 𝕜 E] [TopologicalSpace E] {s t : Set E} {x : E}

@[gcongr]
/-
**tangentConeAt_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentConeAt_mono (h : s subseteq t) : tangentConeAt 𝕜 s x subseteq tange
ntConeAt 𝕜 t x
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tangentConeAt_def`：∀ (R : Type u_1) {E : Type u_2} [inst : AddCommGroup 
E] [inst_1 : SMul R E] [inst_2 : TopologicalSpace E] (s : Set E)   (x : E), tang
entCone…
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `smul_le_smul_left`：smul_le_smul_left [SMul M α] [Preorder α] [CovariantC
lass M α HSMul.hSMul LE.le] (m : M) {a b : α} (h : a <= b) : m • a <= m • b
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem tangentConeAt_mono (h : s ⊆ t) : tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜 t x := by
  simp only [tangentConeAt_def, ofPred_subset_ofPred]
  refine fun y hy ↦ hy.mono ?_
  gcongr

/--
Given `x ∈ s` and a semiring extension `𝕜 ⊆ 𝕜'`, the tangent cone of `s` at `x` with
respect to `𝕜` is contained in the tangent cone of `s` at `x` with respect to `𝕜'`.
-/
/-
**tangentConeAt_mono_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentConeAt_mono_field {𝕜' : Type*} [Monoid 𝕜'] [SMul 𝕜 𝕜'] [MulAction 𝕜
' E] [IsScalarTower 𝕜 𝕜' E] : tangentConeAt 𝕜 s x subseteq tangentConeAt 𝕜' s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tangentConeAt_def`：∀ (R : Type u_1) {E : Type u_2} [inst : AddCommGroup 
E] [inst_1 : SMul R E] [inst_2 : TopologicalSpace E] (s : Set E)   (x : E), tang
entCone…
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Filter.smul_le_smul`：smul_le_smul : f₁ <= f₂ -> g₁ <= g₂ -> f₁ • g₁ <= f
₂ • g₂
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Given `x ∈ s` and a semiring extension `𝕜 ⊆ 𝕜'`, the tangent cone of `s` at `x` 
with
respect to `𝕜` is contained in the tangent cone of `s` at `x` with respect to `𝕜
'`.
-/
theorem tangentConeAt_mono_field
    {𝕜' : Type*} [Monoid 𝕜'] [SMul 𝕜 𝕜'] [MulAction 𝕜' E] [IsScalarTower 𝕜 𝕜' E] :
    tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜' s x := by
  simp only [tangentConeAt_def, ofPred_subset_ofPred]
  refine fun y hy ↦ hy.mono ?_
  rw [← smul_one_smul (Filter 𝕜')]
  grw [le_top (a := ⊤ • 1)]
/-
**Filter.HasBasis.tangentConeAt_eq_biInter_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.tangentConeAt_eq_biInter_closure {ι} {p : ι -> Prop} {U : 
ι -> Set E} (h : (𝓝 0).HasBasis p U) : tangentConeAt 𝕜 s x = ⋂ (i) (_ : p i), cl
osure ((univ : Set 𝕜) • (U i inter (x + ·) ⁻¹' s))
参数：h : (𝓝 0).HasBasis p U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tangentConeAt_def`：∀ (R : Type u_1) {E : Type u_2} [inst : AddCommGroup 
E] [inst_1 : SMul R E] [inst_2 : TopologicalSpace E] (s : Set E)   (x : E), tang
entCone…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.HasBasis.clusterPt_iff_forall_mem_closure`：∀ {X : Type u} [inst :
 TopologicalSpace X] {x : X} {ι : Sort u_3} {p : ι → Prop} {s : ι → Set X} {F : 
Filter X},   F.HasBasis p s → (Cluster…
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.HasBasis.top_prod`：∀ {α : Type u_1} {β : Type u_2} {ι' : Sort u_5
} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β},   lb.HasBasis pb sb → (⊤ ×
ˢ lb).HasBasis…
· 使用定理 `nhdsWithin_hasBasis`：nhdsWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s 
: ι -> Set α} {a : α} (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p
 fun i =>…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Set.image_prod`：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = im
age2 f s t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Filter.HasBasis.tangentConeAt_eq_biInter_closure {ι} {p : ι → Prop} {U : ι → Set E}
    (h : (𝓝 0).HasBasis p U) :
    tangentConeAt 𝕜 s x = ⋂ (i) (_ : p i), closure ((univ : Set 𝕜) • (U i ∩ (x + ·) ⁻¹' s)) := by
  ext y
  simp only [tangentConeAt_def, mem_ofPred_eq, mem_iInter₂, ← map₂_smul, ← map_prod_eq_map₂,
    ((nhdsWithin_hasBasis h _).top_prod.map _).clusterPt_iff_forall_mem_closure, image_prod,
    image2_smul]
/-
**tangentConeAt_eq_biInter_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentConeAt_eq_biInter_closure : tangentConeAt 𝕜 s x = ⋂ U in 𝓝 0, closu
re ((univ : Set 𝕜) • (U inter (x + ·) ⁻¹' s))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.tangentConeAt_eq_biInter_closure`：Filter.HasBasis.tangen
tConeAt_eq_biInter_closure {ι} {p : ι -> Prop} {U : ι -> Set E} (h : (𝓝 0).HasBa
sis p U) : tangentConeAt 𝕜 s x = ⋂ (i)…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem tangentConeAt_eq_biInter_closure :
    tangentConeAt 𝕜 s x = ⋂ U ∈ 𝓝 0, closure ((univ : Set 𝕜) • (U ∩ (x + ·) ⁻¹' s)) :=
  (basis_sets _).tangentConeAt_eq_biInter_closure

variable [ContinuousAdd E]
/-
**tangentConeAt_mono_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentConeAt_mono_nhds (h : 𝓝[s] x <= 𝓝[t] x) : tangentConeAt 𝕜 s x subse
teq tangentConeAt 𝕜 t x
参数：h : 𝓝[s] x <= 𝓝[t] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tangentConeAt_def`：∀ (R : Type u_1) {E : Type u_2} [inst : AddCommGroup 
E] [inst_1 : SMul R E] [inst_2 : TopologicalSpace E] (s : Set E)   (x : E), tang
entCone…
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `smul_le_smul_left`：smul_le_smul_left [SMul M α] [Preorder α] [CovariantC
lass M α HSMul.hSMul LE.le] (m : M) {a b : α} (h : a <= b) : m • a <= m • b
· 使用定理 `nhdsWithin_le_iff`：nhdsWithin_le_iff {s t : Set α} {x : α} : 𝓝[s] x <= 𝓝
[t] x ↔ t in 𝓝[s] x
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `continuous_const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] (m : M),   Continuous fun x => m + x
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Set.MapsTo.tendsto`：Set.MapsTo.tendsto {s : Set α} {t : Set β} {f : α ->
 β} (h : MapsTo f s t) : Filter.Tendsto f (𝓟 s) (𝓟 t)
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
-/
theorem tangentConeAt_mono_nhds (h : 𝓝[s] x ≤ 𝓝[t] x) :
    tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜 t x := by
  simp only [tangentConeAt_def, ofPred_subset_ofPred]
  refine fun y hy ↦ hy.mono ?_
  gcongr _ • ?_
  rw [nhdsWithin_le_iff]
  suffices Tendsto (x + ·) (𝓝[(x + ·) ⁻¹' s] 0) (𝓝[s] x) from
    this.mono_right h |> tendsto_nhdsWithin_iff.mp |>.2
  refine .inf ?_ (mapsTo_preimage _ _).tendsto
  exact (continuous_const_add x).tendsto' 0 x (add_zero _)

/-- Tangent cone of `s` at `x` depends only on `𝓝[s] x`. -/
/-
**tangentConeAt_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentConeAt_congr (h : 𝓝[s] x = 𝓝[t] x) : tangentConeAt 𝕜 s x = tangentC
oneAt 𝕜 t x
参数：h : 𝓝[s] x = 𝓝[t] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `tangentConeAt_mono_nhds`：tangentConeAt_mono_nhds (h : 𝓝[s] x <= 𝓝[t] x) 
: tangentConeAt 𝕜 s x subseteq tangentConeAt 𝕜 t x
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a

--- 原说明 ---
Tangent cone of `s` at `x` depends only on `𝓝[s] x`.
-/
theorem tangentConeAt_congr (h : 𝓝[s] x = 𝓝[t] x) : tangentConeAt 𝕜 s x = tangentConeAt 𝕜 t x :=
  Subset.antisymm (tangentConeAt_mono_nhds h.le) (tangentConeAt_mono_nhds h.ge)

/-- Intersecting with a neighborhood of the point does not change the tangent cone. -/
/-
**tangentConeAt_inter_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentConeAt_inter_nhds (ht : t in 𝓝 x) : tangentConeAt 𝕜 (s inter t) x =
 tangentConeAt 𝕜 s x
参数：ht : t in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tangentConeAt_congr`：tangentConeAt_congr (h : 𝓝[s] x = 𝓝[t] x) : tangent
ConeAt 𝕜 s x = tangentConeAt 𝕜 t x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_restrict'`：nhdsWithin_restrict' {a : α} (s : Set α) {t : Set 
α} (h : t in 𝓝 a) : 𝓝[s] a = 𝓝[s inter t] a

--- 原说明 ---
Intersecting with a neighborhood of the point does not change the tangent cone.
-/
theorem tangentConeAt_inter_nhds (ht : t ∈ 𝓝 x) : tangentConeAt 𝕜 (s ∩ t) x = tangentConeAt 𝕜 s x :=
  tangentConeAt_congr (nhdsWithin_restrict' _ ht).symm
/-
**mem_closure_of_nonempty_tangentConeAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_of_nonempty_tangentConeAt (h : (tangentConeAt 𝕜 s x).Nonempty)
 : x in closure s
参数：h : (tangentConeAt 𝕜 s x).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_fun_of_mem_tangentConeAt`：exists_fun_of_mem_tangentConeAt (h : y 
in tangentConeAt R s x) : exists (α : Type (max u v)) (l : Filter α) (_hl : l.Ne
Bot) (c : α -> R) (d …
· 使用定理 `mem_closure_of_tendsto`：mem_closure_of_tendsto {f : α -> X} {b : Filter 
α} [NeBot b] (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in clos
ure s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem mem_closure_of_nonempty_tangentConeAt (h : (tangentConeAt 𝕜 s x).Nonempty) :
    x ∈ closure s := by
  rcases h with ⟨y, hy⟩
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, -, d, hd, hds, -⟩
  refine mem_closure_of_tendsto ?_ hds
  simpa using tendsto_const_nhds.add hd

variable [ContinuousConstSMul 𝕜 E]

@[simp]
/-
**tangentConeAt_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentConeAt_closure : tangentConeAt 𝕜 (closure s) x = tangentConeAt 𝕜 s 
x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.tangentConeAt_eq_biInter_closure`：Filter.HasBasis.tangen
tConeAt_eq_biInter_closure {ι} {p : ι -> Prop} {U : ι -> Set E} (h : (𝓝 0).HasBa
sis p U) : tangentConeAt 𝕜 s x = ⋂ (i)…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `Set.iInter₂_mono`：iInter₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋂ (i) (j), s i j subseteq ⋂ (i) (j), t i j
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Set.smul_subset_smul`：smul_subset_smul : s₁ subseteq s₂ -> t₁ subseteq t
₂ -> s₁ • t₁ subseteq s₂ • t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `IsOpenMap.preimage_closure_subset_closure_preimage`：∀ {X : Type u_1} {Y 
: Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y
],   IsOpenMap f → ∀ {s : Set Y}, f ⁻¹' …
· 使用定理 `isOpenMap_add_left`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 :
 AddGroup G] [SeparatelyContinuousAdd G] (a : G),   IsOpenMap fun x => a + x
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsOpen.inter_closure`：IsOpen.inter_closure (h : IsOpen s) : s inter clos
ure t subseteq closure (s inter t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `set_smul_closure_subset`：set_smul_closure_subset (s : Set M) (t : Set α)
 : s • closure t subseteq closure (s • t)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `tangentConeAt_mono`：tangentConeAt_mono (h : s subseteq t) : tangentConeA
t 𝕜 s x subseteq tangentConeAt 𝕜 t x
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem tangentConeAt_closure : tangentConeAt 𝕜 (closure s) x = tangentConeAt 𝕜 s x := by
  refine Subset.antisymm ?_ (tangentConeAt_mono subset_closure)
  simp only [(nhds_basis_opens _).tangentConeAt_eq_biInter_closure]
  refine iInter₂_mono fun U hU ↦ closure_minimal ?_ isClosed_closure
  grw [(isOpenMap_add_left x).preimage_closure_subset_closure_preimage, hU.2.inter_closure,
    set_smul_closure_subset]

end SMul

section Module

variable [AddCommGroup E] [Semiring 𝕜] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E]
  {s t : Set E} {x : E}

omit [ContinuousAdd E] in
/-
**UniqueDiffWithinAt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffWithinAt.mono (h : UniqueDiffWithinAt 𝕜 s x) (st : s subseteq t)
 : UniqueDiffWithinAt 𝕜 t x
参数：h : UniqueDiffWithinAt 𝕜 s x；st : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniqueDiffWithinAt_iff`：∀ (R : Type u) {E : Type v} [inst : Semiring R] 
[inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   [inst_3 : TopologicalSp
ace E] (s : …
· 使用引理 `Mathlib.Tactic.GCongr.and_mono`：and_mono (h₁ : a -> c) (h₂ : a -> b -> d
) : (a ∧ b) -> c ∧ d
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `SetLike.coe_mono`：coe_mono : Monotone (SetLike.coe : A -> Set B)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `tangentConeAt_mono`：tangentConeAt_mono (h : s subseteq t) : tangentConeA
t 𝕜 s x subseteq tangentConeAt 𝕜 t x
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
theorem UniqueDiffWithinAt.mono (h : UniqueDiffWithinAt 𝕜 s x) (st : s ⊆ t) :
    UniqueDiffWithinAt 𝕜 t x := by
  rw [uniqueDiffWithinAt_iff] at *
  grw [← st]
  exact h

omit [ContinuousAdd E] in
/-
**UniqueDiffWithinAt.closure** 是 Mathlib 中的一个定理，位于命名空间 `UniqueDiffWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : AddCommGroup E] [inst_1 : Semiring
 𝕜] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : TopologicalSpace E] {s : Set E} {x 
: E}, UniqueDiffWithinAt 𝕜 s x → UniqueDiffWithinAt 𝕜 (closure s) x
参数：closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.mono`：UniqueDiffWithinAt.mono (h : UniqueDiffWithinAt
 𝕜 s x) (st : s subseteq t) : UniqueDiffWithinAt 𝕜 t x
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
protected theorem UniqueDiffWithinAt.closure (h : UniqueDiffWithinAt 𝕜 s x) :
    UniqueDiffWithinAt 𝕜 (closure s) x :=
  h.mono subset_closure
/-
**UniqueDiffWithinAt.mono_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffWithinAt.mono_nhds (h : UniqueDiffWithinAt 𝕜 s x) (st : 𝓝[s] x <
= 𝓝[t] x) : UniqueDiffWithinAt 𝕜 t x
参数：h : UniqueDiffWithinAt 𝕜 s x；st : 𝓝[s] x <= 𝓝[t] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `tangentConeAt_mono_nhds`：tangentConeAt_mono_nhds (h : 𝓝[s] x <= 𝓝[t] x) 
: tangentConeAt 𝕜 s x subseteq tangentConeAt 𝕜 t x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem UniqueDiffWithinAt.mono_nhds (h : UniqueDiffWithinAt 𝕜 s x) (st : 𝓝[s] x ≤ 𝓝[t] x) :
    UniqueDiffWithinAt 𝕜 t x := by
  simp only [uniqueDiffWithinAt_iff] at *
  rw [mem_closure_iff_nhdsWithin_neBot] at h ⊢
  exact ⟨h.1.mono <| Submodule.span_mono <| tangentConeAt_mono_nhds st, h.2.mono st⟩
/-
**uniqueDiffWithinAt_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueDiffWithinAt_congr (st : 𝓝[s] x = 𝓝[t] x) : UniqueDiffWithinAt 𝕜 s x
 ↔ UniqueDiffWithinAt 𝕜 t x
参数：st : 𝓝[s] x = 𝓝[t] x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.mono_nhds`：UniqueDiffWithinAt.mono_nhds (h : UniqueDi
ffWithinAt 𝕜 s x) (st : 𝓝[s] x <= 𝓝[t] x) : UniqueDiffWithinAt 𝕜 t x
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem uniqueDiffWithinAt_congr (st : 𝓝[s] x = 𝓝[t] x) :
    UniqueDiffWithinAt 𝕜 s x ↔ UniqueDiffWithinAt 𝕜 t x :=
  ⟨fun h => h.mono_nhds <| le_of_eq st, fun h => h.mono_nhds <| le_of_eq st.symm⟩
/-
**uniqueDiffWithinAt_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueDiffWithinAt_inter (ht : t in 𝓝 x) : UniqueDiffWithinAt 𝕜 (s inter t
) x ↔ UniqueDiffWithinAt 𝕜 s x
参数：ht : t in 𝓝 x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniqueDiffWithinAt_congr`：uniqueDiffWithinAt_congr (st : 𝓝[s] x = 𝓝[t] x
) : UniqueDiffWithinAt 𝕜 s x ↔ UniqueDiffWithinAt 𝕜 t x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_restrict'`：nhdsWithin_restrict' {a : α} (s : Set α) {t : Set 
α} (h : t in 𝓝 a) : 𝓝[s] a = 𝓝[s inter t] a
-/
theorem uniqueDiffWithinAt_inter (ht : t ∈ 𝓝 x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x ↔ UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_congr <| (nhdsWithin_restrict' _ ht).symm
/-
**UniqueDiffWithinAt.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffWithinAt.inter (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t in 𝓝 x) :
 UniqueDiffWithinAt 𝕜 (s inter t) x
参数：hs : UniqueDiffWithinAt 𝕜 s x；ht : t in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `uniqueDiffWithinAt_inter`：uniqueDiffWithinAt_inter (ht : t in 𝓝 x) : Uni
queDiffWithinAt 𝕜 (s inter t) x ↔ UniqueDiffWithinAt 𝕜 s x
-/
theorem UniqueDiffWithinAt.inter (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t ∈ 𝓝 x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x :=
  (uniqueDiffWithinAt_inter ht).2 hs
/-
**UniqueDiffOn.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsOpen t) : UniqueDiffOn 
𝕜 (s inter t)
参数：hs : UniqueDiffOn 𝕜 s；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.inter`：UniqueDiffWithinAt.inter (hs : UniqueDiffWithi
nAt 𝕜 s x) (ht : t in 𝓝 x) : UniqueDiffWithinAt 𝕜 (s inter t) x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsOpen t) : UniqueDiffOn 𝕜 (s ∩ t) :=
  fun x hx => (hs x hx.1).inter (IsOpen.mem_nhds ht hx.2)
/-
**uniqueDiffWithinAt_inter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueDiffWithinAt_inter' (ht : t in 𝓝[s] x) : UniqueDiffWithinAt 𝕜 (s int
er t) x ↔ UniqueDiffWithinAt 𝕜 s x
参数：ht : t in 𝓝[s] x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniqueDiffWithinAt_congr`：uniqueDiffWithinAt_congr (st : 𝓝[s] x = 𝓝[t] x
) : UniqueDiffWithinAt 𝕜 s x ↔ UniqueDiffWithinAt 𝕜 t x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_restrict''`：nhdsWithin_restrict'' {a : α} (s : Set α) {t : Se
t α} (h : t in 𝓝[s] a) : 𝓝[s] a = 𝓝[s inter t] a
-/
theorem uniqueDiffWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x ↔ UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_congr <| (nhdsWithin_restrict'' _ ht).symm
/-
**UniqueDiffWithinAt.inter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffWithinAt.inter' (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t in 𝓝[s] 
x) : UniqueDiffWithinAt 𝕜 (s inter t) x
参数：hs : UniqueDiffWithinAt 𝕜 s x；ht : t in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `uniqueDiffWithinAt_inter'`：uniqueDiffWithinAt_inter' (ht : t in 𝓝[s] x) 
: UniqueDiffWithinAt 𝕜 (s inter t) x ↔ UniqueDiffWithinAt 𝕜 s x
-/
theorem UniqueDiffWithinAt.inter' (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t ∈ 𝓝[s] x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x :=
  (uniqueDiffWithinAt_inter' ht).2 hs

/-- The tangent cone at a non-isolated point contains `0`. -/
/-
**zero_mem_tangentConeAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_mem_tangentConeAt (hx : x in closure s) : 0 in tangentConeAt 𝕜 s x
参数：hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_tangentConeAt_of_frequently`：mem_tangentConeAt_of_frequently {α : Ty
pe*} (l : Filter α) (c : α -> R) (d : α -> E) (hd₀ : Tendsto d l (𝓝 0)) (hds : e
xistsᶠ n in l, x + d …
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.add_const`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_neg_cancel_comm_assoc`：∀ {G : Type u_1} [inst : AddCommGroup G] (a b
 : G), a + (b + -a) = b
· 使用定理 `mem_closure_iff_frequently`：mem_closure_iff_frequently : x in closure s 
↔ existsᶠ x in 𝓝 x, x in s
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
The tangent cone at a non-isolated point contains `0`.
-/
theorem zero_mem_tangentConeAt (hx : x ∈ closure s) :
    0 ∈ tangentConeAt 𝕜 s x := by
  rw [mem_closure_iff_frequently] at hx
  apply mem_tangentConeAt_of_frequently (𝓝 x) 1 (· + (-x))
  · exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  · simpa
  · simp only [Pi.one_apply, one_smul]
    exact Continuous.tendsto' (by fun_prop) _ _ (by simp)

@[deprecated (since := "2026-01-21")]
alias zero_mem_tangentCone := zero_mem_tangentConeAt

@[simp]
/-
**zero_mem_tangentConeAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_mem_tangentConeAt_iff : 0 in tangentConeAt 𝕜 s x ↔ x in closure s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_closure_of_nonempty_tangentConeAt`：mem_closure_of_nonempty_tangentCo
neAt (h : (tangentConeAt 𝕜 s x).Nonempty) : x in closure s
· 使用定理 `zero_mem_tangentConeAt`：zero_mem_tangentConeAt (hx : x in closure s) : 0
 in tangentConeAt 𝕜 s x
-/
theorem zero_mem_tangentConeAt_iff : 0 ∈ tangentConeAt 𝕜 s x ↔ x ∈ closure s :=
  ⟨fun h ↦ mem_closure_of_nonempty_tangentConeAt ⟨_, h⟩, zero_mem_tangentConeAt⟩

/-- If `x` is not an accumulation point of `s`, then the tangent cone of `s` at `x`
is a subset of `{0}`. -/
/-
**tangentConeAt_subset_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentConeAt_subset_zero [T2Space E] (hx : ¬AccPt x (𝓟 s)) : tangentConeA
t 𝕜 s x subseteq 0
参数：hx : ¬AccPt x (𝓟 s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_fun_of_mem_tangentConeAt`：exists_fun_of_mem_tangentConeAt (h : y 
in tangentConeAt R s x) : exists (α : Type (max u v)) (l : Filter α) (_hl : l.Ne
Bot) (c : α -> R) (d …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `tendsto_nhds_unique_of_eventuallyEq`：tendsto_nhds_unique_of_eventuallyEq
 [T2Space X] {f g : Y -> X} {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l
 (𝓝 a)) (hb : Tendsto g l…

--- 原说明 ---
If `x` is not an accumulation point of `s`, then the tangent cone of `s` at `x`
is a subset of `{0}`.
-/
theorem tangentConeAt_subset_zero [T2Space E] (hx : ¬AccPt x (𝓟 s)) : tangentConeAt 𝕜 s x ⊆ 0 := by
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  have H₁ : Tendsto (x + d ·) l (𝓝 x) := by
    simpa using tendsto_const_nhds.add hd₀
  have H₂ : ∀ᶠ n in l, d n = 0 := by
    simp only [accPt_iff_frequently, not_frequently, not_and', ne_eq, not_not] at hx
    simpa using hds.mp (H₁.eventually hx)
  have H₃ : ∀ᶠ n in l, c n • d n = 0 := H₂.mono fun n hn ↦ by simp [hn]
  simpa using tendsto_nhds_unique_of_eventuallyEq hcd tendsto_const_nhds H₃
/-
**AccPt.of_mem_tangentConeAt_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AccPt.of_mem_tangentConeAt_ne_zero [T2Space E] {y : E} (hy : y in tangentC
oneAt 𝕜 s x) (hy₀ : y != 0) : AccPt x (𝓟 s)
参数：hy : y in tangentConeAt 𝕜 s x；hy₀ : y != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `tangentConeAt_subset_zero`：tangentConeAt_subset_zero [T2Space E] (hx : ¬
AccPt x (𝓟 s)) : tangentConeAt 𝕜 s x subseteq 0
-/
theorem AccPt.of_mem_tangentConeAt_ne_zero [T2Space E] {y : E} (hy : y ∈ tangentConeAt 𝕜 s x)
    (hy₀ : y ≠ 0) : AccPt x (𝓟 s) := by
  contrapose hy₀
  exact tangentConeAt_subset_zero hy₀ hy
/-
**UniqueDiffWithinAt.accPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffWithinAt.accPt [T2Space E] [Nontrivial E] (h : UniqueDiffWithinA
t 𝕜 s x) : AccPt x (𝓟 s)
参数：h : UniqueDiffWithinAt 𝕜 s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `SetLike.coe_mono`：coe_mono : Monotone (SetLike.coe : A -> Set B)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `tangentConeAt_subset_zero`：tangentConeAt_subset_zero [T2Space E] (hx : ¬
AccPt x (𝓟 s)) : tangentConeAt 𝕜 s x subseteq 0
· 使用定理 `UniqueDiffWithinAt.dense_tangentConeAt`：∀ {R : Type u} {E : Type v} [ins
t : Semiring R] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   [inst_3
 : TopologicalSpace E] {s : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_zero`：span_zero : span R (0 : Set M) = ⊥
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
-/
theorem UniqueDiffWithinAt.accPt [T2Space E] [Nontrivial E] (h : UniqueDiffWithinAt 𝕜 s x) :
    AccPt x (𝓟 s) := by
  by_contra! h'
  have : Dense (Submodule.span 𝕜 (0 : Set E) : Set E) :=
    h.1.mono <| by gcongr; exact tangentConeAt_subset_zero h'
  simp [dense_iff_closure_eq] at this

end Module

section TVS

variable [DivisionSemiring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace 𝕜]
  [TopologicalSpace E] [ContinuousSMul 𝕜 E] {s : Set E} {x y : E}

/-
**mem_tangentConeAt_of_add_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_tangentConeAt_of_add_smul_mem {α : Type*} {l : Filter α} [l.NeBot] {c 
: α -> 𝕜} (hc₀ : Tendsto c l (𝓝[!=] 0)) (hmem : forallᶠ n in l, x + c n • y in s
) : y in tangentConeAt 𝕜 s x
参数：hc₀ : Tendsto c l (𝓝[!=] 0)；hmem : forallᶠ n in l, x + c n • y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_tangentConeAt_of_seq`：mem_tangentConeAt_of_seq {α : Type*} (l : Filt
er α) [l.NeBot] (c : α -> R) (d : α -> E) (hd₀ : Tendsto d l (𝓝 0)) (hds : foral
lᶠ n in l, x +…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `tendsto_nhds_of_eventually_eq`：tendsto_nhds_of_eventually_eq {l : Filter
 α} {f : α -> X} (h : forallᶠ x' in l, f x' = x) : Tendsto f l (𝓝 x)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mem_tangentConeAt_of_add_smul_mem {α : Type*} {l : Filter α} [l.NeBot] {c : α → 𝕜}
    (hc₀ : Tendsto c l (𝓝[≠] 0)) (hmem : ∀ᶠ n in l, x + c n • y ∈ s) :
    y ∈ tangentConeAt 𝕜 s x := by
  rw [tendsto_nhdsWithin_iff] at hc₀
  refine mem_tangentConeAt_of_seq l c⁻¹ (c · • y) ?_ hmem ?_
  · simpa using hc₀.1.smul (tendsto_const_nhds (x := y))
  · refine tendsto_nhds_of_eventually_eq <| hc₀.2.mono fun n hn ↦ ?_
    simp_all

variable [(𝓝[≠] (0 : 𝕜)).NeBot]

@[simp]
/-
**tangentConeAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentConeAt_univ : tangentConeAt 𝕜 univ x = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tangentConeAt_def`：∀ (R : Type u_1) {E : Type u_2} [inst : AddCommGroup 
E] [inst_1 : SMul R E] [inst_2 : TopologicalSpace E] (s : Set E)   (x : E), tang
entCone…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Filter.top_smul_nhds_zero`：Filter.top_smul_nhds_zero : (⊤ : Filter G₀) •
 𝓝 (0 : X) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tangentConeAt_univ : tangentConeAt 𝕜 univ x = univ := by
  simp [tangentConeAt]
/-
**tangentConeAt_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentConeAt_of_mem_nhds [ContinuousAdd E] (h : s in 𝓝 x) : tangentConeAt
 𝕜 s x = univ
参数：h : s in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `tangentConeAt_inter_nhds`：tangentConeAt_inter_nhds (ht : t in 𝓝 x) : tan
gentConeAt 𝕜 (s inter t) x = tangentConeAt 𝕜 s x
· 使用定理 `tangentConeAt_univ`：tangentConeAt_univ : tangentConeAt 𝕜 univ x = univ
-/
theorem tangentConeAt_of_mem_nhds [ContinuousAdd E] (h : s ∈ 𝓝 x) : tangentConeAt 𝕜 s x = univ := by
  rw [← s.univ_inter, tangentConeAt_inter_nhds h, tangentConeAt_univ]

end TVS

section UniqueDiff

/-!
### Properties of `UniqueDiffWithinAt` and `UniqueDiffOn`

This section is devoted to properties of the predicates `UniqueDiffWithinAt` and `UniqueDiffOn`. -/

section Semiring
variable [Semiring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {x y : E} {s t : Set E}

/-
**uniqueDiffOn_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueDiffOn_empty : UniqueDiffOn 𝕜 (∅ : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniqueDiffOn_empty : UniqueDiffOn 𝕜 (∅ : Set E) :=
  fun _ hx => hx.elim
/-
**UniqueDiffWithinAt.congr_pt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffWithinAt.congr_pt (h : UniqueDiffWithinAt 𝕜 s x) (hy : x = y) : 
UniqueDiffWithinAt 𝕜 s y
参数：h : UniqueDiffWithinAt 𝕜 s x；hy : x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem UniqueDiffWithinAt.congr_pt (h : UniqueDiffWithinAt 𝕜 s x) (hy : x = y) :
    UniqueDiffWithinAt 𝕜 s y := hy ▸ h

variable {𝕜' : Type*} [Semiring 𝕜'] [SMul 𝕜 𝕜'] [Module 𝕜' E] [IsScalarTower 𝕜 𝕜' E]

/--
Assume that `E` is a normed vector space over semirings `𝕜 ⊆ 𝕜'` and that `x ∈ s` is a point
of unique differentiability with respect to the set `s` and the smaller semiring `𝕜`,
then `x` is also a point of unique differentiability with respect to the set `s`
and the larger semiring `𝕜'`.
-/
/-
**UniqueDiffWithinAt.mono_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffWithinAt.mono_field (hs : UniqueDiffWithinAt 𝕜 s x) : UniqueDiff
WithinAt 𝕜' s x
参数：hs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `tangentConeAt_mono_field`：tangentConeAt_mono_field {𝕜' : Type*} [Monoid 
𝕜'] [SMul 𝕜 𝕜'] [MulAction 𝕜' E] [IsScalarTower 𝕜 𝕜' E] : tangentConeAt 𝕜 s x su
bseteq tangent…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Assume that `E` is a normed vector space over semirings `𝕜 ⊆ 𝕜'` and that `x ∈ s
` is a point
of unique differentiability with respect to the set `s` and the smaller semiring
 `𝕜`,
then `x` is also a point of unique differentiability with respect to the set `s`
and the larger semiring `𝕜'`.
-/
theorem UniqueDiffWithinAt.mono_field (hs : UniqueDiffWithinAt 𝕜 s x) :
    UniqueDiffWithinAt 𝕜' s x := by
  simp_all only [uniqueDiffWithinAt_iff, and_true]
  apply Dense.mono _ hs.1
  trans ↑(Submodule.span 𝕜 (tangentConeAt 𝕜' s x)) <;>
    simp [Submodule.span_mono tangentConeAt_mono_field]

/--
Assume that `E` is a normed vector space over semirings `𝕜 ⊆ 𝕜'`
and all points of `s` are points of unique differentiability
with respect to the smaller semiring `𝕜`,
then they are also points of unique differentiability with respect to the larger semiring `𝕜`.
-/
/-
**UniqueDiffOn.mono_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffOn.mono_field (hs : UniqueDiffOn 𝕜 s) : UniqueDiffOn 𝕜' s
参数：hs : UniqueDiffOn 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.mono_field`：UniqueDiffWithinAt.mono_field (hs : Uniqu
eDiffWithinAt 𝕜 s x) : UniqueDiffWithinAt 𝕜' s x

--- 原说明 ---
Assume that `E` is a normed vector space over semirings `𝕜 ⊆ 𝕜'`
and all points of `s` are points of unique differentiability
with respect to the smaller semiring `𝕜`,
then they are also points of unique differentiability with respect to the larger
 semiring `𝕜`.
-/
theorem UniqueDiffOn.mono_field (hs : UniqueDiffOn 𝕜 s) : UniqueDiffOn 𝕜' s :=
  fun x hx ↦ (hs x hx).mono_field

variable [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]

@[simp]
/-
**uniqueDiffWithinAt_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueDiffWithinAt_closure : UniqueDiffWithinAt 𝕜 (closure s) x ↔ UniqueDi
ffWithinAt 𝕜 s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tangentConeAt_closure`：tangentConeAt_closure : tangentConeAt 𝕜 (closure 
s) x = tangentConeAt 𝕜 s x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem uniqueDiffWithinAt_closure :
    UniqueDiffWithinAt 𝕜 (closure s) x ↔ UniqueDiffWithinAt 𝕜 s x := by
  simp [uniqueDiffWithinAt_iff]

protected alias ⟨UniqueDiffWithinAt.of_closure, _⟩ := uniqueDiffWithinAt_closure
/-
**UniqueDiffWithinAt.mono_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffWithinAt.mono_closure (h : UniqueDiffWithinAt 𝕜 s x) (st : s sub
seteq closure t) : UniqueDiffWithinAt 𝕜 t x
参数：h : UniqueDiffWithinAt 𝕜 s x；st : s subseteq closure t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.of_closure`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : S
emiring 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [inst_3 : To
pologicalSpace E] {…
· 使用定理 `UniqueDiffWithinAt.mono`：UniqueDiffWithinAt.mono (h : UniqueDiffWithinAt
 𝕜 s x) (st : s subseteq t) : UniqueDiffWithinAt 𝕜 t x
-/
theorem UniqueDiffWithinAt.mono_closure (h : UniqueDiffWithinAt 𝕜 s x) (st : s ⊆ closure t) :
    UniqueDiffWithinAt 𝕜 t x :=
  (h.mono st).of_closure

end Semiring

section DivisionSemiring

variable [DivisionSemiring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [TopologicalSpace 𝕜] [(𝓝[≠] (0 : 𝕜)).NeBot] [ContinuousSMul 𝕜 E]
  {x y : E} {s t : Set E}

@[simp]
/-
**uniqueDiffWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 univ x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniqueDiffWithinAt_iff`：∀ (R : Type u) {E : Type v} [inst : Semiring R] 
[inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   [inst_3 : TopologicalSp
ace E] (s : …
· 使用定理 `tangentConeAt_univ`：tangentConeAt_univ : tangentConeAt 𝕜 univ x = univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.span_univ`：span_univ : span R (univ : Set M) = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 univ x := by
  rw [uniqueDiffWithinAt_iff, tangentConeAt_univ]
  simp

@[simp]
/-
**uniqueDiffOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniqueDiffWithinAt_univ`：uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 
univ x
-/
theorem uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E) :=
  fun _ _ => uniqueDiffWithinAt_univ

variable [ContinuousAdd E]
/-
**uniqueDiffWithinAt_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueDiffWithinAt_of_mem_nhds (h : s in 𝓝 x) : UniqueDiffWithinAt 𝕜 s x
参数：h : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `UniqueDiffWithinAt.inter`：UniqueDiffWithinAt.inter (hs : UniqueDiffWithi
nAt 𝕜 s x) (ht : t in 𝓝 x) : UniqueDiffWithinAt 𝕜 (s inter t) x
· 使用定理 `uniqueDiffWithinAt_univ`：uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 
univ x
-/
theorem uniqueDiffWithinAt_of_mem_nhds (h : s ∈ 𝓝 x) : UniqueDiffWithinAt 𝕜 s x := by
  simpa only [univ_inter] using uniqueDiffWithinAt_univ.inter h
/-
**IsOpen.uniqueDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.uniqueDiffWithinAt (hs : IsOpen s) (xs : x in s) : UniqueDiffWithin
At 𝕜 s x
参数：hs : IsOpen s；xs : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniqueDiffWithinAt_of_mem_nhds`：uniqueDiffWithinAt_of_mem_nhds (h : s in
 𝓝 x) : UniqueDiffWithinAt 𝕜 s x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem IsOpen.uniqueDiffWithinAt (hs : IsOpen s) (xs : x ∈ s) : UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_of_mem_nhds (IsOpen.mem_nhds hs xs)
/-
**IsOpen.uniqueDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 𝕜 s
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.uniqueDiffWithinAt`：IsOpen.uniqueDiffWithinAt (hs : IsOpen s) (xs
 : x in s) : UniqueDiffWithinAt 𝕜 s x
-/
theorem IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 𝕜 s :=
  fun _ hx => IsOpen.uniqueDiffWithinAt hs hx

end DivisionSemiring

end UniqueDiff

