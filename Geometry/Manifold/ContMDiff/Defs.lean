/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Geometry.Manifold.LocalInvariantProperties

/-!
# `C^n` functions between manifolds

We define `Cⁿ` functions between manifolds, as functions which are `Cⁿ` in charts, and prove
basic properties of these notions. Here, `n` can be finite, or `∞`, or `ω`.

## Main definitions and statements

Let `M` and `M'` be two manifolds, with respect to models with corners `I` and `I'`. Let
`f : M → M'`.

* `ContMDiffWithinAt I I' n f s x` states that the function `f` is `Cⁿ` within the set `s`
  around the point `x`.
* `ContMDiffAt I I' n f x` states that the function `f` is `Cⁿ` around `x`.
* `ContMDiffOn I I' n f s` states that the function `f` is `Cⁿ` on the set `s`
* `ContMDiff I I' n f` states that the function `f` is `Cⁿ`.

We also give some basic properties of `Cⁿ` functions between manifolds, following the API of
`C^n` functions between vector spaces.
See `Basic.lean` for further basic properties of `Cⁿ` functions between manifolds,
`NormedSpace.lean` for the equivalence of manifold-smoothness to usual smoothness,
`Product.lean` for smoothness results related to the product of manifolds and
`Atlas.lean` for smoothness of atlas members and local structomorphisms.

## Implementation details

Many properties follow for free from the corresponding properties of functions in vector spaces,
as being `Cⁿ` is a local property invariant under the `Cⁿ` groupoid. We take advantage of the
general machinery developed in `LocalInvariantProperties.lean` to get these properties
automatically. For instance, the fact that being `Cⁿ` does not depend on the chart one considers
is given by `liftPropWithinAt_indep_chart`.

For this to work, the definition of `ContMDiffWithinAt` and friends has to
follow definitionally the setup of local invariant properties. Still, we recast the definition
in terms of extended charts in `contMDiffOn_iff` and `contMDiff_iff`.
-/

@[expose] public section


open Set Function Filter ChartedSpace IsManifold

open scoped Topology Manifold ContDiff

/-! ### Definition of `Cⁿ` functions between manifolds -/


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- Prerequisite typeclasses to say that `M` is a manifold over the pair `(E, H)`
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- Prerequisite typeclasses to say that `M'` is a manifold over the pair `(E', H')`
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- Prerequisite typeclasses to say that `M''` is a manifold over the pair `(E'', H'')`
  {E'' : Type*}
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  -- declare functions, sets, points and smoothness indices
  {e : OpenPartialHomeomorph M H} {e' : OpenPartialHomeomorph M' H'}
  {f f₁ : M → M'} {s s₁ t : Set M} {x x' : M} {y : M'} {m n : ℕ∞ω}

variable (I I') in
/-- Property in the model space of a model with corners of being `C^n` within a set at a point,
when read in the model vector space. This property will be lifted to manifolds to define `C^n`
functions between manifolds.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it can be a natural
number, `∞`, or `ω`, where `C^ω` corresponds to analytic functions.
-/
/-
**ContDiffWithinAtProp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContDiffWithinAtProp (n : Nat∞ω) (f : H -> H') (s : Set H) (x : H) : Prop
参数：n : Nat∞ω；f : H -> H'；s : Set H；x : H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Property in the model space of a model with corners of being `C^n` within a set 
at a point,
when read in the model vector space. This property will be lifted to manifolds t
o define `C^n`
functions between manifolds.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it
 can be a natural
number, `∞`, or `ω`, where `C^ω` corresponds to analytic functions.
-/
def ContDiffWithinAtProp (n : ℕ∞ω) (f : H → H') (s : Set H) (x : H) : Prop :=
  ContDiffWithinAt 𝕜 n (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x)
/-
**contDiffWithinAtProp_self_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAtProp_self_source {f : E -> H'} {s : Set E} {x : E} : ContD
iffWithinAtProp 𝓘(𝕜, E) I' n f s x ↔ ContDiffWithinAt 𝕜 n (I' ∘ f) s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contDiffWithinAtProp_self_source {f : E → H'} {s : Set E} {x : E} :
    ContDiffWithinAtProp 𝓘(𝕜, E) I' n f s x ↔ ContDiffWithinAt 𝕜 n (I' ∘ f) s x := by
  simp_rw [ContDiffWithinAtProp, modelWithCornersSelf_coe, range_id, inter_univ,
    modelWithCornersSelf_coe_symm, CompTriple.comp_eq, preimage_id_eq, id_eq]
/-
**contDiffWithinAtProp_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAtProp_self {f : E -> E'} {s : Set E} {x : E} : ContDiffWith
inAtProp 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x ↔ ContDiffWithinAt 𝕜 n f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffWithinAtProp_self_source`：contDiffWithinAtProp_self_source {f : 
E -> H'} {s : Set E} {x : E} : ContDiffWithinAtProp 𝓘(𝕜, E) I' n f s x ↔ ContDif
fWithinAt 𝕜 n (I' ∘ f)…
-/
theorem contDiffWithinAtProp_self {f : E → E'} {s : Set E} {x : E} :
    ContDiffWithinAtProp 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAtProp_self_source
/-
**contDiffWithinAtProp_self_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAtProp_self_target {f : H -> E'} {s : Set H} {x : H} : ContD
iffWithinAtProp I 𝓘(𝕜, E') n f s x ↔ ContDiffWithinAt 𝕜 n (f ∘ I.symm) (I.symm ⁻
¹' s inter range I) (I x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contDiffWithinAtProp_self_target {f : H → E'} {s : Set H} {x : H} :
    ContDiffWithinAtProp I 𝓘(𝕜, E') n f s x ↔
      ContDiffWithinAt 𝕜 n (f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x) :=
  Iff.rfl

/-- Being `Cⁿ` in the model space is a local property, invariant under `Cⁿ` maps. Therefore,
it lifts nicely to manifolds. -/
/-
**contDiffWithinAt_localInvariantProp_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_localInvariantProp_of_le (n m : Nat∞ω) (hmn : m <= n) : (
contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I') (ContDiffWithin
AtProp I I' m) where is_local {s x u f} u_open xu
参数：n m : Nat∞ω；hmn : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_right_comm`：inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ inter s₂ 
inter s₃ = s₁ inter s₃ inter s₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContDiffWithinAtProp.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `contDiffWithinAt_inter`：contDiffWithinAt_inter (h : t in 𝓝 x) : ContDiff
WithinAt 𝕜 n f (s inter t) x ↔ ContDiffWithinAt 𝕜 n f s x
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ModelWithCorners.continuous_symm`：continuous_symm : Continuous I.symm
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ContDiffOn.contDiffWithinAt`：ContDiffOn.contDiffWithinAt (h : ContDiffOn
 𝕜 n f s) (hx : x in s) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_groupoid_of_pregroupoid`：mem_groupoid_of_pregroupoid {PG : Pregroupo
id H} {e : OpenPartialHomeomorph H H} : e in PG.groupoid ↔ PG.property e e.sourc
e ∧ PG.property e…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContDiffWithinAt.mono_of_mem_nhdsWithin`：ContDiffWithinAt.mono_of_mem_nh
dsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : s in 𝓝[t] x) : Cont
DiffWithinAt 𝕜 n f t x
· 使用定理 `ContDiffWithinAt.comp_inter`：ContDiffWithinAt.comp_inter {s : Set E} {t 
: Set F} {g : F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x))
 (hf : ContDiffWi…
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `OpenPartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y
), Set.MapsTo (↑e)…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Being `Cⁿ` in the model space is a local property, invariant under `Cⁿ` maps. Th
erefore,
it lifts nicely to manifolds.
-/
theorem contDiffWithinAt_localInvariantProp_of_le (n m : ℕ∞ω) (hmn : m ≤ n) :
    (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
      (ContDiffWithinAtProp I I' m) where
  is_local {s x u f} u_open xu := by
    have : I.symm ⁻¹' (s ∩ u) ∩ range I = I.symm ⁻¹' s ∩ range I ∩ I.symm ⁻¹' u := by
      simp only [inter_right_comm, preimage_inter]
    rw [ContDiffWithinAtProp, ContDiffWithinAtProp, this]
    symm
    apply contDiffWithinAt_inter
    have : u ∈ 𝓝 (I.symm (I x)) := by
      rw [ModelWithCorners.left_inv]
      exact u_open.mem_nhds xu
    apply ContinuousAt.preimage_mem_nhds I.continuous_symm.continuousAt this
  right_invariance' {s x f e} he hx h := by
    rw [ContDiffWithinAtProp] at h ⊢
    have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)) := by simp only [hx, mfld_simps]
    rw [this] at h
    have : I (e x) ∈ I.symm ⁻¹' e.target ∩ range I := by simp only [hx, mfld_simps]
    have := (mem_groupoid_of_pregroupoid.2 he).2.contDiffWithinAt this
    convert! (h.comp_inter _ (this.of_le hmn)).mono_of_mem_nhdsWithin _ using 1
    · ext y; simp only [mfld_simps]
    refine mem_nhdsWithin.mpr
      ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, by
        simp_rw [mem_preimage, I.left_inv, e.mapsTo hx], ?_⟩
    mfld_set_tac
  congr_of_forall {s x f g} h hx hf := by
    apply hf.congr
    · intro y hy
      simp only [mfld_simps] at hy
      simp only [h, hy, mfld_simps]
    · simp only [hx, mfld_simps]
  left_invariance' {s x f e'} he' hs hx h := by
    rw [ContDiffWithinAtProp] at h ⊢
    have A : (I' ∘ f ∘ I.symm) (I x) ∈ I'.symm ⁻¹' e'.source ∩ range I' := by
      simp only [hx, mfld_simps]
    have := (mem_groupoid_of_pregroupoid.2 he').1.contDiffWithinAt A
    convert! (this.of_le hmn).comp _ h _
    · ext y; simp only [mfld_simps]
    · intro y hy; simp only [mfld_simps] at hy; simpa only [hy, mfld_simps] using hs hy.1

/-- Being `Cⁿ` in the model space is a local property, invariant under `C^n` maps. Therefore,
it lifts nicely to manifolds. -/
/-
**contDiffWithinAt_localInvariantProp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_localInvariantProp (n : Nat∞ω) : (contDiffGroupoid n I).L
ocalInvariantProp (contDiffGroupoid n I') (ContDiffWithinAtProp I I' n)
参数：n : Nat∞ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffWithinAt_localInvariantProp_of_le`：contDiffWithinAt_localInvaria
ntProp_of_le (n m : Nat∞ω) (hmn : m <= n) : (contDiffGroupoid n I).LocalInvarian
tProp (contDiffGroupoid n I') (…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
Being `Cⁿ` in the model space is a local property, invariant under `C^n` maps. T
herefore,
it lifts nicely to manifolds.
-/
theorem contDiffWithinAt_localInvariantProp (n : ℕ∞ω) :
    (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
      (ContDiffWithinAtProp I I' n) :=
  contDiffWithinAt_localInvariantProp_of_le n n le_rfl
/-
**contDiffWithinAtProp_mono_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAtProp_mono_of_mem_nhdsWithin (n : Nat∞ω) ⦃s x t⦄ ⦃f : H -> 
H'⦄ (hts : s in 𝓝[t] x) (h : ContDiffWithinAtProp I I' n f s x) : ContDiffWithin
AtProp I I' n f t x
参数：n : Nat∞ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.mono_of_mem_nhdsWithin`：ContDiffWithinAt.mono_of_mem_nh
dsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : s in 𝓝[t] x) : Cont
DiffWithinAt 𝕜 n f t x
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `ModelWithCorners.image_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `ModelWithCorners.symm_map_nhdsWithin_image`：symm_map_nhdsWithin_image {x
 : H} {s : Set H} : map I.symm (𝓝[I '' s] I x) = 𝓝[s] x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem contDiffWithinAtProp_mono_of_mem_nhdsWithin
    (n : ℕ∞ω) ⦃s x t⦄ ⦃f : H → H'⦄ (hts : s ∈ 𝓝[t] x)
    (h : ContDiffWithinAtProp I I' n f s x) : ContDiffWithinAtProp I I' n f t x := by
  refine h.mono_of_mem_nhdsWithin ?_
  refine inter_mem ?_ (mem_of_superset self_mem_nhdsWithin inter_subset_right)
  rwa [← Filter.mem_map, ← I.image_eq, I.symm_map_nhdsWithin_image]
/-
**contDiffWithinAtProp_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAtProp_id (x : H) : ContDiffWithinAtProp I I n id univ x
参数：x : H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `ContDiffWithinAt.congr`：ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n
 f s x) (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 
n f₁ s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
-/
theorem contDiffWithinAtProp_id (x : H) : ContDiffWithinAtProp I I n id univ x := by
  simp only [ContDiffWithinAtProp, id_comp, preimage_univ, univ_inter]
  have : ContDiffWithinAt 𝕜 n id (range I) (I x) := contDiff_id.contDiffAt.contDiffWithinAt
  refine this.congr (fun y hy => ?_) ?_
  · simp only [ModelWithCorners.right_inv I hy, mfld_simps]
  · simp only [mfld_simps]

variable (I I') in
/-- `ContMDiffWithinAt I I' n f x` indicates that the function `f : M → M'` between manifolds
is `n` times continuously differentiable at `x : M` within the set `s`.

`f` is `n` times continuously differentiable within `s` at `x` if it is continuous and it is `n`
times continuously differentiable in this set around `x`, when read in the preferred chart at `x`.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it can be a natural
number, `∞`, or `ω`, where `C^ω` corresponds to analytic functions. -/
/-
**ContMDiffWithinAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt (n : Nat∞ω) (f : M -> M') (s : Set M) (x : M)
参数：n : Nat∞ω；f : M -> M'；s : Set M；x : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContMDiffWithinAt I I' n f x` indicates that the function `f : M → M'` between 
manifolds
is `n` times continuously differentiable at `x : M` within the set `s`.

`f` is `n` times continuously differentiable within `s` at `x` if it is continuo
us and it is `n`
times continuously differentiable in this set around `x`, when read in the prefe
rred chart at `x`.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it
 can be a natural
number, `∞`, or `ω`, where `C^ω` corresponds to analytic functions.
-/
def ContMDiffWithinAt (n : ℕ∞ω) (f : M → M') (s : Set M) (x : M) :=
  LiftPropWithinAt (ContDiffWithinAtProp I I' n) f s x

variable (I I') in
/-- `ContMDiffAt I I' n f x` indicates that the function `f : M → M'` between manifolds
is `n` times continuously differentiable at `x : M`.

`f` is `n` times continuously differentiable at `x` if it is continuous and it is `n` times
continuously differentiable around `x`, when read in the preferred chart at `x`.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it can be a natural
number, `∞`, or `ω`, where `C^ω` corresponds to analytic functions. -/
/-
**ContMDiffAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContMDiffAt (n : Nat∞ω) (f : M -> M') (x : M)
参数：n : Nat∞ω；f : M -> M'；x : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContMDiffAt I I' n f x` indicates that the function `f : M → M'` between manifo
lds
is `n` times continuously differentiable at `x : M`.

`f` is `n` times continuously differentiable at `x` if it is continuous and it i
s `n` times
continuously differentiable around `x`, when read in the preferred chart at `x`.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it
 can be a natural
number, `∞`, or `ω`, where `C^ω` corresponds to analytic functions.
-/
def ContMDiffAt (n : ℕ∞ω) (f : M → M') (x : M) :=
  ContMDiffWithinAt I I' n f univ x
/-
**contMDiffAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_iff {n : Nat∞ω} {f : M -> M'} {x : M} : ContMDiffAt I I' n f x
 ↔ ContinuousAt f x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartA
t I x).symm) (range I) (extChartAt I x x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ChartedSpace.liftPropAt_iff`：liftPropAt_iff {P : (H -> H') -> Set H -> H
 -> Prop} {f : M -> M'} {x : M} : LiftPropAt P f x ↔ ContinuousAt f x ∧ P (chart
At H' (f x) ∘ f ∘…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffWithinAtProp.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contMDiffAt_iff {n : ℕ∞ω} {f : M → M'} {x : M} :
    ContMDiffAt I I' n f x ↔
      ContinuousAt f x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x x) :=
  liftPropAt_iff.trans <| by rw [ContDiffWithinAtProp, preimage_univ, univ_inter]; rfl

variable (I I') in
/-- `ContMDiffOn I I' n f s` indicates that the function `f : M → M'` between manifolds
is `n` times continuously differentiable in a set `s : Set M`.

`f` is `n` times continuously differentiable on `s` if it is continuous on `s` and,
for any pair of points, it is `n` times continuously differentiable `s` in the charts
around these points.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it can be a natural
number, `∞`, or `ω`, where `C^ω` corresponds to analytic functions. -/
/-
**ContMDiffOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContMDiffOn (n : Nat∞ω) (f : M -> M') (s : Set M)
参数：n : Nat∞ω；f : M -> M'；s : Set M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContMDiffOn I I' n f s` indicates that the function `f : M → M'` between manifo
lds
is `n` times continuously differentiable in a set `s : Set M`.

`f` is `n` times continuously differentiable on `s` if it is continuous on `s` a
nd,
for any pair of points, it is `n` times continuously differentiable `s` in the c
harts
around these points.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it
 can be a natural
number, `∞`, or `ω`, where `C^ω` corresponds to analytic functions.
-/
def ContMDiffOn (n : ℕ∞ω) (f : M → M') (s : Set M) :=
  ∀ x ∈ s, ContMDiffWithinAt I I' n f s x

variable (I I') in
/-- `ContMDiff I I' n f` indicates that the function `f : M → M'` between manifolds
is `n` times continuously differentiable.

`f` is `n` times continuously differentiable if it is continuous and, for any pair of points,
it is `n` times continuously differentiable in the charts around these points.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it can be a natural
number, `∞`, or `ω`, where `C^ω` corresponds to analytic functions. -/
/-
**ContMDiff** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContMDiff (n : Nat∞ω) (f : M -> M')
参数：n : Nat∞ω；f : M -> M'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContMDiff I I' n f` indicates that the function `f : M → M'` between manifolds
is `n` times continuously differentiable.

`f` is `n` times continuously differentiable if it is continuous and, for any pa
ir of points,
it is `n` times continuously differentiable in the charts around these points.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it
 can be a natural
number, `∞`, or `ω`, where `C^ω` corresponds to analytic functions.
-/
def ContMDiff (n : ℕ∞ω) (f : M → M') :=
  ∀ x, ContMDiffAt I I' n f x

/-! ### Deducing smoothness from higher smoothness -/

/-
**ContMDiffWithinAt.of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.of_le (hf : ContMDiffWithinAt I I' n f s x) (le : m <= n
) : ContMDiffWithinAt I I' m f s x
参数：hf : ContMDiffWithinAt I I' n f s x；le : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用定理 `ChartedSpace.LiftPropWithinAt.prop`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…

--- 原说明 ---
### Deducing smoothness from higher smoothness
-/
theorem ContMDiffWithinAt.of_le (hf : ContMDiffWithinAt I I' n f s x) (le : m ≤ n) :
    ContMDiffWithinAt I I' m f s x := by
  simp only [ContMDiffWithinAt] at hf ⊢
  exact ⟨hf.1, hf.2.of_le (mod_cast le)⟩
/-
**ContMDiffAt.of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.of_le (hf : ContMDiffAt I I' n f x) (le : m <= n) : ContMDiffA
t I I' m f x
参数：hf : ContMDiffAt I I' n f x；le : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.of_le`：ContMDiffWithinAt.of_le (hf : ContMDiffWithinAt
 I I' n f s x) (le : m <= n) : ContMDiffWithinAt I I' m f s x
-/
theorem ContMDiffAt.of_le (hf : ContMDiffAt I I' n f x) (le : m ≤ n) : ContMDiffAt I I' m f x :=
  ContMDiffWithinAt.of_le hf le
/-
**ContMDiffOn.of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.of_le (hf : ContMDiffOn I I' n f s) (le : m <= n) : ContMDiffO
n I I' m f s
参数：hf : ContMDiffOn I I' n f s；le : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.of_le`：ContMDiffWithinAt.of_le (hf : ContMDiffWithinAt
 I I' n f s x) (le : m <= n) : ContMDiffWithinAt I I' m f s x
-/
theorem ContMDiffOn.of_le (hf : ContMDiffOn I I' n f s) (le : m ≤ n) : ContMDiffOn I I' m f s :=
  fun x hx => (hf x hx).of_le le
/-
**ContMDiff.of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m <= n) : ContMDiff I I' m
 f
参数：hf : ContMDiff I I' n f；le : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.of_le`：ContMDiffAt.of_le (hf : ContMDiffAt I I' n f x) (le :
 m <= n) : ContMDiffAt I I' m f x
-/
theorem ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m ≤ n) : ContMDiff I I' m f := fun x =>
  (hf x).of_le le

/-! ### Basic properties of `C^n` functions between manifolds -/

/-
**ContMDiff.contMDiffAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : ContMDiffAt I I' n f x
参数：h : ContMDiff I I' n f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Basic properties of `C^n` functions between manifolds
-/
theorem ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : ContMDiffAt I I' n f x :=
  h x
/-
**contMDiffWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_univ : ContMDiffWithinAt I I' n f univ x ↔ ContMDiffAt I
 I' n f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contMDiffWithinAt_univ : ContMDiffWithinAt I I' n f univ x ↔ ContMDiffAt I I' n f x :=
  Iff.rfl

@[simp]
/-
**contMDiffOn_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_empty : ContMDiffOn I I' n f ∅
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem contMDiffOn_empty : ContMDiffOn I I' n f ∅ := fun _x hx ↦ hx.elim
/-
**contMDiffOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDiff I I' n f
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
theorem contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDiff I I' n f := by
  simp only [ContMDiffOn, ContMDiff, contMDiffWithinAt_univ, forall_prop_of_true, mem_univ]

/-- One can reformulate being `C^n` within a set at a point as continuity within this set at this
point, and being `C^n` in the corresponding extended chart. -/
/-
**contMDiffWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff : ContMDiffWithinAt I I' n f s x ↔ ContinuousWithinA
t f s x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
 ((extChartAt I x).symm ⁻¹' s inter range I) (extChartAt I x x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
One can reformulate being `C^n` within a set at a point as continuity within thi
s set at this
point, and being `C^n` in the corresponding extended chart.
-/
theorem contMDiffWithinAt_iff :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  simp_rw [ContMDiffWithinAt, liftPropWithinAt_iff']; rfl

/-- One can reformulate being `Cⁿ` within a set at a point as continuity within this set at this
point, and being `Cⁿ` in the corresponding extended chart. This form states regularity of `f`
written in such a way that the set is restricted to lie within the domain/codomain of the
corresponding charts.
Even though this expression is more complicated than the one in `contMDiffWithinAt_iff`, it is
a smaller set, but their germs at `extChartAt I x x` are equal. It is sometimes useful to rewrite
using this in the goal.
-/
/-
**contMDiffWithinAt_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff' : ContMDiffWithinAt I I' n f s x ↔ ContinuousWithin
At f s x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm
) ((extChartAt I x).target inter (extChartAt I x).symm ⁻¹' (s inter f ⁻¹' (extCh
artAt I' (f x)).source)) (extChartAt I x x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `contDiffWithinAt_congr_set`：contDiffWithinAt_congr_set {t : Set E} (hst 
: s =ᶠ[𝓝 x] t) : ContDiffWithinAt 𝕜 n f s x ↔ ContDiffWithinAt 𝕜 n f t x
· 使用定理 `ContinuousWithinAt.extChartAt_symm_preimage_inter_range_eventuallyEq`：Co
ntinuousWithinAt.extChartAt_symm_preimage_inter_range_eventuallyEq {f : M -> M'}
 {x : M} (hc : ContinuousWithinAt f s x) : ((extChartAt I …

--- 原说明 ---
One can reformulate being `Cⁿ` within a set at a point as continuity within this
 set at this
point, and being `Cⁿ` in the corresponding extended chart. This form states regu
larity of `f`
written in such a way that the set is restricted to lie within the domain/codoma
in of the
corresponding charts.
Even though this expression is more complicated than the one in `contMDiffWithin
At_iff`, it is
a smaller set, but their germs at `extChartAt I x x` are equal. It is sometimes 
useful to rewrite
using this in the goal.
-/
theorem contMDiffWithinAt_iff' :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target ∩
            (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' (f x)).source))
          (extChartAt I x x) := by
  simp only [ContMDiffWithinAt, liftPropWithinAt_iff']
  exact and_congr_right fun hc => contDiffWithinAt_congr_set <|
    hc.extChartAt_symm_preimage_inter_range_eventuallyEq

/-- One can reformulate being `Cⁿ` within a set at a point as continuity within this set at this
point, and being `Cⁿ` in the corresponding extended chart in the target. -/
/-
**contMDiffWithinAt_iff_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff_target : ContMDiffWithinAt I I' n f s x ↔ Continuous
WithinAt f s x ∧ ContMDiffWithinAt I 𝓘(𝕜, E') n (extChartAt I' (f x) ∘ f) s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `continuousAt_extChartAt`：continuousAt_extChartAt (x : M) : ContinuousAt 
(extChartAt I x) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OpenPartialHomeomorph.refl_apply`：∀ (X : Type u_7) [inst : TopologicalSp
ace X], ↑(OpenPartialHomeomorph.refl X) = id
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
One can reformulate being `Cⁿ` within a set at a point as continuity within this
 set at this
point, and being `Cⁿ` in the corresponding extended chart in the target.
-/
theorem contMDiffWithinAt_iff_target :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧ ContMDiffWithinAt I 𝓘(𝕜, E') n (extChartAt I' (f x) ∘ f) s x := by
  simp_rw [ContMDiffWithinAt, liftPropWithinAt_iff', ← and_assoc]
  have cont :
    ContinuousWithinAt f s x ∧ ContinuousWithinAt (extChartAt I' (f x) ∘ f) s x ↔
        ContinuousWithinAt f s x :=
      and_iff_left_of_imp <| (continuousAt_extChartAt _).comp_continuousWithinAt
  simp_rw [cont, ContDiffWithinAtProp, extChartAt, OpenPartialHomeomorph.extend,
    PartialEquiv.coe_trans, ModelWithCorners.toPartialEquiv_coe,
    OpenPartialHomeomorph.coe_toPartialEquiv, modelWithCornersSelf_coe, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, id_comp]
  rfl
/-
**contMDiffAt_iff_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_iff_target {x : M} : ContMDiffAt I I' n f x ↔ ContinuousAt f x
 ∧ ContMDiffAt I 𝓘(𝕜, E') n (extChartAt I' (f x) ∘ f) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContMDiffAt.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `contMDiffWithinAt_iff_target`：contMDiffWithinAt_iff_target : ContMDiffWi
thinAt I I' n f s x ↔ ContinuousWithinAt f s x ∧ ContMDiffWithinAt I 𝓘(𝕜, E') n 
(extChartAt I' (f …
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contMDiffAt_iff_target {x : M} :
    ContMDiffAt I I' n f x ↔
      ContinuousAt f x ∧ ContMDiffAt I 𝓘(𝕜, E') n (extChartAt I' (f x) ∘ f) x := by
  rw [ContMDiffAt, ContMDiffAt, contMDiffWithinAt_iff_target, continuousWithinAt_univ]
/-
**continuousWithinAt_iff_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_iff_source : ContinuousWithinAt f s x ↔ ContinuousWithi
nAt (f ∘ (extChartAt I x).symm) ((extChartAt I x).symm ⁻¹' s inter range I) (ext
ChartAt I x x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.comp_of_eq`：ContinuousWithinAt.comp_of_eq {g : β -> γ
} {t : Set β} {y : β} (hg : ContinuousWithinAt g t y) (hf : ContinuousWithinAt f
 s x) (h : MapsTo f…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `continuousAt_extChartAt_symm`：continuousAt_extChartAt_symm (x : M) : Con
tinuousAt (extChartAt I x).symm ((extChartAt I x) x)
· 使用定理 `Set.MapsTo.mono_left`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t
 : Set β} {f : α → β}, Set.MapsTo f s₁ t → s₂ ⊆ s₁ → Set.MapsTo f s₂ t
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `extChartAt_to_inv`：extChartAt_to_inv (x : M) : (extChartAt I x).symm ((e
xtChartAt I x) x) = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_inter`：continuousWithinAt_inter (h : t in 𝓝 x) : Cont
inuousWithinAt f (s inter t) x ↔ ContinuousWithinAt f s x
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…
· 使用定理 `continuousAt_extChartAt`：continuousAt_extChartAt (x : M) : ContinuousAt 
(extChartAt I x) x
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousWithinAt.congr`：ContinuousWithinAt.congr (h : ContinuousWithin
At f s x) (h₁ : forall y in s, g y = f y) (hx : g x = f x) : ContinuousWithinAt 
g s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem continuousWithinAt_iff_source :
    ContinuousWithinAt f s x ↔
      ContinuousWithinAt (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · apply h.comp_of_eq
    · exact (continuousAt_extChartAt_symm x).continuousWithinAt
    · exact (mapsTo_preimage _ _).mono_left inter_subset_left
    · exact extChartAt_to_inv x
  · rw [← continuousWithinAt_inter (extChartAt_source_mem_nhds (I := I) x)]
    have : ContinuousWithinAt ((f ∘ ↑(extChartAt I x).symm) ∘ ↑(extChartAt I x))
        (s ∩ (extChartAt I x).source) x := by
      apply h.comp (continuousAt_extChartAt x).continuousWithinAt
      intro y hy
      have : (chartAt H x).symm ((chartAt H x) y) = y :=
        OpenPartialHomeomorph.left_inv _ (by simpa using hy.2)
      simpa [this] using hy.1
    apply this.congr
    · intro y hy
      have : (chartAt H x).symm ((chartAt H x) y) = y :=
        OpenPartialHomeomorph.left_inv _ (by simpa using hy.2)
      simp [this]
    · simp

set_option backward.isDefEq.respectTransparency false in
/-- One can reformulate being `Cⁿ` within a set at a point as being `Cⁿ` in the source space when
composing with the extended chart. -/
/-
**contMDiffWithinAt_iff_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff_source : ContMDiffWithinAt I I' n f s x ↔ ContMDiffW
ithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm) ((extChartAt I x).symm ⁻¹' s in
ter range I) (extChartAt I x x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `OpenPartialHomeomorph.refl_apply`：∀ (X : Type u_7) [inst : TopologicalSp
ace X], ↑(OpenPartialHomeomorph.refl X) = id
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
One can reformulate being `Cⁿ` within a set at a point as being `Cⁿ` in the sour
ce space when
composing with the extended chart.
-/
theorem contMDiffWithinAt_iff_source :
    ContMDiffWithinAt I I' n f s x ↔
      ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  simp_rw [ContMDiffWithinAt, liftPropWithinAt_iff', ← continuousWithinAt_iff_source]
  simp only [ContDiffWithinAtProp, mfld_simps, preimage_comp, comp_assoc]

/-- One can reformulate being `Cⁿ` at a point as being `Cⁿ` in the source space when
composing with the extended chart. -/
/-
**contMDiffAt_iff_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_iff_source : ContMDiffAt I I' n f x ↔ ContMDiffWithinAt 𝓘(𝕜, E
) I' n (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffWithinAt_univ`：contMDiffWithinAt_univ : ContMDiffWithinAt I I' 
n f univ x ↔ ContMDiffAt I I' n f x
· 使用定理 `contMDiffWithinAt_iff_source`：contMDiffWithinAt_iff_source : ContMDiffWi
thinAt I I' n f s x ↔ ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm)
 ((extChartAt I x)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
One can reformulate being `Cⁿ` at a point as being `Cⁿ` in the source space when
composing with the extended chart.
-/
theorem contMDiffAt_iff_source :
    ContMDiffAt I I' n f x ↔
      ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) := by
  rw [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_source]
  simp

section IsManifold

/-
**contMDiffWithinAt_iff_source_of_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff_source_of_mem_maximalAtlas (he : e in maximalAtlas I
 n M) (hx : x in e.source) : ContMDiffWithinAt I I' n f s x ↔ ContMDiffWithinAt 
𝓘(𝕜, E) I' n (f ∘ (e.extend I).symm) ((e.extend I).symm ⁻¹' s inter range I) (e.
extend I x)
参数：he : e in maximalAtlas I n M；hx : x in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_source
`：liftPropWithinAt_indep_chart_source (he : e in G.maximalAtlas M) (xe : x in e.
source) : LiftPropWithinAt P g s x ↔ LiftPropWithinAt P (g ∘ e…
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.extend_symm_continuousWithinAt_comp_right_iff`：ext
end_symm_continuousWithinAt_comp_right_iff {X} [TopologicalSpace X] {g : M -> X}
 {s : Set M} {x : M} : ContinuousWithinAt (g ∘ (f.extend …
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.extend_source`：extend_source : (f.extend I).source
 = f.source
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contMDiffWithinAt_iff_source_of_mem_maximalAtlas
    (he : e ∈ maximalAtlas I n M) (hx : x ∈ e.source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (e.extend I).symm) ((e.extend I).symm ⁻¹' s ∩ range I)
        (e.extend I x) := by
  have h2x := hx; rw [← e.extend_source (I := I)] at h2x
  simp_rw [ContMDiffWithinAt,
    (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_indep_chart_source he hx,
    StructureGroupoid.liftPropWithinAt_self_source,
    e.extend_symm_continuousWithinAt_comp_right_iff, contDiffWithinAtProp_self_source,
    ContDiffWithinAtProp, Function.comp, e.left_inv hx, (e.extend I).left_inv h2x]
  rfl
/-
**contMDiffWithinAt_iff_source_of_mem_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff_source_of_mem_source [IsManifold I n M] (hx' : x' in
 (chartAt H x).source) : ContMDiffWithinAt I I' n f s x' ↔ ContMDiffWithinAt 𝓘(𝕜
, E) I' n (f ∘ (extChartAt I x).symm) ((extChartAt I x).symm ⁻¹' s inter range I
) (extChartAt I x x')
参数：hx' : x' in (chartAt H x).source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_iff_source_of_mem_maximalAtlas`：contMDiffWithinAt_iff_
source_of_mem_maximalAtlas (he : e in maximalAtlas I n M) (hx : x in e.source) :
 ContMDiffWithinAt I I' n f s x ↔ Cont…
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M
-/
theorem contMDiffWithinAt_iff_source_of_mem_source
    [IsManifold I n M] (hx' : x' ∈ (chartAt H x).source) :
    ContMDiffWithinAt I I' n f s x' ↔
      ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x') :=
  contMDiffWithinAt_iff_source_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hx'
/-
**contMDiffAt_iff_source_of_mem_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_iff_source_of_mem_source [IsManifold I n M] (hx' : x' in (char
tAt H x).source) : ContMDiffAt I I' n f x' ↔ ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘
 (extChartAt I x).symm) (range I) (extChartAt I x x')
参数：hx' : x' in (chartAt H x).source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_iff_source_of_mem_source`：contMDiffWithinAt_iff_source
_of_mem_source [IsManifold I n M] (hx' : x' in (chartAt H x).source) : ContMDiff
WithinAt I I' n f s x' ↔ ContMDi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contMDiffAt_iff_source_of_mem_source
    [IsManifold I n M] (hx' : x' ∈ (chartAt H x).source) :
    ContMDiffAt I I' n f x' ↔
      ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x') := by
  simp_rw [ContMDiffAt, contMDiffWithinAt_iff_source_of_mem_source hx', preimage_univ, univ_inter]
/-
**contMDiffWithinAt_iff_target_of_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff_target_of_mem_maximalAtlas (he' : e' in maximalAtlas
 I' n M') (hx : f x in e'.source) : ContMDiffWithinAt I I' n f s x ↔ ContinuousW
ithinAt f s x ∧ ContMDiffWithinAt I 𝓘(𝕜, E') n ((e'.extend I') ∘ f) s x
参数：he' : e' in maximalAtlas I' n M'；hx : f x in e'.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_target
`：liftPropWithinAt_indep_chart_target (hf : f in G'.maximalAtlas M') (xf : g x i
n f.source) : LiftPropWithinAt P g s x ↔ ContinuousWithinAt g …
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `OpenPartialHomeomorph.continuousAt_extend`：continuousAt_extend {x : M} (
h : x in f.source) : ContinuousAt (f.extend I) x
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contMDiffWithinAt_iff_target_of_mem_maximalAtlas
    (he' : e' ∈ maximalAtlas I' n M') (hx : f x ∈ e'.source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧ ContMDiffWithinAt I 𝓘(𝕜, E') n ((e'.extend I') ∘ f) s x := by
  simp_rw [ContMDiffWithinAt,
    (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_indep_chart_target he' hx]
  apply and_congr_right (fun h ↦ ?_)
  have A : ContinuousWithinAt ((e'.extend I') ∘ f) s x :=
    (e'.continuousAt_extend hx).comp_continuousWithinAt h
  have A' : ContinuousWithinAt (e' ∘ f) s x := (e'.continuousAt hx).comp_continuousWithinAt h
  simp_rw [StructureGroupoid.liftPropWithinAt_self_target, A, A']
  simp [ContDiffWithinAtProp, comp_assoc]
/-
**contMDiffWithinAt_iff_target_of_mem_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff_target_of_mem_source [IsManifold I' n M'] (hy : f x 
in (chartAt H' y).source) : ContMDiffWithinAt I I' n f s x ↔ ContinuousWithinAt 
f s x ∧ ContMDiffWithinAt I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) s x
参数：hy : f x in (chartAt H' y).source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_iff_target_of_mem_maximalAtlas`：contMDiffWithinAt_iff_
target_of_mem_maximalAtlas (he' : e' in maximalAtlas I' n M') (hx : f x in e'.so
urce) : ContMDiffWithinAt I I' n f s x…
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M
-/
theorem contMDiffWithinAt_iff_target_of_mem_source [IsManifold I' n M']
    (hy : f x ∈ (chartAt H' y).source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧ ContMDiffWithinAt I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) s x :=
  contMDiffWithinAt_iff_target_of_mem_maximalAtlas (chart_mem_maximalAtlas _) hy
/-
**contMDiffAt_iff_target_of_mem_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_iff_target_of_mem_source [IsManifold I' n M'] (hy : f x in (ch
artAt H' y).source) : ContMDiffAt I I' n f x ↔ ContinuousAt f x ∧ ContMDiffAt I 
𝓘(𝕜, E') n (extChartAt I' y ∘ f) x
参数：hy : f x in (chartAt H' y).source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContMDiffAt.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `contMDiffWithinAt_iff_target_of_mem_source`：contMDiffWithinAt_iff_target
_of_mem_source [IsManifold I' n M'] (hy : f x in (chartAt H' y).source) : ContMD
iffWithinAt I I' n f s x ↔ Conti…
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contMDiffAt_iff_target_of_mem_source [IsManifold I' n M']
    (hy : f x ∈ (chartAt H' y).source) :
    ContMDiffAt I I' n f x ↔
      ContinuousAt f x ∧ ContMDiffAt I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) x := by
  rw [ContMDiffAt, contMDiffWithinAt_iff_target_of_mem_source hy, continuousWithinAt_univ,
    ContMDiffAt]
/-
**contMDiffWithinAt_iff_of_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff_of_mem_maximalAtlas (he : e in maximalAtlas I n M) (
he' : e' in maximalAtlas I' n M') (hx : x in e.source) (hy : f x in e'.source) :
 ContMDiffWithinAt I I' n f s x ↔ ContinuousWithinAt f s x ∧ ContDiffWithinAt 𝕜 
n (e'.extend I' ∘ f ∘ (e.extend I).symm) ((e.extend I).symm ⁻¹' s inter range I)
 (e.extend I x)
参数：he : e in maximalAtlas I n M；he' : e' in maximalAtlas I' n M'；hx : x in e.sou
rce；hy : f x in e'.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart`：liftP
ropWithinAt_indep_chart (he : e in G.maximalAtlas M) (xe : x in e.source) (hf : 
f in G'.maximalAtlas M') (xf : g x in f.source) : LiftP…
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
theorem contMDiffWithinAt_iff_of_mem_maximalAtlas (he : e ∈ maximalAtlas I n M)
    (he' : e' ∈ maximalAtlas I' n M') (hx : x ∈ e.source) (hy : f x ∈ e'.source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm)
          ((e.extend I).symm ⁻¹' s ∩ range I) (e.extend I x) :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_indep_chart he hx he' hy

set_option backward.isDefEq.respectTransparency.types false in
/-- An alternative version of `contMDiffWithinAt_iff_of_mem_maximalAtlas` which takes a
chart `e'` in the target in the maximal atlas, but uses the preferred chart on the domain. -/
/-
**contMDiffWithinAt_iff_of_mem_maximalAtlas'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff_of_mem_maximalAtlas' (he' : e' in maximalAtlas I' n 
M') (hy : f x in e'.source) : ContMDiffWithinAt I I' n f s x ↔ ContinuousWithinA
t f s x ∧ ContDiffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (extChartAt I x).symm) ((extC
hartAt I x).symm ⁻¹' s inter range I) (extChartAt I x x)
参数：he' : e' in maximalAtlas I' n M'；hy : f x in e'.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_iff_source`：contMDiffWithinAt_iff_source : ContMDiffWi
thinAt I I' n f s x ↔ ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm)
 ((extChartAt I x)…
· 使用定理 `contMDiffWithinAt_iff_target_of_mem_maximalAtlas`：contMDiffWithinAt_iff_
target_of_mem_maximalAtlas (he' : e' in maximalAtlas I' n M') (hx : f x in e'.so
urce) : ContMDiffWithinAt I I' n f s x…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `continuousWithinAt_iff_source`：continuousWithinAt_iff_source : Continuou
sWithinAt f s x ↔ ContinuousWithinAt (f ∘ (extChartAt I x).symm) ((extChartAt I 
x).symm ⁻¹' s inter…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.refl_apply`：∀ (X : Type u_7) [inst : TopologicalSp
ace X], ↑(OpenPartialHomeomorph.refl X) = id
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `ContDiffWithinAt.continuousWithinAt`：ContDiffWithinAt.continuousWithinAt
 (h : ContDiffWithinAt 𝕜 n f s x) : ContinuousWithinAt f s x

--- 原说明 ---
An alternative version of `contMDiffWithinAt_iff_of_mem_maximalAtlas` which take
s a
chart `e'` in the target in the maximal atlas, but uses the preferred chart on t
he domain.
-/
theorem contMDiffWithinAt_iff_of_mem_maximalAtlas'
    (he' : e' ∈ maximalAtlas I' n M') (hy : f x ∈ e'.source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  rw [contMDiffWithinAt_iff_source,
    contMDiffWithinAt_iff_target_of_mem_maximalAtlas he' (by simpa)]
  apply and_congr continuousWithinAt_iff_source.symm
  -- TODO: this is `contMDiffWithinAt_iff_contDiffWithinAt` copied,
  -- which is not put here for import reasons
  simp +contextual only [ContMDiffWithinAt, liftPropWithinAt_iff',
    ContDiffWithinAtProp, iff_def, mfld_simps]
  exact ContDiffWithinAt.continuousWithinAt

/-- An alternative formulation of `contMDiffWithinAt_iff_of_mem_maximalAtlas`
if the set `s` lies in `e.source`. -/
/-
**contMDiffWithinAt_iff_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff_image (he : e in maximalAtlas I n M) (he' : e' in ma
ximalAtlas I' n M') (hs : s subseteq e.source) (hx : x in e.source) (hy : f x in
 e'.source) : ContMDiffWithinAt I I' n f s x ↔ ContinuousWithinAt f s x ∧ ContDi
ffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) (e.exten
d I x)
参数：he : e in maximalAtlas I n M；he' : e' in maximalAtlas I' n M'；hs : s subseteq
 e.source；hx : x in e.source；hy : f x in e'.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_iff_of_mem_maximalAtlas`：contMDiffWithinAt_iff_of_mem_
maximalAtlas (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I' n M') (
hx : x in e.source) (hy : f x i…
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `contDiffWithinAt_congr_set`：contDiffWithinAt_congr_set {t : Set E} (hst 
: s =ᶠ[𝓝 x] t) : ContDiffWithinAt 𝕜 n f s x ↔ ContDiffWithinAt 𝕜 n f t x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `OpenPartialHomeomorph.extend_symm_preimage_inter_range_eventuallyEq`：ext
end_symm_preimage_inter_range_eventuallyEq {s : Set M} {x : M} (hs : s subseteq 
f.source) (hx : x in f.source) : ((f.extend I).symm ⁻¹' s…

--- 原说明 ---
An alternative formulation of `contMDiffWithinAt_iff_of_mem_maximalAtlas`
if the set `s` lies in `e.source`.
-/
theorem contMDiffWithinAt_iff_image
    (he : e ∈ maximalAtlas I n M) (he' : e' ∈ maximalAtlas I' n M')
    (hs : s ⊆ e.source) (hx : x ∈ e.source) (hy : f x ∈ e'.source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s)
          (e.extend I x) := by
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas he he' hx hy, and_congr_right_iff]
  refine fun _ => contDiffWithinAt_congr_set ?_
  simp_rw [e.extend_symm_preimage_inter_range_eventuallyEq hs hx]
/-
**contMDiffAt_iff_of_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_iff_of_mem_maximalAtlas {x : M} (he : e in maximalAtlas I n M)
 (he' : e' in maximalAtlas I' n M') (hx : x in e.source) (hy : f x in e'.source)
 : ContMDiffAt I I' n f x ↔ ContinuousAt f x ∧ ContDiffWithinAt 𝕜 n (e'.extend I
' ∘ f ∘ (e.extend I).symm) (range I) (e.extend I x)
参数：he : e in maximalAtlas I n M；he' : e' in maximalAtlas I' n M'；hx : x in e.sou
rce；hy : f x in e'.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffWithinAt_univ`：contMDiffWithinAt_univ : ContMDiffWithinAt I I' 
n f univ x ↔ ContMDiffAt I I' n f x
· 使用定理 `contMDiffWithinAt_iff_of_mem_maximalAtlas`：contMDiffWithinAt_iff_of_mem_
maximalAtlas (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I' n M') (
hx : x in e.source) (hy : f x i…
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contMDiffAt_iff_of_mem_maximalAtlas {x : M} (he : e ∈ maximalAtlas I n M)
    (he' : e' ∈ maximalAtlas I' n M') (hx : x ∈ e.source) (hy : f x ∈ e'.source) :
    ContMDiffAt I I' n f x ↔
      ContinuousAt f x ∧
        ContDiffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (range I) (e.extend I x) := by
  rw [← contMDiffWithinAt_univ,
    contMDiffWithinAt_iff_of_mem_maximalAtlas he he' hx hy,
    continuousWithinAt_univ, preimage_univ, univ_inter]

/-- One can reformulate being `C^n` within a set at a point as continuity within this set at this
point, and being `C^n` in any chart containing that point. -/
/-
**contMDiffWithinAt_iff_of_mem_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff_of_mem_source [IsManifold I n M] [IsManifold I' n M'
] (hx : x' in (chartAt H x).source) (hy : f x' in (chartAt H' y).source) : ContM
DiffWithinAt I I' n f s x' ↔ ContinuousWithinAt f s x' ∧ ContDiffWithinAt 𝕜 n (e
xtChartAt I' y ∘ f ∘ (extChartAt I x).symm) ((extChartAt I x).symm ⁻¹' s inter r
ange I) (extChartAt I x x')
参数：hx : x' in (chartAt H x).source；hy : f x' in (chartAt H' y).source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_iff_of_mem_maximalAtlas`：contMDiffWithinAt_iff_of_mem_
maximalAtlas (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I' n M') (
hx : x in e.source) (hy : f x i…
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M

--- 原说明 ---
One can reformulate being `C^n` within a set at a point as continuity within thi
s set at this
point, and being `C^n` in any chart containing that point.
-/
theorem contMDiffWithinAt_iff_of_mem_source [IsManifold I n M] [IsManifold I' n M']
    (hx : x' ∈ (chartAt H x).source) (hy : f x' ∈ (chartAt H' y).source) :
    ContMDiffWithinAt I I' n f s x' ↔
      ContinuousWithinAt f s x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x') :=
  contMDiffWithinAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hx hy
/-
**contMDiffWithinAt_iff_of_mem_source'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff_of_mem_source' [IsManifold I n M] [IsManifold I' n M
'] (hx : x' in (chartAt H x).source) (hy : f x' in (chartAt H' y).source) : Cont
MDiffWithinAt I I' n f s x' ↔ ContinuousWithinAt f s x' ∧ ContDiffWithinAt 𝕜 n (
extChartAt I' y ∘ f ∘ (extChartAt I x).symm) ((extChartAt I x).target inter (ext
ChartAt I x).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' y).source)) (extChartAt I x 
x')
参数：hx : x' in (chartAt H x).source；hy : f x' in (chartAt H' y).source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `contMDiffWithinAt_iff_of_mem_source`：contMDiffWithinAt_iff_of_mem_source
 [IsManifold I n M] [IsManifold I' n M'] (hx : x' in (chartAt H x).source) (hy :
 f x' in (chartAt H' y).s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `contDiffWithinAt_congr_set`：contDiffWithinAt_congr_set {t : Set E} (hst 
: s =ᶠ[𝓝 x] t) : ContDiffWithinAt 𝕜 n f s x ↔ ContDiffWithinAt 𝕜 n f t x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_eq_iff_eventuallyEq`：nhdsWithin_eq_iff_eventuallyEq {s t : Se
t α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t
· 使用定理 `PartialEquiv.image_source_inter_eq'`：image_source_inter_eq' (s : Set α) 
: e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
· 使用定理 `map_extChartAt_nhdsWithin_eq_image'`：map_extChartAt_nhdsWithin_eq_image'
 {x y : M} (hy : y in (extChartAt I x).source) : map (extChartAt I x) (𝓝[s] y) =
 𝓝[extChartAt I x '' ((ex…
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `map_extChartAt_nhdsWithin'`：map_extChartAt_nhdsWithin' {x y : M} (hy : y
 in (extChartAt I x).source) : map (extChartAt I x) (𝓝[s] y) = 𝓝[(extChartAt I x
).symm ⁻¹' s int…
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `nhdsWithin_inter_of_mem`：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (
h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a
· 使用定理 `extChartAt_source_mem_nhds'`：extChartAt_source_mem_nhds' {x x' : M} (h :
 x' in (extChartAt I x).source) : (extChartAt I x).source in 𝓝 x'
-/
theorem contMDiffWithinAt_iff_of_mem_source' [IsManifold I n M] [IsManifold I' n M']
    (hx : x' ∈ (chartAt H x).source) (hy : f x' ∈ (chartAt H' y).source) :
    ContMDiffWithinAt I I' n f s x' ↔
      ContinuousWithinAt f s x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source))
          (extChartAt I x x') := by
  refine (contMDiffWithinAt_iff_of_mem_source hx hy).trans ?_
  rw [← extChartAt_source I] at hx
  rw [← extChartAt_source I'] at hy
  rw [and_congr_right_iff]
  set e := extChartAt I x; set e' := extChartAt I' (f x)
  refine fun hc => contDiffWithinAt_congr_set ?_
  rw [← nhdsWithin_eq_iff_eventuallyEq, ← e.image_source_inter_eq',
    ← map_extChartAt_nhdsWithin_eq_image' hx,
    ← map_extChartAt_nhdsWithin' hx, inter_comm, nhdsWithin_inter_of_mem]
  exact hc (extChartAt_source_mem_nhds' hy)
/-
**contMDiffAt_iff_of_mem_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_iff_of_mem_source [IsManifold I n M] [IsManifold I' n M'] (hx 
: x' in (chartAt H x).source) (hy : f x' in (chartAt H' y).source) : ContMDiffAt
 I I' n f x' ↔ ContinuousAt f x' ∧ ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (
extChartAt I x).symm) (range I) (extChartAt I x x')
参数：hx : x' in (chartAt H x).source；hy : f x' in (chartAt H' y).source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `contMDiffWithinAt_iff_of_mem_source`：contMDiffWithinAt_iff_of_mem_source
 [IsManifold I n M] [IsManifold I' n M'] (hx : x' in (chartAt H x).source) (hy :
 f x' in (chartAt H' y).s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem contMDiffAt_iff_of_mem_source [IsManifold I n M] [IsManifold I' n M']
    (hx : x' ∈ (chartAt H x).source) (hy : f x' ∈ (chartAt H' y).source) :
    ContMDiffAt I I' n f x' ↔
      ContinuousAt f x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x x') :=
  (contMDiffWithinAt_iff_of_mem_source hx hy).trans <| by
    rw [continuousWithinAt_univ, preimage_univ, univ_inter]
/-
**contMDiffOn_iff_of_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_iff_of_mem_maximalAtlas (he : e in maximalAtlas I n M) (he' : 
e' in maximalAtlas I' n M') (hs : s subseteq e.source) (h2s : MapsTo f s e'.sour
ce) : ContMDiffOn I I' n f s ↔ ContinuousOn f s ∧ ContDiffOn 𝕜 n (e'.extend I' ∘
 f ∘ (e.extend I).symm) (e.extend I '' s)
参数：he : e in maximalAtlas I n M；he' : e' in maximalAtlas I' n M'；hs : s subseteq
 e.source；h2s : MapsTo f s e'.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `contMDiffWithinAt_iff_image`：contMDiffWithinAt_iff_image (he : e in maxi
malAtlas I n M) (he' : e' in maximalAtlas I' n M') (hs : s subseteq e.source) (h
x : x in e.source…
-/
theorem contMDiffOn_iff_of_mem_maximalAtlas (he : e ∈ maximalAtlas I n M)
    (he' : e' ∈ maximalAtlas I' n M') (hs : s ⊆ e.source) (h2s : MapsTo f s e'.source) :
    ContMDiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ContDiffOn 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) := by
  simp_rw [ContinuousOn, ContDiffOn, Set.forall_mem_image, ← forall_and, ContMDiffOn]
  exact forall₂_congr fun x hx => contMDiffWithinAt_iff_image he he' hs (hs hx) (h2s hx)
/-
**contMDiffOn_iff_of_mem_maximalAtlas'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_iff_of_mem_maximalAtlas' (he : e in maximalAtlas I n M) (he' :
 e' in maximalAtlas I' n M') (hs : s subseteq e.source) (h2s : MapsTo f s e'.sou
rce) : ContMDiffOn I I' n f s ↔ ContDiffOn 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).
symm) (e.extend I '' s)
参数：he : e in maximalAtlas I n M；he' : e' in maximalAtlas I' n M'；hs : s subseteq
 e.source；h2s : MapsTo f s e'.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `contMDiffOn_iff_of_mem_maximalAtlas`：contMDiffOn_iff_of_mem_maximalAtlas
 (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I' n M') (hs : s subse
teq e.source) (h2s : Maps…
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `OpenPartialHomeomorph.continuousOn_writtenInExtend_iff`：continuousOn_wri
ttenInExtend_iff {f' : OpenPartialHomeomorph M' H'} {g : M -> M'} (hs : s subset
eq f.source) (hmaps : MapsTo g s f'.source) …
· 使用定理 `ContDiffOn.continuousOn`：ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s
) : ContinuousOn f s
-/
theorem contMDiffOn_iff_of_mem_maximalAtlas' (he : e ∈ maximalAtlas I n M)
    (he' : e' ∈ maximalAtlas I' n M') (hs : s ⊆ e.source) (h2s : MapsTo f s e'.source) :
    ContMDiffOn I I' n f s ↔
      ContDiffOn 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) :=
  (contMDiffOn_iff_of_mem_maximalAtlas he he' hs h2s).trans <| and_iff_right_of_imp fun h ↦
    (e.continuousOn_writtenInExtend_iff hs h2s).1 h.continuousOn

/-- If the set where you want `f` to be `C^n` lies entirely in a single chart, and `f` maps it
into a single chart, the fact that `f` is `C^n` on that set can be expressed by purely looking in
these charts.
Note: this lemma uses `extChartAt I x '' s` instead of `(extChartAt I x).symm ⁻¹' s` to ensure
that this set lies in `(extChartAt I x).target`. -/
/-
**contMDiffOn_iff_of_subset_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_iff_of_subset_source [IsManifold I n M] [IsManifold I' n M'] (
hs : s subseteq (chartAt H x).source) (h2s : MapsTo f s (chartAt H' y).source) :
 ContMDiffOn I I' n f s ↔ ContinuousOn f s ∧ ContDiffOn 𝕜 n (extChartAt I' y ∘ f
 ∘ (extChartAt I x).symm) (extChartAt I x '' s)
参数：hs : s subseteq (chartAt H x).source；h2s : MapsTo f s (chartAt H' y).source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffOn_iff_of_mem_maximalAtlas`：contMDiffOn_iff_of_mem_maximalAtlas
 (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I' n M') (hs : s subse
teq e.source) (h2s : Maps…
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M

--- 原说明 ---
If the set where you want `f` to be `C^n` lies entirely in a single chart, and `
f` maps it
into a single chart, the fact that `f` is `C^n` on that set can be expressed by 
purely looking in
these charts.
Note: this lemma uses `extChartAt I x '' s` instead of `(extChartAt I x).symm ⁻¹
' s` to ensure
that this set lies in `(extChartAt I x).target`.
-/
theorem contMDiffOn_iff_of_subset_source [IsManifold I n M] [IsManifold I' n M']
    (hs : s ⊆ (chartAt H x).source)
    (h2s : MapsTo f s (chartAt H' y).source) :
    ContMDiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x '' s) :=
  contMDiffOn_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas y) hs
    h2s

/-- If the set where you want `f` to be `C^n` lies entirely in a single chart, and `f` maps it
into a single chart, the fact that `f` is `C^n` on that set can be expressed by purely looking in
these charts.
Note: this lemma uses `extChartAt I x '' s` instead of `(extChartAt I x).symm ⁻¹' s` to ensure
that this set lies in `(extChartAt I x).target`. -/
/-
**contMDiffOn_iff_of_subset_source'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_iff_of_subset_source' [IsManifold I n M] [IsManifold I' n M'] 
(hs : s subseteq (extChartAt I x).source) (h2s : MapsTo f s (extChartAt I' y).so
urce) : ContMDiffOn I I' n f s ↔ ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChart
At I x).symm) (extChartAt I x '' s)
参数：hs : s subseteq (extChartAt I x).source；h2s : MapsTo f s (extChartAt I' y).so
urce。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffOn_iff_of_mem_maximalAtlas'`：contMDiffOn_iff_of_mem_maximalAtla
s' (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I' n M') (hs : s sub
seteq e.source) (h2s : Map…
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source

--- 原说明 ---
If the set where you want `f` to be `C^n` lies entirely in a single chart, and `
f` maps it
into a single chart, the fact that `f` is `C^n` on that set can be expressed by 
purely looking in
these charts.
Note: this lemma uses `extChartAt I x '' s` instead of `(extChartAt I x).symm ⁻¹
' s` to ensure
that this set lies in `(extChartAt I x).target`.
-/
theorem contMDiffOn_iff_of_subset_source' [IsManifold I n M] [IsManifold I' n M']
    (hs : s ⊆ (extChartAt I x).source) (h2s : MapsTo f s (extChartAt I' y).source) :
    ContMDiffOn I I' n f s ↔
        ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x '' s) := by
  rw [extChartAt_source] at hs h2s
  exact contMDiffOn_iff_of_mem_maximalAtlas' (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hs h2s

/-- One can reformulate being `C^n` on a set as continuity on this set, and being `C^n` in any
extended chart. -/
/-
**contMDiffOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_iff [IsManifold I n M] [IsManifold I' n M'] : ContMDiffOn I I'
 n f s ↔ ContinuousOn f s ∧ forall (x : M) (y : M'), ContDiffOn 𝕜 n (extChartAt 
I' y ∘ f ∘ (extChartAt I x).symm) ((extChartAt I x).target inter (extChartAt I x
).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' y).source))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContDiffWithinAt.mono`：ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f
 s x) {t : Set E} (hst : t subseteq s) : ContDiffWithinAt 𝕜 n f t x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contMDiffWithinAt_iff_of_mem_source`：contMDiffWithinAt_iff_of_mem_source
 [IsManifold I n M] [IsManifold I' n M'] (hx : x' in (chartAt H x).source) (hy :
 f x' in (chartAt H' y).s…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_iff`：liftPropWithi
nAt_iff {f : M -> M'} : LiftPropWithinAt P f s x ↔ ContinuousWithinAt f s x ∧ P 
(chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) ((c…
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x

--- 原说明 ---
One can reformulate being `C^n` on a set as continuity on this set, and being `C
^n` in any
extended chart.
-/
theorem contMDiffOn_iff [IsManifold I n M] [IsManifold I' n M'] :
    ContMDiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ∀ (x : M) (y : M'),
          ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source)) := by
  constructor
  · intro h
    refine ⟨fun x hx => (h x hx).1, fun x y z hz => ?_⟩
    simp only [mfld_simps] at hz
    let w := (extChartAt I x).symm z
    have : w ∈ s := by simp only [w, hz, mfld_simps]
    specialize h w this
    have w1 : w ∈ (chartAt H x).source := by simp only [w, hz, mfld_simps]
    have w2 : f w ∈ (chartAt H' y).source := by simp only [w, hz, mfld_simps]
    convert! ((contMDiffWithinAt_iff_of_mem_source w1 w2).mp h).2.mono _
    · simp only [w, hz, mfld_simps]
    · mfld_set_tac
  · rintro ⟨hcont, hdiff⟩ x hx
    refine (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_iff.mpr ?_
    refine ⟨hcont x hx, ?_⟩
    dsimp [ContDiffWithinAtProp]
    convert! hdiff x (f x) (extChartAt I x x) (by simp only [hx, mfld_simps]) using 1
    mfld_set_tac

/-- zero-smoothness on a set is equivalent to continuity on this set. -/
/-
**contMDiffOn_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_zero_iff : ContMDiffOn I I' 0 f s ↔ ContinuousOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffOn_iff`：contMDiffOn_iff [IsManifold I n M] [IsManifold I' n M']
 : ContMDiffOn I I' n f s ↔ ContinuousOn f s ∧ forall (x : M) (y : M'), ContDiff
On 𝕜 …
· 使用定理 `IsManifold.instOfNatWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `contDiffOn_zero`：contDiffOn_zero : ContDiffOn 𝕜 0 f s ↔ ContinuousOn f s
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `continuousOn_extChartAt`：continuousOn_extChartAt (x : M) : ContinuousOn 
(extChartAt I x) (extChartAt I x).source
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `continuousOn_extChartAt_symm`：continuousOn_extChartAt_symm (x : M) : Con
tinuousOn (extChartAt I x).symm (extChartAt I x).target
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
zero-smoothness on a set is equivalent to continuity on this set.
-/
theorem contMDiffOn_zero_iff : ContMDiffOn I I' 0 f s ↔ ContinuousOn f s := by
  rw [contMDiffOn_iff]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
  intro x y
  rw [contDiffOn_zero]
  apply (continuousOn_extChartAt _).comp
  · apply h.comp ((continuousOn_extChartAt_symm _).mono inter_subset_left) (fun z hz ↦ ?_)
    simp only [preimage_inter, mem_inter_iff, mem_preimage] at hz
    exact hz.2.1
  · intro z hz
    simp only [preimage_inter, mem_inter_iff, mem_preimage] at hz
    exact hz.2.2

/-- One can reformulate being `C^n` on a set as continuity on this set, and being `C^n` in any
extended chart in the target. -/
/-
**contMDiffOn_iff_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_iff_target [IsManifold I n M] [IsManifold I' n M'] : ContMDiff
On I I' n f s ↔ ContinuousOn f s ∧ forall y : M', ContMDiffOn I 𝓘(𝕜, E') n (extC
hartAt I' y ∘ f) (s inter f ⁻¹' (extChartAt I' y).source)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsManifold.instOfTopWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PartialEquiv.refl_trans`：refl_trans : (PartialEquiv.refl α).trans e = e
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ModelWithCorners.continuous`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousOn.comp_inter`：ContinuousOn.comp_inter {g : β -> γ} {t : Set β
} (hg : ContinuousOn g t) (hf : ContinuousOn f s) : ContinuousOn (g ∘ f) (s inte
r f ⁻¹' t)
· 使用定理 `PartialHomeomorph.continuousOn_toFun`：∀ {X : Type u_7} {Y : Type u_8} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeomo
rph X Y), ContinuousOn (↑s…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
One can reformulate being `C^n` on a set as continuity on this set, and being `C
^n` in any
extended chart in the target.
-/
theorem contMDiffOn_iff_target [IsManifold I n M] [IsManifold I' n M'] :
    ContMDiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ∀ y : M',
          ContMDiffOn I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) (s ∩ f ⁻¹' (extChartAt I' y).source) := by
  simp only [contMDiffOn_iff, ModelWithCorners.source_eq, chartAt_self_eq,
    OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_trans, extChartAt,
    OpenPartialHomeomorph.extend, Set.preimage_univ, Set.inter_univ, and_congr_right_iff]
  intro h
  constructor
  · refine fun h' y => ⟨?_, fun x _ => h' x y⟩
    have h'' : ContinuousOn _ univ := (ModelWithCorners.continuous I').continuousOn
    convert! (h''.comp_inter (chartAt H' y).continuousOn_toFun).comp_inter h
    simp
  · exact fun h' x y => (h' y).2 x 0


/-- One can reformulate being `C^n` as continuity and being `C^n` in any extended chart. -/
/-
**contMDiff_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_iff [IsManifold I n M] [IsManifold I' n M'] : ContMDiff I I' n f
 ↔ Continuous f ∧ forall (x : M) (y : M'), ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘
 (extChartAt I x).symm) ((extChartAt I x).target inter (extChartAt I x).symm ⁻¹'
 f ⁻¹' (extChartAt I' y).source)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
One can reformulate being `C^n` as continuity and being `C^n` in any extended ch
art.
-/
theorem contMDiff_iff [IsManifold I n M] [IsManifold I' n M'] :
    ContMDiff I I' n f ↔
      Continuous f ∧
        ∀ (x : M) (y : M'),
          ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' f ⁻¹' (extChartAt I' y).source) := by
  simp [← contMDiffOn_univ, contMDiffOn_iff, continuousOn_univ]

/-- One can reformulate being `C^n` as continuity and being `C^n` in any extended chart in the
target. -/
/-
**contMDiff_iff_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_iff_target [IsManifold I n M] [IsManifold I' n M'] : ContMDiff I
 I' n f ↔ Continuous f ∧ forall y : M', ContMDiffOn I 𝓘(𝕜, E') n (extChartAt I' 
y ∘ f) (f ⁻¹' (extChartAt I' y).source)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffOn_univ`：contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDi
ff I I' n f
· 使用定理 `contMDiffOn_iff_target`：contMDiffOn_iff_target [IsManifold I n M] [IsMan
ifold I' n M'] : ContMDiffOn I I' n f s ↔ ContinuousOn f s ∧ forall y : M', Cont
MDiffOn I 𝓘(…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
One can reformulate being `C^n` as continuity and being `C^n` in any extended ch
art in the
target.
-/
theorem contMDiff_iff_target [IsManifold I n M] [IsManifold I' n M'] :
    ContMDiff I I' n f ↔
      Continuous f ∧ ∀ y : M',
        ContMDiffOn I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) (f ⁻¹' (extChartAt I' y).source) := by
  rw [← contMDiffOn_univ, contMDiffOn_iff_target]
  simp [continuousOn_univ]

/-- zero-smoothness is equivalent to continuity. -/
/-
**contMDiff_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_zero_iff : ContMDiff I I' 0 f ↔ Continuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffOn_univ`：contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDi
ff I I' n f
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `contMDiffOn_zero_iff`：contMDiffOn_zero_iff : ContMDiffOn I I' 0 f s ↔ Co
ntinuousOn f s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
zero-smoothness is equivalent to continuity.
-/
theorem contMDiff_zero_iff :
    ContMDiff I I' 0 f ↔ Continuous f := by
  rw [← contMDiffOn_univ, ← continuousOn_univ, contMDiffOn_zero_iff]

end IsManifold


/-! ### `C^(n+1)` functions are `C^n` -/

/-
**ContMDiffWithinAt.of_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.of_succ (h : ContMDiffWithinAt I I' (n + 1) f s x) : Con
tMDiffWithinAt I I' n f s x
参数：h : ContMDiffWithinAt I I' (n + 1) f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.of_le`：ContMDiffWithinAt.of_le (hf : ContMDiffWithinAt
 I I' n f s x) (le : m <= n) : ContMDiffWithinAt I I' m f s x
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `WithTop.canonicallyOrderedAdd`：∀ {α : Type u} [inst : Add α] [inst_1 : P
reorder α] [CanonicallyOrderedAdd α], CanonicallyOrderedAdd (WithTop α)
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞

--- 原说明 ---
### `C^(n+1)` functions are `C^n`
-/
theorem ContMDiffWithinAt.of_succ (h : ContMDiffWithinAt I I' (n + 1) f s x) :
    ContMDiffWithinAt I I' n f s x :=
  h.of_le le_self_add
/-
**ContMDiffAt.of_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.of_succ (h : ContMDiffAt I I' (n + 1) f x) : ContMDiffAt I I' 
n f x
参数：h : ContMDiffAt I I' (n + 1) f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.of_succ`：ContMDiffWithinAt.of_succ (h : ContMDiffWithi
nAt I I' (n + 1) f s x) : ContMDiffWithinAt I I' n f s x
-/
theorem ContMDiffAt.of_succ (h : ContMDiffAt I I' (n + 1) f x) : ContMDiffAt I I' n f x :=
  ContMDiffWithinAt.of_succ h
/-
**ContMDiffOn.of_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.of_succ (h : ContMDiffOn I I' (n + 1) f s) : ContMDiffOn I I' 
n f s
参数：h : ContMDiffOn I I' (n + 1) f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.of_succ`：ContMDiffWithinAt.of_succ (h : ContMDiffWithi
nAt I I' (n + 1) f s x) : ContMDiffWithinAt I I' n f s x
-/
theorem ContMDiffOn.of_succ (h : ContMDiffOn I I' (n + 1) f s) : ContMDiffOn I I' n f s :=
  fun x hx => (h x hx).of_succ
/-
**ContMDiff.of_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.of_succ (h : ContMDiff I I' (n + 1) f) : ContMDiff I I' n f
参数：h : ContMDiff I I' (n + 1) f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.of_succ`：ContMDiffAt.of_succ (h : ContMDiffAt I I' (n + 1) f
 x) : ContMDiffAt I I' n f x
-/
theorem ContMDiff.of_succ (h : ContMDiff I I' (n + 1) f) : ContMDiff I I' n f := fun x =>
  (h x).of_succ


/-! ### `C^n` functions are continuous -/

/-
**ContMDiffWithinAt.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.continuousWithinAt (hf : ContMDiffWithinAt I I' n f s x)
 : ContinuousWithinAt f s x
参数：hf : ContMDiffWithinAt I I' n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…

--- 原说明 ---
### `C^n` functions are continuous
-/
theorem ContMDiffWithinAt.continuousWithinAt (hf : ContMDiffWithinAt I I' n f s x) :
    ContinuousWithinAt f s x :=
  hf.1
/-
**ContMDiffAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.continuousAt (hf : ContMDiffAt I I' n f x) : ContinuousAt f x
参数：hf : ContMDiffAt I I' n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `ContMDiffWithinAt.continuousWithinAt`：ContMDiffWithinAt.continuousWithin
At (hf : ContMDiffWithinAt I I' n f s x) : ContinuousWithinAt f s x
-/
theorem ContMDiffAt.continuousAt (hf : ContMDiffAt I I' n f x) : ContinuousAt f x :=
  (continuousWithinAt_univ _ _).1 <| ContMDiffWithinAt.continuousWithinAt hf
/-
**ContMDiffOn.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.continuousOn (hf : ContMDiffOn I I' n f s) : ContinuousOn f s
参数：hf : ContMDiffOn I I' n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.continuousWithinAt`：ContMDiffWithinAt.continuousWithin
At (hf : ContMDiffWithinAt I I' n f s x) : ContinuousWithinAt f s x
-/
theorem ContMDiffOn.continuousOn (hf : ContMDiffOn I I' n f s) : ContinuousOn f s := fun x hx =>
  (hf x hx).continuousWithinAt
/-
**ContMDiff.continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.continuous (hf : ContMDiff I I' n f) : Continuous f
参数：hf : ContMDiff I I' n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContMDiffAt.continuousAt`：ContMDiffAt.continuousAt (hf : ContMDiffAt I I
' n f x) : ContinuousAt f x
-/
theorem ContMDiff.continuous (hf : ContMDiff I I' n f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (hf x).continuousAt

/-! ### `C^∞` functions -/

/-
**contMDiffWithinAt_infty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_infty : ContMDiffWithinAt I I' ∞ f s x ↔ forall n : Nat,
 ContMDiffWithinAt I I' n f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffWithinAt_infty`：contDiffWithinAt_infty : ContDiffWithinAt 𝕜 ∞ f 
s x ↔ forall n : Nat, ContDiffWithinAt 𝕜 n f s x
· 使用定理 `ChartedSpace.LiftPropWithinAt.prop`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
### `C^∞` functions
-/
theorem contMDiffWithinAt_infty :
    ContMDiffWithinAt I I' ∞ f s x ↔ ∀ n : ℕ, ContMDiffWithinAt I I' n f s x :=
  ⟨fun h n => ⟨h.1, contDiffWithinAt_infty.1 h.2 n⟩, fun H =>
    ⟨(H 0).1, contDiffWithinAt_infty.2 fun n => (H n).2⟩⟩
/-
**contMDiffAt_infty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_infty : ContMDiffAt I I' ∞ f x ↔ forall n : Nat, ContMDiffAt I
 I' n f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_infty`：contMDiffWithinAt_infty : ContMDiffWithinAt I I
' ∞ f s x ↔ forall n : Nat, ContMDiffWithinAt I I' n f s x
-/
theorem contMDiffAt_infty : ContMDiffAt I I' ∞ f x ↔ ∀ n : ℕ, ContMDiffAt I I' n f x :=
  contMDiffWithinAt_infty
/-
**contMDiffOn_infty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_infty : ContMDiffOn I I' ∞ f s ↔ forall n : Nat, ContMDiffOn I
 I' n f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.of_le`：ContMDiffOn.of_le (hf : ContMDiffOn I I' n f s) (le :
 m <= n) : ContMDiffOn I I' m f s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contMDiffWithinAt_infty`：contMDiffWithinAt_infty : ContMDiffWithinAt I I
' ∞ f s x ↔ forall n : Nat, ContMDiffWithinAt I I' n f s x
-/
theorem contMDiffOn_infty : ContMDiffOn I I' ∞ f s ↔ ∀ n : ℕ, ContMDiffOn I I' n f s :=
  ⟨fun h _ => h.of_le (mod_cast le_top),
    fun h x hx => contMDiffWithinAt_infty.2 fun n => h n x hx⟩
/-
**contMDiff_infty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_infty : ContMDiff I I' ∞ f ↔ forall n : Nat, ContMDiff I I' n f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.of_le`：ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m <= n)
 : ContMDiff I I' m f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contMDiffWithinAt_infty`：contMDiffWithinAt_infty : ContMDiffWithinAt I I
' ∞ f s x ↔ forall n : Nat, ContMDiffWithinAt I I' n f s x
-/
theorem contMDiff_infty : ContMDiff I I' ∞ f ↔ ∀ n : ℕ, ContMDiff I I' n f :=
  ⟨fun h _ => h.of_le (mod_cast le_top), fun h x => contMDiffWithinAt_infty.2 fun n => h n x⟩
/-
**contMDiffWithinAt_iff_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff_nat {n : Nat∞} : ContMDiffWithinAt I I' n f s x ↔ fo
rall m : Nat, (m : Nat∞) <= n -> ContMDiffWithinAt I I' m f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.of_le`：ContMDiffWithinAt.of_le (hf : ContMDiffWithinAt
 I I' n f s x) (le : m <= n) : ContMDiffWithinAt I I' m f s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contMDiffWithinAt_infty`：contMDiffWithinAt_infty : ContMDiffWithinAt I I
' ∞ f s x ↔ forall n : Nat, ContMDiffWithinAt I I' n f s x
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem contMDiffWithinAt_iff_nat {n : ℕ∞} :
    ContMDiffWithinAt I I' n f s x ↔ ∀ m : ℕ, (m : ℕ∞) ≤ n → ContMDiffWithinAt I I' m f s x := by
  refine ⟨fun h m hm => h.of_le (mod_cast hm), fun h => ?_⟩
  obtain - | n := n
  · exact contMDiffWithinAt_infty.2 fun n => h n le_top
  · exact h n le_rfl
/-
**contMDiffAt_iff_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_iff_nat {n : Nat∞} : ContMDiffAt I I' n f x ↔ forall m : Nat, 
(m : Nat∞) <= n -> ContMDiffAt I I' m f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contMDiffAt_iff_nat {n : ℕ∞} :
    ContMDiffAt I I' n f x ↔ ∀ m : ℕ, (m : ℕ∞) ≤ n → ContMDiffAt I I' m f x := by
  simp [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_nat]

/-- A function is `C^n` within a set at a point iff it is `C^m` within this set at this point, for
any `m ≤ n` which is different from `∞`. This result is useful because, when `m ≠ ∞`, being
`C^m` extends locally to a neighborhood, giving flexibility for local proofs. -/
/-
**contMDiffWithinAt_iff_le_ne_infty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff_le_ne_infty : ContMDiffWithinAt I I' n f s x ↔ foral
l m, m <= n -> m != ∞ -> ContMDiffWithinAt I I' m f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.of_le`：ContMDiffWithinAt.of_le (hf : ContMDiffWithinAt
 I I' n f s x) (le : m <= n) : ContMDiffWithinAt I I' m f s x
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contMDiffWithinAt_iff_nat`：contMDiffWithinAt_iff_nat {n : Nat∞} : ContMD
iffWithinAt I I' n f s x ↔ forall m : Nat, (m : Nat∞) <= n -> ContMDiffWithinAt 
I I' m f s x

--- 原说明 ---
A function is `C^n` within a set at a point iff it is `C^m` within this set at t
his point, for
any `m ≤ n` which is different from `∞`. This result is useful because, when `m 
≠ ∞`, being
`C^m` extends locally to a neighborhood, giving flexibility for local proofs.
-/
theorem contMDiffWithinAt_iff_le_ne_infty :
    ContMDiffWithinAt I I' n f s x ↔ ∀ m, m ≤ n → m ≠ ∞ → ContMDiffWithinAt I I' m f s x := by
  refine ⟨fun h m hm h'm ↦ h.of_le hm, fun h ↦ ?_⟩
  cases n with
  | top =>
    exact h _ le_rfl (by simp)
  | coe n =>
    exact contMDiffWithinAt_iff_nat.2 (fun m hm ↦ h _ (mod_cast hm) (by simp))

/-- A function is `C^n` at a point iff it is `C^m` at this point, for
any `m ≤ n` which is different from `∞`. This result is useful because, when `m ≠ ∞`, being
`C^m` extends locally to a neighborhood, giving flexibility for local proofs. -/
/-
**contMDiffAt_iff_le_ne_infty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_iff_le_ne_infty : ContMDiffAt I I' n f x ↔ forall m, m <= n ->
 m != ∞ -> ContMDiffAt I I' m f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `contMDiffWithinAt_iff_le_ne_infty`：contMDiffWithinAt_iff_le_ne_infty : C
ontMDiffWithinAt I I' n f s x ↔ forall m, m <= n -> m != ∞ -> ContMDiffWithinAt 
I I' m f s x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A function is `C^n` at a point iff it is `C^m` at this point, for
any `m ≤ n` which is different from `∞`. This result is useful because, when `m 
≠ ∞`, being
`C^m` extends locally to a neighborhood, giving flexibility for local proofs.
-/
theorem contMDiffAt_iff_le_ne_infty :
    ContMDiffAt I I' n f x ↔ ∀ m, m ≤ n → m ≠ ∞ → ContMDiffAt I I' m f x := by
  simp only [← contMDiffWithinAt_univ]
  rw [contMDiffWithinAt_iff_le_ne_infty]

/-! ### Restriction to a smaller set -/

/-
**ContMDiffWithinAt.mono_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.mono_of_mem_nhdsWithin (hf : ContMDiffWithinAt I I' n f 
s x) (hts : s in 𝓝[t] x) : ContMDiffWithinAt I I' n f t x
参数：hf : ContMDiffWithinAt I I' n f s x；hts : s in 𝓝[t] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_mono_of_mem_nhdsWi
thin`：liftPropWithinAt_mono_of_mem_nhdsWithin (mono_of_mem_nhdsWithin : forall ⦃
s x t⦄ ⦃f : H -> H'⦄, s in 𝓝[t] x -> P f s x -> P f t x) (h : Lift…
· 使用定理 `contDiffWithinAtProp_mono_of_mem_nhdsWithin`：contDiffWithinAtProp_mono_o
f_mem_nhdsWithin (n : Nat∞ω) ⦃s x t⦄ ⦃f : H -> H'⦄ (hts : s in 𝓝[t] x) (h : Cont
DiffWithinAtProp I I' n f s x) : …

--- 原说明 ---
### Restriction to a smaller set
-/
theorem ContMDiffWithinAt.mono_of_mem_nhdsWithin
    (hf : ContMDiffWithinAt I I' n f s x) (hts : s ∈ 𝓝[t] x) :
    ContMDiffWithinAt I I' n f t x :=
  StructureGroupoid.LocalInvariantProp.liftPropWithinAt_mono_of_mem_nhdsWithin
    (contDiffWithinAtProp_mono_of_mem_nhdsWithin n) hf hts
/-
**ContMDiffWithinAt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.mono (hf : ContMDiffWithinAt I I' n f s x) (hts : t subs
eteq s) : ContMDiffWithinAt I I' n f t x
参数：hf : ContMDiffWithinAt I I' n f s x；hts : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.mono_of_mem_nhdsWithin`：ContMDiffWithinAt.mono_of_mem_
nhdsWithin (hf : ContMDiffWithinAt I I' n f s x) (hts : s in 𝓝[t] x) : ContMDiff
WithinAt I I' n f t x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem ContMDiffWithinAt.mono (hf : ContMDiffWithinAt I I' n f s x) (hts : t ⊆ s) :
    ContMDiffWithinAt I I' n f t x :=
  hf.mono_of_mem_nhdsWithin <| mem_of_superset self_mem_nhdsWithin hts
/-
**contMDiffWithinAt_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) : ContMDiffWithinAt I I' n f
 s x ↔ ContMDiffWithinAt I I' n f t x
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_set`：liftPro
pWithinAt_congr_set (hu : s =ᶠ[𝓝 x] t) : LiftPropWithinAt P g s x ↔ LiftPropWith
inAt P g t x
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
theorem contMDiffWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    ContMDiffWithinAt I I' n f s x ↔ ContMDiffWithinAt I I' n f t x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_set h
/-
**ContMDiffWithinAt.congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.congr_set (h : ContMDiffWithinAt I I' n f s x) (hst : s 
=ᶠ[𝓝 x] t) : ContMDiffWithinAt I I' n f t x
参数：h : ContMDiffWithinAt I I' n f s x；hst : s =ᶠ[𝓝 x] t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contMDiffWithinAt_congr_set`：contMDiffWithinAt_congr_set (h : s =ᶠ[𝓝 x] 
t) : ContMDiffWithinAt I I' n f s x ↔ ContMDiffWithinAt I I' n f t x
-/
theorem ContMDiffWithinAt.congr_set (h : ContMDiffWithinAt I I' n f s x) (hst : s =ᶠ[𝓝 x] t) :
    ContMDiffWithinAt I I' n f t x :=
  (contMDiffWithinAt_congr_set hst).1 h
/-
**contMDiffWithinAt_insert_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_insert_self : ContMDiffWithinAt I I' n f (insert x s) x 
↔ ContMDiffWithinAt I I' n f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `contDiffWithinAt_congr_set`：contDiffWithinAt_congr_set {t : Set E} (hst 
: s =ᶠ[𝓝 x] t) : ContDiffWithinAt 𝕜 n f s x ↔ ContDiffWithinAt 𝕜 n f t x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `nhdsWithin_insert`：nhdsWithin_insert (a : α) (s : Set α) : 𝓝[insert a s]
 a = pure a ⊔ 𝓝[s] a
· 使用定理 `Filter.map_sup`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : Filter α} {m : 
α → β},   Filter.map m (f₁ ⊔ f₂) = Filter.map m f₁ ⊔ Filter.map m f₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `contDiffWithinAt_insert_self`：contDiffWithinAt_insert_self : ContDiffWit
hinAt 𝕜 n f (insert x s) x ↔ ContDiffWithinAt 𝕜 n f s x
-/
theorem contMDiffWithinAt_insert_self :
    ContMDiffWithinAt I I' n f (insert x s) x ↔ ContMDiffWithinAt I I' n f s x := by
  simp only [contMDiffWithinAt_iff, continuousWithinAt_insert_self]
  refine Iff.rfl.and <| (contDiffWithinAt_congr_set ?_).trans contDiffWithinAt_insert_self
  simp only [← map_extChartAt_nhdsWithin, nhdsWithin_insert, Filter.map_sup, Filter.map_pure,
    ← nhdsWithin_eq_iff_eventuallyEq]

alias ⟨ContMDiffWithinAt.of_insert, _⟩ := contMDiffWithinAt_insert_self

-- TODO: use `alias` again once it can make protected theorems
/-
**ContMDiffWithinAt.insert** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] {f : M → M'} {s : Set M} {x : M}   {n :
 WithTop ℕ∞}, ContMDiffWithinAt I I' n f s x → ContMDiffWithinAt I I' n f (inser
t x s) x
参数：insert x s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contMDiffWithinAt_insert_self`：contMDiffWithinAt_insert_self : ContMDiff
WithinAt I I' n f (insert x s) x ↔ ContMDiffWithinAt I I' n f s x
-/
protected theorem ContMDiffWithinAt.insert (h : ContMDiffWithinAt I I' n f s x) :
    ContMDiffWithinAt I I' n f (insert x s) x :=
  contMDiffWithinAt_insert_self.2 h

/-- Being `C^n` in a set only depends on the germ of the set. Version where one only requires
the two sets to coincide locally in the complement of a point `y`. -/
/-
**contMDiffWithinAt_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : ContMDiffWi
thinAt I I' n f s x ↔ ContMDiffWithinAt I I' n f t x
参数：y : M；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.t1Space`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffWithinAt_insert_self`：contMDiffWithinAt_insert_self : ContMDiff
WithinAt I I' n f (insert x s) x ↔ ContMDiffWithinAt I I' n f s x
· 使用定理 `contMDiffWithinAt_congr_set`：contMDiffWithinAt_congr_set (h : s =ᶠ[𝓝 x] 
t) : ContMDiffWithinAt I I' n f s x ↔ ContMDiffWithinAt I I' n f t x
· 使用引理 `eventuallyEq_insert`：eventuallyEq_insert [T1Space X] {s t : Set X} {x y 
: X} (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : (insert x s : Set X) =ᶠ[𝓝 x] (insert x t : Set X)

--- 原说明 ---
Being `C^n` in a set only depends on the germ of the set. Version where one only
 requires
the two sets to coincide locally in the complement of a point `y`.
-/
theorem contMDiffWithinAt_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    ContMDiffWithinAt I I' n f s x ↔ ContMDiffWithinAt I I' n f t x := by
  have : T1Space M := I.t1Space M
  rw [← contMDiffWithinAt_insert_self (s := s), ← contMDiffWithinAt_insert_self (s := t)]
  exact contMDiffWithinAt_congr_set (eventuallyEq_insert h)
/-
**ContMDiffAt.contMDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] {f : M → M'} {s : Set M} {x : M}   {n :
 WithTop ℕ∞}, ContMDiffAt I I' n f x → ContMDiffWithinAt I I' n f s x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.mono`：ContMDiffWithinAt.mono (hf : ContMDiffWithinAt I
 I' n f s x) (hts : t subseteq s) : ContMDiffWithinAt I I' n f t x
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
protected theorem ContMDiffAt.contMDiffWithinAt (hf : ContMDiffAt I I' n f x) :
    ContMDiffWithinAt I I' n f s x :=
  ContMDiffWithinAt.mono hf (subset_univ _)
/-
**ContMDiffOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : t subseteq s) : Cont
MDiffOn I I' n f t
参数：hf : ContMDiffOn I I' n f s；hts : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.mono`：ContMDiffWithinAt.mono (hf : ContMDiffWithinAt I
 I' n f s x) (hts : t subseteq s) : ContMDiffWithinAt I I' n f t x
-/
theorem ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : t ⊆ s) : ContMDiffOn I I' n f t :=
  fun x hx => (hf x (hts hx)).mono hts
/-
**ContMDiff.contMDiffOn** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiff`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] {f : M → M'} {s : Set M}   {n : WithTop
 ℕ∞}, ContMDiff I I' n f → ContMDiffOn I I' n f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
-/
protected theorem ContMDiff.contMDiffOn (hf : ContMDiff I I' n f) : ContMDiffOn I I' n f s :=
  fun x _ => (hf x).contMDiffWithinAt
/-
**contMDiffWithinAt_inter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_inter' (ht : t in 𝓝[s] x) : ContMDiffWithinAt I I' n f (
s inter t) x ↔ ContMDiffWithinAt I I' n f s x
参数：ht : t in 𝓝[s] x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_inter'`：liftPropWi
thinAt_inter' (ht : t in 𝓝[s] x) : LiftPropWithinAt P g (s inter t) x ↔ LiftProp
WithinAt P g s x
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
theorem contMDiffWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    ContMDiffWithinAt I I' n f (s ∩ t) x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_inter' ht
/-
**contMDiffWithinAt_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_inter (ht : t in 𝓝 x) : ContMDiffWithinAt I I' n f (s in
ter t) x ↔ ContMDiffWithinAt I I' n f s x
参数：ht : t in 𝓝 x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_inter`：liftPropWit
hinAt_inter (ht : t in 𝓝 x) : LiftPropWithinAt P g (s inter t) x ↔ LiftPropWithi
nAt P g s x
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
theorem contMDiffWithinAt_inter (ht : t ∈ 𝓝 x) :
    ContMDiffWithinAt I I' n f (s ∩ t) x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_inter ht
/-
**ContMDiffWithinAt.contMDiffAt** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] {f : M → M'} {s : Set M} {x : M}   {n :
 WithTop ℕ∞}, ContMDiffWithinAt I I' n f s x → s ∈ nhds x → ContMDiffAt I I' n f
 x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropAt_of_liftPropWithinAt`：lif
tPropAt_of_liftPropWithinAt (h : LiftPropWithinAt P g s x) (hs : s in 𝓝 x) : Lif
tPropAt P g x
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
protected theorem ContMDiffWithinAt.contMDiffAt
    (h : ContMDiffWithinAt I I' n f s x) (ht : s ∈ 𝓝 x) :
    ContMDiffAt I I' n f x :=
  (contDiffWithinAt_localInvariantProp n).liftPropAt_of_liftPropWithinAt h ht
/-
**ContMDiffOn.contMDiffAt** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] {f : M → M'} {s : Set M} {x : M}   {n :
 WithTop ℕ∞}, ContMDiffOn I I' n f s → s ∈ nhds x → ContMDiffAt I I' n f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
protected theorem ContMDiffOn.contMDiffAt (h : ContMDiffOn I I' n f s) (hx : s ∈ 𝓝 x) :
    ContMDiffAt I I' n f x :=
  (h x (mem_of_mem_nhds hx)).contMDiffAt hx
/-
**contMDiffOn_iff_source_of_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_iff_source_of_mem_maximalAtlas (he : e in maximalAtlas I n M) 
(hs : s subseteq e.source) : ContMDiffOn I I' n f s ↔ ContMDiffOn 𝓘(𝕜, E) I' n (
f ∘ (e.extend I).symm) (e.extend I '' s)
参数：he : e in maximalAtlas I n M；hs : s subseteq e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `contMDiffWithinAt_iff_source_of_mem_maximalAtlas`：contMDiffWithinAt_iff_
source_of_mem_maximalAtlas (he : e in maximalAtlas I n M) (hx : x in e.source) :
 ContMDiffWithinAt I I' n f s x ↔ Cont…
· 使用定理 `contMDiffWithinAt_congr_set`：contMDiffWithinAt_congr_set (h : s =ᶠ[𝓝 x] 
t) : ContMDiffWithinAt I I' n f s x ↔ ContMDiffWithinAt I I' n f t x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `OpenPartialHomeomorph.extend_symm_preimage_inter_range_eventuallyEq`：ext
end_symm_preimage_inter_range_eventuallyEq {s : Set M} {x : M} (hs : s subseteq 
f.source) (hx : x in f.source) : ((f.extend I).symm ⁻¹' s…
-/
theorem contMDiffOn_iff_source_of_mem_maximalAtlas
    (he : e ∈ maximalAtlas I n M) (hs : s ⊆ e.source) :
    ContMDiffOn I I' n f s ↔
      ContMDiffOn 𝓘(𝕜, E) I' n (f ∘ (e.extend I).symm) (e.extend I '' s) := by
  simp_rw [ContMDiffOn, Set.forall_mem_image]
  refine forall₂_congr fun x hx => ?_
  rw [contMDiffWithinAt_iff_source_of_mem_maximalAtlas he (hs hx)]
  apply contMDiffWithinAt_congr_set
  simp_rw [e.extend_symm_preimage_inter_range_eventuallyEq hs (hs hx)]

/-- A function is `C^n` within a set at a point, for `n : ℕ` or `n = ω`,
if and only if it is `C^n` on a neighborhood of this point. -/
/-
**contMDiffWithinAt_iff_contMDiffOn_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_iff_contMDiffOn_nhds [IsManifold I n M] [IsManifold I' n
 M'] (hn : n != ∞) : ContMDiffWithinAt I I' n f s x ↔ exists u in 𝓝[insert x s] 
x, ContMDiffOn I I' n f u
参数：hn : n != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `ContDiffWithinAt.contDiffOn`：ContDiffWithinAt.contDiffOn (hm : m <= n) (
h' : m = ∞ -> n = ω) (h : ContDiffWithinAt 𝕜 n f s x) : exists u in 𝓝[insert x s
] x, u subseteq i…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contMDiffWithinAt_iff'`：contMDiffWithinAt_iff' : ContMDiffWithinAt I I' 
n f s x ↔ ContinuousWithinAt f s x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘
 f ∘ (extCha…
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
· 使用定理 `extChartAt_to_inv`：extChartAt_to_inv (x : M) : (extChartAt I x).symm ((e
xtChartAt I x) x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_extChartAt_symm_nhdsWithin`：map_extChartAt_symm_nhdsWithin (x : M) :
 map (extChartAt I x).symm (𝓝[(extChartAt I x).symm ⁻¹' s inter range I] extChar
tAt I x x) = 𝓝[s] x
· 使用定理 `ContinuousWithinAt.nhdsWithin_extChartAt_symm_preimage_inter_range`：Cont
inuousWithinAt.nhdsWithin_extChartAt_symm_preimage_inter_range {f : M -> M'} {x 
: M} (hc : ContinuousWithinAt f s x) : 𝓝[(extChartAt I x…
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `PartialEquiv.map_target`：map_target {x : β} (h : x in e.target) : e.symm
 x in e.source
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `contMDiffOn_iff_of_subset_source'`：contMDiffOn_iff_of_subset_source' [Is
Manifold I n M] [IsManifold I' n M'] (hs : s subseteq (extChartAt I x).source) (
h2s : MapsTo f s (extCh…
· 使用定理 `PartialEquiv.image_symm_image_of_subset_target`：image_symm_image_of_subs
et_target {s : Set β} (h : s subseteq e.target) : e '' e.symm '' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `ContMDiffWithinAt.mono_of_mem_nhdsWithin`：ContMDiffWithinAt.mono_of_mem_
nhdsWithin (hf : ContMDiffWithinAt I I' n f s x) (hts : s in 𝓝[t] x) : ContMDiff
WithinAt I I' n f t x
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
A function is `C^n` within a set at a point, for `n : ℕ` or `n = ω`,
if and only if it is `C^n` on a neighborhood of this point.
-/
theorem contMDiffWithinAt_iff_contMDiffOn_nhds
    [IsManifold I n M] [IsManifold I' n M'] (hn : n ≠ ∞) :
    ContMDiffWithinAt I I' n f s x ↔ ∃ u ∈ 𝓝[insert x s] x, ContMDiffOn I I' n f u := by
  -- WLOG, `x ∈ s`, otherwise we add `x` to `s`
  wlog hxs : x ∈ s generalizing s
  · rw [← contMDiffWithinAt_insert_self, this (mem_insert _ _), insert_idem]
  rw [insert_eq_of_mem hxs]
  -- The `←` implication is trivial
  refine ⟨fun h ↦ ?_, fun ⟨u, hmem, hu⟩ ↦
    (hu _ (mem_of_mem_nhdsWithin hxs hmem)).mono_of_mem_nhdsWithin hmem⟩
  -- The property is true in charts. Let `v` be a good neighborhood in the chart where the function
  -- is `Cⁿ`.
  rcases (contMDiffWithinAt_iff'.1 h).2.contDiffOn le_rfl (by simp [hn]) with ⟨v, hmem, hsub, hv⟩
  have hxs' : extChartAt I x x ∈ (extChartAt I x).target ∩
      (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' (f x)).source) :=
    ⟨(extChartAt I x).map_source (mem_extChartAt_source _), by rwa [extChartAt_to_inv], by
      rw [extChartAt_to_inv]; apply mem_extChartAt_source⟩
  rw [insert_eq_of_mem hxs'] at hmem hsub
  -- Then `(extChartAt I x).symm '' v` is the neighborhood we are looking for.
  refine ⟨(extChartAt I x).symm '' v, ?_, ?_⟩
  · rw [← map_extChartAt_symm_nhdsWithin (I := I),
      h.1.nhdsWithin_extChartAt_symm_preimage_inter_range (I := I) (I' := I')]
    exact image_mem_map hmem
  · have hv₁ : (extChartAt I x).symm '' v ⊆ (extChartAt I x).source :=
      image_subset_iff.2 fun y hy ↦ (extChartAt I x).map_target (hsub hy).1
    have hv₂ : MapsTo f ((extChartAt I x).symm '' v) (extChartAt I' (f x)).source := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hsub hy).2.2
    rwa [contMDiffOn_iff_of_subset_source' hv₁ hv₂, PartialEquiv.image_symm_image_of_subset_target]
    exact hsub.trans inter_subset_left

/-- If a function is `C^m` within a set at a point, for some finite `m`, then it is `C^m` within
this set on an open set around the basepoint. -/
/-
**ContMDiffWithinAt.contMDiffOn'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.contMDiffOn' [IsManifold I n M] [IsManifold I' n M'] (hm
 : m <= n) (h' : m = ∞ -> n = ω) (h : ContMDiffWithinAt I I' n f s x) : exists u
, IsOpen u ∧ x in u ∧ ContMDiffOn I I' m f (insert x s inter u)
参数：hm : m <= n；h' : m = ∞ -> n = ω；h : ContMDiffWithinAt I I' n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsManifold.of_le`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contMDiffWithinAt_iff_contMDiffOn_nhds`：contMDiffWithinAt_iff_contMDiffO
n_nhds [IsManifold I n M] [IsManifold I' n M'] (hn : n != ∞) : ContMDiffWithinAt
 I I' n f s x ↔ exists u in …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ContMDiffWithinAt.of_le`：ContMDiffWithinAt.of_le (hf : ContMDiffWithinAt
 I I' n f s x) (le : m <= n) : ContMDiffWithinAt I I' m f s x
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `ContMDiffOn.mono`：ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : 
t subseteq s) : ContMDiffOn I I' n f t
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContMDiffOn.of_le`：ContMDiffOn.of_le (hf : ContMDiffOn I I' n f s) (le :
 m <= n) : ContMDiffOn I I' m f s

--- 原说明 ---
If a function is `C^m` within a set at a point, for some finite `m`, then it is 
`C^m` within
this set on an open set around the basepoint.
-/
theorem ContMDiffWithinAt.contMDiffOn'
    [IsManifold I n M] [IsManifold I' n M']
    (hm : m ≤ n) (h' : m = ∞ → n = ω)
    (h : ContMDiffWithinAt I I' n f s x) :
    ∃ u, IsOpen u ∧ x ∈ u ∧ ContMDiffOn I I' m f (insert x s ∩ u) := by
  have : IsManifold I m M := .of_le hm
  have : IsManifold I' m M' := .of_le hm
  match m with
  | (m : ℕ) | ω =>
    rcases (contMDiffWithinAt_iff_contMDiffOn_nhds (by simp)).1 (h.of_le hm) with ⟨t, ht, h't⟩
    rcases mem_nhdsWithin.1 ht with ⟨u, u_open, xu, hu⟩
    rw [inter_comm] at hu
    exact ⟨u, u_open, xu, h't.mono hu⟩
  | ∞ =>
    rcases (contMDiffWithinAt_iff_contMDiffOn_nhds (by simp [h'])).1 h with ⟨t, ht, h't⟩
    rcases mem_nhdsWithin.1 ht with ⟨u, u_open, xu, hu⟩
    rw [inter_comm] at hu
    exact ⟨u, u_open, xu, (h't.mono hu).of_le hm⟩

/-- If a function is `C^m` within a set at a point, for some finite `m`, then it is `C^m` within
this set on a neighborhood of the basepoint. -/
/-
**ContMDiffWithinAt.contMDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.contMDiffOn [IsManifold I n M] [IsManifold I' n M'] (hm 
: m <= n) (h' : m = ∞ -> n = ω) (h : ContMDiffWithinAt I I' n f s x) : exists u 
in 𝓝[insert x s] x, u subseteq insert x s ∧ ContMDiffOn I I' m f u
参数：hm : m <= n；h' : m = ∞ -> n = ω；h : ContMDiffWithinAt I I' n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.contMDiffOn'`：ContMDiffWithinAt.contMDiffOn' [IsManifo
ld I n M] [IsManifold I' n M'] (hm : m <= n) (h' : m = ∞ -> n = ω) (h : ContMDif
fWithinAt I I' n f s…
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s

--- 原说明 ---
If a function is `C^m` within a set at a point, for some finite `m`, then it is 
`C^m` within
this set on a neighborhood of the basepoint.
-/
theorem ContMDiffWithinAt.contMDiffOn
    [IsManifold I n M] [IsManifold I' n M']
    (hm : m ≤ n) (h' : m = ∞ → n = ω)
    (h : ContMDiffWithinAt I I' n f s x) :
    ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ ContMDiffOn I I' m f u := by
  let ⟨_u, uo, xu, h⟩ := h.contMDiffOn' hm h'
  exact ⟨_, inter_mem_nhdsWithin _ (uo.mem_nhds xu), inter_subset_left, h⟩

/-- A function is `C^n` at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
/-
**contMDiffAt_iff_contMDiffOn_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_iff_contMDiffOn_nhds [IsManifold I n M] [IsManifold I' n M'] (
hn : n != ∞) : ContMDiffAt I I' n f x ↔ exists u in 𝓝 x, ContMDiffOn I I' n f u
参数：hn : n != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_iff_contMDiffOn_nhds`：contMDiffWithinAt_iff_contMDiffO
n_nhds [IsManifold I n M] [IsManifold I' n M'] (hn : n != ∞) : ContMDiffWithinAt
 I I' n f s x ↔ exists u in …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A function is `C^n` at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point.
-/
theorem contMDiffAt_iff_contMDiffOn_nhds
    [IsManifold I n M] [IsManifold I' n M'] (hn : n ≠ ∞) :
    ContMDiffAt I I' n f x ↔ ∃ u ∈ 𝓝 x, ContMDiffOn I I' n f u := by
  simp [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_contMDiffOn_nhds hn, nhdsWithin_univ]

/-- Note: This does not hold for `n = ∞`. `f` being `C^∞` at `x` means that for every `n`, `f` is
`C^n` on some neighborhood of `x`, but this neighborhood can depend on `n`. -/
/-
**contMDiffAt_iff_contMDiffAt_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_iff_contMDiffAt_nhds [IsManifold I n M] [IsManifold I' n M'] (
hn : n != ∞) : ContMDiffAt I I' n f x ↔ forallᶠ x' in 𝓝 x, ContMDiffAt I I' n f 
x'
参数：hn : n != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffAt_iff_contMDiffOn_nhds`：contMDiffAt_iff_contMDiffOn_nhds [IsMa
nifold I n M] [IsManifold I' n M'] (hn : n != ∞) : ContMDiffAt I I' n f x ↔ exis
ts u in 𝓝 x, ContMDiff…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_mem_nhds_iff`：eventually_mem_nhds_iff : (forallᶠ x' in 𝓝 x, s
 in 𝓝 x') ↔ s in 𝓝 x
· 使用定理 `ContMDiffWithinAt.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x

--- 原说明 ---
Note: This does not hold for `n = ∞`. `f` being `C^∞` at `x` means that for ever
y `n`, `f` is
`C^n` on some neighborhood of `x`, but this neighborhood can depend on `n`.
-/
theorem contMDiffAt_iff_contMDiffAt_nhds
    [IsManifold I n M] [IsManifold I' n M'] (hn : n ≠ ∞) :
    ContMDiffAt I I' n f x ↔ ∀ᶠ x' in 𝓝 x, ContMDiffAt I I' n f x' := by
  refine ⟨?_, fun h => h.self_of_nhds⟩
  rw [contMDiffAt_iff_contMDiffOn_nhds hn]
  rintro ⟨u, hu, h⟩
  refine (eventually_mem_nhds_iff.mpr hu).mono fun x' hx' => ?_
  exact (h x' <| mem_of_mem_nhds hx').contMDiffAt hx'

/-- Note: This does not hold for `n = ∞`. `f` being `C^∞` at `x` means that for every `n`, `f` is
`C^n` on some neighborhood of `x`, but this neighborhood can depend on `n`. -/
/-
**contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin [IsManifold I n M] [IsM
anifold I' n M'] (hn : n != ∞) : ContMDiffWithinAt I I' n f s x ↔ forallᶠ x' in 
𝓝[insert x s] x, ContMDiffWithinAt I I' n f s x'
参数：hn : n != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_iff_contMDiffOn_nhds`：contMDiffWithinAt_iff_contMDiffO
n_nhds [IsManifold I n M] [IsManifold I' n M'] (hn : n != ∞) : ContMDiffWithinAt
 I I' n f s x ↔ exists u in …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_mem_nhdsWithin_iff`：eventually_mem_nhdsWithin_iff {x : α} {s 
t : Set α} : (forallᶠ x' in 𝓝[s] x, t in 𝓝[s] x') ↔ t in 𝓝[s] x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ContMDiffWithinAt.mono_of_mem_nhdsWithin`：ContMDiffWithinAt.mono_of_mem_
nhdsWithin (hf : ContMDiffWithinAt I I' n f s x) (hts : s in 𝓝[t] x) : ContMDiff
WithinAt I I' n f t x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s

--- 原说明 ---
Note: This does not hold for `n = ∞`. `f` being `C^∞` at `x` means that for ever
y `n`, `f` is
`C^n` on some neighborhood of `x`, but this neighborhood can depend on `n`.
-/
theorem contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin
    [IsManifold I n M] [IsManifold I' n M'] (hn : n ≠ ∞) :
    ContMDiffWithinAt I I' n f s x ↔
      ∀ᶠ x' in 𝓝[insert x s] x, ContMDiffWithinAt I I' n f s x' := by
  refine ⟨?_, fun h ↦ mem_of_mem_nhdsWithin (mem_insert x s) h⟩
  rw [contMDiffWithinAt_iff_contMDiffOn_nhds hn]
  rintro ⟨u, hu, h⟩
  filter_upwards [hu, eventually_mem_nhdsWithin_iff.mpr hu] with x' h'x' hx'
  apply (h x' h'x').mono_of_mem_nhdsWithin
  exact nhdsWithin_mono _ (subset_insert x s) hx'

/-! ### Congruence lemmas -/

/-
**ContMDiffWithinAt.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.congr (h : ContMDiffWithinAt I I' n f s x) (h₁ : forall 
y in s, f₁ y = f y) (hx : f₁ x = f x) : ContMDiffWithinAt I I' n f₁ s x
参数：h : ContMDiffWithinAt I I' n f s x；h₁ : forall y in s, f₁ y = f y；hx : f₁ x =
 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr`：liftPropWit
hinAt_congr (h : LiftPropWithinAt P g s x) (h₁ : forall y in s, g' y = g y) (hx 
: g' x = g x) : LiftPropWithinAt P g' s x
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …

--- 原说明 ---
### Congruence lemmas
-/
theorem ContMDiffWithinAt.congr (h : ContMDiffWithinAt I I' n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y)
    (hx : f₁ x = f x) : ContMDiffWithinAt I I' n f₁ s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr h h₁ hx

/-- Version of `ContMDiffWithinAt.congr` where `x` need not be contained in `s`,
but `f` and `f₁` are equal on a set containing both. -/
/-
**ContMDiffWithinAt.congr'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.congr' (h : ContMDiffWithinAt I I' n f s x) (h₁ : forall
 y in t, f₁ y = f y) (hst : s subseteq t) (hxt : x in t) : ContMDiffWithinAt I I
' n f₁ s x
参数：h : ContMDiffWithinAt I I' n f s x；h₁ : forall y in t, f₁ y = f y；hst : s sub
seteq t；hxt : x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.congr`：ContMDiffWithinAt.congr (h : ContMDiffWithinAt 
I I' n f s x) (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) : ContMDiffWith
inAt I I' n f…

--- 原说明 ---
Version of `ContMDiffWithinAt.congr` where `x` need not be contained in `s`,
but `f` and `f₁` are equal on a set containing both.
-/
theorem ContMDiffWithinAt.congr' (h : ContMDiffWithinAt I I' n f s x) (h₁ : ∀ y ∈ t, f₁ y = f y)
    (hst : s ⊆ t) (hxt : x ∈ t) :
    ContMDiffWithinAt I I' n f₁ s x :=
  h.congr (fun _y hy ↦ h₁ _ (hst hy)) (h₁ x hxt)
/-
**contMDiffWithinAt_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_congr (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x)
 : ContMDiffWithinAt I I' n f₁ s x ↔ ContMDiffWithinAt I I' n f s x
参数：h₁ : forall y in s, f₁ y = f y；hx : f₁ x = f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_iff`：liftPro
pWithinAt_congr_iff (h₁ : forall y in s, g' y = g y) (hx : g' x = g x) : LiftPro
pWithinAt P g' s x ↔ LiftPropWithinAt P g s x
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
theorem contMDiffWithinAt_congr (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : f₁ x = f x) :
    ContMDiffWithinAt I I' n f₁ s x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_iff h₁ hx
/-
**ContMDiffWithinAt.congr_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.congr_of_mem (h : ContMDiffWithinAt I I' n f s x) (h₁ : 
forall y in s, f₁ y = f y) (hx : x in s) : ContMDiffWithinAt I I' n f₁ s x
参数：h : ContMDiffWithinAt I I' n f s x；h₁ : forall y in s, f₁ y = f y；hx : x in s
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_of_mem`：lift
PropWithinAt_congr_of_mem (h : LiftPropWithinAt P g s x) (h₁ : forall y in s, g'
 y = g y) (hx : x in s) : LiftPropWithinAt P g' s x
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
theorem ContMDiffWithinAt.congr_of_mem
    (h : ContMDiffWithinAt I I' n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : x ∈ s) :
    ContMDiffWithinAt I I' n f₁ s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_of_mem h h₁ hx
/-
**contMDiffWithinAt_congr_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_congr_of_mem (h₁ : forall y in s, f₁ y = f y) (hx : x in
 s) : ContMDiffWithinAt I I' n f₁ s x ↔ ContMDiffWithinAt I I' n f s x
参数：h₁ : forall y in s, f₁ y = f y；hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_iff_of_mem`：
liftPropWithinAt_congr_iff_of_mem (h₁ : forall y in s, g' y = g y) (hx : x in s)
 : LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
theorem contMDiffWithinAt_congr_of_mem (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : x ∈ s) :
    ContMDiffWithinAt I I' n f₁ s x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_iff_of_mem h₁ hx
/-
**ContMDiffWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.congr_of_eventuallyEq (h : ContMDiffWithinAt I I' n f s 
x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : ContMDiffWithinAt I I' n f₁ s x
参数：h : ContMDiffWithinAt I I' n f s x；h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_of_eventuall
yEq`：liftPropWithinAt_congr_of_eventuallyEq (h : LiftPropWithinAt P g s x) (h₁ :
 g' =ᶠ[𝓝[s] x] g) (hx : g' x = g x) : LiftPropWithinAt P g' s x
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
theorem ContMDiffWithinAt.congr_of_eventuallyEq (h : ContMDiffWithinAt I I' n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : ContMDiffWithinAt I I' n f₁ s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_of_eventuallyEq h h₁ hx
/-
**ContMDiffWithinAt.congr_of_eventuallyEq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.congr_of_eventuallyEq_of_mem (h : ContMDiffWithinAt I I'
 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) : ContMDiffWithinAt I I' n f₁ s x
参数：h : ContMDiffWithinAt I I' n f s x；h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_of_eventuall
yEq_of_mem`：liftPropWithinAt_congr_of_eventuallyEq_of_mem (h : LiftPropWithinAt 
P g s x) (h₁ : g' =ᶠ[𝓝[s] x] g) (h₂ : x in s) : LiftPropWithinAt P g' s …
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
theorem ContMDiffWithinAt.congr_of_eventuallyEq_of_mem (h : ContMDiffWithinAt I I' n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : ContMDiffWithinAt I I' n f₁ s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_of_eventuallyEq_of_mem h h₁ hx
/-
**Filter.EventuallyEq.contMDiffWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.contMDiffWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ 
x = f x) : ContMDiffWithinAt I I' n f₁ s x ↔ ContMDiffWithinAt I I' n f s x
参数：h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_iff_of_event
uallyEq`：liftPropWithinAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝[s] x] g) (hx :
 g' x = g x) : LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
theorem Filter.EventuallyEq.contMDiffWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    ContMDiffWithinAt I I' n f₁ s x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_iff_of_eventuallyEq h₁ hx
/-
**ContMDiffAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.congr_of_eventuallyEq (h : ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ
[𝓝 x] f) : ContMDiffAt I I' n f₁ x
参数：h : ContMDiffAt I I' n f x；h₁ : f₁ =ᶠ[𝓝 x] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropAt_congr_of_eventuallyEq`：l
iftPropAt_congr_of_eventuallyEq (h : LiftPropAt P g x) (h₁ : g' =ᶠ[𝓝 x] g) : Lif
tPropAt P g' x
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
theorem ContMDiffAt.congr_of_eventuallyEq (h : ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    ContMDiffAt I I' n f₁ x :=
  (contDiffWithinAt_localInvariantProp n).liftPropAt_congr_of_eventuallyEq h h₁
/-
**Filter.EventuallyEq.contMDiffAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.contMDiffAt_iff (h₁ : f₁ =ᶠ[𝓝 x] f) : ContMDiffAt I I'
 n f₁ x ↔ ContMDiffAt I I' n f x
参数：h₁ : f₁ =ᶠ[𝓝 x] f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropAt_congr_iff_of_eventuallyE
q`：liftPropAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝 x] g) : LiftPropAt P g' x 
↔ LiftPropAt P g x
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
theorem Filter.EventuallyEq.contMDiffAt_iff (h₁ : f₁ =ᶠ[𝓝 x] f) :
    ContMDiffAt I I' n f₁ x ↔ ContMDiffAt I I' n f x :=
  (contDiffWithinAt_localInvariantProp n).liftPropAt_congr_iff_of_eventuallyEq h₁
/-
**ContMDiffOn.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : forall y in s, f₁ y =
 f y) : ContMDiffOn I I' n f₁ s
参数：h : ContMDiffOn I I' n f s；h₁ : forall y in s, f₁ y = f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropOn_congr`：liftPropOn_congr 
(h : LiftPropOn P g s) (h₁ : forall y in s, g' y = g y) : LiftPropOn P g' s
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
theorem ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : ∀ y ∈ s, f₁ y = f y) :
    ContMDiffOn I I' n f₁ s :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_congr h h₁
/-
**contMDiffOn_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_congr (h₁ : forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁
 s ↔ ContMDiffOn I I' n f s
参数：h₁ : forall y in s, f₁ y = f y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropOn_congr_iff`：liftPropOn_co
ngr_iff (h₁ : forall y in s, g' y = g y) : LiftPropOn P g' s ↔ LiftPropOn P g s
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
theorem contMDiffOn_congr (h₁ : ∀ y ∈ s, f₁ y = f y) :
    ContMDiffOn I I' n f₁ s ↔ ContMDiffOn I I' n f s :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_congr_iff h₁
/-
**ContMDiffOn.congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.congr_mono (hf : ContMDiffOn I I' n f s) (h₁ : forall y in s₁,
 f₁ y = f y) (hs : s₁ subseteq s) : ContMDiffOn I I' n f₁ s₁
参数：hf : ContMDiffOn I I' n f s；h₁ : forall y in s₁, f₁ y = f y；hs : s₁ subseteq 
s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `ContMDiffOn.mono`：ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : 
t subseteq s) : ContMDiffOn I I' n f t
-/
theorem ContMDiffOn.congr_mono (hf : ContMDiffOn I I' n f s) (h₁ : ∀ y ∈ s₁, f₁ y = f y)
    (hs : s₁ ⊆ s) : ContMDiffOn I I' n f₁ s₁ :=
  (hf.mono hs).congr h₁
/-
**ContMDiff.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.congr (h : ContMDiff I I' n f) (h₁ : forall y, f₁ y = f y) : Con
tMDiff I I' n f₁
参数：h : ContMDiff I I' n f；h₁ : forall y, f₁ y = f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffOn_univ`：contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDi
ff I I' n f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contMDiffOn_congr`：contMDiffOn_congr (h₁ : forall y in s, f₁ y = f y) : 
ContMDiffOn I I' n f₁ s ↔ ContMDiffOn I I' n f s
-/
theorem ContMDiff.congr (h : ContMDiff I I' n f) (h₁ : ∀ y, f₁ y = f y) :
    ContMDiff I I' n f₁ := by
  rw [← contMDiffOn_univ] at h ⊢
  exact (contMDiffOn_congr fun y _ ↦ h₁ y).mpr h
/-
**contMDiff_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_congr (h₁ : forall y, f₁ y = f y) : ContMDiff I I' n f₁ ↔ ContMD
iff I I' n f
参数：h₁ : forall y, f₁ y = f y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffOn_congr`：contMDiffOn_congr (h₁ : forall y in s, f₁ y = f y) : 
ContMDiffOn I I' n f₁ s ↔ ContMDiffOn I I' n f s
-/
theorem contMDiff_congr (h₁ : ∀ y, f₁ y = f y) :
    ContMDiff I I' n f₁ ↔ ContMDiff I I' n f := by
  simp_rw [← contMDiffOn_univ]
  exact contMDiffOn_congr fun y _ ↦ h₁ y

/-! ### Locality -/


/-- Being `C^n` is a local property. -/
/-
**contMDiffOn_of_locally_contMDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_of_locally_contMDiffOn (h : forall x in s, exists u, IsOpen u 
∧ x in u ∧ ContMDiffOn I I' n f (s inter u)) : ContMDiffOn I I' n f s
参数：h : forall x in s, exists u, IsOpen u ∧ x in u ∧ ContMDiffOn I I' n f (s inte
r u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropOn_of_locally_liftPropOn`：l
iftPropOn_of_locally_liftPropOn (h : forall x in s, exists u, IsOpen u ∧ x in u 
∧ LiftPropOn P g (s inter u)) : LiftPropOn P g s
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …

--- 原说明 ---
Being `C^n` is a local property.
-/
theorem contMDiffOn_of_locally_contMDiffOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ ContMDiffOn I I' n f (s ∩ u)) : ContMDiffOn I I' n f s :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_of_locally_liftPropOn h
/-
**contMDiff_of_locally_contMDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_of_locally_contMDiffOn (h : forall x, exists u, IsOpen u ∧ x in 
u ∧ ContMDiffOn I I' n f u) : ContMDiff I I' n f
参数：h : forall x, exists u, IsOpen u ∧ x in u ∧ ContMDiffOn I I' n f u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftProp_of_locally_liftPropOn`：lif
tProp_of_locally_liftPropOn (h : forall x, exists u, IsOpen u ∧ x in u ∧ LiftPro
pOn P g u) : LiftProp P g
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
theorem contMDiff_of_locally_contMDiffOn (h : ∀ x, ∃ u, IsOpen u ∧ x ∈ u ∧ ContMDiffOn I I' n f u) :
    ContMDiff I I' n f :=
  (contDiffWithinAt_localInvariantProp n).liftProp_of_locally_liftPropOn h
