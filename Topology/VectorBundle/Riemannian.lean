/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.Hom

/-! # Riemannian vector bundles

Given a real vector bundle over a topological space whose fibers are all endowed with an inner
product, we say that this bundle is Riemannian if the inner product depends continuously on the
base point.

We introduce a typeclass `[IsContinuousRiemannianBundle F E]` registering this property.
Under this assumption, we show that the inner product of two continuous maps into the same fibers
of the bundle is a continuous function.

If one wants to endow an existing vector bundle with a Riemannian metric, there is a subtlety:
the inner product space structure on the fibers should give rise to a topology on the fibers
which is defeq to the original one, to avoid diamonds. To do this, we introduce a
class `[RiemannianBundle E]` containing the data of an inner
product on the fibers defining the same topology as the original one. Given this class, we can
construct `NormedAddCommGroup` and `InnerProductSpace` instances on the fibers, compatible in a
defeq way with the initial topology. If the data used to register the instance `RiemannianBundle E`
depends continuously on the base point, we register automatically an instance of
`[IsContinuousRiemannianBundle F E]` (and similarly if the data is smooth).

The general theory should be built assuming `[IsContinuousRiemannianBundle F E]`, while the
`[RiemannianBundle E]` mechanism is only to build data in specific situations, for instance for
the tangent bundle. As instances related to Riemannian bundles are both costly and quite specific,
they are scoped to the `Bundle` namespace.

## Keywords
Vector bundle, Riemannian metric
-/

@[expose] public section

open Bundle ContinuousLinearMap Filter
open scoped Topology

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable (F E) in
/-- Consider a real vector bundle in which each fiber is endowed with an inner product.
We say that the bundle is *Riemannian* if the inner product depends continuously on the base point.
This assumption is spelled `IsContinuousRiemannianBundle F E` where `F` is the model fiber,
and `E : B → Type*` is the bundle. -/
/-
**IsContinuousRiemannianBundle** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{B : Type u_1} →   [inst : TopologicalSpace B] →     (F : Type u_2) →     
  [inst_1 : NormedAddCommGroup F] →         [inst_2 : NormedSpace ℝ F] →        
   (E : B → Type u_3) →             [inst_3 : TopologicalSpace (Bundle.TotalSpac
e F E)] →               [inst_4 : (x : B) → NormedAddCommGroup (E x)] →         
        [inst_5 : (x : B) → InnerProductSpace ℝ (E x)] →                   [inst
_6 : FiberBundle F E] → [VectorBundle ℝ F E] → Prop
参数：F : Type u_2；E : B → Type u_3；Bundle.TotalSpace F E；x : B；E x；x : B；E x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider a real vector bundle in which each fiber is endowed with an inner produ
ct.
We say that the bundle is *Riemannian* if the inner product depends continuously
 on the base point.
This assumption is spelled `IsContinuousRiemannianBundle F E` where `F` is the m
odel fiber,
and `E : B → Type*` is the bundle.
-/
class IsContinuousRiemannianBundle : Prop where
  /-- There exists a bilinear form, depending continuously on the basepoint and defining the
  inner product in the fibers. This is expressed as an existence statement so that it is Prop-valued
  in terms of existing data, the inner product on the fibers and the fiber bundle structure. -/
  exists_continuous : ∃ g : (Π x, E x →L[ℝ] E x →L[ℝ] ℝ),
    Continuous (fun (x : B) ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g x))
    ∧ ∀ (x : B) (v w : E x), ⟪v, w⟫ = g x v w

section Trivial

variable {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]

set_option backward.isDefEq.respectTransparency false in
/-- A trivial vector bundle, in which the model fiber has an inner product,
is a Riemannian bundle. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A trivial vector bundle, in which the model fiber has an inner product,
is a Riemannian bundle.
-/
instance : IsContinuousRiemannianBundle F₁ (Bundle.Trivial B F₁) := by
  refine ⟨fun x ↦ innerSL ℝ, ?_, fun x v w ↦ rfl⟩
  rw [continuous_iff_continuousAt]
  intro x
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  convert! continuousAt_const (y := innerSL ℝ)
  ext v w
  simp [hom_trivializationAt_apply, inCoordinates]

end Trivial

section Continuous

variable
  {M : Type*} [TopologicalSpace M] [h : IsContinuousRiemannianBundle F E]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}

/-- Given two continuous maps into the same fibers of a continuous Riemannian bundle,
their inner product is continuous. Version with `ContinuousWithinAt`. -/
/-
**ContinuousWithinAt.inner_bundle** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.inner_bundle (hv : ContinuousWithinAt (fun m => (v m : 
TotalSpace F E)) s x) (hw : ContinuousWithinAt (fun m => (w m : TotalSpace F E))
 s x) : ContinuousWithinAt (fun m => ⟪v m, w m⟫) s x
参数：hv : ContinuousWithinAt (fun m => (v m : TotalSpace F E)) s x；hw : Continuous
WithinAt (fun m => (w m : TotalSpace F E)) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsContinuousRiemannianBundle.exists_continuous`：∀ {B : Type u_1} {inst :
 TopologicalSpace B} {F : Type u_2} {inst_1 : NormedAddCommGroup F} {inst_2 : No
rmedSpace ℝ F}   {E : B → Type u_3} …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ContinuousWithinAt.clm_bundle_apply₂`：ContinuousWithinAt.clm_bundle_appl
y₂ (hψ : ContinuousWithinAt (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (E
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Given two continuous maps into the same fibers of a continuous Riemannian bundle
,
their inner product is continuous. Version with `ContinuousWithinAt`.
-/
lemma ContinuousWithinAt.inner_bundle
    (hv : ContinuousWithinAt (fun m ↦ (v m : TotalSpace F E)) s x)
    (hw : ContinuousWithinAt (fun m ↦ (w m : TotalSpace F E)) s x) :
    ContinuousWithinAt (fun m ↦ ⟪v m, w m⟫) s x := by
  rcases h.exists_continuous with ⟨g, g_cont, hg⟩
  have hf : ContinuousWithinAt b s x := by
    simp only [FiberBundle.continuousWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x :=
    (g_cont.continuousAt.comp_continuousWithinAt hf).clm_bundle_apply₂ (F₁ := F) (F₂ := F) hv hw
  simp only [FiberBundle.continuousWithinAt_totalSpace] at this
  exact this.2

/-- Given two continuous maps into the same fibers of a continuous Riemannian bundle,
their inner product is continuous. Version with `ContinuousAt`. -/
/-
**ContinuousAt.inner_bundle** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousAt.inner_bundle (hv : ContinuousAt (fun m => (v m : TotalSpace F
 E)) x) (hw : ContinuousAt (fun m => (w m : TotalSpace F E)) x) : ContinuousAt (
fun b => ⟪v b, w b⟫) x
参数：hv : ContinuousAt (fun m => (v m : TotalSpace F E)) x；hw : ContinuousAt (fun 
m => (w m : TotalSpace F E)) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.inner_bundle`：ContinuousWithinAt.inner_bundle (hv : C
ontinuousWithinAt (fun m => (v m : TotalSpace F E)) s x) (hw : ContinuousWithinA
t (fun m => (w m : To…

--- 原说明 ---
Given two continuous maps into the same fibers of a continuous Riemannian bundle
,
their inner product is continuous. Version with `ContinuousAt`.
-/
lemma ContinuousAt.inner_bundle
    (hv : ContinuousAt (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : ContinuousAt (fun m ↦ (w m : TotalSpace F E)) x) :
    ContinuousAt (fun b ↦ ⟪v b, w b⟫) x := by
  simp only [← continuousWithinAt_univ] at hv hw ⊢
  exact ContinuousWithinAt.inner_bundle hv hw

/-- Given two continuous maps into the same fibers of a continuous Riemannian bundle,
their inner product is continuous. Version with `ContinuousOn`. -/
/-
**ContinuousOn.inner_bundle** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.inner_bundle (hv : ContinuousOn (fun m => (v m : TotalSpace F
 E)) s) (hw : ContinuousOn (fun m => (w m : TotalSpace F E)) s) : ContinuousOn (
fun b => ⟪v b, w b⟫) s
参数：hv : ContinuousOn (fun m => (v m : TotalSpace F E)) s；hw : ContinuousOn (fun 
m => (w m : TotalSpace F E)) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.inner_bundle`：ContinuousWithinAt.inner_bundle (hv : C
ontinuousWithinAt (fun m => (v m : TotalSpace F E)) s x) (hw : ContinuousWithinA
t (fun m => (w m : To…

--- 原说明 ---
Given two continuous maps into the same fibers of a continuous Riemannian bundle
,
their inner product is continuous. Version with `ContinuousOn`.
-/
lemma ContinuousOn.inner_bundle
    (hv : ContinuousOn (fun m ↦ (v m : TotalSpace F E)) s)
    (hw : ContinuousOn (fun m ↦ (w m : TotalSpace F E)) s) :
    ContinuousOn (fun b ↦ ⟪v b, w b⟫) s :=
  fun x hx ↦ (hv x hx).inner_bundle (hw x hx)

/-- Given two continuous maps into the same fibers of a continuous Riemannian bundle,
their inner product is continuous. -/
/-
**Continuous.inner_bundle** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.inner_bundle (hv : Continuous (fun m => (v m : TotalSpace F E))
) (hw : Continuous (fun m => (w m : TotalSpace F E))) : Continuous (fun b => ⟪v 
b, w b⟫)
参数：hv : Continuous (fun m => (v m : TotalSpace F E))；hw : Continuous (fun m => (
w m : TotalSpace F E))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousAt.inner_bundle`：ContinuousAt.inner_bundle (hv : ContinuousAt 
(fun m => (v m : TotalSpace F E)) x) (hw : ContinuousAt (fun m => (w m : TotalSp
ace F E)) x) : …

--- 原说明 ---
Given two continuous maps into the same fibers of a continuous Riemannian bundle
,
their inner product is continuous.
-/
lemma Continuous.inner_bundle
    (hv : Continuous (fun m ↦ (v m : TotalSpace F E)))
    (hw : Continuous (fun m ↦ (w m : TotalSpace F E))) :
    Continuous (fun b ↦ ⟪v b, w b⟫) := by
  simp only [continuous_iff_continuousAt] at hv hw ⊢
  exact fun x ↦ (hv x).inner_bundle (hw x)

variable (F E)

/-- In a continuous Riemannian bundle, local changes of coordinates given by the trivialization at
a point distort the norm by a factor arbitrarily close to 1. -/
/-
**eventually_norm_symmL_trivializationAt_self_comp_lt** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：eventually_norm_symmL_trivializationAt_self_comp_lt (x : B) {r : Real} (hr
 : 1 < r) : forallᶠ y in 𝓝 x, ‖((trivializationAt F E x).symmL Real x) ∘L ((triv
ializationAt F E x).continuousLinearMapAt Real y)‖ < r
参数：x : B；hr : 1 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.tendsto_inf_left`：tendsto_inf_left {f : α -> β} {x₁ x₂ : Filter α
} {y : Filter β} (h : Tendsto f x₁ y) : Tendsto f (x₁ ⊓ x₂) y
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `inv_lt_one_of_one_lt₀`：inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
（共 183 条，此处仅展示前 30 条）

--- 原说明 ---
In a continuous Riemannian bundle, local changes of coordinates given by the tri
vialization at
a point distort the norm by a factor arbitrarily close to 1.
-/
lemma eventually_norm_symmL_trivializationAt_self_comp_lt (x : B) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ y in 𝓝 x, ‖((trivializationAt F E x).symmL ℝ x)
      ∘L ((trivializationAt F E x).continuousLinearMapAt ℝ y)‖ < r := by
  /- We will expand the definition of continuity of the inner product structure, in the chart.
  Denote `g' x` the metric in the fiber of `x`, read in the chart. For `y` close to `x`, then
  `g' y` and `g' x` are close. The inequality we have to prove reduces to comparing
  `g' y w w` and `g' x w w`, where `w` is the image in the chart of a tangent vector `v` at `y`.
  Their difference is controlled by `δ ‖w‖ ^ 2` for any small `δ > 0`. To conclude, we argue that
  `‖w‖` is comparable to the norm inside the fiber over `x`, i.e., `g' x w w`, because there
  is a continuous linear equivalence between these two spaces by definition of vector bundles. -/
  obtain ⟨r', hr', r'r⟩ : ∃ r', 1 < r' ∧ r' < r := exists_between hr
  have h'x : x ∈ (trivializationAt F E x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let G := (trivializationAt F E x).continuousLinearEquivAt ℝ x h'x
  let C := (‖(G : E x →L[ℝ] F)‖) ^ 2
  -- choose `δ` small enough that the computation below works when the metrics at `x` and `y`
  -- are `δ` close. When writing this proof, I have followed my nose in the computation, and
  -- recorded only in the end how small `δ` needs to be. The reader should skip the precise
  -- condition for now, as it doesn't give any useful insight.
  obtain ⟨δ, δpos, hδ⟩ : ∃ δ, 0 < δ ∧ (r' ^ 2)⁻¹ < 1 - δ * C := by
    have A : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    have B : Tendsto (fun δ ↦ 1 - δ * C) (𝓝[>] 0) (𝓝 (1 - 0 * C)) := by
      apply tendsto_inf_left
      exact tendsto_const_nhds.sub (tendsto_id.mul tendsto_const_nhds)
    have B' : ∀ᶠ δ in 𝓝[>] 0, (r' ^ 2)⁻¹ < 1 - δ * C := by
      apply (tendsto_order.1 B).1
      simpa using inv_lt_one_of_one_lt₀ (by nlinarith)
    exact (A.and B').exists
  rcases h.exists_continuous with ⟨g, g_cont, hg⟩
  let g' : B → F →L[ℝ] F →L[ℝ] ℝ := fun y ↦
    inCoordinates F E (F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] ℝ) x y x y (g y)
  have hg' : ContinuousAt g' x := by
    have W := g_cont.continuousAt (x := x)
    simp only [continuousAt_hom_bundle] at W
    exact W.2
  have : ∀ᶠ y in 𝓝 x, dist (g' y) (g' x) < δ := by
    rw [Metric.continuousAt_iff'] at hg'
    apply hg' _ δpos
  filter_upwards [this, (trivializationAt F E x).open_baseSet.mem_nhds h'x] with y hy h'y
  have : ‖g' x - g' y‖ ≤ δ := by rw [← dist_eq_norm']; exact hy.le
  -- To show that the norm of the composition is bounded by `r'`, we start from a vector
  -- `‖v‖`. We will show that its image has a controlled norm.
  apply (opNorm_le_bound _ (by linarith) (fun v ↦ ?_)).trans_lt r'r
  -- rewrite the norm of `‖v‖` and of its image in terms of norms in the model space
  let w := (trivializationAt F E x).continuousLinearMapAt ℝ y v
  suffices ‖((trivializationAt F E x).symmL ℝ x) w‖ ^ 2 ≤ r' ^ 2 * ‖v‖ ^ 2 from
    le_of_sq_le_sq (by simpa [mul_pow]) (by positivity)
  simp only [Trivialization.symmL_apply, mem_baseSet_trivializationAt,
    ← real_inner_self_eq_norm_sq, hg]
  have hgy : g y v v = g' y w w := by
    rw [inCoordinates_apply_eq₂ h'y h'y (Set.mem_univ _)]
    have A : ((trivializationAt F E x).symm y)
       ((trivializationAt F E x).linearMapAt ℝ y v) = v := by
      convert! ((trivializationAt F E x).continuousLinearEquivAt ℝ _ h'y).symm_apply_apply v
      simp [Trivialization.coe_continuousLinearEquivAt_eq _ h'y]
    simp [A, w]
  have hgx : g x ((trivializationAt F E x).symm x w) ((trivializationAt F E x).symm x w) =
      g' x w w := by
    rw [inCoordinates_apply_eq₂ h'x h'x (Set.mem_univ _)]
    simp
  rw [hgx, hgy]
  -- get a good control for the norms of `w` in the model space, using continuity
  have : g' x w w ≤ δ * C * g' x w w + g' y w w := calc
        g' x w w
    _ = (g' x - g' y) w w + g' y w w := by simp
    _ ≤ ‖g' x - g' y‖ * ‖w‖ * ‖w‖ + g' y w w := by
      grw [← le_opNorm₂, ← Real.le_norm_self]
    _ ≤ δ * ‖w‖ ^ 2 + g' y w w := by
      rw [pow_two, mul_assoc]; gcongr
    _ ≤ δ * (‖(G : E x →L[ℝ] F)‖ * ‖G.symm w‖) ^ 2 + g' y w w := by
      grw [← le_opNorm]
      simp
    _ = δ * C * ‖G.symm w‖ ^ 2 + g' y w w := by ring
    _ = δ * C * g x (G.symm w) (G.symm w) + g' y w w := by simp [← hg]
    _ = δ * C * g' x w w + g' y w w := by
      rw [← hgx]; rfl
  have : (1 - δ * C) * g' x w w ≤ g' y w w := by linarith
  rw [← (le_div_iff₀' (lt_of_le_of_lt (by positivity) hδ)), div_eq_inv_mul] at this
  grw [this]
  gcongr
  · rw [← hgy, ← hg, real_inner_self_eq_norm_sq]
    positivity
  · exact inv_le_of_inv_le₀ (by positivity) hδ.le

/-- In a continuous Riemannian bundle, the trivialization at a point is locally bounded in norm. -/
/-
**eventually_norm_trivializationAt_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eventually_norm_trivializationAt_lt (x : B) : exists C > 0, forallᶠ y in 𝓝
 x, ‖(trivializationAt F E x).continuousLinearMapAt Real y‖ < C
参数：x : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `eventually_norm_symmL_trivializationAt_self_comp_lt`：eventually_norm_sym
mL_trivializationAt_self_comp_lt (x : B) {r : Real} (hr : 1 < r) : forallᶠ y in 
𝓝 x, ‖((trivializationAt F E x).symmL Rea…
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bundle.Trivialization.symmL_apply`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x :
 B) → AddCommMonoid (E …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
In a continuous Riemannian bundle, the trivialization at a point is locally boun
ded in norm.
-/
lemma eventually_norm_trivializationAt_lt (x : B) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, ‖(trivializationAt F E x).continuousLinearMapAt ℝ y‖ < C := by
  refine ⟨(1 + ‖(trivializationAt F E x).continuousLinearMapAt ℝ  x‖) * 2, by positivity, ?_⟩
  filter_upwards [eventually_norm_symmL_trivializationAt_self_comp_lt F E x one_lt_two] with y hy
  have A : ((trivializationAt F E x).continuousLinearMapAt ℝ x) ∘L
      ((trivializationAt F E x).symmL ℝ x) = ContinuousLinearMap.id _ _ := by
    ext v
    have h'x : x ∈ (trivializationAt F E x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    simp only [Trivialization.continuousLinearMapAt_apply, Trivialization.symmL_apply,
      mem_baseSet_trivializationAt, comp_apply, id_apply]
    convert! ((trivializationAt F E x).continuousLinearEquivAt ℝ _ h'x).apply_symm_apply v
    simp [Trivialization.coe_continuousLinearEquivAt_eq _ h'x]
  have : (trivializationAt F E x).continuousLinearMapAt ℝ y =
    (ContinuousLinearMap.id _ _) ∘L ((trivializationAt F E x).continuousLinearMapAt ℝ y) := by simp
  grw [this, ← A, comp_assoc, opNorm_comp_le]
  gcongr
  linarith

/-- In a continuous Riemannian bundle, local changes of coordinates given by the trivialization at
a point distort the norm by a factor arbitrarily close to 1. -/
/-
**eventually_norm_symmL_trivializationAt_comp_self_lt** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：eventually_norm_symmL_trivializationAt_comp_self_lt (x : B) {r : Real} (hr
 : 1 < r) : forallᶠ y in 𝓝 x, ‖((trivializationAt F E x).symmL Real y) ∘L ((triv
ializationAt F E x).continuousLinearMapAt Real x)‖ < r
参数：x : B；hr : 1 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.tendsto_inf_left`：tendsto_inf_left {f : α -> β} {x₁ x₂ : Filter α
} {y : Filter β} (h : Tendsto f x₁ y) : Tendsto f (x₁ ⊓ x₂) y
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
（共 151 条，此处仅展示前 30 条）

--- 原说明 ---
In a continuous Riemannian bundle, local changes of coordinates given by the tri
vialization at
a point distort the norm by a factor arbitrarily close to 1.
-/
lemma eventually_norm_symmL_trivializationAt_comp_self_lt (x : B) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ y in 𝓝 x, ‖((trivializationAt F E x).symmL ℝ y)
      ∘L ((trivializationAt F E x).continuousLinearMapAt ℝ x)‖ < r := by
  /- We will expand the definition of continuity of the inner product structure, in the chart.
  Denote `g' x` the metric in the fiber of `x`, read in the chart. For `y` close to `x`, then
  `g' y` and `g' x` are close. The inequality we have to prove reduces to comparing
  `g' y w w` and `g' x w w`, where `w` is the image in the chart of a tangent vector `v` at `x`.
  Their difference is controlled by `δ ‖w‖ ^ 2` for any small `δ > 0`. To conclude, we argue that
  `‖w‖` is comparable to the norm inside the fiber over `x`, i.e., `g' x w w`, because there
  is a continuous linear equivalence between these two spaces by definition of vector bundles. -/
  obtain ⟨r', hr', r'r⟩ : ∃ r', 1 < r' ∧ r' < r := exists_between hr
  have h'x : x ∈ (trivializationAt F E x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let G := (trivializationAt F E x).continuousLinearEquivAt ℝ x h'x
  let C := (‖(G : E x →L[ℝ] F)‖) ^ 2
  -- choose `δ` small enough that the computation below works when the metrics at `x` and `y`
  -- are `δ` close. When writing this proof, I have followed my nose in the computation, and
  -- recorded only in the end how small `δ` needs to be. The reader should skip the precise
  -- condition for now, as it doesn't give any useful insight.
  obtain ⟨δ, δpos, h'δ⟩ : ∃ δ, 0 < δ ∧ (1 + δ * C) < r' ^ 2 := by
    have A : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    have B : Tendsto (fun δ ↦ 1 + δ * C) (𝓝[>] 0) (𝓝 (1 + 0 * C)) := by
      apply tendsto_inf_left
      exact tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
    have B' : ∀ᶠ δ in 𝓝[>] 0, 1 + δ * C < r' ^ 2 := by
      apply (tendsto_order.1 B).2
      simpa using hr'.trans_le (le_abs_self _)
    exact (A.and B').exists
  rcases h.exists_continuous with ⟨g, g_cont, hg⟩
  let g' : B → F →L[ℝ] F →L[ℝ] ℝ := fun y ↦
    inCoordinates F E (F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] ℝ) x y x y (g y)
  have hg' : ContinuousAt g' x := by
    have W := g_cont.continuousAt (x := x)
    simp only [continuousAt_hom_bundle] at W
    exact W.2
  have : ∀ᶠ y in 𝓝 x, dist (g' y) (g' x) < δ := by
    rw [Metric.continuousAt_iff'] at hg'
    apply hg' _ δpos
  filter_upwards [this, (trivializationAt F E x).open_baseSet.mem_nhds h'x] with y hy h'y
  have : ‖g' y - g' x‖ ≤ δ := by rw [← dist_eq_norm]; exact hy.le
  -- To show that the norm of the composition is bounded by `r'`, we start from a vector
  -- `‖v‖`. We will show that its image has a controlled norm.
  apply (opNorm_le_bound _ (by linarith) (fun v ↦ ?_)).trans_lt r'r
  -- rewrite the norm of `‖v‖` and of its image in terms of norms in the model space
  let w := (trivializationAt F E x).continuousLinearMapAt ℝ x v
  suffices ‖((trivializationAt F E x).symmL ℝ y) w‖ ^ 2 ≤ r' ^ 2 * ‖v‖ ^ 2 from
    le_of_sq_le_sq (by simpa [mul_pow]) (by positivity)
  simp only [Trivialization.symmL_apply, h'y, ← real_inner_self_eq_norm_sq, hg]
  have hgx : g x v v = g' x w w := by
    rw [inCoordinates_apply_eq₂ h'x h'x (Set.mem_univ _)]
    have A : ((trivializationAt F E x).symm x)
       ((trivializationAt F E x).linearMapAt ℝ x v) = v := by
      convert! ((trivializationAt F E x).continuousLinearEquivAt ℝ _ h'x).symm_apply_apply v
      simp [Trivialization.coe_continuousLinearEquivAt_eq _ h'x]
    simp [A, w]
  have hgy : g y ((trivializationAt F E x).symm y w) ((trivializationAt F E x).symm y w)
      = g' y w w := by
    rw [inCoordinates_apply_eq₂ h'y h'y (Set.mem_univ _)]
    simp
  rw [hgx, hgy]
  -- get a good control for the norms of `w` in the model space, using continuity
  calc g' y w w
    _ = (g' y - g' x) w w + g' x w w := by simp
    _ ≤ ‖g' y - g' x‖ * ‖w‖ * ‖w‖ + g' x w w := by
      grw [← le_opNorm₂, ← Real.le_norm_self]
    _ ≤ δ * ‖w‖ ^ 2 + g' x w w := by
      rw [pow_two, mul_assoc]; gcongr
    _ ≤ δ * (‖(G : E x →L[ℝ] F)‖ * ‖G.symm w‖) ^ 2 + g' x w w := by
      grw [← le_opNorm]
      simp
    _ = δ * C * ‖G.symm w‖ ^ 2 + g' x w w := by ring
    _ = δ * C * g x (G.symm w) (G.symm w) + g' x w w := by simp [← hg]
    _ = δ * C * g' x w w + g' x w w := by
      congr
      rw [inCoordinates_apply_eq₂ h'x h'x (Set.mem_univ _)]
      simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
        LinearMap.id_coe, id_eq, w]
      rfl
    _ = (1 + δ * C) * g' x w w := by ring
    _ ≤ r' ^ 2 * g' x w w := by
      gcongr
      rw [← hgx, ← hg, real_inner_self_eq_norm_sq]
      positivity

/-- In a continuous Riemannian bundle, the inverse of the trivialization at a point is locally
bounded in norm. -/
/-
**eventually_norm_symmL_trivializationAt_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eventually_norm_symmL_trivializationAt_lt (x : B) : exists C > 0, forallᶠ 
y in 𝓝 x, ‖(trivializationAt F E x).symmL Real y‖ < C
参数：x : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `eventually_norm_symmL_trivializationAt_comp_self_lt`：eventually_norm_sym
mL_trivializationAt_comp_self_lt (x : B) {r : Real} (hr : 1 < r) : forallᶠ y in 
𝓝 x, ‖((trivializationAt F E x).symmL Rea…
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bundle.Trivialization.symmL_apply`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x :
 B) → AddCommMonoid (E …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
In a continuous Riemannian bundle, the inverse of the trivialization at a point 
is locally
bounded in norm.
-/
lemma eventually_norm_symmL_trivializationAt_lt (x : B) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, ‖(trivializationAt F E x).symmL ℝ y‖ < C := by
  refine ⟨2 * (1 + ‖(trivializationAt F E x).symmL ℝ x‖), by positivity, ?_⟩
  filter_upwards [eventually_norm_symmL_trivializationAt_comp_self_lt F E x one_lt_two] with y hy
  have A : ((trivializationAt F E x).continuousLinearMapAt ℝ x) ∘L
      ((trivializationAt F E x).symmL ℝ x) = ContinuousLinearMap.id _ _ := by
    ext v
    have h'x : x ∈ (trivializationAt F E x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    simp only [Trivialization.continuousLinearMapAt_apply, Trivialization.symmL_apply,
      mem_baseSet_trivializationAt, comp_apply, id_apply]
    convert! ((trivializationAt F E x).continuousLinearEquivAt ℝ _ h'x).apply_symm_apply v
    simp [Trivialization.coe_continuousLinearEquivAt_eq _ h'x]
  have : (trivializationAt F E x).symmL ℝ y =
     ((trivializationAt F E x).symmL ℝ y) ∘L (ContinuousLinearMap.id _ _) := by simp
  grw [this, ← A, ← comp_assoc, opNorm_comp_le]
  gcongr
  linarith

end Continuous

namespace Bundle

section Construction

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

open Bornology

variable (E) in
/-- A family of inner product space structures on the fibers of a fiber bundle, defining the same
topology as the already existing one. This family is not assumed to be continuous or smooth: to
guarantee continuity, resp. smoothness, of the inner product as a function of the base point,
use `ContinuousRiemannianMetric` or `ContMDiffRiemannianMetric`.

This structure is used through `RiemannianBundle` for typeclass inference, to register the inner
product space structure on the fibers without creating diamonds. -/
/-
**Bundle.RiemannianMetric** 是 Mathlib 中的一个归纳类型，位于命名空间 `Bundle`。
形式化陈述：{B : Type u_4} →   (E : B → Type u_6) →     [(b : B) → TopologicalSpace (E
 b)] →       [inst : (b : B) → AddCommGroup (E b)] → [(b : B) → _root_.Module ℝ 
(E b)] → Type (max u_4 u_6)
参数：E : B → Type u_6；b : B；E b；b : B；E b；b : B；E b；max u_4 u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of inner product space structures on the fibers of a fiber bundle, defi
ning the same
topology as the already existing one. This family is not assumed to be continuou
s or smooth: to
guarantee continuity, resp. smoothness, of the inner product as a function of th
e base point,
use `ContinuousRiemannianMetric` or `ContMDiffRiemannianMetric`.

This structure is used through `RiemannianBundle` for typeclass inference, to re
gister the inner
product space structure on the fibers without creating diamonds.
-/
structure RiemannianMetric where
  /-- The inner product along the fibers of the bundle. -/
  inner (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  symm (b : B) (v w : E b) : inner b v w = inner b w v
  pos (b : B) (v : E b) (hv : v ≠ 0) : 0 < inner b v v
  /-- The continuity at `0` is automatic when `E b` is isomorphic to a normed space, but since
  we are not making this assumption here we have to include it. -/
  continuousAt (b : B) : ContinuousAt (fun (v : E b) ↦ inner b v v) 0
  isVonNBounded (b : B) : IsVonNBounded ℝ {v : E b | inner b v v < 1}

/-- `Core` structure associated to a family of inner products on the fibers of a fiber bundle. This
is an auxiliary construction to endow the fibers with an inner product space structure without
creating diamonds.

Warning: Do not use this `Core` structure if the space you are interested in already has a norm
/-
**Bundle.defined** 是 Mathlib 中的一个实例，位于命名空间 `Bundle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance defined on it, otherwise this will create a second non-defeq norm instance! -/
/-
**Bundle.RiemannianMetric.toCore** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.RiemannianMet
ric`。
形式化陈述：{B : Type u_4} →   {E : B → Type u_6} →     [inst : (b : B) → TopologicalS
pace (E b)] →       [inst_1 : (b : B) → AddCommGroup (E b)] →         [inst_2 : 
(b : B) → _root_.Module ℝ (E b)] →           Bundle.RiemannianMetric E → (b : B)
 → InnerProductSpace.Core ℝ (E b)
参数：b : B；E b；b : B；E b；b : B；E b；b : B；E b。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Bundle.RiemannianMetric.symm`：∀ {B : Type u_4} {E : B → Type u_6} [inst 
: (b : B) → TopologicalSpace (E b)] [inst_1 : (b : B) → AddCommGroup (E b)]   [i
nst_2 : (b : B) → …

--- 原说明 ---
`Core` structure associated to a family of inner products on the fibers of a fib
er bundle. This
is an auxiliary construction to endow the fibers with an inner product space str
ucture without
creating diamonds.

Warning: Do not use this `Core` structure if the space you are interested in alr
eady has a norm
instance defined on it, otherwise this will create a second non-defeq norm insta
nce!
-/
@[reducible] noncomputable def RiemannianMetric.toCore (g : RiemannianMetric E) (b : B) :
    InnerProductSpace.Core ℝ (E b) where
  inner v w := g.inner b v w
  conj_inner_symm v w := g.symm b w v
  re_inner_nonneg v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · simpa using (g.pos b v hv).le
  add_left v w x := by simp
  smul_left c v := by simp
  definite v h := by contrapose! h; exact (g.pos b v h).ne'

variable (E) in
/-- Class used to create an inner product structure space on the fibers of a fiber bundle, without
creating diamonds. Use as follows:
* `instance : RiemannianBundle E := ⟨g⟩` where `g : RiemannianMetric E` registers the inner product
  space on the fibers;
* `instance : RiemannianBundle E := ⟨g.toRiemannianMetric⟩` where
  `g : ContinuousRiemannianMetric F E` registers the inner product space on the fibers, and the fact
  that it varies continuously (i.e., a `[IsContinuousRiemannianBundle]` instance).
* `instance : RiemannianBundle E := ⟨g.toRiemannianMetric⟩` where
  `g : ContMDiffRiemannianMetric IB n F E` registers the inner product space on the fibers, and the
  fact that it varies smoothly (and continuously), i.e., `[IsContMDiffRiemannianBundle]` and
  `[IsContinuousRiemannianBundle]` instances.

Note that this is only useful when there is a preexisting topology in the fibers of a vector
bundle, like for the tangent bundle. This should *not* be used to express theorems for general
bundles with a metric. Instead, use
```
variable {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]
```
-/
/-
**Bundle.RiemannianBundle** 是 Mathlib 中的一个类，位于命名空间 `Bundle`。
形式化陈述：RiemannianBundle where /-- The family of inner products on the fibers -/ g
 : RiemannianMetric E  /-- A fiber in a bundle satisfying the `[RiemannianBundle
 E]` typeclass inherits a `NormedAddCommGroup` structure.  The normal priority f
or an instance which always applies like this one should be 100. We use 80 as th
is is rather specialized, so we want other paths to be tried first typically. As
 this instance is quite specific and very costly because of higher-order unifica
tion, we also scope it to 
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class used to create an inner product structure space on the fibers of a fiber b
undle, without
creating diamonds. Use as follows:
* `instance : RiemannianBundle E := ⟨g⟩` where `g : RiemannianMetric E` register
s the inner product
  space on the fibers;
* `instance : RiemannianBundle E := ⟨g.toRiemannianMetric⟩` where
  `g : ContinuousRiemannianMetric F E` registers the inner product space on the 
fibers, and the fact
  that it varies continuously (i.e., a `[IsContinuousRiemannianBundle]` instance
).
* `instance : RiemannianBundle E := ⟨g.toRiemannianMetric⟩` where
  `g : ContMDiffRiemannianMetric IB n F E` registers the inner product space on 
the fibers, and the
  fact that it varies smoothly (and continuously), i.e., `[IsContMDiffRiemannian
Bundle]` and
  `[IsContinuousRiemannianBundle]` instances.

Note that this is only useful when there is a preexisting topology in the fibers
 of a vector
bundle, like for the tangent bundle. This should *not* be used to express theore
ms for general
bundles with a metric. Instead, use
```
variable {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]
``` -/
-/
class RiemannianBundle where
  /-- The family of inner products on the fibers -/
  g : RiemannianMetric E

/-- A fiber in a bundle satisfying the `[RiemannianBundle E]` typeclass inherits
a `NormedAddCommGroup` structure.

The normal priority for an instance which always applies like this one should be 100.
We use 80 as this is rather specialized, so we want other paths to be tried first typically.
As this instance is quite specific and very costly because of higher-order unification, we
also scope it to the `Bundle` namespace. -/
/-
**Bundle.** 是 Mathlib 中的一个实例，位于命名空间 `Bundle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fiber in a bundle satisfying the `[RiemannianBundle E]` typeclass inherits
a `NormedAddCommGroup` structure.

The normal priority for an instance which always applies like this one should be
 100.
We use 80 as this is rather specialized, so we want other paths to be tried firs
t typically.
As this instance is quite specific and very costly because of higher-order unifi
cation, we
also scope it to the `Bundle` namespace.
-/
noncomputable scoped instance (priority := 80)
    {B : Type*} {E : B → Type*} [(b : B) → TopologicalSpace (E b)]
    [(b : B) → AddCommGroup (E b)] [(b : B) → Module ℝ (E b)]
    /- We are careful about the parameter order, putting `RiemannianBundle E`
    before `IsTopologicalAddGroup` to avoid the following loop: to put a `IsTopologicalAddGroup`
    structure on `E b`, one tries to find a `NormedAddCommGroup`, then one tries to apply the
    current instance. If `IsTopologicalAddGroup (E b)` were before `RiemannianBundle`, then one
    would try to find a `IsTopologicalAddGroup` to apply the instance, and loop.
    Normally, loops are detected by typeclass inference but here it is not the case as the loop is
    at different depth levels. See lean4#13063. -/
    [h : RiemannianBundle E] [∀ (b : B), IsTopologicalAddGroup (E b)]
    [∀ (b : B), ContinuousConstSMul ℝ (E b)] (b : B) :
    NormedAddCommGroup (E b) := fast_instance%
  (h.g.toCore b).toNormedAddCommGroupOfTopology (h.g.continuousAt b) (h.g.isVonNBounded b)

/-- A fiber in a bundle satisfying the `[RiemannianBundle E]` typeclass inherits
an `InnerProductSpace ℝ` structure.

The normal priority for an instance which always applies like this one should be 100.
We use 80 as this is rather specialized, so we want other paths to be tried first typically.
As this instance is quite specific and very costly because of higher-order unification, we
also scope it to the `Bundle` namespace. -/
/-
**Bundle.** 是 Mathlib 中的一个实例，位于命名空间 `Bundle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fiber in a bundle satisfying the `[RiemannianBundle E]` typeclass inherits
an `InnerProductSpace ℝ` structure.

The normal priority for an instance which always applies like this one should be
 100.
We use 80 as this is rather specialized, so we want other paths to be tried firs
t typically.
As this instance is quite specific and very costly because of higher-order unifi
cation, we
also scope it to the `Bundle` namespace.
-/
noncomputable scoped instance (priority := 80)
    {B : Type*} {E : B → Type*} [(b : B) → TopologicalSpace (E b)]
    [(b : B) → AddCommGroup (E b)] [(b : B) → Module ℝ (E b)]
    [h : RiemannianBundle E] [∀ (b : B), IsTopologicalAddGroup (E b)]
    [∀ (b : B), ContinuousConstSMul ℝ (E b)] (b : B) :
    InnerProductSpace ℝ (E b) := fast_instance%
  .ofCoreOfTopology (h.g.toCore b) (h.g.continuousAt b) (h.g.isVonNBounded b)

variable (F E) in
/-- A family of inner product space structures on the fibers of a fiber bundle, defining the same
topology as the already existing one, and varying continuously with the base point. See also
`ContMDiffRiemannianMetric` for a smooth version.

This structure is used through `RiemannianBundle` for typeclass inference, to register the inner
product space structure on the fibers without creating diamonds. -/
/-
**Bundle.ContinuousRiemannianMetric** 是 Mathlib 中的一个归纳类型，位于命名空间 `Bundle`。
形式化陈述：{B : Type u_4} →   [inst : TopologicalSpace B] →     (F : Type u_5) →     
  [inst_1 : NormedAddCommGroup F] →         [inst_2 : NormedSpace ℝ F] →        
   (E : B → Type u_6) →             [inst_3 : TopologicalSpace (Bundle.TotalSpac
e F E)] →               [inst_4 : (b : B) → TopologicalSpace (E b)] →           
      [inst_5 : (b : B) → AddCommGroup (E b)] →                   [inst_6 : (b :
 B) → _root_.Module ℝ (E b)] →                     [inst_7 : FiberBundle F E] → 
[VectorBundle ℝ F E] → Type (max u_4 u_6)
参数：F : Type u_5；E : B → Type u_6；Bundle.TotalSpace F E；b : B；E b；b : B；E b；b : B
；E b；max u_4 u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of inner product space structures on the fibers of a fiber bundle, defi
ning the same
topology as the already existing one, and varying continuously with the base poi
nt. See also
`ContMDiffRiemannianMetric` for a smooth version.

This structure is used through `RiemannianBundle` for typeclass inference, to re
gister the inner
product space structure on the fibers without creating diamonds.
-/
structure ContinuousRiemannianMetric where
  /-- The inner product along the fibers of the bundle. -/
  inner (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  symm (b : B) (v w : E b) : inner b v w = inner b w v
  pos (b : B) (v : E b) (hv : v ≠ 0) : 0 < inner b v v
  isVonNBounded (b : B) : IsVonNBounded ℝ {v : E b | inner b v v < 1}
  continuous : Continuous (fun (b : B) ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (inner b))

/-- A continuous Riemannian metric is in particular a Riemannian metric. -/
/-
**Bundle.ContinuousRiemannianMetric.toRiemannianMetric** 是 Mathlib 中的一个定义，位于命名空间
 `Bundle.ContinuousRiemannianMetric`。
形式化陈述：{B : Type u_4} →   [inst : TopologicalSpace B] →     {F : Type u_5} →     
  [inst_1 : NormedAddCommGroup F] →         [inst_2 : NormedSpace ℝ F] →        
   {E : B → Type u_6} →             [inst_3 : TopologicalSpace (Bundle.TotalSpac
e F E)] →               [inst_4 : (b : B) → TopologicalSpace (E b)] →           
      [inst_5 : (b : B) → AddCommGroup (E b)] →                   [inst_6 : (b :
 B) → _root_.Module ℝ (E b)] →                     [inst_7 : FiberBundle F E] → 
                      [inst_8 : VectorBundle ℝ F E] → Bundle.ContinuousRiemannia
nMetric F E → Bundle.RiemannianMetric E
参数：Bundle.TotalSpace F E；b : B；E b；b : B；E b；b : B；E b。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.ContinuousRiemannianMetric.symm`：∀ {B : Type u_4} [inst : Topolog
icalSpace B] {F : Type u_5} [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpac
e ℝ F]   {E : B → Type u_6} …
· 使用定理 `Bundle.ContinuousRiemannianMetric.pos`：∀ {B : Type u_4} [inst : Topologi
calSpace B] {F : Type u_5} [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace
 ℝ F]   {E : B → Type u_6} …
· 使用定理 `Bundle.ContinuousRiemannianMetric.isVonNBounded`：∀ {B : Type u_4} [inst 
: TopologicalSpace B] {F : Type u_5} [inst_1 : NormedAddCommGroup F] [inst_2 : N
ormedSpace ℝ F]   {E : B → Type u_6} …

--- 原说明 ---
A continuous Riemannian metric is in particular a Riemannian metric.
-/
def ContinuousRiemannianMetric.toRiemannianMetric (g : ContinuousRiemannianMetric F E) :
    RiemannianMetric E where
  inner := g.inner
  symm := g.symm
  pos := g.pos
  isVonNBounded := g.isVonNBounded
  continuousAt b := by
    -- Continuity of bilinear maps is only true on normed spaces. As `F` is a normed space by
    -- assumption, we transfer everything to `F` and argue there.
    let e : E b ≃L[ℝ] F := Trivialization.continuousLinearEquivAt ℝ (trivializationAt F E b) _
      (FiberBundle.mem_baseSet_trivializationAt' b)
    let m : (E b →L[ℝ] E b →L[ℝ] ℝ) ≃L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ) :=
      e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
    have A (v : E b) : g.inner b v v = ((fun w ↦ m (g.inner b) w w) ∘ e) v := by simp [m]
    simp only [A]
    fun_prop

/-- If a Riemannian bundle structure is defined using `g.toRiemannianMetric` where `g` is
a `ContinuousRiemannianMetric`, then we make sure typeclass inference can infer automatically
that the bundle is a continuous Riemannian bundle. -/
/-
**Bundle.** 是 Mathlib 中的一个实例，位于命名空间 `Bundle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a Riemannian bundle structure is defined using `g.toRiemannianMetric` where `
g` is
a `ContinuousRiemannianMetric`, then we make sure typeclass inference can infer 
automatically
that the bundle is a continuous Riemannian bundle.
-/
instance (g : ContinuousRiemannianMetric F E) :
    letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩;
    IsContinuousRiemannianBundle F E := by
  let : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
  exact ⟨⟨g.inner, g.continuous, fun b v w ↦ rfl⟩⟩

end Construction

end Bundle

