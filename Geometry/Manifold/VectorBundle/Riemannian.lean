/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Topology.VectorBundle.Riemannian

/-! # Riemannian vector bundles

Given a vector bundle over a manifold whose fibers are all endowed with a scalar product, we
say that this bundle is Riemannian if the scalar product depends smoothly on the base point.

We introduce a typeclass `[IsContMDiffRiemannianBundle IB n F E]` registering this property.
Under this assumption, we show that the scalar product of two smooth maps into the same fibers of
the bundle is a smooth function.

If the fibers of a bundle `E` have a preexisting topology (like the tangent bundle), one cannot
assume additionally `[∀ b, InnerProductSpace ℝ (E b)]` as this would create diamonds. Instead,
use `[RiemannianBundle E]`, which endows the fibers with a scalar product while ensuring that
there is no diamond (for this, the `Bundle` scope should be open). We provide a
constructor for `[RiemannianBundle E]` from a smooth family of metrics, which registers
automatically `[IsContMDiffRiemannianBundle IB n F E]`.

The following code block is the standard way to say "Let `E` be a smooth vector bundle equipped with
a `C^n` Riemannian structure over a `C^n` manifold `B`":
```
variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB n B] [ContMDiffVectorBundle n F E IB]
  [IsContMDiffRiemannianBundle IB n F E]
```
-/

@[expose] public section

open Manifold Bundle ContinuousLinearMap ENat Bornology
open scoped ContDiff Topology

section

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n n' : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable (IB n F E) in
/-- Consider a real vector bundle in which each fiber is endowed with a scalar product.
We say that the bundle is Riemannian if the scalar product depends smoothly on the base point.
This assumption is spelled `IsContMDiffRiemannianBundle IB n F E` where `IB` is the model space of
the base, `n` is the smoothness, `F` is the model fiber, and `E : B → Type*` is the bundle. -/
/-
**IsContMDiffRiemannianBundle** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{EB : Type u_1} →   [inst : NormedAddCommGroup EB] →     [inst_1 : NormedS
pace ℝ EB] →       {HB : Type u_2} →         [inst_2 : TopologicalSpace HB] →   
        ModelWithCorners ℝ EB HB →             WithTop ℕ∞ →               {B : T
ype u_3} →                 [inst : TopologicalSpace B] →                   [Char
tedSpace HB B] →                     (F : Type u_4) →                       [ins
t_4 : NormedAddCommGroup F] →                         [inst_5 : NormedSpace ℝ F]
 →                           (E : B → Type u_5) →                             [i
nst_6 : TopologicalSpace (Bundle.TotalSpace F E)] →                             
  [inst_7 : (x : B) → NormedAddCommGroup (E x)] →                               
  [inst_8 : (x : B) → InnerProductSpace ℝ (E x)] →                              
     [inst_9 : FiberBundle F E] → [VectorBundle ℝ F E] → Prop
参数：F : Type u_4；E : B → Type u_5；Bundle.TotalSpace F E；x : B；E x；x : B；E x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider a real vector bundle in which each fiber is endowed with a scalar produ
ct.
We say that the bundle is Riemannian if the scalar product depends smoothly on t
he base point.
This assumption is spelled `IsContMDiffRiemannianBundle IB n F E` where `IB` is 
the model space of
the base, `n` is the smoothness, `F` is the model fiber, and `E : B → Type*` is 
the bundle.
-/
class IsContMDiffRiemannianBundle : Prop where
  exists_contMDiff : ∃ g : Π (x : B), E x →L[ℝ] E x →L[ℝ] ℝ,
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (g b))
    ∧ ∀ (x : B) (v w : E x), ⟪v, w⟫ = g x v w
/-
**IsContMDiffRiemannianBundle.of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsContMDiffRiemannianBundle.of_le [h : IsContMDiffRiemannianBundle IB n F 
E] (h' : n' <= n) : IsContMDiffRiemannianBundle IB n' F E
参数：h' : n' <= n。
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
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsContMDiffRiemannianBundle.exists_contMDiff`：∀ {EB : Type u_1} {inst : 
NormedAddCommGroup EB} {inst_1 : NormedSpace ℝ EB} {HB : Type u_2}   {inst_2 : T
opologicalSpace HB} {IB : ModelWit…
· 使用定理 `ContMDiff.of_le`：ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m <= n)
 : ContMDiff I I' m f
-/
lemma IsContMDiffRiemannianBundle.of_le [h : IsContMDiffRiemannianBundle IB n F E] (h' : n' ≤ n) :
    IsContMDiffRiemannianBundle IB n' F E := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  exact ⟨g, g_smooth.of_le h', hg⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {a : ℕ∞ω} [IsContMDiffRiemannianBundle IB ∞ F E] [h : LEInfty a] :
    IsContMDiffRiemannianBundle IB a F E :=
  IsContMDiffRiemannianBundle.of_le h.out
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {a : ℕ∞ω} [IsContMDiffRiemannianBundle IB ω F E] :
    IsContMDiffRiemannianBundle IB a F E :=
  IsContMDiffRiemannianBundle.of_le le_top
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsContMDiffRiemannianBundle IB 1 F E] : IsContMDiffRiemannianBundle IB 0 F E :=
  IsContMDiffRiemannianBundle.of_le zero_le_one
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsContMDiffRiemannianBundle IB 2 F E] : IsContMDiffRiemannianBundle IB 1 F E :=
  IsContMDiffRiemannianBundle.of_le one_le_two
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsContMDiffRiemannianBundle IB 3 F E] : IsContMDiffRiemannianBundle IB 2 F E :=
  IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_cast)

section Trivial

variable {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]

set_option backward.isDefEq.respectTransparency false in
/-- A trivial vector bundle, in which the model fiber has a scalar product,
is a Riemannian bundle. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A trivial vector bundle, in which the model fiber has a scalar product,
is a Riemannian bundle.
-/
instance : IsContMDiffRiemannianBundle IB n F₁ (Bundle.Trivial B F₁) := by
  refine ⟨fun x ↦ innerSL ℝ, fun x ↦ ?_, fun x v w ↦ rfl⟩
  simp only [contMDiffAt_section]
  convert! contMDiffAt_const (c := innerSL ℝ)
  ext v w
  simp [hom_trivializationAt_apply, inCoordinates]

end Trivial

section ContMDiff

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [h : IsContMDiffRiemannianBundle IB n F E]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}

/-- Given two smooth maps into the same fibers of a Riemannian bundle,
their scalar product is smooth. -/
/-
**ContMDiffWithinAt.inner_bundle** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.inner_bundle (hv : CMDiffAt[s] n (fun m => (v m : TotalS
pace F E)) x) (hw : CMDiffAt[s] n (fun m => (w m : TotalSpace F E)) x) : CMDiffA
t[s] n (fun m => ⟪v m, w m⟫) x
参数：hv : CMDiffAt[s] n (fun m => (v m : TotalSpace F E)) x；hw : CMDiffAt[s] n (fu
n m => (w m : TotalSpace F E)) x。
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
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsContMDiffRiemannianBundle.exists_contMDiff`：∀ {EB : Type u_1} {inst : 
NormedAddCommGroup EB} {inst_1 : NormedSpace ℝ EB} {HB : Type u_2}   {inst_2 : T
opologicalSpace HB} {IB : ModelWit…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ContMDiffWithinAt.clm_bundle_apply₂`：ContMDiffWithinAt.clm_bundle_apply₂
 (hψ : CMDiffAt[s] n (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (E
· 使用定理 `ContMDiffAt.comp_contMDiffWithinAt`：ContMDiffAt.comp_contMDiffWithinAt {
g : M' -> M''} (x : M) (hg : ContMDiffAt I' I'' n g (f x)) (hf : ContMDiffWithin
At I I' n f s x) : ContM…
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Given two smooth maps into the same fibers of a Riemannian bundle,
their scalar product is smooth.
-/
lemma ContMDiffWithinAt.inner_bundle
    (hv : CMDiffAt[s] n (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : CMDiffAt[s] n (fun m ↦ (w m : TotalSpace F E)) x) :
    CMDiffAt[s] n (fun m ↦ ⟪v m, w m⟫) x := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  have hb : CMDiffAt[s] n b x := by
    simp only [contMDiffWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ)) n
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x := by
    apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact ContMDiffAt.comp_contMDiffWithinAt x g_smooth.contMDiffAt hb
    · exact hv
    · exact hw
  simp only [contMDiffWithinAt_totalSpace] at this
  exact this.2

/-- Given two smooth maps into the same fibers of a Riemannian bundle,
their scalar product is smooth. -/
/-
**ContMDiffAt.inner_bundle** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffAt.inner_bundle (hv : CMDiffAt n (fun m => (v m : TotalSpace F E)
) x) (hw : CMDiffAt n (fun m => (w m : TotalSpace F E)) x) : CMDiffAt n (fun b =
> ⟪v b, w b⟫) x
参数：hv : CMDiffAt n (fun m => (v m : TotalSpace F E)) x；hw : CMDiffAt n (fun m =>
 (w m : TotalSpace F E)) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffWithinAt.inner_bundle`：ContMDiffWithinAt.inner_bundle (hv : CMD
iffAt[s] n (fun m => (v m : TotalSpace F E)) x) (hw : CMDiffAt[s] n (fun m => (w
 m : TotalSpace F E)…

--- 原说明 ---
Given two smooth maps into the same fibers of a Riemannian bundle,
their scalar product is smooth.
-/
lemma ContMDiffAt.inner_bundle
    (hv : CMDiffAt n (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : CMDiffAt n (fun m ↦ (w m : TotalSpace F E)) x) :
    CMDiffAt n (fun b ↦ ⟪v b, w b⟫) x :=
  ContMDiffWithinAt.inner_bundle hv hw

/-- Given two smooth maps into the same fibers of a Riemannian bundle,
their scalar product is smooth. -/
/-
**ContMDiffOn.inner_bundle** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffOn.inner_bundle (hv : CMDiff[s] n (fun m => (v m : TotalSpace F E
))) (hw : CMDiff[s] n (fun m => (w m : TotalSpace F E))) : CMDiff[s] n (fun b =>
 ⟪v b, w b⟫)
参数：hv : CMDiff[s] n (fun m => (v m : TotalSpace F E))；hw : CMDiff[s] n (fun m =>
 (w m : TotalSpace F E))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffWithinAt.inner_bundle`：ContMDiffWithinAt.inner_bundle (hv : CMD
iffAt[s] n (fun m => (v m : TotalSpace F E)) x) (hw : CMDiffAt[s] n (fun m => (w
 m : TotalSpace F E)…

--- 原说明 ---
Given two smooth maps into the same fibers of a Riemannian bundle,
their scalar product is smooth.
-/
lemma ContMDiffOn.inner_bundle
    (hv : CMDiff[s] n (fun m ↦ (v m : TotalSpace F E)))
    (hw : CMDiff[s] n (fun m ↦ (w m : TotalSpace F E))) :
    CMDiff[s] n (fun b ↦ ⟪v b, w b⟫) :=
  fun x hx ↦ (hv x hx).inner_bundle (hw x hx)

/-- Given two smooth maps into the same fibers of a Riemannian bundle,
their scalar product is smooth. -/
/-
**ContMDiff.inner_bundle** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.inner_bundle (hv : CMDiff n (fun m => (v m : TotalSpace F E))) (
hw : CMDiff n (fun m => (w m : TotalSpace F E))) : CMDiff n (fun b => ⟪v b, w b⟫
)
参数：hv : CMDiff n (fun m => (v m : TotalSpace F E))；hw : CMDiff n (fun m => (w m 
: TotalSpace F E))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiffAt.inner_bundle`：ContMDiffAt.inner_bundle (hv : CMDiffAt n (fun
 m => (v m : TotalSpace F E)) x) (hw : CMDiffAt n (fun m => (w m : TotalSpace F 
E)) x) : CMDif…

--- 原说明 ---
Given two smooth maps into the same fibers of a Riemannian bundle,
their scalar product is smooth.
-/
lemma ContMDiff.inner_bundle
    (hv : CMDiff n (fun m ↦ (v m : TotalSpace F E)))
    (hw : CMDiff n (fun m ↦ (w m : TotalSpace F E))) :
    CMDiff n (fun b ↦ ⟪v b, w b⟫) :=
  fun x ↦ (hv x).inner_bundle (hw x)

end ContMDiff

section MDifferentiable

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [h : IsContMDiffRiemannianBundle IB 1 F E]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}

/-- Given two differentiable maps into the same fibers of a Riemannian bundle,
their scalar product is differentiable. -/
/-
**MDifferentiableWithinAt.inner_bundle** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.inner_bundle (hv : MDiffAt[s] (fun m => (v m : Tot
alSpace F E)) x) (hw : MDiffAt[s] (fun m => (w m : TotalSpace F E)) x) : MDiffAt
[s] (fun m => ⟪v m, w m⟫) x
参数：hv : MDiffAt[s] (fun m => (v m : TotalSpace F E)) x；hw : MDiffAt[s] (fun m =>
 (w m : TotalSpace F E)) x。
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
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsContMDiffRiemannianBundle.exists_contMDiff`：∀ {EB : Type u_1} {inst : 
NormedAddCommGroup EB} {inst_1 : NormedSpace ℝ EB} {HB : Type u_2}   {inst_2 : T
opologicalSpace HB} {IB : ModelWit…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MDifferentiableWithinAt.clm_bundle_apply₂`：MDifferentiableWithinAt.clm_b
undle_apply₂ (hψ : MDiffAt[s] (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) 
(E
· 使用定理 `MDifferentiableAt.comp_mdifferentiableWithinAt`：MDifferentiableAt.comp_m
differentiableWithinAt (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x) : MDiffAt[s]
 (g ∘ f) x
· 使用定理 `ContMDiff.mdifferentiableAt`：ContMDiff.mdifferentiableAt (hf : CMDiff n 
f) (hn : n != 0) : MDiffAt f x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Given two differentiable maps into the same fibers of a Riemannian bundle,
their scalar product is differentiable.
-/
lemma MDifferentiableWithinAt.inner_bundle
    (hv : MDiffAt[s] (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : MDiffAt[s] (fun m ↦ (w m : TotalSpace F E)) x) :
    MDiffAt[s] (fun m ↦ ⟪v m, w m⟫) x := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  have hb : MDiffAt[s] b x := by
    simp only [mdifferentiableWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : MDifferentiableWithinAt IM (IB.prod 𝓘(ℝ))
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x := by
    apply MDifferentiableWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact MDifferentiableAt.comp_mdifferentiableWithinAt x
        (g_smooth.mdifferentiableAt one_ne_zero) hb
    · exact hv
    · exact hw
  simp only [mdifferentiableWithinAt_totalSpace] at this
  exact this.2

/-- Given two differentiable maps into the same fibers of a Riemannian bundle,
their scalar product is differentiable. -/
/-
**MDifferentiableAt.inner_bundle** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.inner_bundle (hv : MDiffAt (fun m => (v m : TotalSpace F
 E)) x) (hw : MDiffAt (fun m => (w m : TotalSpace F E)) x) : MDiffAt (fun b => ⟪
v b, w b⟫) x
参数：hv : MDiffAt (fun m => (v m : TotalSpace F E)) x；hw : MDiffAt (fun m => (w m 
: TotalSpace F E)) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableWithinAt.inner_bundle`：MDifferentiableWithinAt.inner_bund
le (hv : MDiffAt[s] (fun m => (v m : TotalSpace F E)) x) (hw : MDiffAt[s] (fun m
 => (w m : TotalSpace F E)…

--- 原说明 ---
Given two differentiable maps into the same fibers of a Riemannian bundle,
their scalar product is differentiable.
-/
lemma MDifferentiableAt.inner_bundle
    (hv : MDiffAt (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : MDiffAt (fun m ↦ (w m : TotalSpace F E)) x) :
    MDiffAt (fun b ↦ ⟪v b, w b⟫) x :=
  MDifferentiableWithinAt.inner_bundle hv hw

/-- Given two differentiable maps into the same fibers of a Riemannian bundle,
their scalar product is differentiable. -/
/-
**MDifferentiableOn.inner_bundle** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.inner_bundle (hv : MDiff[s] (fun m => (v m : TotalSpace 
F E))) (hw : MDiff[s] (fun m => (w m : TotalSpace F E))) : MDiff[s] (fun b => ⟪v
 b, w b⟫)
参数：hv : MDiff[s] (fun m => (v m : TotalSpace F E))；hw : MDiff[s] (fun m => (w m 
: TotalSpace F E))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableWithinAt.inner_bundle`：MDifferentiableWithinAt.inner_bund
le (hv : MDiffAt[s] (fun m => (v m : TotalSpace F E)) x) (hw : MDiffAt[s] (fun m
 => (w m : TotalSpace F E)…

--- 原说明 ---
Given two differentiable maps into the same fibers of a Riemannian bundle,
their scalar product is differentiable.
-/
lemma MDifferentiableOn.inner_bundle
    (hv : MDiff[s] (fun m ↦ (v m : TotalSpace F E)))
    (hw : MDiff[s] (fun m ↦ (w m : TotalSpace F E))) :
    MDiff[s] (fun b ↦ ⟪v b, w b⟫) :=
  fun x hx ↦ (hv x hx).inner_bundle (hw x hx)

/-- Given two differentiable maps into the same fibers of a Riemannian bundle,
their scalar product is differentiable. -/
/-
**MDifferentiable.inner_bundle** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiable.inner_bundle (hv : MDiff (fun m => (v m : TotalSpace F E))
) (hw : MDiff (fun m => (w m : TotalSpace F E))) : MDiff (fun b => ⟪v b, w b⟫)
参数：hv : MDiff (fun m => (v m : TotalSpace F E))；hw : MDiff (fun m => (w m : Tota
lSpace F E))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableAt.inner_bundle`：MDifferentiableAt.inner_bundle (hv : MDi
ffAt (fun m => (v m : TotalSpace F E)) x) (hw : MDiffAt (fun m => (w m : TotalSp
ace F E)) x) : MDiff…

--- 原说明 ---
Given two differentiable maps into the same fibers of a Riemannian bundle,
their scalar product is differentiable.
-/
lemma MDifferentiable.inner_bundle
    (hv : MDiff (fun m ↦ (v m : TotalSpace F E)))
    (hw : MDiff (fun m ↦ (w m : TotalSpace F E))) :
    MDiff (fun b ↦ ⟪v b, w b⟫) :=
  fun x ↦ (hv x).inner_bundle (hw x)

end MDifferentiable

end

namespace Bundle

section Construction

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n n' : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

variable (IB n F E) in
/-- A family of inner product space structures on the fibers of a fiber bundle, defining the same
topology as the already existing one, and varying continuously with the base point. See also
`ContinuousRiemannianMetric` for a continuous version.

This structure is used through `RiemannianBundle` for typeclass inference, to register the inner
product space structure on the fibers without creating diamonds. -/
/-
**Bundle.ContMDiffRiemannianMetric** 是 Mathlib 中的一个归纳类型，位于命名空间 `Bundle`。
形式化陈述：{EB : Type u_1} →   [inst : NormedAddCommGroup EB] →     [inst_1 : NormedS
pace ℝ EB] →       {HB : Type u_2} →         [inst_2 : TopologicalSpace HB] →   
        ModelWithCorners ℝ EB HB →             WithTop ℕ∞ →               {B : T
ype u_3} →                 [inst : TopologicalSpace B] →                   [Char
tedSpace HB B] →                     (F : Type u_4) →                       [ins
t_4 : NormedAddCommGroup F] →                         [inst_5 : NormedSpace ℝ F]
 →                           (E : B → Type u_5) →                             [i
nst_6 : TopologicalSpace (Bundle.TotalSpace F E)] →                             
  [inst_7 : (b : B) → TopologicalSpace (E b)] →                                 
[inst_8 : (b : B) → AddCommGroup (E b)] →                                   [ins
t_9 : (b : B) → _root_.Module ℝ (E b)] →                                     [in
st_10 : FiberBundle F E] → [VectorBundle ℝ F E] → Type (max u_3 u_5)
参数：F : Type u_4；E : B → Type u_5；Bundle.TotalSpace F E；b : B；E b；b : B；E b；b : B
；E b；max u_3 u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of inner product space structures on the fibers of a fiber bundle, defi
ning the same
topology as the already existing one, and varying continuously with the base poi
nt. See also
`ContinuousRiemannianMetric` for a continuous version.

This structure is used through `RiemannianBundle` for typeclass inference, to re
gister the inner
product space structure on the fibers without creating diamonds.
-/
structure ContMDiffRiemannianMetric where
  /-- The scalar product along the fibers of the bundle. -/
  inner (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  symm (b : B) (v w : E b) : inner b v w = inner b w v
  pos (b : B) (v : E b) (hv : v ≠ 0) : 0 < inner b v v
  isVonNBounded (b : B) : IsVonNBounded ℝ {v : E b | inner b v v < 1}
  contMDiff : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
    (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (inner b))

/-- A smooth Riemannian metric defines in particular a continuous Riemannian metric. -/
/-
**Bundle.ContMDiffRiemannianMetric.toContinuousRiemannianMetric** 是 Mathlib 中的一个
定义，位于命名空间 `Bundle.ContMDiffRiemannianMetric`。
形式化陈述：{EB : Type u_1} →   [inst : NormedAddCommGroup EB] →     [inst_1 : NormedS
pace ℝ EB] →       {HB : Type u_2} →         [inst_2 : TopologicalSpace HB] →   
        {IB : ModelWithCorners ℝ EB HB} →             {n : WithTop ℕ∞} →        
       {B : Type u_3} →                 [inst_3 : TopologicalSpace B] →         
          [inst_4 : ChartedSpace HB B] →                     {F : Type u_4} →   
                    [inst_5 : NormedAddCommGroup F] →                         [i
nst_6 : NormedSpace ℝ F] →                           {E : B → Type u_5} →       
                      [inst_7 : TopologicalSpace (Bundle.TotalSpace F E)] →     
                          [inst_8 : (b : B) → TopologicalSpace (E b)] →         
                        [inst_9 : (b : B) → AddCommGroup (E b)] →               
                    [inst_10 : (b : B) → _root_.Module ℝ (E b)] →               
                      [inst_11 : FiberBundle F E] →                             
          [inst_12 : VectorBundle ℝ F E] →                                      
   Bundle.ContMDiffRiemannianMetric IB n F E →                                  
         Bundle.ContinuousRiemannianMetric F E
参数：Bundle.TotalSpace F E；b : B；E b；b : B；E b；b : B；E b。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.ContMDiffRiemannianMetric.symm`：∀ {EB : Type u_1} [inst : NormedA
ddCommGroup EB] [inst_1 : NormedSpace ℝ EB] {HB : Type u_2}   [inst_2 : Topologi
calSpace HB] {IB : ModelWit…
· 使用定理 `Bundle.ContMDiffRiemannianMetric.pos`：∀ {EB : Type u_1} [inst : NormedAd
dCommGroup EB] [inst_1 : NormedSpace ℝ EB] {HB : Type u_2}   [inst_2 : Topologic
alSpace HB] {IB : ModelWit…
· 使用定理 `Bundle.ContMDiffRiemannianMetric.isVonNBounded`：∀ {EB : Type u_1} [inst 
: NormedAddCommGroup EB] [inst_1 : NormedSpace ℝ EB] {HB : Type u_2}   [inst_2 :
 TopologicalSpace HB] {IB : ModelWit…

--- 原说明 ---
A smooth Riemannian metric defines in particular a continuous Riemannian metric.
-/
def ContMDiffRiemannianMetric.toContinuousRiemannianMetric
    (g : ContMDiffRiemannianMetric IB n F E) : ContinuousRiemannianMetric F E :=
  { g with continuous := g.contMDiff.continuous }

/-- A smooth Riemannian metric defines in particular a Riemannian metric. -/
/-
**Bundle.ContMDiffRiemannianMetric.toRiemannianMetric** 是 Mathlib 中的一个定义，位于命名空间 
`Bundle.ContMDiffRiemannianMetric`。
形式化陈述：{EB : Type u_1} →   [inst : NormedAddCommGroup EB] →     [inst_1 : NormedS
pace ℝ EB] →       {HB : Type u_2} →         [inst_2 : TopologicalSpace HB] →   
        {IB : ModelWithCorners ℝ EB HB} →             {n : WithTop ℕ∞} →        
       {B : Type u_3} →                 [inst_3 : TopologicalSpace B] →         
          [inst_4 : ChartedSpace HB B] →                     {F : Type u_4} →   
                    [inst_5 : NormedAddCommGroup F] →                         [i
nst_6 : NormedSpace ℝ F] →                           {E : B → Type u_5} →       
                      [inst_7 : TopologicalSpace (Bundle.TotalSpace F E)] →     
                          [inst_8 : (b : B) → TopologicalSpace (E b)] →         
                        [inst_9 : (b : B) → AddCommGroup (E b)] →               
                    [inst_10 : (b : B) → _root_.Module ℝ (E b)] →               
                      [inst_11 : FiberBundle F E] →                             
          [inst_12 : VectorBundle ℝ F E] →                                      
   Bundle.ContMDiffRiemannianMetric IB n F E → Bundle.RiemannianMetric E
参数：Bundle.TotalSpace F E；b : B；E b；b : B；E b；b : B；E b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A smooth Riemannian metric defines in particular a Riemannian metric.
-/
def ContMDiffRiemannianMetric.toRiemannianMetric
    (g : ContMDiffRiemannianMetric IB n F E) : RiemannianMetric E :=
  g.toContinuousRiemannianMetric.toRiemannianMetric
/-
**Bundle.** 是 Mathlib 中的一个实例，位于命名空间 `Bundle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (g : ContMDiffRiemannianMetric IB n F E) :
    letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
    IsContMDiffRiemannianBundle IB n F E :=
  letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
  ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩

end Construction

end Bundle

