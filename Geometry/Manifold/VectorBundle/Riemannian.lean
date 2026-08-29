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
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace Real EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners Real EB HB} {n n' : Nat∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  {E : B -> Type*} [TopologicalSpace (TotalSpace F E)] [forall x, NormedAddCommGroup (E x)]
  [forall x, InnerProductSpace Real (E x)]
  [FiberBundle F E] [VectorBundle Real F E]

local notation "⟪" x ", " y "⟫" => inner Real x y

variable (IB n F E) in
/--
Definition of `IsContMDiffRiemannianBundle` / `IsContMDiffRiemannianBundle` 的定义

English:
class IsContMDiffRiemannianBundle
  parameters: : Prop where
  axioms and operations (1):
    - exists_contMDiff : exists g : Π (x : B), E x ->L[Real] E x ->L[Real] Real, ContMDiff IB (IB.prod 𝓘(Real, F ->L[Real] F ->L[Real] Real)) n (fun b => TotalSpace.mk' (F ->L[Real] F ->L[Real] Real) b (g b)) ∧ forall (x : B) (v w : E x), ⟪v, w⟫ = g x v w

中文:
类 是余ntMDiffRiemannianBundle
  参数: : 命题 where
  公理与运算 (1 个):
    - exists_contMDiff : 存在 g : Π (x : B), E x ->L[实数] E x ->L[实数] 实数, ContMDiff IB (IB.乘积 𝓘(实数, F ->L[实数] F ->L[实数] 实数)) n (fun b => 全空间.mk' (F ->L[实数] F ->L[实数] 实数) b (g b)) ∧ 对任意 (x : B) (v w : E x), ⟪v, w⟫ = g x v w
-/
class IsContMDiffRiemannianBundle : Prop where
  exists_contMDiff : exists g : Π (x : B), E x ->L[Real] E x ->L[Real] Real,
    ContMDiff IB (IB.prod 𝓘(Real, F ->L[Real] F ->L[Real] Real)) n
      (fun b => TotalSpace.mk' (F ->L[Real] F ->L[Real] Real) b (g b))
    ∧ forall (x : B) (v w : E x), ⟪v, w⟫ = g x v w

/--
lemma `IsContMDiffRiemannianBundle.of_le` / 引理 `IsContMDiffRiemannianBundle.of_le`

English:
lemma IsContMDiffRiemannianBundle.of_le
  given: [h : IsContMDiffRiemannianBundle IB n F E] (h' : n' <= n)
  proof: by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  exact ⟨g, g_smooth.of_le h', hg⟩

中文:
引理 是余ntMDiffRiemannianBundle.of_le
  条件: [h : 是余ntMDiffRiemannianBundle IB n F E] (h' : n' <= n)
  证明: by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  exact ⟨g, g_smooth.of_le h', hg⟩

Depends on / 依赖: exists_contMDiff, g_smooth, g_smooth.of_le, h.exists_contMDiff, of_le
-/
lemma IsContMDiffRiemannianBundle.of_le [h : IsContMDiffRiemannianBundle IB n F E] (h' : n' <= n) :
    IsContMDiffRiemannianBundle IB n' F E := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  exact ⟨g, g_smooth.of_le h', hg⟩

instance {a : Nat∞ω} [IsContMDiffRiemannianBundle IB ∞ F E] [h : LEInfty a] :
    IsContMDiffRiemannianBundle IB a F E :=
  IsContMDiffRiemannianBundle.of_le h.out

instance {a : Nat∞ω} [IsContMDiffRiemannianBundle IB ω F E] :
    IsContMDiffRiemannianBundle IB a F E :=
  IsContMDiffRiemannianBundle.of_le le_top

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsContMDiffRiemannianBundle
  signature: IB 1 F E] : IsContMDiffRiemannianBundle IB 0 F E
  body: IsContMDiffRiemannianBundle.of_le zero_le_one

中文:
实例 [是余ntMDiffRiemannianBundle
  签名: IB 1 F E] : 是余ntMDiffRiemannianBundle IB 0 F E
  定义体: IsContMDiffRiemannianBundle.of_le zero_le_one

Depends on / 依赖: IsContMDiffRiemannianBundle, IsContMDiffRiemannianBundle.of_le, of_le, zero_le_one
-/
instance [IsContMDiffRiemannianBundle IB 1 F E] : IsContMDiffRiemannianBundle IB 0 F E :=
  IsContMDiffRiemannianBundle.of_le zero_le_one

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsContMDiffRiemannianBundle
  signature: IB 2 F E] : IsContMDiffRiemannianBundle IB 1 F E
  body: IsContMDiffRiemannianBundle.of_le one_le_two

中文:
实例 [是余ntMDiffRiemannianBundle
  签名: IB 2 F E] : 是余ntMDiffRiemannianBundle IB 1 F E
  定义体: IsContMDiffRiemannianBundle.of_le one_le_two

Depends on / 依赖: IsContMDiffRiemannianBundle, IsContMDiffRiemannianBundle.of_le, of_le, one_le_two
-/
instance [IsContMDiffRiemannianBundle IB 2 F E] : IsContMDiffRiemannianBundle IB 1 F E :=
  IsContMDiffRiemannianBundle.of_le one_le_two

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsContMDiffRiemannianBundle
  signature: IB 3 F E] : IsContMDiffRiemannianBundle IB 2 F E
  body: IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_cast)

中文:
实例 [是余ntMDiffRiemannianBundle
  签名: IB 3 F E] : 是余ntMDiffRiemannianBundle IB 2 F E
  定义体: IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_cast)

Depends on / 依赖: IsContMDiffRiemannianBundle, IsContMDiffRiemannianBundle.of_le, of_le
-/
instance [IsContMDiffRiemannianBundle IB 3 F E] : IsContMDiffRiemannianBundle IB 2 F E :=
  IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_cast)

section Trivial

variable {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace Real F₁]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsContMDiffRiemannianBundle IB n F₁ (Bundle.Trivial B F₁)
  body: by
  refine ⟨fun x => innerSL Real, fun x => ?_, fun x v w => rfl⟩
  simp only [contMDiffAt_section]
  convert! contMDiffAt_const (c := innerSL Real)
  ext v w
  simp [hom_trivializationAt_apply, inCoordinates]

中文:
实例 :
  签名: 是余ntMDiffRiemannianBundle IB n F₁ (Bundle.平凡 B F₁)
  定义体: by
  refine ⟨fun x => innerSL Real, fun x => ?_, fun x v w => rfl⟩
  simp only [contMDiffAt_section]
  convert! contMDiffAt_const (c := innerSL Real)
  ext v w
  simp [hom_trivializationAt_apply, inCoordinates]

Depends on / 依赖: contMDiffAt_const, contMDiffAt_section, convert, hom_trivializationAt_apply, inCoordinates, innerSL
-/
instance : IsContMDiffRiemannianBundle IB n F₁ (Bundle.Trivial B F₁) := by
  refine ⟨fun x => innerSL Real, fun x => ?_, fun x v w => rfl⟩
  simp only [contMDiffAt_section]
  convert! contMDiffAt_const (c := innerSL Real)
  ext v w
  simp [hom_trivializationAt_apply, inCoordinates]

end Trivial

section ContMDiff

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace Real EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners Real EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [h : IsContMDiffRiemannianBundle IB n F E]
  {b : M -> B} {v w : forall x, E (b x)} {s : Set M} {x : M}

/--
lemma `ContMDiffWithinAt.inner_bundle` / 引理 `ContMDiffWithinAt.inner_bundle`

English:
lemma ContMDiffWithinAt.inner_bundle
  proof: by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  have hb : CMDiffAt[s] n b x := by
    simp only [contMDiffWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : ContMDiffWithinAt IM (IB.prod 𝓘(Real)) n
      (fun m => TotalSpace.mk' Real (E := Bundle.Trivial B Real) (b m) (g (b 

中文:
引理 ContMDiffWithinAt.inner_bundle
  证明: by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  have hb : CMDiffAt[s] n b x := by
    simp only [contMDiffWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : ContMDiffWithinAt IM (IB.prod 𝓘(Real)) n
      (fun m => TotalSpace.mk' Real (E := Bundle.Trivial B Real) (b m) (g (b 

Depends on / 依赖: Bundle, Bundle.Trivial, CMDiffAt, ContMDiffAt, ContMDiffAt.comp_contMDiffWithinAt, ContMDiffWithinAt, ContMDiffWithinAt.clm_bundle_apply, IB.prod, TotalSpace, TotalSpace.mk, Trivial, comp_contMDiffWithinAt, contMDiffAt, contMDiffWithinAt_totalSpace, exists_contMDiff, g_smooth, g_smooth.contMDiffAt, h.exists_contMDiff
-/
lemma ContMDiffWithinAt.inner_bundle
    (hv : CMDiffAt[s] n (fun m => (v m : TotalSpace F E)) x)
    (hw : CMDiffAt[s] n (fun m => (w m : TotalSpace F E)) x) :
    CMDiffAt[s] n (fun m => ⟪v m, w m⟫) x := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  have hb : CMDiffAt[s] n b x := by
    simp only [contMDiffWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : ContMDiffWithinAt IM (IB.prod 𝓘(Real)) n
      (fun m => TotalSpace.mk' Real (E := Bundle.Trivial B Real) (b m) (g (b m) (v m) (w m))) s x := by
    apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact ContMDiffAt.comp_contMDiffWithinAt x g_smooth.contMDiffAt hb
    · exact hv
    · exact hw
  simp only [contMDiffWithinAt_totalSpace] at this
  exact this.2

/--
lemma `ContMDiffAt.inner_bundle` / 引理 `ContMDiffAt.inner_bundle`

English:
lemma ContMDiffAt.inner_bundle
  proof: ContMDiffWithinAt.inner_bundle hv hw

中文:
引理 ContMDiffAt.inner_bundle
  证明: ContMDiffWithinAt.inner_bundle hv hw

Depends on / 依赖: ContMDiffWithinAt, ContMDiffWithinAt.inner_bundle, inner_bundle
-/
lemma ContMDiffAt.inner_bundle
    (hv : CMDiffAt n (fun m => (v m : TotalSpace F E)) x)
    (hw : CMDiffAt n (fun m => (w m : TotalSpace F E)) x) :
    CMDiffAt n (fun b => ⟪v b, w b⟫) x :=
  ContMDiffWithinAt.inner_bundle hv hw

/--
lemma `ContMDiffOn.inner_bundle` / 引理 `ContMDiffOn.inner_bundle`

English:
lemma ContMDiffOn.inner_bundle
  proof: fun x hx => (hv x hx).inner_bundle (hw x hx)

中文:
引理 ContMDiffOn.inner_bundle
  证明: fun x hx => (hv x hx).inner_bundle (hw x hx)

Depends on / 依赖: inner_bundle
-/
lemma ContMDiffOn.inner_bundle
    (hv : CMDiff[s] n (fun m => (v m : TotalSpace F E)))
    (hw : CMDiff[s] n (fun m => (w m : TotalSpace F E))) :
    CMDiff[s] n (fun b => ⟪v b, w b⟫) :=
  fun x hx => (hv x hx).inner_bundle (hw x hx)

/--
lemma `ContMDiff.inner_bundle` / 引理 `ContMDiff.inner_bundle`

English:
lemma ContMDiff.inner_bundle
  proof: fun x => (hv x).inner_bundle (hw x)

中文:
引理 ContMDiff.inner_bundle
  证明: fun x => (hv x).inner_bundle (hw x)

Depends on / 依赖: inner_bundle
-/
lemma ContMDiff.inner_bundle
    (hv : CMDiff n (fun m => (v m : TotalSpace F E)))
    (hw : CMDiff n (fun m => (w m : TotalSpace F E))) :
    CMDiff n (fun b => ⟪v b, w b⟫) :=
  fun x => (hv x).inner_bundle (hw x)

end ContMDiff

section MDifferentiable

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace Real EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners Real EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [h : IsContMDiffRiemannianBundle IB 1 F E]
  {b : M -> B} {v w : forall x, E (b x)} {s : Set M} {x : M}

/--
lemma `MDifferentiableWithinAt.inner_bundle` / 引理 `MDifferentiableWithinAt.inner_bundle`

English:
lemma MDifferentiableWithinAt.inner_bundle
  proof: by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  have hb : MDiffAt[s] b x := by
    simp only [mdifferentiableWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : MDifferentiableWithinAt IM (IB.prod 𝓘(Real))
      (fun m => TotalSpace.mk' Real (E := Bundle.Trivial B Real) (b m)

中文:
引理 MDifferentiableWithinAt.inner_bundle
  证明: by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  have hb : MDiffAt[s] b x := by
    simp only [mdifferentiableWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : MDifferentiableWithinAt IM (IB.prod 𝓘(Real))
      (fun m => TotalSpace.mk' Real (E := Bundle.Trivial B Real) (b m)

Depends on / 依赖: Bundle, Bundle.Trivial, IB.prod, MDiffAt, MDifferentiableAt, MDifferentiableAt.comp_mdifferentiableWithinAt, MDifferentiableWithinAt, MDifferentiableWithinAt.clm_bundle_apply, TotalSpace, TotalSpace.mk, Trivial, comp_mdifferentiableWithinAt, exists_contMDiff, g_smooth, g_smooth.mdifferentiableAt, h.exists_contMDiff, mdifferentiableAt, mdifferentiableWithinAt_totalSpace, one_ne_zero
-/
lemma MDifferentiableWithinAt.inner_bundle
    (hv : MDiffAt[s] (fun m => (v m : TotalSpace F E)) x)
    (hw : MDiffAt[s] (fun m => (w m : TotalSpace F E)) x) :
    MDiffAt[s] (fun m => ⟪v m, w m⟫) x := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  have hb : MDiffAt[s] b x := by
    simp only [mdifferentiableWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : MDifferentiableWithinAt IM (IB.prod 𝓘(Real))
      (fun m => TotalSpace.mk' Real (E := Bundle.Trivial B Real) (b m) (g (b m) (v m) (w m))) s x := by
    apply MDifferentiableWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact MDifferentiableAt.comp_mdifferentiableWithinAt x
        (g_smooth.mdifferentiableAt one_ne_zero) hb
    · exact hv
    · exact hw
  simp only [mdifferentiableWithinAt_totalSpace] at this
  exact this.2

/--
lemma `MDifferentiableAt.inner_bundle` / 引理 `MDifferentiableAt.inner_bundle`

English:
lemma MDifferentiableAt.inner_bundle
  proof: MDifferentiableWithinAt.inner_bundle hv hw

中文:
引理 MDifferentiableAt.inner_bundle
  证明: MDifferentiableWithinAt.inner_bundle hv hw

Depends on / 依赖: MDifferentiableWithinAt, MDifferentiableWithinAt.inner_bundle, inner_bundle
-/
lemma MDifferentiableAt.inner_bundle
    (hv : MDiffAt (fun m => (v m : TotalSpace F E)) x)
    (hw : MDiffAt (fun m => (w m : TotalSpace F E)) x) :
    MDiffAt (fun b => ⟪v b, w b⟫) x :=
  MDifferentiableWithinAt.inner_bundle hv hw

/--
lemma `MDifferentiableOn.inner_bundle` / 引理 `MDifferentiableOn.inner_bundle`

English:
lemma MDifferentiableOn.inner_bundle
  proof: fun x hx => (hv x hx).inner_bundle (hw x hx)

中文:
引理 MDifferentiableOn.inner_bundle
  证明: fun x hx => (hv x hx).inner_bundle (hw x hx)

Depends on / 依赖: inner_bundle
-/
lemma MDifferentiableOn.inner_bundle
    (hv : MDiff[s] (fun m => (v m : TotalSpace F E)))
    (hw : MDiff[s] (fun m => (w m : TotalSpace F E))) :
    MDiff[s] (fun b => ⟪v b, w b⟫) :=
  fun x hx => (hv x hx).inner_bundle (hw x hx)

/--
lemma `MDifferentiable.inner_bundle` / 引理 `MDifferentiable.inner_bundle`

English:
lemma MDifferentiable.inner_bundle
  proof: fun x => (hv x).inner_bundle (hw x)

中文:
引理 MDifferentiable.inner_bundle
  证明: fun x => (hv x).inner_bundle (hw x)

Depends on / 依赖: inner_bundle
-/
lemma MDifferentiable.inner_bundle
    (hv : MDiff (fun m => (v m : TotalSpace F E)))
    (hw : MDiff (fun m => (w m : TotalSpace F E))) :
    MDiff (fun b => ⟪v b, w b⟫) :=
  fun x => (hv x).inner_bundle (hw x)

end MDifferentiable

end

namespace Bundle

section Construction

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace Real EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners Real EB HB} {n n' : Nat∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  {E : B -> Type*} [TopologicalSpace (TotalSpace F E)]
  [forall b, TopologicalSpace (E b)] [forall b, AddCommGroup (E b)] [forall b, Module Real (E b)]
  [forall b, IsTopologicalAddGroup (E b)] [forall b, ContinuousConstSMul Real (E b)]
  [FiberBundle F E] [VectorBundle Real F E]

variable (IB n F E) in
/--
Definition of `ContMDiffRiemannianMetric` / `ContMDiffRiemannianMetric` 的定义

English:
structure ContMDiffRiemannianMetric
  parameters: where
  axioms and operations (5):
    - inner((b : B)) : E b ->L[Real] E b ->L[Real] Real
    - symm((b : B) (v w : E b)) : inner b v w = inner b w v
    - pos((b : B) (v : E b) (hv : v != 0)) : 0 < inner b v v
    - isVonNBounded((b : B)) : IsVonNBounded Real {v : E b | inner b v v < 1}
    - contMDiff : ContMDiff IB (IB.prod 𝓘(Real, F ->L[Real] F ->L[Real] Real)) n (fun b => TotalSpace.mk' (F ->L[Real] F ->L[Real] Real) b (inner b))

中文:
结构 余ntMDiffRiemannianMetric
  参数: where
  公理与运算 (5 个):
    - inner((b : B)) : E b ->L[实数] E b ->L[实数] 实数
    - symm((b : B) (v w : E b)) : inner b v w = inner b w v
    - pos((b : B) (v : E b) (hv : v != 0)) : 0 < inner b v v
    - isVonNBounded((b : B)) : IsVonNBounded 实数 {v : E b | inner b v v < 1}
    - contMDiff : ContMDiff IB (IB.乘积 𝓘(实数, F ->L[实数] F ->L[实数] 实数)) n (fun b => 全空间.mk' (F ->L[实数] F ->L[实数] 实数) b (inner b))
-/
structure ContMDiffRiemannianMetric where
  /-- The scalar product along the fibers of the bundle. -/
  inner (b : B) : E b ->L[Real] E b ->L[Real] Real
  symm (b : B) (v w : E b) : inner b v w = inner b w v
  pos (b : B) (v : E b) (hv : v != 0) : 0 < inner b v v
  isVonNBounded (b : B) : IsVonNBounded Real {v : E b | inner b v v < 1}
  contMDiff : ContMDiff IB (IB.prod 𝓘(Real, F ->L[Real] F ->L[Real] Real)) n
    (fun b => TotalSpace.mk' (F ->L[Real] F ->L[Real] Real) b (inner b))

/--
Definition of `ContMDiffRiemannianMetric.toContinuousRiemannianMetric` / `ContMDiffRiemannianMetric.toContinuousRiemannianMetric` 的定义

English:
definition ContMDiffRiemannianMetric.toContinuousRiemannianMetric
  body: { g with continuous := g.contMDiff.continuous }

中文:
定义 余ntMDiffRiemannianMetric.toContinuousRiemannianMetric
  定义体: { g with continuous := g.contMDiff.continuous }

Depends on / 依赖: contMDiff, continuous, g.contMDiff.continuous
-/
def ContMDiffRiemannianMetric.toContinuousRiemannianMetric
    (g : ContMDiffRiemannianMetric IB n F E) : ContinuousRiemannianMetric F E :=
  { g with continuous := g.contMDiff.continuous }

/--
Definition of `ContMDiffRiemannianMetric.toRiemannianMetric` / `ContMDiffRiemannianMetric.toRiemannianMetric` 的定义

English:
definition ContMDiffRiemannianMetric.toRiemannianMetric
  body: g.toContinuousRiemannianMetric.toRiemannianMetric

中文:
定义 余ntMDiffRiemannianMetric.toRiemannianMetric
  定义体: g.toContinuousRiemannianMetric.toRiemannianMetric

Depends on / 依赖: g.toContinuousRiemannianMetric.toRiemannianMetric, toContinuousRiemannianMetric, toRiemannianMetric
-/
def ContMDiffRiemannianMetric.toRiemannianMetric
    (g : ContMDiffRiemannianMetric IB n F E) : RiemannianMetric E :=
  g.toContinuousRiemannianMetric.toRiemannianMetric

instance (g : ContMDiffRiemannianMetric IB n F E) :
    letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
    IsContMDiffRiemannianBundle IB n F E :=
  letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
  ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩

end Construction

end Bundle
