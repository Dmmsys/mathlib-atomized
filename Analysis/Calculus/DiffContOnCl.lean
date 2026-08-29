/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Functions differentiable on a domain and continuous on its closure

Many theorems in complex analysis assume that a function is complex differentiable on a domain and
is continuous on its closure. In this file we define a predicate `DiffContOnCl` that expresses
this property and prove basic facts about this predicate.
-/

public section


open Set Filter Metric

open scoped Topology

variable (𝕜 : Type*) {E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] {f g : E -> F} {s t : Set E} {x : E}

/--
Definition of `DiffContOnCl` / `DiffContOnCl` 的定义

English:
structure DiffContOnCl
  parameters: (f : E -> F) (s : Set E)
  axioms and operations (2):
    - differentiableOn : DifferentiableOn 𝕜 f s
    - continuousOn : ContinuousOn f (closure s)

中文:
结构 DiffContOnCl
  参数: (f : E -> F) (s : Set E)
  公理与运算 (2 个):
    - differentiableOn : DifferentiableOn 𝕜 f s
    - continuousOn : ContinuousOn f (closure s)
-/
structure DiffContOnCl (f : E -> F) (s : Set E) : Prop where
  protected differentiableOn : DifferentiableOn 𝕜 f s
  protected continuousOn : ContinuousOn f (closure s)

variable {𝕜}

/--
theorem `DifferentiableOn.diffContOnCl` / 定理 `DifferentiableOn.diffContOnCl`

English:
theorem DifferentiableOn.diffContOnCl
  given: (h : DifferentiableOn 𝕜 f (closure s))
  statement: DiffContOnCl 𝕜 f s
  proof: ⟨h.mono subset_closure, h.continuousOn⟩

中文:
定理 DifferentiableOn.diffContOnCl
  条件: (h : DifferentiableOn 𝕜 f (closure s))
  结论: DiffContOnCl 𝕜 f s
  证明: ⟨h.mono subset_closure, h.continuousOn⟩

Depends on / 依赖: continuousOn, h.continuousOn, h.mono, subset_closure
-/
theorem DifferentiableOn.diffContOnCl (h : DifferentiableOn 𝕜 f (closure s)) : DiffContOnCl 𝕜 f s :=
  ⟨h.mono subset_closure, h.continuousOn⟩

/--
theorem `Differentiable.diffContOnCl` / 定理 `Differentiable.diffContOnCl`

English:
theorem Differentiable.diffContOnCl
  given: (h : Differentiable 𝕜 f)
  statement: DiffContOnCl 𝕜 f s
  proof: ⟨h.differentiableOn, h.continuous.continuousOn⟩

中文:
定理 Differentiable.diffContOnCl
  条件: (h : Differentiable 𝕜 f)
  结论: DiffContOnCl 𝕜 f s
  证明: ⟨h.differentiableOn, h.continuous.continuousOn⟩

Depends on / 依赖: continuous, continuousOn, differentiableOn, h.continuous.continuousOn, h.differentiableOn
-/
theorem Differentiable.diffContOnCl (h : Differentiable 𝕜 f) : DiffContOnCl 𝕜 f s :=
  ⟨h.differentiableOn, h.continuous.continuousOn⟩

/--
theorem `IsClosed.diffContOnCl_iff` / 定理 `IsClosed.diffContOnCl_iff`

English:
theorem IsClosed.diffContOnCl_iff
  given: (hs : IsClosed s)
  statement: DiffContOnCl 𝕜 f s ↔ DifferentiableOn 𝕜 f s
  proof: ⟨fun h => h.differentiableOn, fun h => ⟨h, hs.closure_eq.symm ▸ h.continuousOn⟩⟩

中文:
定理 IsClosed.diffContOnCl_iff
  条件: (hs : IsClosed s)
  结论: DiffContOnCl 𝕜 f s ↔ DifferentiableOn 𝕜 f s
  证明: ⟨fun h => h.differentiableOn, fun h => ⟨h, hs.closure_eq.symm ▸ h.continuousOn⟩⟩

Depends on / 依赖: closure_eq, continuousOn, differentiableOn, h.continuousOn, h.differentiableOn, hs.closure_eq.symm
-/
theorem IsClosed.diffContOnCl_iff (hs : IsClosed s) : DiffContOnCl 𝕜 f s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => h.differentiableOn, fun h => ⟨h, hs.closure_eq.symm ▸ h.continuousOn⟩⟩

/--
theorem `diffContOnCl_univ` / 定理 `diffContOnCl_univ`

English:
theorem diffContOnCl_univ
  statement: DiffContOnCl 𝕜 f univ ↔ Differentiable 𝕜 f
  proof: isClosed_univ.diffContOnCl_iff.trans differentiableOn_univ

中文:
定理 diffContOnCl_univ
  结论: DiffContOnCl 𝕜 f univ ↔ Differentiable 𝕜 f
  证明: isClosed_univ.diffContOnCl_iff.trans differentiableOn_univ

Depends on / 依赖: diffContOnCl_iff, differentiableOn_univ, isClosed_univ, isClosed_univ.diffContOnCl_iff.trans
-/
theorem diffContOnCl_univ : DiffContOnCl 𝕜 f univ ↔ Differentiable 𝕜 f :=
  isClosed_univ.diffContOnCl_iff.trans differentiableOn_univ

/--
theorem `diffContOnCl_const` / 定理 `diffContOnCl_const`

English:
theorem diffContOnCl_const
  given: {c : F}
  statement: DiffContOnCl 𝕜 (fun _ : E => c) s
  proof: ⟨differentiableOn_const c, continuousOn_const⟩

中文:
定理 diffContOnCl_const
  条件: {c : F}
  结论: DiffContOnCl 𝕜 (fun _ : E => c) s
  证明: ⟨differentiableOn_const c, continuousOn_const⟩

Depends on / 依赖: continuousOn_const, differentiableOn_const
-/
theorem diffContOnCl_const {c : F} : DiffContOnCl 𝕜 (fun _ : E => c) s :=
  ⟨differentiableOn_const c, continuousOn_const⟩

namespace DiffContOnCl

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  statement: {g : G -> E} {t : Set G} (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g t)
  proof: ⟨hf.1.comp hg.1 h, hf.2.comp hg.2 h.closure_of_continuousOn hg.2⟩

中文:
定理 comp
  结论: {g : G -> E} {t : Set G} (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g t)
  证明: ⟨hf.1.comp hg.1 h, hf.2.comp hg.2 h.closure_of_continuousOn hg.2⟩

Depends on / 依赖: closure_of_continuousOn, h.closure_of_continuousOn
-/
theorem comp {g : G -> E} {t : Set G} (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g t)
    (h : MapsTo g t s) : DiffContOnCl 𝕜 (f ∘ g) t :=
⟨hf.1.comp hg.1 h, hf.2.comp hg.2 h.closure_of_continuousOn hg.2⟩

/--
theorem `continuousOn_ball` / 定理 `continuousOn_ball`

English:
theorem continuousOn_ball
  given: [NormedSpace Real E] {x : E} {r : Real} (h : DiffContOnCl 𝕜 f (ball x r))
  proof: by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero]
    exact continuousOn_singleton f x
  · rw [← closure_ball x hr]
    exact h.continuousOn

中文:
定理 continuousOn_ball
  条件: [NormedSpace 实数 E] {x : E} {r : 实数} (h : DiffContOnCl 𝕜 f (ball x r))
  证明: by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero]
    exact continuousOn_singleton f x
  · rw [← closure_ball x hr]
    exact h.continuousOn

Depends on / 依赖: closedBall_zero, closure_ball, continuousOn, continuousOn_singleton, eq_or_ne, h.continuousOn
-/
theorem continuousOn_ball [NormedSpace Real E] {x : E} {r : Real} (h : DiffContOnCl 𝕜 f (ball x r)) :
    ContinuousOn f (closedBall x r) := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero]
    exact continuousOn_singleton f x
  · rw [← closure_ball x hr]
    exact h.continuousOn

/--
theorem `mk_ball` / 定理 `mk_ball`

English:
theorem mk_ball
  statement: {x : E} {r : Real} (hd : DifferentiableOn 𝕜 f (ball x r))
  proof: ⟨hd, hc.mono closure_ball_subset_closedBall⟩

中文:
定理 mk_ball
  结论: {x : E} {r : 实数} (hd : DifferentiableOn 𝕜 f (ball x r))
  证明: ⟨hd, hc.mono closure_ball_subset_closedBall⟩

Depends on / 依赖: closure_ball_subset_closedBall, hc.mono
-/
theorem mk_ball {x : E} {r : Real} (hd : DifferentiableOn 𝕜 f (ball x r))
    (hc : ContinuousOn f (closedBall x r)) : DiffContOnCl 𝕜 f (ball x r) :=
⟨hd, hc.mono closure_ball_subset_closedBall⟩

/--
theorem `differentiableAt` / 定理 `differentiableAt`

English:
theorem differentiableAt
  given: (h : DiffContOnCl 𝕜 f s) (hs : IsOpen s) (hx : x in s)
  proof: h.differentiableOn.differentiableAt hs.mem_nhds hx

中文:
定理 differentiableAt
  条件: (h : DiffContOnCl 𝕜 f s) (hs : IsOpen s) (hx : x in s)
  证明: h.differentiableOn.differentiableAt hs.mem_nhds hx
-/
protected theorem differentiableAt (h : DiffContOnCl 𝕜 f s) (hs : IsOpen s) (hx : x in s) :
    DifferentiableAt 𝕜 f x :=
h.differentiableOn.differentiableAt hs.mem_nhds hx

/--
theorem `differentiableAt'` / 定理 `differentiableAt'`

English:
theorem differentiableAt'
  given: (h : DiffContOnCl 𝕜 f s) (hx : s in 𝓝 x)
  statement: DifferentiableAt 𝕜 f x
  proof: h.differentiableOn.differentiableAt hx

中文:
定理 differentiableAt'
  条件: (h : DiffContOnCl 𝕜 f s) (hx : s in 𝓝 x)
  结论: DifferentiableAt 𝕜 f x
  证明: h.differentiableOn.differentiableAt hx

Depends on / 依赖: differentiableAt, differentiableOn, h.differentiableOn.differentiableAt
-/
theorem differentiableAt' (h : DiffContOnCl 𝕜 f s) (hx : s in 𝓝 x) : DifferentiableAt 𝕜 f x :=
  h.differentiableOn.differentiableAt hx

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (h : DiffContOnCl 𝕜 f s) (ht : t subseteq s)
  statement: DiffContOnCl 𝕜 f t
  proof: ⟨h.differentiableOn.mono ht, h.continuousOn.mono (closure_mono ht)⟩

中文:
定理 mono
  条件: (h : DiffContOnCl 𝕜 f s) (ht : t subseteq s)
  结论: DiffContOnCl 𝕜 f t
  证明: ⟨h.differentiableOn.mono ht, h.continuousOn.mono (closure_mono ht)⟩
-/
protected theorem mono (h : DiffContOnCl 𝕜 f s) (ht : t subseteq s) : DiffContOnCl 𝕜 f t :=
  ⟨h.differentiableOn.mono ht, h.continuousOn.mono (closure_mono ht)⟩

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s)
  statement: DiffContOnCl 𝕜 (f + g) s
  proof: ⟨hf.1.add hg.1, hf.2.add hg.2⟩

中文:
定理 add
  条件: (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s)
  结论: DiffContOnCl 𝕜 (f + g) s
  证明: ⟨hf.1.add hg.1, hf.2.add hg.2⟩
-/
theorem add (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s) : DiffContOnCl 𝕜 (f + g) s :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

/--
theorem `add_const` / 定理 `add_const`

English:
theorem add_const
  given: (hf : DiffContOnCl 𝕜 f s) (c : F)
  statement: DiffContOnCl 𝕜 (fun x => f x + c) s
  proof: hf.add diffContOnCl_const

中文:
定理 add_const
  条件: (hf : DiffContOnCl 𝕜 f s) (c : F)
  结论: DiffContOnCl 𝕜 (fun x => f x + c) s
  证明: hf.add diffContOnCl_const

Depends on / 依赖: diffContOnCl_const, hf.add
-/
theorem add_const (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => f x + c) s :=
  hf.add diffContOnCl_const

/--
theorem `const_add` / 定理 `const_add`

English:
theorem const_add
  given: (hf : DiffContOnCl 𝕜 f s) (c : F)
  statement: DiffContOnCl 𝕜 (fun x => c + f x) s
  proof: diffContOnCl_const.add hf

中文:
定理 const_add
  条件: (hf : DiffContOnCl 𝕜 f s) (c : F)
  结论: DiffContOnCl 𝕜 (fun x => c + f x) s
  证明: diffContOnCl_const.add hf

Depends on / 依赖: diffContOnCl_const, diffContOnCl_const.add
-/
theorem const_add (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => c + f x) s :=
  diffContOnCl_const.add hf

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (hf : DiffContOnCl 𝕜 f s)
  statement: DiffContOnCl 𝕜 (-f) s
  proof: ⟨hf.1.neg, hf.2.neg⟩

中文:
定理 neg
  条件: (hf : DiffContOnCl 𝕜 f s)
  结论: DiffContOnCl 𝕜 (-f) s
  证明: ⟨hf.1.neg, hf.2.neg⟩
-/
theorem neg (hf : DiffContOnCl 𝕜 f s) : DiffContOnCl 𝕜 (-f) s :=
  ⟨hf.1.neg, hf.2.neg⟩

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s)
  statement: DiffContOnCl 𝕜 (f - g) s
  proof: ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

中文:
定理 sub
  条件: (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s)
  结论: DiffContOnCl 𝕜 (f - g) s
  证明: ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩
-/
theorem sub (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s) : DiffContOnCl 𝕜 (f - g) s :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

/--
theorem `sub_const` / 定理 `sub_const`

English:
theorem sub_const
  given: (hf : DiffContOnCl 𝕜 f s) (c : F)
  statement: DiffContOnCl 𝕜 (fun x => f x - c) s
  proof: hf.sub diffContOnCl_const

中文:
定理 sub_const
  条件: (hf : DiffContOnCl 𝕜 f s) (c : F)
  结论: DiffContOnCl 𝕜 (fun x => f x - c) s
  证明: hf.sub diffContOnCl_const

Depends on / 依赖: diffContOnCl_const, hf.sub
-/
theorem sub_const (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => f x - c) s :=
  hf.sub diffContOnCl_const

/--
theorem `const_sub` / 定理 `const_sub`

English:
theorem const_sub
  given: (hf : DiffContOnCl 𝕜 f s) (c : F)
  statement: DiffContOnCl 𝕜 (fun x => c - f x) s
  proof: diffContOnCl_const.sub hf

中文:
定理 const_sub
  条件: (hf : DiffContOnCl 𝕜 f s) (c : F)
  结论: DiffContOnCl 𝕜 (fun x => c - f x) s
  证明: diffContOnCl_const.sub hf

Depends on / 依赖: diffContOnCl_const, diffContOnCl_const.sub
-/
theorem const_sub (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => c - f x) s :=
  diffContOnCl_const.sub hf

/--
theorem `const_smul` / 定理 `const_smul`

English:
theorem const_smul
  statement: {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F]
  proof: ⟨hf.1.const_smul c, hf.2.const_smul c⟩

中文:
定理 const_smul
  结论: {R : 类型} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F]
  证明: ⟨hf.1.const_smul c, hf.2.const_smul c⟩

Depends on / 依赖: const_smul
-/
theorem const_smul {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F]
    [ContinuousConstSMul R F] (hf : DiffContOnCl 𝕜 f s) (c : R) : DiffContOnCl 𝕜 (c • f) s :=
  ⟨hf.1.const_smul c, hf.2.const_smul c⟩

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  proof: ⟨hc.1.smul hf.1, hc.2.smul hf.2⟩

中文:
定理 smul
  结论: {𝕜' : 类型} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  证明: ⟨hc.1.smul hf.1, hc.2.smul hf.2⟩
-/
theorem smul {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
    [IsScalarTower 𝕜 𝕜' F] {c : E -> 𝕜'} {f : E -> F} {s : Set E} (hc : DiffContOnCl 𝕜 c s)
    (hf : DiffContOnCl 𝕜 f s) : DiffContOnCl 𝕜 (fun x => c x • f x) s :=
  ⟨hc.1.smul hf.1, hc.2.smul hf.2⟩

/--
theorem `smul_const` / 定理 `smul_const`

English:
theorem smul_const
  statement: {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  proof: hc.smul diffContOnCl_const

中文:
定理 smul_const
  结论: {𝕜' : 类型} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  证明: hc.smul diffContOnCl_const

Depends on / 依赖: diffContOnCl_const, hc.smul
-/
theorem smul_const {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F] {c : E -> 𝕜'} {s : Set E} (hc : DiffContOnCl 𝕜 c s)
    (y : F) : DiffContOnCl 𝕜 (fun x => c x • y) s :=
  hc.smul diffContOnCl_const

/--
theorem `inv` / 定理 `inv`

English:
theorem inv
  given: {f : E -> 𝕜} (hf : DiffContOnCl 𝕜 f s) (h₀ : forall x in closure s, f x != 0)
  proof: ⟨(differentiableOn_inv.comp hf.1 fun _ hx => h₀ _ (subset_closure hx) :), hf.2.inv₀ h₀⟩

中文:
定理 inv
  条件: {f : E -> 𝕜} (hf : DiffContOnCl 𝕜 f s) (h₀ : 对任意 x in closure s, f x != 0)
  证明: ⟨(differentiableOn_inv.comp hf.1 fun _ hx => h₀ _ (subset_closure hx) :), hf.2.inv₀ h₀⟩

Depends on / 依赖: differentiableOn_inv, differentiableOn_inv.comp, subset_closure
-/
theorem inv {f : E -> 𝕜} (hf : DiffContOnCl 𝕜 f s) (h₀ : forall x in closure s, f x != 0) :
    DiffContOnCl 𝕜 f⁻¹ s :=
  ⟨(differentiableOn_inv.comp hf.1 fun _ hx => h₀ _ (subset_closure hx) :), hf.2.inv₀ h₀⟩

end DiffContOnCl

/--
theorem `Differentiable.comp_diffContOnCl` / 定理 `Differentiable.comp_diffContOnCl`

English:
theorem Differentiable.comp_diffContOnCl
  statement: {g : G -> E} {t : Set G} (hf : Differentiable 𝕜 f)
  proof: hf.diffContOnCl.comp hg (mapsTo_image _ _)

中文:
定理 Differentiable.comp_diffContOnCl
  结论: {g : G -> E} {t : Set G} (hf : Differentiable 𝕜 f)
  证明: hf.diffContOnCl.comp hg (mapsTo_image _ _)

Depends on / 依赖: diffContOnCl, hf.diffContOnCl.comp, mapsTo_image
-/
theorem Differentiable.comp_diffContOnCl {g : G -> E} {t : Set G} (hf : Differentiable 𝕜 f)
    (hg : DiffContOnCl 𝕜 g t) : DiffContOnCl 𝕜 (f ∘ g) t :=
  hf.diffContOnCl.comp hg (mapsTo_image _ _)

/--
theorem `DifferentiableOn.diffContOnCl_ball` / 定理 `DifferentiableOn.diffContOnCl_ball`

English:
theorem DifferentiableOn.diffContOnCl_ball
  statement: {U : Set E} {c : E} {R : Real} (hf : DifferentiableOn 𝕜 f U)
  proof: DiffContOnCl.mk_ball (hf.mono (ball_subset_closedBall.trans hc)) (hf.continuousOn.mono hc)

中文:
定理 DifferentiableOn.diffContOnCl_ball
  结论: {U : Set E} {c : E} {R : 实数} (hf : DifferentiableOn 𝕜 f U)
  证明: DiffContOnCl.mk_ball (hf.mono (ball_subset_closedBall.trans hc)) (hf.continuousOn.mono hc)

Depends on / 依赖: DiffContOnCl, DiffContOnCl.mk_ball, ball_subset_closedBall, ball_subset_closedBall.trans, continuousOn, hf.continuousOn.mono, hf.mono, mk_ball
-/
theorem DifferentiableOn.diffContOnCl_ball {U : Set E} {c : E} {R : Real} (hf : DifferentiableOn 𝕜 f U)
    (hc : closedBall c R subseteq U) : DiffContOnCl 𝕜 f (ball c R) :=
  DiffContOnCl.mk_ball (hf.mono (ball_subset_closedBall.trans hc)) (hf.continuousOn.mono hc)
