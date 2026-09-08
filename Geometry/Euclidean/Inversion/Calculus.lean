/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.AdaptationNote

/-!
# Derivative of the inversion

In this file we prove a formula for the derivative of `EuclideanGeometry.inversion c R`.

## Implementation notes

Since `fderiv` and related definitions do not work for affine spaces, we deal with an inner product
space in this file.

## Keywords

inversion, derivative
-/

public section

open Metric Function AffineMap Set AffineSubspace
open scoped Topology RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

open EuclideanGeometry

section DotNotation

variable {c x : E → F} {R : E → ℝ} {s : Set E} {a : E} {n : ℕ∞}

/-
**ContDiffWithinAt.inversion** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffWithinAt`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : InnerProductSpace ℝ F
] {c x : E → F} {R : E → ℝ} {s : Set E} {a : E} {n : ℕ∞},   ContDiffWithinAt ℝ (
↑n) c s a →     ContDiffWithinAt ℝ (↑n) R s a →       ContDiffWithinAt ℝ (↑n) x 
s a →         x a ≠ c a → ContDiffWithinAt ℝ (↑n) (fun a => EuclideanGeometry.in
version (c a) (R a) (x a)) s a
参数：↑n；↑n；↑n；↑n；fun a => EuclideanGeometry.inversion (c a) (R a) (x a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.add`：ContDiffWithinAt.add {s : Set E} {f g : E -> F} (h
f : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWith
inAt 𝕜 n (…
· 使用定理 `ContDiffWithinAt.smul`：ContDiffWithinAt.smul {s : Set E} {f : E -> 𝕜'} {
g : E -> F} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) 
: ContDiffW…
· 使用定理 `ContDiffWithinAt.pow`：ContDiffWithinAt.pow {f : E -> 𝔸} (hf : ContDiffWi
thinAt 𝕜 n f s x) (m : Nat) : ContDiffWithinAt 𝕜 n (fun y => f y ^ m) s x
· 使用定理 `ContDiffWithinAt.div`：ContDiffWithinAt.div {f g : E -> 𝕜} {n} (hf : Cont
DiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) (hx : g x != 0) : Cont
DiffWithin…
· 使用定理 `ContDiffWithinAt.dist`：ContDiffWithinAt.dist (hf : ContDiffWithinAt Real
 n f s x) (hg : ContDiffWithinAt Real n g s x) (hne : f x != g x) : ContDiffWith
inAt Real n…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dist_ne_zero`：dist_ne_zero {x y : γ} : dist x y != 0 ↔ x != y
· 使用定理 `ContDiffWithinAt.sub`：ContDiffWithinAt.sub {s : Set E} {f g : E -> F} (h
f : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWith
inAt 𝕜 n (…
-/
protected theorem ContDiffWithinAt.inversion (hc : ContDiffWithinAt ℝ n c s a)
    (hR : ContDiffWithinAt ℝ n R s a) (hx : ContDiffWithinAt ℝ n x s a) (hne : x a ≠ c a) :
    ContDiffWithinAt ℝ n (fun a ↦ inversion (c a) (R a) (x a)) s a :=
  (((hR.div (hx.dist ℝ hc hne) (dist_ne_zero.2 hne)).pow _).smul (hx.sub hc)).add hc
/-
**ContDiffOn.inversion** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffOn`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : InnerProductSpace ℝ F
] {c x : E → F} {R : E → ℝ} {s : Set E} {n : ℕ∞},   ContDiffOn ℝ (↑n) c s →     
ContDiffOn ℝ (↑n) R s →       ContDiffOn ℝ (↑n) x s →         (∀ a ∈ s, x a ≠ c 
a) → ContDiffOn ℝ (↑n) (fun a => EuclideanGeometry.inversion (c a) (R a) (x a)) 
s
参数：↑n；↑n；↑n；∀ a ∈ s, x a ≠ c a；↑n；fun a => EuclideanGeometry.inversion (c a) (R 
a) (x a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.inversion`：∀ {E : Type u_1} {F : Type u_2} [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [
inst_3 : InnerPr…
-/
protected theorem ContDiffOn.inversion (hc : ContDiffOn ℝ n c s) (hR : ContDiffOn ℝ n R s)
    (hx : ContDiffOn ℝ n x s) (hne : ∀ a ∈ s, x a ≠ c a) :
    ContDiffOn ℝ n (fun a ↦ inversion (c a) (R a) (x a)) s := fun a ha ↦
  (hc a ha).inversion (hR a ha) (hx a ha) (hne a ha)

protected nonrec theorem ContDiffAt.inversion (hc : ContDiffAt ℝ n c a) (hR : ContDiffAt ℝ n R a)
    (hx : ContDiffAt ℝ n x a) (hne : x a ≠ c a) :
    ContDiffAt ℝ n (fun a ↦ inversion (c a) (R a) (x a)) a :=
  hc.inversion hR hx hne

protected nonrec theorem ContDiff.inversion (hc : ContDiff ℝ n c) (hR : ContDiff ℝ n R)
    (hx : ContDiff ℝ n x) (hne : ∀ a, x a ≠ c a) :
    ContDiff ℝ n (fun a ↦ inversion (c a) (R a) (x a)) :=
  contDiff_iff_contDiffAt.2 fun a ↦ hc.contDiffAt.inversion hR.contDiffAt hx.contDiffAt (hne a)
/-
**DifferentiableWithinAt.inversion** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableWith
inAt`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : InnerProductSpace ℝ F
] {c x : E → F} {R : E → ℝ} {s : Set E} {a : E},   DifferentiableWithinAt ℝ c s 
a →     DifferentiableWithinAt ℝ R s a →       DifferentiableWithinAt ℝ x s a → 
        x a ≠ c a → DifferentiableWithinAt ℝ (fun a => EuclideanGeometry.inversi
on (c a) (R a) (x a)) s a
参数：fun a => EuclideanGeometry.inversion (c a) (R a) (x a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.add`：DifferentiableWithinAt.add (hf : Differentia
bleWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithi
nAt 𝕜 (f + g) s …
· 使用定理 `DifferentiableWithinAt.smul`：DifferentiableWithinAt.smul (hc : Different
iableWithinAt 𝕜 c s x) (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWit
hinAt 𝕜 (c • f) s…
· 使用定理 `DifferentiableWithinAt.pow`：DifferentiableWithinAt.pow (hf : Differentia
bleWithinAt 𝕜 f s x) : forall n : Nat, DifferentiableWithinAt 𝕜 (f ^ n) s x
· 使用定理 `DifferentiableWithinAt.mul`：DifferentiableWithinAt.mul (ha : Differentia
bleWithinAt 𝕜 a s x) (hb : DifferentiableWithinAt 𝕜 b s x) : DifferentiableWithi
nAt 𝕜 (a * b) s …
· 使用定理 `DifferentiableWithinAt.inv`：DifferentiableWithinAt.inv (hf : Differentia
bleWithinAt 𝕜 h S z) (hz : h z != 0) : DifferentiableWithinAt 𝕜 (h⁻¹) S z
· 使用定理 `DifferentiableWithinAt.dist`：DifferentiableWithinAt.dist (hf : Different
iableWithinAt Real f s x) (hg : DifferentiableWithinAt Real g s x) (hne : f x !=
 g x) : Different…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dist_ne_zero`：dist_ne_zero {x y : γ} : dist x y != 0 ↔ x != y
· 使用定理 `DifferentiableWithinAt.sub`：DifferentiableWithinAt.sub (hf : Differentia
bleWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithi
nAt 𝕜 (f - g) s …
-/
protected theorem DifferentiableWithinAt.inversion (hc : DifferentiableWithinAt ℝ c s a)
    (hR : DifferentiableWithinAt ℝ R s a) (hx : DifferentiableWithinAt ℝ x s a) (hne : x a ≠ c a) :
    DifferentiableWithinAt ℝ (fun a ↦ inversion (c a) (R a) (x a)) s a :=
  -- TODO: Use `.div` https://github.com/leanprover-community/mathlib4/issues/5870
  (((hR.mul <| (hx.dist ℝ hc hne).inv (dist_ne_zero.2 hne)).pow _).smul (hx.sub hc)).add hc
/-
**DifferentiableOn.inversion** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableOn`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : InnerProductSpace ℝ F
] {c x : E → F} {R : E → ℝ} {s : Set E},   DifferentiableOn ℝ c s →     Differen
tiableOn ℝ R s →       DifferentiableOn ℝ x s →         (∀ a ∈ s, x a ≠ c a) → D
ifferentiableOn ℝ (fun a => EuclideanGeometry.inversion (c a) (R a) (x a)) s
参数：∀ a ∈ s, x a ≠ c a；fun a => EuclideanGeometry.inversion (c a) (R a) (x a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.inversion`：∀ {E : Type u_1} {F : Type u_2} [inst 
: NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup 
F]   [inst_3 : InnerPr…
-/
protected theorem DifferentiableOn.inversion (hc : DifferentiableOn ℝ c s)
    (hR : DifferentiableOn ℝ R s) (hx : DifferentiableOn ℝ x s) (hne : ∀ a ∈ s, x a ≠ c a) :
    DifferentiableOn ℝ (fun a ↦ inversion (c a) (R a) (x a)) s := fun a ha ↦
  (hc a ha).inversion (hR a ha) (hx a ha) (hne a ha)
/-
**DifferentiableAt.inversion** 是 Mathlib 中的一个定理，位于命名空间 `DifferentiableAt`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : InnerProductSpace ℝ F
] {c x : E → F} {R : E → ℝ} {a : E},   DifferentiableAt ℝ c a →     Differentiab
leAt ℝ R a →       DifferentiableAt ℝ x a → x a ≠ c a → DifferentiableAt ℝ (fun 
a => EuclideanGeometry.inversion (c a) (R a) (x a)) a
参数：fun a => EuclideanGeometry.inversion (c a) (R a) (x a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `differentiableWithinAt_univ`：differentiableWithinAt_univ : Differentiabl
eWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x
· 使用定理 `DifferentiableWithinAt.inversion`：∀ {E : Type u_1} {F : Type u_2} [inst 
: NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup 
F]   [inst_3 : InnerPr…
-/
protected theorem DifferentiableAt.inversion (hc : DifferentiableAt ℝ c a)
    (hR : DifferentiableAt ℝ R a) (hx : DifferentiableAt ℝ x a) (hne : x a ≠ c a) :
    DifferentiableAt ℝ (fun a ↦ inversion (c a) (R a) (x a)) a := by
  rw [← differentiableWithinAt_univ] at *
  exact hc.inversion hR hx hne
/-
**Differentiable.inversion** 是 Mathlib 中的一个定理，位于命名空间 `Differentiable`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : InnerProductSpace ℝ F
] {c x : E → F} {R : E → ℝ},   Differentiable ℝ c →     Differentiable ℝ R →    
   Differentiable ℝ x →         (∀ (a : E), x a ≠ c a) → Differentiable ℝ fun a 
=> EuclideanGeometry.inversion (c a) (R a) (x a)
参数：∀ (a : E), x a ≠ c a；c a；R a；x a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.inversion`：∀ {E : Type u_1} {F : Type u_2} [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [
inst_3 : InnerPr…
-/
protected theorem Differentiable.inversion (hc : Differentiable ℝ c)
    (hR : Differentiable ℝ R) (hx : Differentiable ℝ x) (hne : ∀ a, x a ≠ c a) :
    Differentiable ℝ (fun a ↦ inversion (c a) (R a) (x a)) := fun a ↦
  (hc a).inversion (hR a) (hx a) (hne a)

end DotNotation

namespace EuclideanGeometry

variable {c x : F} {R : ℝ}

/-- Formula for the Fréchet derivative of `EuclideanGeometry.inversion c R`. -/
/-
**EuclideanGeometry.hasFDerivAt_inversion** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGe
ometry`。
形式化陈述：hasFDerivAt_inversion (hx : x != c) : HasFDerivAt (inversion c R) ((R / di
st x c) ^ 2 • ((Real ∙ (x - c))ᗮ.reflection : F ->L[Real] F)) x
参数：hx : x != c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `add_left_surjective`：∀ {G : Type u_3} [inst : AddGroup G] (a : G), Funct
ion.Surjective fun x => a + x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `HasFDerivAt.sub_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
F : Type u_…
· 使用定理 `hasFDerivAt_id`：hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x
· 使用定理 `HasFDerivAt.const_mul`：HasFDerivAt.const_mul (ha : HasFDerivAt a a' x) (
b : 𝔸) : HasFDerivAt (fun y => b * a y) (b • a') x
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
（共 88 条，此处仅展示前 30 条）

--- 原说明 ---
Formula for the Fréchet derivative of `EuclideanGeometry.inversion c R`.
-/
theorem hasFDerivAt_inversion (hx : x ≠ c) :
    HasFDerivAt (inversion c R)
      ((R / dist x c) ^ 2 • ((ℝ ∙ (x - c))ᗮ.reflection : F →L[ℝ] F)) x := by
  rcases add_left_surjective c x with ⟨x, rfl⟩
  have : HasFDerivAt (inversion c R) (?_ : F →L[ℝ] F) (c + x) := by
    simp +unfoldPartialApp only [inversion]
    simp_rw [dist_eq_norm, div_pow, div_eq_mul_inv]
    have A := (hasFDerivAt_id (𝕜 := ℝ) (c + x)).sub_const c
    have B := ((hasDerivAt_inv <| by simpa using hx).comp_hasFDerivAt _ A.norm_sq).const_mul
      (R ^ 2)
    exact (B.smul A).add_const c
  refine this.congr_fderiv (LinearMap.ext_on_codisjoint
    (Submodule.isCompl_orthogonal (ℝ ∙ x)).codisjoint
    (LinearMap.eqOn_span' ?_) fun y hy ↦ ?_)
  · have : ((‖x‖ ^ 2) ^ 2)⁻¹ * (‖x‖ ^ 2) = (‖x‖ ^ 2)⁻¹ := by
      rw [← div_eq_inv_mul, sq (‖x‖ ^ 2), div_self_mul_self']
    simp [Submodule.reflection_orthogonalComplement_singleton_eq_neg,
      two_mul, this, div_eq_mul_inv, mul_add, add_smul, mul_pow]
  · simp [Submodule.mem_orthogonal_singleton_iff_inner_right.1 hy,
      Submodule.reflection_mem_subspace_eq_self hy, div_eq_mul_inv, mul_pow]

end EuclideanGeometry

