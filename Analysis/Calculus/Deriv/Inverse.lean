/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Inverse function theorem - the easy half

In this file we prove that `g' (f x) = (f' x)⁻¹` provided that `f` is strictly differentiable at
`x`, `f' x ≠ 0`, and `g` is a local left inverse of `f` that is continuous at `f x`. This is the
easy half of the inverse function theorem: the harder half states that `g` exists.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative, inverse function
-/

public section


universe u v

open scoped Topology
open Filter Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : 𝕜 → F}
variable {f' : F}
variable {s : Set 𝕜} {x : 𝕜} {c : F}

/-
**HasStrictDerivAt.hasStrictFDerivAt_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.hasStrictFDerivAt_equiv {f : 𝕜 -> 𝕜} {f' x : 𝕜} (hf : Has
StrictDerivAt f f' x) (hf' : f' != 0) : HasStrictFDerivAt f (ContinuousLinearEqu
iv.unitsEquivAut 𝕜 (Units.mk0 f' hf') : 𝕜 ->L[𝕜] 𝕜) x
参数：hf : HasStrictDerivAt f f' x；hf' : f' != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
-/
theorem HasStrictDerivAt.hasStrictFDerivAt_equiv {f : 𝕜 → 𝕜} {f' x : 𝕜}
    (hf : HasStrictDerivAt f f' x) (hf' : f' ≠ 0) :
    HasStrictFDerivAt f (ContinuousLinearEquiv.unitsEquivAut 𝕜 (Units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) x :=
  hf
/-
**HasDerivAt.hasFDerivAt_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.hasFDerivAt_equiv {f : 𝕜 -> 𝕜} {f' x : 𝕜} (hf : HasDerivAt f f'
 x) (hf' : f' != 0) : HasFDerivAt f (ContinuousLinearEquiv.unitsEquivAut 𝕜 (Unit
s.mk0 f' hf') : 𝕜 ->L[𝕜] 𝕜) x
参数：hf : HasDerivAt f f' x；hf' : f' != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
-/
theorem HasDerivAt.hasFDerivAt_equiv {f : 𝕜 → 𝕜} {f' x : 𝕜} (hf : HasDerivAt f f' x)
    (hf' : f' ≠ 0) :
    HasFDerivAt f (ContinuousLinearEquiv.unitsEquivAut 𝕜 (Units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) x :=
  hf

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
/-
**HasStrictDerivAt.of_local_left_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.of_local_left_inverse {f g : 𝕜 -> 𝕜} {f' a : 𝕜} (hg : Con
tinuousAt g a) (hf : HasStrictDerivAt f f' (g a)) (hf' : f' != 0) (hfg : forallᶠ
 y in 𝓝 a, f (g y) = y) : HasStrictDerivAt g f'⁻¹ a
参数：hg : ContinuousAt g a；hf : HasStrictDerivAt f f' (g a)；hf' : f' != 0；hfg : fo
rallᶠ y in 𝓝 a, f (g y) = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasStrictFDerivAt.of_local_left_inverse`：HasStrictFDerivAt.of_local_left
_inverse {f : E -> F} {f' : E ≃L[𝕜] F} {g : F -> E} {a : F} (hg : ContinuousAt g
 a) (hf : HasStrictFDerivAt f…
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt_equiv`：HasStrictDerivAt.hasStrictFDer
ivAt_equiv {f : 𝕜 -> 𝕜} {f' x : 𝕜} (hf : HasStrictDerivAt f f' x) (hf' : f' != 0
) : HasStrictFDerivAt f (Conti…

--- 原说明 ---
If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, 
and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the deriva
tive `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that w
e already have an
inverse function.
-/
theorem HasStrictDerivAt.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
    (hf : HasStrictDerivAt f f' (g a)) (hf' : f' ≠ 0) (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
    HasStrictDerivAt g f'⁻¹ a :=
  (hf.hasStrictFDerivAt_equiv hf').of_local_left_inverse hg hfg

/-- If `f` is an open partial homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has a
nonzero derivative `f'` at `f.symm a` in the strict sense, then `f.symm` has the derivative `f'⁻¹`
at `a` in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
/-
**OpenPartialHomeomorph.hasStrictDerivAt_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.hasStrictDerivAt_symm (f : OpenPartialHomeomorph 𝕜 𝕜
) {a f' : 𝕜} (ha : a in f.target) (hf' : f' != 0) (htff' : HasStrictDerivAt f f'
 (f.symm a)) : HasStrictDerivAt f.symm f'⁻¹ a
参数：f : OpenPartialHomeomorph 𝕜 𝕜；ha : a in f.target；hf' : f' != 0；htff' : HasStr
ictDerivAt f f' (f.symm a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasStrictDerivAt.of_local_left_inverse`：HasStrictDerivAt.of_local_left_i
nverse {f g : 𝕜 -> 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a) (hf : HasStrictDerivAt 
f f' (g a)) (hf' : f' != 0) …
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `OpenPartialHomeomorph.eventually_right_inverse`：eventually_right_inverse
 {x} (hx : x in e.target) : forallᶠ y in 𝓝 x, e (e.symm y) = y

--- 原说明 ---
If `f` is an open partial homeomorphism defined on a neighbourhood of `f.symm a`
, and `f` has a
nonzero derivative `f'` at `f.symm a` in the strict sense, then `f.symm` has the
 derivative `f'⁻¹`
at `a` in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that w
e already have
an inverse function.
-/
theorem OpenPartialHomeomorph.hasStrictDerivAt_symm (f : OpenPartialHomeomorph 𝕜 𝕜) {a f' : 𝕜}
    (ha : a ∈ f.target) (hf' : f' ≠ 0) (htff' : HasStrictDerivAt f f' (f.symm a)) :
    HasStrictDerivAt f.symm f'⁻¹ a :=
  htff'.of_local_left_inverse (f.symm.continuousAt ha) hf' (f.eventually_right_inverse ha)
/-
**HasDerivAt.of_comp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.of_comp_left {f g h : 𝕜 -> 𝕜} {f' h' a : 𝕜} (hst : ContinuousAt
 g a) (hf : HasDerivAt f f' (g a)) (hh : HasDerivAt h h' a) (hf' : f' != 0) (hco
mp : f ∘ g =ᶠ[𝓝 a] h) : HasDerivAt g (h' / f') a
参数：hst : ContinuousAt g a；hf : HasDerivAt f f' (g a)；hh : HasDerivAt h h' a；hf' 
: f' != 0；hcomp : f ∘ g =ᶠ[𝓝 a] h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFDerivAt.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `HasFDerivAt.of_comp_of_leftInverse`：HasFDerivAt.of_comp_of_leftInverse (
hgc : ContinuousAt g a) (hf : HasFDerivAt f f' (g a)) (hh : HasFDerivAt h h' a) 
(hcomp : f ∘ g =ᶠ[𝓝 a] h…
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_cancel_right₀`：mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b * b⁻¹ = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem HasDerivAt.of_comp_left {f g h : 𝕜 → 𝕜} {f' h' a : 𝕜} (hst : ContinuousAt g a)
    (hf : HasDerivAt f f' (g a)) (hh : HasDerivAt h h' a) (hf' : f' ≠ 0)
    (hcomp : f ∘ g =ᶠ[𝓝 a] h) : HasDerivAt g (h' / f') a := by
  convert! hf.hasFDerivAt.of_comp_of_leftInverse hst hh hcomp (f'symm := .toSpanSingleton 𝕜 f'⁻¹)
    (fun _ ↦ by simp [hf']) |>.hasDerivAt using 1
  simp [div_eq_mul_inv]

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
/-
**HasDerivAt.of_local_left_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.of_local_left_inverse {f g : 𝕜 -> 𝕜} {f' a : 𝕜} (hg : Continuou
sAt g a) (hf : HasDerivAt f f' (g a)) (hf' : f' != 0) (hfg : forallᶠ y in 𝓝 a, f
 (g y) = y) : HasDerivAt g f'⁻¹ a
参数：hg : ContinuousAt g a；hf : HasDerivAt f f' (g a)；hf' : f' != 0；hfg : forallᶠ 
y in 𝓝 a, f (g y) = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasFDerivAt.of_local_left_inverse`：HasFDerivAt.of_local_left_inverse (hg
 : ContinuousAt g a) (hf : HasFDerivAt f (f' : F ->L[𝕜] E) (g a)) (hfg : forallᶠ
 y in 𝓝 a, f (g y) = y)…
· 使用定理 `HasDerivAt.hasFDerivAt_equiv`：HasDerivAt.hasFDerivAt_equiv {f : 𝕜 -> 𝕜} 
{f' x : 𝕜} (hf : HasDerivAt f f' x) (hf' : f' != 0) : HasFDerivAt f (ContinuousL
inearEquiv.unitsEq…

--- 原说明 ---
If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, 
and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that w
e already have
an inverse function.
-/
theorem HasDerivAt.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
    (hf : HasDerivAt f f' (g a)) (hf' : f' ≠ 0) (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
    HasDerivAt g f'⁻¹ a :=
  (hf.hasFDerivAt_equiv hf').of_local_left_inverse hg hfg

/-- If `f` is an open partial homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has a
nonzero derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
/-
**OpenPartialHomeomorph.hasDerivAt_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.hasDerivAt_symm (f : OpenPartialHomeomorph 𝕜 𝕜) {a f
' : 𝕜} (ha : a in f.target) (hf' : f' != 0) (htff' : HasDerivAt f f' (f.symm a))
 : HasDerivAt f.symm f'⁻¹ a
参数：f : OpenPartialHomeomorph 𝕜 𝕜；ha : a in f.target；hf' : f' != 0；htff' : HasDer
ivAt f f' (f.symm a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasDerivAt.of_local_left_inverse`：HasDerivAt.of_local_left_inverse {f g 
: 𝕜 -> 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a) (hf : HasDerivAt f f' (g a)) (hf' :
 f' != 0) (hfg : foral…
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `OpenPartialHomeomorph.eventually_right_inverse`：eventually_right_inverse
 {x} (hx : x in e.target) : forallᶠ y in 𝓝 x, e (e.symm y) = y

--- 原说明 ---
If `f` is an open partial homeomorphism defined on a neighbourhood of `f.symm a`
, and `f` has a
nonzero derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` a
t `a`.

This is one of the easy parts of the inverse function theorem: it assumes that w
e already have
an inverse function.
-/
theorem OpenPartialHomeomorph.hasDerivAt_symm (f : OpenPartialHomeomorph 𝕜 𝕜) {a f' : 𝕜}
    (ha : a ∈ f.target) (hf' : f' ≠ 0) (htff' : HasDerivAt f f' (f.symm a)) :
    HasDerivAt f.symm f'⁻¹ a :=
  htff'.of_local_left_inverse (f.symm.continuousAt ha) hf' (f.eventually_right_inverse ha)
/-
**HasDerivWithinAt.tendsto_nhdsWithin_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.tendsto_nhdsWithin_nhdsNE (h : HasDerivWithinAt f f' s x)
 (hf' : f' != 0) : Tendsto f (𝓝[s \ {x}] x) (𝓝[!=] f x)
参数：h : HasDerivWithinAt f f' s x；hf' : f' != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE`：HasFDerivWithinAt.tendsto_n
hdsWithin_nhdsNE (h : HasFDerivWithinAt f f' s x) (hf' : exists C, Antilipschitz
With C f') : Tendsto f (𝓝[s \ {x}…
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `AntilipschitzWith.of_le_mul_dist`：∀ {α : Type u_1} {β : Type u_2} [inst 
: PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β}, 
  (∀ (x y : α), dist x…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), dist a b = ‖a - b‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Mathlib.Tactic.FieldSimp.le_eq_cancel_le`：le_eq_cancel_le {M : Type*} [M
onoidWithZero M] [PartialOrder M] [PosMulMono M] [PosMulReflectLE M] {e₁ e₂ f₁ f
₂ L : M} (H₁ : e₁ = L * f₁) (H…
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 40 条，此处仅展示前 30 条）
-/
theorem HasDerivWithinAt.tendsto_nhdsWithin_nhdsNE (h : HasDerivWithinAt f f' s x) (hf' : f' ≠ 0) :
    Tendsto f (𝓝[s \ {x}] x) (𝓝[≠] f x) :=
  h.hasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE ⟨‖f'‖₊⁻¹, AntilipschitzWith.of_le_mul_dist
    fun _ _ ↦ by simp [dist_eq_norm_sub, ← sub_smul, norm_smul]; field_simp; rfl⟩
/-
**HasDerivWithinAt.eventually_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.eventually_ne (h : HasDerivWithinAt f f' s x) (hf' : f' !
= 0) : forallᶠ z in 𝓝[s \ {x}] x, f z != c
参数：h : HasDerivWithinAt f f' s x；hf' : f' != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.eventually_ne`：HasFDerivWithinAt.eventually_ne (h : Ha
sFDerivWithinAt f f' s x) (hf' : exists C, AntilipschitzWith C f') : forallᶠ z i
n 𝓝[s \ {x}] x, f z !…
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `AntilipschitzWith.of_le_mul_dist`：∀ {α : Type u_1} {β : Type u_2} [inst 
: PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β}, 
  (∀ (x y : α), dist x…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), dist a b = ‖a - b‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Mathlib.Tactic.FieldSimp.le_eq_cancel_le`：le_eq_cancel_le {M : Type*} [M
onoidWithZero M] [PartialOrder M] [PosMulMono M] [PosMulReflectLE M] {e₁ e₂ f₁ f
₂ L : M} (H₁ : e₁ = L * f₁) (H…
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 40 条，此处仅展示前 30 条）
-/
theorem HasDerivWithinAt.eventually_ne (h : HasDerivWithinAt f f' s x) (hf' : f' ≠ 0) :
    ∀ᶠ z in 𝓝[s \ {x}] x, f z ≠ c :=
  h.hasFDerivWithinAt.eventually_ne ⟨‖f'‖₊⁻¹, AntilipschitzWith.of_le_mul_dist
    fun _ _ ↦ by simp [dist_eq_norm_sub, ← sub_smul, norm_smul]; field_simp; rfl⟩
/-
**HasDerivWithinAt.eventually_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.eventually_notMem (h : HasDerivWithinAt f f' s x) (hf' : 
f' != 0) (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t)) : forallᶠ z in 𝓝[s \ {x}] x, f z
 ∉ t
参数：h : HasDerivWithinAt f f' s x；hf' : f' != 0；t : Set F；ht : ¬ AccPt (f x) (𝓟 t
)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.eventually_notMem`：HasFDerivWithinAt.eventually_notMem
 (h : HasFDerivWithinAt f f' s x) (hf' : exists C, AntilipschitzWith C f') (t : 
Set F) (ht : ¬ AccPt (f x…
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `AntilipschitzWith.of_le_mul_dist`：∀ {α : Type u_1} {β : Type u_2} [inst 
: PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β}, 
  (∀ (x y : α), dist x…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), dist a b = ‖a - b‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Mathlib.Tactic.FieldSimp.le_eq_cancel_le`：le_eq_cancel_le {M : Type*} [M
onoidWithZero M] [PartialOrder M] [PosMulMono M] [PosMulReflectLE M] {e₁ e₂ f₁ f
₂ L : M} (H₁ : e₁ = L * f₁) (H…
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 40 条，此处仅展示前 30 条）
-/
theorem HasDerivWithinAt.eventually_notMem (h : HasDerivWithinAt f f' s x) (hf' : f' ≠ 0)
    (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t)) : ∀ᶠ z in 𝓝[s \ {x}] x, f z ∉ t :=
  h.hasFDerivWithinAt.eventually_notMem ⟨‖f'‖₊⁻¹, AntilipschitzWith.of_le_mul_dist
    fun _ _ ↦ by simp [dist_eq_norm_sub, ← sub_smul, norm_smul]; field_simp; rfl⟩ t ht
/-
**HasDerivAt.tendsto_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.tendsto_nhdsNE (h : HasDerivAt f f' x) (hf' : f' != 0) : Tendst
o f (𝓝[!=] x) (𝓝[!=] f x)
参数：h : HasDerivAt f f' x；hf' : f' != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `HasDerivWithinAt.tendsto_nhdsWithin_nhdsNE`：HasDerivWithinAt.tendsto_nhd
sWithin_nhdsNE (h : HasDerivWithinAt f f' s x) (hf' : f' != 0) : Tendsto f (𝓝[s 
\ {x}] x) (𝓝[!=] f x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
-/
theorem HasDerivAt.tendsto_nhdsNE (h : HasDerivAt f f' x) (hf' : f' ≠ 0) :
    Tendsto f (𝓝[≠] x) (𝓝[≠] f x) := by
  simpa only [compl_eq_univ_sdiff] using (hasDerivWithinAt_univ.2 h).tendsto_nhdsWithin_nhdsNE hf'
/-
**HasDerivAt.eventually_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.eventually_ne (h : HasDerivAt f f' x) (hf' : f' != 0) : forallᶠ
 z in 𝓝[!=] x, f z != c
参数：h : HasDerivAt f f' x；hf' : f' != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `HasDerivWithinAt.eventually_ne`：HasDerivWithinAt.eventually_ne (h : HasD
erivWithinAt f f' s x) (hf' : f' != 0) : forallᶠ z in 𝓝[s \ {x}] x, f z != c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
-/
theorem HasDerivAt.eventually_ne (h : HasDerivAt f f' x) (hf' : f' ≠ 0) :
    ∀ᶠ z in 𝓝[≠] x, f z ≠ c := by
  simpa only [compl_eq_univ_sdiff] using (hasDerivWithinAt_univ.2 h).eventually_ne hf'
/-
**HasDerivAt.eventually_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.eventually_notMem (h : HasDerivAt f f' x) (hf' : f' != 0) (t : 
Set F) (ht : ¬ AccPt (f x) (𝓟 t)) : forallᶠ z in 𝓝[!=] x, f z ∉ t
参数：h : HasDerivAt f f' x；hf' : f' != 0；t : Set F；ht : ¬ AccPt (f x) (𝓟 t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `HasDerivWithinAt.eventually_notMem`：HasDerivWithinAt.eventually_notMem (
h : HasDerivWithinAt f f' s x) (hf' : f' != 0) (t : Set F) (ht : ¬ AccPt (f x) (
𝓟 t)) : forallᶠ z in 𝓝[s…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
-/
theorem HasDerivAt.eventually_notMem (h : HasDerivAt f f' x) (hf' : f' ≠ 0)
    (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t)) : ∀ᶠ z in 𝓝[≠] x, f z ∉ t := by
  simpa only [compl_eq_univ_sdiff] using (hasDerivWithinAt_univ.2 h).eventually_notMem hf' t ht

/-- If a function is equal to a constant at a set of points that accumulates to `x` in `s`,
then its derivative within `s` at `x` equals zero,
either because it has derivative zero or because it isn't differentiable at this point. -/
/-
**derivWithin_zero_of_frequently_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_zero_of_frequently_const {c} (h : existsᶠ y in 𝓝[s \ {x}] x, f
 y = c) : derivWithin f s x = 0
参数：h : existsᶠ y in 𝓝[s \ {x}] x, f y = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `HasDerivWithinAt.eventually_ne`：HasDerivWithinAt.eventually_ne (h : HasD
erivWithinAt f f' s x) (hf' : f' != 0) : forallᶠ z in 𝓝[s \ {x}] x, f z != c
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `derivWithin_zero_of_not_differentiableWithinAt`：derivWithin_zero_of_not_
differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : derivWithin f s x
 = 0

--- 原说明 ---
If a function is equal to a constant at a set of points that accumulates to `x` 
in `s`,
then its derivative within `s` at `x` equals zero,
either because it has derivative zero or because it isn't differentiable at this
 point.
-/
theorem derivWithin_zero_of_frequently_const {c} (h : ∃ᶠ y in 𝓝[s \ {x}] x, f y = c) :
    derivWithin f s x = 0 := by
  by_cases hf : DifferentiableWithinAt 𝕜 f s x
  · contrapose! h
    exact hf.hasDerivWithinAt.eventually_ne h
  · exact derivWithin_zero_of_not_differentiableWithinAt hf

/-- If a function frequently (in `𝓝[s ∖ {x}] x`) takes values in a set `t` that does not
accumulate at `f x`, then its derivative within `s` at `x` equals zero,
either because it has derivative zero or because it isn't differentiable at this point. -/
/-
**derivWithin_zero_of_frequently_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_zero_of_frequently_mem (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t)) 
(h : existsᶠ y in 𝓝[s \ {x}] x, f y in t) : derivWithin f s x = 0
参数：t : Set F；ht : ¬ AccPt (f x) (𝓟 t)；h : existsᶠ y in 𝓝[s \ {x}] x, f y in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `HasDerivWithinAt.eventually_notMem`：HasDerivWithinAt.eventually_notMem (
h : HasDerivWithinAt f f' s x) (hf' : f' != 0) (t : Set F) (ht : ¬ AccPt (f x) (
𝓟 t)) : forallᶠ z in 𝓝[s…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `derivWithin_zero_of_not_differentiableWithinAt`：derivWithin_zero_of_not_
differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : derivWithin f s x
 = 0

--- 原说明 ---
If a function frequently (in `𝓝[s ∖ {x}] x`) takes values in a set `t` that does
 not
accumulate at `f x`, then its derivative within `s` at `x` equals zero,
either because it has derivative zero or because it isn't differentiable at this
 point.
-/
theorem derivWithin_zero_of_frequently_mem (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t))
    (h : ∃ᶠ y in 𝓝[s \ {x}] x, f y ∈ t) : derivWithin f s x = 0 := by
  by_cases hf : DifferentiableWithinAt 𝕜 f s x
  · contrapose! h
    exact hf.hasDerivWithinAt.eventually_notMem h t ht
  · exact derivWithin_zero_of_not_differentiableWithinAt hf

/-- If a function is equal to a constant at a set of points that accumulates to `x`,
then its derivative at `x` equals zero,
either because it has derivative zero or because it isn't differentiable at this point. -/
/-
**deriv_zero_of_frequently_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_zero_of_frequently_const {c} (h : existsᶠ y in 𝓝[!=] x, f y = c) : d
eriv f x = 0
参数：h : existsᶠ y in 𝓝[!=] x, f y = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `derivWithin_univ`：derivWithin_univ : derivWithin f univ = deriv f
· 使用定理 `derivWithin_zero_of_frequently_const`：derivWithin_zero_of_frequently_con
st {c} (h : existsᶠ y in 𝓝[s \ {x}] x, f y = c) : derivWithin f s x = 0
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s

--- 原说明 ---
If a function is equal to a constant at a set of points that accumulates to `x`,
then its derivative at `x` equals zero,
either because it has derivative zero or because it isn't differentiable at this
 point.
-/
theorem deriv_zero_of_frequently_const {c} (h : ∃ᶠ y in 𝓝[≠] x, f y = c) : deriv f x = 0 := by
  rw [← derivWithin_univ, derivWithin_zero_of_frequently_const]
  rwa [← compl_eq_univ_sdiff]

/-- If a function frequently (in `𝓝[≠] x`) takes values in a set `t` that does not
accumulate at `f x`, then its derivative at `x` equals zero,
either because it has derivative zero or because it isn't differentiable at this point. -/
/-
**deriv_zero_of_frequently_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_zero_of_frequently_mem (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t)) (h : e
xistsᶠ y in 𝓝[!=] x, f y in t) : deriv f x = 0
参数：t : Set F；ht : ¬ AccPt (f x) (𝓟 t)；h : existsᶠ y in 𝓝[!=] x, f y in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `derivWithin_univ`：derivWithin_univ : derivWithin f univ = deriv f
· 使用定理 `derivWithin_zero_of_frequently_mem`：derivWithin_zero_of_frequently_mem (
t : Set F) (ht : ¬ AccPt (f x) (𝓟 t)) (h : existsᶠ y in 𝓝[s \ {x}] x, f y in t) 
: derivWithin f s x = 0
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s

--- 原说明 ---
If a function frequently (in `𝓝[≠] x`) takes values in a set `t` that does not
accumulate at `f x`, then its derivative at `x` equals zero,
either because it has derivative zero or because it isn't differentiable at this
 point.
-/
theorem deriv_zero_of_frequently_mem (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t))
    (h : ∃ᶠ y in 𝓝[≠] x, f y ∈ t) : deriv f x = 0 := by
  rw [← derivWithin_univ, derivWithin_zero_of_frequently_mem t ht]
  rwa [← compl_eq_univ_sdiff]
/-
**not_differentiableWithinAt_of_local_left_inverse_hasDerivWithinAt_zero** 是 Mat
hlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_differentiableWithinAt_of_local_left_inverse_hasDerivWithinAt_zero {f 
g : 𝕜 -> 𝕜} {a : 𝕜} {s t : Set 𝕜} (ha : a in s) (hsu : UniqueDiffWithinAt 𝕜 s a)
 (hf : HasDerivWithinAt f 0 t (g a)) (hst : MapsTo g s t) (hfg : f ∘ g =ᶠ[𝓝[s] a
] id) : ¬DifferentiableWithinAt 𝕜 g s a
参数：ha : a in s；hsu : UniqueDiffWithinAt 𝕜 s a；hf : HasDerivWithinAt f 0 t (g a)；
hst : MapsTo g s t；hfg : f ∘ g =ᶠ[𝓝[s] a] id。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_of_eventuallyEq_of_mem`：HasDerivWithinAt.congr_of
_eventuallyEq_of_mem (h : HasDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx 
: x in s) : HasDerivWithinAt f₁ f' …
· 使用定理 `HasDerivWithinAt.comp`：HasDerivWithinAt.comp (hh₂ : HasDerivWithinAt h₂ 
h₂' s' (h x)) (hh : HasDerivWithinAt h h' s x) (hst : MapsTo h s s') : HasDerivW
ithinAt (h₂…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `UniqueDiffWithinAt.eq_deriv`：UniqueDiffWithinAt.eq_deriv (s : Set 𝕜) (H 
: UniqueDiffWithinAt 𝕜 s x) (h : HasDerivWithinAt f f' s x) (h₁ : HasDerivWithin
At f f₁' s x) : f…
· 使用定理 `hasDerivWithinAt_id`：hasDerivWithinAt_id : HasDerivWithinAt id 1 s x
-/
theorem not_differentiableWithinAt_of_local_left_inverse_hasDerivWithinAt_zero {f g : 𝕜 → 𝕜} {a : 𝕜}
    {s t : Set 𝕜} (ha : a ∈ s) (hsu : UniqueDiffWithinAt 𝕜 s a) (hf : HasDerivWithinAt f 0 t (g a))
    (hst : MapsTo g s t) (hfg : f ∘ g =ᶠ[𝓝[s] a] id) : ¬DifferentiableWithinAt 𝕜 g s a := by
  intro hg
  have := (hf.comp a hg.hasDerivWithinAt hst).congr_of_eventuallyEq_of_mem hfg.symm ha
  simpa using hsu.eq_deriv _ this (hasDerivWithinAt_id _ _)
/-
**not_differentiableAt_of_local_left_inverse_hasDerivAt_zero** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：not_differentiableAt_of_local_left_inverse_hasDerivAt_zero {f g : 𝕜 -> 𝕜} 
{a : 𝕜} (hf : HasDerivAt f 0 (g a)) (hfg : f ∘ g =ᶠ[𝓝 a] id) : ¬DifferentiableAt
 𝕜 g a
参数：hf : HasDerivAt f 0 (g a)；hfg : f ∘ g =ᶠ[𝓝 a] id。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_of_eventuallyEq`：HasDerivAt.congr_of_eventuallyEq (h : 
HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) : HasDerivAt f₁ f' x
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `HasDerivAt.unique`：HasDerivAt.unique (h₀ : HasDerivAt f f₀' x) (h₁ : Has
DerivAt f f₁' x) : f₀' = f₁'
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
-/
theorem not_differentiableAt_of_local_left_inverse_hasDerivAt_zero {f g : 𝕜 → 𝕜} {a : 𝕜}
    (hf : HasDerivAt f 0 (g a)) (hfg : f ∘ g =ᶠ[𝓝 a] id) : ¬DifferentiableAt 𝕜 g a := by
  intro hg
  have := (hf.comp a hg.hasDerivAt).congr_of_eventuallyEq hfg.symm
  simpa using this.unique (hasDerivAt_id a)
