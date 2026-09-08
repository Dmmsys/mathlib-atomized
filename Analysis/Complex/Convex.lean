/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Theorems about convexity on the complex plane

We show that the open and closed half-spaces in ℂ given by an inequality on either the real or
imaginary part are all convex over ℝ. We also prove some results on star-convexity for the
slit plane.
-/

public section

open Set
open scoped ComplexOrder

namespace Complex

/-- A version of `convexHull_prod` for `Set.reProdIm`. -/
/-
**Complex.convexHull_reProdIm** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：convexHull_reProdIm (s t : Set Real) : convexHull Real (s ×Complex t) = co
nvexHull Real s ×Complex convexHull Real t
参数：s t : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.image_convexHull`：LinearMap.image_convexHull (f : E ->ₗ[𝕜] F) 
(s : Set E) : f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s)
· 使用定理 `convexHull_prod`：convexHull_prod (s : Set E) (t : Set F) : convexHull R 
(s ×ˢ t) = convexHull R s ×ˢ convexHull R t

--- 原说明 ---
A version of `convexHull_prod` for `Set.reProdIm`.
-/
lemma convexHull_reProdIm (s t : Set ℝ) :
    convexHull ℝ (s ×ℂ t) = convexHull ℝ s ×ℂ convexHull ℝ t :=
  calc
    convexHull ℝ (equivRealProdLm ⁻¹' (s ×ˢ t)) = equivRealProdLm ⁻¹' convexHull ℝ (s ×ˢ t) := by
      simpa only [← LinearEquiv.image_symm_eq_preimage]
        using! ((equivRealProdLm.symm.toLinearMap).image_convexHull (s ×ˢ t)).symm
    _ = convexHull ℝ s ×ℂ convexHull ℝ t := by rw [convexHull_prod]; rfl

/-- The slit plane is star-convex at a positive number. -/
/-
**Complex.starConvex_slitPlane** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：starConvex_slitPlane {z : Complex} (hz : 0 < z) : StarConvex Real z slitPl
ane
参数：hz : 0 < z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `starConvex_compl_Iic`：starConvex_compl_Iic (h : x < y) : StarConvex 𝕜 y 
(Iic x)ᶜ
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用定理 `RCLike.toIsStrictOrderedModule`：toIsStrictOrderedModule : IsStrictOrdere
dModule Real K where smul_lt_smul_of_pos_left r hr a b hab
· 使用定理 `PosSMulStrictMono.toPosSMulReflectLT`：∀ {𝕜 : Type u_1} {G : Type u_2} [i
nst : Semifield 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : 
AddCommGroup G] [inst_4 : …
· 使用定理 `instPosSMulStrictMono`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring 
R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4
 : NonUnita…
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `Complex.instStarModuleReal`：StarModule ℝ ℂ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用引理 `RCLike.toIsStrictOrderedRing`：toIsStrictOrderedRing : IsStrictOrderedRin
g K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Complex.compl_Iic_zero`：(Set.Iic 0)ᶜ = Complex.slitPlane

--- 原说明 ---
The slit plane is star-convex at a positive number.
-/
lemma starConvex_slitPlane {z : ℂ} (hz : 0 < z) : StarConvex ℝ z slitPlane :=
  Complex.compl_Iic_zero ▸ starConvex_compl_Iic hz

/-- The slit plane is star-shaped at a positive real number. -/
/-
**Complex.starConvex_ofReal_slitPlane** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：starConvex_ofReal_slitPlane {x : Real} (hx : 0 < x) : StarConvex Real ↑x s
litPlane
参数：hx : 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.starConvex_slitPlane`：starConvex_slitPlane {z : Complex} (hz : 0
 < z) : StarConvex Real z slitPlane
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.zero_lt_real`：zero_lt_real {x : Real} : (0 : Complex) < (x : Com
plex) ↔ 0 < x

--- 原说明 ---
The slit plane is star-shaped at a positive real number.
-/
lemma starConvex_ofReal_slitPlane {x : ℝ} (hx : 0 < x) : StarConvex ℝ ↑x slitPlane :=
  starConvex_slitPlane <| zero_lt_real.2 hx

/-- The slit plane is star-shaped at `1`. -/
/-
**Complex.starConvex_one_slitPlane** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：starConvex_one_slitPlane : StarConvex Real 1 slitPlane
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.starConvex_slitPlane`：starConvex_slitPlane {z : Complex} (hz : 0
 < z) : StarConvex Real z slitPlane
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用引理 `RCLike.toZeroLEOneClass`：toZeroLEOneClass : ZeroLEOneClass K where zero_
le_one

--- 原说明 ---
The slit plane is star-shaped at `1`.
-/
lemma starConvex_one_slitPlane : StarConvex ℝ 1 slitPlane := starConvex_slitPlane one_pos

end Complex

open Complex

variable (r : ℝ)

/-
**convex_halfSpace_re_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_halfSpace_re_lt : Convex Real { c : Complex | c.re < r }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_halfSpace_lt`：convex_halfSpace_lt {f : E -> β} (h : IsLinearMap 𝕜
 f) (r : β) : Convex 𝕜 { w | f w < r }
· 使用定理 `instPosSMulStrictMono`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring 
R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4
 : NonUnita…
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `RCLike.instStarModuleReal`：∀ {K : Type u_1} [inst : RCLike K], StarModul
e ℝ K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Complex.add_re`：add_re (z w : Complex) : (z + w).re = z.re + w.re
· 使用定理 `Complex.smul_re`：smul_re (r : R) (z : Complex) : (r • z).re = r • z.re
-/
theorem convex_halfSpace_re_lt : Convex ℝ { c : ℂ | c.re < r } :=
  convex_halfSpace_lt (.mk add_re smul_re) _
/-
**convex_halfSpace_re_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_halfSpace_re_le : Convex Real { c : Complex | c.re <= r }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_halfSpace_le`：convex_halfSpace_le {f : E -> β} (h : IsLinearMap 𝕜
 f) (r : β) : Convex 𝕜 { w | f w <= r }
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `instIsOrderedModule`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 :
 NonUnita…
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `RCLike.instStarModuleReal`：∀ {K : Type u_1} [inst : RCLike K], StarModul
e ℝ K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Complex.add_re`：add_re (z w : Complex) : (z + w).re = z.re + w.re
· 使用定理 `Complex.smul_re`：smul_re (r : R) (z : Complex) : (r • z).re = r • z.re
-/
theorem convex_halfSpace_re_le : Convex ℝ { c : ℂ | c.re ≤ r } :=
  convex_halfSpace_le (.mk add_re smul_re) _
/-
**convex_halfSpace_re_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_halfSpace_re_gt : Convex Real { c : Complex | r < c.re }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_halfSpace_gt`：convex_halfSpace_gt {f : E -> β} (h : IsLinearMap 𝕜
 f) (r : β) : Convex 𝕜 { w | r < f w }
· 使用定理 `instPosSMulStrictMono`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring 
R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4
 : NonUnita…
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `RCLike.instStarModuleReal`：∀ {K : Type u_1} [inst : RCLike K], StarModul
e ℝ K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Complex.add_re`：add_re (z w : Complex) : (z + w).re = z.re + w.re
· 使用定理 `Complex.smul_re`：smul_re (r : R) (z : Complex) : (r • z).re = r • z.re
-/
theorem convex_halfSpace_re_gt : Convex ℝ { c : ℂ | r < c.re } :=
  convex_halfSpace_gt (.mk add_re smul_re) _
/-
**convex_halfSpace_re_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_halfSpace_re_ge : Convex Real { c : Complex | r <= c.re }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_halfSpace_ge`：convex_halfSpace_ge {f : E -> β} (h : IsLinearMap 𝕜
 f) (r : β) : Convex 𝕜 { w | r <= f w }
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `instIsOrderedModule`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 :
 NonUnita…
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `RCLike.instStarModuleReal`：∀ {K : Type u_1} [inst : RCLike K], StarModul
e ℝ K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Complex.add_re`：add_re (z w : Complex) : (z + w).re = z.re + w.re
· 使用定理 `Complex.smul_re`：smul_re (r : R) (z : Complex) : (r • z).re = r • z.re
-/
theorem convex_halfSpace_re_ge : Convex ℝ { c : ℂ | r ≤ c.re } :=
  convex_halfSpace_ge (.mk add_re smul_re) _
/-
**convex_halfSpace_im_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_halfSpace_im_lt : Convex Real { c : Complex | c.im < r }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_halfSpace_lt`：convex_halfSpace_lt {f : E -> β} (h : IsLinearMap 𝕜
 f) (r : β) : Convex 𝕜 { w | f w < r }
· 使用定理 `instPosSMulStrictMono`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring 
R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4
 : NonUnita…
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `RCLike.instStarModuleReal`：∀ {K : Type u_1} [inst : RCLike K], StarModul
e ℝ K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Complex.add_im`：add_im (z w : Complex) : (z + w).im = z.im + w.im
· 使用定理 `Complex.smul_im`：smul_im (r : R) (z : Complex) : (r • z).im = r • z.im
-/
theorem convex_halfSpace_im_lt : Convex ℝ { c : ℂ | c.im < r } :=
  convex_halfSpace_lt (.mk add_im smul_im) _
/-
**convex_halfSpace_im_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_halfSpace_im_le : Convex Real { c : Complex | c.im <= r }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_halfSpace_le`：convex_halfSpace_le {f : E -> β} (h : IsLinearMap 𝕜
 f) (r : β) : Convex 𝕜 { w | f w <= r }
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `instIsOrderedModule`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 :
 NonUnita…
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `RCLike.instStarModuleReal`：∀ {K : Type u_1} [inst : RCLike K], StarModul
e ℝ K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Complex.add_im`：add_im (z w : Complex) : (z + w).im = z.im + w.im
· 使用定理 `Complex.smul_im`：smul_im (r : R) (z : Complex) : (r • z).im = r • z.im
-/
theorem convex_halfSpace_im_le : Convex ℝ { c : ℂ | c.im ≤ r } :=
  convex_halfSpace_le (.mk add_im smul_im) _
/-
**convex_halfSpace_im_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_halfSpace_im_gt : Convex Real { c : Complex | r < c.im }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_halfSpace_gt`：convex_halfSpace_gt {f : E -> β} (h : IsLinearMap 𝕜
 f) (r : β) : Convex 𝕜 { w | r < f w }
· 使用定理 `instPosSMulStrictMono`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring 
R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4
 : NonUnita…
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `RCLike.instStarModuleReal`：∀ {K : Type u_1} [inst : RCLike K], StarModul
e ℝ K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Complex.add_im`：add_im (z w : Complex) : (z + w).im = z.im + w.im
· 使用定理 `Complex.smul_im`：smul_im (r : R) (z : Complex) : (r • z).im = r • z.im
-/
theorem convex_halfSpace_im_gt : Convex ℝ { c : ℂ | r < c.im } :=
  convex_halfSpace_gt (.mk add_im smul_im) _
/-
**convex_halfSpace_im_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_halfSpace_im_ge : Convex Real { c : Complex | r <= c.im }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_halfSpace_ge`：convex_halfSpace_ge {f : E -> β} (h : IsLinearMap 𝕜
 f) (r : β) : Convex 𝕜 { w | r <= f w }
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `instIsOrderedModule`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 :
 NonUnita…
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `RCLike.instStarModuleReal`：∀ {K : Type u_1} [inst : RCLike K], StarModul
e ℝ K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Complex.add_im`：add_im (z w : Complex) : (z + w).im = z.im + w.im
· 使用定理 `Complex.smul_im`：smul_im (r : R) (z : Complex) : (r • z).im = r • z.im
-/
theorem convex_halfSpace_im_ge : Convex ℝ { c : ℂ | r ≤ c.im } :=
  convex_halfSpace_ge (.mk add_im smul_im) _

namespace Complex

/-
**Complex.isConnected_of_upperHalfPlane** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：isConnected_of_upperHalfPlane {r} {s : Set Complex} (hs₁ : {z | r < z.im} 
subseteq s) (hs₂ : s subseteq {z | r <= z.im}) : IsConnected s
参数：hs₁ : {z | r < z.im} subseteq s；hs₂ : s subseteq {z | r <= z.im}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConnected.subset_closure`：∀ {α : Type u} [inst : TopologicalSpace α] {
s t : Set α}, IsConnected s → s ⊆ t → t ⊆ closure s → IsConnected t
· 使用定理 `Convex.isConnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [ContinuousS
Mul ℝ E]…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `convex_halfSpace_im_gt`：convex_halfSpace_im_gt : Convex Real { c : Compl
ex | r < c.im }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Complex.closure_setOfPred_lt_im`：closure_setOfPred_lt_im (a : Real) : cl
osure { z : Complex | a < z.im } = { z | a <= z.im }
-/
lemma isConnected_of_upperHalfPlane {r} {s : Set ℂ} (hs₁ : {z | r < z.im} ⊆ s)
    (hs₂ : s ⊆ {z | r ≤ z.im}) : IsConnected s := by
  refine .subset_closure ?_ hs₁ (by simpa only [closure_setOfPred_lt_im] using hs₂)
  exact (convex_halfSpace_im_gt r).isConnected ⟨(r + 1) * I, by simp⟩
/-
**Complex.isConnected_of_lowerHalfPlane** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：isConnected_of_lowerHalfPlane {r} {s : Set Complex} (hs₁ : {z | z.im < r} 
subseteq s) (hs₂ : s subseteq {z | z.im <= r}) : IsConnected s
参数：hs₁ : {z | z.im < r} subseteq s；hs₂ : s subseteq {z | z.im <= r}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConnected.subset_closure`：∀ {α : Type u} [inst : TopologicalSpace α] {
s t : Set α}, IsConnected s → s ⊆ t → t ⊆ closure s → IsConnected t
· 使用定理 `Convex.isConnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [ContinuousS
Mul ℝ E]…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `convex_halfSpace_im_lt`：convex_halfSpace_im_lt : Convex Real { c : Compl
ex | c.im < r }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Complex.closure_setOfPred_im_lt`：closure_setOfPred_im_lt (a : Real) : cl
osure { z : Complex | z.im < a } = { z | z.im <= a }
-/
lemma isConnected_of_lowerHalfPlane {r} {s : Set ℂ} (hs₁ : {z | z.im < r} ⊆ s)
    (hs₂ : s ⊆ {z | z.im ≤ r}) : IsConnected s := by
  refine .subset_closure ?_ hs₁ (by simpa only [closure_setOfPred_im_lt] using hs₂)
  exact (convex_halfSpace_im_lt r).isConnected ⟨(r - 1) * I, by simp⟩
/-
**Complex.rectangle_eq_convexHull** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：rectangle_eq_convexHull (z w : Complex) : Rectangle z w = convexHull Real 
{z, z.re + w.im * I, w.re + z.im * I, w}
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.insert_prod`：insert_prod : insert a s ×ˢ t = Prod.mk a '' t union s 
×ˢ t
· 使用定理 `Set.singleton_prod`：singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t
· 使用定理 `Set.image_pair`：image_pair (f : α -> β) (a b : α) : f '' {a, b} = {f a, 
f b}
· 使用定理 `Set.insert_union`：insert_union : insert a s union t = insert a (s union 
t)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Complex.equivRealProd_symm_apply`：equivRealProd_symm_apply (p : Real × R
eal) : equivRealProd.symm p = p.1 + p.2 * I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rectangle_eq_convexHull (z w : ℂ) :
    Rectangle z w = convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} := by
  simp_rw [Rectangle, ← segment_eq_uIcc, ← convexHull_pair, ← convexHull_reProdIm,
    ← preimage_equivRealProd_prod, insert_prod, singleton_prod, image_pair, insert_union,
    ← insert_eq, ← Equiv.image_symm_eq_preimage, image_insert_eq, image_singleton,
    equivRealProd_symm_apply, re_add_im]

/-- If opposite corners of a rectangle are contained in a convex set, the whole rectangle is. -/
/-
**Complex.Convex.rectangle_subset** 是 Mathlib 中的一个定理，位于命名空间 `Complex.Convex`。
形式化陈述：∀ {U : Set ℂ},   Convex ℝ U →     ∀ {z w : ℂ}, z ∈ U → w ∈ U → ↑z.re + ↑w.
im * Complex.I ∈ U → ↑w.re + ↑z.im * Complex.I ∈ U → z.Rectangle w ⊆ U
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.rectangle_eq_convexHull`：rectangle_eq_convexHull (z w : Complex)
 : Rectangle z w = convexHull Real {z, z.re + w.im * I, w.re + z.im * I, w}
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t

--- 原说明 ---
If opposite corners of a rectangle are contained in a convex set, the whole rect
angle is.
-/
lemma Convex.rectangle_subset {U : Set ℂ} (U_convex : Convex ℝ U) {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ U) (hzw : (z.re + w.im * I) ∈ U) (hwz : (w.re + z.im * I) ∈ U) :
    Rectangle z w ⊆ U := by
  simpa only [rectangle_eq_convexHull] using convexHull_min (by grind) U_convex

-- This also follows easily from `isPathConnected_compl_singleton_of_one_lt_rank`,
-- or that `Complex.range_exp` and `Complex.continuous_exp`,
-- but both of them requires a lot more import.
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PathConnectedSpace ℂˣ :=
  have : PathConnectedSpace { z : ℂ // z ≠ 0 } :=
    (isPathConnected_iff_pathConnectedSpace (F := {0}ᶜ)).mp (by
      convert!
        (((convex_halfSpace_im_gt 0).isPathConnected ⟨.I, by simp⟩).union
              ((convex_halfSpace_re_gt 0).isPathConnected ⟨1, by simp⟩) ⟨1 + .I, by simp⟩).union
          (((convex_halfSpace_im_lt 0).isPathConnected ⟨-.I, by simp⟩).union
            ((convex_halfSpace_re_lt 0).isPathConnected ⟨-1, by simp⟩) ⟨-1 - .I, by simp⟩)
          ⟨1 - .I, by simp⟩ using 1
      ext x
      refine ⟨?_, by aesop⟩
      simp +contextual [Complex.ext_iff, -not_and, not_and_or, or_imp, ← ne_eq, ← lt_or_lt_iff_ne])
  let e := unitsHomeomorphNeZero (G₀ := ℂ)
  e.symm.surjective.pathConnectedSpace e.symm.continuous

end Complex

