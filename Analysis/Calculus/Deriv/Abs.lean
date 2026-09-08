/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Derivative of the absolute value

This file compiles basic derivability properties of the absolute value, and is largely inspired from
`Mathlib/Analysis/InnerProductSpace/Calculus.lean`, which is the analogous file for norms derived
from an inner product space.

## Tags

absolute value, derivative
-/

public section

open Filter Real Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ∞} {f : E → ℝ} {f' : StrongDual ℝ E} {s : Set E} {x : E}

/-
**contDiffAt_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_abs {x : Real} (hx : x != 0) : ContDiffAt Real n (|·|) x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffAt_norm`：contDiffAt_norm {x : E} (hx : x != 0) : ContDiffAt Real
 n norm x
-/
theorem contDiffAt_abs {x : ℝ} (hx : x ≠ 0) : ContDiffAt ℝ n (|·|) x := contDiffAt_norm ℝ hx
/-
**ContDiffAt.abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.abs (hf : ContDiffAt Real n f x) (h₀ : f x != 0) : ContDiffAt R
eal n (fun x => |f x|) x
参数：hf : ContDiffAt Real n f x；h₀ : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.norm`：ContDiffAt.norm (hf : ContDiffAt Real n f x) (h0 : f x 
!= 0) : ContDiffAt Real n (fun y => ‖f y‖) x
-/
theorem ContDiffAt.abs (hf : ContDiffAt ℝ n f x) (h₀ : f x ≠ 0) :
    ContDiffAt ℝ n (fun x ↦ |f x|) x := hf.norm ℝ h₀
/-
**contDiffWithinAt_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_abs {x : Real} (hx : x != 0) (s : Set Real) : ContDiffWit
hinAt Real n (|·|) s x
参数：hx : x != 0；s : Set Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `contDiffAt_abs`：contDiffAt_abs {x : Real} (hx : x != 0) : ContDiffAt Rea
l n (|·|) x
-/
theorem contDiffWithinAt_abs {x : ℝ} (hx : x ≠ 0) (s : Set ℝ) :
    ContDiffWithinAt ℝ n (|·|) s x := (contDiffAt_abs hx).contDiffWithinAt
/-
**ContDiffWithinAt.abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.abs (hf : ContDiffWithinAt Real n f s x) (h₀ : f x != 0) 
: ContDiffWithinAt Real n (fun y => |f y|) s x
参数：hf : ContDiffWithinAt Real n f s x；h₀ : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `contDiffAt_abs`：contDiffAt_abs {x : Real} (hx : x != 0) : ContDiffAt Rea
l n (|·|) x
-/
theorem ContDiffWithinAt.abs (hf : ContDiffWithinAt ℝ n f s x) (h₀ : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun y ↦ |f y|) s x :=
  (contDiffAt_abs h₀).comp_contDiffWithinAt x hf
/-
**contDiffOn_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_abs {s : Set Real} (hs : forall x in s, x != 0) : ContDiffOn Re
al n (|·|) s
参数：hs : forall x in s, x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffWithinAt_abs`：contDiffWithinAt_abs {x : Real} (hx : x != 0) (s :
 Set Real) : ContDiffWithinAt Real n (|·|) s x
-/
theorem contDiffOn_abs {s : Set ℝ} (hs : ∀ x ∈ s, x ≠ 0) :
    ContDiffOn ℝ n (|·|) s := fun x hx ↦ contDiffWithinAt_abs (hs x hx) s
/-
**ContDiffOn.abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.abs (hf : ContDiffOn Real n f s) (h₀ : forall x in s, f x != 0)
 : ContDiffOn Real n (fun y => |f y|) s
参数：hf : ContDiffOn Real n f s；h₀ : forall x in s, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.abs`：ContDiffWithinAt.abs (hf : ContDiffWithinAt Real n
 f s x) (h₀ : f x != 0) : ContDiffWithinAt Real n (fun y => |f y|) s x
-/
theorem ContDiffOn.abs (hf : ContDiffOn ℝ n f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun y ↦ |f y|) s := fun x hx ↦ (hf x hx).abs (h₀ x hx)
/-
**ContDiff.abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.abs (hf : ContDiff Real n f) (h₀ : forall x, f x != 0) : ContDiff
 Real n fun y => |f y|
参数：hf : ContDiff Real n f；h₀ : forall x, f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.abs`：ContDiffAt.abs (hf : ContDiffAt Real n f x) (h₀ : f x !=
 0) : ContDiffAt Real n (fun x => |f x|) x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
-/
theorem ContDiff.abs (hf : ContDiff ℝ n f) (h₀ : ∀ x, f x ≠ 0) : ContDiff ℝ n fun y ↦ |f y| :=
  contDiff_iff_contDiffAt.2 fun x ↦ hf.contDiffAt.abs (h₀ x)
/-
**hasStrictDerivAt_abs_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_abs_neg {x : Real} (hx : x < 0) : HasStrictDerivAt (|·|) 
(-1) x
参数：hx : x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.congr_of_eventuallyEq`：HasStrictDerivAt.congr_of_eventu
allyEq (h : HasStrictDerivAt f f' x) (h₁ : f =ᶠ[𝓝 x] f₁) : HasStrictDerivAt f₁ f
' x
· 使用定理 `hasStrictDerivAt_neg`：hasStrictDerivAt_neg : HasStrictDerivAt Neg.neg (-
1) x
· 使用定理 `Set.EqOn.eventuallyEq_of_mem`：Set.EqOn.eventuallyEq_of_mem {α β} {s : Se
t α} {l : Filter α} {f g : α -> β} (h : EqOn f g s) (hl : s in l) : f =ᶠ[l] g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem hasStrictDerivAt_abs_neg {x : ℝ} (hx : x < 0) :
    HasStrictDerivAt (|·|) (-1) x :=
  (hasStrictDerivAt_neg x).congr_of_eventuallyEq <|
    EqOn.eventuallyEq_of_mem (fun _ hy ↦ (abs_of_neg (mem_Iio.1 hy)).symm) (Iio_mem_nhds hx)
/-
**hasDerivAt_abs_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_abs_neg {x : Real} (hx : x < 0) : HasDerivAt (|·|) (-1) x
参数：hx : x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `hasStrictDerivAt_abs_neg`：hasStrictDerivAt_abs_neg {x : Real} (hx : x < 
0) : HasStrictDerivAt (|·|) (-1) x
-/
theorem hasDerivAt_abs_neg {x : ℝ} (hx : x < 0) :
    HasDerivAt (|·|) (-1) x := (hasStrictDerivAt_abs_neg hx).hasDerivAt
/-
**hasStrictDerivAt_abs_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_abs_pos {x : Real} (hx : 0 < x) : HasStrictDerivAt (|·|) 
1 x
参数：hx : 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.congr_of_eventuallyEq`：HasStrictDerivAt.congr_of_eventu
allyEq (h : HasStrictDerivAt f f' x) (h₁ : f =ᶠ[𝓝 x] f₁) : HasStrictDerivAt f₁ f
' x
· 使用定理 `hasStrictDerivAt_id`：hasStrictDerivAt_id : HasStrictDerivAt id 1 x
· 使用定理 `Set.EqOn.eventuallyEq_of_mem`：Set.EqOn.eventuallyEq_of_mem {α β} {s : Se
t α} {l : Filter α} {f g : α -> β} (h : EqOn f g s) (hl : s in l) : f =ᶠ[l] g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem hasStrictDerivAt_abs_pos {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (|·|) 1 x :=
  (hasStrictDerivAt_id x).congr_of_eventuallyEq <|
    EqOn.eventuallyEq_of_mem (fun _ hy ↦ (abs_of_pos (mem_Iio.1 hy)).symm) (Ioi_mem_nhds hx)
/-
**hasDerivAt_abs_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_abs_pos {x : Real} (hx : 0 < x) : HasDerivAt (|·|) 1 x
参数：hx : 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `hasStrictDerivAt_abs_pos`：hasStrictDerivAt_abs_pos {x : Real} (hx : 0 < 
x) : HasStrictDerivAt (|·|) 1 x
-/
theorem hasDerivAt_abs_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt (|·|) 1 x := (hasStrictDerivAt_abs_pos hx).hasDerivAt
/-
**hasStrictDerivAt_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_abs {x : Real} (hx : x != 0) : HasStrictDerivAt (|·|) (Si
gnType.sign x : Real) x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用引理 `SignType.coe_neg`：coe_neg {α : Type*} [One α] [SubtractionMonoid α] (s :
 SignType) : (↑(-s) : α) = -↑s
· 使用定理 `hasStrictDerivAt_abs_neg`：hasStrictDerivAt_abs_neg {x : Real} (hx : x < 
0) : HasStrictDerivAt (|·|) (-1) x
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `hasStrictDerivAt_abs_pos`：hasStrictDerivAt_abs_pos {x : Real} (hx : 0 < 
x) : HasStrictDerivAt (|·|) 1 x
-/
theorem hasStrictDerivAt_abs {x : ℝ} (hx : x ≠ 0) :
    HasStrictDerivAt (|·|) (SignType.sign x : ℝ) x := by
  obtain hx | hx := hx.lt_or_gt
  · simpa [hx] using hasStrictDerivAt_abs_neg hx
  · simpa [hx] using hasStrictDerivAt_abs_pos hx
/-
**hasDerivAt_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_abs {x : Real} (hx : x != 0) : HasDerivAt (|·|) (SignType.sign 
x : Real) x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `hasStrictDerivAt_abs`：hasStrictDerivAt_abs {x : Real} (hx : x != 0) : Ha
sStrictDerivAt (|·|) (SignType.sign x : Real) x
-/
theorem hasDerivAt_abs {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (|·|) (SignType.sign x : ℝ) x := (hasStrictDerivAt_abs hx).hasDerivAt
/-
**HasStrictFDerivAt.abs_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.abs_of_neg (hf : HasStrictFDerivAt f f' x) (h₀ : f x < 0
) : HasStrictFDerivAt (fun x => |f x|) (-f') x
参数：hf : HasStrictFDerivAt f f' x；h₀ : f x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `hasStrictDerivAt_abs_neg`：hasStrictDerivAt_abs_neg {x : Real} (hx : x < 
0) : HasStrictDerivAt (|·|) (-1) x
-/
theorem HasStrictFDerivAt.abs_of_neg (hf : HasStrictFDerivAt f f' x)
    (h₀ : f x < 0) : HasStrictFDerivAt (fun x ↦ |f x|) (-f') x := by
  convert! (hasStrictDerivAt_abs_neg h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp
/-
**HasFDerivAt.abs_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.abs_of_neg (hf : HasFDerivAt f f' x) (h₀ : f x < 0) : HasFDeri
vAt (fun x => |f x|) (-f') x
参数：hf : HasFDerivAt f f' x；h₀ : f x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `hasDerivAt_abs_neg`：hasDerivAt_abs_neg {x : Real} (hx : x < 0) : HasDeri
vAt (|·|) (-1) x
-/
theorem HasFDerivAt.abs_of_neg (hf : HasFDerivAt f f' x)
    (h₀ : f x < 0) : HasFDerivAt (fun x ↦ |f x|) (-f') x := by
  convert! (hasDerivAt_abs_neg h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp
/-
**HasStrictFDerivAt.abs_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.abs_of_pos (hf : HasStrictFDerivAt f f' x) (h₀ : 0 < f x
) : HasStrictFDerivAt (fun x => |f x|) f' x
参数：hf : HasStrictFDerivAt f f' x；h₀ : 0 < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `hasStrictDerivAt_abs_pos`：hasStrictDerivAt_abs_pos {x : Real} (hx : 0 < 
x) : HasStrictDerivAt (|·|) 1 x
-/
theorem HasStrictFDerivAt.abs_of_pos (hf : HasStrictFDerivAt f f' x)
    (h₀ : 0 < f x) : HasStrictFDerivAt (fun x ↦ |f x|) f' x := by
  convert! (hasStrictDerivAt_abs_pos h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp
/-
**HasFDerivAt.abs_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.abs_of_pos (hf : HasFDerivAt f f' x) (h₀ : 0 < f x) : HasFDeri
vAt (fun x => |f x|) f' x
参数：hf : HasFDerivAt f f' x；h₀ : 0 < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `hasDerivAt_abs_pos`：hasDerivAt_abs_pos {x : Real} (hx : 0 < x) : HasDeri
vAt (|·|) 1 x
-/
theorem HasFDerivAt.abs_of_pos (hf : HasFDerivAt f f' x)
    (h₀ : 0 < f x) : HasFDerivAt (fun x ↦ |f x|) f' x := by
  convert! (hasDerivAt_abs_pos h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp
/-
**HasStrictFDerivAt.abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.abs (hf : HasStrictFDerivAt f f' x) (h₀ : f x != 0) : Ha
sStrictFDerivAt (fun x => |f x|) ((SignType.sign (f x) : Real) • f') x
参数：hf : HasStrictFDerivAt f f' x；h₀ : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `hasStrictDerivAt_abs`：hasStrictDerivAt_abs {x : Real} (hx : x != 0) : Ha
sStrictDerivAt (|·|) (SignType.sign x : Real) x
-/
theorem HasStrictFDerivAt.abs (hf : HasStrictFDerivAt f f' x)
    (h₀ : f x ≠ 0) : HasStrictFDerivAt (fun x ↦ |f x|) ((SignType.sign (f x) : ℝ) • f') x := by
  convert! (hasStrictDerivAt_abs h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp [mul_comm]
/-
**HasFDerivAt.abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.abs (hf : HasFDerivAt f f' x) (h₀ : f x != 0) : HasFDerivAt (f
un x => |f x|) ((SignType.sign (f x) : Real) • f') x
参数：hf : HasFDerivAt f f' x；h₀ : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `hasDerivAt_abs`：hasDerivAt_abs {x : Real} (hx : x != 0) : HasDerivAt (|·
|) (SignType.sign x : Real) x
-/
theorem HasFDerivAt.abs (hf : HasFDerivAt f f' x)
    (h₀ : f x ≠ 0) : HasFDerivAt (fun x ↦ |f x|) ((SignType.sign (f x) : ℝ) • f') x := by
  convert! (hasDerivAt_abs h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp [mul_comm]
/-
**hasDerivWithinAt_abs_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_abs_neg (s : Set Real) {x : Real} (hx : x < 0) : HasDeriv
WithinAt (|·|) (-1) s x
参数：s : Set Real；hx : x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `hasDerivAt_abs_neg`：hasDerivAt_abs_neg {x : Real} (hx : x < 0) : HasDeri
vAt (|·|) (-1) x
-/
theorem hasDerivWithinAt_abs_neg (s : Set ℝ) {x : ℝ} (hx : x < 0) :
    HasDerivWithinAt (|·|) (-1) s x := (hasDerivAt_abs_neg hx).hasDerivWithinAt
/-
**hasDerivWithinAt_abs_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_abs_pos (s : Set Real) {x : Real} (hx : 0 < x) : HasDeriv
WithinAt (|·|) 1 s x
参数：s : Set Real；hx : 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `hasDerivAt_abs_pos`：hasDerivAt_abs_pos {x : Real} (hx : 0 < x) : HasDeri
vAt (|·|) 1 x
-/
theorem hasDerivWithinAt_abs_pos (s : Set ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt (|·|) 1 s x := (hasDerivAt_abs_pos hx).hasDerivWithinAt
/-
**hasDerivWithinAt_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_abs (s : Set Real) {x : Real} (hx : x != 0) : HasDerivWit
hinAt (|·|) (SignType.sign x : Real) s x
参数：s : Set Real；hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `hasDerivAt_abs`：hasDerivAt_abs {x : Real} (hx : x != 0) : HasDerivAt (|·
|) (SignType.sign x : Real) x
-/
theorem hasDerivWithinAt_abs (s : Set ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivWithinAt (|·|) (SignType.sign x : ℝ) s x := (hasDerivAt_abs hx).hasDerivWithinAt
/-
**HasFDerivWithinAt.abs_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.abs_of_neg (hf : HasFDerivWithinAt f f' s x) (h₀ : f x <
 0) : HasFDerivWithinAt (fun x => |f x|) (-f') s x
参数：hf : HasFDerivWithinAt f f' s x；h₀ : f x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `hasDerivAt_abs_neg`：hasDerivAt_abs_neg {x : Real} (hx : x < 0) : HasDeri
vAt (|·|) (-1) x
-/
theorem HasFDerivWithinAt.abs_of_neg (hf : HasFDerivWithinAt f f' s x)
    (h₀ : f x < 0) : HasFDerivWithinAt (fun x ↦ |f x|) (-f') s x := by
  convert! (hasDerivAt_abs_neg h₀).comp_hasFDerivWithinAt x hf using 1
  simp
/-
**HasFDerivWithinAt.abs_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.abs_of_pos (hf : HasFDerivWithinAt f f' s x) (h₀ : 0 < f
 x) : HasFDerivWithinAt (fun x => |f x|) f' s x
参数：hf : HasFDerivWithinAt f f' s x；h₀ : 0 < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `hasDerivAt_abs_pos`：hasDerivAt_abs_pos {x : Real} (hx : 0 < x) : HasDeri
vAt (|·|) 1 x
-/
theorem HasFDerivWithinAt.abs_of_pos (hf : HasFDerivWithinAt f f' s x)
    (h₀ : 0 < f x) : HasFDerivWithinAt (fun x ↦ |f x|) f' s x := by
  convert! (hasDerivAt_abs_pos h₀).comp_hasFDerivWithinAt x hf using 1
  simp
/-
**HasFDerivWithinAt.abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.abs (hf : HasFDerivWithinAt f f' s x) (h₀ : f x != 0) : 
HasFDerivWithinAt (fun x => |f x|) ((SignType.sign (f x) : Real) • f') s x
参数：hf : HasFDerivWithinAt f f' s x；h₀ : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `hasDerivAt_abs`：hasDerivAt_abs {x : Real} (hx : x != 0) : HasDerivAt (|·
|) (SignType.sign x : Real) x
-/
theorem HasFDerivWithinAt.abs (hf : HasFDerivWithinAt f f' s x)
    (h₀ : f x ≠ 0) : HasFDerivWithinAt (fun x ↦ |f x|) ((SignType.sign (f x) : ℝ) • f') s x :=
  (hasDerivAt_abs h₀).comp_hasFDerivWithinAt x hf
/-
**differentiableAt_abs_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_abs_neg {x : Real} (hx : x < 0) : DifferentiableAt Real (
|·|) x
参数：hx : x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `hasDerivAt_abs_neg`：hasDerivAt_abs_neg {x : Real} (hx : x < 0) : HasDeri
vAt (|·|) (-1) x
-/
theorem differentiableAt_abs_neg {x : ℝ} (hx : x < 0) :
    DifferentiableAt ℝ (|·|) x := (hasDerivAt_abs_neg hx).differentiableAt
/-
**differentiableAt_abs_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_abs_pos {x : Real} (hx : 0 < x) : DifferentiableAt Real (
|·|) x
参数：hx : 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `hasDerivAt_abs_pos`：hasDerivAt_abs_pos {x : Real} (hx : 0 < x) : HasDeri
vAt (|·|) 1 x
-/
theorem differentiableAt_abs_pos {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (|·|) x := (hasDerivAt_abs_pos hx).differentiableAt
/-
**differentiableAt_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_abs {x : Real} (hx : x != 0) : DifferentiableAt Real (|·|
) x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `hasDerivAt_abs`：hasDerivAt_abs {x : Real} (hx : x != 0) : HasDerivAt (|·
|) (SignType.sign x : Real) x
-/
theorem differentiableAt_abs {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ (|·|) x := (hasDerivAt_abs hx).differentiableAt
/-
**DifferentiableAt.abs_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.abs_of_neg (hf : DifferentiableAt Real f x) (h₀ : f x < 0
) : DifferentiableAt Real (fun x => |f x|) x
参数：hf : DifferentiableAt Real f x；h₀ : f x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `differentiableAt_abs_neg`：differentiableAt_abs_neg {x : Real} (hx : x < 
0) : DifferentiableAt Real (|·|) x
-/
theorem DifferentiableAt.abs_of_neg (hf : DifferentiableAt ℝ f x) (h₀ : f x < 0) :
    DifferentiableAt ℝ (fun x ↦ |f x|) x := (differentiableAt_abs_neg h₀).comp x hf
/-
**DifferentiableAt.abs_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.abs_of_pos (hf : DifferentiableAt Real f x) (h₀ : 0 < f x
) : DifferentiableAt Real (fun x => |f x|) x
参数：hf : DifferentiableAt Real f x；h₀ : 0 < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `differentiableAt_abs_pos`：differentiableAt_abs_pos {x : Real} (hx : 0 < 
x) : DifferentiableAt Real (|·|) x
-/
theorem DifferentiableAt.abs_of_pos (hf : DifferentiableAt ℝ f x) (h₀ : 0 < f x) :
    DifferentiableAt ℝ (fun x ↦ |f x|) x := (differentiableAt_abs_pos h₀).comp x hf
/-
**DifferentiableAt.abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.abs (hf : DifferentiableAt Real f x) (h₀ : f x != 0) : Di
fferentiableAt Real (fun x => |f x|) x
参数：hf : DifferentiableAt Real f x；h₀ : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `differentiableAt_abs`：differentiableAt_abs {x : Real} (hx : x != 0) : Di
fferentiableAt Real (|·|) x
-/
theorem DifferentiableAt.abs (hf : DifferentiableAt ℝ f x) (h₀ : f x ≠ 0) :
    DifferentiableAt ℝ (fun x ↦ |f x|) x := (differentiableAt_abs h₀).comp x hf
/-
**differentiableWithinAt_abs_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_abs_neg (s : Set Real) {x : Real} (hx : x < 0) : Di
fferentiableWithinAt Real (|·|) s x
参数：s : Set Real；hx : x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_abs_neg`：differentiableAt_abs_neg {x : Real} (hx : x < 
0) : DifferentiableAt Real (|·|) x
-/
theorem differentiableWithinAt_abs_neg (s : Set ℝ) {x : ℝ} (hx : x < 0) :
    DifferentiableWithinAt ℝ (|·|) s x := (differentiableAt_abs_neg hx).differentiableWithinAt
/-
**differentiableWithinAt_abs_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_abs_pos (s : Set Real) {x : Real} (hx : 0 < x) : Di
fferentiableWithinAt Real (|·|) s x
参数：s : Set Real；hx : 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_abs_pos`：differentiableAt_abs_pos {x : Real} (hx : 0 < 
x) : DifferentiableAt Real (|·|) x
-/
theorem differentiableWithinAt_abs_pos (s : Set ℝ) {x : ℝ} (hx : 0 < x) :
    DifferentiableWithinAt ℝ (|·|) s x := (differentiableAt_abs_pos hx).differentiableWithinAt
/-
**differentiableWithinAt_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_abs (s : Set Real) {x : Real} (hx : x != 0) : Diffe
rentiableWithinAt Real (|·|) s x
参数：s : Set Real；hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_abs`：differentiableAt_abs {x : Real} (hx : x != 0) : Di
fferentiableAt Real (|·|) x
-/
theorem differentiableWithinAt_abs (s : Set ℝ) {x : ℝ} (hx : x ≠ 0) :
    DifferentiableWithinAt ℝ (|·|) s x := (differentiableAt_abs hx).differentiableWithinAt
/-
**DifferentiableWithinAt.abs_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.abs_of_neg (hf : DifferentiableWithinAt Real f s x)
 (h₀ : f x < 0) : DifferentiableWithinAt Real (fun x => |f x|) s x
参数：hf : DifferentiableWithinAt Real f s x；h₀ : f x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp_differentiableWithinAt`：DifferentiableAt.comp_diff
erentiableWithinAt {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : Differen
tiableWithinAt 𝕜 f s x) : Differen…
· 使用定理 `differentiableAt_abs_neg`：differentiableAt_abs_neg {x : Real} (hx : x < 
0) : DifferentiableAt Real (|·|) x
-/
theorem DifferentiableWithinAt.abs_of_neg (hf : DifferentiableWithinAt ℝ f s x) (h₀ : f x < 0) :
    DifferentiableWithinAt ℝ (fun x ↦ |f x|) s x :=
  (differentiableAt_abs_neg h₀).comp_differentiableWithinAt x hf
/-
**DifferentiableWithinAt.abs_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.abs_of_pos (hf : DifferentiableWithinAt Real f s x)
 (h₀ : 0 < f x) : DifferentiableWithinAt Real (fun x => |f x|) s x
参数：hf : DifferentiableWithinAt Real f s x；h₀ : 0 < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp_differentiableWithinAt`：DifferentiableAt.comp_diff
erentiableWithinAt {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : Differen
tiableWithinAt 𝕜 f s x) : Differen…
· 使用定理 `differentiableAt_abs_pos`：differentiableAt_abs_pos {x : Real} (hx : 0 < 
x) : DifferentiableAt Real (|·|) x
-/
theorem DifferentiableWithinAt.abs_of_pos (hf : DifferentiableWithinAt ℝ f s x) (h₀ : 0 < f x) :
    DifferentiableWithinAt ℝ (fun x ↦ |f x|) s x :=
  (differentiableAt_abs_pos h₀).comp_differentiableWithinAt x hf
/-
**DifferentiableWithinAt.abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.abs (hf : DifferentiableWithinAt Real f s x) (h₀ : 
f x != 0) : DifferentiableWithinAt Real (fun x => |f x|) s x
参数：hf : DifferentiableWithinAt Real f s x；h₀ : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp_differentiableWithinAt`：DifferentiableAt.comp_diff
erentiableWithinAt {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : Differen
tiableWithinAt 𝕜 f s x) : Differen…
· 使用定理 `differentiableAt_abs`：differentiableAt_abs {x : Real} (hx : x != 0) : Di
fferentiableAt Real (|·|) x
-/
theorem DifferentiableWithinAt.abs (hf : DifferentiableWithinAt ℝ f s x) (h₀ : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun x ↦ |f x|) s x :=
  (differentiableAt_abs h₀).comp_differentiableWithinAt x hf
/-
**differentiableOn_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_abs {s : Set Real} (hs : forall x in s, x != 0) : Differe
ntiableOn Real (|·|) s
参数：hs : forall x in s, x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableWithinAt_abs`：differentiableWithinAt_abs (s : Set Real) {x
 : Real} (hx : x != 0) : DifferentiableWithinAt Real (|·|) s x
-/
theorem differentiableOn_abs {s : Set ℝ} (hs : ∀ x ∈ s, x ≠ 0) : DifferentiableOn ℝ (|·|) s :=
  fun x hx ↦ differentiableWithinAt_abs s (hs x hx)
/-
**DifferentiableOn.abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.abs (hf : DifferentiableOn Real f s) (h₀ : forall x in s,
 f x != 0) : DifferentiableOn Real (fun x => |f x|) s
参数：hf : DifferentiableOn Real f s；h₀ : forall x in s, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.abs`：DifferentiableWithinAt.abs (hf : Differentia
bleWithinAt Real f s x) (h₀ : f x != 0) : DifferentiableWithinAt Real (fun x => 
|f x|) s x
-/
theorem DifferentiableOn.abs (hf : DifferentiableOn ℝ f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
    DifferentiableOn ℝ (fun x ↦ |f x|) s :=
  fun x hx ↦ (hf x hx).abs (h₀ x hx)
/-
**Differentiable.abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.abs (hf : Differentiable Real f) (h₀ : forall x, f x != 0) 
: Differentiable Real (fun x => |f x|)
参数：hf : Differentiable Real f；h₀ : forall x, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.abs`：DifferentiableAt.abs (hf : DifferentiableAt Real f
 x) (h₀ : f x != 0) : DifferentiableAt Real (fun x => |f x|) x
-/
theorem Differentiable.abs (hf : Differentiable ℝ f) (h₀ : ∀ x, f x ≠ 0) :
    Differentiable ℝ (fun x ↦ |f x|) := fun x ↦ (hf x).abs (h₀ x)
/-
**not_differentiableAt_abs_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_differentiableAt_abs_zero : ¬ DifferentiableAt Real (abs : Real -> Rea
l) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.eq_deriv`：UniqueDiffWithinAt.eq_deriv (s : Set 𝕜) (H 
: UniqueDiffWithinAt 𝕜 s x) (h : HasDerivWithinAt f f' s x) (h₁ : HasDerivWithin
At f f₁' s x) : f…
· 使用定理 `uniqueDiffOn_Ici`：uniqueDiffOn_Ici (a : Real) : UniqueDiffOn Real (Ici a
)
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `HasDerivWithinAt.congr_of_mem`：HasDerivWithinAt.congr_of_mem (h : HasDer
ivWithinAt f f' s x) (hs : forall x in s, f₁ x = f x) (hx : x in s) : HasDerivWi
thinAt f₁ f' s x
· 使用定理 `hasDerivWithinAt_id`：hasDerivWithinAt_id : HasDerivWithinAt id 1 s x
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `uniqueDiffOn_Iic`：uniqueDiffOn_Iic (a : Real) : UniqueDiffOn Real (Iic a
)
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
· 使用定理 `hasDerivWithinAt_neg`：hasDerivWithinAt_neg : HasDerivWithinAt Neg.neg (-
1) s x
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 63 条，此处仅展示前 30 条）
-/
theorem not_differentiableAt_abs_zero : ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
  intro h
  have h₁ : deriv abs (0 : ℝ) = 1 :=
    (uniqueDiffOn_Ici _ _ Set.self_mem_Ici).eq_deriv _ h.hasDerivAt.hasDerivWithinAt <|
      (hasDerivWithinAt_id _ _).congr_of_mem (fun _ h ↦ abs_of_nonneg h) Set.self_mem_Ici
  have h₂ : deriv abs (0 : ℝ) = -1 :=
    (uniqueDiffOn_Iic _ _ Set.self_mem_Iic).eq_deriv _ h.hasDerivAt.hasDerivWithinAt <|
      (hasDerivWithinAt_neg _ _).congr_of_mem (fun _ h ↦ abs_of_nonpos h) Set.self_mem_Iic
  linarith
/-
**deriv_abs_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_abs_neg {x : Real} (hx : x < 0) : deriv (|·|) x = -1
参数：hx : x < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `hasDerivAt_abs_neg`：hasDerivAt_abs_neg {x : Real} (hx : x < 0) : HasDeri
vAt (|·|) (-1) x
-/
theorem deriv_abs_neg {x : ℝ} (hx : x < 0) : deriv (|·|) x = -1 := (hasDerivAt_abs_neg hx).deriv
/-
**deriv_abs_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_abs_pos {x : Real} (hx : 0 < x) : deriv (|·|) x = 1
参数：hx : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `hasDerivAt_abs_pos`：hasDerivAt_abs_pos {x : Real} (hx : 0 < x) : HasDeri
vAt (|·|) 1 x
-/
theorem deriv_abs_pos {x : ℝ} (hx : 0 < x) : deriv (|·|) x = 1 := (hasDerivAt_abs_pos hx).deriv
/-
**deriv_abs_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_abs_zero : deriv (|·|) (0 : Real) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `not_differentiableAt_abs_zero`：not_differentiableAt_abs_zero : ¬ Differe
ntiableAt Real (abs : Real -> Real) 0
-/
theorem deriv_abs_zero : deriv (|·|) (0 : ℝ) = 0 :=
  deriv_zero_of_not_differentiableAt not_differentiableAt_abs_zero
/-
**deriv_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_abs (x : Real) : deriv (|·|) x = SignType.sign x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `deriv_abs_zero`：deriv_abs_zero : deriv (|·|) (0 : Real) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `hasDerivAt_abs`：hasDerivAt_abs {x : Real} (hx : x != 0) : HasDerivAt (|·
|) (SignType.sign x : Real) x
-/
theorem deriv_abs (x : ℝ) : deriv (|·|) x = SignType.sign x := by
  obtain rfl | hx := eq_or_ne x 0
  · simpa using deriv_abs_zero
  · simpa [hx] using (hasDerivAt_abs hx).deriv
