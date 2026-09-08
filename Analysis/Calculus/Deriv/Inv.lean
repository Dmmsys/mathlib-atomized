/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Derivatives of `x ↦ x⁻¹` and `f x / g x`

In this file we prove `(x⁻¹)' = -1 / x ^ 2`, `((f x)⁻¹)' = -f' x / (f x) ^ 2`, and
`(f x / g x)' = (f' x * g x - f x * g' x) / (g x) ^ 2` for different notions of derivative.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative
-/

public section


universe u

open scoped Topology
open Filter Asymptotics Set

open ContinuousLinearMap (toSpanSingleton)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜}

section Inverse

/-! ### Derivative of `x ↦ x⁻¹` -/

/-
**hasStrictDerivAt_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_inv (hx : x != 0) : HasStrictDerivAt Inv.inv (-(x ^ 2)⁻¹)
 x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.mul_isLittleO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.inv₀`：Filter.Tendsto.inv₀ {a : G₀} (hf : Tendsto f l (𝓝 a
)) (ha : a != 0) : Tendsto (fun x => (f x)⁻¹) l (𝓝 a⁻¹)
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `HasFDerivAtFilter.of_isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {F : Typ…
· 使用定理 `Asymptotics.IsLittleO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ :
 α → F}, f₁ =o[l] …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpen.prod`：IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : I
sOpen t) : IsOpen (s ×ˢ t)
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
（共 105 条，此处仅展示前 30 条）

--- 原说明 ---
### Derivative of `x ↦ x⁻¹`
-/
theorem hasStrictDerivAt_inv (hx : x ≠ 0) : HasStrictDerivAt Inv.inv (-(x ^ 2)⁻¹) x := by
  suffices
    (fun p : 𝕜 × 𝕜 => (p.1 - p.2) * ((x * x)⁻¹ - (p.1 * p.2)⁻¹)) =o[𝓝 (x, x)] fun p =>
      (p.1 - p.2) * 1 by
    refine .of_isLittleO <| this.congr' ?_ (Eventually.of_forall fun _ => mul_one _)
    refine Eventually.mono ((isOpen_ne.prod isOpen_ne).mem_nhds ⟨hx, hx⟩) ?_
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    simp only [mem_ofPred_eq] at hy hz
    simp [field]
    ring
  refine (isBigO_refl (fun p : 𝕜 × 𝕜 => p.1 - p.2) _).mul_isLittleO ((isLittleO_one_iff 𝕜).2 ?_)
  rw [← sub_self (x * x)⁻¹]
  exact tendsto_const_nhds.sub ((continuous_mul.tendsto (x, x)).inv₀ <| mul_ne_zero hx hx)
/-
**hasDerivAt_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_inv (x_ne_zero : x != 0) : HasDerivAt (fun y => y⁻¹) (-(x ^ 2)⁻
¹) x
参数：x_ne_zero : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `hasStrictDerivAt_inv`：hasStrictDerivAt_inv (hx : x != 0) : HasStrictDeri
vAt Inv.inv (-(x ^ 2)⁻¹) x
-/
theorem hasDerivAt_inv (x_ne_zero : x ≠ 0) : HasDerivAt (fun y => y⁻¹) (-(x ^ 2)⁻¹) x :=
  (hasStrictDerivAt_inv x_ne_zero).hasDerivAt
/-
**hasDerivWithinAt_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_inv (x_ne_zero : x != 0) (s : Set 𝕜) : HasDerivWithinAt (
fun x => x⁻¹) (-(x ^ 2)⁻¹) s x
参数：x_ne_zero : x != 0；s : Set 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `hasDerivAt_inv`：hasDerivAt_inv (x_ne_zero : x != 0) : HasDerivAt (fun y 
=> y⁻¹) (-(x ^ 2)⁻¹) x
-/
theorem hasDerivWithinAt_inv (x_ne_zero : x ≠ 0) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => x⁻¹) (-(x ^ 2)⁻¹) s x :=
  (hasDerivAt_inv x_ne_zero).hasDerivWithinAt
/-
**differentiableAt_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_inv_iff : DifferentiableAt 𝕜 (fun x => x⁻¹) x ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NormedField.continuousAt_inv`：∀ {𝕜 : Type u_4} [inst : NontriviallyNorme
dField 𝕜] {x : 𝕜}, ContinuousAt Inv.inv x ↔ x ≠ 0
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
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
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `hasDerivAt_inv`：hasDerivAt_inv (x_ne_zero : x != 0) : HasDerivAt (fun y 
=> y⁻¹) (-(x ^ 2)⁻¹) x
-/
theorem differentiableAt_inv_iff : DifferentiableAt 𝕜 (fun x => x⁻¹) x ↔ x ≠ 0 :=
  ⟨fun H => NormedField.continuousAt_inv.1 H.continuousAt, fun H =>
    (hasDerivAt_inv H).differentiableAt⟩
/-
**deriv_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_inv : deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `differentiableAt_inv_iff`：differentiableAt_inv_iff : DifferentiableAt 𝕜 
(fun x => x⁻¹) x ↔ x != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `hasDerivAt_inv`：hasDerivAt_inv (x_ne_zero : x != 0) : HasDerivAt (fun y 
=> y⁻¹) (-(x ^ 2)⁻¹) x
-/
theorem deriv_inv : deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹ := by
  rcases eq_or_ne x 0 with (rfl | hne)
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_inv_iff.1 (not_not.2 rfl))]
    simp
  · exact (hasDerivAt_inv hne).deriv

@[simp]
/-
**deriv_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_inv' : (deriv fun x : 𝕜 => x⁻¹) = fun x => -(x ^ 2)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_inv`：deriv_inv : deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹
-/
theorem deriv_inv' : (deriv fun x : 𝕜 => x⁻¹) = fun x => -(x ^ 2)⁻¹ :=
  funext fun _ => deriv_inv
/-
**derivWithin_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_inv (x_ne_zero : x != 0) (hxs : UniqueDiffWithinAt 𝕜 s x) : de
rivWithin (fun x => x⁻¹) s x = -(x ^ 2)⁻¹
参数：x_ne_zero : x != 0；hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DifferentiableAt.derivWithin`：DifferentiableAt.derivWithin (h : Differen
tiableAt 𝕜 f x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = deriv f x
· 使用定理 `differentiableAt_inv`：differentiableAt_inv {x : R} (hx : x != 0) : Diffe
rentiableAt 𝕜 Inv.inv x
· 使用定理 `deriv_inv`：deriv_inv : deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹
-/
theorem derivWithin_inv (x_ne_zero : x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => x⁻¹) s x = -(x ^ 2)⁻¹ := by
  rw [DifferentiableAt.derivWithin (differentiableAt_inv x_ne_zero) hxs]
  exact deriv_inv
/-
**hasFDerivAt_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_inv (x_ne_zero : x != 0) : HasFDerivAt (fun x => x⁻¹) (toSpanS
ingleton 𝕜 (-(x ^ 2)⁻¹) : 𝕜 ->L[𝕜] 𝕜) x
参数：x_ne_zero : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAt_inv`：hasDerivAt_inv (x_ne_zero : x != 0) : HasDerivAt (fun y 
=> y⁻¹) (-(x ^ 2)⁻¹) x
-/
theorem hasFDerivAt_inv (x_ne_zero : x ≠ 0) :
    HasFDerivAt (fun x => x⁻¹) (toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) : 𝕜 →L[𝕜] 𝕜) x :=
  hasDerivAt_inv x_ne_zero
/-
**hasStrictFDerivAt_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_inv (x_ne_zero : x != 0) : HasStrictFDerivAt (fun x => x
⁻¹) (toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) : 𝕜 ->L[𝕜] 𝕜) x
参数：x_ne_zero : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictDerivAt_inv`：hasStrictDerivAt_inv (hx : x != 0) : HasStrictDeri
vAt Inv.inv (-(x ^ 2)⁻¹) x
-/
theorem hasStrictFDerivAt_inv (x_ne_zero : x ≠ 0) :
    HasStrictFDerivAt (fun x => x⁻¹) (toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) : 𝕜 →L[𝕜] 𝕜) x :=
  hasStrictDerivAt_inv x_ne_zero
/-
**hasFDerivWithinAt_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_inv (x_ne_zero : x != 0) : HasFDerivWithinAt (fun x => x
⁻¹) (toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) : 𝕜 ->L[𝕜] 𝕜) s x
参数：x_ne_zero : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
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
· 使用定理 `hasFDerivAt_inv`：hasFDerivAt_inv (x_ne_zero : x != 0) : HasFDerivAt (fun
 x => x⁻¹) (toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) : 𝕜 ->L[𝕜] 𝕜) x
-/
theorem hasFDerivWithinAt_inv (x_ne_zero : x ≠ 0) :
    HasFDerivWithinAt (fun x => x⁻¹) (toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) : 𝕜 →L[𝕜] 𝕜) s x :=
  (hasFDerivAt_inv x_ne_zero).hasFDerivWithinAt
/-
**fderiv_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_inv : fderiv 𝕜 (fun x => x⁻¹) x = toSpanSingleton 𝕜 (-(x ^ 2)⁻¹)
该定理/引理给出了一组等式。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `toSpanSingleton_deriv`：toSpanSingleton_deriv : toSpanSingleton 𝕜 (deriv 
f x) = fderiv 𝕜 f x
· 使用定理 `deriv_inv`：deriv_inv : deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹
-/
theorem fderiv_inv : fderiv 𝕜 (fun x => x⁻¹) x = toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) := by
  rw [← toSpanSingleton_deriv, deriv_inv]
/-
**fderivWithin_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_inv (x_ne_zero : x != 0) (hxs : UniqueDiffWithinAt 𝕜 s x) : f
derivWithin 𝕜 (fun x => x⁻¹) s x = toSpanSingleton 𝕜 (-(x ^ 2)⁻¹)
参数：x_ne_zero : x != 0；hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DifferentiableAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `differentiableAt_inv`：differentiableAt_inv {x : R} (hx : x != 0) : Diffe
rentiableAt 𝕜 Inv.inv x
· 使用定理 `fderiv_inv`：fderiv_inv : fderiv 𝕜 (fun x => x⁻¹) x = toSpanSingleton 𝕜 (
-(x ^ 2)⁻¹)
-/
theorem fderivWithin_inv (x_ne_zero : x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => x⁻¹) s x = toSpanSingleton 𝕜 (-(x ^ 2)⁻¹) := by
  rw [DifferentiableAt.fderivWithin (differentiableAt_inv x_ne_zero) hxs]
  exact fderiv_inv

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
variable {c : 𝕜 → 𝕜'} {c' : 𝕜'}

@[to_fun]
/-
**HasDerivWithinAt.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.inv (hc : HasDerivWithinAt c c' s x) (hx : c x != 0) : Ha
sDerivWithinAt (c⁻¹) (-c' / c x ^ 2) s x
参数：hc : HasDerivWithinAt c c' s x；hx : c x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 42 条，此处仅展示前 30 条）
-/
theorem HasDerivWithinAt.inv (hc : HasDerivWithinAt c c' s x) (hx : c x ≠ 0) :
    HasDerivWithinAt (c⁻¹) (-c' / c x ^ 2) s x := by
  convert! (hasDerivAt_inv hx).comp_hasDerivWithinAt x hc using 1
  ring

@[to_fun]
/-
**HasDerivAt.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.inv (hc : HasDerivAt c c' x) (hx : c x != 0) : HasDerivAt (c⁻¹)
 (-c' / c x ^ 2) x
参数：hc : HasDerivAt c c' x；hx : c x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
· 使用定理 `HasDerivWithinAt.inv`：HasDerivWithinAt.inv (hc : HasDerivWithinAt c c' s
 x) (hx : c x != 0) : HasDerivWithinAt (c⁻¹) (-c' / c x ^ 2) s x
-/
theorem HasDerivAt.inv (hc : HasDerivAt c c' x) (hx : c x ≠ 0) :
    HasDerivAt (c⁻¹) (-c' / c x ^ 2) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.inv hx
/-
**derivWithin_fun_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_fun_inv' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x != 0)
 : derivWithin (fun x => (c x)⁻¹) s x = -derivWithin c s x / c x ^ 2
参数：hc : DifferentiableWithinAt 𝕜 c s x；hx : c x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.inv`：HasDerivWithinAt.inv (hc : HasDerivWithinAt c c' s
 x) (hx : c x != 0) : HasDerivWithinAt (c⁻¹) (-c' / c x ^ 2) s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin_zero_of_not_uniqueDiffWithinAt`：derivWithin_zero_of_not_uniq
ueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_fun_inv' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x ≠ 0) :
    derivWithin (fun x => (c x)⁻¹) s x = -derivWithin c s x / c x ^ 2 := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.inv hx).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]
/-
**derivWithin_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_inv' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x != 0) : d
erivWithin (c⁻¹) s x = -derivWithin c s x / c x ^ 2
参数：hc : DifferentiableWithinAt 𝕜 c s x；hx : c x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_fun_inv'`：derivWithin_fun_inv' (hc : DifferentiableWithinAt 
𝕜 c s x) (hx : c x != 0) : derivWithin (fun x => (c x)⁻¹) s x = -derivWithin c s
 x / c x ^…
-/
theorem derivWithin_inv' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x ≠ 0) :
    derivWithin (c⁻¹) s x = -derivWithin c s x / c x ^ 2 :=
  derivWithin_fun_inv' hc hx

@[simp]
/-
**deriv_fun_inv''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_fun_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x != 0) : deriv (fun
 x => (c x)⁻¹) x = -deriv c x / c x ^ 2
参数：hc : DifferentiableAt 𝕜 c x；hx : c x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.inv`：HasDerivAt.inv (hc : HasDerivAt c c' x) (hx : c x != 0) 
: HasDerivAt (c⁻¹) (-c' / c x ^ 2) x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_fun_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x ≠ 0) :
    deriv (fun x => (c x)⁻¹) x = -deriv c x / c x ^ 2 :=
  (hc.hasDerivAt.inv hx).deriv

@[simp]
/-
**deriv_inv''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x != 0) : deriv (c⁻¹) x 
= -deriv c x / c x ^ 2
参数：hc : DifferentiableAt 𝕜 c x；hx : c x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.inv`：HasDerivAt.inv (hc : HasDerivAt c c' x) (hx : c x != 0) 
: HasDerivAt (c⁻¹) (-c' / c x ^ 2) x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x ≠ 0) :
    deriv (c⁻¹) x = -deriv c x / c x ^ 2 :=
  (hc.hasDerivAt.inv hx).deriv

end Inverse

section Division

/-! ### Derivative of `x ↦ c x / d x` -/

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {c d : 𝕜 → 𝕜'} {c' d' : 𝕜'}

/-
**HasDerivWithinAt.fun_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.fun_div (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWi
thinAt d d' s x) (hx : d x != 0) : HasDerivWithinAt (fun y => c y / d y) ((c' * 
d x - c x * d') / d x ^ 2) s x
参数：hc : HasDerivWithinAt c c' s x；hd : HasDerivWithinAt d d' s x；hx : d x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
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
（共 71 条，此处仅展示前 30 条）
-/
theorem HasDerivWithinAt.fun_div (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x)
    (hx : d x ≠ 0) :
    HasDerivWithinAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) s x := by
  convert hc.fun_mul ((hasDerivAt_inv hx).comp_hasDerivWithinAt x hd)
  · simp only [div_eq_mul_inv, (· ∘ ·)]
  · simp [field]
    ring
/-
**HasDerivWithinAt.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.div (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithin
At d d' s x) (hx : d x != 0) : HasDerivWithinAt (c / d) ((c' * d x - c x * d') /
 d x ^ 2) s x
参数：hc : HasDerivWithinAt c c' s x；hd : HasDerivWithinAt d d' s x；hx : d x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.fun_div`：HasDerivWithinAt.fun_div (hc : HasDerivWithinA
t c c' s x) (hd : HasDerivWithinAt d d' s x) (hx : d x != 0) : HasDerivWithinAt 
(fun y => c y …
-/
theorem HasDerivWithinAt.div (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x)
    (hx : d x ≠ 0) :
    HasDerivWithinAt (c / d) ((c' * d x - c x * d') / d x ^ 2) s x :=
  hc.fun_div hd hx
/-
**HasStrictDerivAt.fun_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.fun_div (hc : HasStrictDerivAt c c' x) (hd : HasStrictDer
ivAt d d' x) (hx : d x != 0) : HasStrictDerivAt (fun y => c y / d y) ((c' * d x 
- c x * d') / d x ^ 2) x
参数：hc : HasStrictDerivAt c c' x；hd : HasStrictDerivAt d d' x；hx : d x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
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
（共 71 条，此处仅展示前 30 条）
-/
theorem HasStrictDerivAt.fun_div (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
    (hx : d x ≠ 0) : HasStrictDerivAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) x := by
  convert hc.fun_mul ((hasStrictDerivAt_inv hx).comp x hd)
  · simp only [div_eq_mul_inv, (· ∘ ·)]
  · simp [field]
    ring
/-
**HasStrictDerivAt.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.div (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt
 d d' x) (hx : d x != 0) : HasStrictDerivAt (c / d) ((c' * d x - c x * d') / d x
 ^ 2) x
参数：hc : HasStrictDerivAt c c' x；hd : HasStrictDerivAt d d' x；hx : d x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.fun_div`：HasStrictDerivAt.fun_div (hc : HasStrictDerivA
t c c' x) (hd : HasStrictDerivAt d d' x) (hx : d x != 0) : HasStrictDerivAt (fun
 y => c y / d …
-/
theorem HasStrictDerivAt.div (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
    (hx : d x ≠ 0) : HasStrictDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x :=
  hc.fun_div hd hx
/-
**HasDerivAt.fun_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.fun_div (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) (hx :
 d x != 0) : HasDerivAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) x
参数：hc : HasDerivAt c c' x；hd : HasDerivAt d d' x；hx : d x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
· 使用定理 `HasDerivWithinAt.div`：HasDerivWithinAt.div (hc : HasDerivWithinAt c c' s
 x) (hd : HasDerivWithinAt d d' s x) (hx : d x != 0) : HasDerivWithinAt (c / d) 
((c' * d x…
-/
theorem HasDerivAt.fun_div (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) (hx : d x ≠ 0) :
    HasDerivAt (fun y => c y / d y) ((c' * d x - c x * d') / d x ^ 2) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.div hd hx
/-
**HasDerivAt.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.div (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) (hx : d x
 != 0) : HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x
参数：hc : HasDerivAt c c' x；hd : HasDerivAt d d' x；hx : d x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.fun_div`：HasDerivAt.fun_div (hc : HasDerivAt c c' x) (hd : Ha
sDerivAt d d' x) (hx : d x != 0) : HasDerivAt (fun y => c y / d y) ((c' * d x - 
c x * d'…
-/
theorem HasDerivAt.div (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) (hx : d x ≠ 0) :
    HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x :=
  hc.fun_div hd hx
/-
**DifferentiableWithinAt.fun_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.fun_div (hc : DifferentiableWithinAt 𝕜 c s x) (hd :
 DifferentiableWithinAt 𝕜 d s x) (hx : d x != 0) : DifferentiableWithinAt 𝕜 (fun
 x => c x / d x) s x
参数：hc : DifferentiableWithinAt 𝕜 c s x；hd : DifferentiableWithinAt 𝕜 d s x；hx : 
d x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivWithinAt.div`：HasDerivWithinAt.div (hc : HasDerivWithinAt c c' s
 x) (hd : HasDerivWithinAt d d' s x) (hx : d x != 0) : HasDerivWithinAt (c / d) 
((c' * d x…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem DifferentiableWithinAt.fun_div (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) (hx : d x ≠ 0) :
    DifferentiableWithinAt 𝕜 (fun x => c x / d x) s x :=
  (hc.hasDerivWithinAt.div hd.hasDerivWithinAt hx).differentiableWithinAt
/-
**DifferentiableWithinAt.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.div (hc : DifferentiableWithinAt 𝕜 c s x) (hd : Dif
ferentiableWithinAt 𝕜 d s x) (hx : d x != 0) : DifferentiableWithinAt 𝕜 (c / d) 
s x
参数：hc : DifferentiableWithinAt 𝕜 c s x；hd : DifferentiableWithinAt 𝕜 d s x；hx : 
d x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.fun_div`：DifferentiableWithinAt.fun_div (hc : Dif
ferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x) (hx : d x != 
0) : DifferentiableW…
-/
theorem DifferentiableWithinAt.div (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) (hx : d x ≠ 0) :
    DifferentiableWithinAt 𝕜 (c / d) s x :=
  hc.fun_div hd hx

@[to_fun (attr := simp, fun_prop)]
/-
**DifferentiableAt.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 
𝕜 d x) (hx : d x != 0) : DifferentiableAt 𝕜 (c / d) x
参数：hc : DifferentiableAt 𝕜 c x；hd : DifferentiableAt 𝕜 d x；hx : d x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasDerivAt.div`：HasDerivAt.div (hc : HasDerivAt c c' x) (hd : HasDerivAt
 d d' x) (hx : d x != 0) : HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) 
x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem DifferentiableAt.div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
    (hx : d x ≠ 0) : DifferentiableAt 𝕜 (c / d) x :=
  (hc.hasDerivAt.div hd.hasDerivAt hx).differentiableAt

@[to_fun (attr := fun_prop)]
/-
**DifferentiableOn.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.div (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 
𝕜 d s) (hx : forall x in s, d x != 0) : DifferentiableOn 𝕜 (c / d) s
参数：hc : DifferentiableOn 𝕜 c s；hd : DifferentiableOn 𝕜 d s；hx : forall x in s, d
 x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.div`：DifferentiableWithinAt.div (hc : Differentia
bleWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x) (hx : d x != 0) : Dif
ferentiableWithi…
-/
theorem DifferentiableOn.div (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s)
    (hx : ∀ x ∈ s, d x ≠ 0) : DifferentiableOn 𝕜 (c / d) s := fun x h =>
  (hc x h).div (hd x h) (hx x h)

@[to_fun (attr := simp, fun_prop)]
/-
**Differentiable.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.div (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d) (hx
 : forall x, d x != 0) : Differentiable 𝕜 (c / d)
参数：hc : Differentiable 𝕜 c；hd : Differentiable 𝕜 d；hx : forall x, d x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.div`：DifferentiableAt.div (hc : DifferentiableAt 𝕜 c x)
 (hd : DifferentiableAt 𝕜 d x) (hx : d x != 0) : DifferentiableAt 𝕜 (c / d) x
-/
theorem Differentiable.div (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d) (hx : ∀ x, d x ≠ 0) :
    Differentiable 𝕜 (c / d) := fun x => (hc x).div (hd x) (hx x)
/-
**derivWithin_fun_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_fun_div (hc : DifferentiableWithinAt 𝕜 c s x) (hd : Differenti
ableWithinAt 𝕜 d s x) (hx : d x != 0) : derivWithin (fun x => c x / d x) s x = (
derivWithin c s x * d x - c x * derivWithin d s x) / d x ^ 2
参数：hc : DifferentiableWithinAt 𝕜 c s x；hd : DifferentiableWithinAt 𝕜 d s x；hx : 
d x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.div`：HasDerivWithinAt.div (hc : HasDerivWithinAt c c' s
 x) (hd : HasDerivWithinAt d d' s x) (hx : d x != 0) : HasDerivWithinAt (c / d) 
((c' * d x…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin_zero_of_not_uniqueDiffWithinAt`：derivWithin_zero_of_not_uniq
ueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivWithin_fun_div
    (hc : DifferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x) (hx : d x ≠ 0) :
    derivWithin (fun x => c x / d x) s x =
      (derivWithin c s x * d x - c x * derivWithin d s x) / d x ^ 2 := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.div hd.hasDerivWithinAt hx).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]
/-
**derivWithin_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_div (hc : DifferentiableWithinAt 𝕜 c s x) (hd : Differentiable
WithinAt 𝕜 d s x) (hx : d x != 0) : derivWithin (c / d) s x = (derivWithin c s x
 * d x - c x * derivWithin d s x) / d x ^ 2
参数：hc : DifferentiableWithinAt 𝕜 c s x；hd : DifferentiableWithinAt 𝕜 d s x；hx : 
d x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `derivWithin_fun_div`：derivWithin_fun_div (hc : DifferentiableWithinAt 𝕜 
c s x) (hd : DifferentiableWithinAt 𝕜 d s x) (hx : d x != 0) : derivWithin (fun 
x => c x …
-/
theorem derivWithin_div (hc : DifferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x)
    (hx : d x ≠ 0) :
    derivWithin (c / d) s x = (derivWithin c s x * d x - c x * derivWithin d s x) / d x ^ 2 :=
  derivWithin_fun_div hc hd hx

@[simp]
/-
**deriv_fun_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_fun_div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) 
(hx : d x != 0) : deriv (fun x => c x / d x) x = (deriv c x * d x - c x * deriv 
d x) / d x ^ 2
参数：hc : DifferentiableAt 𝕜 c x；hd : DifferentiableAt 𝕜 d x；hx : d x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.div`：HasDerivAt.div (hc : HasDerivAt c c' x) (hd : HasDerivAt
 d d' x) (hx : d x != 0) : HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) 
x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_fun_div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) (hx : d x ≠ 0) :
    deriv (fun x => c x / d x) x = (deriv c x * d x - c x * deriv d x) / d x ^ 2 :=
  (hc.hasDerivAt.div hd.hasDerivAt hx).deriv

@[simp]
/-
**deriv_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) (hx 
: d x != 0) : deriv (c / d) x = (deriv c x * d x - c x * deriv d x) / d x ^ 2
参数：hc : DifferentiableAt 𝕜 c x；hd : DifferentiableAt 𝕜 d x；hx : d x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.div`：HasDerivAt.div (hc : HasDerivAt c c' x) (hd : HasDerivAt
 d d' x) (hx : d x != 0) : HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) 
x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) (hx : d x ≠ 0) :
    deriv (c / d) x = (deriv c x * d x - c x * deriv d x) / d x ^ 2 :=
  (hc.hasDerivAt.div hd.hasDerivAt hx).deriv
/-
**deriv_const_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_div (c : 𝕜') (hd : DifferentiableAt 𝕜 d x) (hx : d x != 0) : d
eriv (fun x => c / d x) x = - c * deriv d x / d x ^ 2
参数：c : 𝕜'；hd : DifferentiableAt 𝕜 d x；hx : d x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_fun_div`：deriv_fun_div (hc : DifferentiableAt 𝕜 c x) (hd : Differe
ntiableAt 𝕜 d x) (hx : d x != 0) : deriv (fun x => c x / d x) x = (deriv c x * d
 x …
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deriv_const_div (c : 𝕜') (hd : DifferentiableAt 𝕜 d x) (hx : d x ≠ 0) :
    deriv (fun x => c / d x) x = - c * deriv d x / d x ^ 2 := by
  simp [deriv_fun_div (differentiableAt_const c) hd hx]

@[simp]
/-
**deriv_const_div_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_div_id (c : 𝕜) : deriv (fun x => c / x) x = - c / x ^ 2
参数：c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const_mul_field'`：deriv_const_mul_field' (u : 𝕜') : (deriv fun x =
> u * v x) = fun x => u * deriv v x
· 使用定理 `deriv_inv'`：deriv_inv' : (deriv fun x : 𝕜 => x⁻¹) = fun x => -(x ^ 2)⁻¹
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deriv_const_div_id (c : 𝕜) :
    deriv (fun x => c / x) x = - c / x ^ 2 := by
  simp [div_eq_mul_inv]

end Division

