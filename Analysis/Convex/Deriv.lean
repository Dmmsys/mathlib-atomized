/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov, David Loeffler
-/
module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Convexity of functions and derivatives

Here we relate convexity of functions `ℝ → ℝ` to properties of their derivatives.

## Main results

* `MonotoneOn.convexOn_of_deriv`, `convexOn_of_deriv2_nonneg` : if the derivative of a function
  is increasing or its second derivative is nonnegative, then the original function is convex.
* `ConvexOn.monotoneOn_deriv`: if a function is convex and differentiable, then its derivative is
  monotone.
-/

public section

open Metric Set Asymptotics ContinuousLinearMap Filter
open scoped Topology NNReal

/-!
## Monotonicity of `f'` implies convexity of `f`
-/

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is monotone on the interior, then `f` is convex on `D`. -/
/-
**MonotoneOn.convexOn_of_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.convexOn_of_deriv {D : Set Real} (hD : Convex Real D) {f : Real
 -> Real} (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (interior D)) (
hf'_mono : MonotoneOn (deriv f) (interior D)) : ConvexOn Real D f
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : DifferentiableOn Real f (inter
ior D)；hf'_mono : MonotoneOn (deriv f) (interior D)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexOn_of_slope_mono_adjacent`：convexOn_of_slope_mono_adjacent (hs : C
onvex 𝕜 s) (hf : forall {x y z : 𝕜}, x in s -> z in s -> x < y -> y < z -> (f y 
- f x) / (y - x) <= (…
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Icc_subset_Icc_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ ≤ a₁ → Set.Icc b a₂ ⊆ Set.Icc b a₁
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `Set.Icc_subset_Icc_left`：Icc_subset_Icc_left (h : a₁ <= a₂) : Icc a₂ b s
ubseteq Icc a₁ b
· 使用定理 `exists_deriv_eq_slope`：exists_deriv_eq_slope : exists c in Ioo a b, deri
v f c = (f b - f a) / (b - a)
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c

--- 原说明 ---
If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on it
s interior,
and `f'` is monotone on the interior, then `f` is convex on `D`.
-/
theorem MonotoneOn.convexOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'_mono : MonotoneOn (deriv f) (interior D)) : ConvexOn ℝ D f :=
  convexOn_of_slope_mono_adjacent hD
    (by
      intro x y z hx hz hxy hyz
      -- First we prove some trivial inclusions
      have hxzD : Icc x z ⊆ D := hD.ordConnected.out hx hz
      have hxyD : Icc x y ⊆ D := (Icc_subset_Icc_right hyz.le).trans hxzD
      have hxyD' : Ioo x y ⊆ interior D :=
        subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
      have hyzD : Icc y z ⊆ D := (Icc_subset_Icc_left hxy.le).trans hxzD
      have hyzD' : Ioo y z ⊆ interior D :=
        subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hyzD⟩
      -- Then we apply MVT to both `[x, y]` and `[y, z]`
      obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
        exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD')
      obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : ∃ b ∈ Ioo y z, deriv f b = (f z - f y) / (z - y) :=
        exists_deriv_eq_slope f hyz (hf.mono hyzD) (hf'.mono hyzD')
      rw [← ha, ← hb]
      exact hf'_mono (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (hay.trans hyb).le)

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is antitone on the interior, then `f` is concave on `D`. -/
/-
**AntitoneOn.concaveOn_of_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.concaveOn_of_deriv {D : Set Real} (hD : Convex Real D) {f : Rea
l -> Real} (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (interior D)) 
(h_anti : AntitoneOn (deriv f) (interior D)) : ConcaveOn Real D f
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : DifferentiableOn Real f (inter
ior D)；h_anti : AntitoneOn (deriv f) (interior D)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_convexOn_iff`：neg_convexOn_iff : ConvexOn 𝕜 s (-f) ↔ ConcaveOn 𝕜 s f
· 使用定理 `MonotoneOn.convexOn_of_deriv`：MonotoneOn.convexOn_of_deriv {D : Set Real
} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differe
ntiableOn Real f (…
· 使用定理 `ContinuousOn.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X 
→ G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `DifferentiableOn.neg`：DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) 
: DifferentiableOn 𝕜 (-f) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AntitoneOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_
1 : Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β 
→ α}…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on it
s interior,
and `f'` is antitone on the interior, then `f` is concave on `D`.
-/
theorem AntitoneOn.concaveOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (h_anti : AntitoneOn (deriv f) (interior D)) : ConcaveOn ℝ D f :=
  haveI : MonotoneOn (deriv (-f)) (interior D) := by
    simpa only [← deriv.neg] using h_anti.neg
  neg_convexOn_iff.mp (this.convexOn_of_deriv hD hf.neg hf'.neg)
/-
**StrictMonoOn.exists_slope_lt_deriv_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.exists_slope_lt_deriv_aux {x y : Real} {f : Real -> Real} (hf
 : ContinuousOn f (Icc x y)) (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (I
oo x y)) (h : forall w in Ioo x y, deriv f w != 0) : exists a in Ioo x y, (f y -
 f x) / (y - x) < deriv f a
参数：hf : ContinuousOn f (Icc x y)；hxy : x < y；hf'_mono : StrictMonoOn (deriv f) (
Ioo x y)；h : forall w in Ioo x y, deriv f w != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_of_deriv_ne_zero`：differentiableAt_of_deriv_ne_zero (h 
: deriv f x != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `exists_deriv_eq_slope`：exists_deriv_eq_slope : exists c in Ioo a b, deri
v f c = (f b - f a) / (b - a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Ioo`：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔
 a < b
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
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem StrictMonoOn.exists_slope_lt_deriv_aux {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) (h : ∀ w ∈ Ioo x y, deriv f w ≠ 0) :
    ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a := by
  have A : DifferentiableOn ℝ f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hay with ⟨b, ⟨hab, hby⟩⟩
  refine ⟨b, ⟨hxa.trans hab, hby⟩, ?_⟩
  rw [← ha]
  exact hf'_mono ⟨hxa, hay⟩ ⟨hxa.trans hab, hby⟩ hab
/-
**StrictMonoOn.exists_slope_lt_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.exists_slope_lt_deriv {x y : Real} {f : Real -> Real} (hf : C
ontinuousOn f (Icc x y)) (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x
 y)) : exists a in Ioo x y, (f y - f x) / (y - x) < deriv f a
参数：hf : ContinuousOn f (Icc x y)；hxy : x < y；hf'_mono : StrictMonoOn (deriv f) (
Ioo x y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.exists_slope_lt_deriv_aux`：StrictMonoOn.exists_slope_lt_der
iv_aux {x y : Real} {f : Real -> Real} (hf : ContinuousOn f (Icc x y)) (hxy : x 
< y) (hf'_mono : StrictMonoO…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc
 a₁ b₁ subseteq Icc a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `StrictMonoOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α
 → β} [inst : Preorder α] [inst_1 : Preorder β],   StrictMonoOn f s → s₂ ⊆ s → S
trictMo…
· 使用定理 `Set.Ioo_subset_Ioo`：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo
 a₁ b₁ subseteq Ioo a₂ b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mul_lt_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α]   [MulPosStrictMono α], a < b → c ≤ d →
…
（共 73 条，此处仅展示前 30 条）
-/
theorem StrictMonoOn.exists_slope_lt_deriv {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) :
    ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a := by
  by_cases! h : ∀ w ∈ Ioo x y, deriv f w ≠ 0
  · apply StrictMonoOn.exists_slope_lt_deriv_aux hf hxy hf'_mono h
  · rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : ∃ a ∈ Ioo x w, (f w - f x) / (w - x) < deriv f a := by
      apply StrictMonoOn.exists_slope_lt_deriv_aux _ hxw _ _
      · exact hf.mono (Icc_subset_Icc le_rfl hwy.le)
      · exact hf'_mono.mono (Ioo_subset_Ioo le_rfl hwy.le)
      · intro z hz
        rw [← hw]
        apply ne_of_lt
        exact hf'_mono ⟨hz.1, hz.2.trans hwy⟩ ⟨hxw, hwy⟩ hz.2
    obtain ⟨b, ⟨hwb, hby⟩, hb⟩ : ∃ b ∈ Ioo w y, (f y - f w) / (y - w) < deriv f b := by
      apply StrictMonoOn.exists_slope_lt_deriv_aux _ hwy _ _
      · refine hf.mono (Icc_subset_Icc hxw.le le_rfl)
      · exact hf'_mono.mono (Ioo_subset_Ioo hxw.le le_rfl)
      · intro z hz
        rw [← hw]
        apply ne_of_gt
        exact hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hz.1, hz.2⟩ hz.1
    refine ⟨b, ⟨hxw.trans hwb, hby⟩, ?_⟩
    simp only [div_lt_iff₀, hxy, hxw, hwy, sub_pos] at ha hb ⊢
    have : deriv f a * (w - x) < deriv f b * (w - x) := by
      apply mul_lt_mul _ le_rfl (sub_pos.2 hxw) _
      · exact hf'_mono ⟨hxa, haw.trans hwy⟩ ⟨hxw.trans hwb, hby⟩ (haw.trans hwb)
      · rw [← hw]
        exact (hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hwb, hby⟩ hwb).le
    linarith
/-
**StrictMonoOn.exists_deriv_lt_slope_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.exists_deriv_lt_slope_aux {x y : Real} {f : Real -> Real} (hf
 : ContinuousOn f (Icc x y)) (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (I
oo x y)) (h : forall w in Ioo x y, deriv f w != 0) : exists a in Ioo x y, deriv 
f a < (f y - f x) / (y - x)
参数：hf : ContinuousOn f (Icc x y)；hxy : x < y；hf'_mono : StrictMonoOn (deriv f) (
Ioo x y)；h : forall w in Ioo x y, deriv f w != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_of_deriv_ne_zero`：differentiableAt_of_deriv_ne_zero (h 
: deriv f x != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `exists_deriv_eq_slope`：exists_deriv_eq_slope : exists c in Ioo a b, deri
v f c = (f b - f a) / (b - a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Ioo`：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔
 a < b
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
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem StrictMonoOn.exists_deriv_lt_slope_aux {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) (h : ∀ w ∈ Ioo x y, deriv f w ≠ 0) :
    ∃ a ∈ Ioo x y, deriv f a < (f y - f x) / (y - x) := by
  have A : DifferentiableOn ℝ f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hxa with ⟨b, ⟨hxb, hba⟩⟩
  refine ⟨b, ⟨hxb, hba.trans hay⟩, ?_⟩
  rw [← ha]
  exact hf'_mono ⟨hxb, hba.trans hay⟩ ⟨hxa, hay⟩ hba
/-
**StrictMonoOn.exists_deriv_lt_slope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.exists_deriv_lt_slope {x y : Real} {f : Real -> Real} (hf : C
ontinuousOn f (Icc x y)) (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x
 y)) : exists a in Ioo x y, deriv f a < (f y - f x) / (y - x)
参数：hf : ContinuousOn f (Icc x y)；hxy : x < y；hf'_mono : StrictMonoOn (deriv f) (
Ioo x y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.exists_deriv_lt_slope_aux`：StrictMonoOn.exists_deriv_lt_slo
pe_aux {x y : Real} {f : Real -> Real} (hf : ContinuousOn f (Icc x y)) (hxy : x 
< y) (hf'_mono : StrictMonoO…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc
 a₁ b₁ subseteq Icc a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `StrictMonoOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α
 → β} [inst : Preorder α] [inst_1 : Preorder β],   StrictMonoOn f s → s₂ ⊆ s → S
trictMo…
· 使用定理 `Set.Ioo_subset_Ioo`：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo
 a₁ b₁ subseteq Ioo a₂ b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mul_lt_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α]   [MulPosStrictMono α], a < b → c ≤ d →
…
（共 73 条，此处仅展示前 30 条）
-/
theorem StrictMonoOn.exists_deriv_lt_slope {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) :
    ∃ a ∈ Ioo x y, deriv f a < (f y - f x) / (y - x) := by
  by_cases! h : ∀ w ∈ Ioo x y, deriv f w ≠ 0
  · apply StrictMonoOn.exists_deriv_lt_slope_aux hf hxy hf'_mono h
  · rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : ∃ a ∈ Ioo x w, deriv f a < (f w - f x) / (w - x) := by
      apply StrictMonoOn.exists_deriv_lt_slope_aux _ hxw _ _
      · exact hf.mono (Icc_subset_Icc le_rfl hwy.le)
      · exact hf'_mono.mono (Ioo_subset_Ioo le_rfl hwy.le)
      · intro z hz
        rw [← hw]
        apply ne_of_lt
        exact hf'_mono ⟨hz.1, hz.2.trans hwy⟩ ⟨hxw, hwy⟩ hz.2
    obtain ⟨b, ⟨hwb, hby⟩, hb⟩ : ∃ b ∈ Ioo w y, deriv f b < (f y - f w) / (y - w) := by
      apply StrictMonoOn.exists_deriv_lt_slope_aux _ hwy _ _
      · refine hf.mono (Icc_subset_Icc hxw.le le_rfl)
      · exact hf'_mono.mono (Ioo_subset_Ioo hxw.le le_rfl)
      · intro z hz
        rw [← hw]
        apply ne_of_gt
        exact hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hz.1, hz.2⟩ hz.1
    refine ⟨a, ⟨hxa, haw.trans hwy⟩, ?_⟩
    simp only [lt_div_iff₀, hxy, hxw, hwy, sub_pos] at ha hb ⊢
    have : deriv f a * (y - w) < deriv f b * (y - w) := by
      apply mul_lt_mul _ le_rfl (sub_pos.2 hwy) _
      · exact hf'_mono ⟨hxa, haw.trans hwy⟩ ⟨hxw.trans hwb, hby⟩ (haw.trans hwb)
      · rw [← hw]
        exact (hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hwb, hby⟩ hwb).le
    linarith

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, and `f'` is strictly monotone on the
interior, then `f` is strictly convex on `D`.
Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict monotonicity of `f'`. -/
/-
**StrictMonoOn.strictConvexOn_of_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.strictConvexOn_of_deriv {D : Set Real} (hD : Convex Real D) {
f : Real -> Real} (hf : ContinuousOn f D) (hf' : StrictMonoOn (deriv f) (interio
r D)) : StrictConvexOn Real D f
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : StrictMonoOn (deriv f) (interi
or D)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictConvexOn_of_slope_strict_mono_adjacent`：strictConvexOn_of_slope_st
rict_mono_adjacent (hs : Convex 𝕜 s) (hf : forall {x y z : 𝕜}, x in s -> z in s 
-> x < y -> y < z -> (f y - f x) /…
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Icc_subset_Icc_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ ≤ a₁ → Set.Icc b a₂ ⊆ Set.Icc b a₁
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `Set.Icc_subset_Icc_left`：Icc_subset_Icc_left (h : a₁ <= a₂) : Icc a₂ b s
ubseteq Icc a₁ b
· 使用定理 `StrictMonoOn.exists_slope_lt_deriv`：StrictMonoOn.exists_slope_lt_deriv {
x y : Real} {f : Real -> Real} (hf : ContinuousOn f (Icc x y)) (hxy : x < y) (hf
'_mono : StrictMonoOn (d…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `StrictMonoOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α
 → β} [inst : Preorder α] [inst_1 : Preorder β],   StrictMonoOn f s → s₂ ⊆ s → S
trictMo…
· 使用定理 `StrictMonoOn.exists_deriv_lt_slope`：StrictMonoOn.exists_deriv_lt_slope {
x y : Real} {f : Real -> Real} (hf : ContinuousOn f (Icc x y)) (hxy : x < y) (hf
'_mono : StrictMonoOn (d…
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c

--- 原说明 ---
If a function `f` is continuous on a convex set `D ⊆ ℝ`, and `f'` is strictly mo
notone on the
interior, then `f` is strictly convex on `D`.
Note that we don't require differentiability, since it is guaranteed at all but 
at most
one point by the strict monotonicity of `f'`.
-/
theorem StrictMonoOn.strictConvexOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : StrictMonoOn (deriv f) (interior D)) : StrictConvexOn ℝ D f :=
  strictConvexOn_of_slope_strict_mono_adjacent hD fun {x y z} hx hz hxy hyz => by
    -- First we prove some trivial inclusions
    have hxzD : Icc x z ⊆ D := hD.ordConnected.out hx hz
    have hxyD : Icc x y ⊆ D := (Icc_subset_Icc_right hyz.le).trans hxzD
    have hxyD' : Ioo x y ⊆ interior D :=
      subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
    have hyzD : Icc y z ⊆ D := (Icc_subset_Icc_left hxy.le).trans hxzD
    have hyzD' : Ioo y z ⊆ interior D :=
      subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hyzD⟩
    -- Then we get points `a` and `b` in each interval `[x, y]` and `[y, z]` where the derivatives
    -- can be compared to the slopes between `x, y` and `y, z` respectively.
    obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a :=
      StrictMonoOn.exists_slope_lt_deriv (hf.mono hxyD) hxy (hf'.mono hxyD')
    obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : ∃ b ∈ Ioo y z, deriv f b < (f z - f y) / (z - y) :=
      StrictMonoOn.exists_deriv_lt_slope (hf.mono hyzD) hyz (hf'.mono hyzD')
    apply ha.trans (lt_trans _ hb)
    exact hf' (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (hay.trans hyb)

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f'` is strictly antitone on the
interior, then `f` is strictly concave on `D`.
Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict antitonicity of `f'`. -/
/-
**StrictAntiOn.strictConcaveOn_of_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAntiOn.strictConcaveOn_of_deriv {D : Set Real} (hD : Convex Real D) 
{f : Real -> Real} (hf : ContinuousOn f D) (h_anti : StrictAntiOn (deriv f) (int
erior D)) : StrictConcaveOn Real D f
参数：hD : Convex Real D；hf : ContinuousOn f D；h_anti : StrictAntiOn (deriv f) (int
erior D)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `StrictAntiOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [ins
t_1 : Preorder α] [AddLeftStrictMono α] [AddRightStrictMono α]   [inst_4 : Preor
der β]…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `StrictConvexOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst
 : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : 
AddCommG…
· 使用定理 `StrictMonoOn.strictConvexOn_of_deriv`：StrictMonoOn.strictConvexOn_of_der
iv {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D
) (hf' : StrictMonoOn (der…
· 使用定理 `ContinuousOn.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X 
→ G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a

--- 原说明 ---
If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f'` is strictly ant
itone on the
interior, then `f` is strictly concave on `D`.
Note that we don't require differentiability, since it is guaranteed at all but 
at most
one point by the strict antitonicity of `f'`.
-/
theorem StrictAntiOn.strictConcaveOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (h_anti : StrictAntiOn (deriv f) (interior D)) :
    StrictConcaveOn ℝ D f :=
  have : StrictMonoOn (deriv (-f)) (interior D) := by simpa only [← deriv.neg] using h_anti.neg
  neg_neg f ▸ (this.strictConvexOn_of_deriv hD hf.neg).neg

/-- If a function `f` is differentiable and `f'` is monotone on `ℝ` then `f` is convex. -/
/-
**Monotone.convexOn_univ_of_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.convexOn_univ_of_deriv {f : Real -> Real} (hf : Differentiable Re
al f) (hf'_mono : Monotone (deriv f)) : ConvexOn Real univ f
参数：hf : Differentiable Real f；hf'_mono : Monotone (deriv f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.convexOn_of_deriv`：MonotoneOn.convexOn_of_deriv {D : Set Real
} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differe
ntiableOn Real f (…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
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
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s

--- 原说明 ---
If a function `f` is differentiable and `f'` is monotone on `ℝ` then `f` is conv
ex.
-/
theorem Monotone.convexOn_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf'_mono : Monotone (deriv f)) : ConvexOn ℝ univ f :=
  (hf'_mono.monotoneOn _).convexOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn

/-- If a function `f` is differentiable and `f'` is antitone on `ℝ` then `f` is concave. -/
/-
**Antitone.concaveOn_univ_of_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.concaveOn_univ_of_deriv {f : Real -> Real} (hf : Differentiable R
eal f) (hf'_anti : Antitone (deriv f)) : ConcaveOn Real univ f
参数：hf : Differentiable Real f；hf'_anti : Antitone (deriv f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.concaveOn_of_deriv`：AntitoneOn.concaveOn_of_deriv {D : Set Re
al} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Diffe
rentiableOn Real f …
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
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
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s

--- 原说明 ---
If a function `f` is differentiable and `f'` is antitone on `ℝ` then `f` is conc
ave.
-/
theorem Antitone.concaveOn_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf'_anti : Antitone (deriv f)) : ConcaveOn ℝ univ f :=
  (hf'_anti.antitoneOn _).concaveOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn

/-- If a function `f` is continuous and `f'` is strictly monotone on `ℝ` then `f` is strictly
convex. Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict monotonicity of `f'`. -/
/-
**StrictMono.strictConvexOn_univ_of_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.strictConvexOn_univ_of_deriv {f : Real -> Real} (hf : Continuou
s f) (hf'_mono : StrictMono (deriv f)) : StrictConvexOn Real univ f
参数：hf : Continuous f；hf'_mono : StrictMono (deriv f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.strictConvexOn_of_deriv`：StrictMonoOn.strictConvexOn_of_der
iv {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D
) (hf' : StrictMonoOn (der…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s

--- 原说明 ---
If a function `f` is continuous and `f'` is strictly monotone on `ℝ` then `f` is
 strictly
convex. Note that we don't require differentiability, since it is guaranteed at 
all but at most
one point by the strict monotonicity of `f'`.
-/
theorem StrictMono.strictConvexOn_univ_of_deriv {f : ℝ → ℝ} (hf : Continuous f)
    (hf'_mono : StrictMono (deriv f)) : StrictConvexOn ℝ univ f :=
  (hf'_mono.strictMonoOn _).strictConvexOn_of_deriv convex_univ hf.continuousOn

/-- If a function `f` is continuous and `f'` is strictly antitone on `ℝ` then `f` is strictly
concave. Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict antitonicity of `f'`. -/
/-
**StrictAnti.strictConcaveOn_univ_of_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.strictConcaveOn_univ_of_deriv {f : Real -> Real} (hf : Continuo
us f) (hf'_anti : StrictAnti (deriv f)) : StrictConcaveOn Real univ f
参数：hf : Continuous f；hf'_anti : StrictAnti (deriv f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAntiOn.strictConcaveOn_of_deriv`：StrictAntiOn.strictConcaveOn_of_d
eriv {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f
 D) (h_anti : StrictAntiOn …
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `StrictAnti.strictAntiOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn
 f s

--- 原说明 ---
If a function `f` is continuous and `f'` is strictly antitone on `ℝ` then `f` is
 strictly
concave. Note that we don't require differentiability, since it is guaranteed at
 all but at most
one point by the strict antitonicity of `f'`.
-/
theorem StrictAnti.strictConcaveOn_univ_of_deriv {f : ℝ → ℝ} (hf : Continuous f)
    (hf'_anti : StrictAnti (deriv f)) : StrictConcaveOn ℝ univ f :=
  (hf'_anti.strictAntiOn _).strictConcaveOn_of_deriv convex_univ hf.continuousOn

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonnegative on the interior, then `f` is convex on `D`. -/
/-
**convexOn_of_deriv2_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexOn_of_deriv2_nonneg {D : Set Real} (hD : Convex Real D) {f : Real ->
 Real} (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (interior D)) (hf'
' : DifferentiableOn Real (deriv f) (interior D)) (hf''_nonneg : forall x in int
erior D, 0 <= deriv^[2] f x) : ConvexOn Real D f
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : DifferentiableOn Real f (inter
ior D)；hf'' : DifferentiableOn Real (deriv f) (interior D)；hf''_nonneg : forall 
x in interior D, 0 <= deriv^[2] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.convexOn_of_deriv`：MonotoneOn.convexOn_of_deriv {D : Set Real
} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differe
ntiableOn Real f (…
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `Convex.interior`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_
1 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [in
st_4 …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_interior`：interior_interior : interior (interior s) = interior 
s

--- 原说明 ---
If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable
 on its
interior, and `f''` is nonnegative on the interior, then `f` is convex on `D`.
-/
theorem convexOn_of_deriv2_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (interior D))
    (hf''_nonneg : ∀ x ∈ interior D, 0 ≤ deriv^[2] f x) : ConvexOn ℝ D f :=
  (monotoneOn_of_deriv_nonneg hD.interior hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).convexOn_of_deriv
    hD hf hf'

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonpositive on the interior, then `f` is concave on `D`. -/
/-
**concaveOn_of_deriv2_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：concaveOn_of_deriv2_nonpos {D : Set Real} (hD : Convex Real D) {f : Real -
> Real} (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (interior D)) (hf
'' : DifferentiableOn Real (deriv f) (interior D)) (hf''_nonpos : forall x in in
terior D, deriv^[2] f x <= 0) : ConcaveOn Real D f
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : DifferentiableOn Real f (inter
ior D)；hf'' : DifferentiableOn Real (deriv f) (interior D)；hf''_nonpos : forall 
x in interior D, deriv^[2] f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.concaveOn_of_deriv`：AntitoneOn.concaveOn_of_deriv {D : Set Re
al} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Diffe
rentiableOn Real f …
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `Convex.interior`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_
1 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [in
st_4 …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_interior`：interior_interior : interior (interior s) = interior 
s

--- 原说明 ---
If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable
 on its
interior, and `f''` is nonpositive on the interior, then `f` is concave on `D`.
-/
theorem concaveOn_of_deriv2_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (interior D))
    (hf''_nonpos : ∀ x ∈ interior D, deriv^[2] f x ≤ 0) : ConcaveOn ℝ D f :=
  (antitoneOn_of_deriv_nonpos hD.interior hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).concaveOn_of_deriv
    hD hf hf'

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonnegative on the interior, then `f` is convex on `D`. -/
/-
**convexOn_of_hasDerivWithinAt2_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：convexOn_of_hasDerivWithinAt2_nonneg {D : Set Real} (hD : Convex Real D) {
f f' f'' : Real -> Real} (hf : ContinuousOn f D) (hf' : forall x in interior D, 
HasDerivWithinAt f (f' x) (interior D) x) (hf'' : forall x in interior D, HasDer
ivWithinAt f' (f'' x) (interior D) x) (hf''₀ : forall x in interior D, 0 <= f'' 
x) : ConvexOn Real D f
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : forall x in interior D, HasDer
ivWithinAt f (f' x) (interior D) x；hf'' : forall x in interior D, HasDerivWithin
At f' (f'' x) (interior D) x；hf''₀ : forall x in interior D, 0 <= f'' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `deriv_eqOn`：deriv_eqOn {f' : 𝕜 -> F} (hs : IsOpen s) (hf' : forall x in 
s, HasDerivWithinAt f (f' x) s x) : s.EqOn (deriv f) f'
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `convexOn_of_deriv2_nonneg`：convexOn_of_deriv2_nonneg {D : Set Real} (hD 
: Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentiabl
eOn Real f (int…
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `differentiableOn_congr`：differentiableOn_congr (h' : forall x in s, f₁ x
 = f x) : DifferentiableOn 𝕜 f₁ s ↔ DifferentiableOn 𝕜 f s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasDerivWithinAt.congr`：HasDerivWithinAt.congr (h : HasDerivWithinAt f f
' s x) (hs : forall x in s, f₁ x = f x) (hx : f₁ x = f x) : HasDerivWithinAt f₁ 
f' s x

--- 原说明 ---
If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable
 on its
interior, and `f''` is nonnegative on the interior, then `f` is convex on `D`.
-/
lemma convexOn_of_hasDerivWithinAt2_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f f' f'' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'' : ∀ x ∈ interior D, HasDerivWithinAt f' (f'' x) (interior D) x)
    (hf''₀ : ∀ x ∈ interior D, 0 ≤ f'' x) : ConvexOn ℝ D f := by
  have : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine convexOn_of_deriv2_nonneg hD hf (fun x hx ↦ (hf' _ hx).differentiableWithinAt) ?_ ?_
  · rw [differentiableOn_congr this]
    exact fun x hx ↦ (hf'' _ hx).differentiableWithinAt
  · rintro x hx
    convert hf''₀ _ hx
    dsimp
    rw [deriv_eqOn isOpen_interior (fun y hy ↦ ?_) hx]
    exact (hf'' _ hy).congr this <| by rw [this hy]

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonpositive on the interior, then `f` is concave on `D`. -/
/-
**concaveOn_of_hasDerivWithinAt2_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：concaveOn_of_hasDerivWithinAt2_nonpos {D : Set Real} (hD : Convex Real D) 
{f f' f'' : Real -> Real} (hf : ContinuousOn f D) (hf' : forall x in interior D,
 HasDerivWithinAt f (f' x) (interior D) x) (hf'' : forall x in interior D, HasDe
rivWithinAt f' (f'' x) (interior D) x) (hf''₀ : forall x in interior D, f'' x <=
 0) : ConcaveOn Real D f
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : forall x in interior D, HasDer
ivWithinAt f (f' x) (interior D) x；hf'' : forall x in interior D, HasDerivWithin
At f' (f'' x) (interior D) x；hf''₀ : forall x in interior D, f'' x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `deriv_eqOn`：deriv_eqOn {f' : 𝕜 -> F} (hs : IsOpen s) (hf' : forall x in 
s, HasDerivWithinAt f (f' x) s x) : s.EqOn (deriv f) f'
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `concaveOn_of_deriv2_nonpos`：concaveOn_of_deriv2_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `differentiableOn_congr`：differentiableOn_congr (h' : forall x in s, f₁ x
 = f x) : DifferentiableOn 𝕜 f₁ s ↔ DifferentiableOn 𝕜 f s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasDerivWithinAt.congr`：HasDerivWithinAt.congr (h : HasDerivWithinAt f f
' s x) (hs : forall x in s, f₁ x = f x) (hx : f₁ x = f x) : HasDerivWithinAt f₁ 
f' s x

--- 原说明 ---
If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable
 on its
interior, and `f''` is nonpositive on the interior, then `f` is concave on `D`.
-/
lemma concaveOn_of_hasDerivWithinAt2_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f f' f'' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'' : ∀ x ∈ interior D, HasDerivWithinAt f' (f'' x) (interior D) x)
    (hf''₀ : ∀ x ∈ interior D, f'' x ≤ 0) : ConcaveOn ℝ D f := by
  have : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine concaveOn_of_deriv2_nonpos hD hf (fun x hx ↦ (hf' _ hx).differentiableWithinAt) ?_ ?_
  · rw [differentiableOn_congr this]
    exact fun x hx ↦ (hf'' _ hx).differentiableWithinAt
  · rintro x hx
    convert hf''₀ _ hx
    dsimp
    rw [deriv_eqOn isOpen_interior (fun y hy ↦ ?_) hx]
    exact (hf'' _ hy).congr this <| by rw [this hy]

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly positive on the
interior, then `f` is strictly convex on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point. -/
/-
**strictConvexOn_of_deriv2_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvexOn_of_deriv2_pos {D : Set Real} (hD : Convex Real D) {f : Real
 -> Real} (hf : ContinuousOn f D) (hf'' : forall x in interior D, 0 < (deriv^[2]
 f) x) : StrictConvexOn Real D f
参数：hD : Convex Real D；hf : ContinuousOn f D；hf'' : forall x in interior D, 0 < (
deriv^[2] f) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.strictConvexOn_of_deriv`：StrictMonoOn.strictConvexOn_of_der
iv {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D
) (hf' : StrictMonoOn (der…
· 使用定理 `strictMonoOn_of_deriv_pos`：strictMonoOn_of_deriv_pos {D : Set Real} (hD 
: Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : forall x in i
nterior D, 0 < …
· 使用定理 `Convex.interior`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_
1 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [in
st_4 …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `DifferentiableWithinAt.continuousWithinAt`：DifferentiableWithinAt.contin
uousWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : ContinuousWithinAt f s x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_of_deriv_ne_zero`：differentiableAt_of_deriv_ne_zero (h 
: deriv f x != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_interior`：interior_interior : interior (interior s) = interior 
s

--- 原说明 ---
If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly po
sitive on the
interior, then `f` is strictly convex on `D`.
Note that we don't require twice differentiability explicitly as it is already i
mplied by the second
derivative being strictly positive, except at at most one point.
-/
theorem strictConvexOn_of_deriv2_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ interior D, 0 < (deriv^[2] f) x) :
    StrictConvexOn ℝ D f :=
  ((strictMonoOn_of_deriv_pos hD.interior fun z hz =>
          (differentiableAt_of_deriv_ne_zero
                (hf'' z hz).ne').differentiableWithinAt.continuousWithinAt) <|
        by rwa [interior_interior]).strictConvexOn_of_deriv
    hD hf

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly negative on the
interior, then `f` is strictly concave on `D`.
Note that we don't require twice differentiability explicitly as it already implied by the second
derivative being strictly negative, except at at most one point. -/
/-
**strictConcaveOn_of_deriv2_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConcaveOn_of_deriv2_neg {D : Set Real} (hD : Convex Real D) {f : Rea
l -> Real} (hf : ContinuousOn f D) (hf'' : forall x in interior D, deriv^[2] f x
 < 0) : StrictConcaveOn Real D f
参数：hD : Convex Real D；hf : ContinuousOn f D；hf'' : forall x in interior D, deriv
^[2] f x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAntiOn.strictConcaveOn_of_deriv`：StrictAntiOn.strictConcaveOn_of_d
eriv {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f
 D) (h_anti : StrictAntiOn …
· 使用定理 `strictAntiOn_of_deriv_neg`：strictAntiOn_of_deriv_neg {D : Set Real} (hD 
: Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : forall x in i
nterior D, deri…
· 使用定理 `Convex.interior`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_
1 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [in
st_4 …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `DifferentiableWithinAt.continuousWithinAt`：DifferentiableWithinAt.contin
uousWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : ContinuousWithinAt f s x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_of_deriv_ne_zero`：differentiableAt_of_deriv_ne_zero (h 
: deriv f x != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_interior`：interior_interior : interior (interior s) = interior 
s

--- 原说明 ---
If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly ne
gative on the
interior, then `f` is strictly concave on `D`.
Note that we don't require twice differentiability explicitly as it already impl
ied by the second
derivative being strictly negative, except at at most one point.
-/
theorem strictConcaveOn_of_deriv2_neg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ interior D, deriv^[2] f x < 0) :
    StrictConcaveOn ℝ D f :=
  ((strictAntiOn_of_deriv_neg hD.interior fun z hz =>
          (differentiableAt_of_deriv_ne_zero
                (hf'' z hz).ne).differentiableWithinAt.continuousWithinAt) <|
        by rwa [interior_interior]).strictConcaveOn_of_deriv
    hD hf

/-- If a function `f` is twice differentiable on an open convex set `D ⊆ ℝ` and
`f''` is nonnegative on `D`, then `f` is convex on `D`. -/
/-
**convexOn_of_deriv2_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexOn_of_deriv2_nonneg' {D : Set Real} (hD : Convex Real D) {f : Real -
> Real} (hf' : DifferentiableOn Real f D) (hf'' : DifferentiableOn Real (deriv f
) D) (hf''_nonneg : forall x in D, 0 <= (deriv^[2] f) x) : ConvexOn Real D f
参数：hD : Convex Real D；hf' : DifferentiableOn Real f D；hf'' : DifferentiableOn Re
al (deriv f) D；hf''_nonneg : forall x in D, 0 <= (deriv^[2] f) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexOn_of_deriv2_nonneg`：convexOn_of_deriv2_nonneg {D : Set Real} (hD 
: Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentiabl
eOn Real f (int…
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
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
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s

--- 原说明 ---
If a function `f` is twice differentiable on an open convex set `D ⊆ ℝ` and
`f''` is nonnegative on `D`, then `f` is convex on `D`.
-/
theorem convexOn_of_deriv2_nonneg' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf' : DifferentiableOn ℝ f D) (hf'' : DifferentiableOn ℝ (deriv f) D)
    (hf''_nonneg : ∀ x ∈ D, 0 ≤ (deriv^[2] f) x) : ConvexOn ℝ D f :=
  convexOn_of_deriv2_nonneg hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonneg x (interior_subset hx)

/-- If a function `f` is twice differentiable on an open convex set `D ⊆ ℝ` and
`f''` is nonpositive on `D`, then `f` is concave on `D`. -/
/-
**concaveOn_of_deriv2_nonpos'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：concaveOn_of_deriv2_nonpos' {D : Set Real} (hD : Convex Real D) {f : Real 
-> Real} (hf' : DifferentiableOn Real f D) (hf'' : DifferentiableOn Real (deriv 
f) D) (hf''_nonpos : forall x in D, deriv^[2] f x <= 0) : ConcaveOn Real D f
参数：hD : Convex Real D；hf' : DifferentiableOn Real f D；hf'' : DifferentiableOn Re
al (deriv f) D；hf''_nonpos : forall x in D, deriv^[2] f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `concaveOn_of_deriv2_nonpos`：concaveOn_of_deriv2_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
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
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s

--- 原说明 ---
If a function `f` is twice differentiable on an open convex set `D ⊆ ℝ` and
`f''` is nonpositive on `D`, then `f` is concave on `D`.
-/
theorem concaveOn_of_deriv2_nonpos' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf' : DifferentiableOn ℝ f D) (hf'' : DifferentiableOn ℝ (deriv f) D)
    (hf''_nonpos : ∀ x ∈ D, deriv^[2] f x ≤ 0) : ConcaveOn ℝ D f :=
  concaveOn_of_deriv2_nonpos hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonpos x (interior_subset hx)

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly positive on `D`,
then `f` is strictly convex on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point. -/
/-
**strictConvexOn_of_deriv2_pos'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvexOn_of_deriv2_pos' {D : Set Real} (hD : Convex Real D) {f : Rea
l -> Real} (hf : ContinuousOn f D) (hf'' : forall x in D, 0 < (deriv^[2] f) x) :
 StrictConvexOn Real D f
参数：hD : Convex Real D；hf : ContinuousOn f D；hf'' : forall x in D, 0 < (deriv^[2]
 f) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictConvexOn_of_deriv2_pos`：strictConvexOn_of_deriv2_pos {D : Set Real
} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf'' : forall
 x in interior D, …
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s

--- 原说明 ---
If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly po
sitive on `D`,
then `f` is strictly convex on `D`.
Note that we don't require twice differentiability explicitly as it is already i
mplied by the second
derivative being strictly positive, except at at most one point.
-/
theorem strictConvexOn_of_deriv2_pos' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ D, 0 < (deriv^[2] f) x) : StrictConvexOn ℝ D f :=
  strictConvexOn_of_deriv2_pos hD hf fun x hx => hf'' x (interior_subset hx)

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly negative on `D`,
then `f` is strictly concave on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly negative, except at at most one point. -/
/-
**strictConcaveOn_of_deriv2_neg'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConcaveOn_of_deriv2_neg' {D : Set Real} (hD : Convex Real D) {f : Re
al -> Real} (hf : ContinuousOn f D) (hf'' : forall x in D, deriv^[2] f x < 0) : 
StrictConcaveOn Real D f
参数：hD : Convex Real D；hf : ContinuousOn f D；hf'' : forall x in D, deriv^[2] f x 
< 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictConcaveOn_of_deriv2_neg`：strictConcaveOn_of_deriv2_neg {D : Set Re
al} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf'' : fora
ll x in interior D,…
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s

--- 原说明 ---
If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly ne
gative on `D`,
then `f` is strictly concave on `D`.
Note that we don't require twice differentiability explicitly as it is already i
mplied by the second
derivative being strictly negative, except at at most one point.
-/
theorem strictConcaveOn_of_deriv2_neg' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ D, deriv^[2] f x < 0) : StrictConcaveOn ℝ D f :=
  strictConcaveOn_of_deriv2_neg hD hf fun x hx => hf'' x (interior_subset hx)

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonnegative on `ℝ`,
then `f` is convex on `ℝ`. -/
/-
**convexOn_univ_of_deriv2_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexOn_univ_of_deriv2_nonneg {f : Real -> Real} (hf' : Differentiable Re
al f) (hf'' : Differentiable Real (deriv f)) (hf''_nonneg : forall x, 0 <= (deri
v^[2] f) x) : ConvexOn Real univ f
参数：hf' : Differentiable Real f；hf'' : Differentiable Real (deriv f)；hf''_nonneg 
: forall x, 0 <= (deriv^[2] f) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexOn_of_deriv2_nonneg'`：convexOn_of_deriv2_nonneg' {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf' : DifferentiableOn Real f D) (hf'' : 
DifferentiableOn…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s

--- 原说明 ---
If a function `f` is twice differentiable on `ℝ`, and `f''` is nonnegative on `ℝ
`,
then `f` is convex on `ℝ`.
-/
theorem convexOn_univ_of_deriv2_nonneg {f : ℝ → ℝ} (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f)) (hf''_nonneg : ∀ x, 0 ≤ (deriv^[2] f) x) :
    ConvexOn ℝ univ f :=
  convexOn_of_deriv2_nonneg' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonneg x

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonpositive on `ℝ`,
then `f` is concave on `ℝ`. -/
/-
**concaveOn_univ_of_deriv2_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：concaveOn_univ_of_deriv2_nonpos {f : Real -> Real} (hf' : Differentiable R
eal f) (hf'' : Differentiable Real (deriv f)) (hf''_nonpos : forall x, deriv^[2]
 f x <= 0) : ConcaveOn Real univ f
参数：hf' : Differentiable Real f；hf'' : Differentiable Real (deriv f)；hf''_nonpos 
: forall x, deriv^[2] f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `concaveOn_of_deriv2_nonpos'`：concaveOn_of_deriv2_nonpos' {D : Set Real} 
(hD : Convex Real D) {f : Real -> Real} (hf' : DifferentiableOn Real f D) (hf'' 
: DifferentiableO…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s

--- 原说明 ---
If a function `f` is twice differentiable on `ℝ`, and `f''` is nonpositive on `ℝ
`,
then `f` is concave on `ℝ`.
-/
theorem concaveOn_univ_of_deriv2_nonpos {f : ℝ → ℝ} (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f)) (hf''_nonpos : ∀ x, deriv^[2] f x ≤ 0) :
    ConcaveOn ℝ univ f :=
  concaveOn_of_deriv2_nonpos' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonpos x

/-- If a function `f` is continuous on `ℝ`, and `f''` is strictly positive on `ℝ`,
then `f` is strictly convex on `ℝ`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point. -/
/-
**strictConvexOn_univ_of_deriv2_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvexOn_univ_of_deriv2_pos {f : Real -> Real} (hf : Continuous f) (
hf'' : forall x, 0 < (deriv^[2] f) x) : StrictConvexOn Real univ f
参数：hf : Continuous f；hf'' : forall x, 0 < (deriv^[2] f) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictConvexOn_of_deriv2_pos'`：strictConvexOn_of_deriv2_pos' {D : Set Re
al} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf'' : fora
ll x in D, 0 < (der…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s

--- 原说明 ---
If a function `f` is continuous on `ℝ`, and `f''` is strictly positive on `ℝ`,
then `f` is strictly convex on `ℝ`.
Note that we don't require twice differentiability explicitly as it is already i
mplied by the second
derivative being strictly positive, except at at most one point.
-/
theorem strictConvexOn_univ_of_deriv2_pos {f : ℝ → ℝ} (hf : Continuous f)
    (hf'' : ∀ x, 0 < (deriv^[2] f) x) : StrictConvexOn ℝ univ f :=
  strictConvexOn_of_deriv2_pos' convex_univ hf.continuousOn fun x _ => hf'' x

/-- If a function `f` is continuous on `ℝ`, and `f''` is strictly negative on `ℝ`,
then `f` is strictly concave on `ℝ`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly negative, except at at most one point. -/
/-
**strictConcaveOn_univ_of_deriv2_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConcaveOn_univ_of_deriv2_neg {f : Real -> Real} (hf : Continuous f) 
(hf'' : forall x, deriv^[2] f x < 0) : StrictConcaveOn Real univ f
参数：hf : Continuous f；hf'' : forall x, deriv^[2] f x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictConcaveOn_of_deriv2_neg'`：strictConcaveOn_of_deriv2_neg' {D : Set 
Real} (hD : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf'' : fo
rall x in D, deriv^[…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s

--- 原说明 ---
If a function `f` is continuous on `ℝ`, and `f''` is strictly negative on `ℝ`,
then `f` is strictly concave on `ℝ`.
Note that we don't require twice differentiability explicitly as it is already i
mplied by the second
derivative being strictly negative, except at at most one point.
-/
theorem strictConcaveOn_univ_of_deriv2_neg {f : ℝ → ℝ} (hf : Continuous f)
    (hf'' : ∀ x, deriv^[2] f x < 0) : StrictConcaveOn ℝ univ f :=
  strictConcaveOn_of_deriv2_neg' convex_univ hf.continuousOn fun x _ => hf'' x

/-!
## Convexity of `f` implies monotonicity of `f'`

In this section we prove inequalities relating derivatives of convex functions to slopes of secant
lines, and deduce that if `f` is convex then its derivative is monotone (and similarly for strict
convexity / strict monotonicity).
-/

section slope

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {s : Set 𝕜} {f : 𝕜 → 𝕜} {x : 𝕜}

/-- If `f : 𝕜 → 𝕜` is convex on `s`, then for any point `x ∈ s` the slope of the secant line of `f`
through `x` is monotone on `s \ {x}`. -/
/-
**ConvexOn.slope_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.slope_mono (hfc : ConvexOn 𝕜 s f) (hx : x in s) : MonotoneOn (slo
pe f x) (s \ {x})
参数：hfc : ConvexOn 𝕜 s f；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.secant_mono`：ConvexOn.secant_mono (hf : ConvexOn 𝕜 s f) {a x y 
: 𝕜} (ha : a in s) (hx : x in s) (hy : y in s) (hxa : x != a) (hya : y != a) (hx
y : x <= y…
· 使用定理 `Set.mem_of_mem_sdiff`：mem_of_mem_sdiff {s t : Set α} {x : α} (h : x in s
 \ t) : x in s
· 使用定理 `Set.notMem_of_mem_sdiff`：notMem_of_mem_sdiff {s t : Set α} {x : α} (h : 
x in s \ t) : x ∉ t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `slope_fun_def_field`：slope_fun_def_field (f : k -> k) (a : k) : slope f 
a = fun b => (f b - f a) / (b - a)

--- 原说明 ---
If `f : 𝕜 → 𝕜` is convex on `s`, then for any point `x ∈ s` the slope of the sec
ant line of `f`
through `x` is monotone on `s \ {x}`.
-/
lemma ConvexOn.slope_mono (hfc : ConvexOn 𝕜 s f) (hx : x ∈ s) : MonotoneOn (slope f x) (s \ {x}) :=
  (slope_fun_def_field f _).symm ▸ fun _ hy _ hz hz' ↦ hfc.secant_mono hx (mem_of_mem_sdiff hy)
    (mem_of_mem_sdiff hz) (notMem_of_mem_sdiff hy :) (notMem_of_mem_sdiff hz :) hz'
/-
**ConvexOn.monotoneOn_slope_gt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.monotoneOn_slope_gt (hfc : ConvexOn 𝕜 s f) (hxs : x in s) : Monot
oneOn (slope f x) {y in s | x < y}
参数：hfc : ConvexOn 𝕜 s f；hxs : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   MonotoneOn f s → s₂ ⊆ s → Monot
oneOn…
· 使用引理 `ConvexOn.slope_mono`：ConvexOn.slope_mono (hfc : ConvexOn 𝕜 s f) (hx : x 
in s) : MonotoneOn (slope f x) (s \ {x})
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma ConvexOn.monotoneOn_slope_gt (hfc : ConvexOn 𝕜 s f) (hxs : x ∈ s) :
    MonotoneOn (slope f x) {y ∈ s | x < y} :=
  (hfc.slope_mono hxs).mono fun _ ⟨h1, h2⟩ ↦ ⟨h1, h2.ne'⟩
/-
**ConvexOn.monotoneOn_slope_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.monotoneOn_slope_lt (hfc : ConvexOn 𝕜 s f) (hxs : x in s) : Monot
oneOn (slope f x) {y in s | y < x}
参数：hfc : ConvexOn 𝕜 s f；hxs : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   MonotoneOn f s → s₂ ⊆ s → Monot
oneOn…
· 使用引理 `ConvexOn.slope_mono`：ConvexOn.slope_mono (hfc : ConvexOn 𝕜 s f) (hx : x 
in s) : MonotoneOn (slope f x) (s \ {x})
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
lemma ConvexOn.monotoneOn_slope_lt (hfc : ConvexOn 𝕜 s f) (hxs : x ∈ s) :
    MonotoneOn (slope f x) {y ∈ s | y < x} :=
  (hfc.slope_mono hxs).mono fun _ ⟨h1, h2⟩ ↦ ⟨h1, h2.ne⟩

/-- If `f : 𝕜 → 𝕜` is concave on `s`, then for any point `x ∈ s` the slope of the secant line of `f`
through `x` is antitone on `s \ {x}`. -/
/-
**ConcaveOn.slope_anti** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.slope_anti (hfc : ConcaveOn 𝕜 s f) (hx : x in s) : AntitoneOn (s
lope f x) (s \ {x})
参数：hfc : ConcaveOn 𝕜 s f；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `slope_neg_fun`：∀ {k : Type u_1} {E : Type u_2} [inst : Field k] [inst_1 
: AddCommGroup E] [inst_2 : _root_.Module k E] (f : k → E),   slope (-f) = -slop
e f
· 使用定理 `MonotoneOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_
1 : Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β 
→ α}…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `ConvexOn.slope_mono`：ConvexOn.slope_mono (hfc : ConvexOn 𝕜 s f) (hx : x 
in s) : MonotoneOn (slope f x) (s \ {x})
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…

--- 原说明 ---
If `f : 𝕜 → 𝕜` is concave on `s`, then for any point `x ∈ s` the slope of the se
cant line of `f`
through `x` is antitone on `s \ {x}`.
-/
lemma ConcaveOn.slope_anti (hfc : ConcaveOn 𝕜 s f) (hx : x ∈ s) :
    AntitoneOn (slope f x) (s \ {x}) := by
  rw [← neg_neg f, slope_neg_fun]
  exact (ConvexOn.slope_mono hfc.neg hx).neg
/-
**ConcaveOn.antitoneOn_slope_gt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.antitoneOn_slope_gt (hfc : ConcaveOn 𝕜 s f) (hxs : x in s) : Ant
itoneOn (slope f x) {y in s | x < y}
参数：hfc : ConcaveOn 𝕜 s f；hxs : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   AntitoneOn f s → s₂ ⊆ s → Antit
oneOn…
· 使用引理 `ConcaveOn.slope_anti`：ConcaveOn.slope_anti (hfc : ConcaveOn 𝕜 s f) (hx :
 x in s) : AntitoneOn (slope f x) (s \ {x})
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma ConcaveOn.antitoneOn_slope_gt (hfc : ConcaveOn 𝕜 s f) (hxs : x ∈ s) :
    AntitoneOn (slope f x) {y ∈ s | x < y} :=
  (hfc.slope_anti hxs).mono fun _ ⟨h1, h2⟩ ↦ ⟨h1, h2.ne'⟩
/-
**ConcaveOn.antitoneOn_slope_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.antitoneOn_slope_lt (hfc : ConcaveOn 𝕜 s f) (hxs : x in s) : Ant
itoneOn (slope f x) {y in s | y < x}
参数：hfc : ConcaveOn 𝕜 s f；hxs : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   AntitoneOn f s → s₂ ⊆ s → Antit
oneOn…
· 使用引理 `ConcaveOn.slope_anti`：ConcaveOn.slope_anti (hfc : ConcaveOn 𝕜 s f) (hx :
 x in s) : AntitoneOn (slope f x) (s \ {x})
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
lemma ConcaveOn.antitoneOn_slope_lt (hfc : ConcaveOn 𝕜 s f) (hxs : x ∈ s) :
    AntitoneOn (slope f x) {y ∈ s | y < x} :=
  (hfc.slope_anti hxs).mono fun _ ⟨h1, h2⟩ ↦ ⟨h1, h2.ne⟩

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
/-
**bddBelow_slope_lt_of_mem_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bddBelow_slope_lt_of_mem_interior (hfc : ConvexOn 𝕜 s f) (hxs : x in inter
ior s) : BddBelow (slope f x '' {y in s | x < y})
参数：hfc : ConvexOn 𝕜 s f；hxs : x in interior s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists_lt`：Filter.Eventually.exists_lt {a : α} [NeBot 
(𝓝[<] a)] {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : exists b < a, p b
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
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bddBelow_iff_subset_Ici`：bddBelow_iff_subset_Ici : BddBelow s ↔ exists a
, s subseteq Ici a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ConvexOn.slope_mono`：ConvexOn.slope_mono (hfc : ConvexOn 𝕜 s f) (hx : x 
in s) : MonotoneOn (slope f x) (s \ {x})
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
lemma bddBelow_slope_lt_of_mem_interior (hfc : ConvexOn 𝕜 s f) (hxs : x ∈ interior s) :
    BddBelow (slope f x '' {y ∈ s | x < y}) := by
  obtain ⟨y, hyx, hys⟩ : ∃ y, y < x ∧ y ∈ s :=
    Eventually.exists_lt (mem_interior_iff_mem_nhds.mp hxs)
  refine bddBelow_iff_subset_Ici.mpr ⟨slope f x y, fun y' ⟨z, hz, hz'⟩ ↦ ?_⟩
  simp_rw [mem_Ici, ← hz']
  refine hfc.slope_mono (interior_subset hxs) ?_ ?_ (hyx.trans hz.2).le
  · simp [hys, hyx.ne]
  · simp [hz.2.ne', hz.1]
/-
**bddAbove_slope_gt_of_mem_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bddAbove_slope_gt_of_mem_interior (hfc : ConvexOn 𝕜 s f) (hxs : x in inter
ior s) : BddAbove (slope f x '' {y in s | y < x})
参数：hfc : ConvexOn 𝕜 s f；hxs : x in interior s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists_gt`：∀ {α : Type u_1} [inst : TopologicalSpace α
] [inst_1 : Preorder α] {a : α} [(nhdsWithin a (Set.Ioi a)).NeBot]   {p : α → Pr
op}, (∀ᶠ (x : α) …
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
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bddAbove_iff_subset_Iic`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α
}, BddAbove s ↔ ∃ a, s ⊆ Set.Iic a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ConvexOn.slope_mono`：ConvexOn.slope_mono (hfc : ConvexOn 𝕜 s f) (hx : x 
in s) : MonotoneOn (slope f x) (s \ {x})
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
（共 31 条，此处仅展示前 30 条）
-/
lemma bddAbove_slope_gt_of_mem_interior (hfc : ConvexOn 𝕜 s f) (hxs : x ∈ interior s) :
    BddAbove (slope f x '' {y ∈ s | y < x}) := by
  obtain ⟨y, hyx, hys⟩ : ∃ y, x < y ∧ y ∈ s :=
    Eventually.exists_gt (mem_interior_iff_mem_nhds.mp hxs)
  refine bddAbove_iff_subset_Iic.mpr ⟨slope f x y, fun y' ⟨z, hz, hz'⟩ ↦ ?_⟩
  simp_rw [mem_Iic, ← hz']
  refine hfc.slope_mono (interior_subset hxs) ?_ ?_ (hz.2.trans hyx).le
  · simp [hz.2.ne, hz.1]
  · simp [hys, hyx.ne']

end slope

namespace ConvexOn

variable {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}

section Interior

/-!
### Left and right derivative of a convex function in the interior of the set
-/

/-
**ConvexOn.hasDerivWithinAt_sInf_slope_of_mem_interior** 是 Mathlib 中的一个引理，位于命名空间
 `ConvexOn`。
形式化陈述：hasDerivWithinAt_sInf_slope_of_mem_interior (hfc : ConvexOn Real S f) (hxs
 : x in interior S) : HasDerivWithinAt f (sInf (slope f x '' {y in S | x < y})) 
(Ioi x) x
参数：hfc : ConvexOn Real S f；hxs : x in interior S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nhds_iff_exists_Ioo_subset`：mem_nhds_iff_exists_Ioo_subset [NoMaxOrd
er α] [NoMinOrder α] {a : α} {s : Set α} : s in 𝓝 a ↔ exists l u, a in Ioo l u ∧
 Ioo l u subseteq s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `MonotoneOn.tendsto_nhdsWithin_Ioo_right`：MonotoneOn.tendsto_nhdsWithin_I
oo_right {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [C
onditionallyCompleteLinearOrd…
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
· 使用定理 `MonotoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   MonotoneOn f s → s₂ ⊆ s → Monot
oneOn…
· 使用引理 `ConvexOn.monotoneOn_slope_gt`：ConvexOn.monotoneOn_slope_gt (hfc : Convex
On 𝕜 s f) (hxs : x in s) : MonotoneOn (slope f x) {y in s | x < y}
· 使用定理 `BddBelow.mono`：∀ {α : Type u_1} [inst : Preorder α] ⦃s t : Set α⦄, s ⊆ t
 → BddBelow t → BddBelow s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用引理 `bddBelow_slope_lt_of_mem_interior`：bddBelow_slope_lt_of_mem_interior (hf
c : ConvexOn 𝕜 s f) (hxs : x in interior s) : BddBelow (slope f x '' {y in s | x
 < y})
· 使用引理 `MonotoneOn.csInf_eq_of_subset_of_forall_exists_le`：MonotoneOn.csInf_eq_o
f_subset_of_forall_exists_le [Preorder α] [ConditionallyCompleteLattice β] {f : 
α -> β} {s t : Set α} (ht : BddBelow (f…
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
### Left and right derivative of a convex function in the interior of the set
-/
lemma hasDerivWithinAt_sInf_slope_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    HasDerivWithinAt f (sInf (slope f x '' {y ∈ S | x < y})) (Ioi x) x := by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Ioi, lt_self_iff_false, not_false_eq_true, sdiff_singleton_eq_self]
  have h : Ioo x b ⊆ {y | y ∈ S ∧ x < y} := fun z hz ↦ ⟨habs ⟨hxab.1.trans hz.1, hz.2⟩, hz.1⟩
  have h_Ioo : Tendsto (slope f x) (𝓝[>] x) (𝓝 (sInf (slope f x '' Ioo x b))) :=
    ((monotoneOn_slope_gt hfc (habs hxab)).mono h).tendsto_nhdsWithin_Ioo_right
      (by simpa using hxab.2) ((bddBelow_slope_lt_of_mem_interior hfc hxs).mono (image_mono h))
  suffices sInf (slope f x '' Ioo x b) = sInf (slope f x '' {y ∈ S | x < y}) by rwa [← this]
  apply (monotoneOn_slope_gt hfc (habs hxab)).csInf_eq_of_subset_of_forall_exists_le
    (bddBelow_slope_lt_of_mem_interior hfc hxs) h ?_
  rintro y ⟨hyS, hxy⟩
  obtain ⟨z, hxz, hzy⟩ := exists_between (lt_min hxab.2 hxy)
  exact ⟨z, ⟨hxz, hzy.trans_le (min_le_left _ _)⟩, hzy.le.trans (min_le_right _ _)⟩
/-
**ConvexOn.hasDerivWithinAt_sSup_slope_of_mem_interior** 是 Mathlib 中的一个引理，位于命名空间
 `ConvexOn`。
形式化陈述：hasDerivWithinAt_sSup_slope_of_mem_interior (hfc : ConvexOn Real S f) (hxs
 : x in interior S) : HasDerivWithinAt f (sSup (slope f x '' {y in S | y < x})) 
(Iio x) x
参数：hfc : ConvexOn Real S f；hxs : x in interior S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nhds_iff_exists_Ioo_subset`：mem_nhds_iff_exists_Ioo_subset [NoMaxOrd
er α] [NoMinOrder α] {a : α} {s : Set α} : s in 𝓝 a ↔ exists l u, a in Ioo l u ∧
 Ioo l u subseteq s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `MonotoneOn.tendsto_nhdsWithin_Ioo_left`：MonotoneOn.tendsto_nhdsWithin_Io
o_left {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [Con
ditionallyCompleteLinearOrde…
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
· 使用定理 `MonotoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   MonotoneOn f s → s₂ ⊆ s → Monot
oneOn…
· 使用引理 `ConvexOn.monotoneOn_slope_lt`：ConvexOn.monotoneOn_slope_lt (hfc : Convex
On 𝕜 s f) (hxs : x in s) : MonotoneOn (slope f x) {y in s | y < x}
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用引理 `bddAbove_slope_gt_of_mem_interior`：bddAbove_slope_gt_of_mem_interior (hf
c : ConvexOn 𝕜 s f) (hxs : x in interior s) : BddAbove (slope f x '' {y in s | y
 < x})
· 使用定理 `MonotoneOn.csSup_eq_of_subset_of_forall_exists_le`：∀ {α : Type u_1} {β :
 Type u_2} [inst : Preorder α] [inst_1 : ConditionallyCompleteLattice β] {f : α 
→ β} {s t : Set α},   BddAbove (f '' t)…
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
（共 36 条，此处仅展示前 30 条）
-/
lemma hasDerivWithinAt_sSup_slope_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    HasDerivWithinAt f (sSup (slope f x '' {y ∈ S | y < x})) (Iio x) x := by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Iio, lt_self_iff_false, not_false_eq_true, sdiff_singleton_eq_self]
  have h : Ioo a x ⊆ {y | y ∈ S ∧ y < x} := fun z hz ↦ ⟨habs ⟨hz.1, hz.2.trans hxab.2⟩, hz.2⟩
  have h_Ioo : Tendsto (slope f x) (𝓝[<] x) (𝓝 (sSup (slope f x '' Ioo a x))) :=
    ((monotoneOn_slope_lt hfc (habs hxab)).mono h).tendsto_nhdsWithin_Ioo_left
      (by simpa using hxab.1) ((bddAbove_slope_gt_of_mem_interior hfc hxs).mono (image_mono h))
  suffices sSup (slope f x '' Ioo a x) = sSup (slope f x '' {y ∈ S | y < x}) by rwa [← this]
  apply (monotoneOn_slope_lt hfc (habs hxab)).csSup_eq_of_subset_of_forall_exists_le
    (bddAbove_slope_gt_of_mem_interior hfc hxs) h ?_
  rintro y ⟨hyS, hyx⟩
  obtain ⟨z, hyz, hzx⟩ := exists_between (max_lt hxab.1 hyx)
  exact ⟨z, ⟨(le_max_left _ _).trans_lt hyz, hzx⟩, (le_max_right _ _).trans hyz.le⟩
/-
**ConvexOn.differentiableWithinAt_Ioi_of_mem_interior** 是 Mathlib 中的一个引理，位于命名空间 
`ConvexOn`。
形式化陈述：differentiableWithinAt_Ioi_of_mem_interior (hfc : ConvexOn Real S f) (hxs 
: x in interior S) : DifferentiableWithinAt Real f (Ioi x) x
参数：hfc : ConvexOn Real S f；hxs : x in interior S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用引理 `ConvexOn.hasDerivWithinAt_sInf_slope_of_mem_interior`：hasDerivWithinAt_s
Inf_slope_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) : Ha
sDerivWithinAt f (sInf (slope f x '' {y in…
-/
lemma differentiableWithinAt_Ioi_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    DifferentiableWithinAt ℝ f (Ioi x) x :=
  (hfc.hasDerivWithinAt_sInf_slope_of_mem_interior hxs).differentiableWithinAt
/-
**ConvexOn.differentiableWithinAt_Iio_of_mem_interior** 是 Mathlib 中的一个引理，位于命名空间 
`ConvexOn`。
形式化陈述：differentiableWithinAt_Iio_of_mem_interior (hfc : ConvexOn Real S f) (hxs 
: x in interior S) : DifferentiableWithinAt Real f (Iio x) x
参数：hfc : ConvexOn Real S f；hxs : x in interior S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用引理 `ConvexOn.hasDerivWithinAt_sSup_slope_of_mem_interior`：hasDerivWithinAt_s
Sup_slope_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) : Ha
sDerivWithinAt f (sSup (slope f x '' {y in…
-/
lemma differentiableWithinAt_Iio_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    DifferentiableWithinAt ℝ f (Iio x) x :=
  (hfc.hasDerivWithinAt_sSup_slope_of_mem_interior hxs).differentiableWithinAt
/-
**ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior** 是 Mathlib 中的一个引理，位于命名空间
 `ConvexOn`。
形式化陈述：hasDerivWithinAt_rightDeriv_of_mem_interior (hfc : ConvexOn Real S f) (hxs
 : x in interior S) : HasDerivWithinAt f (derivWithin f (Ioi x) x) (Ioi x) x
参数：hfc : ConvexOn Real S f；hxs : x in interior S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用引理 `ConvexOn.differentiableWithinAt_Ioi_of_mem_interior`：differentiableWithi
nAt_Ioi_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) : Diff
erentiableWithinAt Real f (Ioi x) x
-/
lemma hasDerivWithinAt_rightDeriv_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    HasDerivWithinAt f (derivWithin f (Ioi x) x) (Ioi x) x :=
  (hfc.differentiableWithinAt_Ioi_of_mem_interior hxs).hasDerivWithinAt
/-
**ConvexOn.hasDerivWithinAt_leftDeriv_of_mem_interior** 是 Mathlib 中的一个引理，位于命名空间 
`ConvexOn`。
形式化陈述：hasDerivWithinAt_leftDeriv_of_mem_interior (hfc : ConvexOn Real S f) (hxs 
: x in interior S) : HasDerivWithinAt f (derivWithin f (Iio x) x) (Iio x) x
参数：hfc : ConvexOn Real S f；hxs : x in interior S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用引理 `ConvexOn.differentiableWithinAt_Iio_of_mem_interior`：differentiableWithi
nAt_Iio_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) : Diff
erentiableWithinAt Real f (Iio x) x
-/
lemma hasDerivWithinAt_leftDeriv_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    HasDerivWithinAt f (derivWithin f (Iio x) x) (Iio x) x :=
  (hfc.differentiableWithinAt_Iio_of_mem_interior hxs).hasDerivWithinAt
/-
**ConvexOn.rightDeriv_eq_sInf_slope_of_mem_interior** 是 Mathlib 中的一个引理，位于命名空间 `C
onvexOn`。
形式化陈述：rightDeriv_eq_sInf_slope_of_mem_interior (hfc : ConvexOn Real S f) (hxs : 
x in interior S) : derivWithin f (Ioi x) x = sInf (slope f x '' {y | y in S ∧ x 
< y})
参数：hfc : ConvexOn Real S f；hxs : x in interior S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用引理 `ConvexOn.hasDerivWithinAt_sInf_slope_of_mem_interior`：hasDerivWithinAt_s
Inf_slope_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) : Ha
sDerivWithinAt f (sInf (slope f x '' {y in…
· 使用定理 `uniqueDiffWithinAt_Ioi`：uniqueDiffWithinAt_Ioi (a : Real) : UniqueDiffWi
thinAt Real (Ioi a) a
-/
lemma rightDeriv_eq_sInf_slope_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    derivWithin f (Ioi x) x = sInf (slope f x '' {y | y ∈ S ∧ x < y}) :=
  (hfc.hasDerivWithinAt_sInf_slope_of_mem_interior hxs).derivWithin (uniqueDiffWithinAt_Ioi x)
/-
**ConvexOn.leftDeriv_eq_sSup_slope_of_mem_interior** 是 Mathlib 中的一个引理，位于命名空间 `Co
nvexOn`。
形式化陈述：leftDeriv_eq_sSup_slope_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x
 in interior S) : derivWithin f (Iio x) x = sSup (slope f x '' {y | y in S ∧ y <
 x})
参数：hfc : ConvexOn Real S f；hxs : x in interior S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用引理 `ConvexOn.hasDerivWithinAt_sSup_slope_of_mem_interior`：hasDerivWithinAt_s
Sup_slope_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) : Ha
sDerivWithinAt f (sSup (slope f x '' {y in…
· 使用定理 `uniqueDiffWithinAt_Iio`：uniqueDiffWithinAt_Iio (a : Real) : UniqueDiffWi
thinAt Real (Iio a) a
-/
lemma leftDeriv_eq_sSup_slope_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    derivWithin f (Iio x) x = sSup (slope f x '' {y | y ∈ S ∧ y < x}) :=
  (hfc.hasDerivWithinAt_sSup_slope_of_mem_interior hxs).derivWithin (uniqueDiffWithinAt_Iio x)
/-
**ConvexOn.monotoneOn_rightDeriv** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：monotoneOn_rightDeriv (hfc : ConvexOn Real S f) : MonotoneOn (fun x => der
ivWithin f (Ioi x) x) (interior S)
参数：hfc : ConvexOn Real S f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ConvexOn.rightDeriv_eq_sInf_slope_of_mem_interior`：rightDeriv_eq_sInf_sl
ope_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) : derivWit
hin f (Ioi x) x = sInf (slope f x '' {y…
· 使用定理 `csInf_le_of_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s : Set α} {a b : α}, BddBelow s → b ∈ s → b ≤ a → sInf s ≤ a
· 使用引理 `bddBelow_slope_lt_of_mem_interior`：bddBelow_slope_lt_of_mem_interior (hf
c : ConvexOn 𝕜 s f) (hxs : x in interior s) : BddBelow (slope f x '' {y in s | x
 < y})
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `mem_nhds_iff_exists_Ioo_subset`：mem_nhds_iff_exists_Ioo_subset [NoMaxOrd
er α] [NoMinOrder α] {a : α} {s : Set α} : s in 𝓝 a ↔ exists l u, a in Ioo l u ∧
 Ioo l u subseteq s
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
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
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `slope_comm`：slope_comm (f : k -> PE) (a b : k) : slope f a b = slope f b
 a
· 使用引理 `ConvexOn.slope_mono`：ConvexOn.slope_mono (hfc : ConvexOn 𝕜 s f) (hx : x 
in s) : MonotoneOn (slope f x) (s \ {x})
（共 33 条，此处仅展示前 30 条）
-/
lemma monotoneOn_rightDeriv (hfc : ConvexOn ℝ S f) :
    MonotoneOn (fun x ↦ derivWithin f (Ioi x) x) (interior S) := by
  intro x hxs y hys hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  simp_rw [hfc.rightDeriv_eq_sInf_slope_of_mem_interior hxs,
    hfc.rightDeriv_eq_sInf_slope_of_mem_interior hys]
  refine csInf_le_of_le (b := slope f x y) (bddBelow_slope_lt_of_mem_interior hfc hxs)
    ⟨y, by simp only [mem_ofPred_eq, hxy, and_true]; exact interior_subset hys⟩
    (le_csInf ?_ ?_)
  · have hys' := hys
    rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hys'
    obtain ⟨a, b, hxab, habs⟩ := hys'
    rw [image_nonempty]
    obtain ⟨z, hxz, hzb⟩ := exists_between hxab.2
    exact ⟨z, habs ⟨hxab.1.trans hxz, hzb⟩, hxz⟩
  · rintro _ ⟨z, ⟨hzs, hyz : y < z⟩, rfl⟩
    rw [slope_comm]
    exact slope_mono hfc (interior_subset hys) ⟨interior_subset hxs, hxy.ne⟩ ⟨hzs, hyz.ne'⟩
      (hxy.trans hyz).le
/-
**ConvexOn.monotoneOn_leftDeriv** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：monotoneOn_leftDeriv (hfc : ConvexOn Real S f) : MonotoneOn (fun x => deri
vWithin f (Iio x) x) (interior S)
参数：hfc : ConvexOn Real S f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ConvexOn.leftDeriv_eq_sSup_slope_of_mem_interior`：leftDeriv_eq_sSup_slop
e_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) : derivWithi
n f (Iio x) x = sSup (slope f x '' {y …
· 使用定理 `le_csSup_of_le`：le_csSup_of_le (hs : BddAbove s) (hb : b in s) (h : a <=
 b) : a <= sSup s
· 使用引理 `bddAbove_slope_gt_of_mem_interior`：bddAbove_slope_gt_of_mem_interior (hf
c : ConvexOn 𝕜 s f) (hxs : x in interior s) : BddAbove (slope f x '' {y in s | y
 < x})
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `slope_comm`：slope_comm (f : k -> PE) (a b : k) : slope f a b = slope f b
 a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `mem_nhds_iff_exists_Ioo_subset`：mem_nhds_iff_exists_Ioo_subset [NoMaxOrd
er α] [NoMinOrder α] {a : α} {s : Set α} : s in 𝓝 a ↔ exists l u, a in Ioo l u ∧
 Ioo l u subseteq s
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
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
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `ConvexOn.slope_mono`：ConvexOn.slope_mono (hfc : ConvexOn 𝕜 s f) (hx : x 
in s) : MonotoneOn (slope f x) (s \ {x})
（共 33 条，此处仅展示前 30 条）
-/
lemma monotoneOn_leftDeriv (hfc : ConvexOn ℝ S f) :
    MonotoneOn (fun x ↦ derivWithin f (Iio x) x) (interior S) := by
  intro x hxs y hys hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  simp_rw [hfc.leftDeriv_eq_sSup_slope_of_mem_interior hxs,
    hfc.leftDeriv_eq_sSup_slope_of_mem_interior hys]
  refine le_csSup_of_le (b := slope f x y) (bddAbove_slope_gt_of_mem_interior hfc hys)
    ⟨x, by simp only [slope_comm, mem_ofPred_eq, hxy, and_true]; exact interior_subset hxs⟩
    (csSup_le ?_ ?_)
  · have hxs' := hxs
    rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs'
    obtain ⟨a, b, hxab, habs⟩ := hxs'
    rw [image_nonempty]
    obtain ⟨z, hxz, hzb⟩ := exists_between hxab.1
    exact ⟨z, habs ⟨hxz, hzb.trans hxab.2⟩, hzb⟩
  · rintro _ ⟨z, ⟨hzs, hyz : z < x⟩, rfl⟩
    exact slope_mono hfc (interior_subset hxs) ⟨hzs, hyz.ne⟩ ⟨interior_subset hys, hxy.ne'⟩
      (hyz.trans hxy).le
/-
**ConvexOn.leftDeriv_le_rightDeriv_of_mem_interior** 是 Mathlib 中的一个引理，位于命名空间 `Co
nvexOn`。
形式化陈述：leftDeriv_le_rightDeriv_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x
 in interior S) : derivWithin f (Iio x) x <= derivWithin f (Ioi x) x
参数：hfc : ConvexOn Real S f；hxs : x in interior S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nhds_iff_exists_Ioo_subset`：mem_nhds_iff_exists_Ioo_subset [NoMaxOrd
er α] [NoMinOrder α] {a : α} {s : Set α} : s in 𝓝 a ↔ exists l u, a in Ioo l u ∧
 Ioo l u subseteq s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用引理 `ConvexOn.rightDeriv_eq_sInf_slope_of_mem_interior`：rightDeriv_eq_sInf_sl
ope_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) : derivWit
hin f (Ioi x) x = sInf (slope f x '' {y…
· 使用引理 `ConvexOn.leftDeriv_eq_sSup_slope_of_mem_interior`：leftDeriv_eq_sSup_slop
e_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) : derivWithi
n f (Iio x) x = sSup (slope f x '' {y …
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
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
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用引理 `ConvexOn.slope_mono`：ConvexOn.slope_mono (hfc : ConvexOn 𝕜 s f) (hx : x 
in s) : MonotoneOn (slope f x) (s \ {x})
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma leftDeriv_le_rightDeriv_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    derivWithin f (Iio x) x ≤ derivWithin f (Ioi x) x := by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  rw [hfc.rightDeriv_eq_sInf_slope_of_mem_interior hxs,
    hfc.leftDeriv_eq_sSup_slope_of_mem_interior hxs]
  refine csSup_le ?_ ?_
  · rw [image_nonempty]
    obtain ⟨z, haz, hzx⟩ := exists_between hxab.1
    exact ⟨z, habs ⟨haz, hzx.trans hxab.2⟩, hzx⟩
  rintro _ ⟨z, ⟨hzs, hzx⟩, rfl⟩
  refine le_csInf ?_ ?_
  · rw [image_nonempty]
    obtain ⟨z, hxz, hzb⟩ := exists_between hxab.2
    exact ⟨z, habs ⟨hxab.1.trans hxz, hzb⟩, hxz⟩
  rintro _ ⟨y, ⟨hys, hxy⟩, rfl⟩
  exact slope_mono hfc (interior_subset hxs) ⟨hzs, hzx.ne⟩ ⟨hys, hxy.ne'⟩ (hzx.trans hxy).le

end Interior

section left
/-!
### Convex functions, derivative at left endpoint of secant
-/

/-- If `f : ℝ → ℝ` is convex on `S` and right-differentiable at `x ∈ S`, then the slope of any
secant line with left endpoint at `x` is bounded below by the right derivative of `f` at `x`. -/
/-
**ConvexOn.le_slope_of_hasDerivWithinAt_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`
。
形式化陈述：le_slope_of_hasDerivWithinAt_Ioi (hfc : ConvexOn Real S f) (hx : x in S) (
hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) : f' <= slope
 f x y
参数：hfc : ConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasDerivWit
hinAt f f' (Ioi x) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
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
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasDerivWithinAt_iff_tendsto_slope'`：hasDerivWithinAt_iff_tendsto_slope'
 (hs : x ∉ s) : HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s] x) (𝓝 f')
· 使用定理 `Set.self_notMem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∉ S
et.Ioi a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `slope_def_field`：slope_def_field (f : k -> k) (a b : k) : slope f a b = 
(f b - f a) / (b - a)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_lt_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [ClosedIciTopology α] {a b : α},   a < b → ∀ᶠ (x : α) in nhds a,
 x < b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ConvexOn.secant_mono`：ConvexOn.secant_mono (hf : ConvexOn 𝕜 s f) {a x y 
: 𝕜} (ha : a in s) (hx : x in s) (hy : y in s) (hxa : x != a) (hya : y != a) (hx
y : x <= y…
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : ℝ → ℝ` is convex on `S` and right-differentiable at `x ∈ S`, then the sl
ope of any
secant line with left endpoint at `x` is bounded below by the right derivative o
f `f` at `x`.
-/
lemma le_slope_of_hasDerivWithinAt_Ioi (hfc : ConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    f' ≤ slope f x y := by
  apply le_of_tendsto <| (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hf'
  simp_rw [eventually_nhdsWithin_iff, slope_def_field]
  filter_upwards [eventually_lt_nhds hxy] with t ht (ht' : x < t)
  refine hfc.secant_mono hx (?_ : t ∈ S) hy ht'.ne' hxy.ne' ht.le
  exact hfc.1.ordConnected.out hx hy ⟨ht'.le, ht.le⟩

/-- Reformulation of `ConvexOn.le_slope_of_hasDerivWithinAt_Ioi` using `derivWithin`. -/
/-
**ConvexOn.rightDeriv_le_slope** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：rightDeriv_le_slope (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) 
(hxy : x < y) (hfd : DifferentiableWithinAt Real f (Ioi x) x) : derivWithin f (I
oi x) x <= slope f x y
参数：hfc : ConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Differentia
bleWithinAt Real f (Ioi x) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.le_slope_of_hasDerivWithinAt_Ioi`：le_slope_of_hasDerivWithinAt_
Ioi (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : H
asDerivWithinAt f f' (Ioi x) x)…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x

--- 原说明 ---
Reformulation of `ConvexOn.le_slope_of_hasDerivWithinAt_Ioi` using `derivWithin`
.
-/
lemma rightDeriv_le_slope (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Ioi x) x) :
    derivWithin f (Ioi x) x ≤ slope f x y :=
  le_slope_of_hasDerivWithinAt_Ioi hfc hx hy hxy hfd.hasDerivWithinAt
/-
**ConvexOn.rightDeriv_le_slope_of_mem_interior** 是 Mathlib 中的一个引理，位于命名空间 `Convex
On`。
形式化陈述：rightDeriv_le_slope_of_mem_interior (hfc : ConvexOn Real S f) {y : Real} (
hxs : x in interior S) (hys : y in S) (hxy : x < y) : derivWithin f (Ioi x) x <=
 slope f x y
参数：hfc : ConvexOn Real S f；hxs : x in interior S；hys : y in S；hxy : x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.rightDeriv_le_slope`：rightDeriv_le_slope (hfc : ConvexOn Real S
 f) (hx : x in S) (hy : y in S) (hxy : x < y) (hfd : DifferentiableWithinAt Real
 f (Ioi x) x) : de…
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用引理 `ConvexOn.differentiableWithinAt_Ioi_of_mem_interior`：differentiableWithi
nAt_Ioi_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) : Diff
erentiableWithinAt Real f (Ioi x) x
-/
lemma rightDeriv_le_slope_of_mem_interior (hfc : ConvexOn ℝ S f)
    {y : ℝ} (hxs : x ∈ interior S) (hys : y ∈ S) (hxy : x < y) :
    derivWithin f (Ioi x) x ≤ slope f x y :=
  rightDeriv_le_slope hfc (interior_subset hxs) hys hxy
    (differentiableWithinAt_Ioi_of_mem_interior hfc hxs)

/-- If `f : ℝ → ℝ` is convex on `S` and differentiable within `S` at `x`, then the slope of any
secant line with left endpoint at `x` is bounded below by the derivative of `f` within `S` at `x`.

This is fractionally weaker than `ConvexOn.le_slope_of_hasDerivWithinAt_Ioi` but simpler to apply
under a `DifferentiableOn S` hypothesis. -/
/-
**ConvexOn.le_slope_of_hasDerivWithinAt** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：le_slope_of_hasDerivWithinAt (hfc : ConvexOn Real S f) (hx : x in S) (hy :
 y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S x) : f' <= slope f x y
参数：hfc : ConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasDerivWit
hinAt f f' S x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ConvexOn.le_slope_of_hasDerivWithinAt_Ioi`：le_slope_of_hasDerivWithinAt_
Ioi (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : H
asDerivWithinAt f f' (Ioi x) x)…
· 使用定理 `HasDerivWithinAt.mono_of_mem_nhdsWithin`：HasDerivWithinAt.mono_of_mem_nh
dsWithin (h : HasDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) : HasDerivWithinAt 
f f' s x
· 使用引理 `Set.OrdConnected.mem_nhdsGT`：mem_nhdsGT (hS : OrdConnected S) (hx : x in
 S) (hy : y in S) (hxy : x < y) : S in 𝓝[>] x
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If `f : ℝ → ℝ` is convex on `S` and differentiable within `S` at `x`, then the s
lope of any
secant line with left endpoint at `x` is bounded below by the derivative of `f` 
within `S` at `x`.

This is fractionally weaker than `ConvexOn.le_slope_of_hasDerivWithinAt_Ioi` but
 simpler to apply
under a `DifferentiableOn S` hypothesis.
-/
lemma le_slope_of_hasDerivWithinAt (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' S x) :
    f' ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy <|
    hf'.mono_of_mem_nhdsWithin <| hfc.1.ordConnected.mem_nhdsGT hx hy hxy

/-- Reformulation of `ConvexOn.le_slope_of_hasDerivWithinAt` using `derivWithin`. -/
/-
**ConvexOn.derivWithin_le_slope** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：derivWithin_le_slope (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S)
 (hxy : x < y) (hfd : DifferentiableWithinAt Real f S x) : derivWithin f S x <= 
slope f x y
参数：hfc : ConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Differentia
bleWithinAt Real f S x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.le_slope_of_hasDerivWithinAt`：le_slope_of_hasDerivWithinAt (hfc
 : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivW
ithinAt f f' S x) : f' <= s…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x

--- 原说明 ---
Reformulation of `ConvexOn.le_slope_of_hasDerivWithinAt` using `derivWithin`.
-/
lemma derivWithin_le_slope (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S x) :
    derivWithin f S x ≤ slope f x y :=
  le_slope_of_hasDerivWithinAt hfc hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is convex on `S` and differentiable at `x ∈ S`, then the slope of any secant
line with left endpoint at `x` is bounded below by the derivative of `f` at `x`. -/
/-
**ConvexOn.le_slope_of_hasDerivAt** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：le_slope_of_hasDerivAt (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in 
S) (hxy : x < y) (ha : HasDerivAt f f' x) : f' <= slope f x y
参数：hfc : ConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；ha : HasDerivAt f
 f' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ConvexOn.le_slope_of_hasDerivWithinAt_Ioi`：le_slope_of_hasDerivWithinAt_
Ioi (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : H
asDerivWithinAt f f' (Ioi x) x)…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
If `f : ℝ → ℝ` is convex on `S` and differentiable at `x ∈ S`, then the slope of
 any secant
line with left endpoint at `x` is bounded below by the derivative of `f` at `x`.
-/
lemma le_slope_of_hasDerivAt (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (ha : HasDerivAt f f' x) :
    f' ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy ha.hasDerivWithinAt

/-- Reformulation of `ConvexOn.le_slope_of_hasDerivAt` using `deriv` -/
/-
**ConvexOn.deriv_le_slope** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：deriv_le_slope (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy 
: x < y) (hfd : DifferentiableAt Real f x) : deriv f x <= slope f x y
参数：hfc : ConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Differentia
bleAt Real f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.le_slope_of_hasDerivAt`：le_slope_of_hasDerivAt (hfc : ConvexOn 
Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (ha : HasDerivAt f f' x) : f
' <= slope f x y
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x

--- 原说明 ---
Reformulation of `ConvexOn.le_slope_of_hasDerivAt` using `deriv`
-/
lemma deriv_le_slope (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f x) :
    deriv f x ≤ slope f x y :=
  le_slope_of_hasDerivAt hfc hx hy hxy hfd.hasDerivAt

end left

section right
/-!
### Convex functions, derivative at right endpoint of secant
-/

/-- If `f : ℝ → ℝ` is convex on `S` and left-differentiable at `y ∈ S`, then the slope of any secant
line with right endpoint at `y` is bounded above by the left derivative of `f` at `y`. -/
/-
**ConvexOn.slope_le_of_hasDerivWithinAt_Iio** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`
。
形式化陈述：slope_le_of_hasDerivWithinAt_Iio (hfc : ConvexOn Real S f) (hx : x in S) (
hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) : slope f x y
 <= f'
参数：hfc : ConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasDerivWit
hinAt f f' (Iio y) y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
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
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasDerivWithinAt_iff_tendsto_slope'`：hasDerivWithinAt_iff_tendsto_slope'
 (hs : x ∉ s) : HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s] x) (𝓝 f')
· 使用定理 `Set.self_notMem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∉ S
et.Iio a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `slope_comm`：slope_comm (f : k -> PE) (a b : k) : slope f a b = slope f b
 a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `slope_def_field`：slope_def_field (f : k -> k) (a b : k) : slope f a b = 
(f b - f a) / (b - a)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_gt_nhds`：eventually_gt_nhds (hab : b < a) : forallᶠ x in 𝓝 a,
 b < x
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ConvexOn.secant_mono`：ConvexOn.secant_mono (hf : ConvexOn 𝕜 s f) {a x y 
: 𝕜} (ha : a in s) (hx : x in s) (hy : y in s) (hxa : x != a) (hya : y != a) (hx
y : x <= y…
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : ℝ → ℝ` is convex on `S` and left-differentiable at `y ∈ S`, then the slo
pe of any secant
line with right endpoint at `y` is bounded above by the left derivative of `f` a
t `y`.
-/
lemma slope_le_of_hasDerivWithinAt_Iio (hfc : ConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    slope f x y ≤ f' := by
  apply ge_of_tendsto <| (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp hf'
  simp_rw [eventually_nhdsWithin_iff, slope_comm f x y, slope_def_field]
  filter_upwards [eventually_gt_nhds hxy] with t ht (ht' : t < y)
  refine hfc.secant_mono hy hx (?_ : t ∈ S) hxy.ne ht'.ne ht.le
  exact hfc.1.ordConnected.out hx hy ⟨ht.le, ht'.le⟩

/-- Reformulation of `ConvexOn.slope_le_of_hasDerivWithinAt_Iio` using `derivWithin`. -/
/-
**ConvexOn.slope_le_leftDeriv** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：slope_le_leftDeriv (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (
hxy : x < y) (hfd : DifferentiableWithinAt Real f (Iio y) y) : slope f x y <= de
rivWithin f (Iio y) y
参数：hfc : ConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Differentia
bleWithinAt Real f (Iio y) y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.slope_le_of_hasDerivWithinAt_Iio`：slope_le_of_hasDerivWithinAt_
Iio (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : H
asDerivWithinAt f f' (Iio y) y)…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x

--- 原说明 ---
Reformulation of `ConvexOn.slope_le_of_hasDerivWithinAt_Iio` using `derivWithin`
.
-/
lemma slope_le_leftDeriv (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Iio y) y) :
    slope f x y ≤ derivWithin f (Iio y) y :=
  hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt
/-
**ConvexOn.slope_le_leftDeriv_of_mem_interior** 是 Mathlib 中的一个引理，位于命名空间 `ConvexO
n`。
形式化陈述：slope_le_leftDeriv_of_mem_interior (hfc : ConvexOn Real S f) (hys : x in S
) (hxs : y in interior S) (hxy : x < y) : slope f x y <= derivWithin f (Iio y) y
参数：hfc : ConvexOn Real S f；hys : x in S；hxs : y in interior S；hxy : x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.slope_le_leftDeriv`：slope_le_leftDeriv (hfc : ConvexOn Real S f
) (hx : x in S) (hy : y in S) (hxy : x < y) (hfd : DifferentiableWithinAt Real f
 (Iio y) y) : slo…
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用引理 `ConvexOn.differentiableWithinAt_Iio_of_mem_interior`：differentiableWithi
nAt_Iio_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) : Diff
erentiableWithinAt Real f (Iio x) x
-/
lemma slope_le_leftDeriv_of_mem_interior (hfc : ConvexOn ℝ S f)
    (hys : x ∈ S) (hxs : y ∈ interior S) (hxy : x < y) :
    slope f x y ≤ derivWithin f (Iio y) y :=
  slope_le_leftDeriv hfc hys (interior_subset hxs) hxy
    (differentiableWithinAt_Iio_of_mem_interior hfc hxs)

/-- If `f : ℝ → ℝ` is convex on `S` and differentiable within `S` at `y`, then the slope of any
secant line with right endpoint at `y` is bounded above by the derivative of `f` within `S` at `y`.

This is fractionally weaker than `ConvexOn.slope_le_of_hasDerivWithinAt_Iio` but simpler to apply
under a `DifferentiableOn S` hypothesis. -/
/-
**ConvexOn.slope_le_of_hasDerivWithinAt** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：slope_le_of_hasDerivWithinAt (hfc : ConvexOn Real S f) (hx : x in S) (hy :
 y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S y) : slope f x y <= f'
参数：hfc : ConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasDerivWit
hinAt f f' S y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ConvexOn.slope_le_of_hasDerivWithinAt_Iio`：slope_le_of_hasDerivWithinAt_
Iio (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : H
asDerivWithinAt f f' (Iio y) y)…
· 使用定理 `HasDerivWithinAt.mono_of_mem_nhdsWithin`：HasDerivWithinAt.mono_of_mem_nh
dsWithin (h : HasDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) : HasDerivWithinAt 
f f' s x
· 使用引理 `Set.OrdConnected.mem_nhdsLT`：mem_nhdsLT (hS : OrdConnected S) (hx : x in
 S) (hy : y in S) (hxy : x < y) : S in 𝓝[<] y
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If `f : ℝ → ℝ` is convex on `S` and differentiable within `S` at `y`, then the s
lope of any
secant line with right endpoint at `y` is bounded above by the derivative of `f`
 within `S` at `y`.

This is fractionally weaker than `ConvexOn.slope_le_of_hasDerivWithinAt_Iio` but
 simpler to apply
under a `DifferentiableOn S` hypothesis.
-/
lemma slope_le_of_hasDerivWithinAt (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' S y) :
    slope f x y ≤ f' :=
  hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy <|
    hf'.mono_of_mem_nhdsWithin <| hfc.1.ordConnected.mem_nhdsLT hx hy hxy

/-- Reformulation of `ConvexOn.slope_le_of_hasDerivWithinAt` using `derivWithin`. -/
/-
**ConvexOn.slope_le_derivWithin** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：slope_le_derivWithin (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S)
 (hxy : x < y) (hfd : DifferentiableWithinAt Real f S y) : slope f x y <= derivW
ithin f S y
参数：hfc : ConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Differentia
bleWithinAt Real f S y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.slope_le_of_hasDerivWithinAt`：slope_le_of_hasDerivWithinAt (hfc
 : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivW
ithinAt f f' S y) : slope f…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x

--- 原说明 ---
Reformulation of `ConvexOn.slope_le_of_hasDerivWithinAt` using `derivWithin`.
-/
lemma slope_le_derivWithin (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S y) :
    slope f x y ≤ derivWithin f S y :=
  hfc.slope_le_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is convex on `S` and differentiable at `y ∈ S`, then the slope of any secant
line with right endpoint at `y` is bounded above by the derivative of `f` at `y`. -/
/-
**ConvexOn.slope_le_of_hasDerivAt** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：slope_le_of_hasDerivAt (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in 
S) (hxy : x < y) (hf' : HasDerivAt f f' y) : slope f x y <= f'
参数：hfc : ConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasDerivAt 
f f' y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ConvexOn.slope_le_of_hasDerivWithinAt_Iio`：slope_le_of_hasDerivWithinAt_
Iio (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : H
asDerivWithinAt f f' (Iio y) y)…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
If `f : ℝ → ℝ` is convex on `S` and differentiable at `y ∈ S`, then the slope of
 any secant
line with right endpoint at `y` is bounded above by the derivative of `f` at `y`
.
-/
lemma slope_le_of_hasDerivAt (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    slope f x y ≤ f' :=
  hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

/-- Reformulation of `ConvexOn.slope_le_of_hasDerivAt` using `deriv`. -/
/-
**ConvexOn.slope_le_deriv** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：slope_le_deriv (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy 
: x < y) (hfd : DifferentiableAt Real f y) : slope f x y <= deriv f y
参数：hfc : ConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Differentia
bleAt Real f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.slope_le_of_hasDerivAt`：slope_le_of_hasDerivAt (hfc : ConvexOn 
Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivAt f f' y) : 
slope f x y <= f'
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x

--- 原说明 ---
Reformulation of `ConvexOn.slope_le_of_hasDerivAt` using `deriv`.
-/
lemma slope_le_deriv (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f y) :
    slope f x y ≤ deriv f y :=
  hfc.slope_le_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end right
/-!
### Convex functions, monotonicity of derivative
-/

/-- If `f` is convex on `S` and differentiable on `S`, then its derivative within `S` is monotone
on `S`. -/
/-
**ConvexOn.monotoneOn_derivWithin** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：monotoneOn_derivWithin (hfc : ConvexOn Real S f) (hfd : DifferentiableOn R
eal f S) : MonotoneOn (derivWithin f S) S
参数：hfc : ConvexOn Real S f；hfd : DifferentiableOn Real f S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ConvexOn.derivWithin_le_slope`：derivWithin_le_slope (hfc : ConvexOn Real
 S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hfd : DifferentiableWithinAt Re
al f S x) : derivWi…
· 使用引理 `ConvexOn.slope_le_derivWithin`：slope_le_derivWithin (hfc : ConvexOn Real
 S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hfd : DifferentiableWithinAt Re
al f S y) : slope f…

--- 原说明 ---
If `f` is convex on `S` and differentiable on `S`, then its derivative within `S
` is monotone
on `S`.
-/
lemma monotoneOn_derivWithin (hfc : ConvexOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
    MonotoneOn (derivWithin f S) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.derivWithin_le_slope hx hy hxy' (hfd x hx)).trans
    (hfc.slope_le_derivWithin hx hy hxy' (hfd y hy))

/-- If `f` is convex on `S` and differentiable at all points of `S`, then its derivative is monotone
on `S`. -/
/-
**ConvexOn.monotoneOn_deriv** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`。
形式化陈述：monotoneOn_deriv (hfc : ConvexOn Real S f) (hfd : forall x in S, Different
iableAt Real f x) : MonotoneOn (deriv f) S
参数：hfc : ConvexOn Real S f；hfd : forall x in S, DifferentiableAt Real f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ConvexOn.deriv_le_slope`：deriv_le_slope (hfc : ConvexOn Real S f) (hx : 
x in S) (hy : y in S) (hxy : x < y) (hfd : DifferentiableAt Real f x) : deriv f 
x <= slope f …
· 使用引理 `ConvexOn.slope_le_deriv`：slope_le_deriv (hfc : ConvexOn Real S f) (hx : 
x in S) (hy : y in S) (hxy : x < y) (hfd : DifferentiableAt Real f y) : slope f 
x y <= deriv …

--- 原说明 ---
If `f` is convex on `S` and differentiable at all points of `S`, then its deriva
tive is monotone
on `S`.
-/
theorem monotoneOn_deriv (hfc : ConvexOn ℝ S f) (hfd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    MonotoneOn (deriv f) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.deriv_le_slope hx hy hxy' (hfd x hx)).trans (hfc.slope_le_deriv hx hy hxy' (hfd y hy))
/-
**ConvexOn.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg** 是 Mathlib 中的一个引理，位
于命名空间 `ConvexOn`。
形式化陈述：isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg (hf : ConvexOn Real S f) 
(hx : x in interior S) (hf_ld : derivWithin f (Iio x) x <= 0) (hf_rd : 0 <= deri
vWithin f (Ioi x) x) : IsMinOn f S x
参数：hf : ConvexOn Real S f；hx : x in interior S；hf_ld : derivWithin f (Iio x) x <
= 0；hf_rd : 0 <= derivWithin f (Ioi x) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ConvexOn.rightDeriv_le_slope_of_mem_interior`：rightDeriv_le_slope_of_mem
_interior (hfc : ConvexOn Real S f) {y : Real} (hxs : x in interior S) (hys : y 
in S) (hxy : x < y) : derivWithin …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `slope_def_field`：slope_def_field (f : k -> k) (a b : k) : slope f a b = 
(f b - f a) / (b - a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `slope_comm`：slope_comm (f : k -> PE) (a b : k) : slope f a b = slope f b
 a
· 使用引理 `ConvexOn.slope_le_leftDeriv_of_mem_interior`：slope_le_leftDeriv_of_mem_i
nterior (hfc : ConvexOn Real S f) (hys : x in S) (hxs : y in interior S) (hxy : 
x < y) : slope f x y <= derivWith…
-/
lemma isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg (hf : ConvexOn ℝ S f) (hx : x ∈ interior S)
    (hf_ld : derivWithin f (Iio x) x ≤ 0) (hf_rd : 0 ≤ derivWithin f (Ioi x) x) :
    IsMinOn f S x := by
  intro y hy
  rcases lt_trichotomy x y with hxy | h_eq | hyx
  · suffices 0 ≤ slope f x y by
      simp only [slope_def_field, div_nonneg_iff, sub_nonneg, tsub_le_iff_right, zero_add,
        not_le.mpr hxy, and_false, or_false] at this
      exact this.1
    exact hf_rd.trans <| rightDeriv_le_slope_of_mem_interior hf hx hy hxy
  · simp [h_eq]
  · suffices slope f x y ≤ 0 by
      simp only [slope_def_field, div_nonpos_iff, sub_nonneg, tsub_le_iff_right, zero_add,
        not_le.mpr hyx, and_false, or_false] at this
      exact this.1
    rw [slope_comm]
    exact (slope_le_leftDeriv_of_mem_interior hf hy hx hyx).trans hf_ld
/-
**ConvexOn.isMinOn_of_rightDeriv_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：isMinOn_of_rightDeriv_eq_zero (hf : ConvexOn Real S f) (hx : x in interior
 S) (hf_rd : derivWithin f (Ioi x) x = 0) : IsMinOn f S x
参数：hf : ConvexOn Real S f；hx : x in interior S；hf_rd : derivWithin f (Ioi x) x =
 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg`：isMinOn_of_le
ftDeriv_nonpos_of_rightDeriv_nonneg (hf : ConvexOn Real S f) (hx : x in interior
 S) (hf_ld : derivWithin f (Iio x) x <= 0) (hf_…
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `ConvexOn.leftDeriv_le_rightDeriv_of_mem_interior`：leftDeriv_le_rightDeri
v_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) : derivWithi
n f (Iio x) x <= derivWithin f (Ioi x)…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isMinOn_of_rightDeriv_eq_zero (hf : ConvexOn ℝ S f) (hx : x ∈ interior S)
    (hf_rd : derivWithin f (Ioi x) x = 0) :
    IsMinOn f S x := by
  refine hf.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg hx ?_ hf_rd.symm.le
  exact (hf.leftDeriv_le_rightDeriv_of_mem_interior hx).trans_eq hf_rd
/-
**ConvexOn.isMinOn_of_leftDeriv_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：isMinOn_of_leftDeriv_eq_zero (hf : ConvexOn Real S f) (hx : x in interior 
S) (hf_ld : derivWithin f (Iio x) x = 0) : IsMinOn f S x
参数：hf : ConvexOn Real S f；hx : x in interior S；hf_ld : derivWithin f (Iio x) x =
 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg`：isMinOn_of_le
ftDeriv_nonpos_of_rightDeriv_nonneg (hf : ConvexOn Real S f) (hx : x in interior
 S) (hf_ld : derivWithin f (Iio x) x <= 0) (hf_…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ConvexOn.leftDeriv_le_rightDeriv_of_mem_interior`：leftDeriv_le_rightDeri
v_of_mem_interior (hfc : ConvexOn Real S f) (hxs : x in interior S) : derivWithi
n f (Iio x) x <= derivWithin f (Ioi x)…
-/
lemma isMinOn_of_leftDeriv_eq_zero (hf : ConvexOn ℝ S f) (hx : x ∈ interior S)
    (hf_ld : derivWithin f (Iio x) x = 0) :
    IsMinOn f S x := by
  refine hf.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg hx hf_ld.le ?_
  exact hf_ld.symm.le.trans (hf.leftDeriv_le_rightDeriv_of_mem_interior hx)

end ConvexOn

namespace StrictConvexOn

variable {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}

section left
/-!
### Strict convex functions, derivative at left endpoint of secant
-/

/-- If `f : ℝ → ℝ` is strictly convex on `S` and right-differentiable at `x ∈ S`, then the slope of
any secant line with left endpoint at `x` is strictly greater than the right derivative of `f` at
`x`. -/
/-
**StrictConvexOn.lt_slope_of_hasDerivWithinAt_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Str
ictConvexOn`。
形式化陈述：lt_slope_of_hasDerivWithinAt_Ioi (hfc : StrictConvexOn Real S f) (hx : x i
n S) (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) : f' < 
slope f x y
参数：hfc : StrictConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasDe
rivWithinAt f f' (Ioi x) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
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
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `StrictConvexOn.secant_strict_mono`：StrictConvexOn.secant_strict_mono (hf
 : StrictConvexOn 𝕜 s f) {a x y : 𝕜} (ha : a in s) (hx : x in s) (hy : y in s) (
hxa : x != a) (hya : y …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `ConvexOn.le_slope_of_hasDerivWithinAt_Ioi`：le_slope_of_hasDerivWithinAt_
Ioi (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : H
asDerivWithinAt f f' (Ioi x) x)…
· 使用定理 `StrictConvexOn.convexOn`：StrictConvexOn.convexOn {s : Set E} {f : E -> β
} (hf : StrictConvexOn 𝕜 s f) : ConvexOn 𝕜 s f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If `f : ℝ → ℝ` is strictly convex on `S` and right-differentiable at `x ∈ S`, th
en the slope of
any secant line with left endpoint at `x` is strictly greater than the right der
ivative of `f` at
`x`.
-/
lemma lt_slope_of_hasDerivWithinAt_Ioi (hfc : StrictConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    f' < slope f x y := by
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  have hu : u ∈ S := hfc.1.ordConnected.out hx hy ⟨hxu.le, huy.le⟩
  have := hfc.secant_strict_mono hx hu hy hxu.ne' hxy.ne' huy
  simp only [← slope_def_field] at this
  exact (hfc.convexOn.le_slope_of_hasDerivWithinAt_Ioi hx hu hxu hf').trans_lt this
/-
**StrictConvexOn.rightDeriv_lt_slope** 是 Mathlib 中的一个引理，位于命名空间 `StrictConvexOn`。
形式化陈述：rightDeriv_lt_slope (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y 
in S) (hxy : x < y) (hfd : DifferentiableWithinAt Real f (Ioi x) x) : derivWithi
n f (Ioi x) x < slope f x y
参数：hfc : StrictConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Diffe
rentiableWithinAt Real f (Ioi x) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConvexOn.lt_slope_of_hasDerivWithinAt_Ioi`：lt_slope_of_hasDerivWit
hinAt_Ioi (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x <
 y) (hf' : HasDerivWithinAt f f' (Ioi…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
lemma rightDeriv_lt_slope (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Ioi x) x) :
    derivWithin f (Ioi x) x < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable within `S` at `x ∈ S`, then the
slope of any secant line with left endpoint at `x` is strictly greater than the derivative of `f`
within `S` at `x`.

This is fractionally weaker than `StrictConvexOn.lt_slope_of_hasDerivWithinAt_Ioi` but simpler to
apply under a `DifferentiableOn S` hypothesis. -/
/-
**StrictConvexOn.lt_slope_of_hasDerivWithinAt** 是 Mathlib 中的一个引理，位于命名空间 `StrictC
onvexOn`。
形式化陈述：lt_slope_of_hasDerivWithinAt (hfc : StrictConvexOn Real S f) (hx : x in S)
 (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S x) : f' < slope f x 
y
参数：hfc : StrictConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasDe
rivWithinAt f f' S x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `StrictConvexOn.lt_slope_of_hasDerivWithinAt_Ioi`：lt_slope_of_hasDerivWit
hinAt_Ioi (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x <
 y) (hf' : HasDerivWithinAt f f' (Ioi…
· 使用定理 `HasDerivWithinAt.mono_of_mem_nhdsWithin`：HasDerivWithinAt.mono_of_mem_nh
dsWithin (h : HasDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) : HasDerivWithinAt 
f f' s x
· 使用引理 `Set.OrdConnected.mem_nhdsGT`：mem_nhdsGT (hS : OrdConnected S) (hx : x in
 S) (hy : y in S) (hxy : x < y) : S in 𝓝[>] x
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If `f : ℝ → ℝ` is strictly convex on `S` and differentiable within `S` at `x ∈ S
`, then the
slope of any secant line with left endpoint at `x` is strictly greater than the 
derivative of `f`
within `S` at `x`.

This is fractionally weaker than `StrictConvexOn.lt_slope_of_hasDerivWithinAt_Io
i` but simpler to
apply under a `DifferentiableOn S` hypothesis.
-/
lemma lt_slope_of_hasDerivWithinAt (hfc : StrictConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S x) :
    f' < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy <|
    hf'.mono_of_mem_nhdsWithin <| hfc.1.ordConnected.mem_nhdsGT hx hy hxy
/-
**StrictConvexOn.derivWithin_lt_slope** 是 Mathlib 中的一个引理，位于命名空间 `StrictConvexOn`
。
形式化陈述：derivWithin_lt_slope (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y
 in S) (hxy : x < y) (hfd : DifferentiableWithinAt Real f S x) : derivWithin f S
 x < slope f x y
参数：hfc : StrictConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Diffe
rentiableWithinAt Real f S x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConvexOn.lt_slope_of_hasDerivWithinAt`：lt_slope_of_hasDerivWithinA
t (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf'
 : HasDerivWithinAt f f' S x) : f…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
lemma derivWithin_lt_slope (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S x) :
    derivWithin f S x < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable at `x ∈ S`, then the slope of any
secant line with left endpoint at `x` is strictly greater than the derivative of `f` at `x`. -/
/-
**StrictConvexOn.lt_slope_of_hasDerivAt** 是 Mathlib 中的一个引理，位于命名空间 `StrictConvexO
n`。
形式化陈述：lt_slope_of_hasDerivAt (hfc : StrictConvexOn Real S f) (hx : x in S) (hy :
 y in S) (hxy : x < y) (hf' : HasDerivAt f f' x) : f' < slope f x y
参数：hfc : StrictConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasDe
rivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `StrictConvexOn.lt_slope_of_hasDerivWithinAt_Ioi`：lt_slope_of_hasDerivWit
hinAt_Ioi (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x <
 y) (hf' : HasDerivWithinAt f f' (Ioi…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
If `f : ℝ → ℝ` is strictly convex on `S` and differentiable at `x ∈ S`, then the
 slope of any
secant line with left endpoint at `x` is strictly greater than the derivative of
 `f` at `x`.
-/
lemma lt_slope_of_hasDerivAt (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' x) :
    f' < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.hasDerivWithinAt
/-
**StrictConvexOn.deriv_lt_slope** 是 Mathlib 中的一个引理，位于命名空间 `StrictConvexOn`。
形式化陈述：deriv_lt_slope (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S)
 (hxy : x < y) (hfd : DifferentiableAt Real f x) : deriv f x < slope f x y
参数：hfc : StrictConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Diffe
rentiableAt Real f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConvexOn.lt_slope_of_hasDerivAt`：lt_slope_of_hasDerivAt (hfc : Str
ictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivA
t f f' x) : f' < slope f x …
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
lemma deriv_lt_slope (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f x) :
    deriv f x < slope f x y :=
  hfc.lt_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end left

section right
/-!
### Strict convex functions, derivative at right endpoint of secant
-/

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable at `y ∈ S`, then the slope of any
secant line with right endpoint at `y` is strictly less than the left derivative at `y`. -/
/-
**StrictConvexOn.slope_lt_of_hasDerivWithinAt_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Str
ictConvexOn`。
形式化陈述：slope_lt_of_hasDerivWithinAt_Iio (hfc : StrictConvexOn Real S f) (hx : x i
n S) (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) : slope
 f x y < f'
参数：hfc : StrictConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasDe
rivWithinAt f f' (Iio y) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
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
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `StrictConvexOn.secant_strict_mono`：StrictConvexOn.secant_strict_mono (hf
 : StrictConvexOn 𝕜 s f) {a x y : 𝕜} (ha : a in s) (hx : x in s) (hy : y in s) (
hxa : x != a) (hya : y …
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `slope_comm`：slope_comm (f : k -> PE) (a b : k) : slope f a b = slope f b
 a
· 使用引理 `ConvexOn.slope_le_of_hasDerivWithinAt_Iio`：slope_le_of_hasDerivWithinAt_
Iio (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : H
asDerivWithinAt f f' (Iio y) y)…
· 使用定理 `StrictConvexOn.convexOn`：StrictConvexOn.convexOn {s : Set E} {f : E -> β
} (hf : StrictConvexOn 𝕜 s f) : ConvexOn 𝕜 s f

--- 原说明 ---
If `f : ℝ → ℝ` is strictly convex on `S` and differentiable at `y ∈ S`, then the
 slope of any
secant line with right endpoint at `y` is strictly less than the left derivative
 at `y`.
-/
lemma slope_lt_of_hasDerivWithinAt_Iio (hfc : StrictConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    slope f x y < f' := by
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  have hu : u ∈ S := hfc.1.ordConnected.out hx hy ⟨hxu.le, huy.le⟩
  have := hfc.secant_strict_mono hy hx hu hxy.ne huy.ne hxu
  simp_rw [← slope_def_field, slope_comm _ y] at this
  exact this.trans_le <| hfc.convexOn.slope_le_of_hasDerivWithinAt_Iio hu hy huy hf'
/-
**StrictConvexOn.slope_lt_leftDeriv** 是 Mathlib 中的一个引理，位于命名空间 `StrictConvexOn`。
形式化陈述：slope_lt_leftDeriv (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y i
n S) (hxy : x < y) (hfd : DifferentiableWithinAt Real f (Iio y) y) : slope f x y
 < derivWithin f (Iio y) y
参数：hfc : StrictConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Diffe
rentiableWithinAt Real f (Iio y) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConvexOn.slope_lt_of_hasDerivWithinAt_Iio`：slope_lt_of_hasDerivWit
hinAt_Iio (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x <
 y) (hf' : HasDerivWithinAt f f' (Iio…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
lemma slope_lt_leftDeriv (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Iio y) y) :
    slope f x y < derivWithin f (Iio y) y :=
  hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable within `S` at `y ∈ S`, then the
slope of any secant line with right endpoint at `y` is strictly less than the derivative of `f`
within `S` at `y`.

This is fractionally weaker than `StrictConvexOn.slope_lt_of_hasDerivWithinAt_Iio` but simpler to
apply under a `DifferentiableOn S` hypothesis. -/
/-
**StrictConvexOn.slope_lt_of_hasDerivWithinAt** 是 Mathlib 中的一个引理，位于命名空间 `StrictC
onvexOn`。
形式化陈述：slope_lt_of_hasDerivWithinAt (hfc : StrictConvexOn Real S f) (hx : x in S)
 (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S y) : slope f x y < f
'
参数：hfc : StrictConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasDe
rivWithinAt f f' S y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `StrictConvexOn.slope_lt_of_hasDerivWithinAt_Iio`：slope_lt_of_hasDerivWit
hinAt_Iio (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x <
 y) (hf' : HasDerivWithinAt f f' (Iio…
· 使用定理 `HasDerivWithinAt.mono_of_mem_nhdsWithin`：HasDerivWithinAt.mono_of_mem_nh
dsWithin (h : HasDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) : HasDerivWithinAt 
f f' s x
· 使用引理 `Set.OrdConnected.mem_nhdsLT`：mem_nhdsLT (hS : OrdConnected S) (hx : x in
 S) (hy : y in S) (hxy : x < y) : S in 𝓝[<] y
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If `f : ℝ → ℝ` is strictly convex on `S` and differentiable within `S` at `y ∈ S
`, then the
slope of any secant line with right endpoint at `y` is strictly less than the de
rivative of `f`
within `S` at `y`.

This is fractionally weaker than `StrictConvexOn.slope_lt_of_hasDerivWithinAt_Ii
o` but simpler to
apply under a `DifferentiableOn S` hypothesis.
-/
lemma slope_lt_of_hasDerivWithinAt (hfc : StrictConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S y) :
    slope f x y < f' :=
  hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy <|
    hf'.mono_of_mem_nhdsWithin <| hfc.1.ordConnected.mem_nhdsLT hx hy hxy
/-
**StrictConvexOn.slope_lt_derivWithin** 是 Mathlib 中的一个引理，位于命名空间 `StrictConvexOn`
。
形式化陈述：slope_lt_derivWithin (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y
 in S) (hxy : x < y) (hfd : DifferentiableWithinAt Real f S y) : slope f x y < d
erivWithin f S y
参数：hfc : StrictConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Diffe
rentiableWithinAt Real f S y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConvexOn.slope_lt_of_hasDerivWithinAt`：slope_lt_of_hasDerivWithinA
t (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf'
 : HasDerivWithinAt f f' S y) : s…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
lemma slope_lt_derivWithin (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S y) :
    slope f x y < derivWithin f S y :=
  hfc.slope_lt_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable at `y ∈ S`, then the slope of any
secant line with right endpoint at `y` is strictly less than the derivative of `f` at `y`. -/
/-
**StrictConvexOn.slope_lt_of_hasDerivAt** 是 Mathlib 中的一个引理，位于命名空间 `StrictConvexO
n`。
形式化陈述：slope_lt_of_hasDerivAt (hfc : StrictConvexOn Real S f) (hx : x in S) (hy :
 y in S) (hxy : x < y) (hf' : HasDerivAt f f' y) : slope f x y < f'
参数：hfc : StrictConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasDe
rivAt f f' y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `StrictConvexOn.slope_lt_of_hasDerivWithinAt_Iio`：slope_lt_of_hasDerivWit
hinAt_Iio (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x <
 y) (hf' : HasDerivWithinAt f f' (Iio…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
If `f : ℝ → ℝ` is strictly convex on `S` and differentiable at `y ∈ S`, then the
 slope of any
secant line with right endpoint at `y` is strictly less than the derivative of `
f` at `y`.
-/
lemma slope_lt_of_hasDerivAt (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    slope f x y < f' :=
  hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt
/-
**StrictConvexOn.slope_lt_deriv** 是 Mathlib 中的一个引理，位于命名空间 `StrictConvexOn`。
形式化陈述：slope_lt_deriv (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S)
 (hxy : x < y) (hfd : DifferentiableAt Real f y) : slope f x y < deriv f y
参数：hfc : StrictConvexOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Diffe
rentiableAt Real f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConvexOn.slope_lt_of_hasDerivAt`：slope_lt_of_hasDerivAt (hfc : Str
ictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivA
t f f' y) : slope f x y < f…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
lemma slope_lt_deriv (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f y) :
    slope f x y < deriv f y :=
  hfc.slope_lt_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end right

/-!
### Strict convex functions, strict monotonicity of derivative
-/

/-- If `f` is convex on `S` and differentiable on `S`, then its derivative within `S` is monotone
on `S`. -/
/-
**StrictConvexOn.strictMonoOn_derivWithin** 是 Mathlib 中的一个引理，位于命名空间 `StrictConve
xOn`。
形式化陈述：strictMonoOn_derivWithin (hfc : StrictConvexOn Real S f) (hfd : Differenti
ableOn Real f S) : StrictMonoOn (derivWithin f S) S
参数：hfc : StrictConvexOn Real S f；hfd : DifferentiableOn Real f S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `StrictConvexOn.derivWithin_lt_slope`：derivWithin_lt_slope (hfc : StrictC
onvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hfd : Differentiabl
eWithinAt Real f S x) : d…
· 使用引理 `StrictConvexOn.slope_lt_derivWithin`：slope_lt_derivWithin (hfc : StrictC
onvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hfd : Differentiabl
eWithinAt Real f S y) : s…

--- 原说明 ---
If `f` is convex on `S` and differentiable on `S`, then its derivative within `S
` is monotone
on `S`.
-/
lemma strictMonoOn_derivWithin (hfc : StrictConvexOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
    StrictMonoOn (derivWithin f S) S := by
  intro x hx y hy hxy
  exact (hfc.derivWithin_lt_slope hx hy hxy (hfd x hx)).trans
    (hfc.slope_lt_derivWithin hx hy hxy (hfd y hy))

/-- If `f` is convex on `S` and differentiable at all points of `S`, then its derivative is monotone
on `S`. -/
/-
**StrictConvexOn.strictMonoOn_deriv** 是 Mathlib 中的一个引理，位于命名空间 `StrictConvexOn`。
形式化陈述：strictMonoOn_deriv (hfc : StrictConvexOn Real S f) (hfd : forall x in S, D
ifferentiableAt Real f x) : StrictMonoOn (deriv f) S
参数：hfc : StrictConvexOn Real S f；hfd : forall x in S, DifferentiableAt Real f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `StrictConvexOn.deriv_lt_slope`：deriv_lt_slope (hfc : StrictConvexOn Real
 S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hfd : DifferentiableAt Real f x
) : deriv f x < slo…
· 使用引理 `StrictConvexOn.slope_lt_deriv`：slope_lt_deriv (hfc : StrictConvexOn Real
 S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hfd : DifferentiableAt Real f y
) : slope f x y < d…

--- 原说明 ---
If `f` is convex on `S` and differentiable at all points of `S`, then its deriva
tive is monotone
on `S`.
-/
lemma strictMonoOn_deriv (hfc : StrictConvexOn ℝ S f) (hfd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    StrictMonoOn (deriv f) S := by
  intro x hx y hy hxy
  exact (hfc.deriv_lt_slope hx hy hxy (hfd x hx)).trans (hfc.slope_lt_deriv hx hy hxy (hfd y hy))

end StrictConvexOn

section MirrorImage

variable {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}

namespace ConcaveOn

section left
/-!
### Concave functions, derivative at left endpoint of secant
-/

/-
**ConcaveOn.slope_le_of_hasDerivWithinAt_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `ConcaveO
n`。
形式化陈述：slope_le_of_hasDerivWithinAt_Ioi (hfc : ConcaveOn Real S f) (hx : x in S) 
(hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) : slope f x 
y <= f'
参数：hfc : ConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasDerivWi
thinAt f f' (Ioi x) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `slope_neg`：∀ {k : Type u_1} {E : Type u_2} [inst : Field k] [inst_1 : Ad
dCommGroup E] [inst_2 : _root_.Module k E] (f : k → E)   (x y : k), slope (fun …
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a
· 使用引理 `ConvexOn.le_slope_of_hasDerivWithinAt_Ioi`：le_slope_of_hasDerivWithinAt_
Ioi (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : H
asDerivWithinAt f f' (Ioi x) x)…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `HasDerivWithinAt.neg`：HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s 
x) : HasDerivWithinAt (-f) (-f') s x

--- 原说明 ---
### Concave functions, derivative at left endpoint of secant
-/
lemma slope_le_of_hasDerivWithinAt_Ioi (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    slope f x y ≤ f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_le_neg (hfc.neg.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.neg)
/-
**ConcaveOn.slope_le_rightDeriv** 是 Mathlib 中的一个引理，位于命名空间 `ConcaveOn`。
形式化陈述：slope_le_rightDeriv (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S)
 (hxy : x < y) (hfd : DifferentiableWithinAt Real f (Ioi x) x) : slope f x y <= 
derivWithin f (Ioi x) x
参数：hfc : ConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Differenti
ableWithinAt Real f (Ioi x) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConcaveOn.slope_le_of_hasDerivWithinAt_Ioi`：slope_le_of_hasDerivWithinAt
_Ioi (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' :
 HasDerivWithinAt f f' (Ioi x) x…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
lemma slope_le_rightDeriv (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Ioi x) x) :
    slope f x y ≤ derivWithin f (Ioi x) x :=
  hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt
/-
**ConcaveOn.slope_le_of_hasDerivWithinAt** 是 Mathlib 中的一个引理，位于命名空间 `ConcaveOn`。
形式化陈述：slope_le_of_hasDerivWithinAt (hfc : ConcaveOn Real S f) (hx : x in S) (hy 
: y in S) (hxy : x < y) (hfd : HasDerivWithinAt f f' S x) : slope f x y <= f'
参数：hfc : ConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : HasDerivWi
thinAt f f' S x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ConcaveOn.slope_le_of_hasDerivWithinAt_Ioi`：slope_le_of_hasDerivWithinAt
_Ioi (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' :
 HasDerivWithinAt f f' (Ioi x) x…
· 使用定理 `HasDerivWithinAt.mono_of_mem_nhdsWithin`：HasDerivWithinAt.mono_of_mem_nh
dsWithin (h : HasDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) : HasDerivWithinAt 
f f' s x
· 使用引理 `Set.OrdConnected.mem_nhdsGT`：mem_nhdsGT (hS : OrdConnected S) (hx : x in
 S) (hy : y in S) (hxy : x < y) : S in 𝓝[>] x
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma slope_le_of_hasDerivWithinAt (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : HasDerivWithinAt f f' S x) :
    slope f x y ≤ f' :=
  hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy <|
    hfd.mono_of_mem_nhdsWithin <| hfc.1.ordConnected.mem_nhdsGT hx hy hxy
/-
**ConcaveOn.slope_le_derivWithin** 是 Mathlib 中的一个引理，位于命名空间 `ConcaveOn`。
形式化陈述：slope_le_derivWithin (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S
) (hxy : x < y) (hfd : DifferentiableWithinAt Real f S x) : slope f x y <= deriv
Within f S x
参数：hfc : ConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Differenti
ableWithinAt Real f S x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConcaveOn.slope_le_of_hasDerivWithinAt`：slope_le_of_hasDerivWithinAt (hf
c : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hfd : HasDeri
vWithinAt f f' S x) : slope …
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
lemma slope_le_derivWithin (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S x) :
    slope f x y ≤ derivWithin f S x :=
  hfc.slope_le_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt
/-
**ConcaveOn.slope_le_of_hasDerivAt** 是 Mathlib 中的一个引理，位于命名空间 `ConcaveOn`。
形式化陈述：slope_le_of_hasDerivAt (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in
 S) (hxy : x < y) (hf' : HasDerivAt f f' x) : slope f x y <= f'
参数：hfc : ConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasDerivAt
 f f' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ConcaveOn.slope_le_of_hasDerivWithinAt_Ioi`：slope_le_of_hasDerivWithinAt
_Ioi (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' :
 HasDerivWithinAt f f' (Ioi x) x…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
-/
lemma slope_le_of_hasDerivAt (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivAt f f' x) :
    slope f x y ≤ f' :=
  hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy hf'.hasDerivWithinAt
/-
**ConcaveOn.slope_le_deriv** 是 Mathlib 中的一个引理，位于命名空间 `ConcaveOn`。
形式化陈述：slope_le_deriv (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy
 : x < y) (hfd : DifferentiableAt Real f x) : slope f x y <= deriv f x
参数：hfc : ConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Differenti
ableAt Real f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConcaveOn.slope_le_of_hasDerivAt`：slope_le_of_hasDerivAt (hfc : ConcaveO
n Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivAt f f' x) 
: slope f x y <= f'
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
lemma slope_le_deriv (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hfd : DifferentiableAt ℝ f x) :
    slope f x y ≤ deriv f x :=
  hfc.slope_le_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end left

section right
/-!
### Concave functions, derivative at right endpoint of secant
-/

/-
**ConcaveOn.le_slope_of_hasDerivWithinAt_Iio** 是 Mathlib 中的一个引理，位于命名空间 `ConcaveO
n`。
形式化陈述：le_slope_of_hasDerivWithinAt_Iio (hfc : ConcaveOn Real S f) (hx : x in S) 
(hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) : f' <= slop
e f x y
参数：hfc : ConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasDerivWi
thinAt f f' (Iio y) y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `slope_neg`：∀ {k : Type u_1} {E : Type u_2} [inst : Field k] [inst_1 : Ad
dCommGroup E] [inst_2 : _root_.Module k E] (f : k → E)   (x y : k), slope (fun …
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a
· 使用引理 `ConvexOn.slope_le_of_hasDerivWithinAt_Iio`：slope_le_of_hasDerivWithinAt_
Iio (hfc : ConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : H
asDerivWithinAt f f' (Iio y) y)…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `HasDerivWithinAt.neg`：HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s 
x) : HasDerivWithinAt (-f) (-f') s x

--- 原说明 ---
### Concave functions, derivative at right endpoint of secant
-/
lemma le_slope_of_hasDerivWithinAt_Iio (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    f' ≤ slope f x y := by
  simpa only [neg_neg, Pi.neg_def, slope_neg] using
    neg_le_neg (hfc.neg.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hf'.neg)
/-
**ConcaveOn.leftDeriv_le_slope** 是 Mathlib 中的一个引理，位于命名空间 `ConcaveOn`。
形式化陈述：leftDeriv_le_slope (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) 
(hxy : x < y) (hfd : DifferentiableWithinAt Real f (Iio y) y) : derivWithin f (I
io y) y <= slope f x y
参数：hfc : ConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Differenti
ableWithinAt Real f (Iio y) y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConcaveOn.le_slope_of_hasDerivWithinAt_Iio`：le_slope_of_hasDerivWithinAt
_Iio (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' :
 HasDerivWithinAt f f' (Iio y) y…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
lemma leftDeriv_le_slope (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Iio y) y) :
    derivWithin f (Iio y) y ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt
/-
**ConcaveOn.le_slope_of_hasDerivWithinAt** 是 Mathlib 中的一个引理，位于命名空间 `ConcaveOn`。
形式化陈述：le_slope_of_hasDerivWithinAt (hfc : ConcaveOn Real S f) (hx : x in S) (hy 
: y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S y) : f' <= slope f x y
参数：hfc : ConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasDerivWi
thinAt f f' S y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ConcaveOn.le_slope_of_hasDerivWithinAt_Iio`：le_slope_of_hasDerivWithinAt
_Iio (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' :
 HasDerivWithinAt f f' (Iio y) y…
· 使用定理 `HasDerivWithinAt.mono_of_mem_nhdsWithin`：HasDerivWithinAt.mono_of_mem_nh
dsWithin (h : HasDerivWithinAt f f' t x) (hst : t in 𝓝[s] x) : HasDerivWithinAt 
f f' s x
· 使用引理 `Set.OrdConnected.mem_nhdsLT`：mem_nhdsLT (hS : OrdConnected S) (hx : x in
 S) (hy : y in S) (hxy : x < y) : S in 𝓝[<] y
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma le_slope_of_hasDerivWithinAt (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' S y) :
    f' ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy <|
    hf'.mono_of_mem_nhdsWithin <| hfc.1.ordConnected.mem_nhdsLT hx hy hxy
/-
**ConcaveOn.derivWithin_le_slope** 是 Mathlib 中的一个引理，位于命名空间 `ConcaveOn`。
形式化陈述：derivWithin_le_slope (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S
) (hxy : x < y) (hfd : DifferentiableWithinAt Real f S y) : derivWithin f S y <=
 slope f x y
参数：hfc : ConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Differenti
ableWithinAt Real f S y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConcaveOn.le_slope_of_hasDerivWithinAt`：le_slope_of_hasDerivWithinAt (hf
c : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDeri
vWithinAt f f' S y) : f' <= …
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
lemma derivWithin_le_slope (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S y) :
    derivWithin f S y ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt
/-
**ConcaveOn.le_slope_of_hasDerivAt** 是 Mathlib 中的一个引理，位于命名空间 `ConcaveOn`。
形式化陈述：le_slope_of_hasDerivAt (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in
 S) (hxy : x < y) (hf' : HasDerivAt f f' y) : f' <= slope f x y
参数：hfc : ConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasDerivAt
 f f' y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ConcaveOn.le_slope_of_hasDerivWithinAt_Iio`：le_slope_of_hasDerivWithinAt
_Iio (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' :
 HasDerivWithinAt f f' (Iio y) y…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
-/
lemma le_slope_of_hasDerivAt (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    f' ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt
/-
**ConcaveOn.deriv_le_slope** 是 Mathlib 中的一个引理，位于命名空间 `ConcaveOn`。
形式化陈述：deriv_le_slope (hfc : ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy
 : x < y) (hfd : DifferentiableAt Real f y) : deriv f y <= slope f x y
参数：hfc : ConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Differenti
ableAt Real f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConcaveOn.le_slope_of_hasDerivAt`：le_slope_of_hasDerivAt (hfc : ConcaveO
n Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivAt f f' y) 
: f' <= slope f x y
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
lemma deriv_le_slope (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f y) :
    deriv f y ≤ slope f x y :=
  hfc.le_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end right
/-!
### Concave functions, anti-monotonicity of derivative
-/

/-
**ConcaveOn.antitoneOn_derivWithin** 是 Mathlib 中的一个引理，位于命名空间 `ConcaveOn`。
形式化陈述：antitoneOn_derivWithin (hfc : ConcaveOn Real S f) (hfd : DifferentiableOn 
Real f S) : AntitoneOn (derivWithin f S) S
参数：hfc : ConcaveOn Real S f；hfd : DifferentiableOn Real f S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ConcaveOn.derivWithin_le_slope`：derivWithin_le_slope (hfc : ConcaveOn Re
al S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hfd : DifferentiableWithinAt 
Real f S y) : derivW…
· 使用引理 `ConcaveOn.slope_le_derivWithin`：slope_le_derivWithin (hfc : ConcaveOn Re
al S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hfd : DifferentiableWithinAt 
Real f S x) : slope …

--- 原说明 ---
### Concave functions, anti-monotonicity of derivative
-/
lemma antitoneOn_derivWithin (hfc : ConcaveOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
    AntitoneOn (derivWithin f S) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.derivWithin_le_slope hx hy hxy' (hfd y hy)).trans
    (hfc.slope_le_derivWithin hx hy hxy' (hfd x hx))

/-- If `f` is concave on `S` and differentiable at all points of `S`, then its derivative is
antitone (monotone decreasing) on `S`. -/
/-
**ConcaveOn.antitoneOn_deriv** 是 Mathlib 中的一个定理，位于命名空间 `ConcaveOn`。
形式化陈述：antitoneOn_deriv (hfc : ConcaveOn Real S f) (hfd : forall x in S, Differen
tiableAt Real f x) : AntitoneOn (deriv f) S
参数：hfc : ConcaveOn Real S f；hfd : forall x in S, DifferentiableAt Real f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv.neg'`：deriv.neg' : (deriv (-f)) = fun x => -deriv f x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `MonotoneOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_
1 : Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β 
→ α}…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ConvexOn.monotoneOn_deriv`：monotoneOn_deriv (hfc : ConvexOn Real S f) (h
fd : forall x in S, DifferentiableAt Real f x) : MonotoneOn (deriv f) S
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `DifferentiableAt.neg`：DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) 
: DifferentiableAt 𝕜 (-f) x

--- 原说明 ---
If `f` is concave on `S` and differentiable at all points of `S`, then its deriv
ative is
antitone (monotone decreasing) on `S`.
-/
theorem antitoneOn_deriv (hfc : ConcaveOn ℝ S f) (hfd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    AntitoneOn (deriv f) S := by
  simpa using (hfc.neg.monotoneOn_deriv (fun x hx ↦ (hfd x hx).neg)).neg

end ConcaveOn

namespace StrictConcaveOn

section left
/-!
### Strict concave functions, derivative at left endpoint of secant
-/

/-
**StrictConcaveOn.slope_lt_of_hasDerivWithinAt_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `St
rictConcaveOn`。
形式化陈述：slope_lt_of_hasDerivWithinAt_Ioi (hfc : StrictConcaveOn Real S f) (hx : x 
in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) : slop
e f x y < f'
参数：hfc : StrictConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasD
erivWithinAt f f' (Ioi x) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `slope_neg`：∀ {k : Type u_1} {E : Type u_2} [inst : Field k] [inst_1 : Ad
dCommGroup E] [inst_2 : _root_.Module k E] (f : k → E)   (x y : k), slope (fun …
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_lt_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a < b → -b < -a
· 使用引理 `StrictConvexOn.lt_slope_of_hasDerivWithinAt_Ioi`：lt_slope_of_hasDerivWit
hinAt_Ioi (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x <
 y) (hf' : HasDerivWithinAt f f' (Ioi…
· 使用定理 `StrictConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [ins
t : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 :
 AddCommG…
· 使用定理 `HasDerivWithinAt.neg`：HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s 
x) : HasDerivWithinAt (-f) (-f') s x

--- 原说明 ---
### Strict concave functions, derivative at left endpoint of secant
-/
lemma slope_lt_of_hasDerivWithinAt_Ioi (hfc : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    slope f x y < f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.neg)
/-
**StrictConcaveOn.slope_lt_rightDeriv** 是 Mathlib 中的一个引理，位于命名空间 `StrictConcaveOn
`。
形式化陈述：slope_lt_rightDeriv (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y
 in S) (hxy : x < y) (hfd : DifferentiableWithinAt Real f (Ioi x) x) : slope f x
 y < derivWithin f (Ioi x) x
参数：hfc : StrictConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Diff
erentiableWithinAt Real f (Ioi x) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConcaveOn.slope_lt_of_hasDerivWithinAt_Ioi`：slope_lt_of_hasDerivWi
thinAt_Ioi (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x
 < y) (hf' : HasDerivWithinAt f f' (Io…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
lemma slope_lt_rightDeriv (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Ioi x) x) :
    slope f x y < derivWithin f (Ioi x) x :=
  hfc.slope_lt_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt
/-
**StrictConcaveOn.slope_lt_of_hasDerivWithinAt** 是 Mathlib 中的一个引理，位于命名空间 `Strict
ConcaveOn`。
形式化陈述：slope_lt_of_hasDerivWithinAt (hfc : StrictConcaveOn Real S f) (hx : x in S
) (hy : y in S) (hxy : x < y) (hfd : HasDerivWithinAt f f' S x) : slope f x y < 
f'
参数：hfc : StrictConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : HasD
erivWithinAt f f' S x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `slope_neg`：∀ {k : Type u_1} {E : Type u_2} [inst : Field k] [inst_1 : Ad
dCommGroup E] [inst_2 : _root_.Module k E] (f : k → E)   (x y : k), slope (fun …
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_lt_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a < b → -b < -a
· 使用引理 `StrictConvexOn.lt_slope_of_hasDerivWithinAt`：lt_slope_of_hasDerivWithinA
t (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf'
 : HasDerivWithinAt f f' S x) : f…
· 使用定理 `StrictConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [ins
t : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 :
 AddCommG…
· 使用定理 `HasDerivWithinAt.neg`：HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s 
x) : HasDerivWithinAt (-f) (-f') s x
-/
lemma slope_lt_of_hasDerivWithinAt (hfc : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hfd : HasDerivWithinAt f f' S x) :
    slope f x y < f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.neg)
/-
**StrictConcaveOn.slope_lt_derivWithin** 是 Mathlib 中的一个引理，位于命名空间 `StrictConcaveO
n`。
形式化陈述：slope_lt_derivWithin (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : 
y in S) (hxy : x < y) (hfd : DifferentiableWithinAt Real f S x) : slope f x y < 
derivWithin f S x
参数：hfc : StrictConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Diff
erentiableWithinAt Real f S x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConcaveOn.slope_lt_of_hasDerivWithinAt`：slope_lt_of_hasDerivWithin
At (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (h
fd : HasDerivWithinAt f f' S x) : …
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
lemma slope_lt_derivWithin (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S x) :
    slope f x y < derivWithin f S x :=
  hfc.slope_lt_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt
/-
**StrictConcaveOn.slope_lt_of_hasDerivAt** 是 Mathlib 中的一个引理，位于命名空间 `StrictConcav
eOn`。
形式化陈述：slope_lt_of_hasDerivAt (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy 
: y in S) (hxy : x < y) (hfd : HasDerivAt f f' x) : slope f x y < f'
参数：hfc : StrictConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : HasD
erivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `slope_neg`：∀ {k : Type u_1} {E : Type u_2} [inst : Field k] [inst_1 : Ad
dCommGroup E] [inst_2 : _root_.Module k E] (f : k → E)   (x y : k), slope (fun …
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_lt_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a < b → -b < -a
· 使用引理 `StrictConvexOn.lt_slope_of_hasDerivAt`：lt_slope_of_hasDerivAt (hfc : Str
ictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivA
t f f' x) : f' < slope f x …
· 使用定理 `StrictConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [ins
t : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 :
 AddCommG…
· 使用定理 `HasDerivAt.neg`：HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (-f)
 (-f') x
-/
lemma slope_lt_of_hasDerivAt (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : HasDerivAt f f' x) :
    slope f x y < f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivAt hx hy hxy hfd.neg)
/-
**StrictConcaveOn.slope_lt_deriv** 是 Mathlib 中的一个引理，位于命名空间 `StrictConcaveOn`。
形式化陈述：slope_lt_deriv (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S
) (hxy : x < y) (hfd : DifferentiableAt Real f x) : slope f x y < deriv f x
参数：hfc : StrictConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Diff
erentiableAt Real f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConcaveOn.slope_lt_of_hasDerivAt`：slope_lt_of_hasDerivAt (hfc : St
rictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hfd : HasDeri
vAt f f' x) : slope f x y < …
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
lemma slope_lt_deriv (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f x) :
    slope f x y < deriv f x :=
  hfc.slope_lt_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end left

section right
/-!
### Strict concave functions, derivative at right endpoint of secant
-/

/-
**StrictConcaveOn.lt_slope_of_hasDerivWithinAt_Iio** 是 Mathlib 中的一个引理，位于命名空间 `St
rictConcaveOn`。
形式化陈述：lt_slope_of_hasDerivWithinAt_Iio (hfc : StrictConcaveOn Real S f) (hx : x 
in S) (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) : f' <
 slope f x y
参数：hfc : StrictConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasD
erivWithinAt f f' (Iio y) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `slope_neg`：∀ {k : Type u_1} {E : Type u_2} [inst : Field k] [inst_1 : Ad
dCommGroup E] [inst_2 : _root_.Module k E] (f : k → E)   (x y : k), slope (fun …
· 使用定理 `neg_lt_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a < b → -b < -a
· 使用引理 `StrictConvexOn.slope_lt_of_hasDerivWithinAt_Iio`：slope_lt_of_hasDerivWit
hinAt_Iio (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x <
 y) (hf' : HasDerivWithinAt f f' (Iio…
· 使用定理 `StrictConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [ins
t : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 :
 AddCommG…
· 使用定理 `HasDerivWithinAt.neg`：HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s 
x) : HasDerivWithinAt (-f) (-f') s x

--- 原说明 ---
### Strict concave functions, derivative at right endpoint of secant
-/
lemma lt_slope_of_hasDerivWithinAt_Iio (hfc : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    f' < slope f x y := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hf'.neg)
/-
**StrictConcaveOn.leftDeriv_lt_slope** 是 Mathlib 中的一个引理，位于命名空间 `StrictConcaveOn`
。
形式化陈述：leftDeriv_lt_slope (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y 
in S) (hxy : x < y) (hfd : DifferentiableWithinAt Real f (Iio y) y) : derivWithi
n f (Iio y) y < slope f x y
参数：hfc : StrictConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Diff
erentiableWithinAt Real f (Iio y) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConcaveOn.lt_slope_of_hasDerivWithinAt_Iio`：lt_slope_of_hasDerivWi
thinAt_Iio (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x
 < y) (hf' : HasDerivWithinAt f f' (Ii…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
lemma leftDeriv_lt_slope (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Iio y) y) :
    derivWithin f (Iio y) y < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt
/-
**StrictConcaveOn.lt_slope_of_hasDerivWithinAt** 是 Mathlib 中的一个引理，位于命名空间 `Strict
ConcaveOn`。
形式化陈述：lt_slope_of_hasDerivWithinAt (hfc : StrictConcaveOn Real S f) (hx : x in S
) (hy : y in S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S y) : f' < slope f x
 y
参数：hfc : StrictConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasD
erivWithinAt f f' S y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `slope_neg`：∀ {k : Type u_1} {E : Type u_2} [inst : Field k] [inst_1 : Ad
dCommGroup E] [inst_2 : _root_.Module k E] (f : k → E)   (x y : k), slope (fun …
· 使用定理 `neg_lt_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a < b → -b < -a
· 使用引理 `StrictConvexOn.slope_lt_of_hasDerivWithinAt`：slope_lt_of_hasDerivWithinA
t (hfc : StrictConvexOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf'
 : HasDerivWithinAt f f' S y) : s…
· 使用定理 `StrictConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [ins
t : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 :
 AddCommG…
· 使用定理 `HasDerivWithinAt.neg`：HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s 
x) : HasDerivWithinAt (-f) (-f') s x
-/
lemma lt_slope_of_hasDerivWithinAt (hfc : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S y) :
    f' < slope f x y := by
  simpa only [neg_neg, Pi.neg_def, slope_neg] using
    neg_lt_neg (hfc.neg.slope_lt_of_hasDerivWithinAt hx hy hxy hf'.neg)
/-
**StrictConcaveOn.derivWithin_lt_slope** 是 Mathlib 中的一个引理，位于命名空间 `StrictConcaveO
n`。
形式化陈述：derivWithin_lt_slope (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : 
y in S) (hxy : x < y) (hfd : DifferentiableWithinAt Real f S y) : derivWithin f 
S y < slope f x y
参数：hfc : StrictConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Diff
erentiableWithinAt Real f S y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConcaveOn.lt_slope_of_hasDerivWithinAt`：lt_slope_of_hasDerivWithin
At (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (h
f' : HasDerivWithinAt f f' S y) : …
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
lemma derivWithin_lt_slope (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S y) :
    derivWithin f S y < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt
/-
**StrictConcaveOn.lt_slope_of_hasDerivAt** 是 Mathlib 中的一个引理，位于命名空间 `StrictConcav
eOn`。
形式化陈述：lt_slope_of_hasDerivAt (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy 
: y in S) (hxy : x < y) (hf' : HasDerivAt f f' y) : f' < slope f x y
参数：hfc : StrictConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hf' : HasD
erivAt f f' y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `StrictConcaveOn.lt_slope_of_hasDerivWithinAt_Iio`：lt_slope_of_hasDerivWi
thinAt_Iio (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x
 < y) (hf' : HasDerivWithinAt f f' (Ii…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
-/
lemma lt_slope_of_hasDerivAt (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    f' < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt
/-
**StrictConcaveOn.deriv_lt_slope** 是 Mathlib 中的一个引理，位于命名空间 `StrictConcaveOn`。
形式化陈述：deriv_lt_slope (hfc : StrictConcaveOn Real S f) (hx : x in S) (hy : y in S
) (hxy : x < y) (hfd : DifferentiableAt Real f y) : deriv f y < slope f x y
参数：hfc : StrictConcaveOn Real S f；hx : x in S；hy : y in S；hxy : x < y；hfd : Diff
erentiableAt Real f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConcaveOn.lt_slope_of_hasDerivAt`：lt_slope_of_hasDerivAt (hfc : St
rictConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hf' : HasDeri
vAt f f' y) : f' < slope f x…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
lemma deriv_lt_slope (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f y) :
    deriv f y < slope f x y :=
  hfc.lt_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end right
/-!
### Strict concave functions, anti-monotonicity of derivative
-/

/-
**StrictConcaveOn.strictAntiOn_derivWithin** 是 Mathlib 中的一个引理，位于命名空间 `StrictConc
aveOn`。
形式化陈述：strictAntiOn_derivWithin (hfc : StrictConcaveOn Real S f) (hfd : Different
iableOn Real f S) : StrictAntiOn (derivWithin f S) S
参数：hfc : StrictConcaveOn Real S f；hfd : DifferentiableOn Real f S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `StrictConcaveOn.derivWithin_lt_slope`：derivWithin_lt_slope (hfc : Strict
ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hfd : Differentia
bleWithinAt Real f S y) : …
· 使用引理 `StrictConcaveOn.slope_lt_derivWithin`：slope_lt_derivWithin (hfc : Strict
ConcaveOn Real S f) (hx : x in S) (hy : y in S) (hxy : x < y) (hfd : Differentia
bleWithinAt Real f S x) : …

--- 原说明 ---
### Strict concave functions, anti-monotonicity of derivative
-/
lemma strictAntiOn_derivWithin (hfc : StrictConcaveOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
    StrictAntiOn (derivWithin f S) S := by
  intro x hx y hy hxy
  exact (hfc.derivWithin_lt_slope hx hy hxy (hfd y hy)).trans
    (hfc.slope_lt_derivWithin hx hy hxy (hfd x hx))
/-
**StrictConcaveOn.strictAntiOn_deriv** 是 Mathlib 中的一个定理，位于命名空间 `StrictConcaveOn`
。
形式化陈述：strictAntiOn_deriv (hfc : StrictConcaveOn Real S f) (hfd : forall x in S, 
DifferentiableAt Real f x) : StrictAntiOn (deriv f) S
参数：hfc : StrictConcaveOn Real S f；hfd : forall x in S, DifferentiableAt Real f x
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv.neg'`：deriv.neg' : (deriv (-f)) = fun x => -deriv f x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `StrictMonoOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [ins
t_1 : Preorder α] [AddLeftStrictMono α] [AddRightStrictMono α]   [inst_4 : Preor
der β]…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `StrictConvexOn.strictMonoOn_deriv`：strictMonoOn_deriv (hfc : StrictConve
xOn Real S f) (hfd : forall x in S, DifferentiableAt Real f x) : StrictMonoOn (d
eriv f) S
· 使用定理 `StrictConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [ins
t : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 :
 AddCommG…
· 使用定理 `DifferentiableAt.neg`：DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) 
: DifferentiableAt 𝕜 (-f) x
-/
theorem strictAntiOn_deriv (hfc : StrictConcaveOn ℝ S f) (hfd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    StrictAntiOn (deriv f) S := by
  simpa using (hfc.neg.strictMonoOn_deriv (fun x hx ↦ (hfd x hx).neg)).neg

end StrictConcaveOn

end MirrorImage

