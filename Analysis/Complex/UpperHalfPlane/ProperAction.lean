/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated

/-!
# Transitivity and properness of actions

We show that the actions of `SL(2, ℝ)` and `GL(2, ℝ)` on the upper half-plane are jointly
continuous, and the action of `SL(2, ℝ)` is proper. (These results require more imports
than in `UpperHalfPlane.Topology`, because they use the topology on the group as well)

TODO: Show properness of the action of `PGL(2, ℝ)` once this is defined.
-/

open scoped MatrixGroups Pointwise

public section

namespace UpperHalfPlane

@[fun_prop]
/-
**UpperHalfPlane.num_continuous** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：num_continuous : Continuous ↿num
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
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
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Matrix.GeneralLinearGroup.continuous_apply`：continuous_apply {α : Type*}
 [TopologicalSpace α] (f : α -> GL n R) (hf : Continuous f) (i : n) : Continuous
 (fun x => f x i)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
theorem num_continuous : Continuous ↿num := by unfold num; fun_prop

@[fun_prop]
/-
**UpperHalfPlane.denom_continuous** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：denom_continuous : Continuous ↿denom
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
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
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Matrix.GeneralLinearGroup.continuous_apply`：continuous_apply {α : Type*}
 [TopologicalSpace α] (f : α -> GL n R) (hf : Continuous f) (i : n) : Continuous
 (fun x => f x i)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
theorem denom_continuous : Continuous ↿denom := by unfold denom; fun_prop

set_option backward.isDefEq.respectTransparency.types false in
/-
**UpperHalfPlane.continuous_toSL2R** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：continuous_toSL2R : Continuous toSL2R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UpperHalfPlane.coe_toSL2R`：∀ (z : UpperHalfPlane), ↑z.toSL2R = !![√z.im,
 z.re / √z.im; 0, 1 / √z.im]
· 使用定理 `Continuous.matrixOf`：∀ {α : Type u_2} {m : Type u_4} {n : Type u_5} {R :
 Type u_8} [inst : TopologicalSpace R] [inst_1 : TopologicalSpace α]   {f : α → 
m → n → R…
· 使用定理 `Continuous.matrixVecCons`：Continuous.matrixVecCons {f : X -> Z} {g : X -
> Fin n -> Z} (hf : Continuous f) (hg : Continuous g) : Continuous fun a => Matr
ix.vecCons (f …
· 使用定理 `Continuous.sqrt`：Continuous.sqrt (h : Continuous f) : Continuous fun x =
> √(f x)
· 使用定理 `UpperHalfPlane.continuous_im`：continuous_im : Continuous im
· 使用定理 `Continuous.div₀`：Continuous.div₀ (hf : Continuous f) (hg : Continuous g)
 (h₀ : forall x, g x != 0) : Continuous (fun x => f x / g x)
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `UpperHalfPlane.continuous_re`：continuous_re : Continuous re
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
lemma continuous_toSL2R : Continuous toSL2R := by
  apply continuous_induced_rng.mpr
  simp only [Function.comp_def, coe_toSL2R]
  fun_prop (disch := grind [im_pos])

/-- The action of `SL(2, ℝ)` on `ℍ` is jointly continuous. -/
/-
**UpperHalfPlane.instContinuousSMulSL2R** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlan
e`。
形式化陈述：instContinuousSMulSL2R : ContinuousSMul SL(2, Real) ℍ where continuous_smu
l
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContinuousAt.div₀`：ContinuousAt.div₀ (hf : ContinuousAt f a) (hg : Conti
nuousAt g a) (h₀ : g a != 0) : ContinuousAt (fun x => f x / g x) a
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `ContinuousAt.fun_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f 
g : X → M}…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `ContinuousAt.fun_mul`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Mul M] [ContinuousMul M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f 
g : X → M}…
· 使用定理 `ContinuousAt.comp'`：ContinuousAt.comp' {g : Y -> Z} {x : X} (hg : Contin
uousAt g (f x)) (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Matrix.SpecialLinearGroup.continuous_apply`：continuous_apply {α : Type*}
 [TopologicalSpace α] (f : α -> SL n R) (hf : Continuous f) (i) : Continuous (fu
n x => f x i)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `UpperHalfPlane.continuous_coe`：continuous_coe : Continuous ((↑) : ℍ -> C
omplex)
· 使用定理 `ContinuousAt.snd`：ContinuousAt.snd {f : X -> Y × Z} {x : X} (hf : Contin
uousAt f x) : ContinuousAt (fun x : X => (f x).2) x
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `UpperHalfPlane.denom_ne_zero`：denom_ne_zero (g : GL (Fin 2) Real) (z : ℍ
) : denom g z != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UpperHalfPlane.coe_specialLinearGroup_apply`：coe_specialLinearGroup_appl
y {R : Type*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ) : ↑(g • z) = 
(((algebraMap R Real (g 0 0) : Co…

--- 原说明 ---
The action of `SL(2, ℝ)` on `ℍ` is jointly continuous.
-/
instance instContinuousSMulSL2R : ContinuousSMul SL(2, ℝ) ℍ where
  continuous_smul := by
    suffices ∀ (g : SL(2, ℝ)) (τ : ℍ),
        ContinuousAt (fun ⟨h, z⟩ ↦ (h 0 0 * (z : ℂ) + h 0 1) / (h 1 0 * z + h 1 1)) (g, τ) by
      simpa [continuous_induced_rng, continuous_iff_continuousAt, Function.comp_def,
        coe_specialLinearGroup_apply]
    intro g τ
    fun_prop (disch := exact denom_ne_zero g τ)

open Topology in
/-
**UpperHalfPlane.** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_eventuallyEq (g : GL (Fin 2) ℝ) : σ =ᶠ[𝓝 g] fun _ ↦ σ g := by
  by_cases hg : 0 < g.det.val
  · suffices {h | 0 < h.det.val} ∈ 𝓝 g by
      filter_upwards [this] with h hh using by simp only [σ, hh, ↓reduceIte, hg]
    exact isOpen_Ioi (a := (0 : ℝ)) |>.preimage (by fun_prop) |>.mem_nhds hg
  · suffices {h | ¬0 < h.det.val} ∈ 𝓝 g by
      filter_upwards [this] with h hh using by simp only [σ, hh, ↓reduceIte, hg]
    simp only [not_lt, le_iff_lt_or_eq, Units.ne_zero, or_false] at hg ⊢
    exact isOpen_Iio (a := (0 : ℝ)) |>.preimage (by fun_prop) |>.mem_nhds hg

/-- The action of `GL(2, ℝ)` on `ℍ` is jointly continuous. -/
/-
**UpperHalfPlane.instContinuousSMulGL2R** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlan
e`。
形式化陈述：instContinuousSMulGL2R : ContinuousSMul (GL (Fin 2) Real) ℍ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousAt.congr`：ContinuousAt.congr {g : X -> Y} (hf : ContinuousAt f
 x) (h : f =ᶠ[𝓝 x] g) : ContinuousAt g x
· 使用定理 `ContinuousAt.comp'`：ContinuousAt.comp' {g : Y -> Z} {x : X} (hg : Contin
uousAt g (f x)) (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousAlgEquiv.continuous`：continuous (e : A ≃A[R] B) : Continuous e
· 使用定理 `ContinuousAt.div₀`：ContinuousAt.div₀ (hf : ContinuousAt f a) (hg : Conti
nuousAt g a) (h₀ : g a != 0) : ContinuousAt (fun x => f x / g x) a
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `UpperHalfPlane.num_continuous`：num_continuous : Continuous ↿num
· 使用定理 `ContinuousAt.prodMk`：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : 
X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x
, g x)) x
· 使用定理 `ContinuousAt.fst`：ContinuousAt.fst {f : X -> Y × Z} {x : X} (hf : Contin
uousAt f x) : ContinuousAt (fun x : X => (f x).1) x
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `UpperHalfPlane.continuous_coe`：continuous_coe : Continuous ((↑) : ℍ -> C
omplex)
· 使用定理 `ContinuousAt.snd`：ContinuousAt.snd {f : X -> Y × Z} {x : X} (hf : Contin
uousAt f x) : ContinuousAt (fun x : X => (f x).2) x
· 使用定理 `UpperHalfPlane.denom_continuous`：denom_continuous : Continuous ↿denom
· 使用定理 `UpperHalfPlane.denom_ne_zero`：denom_ne_zero (g : GL (Fin 2) Real) (z : ℍ
) : denom g z != 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Eventually.prod_inl_nhds`：Filter.Eventually.prod_inl_nhds {p : X 
-> Prop} {x : X} (h : forallᶠ x in 𝓝 x, p x) (y : Y) : forallᶠ x in 𝓝 (x, y), p 
(x : X × Y).1
· 使用引理 `UpperHalfPlane.σ_eventuallyEq`：σ_eventuallyEq (g : GL (Fin 2) Real) : σ 
=ᶠ[𝓝 g] fun _ => σ g
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The action of `GL(2, ℝ)` on `ℍ` is jointly continuous.
-/
instance instContinuousSMulGL2R : ContinuousSMul (GL (Fin 2) ℝ) ℍ := by
  constructor
  simp only [continuous_induced_rng, Function.comp_def, coe_smul, continuous_iff_continuousAt,
    Prod.forall]
  refine fun g τ ↦ .congr ?_ (f := fun x ↦ (σ g) (num x.1 x.2 / denom x.1 x.2))
    (by filter_upwards [(σ_eventuallyEq g).prod_inl_nhds _] using by simp +contextual)
  fun_prop (disch := apply denom_ne_zero)

section proper_orbit_map

/-- Preliminary lemma for compactness of the orbit map. -/
/-
**UpperHalfPlane.cdsq_le** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preliminary lemma for compactness of the orbit map.
-/
private lemma cdsq_le {K : Set ℍ} (hK : IsCompact K) :
    ∃ A, ∀ g : SL(2, ℝ), g • I ∈ K → g 1 0 ^ 2 + g 1 1 ^ 2 ≤ A := by
  rcases K.eq_empty_or_nonempty with rfl | hKne; · simp
  obtain ⟨δ, hδ, hδK⟩ : ∃ δ > 0, ∀ z ∈ K, δ ≤ z.im :=
    match hK.exists_isMinOn hKne continuous_im.continuousOn with | ⟨z, _, h⟩ => ⟨_, z.im_pos, h⟩
  refine ⟨1 / δ, fun g hg ↦ ?_⟩
  specialize hδK (g • I) hg
  simp only [MulAction.compHom_smul_def, im_smul_eq_div_normSq, Matrix.SpecialLinearGroup.det_mapGL,
    Units.val_one, abs_one, I_im, mul_one] at hδK
  rw [le_div_iff₀ (normSq_denom_pos (Matrix.SpecialLinearGroup.mapGL ℝ g) (show I.im ≠ 0 by simp)),
    mul_comm, ← le_div_iff₀ hδ] at hδK
  simpa [Complex.normSq, add_comm, denom, sq] using hδK

/-- Preliminary lemma for compactness of the orbit map. -/
/-
**UpperHalfPlane.absq_le** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preliminary lemma for compactness of the orbit map.
-/
private lemma absq_le {K : Set ℍ} (hK : IsCompact K) :
    ∃ A : ℝ, ∀ g : SL(2, ℝ), g • I ∈ K → g 0 0 ^ 2 + g 0 1 ^ 2 ≤ A := by
  let S : SL(2, ℝ) := ⟨!![0, -1; 1, 0], by simp⟩
  obtain ⟨A, hA⟩ := cdsq_le (K := S • K) (hK.image <| continuous_const_smul S)
  refine ⟨A, fun g hg ↦ ?_⟩
  convert! hA (S * g) (by rwa [mul_smul, Set.smul_mem_smul_set_iff]) using 1
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.eta_fin_two g.val, Matrix.mul_fin_two]
  simp

/-- The orbit map `g ↦ g • I` is a proper map `SL(2, ℝ) → ℍ`. -/
/-
**UpperHalfPlane.isProperMap_smul_I** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：isProperMap_smul_I : IsProperMap fun g : SL(2, Real) => g • I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isProperMap_iff_isCompact_preimage`：isProperMap_iff_isCompact_preimage :
 IsProperMap f ↔ Continuous f ∧ forall ⦃K⦄, IsCompact K -> IsCompact (f ⁻¹' K) w
here mp hf
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `UpperHalfPlane.instT3Space`：T3Space UpperHalfPlane
· 使用定理 `instCompactlyGeneratedSpaceOfWeaklyLocallyCompactSpace`：∀ {X : Type u} [
inst : TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X], CompactlyG
eneratedSpace X
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `UpperHalfPlane.instLocallyCompactSpace`：LocallyCompactSpace UpperHalfPla
ne
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `_private.Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction.0.UpperHal
fPlane.absq_le`：∀ {K : Set UpperHalfPlane},   IsCompact K → ∃ A, ∀ (g : Matrix.S
pecialLinearGroup (Fin 2) ℝ), g • UpperHalfPlane.I ∈ K → ↑g 0 0 ^ 2 + ↑g 0 1…
· 使用定理 `_private.Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction.0.UpperHal
fPlane.cdsq_le`：∀ {K : Set UpperHalfPlane},   IsCompact K → ∃ A, ∀ (g : Matrix.S
pecialLinearGroup (Fin 2) ℝ), g • UpperHalfPlane.I ∈ K → ↑g 1 0 ^ 2 + ↑g 1 1…
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `Topology.IsClosedEmbedding.isCompact_preimage`：Topology.IsClosedEmbeddin
g.isCompact_preimage (hf : IsClosedEmbedding f) {K : Set Y} (hK : IsCompact K) :
 IsCompact (f ⁻¹' K)
· 使用引理 `Matrix.SpecialLinearGroup.isClosedEmbedding_val`：isClosedEmbedding_val [
T1Space R] : IsClosedEmbedding ((↑) : SL n R -> Matrix n n R)
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
The orbit map `g ↦ g • I` is a proper map `SL(2, ℝ) → ℍ`.
-/
lemma isProperMap_smul_I : IsProperMap fun g : SL(2, ℝ) ↦ g • I := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨by fun_prop, fun K hK ↦ ?_⟩
  obtain ⟨A, hA⟩ := absq_le hK
  obtain ⟨A', hA'⟩ := cdsq_le hK
  -- activate the sup-norm on matrices
  let : SeminormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℝ) := Matrix.seminormedAddCommGroup
  have : ProperSpace (Matrix (Fin 2) (Fin 2) ℝ) := pi_properSpace
  have : IsCompact {m : Matrix (Fin 2) (Fin 2) ℝ | ∀ i j, |m i j| ≤ max √A √A'} := by
    convert! ProperSpace.isCompact_closedBall (0 : Matrix (Fin 2) (Fin 2) ℝ) (max √A √A')
    simp only [le_sup_iff, Fin.forall_fin_two, Fin.isValue, Metric.closedBall, dist_zero_right,
      Matrix.norm_def, pi_norm_le_iff_of_nonempty, Real.norm_eq_abs]
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `ext` was not necessary.
    The cause of this might be `Matrix` function application defeq abuse. -/
    ext; grind
  have := Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage this
  refine this.of_isClosed_subset (hK.isClosed.preimage <| by fun_prop) (fun g hg ↦ ?_)
  intro i j
  fin_cases i
  · refine le_trans ?_ <| le_max_left √A √A'
    exact Real.le_sqrt_of_sq_le <| le_trans (by fin_cases j <;> simp [sq_nonneg]) (hA g hg)
  · refine le_trans ?_ <| le_max_right √A √A'
    exact Real.le_sqrt_of_sq_le <| le_trans (by fin_cases j <;> simp [sq_nonneg]) (hA' g hg)
/-
**UpperHalfPlane.instProperSMul** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
形式化陈述：instProperSMul : ProperSMul SL(2, Real) ℍ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.properSMul_of_proper_orbitMap`：MulAction.properSMul_of_proper_
orbitMap [ContinuousSMul G X] [IsTopologicalGroup G] [MulAction.IsPretransitive 
G X] {x : X} (hx : IsProperMa…
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `UpperHalfPlane.isProperMap_smul_I`：isProperMap_smul_I : IsProperMap fun 
g : SL(2, Real) => g • I
-/
instance instProperSMul : ProperSMul SL(2, ℝ) ℍ :=
  MulAction.properSMul_of_proper_orbitMap isProperMap_smul_I

end proper_orbit_map

/-- Any discrete subgroup of `SL(2, ℝ)` acts properly discontinuously on `ℍ`. -/
/-
**UpperHalfPlane.instProperlyDiscontinuousSL2RSubgroup** 是 Mathlib 中的一个实例，位于命名空间
 `UpperHalfPlane`。
形式化陈述：instProperlyDiscontinuousSL2RSubgroup (𝒢 : Subgroup SL(2, Real)) [Discrete
Topology 𝒢] : ProperlyDiscontinuousSMul 𝒢 ℍ
参数：𝒢 : Subgroup SL(2, Real)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `properlyDiscontinuousSMul_iff_properSMul`：properlyDiscontinuousSMul_iff_
properSMul [DiscreteTopology G] [ContinuousConstSMul G X] : ProperlyDiscontinuou
sSMul G X ↔ ProperSMul G X
· 使用定理 `UpperHalfPlane.instT3Space`：T3Space UpperHalfPlane
· 使用定理 `instCompactlyGeneratedSpaceOfWeaklyLocallyCompactSpace`：∀ {X : Type u} [
inst : TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X], CompactlyG
eneratedSpace X
· 使用定理 `instWeaklyLocallyCompactSpaceProd`：∀ {X : Type u_1} {Y : Type u_2} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [WeaklyLocallyCompactSpace 
X]   [WeaklyLocallyComp…
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `UpperHalfPlane.instLocallyCompactSpace`：LocallyCompactSpace UpperHalfPla
ne
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `instProperSMulSubtypeMemSubgroupOfIsClosedCoe`：∀ {G : Type u_1} {X : Typ
e u_2} [inst : Group G] [inst_1 : MulAction G X] [inst_2 : TopologicalSpace G]  
 [inst_3 : TopologicalSpace X] {H :…

--- 原说明 ---
Any discrete subgroup of `SL(2, ℝ)` acts properly discontinuously on `ℍ`.
-/
instance instProperlyDiscontinuousSL2RSubgroup (𝒢 : Subgroup SL(2, ℝ)) [DiscreteTopology 𝒢] :
    ProperlyDiscontinuousSMul 𝒢 ℍ := by
  have : IsClosed (𝒢 : Set SL(2, ℝ)) := Subgroup.isClosed_of_discrete
  rw [properlyDiscontinuousSMul_iff_properSMul]
  infer_instance

end UpperHalfPlane

end

