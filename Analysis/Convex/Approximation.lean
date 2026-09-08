/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Semicontinuity.Lindelof

/-!
# Approximation to convex functions

In this file we show that a convex lower-semicontinuous function is the upper envelope of a family
of continuous affine linear functions. We follow the proof in
[N. Bourbaki, *Topological vector spaces*, Chapter II, §5][bourbaki1987].

## Main Statement

* `sSup_affine_eq` : A function `φ : E → ℝ` that is convex and lower-semicontinuous on a closed
  convex subset `s` is the supremum of a family of functions that are the restrictions to `s` of
  continuous affine linear functions.
* `sSup_of_countable_affine_eq` : Suppose `E` is a `HereditarilyLindelofSpace`. A function
  `φ : E → ℝ` that is convex and lower-semicontinuous on a closed convex subset `s` is the supremum
  of a family of countably many functions that are the restrictions to `s` of continuous affine
  linear functions.

-/

public section

open Function Set RCLike ContinuousLinearMap

namespace ConvexOn

variable {𝕜 E F : Type*} {s : Set E} {φ : E → ℝ} [RCLike 𝕜]

/-
**ConvexOn.convex_re_epigraph** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`。
形式化陈述：convex_re_epigraph [AddCommMonoid E] [Module Real E] (hφcv : ConvexOn Real
 s φ) : Convex Real { p : E × 𝕜 | p.1 in s ∧ φ p.1 <= re p.2 }
参数：hφcv : ConvexOn Real s φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Convex.linear_preimage`：Convex.linear_preimage {s : Set F} (hs : Convex 
𝕜 s) (f : E ->ₗ[𝕜] F) : Convex 𝕜 (f ⁻¹' s)
· 使用定理 `ConvexOn.convex_epigraph`：ConvexOn.convex_epigraph (hf : ConvexOn 𝕜 s f)
 : Convex 𝕜 { p : E × β | p.1 in s ∧ f p.1 <= p.2 }
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem convex_re_epigraph [AddCommMonoid E] [Module ℝ E] (hφcv : ConvexOn ℝ s φ) :
    Convex ℝ { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 } := by
  have lem : { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 } =
    ((LinearMap.id : E →ₗ[ℝ] E).prodMap reLm) ⁻¹' { p : E × ℝ | p.1 ∈ s ∧ φ p.1 ≤ p.2 } := by simp
  exact lem ▸ hφcv.convex_epigraph.linear_preimage _

variable [TopologicalSpace E]
/-
**ConvexOn._root_.LowerSemicontinuousOn.isClosed_re_epigraph** 是 Mathlib 中的一个定理，
位于命名空间 `ConvexOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LowerSemicontinuousOn.isClosed_re_epigraph (hsc : IsClosed s)
    (hφ_cont : LowerSemicontinuousOn φ s) :
    IsClosed { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 } := by
  let A := { p : E × EReal | p.1 ∈ s ∧ φ p.1 ≤ p.2 }
  have hC : { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 }
    = (Prod.map id ((Real.toEReal ∘ re) : 𝕜 → EReal)) ⁻¹' A := by simp [A]
  refine hC.symm ▸ IsClosed.preimage ?_ ?_
  · exact continuous_id.prodMap <| continuous_coe_real_ereal.comp reCLM.cont
  · exact (lowerSemicontinuousOn_iff_isClosed_epigraph hsc).1
      (continuous_coe_real_ereal.comp_lowerSemicontinuousOn hφ_cont (EReal.coe_strictMono.monotone))

section RCLike

variable [AddCommGroup E] [Module ℝ E] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]

/-- Let `φ : E → ℝ` be a convex and lower-semicontinuous function on a closed convex subset `s`. For
any point `x ∈ s` and `a < φ x`, there exists a continuous affine linear function `f` in `E` such
that `f ≤ φ` on `s` and `f x = a`. This is an auxiliary lemma used in the proof of
`ConvexOn.sSup_affine_eq.` -/
/-
**ConvexOn.exists_affine_le_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：exists_affine_le_of_lt {x : E} {a : Real} (hx : x in s) (hax : a < φ x) (h
sc : IsClosed s) (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn Real s φ) : 
exists (l : E ->L[𝕜] 𝕜) (c : Real), s.domRestrict (re ∘ l) + const s c <= s.domR
estrict φ ∧ re (l x) + c = a
参数：hx : x in s；hax : a < φ x；hsc : IsClosed s；hφc : LowerSemicontinuousOn φ s；hφ
cv : ConvexOn Real s φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.geometric_hahn_banach_point_closed`：geometric_hahn_banach_point_c
losed (ht₁ : Convex Real t) (ht₂ : IsClosed t) (disj : x ∉ t) : exists (f : Stro
ngDual 𝕜 E) (u : Real), re (f x…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Prod.instIsTopologicalAddGroup`：∀ {G : Type w} {H : Type x} [inst : Topo
logicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [inst_3 : Topo
logicalSpace H] [ins…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `ConvexOn.convex_re_epigraph`：convex_re_epigraph [AddCommMonoid E] [Modul
e Real E] (hφcv : ConvexOn Real s φ) : Convex Real { p : E × 𝕜 | p.1 in s ∧ φ p.
1 <= re p.2 }
· 使用定理 `LowerSemicontinuousOn.isClosed_re_epigraph`：∀ {𝕜 : Type u_1} {E : Type u
_2} {s : Set E} {φ : E → ℝ} [inst : RCLike 𝕜] [inst_1 : TopologicalSpace E],   I
sClosed s → LowerSemicontinuousO…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 85 条，此处仅展示前 30 条）

--- 原说明 ---
Let `φ : E → ℝ` be a convex and lower-semicontinuous function on a closed convex
 subset `s`. For
any point `x ∈ s` and `a < φ x`, there exists a continuous affine linear functio
n `f` in `E` such
that `f ≤ φ` on `s` and `f x = a`. This is an auxiliary lemma used in the proof 
of
`ConvexOn.sSup_affine_eq.`
-/
lemma exists_affine_le_of_lt {x : E} {a : ℝ} (hx : x ∈ s) (hax : a < φ x) (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    ∃ (l : E →L[𝕜] 𝕜) (c : ℝ),
      s.domRestrict (re ∘ l) + const s c ≤ s.domRestrict φ ∧ re (l x) + c = a := by
  let A := { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 }
  obtain ⟨L, ⟨b, hLb⟩⟩ := geometric_hahn_banach_point_closed (𝕜 := 𝕜) hφcv.convex_re_epigraph
    (hφc.isClosed_re_epigraph hsc) (by simp [A, hax] : (x, ofReal a) ∉ A)
  let u := L.comp (.inl 𝕜 E 𝕜)
  let c := (re (L (0, 1)))⁻¹
  refine ⟨- c • u, c * re (u x) + a, fun z => ?_, ?_⟩
  · have hv (v : 𝕜) : v * L (0, 1) = L (0, v) := by rw [← smul_eq_mul, ← map_smul]; simp
    have hine {w : E} (h : w ∈ s) : re (L (x, 0)) + re (L (0, 1)) * a
      < re (L (w, 0)) + re (L (0, 1)) * φ w := by
      have hw := hLb.1.trans (hLb.2 _ (by simp [A, h] : (w, ofReal (φ w)) ∈ A))
      rw [← coprod_comp_inl_inr L] at hw
      simpa [-coprod_comp_inl_inr, ← hv (ofReal a), ← hv (ofReal (φ w)), mul_comm a,
        mul_comm (φ w)] using hw
    have hc : 0 < c := inv_pos.2 (pos_of_right_mul_lt_le (lt_of_add_lt_add_left (hine hx)) hax.le)
    simpa [smul_re, u, c, mul_add, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (inv_pos.1 hc))]
      using mul_le_mul_of_nonneg_left (hine z.2).le hc.le
  · simp [u, c, smul_re]
/-
**ConvexOn.exists_affine_le_of_lt_real** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：exists_affine_le_of_lt_real {s : Set Real} {f : Real -> Real} {x : Real} {
a : Real} (hx : x in s) (hax : a < f x) (hsc : IsClosed s) (hfc : LowerSemiconti
nuousOn f s) (hf : ConvexOn Real s f) : exists (c c' : Real), (forall y in s, c 
* y + c' <= f y) ∧ c * x + c' = a
参数：hx : x in s；hax : a < f x；hsc : IsClosed s；hfc : LowerSemicontinuousOn f s；hf
 : ConvexOn Real s f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.exists_affine_le_of_lt`：exists_affine_le_of_lt {x : E} {a : Rea
l} (hx : x in s) (hax : a < φ x) (hsc : IsClosed s) (hφc : LowerSemicontinuousOn
 φ s) (hφcv : ConvexO…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma exists_affine_le_of_lt_real {s : Set ℝ} {f : ℝ → ℝ} {x : ℝ} {a : ℝ} (hx : x ∈ s)
    (hax : a < f x) (hsc : IsClosed s) (hfc : LowerSemicontinuousOn f s) (hf : ConvexOn ℝ s f) :
    ∃ (c c' : ℝ), (∀ y ∈ s, c * y + c' ≤ f y) ∧ c * x + c' = a := by
  obtain ⟨l, c', hlc'_le, hlc'_eq⟩ := exists_affine_le_of_lt (𝕜 := ℝ) hx hax hsc hfc hf
  have h1 y : l 1 * y = l y := by rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  exact ⟨l 1, c', fun y hy ↦ by simpa [h1] using hlc'_le ⟨y, hy⟩, by simpa [h1] using hlc'_eq⟩
/-
**ConvexOn.exists_affine_le_real** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：exists_affine_le_real {s : Set Real} {f : Real -> Real} (hsc : IsClosed s)
 (hfc : LowerSemicontinuousOn f s) (hf : ConvexOn Real s f) : exists c c', foral
l x in s, c * x + c' <= f x
参数：hsc : IsClosed s；hfc : LowerSemicontinuousOn f s；hf : ConvexOn Real s f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ConvexOn.exists_affine_le_of_lt_real`：exists_affine_le_of_lt_real {s : S
et Real} {f : Real -> Real} {x : Real} {a : Real} (hx : x in s) (hax : a < f x) 
(hsc : IsClosed s) (hfc : …
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
-/
lemma exists_affine_le_real {s : Set ℝ} {f : ℝ → ℝ}
    (hsc : IsClosed s) (hfc : LowerSemicontinuousOn f s) (hf : ConvexOn ℝ s f) :
    ∃ c c', ∀ x ∈ s, c * x + c' ≤ f x := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hxs⟩
  · simp
  obtain ⟨c, c', hlc'_le, -⟩ :=
    hf.exists_affine_le_of_lt_real (a := f x - 1) hxs (by simp) hsc hfc
  exact ⟨c, c', hlc'_le⟩

/-- A function `φ : E → ℝ` that is convex and lower-semicontinuous on a closed convex subset `s` is
the supremum of a family of functions that are the restrictions to `s` of continuous affine linear
functions in `E`. -/
/-
**ConvexOn.sSup_affine_eq** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`。
形式化陈述：sSup_affine_eq (hsc : IsClosed s) (hφc : LowerSemicontinuousOn φ s) (hφcv 
: ConvexOn Real s φ) : sSup {f | f <= s.domRestrict φ ∧ exists (l : E ->L[𝕜] 𝕜) 
(c : Real), f = s.domRestrict (re ∘ l) + const s c} = s.domRestrict φ
参数：hsc : IsClosed s；hφc : LowerSemicontinuousOn φ s；hφcv : ConvexOn Real s φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_apply`：sSup_apply {α : Type*} {β : α -> Type*} [forall i, SupSet (β
 i)] {s : Set (forall a, β a)} {a : α} : (sSup s) a = ⨆ f : s, (f : forall a, β 
…
· 使用定理 `csSup_eq_of_forall_le_of_forall_lt_exists_gt`：csSup_eq_of_forall_le_of_f
orall_lt_exists_gt (hs : s.Nonempty) (H : forall a in s, a <= b) (H' : forall w,
 w < b -> exists a in s, w < a) : …
· 使用引理 `ConvexOn.exists_affine_le_of_lt`：exists_affine_le_of_lt {x : E} {a : Rea
l} (hx : x in s) (hax : a < φ x) (hsc : IsClosed s) (hφc : LowerSemicontinuousOn
 φ s) (hφcv : ConvexO…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
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

--- 原说明 ---
A function `φ : E → ℝ` that is convex and lower-semicontinuous on a closed conve
x subset `s` is
the supremum of a family of functions that are the restrictions to `s` of contin
uous affine linear
functions in `E`.
-/
theorem sSup_affine_eq (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    sSup {f | f ≤ s.domRestrict φ ∧
      ∃ (l : E →L[𝕜] 𝕜) (c : ℝ), f = s.domRestrict (re ∘ l) + const s c} = s.domRestrict φ := by
  let A := { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 }
  ext x
  rw [sSup_apply]
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ (fun r ⟨f, hf⟩ => ?_) (fun r hr => ?_)
  · obtain ⟨l, c, hlc⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) x.2 (show φ x - 1 < φ x by grind)
      hsc hφc hφcv
    exact ⟨φ x - 1, hlc.2 ▸ ⟨⟨s.domRestrict (re ∘ l) + const s c, hlc.1, l, c, rfl⟩, rfl⟩⟩
  · exact hf ▸ f.2.1 x
  · obtain ⟨z, hz⟩ := exists_between hr
    obtain ⟨l, c, hlc⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) x.2 hz.2 hsc hφc hφcv
    exact ⟨z, hlc.2 ▸ ⟨⟨s.domRestrict (re ∘ l) + const s c, hlc.1, l, c, rfl⟩, rfl⟩, hz.1⟩

/-- The countable version of `sSup_affine_eq`. -/
/-
**ConvexOn.sSup_of_countable_affine_eq** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`。
形式化陈述：sSup_of_countable_affine_eq [HereditarilyLindelofSpace E] (hsc : IsClosed 
s) (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn Real s φ) : exists 𝓕' : Se
t (s -> Real), 𝓕'.Countable ∧ sSup 𝓕' = s.domRestrict φ ∧ forall f in 𝓕', f <= s
.domRestrict φ ∧ exists (l : E ->L[𝕜] 𝕜) (c : Real), f = s.domRestrict (re ∘ l) 
+ const s c
参数：hsc : IsClosed s；hφc : LowerSemicontinuousOn φ s；hφcv : ConvexOn Real s φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用引理 `ConvexOn.exists_affine_le_of_lt`：exists_affine_le_of_lt {x : E} {a : Rea
l} (hx : x in s) (hax : a < φ x) (hsc : IsClosed s) (hφc : LowerSemicontinuousOn
 φ s) (hφcv : ConvexO…
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bddAbove_def`：bddAbove_def : BddAbove s ↔ exists x, forall y in s, y <= 
x
· 使用定理 `ConvexOn.sSup_affine_eq`：sSup_affine_eq (hsc : IsClosed s) (hφc : LowerS
emicontinuousOn φ s) (hφcv : ConvexOn Real s φ) : sSup {f | f <= s.domRestrict φ
 ∧ exists (l …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Continuous.lowerSemicontinuous`：Continuous.lowerSemicontinuous {f : α ->
 γ} (h : Continuous f) : LowerSemicontinuous f
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
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
· 使用定理 `Pi.continuous_domRestrict_apply`：Pi.continuous_domRestrict_apply (s : Se
t X) {f : X -> Z} (hf : Continuous f) : Continuous (s.domRestrict f)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `RCLike.continuous_re`：continuous_re : Continuous (re : K -> Real)
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `exists_countable_lowerSemicontinuous_isLUB`：exists_countable_lowerSemico
ntinuous_isLUB {s : X -> E} {𝓕 : Set (X -> E)} (h𝓕_cont : forall f in 𝓕, LowerSe
micontinuous f) (h𝓕 : IsLUB 𝓕 s)…
· 使用定理 `instHereditarilyLindelofSpaceSubtype`：∀ {X : Type u} [inst : Topological
Space X] [HereditarilyLindelofSpace X] (p : X → Prop),   HereditarilyLindelofSpa
ce { x // p x }
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
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
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
The countable version of `sSup_affine_eq`.
-/
theorem sSup_of_countable_affine_eq [HereditarilyLindelofSpace E] (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    ∃ 𝓕' : Set (s → ℝ), 𝓕'.Countable ∧ sSup 𝓕' = s.domRestrict φ ∧
      ∀ f ∈ 𝓕', f ≤ s.domRestrict φ ∧
      ∃ (l : E →L[𝕜] 𝕜) (c : ℝ), f = s.domRestrict (re ∘ l) + const s c := by
  by_cases! hs : s.Nonempty
  · let 𝓕 := {f | f ≤ s.domRestrict φ ∧
      ∃ (l : E →L[𝕜] 𝕜) (c : ℝ), f = s.domRestrict (re ∘ l) + const s c}
    have hl : IsLUB 𝓕 (s.domRestrict φ) := by
      refine (hφcv.sSup_affine_eq (𝕜 := 𝕜) hsc hφc) ▸ isLUB_csSup ?_ ?_
      · obtain ⟨l, c, hlc⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) hs.some_mem
          (by grind : φ hs.some - 1 < φ (⟨hs.some, hs.some_mem⟩ : s)) hsc hφc hφcv
        exact ⟨s.domRestrict (re ∘ l) + const s c, hlc.1, l, c, rfl⟩
      · exact (bddAbove_def.2 ⟨φ ∘ Subtype.val, fun y hy => hy.1⟩)
    have hr (f) (hf : f ∈ 𝓕) : LowerSemicontinuous f := by
      obtain ⟨l, c, hlc⟩ := hf.2
      exact Continuous.lowerSemicontinuous (hlc ▸ by fun_prop)
    obtain ⟨𝓕', h𝓕'⟩ := exists_countable_lowerSemicontinuous_isLUB hr hl
    refine ⟨𝓕', h𝓕'.2.1, h𝓕'.2.2.csSup_eq ?_, fun f hf => h𝓕'.1 hf⟩
    by_contra!
    grind [(isLUB_empty_iff.1 (this ▸ h𝓕'.2.2)) (fun x : s => φ x - 1) ⟨hs.some, hs.some_mem⟩]
  · use ∅; simp [domRestrict_def]; grind

/-- The sequential version of `sSup_of_countable_affine_eq`. -/
/-
**ConvexOn.sSup_of_nat_affine_eq** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`。
形式化陈述：sSup_of_nat_affine_eq [HereditarilyLindelofSpace E] (hsc : IsClosed s) (hφ
c : LowerSemicontinuousOn φ s) (hφcv : ConvexOn Real s φ) : exists (l : Nat -> E
 ->L[𝕜] 𝕜) (c : Nat -> Real), (forall i, s.domRestrict (re ∘ (l i)) + const s (c
 i) <= s.domRestrict φ) ∧ ⨆ i, s.domRestrict (re ∘ (l i)) + const s (c i) = s.do
mRestrict φ
参数：hsc : IsClosed s；hφc : LowerSemicontinuousOn φ s；hφcv : ConvexOn Real s φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.sSup_of_countable_affine_eq`：sSup_of_countable_affine_eq [Hered
itarilyLindelofSpace E] (hsc : IsClosed s) (hφc : LowerSemicontinuousOn φ s) (hφ
cv : ConvexOn Real s φ) : …
· 使用定理 `Set.Countable.exists_eq_range`：∀ {α : Type u} {s : Set α}, s.Countable →
 s.Nonempty → ∃ f, s = Set.range f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The sequential version of `sSup_of_countable_affine_eq`.
-/
theorem sSup_of_nat_affine_eq [HereditarilyLindelofSpace E] (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    ∃ (l : ℕ → E →L[𝕜] 𝕜) (c : ℕ → ℝ),
      (∀ i, s.domRestrict (re ∘ (l i)) + const s (c i) ≤ s.domRestrict φ) ∧
      ⨆ i, s.domRestrict (re ∘ (l i)) + const s (c i) = s.domRestrict φ := by
  obtain ⟨𝓕', h𝓕'⟩ := hφcv.sSup_of_countable_affine_eq (𝕜 := 𝕜) hsc hφc
  by_cases! he : 𝓕'.Nonempty
  · obtain ⟨f, hf⟩ := h𝓕'.1.exists_eq_range he
    have (i : ℕ) : ∃ (l : E →L[𝕜] 𝕜) (c : ℝ),
        f i = s.domRestrict (re ∘ l) + const s c := by simp_all
    choose l c hlc using this
    refine ⟨l, c, fun i => (hlc i) ▸ (h𝓕'.2.2 (f i) (hf ▸ mem_range_self i)).1, ?_⟩
    calc
    _ = ⨆ i, f i := by congr with i x; exact congrFun (hlc i).symm x
    _ = _ := by rw [← sSup_range, ← hf, h𝓕'.2.1]
  · by_cases! hsφ : s.domRestrict φ = 0
    · have := congrFun hsφ
      refine ⟨fun _ => 0, fun _ => 0, ?_, ?_⟩
      · simp_all [domRestrict_def]
      · ext; simp_all
    · obtain ⟨x, hx⟩ := Function.ne_iff.1 hsφ
      have : s = ∅ := by have := congrFun h𝓕'.2.1 x; simp_all
      grind

/-- A function `φ : E → ℝ` that is convex and lower-semicontinuous is the supremum of a family of
of continuous affine linear functions. -/
/-
**ConvexOn.univ_sSup_affine_eq** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`。
形式化陈述：univ_sSup_affine_eq (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn Real un
iv φ) : sSup {f | f <= φ ∧ exists (l : E ->L[𝕜] 𝕜) (c : Real), f = (re ∘ l) + co
nst E c} = φ
参数：hφc : LowerSemicontinuous φ；hφcv : ConvexOn Real univ φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.sSup_affine_eq`：sSup_affine_eq (hsc : IsClosed s) (hφc : LowerS
emicontinuousOn φ s) (hφcv : ConvexOn Real s φ) : sSup {f | f <= s.domRestrict φ
 ∧ exists (l …
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lowerSemicontinuousOn_univ_iff`：lowerSemicontinuousOn_univ_iff : LowerSe
micontinuousOn f univ ↔ LowerSemicontinuous f
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `trivial`：True
· 使用定理 `Equiv.Set.univ_symm_apply`：∀ (α : Type u_3) (a : α), (Equiv.Set.univ α).
symm a = ⟨a, trivial⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_image'`：sSup_image' {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a 
: s, f a
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a

--- 原说明 ---
A function `φ : E → ℝ` that is convex and lower-semicontinuous is the supremum o
f a family of
of continuous affine linear functions.
-/
theorem univ_sSup_affine_eq (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ) :
    sSup {f | f ≤ φ ∧ ∃ (l : E →L[𝕜] 𝕜) (c : ℝ), f = (re ∘ l) + const E c} = φ := by
  let 𝓕 := {f | f ≤ φ ∘ Subtype.val ∧ ∃ (l : E →L[𝕜] 𝕜) (c : ℝ), f = (re ∘ l) ∘ Subtype.val +
    const univ c}
  have := hφcv.sSup_affine_eq (𝕜 := 𝕜) isClosed_univ (lowerSemicontinuousOn_univ_iff.2 hφc)
  simp only [domRestrict_eq] at this
  calc
  _ = sSup ((fun g => g ∘ (Equiv.Set.univ E).symm) '' 𝓕) := by
    congr
    ext f
    refine ⟨fun ⟨hp, l, c, hlc⟩ => ⟨f ∘ Subtype.val, ⟨fun x => hp (Subtype.val x), ⟨l, c, ?_⟩⟩, ?_⟩,
      fun ⟨a, ⟨⟨h, ⟨l, c, hlc⟩⟩, hb⟩⟩ => ⟨fun x => ?_, ⟨l, c, ?_⟩⟩⟩
    · ext x; simpa using! congrFun hlc x
    · ext; simp
    · simpa using! hb ▸ h ⟨x, trivial⟩
    · subst hlc; simpa using! hb.symm
  _ = sSup 𝓕 ∘ (Equiv.Set.univ E).symm := by ext x; rw [sSup_image', sSup_eq_iSup']; simp
  _ = φ ∘ Subtype.val ∘ (Equiv.Set.univ E).symm :=
    congrArg (fun g => g ∘ (Equiv.Set.univ E).symm) this
  _ = φ := by ext; simp

/-- The countable version of `univ_sSup_affine_eq`. -/
/-
**ConvexOn.univ_sSup_of_countable_affine_eq** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`
。
形式化陈述：univ_sSup_of_countable_affine_eq [HereditarilyLindelofSpace E] (hφc : Lowe
rSemicontinuous φ) (hφcv : ConvexOn Real univ φ) : exists 𝓕' : Set (E -> Real), 
𝓕'.Countable ∧ sSup 𝓕' = φ ∧ forall f in 𝓕', f <= φ ∧ exists (l : E ->L[𝕜] 𝕜) (c
 : Real), f = (re ∘ l) + const E c
参数：hφc : LowerSemicontinuous φ；hφcv : ConvexOn Real univ φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用引理 `ConvexOn.exists_affine_le_of_lt`：exists_affine_le_of_lt {x : E} {a : Rea
l} (hx : x in s) (hax : a < φ x) (hsc : IsClosed s) (hφc : LowerSemicontinuousOn
 φ s) (hφcv : ConvexO…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lowerSemicontinuousOn_univ_iff`：lowerSemicontinuousOn_univ_iff : LowerSe
micontinuousOn f univ ↔ LowerSemicontinuous f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `bddAbove_def`：bddAbove_def : BddAbove s ↔ exists x, forall y in s, y <= 
x
· 使用定理 `ConvexOn.univ_sSup_affine_eq`：univ_sSup_affine_eq (hφc : LowerSemicontin
uous φ) (hφcv : ConvexOn Real univ φ) : sSup {f | f <= φ ∧ exists (l : E ->L[𝕜] 
𝕜) (c : Real), f =…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Continuous.lowerSemicontinuous`：Continuous.lowerSemicontinuous {f : α ->
 γ} (h : Continuous f) : LowerSemicontinuous f
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
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
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `RCLike.continuous_re`：continuous_re : Continuous (re : K -> Real)
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `exists_countable_lowerSemicontinuous_isLUB`：exists_countable_lowerSemico
ntinuous_isLUB {s : X -> E} {𝓕 : Set (X -> E)} (h𝓕_cont : forall f in 𝓕, LowerSe
micontinuous f) (h𝓕 : IsLUB 𝓕 s)…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
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
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The countable version of `univ_sSup_affine_eq`.
-/
theorem univ_sSup_of_countable_affine_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ) :
    ∃ 𝓕' : Set (E → ℝ), 𝓕'.Countable ∧ sSup 𝓕' = φ ∧
      ∀ f ∈ 𝓕', f ≤ φ ∧ ∃ (l : E →L[𝕜] 𝕜) (c : ℝ), f = (re ∘ l) + const E c := by
  let 𝓕 := {f | f ≤ φ ∧ ∃ (l : E →L[𝕜] 𝕜) (c : ℝ), f = (re ∘ l) + const E c}
  have hl : IsLUB 𝓕 φ := by
    refine (hφcv.univ_sSup_affine_eq (𝕜 := 𝕜) hφc) ▸ isLUB_csSup ?_ ?_
    · obtain ⟨l, c, hlc⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) (@mem_univ E 0)
        (by grind : φ 0 - 1 < φ (⟨0, @mem_univ E 0⟩ : univ)) isClosed_univ
        (lowerSemicontinuousOn_univ_iff.2 hφc) hφcv
      exact ⟨(re ∘ l) + const E c, fun x => hlc.1 ⟨x, mem_univ x⟩, ⟨l, c, rfl⟩⟩
    · exact (bddAbove_def.2 ⟨φ, fun y hy => hy.1⟩)
  have hr (f) (hf : f ∈ 𝓕) : LowerSemicontinuous f := by
    obtain ⟨l, c, hlc⟩ := hf.2
    exact Continuous.lowerSemicontinuous (by rw [hlc]; fun_prop)
  obtain ⟨𝓕', h𝓕'⟩ := exists_countable_lowerSemicontinuous_isLUB hr hl
  refine ⟨𝓕', h𝓕'.2.1, h𝓕'.2.2.csSup_eq ?_, fun f hf => h𝓕'.1 hf⟩
  by_contra!
  grind [(isLUB_empty_iff.1 (this ▸ h𝓕'.2.2)) (fun x => φ x - 1) 0]

/-- The sequential version of `univ_sSup_of_countable_affine_eq`. -/
/-
**ConvexOn.univ_sSup_of_nat_affine_eq** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`。
形式化陈述：univ_sSup_of_nat_affine_eq [HereditarilyLindelofSpace E] (hφc : LowerSemic
ontinuous φ) (hφcv : ConvexOn Real univ φ) : exists (l : Nat -> E ->L[𝕜] 𝕜) (c :
 Nat -> Real), (forall i, re ∘ (l i) + const E (c i) <= φ) ∧ ⨆ i, re ∘ (l i) + c
onst E (c i) = φ
参数：hφc : LowerSemicontinuous φ；hφcv : ConvexOn Real univ φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.sSup_of_nat_affine_eq`：sSup_of_nat_affine_eq [HereditarilyLinde
lofSpace E] (hsc : IsClosed s) (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexO
n Real s φ) : exists…
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lowerSemicontinuousOn_univ_iff`：lowerSemicontinuousOn_univ_iff : LowerSe
micontinuousOn f univ ↔ LowerSemicontinuous f
· 使用定理 `trivial`：True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a

--- 原说明 ---
The sequential version of `univ_sSup_of_countable_affine_eq`.
-/
theorem univ_sSup_of_nat_affine_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ) :
    ∃ (l : ℕ → E →L[𝕜] 𝕜) (c : ℕ → ℝ), (∀ i, re ∘ (l i) + const E (c i) ≤ φ)
      ∧ ⨆ i, re ∘ (l i) + const E (c i) = φ := by
  obtain ⟨l, c, hle, hsup⟩ := hφcv.sSup_of_nat_affine_eq (𝕜 := 𝕜) (s := univ) isClosed_univ
    (lowerSemicontinuousOn_univ_iff.2 hφc)
  refine ⟨l, c, fun i x ↦ hle i ⟨x, trivial⟩, ?_⟩
  ext x
  simpa using congrFun hsup ⟨x, trivial⟩

end RCLike

section Real

variable [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E]

/-- The real version of `sSup_affine_eq`. -/
/-
**ConvexOn.real_sSup_affine_eq** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`。
形式化陈述：real_sSup_affine_eq (hsc : IsClosed s) (hφc : LowerSemicontinuousOn φ s) (
hφcv : ConvexOn Real s φ) : sSup {f | f <= s.domRestrict φ ∧ exists (l : E ->L[R
eal] Real) (c : Real), f = s.domRestrict l + const s c} = s.domRestrict φ
参数：hsc : IsClosed s；hφc : LowerSemicontinuousOn φ s；hφcv : ConvexOn Real s φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.sSup_affine_eq`：sSup_affine_eq (hsc : IsClosed s) (hφc : LowerS
emicontinuousOn φ s) (hφcv : ConvexOn Real s φ) : sSup {f | f <= s.domRestrict φ
 ∧ exists (l …

--- 原说明 ---
The real version of `sSup_affine_eq`.
-/
theorem real_sSup_affine_eq (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    sSup {f | f ≤ s.domRestrict φ ∧
      ∃ (l : E →L[ℝ] ℝ) (c : ℝ), f = s.domRestrict l + const s c} = s.domRestrict φ :=
  sSup_affine_eq (𝕜 := ℝ) hsc hφc hφcv

/-- The real version of `sSup_of_countable_affine_eq`. -/
/-
**ConvexOn.real_sSup_of_countable_affine_eq** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`
。
形式化陈述：real_sSup_of_countable_affine_eq [HereditarilyLindelofSpace E] (hsc : IsCl
osed s) (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn Real s φ) : exists 𝓕'
 : Set (s -> Real), 𝓕'.Countable ∧ sSup 𝓕' = s.domRestrict φ ∧ forall f in 𝓕', f
 <= s.domRestrict φ ∧ exists (l : E ->L[Real] Real) (c : Real), f = s.domRestric
t l + const s c
参数：hsc : IsClosed s；hφc : LowerSemicontinuousOn φ s；hφcv : ConvexOn Real s φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.sSup_of_countable_affine_eq`：sSup_of_countable_affine_eq [Hered
itarilyLindelofSpace E] (hsc : IsClosed s) (hφc : LowerSemicontinuousOn φ s) (hφ
cv : ConvexOn Real s φ) : …

--- 原说明 ---
The real version of `sSup_of_countable_affine_eq`.
-/
theorem real_sSup_of_countable_affine_eq [HereditarilyLindelofSpace E] (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    ∃ 𝓕' : Set (s → ℝ), 𝓕'.Countable ∧ sSup 𝓕' = s.domRestrict φ ∧
      ∀ f ∈ 𝓕', f ≤ s.domRestrict φ ∧ ∃ (l : E →L[ℝ] ℝ) (c : ℝ), f = s.domRestrict l + const s c :=
  sSup_of_countable_affine_eq (𝕜 := ℝ) hsc hφc hφcv

/-- The real version of `sSup_of_nat_affine_eq`. -/
/-
**ConvexOn.real_sSup_of_nat_affine_eq** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`。
形式化陈述：real_sSup_of_nat_affine_eq [HereditarilyLindelofSpace E] (hsc : IsClosed s
) (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn Real s φ) : exists (l : Nat
 -> E ->L[Real] Real) (c : Nat -> Real), (forall i, s.domRestrict (l i) + const 
s (c i) <= s.domRestrict φ) ∧ ⨆ i, s.domRestrict (l i) + const s (c i) = s.domRe
strict φ
参数：hsc : IsClosed s；hφc : LowerSemicontinuousOn φ s；hφcv : ConvexOn Real s φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.sSup_of_nat_affine_eq`：sSup_of_nat_affine_eq [HereditarilyLinde
lofSpace E] (hsc : IsClosed s) (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexO
n Real s φ) : exists…

--- 原说明 ---
The real version of `sSup_of_nat_affine_eq`.
-/
theorem real_sSup_of_nat_affine_eq [HereditarilyLindelofSpace E] (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    ∃ (l : ℕ → E →L[ℝ] ℝ) (c : ℕ → ℝ),
      (∀ i, s.domRestrict (l i) + const s (c i) ≤ s.domRestrict φ) ∧
      ⨆ i, s.domRestrict (l i) + const s (c i) = s.domRestrict φ :=
  sSup_of_nat_affine_eq (𝕜 := ℝ) hsc hφc hφcv

/-- The real version of `univ_sSup_affine_eq`. -/
/-
**ConvexOn.real_univ_sSup_affine_eq** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`。
形式化陈述：real_univ_sSup_affine_eq (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn Re
al univ φ) : sSup {f | f <= φ ∧ exists (l : E ->L[Real] Real) (c : Real), f = l 
+ const E c} = φ
参数：hφc : LowerSemicontinuous φ；hφcv : ConvexOn Real univ φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.univ_sSup_affine_eq`：univ_sSup_affine_eq (hφc : LowerSemicontin
uous φ) (hφcv : ConvexOn Real univ φ) : sSup {f | f <= φ ∧ exists (l : E ->L[𝕜] 
𝕜) (c : Real), f =…

--- 原说明 ---
The real version of `univ_sSup_affine_eq`.
-/
theorem real_univ_sSup_affine_eq (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ) :
    sSup {f | f ≤ φ ∧ ∃ (l : E →L[ℝ] ℝ) (c : ℝ), f = l + const E c} = φ :=
  univ_sSup_affine_eq (𝕜 := ℝ) hφc hφcv

/-- The real version of `univ_sSup_of_countable_affine_eq`. -/
/-
**ConvexOn.real_univ_sSup_of_countable_affine_eq** 是 Mathlib 中的一个定理，位于命名空间 `Conv
exOn`。
形式化陈述：real_univ_sSup_of_countable_affine_eq [HereditarilyLindelofSpace E] (hφc :
 LowerSemicontinuous φ) (hφcv : ConvexOn Real univ φ) : exists 𝓕' : Set (E -> Re
al), 𝓕'.Countable ∧ sSup 𝓕' = φ ∧ forall f in 𝓕', f <= φ ∧ exists (l : E ->L[Rea
l] Real) (c : Real), f = l + const E c
参数：hφc : LowerSemicontinuous φ；hφcv : ConvexOn Real univ φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.univ_sSup_of_countable_affine_eq`：univ_sSup_of_countable_affine
_eq [HereditarilyLindelofSpace E] (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn
 Real univ φ) : exists 𝓕' : Set…

--- 原说明 ---
The real version of `univ_sSup_of_countable_affine_eq`.
-/
theorem real_univ_sSup_of_countable_affine_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ) :
    ∃ 𝓕' : Set (E → ℝ), 𝓕'.Countable ∧ sSup 𝓕' = φ ∧
      ∀ f ∈ 𝓕', f ≤ φ ∧ ∃ (l : E →L[ℝ] ℝ) (c : ℝ), f = l + const E c :=
  univ_sSup_of_countable_affine_eq (𝕜 := ℝ) hφc hφcv

/-- The real version of `univ_sSup_of_nat_affine_eq`. -/
/-
**ConvexOn.real_univ_sSup_of_nat_affine_eq** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`。
形式化陈述：real_univ_sSup_of_nat_affine_eq [HereditarilyLindelofSpace E] (hφc : Lower
Semicontinuous φ) (hφcv : ConvexOn Real univ φ) : exists (l : Nat -> E ->L[Real]
 Real) (c : Nat -> Real), (forall i, (l i) + const E (c i) <= φ) ∧ ⨆ i, (l i) + 
const E (c i) = φ
参数：hφc : LowerSemicontinuous φ；hφcv : ConvexOn Real univ φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.univ_sSup_of_nat_affine_eq`：univ_sSup_of_nat_affine_eq [Heredit
arilyLindelofSpace E] (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn Real univ φ
) : exists (l : Nat -> E …

--- 原说明 ---
The real version of `univ_sSup_of_nat_affine_eq`.
-/
theorem real_univ_sSup_of_nat_affine_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ) :
    ∃ (l : ℕ → E →L[ℝ] ℝ) (c : ℕ → ℝ), (∀ i, (l i) + const E (c i) ≤ φ) ∧
      ⨆ i, (l i) + const E (c i) = φ :=
  univ_sSup_of_nat_affine_eq (𝕜 := ℝ) hφc hφcv

end Real

end ConvexOn

