/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup

/-!
# Arithmetic subgroups of `GL(2, ℝ)`

We define a subgroup of `GL (Fin 2) ℝ` to be *arithmetic* if it is commensurable with the image
of `SL(2, ℤ)`.
-/

@[expose] public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

local notation "SL" => SpecialLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Subgroup

section det_typeclasses

variable {R : Type*} [CommRing R] (Γ : Subgroup (GL n R))

/-- Typeclass saying that a subgroup of `GL(2, ℝ)` has determinant contained in `{±1}`. Necessary
so that the typeclass system can detect when the slash action is multiplicative. -/
/-
**Subgroup.HasDetPlusMinusOne** 是 Mathlib 中的一个归纳类型，位于命名空间 `Subgroup`。
形式化陈述：{n : Type u_1} →   [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Ty
pe u_2} → [inst_2 : CommRing R] → Subgroup (GL n R) → Prop
参数：GL n R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass saying that a subgroup of `GL(2, ℝ)` has determinant contained in `{±1
}`. Necessary
so that the typeclass system can detect when the slash action is multiplicative.
-/
class HasDetPlusMinusOne : Prop where
  det_eq {g} (hg : g ∈ Γ) : g.det = 1 ∨ g.det = -1

variable {Γ} in
/-
**Subgroup.HasDetPlusMinusOne.abs_det** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.HasDet
PlusMinusOne`。
形式化陈述：∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2
} [inst_2 : CommRing R]   {Γ : Subgroup (GL n R)} [inst_3 : LinearOrder R] [IsOr
deredRing R] [Γ.HasDetPlusMinusOne] {g : GL n R},   g ∈ Γ → |↑(Matrix.GeneralLin
earGroup.det g)| = 1
参数：GL n R；Matrix.GeneralLinearGroup.det g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.HasDetPlusMinusOne.det_eq`：∀ {n : Type u_1} {inst : Fintype n} 
{inst_1 : DecidableEq n} {R : Type u_2} {inst_2 : CommRing R}   {Γ : Subgroup (G
L n R)} [self : Γ.HasDet…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
-/
lemma HasDetPlusMinusOne.abs_det [LinearOrder R] [IsOrderedRing R] [HasDetPlusMinusOne Γ]
    {g} (hg : g ∈ Γ) : |g.det.val| = 1 := by
  rcases HasDetPlusMinusOne.det_eq hg with h | h <;> simp [h]
/-
**Subgroup.hasDetPlusMinusOne_iff_abs_det** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：hasDetPlusMinusOne_iff_abs_det [LinearOrder R] [IsOrderedRing R] : HasDetP
lusMinusOne Γ ↔ forall {g}, g in Γ -> |g.det.val| = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.HasDetPlusMinusOne.abs_det`：∀ {n : Type u_1} [inst : Fintype n]
 [inst_1 : DecidableEq n] {R : Type u_2} [inst_2 : CommRing R]   {Γ : Subgroup (
GL n R)} [inst_3 : Linear…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_eq`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   0 ≤ b → (|a| = b ↔ a = b ∨ a = -b)
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma hasDetPlusMinusOne_iff_abs_det [LinearOrder R] [IsOrderedRing R] :
    HasDetPlusMinusOne Γ ↔ ∀ {g}, g ∈ Γ → |g.det.val| = 1 := by
  refine ⟨fun h {g} hg ↦ h.abs_det hg, fun h ↦ ⟨?_⟩⟩
  simpa [-GeneralLinearGroup.val_det_apply, abs_eq zero_le_one] using @h

/-- Typeclass saying that a subgroup of `GL(n, R)` is contained in `SL(n, R)`. Necessary so that
the typeclass system can detect when the slash action is `ℂ`-linear. -/
/-
**Subgroup.HasDetOne** 是 Mathlib 中的一个归纳类型，位于命名空间 `Subgroup`。
形式化陈述：{n : Type u_1} →   [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Ty
pe u_2} → [inst_2 : CommRing R] → Subgroup (GL n R) → Prop
参数：GL n R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass saying that a subgroup of `GL(n, R)` is contained in `SL(n, R)`. Neces
sary so that
the typeclass system can detect when the slash action is `ℂ`-linear.
-/
class HasDetOne : Prop where
  det_eq {g} (hg : g ∈ Γ) : g.det = 1
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Γ : Subgroup (SL n R)) : HasDetOne (Γ.map toGL) where
  det_eq {g} hg := by rcases hg with ⟨g, hg, rfl⟩; simp
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Type*} [CommRing S] [Algebra R S] (Γ : Subgroup (SL n R)) :
    HasDetOne (Γ.map <| mapGL S) where
  det_eq {g} hg := by rcases hg with ⟨g, hg, rfl⟩; simp
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Type*} [CommRing S] [Algebra R S] :
    HasDetOne (mapGL (n := n) (R := R) S).range where
  det_eq {g} hg := by rcases hg with ⟨g, hg, rfl⟩; simp
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasDetOne Γ] : HasDetPlusMinusOne Γ := ⟨fun {g} hg ↦ by simp [HasDetOne.det_eq hg]⟩
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Γ' : Subgroup (GL n R)) [HasDetOne Γ] : HasDetOne (Γ ⊓ Γ') where
  det_eq hg := HasDetOne.det_eq hg.1
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Γ' : Subgroup (GL n R)) [HasDetOne Γ] : HasDetOne (Γ' ⊓ Γ) where
  det_eq hg := HasDetOne.det_eq hg.2

open scoped Pointwise in
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Γ : Subgroup (GL n R)) [HasDetOne Γ] (g : ConjAct <| GL n R) :
    HasDetOne (g • Γ) where
  det_eq {h} hh := by
    rw [mem_pointwise_smul_iff_inv_smul_mem] at hh
    simpa [ConjAct.smul_def] using HasDetOne.det_eq hh

open scoped Pointwise in
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Γ : Subgroup (GL n R)) [HasDetPlusMinusOne Γ] (g : ConjAct <| GL n R) :
    HasDetPlusMinusOne (g • Γ) where
  det_eq {h} hh := by
    rw [mem_pointwise_smul_iff_inv_smul_mem] at hh
    simpa [ConjAct.smul_def] using HasDetPlusMinusOne.det_eq hh

end det_typeclasses

section SL2Z_in_GL2R

/-- The image of the modular group `SL(2, ℤ)`, as a subgroup of `GL(2, ℝ)`. -/
scoped[MatrixGroups] notation "𝒮ℒ" => MonoidHom.range (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)

/-- Coercion from subgroups of `SL(2, ℤ)` to subgroups of `GL(2, ℝ)` by mapping along the obvious
inclusion homomorphism. -/
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from subgroups of `SL(2, ℤ)` to subgroups of `GL(2, ℝ)` by mapping alon
g the obvious
inclusion homomorphism.
-/
instance : Coe (Subgroup SL(2, ℤ)) (Subgroup (GL (Fin 2) ℝ)) where
  coe := map (mapGL ℝ)

/-- A subgroup of `GL(2, ℝ)` is arithmetic if it is commensurable with the image of `SL(2, ℤ)`. -/
/-
**Subgroup.IsArithmetic** 是 Mathlib 中的一个归纳类型，位于命名空间 `Subgroup`。
形式化陈述：Subgroup (GL (Fin 2) ℝ) → Prop
参数：GL (Fin 2) ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup of `GL(2, ℝ)` is arithmetic if it is commensurable with the image of 
`SL(2, ℤ)`.
-/
class IsArithmetic (𝒢 : Subgroup (GL (Fin 2) ℝ)) : Prop where
  is_commensurable : Commensurable 𝒢 𝒮ℒ

/-- The image of `SL(2, ℤ)` in `GL(2, ℝ)` is arithmetic. -/
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of `SL(2, ℤ)` in `GL(2, ℝ)` is arithmetic.
-/
instance : IsArithmetic 𝒮ℒ where is_commensurable := .refl 𝒮ℒ
/-
**Subgroup.isArithmetic_iff_finiteIndex** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：isArithmetic_iff_finiteIndex {Γ : Subgroup SL(2, Int)} : IsArithmetic Γ ↔ 
Γ.FiniteIndex
参数：2, Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Subgroup.comap_map_eq_self_of_injective`：comap_map_eq_self_of_injective 
{f : G ->* N} (h : Function.Injective f) (H : Subgroup G) : comap f (map f H) = 
H
· 使用引理 `Matrix.SpecialLinearGroup.mapGL_injective`：mapGL_injective [FaithfulSMul
 R S] : Function.Injective (mapGL (R
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Subgroup.relIndex_top_right`：relIndex_top_right : H.relIndex ⊤ = H.index
· 使用定理 `Subgroup.relIndex_top_left`：relIndex_top_left : (⊤ : Subgroup G).relInde
x H = 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma isArithmetic_iff_finiteIndex {Γ : Subgroup SL(2, ℤ)} : IsArithmetic Γ ↔ Γ.FiniteIndex := by
  constructor <;>
  · refine fun ⟨h⟩ ↦ ⟨?_⟩
    simpa [Commensurable, MonoidHom.range_eq_map, ← relIndex_comap,
      comap_map_eq_self_of_injective mapGL_injective] using h

/-- Images in `GL(2, ℝ)` of finite-index subgroups of `SL(2, ℤ)` are arithmetic. -/
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Images in `GL(2, ℝ)` of finite-index subgroups of `SL(2, ℤ)` are arithmetic.
-/
instance (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : IsArithmetic Γ :=
  isArithmetic_iff_finiteIndex.mpr ‹_›

/-- If `Γ` is arithmetic, its preimage in `SL(2, ℤ)` has finite index. -/
/-
**Subgroup.IsArithmetic.finiteIndex_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Is
Arithmetic`。
形式化陈述：∀ (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic], (Subgroup.comap (Matrix.
SpecialLinearGroup.mapGL ℝ) 𝒢).FiniteIndex
参数：𝒢 : Subgroup (GL (Fin 2) ℝ)；Subgroup.comap (Matrix.SpecialLinearGroup.mapGL ℝ
) 𝒢。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subgroup.IsArithmetic.is_commensurable`：∀ {𝒢 : Subgroup (GL (Fin 2) ℝ)} 
[self : 𝒢.IsArithmetic], 𝒢.Commensurable (Matrix.SpecialLinearGroup.mapGL ℝ).ran
ge
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.index_comap`：index_comap (f : G' ->* G) : (H.comap f).index = H
.relIndex f.range

--- 原说明 ---
If `Γ` is arithmetic, its preimage in `SL(2, ℤ)` has finite index.
-/
instance IsArithmetic.finiteIndex_comap (𝒢 : Subgroup (GL (Fin 2) ℝ)) [IsArithmetic 𝒢] :
    (𝒢.comap (mapGL (R := ℤ) ℝ)).FiniteIndex :=
  ⟨𝒢.index_comap (mapGL (R := ℤ) ℝ) ▸ IsArithmetic.is_commensurable.1⟩
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {Γ : Subgroup (GL (Fin 2) ℝ)} [h : Γ.IsArithmetic] : HasDetPlusMinusOne Γ := by
  rw [hasDetPlusMinusOne_iff_abs_det]
  intro g hg
  obtain ⟨n, hn, _, hgn⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero
    Subgroup.IsArithmetic.is_commensurable.2 hg
  suffices |(g.det ^ n).val| = 1 by simpa [← abs_pow, abs_pow_eq_one _ (Nat.ne_zero_of_lt hn)]
  obtain ⟨t, ht⟩ := hgn.1
  have := congr_arg Matrix.GeneralLinearGroup.det ht.symm
  rw [Matrix.SpecialLinearGroup.det_mapGL, map_pow] at this
  simp [this]
/-
**Subgroup.IsArithmetic.isFiniteRelIndexSL** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.I
sArithmetic`。
形式化陈述：∀ (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic], 𝒢.IsFiniteRelIndex (Matr
ix.SpecialLinearGroup.mapGL ℝ).range
参数：𝒢 : Subgroup (GL (Fin 2) ℝ)；Matrix.SpecialLinearGroup.mapGL ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subgroup.IsArithmetic.is_commensurable`：∀ {𝒢 : Subgroup (GL (Fin 2) ℝ)} 
[self : 𝒢.IsArithmetic], 𝒢.Commensurable (Matrix.SpecialLinearGroup.mapGL ℝ).ran
ge
-/
instance IsArithmetic.isFiniteRelIndexSL (𝒢 : Subgroup (GL (Fin 2) ℝ)) [IsArithmetic 𝒢] :
    𝒢.IsFiniteRelIndex 𝒮ℒ :=
  ⟨IsArithmetic.is_commensurable.1⟩
/-
**Subgroup.IsArithmetic.inter** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsArithmetic`。
形式化陈述：∀ {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] [Γ'.IsArithmetic], (Γ 
⊓ Γ').IsArithmetic
参数：GL (Fin 2) ℝ；Γ ⊓ Γ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.relIndex_inf_ne_zero`：relIndex_inf_ne_zero (hH : H.relIndex L !
= 0) (hK : K.relIndex L != 0) : (H ⊓ K).relIndex L != 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subgroup.IsArithmetic.is_commensurable`：∀ {𝒢 : Subgroup (GL (Fin 2) ℝ)} 
[self : 𝒢.IsArithmetic], 𝒢.Commensurable (Matrix.SpecialLinearGroup.mapGL ℝ).ran
ge
· 使用定理 `Subgroup.relIndex_ne_zero_trans`：relIndex_ne_zero_trans (hHK : H.relInde
x K != 0) (hKL : K.relIndex L != 0) : H.relIndex L != 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.relIndex_eq_one`：relIndex_eq_one : H.relIndex K = 1 ↔ K <= H
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
instance IsArithmetic.inter {Γ Γ'} [IsArithmetic Γ] [IsArithmetic Γ'] : IsArithmetic (Γ ⊓ Γ') := by
  constructor
  constructor
  · apply relIndex_inf_ne_zero <;> exact IsArithmetic.is_commensurable.1
  · apply relIndex_ne_zero_trans (K := Γ) IsArithmetic.is_commensurable.2
    rw [relIndex_eq_one.mpr inf_le_left]
    simp

end SL2Z_in_GL2R

end Subgroup

namespace Matrix.SpecialLinearGroup

/-- The image of `SL(n, ℤ)` in `GL(n, ℝ)` is discrete. -/
/-
**Matrix.SpecialLinearGroup.discreteSpecialLinearGroupIntRange** 是 Mathlib 中的一个实
例，位于命名空间 `Matrix.SpecialLinearGroup`。
形式化陈述：discreteSpecialLinearGroupIntRange : DiscreteTopology (mapGL (n
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.discreteTopology`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] [DiscreteTopology X]   (h : X ≃ₜ 
Y), DiscreteTopol…
· 使用定理 `Matrix.SpecialLinearGroup.instDiscreteTopology`：∀ {n : Type u_1} {R : Ty
pe u_2} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing R]   [ins
t_3 : TopologicalSpace R] [DiscreteT…
· 使用定理 `instDiscreteTopologyInt`：DiscreteTopology ℤ
· 使用引理 `Matrix.SpecialLinearGroup.isEmbedding_mapGL`：isEmbedding_mapGL (h : IsEm
bedding (algebraMap R S)) : IsEmbedding (mapGL S : SL n R -> _)
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用定理 `Real.isClosedEmbedding_intCast`：isClosedEmbedding_intCast : IsClosedEmbe
dding ((↑) : Int -> Real)

--- 原说明 ---
The image of `SL(n, ℤ)` in `GL(n, ℝ)` is discrete.
-/
instance discreteSpecialLinearGroupIntRange : DiscreteTopology (mapGL (n := n) (R := ℤ) ℝ).range :=
  (isEmbedding_mapGL Real.isClosedEmbedding_intCast.1).toHomeomorph.discreteTopology

/-- The image of `SL(n, ℤ)` in `SL(n, ℝ)` is discrete. -/
/-
**Matrix.SpecialLinearGroup.discreteSpecialLinearGroupIntRangeSL** 是 Mathlib 中的一
个实例，位于命名空间 `Matrix.SpecialLinearGroup`。
形式化陈述：discreteSpecialLinearGroupIntRangeSL : DiscreteTopology (SpecialLinearGrou
p.map (Int.castRingHom Real) (n
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.discreteTopology`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] [DiscreteTopology X]   (h : X ≃ₜ 
Y), DiscreteTopol…
· 使用定理 `Matrix.SpecialLinearGroup.instDiscreteTopology`：∀ {n : Type u_1} {R : Ty
pe u_2} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing R]   [ins
t_3 : TopologicalSpace R] [DiscreteT…
· 使用定理 `instDiscreteTopologyInt`：DiscreteTopology ℤ
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用定理 `Topology.IsClosedEmbedding.specialLinearGroup_map`：∀ {n : Type u_1} {R :
 Type u_2} {S : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : 
CommRing R]   [inst_3 : TopologicalSpac…
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `Real.isClosedEmbedding_intCast`：isClosedEmbedding_intCast : IsClosedEmbe
dding ((↑) : Int -> Real)

--- 原说明 ---
The image of `SL(n, ℤ)` in `SL(n, ℝ)` is discrete.
-/
instance discreteSpecialLinearGroupIntRangeSL :
    DiscreteTopology (SpecialLinearGroup.map (Int.castRingHom ℝ) (n := n)).range := by
  refine (Topology.IsEmbedding.toHomeomorph ?_).discreteTopology
  exact Real.isClosedEmbedding_intCast.specialLinearGroup_map.1
/-
**Matrix.SpecialLinearGroup.isClosedEmbedding_mapGLInt** 是 Mathlib 中的一个引理，位于命名空间
 `Matrix.SpecialLinearGroup`。
形式化陈述：isClosedEmbedding_mapGLInt : Topology.IsClosedEmbedding (mapGL Real : SL n
 Int -> GL n Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.SpecialLinearGroup.isClosedEmbedding_mapGL`：isClosedEmbedding_map
GL [IsTopologicalRing R] [T1Space R] [T1Space S] (h : IsClosedEmbedding (algebra
Map R S)) : IsClosedEmbedding (mapGL S …
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `instDiscreteTopologyInt`：DiscreteTopology ℤ
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Real.isClosedEmbedding_intCast`：isClosedEmbedding_intCast : IsClosedEmbe
dding ((↑) : Int -> Real)
-/
lemma isClosedEmbedding_mapGLInt : Topology.IsClosedEmbedding (mapGL ℝ : SL n ℤ → GL n ℝ) :=
  isClosedEmbedding_mapGL Real.isClosedEmbedding_intCast

end Matrix.SpecialLinearGroup

/-- Arithmetic subgroups of `GL(2, ℝ)` are discrete. -/
/-
**Subgroup.IsArithmetic.discreteTopology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subgroup.IsArithmetic.discreteTopology {𝒢 : Subgroup (GL (Fin 2) Real)} [I
sArithmetic 𝒢] : DiscreteTopology 𝒢
参数：GL (Fin 2) Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.Commensurable.discreteTopology_iff`：Subgroup.Commensurable.disc
reteTopology_iff {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup 
G] [T2Space G] {H K : Subgroup G}…
· 使用定理 `Units.instIsTopologicalGroupOfContinuousMul`：∀ {α : Type u} [inst : Mono
id α] [inst_1 : TopologicalSpace α] [ContinuousMul α], IsTopologicalGroup αˣ
· 使用定理 `instContinuousMulMatrixOfContinuousAdd`：∀ {n : Type u_5} {R : Type u_8} 
[inst : TopologicalSpace R] [inst_1 : Fintype n] [inst_2 : Mul R]   [inst_3 : Ad
dCommMonoid R] [ContinuousAd…
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
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Subgroup.IsArithmetic.is_commensurable`：∀ {𝒢 : Subgroup (GL (Fin 2) ℝ)} 
[self : 𝒢.IsArithmetic], 𝒢.Commensurable (Matrix.SpecialLinearGroup.mapGL ℝ).ran
ge

--- 原说明 ---
Arithmetic subgroups of `GL(2, ℝ)` are discrete.
-/
instance Subgroup.IsArithmetic.discreteTopology {𝒢 : Subgroup (GL (Fin 2) ℝ)} [IsArithmetic 𝒢] :
    DiscreteTopology 𝒢 := by
  rw [is_commensurable.discreteTopology_iff]
  infer_instance

section adjoinNeg

variable {R : Type*} [Ring R]

/-- Given a subgroup `𝒢` of `GL n R`, this is the subgroup generated by `𝒢` and `-1`. -/
/-
**Subgroup.adjoinNegOne** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subgroup.adjoinNegOne (𝒢 : Subgroup (GL n R)) : Subgroup (GL n R) where ca
rrier
参数：𝒢 : Subgroup (GL n R)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a subgroup `𝒢` of `GL n R`, this is the subgroup generated by `𝒢` and `-1`
.
-/
def Subgroup.adjoinNegOne (𝒢 : Subgroup (GL n R)) : Subgroup (GL n R) where
  carrier := {g | g ∈ 𝒢 ∨ -g ∈ 𝒢}
  mul_mem' ha hb := by
    rcases ha with ha | ha <;>
      rcases hb with hb | hb <;>
      · have := mul_mem ha hb
        aesop
  one_mem' := by simp
  inv_mem' ha := by
    rcases ha with (ha | ha) <;>
    · have := inv_mem ha
      aesop
/-
**Subgroup.mem_adjoinNegOne_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2
} [inst_2 : Ring R] {𝒢 : Subgroup (GL n R)}   {g : GL n R}, g ∈ 𝒢.adjoinNegOne ↔
 g ∈ 𝒢 ∨ -g ∈ 𝒢
参数：GL n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma Subgroup.mem_adjoinNegOne_iff {𝒢 : Subgroup (GL n R)} {g : GL n R} :
    g ∈ 𝒢.adjoinNegOne ↔ g ∈ 𝒢 ∨ -g ∈ 𝒢 :=
  Iff.rfl
/-
**Subgroup.le_adjoinNegOne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.le_adjoinNegOne (𝒢 : Subgroup (GL n R)) : 𝒢 <= 𝒢.adjoinNegOne
参数：𝒢 : Subgroup (GL n R)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Subgroup.le_adjoinNegOne (𝒢 : Subgroup (GL n R)) : 𝒢 ≤ 𝒢.adjoinNegOne :=
  fun _ hg ↦ .inl hg
/-
**Subgroup.negOne_mem_adjoinNegOne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.negOne_mem_adjoinNegOne (𝒢 : Subgroup (GL n R)) : -1 in 𝒢.adjoinN
egOne
参数：𝒢 : Subgroup (GL n R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma Subgroup.negOne_mem_adjoinNegOne (𝒢 : Subgroup (GL n R)) : -1 ∈ 𝒢.adjoinNegOne := by simp
/-
**Subgroup.adjoinNegOne_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2
} [inst_2 : Ring R] {𝒢 : Subgroup (GL n R)},   𝒢.adjoinNegOne = 𝒢 ↔ -1 ∈ 𝒢
参数：GL n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.negOne_mem_adjoinNegOne`：Subgroup.negOne_mem_adjoinNegOne (𝒢 : 
Subgroup (GL n R)) : -1 in 𝒢.adjoinNegOne
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用引理 `Subgroup.le_adjoinNegOne`：Subgroup.le_adjoinNegOne (𝒢 : Subgroup (GL n R
)) : 𝒢 <= 𝒢.adjoinNegOne
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
@[simp] lemma Subgroup.adjoinNegOne_eq_self_iff {𝒢 : Subgroup (GL n R)} :
    𝒢.adjoinNegOne = 𝒢 ↔ -1 ∈ 𝒢 :=
  ⟨fun h ↦ h ▸ negOne_mem_adjoinNegOne 𝒢, fun hG ↦ 𝒢.le_adjoinNegOne.antisymm'
    fun g hg ↦ hg.elim id (fun h ↦ by simpa using mul_mem hG h)⟩
/-
**Subgroup.relindex_adjoinNegOne_eq_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.relindex_adjoinNegOne_eq_two {𝒢 : Subgroup (GL n R)} (h𝒢 : -1 ∉ 𝒢
) : 𝒢.relIndex 𝒢.adjoinNegOne = 2
参数：GL n R；h𝒢 : -1 ∉ 𝒢。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Subgroup.relIndex_eq_two_iff_exists_notMem_and`：relIndex_eq_two_iff_exis
ts_notMem_and : H.relIndex K = 2 ↔ exists a in K, a ∉ H ∧ forall b in K, (b * a 
in H) ∨ (b in H)
· 使用引理 `Subgroup.negOne_mem_adjoinNegOne`：Subgroup.negOne_mem_adjoinNegOne (𝒢 : 
Subgroup (GL n R)) : -1 in 𝒢.adjoinNegOne
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma Subgroup.relindex_adjoinNegOne_eq_two {𝒢 : Subgroup (GL n R)} (h𝒢 : -1 ∉ 𝒢) :
    𝒢.relIndex 𝒢.adjoinNegOne = 2 := by
  refine relIndex_eq_two_iff_exists_notMem_and.mpr ⟨_, 𝒢.negOne_mem_adjoinNegOne, h𝒢, ?_⟩
  simp [mem_adjoinNegOne_iff, or_comm]
/-
**Subgroup.relIndex_adjoinNegOne_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.relIndex_adjoinNegOne_ne_zero (𝒢 : Subgroup (GL n R)) : 𝒢.relInde
x 𝒢.adjoinNegOne != 0
参数：𝒢 : Subgroup (GL n R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.adjoinNegOne_eq_self_iff`：∀ {n : Type u_1} [inst : Fintype n] [
inst_1 : DecidableEq n] {R : Type u_2} [inst_2 : Ring R] {𝒢 : Subgroup (GL n R)}
,   𝒢.adjoinNegOne = 𝒢 …
· 使用定理 `Subgroup.relIndex_self`：relIndex_self : H.relIndex H = 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Subgroup.relindex_adjoinNegOne_eq_two`：Subgroup.relindex_adjoinNegOne_eq
_two {𝒢 : Subgroup (GL n R)} (h𝒢 : -1 ∉ 𝒢) : 𝒢.relIndex 𝒢.adjoinNegOne = 2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
-/
lemma Subgroup.relIndex_adjoinNegOne_ne_zero (𝒢 : Subgroup (GL n R)) :
    𝒢.relIndex 𝒢.adjoinNegOne ≠ 0 := by
  by_cases hG : -1 ∈ 𝒢
  · simp [adjoinNegOne_eq_self_iff.mpr hG]
  · simp [𝒢.relindex_adjoinNegOne_eq_two hG]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (𝒢 : Subgroup (GL n R)) : Subgroup.IsFiniteRelIndex 𝒢 𝒢.adjoinNegOne :=
  ⟨𝒢.relIndex_adjoinNegOne_ne_zero⟩
/-
**Subgroup.commensurable_adjoinNegOne_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.commensurable_adjoinNegOne_self (𝒢 : Subgroup (GL n R)) : Commens
urable 𝒢.adjoinNegOne 𝒢
参数：𝒢 : Subgroup (GL n R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.relIndex_eq_one`：relIndex_eq_one : H.relIndex K = 1 ↔ K <= H
· 使用引理 `Subgroup.le_adjoinNegOne`：Subgroup.le_adjoinNegOne (𝒢 : Subgroup (GL n R
)) : 𝒢 <= 𝒢.adjoinNegOne
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Subgroup.relIndex_adjoinNegOne_ne_zero`：Subgroup.relIndex_adjoinNegOne_n
e_zero (𝒢 : Subgroup (GL n R)) : 𝒢.relIndex 𝒢.adjoinNegOne != 0
-/
lemma Subgroup.commensurable_adjoinNegOne_self (𝒢 : Subgroup (GL n R)) :
    Commensurable 𝒢.adjoinNegOne 𝒢 :=
  ⟨by simp [Subgroup.relIndex_eq_one.mpr 𝒢.le_adjoinNegOne], 𝒢.relIndex_adjoinNegOne_ne_zero⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (𝒢 : Subgroup (GL n R)) [DiscreteTopology 𝒢] :
    DiscreteTopology 𝒢.adjoinNegOne := by
  rwa [𝒢.commensurable_adjoinNegOne_self.discreteTopology_iff]

section CommRing

variable {R : Type*} [CommRing R]

/-
**Subgroup.hasDetPlusMinusOne_adjoinNegOne_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgro
up`。
形式化陈述：∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_3
} [inst_2 : CommRing R]   {𝒢 : Subgroup (GL n R)}, 𝒢.adjoinNegOne.HasDetPlusMinu
sOne ↔ 𝒢.HasDetPlusMinusOne
参数：GL n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.HasDetPlusMinusOne.det_eq`：∀ {n : Type u_1} {inst : Fintype n} 
{inst_1 : DecidableEq n} {R : Type u_2} {inst_2 : CommRing R}   {Γ : Subgroup (G
L n R)} [self : Γ.HasDet…
· 使用引理 `Subgroup.le_adjoinNegOne`：Subgroup.le_adjoinNegOne (𝒢 : Subgroup (GL n R
)) : 𝒢 <= 𝒢.adjoinNegOne
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `Matrix.det_neg`：det_neg (A : Matrix n n R) : det (-A) = (-1) ^ Fintype.c
ard n * det A
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Odd.neg_one_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistrib
Neg α] {n : ℕ}, Odd n → (-1) ^ n = -1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
-/
@[simp] lemma Subgroup.hasDetPlusMinusOne_adjoinNegOne_iff {𝒢 : Subgroup (GL n R)} :
    𝒢.adjoinNegOne.HasDetPlusMinusOne ↔ 𝒢.HasDetPlusMinusOne := by
  refine ⟨fun _ ↦ ⟨fun {g} hg ↦ HasDetPlusMinusOne.det_eq (𝒢.le_adjoinNegOne hg)⟩, fun _ ↦ ⟨?_⟩⟩
  rintro g (hg | hg)
  · exact HasDetPlusMinusOne.det_eq hg
  · by_cases hn : Even (Fintype.card n)
    · convert! HasDetPlusMinusOne.det_eq hg using 1 <;>
        simp [Units.ext_iff, det_neg, hn]
    · convert! (HasDetPlusMinusOne.det_eq hg).symm using 1 <;>
        simp [Units.ext_iff, det_neg, Nat.not_even_iff_odd.mp hn, neg_eq_iff_eq_neg]
/-
**Subgroup.hasDetOne_adjoinNegOne_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.hasDetOne_adjoinNegOne_iff {𝒢 : Subgroup (GL n R)} (hn : Even (Fi
ntype.card n)) : 𝒢.adjoinNegOne.HasDetOne ↔ 𝒢.HasDetOne
参数：GL n R；hn : Even (Fintype.card n)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.HasDetOne.det_eq`：∀ {n : Type u_1} {inst : Fintype n} {inst_1 :
 DecidableEq n} {R : Type u_2} {inst_2 : CommRing R}   {Γ : Subgroup (GL n R)} [
self : Γ.HasDet…
· 使用引理 `Subgroup.le_adjoinNegOne`：Subgroup.le_adjoinNegOne (𝒢 : Subgroup (GL n R
)) : 𝒢 <= 𝒢.adjoinNegOne
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `Matrix.det_neg`：det_neg (A : Matrix n n R) : det (-A) = (-1) ^ Fintype.c
ard n * det A
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma Subgroup.hasDetOne_adjoinNegOne_iff {𝒢 : Subgroup (GL n R)} (hn : Even (Fintype.card n)) :
    𝒢.adjoinNegOne.HasDetOne ↔ 𝒢.HasDetOne := by
  refine ⟨fun _ ↦ ⟨fun {g} hg ↦ HasDetOne.det_eq (𝒢.le_adjoinNegOne hg)⟩, fun _ ↦ ⟨?_⟩⟩
  rintro g (hg | hg)
  · exact HasDetOne.det_eq hg
  · simpa [Units.ext_iff, det_neg, hn] using HasDetOne.det_eq hg
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {𝒢 : Subgroup (GL n R)} [𝒢.HasDetPlusMinusOne] :
    𝒢.adjoinNegOne.HasDetPlusMinusOne :=
  Subgroup.hasDetPlusMinusOne_adjoinNegOne_iff.2 ‹_›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {𝒢 : Subgroup (GL n R)} [𝒢.HasDetOne] [Fact (Even (Fintype.card n))] :
    𝒢.adjoinNegOne.HasDetOne :=
  (Subgroup.hasDetOne_adjoinNegOne_iff Fact.out).2 ‹_›

end CommRing

/-
**Subgroup.instIsArithmeticAdjoinNegOne** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subgroup.instIsArithmeticAdjoinNegOne {𝒢 : Subgroup (GL (Fin 2) Real)} [𝒢.
IsArithmetic] : 𝒢.adjoinNegOne.IsArithmetic
参数：GL (Fin 2) Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Commensurable.trans`：trans {H K L : Subgroup G} (hhk : Commensu
rable H K) (hkl : Commensurable K L) : Commensurable H L
· 使用引理 `Subgroup.commensurable_adjoinNegOne_self`：Subgroup.commensurable_adjoinN
egOne_self (𝒢 : Subgroup (GL n R)) : Commensurable 𝒢.adjoinNegOne 𝒢
· 使用定理 `Subgroup.IsArithmetic.is_commensurable`：∀ {𝒢 : Subgroup (GL (Fin 2) ℝ)} 
[self : 𝒢.IsArithmetic], 𝒢.Commensurable (Matrix.SpecialLinearGroup.mapGL ℝ).ran
ge
-/
instance Subgroup.instIsArithmeticAdjoinNegOne {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] :
    𝒢.adjoinNegOne.IsArithmetic :=
  ⟨(𝒢.commensurable_adjoinNegOne_self).trans IsArithmetic.is_commensurable⟩

end adjoinNeg

