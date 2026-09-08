/-
Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar
-/
module

public import Batteries.Data.Fin.Fold
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Subpaths and concatenation of paths

This file defines `Path.subpath` as a restriction of a path to a subinterval, reparameterized to
have domain `[0, 1]` and possibly with a reverse of direction. It then defines `Path.concat` as
a way to concatenate finite sequences of paths with compatible endpoints.

The main result `Path.Homotopy.concatSubpath` shows that subpaths concatenate nicely.
In particular: following the subpaths of `γ` from `t i` to `t (i + 1)` for `0 ≤ i < n` is
homotopic to the subpath of `γ` from `t 0` to `t n`.

## TODO

Prove that `Path.truncateOfLE` and `Path.subpath` are reparameterizations of each other.
(`Path.subpath` is still a useful definition because it works without assuming an order on `t₀` and
`t₁`, and is convenient for concrete manipulations.)
-/

@[expose] public noncomputable section

open Fin Function Set unitInterval

variable {X : Type*} [TopologicalSpace X] {a b : X}

namespace Path

/-!
## Subpaths
-/

@[deprecated (since := "2026-03-20")]
alias subpathAux := Icc.convexComb

@[deprecated (since := "2026-03-20")]
alias subpathAux_zero := Icc.convexComb_zero

@[deprecated (since := "2026-03-20")]
alias subpathAux_one := Icc.convexComb_one

@[deprecated (since := "2026-03-20")]
alias subpathAux_continuous := Icc.continuous_convexComb_prod

/-- The subpath of `γ` from `t₀` to `t₁`. -/
/-
**Path.subpath** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：subpath (γ : Path a b) (t₀ t₁ : I) : Path (γ t₀) (γ t₁) where toFun
参数：γ : Path a b；t₀ t₁ : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subpath of `γ` from `t₀` to `t₁`.
-/
def subpath (γ : Path a b) (t₀ t₁ : I) : Path (γ t₀) (γ t₁) where
  toFun := γ ∘ Icc.convexComb t₀ t₁
  source' := by simp
  target' := by simp

/-- Reversing `γ.subpath t₀ t₁` results in `γ.subpath t₁ t₀`. -/
@[simp]
/-
**Path.symm_subpath** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：symm_subpath (γ : Path a b) (t₀ t₁ : I) : symm (γ.subpath t₀ t₁) = γ.subpa
th t₁ t₀
参数：γ : Path a b；t₀ t₁ : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.symm_apply`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} 
(γ : Path x y) (a : ↑unitInterval),   γ.symm a = (⇑γ ∘ unitInterval.symm) a
· 使用定理 `Set.Icc.convexComb_symm`：convexComb_symm {a b : Real} (x y : Icc a b) (t
 : unitInterval) : convexComb x y (unitInterval.symm t) = convexComb y x t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Reversing `γ.subpath t₀ t₁` results in `γ.subpath t₁ t₀`.
-/
theorem symm_subpath (γ : Path a b) (t₀ t₁ : I) : symm (γ.subpath t₀ t₁) = γ.subpath t₁ t₀ := by
  ext s
  simp [subpath]
/-
**Path.range_subpathAux** 是 Mathlib 中的一个引理，位于命名空间 `Path`。
形式化陈述：range_subpathAux (t₀ t₁ : I) : range (Icc.convexComb t₀ t₁) = uIcc t₀ t₁
参数：t₀ t₁ : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_eq_iff`：range_eq_iff (f : α -> β) (s : Set β) : range f = s ↔ 
(forall a, f a in s) ∧ forall b in s, exists a, f a = b
· 使用定理 `convex_uIcc`：convex_uIcc (r s : β) : Convex 𝕜 (uIcc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Set.left_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, a ∈ Se
t.uIcc a b
· 使用定理 `Set.right_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, b ∈ S
et.uIcc a b
· 使用定理 `unitInterval.one_minus_nonneg`：one_minus_nonneg (x : I) : 0 <= 1 - (x : 
Real)
· 使用定理 `unitInterval.nonneg`：nonneg (x : I) : 0 <= (x : Real)
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `segment_eq_image`：segment_eq_image (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜 =
> (1 - θ) • x + θ • y) '' Icc (0 : 𝕜) 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `segment_eq_uIcc`：segment_eq_uIcc (x y : 𝕜) : [x -[𝕜] y] = uIcc x y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
lemma range_subpathAux (t₀ t₁ : I) : range (Icc.convexComb t₀ t₁) = uIcc t₀ t₁ := by
  rw [range_eq_iff]
  constructor
  · intro s
    exact convex_uIcc (t₀ : ℝ) t₁ left_mem_uIcc right_mem_uIcc
      (one_minus_nonneg s) (nonneg s) (sub_add_cancel _ _)
  · intro t (ht : (t : ℝ) ∈ uIcc (t₀ : ℝ) (t₁ : ℝ))
    rw [← segment_eq_uIcc, segment_eq_image] at ht
    obtain ⟨s, hs, hst⟩ := ht
    use ⟨s, hs⟩
    ext
    exact hst

/-- The range of a subpath is the image of the original path on the relevant interval. -/
@[simp]
/-
**Path.range_subpath** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：range_subpath (γ : Path a b) (t₀ t₁ : I) : range (γ.subpath t₀ t₁) = γ '' 
(uIcc t₀ t₁)
参数：γ : Path a b；t₀ t₁ : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Path.range_subpathAux`：range_subpathAux (t₀ t₁ : I) : range (Icc.convexC
omb t₀ t₁) = uIcc t₀ t₁
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Path.subpath.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] {a b : X
} (γ : Path a b) (t₀ t₁ : ↑unitInterval),   γ.subpath t₀ t₁ = { toFun := ⇑γ ∘ Se
t.Icc.c…
· 使用定理 `Path.coe_mk'`：coe_mk' (f : C(I, X)) (h₁ h₂) : ⇑(mk f h₁ h₂ : Path x y) =
 f
· 使用定理 `ContinuousMap.coe_mk`：coe_mk (f : X -> Y) (h : Continuous f) : ⇑(⟨f, h⟩ 
: C(X, Y)) = f

--- 原说明 ---
The range of a subpath is the image of the original path on the relevant interva
l.
-/
theorem range_subpath (γ : Path a b) (t₀ t₁ : I) :
    range (γ.subpath t₀ t₁) = γ '' (uIcc t₀ t₁) := by
  rw [← range_subpathAux, ← range_comp, subpath, coe_mk', ContinuousMap.coe_mk]
/-
**Path.range_subpath_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Path`。
形式化陈述：range_subpath_of_le (γ : Path a b) (t₀ t₁ : I) (h : t₀ <= t₁) : range (γ.s
ubpath t₀ t₁) = γ '' (Icc t₀ t₁)
参数：γ : Path a b；t₀ t₁ : I；h : t₀ <= t₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.range_subpath`：range_subpath (γ : Path a b) (t₀ t₁ : I) : range (γ.
subpath t₀ t₁) = γ '' (uIcc t₀ t₁)
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_subpath_of_le (γ : Path a b) (t₀ t₁ : I) (h : t₀ ≤ t₁) :
    range (γ.subpath t₀ t₁) = γ '' (Icc t₀ t₁) := by
  simp [h]
/-
**Path.range_subpath_of_ge** 是 Mathlib 中的一个引理，位于命名空间 `Path`。
形式化陈述：range_subpath_of_ge (γ : Path a b) (t₀ t₁ : I) (h : t₁ <= t₀) : range (γ.s
ubpath t₀ t₁) = γ '' (Icc t₁ t₀)
参数：γ : Path a b；t₀ t₁ : I；h : t₁ <= t₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.range_subpath`：range_subpath (γ : Path a b) (t₀ t₁ : I) : range (γ.
subpath t₀ t₁) = γ '' (uIcc t₀ t₁)
· 使用引理 `Set.uIcc_of_ge`：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_subpath_of_ge (γ : Path a b) (t₀ t₁ : I) (h : t₁ ≤ t₀) :
    range (γ.subpath t₀ t₁) = γ '' (Icc t₁ t₀) := by
  simp [h]

/-- The subpath of `γ` from `t` to `t` is just the constant path at `γ t`. -/
@[simp]
/-
**Path.subpath_self** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：subpath_self (γ : Path a b) (t : I) : γ.subpath t t = Path.refl (γ t)
参数：γ : Path a b；t : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc.convexComb_eq`：convexComb_eq {a b : Real} (x : Icc a b) (t : uni
tInterval) : convexComb x x t = x
· 使用定理 `Path.refl_apply`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (x
_1 : ↑unitInterval), (Path.refl x) x_1 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The subpath of `γ` from `t` to `t` is just the constant path at `γ t`.
-/
theorem subpath_self (γ : Path a b) (t : I) : γ.subpath t t = Path.refl (γ t) := by
  ext s
  simp [subpath]

/-- The subpath of `γ` from `0` to `1` is just `γ`, with a slightly different type. -/
@[simp]
/-
**Path.subpath_zero_one** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：subpath_zero_one (γ : Path a b) : γ.subpath 0 1 = γ.cast γ.source γ.target
参数：γ : Path a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc.convexComb_zero_one`：convexComb_zero_one (t : unitInterval) : co
nvexComb 0 1 t = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The subpath of `γ` from `0` to `1` is just `γ`, with a slightly different type.
-/
theorem subpath_zero_one (γ : Path a b) : γ.subpath 0 1 = γ.cast γ.source γ.target := by
  ext s
  simp [subpath]

/-- For a path `γ`, `γ.subpath` gives a "continuous family of paths", by which we mean
the uncurried function which maps `(t₀, t₁, s)` to `γ.subpath t₀ t₁ s` is continuous. -/
@[continuity]
/-
**Path.subpath_continuous_family** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：subpath_continuous_family (γ : Path a b) : Continuous (fun x => γ.subpath 
x.1 x.2.1 x.2.2 : I × I × I -> X)
参数：γ : Path a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `Set.Icc.continuous_convexComb_prod`：continuous_convexComb_prod {a b : Re
al} : Continuous fun x : Icc a b × Icc a b × unitInterval => Icc.convexComb x.1 
x.2.1 x.2.2

--- 原说明 ---
For a path `γ`, `γ.subpath` gives a "continuous family of paths", by which we me
an
the uncurried function which maps `(t₀, t₁, s)` to `γ.subpath t₀ t₁ s` is contin
uous.
-/
theorem subpath_continuous_family (γ : Path a b) :
    Continuous (fun x => γ.subpath x.1 x.2.1 x.2.2 : I × I × I → X) :=
  Continuous.comp' (map_continuous γ) Set.Icc.continuous_convexComb_prod

namespace Homotopy

/-- Auxiliary homotopy for `Path.Homotopy.subpathTransSubpath` which includes an unnecessary
copy of `Path.refl`. -/
/-
**Path.Homotopy.subpathTransSubpathRefl** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy
`。
形式化陈述：subpathTransSubpathRefl (γ : Path a b) (t₀ t₁ t₂ : I) : Homotopy ((γ.subpa
th t₀ t₁).trans (γ.subpath t₁ t₂)) ((γ.subpath t₀ t₂).trans (Path.refl _)) where
 toFun x
参数：γ : Path a b；t₀ t₁ t₂ : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary homotopy for `Path.Homotopy.subpathTransSubpath` which includes an unn
ecessary
copy of `Path.refl`.
-/
def subpathTransSubpathRefl (γ : Path a b) (t₀ t₁ t₂ : I) : Homotopy
    ((γ.subpath t₀ t₁).trans (γ.subpath t₁ t₂)) ((γ.subpath t₀ t₂).trans (Path.refl _)) where
  toFun x := ((γ.subpath t₀ (Icc.convexComb t₁ t₂ x.1)).trans (γ.subpath _ t₂)) x.2
  continuous_toFun := by
    let γ₁ (t : I) := γ.subpath t₀ (Icc.convexComb t₁ t₂ t)
    let γ₂ (t : I) := γ.subpath (Icc.convexComb t₁ t₂ t) t₂
    refine Path.trans_continuous_family γ₁ ?_ γ₂ ?_ <;>
    refine γ.subpath_continuous_family.comp (.prodMk ?_ <| .prodMk ?_ ?_) <;>
    fun_prop
  map_zero_left _ := by rw [Icc.convexComb_zero, coe_toContinuousMap]
  map_one_left _ := by rw [Icc.convexComb_one, subpath_self, coe_toContinuousMap]
  prop' _ _ hx := by
    rcases hx with rfl | rfl <;>
    simp

/-- Following the subpath of `γ` from `t₀` to `t₁`, and then that from `t₁` to `t₂`,
is in natural homotopy with following the subpath of `γ` from `t₀` to `t₂`. -/
/-
**Path.Homotopy.subpathTransSubpath** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：subpathTransSubpath (γ : Path a b) (t₀ t₁ t₂ : I) : Homotopy ((γ.subpath t
₀ t₁).trans (γ.subpath t₁ t₂)) (γ.subpath t₀ t₂)
参数：γ : Path a b；t₀ t₁ t₂ : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Following the subpath of `γ` from `t₀` to `t₁`, and then that from `t₁` to `t₂`,
is in natural homotopy with following the subpath of `γ` from `t₀` to `t₂`.
-/
def subpathTransSubpath (γ : Path a b) (t₀ t₁ t₂ : I) : Homotopy
    ((γ.subpath t₀ t₁).trans (γ.subpath t₁ t₂)) (γ.subpath t₀ t₂) :=
  trans (subpathTransSubpathRefl γ t₀ t₁ t₂) (transRefl _)

end Homotopy

/-!
## Concatenation of paths
-/

variable {n : ℕ}

/-- Concatenation of a sequence of paths with compatible endpoints. -/
/-
**Path.concat** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：concat (p : Fin (n + 1) -> X) (F : (k : Fin n) -> Path (p k.castSucc) (p k
.succ)) : Path (p 0) (p (last n))
参数：p : Fin (n + 1) -> X；F : (k : Fin n) -> Path (p k.castSucc) (p k.succ)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Concatenation of a sequence of paths with compatible endpoints.
-/
def concat (p : Fin (n + 1) → X) (F : (k : Fin n) → Path (p k.castSucc) (p k.succ)) :
    Path (p 0) (p (last n)) :=
  dfoldl n (fun i => Path (p 0) (p i)) (fun i ih => ih.trans (F i)) (refl (p 0))

/-- Concatenating zero paths yields the constant path (the identity of `Path.trans`). -/
/-
**Path.concat_zero** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] (p : Fin 1 → X) (F : (k : Fin
 0) → Path (p k.castSucc) (p k.succ)),   Path.concat p F = Path.refl (p 0)
参数：p : Fin 1 → X；F : (k : Fin 0) → Path (p k.castSucc) (p k.succ)；p 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.concat.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] {n : ℕ} (
p : Fin (n + 1) → X)   (F : (k : Fin n) → Path (p k.castSucc) (p k.succ)),   Pat
h.conc…
· 使用定理 `Fin.dfoldl_zero`：∀ {α : Fin (0 + 1) → Type u_1} (f : (i : Fin 0) → α i.c
astSucc → α i.succ) (x : α 0), Fin.dfoldl 0 α f x = x

--- 原说明 ---
Concatenating zero paths yields the constant path (the identity of `Path.trans`)
.
-/
@[simp] lemma concat_zero (p : Fin 1 → X) (F) :
    concat p F = refl (p 0) := by
  rw [concat, dfoldl_zero]

/-- Concatenating `n + 1` paths corresponds to concatenating `n` paths and then the last path. -/
/-
**Path.concat_succ** 是 Mathlib 中的一个引理，位于命名空间 `Path`。
形式化陈述：concat_succ (p : Fin (n + 2) -> X) (F) : concat p F = (concat (p ∘ castSuc
c) (fun k => (F k.castSucc))).trans (F (last n))
参数：p : Fin (n + 2) -> X；F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.concat.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] {n : ℕ} (
p : Fin (n + 1) → X)   (F : (k : Fin n) → Path (p k.castSucc) (p k.succ)),   Pat
h.conc…
· 使用定理 `Fin.dfoldl_succ_last`：∀ {n : ℕ} {α : Fin (n + 1 + 1) → Type u_1} (f : (i
 : Fin (n + 1)) → α i.castSucc → α i.succ) (x : α 0),   Fin.dfoldl (n + 1) α f x
 = f (Fin.…

--- 原说明 ---
Concatenating `n + 1` paths corresponds to concatenating `n` paths and then the 
last path.
-/
lemma concat_succ (p : Fin (n + 2) → X) (F) :
    concat p F = (concat (p ∘ castSucc) (fun k ↦ (F k.castSucc))).trans (F (last n)) := by
  rw [concat, dfoldl_succ_last]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Concatenating the constant path at `x` with itself just yields the constant path at `x`. -/
@[simp]
/-
**Path.concat_refl** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：concat_refl (n : Nat) (x : X) : concat (fun (_ : Fin (n + 1)) => x) (fun _
 => Path.refl x) = Path.refl x
参数：n : Nat；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.concat_zero`：∀ {X : Type u_1} [inst : TopologicalSpace X] (p : Fin 
1 → X) (F : (k : Fin 0) → Path (p k.castSucc) (p k.succ)),   Path.concat p F = P
ath.re…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Path.concat_succ`：concat_succ (p : Fin (n + 2) -> X) (F) : concat p F = 
(concat (p ∘ castSucc) (fun k => (F k.castSucc))).trans (F (last n))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Path.refl_trans_refl`：refl_trans_refl {a : X} : (Path.refl a).trans (Pat
h.refl a) = Path.refl a

--- 原说明 ---
Concatenating the constant path at `x` with itself just yields the constant path
 at `x`.
-/
theorem concat_refl (n : ℕ) (x : X) :
    concat (fun (_ : Fin (n + 1)) ↦ x) (fun _ ↦ Path.refl x) = Path.refl x := by
  induction n with
  | zero => rw [concat_zero]
  | succ _ _ =>
    rw [concat_succ]
    convert! refl_trans_refl

namespace Homotopy

/-- Given two sequences of paths `F` and `G`, and a sequence `H` of homotopies between them,
there is a natural homotopy between `concat _ F` and `concat _ G`. -/
/-
**Path.Homotopy.concat** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：{X : Type u_1} →   [inst : TopologicalSpace X] →     {n : ℕ} →       (p : 
Fin (n + 1) → X) →         (F G : (k : Fin n) → Path (p k.castSucc) (p k.succ)) 
→           ((k : Fin n) → (F k).Homotopy (G k)) → (Path.concat p F).Homotopy (P
ath.concat p G)
参数：p : Fin (n + 1) → X；F G : (k : Fin n) → Path (p k.castSucc) (p k.succ)；(k : F
in n) → (F k).Homotopy (G k)；Path.concat p F；Path.concat p G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two sequences of paths `F` and `G`, and a sequence `H` of homotopies betwe
en them,
there is a natural homotopy between `concat _ F` and `concat _ G`.
-/
protected def concat (p : Fin (n + 1) → X) (F G : (k : Fin n) → Path (p k.castSucc) (p k.succ))
    (H : (k : Fin n) → (F k).Homotopy (G k)) : Homotopy (concat p F) (concat p G) := by
  induction n with
  | zero =>
    rw [concat_zero, concat_zero]
    exact refl (Path.refl _)
  | succ n ih =>
    rw [concat_succ, concat_succ]
    exact hcomp (ih _ _ _ (fun k ↦ H k.castSucc)) (H (last n))

/-- Given a path `γ` and a sequence `t` of `n + 1` points in `[0, 1]`, there is a natural homotopy
between the concatenation of paths `γ.subpath (t k) (t (k + 1))`, and `γ.subpath (t 0) (t n)`. -/
/-
**Path.Homotopy.concatSubpath** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：concatSubpath (γ : Path a b) (t : Fin (n + 1) -> I) : Homotopy (concat (γ 
∘ t) (fun k => γ.subpath (t k.castSucc) (t k.succ))) (γ.subpath (t 0) (t (last n
)))
参数：γ : Path a b；t : Fin (n + 1) -> I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a path `γ` and a sequence `t` of `n + 1` points in `[0, 1]`, there is a na
tural homotopy
between the concatenation of paths `γ.subpath (t k) (t (k + 1))`, and `γ.subpath
 (t 0) (t n)`.
-/
def concatSubpath (γ : Path a b) (t : Fin (n + 1) → I) :
    Homotopy
      (concat (γ ∘ t) (fun k ↦ γ.subpath (t k.castSucc) (t k.succ)))
      (γ.subpath (t 0) (t (last n))) := by
  induction n with
  | zero =>
    simp only [concat_zero, reduceLast, subpath_self]
    exact refl _
  | succ n ih =>
    rw [concat_succ]
    exact trans ((ih (t ∘ castSucc)).hcomp (refl _)) (subpathTransSubpath γ _ _ _)

end Homotopy

namespace Homotopic

/-- Concatenating one path `F 0` is homotopic to that path. -/
/-
**Path.Homotopic.concat_one** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：concat_one (p : Fin 2 -> X) (F) : Homotopic (concat p F) (F 0)
参数：p : Fin 2 -> X；F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Path.concat_succ`：concat_succ (p : Fin (n + 2) -> X) (F) : concat p F = 
(concat (p ∘ castSucc) (fun k => (F k.castSucc))).trans (F (last n))
· 使用定理 `Path.concat_zero`：∀ {X : Type u_1} [inst : TopologicalSpace X] (p : Fin 
1 → X) (F : (k : Fin 0) → Path (p k.castSucc) (p k.succ)),   Path.concat p F = P
ath.re…

--- 原说明 ---
Concatenating one path `F 0` is homotopic to that path.
-/
theorem concat_one (p : Fin 2 → X) (F) :
    Homotopic (concat p F) (F 0) := by
  simpa [concat_succ] using ⟨Homotopy.reflTrans _⟩

/-- Concatenating two paths `F 0` and `F 1` is homotopic to `Path.trans (F 0) (F 1)`. -/
/-
**Path.Homotopic.concat_two** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：concat_two (p : Fin 3 -> X) (F) : Homotopic (concat p F) ((F 0).trans (F 1
))
参数：p : Fin 3 -> X；F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Path.concat_succ`：concat_succ (p : Fin (n + 2) -> X) (F) : concat p F = 
(concat (p ∘ castSucc) (fun k => (F k.castSucc))).trans (F (last n))
· 使用定理 `Path.concat_zero`：∀ {X : Type u_1} [inst : TopologicalSpace X] (p : Fin 
1 → X) (F : (k : Fin 0) → Path (p k.castSucc) (p k.succ)),   Path.concat p F = P
ath.re…
· 使用定理 `Path.Homotopic.hcomp`：hcomp {p₀ p₁ : Path x₀ x₁} {q₀ q₁ : Path x₁ x₂} (h
p : p₀.Homotopic p₁) (hq : q₀.Homotopic q₁) : (p₀.trans q₀).Homotopic (p₁.trans 
q₁)
· 使用定理 `Path.Homotopic.refl`：refl (p : Path x₀ x₁) : p.Homotopic p

--- 原说明 ---
Concatenating two paths `F 0` and `F 1` is homotopic to `Path.trans (F 0) (F 1)`
.
-/
theorem concat_two (p : Fin 3 → X) (F) :
    Homotopic (concat p F) ((F 0).trans (F 1)) := by
  simpa [concat_succ] using hcomp ⟨Homotopy.reflTrans _⟩ (refl _)


/-- Alternative to `Path.Homotopy.concatHcomp` in terms of `Path.Homotopic`. -/
/-
**Path.Homotopic.concat_hcomp** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：concat_hcomp (p : Fin (n + 1) -> X) (F G : (k : Fin n) -> Path (p k.castSu
cc) (p k.succ)) (h : (k : Fin n) -> (F k).Homotopic (G k)) : Homotopic (concat p
 F) (concat p G)
参数：p : Fin (n + 1) -> X；F G : (k : Fin n) -> Path (p k.castSucc) (p k.succ)；h : 
(k : Fin n) -> (F k).Homotopic (G k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
Alternative to `Path.Homotopy.concatHcomp` in terms of `Path.Homotopic`.
-/
theorem concat_hcomp (p : Fin (n + 1) → X) (F G : (k : Fin n) → Path (p k.castSucc) (p k.succ))
    (h : (k : Fin n) → (F k).Homotopic (G k)) : Homotopic (concat p F) (concat p G) :=
  ⟨Homotopy.concat p F G (fun k ↦ (h k).some)⟩

/-- Alternative to `Path.Homotopy.concatSubpath` in terms of `Path.Homotopic`. -/
@[simp]
/-
**Path.Homotopic.concat_subpath** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：concat_subpath (γ : Path a b) (t : Fin (n + 1) -> I) : Homotopic (concat (
γ ∘ t) (fun k => γ.subpath (t k.castSucc) (t k.succ))) (γ.subpath (t 0) (t (last
 n)))
参数：γ : Path a b；t : Fin (n + 1) -> I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
Alternative to `Path.Homotopy.concatSubpath` in terms of `Path.Homotopic`.
-/
theorem concat_subpath (γ : Path a b) (t : Fin (n + 1) → I) :
    Homotopic
      (concat (γ ∘ t) (fun k ↦ γ.subpath (t k.castSucc) (t k.succ)))
      (γ.subpath (t 0) (t (last n))) :=
  ⟨Homotopy.concatSubpath γ t⟩

end Path.Homotopic

end

