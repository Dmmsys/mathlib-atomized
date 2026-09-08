/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Connected.PathConnected

/-!
# Segment between 2 points as a bundled path

In this file we define `Path.segment a b : Path a b`
to be the path going from `a` to `b` along the straight segment with constant velocity `b - a`.

We also prove basic properties of this construction,
then use it to show that a nonempty convex set is path connected.
In particular, a topological vector space over `ℝ` is path connected.
-/

@[expose] public section

open AffineMap Set
open scoped Convex unitInterval

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

namespace Path

set_option backward.isDefEq.respectTransparency false in
/-- The path from `a` to `b` going along a straight line segment -/
@[simps]
/-
**Path.segment** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：{E : Type u_1} →   [inst : AddCommGroup E] →     [inst_1 : _root_.Module ℝ
 E] →       [inst_2 : TopologicalSpace E] → [ContinuousAdd E] → [ContinuousSMul 
ℝ E] → (a b : E) → Path a b
参数：a b : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The path from `a` to `b` going along a straight line segment
-/
protected def segment (a b : E) : Path a b where
  toFun t := lineMap a b (t : ℝ)
  continuous_toFun := by dsimp [lineMap]; fun_prop
  source' := by simp
  target' := by simp

@[simp]
/-
**Path.range_segment** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：range_segment (a b : E) : Set.range (Path.segment a b) = [a -[Real] b]
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `segment_eq_image_lineMap`：segment_eq_image_lineMap (x y : E) : [x -[𝕜] y
] = AffineMap.lineMap x y '' Icc (0 : 𝕜) 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_segment (a b : E) : Set.range (Path.segment a b) = [a -[ℝ] b] := by
  rw [segment_eq_image_lineMap, image_eq_range]
  simp only [← segment_apply]

@[simp]
/-
**Path.segment_same** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _root_.Module ℝ E] [ins
t_2 : TopologicalSpace E]   [inst_3 : ContinuousAdd E] [inst_4 : ContinuousSMul 
ℝ E] (a : E), Path.segment a a = Path.refl a
参数：a : E。
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
· 使用定理 `Path.segment_apply`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E]   [inst_3 : ContinuousAdd E] [in
st_4 : C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineMap.lineMap_same`：lineMap_same (p : P1) : lineMap p p = const k k 
p
· 使用定理 `Path.refl_apply`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (x
_1 : ↑unitInterval), (Path.refl x) x_1 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem segment_same (a : E) : Path.segment a a = .refl a := by ext; simp

@[simp]
/-
**Path.segment_symm** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _root_.Module ℝ E] [ins
t_2 : TopologicalSpace E]   [inst_3 : ContinuousAdd E] [inst_4 : ContinuousSMul 
ℝ E] (a b : E), (Path.segment a b).symm = Path.segment b a
参数：a b : E；Path.segment a b。
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
· 使用定理 `Path.symm_apply`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} 
(γ : Path x y) (a : ↑unitInterval),   γ.symm a = (⇑γ ∘ unitInterval.symm) a
· 使用定理 `Path.segment_apply`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E]   [inst_3 : ContinuousAdd E] [in
st_4 : C…
· 使用定理 `AffineMap.lineMap_apply_one_sub`：lineMap_apply_one_sub (p₀ p₁ : P1) (c :
 k) : lineMap p₀ p₁ (1 - c) = lineMap p₁ p₀ c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem segment_symm (a b : E) : (Path.segment a b).symm = .segment b a := by
  ext; simp

@[simp]
/-
**Path.segment_add_segment** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：segment_add_segment (a b c d : E) : (Path.segment a b).add (.segment c d) 
= .segment (a + c) (b + d)
参数：a b c d : E。
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
· 使用定理 `Path.add_apply`：∀ {X : Type u_1} [inst : TopologicalSpace X] [inst_1 : A
dd X] [inst_2 : ContinuousAdd X] {a₁ b₁ a₂ b₂ : X}   (γ₁ : Path a₁ b₁) (γ₂ : Pat
h a₂…
· 使用定理 `Path.segment_apply`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E]   [inst_3 : ContinuousAdd E] [in
st_4 : C…
· 使用定理 `AffineMap.lineMap_apply_module`：lineMap_apply_module (p₀ p₁ : V1) (c : k
) : lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem segment_add_segment (a b c d : E) :
    (Path.segment a b).add (.segment c d) = .segment (a + c) (b + d) := by
  ext
  simp [lineMap_apply_module, add_add_add_comm]

@[simp]
/-
**Path.cast_segment** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：cast_segment {a b c d : E} (hac : c = a) (hbd : d = b) : (Path.segment a b
).cast hac hbd = .segment c d
参数：hac : c = a；hbd : d = b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_segment {a b c d : E} (hac : c = a) (hbd : d = b) :
    (Path.segment a b).cast hac hbd = .segment c d := by
  subst_vars; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Path.eqOn_extend_segment** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：eqOn_extend_segment (a b : E) : EqOn (Path.segment a b).extend (AffineMap.
lineMap a b) I
参数：a b : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.extend_apply`：extend_apply {a b : X} (γ : Path a b) {t : Real} (ht 
: t in (Icc 0 1 : Set Real)) : γ.extend t = γ ⟨t, ht⟩
· 使用定理 `Path.segment_apply`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E]   [inst_3 : ContinuousAdd E] [in
st_4 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eqOn_extend_segment (a b : E) :
    EqOn (Path.segment a b).extend (AffineMap.lineMap a b) I := by
  intro t ht
  simp [ht]
/-
**Path.segment_injective_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：segment_injective_of_ne {a b : E} (hne : a != b) : Function.Injective (Pat
h.segment a b)
参数：hne : a != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `AffineMap.lineMap_injective`：lineMap_injective [IsDomain k] [IsTorsionFr
ee k V1] {p₀ p₁ : P1} (h : p₀ != p₁) : Function.Injective (lineMap p₀ p₁ : k -> 
P1)
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem segment_injective_of_ne {a b : E} (hne : a ≠ b) :
    Function.Injective (Path.segment a b) := (lineMap_injective _ hne).comp Subtype.coe_injective

end Path

/-
**JoinedIn.of_segment_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：JoinedIn.of_segment_subset {x y : E} {s : Set E} (h : [x -[Real] y] subset
eq s) : JoinedIn s x y
参数：h : [x -[Real] y] subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Path.range_segment`：range_segment (a b : E) : Set.range (Path.segment a 
b) = [a -[Real] b]
-/
theorem JoinedIn.of_segment_subset {x y : E} {s : Set E} (h : [x -[ℝ] y] ⊆ s) : JoinedIn s x y := by
  use .segment x y
  rwa [← range_subset_iff, Path.range_segment]
/-
**StarConvex.isPathConnected** 是 Mathlib 中的一个定理，位于命名空间 `StarConvex`。
形式化陈述：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _root_.Module ℝ E] [ins
t_2 : TopologicalSpace E] [ContinuousAdd E]   [ContinuousSMul ℝ E] {s : Set E} {
a : E}, StarConvex ℝ a s → a ∈ s → IsPathConnected s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `JoinedIn.of_segment_subset`：JoinedIn.of_segment_subset {x y : E} {s : Se
t E} (h : [x -[Real] y] subseteq s) : JoinedIn s x y
· 使用定理 `StarConvex.segment_subset`：StarConvex.segment_subset (h : StarConvex 𝕜 x
 s) {y : E} (hy : y in s) : [x -[𝕜] y] subseteq s
-/
protected theorem StarConvex.isPathConnected {s : Set E} {a : E} (h : StarConvex ℝ a s)
    (ha : a ∈ s) : IsPathConnected s :=
  ⟨a, ha, fun _y hy ↦ .of_segment_subset <| h.segment_subset hy⟩

/-- A nonempty convex set is path connected. -/
/-
**Convex.isPathConnected** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _root_.Module ℝ E] [ins
t_2 : TopologicalSpace E] [ContinuousAdd E]   [ContinuousSMul ℝ E] {s : Set E}, 
Convex ℝ s → s.Nonempty → IsPathConnected s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarConvex.isPathConnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [in
st_1 : _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Con
tinuousSMul ℝ E]…

--- 原说明 ---
A nonempty convex set is path connected.
-/
protected theorem Convex.isPathConnected {s : Set E} (hconv : Convex ℝ s) (hne : s.Nonempty) :
    IsPathConnected s :=
  let ⟨_a, ha⟩ := hne; (hconv ha).isPathConnected ha

/-- A nonempty convex set is connected. -/
/-
**Convex.isConnected** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _root_.Module ℝ E] [ins
t_2 : TopologicalSpace E] [ContinuousAdd E]   [ContinuousSMul ℝ E] {s : Set E}, 
Convex ℝ s → s.Nonempty → IsConnected s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPathConnected.isConnected`：IsPathConnected.isConnected (hF : IsPathCon
nected F) : IsConnected F
· 使用定理 `Convex.isPathConnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1
 : _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continu
ousSMul ℝ E]…

--- 原说明 ---
A nonempty convex set is connected.
-/
protected theorem Convex.isConnected {s : Set E} (h : Convex ℝ s) (hne : s.Nonempty) :
    IsConnected s :=
  (h.isPathConnected hne).isConnected

/-- A convex set is preconnected. -/
/-
**Convex.isPreconnected** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _root_.Module ℝ E] [ins
t_2 : TopologicalSpace E] [ContinuousAdd E]   [ContinuousSMul ℝ E] {s : Set E}, 
Convex ℝ s → IsPreconnected s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `isPreconnected_empty`：isPreconnected_empty : IsPreconnected (∅ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `Convex.isConnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [ContinuousS
Mul ℝ E]…

--- 原说明 ---
A convex set is preconnected.
-/
protected theorem Convex.isPreconnected {s : Set E} (h : Convex ℝ s) : IsPreconnected s :=
  s.eq_empty_or_nonempty.elim (fun h => h.symm ▸ isPreconnected_empty) fun hne =>
    (h.isConnected hne).isPreconnected

/-- A subspace in a topological vector space over `ℝ` is path connected. -/
/-
**Submodule.isPathConnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.isPathConnected (s : Submodule Real E) : IsPathConnected (s : Se
t E)
参数：s : Submodule Real E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.isPathConnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1
 : _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continu
ousSMul ℝ E]…
· 使用定理 `Submodule.convex`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (K :…
· 使用定理 `Submodule.nonempty`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), (↑p
).Nonemp…

--- 原说明 ---
A subspace in a topological vector space over `ℝ` is path connected.
-/
theorem Submodule.isPathConnected (s : Submodule ℝ E) : IsPathConnected (s : Set E) :=
  s.convex.isPathConnected s.nonempty

/-- Every topological vector space over ℝ is path connected.

Not an instance, because it creates enormous TC subproblems (turn on `pp.all`).
-/
/-
**IsTopologicalAddGroup.pathConnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 `IsTopologi
calAddGroup`。
形式化陈述：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _root_.Module ℝ E] [ins
t_2 : TopologicalSpace E] [ContinuousAdd E]   [ContinuousSMul ℝ E], PathConnecte
dSpace E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pathConnectedSpace_iff_univ`：pathConnectedSpace_iff_univ : PathConnected
Space X ↔ IsPathConnected (univ : Set X)
· 使用定理 `Convex.isPathConnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1
 : _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continu
ousSMul ℝ E]…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `trivial`：True

--- 原说明 ---
Every topological vector space over ℝ is path connected.

Not an instance, because it creates enormous TC subproblems (turn on `pp.all`).
-/
protected theorem IsTopologicalAddGroup.pathConnectedSpace : PathConnectedSpace E :=
  pathConnectedSpace_iff_univ.mpr <| convex_univ.isPathConnected ⟨(0 : E), trivial⟩

/-- Given two complementary subspaces `p` and `q` in `E`, if the complement of `{0}`
is path connected in `p` then the complement of `q` is path connected in `E`. -/
/-
**isPathConnected_compl_of_isPathConnected_compl_zero** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：isPathConnected_compl_of_isPathConnected_compl_zero {p q : Submodule Real 
E} (hpq : IsCompl p q) (hpc : IsPathConnected ({0}ᶜ : Set p)) : IsPathConnected 
(qᶜ : Set E)
参数：hpq : IsCompl p q；hpc : IsPathConnected ({0}ᶜ : Set p)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.prod_univ`：prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹
' s
· 使用定理 `LinearEquiv.image_eq_preimage_symm`：∀ {R : Type u_1} {S : Type u_6} {M :
 Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 :
 AddCommMonoid M] [inst_…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Submodule.prodEquivOfIsCompl_symm_apply`：prodEquivOfIsCompl_symm_apply (
hpq : IsCompl p q) (x : E) : (p.prodEquivOfIsCompl q hpq).symm x = (p.projection
Onto q hpq x, q.projectionOnt…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsPathConnected.add`：∀ {M : Type u_4} [inst : Add M] [inst_1 : Topologic
alSpace M] [ContinuousAdd M] {s t : Set M},   IsPathConnected s → IsPathConnecte
d t → IsP…
· 使用定理 `IsPathConnected.image`：IsPathConnected.image (hF : IsPathConnected F) {f
 : X -> Y} (hf : Continuous f) : IsPathConnected (f '' F)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Submodule.isPathConnected`：Submodule.isPathConnected (s : Submodule Real
 E) : IsPathConnected (s : Set E)

--- 原说明 ---
Given two complementary subspaces `p` and `q` in `E`, if the complement of `{0}`
is path connected in `p` then the complement of `q` is path connected in `E`.
-/
theorem isPathConnected_compl_of_isPathConnected_compl_zero {p q : Submodule ℝ E}
    (hpq : IsCompl p q) (hpc : IsPathConnected ({0}ᶜ : Set p)) : IsPathConnected (qᶜ : Set E) := by
  convert (hpc.image continuous_subtype_val).add q.isPathConnected
  trans Submodule.prodEquivOfIsCompl p q hpq '' ({0}ᶜ ×ˢ univ)
  · rw [prod_univ, LinearEquiv.image_eq_preimage_symm]
    ext
    simp
  · ext
    simp [mem_add, and_assoc]

section Real

set_option backward.isDefEq.respectTransparency.types false in
/-
**segment_image_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_image_Ico {x y : Real} (h : x < y) : (Path.segment x y) '' Ico 0 1
 = Ico x y
参数：h : x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Path.segment_apply`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E]   [inst_3 : ContinuousAdd E] [in
st_4 : C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.image_subtype_val_Ico`：image_subtype_val_Ico {s : Set α} [OrdConnect
ed s] (x y : s) : Subtype.val '' Ico x y = Ico x.1 y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 64 条，此处仅展示前 30 条）
-/
theorem segment_image_Ico {x y : ℝ} (h : x < y) : (Path.segment x y) '' Ico 0 1 = Ico x y := by
  simp_rw [Path.segment_apply, ← image_image _ Subtype.val (Ico 0 1)]
  simp only [lineMap_apply, vsub_eq_sub, smul_eq_mul, vadd_eq_add, image_subtype_val_Ico,
    Icc.coe_zero, Icc.coe_one]
  convert! image_affine_Ico (sub_pos_of_lt h) x 0 1 using 2 <;> ring

set_option backward.isDefEq.respectTransparency.types false in
/-
**segment_image_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_image_Ioc {x y : Real} (h : x < y) : (Path.segment x y) '' Ioc 0 1
 = Ioc x y
参数：h : x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Path.segment_apply`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E]   [inst_3 : ContinuousAdd E] [in
st_4 : C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.image_subtype_val_Ioc`：image_subtype_val_Ioc {s : Set α} [OrdConnect
ed s] (x y : s) : Subtype.val '' Ioc x y = Ioc x.1 y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 64 条，此处仅展示前 30 条）
-/
theorem segment_image_Ioc {x y : ℝ} (h : x < y) : (Path.segment x y) '' Ioc 0 1 = Ioc x y := by
  simp_rw [Path.segment_apply, ← image_image _ Subtype.val (Ioc 0 1)]
  simp only [lineMap_apply, vsub_eq_sub, smul_eq_mul, vadd_eq_add, image_subtype_val_Ioc,
    Icc.coe_zero, Icc.coe_one]
  convert! image_affine_Ioc (sub_pos_of_lt h) x 0 1 using 2 <;> ring

end Real

