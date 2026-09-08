/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

/-!
# Bounded at infinity

For complex-valued functions on the upper half plane, this file defines the filter
`UpperHalfPlane.atImInfty` required for defining when functions are bounded at infinity and zero at
infinity. Both of which are relevant for defining modular forms.
-/

@[expose] public section

open Complex Filter

open scoped Topology UpperHalfPlane

noncomputable section

namespace UpperHalfPlane

/-- Filter for approaching `i∞`. -/
/-
**UpperHalfPlane.atImInfty** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：atImInfty
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Filter for approaching `i∞`.
-/
def atImInfty :=
  Filter.atTop.comap UpperHalfPlane.im
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : atImInfty.NeBot := by
  refine comap_neBot_iff_frequently.mpr (Eventually.frequently ?_)
  filter_upwards [eventually_gt_atTop 0] with t ht
    using ⟨⟨I * t, by simp [ht]⟩, by simp⟩
/-
**UpperHalfPlane.atImInfty_basis** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：atImInfty_basis : atImInfty.HasBasis (fun _ => True) fun i : Real => im ⁻¹
' Set.Ici i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem atImInfty_basis : atImInfty.HasBasis (fun _ => True) fun i : ℝ => im ⁻¹' Set.Ici i :=
  Filter.HasBasis.comap UpperHalfPlane.im Filter.atTop_basis
/-
**UpperHalfPlane.atImInfty_mem** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：atImInfty_mem (S : Set ℍ) : S in atImInfty ↔ exists A : Real, forall z : ℍ
, A <= im z -> z in S
参数：S : Set ℍ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `UpperHalfPlane.atImInfty_basis`：atImInfty_basis : atImInfty.HasBasis (fu
n _ => True) fun i : Real => im ⁻¹' Set.Ici i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem atImInfty_mem (S : Set ℍ) : S ∈ atImInfty ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ im z → z ∈ S := by
  simp only [atImInfty_basis.mem_iff, true_and]; rfl

/-- A function `f : ℍ → α` is bounded at infinity if it is bounded along `atImInfty`. -/
/-
**UpperHalfPlane.IsBoundedAtImInfty** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：IsBoundedAtImInfty {α : Type*} [Norm α] (f : ℍ -> α) : Prop
参数：f : ℍ -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : ℍ → α` is bounded at infinity if it is bounded along `atImInfty`
.
-/
def IsBoundedAtImInfty {α : Type*} [Norm α] (f : ℍ → α) : Prop :=
  BoundedAtFilter atImInfty f

/-- A function `f : ℍ → α` is zero at infinity it is zero along `atImInfty`. -/
/-
**UpperHalfPlane.IsZeroAtImInfty** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：IsZeroAtImInfty {α : Type*} [Zero α] [TopologicalSpace α] (f : ℍ -> α) : P
rop
参数：f : ℍ -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : ℍ → α` is zero at infinity it is zero along `atImInfty`.
-/
def IsZeroAtImInfty {α : Type*} [Zero α] [TopologicalSpace α] (f : ℍ → α) : Prop :=
  ZeroAtFilter atImInfty f
/-
**UpperHalfPlane.zero_form_isBoundedAtImInfty** 是 Mathlib 中的一个定理，位于命名空间 `UpperHa
lfPlane`。
形式化陈述：zero_form_isBoundedAtImInfty {α : Type*} [NormedField α] : IsBoundedAtImIn
fty (0 : ℍ -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.const_boundedAtFilter`：const_boundedAtFilter [Norm β] (l : Filter
 α) (c : β) : BoundedAtFilter l (Function.const α c : α -> β)
-/
theorem zero_form_isBoundedAtImInfty {α : Type*} [NormedField α] :
    IsBoundedAtImInfty (0 : ℍ → α) :=
  const_boundedAtFilter atImInfty (0 : α)

/-- Module of functions that are zero at infinity. -/
/-
**UpperHalfPlane.zeroAtImInftySubmodule** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlan
e`。
形式化陈述：zeroAtImInftySubmodule (α : Type*) [NormedField α] : Submodule α (ℍ -> α)
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Module of functions that are zero at infinity.
-/
def zeroAtImInftySubmodule (α : Type*) [NormedField α] : Submodule α (ℍ → α) :=
  zeroAtFilterSubmodule _ atImInfty

/-- Subalgebra of functions that are bounded at infinity. -/
/-
**UpperHalfPlane.boundedAtImInftySubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalf
Plane`。
形式化陈述：boundedAtImInftySubalgebra (α : Type*) [NormedField α] : Subalgebra α (ℍ -
> α)
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subalgebra of functions that are bounded at infinity.
-/
def boundedAtImInftySubalgebra (α : Type*) [NormedField α] : Subalgebra α (ℍ → α) :=
  boundedFilterSubalgebra _ atImInfty
/-
**UpperHalfPlane.isBoundedAtImInfty_iff** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlan
e`。
形式化陈述：isBoundedAtImInfty_iff {α : Type*} [Norm α] {f : ℍ -> α} : IsBoundedAtImIn
fty f ↔ exists M A : Real, forall z : ℍ, A <= im z -> ‖f z‖ <= M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBoundedAtImInfty_iff {α : Type*} [Norm α] {f : ℍ → α} :
    IsBoundedAtImInfty f ↔ ∃ M A : ℝ, ∀ z : ℍ, A ≤ im z → ‖f z‖ ≤ M := by
  simp [IsBoundedAtImInfty, BoundedAtFilter, Asymptotics.isBigO_iff, Filter.Eventually,
    atImInfty_mem]
/-
**UpperHalfPlane.isZeroAtImInfty_iff** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：isZeroAtImInfty_iff {α : Type*} [SeminormedAddGroup α] {f : ℍ -> α} : IsZe
roAtImInfty f ↔ forall ε : Real, 0 < ε -> exists A : Real, forall z : ℍ, A <= im
 z -> ‖f z‖ <= ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `UpperHalfPlane.atImInfty_basis`：atImInfty_basis : atImInfty.HasBasis (fu
n _ => True) fun i : Real => im ⁻¹' Set.Ici i
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isZeroAtImInfty_iff {α : Type*} [SeminormedAddGroup α] {f : ℍ → α} :
    IsZeroAtImInfty f ↔ ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ z : ℍ, A ≤ im z → ‖f z‖ ≤ ε :=
  (atImInfty_basis.tendsto_iff Metric.nhds_basis_closedBall).trans <| by simp
/-
**UpperHalfPlane.IsZeroAtImInfty.isBoundedAtImInfty** 是 Mathlib 中的一个定理，位于命名空间 `U
pperHalfPlane.IsZeroAtImInfty`。
形式化陈述：∀ {α : Type u_1} [inst : SeminormedAddGroup α] {f : UpperHalfPlane → α},  
 UpperHalfPlane.IsZeroAtImInfty f → UpperHalfPlane.IsBoundedAtImInfty f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ZeroAtFilter.boundedAtFilter`：∀ {α : Type u_2} {β : Type u_3} [in
st : SeminormedAddGroup β] {l : Filter α} {f : α → β},   l.ZeroAtFilter f → l.Bo
undedAtFilter f
-/
theorem IsZeroAtImInfty.isBoundedAtImInfty {α : Type*} [SeminormedAddGroup α] {f : ℍ → α}
    (hf : IsZeroAtImInfty f) : IsBoundedAtImInfty f :=
  hf.boundedAtFilter

set_option backward.isDefEq.respectTransparency false in
/-
**UpperHalfPlane.tendsto_comap_im_ofComplex** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalf
Plane`。
形式化陈述：tendsto_comap_im_ofComplex : Tendsto ofComplex (comap Complex.im atTop) at
ImInfty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.ofComplex_apply_of_im_pos`：ofComplex_apply_of_im_pos {z :
 Complex} (hz : 0 < z.im) : ofComplex z = ⟨z, hz⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
-/
lemma tendsto_comap_im_ofComplex :
    Tendsto ofComplex (comap Complex.im atTop) atImInfty := by
  simp only [atImInfty, tendsto_comap_iff, Function.comp_def]
  refine tendsto_comap.congr' ?_
  filter_upwards [preimage_mem_comap (Ioi_mem_atTop 0)] with z hz
  simp [ofComplex_apply_of_im_pos hz]
/-
**UpperHalfPlane.tendsto_coe_atImInfty** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane
`。
形式化陈述：tendsto_coe_atImInfty : Tendsto UpperHalfPlane.coe atImInfty (comap Comple
x.im atTop)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UpperHalfPlane.coe_im`：coe_im (z : ℍ) : (z : Complex).im = z.im
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
-/
lemma tendsto_coe_atImInfty :
    Tendsto UpperHalfPlane.coe atImInfty (comap Complex.im atTop) := by
  simpa only [atImInfty, tendsto_comap_iff, Function.comp_def,
    funext UpperHalfPlane.coe_im] using tendsto_comap
/-
**UpperHalfPlane.tendsto_smul_atImInfty** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlan
e`。
形式化陈述：tendsto_smul_atImInfty {g : GL (Fin 2) Real} (hg : g 1 0 = 0) : Tendsto (f
un τ => g • τ) atImInfty atImInfty
参数：Fin 2；hg : g 1 0 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Matrix.GeneralLinearGroup.det_ne_zero`：det_ne_zero [Nontrivial R] (g : G
L n R) : g.val.det != 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UpperHalfPlane.im_smul`：im_smul : (g • z).im = |(num g z / denom g z).im
|
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Complex.div_ofReal_im`：∀ (z : ℂ) (x : ℝ), (z / ↑x).im = z.im / x
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_div_right_comm`：mul_div_right_comm : a * b / c = a / c * b
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
-/
lemma tendsto_smul_atImInfty {g : GL (Fin 2) ℝ} (hg : g 1 0 = 0) :
    Tendsto (fun τ ↦ g • τ) atImInfty atImInfty := by
  suffices Tendsto (fun τ ↦ |g 0 0 / g 1 1| * τ.im) atImInfty atTop by
    simpa [atImInfty, Function.comp_def, im_smul, num, denom, hg, abs_div, abs_mul,
      abs_of_pos (UpperHalfPlane.im_pos _), mul_div_right_comm]
  apply tendsto_comap.const_mul_atTop
  simpa [Matrix.det_fin_two, hg] using g.det_ne_zero

end UpperHalfPlane

