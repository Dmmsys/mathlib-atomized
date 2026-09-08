/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Complement

/-! # Continuous linear maps with a continuous left/right inverse

This file defines continuous linear maps which admit a continuous left/right inverse.

We prove that both of these classes of maps are closed under products, composition and contain
linear equivalences, and a sufficient criterion in finite dimension: a surjective linear map on a
finite-dimensional space always admits a continuous right inverse; an injective linear map on a
finite-dimensional space always admits a continuous left inverse.

We also prove an equivalent characterisation of admitting a continuous left inverse: `f` admits a
continuous left inverse if and only if it is injective, has closed range and its range admits a
closed complement. This characterisation is used to extract a complement from immersions, for use
in the regular value theorem. (For submersions, there is a natural choice of complement, and an
analogous statement is not necessary.)

This concept is used to give an equivalent definition of immersions and submersions of manifolds.

## Main definitions and results

* `ContinuousLinearMap.HasLeftInverse`: a continuous linear map admits a left inverse
  which is a continuous linear map itself
* `ContinuousLinearMap.HasRightInverse`: a continuous linear map admits a right inverse
  which is a continuous linear map itself

* `ContinuousLinearMap.HasLeftInverse.isClosed_range`: if `f` has a continuous left inverse,
  its range is closed
* `ContinuousLinearMap.HasLeftInverse.closedComplemented_range`: if `f` has a continuous left
  inverse, its range admits a closed complement
* `ContinuousLinearMap.HasLeftInverse.complement`: a choice of closed complement for `range f`
* `ContinuousLinearMap.HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range`:
  if `f` is injective and has closed range with a closed complement, it admits a continuous left
  inverse

* `ContinuousLinearEquiv.hasLeftInverse` and `ContinuousLinearEquiv.hasRightInverse`:
  a continuous linear equivalence admits a continuous left (resp. right) inverse
* `ContinuousLinearMap.HasLeftInverse.comp`, `ContinuousLinearMap.HasRightInverse.comp`:
  if `f : E → F` and `g : F → G` both admit a continuous left (resp. right) inverse,
  so does `g.comp f`.
* `ContinuousLinearMap.HasLeftInverse.of_comp`, `ContinuousLinearMap.HasRightInverse.of_comp`:
  suppose `f : E → F` and `g : F → G` are continuous linear maps.
  If `g.comp f : E → G` admits a continuous left inverse, then so does `f`.
  If `g.comp f : E → G` admits a continuous right inverse, then so does `g`.
* `ContinuousLinearMap.HasLeftInverse.prodMap`, `ContinuousLinearMap.HasRightInverse.prodMap`:
  having a continuous left/right inverse is closed under taking products
* `ContinuousLinearMap.HasLeftInverse.inl`, `ContinuousLinearMap.HasLeftInverse.inr`:
  `ContinuousLinearMap.inl` and `.inr` have a continuous left inverse
* `ContinuousLinearMap.HasRightInverse.fst`, `ContinuousLinearMap.HasRightInverse.snd`:
  `ContinuousLinearMap.fst` and `.snd` have a continuous right inverse
* `ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional`:
  if `f : E → F` is injective and `F` is finite-dimensional, `f` has a continuous left inverse.
* `ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional`:
  if `f : E → F` is surjective and `F` is finite-dimensional, `f` has a continuous right inverse.

## TODO

* Suppose `E` and `F` are Banach and `f : E → F` is Fredholm.
  If `f` is surjective, it has a continuous right inverse.
  If `f` is injective, it has a continuous left inverse.

-/

public section

open Function Set

variable {R : Type*} [Semiring R] {E E' F F' G : Type*}
  [TopologicalSpace E] [AddCommMonoid E] [Module R E]
  [TopologicalSpace E'] [AddCommMonoid E'] [Module R E']
  [TopologicalSpace F] [AddCommMonoid F] [Module R F]
  [TopologicalSpace F'] [AddCommMonoid F'] [Module R F']

noncomputable section

/-- A continuous linear map admits a left inverse which is a continuous linear map itself. -/
/-
**ContinuousLinearMap.HasLeftInverse** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：{R : Type u_1} →   [inst : Semiring R] →     {E : Type u_2} →       {F : T
ype u_4} →         [inst_1 : TopologicalSpace E] →           [inst_2 : AddCommMo
noid E] →             [inst_3 : _root_.Module R E] →               [inst_4 : Top
ologicalSpace F] →                 [inst_5 : AddCommMonoid F] → [inst_6 : _root_
.Module R F] → (E →L[R] F) → Prop
参数：E →L[R] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear map admits a left inverse which is a continuous linear map i
tself.
-/
@[expose] protected def ContinuousLinearMap.HasLeftInverse (f : E →L[R] F) : Prop :=
  ∃ g : F →L[R] E, LeftInverse g f

/-- A continuous linear map admits a right inverse which is a continuous linear map itself. -/
/-
**ContinuousLinearMap.HasRightInverse** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：{R : Type u_1} →   [inst : Semiring R] →     {E : Type u_2} →       {F : T
ype u_4} →         [inst_1 : TopologicalSpace E] →           [inst_2 : AddCommMo
noid E] →             [inst_3 : _root_.Module R E] →               [inst_4 : Top
ologicalSpace F] →                 [inst_5 : AddCommMonoid F] → [inst_6 : _root_
.Module R F] → (E →L[R] F) → Prop
参数：E →L[R] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear map admits a right inverse which is a continuous linear map 
itself.
-/
@[expose] protected def ContinuousLinearMap.HasRightInverse (f : E →L[R] F) : Prop :=
  ∃ g : F →L[R] E, RightInverse g f

namespace ContinuousLinearMap

namespace HasLeftInverse

variable {f : E →L[R] F}

/-- Choice of continuous left inverse for `f : F →L[R] E`, given that such an inverse exists. -/
/-
**ContinuousLinearMap.HasLeftInverse.leftInverse** 是 Mathlib 中的一个定义，位于命名空间 `Cont
inuousLinearMap.HasLeftInverse`。
形式化陈述：leftInverse (h : f.HasLeftInverse) : F ->L[R] E
参数：h : f.HasLeftInverse。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Choice of continuous left inverse for `f : F →L[R] E`, given that such an invers
e exists.
-/
def leftInverse (h : f.HasLeftInverse) : F →L[R] E := Classical.choose h
/-
**ContinuousLinearMap.HasLeftInverse.leftInverse_leftInverse** 是 Mathlib 中的一个引理，
位于命名空间 `ContinuousLinearMap.HasLeftInverse`。
形式化陈述：leftInverse_leftInverse (h : f.HasLeftInverse) : LeftInverse h.leftInverse
 f
参数：h : f.HasLeftInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma leftInverse_leftInverse (h : f.HasLeftInverse) : LeftInverse h.leftInverse f :=
  Classical.choose_spec h
/-
**ContinuousLinearMap.HasLeftInverse.injective** 是 Mathlib 中的一个引理，位于命名空间 `Contin
uousLinearMap.HasLeftInverse`。
形式化陈述：injective (h : f.HasLeftInverse) : Injective f
参数：h : f.HasLeftInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用引理 `ContinuousLinearMap.HasLeftInverse.leftInverse_leftInverse`：leftInverse_
leftInverse (h : f.HasLeftInverse) : LeftInverse h.leftInverse f
-/
lemma injective (h : f.HasLeftInverse) : Injective f :=
  h.leftInverse_leftInverse.injective
/-
**ContinuousLinearMap.HasLeftInverse.** 是 Mathlib 中的一个示例，位于命名空间 `ContinuousLinea
rMap.HasLeftInverse`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (h : f.HasLeftInverse) (x : E) : h.leftInverse (f x) = x :=
  h.leftInverse_leftInverse x
/-
**ContinuousLinearMap.HasLeftInverse.congr** 是 Mathlib 中的一个引理，位于命名空间 `Continuous
LinearMap.HasLeftInverse`。
形式化陈述：congr {g : E ->L[R] F} (hf : f.HasLeftInverse) (hfg : g = f) : g.HasLeftIn
verse
参数：hf : f.HasLeftInverse；hfg : g = f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma congr {g : E →L[R] F} (hf : f.HasLeftInverse) (hfg : g = f) :
    g.HasLeftInverse :=
  hfg ▸ hf

/-- A continuous linear equivalence has a continuous left inverse. -/
/-
**ContinuousLinearMap.HasLeftInverse._root_.ContinuousLinearEquiv.hasLeftInverse
** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap.HasLeftInverse`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear equivalence has a continuous left inverse.
-/
lemma _root_.ContinuousLinearEquiv.hasLeftInverse (f : E ≃L[R] F) :
    f.toContinuousLinearMap.HasLeftInverse :=
  ⟨f.symm, rightInverse_of_comp (by simp)⟩
/-
**ContinuousLinearMap.HasLeftInverse._root_.ContinuousLinearEquiv.leftInverse_ha
sLeftInverse** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap.HasLeftInverse`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.ContinuousLinearEquiv.leftInverse_hasLeftInverse (f : E ≃L[R] F) :
    f.hasLeftInverse.leftInverse = f.symm := by
  ext y
  calc f.hasLeftInverse.leftInverse y
    _ = f.hasLeftInverse.leftInverse (f (f.symm y)) := by simp
    _ = f.symm y := f.hasLeftInverse.leftInverse_leftInverse (f.symm y)

/-- An invertible continuous linear map has a continuous left inverse. -/
/-
**ContinuousLinearMap.HasLeftInverse.of_isInvertible** 是 Mathlib 中的一个引理，位于命名空间 `
ContinuousLinearMap.HasLeftInverse`。
形式化陈述：of_isInvertible (hf : IsInvertible f) : f.HasLeftInverse
参数：hf : IsInvertible f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.hasLeftInverse`：∀ {R : Type u_1} [inst : Semiring 
R] {E : Type u_2} {F : Type u_4} [inst_1 : TopologicalSpace E]   [inst_2 : AddCo
mmMonoid E] [inst_3 : _roo…

--- 原说明 ---
An invertible continuous linear map has a continuous left inverse.
-/
lemma of_isInvertible (hf : IsInvertible f) : f.HasLeftInverse := by
  obtain ⟨e, rfl⟩ := hf
  exact e.hasLeftInverse

/-- If `f` and `g` admit continuous left inverses, so does `f × g`. -/
/-
**ContinuousLinearMap.HasLeftInverse.prodMap** 是 Mathlib 中的一个引理，位于命名空间 `Continuo
usLinearMap.HasLeftInverse`。
形式化陈述：prodMap {g : E' ->L[R] F'} (hf : f.HasLeftInverse) (hg : g.HasLeftInverse)
 : (f.prodMap g).HasLeftInverse
参数：hf : f.HasLeftInverse；hg : g.HasLeftInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
If `f` and `g` admit continuous left inverses, so does `f × g`.
-/
lemma prodMap {g : E' →L[R] F'} (hf : f.HasLeftInverse) (hg : g.HasLeftInverse) :
    (f.prodMap g).HasLeftInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  use finv.prodMap ginv
  simp [hfinv, hginv]

variable [TopologicalSpace G] [AddCommMonoid G] [Module R G]
/-
**ContinuousLinearMap.HasLeftInverse.comp** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousL
inearMap.HasLeftInverse`。
形式化陈述：comp {g : F ->L[R] G} (hg : g.HasLeftInverse) (hf : f.HasLeftInverse) : (g
.comp f).HasLeftInverse
参数：hg : g.HasLeftInverse；hf : f.HasLeftInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma comp {g : F →L[R] G} (hg : g.HasLeftInverse) (hf : f.HasLeftInverse) :
    (g.comp f).HasLeftInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  refine ⟨finv.comp ginv, fun x ↦ ?_⟩
  simp only [comp_apply]
  rw [hginv, hfinv]
/-
**ContinuousLinearMap.HasLeftInverse.of_comp** 是 Mathlib 中的一个引理，位于命名空间 `Continuo
usLinearMap.HasLeftInverse`。
形式化陈述：of_comp {g : F ->L[R] G} (hfg : (g.comp f).HasLeftInverse) : f.HasLeftInve
rse
参数：hfg : (g.comp f).HasLeftInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_comp {g : F →L[R] G} (hfg : (g.comp f).HasLeftInverse) :
    f.HasLeftInverse := by
  obtain ⟨fginv, hfginv⟩ := hfg
  refine ⟨fginv.comp g, fun y ↦ ?_⟩
  simp only [comp_apply]
  exact hfginv y
/-
**ContinuousLinearMap.HasLeftInverse.comp_continuousLinearEquivalence** 是 Mathli
b 中的一个引理，位于命名空间 `ContinuousLinearMap.HasLeftInverse`。
形式化陈述：comp_continuousLinearEquivalence {f₀ : F' ≃L[R] E} (hf : f.HasLeftInverse)
 : (f.comp f₀.toContinuousLinearMap).HasLeftInverse
参数：hf : f.HasLeftInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.HasLeftInverse.comp`：comp {g : F ->L[R] G} (hg : g.H
asLeftInverse) (hf : f.HasLeftInverse) : (g.comp f).HasLeftInverse
· 使用定理 `ContinuousLinearEquiv.hasLeftInverse`：∀ {R : Type u_1} [inst : Semiring 
R] {E : Type u_2} {F : Type u_4} [inst_1 : TopologicalSpace E]   [inst_2 : AddCo
mmMonoid E] [inst_3 : _roo…
-/
lemma comp_continuousLinearEquivalence {f₀ : F' ≃L[R] E} (hf : f.HasLeftInverse) :
    (f.comp f₀.toContinuousLinearMap).HasLeftInverse :=
  hf.comp f₀.hasLeftInverse
/-
**ContinuousLinearMap.HasLeftInverse.continuousLinearEquivalence_comp** 是 Mathli
b 中的一个引理，位于命名空间 `ContinuousLinearMap.HasLeftInverse`。
形式化陈述：continuousLinearEquivalence_comp {g : F ≃L[R] F'} (hf : f.HasLeftInverse) 
: (g.toContinuousLinearMap.comp f).HasLeftInverse
参数：hf : f.HasLeftInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.HasLeftInverse.comp`：comp {g : F ->L[R] G} (hg : g.H
asLeftInverse) (hf : f.HasLeftInverse) : (g.comp f).HasLeftInverse
· 使用定理 `ContinuousLinearEquiv.hasLeftInverse`：∀ {R : Type u_1} [inst : Semiring 
R] {E : Type u_2} {F : Type u_4} [inst_1 : TopologicalSpace E]   [inst_2 : AddCo
mmMonoid E] [inst_3 : _roo…
-/
lemma continuousLinearEquivalence_comp {g : F ≃L[R] F'} (hf : f.HasLeftInverse) :
    (g.toContinuousLinearMap.comp f).HasLeftInverse :=
  g.hasLeftInverse.comp hf

/-- `ContinuousLinearMap.inl` has a continuous left inverse. -/
/-
**ContinuousLinearMap.HasLeftInverse.inl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap.HasLeftInverse`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {F : Type u_4} {G : Type u_6} [inst_1
 : TopologicalSpace F]   [inst_2 : AddCommMonoid F] [inst_3 : _root_.Module R F]
 [inst_4 : TopologicalSpace G] [inst_5 : AddCommMonoid G]   [inst_6 : _root_.Mod
ule R G], (ContinuousLinearMap.inl R F G).HasLeftInverse
参数：ContinuousLinearMap.inl R F G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`ContinuousLinearMap.inl` has a continuous left inverse.
-/
protected lemma inl : (ContinuousLinearMap.inl R F G).HasLeftInverse := by
  use ContinuousLinearMap.fst _ _ _
  intro x
  simp

/-- `ContinuousLinearMap.inr` has a continuous left inverse. -/
/-
**ContinuousLinearMap.HasLeftInverse.inr** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap.HasLeftInverse`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {F : Type u_4} {G : Type u_6} [inst_1
 : TopologicalSpace F]   [inst_2 : AddCommMonoid F] [inst_3 : _root_.Module R F]
 [inst_4 : TopologicalSpace G] [inst_5 : AddCommMonoid G]   [inst_6 : _root_.Mod
ule R G], (ContinuousLinearMap.inr R F G).HasLeftInverse
参数：ContinuousLinearMap.inr R F G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`ContinuousLinearMap.inr` has a continuous left inverse.
-/
protected lemma inr : (ContinuousLinearMap.inr R F G).HasLeftInverse := by
  use ContinuousLinearMap.snd _ _ _
  intro x
  simp

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [T2Space F] {f : E →L[𝕜] F}

/-- If `f : E → F` is injective and `E` is finite-dimensional,
`f` has a continuous left inverse. -/
/-
**ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional** 是 Mathl
ib 中的一个引理，位于命名空间 `ContinuousLinearMap.HasLeftInverse`。
形式化陈述：of_injective_of_finiteDimensional [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F
] (hf : Injective f) : f.HasLeftInverse
参数：hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.exists_leftInverse_of_injective`：LinearMap.exists_leftInverse_
of_injective (f : V ->ₗ[K] V') (hf_inj : LinearMap.ker f = ⊥) : exists g : V' ->
ₗ[K] V, g.comp f = LinearMap.id
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If `f : E → F` is injective and `E` is finite-dimensional,
`f` has a continuous left inverse.
-/
lemma of_injective_of_finiteDimensional [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    (hf : Injective f) :
    f.HasLeftInverse := by
  -- An injective linear map has a linear inverse; this inverse is automatically continuous
  -- because its domain is finite-dimensional.
  obtain ⟨g, hg⟩ :=
    f.toLinearMap.exists_leftInverse_of_injective (f.ker_eq_bot_of_injective hf)
  exact ⟨⟨g, LinearMap.continuous_of_finiteDimensional _⟩, fun x ↦ congr($hg x)⟩

end NontriviallyNormedField

/-! An equivalent characterisation of maps with a continuous left inverse -/
section Ring

-- The next lemmas assume we are working over a ring.
variable {R E E' F F' G : Type*} [Ring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F] {f : E →L[R] F}

set_option backward.isDefEq.respectTransparency false in
/-- If `f` has a continuous left inverse, its range admits a closed complement. -/
/-
**ContinuousLinearMap.HasLeftInverse.closedComplemented_range** 是 Mathlib 中的一个引理
，位于命名空间 `ContinuousLinearMap.HasLeftInverse`。
形式化陈述：closedComplemented_range (hf : f.HasLeftInverse) : Submodule.ClosedComplem
ented f.range
参数：hf : f.HasLeftInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousLinearMap.HasLeftInverse.leftInverse_leftInverse`：leftInverse_
leftInverse (h : f.HasLeftInverse) : LeftInverse h.leftInverse f

--- 原说明 ---
If `f` has a continuous left inverse, its range admits a closed complement.
-/
lemma closedComplemented_range (hf : f.HasLeftInverse) : Submodule.ClosedComplemented f.range := by
  -- Idea of proof: let g be a left inverse for f. Then ker g is a closed subspace of F,
  -- and a complement to range f.
  -- Mathlib's definition of closed complement takes a continuous projection to f.range instead
  -- of a complementary subspace: consider `f.comp g` instead, which is continuous as both maps are,
  -- and idempotent as a continuous left inverse.
  use (f.comp hf.leftInverse).codRestrict f.range (by intro y; simp)
  rintro ⟨y, x, rfl⟩
  ext
  simp only [coe_coe, coe_codRestrict_apply, comp_apply]
  rw [hf.leftInverse_leftInverse]

section

variable [T1Space F]

/-
**ContinuousLinearMap.HasLeftInverse.isClosed_range** 是 Mathlib 中的一个引理，位于命名空间 `C
ontinuousLinearMap.HasLeftInverse`。
形式化陈述：isClosed_range (hf : f.HasLeftInverse) [IsTopologicalAddGroup F] : IsClose
d (range f)
参数：hf : f.HasLeftInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ContinuousLinearMap.range_toLinearMap`：range_toLinearMap (f : M₁ ->SL[σ₁
₂] M₂) : Set.range f.toLinearMap = Set.range f
· 使用定理 `LinearMap.coe_range`：coe_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] 
M₂) : (range f : Set M₂) = Set.range f
· 使用引理 `LinearMap.range_eq_ker_of_leftInverse`：range_eq_ker_of_leftInverse {M P}
 [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] {f : M ->ₗ[R] P} {g
 : P ->ₗ[R] M} (h : LeftInv…
· 使用引理 `ContinuousLinearMap.HasLeftInverse.leftInverse_leftInverse`：leftInverse_
leftInverse (h : f.HasLeftInverse) : LeftInverse h.leftInverse f
· 使用定理 `ContinuousLinearMap.isClosed_ker`：isClosed_ker [T1Space M₂] (f : M₁ ->SL
[σ₁₂] M₂) : IsClosed (f.ker : Set M₁)
-/
lemma isClosed_range (hf : f.HasLeftInverse) [IsTopologicalAddGroup F] :
    IsClosed (range f) := by
  -- `range f = ker (f ∘ g - id)` is closed since `f ∘ g - id` is continuous.
  rw [← f.range_toLinearMap, ← f.coe_range,
    f.range_eq_ker_of_leftInverse (hf.leftInverse_leftInverse)]
  exact ((f.comp hf.leftInverse) - (ContinuousLinearMap.id R F)).isClosed_ker

/-- Choice of a closed complement of `range f` -/
/-
**ContinuousLinearMap.HasLeftInverse.complement** 是 Mathlib 中的一个定义，位于命名空间 `Conti
nuousLinearMap.HasLeftInverse`。
形式化陈述：complement (h : f.HasLeftInverse) : Submodule R F
参数：h : f.HasLeftInverse。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.HasLeftInverse.closedComplemented_range`：closedCompl
emented_range (hf : f.HasLeftInverse) : Submodule.ClosedComplemented f.range

--- 原说明 ---
Choice of a closed complement of `range f`
-/
def complement (h : f.HasLeftInverse) : Submodule R F :=
  h.closedComplemented_range.complement
/-
**ContinuousLinearMap.HasLeftInverse.isClosed_complement** 是 Mathlib 中的一个引理，位于命名
空间 `ContinuousLinearMap.HasLeftInverse`。
形式化陈述：isClosed_complement (h : f.HasLeftInverse) : IsClosed (X
参数：h : f.HasLeftInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ClosedComplemented.isClosed_complement`：∀ {R : Type u_1} [inst
 : Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M
]   [inst_3 : _root_.Module R M] {p : …
· 使用引理 `ContinuousLinearMap.HasLeftInverse.closedComplemented_range`：closedCompl
emented_range (hf : f.HasLeftInverse) : Submodule.ClosedComplemented f.range
-/
lemma isClosed_complement (h : f.HasLeftInverse) : IsClosed (X := F) h.complement :=
  h.closedComplemented_range.isClosed_complement

omit [T1Space F] in
/-
**ContinuousLinearMap.HasLeftInverse.isCompl_complement** 是 Mathlib 中的一个引理，位于命名空
间 `ContinuousLinearMap.HasLeftInverse`。
形式化陈述：isCompl_complement (h : f.HasLeftInverse) : IsCompl f.range h.complement
参数：h : f.HasLeftInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ClosedComplemented.isCompl_complement`：∀ {R : Type u_1} [inst 
: Ring R] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]
   [inst_3 : _root_.Module R M] {p : …
· 使用引理 `ContinuousLinearMap.HasLeftInverse.closedComplemented_range`：closedCompl
emented_range (hf : f.HasLeftInverse) : Submodule.ClosedComplemented f.range
-/
lemma isCompl_complement (h : f.HasLeftInverse) : IsCompl f.range h.complement :=
  h.closedComplemented_range.isCompl_complement

end

end Ring

section

variable {R E F : Type*} [NontriviallyNormedField R]
  [NormedAddCommGroup E] [NormedSpace R E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace R F] [CompleteSpace F]

/-- A continuous linear map between Banach spaces has a continuous left inverse if it is injective,
has closed range and its range has a closed complement. -/
/-
**ContinuousLinearMap.HasLeftInverse.of_injective_of_isClosed_range_of_closedCom
plement_range** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap.HasLeftInverse`。
形式化陈述：of_injective_of_isClosed_range_of_closedComplement_range {f : E ->L[R] F} 
(hf : Injective f) (hf' : IsClosed (range f)) (hf'' : Submodule.ClosedComplement
ed f.range) : f.HasLeftInverse
参数：hf : Injective f；hf' : IsClosed (range f)；hf'' : Submodule.ClosedComplemented
 f.range。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.ker_codRestrict`：ker_codRestrict (f : M₁ ->SL[σ₁₂] M
₂) (p : Submodule R₂ M₂) (h : forall x, f x in p) : ker (f.codRestrict p h : M₁ 
->ₛₗ[σ₁₂] p) = ker (f : M…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.leftInverse_apply_of_inj`：LinearMap.leftInverse_apply_of_inj {
f : V ->ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥) (x : V) : f.leftInverse (f x) = x

--- 原说明 ---
A continuous linear map between Banach spaces has a continuous left inverse if i
t is injective,
has closed range and its range has a closed complement.
-/
lemma of_injective_of_isClosed_range_of_closedComplement_range {f : E →L[R] F}
    (hf : Injective f) (hf' : IsClosed (range f)) (hf'' : Submodule.ClosedComplemented f.range) :
    f.HasLeftInverse := by
  have : (f.rangeRestrict).ker = ⊥ := by
    rw [ker_codRestrict]; exact LinearMap.ker_eq_bot.mpr hf
  -- We compose the continuous inverse of `f : E → range f` with the projection `p : F → range f`.
  obtain ⟨p, hp⟩ := hf''
  refine ⟨(f.leftInverse_of_injective_of_isClosed_range hf hf').comp p, fun x ↦ ?_⟩
  simpa [hp ⟨f x, by simp⟩] using! f.rangeRestrict.leftInverse_apply_of_inj this x

end

end HasLeftInverse

namespace HasRightInverse

variable {f : E →L[R] F}

/-- Choice of continuous right inverse for `f : F →L[R] E`, given that such an inverse exists. -/
/-
**ContinuousLinearMap.HasRightInverse.rightInverse** 是 Mathlib 中的一个定义，位于命名空间 `Co
ntinuousLinearMap.HasRightInverse`。
形式化陈述：rightInverse (h : f.HasRightInverse) : F ->L[R] E
参数：h : f.HasRightInverse。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Choice of continuous right inverse for `f : F →L[R] E`, given that such an inver
se exists.
-/
def rightInverse (h : f.HasRightInverse) : F →L[R] E := Classical.choose h
/-
**ContinuousLinearMap.HasRightInverse.rightInverse_rightInverse** 是 Mathlib 中的一个
引理，位于命名空间 `ContinuousLinearMap.HasRightInverse`。
形式化陈述：rightInverse_rightInverse (h : f.HasRightInverse) : RightInverse h.rightIn
verse f
参数：h : f.HasRightInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma rightInverse_rightInverse (h : f.HasRightInverse) : RightInverse h.rightInverse f :=
  Classical.choose_spec h
/-
**ContinuousLinearMap.HasRightInverse.surjective** 是 Mathlib 中的一个引理，位于命名空间 `Cont
inuousLinearMap.HasRightInverse`。
形式化陈述：surjective (h : f.HasRightInverse) : Surjective f
参数：h : f.HasRightInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用引理 `ContinuousLinearMap.HasRightInverse.rightInverse_rightInverse`：rightInve
rse_rightInverse (h : f.HasRightInverse) : RightInverse h.rightInverse f
-/
lemma surjective (h : f.HasRightInverse) : Surjective f :=
  h.rightInverse_rightInverse.surjective
/-
**ContinuousLinearMap.HasRightInverse.congr** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sLinearMap.HasRightInverse`。
形式化陈述：congr {g : E ->L[R] F} (hf : f.HasRightInverse) (hfg : g = f) : g.HasRight
Inverse
参数：hf : f.HasRightInverse；hfg : g = f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma congr {g : E →L[R] F} (hf : f.HasRightInverse) (hfg : g = f) :
    g.HasRightInverse :=
  hfg ▸ hf

/-- A continuous linear equivalence has a continuous right inverse. -/
/-
**ContinuousLinearMap.HasRightInverse._root_.ContinuousLinearEquiv.hasRightInver
se** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap.HasRightInverse`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear equivalence has a continuous right inverse.
-/
lemma _root_.ContinuousLinearEquiv.hasRightInverse (f : E ≃L[R] F) :
    f.toContinuousLinearMap.HasRightInverse :=
  ⟨f.symm, rightInverse_of_comp (by simp)⟩
/-
**ContinuousLinearMap.HasRightInverse._root_.ContinuousLinearEquiv.rightInverse_
hasRightInverse** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap.HasRightInverse`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.ContinuousLinearEquiv.rightInverse_hasRightInverse (f : E ≃L[R] F) :
    f.hasRightInverse.rightInverse = f.symm := by
  ext y
  exact f.injective <| by simpa using f.hasRightInverse.rightInverse_rightInverse y

/-- An invertible continuous linear map has a continuous right inverse. -/
/-
**ContinuousLinearMap.HasRightInverse.of_isInvertible** 是 Mathlib 中的一个引理，位于命名空间 
`ContinuousLinearMap.HasRightInverse`。
形式化陈述：of_isInvertible (hf : IsInvertible f) : f.HasRightInverse
参数：hf : IsInvertible f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.hasRightInverse`：∀ {R : Type u_1} [inst : Semiring
 R] {E : Type u_2} {F : Type u_4} [inst_1 : TopologicalSpace E]   [inst_2 : AddC
ommMonoid E] [inst_3 : _roo…

--- 原说明 ---
An invertible continuous linear map has a continuous right inverse.
-/
lemma of_isInvertible (hf : IsInvertible f) : f.HasRightInverse := by
  obtain ⟨e, rfl⟩ := hf
  exact e.hasRightInverse

/-- If `f` and `g` split, then so does `f × g`. -/
/-
**ContinuousLinearMap.HasRightInverse.prodMap** 是 Mathlib 中的一个引理，位于命名空间 `Continu
ousLinearMap.HasRightInverse`。
形式化陈述：prodMap {g : E' ->L[R] F'} (hf : f.HasRightInverse) (hg : g.HasRightInvers
e) : (f.prodMap g).HasRightInverse
参数：hf : f.HasRightInverse；hg : g.HasRightInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
If `f` and `g` split, then so does `f × g`.
-/
lemma prodMap {g : E' →L[R] F'} (hf : f.HasRightInverse) (hg : g.HasRightInverse) :
    (f.prodMap g).HasRightInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  use finv.prodMap ginv
  simp [hfinv, hginv]

variable [TopologicalSpace G] [AddCommMonoid G] [Module R G]
/-
**ContinuousLinearMap.HasRightInverse.comp** 是 Mathlib 中的一个引理，位于命名空间 `Continuous
LinearMap.HasRightInverse`。
形式化陈述：comp {g : F ->L[R] G} (hg : g.HasRightInverse) (hf : f.HasRightInverse) : 
(g.comp f).HasRightInverse
参数：hg : g.HasRightInverse；hf : f.HasRightInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma comp {g : F →L[R] G} (hg : g.HasRightInverse) (hf : f.HasRightInverse) :
    (g.comp f).HasRightInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  refine ⟨finv.comp ginv, fun x ↦ ?_⟩
  simp only [comp_apply]
  rw [hfinv, hginv]
/-
**ContinuousLinearMap.HasRightInverse.of_comp** 是 Mathlib 中的一个引理，位于命名空间 `Continu
ousLinearMap.HasRightInverse`。
形式化陈述：of_comp {g : F ->L[R] G} (hfg : (g.comp f).HasRightInverse) : g.HasRightIn
verse
参数：hfg : (g.comp f).HasRightInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_comp {g : F →L[R] G} (hfg : (g.comp f).HasRightInverse) :
    g.HasRightInverse := by
  obtain ⟨fginv, hfginv⟩ := hfg
  exact ⟨f.comp fginv, fun y ↦ by simpa using hfginv y⟩
/-
**ContinuousLinearMap.HasRightInverse.comp_continuousLinearEquivalence** 是 Mathl
ib 中的一个引理，位于命名空间 `ContinuousLinearMap.HasRightInverse`。
形式化陈述：comp_continuousLinearEquivalence {f₀ : F' ≃L[R] E} (hf : f.HasRightInverse
) : (f.comp f₀.toContinuousLinearMap).HasRightInverse
参数：hf : f.HasRightInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.HasRightInverse.comp`：comp {g : F ->L[R] G} (hg : g.
HasRightInverse) (hf : f.HasRightInverse) : (g.comp f).HasRightInverse
· 使用定理 `ContinuousLinearEquiv.hasRightInverse`：∀ {R : Type u_1} [inst : Semiring
 R] {E : Type u_2} {F : Type u_4} [inst_1 : TopologicalSpace E]   [inst_2 : AddC
ommMonoid E] [inst_3 : _roo…
-/
lemma comp_continuousLinearEquivalence {f₀ : F' ≃L[R] E} (hf : f.HasRightInverse) :
    (f.comp f₀.toContinuousLinearMap).HasRightInverse :=
  hf.comp f₀.hasRightInverse
/-
**ContinuousLinearMap.HasRightInverse.continuousLinearEquivalence_comp** 是 Mathl
ib 中的一个引理，位于命名空间 `ContinuousLinearMap.HasRightInverse`。
形式化陈述：continuousLinearEquivalence_comp {g : F ≃L[R] F'} (hf : f.HasRightInverse)
 : (g.toContinuousLinearMap.comp f).HasRightInverse
参数：hf : f.HasRightInverse。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.HasRightInverse.comp`：comp {g : F ->L[R] G} (hg : g.
HasRightInverse) (hf : f.HasRightInverse) : (g.comp f).HasRightInverse
· 使用定理 `ContinuousLinearEquiv.hasRightInverse`：∀ {R : Type u_1} [inst : Semiring
 R] {E : Type u_2} {F : Type u_4} [inst_1 : TopologicalSpace E]   [inst_2 : AddC
ommMonoid E] [inst_3 : _roo…
-/
lemma continuousLinearEquivalence_comp {g : F ≃L[R] F'} (hf : f.HasRightInverse) :
    (g.toContinuousLinearMap.comp f).HasRightInverse :=
  g.hasRightInverse.comp hf

/-- `ContinuousLinearMap.fst` has a continuous right inverse. -/
/-
**ContinuousLinearMap.HasRightInverse.fst** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap.HasRightInverse`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {F : Type u_4} {G : Type u_6} [inst_1
 : TopologicalSpace F]   [inst_2 : AddCommMonoid F] [inst_3 : _root_.Module R F]
 [inst_4 : TopologicalSpace G] [inst_5 : AddCommMonoid G]   [inst_6 : _root_.Mod
ule R G], (ContinuousLinearMap.fst R F G).HasRightInverse
参数：ContinuousLinearMap.fst R F G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`ContinuousLinearMap.fst` has a continuous right inverse.
-/
protected lemma fst : (ContinuousLinearMap.fst R F G).HasRightInverse := by
  use (ContinuousLinearMap.id _ _).prod 0
  intro x
  simp

/-- `ContinuousLinearMap.snd` has a continuous right inverse. -/
/-
**ContinuousLinearMap.HasRightInverse.snd** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap.HasRightInverse`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {F : Type u_4} {G : Type u_6} [inst_1
 : TopologicalSpace F]   [inst_2 : AddCommMonoid F] [inst_3 : _root_.Module R F]
 [inst_4 : TopologicalSpace G] [inst_5 : AddCommMonoid G]   [inst_6 : _root_.Mod
ule R G], (ContinuousLinearMap.snd R F G).HasRightInverse
参数：ContinuousLinearMap.snd R F G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`ContinuousLinearMap.snd` has a continuous right inverse.
-/
protected lemma snd : (ContinuousLinearMap.snd R F G).HasRightInverse := by
  use ContinuousLinearMap.prod 0 (.id R G)
  intro x
  simp

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [T2Space F] {f : E →L[𝕜] F}

/-- If `f : E → F` is surjective and `F` is finite-dimensional,
`f` has a continuous right inverse. -/
/-
**ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional** 是 Mat
hlib 中的一个引理，位于命名空间 `ContinuousLinearMap.HasRightInverse`。
形式化陈述：of_surjective_of_finiteDimensional [CompleteSpace 𝕜] [FiniteDimensional 𝕜 
F] (hf : Surjective f) : f.HasRightInverse
参数：hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.exists_rightInverse_of_surjective`：∀ {R : Type u_1} [inst : Se
miring R] {P : Type u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]
   {M : Type u_3} [inst_3 : AddCo…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `LinearMap.range_eq_top_of_surjective`：range_eq_top_of_surjective [RingHo
mSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (hf : Surjective f) : range f = ⊤
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If `f : E → F` is surjective and `F` is finite-dimensional,
`f` has a continuous right inverse.
-/
lemma of_surjective_of_finiteDimensional [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    (hf : Surjective f) :
    f.HasRightInverse := by
  -- A surjective linear map has a linear inverse, which is automatically continuous
  -- because its domain is finite-dimensional.
  obtain ⟨g, hg⟩ :=
    f.toLinearMap.exists_rightInverse_of_surjective (f.range_eq_top_of_surjective hf)
  exact ⟨⟨g, g.continuous_of_finiteDimensional⟩, fun x ↦ congr($hg x)⟩

end NontriviallyNormedField

end HasRightInverse

end ContinuousLinearMap

end

