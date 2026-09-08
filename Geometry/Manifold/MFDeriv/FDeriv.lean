/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.Notation

/-!
### Relations between vector space derivative and manifold derivative

The manifold derivative `mfderiv`, when considered on the model vector space with its trivial
manifold structure, coincides with the usual Fréchet derivative `fderiv`. In this section, we prove
this and related statements.
-/

public section

noncomputable section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {f : E → E'}
  {s : Set E} {x : E}

section MFDerivFDeriv

set_option backward.isDefEq.respectTransparency false in
/-
**uniqueMDiffWithinAt_iff_uniqueDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueMDiffWithinAt_iff_uniqueDiffWithinAt : UniqueMDiffAt[s] x ↔ UniqueDi
ffWithinAt 𝕜 s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem uniqueMDiffWithinAt_iff_uniqueDiffWithinAt :
    UniqueMDiffAt[s] x ↔ UniqueDiffWithinAt 𝕜 s x := by
  simp only [UniqueMDiffWithinAt, mfld_simps]

alias ⟨UniqueMDiffWithinAt.uniqueDiffWithinAt, UniqueDiffWithinAt.uniqueMDiffWithinAt⟩ :=
  uniqueMDiffWithinAt_iff_uniqueDiffWithinAt
/-
**uniqueMDiffOn_iff_uniqueDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueMDiffOn_iff_uniqueDiffOn : UniqueMDiff[s] ↔ UniqueDiffOn 𝕜 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem uniqueMDiffOn_iff_uniqueDiffOn : UniqueMDiff[s] ↔ UniqueDiffOn 𝕜 s := by
  simp [UniqueMDiffOn, UniqueDiffOn, uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]

alias ⟨UniqueMDiffOn.uniqueDiffOn, UniqueDiffOn.uniqueMDiffOn⟩ := uniqueMDiffOn_iff_uniqueDiffOn
/-
**ModelWithCorners.uniqueMDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ModelWithCorners.uniqueMDiffOn {H : Type*} [TopologicalSpace H] (I : Model
WithCorners 𝕜 E H) : UniqueMDiff[Set.range I]
参数：I : ModelWithCorners 𝕜 E H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffOn.uniqueMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {s : Set E},…
· 使用定理 `ModelWithCorners.uniqueDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
-/
theorem ModelWithCorners.uniqueMDiffOn {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) : UniqueMDiff[Set.range I] :=
  I.uniqueDiffOn.uniqueMDiffOn

@[simp, mfld_simps]
/-
**writtenInExtChartAt_model_space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：writtenInExtChartAt_model_space : writtenInExtChartAt 𝓘(𝕜, E) 𝓘(𝕜, E') x f
 = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem writtenInExtChartAt_model_space : writtenInExtChartAt 𝓘(𝕜, E) 𝓘(𝕜, E') x f = f :=
  rfl

variable {f' : TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E') (f x)}

set_option backward.isDefEq.respectTransparency false in
/-
**hasMFDerivWithinAt_iff_hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivWithinAt_iff_hasFDerivWithinAt : HasMFDerivAt[s] f x f' ↔ HasFDe
rivWithinAt f f' s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `HasFDerivWithinAt.continuousWithinAt`：HasFDerivWithinAt.continuousWithin
At (h : HasFDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasMFDerivWithinAt_iff_hasFDerivWithinAt :
    HasMFDerivAt[s] f x f' ↔ HasFDerivWithinAt f f' s x := by
  simpa only [HasMFDerivWithinAt, and_iff_right_iff_imp, mfld_simps] using
    HasFDerivWithinAt.continuousWithinAt

alias ⟨HasMFDerivWithinAt.hasFDerivWithinAt, HasFDerivWithinAt.hasMFDerivWithinAt⟩ :=
  hasMFDerivWithinAt_iff_hasFDerivWithinAt

set_option backward.isDefEq.respectTransparency false in
/-
**hasMFDerivAt_iff_hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivAt_iff_hasFDerivAt : HasMFDerivAt% f x f' ↔ HasFDerivAt f f' x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasMFDerivWithinAt_univ`：hasMFDerivWithinAt_univ : HasMFDerivAt[univ] f 
x f' ↔ HasMFDerivAt% f x f'
· 使用定理 `hasMFDerivWithinAt_iff_hasFDerivWithinAt`：hasMFDerivWithinAt_iff_hasFDer
ivWithinAt : HasMFDerivAt[s] f x f' ↔ HasFDerivWithinAt f f' s x
· 使用定理 `hasFDerivWithinAt_univ`：hasFDerivWithinAt_univ : HasFDerivWithinAt f f' 
univ x ↔ HasFDerivAt f f' x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasMFDerivAt_iff_hasFDerivAt : HasMFDerivAt% f x f' ↔ HasFDerivAt f f' x := by
  rw [← hasMFDerivWithinAt_univ, hasMFDerivWithinAt_iff_hasFDerivWithinAt, hasFDerivWithinAt_univ]

alias ⟨HasMFDerivAt.hasFDerivAt, HasFDerivAt.hasMFDerivAt⟩ := hasMFDerivAt_iff_hasFDerivAt

/-- For maps between vector spaces, `MDifferentiableWithinAt` and `DifferentiableWithinAt`
coincide -/
/-
**mdifferentiableWithinAt_iff_differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：mdifferentiableWithinAt_iff_differentiableWithinAt : MDiffAt[s] f x ↔ Diff
erentiableWithinAt 𝕜 f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `DifferentiableWithinAt.continuousWithinAt`：DifferentiableWithinAt.contin
uousWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : ContinuousWithinAt f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
For maps between vector spaces, `MDifferentiableWithinAt` and `DifferentiableWit
hinAt`
coincide
-/
theorem mdifferentiableWithinAt_iff_differentiableWithinAt :
    MDiffAt[s] f x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [mdifferentiableWithinAt_iff', mfld_simps]
  exact ⟨fun H => H.2, fun H => ⟨H.continuousWithinAt, H⟩⟩

alias ⟨MDifferentiableWithinAt.differentiableWithinAt,
    DifferentiableWithinAt.mdifferentiableWithinAt⟩ :=
  mdifferentiableWithinAt_iff_differentiableWithinAt

/-- For maps between vector spaces, `MDifferentiableAt` and `DifferentiableAt` coincide -/
/-
**mdifferentiableAt_iff_differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_iff_differentiableAt : MDiffAt f x ↔ DifferentiableAt 𝕜 
f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
For maps between vector spaces, `MDifferentiableAt` and `DifferentiableAt` coinc
ide
-/
theorem mdifferentiableAt_iff_differentiableAt :
    MDiffAt f x ↔ DifferentiableAt 𝕜 f x := by
  simp only [mdifferentiableAt_iff, differentiableWithinAt_univ, mfld_simps]
  exact ⟨fun H => H.2, fun H => ⟨H.continuousAt, H⟩⟩

alias ⟨MDifferentiableAt.differentiableAt, DifferentiableAt.mdifferentiableAt⟩ :=
  mdifferentiableAt_iff_differentiableAt

/-- For maps between vector spaces, `MDifferentiableOn` and `DifferentiableOn` coincide -/
/-
**mdifferentiableOn_iff_differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_iff_differentiableOn : MDiff[s] f ↔ DifferentiableOn 𝕜 f
 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
For maps between vector spaces, `MDifferentiableOn` and `DifferentiableOn` coinc
ide
-/
theorem mdifferentiableOn_iff_differentiableOn :
    MDiff[s] f ↔ DifferentiableOn 𝕜 f s := by
  simp only [MDifferentiableOn, DifferentiableOn,
    mdifferentiableWithinAt_iff_differentiableWithinAt]

alias ⟨MDifferentiableOn.differentiableOn, DifferentiableOn.mdifferentiableOn⟩ :=
  mdifferentiableOn_iff_differentiableOn

/-- For maps between vector spaces, `MDifferentiable` and `Differentiable` coincide -/
/-
**mdifferentiable_iff_differentiable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiable_iff_differentiable : MDiff f ↔ Differentiable 𝕜 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
For maps between vector spaces, `MDifferentiable` and `Differentiable` coincide
-/
theorem mdifferentiable_iff_differentiable : MDiff f ↔ Differentiable 𝕜 f := by
  simp only [MDifferentiable, Differentiable, mdifferentiableAt_iff_differentiableAt]

alias ⟨MDifferentiable.differentiable, Differentiable.mdifferentiable⟩ :=
  mdifferentiable_iff_differentiable

set_option backward.isDefEq.respectTransparency false in
/-- For maps between vector spaces, `mfderivWithin` and `fderivWithin` coincide -/
@[simp]
/-
**mfderivWithin_eq_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_eq_fderivWithin : mfderiv[s] f x = fderivWithin 𝕜 f s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fderivWithin_zero_of_not_differentiableWithinAt`：fderivWithin_zero_of_no
t_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 
f s x = 0
· 使用定理 `mdifferentiableWithinAt_iff_differentiableWithinAt`：mdifferentiableWithi
nAt_iff_differentiableWithinAt : MDiffAt[s] f x ↔ DifferentiableWithinAt 𝕜 f s x

--- 原说明 ---
For maps between vector spaces, `mfderivWithin` and `fderivWithin` coincide
-/
theorem mfderivWithin_eq_fderivWithin :
    mfderiv[s] f x = fderivWithin 𝕜 f s x := by
  by_cases h : MDiffAt[s] f x
  · simp only [mfderivWithin, h, if_pos, mfld_simps]
  · simp only [mfderivWithin, h, if_neg, not_false_iff]
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt] at h
    exact (fderivWithin_zero_of_not_differentiableWithinAt h).symm

/-- For maps between vector spaces, `mfderiv` and `fderiv` coincide -/
@[simp]
/-
**mfderiv_eq_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_eq_fderiv : mfderiv% f x = fderiv 𝕜 f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mfderivWithin_univ`：mfderivWithin_univ : mfderiv[univ] f = mfderiv% f
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `mfderivWithin_eq_fderivWithin`：mfderivWithin_eq_fderivWithin : mfderiv[s
] f x = fderivWithin 𝕜 f s x

--- 原说明 ---
For maps between vector spaces, `mfderiv` and `fderiv` coincide
-/
theorem mfderiv_eq_fderiv : mfderiv% f x = fderiv 𝕜 f x := by
  rw [← mfderivWithin_univ, ← fderivWithin_univ]
  exact mfderivWithin_eq_fderivWithin

end MFDerivFDeriv

