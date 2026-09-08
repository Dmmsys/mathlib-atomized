/-
Copyright (c) 2026 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Anatole Dedecker, Yongxi Lin
-/
module

public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.Algebra.Module.Submodule.EqLocus

/-!
# `HasFiniteRange` predicate on linear maps, and the associated equivalence relation

In this file, we define:

* `LinearMap.HasFiniteRange`: a predicate expressing that a linear map has finitely generated range.
* `LinearMap.HasNoetherianRange`: a predicate expressing that a linear map has noetherian range,
  i.e, all submodules of the range are finitely generated. This should be thought of as the
  "better behaved" version of `LinearMap.HasFiniteRange`: for example, `HasNoetherianRange`
  is always stable by addition, whereas `HasFiniteRange` might not be. The two notions agree
  over noetherian rings (hence, in particular, over fields).
* `LinearMap.finiteRange`: the submodule of `E →ₗ[K] F` consisting of linear maps with
  *noetherian* ranges. We allow ourself this slightly abusive name because the more natural
  definition (the submodule of linear maps with finitely generated ranges) only makes sense over a
  noetherian ring, in which case the two notions agree.
* `LinearMap.FiniteRangeSetoid.setoid`: the setoid on `E →ₗ[K] F` associated to
  `LinearMap.finiteRange`. This identifies linear maps which differ by a linear map with
  noetherian range. Equivalently, two linear maps are equivalent for this
  relation if and only if they agree on a subspace `A` of the domain such that `E ⧸ A` is
  noetherian. As with `LinearMap.finiteRange`, we allow ourself a slightly abusive name because the
  more natural definition in terms of `LinearMap.HasFiniteRange` is only well behaved over a
  noetherian ring, in which case the two notions agree.
  This is an instance in the scope `LinearMap.FiniteRangeSetoid`,
  so opening this scope allows this relation to be denoted by `≈`.
* `LinearMap.IsQuasiInverse`: two linear maps `u` and `v` are **quasi-inverses** if we have
  `u ∘ₗ v ≈ id` and `v ∘ₗ u ≈ id` modulo linear maps with noetherian ranges.

-/

@[expose] public section

open LinearMap Submodule Module

namespace LinearMap

variable {K V V' V₂ V₂' V₃ : Type*}

section Semiring

variable [Semiring K]
  [AddCommMonoid V] [Module K V]
  [AddCommMonoid V₂] [Module K V₂]
  [AddCommMonoid V₃] [Module K V₃]

/-- A linear map **has Noetherian range** if its range is a Noetherian module. -/
/-
**LinearMap.HasNoetherianRange** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：HasNoetherianRange (f : V ->ₗ[K] V₂) : Prop
参数：f : V ->ₗ[K] V₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map **has Noetherian range** if its range is a Noetherian module.
-/
def HasNoetherianRange (f : V →ₗ[K] V₂) : Prop :=
  IsNoetherian K f.range

/-- A linear map **has finite range** if its range is finitely generated. -/
/-
**LinearMap.HasFiniteRange** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：HasFiniteRange (f : V ->ₗ[K] V₂) : Prop
参数：f : V ->ₗ[K] V₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map **has finite range** if its range is finitely generated.
-/
def HasFiniteRange (f : V →ₗ[K] V₂) : Prop :=
  f.range.FG
/-
**LinearMap.hasNoetherianRange_iff_range** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：hasNoetherianRange_iff_range {f : V ->ₗ[K] V₂} : f.HasNoetherianRange ↔ Is
Noetherian K f.range
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasNoetherianRange_iff_range {f : V →ₗ[K] V₂} :
    f.HasNoetherianRange ↔ IsNoetherian K f.range :=
  Iff.rfl
/-
**LinearMap.hasFiniteRange_iff_range** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：hasFiniteRange_iff_range {f : V ->ₗ[K] V₂} : f.HasFiniteRange ↔ f.range.FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasFiniteRange_iff_range {f : V →ₗ[K] V₂} :
    f.HasFiniteRange ↔ f.range.FG :=
  Iff.rfl

alias ⟨HasNoetherianRange.isNoetherian_range, _⟩ := hasNoetherianRange_iff_range
alias ⟨HasFiniteRange.fg_range, _⟩ := hasFiniteRange_iff_range
/-
**LinearMap.HasNoetherianRange.hasFiniteRange** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap.HasNoetherianRange`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} [inst : Semiring K] [inst_
1 : AddCommMonoid V]   [inst_2 : _root_.Module K V] [inst_3 : AddCommMonoid V₂] 
[inst_4 : _root_.Module K V₂] {u : V →ₗ[K] V₂},   u.HasNoetherianRange → u.HasFi
niteRange
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.HasNoetherianRange.isNoetherian_range`：∀ {K : Type u_1} {V : T
ype u_2} {V₂ : Type u_4} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [inst_
2 : _root_.Module K V] [inst_3 : AddC…
· 使用定理 `Submodule.FG.of_finite`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M
} [Module.Fi…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
-/
lemma HasNoetherianRange.hasFiniteRange {u : V →ₗ[K] V₂} (h : u.HasNoetherianRange) :
    u.HasFiniteRange :=
  have := h.isNoetherian_range; FG.of_finite
/-
**LinearMap.HasNoetherianRange.zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.HasNoet
herianRange`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} [inst : Semiring K] [inst_
1 : AddCommMonoid V]   [inst_2 : _root_.Module K V] [inst_3 : AddCommMonoid V₂] 
[inst_4 : _root_.Module K V₂], LinearMap.HasNoetherianRange 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_zero`：range_zero [RingHomSurjective τ₁₂] : range (0 : M 
->ₛₗ[τ₁₂] M₂) = ⊥
-/
@[simp] lemma HasNoetherianRange.zero : (0 : V →ₗ[K] V₂).HasNoetherianRange := by
  simp [HasNoetherianRange, isNoetherian_submodule, Submodule.fg_bot]
/-
**LinearMap.HasFiniteRange.zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.HasFiniteRa
nge`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} [inst : Semiring K] [inst_
1 : AddCommMonoid V]   [inst_2 : _root_.Module K V] [inst_3 : AddCommMonoid V₂] 
[inst_4 : _root_.Module K V₂], LinearMap.HasFiniteRange 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.HasNoetherianRange.hasFiniteRange`：∀ {K : Type u_1} {V : Type 
u_2} {V₂ : Type u_4} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [inst_2 : 
_root_.Module K V] [inst_3 : AddC…
· 使用定理 `LinearMap.HasNoetherianRange.zero`：∀ {K : Type u_1} {V : Type u_2} {V₂ :
 Type u_4} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [inst_2 : _root_.Mod
ule K V] [inst_3 : AddC…
-/
@[simp] lemma HasFiniteRange.zero : (0 : V →ₗ[K] V₂).HasFiniteRange :=
  HasNoetherianRange.zero.hasFiniteRange
/-
**LinearMap.HasNoetherianRange.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Ha
sNoetherianRange`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} {V₃ : Type u_6} [inst : Se
miring K] [inst_1 : AddCommMonoid V]   [inst_2 : _root_.Module K V] [inst_3 : Ad
dCommMonoid V₂] [inst_4 : _root_.Module K V₂] [inst_5 : AddCommMonoid V₃]   [ins
t_6 : _root_.Module K V₃] {u : V →ₗ[K] V₂},   u.HasNoetherianRange → ∀ (v : V₂ →
ₗ[K] V₃), (v ∘ₗ u).HasNoetherianRange
参数：v : V₂ →ₗ[K] V₃；v ∘ₗ u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.HasNoetherianRange.eq_1`：∀ {K : Type u_1} {V : Type u_2} {V₂ :
 Type u_4} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [inst_2 : _root_.Mod
ule K V] [inst_3 : AddC…
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
-/
lemma HasNoetherianRange.comp_left {u : V →ₗ[K] V₂} (h : u.HasNoetherianRange)
    (v : V₂ →ₗ[K] V₃) : (v ∘ₗ u).HasNoetherianRange := by
  rw [LinearMap.HasNoetherianRange, LinearMap.range_comp] at *
  infer_instance
/-
**LinearMap.HasFiniteRange.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.HasFin
iteRange`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} {V₃ : Type u_6} [inst : Se
miring K] [inst_1 : AddCommMonoid V]   [inst_2 : _root_.Module K V] [inst_3 : Ad
dCommMonoid V₂] [inst_4 : _root_.Module K V₂] [inst_5 : AddCommMonoid V₃]   [ins
t_6 : _root_.Module K V₃] {u : V →ₗ[K] V₂}, u.HasFiniteRange → ∀ (v : V₂ →ₗ[K] V
₃), (v ∘ₗ u).HasFiniteRange
参数：v : V₂ →ₗ[K] V₃；v ∘ₗ u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.HasFiniteRange.eq_1`：∀ {K : Type u_1} {V : Type u_2} {V₂ : Typ
e u_4} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [inst_2 : _root_.Module 
K V] [inst_3 : AddC…
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
-/
lemma HasFiniteRange.comp_left {u : V →ₗ[K] V₂} (h : u.HasFiniteRange)
    (v : V₂ →ₗ[K] V₃) : (v ∘ₗ u).HasFiniteRange := by
  rw [LinearMap.HasFiniteRange, LinearMap.range_comp] at *
  exact Submodule.FG.map v h
/-
**LinearMap.HasNoetherianRange.of_isNoetherian_dom** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap.HasNoetherianRange`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} [inst : Semiring K] [inst_
1 : AddCommMonoid V]   [inst_2 : _root_.Module K V] [inst_3 : AddCommMonoid V₂] 
[inst_4 : _root_.Module K V₂] [IsNoetherian K V]   {f : V →ₗ[K] V₂}, f.HasNoethe
rianRange
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.hasNoetherianRange_iff_range`：hasNoetherianRange_iff_range {f 
: V ->ₗ[K] V₂} : f.HasNoetherianRange ↔ IsNoetherian K f.range
-/
@[simp] lemma HasNoetherianRange.of_isNoetherian_dom [IsNoetherian K V] {f : V →ₗ[K] V₂} :
    f.HasNoetherianRange :=
  hasNoetherianRange_iff_range.mpr inferInstance
/-
**LinearMap.HasFiniteRange.of_finite_dom** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Ha
sFiniteRange`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} [inst : Semiring K] [inst_
1 : AddCommMonoid V]   [inst_2 : _root_.Module K V] [inst_3 : AddCommMonoid V₂] 
[inst_4 : _root_.Module K V₂] [Module.Finite K V]   {f : V →ₗ[K] V₂}, f.HasFinit
eRange
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[simp] lemma HasFiniteRange.of_finite_dom [Module.Finite K V] {f : V →ₗ[K] V₂} :
    f.HasFiniteRange := by
  simp [HasFiniteRange]
/-
**LinearMap.HasNoetherianRange.of_isNoetherian_rng** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap.HasNoetherianRange`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} [inst : Semiring K] [inst_
1 : AddCommMonoid V]   [inst_2 : _root_.Module K V] [inst_3 : AddCommMonoid V₂] 
[inst_4 : _root_.Module K V₂] [IsNoetherian K V₂]   {f : V →ₗ[K] V₂}, f.HasNoeth
erianRange
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.hasNoetherianRange_iff_range`：hasNoetherianRange_iff_range {f 
: V ->ₗ[K] V₂} : f.HasNoetherianRange ↔ IsNoetherian K f.range
-/
@[simp] lemma HasNoetherianRange.of_isNoetherian_rng [IsNoetherian K V₂] {f : V →ₗ[K] V₂} :
    f.HasNoetherianRange :=
  hasNoetherianRange_iff_range.mpr inferInstance
/-
**LinearMap.HasFiniteRange.of_isNoetherian_rng** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map.HasFiniteRange`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} [inst : Semiring K] [inst_
1 : AddCommMonoid V]   [inst_2 : _root_.Module K V] [inst_3 : AddCommMonoid V₂] 
[inst_4 : _root_.Module K V₂] [IsNoetherian K V₂]   {f : V →ₗ[K] V₂}, f.HasFinit
eRange
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.HasNoetherianRange.hasFiniteRange`：∀ {K : Type u_1} {V : Type 
u_2} {V₂ : Type u_4} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [inst_2 : 
_root_.Module K V] [inst_3 : AddC…
· 使用定理 `LinearMap.HasNoetherianRange.of_isNoetherian_rng`：∀ {K : Type u_1} {V : 
Type u_2} {V₂ : Type u_4} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [inst
_2 : _root_.Module K V] [inst_3 : AddC…
-/
@[simp] lemma HasFiniteRange.of_isNoetherian_rng [IsNoetherian K V₂] {f : V →ₗ[K] V₂} :
    f.HasFiniteRange :=
  HasNoetherianRange.of_isNoetherian_rng.hasFiniteRange

end Semiring

section Ring

variable [Ring K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

/-
**LinearMap.HasFiniteRange.hasNoetherianRange** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap.HasFiniteRange`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} [inst : Ring K] [inst_1 : 
AddCommGroup V] [inst_2 : _root_.Module K V]   [inst_3 : AddCommGroup V₂] [inst_
4 : _root_.Module K V₂] [IsNoetherianRing K] {u : V →ₗ[K] V₂},   u.HasFiniteRang
e → u.HasNoetherianRange
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.HasNoetherianRange.eq_1`：∀ {K : Type u_1} {V : Type u_2} {V₂ :
 Type u_4} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [inst_2 : _root_.Mod
ule K V] [inst_3 : AddC…
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `LinearMap.HasFiniteRange.fg_range`：∀ {K : Type u_1} {V : Type u_2} {V₂ :
 Type u_4} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [inst_2 : _root_.Mod
ule K V] [inst_3 : AddC…
-/
lemma HasFiniteRange.hasNoetherianRange [IsNoetherianRing K] {u : V →ₗ[K] V₂}
    (h : u.HasFiniteRange) : u.HasNoetherianRange := by
  rw [HasNoetherianRange]
  have := Finite.of_fg h.fg_range
  infer_instance
/-
**LinearMap.hasNoetherianRange_iff_hasFiniteRange** 是 Mathlib 中的一个引理，位于命名空间 `Lin
earMap`。
形式化陈述：hasNoetherianRange_iff_hasFiniteRange [IsNoetherianRing K] {u : V ->ₗ[K] V
₂} : u.HasNoetherianRange ↔ u.HasFiniteRange
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.HasNoetherianRange.hasFiniteRange`：∀ {K : Type u_1} {V : Type 
u_2} {V₂ : Type u_4} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [inst_2 : 
_root_.Module K V] [inst_3 : AddC…
· 使用定理 `LinearMap.HasFiniteRange.hasNoetherianRange`：∀ {K : Type u_1} {V : Type 
u_2} {V₂ : Type u_4} [inst : Ring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.
Module K V]   [inst_3 : AddCommGr…
-/
lemma hasNoetherianRange_iff_hasFiniteRange [IsNoetherianRing K] {u : V →ₗ[K] V₂} :
    u.HasNoetherianRange ↔ u.HasFiniteRange :=
  ⟨HasNoetherianRange.hasFiniteRange, HasFiniteRange.hasNoetherianRange⟩
/-
**LinearMap.HasNoetherianRange.comp_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.H
asNoetherianRange`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} {V₃ : Type u_6} [inst : Ri
ng K] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module K V] [inst_3 : AddComm
Group V₂] [inst_4 : _root_.Module K V₂] [inst_5 : AddCommGroup V₃]   [inst_6 : _
root_.Module K V₃] {v : V₂ →ₗ[K] V₃},   v.HasNoetherianRange → ∀ (u : V →ₗ[K] V₂
), (v ∘ₗ u).HasNoetherianRange
参数：u : V →ₗ[K] V₂；v ∘ₗ u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.HasNoetherianRange.eq_1`：∀ {K : Type u_1} {V : Type u_2} {V₂ :
 Type u_4} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [inst_2 : _root_.Mod
ule K V] [inst_3 : AddC…
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `isNoetherian_of_le`：isNoetherian_of_le {s t : Submodule R M} [ht : IsNoe
therian R t] (h : s <= t) : IsNoetherian R s
· 使用定理 `LinearMap.map_le_range`：map_le_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} {p : Submodule R M} : map f p <= range f
-/
lemma HasNoetherianRange.comp_right {v : V₂ →ₗ[K] V₃} (h : v.HasNoetherianRange)
    (u : V →ₗ[K] V₂) : (v ∘ₗ u).HasNoetherianRange := by
  rw [HasNoetherianRange, LinearMap.range_comp] at *
  exact isNoetherian_of_le map_le_range
/-
**LinearMap.HasFiniteRange.comp_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.HasFi
niteRange`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} {V₃ : Type u_6} [inst : Ri
ng K] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module K V] [inst_3 : AddComm
Group V₂] [inst_4 : _root_.Module K V₂] [inst_5 : AddCommGroup V₃]   [inst_6 : _
root_.Module K V₃] [IsNoetherianRing K] {v : V₂ →ₗ[K] V₃},   v.HasFiniteRange → 
∀ (u : V →ₗ[K] V₂), (v ∘ₗ u).HasFiniteRange
参数：u : V →ₗ[K] V₂；v ∘ₗ u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.HasNoetherianRange.hasFiniteRange`：∀ {K : Type u_1} {V : Type 
u_2} {V₂ : Type u_4} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [inst_2 : 
_root_.Module K V] [inst_3 : AddC…
· 使用定理 `LinearMap.HasNoetherianRange.comp_right`：∀ {K : Type u_1} {V : Type u_2}
 {V₂ : Type u_4} {V₃ : Type u_6} [inst : Ring K] [inst_1 : AddCommGroup V]   [in
st_2 : _root_.Module K V] [in…
· 使用定理 `LinearMap.HasFiniteRange.hasNoetherianRange`：∀ {K : Type u_1} {V : Type 
u_2} {V₂ : Type u_4} [inst : Ring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.
Module K V]   [inst_3 : AddCommGr…
-/
lemma HasFiniteRange.comp_right [IsNoetherianRing K] {v : V₂ →ₗ[K] V₃} (h : v.HasFiniteRange)
    (u : V →ₗ[K] V₂) : (v ∘ₗ u).HasFiniteRange :=
  h.hasNoetherianRange.comp_right _ |>.hasFiniteRange
/-
**LinearMap.HasNoetherianRange.neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.HasNoeth
erianRange`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} [inst : Ring K] [inst_1 : 
AddCommGroup V] [inst_2 : _root_.Module K V]   [inst_3 : AddCommGroup V₂] [inst_
4 : _root_.Module K V₂] {f : V →ₗ[K] V₂},   f.HasNoetherianRange → (-f).HasNoeth
erianRange
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.HasNoetherianRange.eq_1`：∀ {K : Type u_1} {V : Type u_2} {V₂ :
 Type u_4} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [inst_2 : _root_.Mod
ule K V] [inst_3 : AddC…
· 使用定理 `LinearMap.range_neg`：range_neg {R : Type*} {R₂ : Type*} {M : Type*} {M₂ 
: Type*} [Semiring R] [Ring R₂] [AddCommMonoid M] [AddCommGroup M₂] [Module R M]
 [Module …
-/
@[simp] lemma HasNoetherianRange.neg {f : V →ₗ[K] V₂}
    (hf : f.HasNoetherianRange) : (-f).HasNoetherianRange := by
  rwa [HasNoetherianRange, LinearMap.range_neg]
/-
**LinearMap.HasFiniteRange.neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.HasFiniteRan
ge`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} [inst : Ring K] [inst_1 : 
AddCommGroup V] [inst_2 : _root_.Module K V]   [inst_3 : AddCommGroup V₂] [inst_
4 : _root_.Module K V₂] {f : V →ₗ[K] V₂}, f.HasFiniteRange → (-f).HasFiniteRange
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.HasFiniteRange.eq_1`：∀ {K : Type u_1} {V : Type u_2} {V₂ : Typ
e u_4} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [inst_2 : _root_.Module 
K V] [inst_3 : AddC…
· 使用定理 `LinearMap.range_neg`：range_neg {R : Type*} {R₂ : Type*} {M : Type*} {M₂ 
: Type*} [Semiring R] [Ring R₂] [AddCommMonoid M] [AddCommGroup M₂] [Module R M]
 [Module …
-/
@[simp] lemma HasFiniteRange.neg {f : V →ₗ[K] V₂}
    (hf : f.HasFiniteRange) : (-f).HasFiniteRange := by
  rwa [HasFiniteRange, LinearMap.range_neg]
/-
**LinearMap.HasNoetherianRange.add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.HasNoeth
erianRange`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} [inst : Ring K] [inst_1 : 
AddCommGroup V] [inst_2 : _root_.Module K V]   [inst_3 : AddCommGroup V₂] [inst_
4 : _root_.Module K V₂] {f g : V →ₗ[K] V₂},   f.HasNoetherianRange → g.HasNoethe
rianRange → (f + g).HasNoetherianRange
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.HasNoetherianRange.eq_1`：∀ {K : Type u_1} {V : Type u_2} {V₂ :
 Type u_4} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [inst_2 : _root_.Mod
ule K V] [inst_3 : AddC…
· 使用定理 `isNoetherian_of_le`：isNoetherian_of_le {s t : Submodule R M} [ht : IsNoe
therian R t] (h : s <= t) : IsNoetherian R s
· 使用定理 `LinearMap.range_add_le`：range_add_le [RingHomSurjective τ₁₂] (f g : M ->
ₛₗ[τ₁₂] M₂) : range (f + g) <= range f ⊔ range g
-/
@[simp] lemma HasNoetherianRange.add {f g : V →ₗ[K] V₂}
    (hf : f.HasNoetherianRange) (hg : g.HasNoetherianRange) : (f + g).HasNoetherianRange := by
  rw [HasNoetherianRange] at *
  exact isNoetherian_of_le (range_add_le f g)
/-
**LinearMap.HasFiniteRange.add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.HasFiniteRan
ge`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} [inst : Ring K] [inst_1 : 
AddCommGroup V] [inst_2 : _root_.Module K V]   [inst_3 : AddCommGroup V₂] [inst_
4 : _root_.Module K V₂] [IsNoetherianRing K] {f g : V →ₗ[K] V₂},   f.HasFiniteRa
nge → g.HasFiniteRange → (f + g).HasFiniteRange
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.HasNoetherianRange.hasFiniteRange`：∀ {K : Type u_1} {V : Type 
u_2} {V₂ : Type u_4} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [inst_2 : 
_root_.Module K V] [inst_3 : AddC…
· 使用定理 `LinearMap.HasNoetherianRange.add`：∀ {K : Type u_1} {V : Type u_2} {V₂ : 
Type u_4} [inst : Ring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
   [inst_3 : AddCommGr…
· 使用定理 `LinearMap.HasFiniteRange.hasNoetherianRange`：∀ {K : Type u_1} {V : Type 
u_2} {V₂ : Type u_4} [inst : Ring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.
Module K V]   [inst_3 : AddCommGr…
-/
@[simp] lemma HasFiniteRange.add [IsNoetherianRing K] {f g : V →ₗ[K] V₂}
    (hf : f.HasFiniteRange) (hg : g.HasFiniteRange) : (f + g).HasFiniteRange :=
  hf.hasNoetherianRange.add hg.hasNoetherianRange |>.hasFiniteRange
/-
**LinearMap.HasNoetherianRange.sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.HasNoeth
erianRange`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} [inst : Ring K] [inst_1 : 
AddCommGroup V] [inst_2 : _root_.Module K V]   [inst_3 : AddCommGroup V₂] [inst_
4 : _root_.Module K V₂] {f g : V →ₗ[K] V₂},   f.HasNoetherianRange → g.HasNoethe
rianRange → (f - g).HasNoetherianRange
参数：f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.HasNoetherianRange.add`：∀ {K : Type u_1} {V : Type u_2} {V₂ : 
Type u_4} [inst : Ring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
   [inst_3 : AddCommGr…
· 使用定理 `LinearMap.HasNoetherianRange.neg`：∀ {K : Type u_1} {V : Type u_2} {V₂ : 
Type u_4} [inst : Ring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
   [inst_3 : AddCommGr…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
@[simp] lemma HasNoetherianRange.sub {f g : V →ₗ[K] V₂}
    (hf : f.HasNoetherianRange) (hg : g.HasNoetherianRange) : (f - g).HasNoetherianRange :=
  sub_eq_add_neg f g ▸ hf.add hg.neg
/-
**LinearMap.HasFiniteRange.sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.HasFiniteRan
ge`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} [inst : Ring K] [inst_1 : 
AddCommGroup V] [inst_2 : _root_.Module K V]   [inst_3 : AddCommGroup V₂] [inst_
4 : _root_.Module K V₂] [IsNoetherianRing K] {f g : V →ₗ[K] V₂},   f.HasFiniteRa
nge → g.HasFiniteRange → (f - g).HasFiniteRange
参数：f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.HasFiniteRange.add`：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type
 u_4} [inst : Ring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [
inst_3 : AddCommGr…
· 使用定理 `LinearMap.HasFiniteRange.neg`：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type
 u_4} [inst : Ring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [
inst_3 : AddCommGr…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
@[simp] lemma HasFiniteRange.sub [IsNoetherianRing K] {f g : V →ₗ[K] V₂}
    (hf : f.HasFiniteRange) (hg : g.HasFiniteRange) : (f - g).HasFiniteRange :=
  sub_eq_add_neg f g ▸ hf.add hg.neg
/-
**LinearMap.hasNoetherianRange_iff_quotient_ker** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap`。
形式化陈述：hasNoetherianRange_iff_quotient_ker {f : V ->ₗ[K] V₂} : f.HasNoetherianRan
ge ↔ IsNoetherian K (V ⧸ f.ker)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LinearEquiv.isNoetherian_iff`：LinearEquiv.isNoetherian_iff {σ : R ->+* S
} {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) :
 IsNoetherian R M …
-/
theorem hasNoetherianRange_iff_quotient_ker {f : V →ₗ[K] V₂} :
    f.HasNoetherianRange ↔ IsNoetherian K (V ⧸ f.ker) :=
  f.quotKerEquivRange.isNoetherian_iff.symm

@[simp]
/-
**LinearMap.ker_coFG_iff_hasFiniteRange** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_coFG_iff_hasFiniteRange {f : V ->ₗ[K] V₂} : f.ker.CoFG ↔ f.HasFiniteRa
nge
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Submodule.range_fg_iff_ker_cofg`：range_fg_iff_ker_cofg {f : M ->ₗ[R] N} 
: (range f).FG ↔ (ker f).CoFG
-/
theorem ker_coFG_iff_hasFiniteRange {f : V →ₗ[K] V₂} :
    f.ker.CoFG ↔ f.HasFiniteRange :=
  range_fg_iff_ker_cofg.symm

alias ⟨HasNoetherianRange.quotient_ker, _⟩ := hasNoetherianRange_iff_quotient_ker
alias ⟨_, HasFiniteRange.cofg_ker⟩ := ker_coFG_iff_hasFiniteRange

end Ring

section CommRing

variable [CommRing K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

/-
**LinearMap.HasNoetherianRange.smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.HasNoet
herianRange`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} [inst : CommRing K] [inst_
1 : AddCommGroup V]   [inst_2 : _root_.Module K V] [inst_3 : AddCommGroup V₂] [i
nst_4 : _root_.Module K V₂] {f : V →ₗ[K] V₂},   f.HasNoetherianRange → ∀ (c : K)
, (c • f).HasNoetherianRange
参数：c : K；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.HasNoetherianRange.comp_left`：∀ {K : Type u_1} {V : Type u_2} 
{V₂ : Type u_4} {V₃ : Type u_6} [inst : Semiring K] [inst_1 : AddCommMonoid V]  
 [inst_2 : _root_.Module K V…
-/
@[simp] lemma HasNoetherianRange.smul {f : V →ₗ[K] V₂}
    (hf : f.HasNoetherianRange) (c : K) : (c • f).HasNoetherianRange :=
  hf.comp_left (lsmul K V₂ c)
/-
**LinearMap.HasFiniteRange.smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.HasFiniteRa
nge`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} [inst : CommRing K] [inst_
1 : AddCommGroup V]   [inst_2 : _root_.Module K V] [inst_3 : AddCommGroup V₂] [i
nst_4 : _root_.Module K V₂] {f : V →ₗ[K] V₂},   f.HasFiniteRange → ∀ (c : K), (c
 • f).HasFiniteRange
参数：c : K；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.HasFiniteRange.comp_left`：∀ {K : Type u_1} {V : Type u_2} {V₂ 
: Type u_4} {V₃ : Type u_6} [inst : Semiring K] [inst_1 : AddCommMonoid V]   [in
st_2 : _root_.Module K V…
-/
@[simp] lemma HasFiniteRange.smul {f : V →ₗ[K] V₂}
    (hf : f.HasFiniteRange) (c : K) : (c • f).HasFiniteRange :=
  hf.comp_left (lsmul K V₂ c)

variable (K V V₂) in
/-- `LinearMap.finiteRange` is the submodule of `V →ₗ[K] W` consisting of linear maps satisfying
`LinearMap.HasNoetherianRange`. We allow ourself this slightly abusive name because the set of
linear maps satisfying `LinearMap.HasFiniteRange` is only a submodule over a noetherian ring,
in which case the two notions agree. -/
/-
**LinearMap.finiteRange** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：finiteRange : Submodule K (V ->ₗ[K] V₂) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMap.finiteRange` is the submodule of `V →ₗ[K] W` consisting of linear map
s satisfying
`LinearMap.HasNoetherianRange`. We allow ourself this slightly abusive name beca
use the set of
linear maps satisfying `LinearMap.HasFiniteRange` is only a submodule over a noe
therian ring,
in which case the two notions agree.
-/
def finiteRange : Submodule K (V →ₗ[K] V₂) where
  carrier := {u | u.HasNoetherianRange}
  add_mem' hu hv := by simp_all
  zero_mem' := by simp
  smul_mem' c hu := by simp_all
/-
**LinearMap.mem_finiteRange_iff_hasNoetherianRange** 是 Mathlib 中的一个引理，位于命名空间 `Li
nearMap`。
形式化陈述：mem_finiteRange_iff_hasNoetherianRange {f : V ->ₗ[K] V₂} : f in finiteRang
e K V V₂ ↔ f.HasNoetherianRange
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_finiteRange_iff_hasNoetherianRange {f : V →ₗ[K] V₂} :
    f ∈ finiteRange K V V₂ ↔ f.HasNoetherianRange :=
  Iff.rfl
/-
**LinearMap.mem_finiteRange_iff_hasFiniteRange** 是 Mathlib 中的一个引理，位于命名空间 `Linear
Map`。
形式化陈述：mem_finiteRange_iff_hasFiniteRange [IsNoetherianRing K] {f : V ->ₗ[K] V₂} 
: f in finiteRange K V V₂ ↔ f.HasFiniteRange
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.mem_finiteRange_iff_hasNoetherianRange`：mem_finiteRange_iff_ha
sNoetherianRange {f : V ->ₗ[K] V₂} : f in finiteRange K V V₂ ↔ f.HasNoetherianRa
nge
· 使用引理 `LinearMap.hasNoetherianRange_iff_hasFiniteRange`：hasNoetherianRange_iff_
hasFiniteRange [IsNoetherianRing K] {u : V ->ₗ[K] V₂} : u.HasNoetherianRange ↔ u
.HasFiniteRange
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_finiteRange_iff_hasFiniteRange [IsNoetherianRing K] {f : V →ₗ[K] V₂} :
    f ∈ finiteRange K V V₂ ↔ f.HasFiniteRange := by
  rw [mem_finiteRange_iff_hasNoetherianRange, hasNoetherianRange_iff_hasFiniteRange]

end CommRing

section Setoid

variable [CommRing K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

namespace FiniteRangeSetoid

/-- This is the equivalence relation on linear maps such that `u ≈ v` precisely
when `u - v` is a linear map with noetherian range. We allow ourself this slightly abusive name
because the more natural definition (`u - v` has finitely generated range) only yields a
well-behaved relation (more precisely, an additive congruence relation compatible with composition
on both sides) over a noetherian ring, in which case the two notions agree.

This setoid is declared as an instance in scope `LinearMap.FiniteRangeSetoid`. -/
/-
**LinearMap.FiniteRangeSetoid.setoid** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.Finite
RangeSetoid`。
形式化陈述：{K : Type u_1} →   {V : Type u_2} →     {V₂ : Type u_4} →       [inst : Co
mmRing K] →         [inst_1 : AddCommGroup V] →           [inst_2 : _root_.Modul
e K V] →             [inst_3 : AddCommGroup V₂] → [inst_4 : _root_.Module K V₂] 
→ Setoid (V →ₗ[K] V₂)
参数：V →ₗ[K] V₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the equivalence relation on linear maps such that `u ≈ v` precisely
when `u - v` is a linear map with noetherian range. We allow ourself this slight
ly abusive name
because the more natural definition (`u - v` has finitely generated range) only 
yields a
well-behaved relation (more precisely, an additive congruence relation compatibl
e with composition
on both sides) over a noetherian ring, in which case the two notions agree.

This setoid is declared as an instance in scope `LinearMap.FiniteRangeSetoid`.
-/
scoped instance setoid : Setoid (V →ₗ[K] V₂) := (LinearMap.finiteRange K V V₂).quotientRel
/-
**LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange** 是 Mathlib 中的一个引理，位于
命名空间 `LinearMap.FiniteRangeSetoid`。
形式化陈述：equiv_iff_hasNoetherianRange {u v : V ->ₗ[K] V₂} : u ≈ v ↔ (u - v).HasNoet
herianRange
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.quotientRel_def`：quotientRel_def {x y : M} : p.quotientRel x y
 ↔ x - y in p
-/
lemma equiv_iff_hasNoetherianRange {u v : V →ₗ[K] V₂} : u ≈ v ↔ (u - v).HasNoetherianRange :=
  Submodule.quotientRel_def _
/-
**LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange** 是 Mathlib 中的一个引理，位于命名空间
 `LinearMap.FiniteRangeSetoid`。
形式化陈述：equiv_iff_hasFiniteRange [IsNoetherianRing K] {u v : V ->ₗ[K] V₂} : u ≈ v 
↔ (u - v).HasFiniteRange
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange`：equiv_iff_hasN
oetherianRange {u v : V ->ₗ[K] V₂} : u ≈ v ↔ (u - v).HasNoetherianRange
· 使用引理 `LinearMap.hasNoetherianRange_iff_hasFiniteRange`：hasNoetherianRange_iff_
hasFiniteRange [IsNoetherianRing K] {u : V ->ₗ[K] V₂} : u.HasNoetherianRange ↔ u
.HasFiniteRange
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma equiv_iff_hasFiniteRange [IsNoetherianRing K] {u v : V →ₗ[K] V₂} :
    u ≈ v ↔ (u - v).HasFiniteRange := by
  rw [equiv_iff_hasNoetherianRange, hasNoetherianRange_iff_hasFiniteRange]
/-
**LinearMap.FiniteRangeSetoid.equiv_zero_iff_hasNoetherianRange** 是 Mathlib 中的一个
引理，位于命名空间 `LinearMap.FiniteRangeSetoid`。
形式化陈述：equiv_zero_iff_hasNoetherianRange {u : V ->ₗ[K] V₂} : u ≈ 0 ↔ u.HasNoether
ianRange
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma equiv_zero_iff_hasNoetherianRange {u : V →ₗ[K] V₂} : u ≈ 0 ↔ u.HasNoetherianRange := by
  simp [equiv_iff_hasNoetherianRange]
/-
**LinearMap.FiniteRangeSetoid.equiv_zero_iff_hasFiniteRange** 是 Mathlib 中的一个引理，位
于命名空间 `LinearMap.FiniteRangeSetoid`。
形式化陈述：equiv_zero_iff_hasFiniteRange [IsNoetherianRing K] {u : V ->ₗ[K] V₂} : u ≈
 0 ↔ u.HasFiniteRange
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma equiv_zero_iff_hasFiniteRange [IsNoetherianRing K] {u : V →ₗ[K] V₂} :
    u ≈ 0 ↔ u.HasFiniteRange := by
  simp [equiv_iff_hasFiniteRange]
/-
**LinearMap.FiniteRangeSetoid.equiv_iff_isNoetherian_quotient_eqLocus** 是 Mathli
b 中的一个引理，位于命名空间 `LinearMap.FiniteRangeSetoid`。
形式化陈述：equiv_iff_isNoetherian_quotient_eqLocus {u v : V ->ₗ[K] V₂} : u ≈ v ↔ IsNo
etherian K (V ⧸ eqLocus u v)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange`：equiv_iff_hasN
oetherianRange {u v : V ->ₗ[K] V₂} : u ≈ v ↔ (u - v).HasNoetherianRange
· 使用定理 `LinearMap.hasNoetherianRange_iff_quotient_ker`：hasNoetherianRange_iff_qu
otient_ker {f : V ->ₗ[K] V₂} : f.HasNoetherianRange ↔ IsNoetherian K (V ⧸ f.ker)
· 使用定理 `LinearMap.eqLocus_eq_ker_sub`：eqLocus_eq_ker_sub (f g : M ->ₛₗ[τ₁₂] M₂) 
: eqLocus f g = ker (f - g)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma equiv_iff_isNoetherian_quotient_eqLocus {u v : V →ₗ[K] V₂} :
    u ≈ v ↔ IsNoetherian K (V ⧸ eqLocus u v) := by
  rw [equiv_iff_hasNoetherianRange, hasNoetherianRange_iff_quotient_ker, eqLocus_eq_ker_sub]
/-
**LinearMap.FiniteRangeSetoid.equiv_iff_eqLocus_coFG** 是 Mathlib 中的一个引理，位于命名空间 `
LinearMap.FiniteRangeSetoid`。
形式化陈述：equiv_iff_eqLocus_coFG [IsNoetherianRing K] {u v : V ->ₗ[K] V₂} : u ≈ v ↔ 
(eqLocus u v).CoFG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.eqLocus_eq_ker_sub`：eqLocus_eq_ker_sub (f g : M ->ₛₗ[τ₁₂] M₂) 
: eqLocus f g = ker (f - g)
· 使用定理 `LinearMap.ker_coFG_iff_hasFiniteRange`：ker_coFG_iff_hasFiniteRange {f : 
V ->ₗ[K] V₂} : f.ker.CoFG ↔ f.HasFiniteRange
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange`：equiv_iff_hasFinit
eRange [IsNoetherianRing K] {u v : V ->ₗ[K] V₂} : u ≈ v ↔ (u - v).HasFiniteRange
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma equiv_iff_eqLocus_coFG [IsNoetherianRing K] {u v : V →ₗ[K] V₂} :
    u ≈ v ↔ (eqLocus u v).CoFG := by
  rw [eqLocus_eq_ker_sub, ker_coFG_iff_hasFiniteRange, equiv_iff_hasFiniteRange]
/-
**LinearMap.FiniteRangeSetoid.equiv_of_eqOn_of_isNoetherian** 是 Mathlib 中的一个引理，位
于命名空间 `LinearMap.FiniteRangeSetoid`。
形式化陈述：equiv_of_eqOn_of_isNoetherian {u v : V ->ₗ[K] V₂} (A : Submodule K V) [quo
t_A_noeth : IsNoetherian K (V ⧸ A)] (eqOn_A : Set.EqOn u v A) : u ≈ v
参数：A : Submodule K V；V ⧸ A；eqOn_A : Set.EqOn u v A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.le_eqLocus`：le_eqLocus {f g : M ->ₛₗ[τ₁₂] M₂} {S : Submodule R
 M} : S <= eqLocus f g ↔ Set.EqOn f g S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_iff_isNoetherian_quotient_eqLocus`：equ
iv_iff_isNoetherian_quotient_eqLocus {u v : V ->ₗ[K] V₂} : u ≈ v ↔ IsNoetherian 
K (V ⧸ eqLocus u v)
· 使用定理 `isNoetherian_of_surjective`：isNoetherian_of_surjective {σ : R ->+* S} [R
ingHomSurjective σ] (f : M ->ₛₗ[σ] P) (hf : LinearMap.range f = ⊤) [IsNoetherian
 R M] : IsNoethe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.range_mapQ`：range_mapQ [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂
] M₂) (h : p <= comap f q) : (p.mapQ q f h).range = f.range.map q.mkQ
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `LinearMap.range_id`：range_id : range (LinearMap.id : M ->ₗ[R] M) = ⊤
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_mkQ`：range_mkQ : range p.mkQ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equiv_of_eqOn_of_isNoetherian {u v : V →ₗ[K] V₂} (A : Submodule K V)
    [quot_A_noeth : IsNoetherian K (V ⧸ A)] (eqOn_A : Set.EqOn u v A) : u ≈ v := by
  have A_le : A ≤ eqLocus u v := le_eqLocus.mpr eqOn_A
  rw [equiv_iff_isNoetherian_quotient_eqLocus]
  refine isNoetherian_of_surjective (A.mapQ (eqLocus u v) id A_le) (by simp [range_mapQ])
/-
**LinearMap.FiniteRangeSetoid.equiv_of_eqOn_coFG** 是 Mathlib 中的一个引理，位于命名空间 `Line
arMap.FiniteRangeSetoid`。
形式化陈述：equiv_of_eqOn_coFG [IsNoetherianRing K] {u v : V ->ₗ[K] V₂} {A : Submodule
 K V} (A_coFG : A.CoFG) (eqOn_A : Set.EqOn u v A) : u ≈ v
参数：A_coFG : A.CoFG；eqOn_A : Set.EqOn u v A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_iff_eqLocus_coFG`：equiv_iff_eqLocus_co
FG [IsNoetherianRing K] {u v : V ->ₗ[K] V₂} : u ≈ v ↔ (eqLocus u v).CoFG
· 使用定理 `Submodule.CoFG.of_le`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [i
nst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {S T : Submodule R M}, S 
≤ T → S.Co…
· 使用定理 `LinearMap.le_eqLocus`：le_eqLocus {f g : M ->ₛₗ[τ₁₂] M₂} {S : Submodule R
 M} : S <= eqLocus f g ↔ Set.EqOn f g S
-/
lemma equiv_of_eqOn_coFG [IsNoetherianRing K] {u v : V →ₗ[K] V₂} {A : Submodule K V}
    (A_coFG : A.CoFG) (eqOn_A : Set.EqOn u v A) : u ≈ v :=
  equiv_iff_eqLocus_coFG.mpr <| A_coFG.of_le <| le_eqLocus.mpr eqOn_A

@[gcongr]
/-
**LinearMap.FiniteRangeSetoid.equiv_comp_right** 是 Mathlib 中的一个引理，位于命名空间 `Linear
Map.FiniteRangeSetoid`。
形式化陈述：equiv_comp_right {u : V ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃} (h' : v ≈ v') : v
 ∘ₗ u ≈ v' ∘ₗ u
参数：h' : v ≈ v'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange`：equiv_iff_hasN
oetherianRange {u v : V ->ₗ[K] V₂} : u ≈ v ↔ (u - v).HasNoetherianRange
· 使用定理 `LinearMap.HasNoetherianRange.comp_right`：∀ {K : Type u_1} {V : Type u_2}
 {V₂ : Type u_4} {V₃ : Type u_6} [inst : Ring K] [inst_1 : AddCommGroup V]   [in
st_2 : _root_.Module K V] [in…
-/
lemma equiv_comp_right {u : V →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃} (h' : v ≈ v') :
    v ∘ₗ u ≈ v' ∘ₗ u := by
  rw [equiv_iff_hasNoetherianRange] at *
  exact h'.comp_right u

@[gcongr]
/-
**LinearMap.FiniteRangeSetoid.equiv_comp_left** 是 Mathlib 中的一个引理，位于命名空间 `LinearM
ap.FiniteRangeSetoid`。
形式化陈述：equiv_comp_left {u v : V ->ₗ[K] V₂} {u' : V₂ ->ₗ[K] V₃} (h : u ≈ v) : u' ∘
ₗ u ≈ u' ∘ₗ v
参数：h : u ≈ v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange`：equiv_iff_hasN
oetherianRange {u v : V ->ₗ[K] V₂} : u ≈ v ↔ (u - v).HasNoetherianRange
· 使用定理 `LinearMap.comp_sub`：comp_sub (f g : M ->ₛₗ[σ₁₂] N₂) (h : N₂ ->ₛₗ[σ₂₃] N₃
) : h.comp (g - f) = h.comp g - h.comp f
· 使用定理 `LinearMap.HasNoetherianRange.comp_left`：∀ {K : Type u_1} {V : Type u_2} 
{V₂ : Type u_4} {V₃ : Type u_6} [inst : Semiring K] [inst_1 : AddCommMonoid V]  
 [inst_2 : _root_.Module K V…
-/
lemma equiv_comp_left {u v : V →ₗ[K] V₂} {u' : V₂ →ₗ[K] V₃} (h : u ≈ v) :
    u' ∘ₗ u ≈ u' ∘ₗ v := by
  rw [equiv_iff_hasNoetherianRange] at *
  simpa only [LinearMap.comp_sub] using h.comp_left u'
/-
**LinearMap.FiniteRangeSetoid.equiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.Fi
niteRangeSetoid`。
形式化陈述：equiv_comp {u v : V ->ₗ[K] V₂} {u' v' : V₂ ->ₗ[K] V₃} (h : u ≈ v) (h' : u'
 ≈ v') : u' ∘ₗ u ≈ v' ∘ₗ v
参数：h : u ≈ v；h' : u' ≈ v'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Quotient.instIsEquivEquiv`：∀ {α : Type u_4} [inst : Setoid α], IsEquiv α
 fun x1 x2 => x1 ≈ x2
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_comp_right`：equiv_comp_right {u : V ->
ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃} (h' : v ≈ v') : v ∘ₗ u ≈ v' ∘ₗ u
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_comp_left`：equiv_comp_left {u v : V ->
ₗ[K] V₂} {u' : V₂ ->ₗ[K] V₃} (h : u ≈ v) : u' ∘ₗ u ≈ u' ∘ₗ v
-/
lemma equiv_comp {u v : V →ₗ[K] V₂} {u' v' : V₂ →ₗ[K] V₃} (h : u ≈ v) (h' : u' ≈ v') :
    u' ∘ₗ u ≈ v' ∘ₗ v := by
  grw [equiv_comp_right h', equiv_comp_left h]
/-
**LinearMap.FiniteRangeSetoid.projection_equiv_zero_iff_isNoetherian** 是 Mathlib
 中的一个引理，位于命名空间 `LinearMap.FiniteRangeSetoid`。
形式化陈述：projection_equiv_zero_iff_isNoetherian {S T : Submodule K V} (hST : IsComp
l S T) : S.projection T hST ≈ 0 ↔ IsNoetherian K S
参数：hST : IsCompl S T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_zero_iff_hasNoetherianRange`：equiv_zer
o_iff_hasNoetherianRange {u : V ->ₗ[K] V₂} : u ≈ 0 ↔ u.HasNoetherianRange
· 使用引理 `LinearMap.hasNoetherianRange_iff_range`：hasNoetherianRange_iff_range {f 
: V ->ₗ[K] V₂} : f.HasNoetherianRange ↔ IsNoetherian K f.range
· 使用定理 `Submodule.range_projection`：range_projection (hpq : IsCompl p q) : range
 (p.projection q hpq) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma projection_equiv_zero_iff_isNoetherian {S T : Submodule K V} (hST : IsCompl S T) :
    S.projection T hST ≈ 0 ↔ IsNoetherian K S := by
  rw [equiv_zero_iff_hasNoetherianRange, hasNoetherianRange_iff_range, range_projection]
/-
**LinearMap.FiniteRangeSetoid.projection_equiv_zero** 是 Mathlib 中的一个引理，位于命名空间 `L
inearMap.FiniteRangeSetoid`。
形式化陈述：projection_equiv_zero {S T : Submodule K V} [IsNoetherian K S] (hST : IsCo
mpl S T) : S.projection T hST ≈ 0
参数：hST : IsCompl S T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.FiniteRangeSetoid.projection_equiv_zero_iff_isNoetherian`：proj
ection_equiv_zero_iff_isNoetherian {S T : Submodule K V} (hST : IsCompl S T) : S
.projection T hST ≈ 0 ↔ IsNoetherian K S
-/
lemma projection_equiv_zero {S T : Submodule K V} [IsNoetherian K S] (hST : IsCompl S T) :
    S.projection T hST ≈ 0 :=
  projection_equiv_zero_iff_isNoetherian hST |>.mpr inferInstance
/-
**LinearMap.FiniteRangeSetoid.projection_equiv_id_iff_isNoetherian** 是 Mathlib 中
的一个引理，位于命名空间 `LinearMap.FiniteRangeSetoid`。
形式化陈述：projection_equiv_id_iff_isNoetherian {S T : Submodule K V} (hST : IsCompl 
S T) : S.projection T hST ≈ id ↔ IsNoetherian K T
参数：hST : IsCompl S T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Setoid.comm`：comm [Setoid α] {x y : α} : x ≈ y ↔ y ≈ x
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange`：equiv_iff_hasN
oetherianRange {u v : V ->ₗ[K] V₂} : u ≈ v ↔ (u - v).HasNoetherianRange
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.projection_eq_id_sub_projection`：projection_eq_id_sub_projecti
on (hpq : IsCompl p q) : q.projection p hpq.symm = .id - p.projection q hpq
· 使用引理 `LinearMap.hasNoetherianRange_iff_range`：hasNoetherianRange_iff_range {f 
: V ->ₗ[K] V₂} : f.HasNoetherianRange ↔ IsNoetherian K f.range
· 使用定理 `Submodule.range_projection`：range_projection (hpq : IsCompl p q) : range
 (p.projection q hpq) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma projection_equiv_id_iff_isNoetherian {S T : Submodule K V} (hST : IsCompl S T) :
    S.projection T hST ≈ id ↔ IsNoetherian K T := by
  rw [Setoid.comm, equiv_iff_hasNoetherianRange, ← projection_eq_id_sub_projection,
    hasNoetherianRange_iff_range, range_projection]
/-
**LinearMap.FiniteRangeSetoid.projection_equiv_id** 是 Mathlib 中的一个引理，位于命名空间 `Lin
earMap.FiniteRangeSetoid`。
形式化陈述：projection_equiv_id {S T : Submodule K V} [IsNoetherian K T] (hST : IsComp
l S T) : S.projection T hST ≈ id
参数：hST : IsCompl S T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.FiniteRangeSetoid.projection_equiv_id_iff_isNoetherian`：projec
tion_equiv_id_iff_isNoetherian {S T : Submodule K V} (hST : IsCompl S T) : S.pro
jection T hST ≈ id ↔ IsNoetherian K T
-/
lemma projection_equiv_id {S T : Submodule K V} [IsNoetherian K T] (hST : IsCompl S T) :
    S.projection T hST ≈ id :=
  projection_equiv_id_iff_isNoetherian hST |>.mpr inferInstance

end FiniteRangeSetoid

end Setoid

section QuasiInverse

variable [CommRing K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

open scoped LinearMap.FiniteRangeSetoid

/-- `u` is a **left quasi-inverse** to `v` if `u ∘ₗ v ≈ id` modulo
linear maps with noetherian ranges. Recall that if the scalar ring is noetherian
(e.g a field), then "noetherian range" can be replaced by "finitely generated range". -/
/-
**LinearMap.IsLeftQuasiInverse** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsLeftQuasiInverse (u : V ->ₗ[K] V₂) (v : V₂ ->ₗ[K] V) : Prop
参数：u : V ->ₗ[K] V₂；v : V₂ ->ₗ[K] V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`u` is a **left quasi-inverse** to `v` if `u ∘ₗ v ≈ id` modulo
linear maps with noetherian ranges. Recall that if the scalar ring is noetherian
(e.g a field), then "noetherian range" can be replaced by "finitely generated ra
nge".
-/
def IsLeftQuasiInverse (u : V →ₗ[K] V₂) (v : V₂ →ₗ[K] V) : Prop :=
  u ∘ₗ v ≈ .id

/-- `u` is a **right quasi-inverse** to `v` if `v ∘ₗ u ≈ id` modulo
linear maps with noetherian ranges. Recall that if the scalar ring is noetherian
(e.g a field), then "noetherian range" can be replaced by "finitely generated range". -/
/-
**LinearMap.IsRightQuasiInverse** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsRightQuasiInverse (u : V₃ ->ₗ[K] V₂) (v : V₂ ->ₗ[K] V₃) : Prop
参数：u : V₃ ->ₗ[K] V₂；v : V₂ ->ₗ[K] V₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`u` is a **right quasi-inverse** to `v` if `v ∘ₗ u ≈ id` modulo
linear maps with noetherian ranges. Recall that if the scalar ring is noetherian
(e.g a field), then "noetherian range" can be replaced by "finitely generated ra
nge".
-/
def IsRightQuasiInverse (u : V₃ →ₗ[K] V₂) (v : V₂ →ₗ[K] V₃) : Prop :=
  v ∘ₗ u ≈ .id

/-- `u` is a **quasi-inverse** to `v` if `u ∘ₗ v ≈ id` and `v ∘ₗ u ≈ id` modulo
linear maps with noetherian ranges. Recall that if the scalar ring is noetherian
(e.g a field), then "noetherian range" can be replaced by "finitely generated range". -/
/-
**LinearMap.IsQuasiInverse** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsQuasiInverse (u : V₃ ->ₗ[K] V₂) (v : V₂ ->ₗ[K] V₃) : Prop
参数：u : V₃ ->ₗ[K] V₂；v : V₂ ->ₗ[K] V₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`u` is a **quasi-inverse** to `v` if `u ∘ₗ v ≈ id` and `v ∘ₗ u ≈ id` modulo
linear maps with noetherian ranges. Recall that if the scalar ring is noetherian
(e.g a field), then "noetherian range" can be replaced by "finitely generated ra
nge".
-/
def IsQuasiInverse (u : V₃ →ₗ[K] V₂) (v : V₂ →ₗ[K] V₃) : Prop :=
  u.IsLeftQuasiInverse v ∧ u.IsRightQuasiInverse v
/-
**LinearMap.isLeftQuasiInverse_iff_isRightQuasiInverse_swap** 是 Mathlib 中的一个引理，位
于命名空间 `LinearMap`。
形式化陈述：isLeftQuasiInverse_iff_isRightQuasiInverse_swap {u : V₃ ->ₗ[K] V₂} {v : V₂
 ->ₗ[K] V₃} : u.IsLeftQuasiInverse v ↔ v.IsRightQuasiInverse u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLeftQuasiInverse_iff_isRightQuasiInverse_swap {u : V₃ →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} :
    u.IsLeftQuasiInverse v ↔ v.IsRightQuasiInverse u := Iff.rfl

alias ⟨IsLeftQuasiInverse.isRightQuasiInverse, IsRightQuasiInverse.isLeftQuasiInverse⟩ :=
  isLeftQuasiInverse_iff_isRightQuasiInverse_swap
/-
**LinearMap.IsLeftQuasiInverse.equiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsLeft
QuasiInverse`。
形式化陈述：∀ {K : Type u_1} {V₂ : Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst
_1 : AddCommGroup V₂]   [inst_2 : _root_.Module K V₂] [inst_3 : AddCommGroup V₃]
 [inst_4 : _root_.Module K V₃] {u : V₃ →ₗ[K] V₂}   {v : V₂ →ₗ[K] V₃}, u.IsLeftQu
asiInverse v → u ∘ₗ v ≈ LinearMap.id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsLeftQuasiInverse.equiv {u : V₃ →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    (h : u.IsLeftQuasiInverse v) : u ∘ₗ v ≈ .id := h
/-
**LinearMap.IsRightQuasiInverse.equiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsRig
htQuasiInverse`。
形式化陈述：∀ {K : Type u_1} {V₂ : Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst
_1 : AddCommGroup V₂]   [inst_2 : _root_.Module K V₂] [inst_3 : AddCommGroup V₃]
 [inst_4 : _root_.Module K V₃] {u : V₃ →ₗ[K] V₂}   {v : V₂ →ₗ[K] V₃}, u.IsRightQ
uasiInverse v → v ∘ₗ u ≈ LinearMap.id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsRightQuasiInverse.equiv {u : V₃ →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    (h : u.IsRightQuasiInverse v) : v ∘ₗ u ≈ .id := h
/-
**LinearMap._root_.LinearEquiv.isQuasiInverse** 是 Mathlib 中的一个引理，位于命名空间 `LinearM
ap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearEquiv.isQuasiInverse (e : V ≃ₗ[K] V₂) :
    e.symm.IsQuasiInverse e := by
  simp [IsQuasiInverse, IsLeftQuasiInverse, IsRightQuasiInverse]

@[symm]
/-
**LinearMap.IsQuasiInverse.symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsQuasiInve
rse`。
形式化陈述：∀ {K : Type u_1} {V₂ : Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst
_1 : AddCommGroup V₂]   [inst_2 : _root_.Module K V₂] [inst_3 : AddCommGroup V₃]
 [inst_4 : _root_.Module K V₃] {u : V₃ →ₗ[K] V₂}   {v : V₂ →ₗ[K] V₃}, u.IsQuasiI
nverse v → v.IsQuasiInverse u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
-/
lemma IsQuasiInverse.symm {u : V₃ →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    (h : u.IsQuasiInverse v) : v.IsQuasiInverse u :=
  And.symm h

@[gcongr]
/-
**LinearMap.IsLeftQuasiInverse.congr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsLeft
QuasiInverse`。
形式化陈述：∀ {K : Type u_1} {V₂ : Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst
_1 : AddCommGroup V₂]   [inst_2 : _root_.Module K V₂] [inst_3 : AddCommGroup V₃]
 [inst_4 : _root_.Module K V₃] {u u' : V₃ →ₗ[K] V₂}   {v v' : V₂ →ₗ[K] V₃}, u.Is
LeftQuasiInverse v → u' ≈ u → v' ≈ v → u'.IsLeftQuasiInverse v'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Quotient.instIsEquivEquiv`：∀ {α : Type u_4} [inst : Setoid α], IsEquiv α
 fun x1 x2 => x1 ≈ x2
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_comp_right`：equiv_comp_right {u : V ->
ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃} (h' : v ≈ v') : v ∘ₗ u ≈ v' ∘ₗ u
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_comp_left`：equiv_comp_left {u v : V ->
ₗ[K] V₂} {u' : V₂ ->ₗ[K] V₃} (h : u ≈ v) : u' ∘ₗ u ≈ u' ∘ₗ v
-/
lemma IsLeftQuasiInverse.congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.IsLeftQuasiInverse v) (hu : u' ≈ u) (hv : v' ≈ v) :
    u'.IsLeftQuasiInverse v' := by
  unfold IsLeftQuasiInverse at *
  grw [hu, hv]
  assumption

@[gcongr]
/-
**LinearMap.isLeftQuasiInverse_congr** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：isLeftQuasiInverse_congr {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃} (hu :
 u' ≈ u) (hv : v' ≈ v) : u.IsLeftQuasiInverse v ↔ u'.IsLeftQuasiInverse v'
参数：hu : u' ≈ u；hv : v' ≈ v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsLeftQuasiInverse.congr`：∀ {K : Type u_1} {V₂ : Type u_4} {V₃
 : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [inst_2 : _root_.M
odule K V₂] [inst_3 : Ad…
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
-/
lemma isLeftQuasiInverse_congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (hu : u' ≈ u) (hv : v' ≈ v) :
    u.IsLeftQuasiInverse v ↔ u'.IsLeftQuasiInverse v' :=
  ⟨fun H ↦ H.congr hu hv, fun H ↦ H.congr (Setoid.symm hu) (Setoid.symm hv)⟩

@[gcongr]
/-
**LinearMap.IsRightQuasiInverse.congr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsRig
htQuasiInverse`。
形式化陈述：∀ {K : Type u_1} {V₂ : Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst
_1 : AddCommGroup V₂]   [inst_2 : _root_.Module K V₂] [inst_3 : AddCommGroup V₃]
 [inst_4 : _root_.Module K V₃] {u u' : V₃ →ₗ[K] V₂}   {v v' : V₂ →ₗ[K] V₃}, u.Is
RightQuasiInverse v → u' ≈ u → v' ≈ v → u'.IsRightQuasiInverse v'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsLeftQuasiInverse.isRightQuasiInverse`：∀ {K : Type u_1} {V₂ :
 Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [ins
t_2 : _root_.Module K V₂] [inst_3 : Ad…
· 使用定理 `LinearMap.IsLeftQuasiInverse.congr`：∀ {K : Type u_1} {V₂ : Type u_4} {V₃
 : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [inst_2 : _root_.M
odule K V₂] [inst_3 : Ad…
· 使用定理 `LinearMap.IsRightQuasiInverse.isLeftQuasiInverse`：∀ {K : Type u_1} {V₂ :
 Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [ins
t_2 : _root_.Module K V₂] [inst_3 : Ad…
-/
lemma IsRightQuasiInverse.congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.IsRightQuasiInverse v) (hu : u' ≈ u) (hv : v' ≈ v) :
    u'.IsRightQuasiInverse v' :=
  h.isLeftQuasiInverse.congr hv hu |>.isRightQuasiInverse
/-
**LinearMap.isRightQuasiInverse_congr** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：isRightQuasiInverse_congr {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃} (hu 
: u' ≈ u) (hv : v' ≈ v) : u.IsRightQuasiInverse v ↔ u'.IsRightQuasiInverse v'
参数：hu : u' ≈ u；hv : v' ≈ v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsRightQuasiInverse.congr`：∀ {K : Type u_1} {V₂ : Type u_4} {V
₃ : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [inst_2 : _root_.
Module K V₂] [inst_3 : Ad…
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
-/
lemma isRightQuasiInverse_congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (hu : u' ≈ u) (hv : v' ≈ v) :
    u.IsRightQuasiInverse v ↔ u'.IsRightQuasiInverse v' :=
  ⟨fun H ↦ H.congr hu hv, fun H ↦ H.congr (Setoid.symm hu) (Setoid.symm hv)⟩

@[gcongr]
/-
**LinearMap.IsQuasiInverse.congr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsQuasiInv
erse`。
形式化陈述：∀ {K : Type u_1} {V₂ : Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst
_1 : AddCommGroup V₂]   [inst_2 : _root_.Module K V₂] [inst_3 : AddCommGroup V₃]
 [inst_4 : _root_.Module K V₃] {u u' : V₃ →ₗ[K] V₂}   {v v' : V₂ →ₗ[K] V₃}, u.Is
QuasiInverse v → u' ≈ u → v' ≈ v → u'.IsQuasiInverse v'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsLeftQuasiInverse.congr`：∀ {K : Type u_1} {V₂ : Type u_4} {V₃
 : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [inst_2 : _root_.M
odule K V₂] [inst_3 : Ad…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LinearMap.IsRightQuasiInverse.congr`：∀ {K : Type u_1} {V₂ : Type u_4} {V
₃ : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [inst_2 : _root_.
Module K V₂] [inst_3 : Ad…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsQuasiInverse.congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.IsQuasiInverse v) (hu : u' ≈ u) (hv : v' ≈ v) :
    u'.IsQuasiInverse v' :=
  ⟨h.1.congr hu hv, h.2.congr hu hv⟩
/-
**LinearMap.isQuasiInverse_congr** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：isQuasiInverse_congr {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃} (hu : u' 
≈ u) (hv : v' ≈ v) : u.IsQuasiInverse v ↔ u'.IsQuasiInverse v'
参数：hu : u' ≈ u；hv : v' ≈ v。
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
· 使用引理 `LinearMap.isLeftQuasiInverse_congr`：isLeftQuasiInverse_congr {u u' : V₃ 
->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃} (hu : u' ≈ u) (hv : v' ≈ v) : u.IsLeftQuasiInve
rse v ↔ u'.IsLeftQuasiIn…
· 使用引理 `LinearMap.isRightQuasiInverse_congr`：isRightQuasiInverse_congr {u u' : V
₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃} (hu : u' ≈ u) (hv : v' ≈ v) : u.IsRightQuasiI
nverse v ↔ u'.IsRightQuas…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isQuasiInverse_congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (hu : u' ≈ u) (hv : v' ≈ v) :
    u.IsQuasiInverse v ↔ u'.IsQuasiInverse v' := by
  simp [IsQuasiInverse, isLeftQuasiInverse_congr hu hv, isRightQuasiInverse_congr hu hv]
/-
**LinearMap.IsQuasiInverse.equiv_of_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Is
QuasiInverse`。
形式化陈述：∀ {K : Type u_1} {V₂ : Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst
_1 : AddCommGroup V₂]   [inst_2 : _root_.Module K V₂] [inst_3 : AddCommGroup V₃]
 [inst_4 : _root_.Module K V₃] {u u' : V₃ →ₗ[K] V₂}   {v v' : V₂ →ₗ[K] V₃}, u.Is
QuasiInverse v → u'.IsQuasiInverse v' → u ≈ u' → v ≈ v'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Quotient.instIsEquivEquiv`：∀ {α : Type u_4} [inst : Setoid α], IsEquiv α
 fun x1 x2 => x1 ≈ x2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_comp_left`：equiv_comp_left {u v : V ->
ₗ[K] V₂} {u' : V₂ ->ₗ[K] V₃} (h : u ≈ v) : u' ∘ₗ u ≈ u' ∘ₗ v
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `LinearMap.IsLeftQuasiInverse.equiv`：∀ {K : Type u_1} {V₂ : Type u_4} {V₃
 : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [inst_2 : _root_.M
odule K V₂] [inst_3 : Ad…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_comp_right`：equiv_comp_right {u : V ->
ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃} (h' : v ≈ v') : v ∘ₗ u ≈ v' ∘ₗ u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearMap.IsRightQuasiInverse.equiv`：∀ {K : Type u_1} {V₂ : Type u_4} {V
₃ : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [inst_2 : _root_.
Module K V₂] [inst_3 : Ad…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsQuasiInverse.equiv_of_left {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.IsQuasiInverse v) (h' : u'.IsQuasiInverse v') (hu : u ≈ u') :
    v ≈ v' := by
  calc
    v = v ∘ₗ .id := by simp
    _ ≈ v ∘ₗ (u' ∘ₗ v') := by grw [h'.1.equiv]
    _ ≈ v ∘ₗ (u ∘ₗ v') := by grw [hu]
    _ = (v ∘ₗ u) ∘ₗ v' := by rw [comp_assoc]
    _ ≈ .id ∘ₗ v' := by grw [h.2.equiv]
    _ = v' := by simp
/-
**LinearMap.IsQuasiInverse.equiv_of_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.I
sQuasiInverse`。
形式化陈述：∀ {K : Type u_1} {V₂ : Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst
_1 : AddCommGroup V₂]   [inst_2 : _root_.Module K V₂] [inst_3 : AddCommGroup V₃]
 [inst_4 : _root_.Module K V₃] {u u' : V₃ →ₗ[K] V₂}   {v v' : V₂ →ₗ[K] V₃}, u.Is
QuasiInverse v → u'.IsQuasiInverse v' → v ≈ v' → u ≈ u'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsQuasiInverse.equiv_of_left`：∀ {K : Type u_1} {V₂ : Type u_4}
 {V₃ : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [inst_2 : _roo
t_.Module K V₂] [inst_3 : Ad…
· 使用定理 `LinearMap.IsQuasiInverse.symm`：∀ {K : Type u_1} {V₂ : Type u_4} {V₃ : Ty
pe u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [inst_2 : _root_.Module
 K V₂] [inst_3 : Ad…
-/
lemma IsQuasiInverse.equiv_of_right {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.IsQuasiInverse v) (h' : u'.IsQuasiInverse v') (hv : v ≈ v') :
    u ≈ u' :=
  h.symm.equiv_of_left h'.symm hv

/-- Left quasi-inverses compose in the opposite order. -/
/-
**LinearMap.IsLeftQuasiInverse.comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsLeftQ
uasiInverse`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} {V₃ : Type u_6} [inst : Co
mmRing K] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module K V] [inst_3 : Add
CommGroup V₂] [inst_4 : _root_.Module K V₂] [inst_5 : AddCommGroup V₃]   [inst_6
 : _root_.Module K V₃] {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} {u' : V₂ →ₗ[K] V} {v' 
: V₃ →ₗ[K] V₂},   u'.IsLeftQuasiInverse u → v'.IsLeftQuasiInverse v → (u' ∘ₗ v')
.IsLeftQuasiInverse (v ∘ₗ u)
参数：u' ∘ₗ v'；v ∘ₗ u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Quotient.instIsEquivEquiv`：∀ {α : Type u_4} [inst : Setoid α], IsEquiv α
 fun x1 x2 => x1 ≈ x2
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_comp_left`：equiv_comp_left {u v : V ->
ₗ[K] V₂} {u' : V₂ ->ₗ[K] V₃} (h : u ≈ v) : u' ∘ₗ u ≈ u' ∘ₗ v
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_comp_right`：equiv_comp_right {u : V ->
ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃} (h' : v ≈ v') : v ∘ₗ u ≈ v' ∘ₗ u
· 使用定理 `LinearMap.IsLeftQuasiInverse.equiv`：∀ {K : Type u_1} {V₂ : Type u_4} {V₃
 : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [inst_2 : _root_.M
odule K V₂] [inst_3 : Ad…
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a

--- 原说明 ---
Left quasi-inverses compose in the opposite order.
-/
lemma IsLeftQuasiInverse.comp {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} {u' : V₂ →ₗ[K] V}
    {v' : V₃ →ₗ[K] V₂} (hu : u'.IsLeftQuasiInverse u) (hv : v'.IsLeftQuasiInverse v) :
    (u' ∘ₗ v').IsLeftQuasiInverse (v ∘ₗ u) :=
  calc
    _ = u' ∘ₗ (v' ∘ₗ v) ∘ₗ u := rfl
    _ ≈ u' ∘ₗ .id ∘ₗ u := by grw [hv.equiv]
    _ ≈ .id := hu.equiv

/-- Right quasi-inverses compose in the opposite order. -/
/-
**LinearMap.IsRightQuasiInverse.comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsRigh
tQuasiInverse`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} {V₃ : Type u_6} [inst : Co
mmRing K] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module K V] [inst_3 : Add
CommGroup V₂] [inst_4 : _root_.Module K V₂] [inst_5 : AddCommGroup V₃]   [inst_6
 : _root_.Module K V₃] {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} {u' : V₂ →ₗ[K] V} {v' 
: V₃ →ₗ[K] V₂},   u'.IsRightQuasiInverse u → v'.IsRightQuasiInverse v → (u' ∘ₗ v
').IsRightQuasiInverse (v ∘ₗ u)
参数：u' ∘ₗ v'；v ∘ₗ u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsLeftQuasiInverse.isRightQuasiInverse`：∀ {K : Type u_1} {V₂ :
 Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [ins
t_2 : _root_.Module K V₂] [inst_3 : Ad…
· 使用定理 `LinearMap.IsLeftQuasiInverse.comp`：∀ {K : Type u_1} {V : Type u_2} {V₂ :
 Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V]   [inst
_2 : _root_.Module K V]…
· 使用定理 `LinearMap.IsRightQuasiInverse.isLeftQuasiInverse`：∀ {K : Type u_1} {V₂ :
 Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [ins
t_2 : _root_.Module K V₂] [inst_3 : Ad…

--- 原说明 ---
Right quasi-inverses compose in the opposite order.
-/
lemma IsRightQuasiInverse.comp {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} {u' : V₂ →ₗ[K] V}
    {v' : V₃ →ₗ[K] V₂} (hu : u'.IsRightQuasiInverse u) (hv : v'.IsRightQuasiInverse v) :
    (u' ∘ₗ v').IsRightQuasiInverse (v ∘ₗ u) :=
  hv.isLeftQuasiInverse.comp hu.isLeftQuasiInverse |>.isRightQuasiInverse

/-- Quasi-inverses compose in the opposite order. -/
/-
**LinearMap.IsQuasiInverse.comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsQuasiInve
rse`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} {V₃ : Type u_6} [inst : Co
mmRing K] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module K V] [inst_3 : Add
CommGroup V₂] [inst_4 : _root_.Module K V₂] [inst_5 : AddCommGroup V₃]   [inst_6
 : _root_.Module K V₃] {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} {u' : V₂ →ₗ[K] V} {v' 
: V₃ →ₗ[K] V₂},   u'.IsQuasiInverse u → v'.IsQuasiInverse v → (u' ∘ₗ v').IsQuasi
Inverse (v ∘ₗ u)
参数：u' ∘ₗ v'；v ∘ₗ u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsLeftQuasiInverse.comp`：∀ {K : Type u_1} {V : Type u_2} {V₂ :
 Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V]   [inst
_2 : _root_.Module K V]…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LinearMap.IsRightQuasiInverse.comp`：∀ {K : Type u_1} {V : Type u_2} {V₂ 
: Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V]   [ins
t_2 : _root_.Module K V]…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Quasi-inverses compose in the opposite order.
-/
lemma IsQuasiInverse.comp {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} {u' : V₂ →ₗ[K] V}
    {v' : V₃ →ₗ[K] V₂} (hu : u'.IsQuasiInverse u) (hv : v'.IsQuasiInverse v) :
    (u' ∘ₗ v').IsQuasiInverse (v ∘ₗ u) :=
  ⟨hu.1.comp hv.1, hu.2.comp hv.2⟩

/-- If `u'` is a right quasi-inverse of `u` and `w` is a left quasi-inverse of `v ∘ₗ u`,
then `u ∘ₗ w` is a left quasi-inverse of `v`. -/
/-
**LinearMap.IsLeftQuasiInverse.of_comp_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
.IsLeftQuasiInverse`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} {V₃ : Type u_6} [inst : Co
mmRing K] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module K V] [inst_3 : Add
CommGroup V₂] [inst_4 : _root_.Module K V₂] [inst_5 : AddCommGroup V₃]   [inst_6
 : _root_.Module K V₃] {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} {u' : V₂ →ₗ[K] V} {w :
 V₃ →ₗ[K] V},   u'.IsRightQuasiInverse u → w.IsLeftQuasiInverse (v ∘ₗ u) → (u ∘ₗ
 w).IsLeftQuasiInverse v
参数：v ∘ₗ u；u ∘ₗ w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Quotient.instIsEquivEquiv`：∀ {α : Type u_4} [inst : Setoid α], IsEquiv α
 fun x1 x2 => x1 ≈ x2
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_comp_left`：equiv_comp_left {u v : V ->
ₗ[K] V₂} {u' : V₂ ->ₗ[K] V₃} (h : u ≈ v) : u' ∘ₗ u ≈ u' ∘ₗ v
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `LinearMap.IsRightQuasiInverse.equiv`：∀ {K : Type u_1} {V₂ : Type u_4} {V
₃ : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [inst_2 : _root_.
Module K V₂] [inst_3 : Ad…
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_comp_right`：equiv_comp_right {u : V ->
ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃} (h' : v ≈ v') : v ∘ₗ u ≈ v' ∘ₗ u
· 使用定理 `LinearMap.IsLeftQuasiInverse.equiv`：∀ {K : Type u_1} {V₂ : Type u_4} {V₃
 : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [inst_2 : _root_.M
odule K V₂] [inst_3 : Ad…

--- 原说明 ---
If `u'` is a right quasi-inverse of `u` and `w` is a left quasi-inverse of `v ∘ₗ
 u`,
then `u ∘ₗ w` is a left quasi-inverse of `v`.
-/
lemma IsLeftQuasiInverse.of_comp_left {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {u' : V₂ →ₗ[K] V} {w : V₃ →ₗ[K] V} (hu : u'.IsRightQuasiInverse u)
    (hw : w.IsLeftQuasiInverse (v ∘ₗ u)) :
    (u ∘ₗ w).IsLeftQuasiInverse v := by
  calc
    _ = ((u ∘ₗ w) ∘ₗ v) ∘ₗ .id := rfl
    _ ≈ ((u ∘ₗ w) ∘ₗ v) ∘ₗ (u ∘ₗ u') := by grw [hu.equiv]
    _ = u ∘ₗ (w ∘ₗ (v ∘ₗ u)) ∘ₗ u' := rfl
    _ ≈ u ∘ₗ .id ∘ₗ u' := by grw [hw.equiv]
    _ ≈ .id := hu.equiv

/-- If `u'` is a quasi-inverse of `u` and `w` is a quasi-inverse of `v ∘ₗ u`, then
`u ∘ₗ w` is a quasi-inverse of `v`. -/
/-
**LinearMap.IsQuasiInverse.of_comp_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsQ
uasiInverse`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} {V₃ : Type u_6} [inst : Co
mmRing K] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module K V] [inst_3 : Add
CommGroup V₂] [inst_4 : _root_.Module K V₂] [inst_5 : AddCommGroup V₃]   [inst_6
 : _root_.Module K V₃] {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} {u' : V₂ →ₗ[K] V} {w :
 V₃ →ₗ[K] V},   u'.IsQuasiInverse u → w.IsQuasiInverse (v ∘ₗ u) → (u ∘ₗ w).IsQua
siInverse v
参数：v ∘ₗ u；u ∘ₗ w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsLeftQuasiInverse.of_comp_left`：∀ {K : Type u_1} {V : Type u_
2} {V₂ : Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V]
   [inst_2 : _root_.Module K V]…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If `u'` is a quasi-inverse of `u` and `w` is a quasi-inverse of `v ∘ₗ u`, then
`u ∘ₗ w` is a quasi-inverse of `v`.
-/
lemma IsQuasiInverse.of_comp_left {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {u' : V₂ →ₗ[K] V} {w : V₃ →ₗ[K] V} (hu : u'.IsQuasiInverse u)
    (hw : w.IsQuasiInverse (v ∘ₗ u)) :
    (u ∘ₗ w).IsQuasiInverse v :=
  ⟨.of_comp_left hu.2 hw.1, hw.2⟩

/-- If `v'` is a left quasi-inverse of `v` and `w` is a right quasi-inverse of `v ∘ₗ u`,
then `w ∘ₗ v` is a right quasi-inverse of `u`. -/
/-
**LinearMap.IsRightQuasiInverse.of_comp_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap.IsRightQuasiInverse`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} {V₃ : Type u_6} [inst : Co
mmRing K] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module K V] [inst_3 : Add
CommGroup V₂] [inst_4 : _root_.Module K V₂] [inst_5 : AddCommGroup V₃]   [inst_6
 : _root_.Module K V₃] {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} {v' : V₃ →ₗ[K] V₂} {w 
: V₃ →ₗ[K] V},   v'.IsLeftQuasiInverse v → w.IsRightQuasiInverse (v ∘ₗ u) → (w ∘
ₗ v).IsRightQuasiInverse u
参数：v ∘ₗ u；w ∘ₗ v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Quotient.instIsEquivEquiv`：∀ {α : Type u_4} [inst : Setoid α], IsEquiv α
 fun x1 x2 => x1 ≈ x2
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_comp_right`：equiv_comp_right {u : V ->
ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃} (h' : v ≈ v') : v ∘ₗ u ≈ v' ∘ₗ u
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `LinearMap.IsLeftQuasiInverse.equiv`：∀ {K : Type u_1} {V₂ : Type u_4} {V₃
 : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [inst_2 : _root_.M
odule K V₂] [inst_3 : Ad…
· 使用引理 `LinearMap.FiniteRangeSetoid.equiv_comp_left`：equiv_comp_left {u v : V ->
ₗ[K] V₂} {u' : V₂ ->ₗ[K] V₃} (h : u ≈ v) : u' ∘ₗ u ≈ u' ∘ₗ v
· 使用定理 `LinearMap.IsRightQuasiInverse.equiv`：∀ {K : Type u_1} {V₂ : Type u_4} {V
₃ : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [inst_2 : _root_.
Module K V₂] [inst_3 : Ad…

--- 原说明 ---
If `v'` is a left quasi-inverse of `v` and `w` is a right quasi-inverse of `v ∘ₗ
 u`,
then `w ∘ₗ v` is a right quasi-inverse of `u`.
-/
lemma IsRightQuasiInverse.of_comp_right {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {v' : V₃ →ₗ[K] V₂} {w : V₃ →ₗ[K] V} (hv : v'.IsLeftQuasiInverse v)
    (hw : w.IsRightQuasiInverse (v ∘ₗ u)) :
    (w ∘ₗ v).IsRightQuasiInverse u := by
  calc
    _ = .id ∘ₗ (u ∘ₗ (w ∘ₗ v)) := rfl
    _ ≈ (v' ∘ₗ v) ∘ₗ (u ∘ₗ (w ∘ₗ v)) := by grw [hv.equiv]
    _ = v' ∘ₗ ((v ∘ₗ u) ∘ₗ w) ∘ₗ v := rfl
    _ ≈ v' ∘ₗ .id ∘ₗ v := by grw [hw.equiv]
    _ ≈ .id := hv.equiv

/-- If `v'` is a quasi-inverse of `v` and `w` is a quasi-inverse of `v ∘ₗ u`, then
`w ∘ₗ v` is a quasi-inverse of `u`. -/
/-
**LinearMap.IsQuasiInverse.of_comp_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Is
QuasiInverse`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} {V₂ : Type u_4} {V₃ : Type u_6} [inst : Co
mmRing K] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module K V] [inst_3 : Add
CommGroup V₂] [inst_4 : _root_.Module K V₂] [inst_5 : AddCommGroup V₃]   [inst_6
 : _root_.Module K V₃] {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} {v' : V₃ →ₗ[K] V₂} {w 
: V₃ →ₗ[K] V},   v'.IsQuasiInverse v → w.IsQuasiInverse (v ∘ₗ u) → (w ∘ₗ v).IsQu
asiInverse u
参数：v ∘ₗ u；w ∘ₗ v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LinearMap.IsRightQuasiInverse.of_comp_right`：∀ {K : Type u_1} {V : Type 
u_2} {V₂ : Type u_4} {V₃ : Type u_6} [inst : CommRing K] [inst_1 : AddCommGroup 
V]   [inst_2 : _root_.Module K V]…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `v'` is a quasi-inverse of `v` and `w` is a quasi-inverse of `v ∘ₗ u`, then
`w ∘ₗ v` is a quasi-inverse of `u`.
-/
lemma IsQuasiInverse.of_comp_right {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {v' : V₃ →ₗ[K] V₂} {w : V₃ →ₗ[K] V} (hv : v'.IsQuasiInverse v)
    (hw : w.IsQuasiInverse (v ∘ₗ u)) :
    (w ∘ₗ v).IsQuasiInverse u :=
  ⟨hw.1, IsRightQuasiInverse.of_comp_right hv.1 hw.2⟩
/-
**LinearMap.isQuasiInverse_subtype_projectionOnto_iff** 是 Mathlib 中的一个引理，位于命名空间 
`LinearMap`。
形式化陈述：isQuasiInverse_subtype_projectionOnto_iff {S T : Submodule K V} (hST : IsC
ompl S T) : IsQuasiInverse S.subtype (S.projectionOnto T hST) ↔ IsNoetherian K T
参数：hST : IsCompl S T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsQuasiInverse.eq_1`：∀ {K : Type u_1} {V₂ : Type u_4} {V₃ : Ty
pe u_6} [inst : CommRing K] [inst_1 : AddCommGroup V₂]   [inst_2 : _root_.Module
 K V₂] [inst_3 : Ad…
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.projectionOnto_comp_subtype`：projectionOnto_comp_subtype (h : 
IsCompl p q) : (projectionOnto p q h).comp p.subtype = LinearMap.id
· 使用定理 `LinearMap.IsLeftQuasiInverse.eq_1`：∀ {K : Type u_1} {V : Type u_2} {V₂ :
 Type u_4} [inst : CommRing K] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Modu
le K V] [inst_3 : AddCo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.projection.eq_1`：∀ {R : Type u_1} [inst : Ring R] {E : Type u_
2} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   (p q : Submodule R E
) (hpq : IsComp…
· 使用引理 `LinearMap.FiniteRangeSetoid.projection_equiv_id_iff_isNoetherian`：projec
tion_equiv_id_iff_isNoetherian {S T : Submodule K V} (hST : IsCompl S T) : S.pro
jection T hST ≈ id ↔ IsNoetherian K T
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isQuasiInverse_subtype_projectionOnto_iff {S T : Submodule K V} (hST : IsCompl S T) :
    IsQuasiInverse S.subtype (S.projectionOnto T hST) ↔ IsNoetherian K T := by
  rw [IsQuasiInverse, and_iff_left (by simp [IsRightQuasiInverse, projectionOnto_comp_subtype]),
    IsLeftQuasiInverse, ← projection,
    FiniteRangeSetoid.projection_equiv_id_iff_isNoetherian hST]
/-
**LinearMap.isQuasiInverse_subtype_projectionOnto** 是 Mathlib 中的一个引理，位于命名空间 `Lin
earMap`。
形式化陈述：isQuasiInverse_subtype_projectionOnto {S T : Submodule K V} [IsNoetherian 
K T] (hST : IsCompl S T) : IsQuasiInverse S.subtype (S.projectionOnto T hST)
参数：hST : IsCompl S T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.isQuasiInverse_subtype_projectionOnto_iff`：isQuasiInverse_subt
ype_projectionOnto_iff {S T : Submodule K V} (hST : IsCompl S T) : IsQuasiInvers
e S.subtype (S.projectionOnto T hST) ↔ Is…
-/
lemma isQuasiInverse_subtype_projectionOnto {S T : Submodule K V} [IsNoetherian K T]
    (hST : IsCompl S T) :
    IsQuasiInverse S.subtype (S.projectionOnto T hST) :=
  isQuasiInverse_subtype_projectionOnto_iff hST |>.mpr inferInstance

end QuasiInverse

end LinearMap

