/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Evaluation of power series

Power series in one indeterminate are the particular case of multivariate power series,
for the `Unit` type of indeterminates.
This file provides a simpler syntax.

Let `R`, `S` be types, with `CommRing R`, `CommRing S`.
One assumes that `IsTopologicalRing R` and `IsUniformAddGroup R`,
and that `S` is a complete and separated topological `R`-algebra,
with `IsLinearTopology S S`, which means there is a basis of neighborhoods of 0
consisting of ideals.

Given `φ : R →+* S`, `a : S`, and `f : MvPowerSeries σ R`,
`PowerSeries.eval₂ f φ a` is the evaluation of the power series `f` at `a`.
It `f` is (the coercion of) a polynomial, it coincides with the evaluation of that polynomial.
Otherwise, it is defined by density from polynomials;
its values are irrelevant unless `φ` is continuous and `a` is topologically
nilpotent (`a ^ n` tends to 0 when `n` tends to infinity).

For consistency with the case of multivariate power series,
we define `PowerSeries.HasEval` as an abbrev to `IsTopologicallyNilpotent`.

Under `Continuous φ` and `HasEval a`,
the following lemmas furnish the properties of evaluation:

* `PowerSeries.eval₂Hom`: the evaluation of multivariate power series, as a ring morphism,
* `PowerSeries.aeval`: the evaluation map as an algebra morphism
* `PowerSeries.uniformContinuous_eval₂`: uniform continuity of the evaluation
* `PowerSeries.continuous_eval₂`: continuity of the evaluation
* `PowerSeries.eval₂_eq_tsum`: the evaluation is given by the sum of its monomials, evaluated.

We refer to the documentation of `MvPowerSeries.eval₂` for more details.

-/

@[expose] public section
namespace PowerSeries

open WithPiTopology

variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S]
variable {φ : R →+* S}

section

variable [TopologicalSpace R] [TopologicalSpace S]

/-- Points at which evaluation of power series is well behaved -/
/-
**PowerSeries.HasEval** 是 Mathlib 中的一个缩写定义，位于命名空间 `PowerSeries`。
形式化陈述：HasEval (a : S)
参数：a : S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Points at which evaluation of power series is well behaved
-/
abbrev HasEval (a : S) := IsTopologicallyNilpotent a
/-
**PowerSeries.hasEval_def** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：hasEval_def (a : S) : HasEval a ↔ IsTopologicallyNilpotent a
参数：a : S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasEval_def (a : S) : HasEval a ↔ IsTopologicallyNilpotent a := .rfl
/-
**PowerSeries.hasEval_iff** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：hasEval_iff {a : S} : HasEval a ↔ MvPowerSeries.HasEval (fun (_ : Unit) =>
 a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.cofinite_eq_bot`：cofinite_eq_bot [Finite α] : @cofinite α = ⊥
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MvPowerSeries.HasEval.hpow`：∀ {σ : Type u_1} {S : Type u_3} [inst : Comm
Ring S] [inst_1 : TopologicalSpace S] {a : σ → S},   MvPowerSeries.HasEval a → ∀
 (s : σ), IsTopo…
-/
theorem hasEval_iff {a : S} :
    HasEval a ↔ MvPowerSeries.HasEval (fun (_ : Unit) ↦ a) :=
  ⟨fun ha ↦ ⟨fun _ ↦ ha, by simp⟩, fun ha ↦ ha.hpow default⟩
/-
**PowerSeries.hasEval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：hasEval {a : S} (ha : HasEval a) : MvPowerSeries.HasEval (fun (_ : Unit) =
> a)
参数：ha : HasEval a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PowerSeries.hasEval_iff`：hasEval_iff {a : S} : HasEval a ↔ MvPowerSeries
.HasEval (fun (_ : Unit) => a)
-/
theorem hasEval {a : S} (ha : HasEval a) :
    MvPowerSeries.HasEval (fun (_ : Unit) ↦ a) := hasEval_iff.mp ha
/-
**PowerSeries.HasEval.mono** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasEval`。
形式化陈述：∀ {S : Type u_3} [inst : CommRing S] {a : S} {t u : TopologicalSpace S},  
 t ≤ u → PowerSeries.HasEval a → PowerSeries.HasEval a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasEval.mono`：∀ {σ : Type u_1} {S : Type u_4} [inst : Comm
Ring S] {a : σ → S} {t u : TopologicalSpace S},   t ≤ u → MvPowerSeries.HasEval 
a → MvPowerSerie…
-/
theorem HasEval.mono {S : Type*} [CommRing S] {a : S}
    {t u : TopologicalSpace S} (h : t ≤ u) (ha : @HasEval _ _ t a) :
    @HasEval _ _ u a := by
  simp only [hasEval_iff] at ha ⊢
  exact ha.mono h
/-
**PowerSeries.HasEval.zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasEval`。
形式化陈述：∀ {S : Type u_2} [inst : CommRing S] [inst_1 : TopologicalSpace S], PowerS
eries.HasEval 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.hasEval_iff`：hasEval_iff {a : S} : HasEval a ↔ MvPowerSeries
.HasEval (fun (_ : Unit) => a)
· 使用定理 `MvPowerSeries.HasEval.zero`：∀ {σ : Type u_1} {S : Type u_3} [inst : Comm
Ring S] [inst_1 : TopologicalSpace S], MvPowerSeries.HasEval 0
-/
theorem HasEval.zero : HasEval (0 : S) := by
    rw [hasEval_iff]; exact MvPowerSeries.HasEval.zero
/-
**PowerSeries.HasEval.add** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasEval`。
形式化陈述：∀ {S : Type u_2} [inst : CommRing S] [inst_1 : TopologicalSpace S] [Contin
uousAdd S] [IsLinearTopology S S] {a b : S},   PowerSeries.HasEval a → PowerSeri
es.HasEval b → PowerSeries.HasEval (a + b)
参数：a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasEval.add`：∀ {σ : Type u_1} {S : Type u_3} [inst : CommR
ing S] [inst_1 : TopologicalSpace S] [ContinuousAdd S]   [IsLinearTopology S S] 
{a b : σ → S}, …
-/
theorem HasEval.add [ContinuousAdd S] [IsLinearTopology S S]
    {a b : S} (ha : HasEval a) (hb : HasEval b) : HasEval (a + b) := by
  simp only [hasEval_iff] at ha hb ⊢
  exact ha.add hb
/-
**PowerSeries.HasEval.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasEval`。
形式化陈述：∀ {S : Type u_2} [inst : CommRing S] [inst_1 : TopologicalSpace S] [IsLine
arTopology S S] (c : S) {x : S},   PowerSeries.HasEval x → PowerSeries.HasEval (
c * x)
参数：c : S；c * x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasEval.mul_left`：∀ {σ : Type u_1} {S : Type u_3} [inst : 
CommRing S] [inst_1 : TopologicalSpace S] [IsLinearTopology S S] (c : σ → S)   {
x : σ → S}, MvPowerS…
-/
theorem HasEval.mul_left [IsLinearTopology S S]
    (c : S) {x : S} (hx : HasEval x) : HasEval (c * x) := by
  simp only [hasEval_iff] at hx ⊢
  exact hx.mul_left _
/-
**PowerSeries.HasEval.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasEval`。
形式化陈述：∀ {S : Type u_2} [inst : CommRing S] [inst_1 : TopologicalSpace S] [IsLine
arTopology S S] (c : S) {x : S},   PowerSeries.HasEval x → PowerSeries.HasEval (
x * c)
参数：c : S；x * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasEval.mul_right`：∀ {σ : Type u_1} {S : Type u_3} [inst :
 CommRing S] [inst_1 : TopologicalSpace S] [IsLinearTopology S S] (c : σ → S)   
{x : σ → S}, MvPowerS…
-/
theorem HasEval.mul_right [IsLinearTopology S S]
    (c : S) {x : S} (hx : HasEval x) : HasEval (x * c) := by
  simp only [hasEval_iff] at hx ⊢
  exact hx.mul_right _

/-- [Bourbaki, *Algebra*, chap. 4, §4, n°3, Prop. 4 (i) (a & b)][bourbaki1981]. -/
/-
**PowerSeries.HasEval.map** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasEval`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] 
{φ : R →+* S} [inst_2 : TopologicalSpace R]   [inst_3 : TopologicalSpace S], Con
tinuous ⇑φ → ∀ {a : R}, PowerSeries.HasEval a → PowerSeries.HasEval (φ a)
参数：φ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasEval.map`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommR
ing R] [inst_1 : TopologicalSpace R] {S : Type u_3} [inst_2 : CommRing S]   [ins
t_3 : Topologic…

--- 原说明 ---
[Bourbaki, *Algebra*, chap. 4, §4, n°3, Prop. 4 (i) (a & b)][bourbaki1981].
-/
theorem HasEval.map (hφ : Continuous φ) {a : R} (ha : HasEval a) :
    HasEval (φ a) := by
  simp only [hasEval_iff] at ha ⊢
  exact ha.map hφ
/-
**PowerSeries.HasEval.X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasEval`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : TopologicalSpace R], PowerS
eries.HasEval PowerSeries.X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.hasEval_iff`：hasEval_iff {a : S} : HasEval a ↔ MvPowerSeries
.HasEval (fun (_ : Unit) => a)
· 使用定理 `MvPowerSeries.HasEval.X`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommRin
g R] [inst_1 : TopologicalSpace R],   MvPowerSeries.HasEval fun s => MvPowerSeri
es.X s
-/
protected theorem HasEval.X :
    HasEval (X : R⟦X⟧) := by
  rw [hasEval_iff]
  exact MvPowerSeries.HasEval.X


variable [IsTopologicalRing S] [IsLinearTopology S S]

/-- The domain of evaluation of `MvPowerSeries`, as an ideal -/
@[simps]
/-
**PowerSeries.hasEvalIdeal** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：hasEvalIdeal : Ideal S where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasEval.zero`：∀ {S : Type u_2} [inst : CommRing S] [inst_1 :
 TopologicalSpace S], PowerSeries.HasEval 0
· 使用定理 `PowerSeries.HasEval.mul_left`：∀ {S : Type u_2} [inst : CommRing S] [inst
_1 : TopologicalSpace S] [IsLinearTopology S S] (c : S) {x : S},   PowerSeries.H
asEval x → PowerSe…

--- 原说明 ---
The domain of evaluation of `MvPowerSeries`, as an ideal
-/
def hasEvalIdeal : Ideal S where
  carrier := {a | HasEval a}
  add_mem' := HasEval.add
  zero_mem' := HasEval.zero
  smul_mem' := HasEval.mul_left

set_option backward.isDefEq.respectTransparency false in
/-
**PowerSeries.mem_hasEvalIdeal_iff** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：mem_hasEvalIdeal_iff {a : S} : a in hasEvalIdeal ↔ HasEval a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.HasEval.zero`：∀ {S : Type u_2} [inst : CommRing S] [inst_1 :
 TopologicalSpace S], PowerSeries.HasEval 0
· 使用定理 `PowerSeries.HasEval.mul_left`：∀ {S : Type u_2} [inst : CommRing S] [inst
_1 : TopologicalSpace S] [IsLinearTopology S S] (c : S) {x : S},   PowerSeries.H
asEval x → PowerSe…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_hasEvalIdeal_iff {a : S} :
    a ∈ hasEvalIdeal ↔ HasEval a := by
  simp [hasEvalIdeal]

end

variable (φ : R →+* S) (a : S)

variable [UniformSpace R] [UniformSpace S]

/-- Evaluation of a power series `f` at a point `a`.

It coincides with the evaluation of `f` as a polynomial if `f` is the coercion of a polynomial.
Otherwise, it is only relevant if `φ` is continuous and `a` is topologically nilpotent. -/
/-
**PowerSeries.eval** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation of a power series `f` at a point `a`.

It coincides with the evaluation of `f` as a polynomial if `f` is the coercion o
f a polynomial.
Otherwise, it is only relevant if `φ` is continuous and `a` is topologically nil
potent.
-/
noncomputable def eval₂ : PowerSeries R → S :=
  MvPowerSeries.eval₂ φ (fun _ ↦ a)

@[simp]
/-
**PowerSeries.eval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_coe (f : Polynomial R) : eval₂ φ a f = f.eval₂ φ a := by
  rw [← (MvPolynomial.uniqueAlgEquiv R Unit).apply_symm_apply f]
  simp only [PowerSeries.eval₂, MvPolynomial.eval₂_const_uniqueAlgEquiv]
  rw [← MvPolynomial.toMvPowerSeries_pUnitAlgEquiv, MvPowerSeries.eval₂_coe]

@[simp]
/-
**PowerSeries.eval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_C (r : R) :
    eval₂ φ a (C r) = φ r := by
  rw [← Polynomial.coe_C, eval₂_coe, Polynomial.eval₂_C]

@[simp]
/-
**PowerSeries.eval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_X :
    eval₂ φ a X = a := by
  rw [← Polynomial.coe_X, eval₂_coe, Polynomial.eval₂_X]

variable {φ a}

variable [IsUniformAddGroup R] [IsTopologicalSemiring R]
    [IsUniformAddGroup S] [T2Space S] [CompleteSpace S]
    [IsTopologicalRing S] [IsLinearTopology S S]

/-- The evaluation homomorphism at `a` on `PowerSeries`, as a `RingHom`. -/
/-
**PowerSeries.eval** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evaluation homomorphism at `a` on `PowerSeries`, as a `RingHom`.
-/
noncomputable def eval₂Hom (hφ : Continuous φ) (ha : HasEval a) :
    PowerSeries R →+* S :=
  MvPowerSeries.eval₂Hom hφ (hasEval ha)
/-
**PowerSeries.coe_eval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_eval₂Hom (hφ : Continuous φ) (ha : HasEval a) :
    ⇑(eval₂Hom hφ ha) = eval₂ φ a :=
  MvPowerSeries.coe_eval₂Hom hφ (hasEval ha)

-- Note: this is still true without the `T2Space` hypothesis, by arguing that the case
-- disjunction in the definition of `eval₂` only replaces some values by topologically
-- inseparable ones.
/-
**PowerSeries.uniformContinuous_eval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformContinuous_eval₂ (hφ : Continuous φ) (ha : HasEval a) :
    UniformContinuous (eval₂ φ a) :=
  MvPowerSeries.uniformContinuous_eval₂ hφ (hasEval ha)
/-
**PowerSeries.continuous_eval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem continuous_eval₂ (hφ : Continuous φ) (ha : HasEval a) :
    Continuous (eval₂ φ a : PowerSeries R → S) :=
  (uniformContinuous_eval₂ hφ ha).continuous
/-
**PowerSeries.hasSum_eval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hasSum_eval₂ (hφ : Continuous φ) (ha : HasEval a) (f : PowerSeries R) :
    HasSum (fun (d : ℕ) ↦ φ (coeff d f) * a ^ d) (f.eval₂ φ a) := by
  have := MvPowerSeries.hasSum_eval₂ hφ (hasEval ha) f
  simp only [PowerSeries.eval₂]
  rw [← (Finsupp.single_injective ()).hasSum_iff] at this
  · convert this; simp
  · intro d hd
    exact False.elim (hd ⟨d (), by ext; simp⟩)
/-
**PowerSeries.eval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_eq_tsum (hφ : Continuous φ) (ha : HasEval a) (f : PowerSeries R) :
    PowerSeries.eval₂ φ a f =
      ∑' d : ℕ, φ (coeff d f) * a ^ d :=
  (hasSum_eval₂ hφ ha f).tsum_eq.symm
/-
**PowerSeries.eval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_unique (hφ : Continuous φ) (ha : HasEval a)
    {ε : PowerSeries R → S} (hε : Continuous ε)
    (h : ∀ p : Polynomial R, ε p = Polynomial.eval₂ φ a p) :
    ε = eval₂ φ a := by
  refine MvPowerSeries.eval₂_unique hφ (hasEval ha) hε (fun p ↦ ?_)
  rw [MvPolynomial.toMvPowerSeries_pUnitAlgEquiv, h, ← MvPolynomial.eval₂_uniqueAlgEquiv]
/-
**PowerSeries.comp_eval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_eval₂ (hφ : Continuous φ) (ha : HasEval a)
    {T : Type*} [UniformSpace T] [CompleteSpace T] [T2Space T]
    [CommRing T] [IsTopologicalRing T] [IsLinearTopology T T] [IsUniformAddGroup T]
    {ε : S →+* T} (hε : Continuous ε) :
    ε ∘ eval₂ φ a = eval₂ (ε.comp φ) (ε a) := by
  refine eval₂_unique (by simp only [RingHom.coe_comp, hε.comp hφ]) (ha.map hε)
    (hε.comp (continuous_eval₂ hφ ha)) (fun p ↦ ?_)
  simpa [Function.comp_apply, eval₂_coe] using p.hom_eval₂ φ ε a

variable [Algebra R S] [ContinuousSMul R S]

/-- For `HasEval a`,
the evaluation homomorphism at `a` on `PowerSeries`, as an `AlgHom`. -/
/-
**PowerSeries.aeval** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：aeval (ha : HasEval a) : PowerSeries R ->ₐ[R] S
参数：ha : HasEval a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `HasEval a`,
the evaluation homomorphism at `a` on `PowerSeries`, as an `AlgHom`.
-/
noncomputable def aeval (ha : HasEval a) :
    PowerSeries R →ₐ[R] S :=
  MvPowerSeries.aeval (hasEval ha)
/-
**PowerSeries.coe_aeval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coe_aeval (ha : HasEval a) : ↑(aeval ha) = eval₂ (algebraMap R S) a
参数：ha : HasEval a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coe_aeval`：coe_aeval (ha : HasEval a) : ↑(aeval ha) = eval
₂ (algebraMap R S) a
· 使用定理 `PowerSeries.hasEval`：hasEval {a : S} (ha : HasEval a) : MvPowerSeries.Ha
sEval (fun (_ : Unit) => a)
-/
theorem coe_aeval (ha : HasEval a) :
    ↑(aeval ha) = eval₂ (algebraMap R S) a :=
  MvPowerSeries.coe_aeval (hasEval ha)
/-
**PowerSeries.continuous_aeval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：continuous_aeval (ha : HasEval a) : Continuous (aeval ha : PowerSeries R -
> S)
参数：ha : HasEval a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.continuous_aeval`：continuous_aeval (ha : HasEval a) : Cont
inuous (aeval ha : MvPowerSeries σ R -> S)
· 使用定理 `PowerSeries.hasEval`：hasEval {a : S} (ha : HasEval a) : MvPowerSeries.Ha
sEval (fun (_ : Unit) => a)
-/
theorem continuous_aeval (ha : HasEval a) :
    Continuous (aeval ha : PowerSeries R → S) :=
  MvPowerSeries.continuous_aeval (hasEval ha)

@[simp]
/-
**PowerSeries.aeval_coe** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：aeval_coe (ha : HasEval a) (p : Polynomial R) : aeval ha (p : PowerSeries 
R) = Polynomial.aeval a p
参数：ha : HasEval a；p : Polynomial R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coe_aeval`：coe_aeval (ha : HasEval a) : ↑(aeval ha) = eval₂ 
(algebraMap R S) a
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `PowerSeries.eval₂_coe`：eval₂_coe (f : Polynomial R) : eval₂ φ a f = f.ev
al₂ φ a
-/
theorem aeval_coe (ha : HasEval a) (p : Polynomial R) :
    aeval ha (p : PowerSeries R) = Polynomial.aeval a p := by
  rw [coe_aeval, Polynomial.aeval_def, eval₂_coe]
/-
**PowerSeries.aeval_unique** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：aeval_unique {ε : PowerSeries R ->ₐ[R] S} (hε : Continuous ε) : aeval (Has
Eval.X.map hε) = ε
参数：hε : Continuous ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.aeval_unique`：aeval_unique {ε : MvPowerSeries σ R ->ₐ[R] S
} (hε : Continuous ε) : aeval (HasEval.X.map hε) = ε
-/
theorem aeval_unique {ε : PowerSeries R →ₐ[R] S} (hε : Continuous ε) :
    aeval (HasEval.X.map hε) = ε :=
  MvPowerSeries.aeval_unique hε
/-
**PowerSeries.hasSum_aeval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：hasSum_aeval (ha : HasEval a) (f : PowerSeries R) : HasSum (fun d => coeff
 d f • a ^ d) (f.aeval ha)
参数：ha : HasEval a；f : PowerSeries R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coe_aeval`：coe_aeval (ha : HasEval a) : ↑(aeval ha) = eval₂ 
(algebraMap R S) a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `PowerSeries.hasSum_eval₂`：hasSum_eval₂ (hφ : Continuous φ) (ha : HasEval
 a) (f : PowerSeries R) : HasSum (fun (d : Nat) => φ (coeff d f) * a ^ d) (f.eva
l₂ φ a)
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
-/
theorem hasSum_aeval (ha : HasEval a) (f : PowerSeries R) :
    HasSum (fun d ↦ coeff d f • a ^ d) (f.aeval ha) := by
  simp_rw [coe_aeval, ← algebraMap_smul (R := R) S, smul_eq_mul]
  exact hasSum_eval₂ (continuous_algebraMap R S) ha f
/-
**PowerSeries.aeval_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：aeval_eq_sum (ha : HasEval a) (f : PowerSeries R) : aeval ha f = tsum fun 
d => coeff d f • a ^ d
参数：ha : HasEval a；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `PowerSeries.hasSum_aeval`：hasSum_aeval (ha : HasEval a) (f : PowerSeries
 R) : HasSum (fun d => coeff d f • a ^ d) (f.aeval ha)
-/
theorem aeval_eq_sum (ha : HasEval a) (f : PowerSeries R) :
    aeval ha f = tsum fun d ↦ coeff d f • a ^ d :=
  (hasSum_aeval ha f).tsum_eq.symm
/-
**PowerSeries.comp_aeval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：comp_aeval (ha : HasEval a) {T : Type*} [CommRing T] [UniformSpace T] [IsU
niformAddGroup T] [IsTopologicalRing T] [IsLinearTopology T T] [T2Space T] [Alge
bra R T] [ContinuousSMul R T] [CompleteSpace T] {ε : S ->ₐ[R] T} (hε : Continuou
s ε) : ε.comp (aeval ha) = aeval (ha.map hε)
参数：ha : HasEval a；hε : Continuous ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.comp_aeval`：comp_aeval (ha : HasEval a) {T : Type*} [CommR
ing T] [UniformSpace T] [IsUniformAddGroup T] [IsTopologicalRing T] [IsLinearTop
ology T T] [T2…
· 使用定理 `PowerSeries.hasEval`：hasEval {a : S} (ha : HasEval a) : MvPowerSeries.Ha
sEval (fun (_ : Unit) => a)
-/
theorem comp_aeval (ha : HasEval a)
    {T : Type*} [CommRing T] [UniformSpace T] [IsUniformAddGroup T]
    [IsTopologicalRing T] [IsLinearTopology T T]
    [T2Space T] [Algebra R T] [ContinuousSMul R T] [CompleteSpace T]
    {ε : S →ₐ[R] T} (hε : Continuous ε) :
    ε.comp (aeval ha) = aeval (ha.map hε) :=
  MvPowerSeries.comp_aeval (hasEval ha) hε

end PowerSeries

