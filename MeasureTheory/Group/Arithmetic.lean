/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Typeclasses for measurability of operations

In this file we define classes `MeasurableMul` etc. and prove dot-style lemmas
(`Measurable.mul`, `AEMeasurable.mul` etc). For binary operations we define two typeclasses:

- `MeasurableMul` says that both left and right multiplication are measurable;
- `MeasurableMul₂` says that `fun p : α × α => p.1 * p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `MeasurableMul₂`
etc. require `α` to have a second countable topology.

We define separate classes for `MeasurableDiv`/`MeasurableSub`
because on some types (e.g., `ℕ`, `ℝ≥0∞`) division and/or subtraction are not defined as `a * b⁻¹` /
`a + (-b)`.

For instances relating, e.g., `ContinuousMul` to `MeasurableMul` see file
`MeasureTheory.BorelSpace`.

## Implementation notes

For the heuristics of `@[to_additive]` it is important that the type with a multiplication
(or another multiplicative operation) is the first (implicit) argument of all declarations.

## Tags

measurable function, arithmetic operator

## TODO

* Uniformize the treatment of `pow` and `smul`.
* Use `@[to_additive]` to send `MeasurablePow` to `MeasurableSMul₂`.
* This might require changing the definition (swapping the arguments in the function that is
  in the conclusion of `MeasurableSMul`.)
-/

public section

open MeasureTheory
open scoped Pointwise

universe u v
variable {α : Type*}

/-!
### Binary operations: `(· + ·)`, `(· * ·)`, `(· - ·)`, `(· / ·)`
-/


/--
Definition of `MeasurableAdd` / `MeasurableAdd` 的定义

English:
class MeasurableAdd
  parameters: (M : Type*) [MeasurableSpace M] [Add M]
  axioms and operations (2):
    - measurable_const_add : forall c : M, Measurable (c + ·)  [default: by intro; fun_prop]
    - measurable_add_const : forall c : M, Measurable (· + c)  [default: by intro; fun_prop]

中文:
类 MeasurableAdd
  参数: (M : 类型) [可测空间 M] [加法 M]
  公理与运算 (2 个):
    - measurable_const_add : 对任意 c : M, 可测 (c + ·)  [默认: by intro; fun_prop]
    - measurable_add_const : 对任意 c : M, 可测 (· + c)  [默认: by intro; fun_prop]

Depends on / 依赖: Measurable, fun_prop, measurable_add_const
-/
class MeasurableAdd (M : Type*) [MeasurableSpace M] [Add M] : Prop where
  measurable_const_add : forall c : M, Measurable (c + ·) := by intro; fun_prop
  measurable_add_const : forall c : M, Measurable (· + c) := by intro; fun_prop

export MeasurableAdd (measurable_const_add measurable_add_const)

/--
Definition of `MeasurableAdd₂` / `MeasurableAdd₂` 的定义

English:
class MeasurableAdd₂
  parameters: (M : Type*) [MeasurableSpace M] [Add M]
  axioms and operations (1):
    - measurable_add : Measurable fun p : M × M => p.1 + p.2

中文:
类 MeasurableAdd₂
  参数: (M : 类型) [可测空间 M] [加法 M]
  公理与运算 (1 个):
    - measurable_add : 可测 fun p : M × M => p.1 + p.2
-/
class MeasurableAdd₂ (M : Type*) [MeasurableSpace M] [Add M] : Prop where
  measurable_add : Measurable fun p : M × M => p.1 + p.2

export MeasurableAdd₂ (measurable_add)

/-- We say that a type has `MeasurableMul` if `(c * ·)` and `(· * c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (*)` see `MeasurableMul₂`. -/
@[to_additive]
/--
Definition of `MeasurableMul` / `MeasurableMul` 的定义

English:
class MeasurableMul
  parameters: (M : Type*) [MeasurableSpace M] [Mul M]
  axioms and operations (2):
    - measurable_const_mul : forall c : M, Measurable (c * ·)  [default: by intro; fun_prop]
    - measurable_mul_const : forall c : M, Measurable (· * c)  [default: by intro; fun_prop]

中文:
类 MeasurableMul
  参数: (M : 类型) [可测空间 M] [乘法 M]
  公理与运算 (2 个):
    - measurable_const_mul : 对任意 c : M, 可测 (c * ·)  [默认: by intro; fun_prop]
    - measurable_mul_const : 对任意 c : M, 可测 (· * c)  [默认: by intro; fun_prop]

Depends on / 依赖: Measurable, fun_prop, measurable_mul_const
-/
class MeasurableMul (M : Type*) [MeasurableSpace M] [Mul M] : Prop where
  measurable_const_mul : forall c : M, Measurable (c * ·) := by intro; fun_prop
  measurable_mul_const : forall c : M, Measurable (· * c) := by intro; fun_prop

export MeasurableMul (measurable_const_mul measurable_mul_const)

/-- We say that a type has `MeasurableMul₂` if `uncurry (· * ·)` is a measurable function.
For a typeclass assuming measurability of `(c * ·)` and `(· * c)` see `MeasurableMul`. -/
@[to_additive MeasurableAdd₂]
/--
Definition of `MeasurableMul₂` / `MeasurableMul₂` 的定义

English:
class MeasurableMul₂
  parameters: (M : Type*) [MeasurableSpace M] [Mul M]
  axioms and operations (1):
    - measurable_mul : Measurable fun p : M × M => p.1 * p.2

中文:
类 MeasurableMul₂
  参数: (M : 类型) [可测空间 M] [乘法 M]
  公理与运算 (1 个):
    - measurable_mul : 可测 fun p : M × M => p.1 * p.2
-/
class MeasurableMul₂ (M : Type*) [MeasurableSpace M] [Mul M] : Prop where
  measurable_mul : Measurable fun p : M × M => p.1 * p.2

export MeasurableMul₂ (measurable_mul)

section Mul

variable {M α β : Type*} [MeasurableSpace M] [Mul M] {m : MeasurableSpace α}
  {mβ : MeasurableSpace β} {f g : α -> M} {μ : Measure α}

@[to_additive (attr := fun_prop)]
/--
theorem `Measurable.const_mul` / 定理 `Measurable.const_mul`

English:
theorem Measurable.const_mul
  given: [MeasurableMul M] (hf : Measurable f) (c : M)
  proof: (measurable_const_mul c).comp hf

@[to_additive (attr := fun_prop)]

中文:
定理 可测.const_mul
  条件: [MeasurableMul M] (hf : 可测 f) (c : M)
  证明: (measurable_const_mul c).comp hf

@[to_additive (attr := fun_prop)]

Depends on / 依赖: measurable_const_mul
-/
theorem Measurable.const_mul [MeasurableMul M] (hf : Measurable f) (c : M) :
    Measurable fun x => c * f x :=
  (measurable_const_mul c).comp hf

@[to_additive (attr := fun_prop)]
/--
theorem `AEMeasurable.const_mul` / 定理 `AEMeasurable.const_mul`

English:
theorem AEMeasurable.const_mul
  given: [MeasurableMul M] (hf : AEMeasurable f μ) (c : M)
  proof: (MeasurableMul.measurable_const_mul c).comp_aemeasurable hf

@[to_additive (attr := fun_prop)]

中文:
定理 几乎处处可测.const_mul
  条件: [MeasurableMul M] (hf : 几乎处处可测 f μ) (c : M)
  证明: (MeasurableMul.measurable_const_mul c).comp_aemeasurable hf

@[to_additive (attr := fun_prop)]

Depends on / 依赖: MeasurableMul, MeasurableMul.measurable_const_mul, comp_aemeasurable, measurable_const_mul
-/
theorem AEMeasurable.const_mul [MeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => c * f x) μ :=
  (MeasurableMul.measurable_const_mul c).comp_aemeasurable hf

@[to_additive (attr := fun_prop)]
/--
theorem `Measurable.mul_const` / 定理 `Measurable.mul_const`

English:
theorem Measurable.mul_const
  given: [MeasurableMul M] (hf : Measurable f) (c : M)
  proof: (measurable_mul_const c).comp hf

@[to_additive (attr := fun_prop)]

中文:
定理 可测.mul_const
  条件: [MeasurableMul M] (hf : 可测 f) (c : M)
  证明: (measurable_mul_const c).comp hf

@[to_additive (attr := fun_prop)]

Depends on / 依赖: measurable_mul_const
-/
theorem Measurable.mul_const [MeasurableMul M] (hf : Measurable f) (c : M) :
    Measurable fun x => f x * c :=
  (measurable_mul_const c).comp hf

@[to_additive (attr := fun_prop)]
/--
theorem `AEMeasurable.mul_const` / 定理 `AEMeasurable.mul_const`

English:
theorem AEMeasurable.mul_const
  given: [MeasurableMul M] (hf : AEMeasurable f μ) (c : M)
  proof: (measurable_mul_const c).comp_aemeasurable hf

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 几乎处处可测.mul_const
  条件: [MeasurableMul M] (hf : 几乎处处可测 f μ) (c : M)
  证明: (measurable_mul_const c).comp_aemeasurable hf

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: comp_aemeasurable, measurable_mul_const
-/
theorem AEMeasurable.mul_const [MeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => f x * c) μ :=
  (measurable_mul_const c).comp_aemeasurable hf

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `Measurable.mul` / 定理 `Measurable.mul`

English:
theorem Measurable.mul
  given: [MeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g)
  proof: measurable_mul.comp (hf.prodMk hg)

中文:
定理 可测.mul
  条件: [MeasurableMul₂ M] (hf : 可测 f) (hg : 可测 g)
  证明: measurable_mul.comp (hf.prodMk hg)

Depends on / 依赖: hf.prodMk, measurable_mul, measurable_mul.comp, prodMk
-/
theorem Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) :
    Measurable (f * g) :=
  measurable_mul.comp (hf.prodMk hg)

/-- Compositional version of `Measurable.mul` for use by `fun_prop`. -/
@[to_additive (attr := fun_prop)
/-- Compositional version of `Measurable.add` for use by `fun_prop`. -/]
/--
lemma `Measurable.mul'` / 引理 `Measurable.mul'`

English:
lemma Measurable.mul'
  statement: [MeasurableMul₂ M] {f g : α -> β -> M} {h : α -> β} (hf : Measurable ↿f)
  proof: by
  dsimp; fun_prop

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
引理 可测.mul'
  结论: [MeasurableMul₂ M] {f g : α -> β -> M} {h : α -> β} (hf : 可测 ↿f)
  证明: by
  dsimp; fun_prop

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: fun_prop
-/
lemma Measurable.mul' [MeasurableMul₂ M] {f g : α -> β -> M} {h : α -> β} (hf : Measurable ↿f)
    (hg : Measurable ↿g) (hh : Measurable h) : Measurable fun a => (f a * g a) (h a) := by
  dsimp; fun_prop

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `AEMeasurable.mul` / 定理 `AEMeasurable.mul`

English:
theorem AEMeasurable.mul
  given: [MeasurableMul₂ M] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
  proof: measurable_mul.comp_aemeasurable (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias AEMeasurable.mul' := AEMeasurable.mul
@[deprecated (since := "2026-06-26")] alias AEMeasurable.add' := AEMeasurable.add

@[to_additive]

中文:
定理 几乎处处可测.mul
  条件: [MeasurableMul₂ M] (hf : 几乎处处可测 f μ) (hg : 几乎处处可测 g μ)
  证明: measurable_mul.comp_aemeasurable (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias AEMeasurable.mul' := AEMeasurable.mul
@[deprecated (since := "2026-06-26")] alias AEMeasurable.add' := AEMeasurable.add

@[to_additive]

Depends on / 依赖: comp_aemeasurable, hf.prodMk, measurable_mul, measurable_mul.comp_aemeasurable, prodMk
-/
theorem AEMeasurable.mul [MeasurableMul₂ M] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f * g) μ :=
  measurable_mul.comp_aemeasurable (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias AEMeasurable.mul' := AEMeasurable.mul
@[deprecated (since := "2026-06-26")] alias AEMeasurable.add' := AEMeasurable.add

@[to_additive]
instance (priority := 100) MeasurableMul₂.toMeasurableMul [MeasurableMul₂ M] :
    MeasurableMul M where

@[to_additive]
/--
Instance `Pi.measurableMul` / 实例 `Pi.measurableMul`

English:
instance Pi.measurableMul
  signature: {ι : Type*} {α : ι -> Type*} [forall i, Mul (α i)]
  body: ⟨fun _ => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_mul _, fun _ =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).mul_const _⟩

@[to_additive Pi.measurableAdd₂]

中文:
实例 依赖函数类型.measurableMul
  签名: {ι : 类型} {α : ι -> 类型} [对任意 i, 乘法 (α i)]
  定义体: ⟨fun _ => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_mul _, fun _ =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).mul_const _⟩

@[to_additive Pi.measurableAdd₂]

Depends on / 依赖: const_mul, measurable_pi_apply, measurable_pi_iff, measurable_pi_iff.mpr, mul_const
-/
instance Pi.measurableMul {ι : Type*} {α : ι -> Type*} [forall i, Mul (α i)]
    [forall i, MeasurableSpace (α i)] [forall i, MeasurableMul (α i)] : MeasurableMul (forall i, α i) :=
  ⟨fun _ => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_mul _, fun _ =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).mul_const _⟩

@[to_additive Pi.measurableAdd₂]
/--
Instance `Pi.measurableMul₂` / 实例 `Pi.measurableMul₂`

English:
instance Pi.measurableMul₂
  signature: {ι : Type*} {α : ι -> Type*} [forall i, Mul (α i)]
  body: ⟨measurable_pi_iff.mpr fun _ => measurable_fst.eval.mul measurable_snd.eval⟩

中文:
实例 依赖函数类型.measurableMul₂
  签名: {ι : 类型} {α : ι -> 类型} [对任意 i, 乘法 (α i)]
  定义体: ⟨measurable_pi_iff.mpr fun _ => measurable_fst.eval.mul measurable_snd.eval⟩

Depends on / 依赖: measurable_fst, measurable_fst.eval.mul, measurable_pi_iff, measurable_pi_iff.mpr, measurable_snd, measurable_snd.eval
-/
instance Pi.measurableMul₂ {ι : Type*} {α : ι -> Type*} [forall i, Mul (α i)]
    [forall i, MeasurableSpace (α i)] [forall i, MeasurableMul₂ (α i)] : MeasurableMul₂ (forall i, α i) :=
  ⟨measurable_pi_iff.mpr fun _ => measurable_fst.eval.mul measurable_snd.eval⟩

end Mul

/-- A version of `measurable_div_const` that assumes `MeasurableMul` instead of
  `MeasurableDiv`. This can be nice to avoid unnecessary type-class assumptions. -/
@[to_additive /-- A version of `measurable_sub_const` that assumes `MeasurableAdd` instead of
  `MeasurableSub`. This can be nice to avoid unnecessary type-class assumptions. -/]
/--
theorem `measurable_div_const'` / 定理 `measurable_div_const'`

English:
theorem measurable_div_const'
  statement: {G : Type*} [DivInvMonoid G] [MeasurableSpace G] [MeasurableMul G]
  proof: by simp_rw [div_eq_mul_inv, measurable_mul_const]

中文:
定理 measurable_div_const'
  结论: {G : 类型} [除逆幺半群 G] [可测空间 G] [MeasurableMul G]
  证明: by simp_rw [div_eq_mul_inv, measurable_mul_const]

Depends on / 依赖: div_eq_mul_inv, measurable_mul_const, simp_rw
-/
theorem measurable_div_const' {G : Type*} [DivInvMonoid G] [MeasurableSpace G] [MeasurableMul G]
    (g : G) : Measurable fun h => h / g := by simp_rw [div_eq_mul_inv, measurable_mul_const]

/--
Definition of `MeasurablePow` / `MeasurablePow` 的定义

English:
class MeasurablePow
  parameters: (β γ : Type*) [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ]
  axioms and operations (1):
    - measurable_pow : Measurable fun p : β × γ => p.1 ^ p.2

中文:
类 MeasurablePow
  参数: (β γ : 类型) [可测空间 β] [可测空间 γ] [幂 β γ]
  公理与运算 (1 个):
    - measurable_pow : 可测 fun p : β × γ => p.1 ^ p.2
-/
class MeasurablePow (β γ : Type*) [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] : Prop where
  measurable_pow : Measurable fun p : β × γ => p.1 ^ p.2

export MeasurablePow (measurable_pow)

/--
Instance `Monoid.measurablePow` / 实例 `Monoid.measurablePow`

English:
instance Monoid.measurablePow
  signature: (M : Type*) [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M]
  body: ⟨measurable_from_prod_countable_left fun n => by
      induction n with
      | zero => simp only [pow_zero, ← Pi.one_def, measurable_one]
      | succ n ih =>
        simp only [pow_succ]
        exact ih.mul measurable_id⟩

中文:
实例 幺半群.measurablePow
  签名: (M : 类型) [幺半群 M] [可测空间 M] [MeasurableMul₂ M]
  定义体: ⟨measurable_from_prod_countable_left fun n => by
      induction n with
      | zero => simp only [pow_zero, ← Pi.one_def, measurable_one]
      | succ n ih =>
        simp only [pow_succ]
        exact ih.mul measurable_id⟩

Depends on / 依赖: Pi.one_def, ih.mul, measurable_from_prod_countable_left, measurable_id, measurable_one, one_def, pow_succ, pow_zero
-/
instance Monoid.measurablePow (M : Type*) [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M] :
    MeasurablePow M Nat :=
  ⟨measurable_from_prod_countable_left fun n => by
      induction n with
      | zero => simp only [pow_zero, ← Pi.one_def, measurable_one]
      | succ n ih =>
        simp only [pow_succ]
        exact ih.mul measurable_id⟩

section Pow

variable {β γ α : Type*} [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] [MeasurablePow β γ]
  {m : MeasurableSpace α} {μ : Measure α} {f : α -> β} {g : α -> γ}

@[fun_prop]
/--
theorem `Measurable.pow` / 定理 `Measurable.pow`

English:
theorem Measurable.pow
  given: (hf : Measurable f) (hg : Measurable g)
  statement: Measurable fun x => f x ^ g x
  proof: measurable_pow.comp (hf.prodMk hg)

@[fun_prop]

中文:
定理 可测.pow
  条件: (hf : 可测 f) (hg : 可测 g)
  结论: 可测 fun x => f x ^ g x
  证明: measurable_pow.comp (hf.prodMk hg)

@[fun_prop]

Depends on / 依赖: hf.prodMk, measurable_pow, measurable_pow.comp, prodMk
-/
theorem Measurable.pow (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x ^ g x :=
  measurable_pow.comp (hf.prodMk hg)

@[fun_prop]
/--
theorem `AEMeasurable.pow` / 定理 `AEMeasurable.pow`

English:
theorem AEMeasurable.pow
  given: (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
  proof: measurable_pow.comp_aemeasurable (hf.prodMk hg)

@[fun_prop]

中文:
定理 几乎处处可测.pow
  条件: (hf : 几乎处处可测 f μ) (hg : 几乎处处可测 g μ)
  证明: measurable_pow.comp_aemeasurable (hf.prodMk hg)

@[fun_prop]

Depends on / 依赖: comp_aemeasurable, hf.prodMk, measurable_pow, measurable_pow.comp_aemeasurable, prodMk
-/
theorem AEMeasurable.pow (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun x => f x ^ g x) μ :=
  measurable_pow.comp_aemeasurable (hf.prodMk hg)

@[fun_prop]
/--
theorem `Measurable.pow_const` / 定理 `Measurable.pow_const`

English:
theorem Measurable.pow_const
  given: (hf : Measurable f) (c : γ)
  statement: Measurable fun x => f x ^ c
  proof: hf.pow measurable_const

@[fun_prop]

中文:
定理 可测.pow_const
  条件: (hf : 可测 f) (c : γ)
  结论: 可测 fun x => f x ^ c
  证明: hf.pow measurable_const

@[fun_prop]

Depends on / 依赖: hf.pow, measurable_const
-/
theorem Measurable.pow_const (hf : Measurable f) (c : γ) : Measurable fun x => f x ^ c :=
  hf.pow measurable_const

@[fun_prop]
/--
theorem `AEMeasurable.pow_const` / 定理 `AEMeasurable.pow_const`

English:
theorem AEMeasurable.pow_const
  given: (hf : AEMeasurable f μ) (c : γ)
  proof: hf.pow aemeasurable_const

@[fun_prop]

中文:
定理 几乎处处可测.pow_const
  条件: (hf : 几乎处处可测 f μ) (c : γ)
  证明: hf.pow aemeasurable_const

@[fun_prop]

Depends on / 依赖: aemeasurable_const, hf.pow
-/
theorem AEMeasurable.pow_const (hf : AEMeasurable f μ) (c : γ) :
    AEMeasurable (fun x => f x ^ c) μ :=
  hf.pow aemeasurable_const

@[fun_prop]
/--
theorem `Measurable.const_pow` / 定理 `Measurable.const_pow`

English:
theorem Measurable.const_pow
  given: (hg : Measurable g) (c : β)
  statement: Measurable fun x => c ^ g x
  proof: measurable_const.pow hg

@[fun_prop]

中文:
定理 可测.const_pow
  条件: (hg : 可测 g) (c : β)
  结论: 可测 fun x => c ^ g x
  证明: measurable_const.pow hg

@[fun_prop]

Depends on / 依赖: measurable_const, measurable_const.pow
-/
theorem Measurable.const_pow (hg : Measurable g) (c : β) : Measurable fun x => c ^ g x :=
  measurable_const.pow hg

@[fun_prop]
/--
theorem `AEMeasurable.const_pow` / 定理 `AEMeasurable.const_pow`

English:
theorem AEMeasurable.const_pow
  given: (hg : AEMeasurable g μ) (c : β)
  proof: aemeasurable_const.pow hg

中文:
定理 几乎处处可测.const_pow
  条件: (hg : 几乎处处可测 g μ) (c : β)
  证明: aemeasurable_const.pow hg

Depends on / 依赖: aemeasurable_const, aemeasurable_const.pow
-/
theorem AEMeasurable.const_pow (hg : AEMeasurable g μ) (c : β) :
    AEMeasurable (fun x => c ^ g x) μ :=
  aemeasurable_const.pow hg

end Pow

/--
Definition of `MeasurableSub` / `MeasurableSub` 的定义

English:
class MeasurableSub
  parameters: (G : Type*) [MeasurableSpace G] [Sub G]
  axioms and operations (2):
    - measurable_const_sub : forall c : G, Measurable (c - ·)  [default: by intro; fun_prop]
    - measurable_sub_const : forall c : G, Measurable (· - c)  [default: by intro; fun_prop]

中文:
类 MeasurableSub
  参数: (G : 类型) [可测空间 G] [减法 G]
  公理与运算 (2 个):
    - measurable_const_sub : 对任意 c : G, 可测 (c - ·)  [默认: by intro; fun_prop]
    - measurable_sub_const : 对任意 c : G, 可测 (· - c)  [默认: by intro; fun_prop]

Depends on / 依赖: Measurable, fun_prop, measurable_sub_const
-/
class MeasurableSub (G : Type*) [MeasurableSpace G] [Sub G] : Prop where
  measurable_const_sub : forall c : G, Measurable (c - ·) := by intro; fun_prop
  measurable_sub_const : forall c : G, Measurable (· - c) := by intro; fun_prop

export MeasurableSub (measurable_const_sub measurable_sub_const)

/--
Definition of `MeasurableSub₂` / `MeasurableSub₂` 的定义

English:
class MeasurableSub₂
  parameters: (G : Type*) [MeasurableSpace G] [Sub G]
  axioms and operations (1):
    - measurable_sub : Measurable fun p : G × G => p.1 - p.2

中文:
类 MeasurableSub₂
  参数: (G : 类型) [可测空间 G] [减法 G]
  公理与运算 (1 个):
    - measurable_sub : 可测 fun p : G × G => p.1 - p.2
-/
class MeasurableSub₂ (G : Type*) [MeasurableSpace G] [Sub G] : Prop where
  measurable_sub : Measurable fun p : G × G => p.1 - p.2

export MeasurableSub₂ (measurable_sub)

/-- We say that a type has `MeasurableDiv` if `(c / ·)` and `(· / c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (· / ·)` see `MeasurableDiv₂`. -/
@[to_additive]
/--
Definition of `MeasurableDiv` / `MeasurableDiv` 的定义

English:
class MeasurableDiv
  parameters: (G₀ : Type*) [MeasurableSpace G₀] [Div G₀]
  axioms and operations (2):
    - measurable_const_div : forall c : G₀, Measurable (c / ·)  [default: by intro; fun_prop]
    - measurable_div_const : forall c : G₀, Measurable (· / c)  [default: by intro; fun_prop]

中文:
类 MeasurableDiv
  参数: (G₀ : 类型) [可测空间 G₀] [除法 G₀]
  公理与运算 (2 个):
    - measurable_const_div : 对任意 c : G₀, 可测 (c / ·)  [默认: by intro; fun_prop]
    - measurable_div_const : 对任意 c : G₀, 可测 (· / c)  [默认: by intro; fun_prop]

Depends on / 依赖: Measurable, fun_prop, measurable_div_const
-/
class MeasurableDiv (G₀ : Type*) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurable_const_div : forall c : G₀, Measurable (c / ·) := by intro; fun_prop
  measurable_div_const : forall c : G₀, Measurable (· / c) := by intro; fun_prop

export MeasurableDiv (measurable_const_div measurable_div_const)

/-- We say that a type has `MeasurableDiv₂` if `uncurry (· / ·)` is a measurable function.
For a typeclass assuming measurability of `(c / ·)` and `(· / c)` see `MeasurableDiv`. -/
@[to_additive MeasurableSub₂]
/--
Definition of `MeasurableDiv₂` / `MeasurableDiv₂` 的定义

English:
class MeasurableDiv₂
  parameters: (G₀ : Type*) [MeasurableSpace G₀] [Div G₀]
  axioms and operations (1):
    - measurable_div : Measurable fun p : G₀ × G₀ => p.1 / p.2

中文:
类 MeasurableDiv₂
  参数: (G₀ : 类型) [可测空间 G₀] [除法 G₀]
  公理与运算 (1 个):
    - measurable_div : 可测 fun p : G₀ × G₀ => p.1 / p.2
-/
class MeasurableDiv₂ (G₀ : Type*) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurable_div : Measurable fun p : G₀ × G₀ => p.1 / p.2

export MeasurableDiv₂ (measurable_div)

section Div

variable {G α β : Type*} [MeasurableSpace G] [Div G] {m : MeasurableSpace α}
  {mβ : MeasurableSpace β} {f g : α -> G} {μ : Measure α}

@[to_additive (attr := fun_prop)]
/--
theorem `Measurable.const_div` / 定理 `Measurable.const_div`

English:
theorem Measurable.const_div
  given: [MeasurableDiv G] (hf : Measurable f) (c : G)
  proof: (MeasurableDiv.measurable_const_div c).comp hf

@[to_additive (attr := fun_prop)]

中文:
定理 可测.const_div
  条件: [MeasurableDiv G] (hf : 可测 f) (c : G)
  证明: (MeasurableDiv.measurable_const_div c).comp hf

@[to_additive (attr := fun_prop)]

Depends on / 依赖: MeasurableDiv, MeasurableDiv.measurable_const_div, measurable_const_div
-/
theorem Measurable.const_div [MeasurableDiv G] (hf : Measurable f) (c : G) :
    Measurable fun x => c / f x :=
  (MeasurableDiv.measurable_const_div c).comp hf

@[to_additive (attr := fun_prop)]
/--
theorem `AEMeasurable.const_div` / 定理 `AEMeasurable.const_div`

English:
theorem AEMeasurable.const_div
  given: [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G)
  proof: (MeasurableDiv.measurable_const_div c).comp_aemeasurable hf

@[to_additive (attr := fun_prop)]

中文:
定理 几乎处处可测.const_div
  条件: [MeasurableDiv G] (hf : 几乎处处可测 f μ) (c : G)
  证明: (MeasurableDiv.measurable_const_div c).comp_aemeasurable hf

@[to_additive (attr := fun_prop)]

Depends on / 依赖: MeasurableDiv, MeasurableDiv.measurable_const_div, comp_aemeasurable, measurable_const_div
-/
theorem AEMeasurable.const_div [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
    AEMeasurable (fun x => c / f x) μ :=
  (MeasurableDiv.measurable_const_div c).comp_aemeasurable hf

@[to_additive (attr := fun_prop)]
/--
theorem `Measurable.div_const` / 定理 `Measurable.div_const`

English:
theorem Measurable.div_const
  given: [MeasurableDiv G] (hf : Measurable f) (c : G)
  proof: (MeasurableDiv.measurable_div_const c).comp hf

@[to_additive (attr := fun_prop)]

中文:
定理 可测.div_const
  条件: [MeasurableDiv G] (hf : 可测 f) (c : G)
  证明: (MeasurableDiv.measurable_div_const c).comp hf

@[to_additive (attr := fun_prop)]

Depends on / 依赖: MeasurableDiv, MeasurableDiv.measurable_div_const, measurable_div_const
-/
theorem Measurable.div_const [MeasurableDiv G] (hf : Measurable f) (c : G) :
    Measurable fun x => f x / c :=
  (MeasurableDiv.measurable_div_const c).comp hf

@[to_additive (attr := fun_prop)]
/--
theorem `AEMeasurable.div_const` / 定理 `AEMeasurable.div_const`

English:
theorem AEMeasurable.div_const
  given: [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G)
  proof: (MeasurableDiv.measurable_div_const c).comp_aemeasurable hf

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 几乎处处可测.div_const
  条件: [MeasurableDiv G] (hf : 几乎处处可测 f μ) (c : G)
  证明: (MeasurableDiv.measurable_div_const c).comp_aemeasurable hf

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: MeasurableDiv, MeasurableDiv.measurable_div_const, comp_aemeasurable, measurable_div_const
-/
theorem AEMeasurable.div_const [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
    AEMeasurable (fun x => f x / c) μ :=
  (MeasurableDiv.measurable_div_const c).comp_aemeasurable hf

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `Measurable.div` / 定理 `Measurable.div`

English:
theorem Measurable.div
  given: [MeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g)
  proof: measurable_div.comp (hf.prodMk hg)

@[to_additive (attr := fun_prop)]

中文:
定理 可测.div
  条件: [MeasurableDiv₂ G] (hf : 可测 f) (hg : 可测 g)
  证明: measurable_div.comp (hf.prodMk hg)

@[to_additive (attr := fun_prop)]

Depends on / 依赖: hf.prodMk, measurable_div, measurable_div.comp, prodMk
-/
theorem Measurable.div [MeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g) :
    Measurable (f / g) :=
  measurable_div.comp (hf.prodMk hg)

@[to_additive (attr := fun_prop)]
/--
lemma `Measurable.div'` / 引理 `Measurable.div'`

English:
lemma Measurable.div'
  statement: [MeasurableDiv₂ G] {f g : α -> β -> G} {h : α -> β} (hf : Measurable ↿f)
  proof: by
  dsimp; fun_prop

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
引理 可测.div'
  结论: [MeasurableDiv₂ G] {f g : α -> β -> G} {h : α -> β} (hf : 可测 ↿f)
  证明: by
  dsimp; fun_prop

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: fun_prop
-/
lemma Measurable.div' [MeasurableDiv₂ G] {f g : α -> β -> G} {h : α -> β} (hf : Measurable ↿f)
    (hg : Measurable ↿g) (hh : Measurable h) : Measurable fun a => (f a / g a) (h a) := by
  dsimp; fun_prop

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `AEMeasurable.div` / 定理 `AEMeasurable.div`

English:
theorem AEMeasurable.div
  given: [MeasurableDiv₂ G] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
  proof: measurable_div.comp_aemeasurable (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias AEMeasurable.div' := AEMeasurable.div
@[deprecated (since := "2026-06-26")] alias AEMeasurable.sub' := AEMeasurable.sub

@[to_additive]

中文:
定理 几乎处处可测.div
  条件: [MeasurableDiv₂ G] (hf : 几乎处处可测 f μ) (hg : 几乎处处可测 g μ)
  证明: measurable_div.comp_aemeasurable (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias AEMeasurable.div' := AEMeasurable.div
@[deprecated (since := "2026-06-26")] alias AEMeasurable.sub' := AEMeasurable.sub

@[to_additive]

Depends on / 依赖: comp_aemeasurable, hf.prodMk, measurable_div, measurable_div.comp_aemeasurable, prodMk
-/
theorem AEMeasurable.div [MeasurableDiv₂ G] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f / g) μ :=
  measurable_div.comp_aemeasurable (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias AEMeasurable.div' := AEMeasurable.div
@[deprecated (since := "2026-06-26")] alias AEMeasurable.sub' := AEMeasurable.sub

@[to_additive]
instance (priority := 100) MeasurableDiv₂.toMeasurableDiv [MeasurableDiv₂ G] :
    MeasurableDiv G :=
  ⟨fun _ => measurable_const.div measurable_id, fun _ => measurable_id.div measurable_const⟩

@[to_additive]
/--
Instance `Pi.measurableDiv` / 实例 `Pi.measurableDiv`

English:
instance Pi.measurableDiv
  signature: {ι : Type*} {α : ι -> Type*} [forall i, Div (α i)]
  body: ⟨fun _ => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_div _, fun _ =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).div_const _⟩

@[to_additive Pi.measurableSub₂]

中文:
实例 依赖函数类型.measurableDiv
  签名: {ι : 类型} {α : ι -> 类型} [对任意 i, 除法 (α i)]
  定义体: ⟨fun _ => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_div _, fun _ =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).div_const _⟩

@[to_additive Pi.measurableSub₂]

Depends on / 依赖: const_div, div_const, measurable_pi_apply, measurable_pi_iff, measurable_pi_iff.mpr
-/
instance Pi.measurableDiv {ι : Type*} {α : ι -> Type*} [forall i, Div (α i)]
    [forall i, MeasurableSpace (α i)] [forall i, MeasurableDiv (α i)] : MeasurableDiv (forall i, α i) :=
  ⟨fun _ => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_div _, fun _ =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).div_const _⟩

@[to_additive Pi.measurableSub₂]
/--
Instance `Pi.measurableDiv₂` / 实例 `Pi.measurableDiv₂`

English:
instance Pi.measurableDiv₂
  signature: {ι : Type*} {α : ι -> Type*} [forall i, Div (α i)]
  body: ⟨measurable_pi_iff.mpr fun _ => measurable_fst.eval.div measurable_snd.eval⟩

中文:
实例 依赖函数类型.measurableDiv₂
  签名: {ι : 类型} {α : ι -> 类型} [对任意 i, 除法 (α i)]
  定义体: ⟨measurable_pi_iff.mpr fun _ => measurable_fst.eval.div measurable_snd.eval⟩

Depends on / 依赖: measurable_fst, measurable_fst.eval.div, measurable_pi_iff, measurable_pi_iff.mpr, measurable_snd, measurable_snd.eval
-/
instance Pi.measurableDiv₂ {ι : Type*} {α : ι -> Type*} [forall i, Div (α i)]
    [forall i, MeasurableSpace (α i)] [forall i, MeasurableDiv₂ (α i)] : MeasurableDiv₂ (forall i, α i) :=
  ⟨measurable_pi_iff.mpr fun _ => measurable_fst.eval.div measurable_snd.eval⟩

instance {E} [MeasurableSpace E] [AddGroup E] [MeasurableSingletonClass E] [MeasurableSub₂ E] :
    MeasurableEq E := by
  constructor
  simp_rw +singlePass [Set.diagonal, ← sub_eq_zero]
  measurability

instance {β : Type*} [AddCommMonoid β] [PartialOrder β]
    [CanonicallyOrderedAdd β] [Sub β] [OrderedSub β]
    {_ : MeasurableSpace β} [MeasurableSub₂ β] [MeasurableSingletonClass β] :
    MeasurableEq β := by
  constructor
  simp_rw [Set.diagonal, le_antisymm_iff, ← tsub_eq_zero_iff_le]
  measurability

end Div

/--
Definition of `MeasurableNeg` / `MeasurableNeg` 的定义

English:
class MeasurableNeg
  parameters: (G : Type*) [Neg G] [MeasurableSpace G]
  axioms and operations (1):
    - measurable_neg : Measurable (Neg.neg : G -> G)

中文:
类 MeasurableNeg
  参数: (G : 类型) [取负 G] [可测空间 G]
  公理与运算 (1 个):
    - measurable_neg : 可测 (取负.neg : G -> G)
-/
class MeasurableNeg (G : Type*) [Neg G] [MeasurableSpace G] : Prop where
  measurable_neg : Measurable (Neg.neg : G -> G)

/-- We say that a type has `MeasurableInv` if `x ↦ x⁻¹` is a measurable function. -/
@[to_additive]
/--
Definition of `MeasurableInv` / `MeasurableInv` 的定义

English:
class MeasurableInv
  parameters: (G : Type*) [Inv G] [MeasurableSpace G]
  axioms and operations (1):
    - measurable_inv : Measurable (Inv.inv : G -> G)

中文:
类 MeasurableInv
  参数: (G : 类型) [取逆 G] [可测空间 G]
  公理与运算 (1 个):
    - measurable_inv : 可测 (取逆.inv : G -> G)
-/
class MeasurableInv (G : Type*) [Inv G] [MeasurableSpace G] : Prop where
  measurable_inv : Measurable (Inv.inv : G -> G)

export MeasurableInv (measurable_inv)

export MeasurableNeg (measurable_neg)

@[to_additive]
instance (priority := 100) measurableDiv_of_mul_inv (G : Type*) [MeasurableSpace G]
    [DivInvMonoid G] [MeasurableMul G] [MeasurableInv G] : MeasurableDiv G where
  measurable_const_div c := by
    convert! measurable_inv.const_mul c using 1
    ext1
    apply div_eq_mul_inv
  measurable_div_const c := by
    convert! measurable_id.mul_const c⁻¹ using 1
    ext1
    apply div_eq_mul_inv

section Inv

variable {G α : Type*} [Inv G] [MeasurableSpace G] [MeasurableInv G] {m : MeasurableSpace α}
  {f : α -> G} {μ : Measure α}

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `Measurable.inv` / 定理 `Measurable.inv`

English:
theorem Measurable.inv
  given: (hf : Measurable f)
  statement: Measurable f⁻¹
  proof: measurable_inv.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 可测.inv
  条件: (hf : 可测 f)
  结论: 可测 f⁻¹
  证明: measurable_inv.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: measurable_inv, measurable_inv.comp
-/
theorem Measurable.inv (hf : Measurable f) : Measurable f⁻¹ :=
  measurable_inv.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `AEMeasurable.inv` / 定理 `AEMeasurable.inv`

English:
theorem AEMeasurable.inv
  given: (hf : AEMeasurable f μ)
  statement: AEMeasurable f⁻¹ μ
  proof: measurable_inv.comp_aemeasurable hf

@[to_additive (attr := simp)]

中文:
定理 几乎处处可测.inv
  条件: (hf : 几乎处处可测 f μ)
  结论: 几乎处处可测 f⁻¹ μ
  证明: measurable_inv.comp_aemeasurable hf

@[to_additive (attr := simp)]

Depends on / 依赖: comp_aemeasurable, measurable_inv, measurable_inv.comp_aemeasurable
-/
theorem AEMeasurable.inv (hf : AEMeasurable f μ) : AEMeasurable f⁻¹ μ :=
  measurable_inv.comp_aemeasurable hf

@[to_additive (attr := simp)]
/--
theorem `measurable_inv_iff` / 定理 `measurable_inv_iff`

English:
theorem measurable_inv_iff
  statement: {G : Type*} [InvolutiveInv G] [MeasurableSpace G] [MeasurableInv G]
  proof: ⟨fun h => by simpa only [inv_inv] using h.fun_inv, fun h => h.inv⟩

@[to_additive (attr := simp)]

中文:
定理 measurable_inv_iff
  结论: {G : 类型} [InvolutiveInv G] [可测空间 G] [MeasurableInv G]
  证明: ⟨fun h => by simpa only [inv_inv] using h.fun_inv, fun h => h.inv⟩

@[to_additive (attr := simp)]

Depends on / 依赖: fun_inv, h.fun_inv, h.inv, inv_inv
-/
theorem measurable_inv_iff {G : Type*} [InvolutiveInv G] [MeasurableSpace G] [MeasurableInv G]
    {f : α -> G} : (Measurable fun x => (f x)⁻¹) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_inv] using h.fun_inv, fun h => h.inv⟩

@[to_additive (attr := simp)]
/--
theorem `aemeasurable_inv_iff` / 定理 `aemeasurable_inv_iff`

English:
theorem aemeasurable_inv_iff
  statement: {G : Type*} [InvolutiveInv G] [MeasurableSpace G] [MeasurableInv G]
  proof: ⟨fun h => by simpa only [inv_inv] using h.fun_inv, fun h => h.inv⟩

@[to_additive]

中文:
定理 aemeasurable_inv_iff
  结论: {G : 类型} [InvolutiveInv G] [可测空间 G] [MeasurableInv G]
  证明: ⟨fun h => by simpa only [inv_inv] using h.fun_inv, fun h => h.inv⟩

@[to_additive]

Depends on / 依赖: fun_inv, h.fun_inv, h.inv, inv_inv
-/
theorem aemeasurable_inv_iff {G : Type*} [InvolutiveInv G] [MeasurableSpace G] [MeasurableInv G]
    {f : α -> G} : AEMeasurable (fun x => (f x)⁻¹) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa only [inv_inv] using h.fun_inv, fun h => h.inv⟩

@[to_additive]
/--
Instance `Pi.measurableInv` / 实例 `Pi.measurableInv`

English:
instance Pi.measurableInv
  signature: {ι : Type*} {α : ι -> Type*} [forall i, Inv (α i)]
  body: ⟨measurable_pi_iff.mpr fun i => (measurable_pi_apply i).inv⟩

@[to_additive]

中文:
实例 依赖函数类型.measurableInv
  签名: {ι : 类型} {α : ι -> 类型} [对任意 i, 取逆 (α i)]
  定义体: ⟨measurable_pi_iff.mpr fun i => (measurable_pi_apply i).inv⟩

@[to_additive]

Depends on / 依赖: measurable_pi_apply, measurable_pi_iff, measurable_pi_iff.mpr
-/
instance Pi.measurableInv {ι : Type*} {α : ι -> Type*} [forall i, Inv (α i)]
    [forall i, MeasurableSpace (α i)] [forall i, MeasurableInv (α i)] : MeasurableInv (forall i, α i) :=
  ⟨measurable_pi_iff.mpr fun i => (measurable_pi_apply i).inv⟩

@[to_additive]
/--
theorem `MeasurableSet.inv` / 定理 `MeasurableSet.inv`

English:
theorem MeasurableSet.inv
  given: {s : Set G} (hs : MeasurableSet s)
  statement: MeasurableSet s⁻¹
  proof: measurable_inv hs

@[to_additive]

中文:
定理 可测集.inv
  条件: {s : 集合 G} (hs : 可测集 s)
  结论: 可测集 s⁻¹
  证明: measurable_inv hs

@[to_additive]

Depends on / 依赖: measurable_inv
-/
theorem MeasurableSet.inv {s : Set G} (hs : MeasurableSet s) : MeasurableSet s⁻¹ :=
  measurable_inv hs

@[to_additive]
/--
theorem `measurableEmbedding_inv` / 定理 `measurableEmbedding_inv`

English:
theorem measurableEmbedding_inv
  given: [InvolutiveInv α] [MeasurableInv α]
  proof: ⟨inv_injective, measurable_inv, fun s hs => s.image_inv_eq_inv ▸ hs.inv⟩

中文:
定理 measurableEmbedding_inv
  条件: [InvolutiveInv α] [MeasurableInv α]
  证明: ⟨inv_injective, measurable_inv, fun s hs => s.image_inv_eq_inv ▸ hs.inv⟩
-/
theorem measurableEmbedding_inv [InvolutiveInv α] [MeasurableInv α] :
    MeasurableEmbedding (Inv.inv (α := α)) :=
  ⟨inv_injective, measurable_inv, fun s hs => s.image_inv_eq_inv ▸ hs.inv⟩

end Inv

@[to_additive]
/--
theorem `Measurable.mul_iff_right` / 定理 `Measurable.mul_iff_right`

English:
theorem Measurable.mul_iff_right
  statement: {G : Type*} [MeasurableSpace G] [MeasurableSpace α] [CommGroup G]
  proof: ⟨fun h => show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h => hf.mul h⟩

@[to_additive]

中文:
定理 可测.mul_iff_right
  结论: {G : 类型} [可测空间 G] [可测空间 α] [交换群 G]
  证明: ⟨fun h => show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h => hf.mul h⟩

@[to_additive]

Depends on / 依赖: h.mul, hf.inv, hf.mul, mul_inv_cancel_comm
-/
theorem Measurable.mul_iff_right {G : Type*} [MeasurableSpace G] [MeasurableSpace α] [CommGroup G]
    [MeasurableMul₂ G] [MeasurableInv G] {f g : α -> G} (hf : Measurable f) :
    Measurable (f * g) ↔ Measurable g :=
  ⟨fun h => show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h => hf.mul h⟩

@[to_additive]
/--
theorem `AEMeasurable.mul_iff_right` / 定理 `AEMeasurable.mul_iff_right`

English:
theorem AEMeasurable.mul_iff_right
  statement: {G : Type*} [MeasurableSpace G] [MeasurableSpace α] [CommGroup G]
  proof: ⟨fun h => show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h => hf.mul h⟩

@[to_additive]

中文:
定理 几乎处处可测.mul_iff_right
  结论: {G : 类型} [可测空间 G] [可测空间 α] [交换群 G]
  证明: ⟨fun h => show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h => hf.mul h⟩

@[to_additive]

Depends on / 依赖: h.mul, hf.inv, hf.mul, mul_inv_cancel_comm
-/
theorem AEMeasurable.mul_iff_right {G : Type*} [MeasurableSpace G] [MeasurableSpace α] [CommGroup G]
    [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure α} {f g : α -> G} (hf : AEMeasurable f μ) :
    AEMeasurable (f * g) μ ↔ AEMeasurable g μ :=
  ⟨fun h => show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h => hf.mul h⟩

@[to_additive]
/--
theorem `Measurable.mul_iff_left` / 定理 `Measurable.mul_iff_left`

English:
theorem Measurable.mul_iff_left
  statement: {G : Type*} [MeasurableSpace G] [MeasurableSpace α] [CommGroup G]
  proof: mul_comm g f ▸ Measurable.mul_iff_right hf

@[to_additive]

中文:
定理 可测.mul_iff_left
  结论: {G : 类型} [可测空间 G] [可测空间 α] [交换群 G]
  证明: mul_comm g f ▸ Measurable.mul_iff_right hf

@[to_additive]

Depends on / 依赖: Measurable, Measurable.mul_iff_right, mul_comm, mul_iff_right
-/
theorem Measurable.mul_iff_left {G : Type*} [MeasurableSpace G] [MeasurableSpace α] [CommGroup G]
    [MeasurableMul₂ G] [MeasurableInv G] {f g : α -> G} (hf : Measurable f) :
    Measurable (g * f) ↔ Measurable g :=
  mul_comm g f ▸ Measurable.mul_iff_right hf

@[to_additive]
/--
theorem `AEMeasurable.mul_iff_left` / 定理 `AEMeasurable.mul_iff_left`

English:
theorem AEMeasurable.mul_iff_left
  statement: {G : Type*} [MeasurableSpace G] [MeasurableSpace α] [CommGroup G]
  proof: mul_comm g f ▸ AEMeasurable.mul_iff_right hf

中文:
定理 几乎处处可测.mul_iff_left
  结论: {G : 类型} [可测空间 G] [可测空间 α] [交换群 G]
  证明: mul_comm g f ▸ AEMeasurable.mul_iff_right hf

Depends on / 依赖: AEMeasurable, AEMeasurable.mul_iff_right, mul_comm, mul_iff_right
-/
theorem AEMeasurable.mul_iff_left {G : Type*} [MeasurableSpace G] [MeasurableSpace α] [CommGroup G]
    [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure α} {f g : α -> G} (hf : AEMeasurable f μ) :
    AEMeasurable (g * f) μ ↔ AEMeasurable g μ :=
  mul_comm g f ▸ AEMeasurable.mul_iff_right hf

/--
Instance `DivInvMonoid.measurableZPow` / 实例 `DivInvMonoid.measurableZPow`

English:
instance DivInvMonoid.measurableZPow
  signature: (G : Type u) [DivInvMonoid G] [MeasurableSpace G]
  body: ⟨measurable_from_prod_countable_left fun n => by
      rcases n with n | n
      · simp_rw [Int.ofNat_eq_natCast, zpow_natCast]
        exact measurable_id.pow_const _
      · simp_rw [zpow_negSucc]
        exact (measurable_id.pow_const (n + 1)).inv⟩

@[to_additive]

中文:
实例 除逆幺半群.measurableZPow
  签名: (G : 类型u) [除逆幺半群 G] [可测空间 G]
  定义体: ⟨measurable_from_prod_countable_left fun n => by
      rcases n with n | n
      · simp_rw [Int.ofNat_eq_natCast, zpow_natCast]
        exact measurable_id.pow_const _
      · simp_rw [zpow_negSucc]
        exact (measurable_id.pow_const (n + 1)).inv⟩

@[to_additive]

Depends on / 依赖: Int.ofNat_eq_natCast, measurable_from_prod_countable_left, measurable_id, measurable_id.pow_const, ofNat_eq_natCast, pow_const, simp_rw, zpow_natCast, zpow_negSucc
-/
instance DivInvMonoid.measurableZPow (G : Type u) [DivInvMonoid G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] : MeasurablePow G Int :=
  ⟨measurable_from_prod_countable_left fun n => by
      rcases n with n | n
      · simp_rw [Int.ofNat_eq_natCast, zpow_natCast]
        exact measurable_id.pow_const _
      · simp_rw [zpow_negSucc]
        exact (measurable_id.pow_const (n + 1)).inv⟩

@[to_additive]
instance (priority := 100) measurableDiv₂_of_mul_inv (G : Type*) [MeasurableSpace G]
    [DivInvMonoid G] [MeasurableMul₂ G] [MeasurableInv G] : MeasurableDiv₂ G :=
  ⟨by
    simp only [div_eq_mul_inv]
    exact measurable_fst.mul measurable_snd.inv⟩

-- See note [lower instance priority]
instance (priority := 100) MeasurableDiv.toMeasurableInv [MeasurableSpace α] [Group α]
    [MeasurableDiv α] : MeasurableInv α where
  measurable_inv := by simpa using measurable_const_div (1 : α)

/--
Definition of `MeasurableConstVAdd` / `MeasurableConstVAdd` 的定义

English:
class MeasurableConstVAdd
  parameters: (M α : Type*) [VAdd M α] [MeasurableSpace α]
  axioms and operations (1):
    - measurable_const_vadd : forall c : M, Measurable (c +ᵥ · : α -> α)

中文:
类 可测常数向量加法
  参数: (M α : 类型) [向量加法 M α] [可测空间 α]
  公理与运算 (1 个):
    - measurable_const_vadd : 对任意 c : M, 可测 (c +ᵥ · : α -> α)
-/
class MeasurableConstVAdd (M α : Type*) [VAdd M α] [MeasurableSpace α] : Prop where
  measurable_const_vadd : forall c : M, Measurable (c +ᵥ · : α -> α)

/-- We say that the action of `M` on `α` has `MeasurableConstSMul` if for each `c` the map
`x ↦ c • x` is a measurable function. -/
@[to_additive]
/--
Definition of `MeasurableConstSMul` / `MeasurableConstSMul` 的定义

English:
class MeasurableConstSMul
  parameters: (M α : Type*) [SMul M α] [MeasurableSpace α]
  axioms and operations (1):
    - measurable_const_smul : forall c : M, Measurable (c • · : α -> α)  [default: by measurability]

中文:
类 可测常数标量乘法
  参数: (M α : 类型) [标量乘法 M α] [可测空间 α]
  公理与运算 (1 个):
    - measurable_const_smul : 对任意 c : M, 可测 (c • · : α -> α)  [默认: by measurability]

Depends on / 依赖: measurability
-/
class MeasurableConstSMul (M α : Type*) [SMul M α] [MeasurableSpace α] : Prop where
  measurable_const_smul : forall c : M, Measurable (c • · : α -> α) := by measurability

/--
Definition of `MeasurableVAdd` / `MeasurableVAdd` 的定义

English:
class MeasurableVAdd
  parameters: (M α : Type*) [VAdd M α] [MeasurableSpace M] [MeasurableSpace α]
  extends: MeasurableConstVAdd M α
  axioms and operations (1):
    - measurable_vadd_const : forall x : α, Measurable (· +ᵥ x : M -> α)

中文:
类 可测向量加法
  参数: (M α : 类型) [向量加法 M α] [可测空间 M] [可测空间 α]
  继承: 可测常数向量加法 M α
  公理与运算 (1 个):
    - measurable_vadd_const : 对任意 x : α, 可测 (· +ᵥ x : M -> α)
-/
class MeasurableVAdd (M α : Type*) [VAdd M α] [MeasurableSpace M] [MeasurableSpace α]
    extends MeasurableConstVAdd M α where
  measurable_vadd_const : forall x : α, Measurable (· +ᵥ x : M -> α)

/-- We say that the action of `M` on `α` has `MeasurableSMul` if for each `c` the map `x ↦ c • x`
is a measurable function and for each `x` the map `c ↦ c • x` is a measurable function. -/
@[to_additive]
/--
Definition of `MeasurableSMul` / `MeasurableSMul` 的定义

English:
class MeasurableSMul
  parameters: (M α : Type*) [SMul M α] [MeasurableSpace M] [MeasurableSpace α]
  extends: MeasurableConstSMul M α
  axioms and operations (1):
    - measurable_smul_const : forall x : α, Measurable (· • x : M -> α)  [default: by measurability]

中文:
类 可测标量乘法
  参数: (M α : 类型) [标量乘法 M α] [可测空间 M] [可测空间 α]
  继承: 可测常数标量乘法 M α
  公理与运算 (1 个):
    - measurable_smul_const : 对任意 x : α, 可测 (· • x : M -> α)  [默认: by measurability]

Depends on / 依赖: measurability
-/
class MeasurableSMul (M α : Type*) [SMul M α] [MeasurableSpace M] [MeasurableSpace α]
    extends MeasurableConstSMul M α where
  measurable_smul_const : forall x : α, Measurable (· • x : M -> α) := by measurability

/--
Definition of `MeasurableVAdd₂` / `MeasurableVAdd₂` 的定义

English:
class MeasurableVAdd₂
  parameters: (M α : Type*) [VAdd M α] [MeasurableSpace M] [MeasurableSpace α]
  axioms and operations (1):
    - measurable_vadd : Measurable (Function.uncurry (· +ᵥ ·) : M × α -> α)

中文:
类 MeasurableVAdd₂
  参数: (M α : 类型) [向量加法 M α] [可测空间 M] [可测空间 α]
  公理与运算 (1 个):
    - measurable_vadd : 可测 (函数.uncurry (· +ᵥ ·) : M × α -> α)
-/
class MeasurableVAdd₂ (M α : Type*) [VAdd M α] [MeasurableSpace M] [MeasurableSpace α] :
    Prop where
  measurable_vadd : Measurable (Function.uncurry (· +ᵥ ·) : M × α -> α)

/-- We say that the action of `M` on `α` has `MeasurableSMul₂` if the map
`(c, x) ↦ c • x` is a measurable function. -/
@[to_additive MeasurableVAdd₂]
/--
Definition of `MeasurableSMul₂` / `MeasurableSMul₂` 的定义

English:
class MeasurableSMul₂
  parameters: (M α : Type*) [SMul M α] [MeasurableSpace M] [MeasurableSpace α]
  axioms and operations (1):
    - measurable_smul : Measurable (Function.uncurry (· • ·) : M × α -> α)

中文:
类 MeasurableSMul₂
  参数: (M α : 类型) [标量乘法 M α] [可测空间 M] [可测空间 α]
  公理与运算 (1 个):
    - measurable_smul : 可测 (函数.uncurry (· • ·) : M × α -> α)
-/
class MeasurableSMul₂ (M α : Type*) [SMul M α] [MeasurableSpace M] [MeasurableSpace α] :
    Prop where
  measurable_smul : Measurable (Function.uncurry (· • ·) : M × α -> α)

export MeasurableConstVAdd (measurable_const_vadd)
export MeasurableConstSMul (measurable_const_smul)
export MeasurableVAdd (measurable_vadd_const)
export MeasurableSMul (measurable_smul_const)
export MeasurableSMul₂ (measurable_smul)
export MeasurableVAdd₂ (measurable_vadd)

@[to_additive]
/--
Instance `measurableSMul_of_mul` / 实例 `measurableSMul_of_mul`

English:
instance measurableSMul_of_mul
  signature: (M : Type*) [Mul M] [MeasurableSpace M] [MeasurableMul M]

中文:
实例 measurableSMul_of_mul
  签名: (M : 类型) [乘法 M] [可测空间 M] [MeasurableMul M]
-/
instance measurableSMul_of_mul (M : Type*) [Mul M] [MeasurableSpace M] [MeasurableMul M] :
    MeasurableSMul M M where

@[to_additive]
/--
Instance `measurableSMul₂_of_mul` / 实例 `measurableSMul₂_of_mul`

English:
instance measurableSMul₂_of_mul
  signature: (M : Type*) [Mul M] [MeasurableSpace M] [MeasurableMul₂ M]
  body: ⟨measurable_mul⟩

@[to_additive]

中文:
实例 measurableSMul₂_of_mul
  签名: (M : 类型) [乘法 M] [可测空间 M] [MeasurableMul₂ M]
  定义体: ⟨measurable_mul⟩

@[to_additive]

Depends on / 依赖: measurable_mul
-/
instance measurableSMul₂_of_mul (M : Type*) [Mul M] [MeasurableSpace M] [MeasurableMul₂ M] :
    MeasurableSMul₂ M M :=
  ⟨measurable_mul⟩

@[to_additive]
/--
Instance `Submonoid.instMeasurableConstSMul` / 实例 `Submonoid.instMeasurableConstSMul`

English:
instance Submonoid.instMeasurableConstSMul
  signature: {M α} [MeasurableSpace α] [Monoid M] [MulAction M α]
  body: by simpa only using! measurable_const_smul (c : M)

@[to_additive]

中文:
实例 子幺半群.instMeasurableConstSMul
  签名: {M α} [可测空间 α] [幺半群 M] [乘法作用 M α]
  定义体: by simpa only using! measurable_const_smul (c : M)

@[to_additive]

Depends on / 依赖: measurable_const_smul
-/
instance Submonoid.instMeasurableConstSMul {M α} [MeasurableSpace α] [Monoid M] [MulAction M α]
    [MeasurableConstSMul M α] (s : Submonoid M) : MeasurableConstSMul s α where
  measurable_const_smul c := by simpa only using! measurable_const_smul (c : M)

@[to_additive]
/--
Instance `Submonoid.instMeasurableSMul` / 实例 `Submonoid.instMeasurableSMul`

English:
instance Submonoid.instMeasurableSMul
  signature: {M α} [MeasurableSpace M] [MeasurableSpace α] [Monoid M]
  body: (measurable_smul_const (M := M) x).comp measurable_subtype_coe

@[to_additive]

中文:
实例 子幺半群.instMeasurableSMul
  签名: {M α} [可测空间 M] [可测空间 α] [幺半群 M]
  定义体: (measurable_smul_const (M := M) x).comp measurable_subtype_coe

@[to_additive]

Depends on / 依赖: measurable_smul_const, measurable_subtype_coe
-/
instance Submonoid.instMeasurableSMul {M α} [MeasurableSpace M] [MeasurableSpace α] [Monoid M]
    [MulAction M α] [MeasurableSMul M α] (s : Submonoid M) : MeasurableSMul s α where
  measurable_smul_const x := (measurable_smul_const (M := M) x).comp measurable_subtype_coe

@[to_additive]
/--
Instance `Subgroup.instMeasurableConstSMul` / 实例 `Subgroup.instMeasurableConstSMul`

English:
instance Subgroup.instMeasurableConstSMul
  signature: {G α} [MeasurableSpace α] [Group G] [MulAction G α]
  body: s.toSubmonoid.instMeasurableConstSMul

@[to_additive]

中文:
实例 子群.instMeasurableConstSMul
  签名: {G α} [可测空间 α] [群 G] [乘法作用 G α]
  定义体: s.toSubmonoid.instMeasurableConstSMul

@[to_additive]

Depends on / 依赖: instMeasurableConstSMul, s.toSubmonoid.instMeasurableConstSMul, toSubmonoid
-/
instance Subgroup.instMeasurableConstSMul {G α} [MeasurableSpace α] [Group G] [MulAction G α]
    [MeasurableConstSMul G α] (s : Subgroup G) : MeasurableConstSMul s α :=
  s.toSubmonoid.instMeasurableConstSMul

@[to_additive]
/--
Instance `Subgroup.instMeasurableSMul` / 实例 `Subgroup.instMeasurableSMul`

English:
instance Subgroup.instMeasurableSMul
  signature: {G α} [MeasurableSpace G] [MeasurableSpace α] [Group G]
  body: s.toSubmonoid.instMeasurableSMul

中文:
实例 子群.instMeasurableSMul
  签名: {G α} [可测空间 G] [可测空间 α] [群 G]
  定义体: s.toSubmonoid.instMeasurableSMul

Depends on / 依赖: instMeasurableSMul, s.toSubmonoid.instMeasurableSMul, toSubmonoid
-/
instance Subgroup.instMeasurableSMul {G α} [MeasurableSpace G] [MeasurableSpace α] [Group G]
    [MulAction G α] [MeasurableSMul G α] (s : Subgroup G) : MeasurableSMul s α :=
  s.toSubmonoid.instMeasurableSMul

section SMul
variable {M X α β : Type*} [MeasurableSpace X] [SMul M X]
  {m : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} {f : α -> M} {g : α -> X}

section MeasurableConstSMul
variable [MeasurableConstSMul M X]

@[to_additive (attr := to_fun (attr := fun_prop))]
/--
lemma `Measurable.const_smul` / 引理 `Measurable.const_smul`

English:
lemma Measurable.const_smul
  given: (hg : Measurable g) (c : M)
  statement: Measurable (c • g)
  proof: (measurable_const_smul c).comp hg

@[to_additive (attr := to_fun (attr := fun_prop))]

中文:
引理 可测.const_smul
  条件: (hg : 可测 g) (c : M)
  结论: 可测 (c • g)
  证明: (measurable_const_smul c).comp hg

@[to_additive (attr := to_fun (attr := fun_prop))]

Depends on / 依赖: measurable_const_smul
-/
lemma Measurable.const_smul (hg : Measurable g) (c : M) : Measurable (c • g) :=
  (measurable_const_smul c).comp hg

@[to_additive (attr := to_fun (attr := fun_prop))]
/--
lemma `AEMeasurable.const_smul` / 引理 `AEMeasurable.const_smul`

English:
lemma AEMeasurable.const_smul
  given: (hg : AEMeasurable g μ) (c : M)
  statement: AEMeasurable (c • g) μ
  proof: (measurable_const_smul c).comp_aemeasurable hg

@[to_additive]

中文:
引理 几乎处处可测.const_smul
  条件: (hg : 几乎处处可测 g μ) (c : M)
  结论: 几乎处处可测 (c • g) μ
  证明: (measurable_const_smul c).comp_aemeasurable hg

@[to_additive]

Depends on / 依赖: comp_aemeasurable, measurable_const_smul
-/
lemma AEMeasurable.const_smul (hg : AEMeasurable g μ) (c : M) : AEMeasurable (c • g) μ :=
  (measurable_const_smul c).comp_aemeasurable hg

@[to_additive]
/--
Instance `Pi.instMeasurableConstSMul` / 实例 `Pi.instMeasurableConstSMul`

English:
instance Pi.instMeasurableConstSMul
  signature: {ι : Type*} {α : ι -> Type*} [forall i, SMul M (α i)]
  body: measurable_pi_iff.2 fun i => (measurable_pi_apply i).const_smul _

中文:
实例 依赖函数类型.instMeasurableConstSMul
  签名: {ι : 类型} {α : ι -> 类型} [对任意 i, 标量乘法 M (α i)]
  定义体: measurable_pi_iff.2 fun i => (measurable_pi_apply i).const_smul _

Depends on / 依赖: const_smul, measurable_pi_apply, measurable_pi_iff
-/
instance Pi.instMeasurableConstSMul {ι : Type*} {α : ι -> Type*} [forall i, SMul M (α i)]
    [forall i, MeasurableSpace (α i)] [forall i, MeasurableConstSMul M (α i)] :
    MeasurableConstSMul M (forall i, α i) where
  measurable_const_smul _ := measurable_pi_iff.2 fun i => (measurable_pi_apply i).const_smul _

/-- If a scalar is central, then its right action is measurable when its left action is. -/
@[to_additive /-- If a vector is central, then its right action is measurable when its left
action is. -/]
nonrec instance MulOpposite.instMeasurableConstSMul [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [MeasurableConstSMul M α] : MeasurableConstSMul Mᵐᵒᵖ α where
  measurable_const_smul := by simpa using measurable_const_smul

end MeasurableConstSMul

variable [MeasurableSpace M]

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `Measurable.smul` / 定理 `Measurable.smul`

English:
theorem Measurable.smul
  given: [MeasurableSMul₂ M X] (hf : Measurable f) (hg : Measurable g)
  proof: measurable_smul.comp (hf.prodMk hg)

中文:
定理 可测.smul
  条件: [MeasurableSMul₂ M X] (hf : 可测 f) (hg : 可测 g)
  证明: measurable_smul.comp (hf.prodMk hg)

Depends on / 依赖: hf.prodMk, measurable_smul, measurable_smul.comp, prodMk
-/
theorem Measurable.smul [MeasurableSMul₂ M X] (hf : Measurable f) (hg : Measurable g) :
    Measurable (f • g) :=
  measurable_smul.comp (hf.prodMk hg)

/-- Compositional version of `Measurable.smul` for use by `fun_prop`. -/
@[to_additive (attr := fun_prop)
/-- Compositional version of `Measurable.vadd` for use by `fun_prop`. -/]
/--
lemma `Measurable.smul'` / 引理 `Measurable.smul'`

English:
lemma Measurable.smul'
  statement: [MeasurableSMul₂ M X] {f : α -> β -> M} {g : α -> β -> X} {h : α -> β}
  proof: by dsimp; fun_prop

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
引理 可测.smul'
  结论: [MeasurableSMul₂ M X] {f : α -> β -> M} {g : α -> β -> X} {h : α -> β}
  证明: by dsimp; fun_prop

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: fun_prop
-/
lemma Measurable.smul' [MeasurableSMul₂ M X] {f : α -> β -> M} {g : α -> β -> X} {h : α -> β}
    (hf : Measurable ↿f) (hg : Measurable ↿g) (hh : Measurable h) :
    Measurable fun a => (f a • g a) (h a) := by dsimp; fun_prop

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `AEMeasurable.smul` / 定理 `AEMeasurable.smul`

English:
theorem AEMeasurable.smul
  statement: [MeasurableSMul₂ M X] {μ : Measure α} (hf : AEMeasurable f μ)
  proof: MeasurableSMul₂.measurable_smul.comp_aemeasurable (hf.prodMk hg)

@[to_additive]

中文:
定理 几乎处处可测.smul
  结论: [MeasurableSMul₂ M X] {μ : 测度 α} (hf : 几乎处处可测 f μ)
  证明: MeasurableSMul₂.measurable_smul.comp_aemeasurable (hf.prodMk hg)

@[to_additive]

Depends on / 依赖: comp_aemeasurable, hf.prodMk, measurable_smul, measurable_smul.comp_aemeasurable, prodMk
-/
theorem AEMeasurable.smul [MeasurableSMul₂ M X] {μ : Measure α} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (f • g) μ :=
  MeasurableSMul₂.measurable_smul.comp_aemeasurable (hf.prodMk hg)

@[to_additive]
instance (priority := 100) MeasurableSMul₂.toMeasurableSMul [MeasurableSMul₂ M X] :
    MeasurableSMul M X where

variable [MeasurableSMul M X]

@[to_additive (attr := fun_prop)]
/--
theorem `Measurable.smul_const` / 定理 `Measurable.smul_const`

English:
theorem Measurable.smul_const
  given: (hf : Measurable f) (y : X)
  statement: Measurable fun x => f x • y
  proof: (MeasurableSMul.measurable_smul_const y).comp hf

@[to_additive (attr := fun_prop)]

中文:
定理 可测.smul_const
  条件: (hf : 可测 f) (y : X)
  结论: 可测 fun x => f x • y
  证明: (MeasurableSMul.measurable_smul_const y).comp hf

@[to_additive (attr := fun_prop)]

Depends on / 依赖: MeasurableSMul, MeasurableSMul.measurable_smul_const, measurable_smul_const
-/
theorem Measurable.smul_const (hf : Measurable f) (y : X) : Measurable fun x => f x • y :=
  (MeasurableSMul.measurable_smul_const y).comp hf

@[to_additive (attr := fun_prop)]
/--
theorem `AEMeasurable.smul_const` / 定理 `AEMeasurable.smul_const`

English:
theorem AEMeasurable.smul_const
  given: (hf : AEMeasurable f μ) (y : X)
  proof: by fun_prop

@[to_additive]

中文:
定理 几乎处处可测.smul_const
  条件: (hf : 几乎处处可测 f μ) (y : X)
  证明: by fun_prop

@[to_additive]

Depends on / 依赖: fun_prop
-/
theorem AEMeasurable.smul_const (hf : AEMeasurable f μ) (y : X) :
    AEMeasurable (fun x => f x • y) μ := by fun_prop

@[to_additive]
/--
Instance `Pi.measurableSMul` / 实例 `Pi.measurableSMul`

English:
instance Pi.measurableSMul
  signature: {ι : Type*} {α : ι -> Type*} [forall i, SMul M (α i)]
  body: measurable_pi_iff.2 fun _ => measurable_smul_const _

中文:
实例 依赖函数类型.measurableSMul
  签名: {ι : 类型} {α : ι -> 类型} [对任意 i, 标量乘法 M (α i)]
  定义体: measurable_pi_iff.2 fun _ => measurable_smul_const _

Depends on / 依赖: measurable_pi_iff, measurable_smul_const
-/
instance Pi.measurableSMul {ι : Type*} {α : ι -> Type*} [forall i, SMul M (α i)]
    [forall i, MeasurableSpace (α i)] [forall i, MeasurableSMul M (α i)] :
    MeasurableSMul M (forall i, α i) where
  measurable_smul_const _ := measurable_pi_iff.2 fun _ => measurable_smul_const _

/--
Instance `AddMonoid.measurableSMul_nat₂` / 实例 `AddMonoid.measurableSMul_nat₂`

English:
instance AddMonoid.measurableSMul_nat₂
  signature: (M : Type*) [AddMonoid M] [MeasurableSpace M]
  body: ⟨by
    suffices Measurable fun p : M × Nat => p.2 • p.1 by apply this.comp measurable_swap
    refine measurable_from_prod_countable_left fun n => ?_
    induction n with
    | zero => simp only [zero_smul, ← Pi.zero_def, measurable_zero]
    | succ n ih =>
      simp only [succ_nsmul]
      exact ih.add measurable_id⟩

中文:
实例 加法幺半群.measurableSMul_nat₂
  签名: (M : 类型) [加法幺半群 M] [可测空间 M]
  定义体: ⟨by
    suffices Measurable fun p : M × Nat => p.2 • p.1 by apply this.comp measurable_swap
    refine measurable_from_prod_countable_left fun n => ?_
    induction n with
    | zero => simp only [zero_smul, ← Pi.zero_def, measurable_zero]
    | succ n ih =>
      simp only [succ_nsmul]
      exact ih.add measurable_id⟩

Depends on / 依赖: Measurable, Pi.zero_def, ih.add, measurable_from_prod_countable_left, measurable_id, measurable_swap, measurable_zero, succ_nsmul, this.comp, zero_def, zero_smul
-/
instance AddMonoid.measurableSMul_nat₂ (M : Type*) [AddMonoid M] [MeasurableSpace M]
    [MeasurableAdd₂ M] : MeasurableSMul₂ Nat M :=
  ⟨by
    suffices Measurable fun p : M × Nat => p.2 • p.1 by apply this.comp measurable_swap
    refine measurable_from_prod_countable_left fun n => ?_
    induction n with
    | zero => simp only [zero_smul, ← Pi.zero_def, measurable_zero]
    | succ n ih =>
      simp only [succ_nsmul]
      exact ih.add measurable_id⟩

/--
Instance `SubNegMonoid.measurableSMul_int₂` / 实例 `SubNegMonoid.measurableSMul_int₂`

English:
instance SubNegMonoid.measurableSMul_int₂
  signature: (M : Type*) [SubNegMonoid M] [MeasurableSpace M]
  body: ⟨by
    suffices Measurable fun p : M × Int => p.2 • p.1 by apply this.comp measurable_swap
    refine measurable_from_prod_countable_left fun n => ?_
    cases n with
    | ofNat n =>
      simp only [Int.ofNat_eq_natCast, natCast_zsmul]
      exact measurable_const_smul _
    | negSucc n =>
      simp only [negSucc_zsmul]
      exact (measurable_const_smul _).neg⟩

中文:
实例 SubNeg幺半群.measurableSMul_int₂
  签名: (M : 类型) [SubNeg幺半群 M] [可测空间 M]
  定义体: ⟨by
    suffices Measurable fun p : M × Int => p.2 • p.1 by apply this.comp measurable_swap
    refine measurable_from_prod_countable_left fun n => ?_
    cases n with
    | ofNat n =>
      simp only [Int.ofNat_eq_natCast, natCast_zsmul]
      exact measurable_const_smul _
    | negSucc n =>
      simp only [negSucc_zsmul]
      exact (measurable_const_smul _).neg⟩

Depends on / 依赖: Int.ofNat_eq_natCast, Measurable, measurable_const_smul, measurable_from_prod_countable_left, measurable_swap, natCast_zsmul, negSucc, negSucc_zsmul, ofNat_eq_natCast, this.comp
-/
instance SubNegMonoid.measurableSMul_int₂ (M : Type*) [SubNegMonoid M] [MeasurableSpace M]
    [MeasurableAdd₂ M] [MeasurableNeg M] : MeasurableSMul₂ Int M :=
  ⟨by
    suffices Measurable fun p : M × Int => p.2 • p.1 by apply this.comp measurable_swap
    refine measurable_from_prod_countable_left fun n => ?_
    cases n with
    | ofNat n =>
      simp only [Int.ofNat_eq_natCast, natCast_zsmul]
      exact measurable_const_smul _
    | negSucc n =>
      simp only [negSucc_zsmul]
      exact (measurable_const_smul _).neg⟩

end SMul

section IterateMulAct

variable {α : Type*} {_ : MeasurableSpace α} {f : α -> α}

@[to_additive]
/--
theorem `Measurable.measurableSMul₂_iterateMulAct` / 定理 `Measurable.measurableSMul₂_iterateMulAct`

English:
theorem Measurable.measurableSMul₂_iterateMulAct
  given: (h : Measurable f)
  proof: suffices Measurable fun p : α × IterateMulAct f => f^[p.2.val] p.1 from this.comp measurable_swap
    measurable_from_prod_countable_left fun n => h.iterate n.val

@[to_additive (attr := simp)]

中文:
定理 可测.measurableSMul₂_iterateMulAct
  条件: (h : 可测 f)
  证明: suffices Measurable fun p : α × IterateMulAct f => f^[p.2.val] p.1 from this.comp measurable_swap
    measurable_from_prod_countable_left fun n => h.iterate n.val

@[to_additive (attr := simp)]

Depends on / 依赖: IterateMulAct, Measurable, h.iterate, iterate, measurable_from_prod_countable_left, measurable_swap, n.val, this.comp
-/
theorem Measurable.measurableSMul₂_iterateMulAct (h : Measurable f) :
    MeasurableSMul₂ (IterateMulAct f) α where
  measurable_smul :=
    suffices Measurable fun p : α × IterateMulAct f => f^[p.2.val] p.1 from this.comp measurable_swap
    measurable_from_prod_countable_left fun n => h.iterate n.val

@[to_additive (attr := simp)]
/--
theorem `measurableSMul_iterateMulAct` / 定理 `measurableSMul_iterateMulAct`

English:
theorem measurableSMul_iterateMulAct
  statement: MeasurableSMul (IterateMulAct f) α ↔ Measurable f
  proof: ⟨fun _ => measurable_const_smul (IterateMulAct.mk (f := f) 1), fun h =>
    have := h.measurableSMul₂_iterateMulAct; inferInstance⟩

@[to_additive (attr := simp)]

中文:
定理 measurableSMul_iterateMulAct
  结论: 可测标量乘法 (IterateMulAct f) α ↔ 可测 f
  证明: ⟨fun _ => measurable_const_smul (IterateMulAct.mk (f := f) 1), fun h =>
    have := h.measurableSMul₂_iterateMulAct; inferInstance⟩

@[to_additive (attr := simp)]

Depends on / 依赖: IterateMulAct, IterateMulAct.mk, h.measurableSMul, measurable_const_smul
-/
theorem measurableSMul_iterateMulAct : MeasurableSMul (IterateMulAct f) α ↔ Measurable f :=
  ⟨fun _ => measurable_const_smul (IterateMulAct.mk (f := f) 1), fun h =>
    have := h.measurableSMul₂_iterateMulAct; inferInstance⟩

@[to_additive (attr := simp)]
/--
theorem `measurableSMul₂_iterateMulAct` / 定理 `measurableSMul₂_iterateMulAct`

English:
theorem measurableSMul₂_iterateMulAct
  statement: MeasurableSMul₂ (IterateMulAct f) α ↔ Measurable f
  proof: ⟨fun _ => measurableSMul_iterateMulAct.mp inferInstance,
    Measurable.measurableSMul₂_iterateMulAct⟩

中文:
定理 measurableSMul₂_iterateMulAct
  结论: MeasurableSMul₂ (IterateMulAct f) α ↔ 可测 f
  证明: ⟨fun _ => measurableSMul_iterateMulAct.mp inferInstance,
    Measurable.measurableSMul₂_iterateMulAct⟩

Depends on / 依赖: Measurable, Measurable.measurableSMul, measurableSMul_iterateMulAct, measurableSMul_iterateMulAct.mp
-/
theorem measurableSMul₂_iterateMulAct : MeasurableSMul₂ (IterateMulAct f) α ↔ Measurable f :=
  ⟨fun _ => measurableSMul_iterateMulAct.mp inferInstance,
    Measurable.measurableSMul₂_iterateMulAct⟩

end IterateMulAct

section MulAction
variable {G G₀ M β α : Type*} [MeasurableSpace β] [MeasurableSpace α] {f : α -> β} {μ : Measure α}

section Group
variable {G : Type*} [Group G] [MulAction G β] [MeasurableConstSMul G β]

@[to_additive]
/--
theorem `measurable_const_smul_iff` / 定理 `measurable_const_smul_iff`

English:
theorem measurable_const_smul_iff
  given: (c : G)
  statement: (Measurable fun x => c • f x) ↔ Measurable f
  proof: ⟨fun h => by simpa [inv_smul_smul, Pi.smul_def] using h.const_smul c⁻¹, fun h => h.const_smul c⟩

@[to_additive]

中文:
定理 measurable_const_smul_iff
  条件: (c : G)
  结论: (可测 fun x => c • f x) ↔ 可测 f
  证明: ⟨fun h => by simpa [inv_smul_smul, Pi.smul_def] using h.const_smul c⁻¹, fun h => h.const_smul c⟩

@[to_additive]

Depends on / 依赖: Pi.smul_def, const_smul, h.const_smul, inv_smul_smul, smul_def
-/
theorem measurable_const_smul_iff (c : G) : (Measurable fun x => c • f x) ↔ Measurable f :=
  ⟨fun h => by simpa [inv_smul_smul, Pi.smul_def] using h.const_smul c⁻¹, fun h => h.const_smul c⟩

@[to_additive]
/--
theorem `aemeasurable_const_smul_iff` / 定理 `aemeasurable_const_smul_iff`

English:
theorem aemeasurable_const_smul_iff
  given: (c : G)
  proof: ⟨fun h => by simpa [inv_smul_smul, Pi.smul_def] using h.const_smul c⁻¹, fun h => h.const_smul c⟩

中文:
定理 aemeasurable_const_smul_iff
  条件: (c : G)
  证明: ⟨fun h => by simpa [inv_smul_smul, Pi.smul_def] using h.const_smul c⁻¹, fun h => h.const_smul c⟩

Depends on / 依赖: Pi.smul_def, const_smul, h.const_smul, inv_smul_smul, smul_def
-/
theorem aemeasurable_const_smul_iff (c : G) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa [inv_smul_smul, Pi.smul_def] using h.const_smul c⁻¹, fun h => h.const_smul c⟩

end Group

section Monoid
variable [Monoid M] [MulAction M β]

section MeasurableConstSMul
variable [MeasurableConstSMul M β]

@[to_additive]
/--
Instance `Units.instMeasurableConstSMul` / 实例 `Units.instMeasurableConstSMul`

English:
instance Units.instMeasurableConstSMul
  signature: : MeasurableConstSMul Mˣ β where
  body: measurable_const_smul (c : M)

@[to_additive]
nonrec theorem IsUnit.measurable_const_smul_iff {c : M} (hc : IsUnit c) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ measurable_const_smul_iff u

@[to_additive]
nonrec theorem IsUnit.aemeasurable_const_smul_iff {c : M} (hc : IsUnit c) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ aemeasurable_const_smul_iff u

中文:
实例 单位群.instMeasurableConstSMul
  签名: : 可测常数标量乘法 Mˣ β where
  定义体: measurable_const_smul (c : M)

@[to_additive]
nonrec theorem IsUnit.measurable_const_smul_iff {c : M} (hc : IsUnit c) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ measurable_const_smul_iff u

@[to_additive]
nonrec theorem IsUnit.aemeasurable_const_smul_iff {c : M} (hc : IsUnit c) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ aemeasurable_const_smul_iff u

Depends on / 依赖: measurable_const_smul
-/
instance Units.instMeasurableConstSMul : MeasurableConstSMul Mˣ β where
  measurable_const_smul c := measurable_const_smul (c : M)

@[to_additive]
nonrec theorem IsUnit.measurable_const_smul_iff {c : M} (hc : IsUnit c) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ measurable_const_smul_iff u

@[to_additive]
nonrec theorem IsUnit.aemeasurable_const_smul_iff {c : M} (hc : IsUnit c) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ aemeasurable_const_smul_iff u

end MeasurableConstSMul

section MeasurableSMul
variable [MeasurableSpace M] [MeasurableSMul M β]

@[to_additive]
/--
Instance `Units.instMeasurableSpace` / 实例 `Units.instMeasurableSpace`

English:
instance Units.instMeasurableSpace
  signature: : MeasurableSpace Mˣ
  body: .comap Units.val ‹_›

@[to_additive]

中文:
实例 单位群.instMeasurableSpace
  签名: : 可测空间 Mˣ
  定义体: .comap Units.val ‹_›

@[to_additive]

Depends on / 依赖: Units.val
-/
instance Units.instMeasurableSpace : MeasurableSpace Mˣ := .comap Units.val ‹_›

@[to_additive]
/--
Instance `Units.measurableSMul` / 实例 `Units.measurableSMul`

English:
instance Units.measurableSMul
  signature: : MeasurableSMul Mˣ β where
  body: (measurable_smul_const x : Measurable fun c : M => c • x).comp MeasurableSpace.le_map_comap

中文:
实例 单位群.measurableSMul
  签名: : 可测标量乘法 Mˣ β where
  定义体: (measurable_smul_const x : Measurable fun c : M => c • x).comp MeasurableSpace.le_map_comap

Depends on / 依赖: Measurable, MeasurableSpace, MeasurableSpace.le_map_comap, le_map_comap, measurable_smul_const
-/
instance Units.measurableSMul : MeasurableSMul Mˣ β where
  measurable_smul_const x :=
    (measurable_smul_const x : Measurable fun c : M => c • x).comp MeasurableSpace.le_map_comap

end MeasurableSMul
end Monoid

section GroupWithZero
variable [GroupWithZero G₀] [MulAction G₀ β] [MeasurableConstSMul G₀ β]

/--
theorem `measurable_const_smul_iff₀` / 定理 `measurable_const_smul_iff₀`

English:
theorem measurable_const_smul_iff₀
  given: {c : G₀} (hc : c != 0)
  proof: (IsUnit.mk0 c hc).measurable_const_smul_iff

中文:
定理 measurable_const_smul_iff₀
  条件: {c : G₀} (hc : c != 0)
  证明: (IsUnit.mk0 c hc).measurable_const_smul_iff

Depends on / 依赖: IsUnit, IsUnit.mk0, measurable_const_smul_iff
-/
theorem measurable_const_smul_iff₀ {c : G₀} (hc : c != 0) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  (IsUnit.mk0 c hc).measurable_const_smul_iff

/--
theorem `aemeasurable_const_smul_iff₀` / 定理 `aemeasurable_const_smul_iff₀`

English:
theorem aemeasurable_const_smul_iff₀
  given: {c : G₀} (hc : c != 0)
  proof: (IsUnit.mk0 c hc).aemeasurable_const_smul_iff

中文:
定理 aemeasurable_const_smul_iff₀
  条件: {c : G₀} (hc : c != 0)
  证明: (IsUnit.mk0 c hc).aemeasurable_const_smul_iff

Depends on / 依赖: IsUnit, IsUnit.mk0, aemeasurable_const_smul_iff
-/
theorem aemeasurable_const_smul_iff₀ {c : G₀} (hc : c != 0) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  (IsUnit.mk0 c hc).aemeasurable_const_smul_iff

end GroupWithZero
end MulAction

/-!
### Opposite monoid
-/


section Opposite

open MulOpposite

@[to_additive]
/--
Instance `MulOpposite.instMeasurableSpace` / 实例 `MulOpposite.instMeasurableSpace`

English:
instance MulOpposite.instMeasurableSpace
  signature: {α : Type*} [h : MeasurableSpace α]
  body: MeasurableSpace.map op h

@[to_additive]

中文:
实例 MulOpposite.instMeasurableSpace
  签名: {α : 类型} [h : 可测空间 α]
  定义体: MeasurableSpace.map op h

@[to_additive]

Depends on / 依赖: MeasurableSpace, MeasurableSpace.map
-/
instance MulOpposite.instMeasurableSpace {α : Type*} [h : MeasurableSpace α] :
    MeasurableSpace αᵐᵒᵖ :=
  MeasurableSpace.map op h

@[to_additive]
/--
theorem `measurable_mul_op` / 定理 `measurable_mul_op`

English:
theorem measurable_mul_op
  given: {α : Type*} [MeasurableSpace α]
  statement: Measurable (op : α -> αᵐᵒᵖ)
  proof: fun _ =>
  id

@[to_additive]

中文:
定理 measurable_mul_op
  条件: {α : 类型} [可测空间 α]
  结论: 可测 (op : α -> αᵐᵒᵖ)
  证明: fun _ =>
  id

@[to_additive]
-/
theorem measurable_mul_op {α : Type*} [MeasurableSpace α] : Measurable (op : α -> αᵐᵒᵖ) := fun _ =>
  id

@[to_additive]
/--
theorem `measurable_mul_unop` / 定理 `measurable_mul_unop`

English:
theorem measurable_mul_unop
  given: {α : Type*} [MeasurableSpace α]
  statement: Measurable (unop : αᵐᵒᵖ -> α)
  proof: fun _ => id

@[to_additive]

中文:
定理 measurable_mul_unop
  条件: {α : 类型} [可测空间 α]
  结论: 可测 (unop : αᵐᵒᵖ -> α)
  证明: fun _ => id

@[to_additive]
-/
theorem measurable_mul_unop {α : Type*} [MeasurableSpace α] : Measurable (unop : αᵐᵒᵖ -> α) :=
  fun _ => id

@[to_additive]
/--
Instance `MulOpposite.instMeasurableMul` / 实例 `MulOpposite.instMeasurableMul`

English:
instance MulOpposite.instMeasurableMul
  signature: {M : Type*} [Mul M] [MeasurableSpace M]
  body: ⟨fun _ => measurable_mul_op.comp (measurable_mul_unop.mul_const _), fun _ =>
    measurable_mul_op.comp (measurable_mul_unop.const_mul _)⟩

@[to_additive]

中文:
实例 MulOpposite.instMeasurableMul
  签名: {M : 类型} [乘法 M] [可测空间 M]
  定义体: ⟨fun _ => measurable_mul_op.comp (measurable_mul_unop.mul_const _), fun _ =>
    measurable_mul_op.comp (measurable_mul_unop.const_mul _)⟩

@[to_additive]

Depends on / 依赖: const_mul, measurable_mul_op, measurable_mul_op.comp, measurable_mul_unop, measurable_mul_unop.const_mul, measurable_mul_unop.mul_const, mul_const
-/
instance MulOpposite.instMeasurableMul {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul M] : MeasurableMul Mᵐᵒᵖ :=
  ⟨fun _ => measurable_mul_op.comp (measurable_mul_unop.mul_const _), fun _ =>
    measurable_mul_op.comp (measurable_mul_unop.const_mul _)⟩

@[to_additive]
/--
Instance `MulOpposite.instMeasurableMul₂` / 实例 `MulOpposite.instMeasurableMul₂`

English:
instance MulOpposite.instMeasurableMul₂
  signature: {M : Type*} [Mul M] [MeasurableSpace M]
  body: ⟨measurable_mul_op.comp
      ((measurable_mul_unop.comp measurable_snd).mul (measurable_mul_unop.comp measurable_fst))⟩

中文:
实例 MulOpposite.instMeasurableMul₂
  签名: {M : 类型} [乘法 M] [可测空间 M]
  定义体: ⟨measurable_mul_op.comp
      ((measurable_mul_unop.comp measurable_snd).mul (measurable_mul_unop.comp measurable_fst))⟩

Depends on / 依赖: measurable_fst, measurable_mul_op, measurable_mul_op.comp, measurable_mul_unop, measurable_mul_unop.comp, measurable_snd
-/
instance MulOpposite.instMeasurableMul₂ {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul₂ M] : MeasurableMul₂ Mᵐᵒᵖ :=
  ⟨measurable_mul_op.comp
      ((measurable_mul_unop.comp measurable_snd).mul (measurable_mul_unop.comp measurable_fst))⟩

/-- If a scalar is central, then its right action is measurable when its left action is. -/
@[to_additive /-- If a vector is central, then its right action is measurable when its left
action is. -/]
nonrec instance MeasurableSMul.op {M α} [MeasurableSpace M] [MeasurableSpace α] [SMul M α]
    [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] [MeasurableSMul M α] : MeasurableSMul Mᵐᵒᵖ α where
  measurable_smul_const x :=
    show Measurable fun c => op (unop c) • x by
      simpa only [op_smul_eq_smul] using! (measurable_smul_const x).comp measurable_mul_unop

/-- If a scalar is central, then its right action is measurable when its left action is. -/
nonrec instance MeasurableSMul₂.op {M α} [MeasurableSpace M] [MeasurableSpace α] [SMul M α]
    [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] [MeasurableSMul₂ M α] : MeasurableSMul₂ Mᵐᵒᵖ α :=
  ⟨show Measurable fun x : Mᵐᵒᵖ × α => op (unop x.1) • x.2 by
      simp_rw [op_smul_eq_smul]
      exact (measurable_mul_unop.comp measurable_fst).smul measurable_snd⟩

@[to_additive]
/--
Instance `measurableSMul_opposite_of_mul` / 实例 `measurableSMul_opposite_of_mul`

English:
instance measurableSMul_opposite_of_mul
  signature: {M : Type*} [Mul M] [MeasurableSpace M]
  body: measurable_mul_unop.const_mul x

@[to_additive]

中文:
实例 measurableSMul_opposite_of_mul
  签名: {M : 类型} [乘法 M] [可测空间 M]
  定义体: measurable_mul_unop.const_mul x

@[to_additive]

Depends on / 依赖: const_mul, measurable_mul_unop, measurable_mul_unop.const_mul
-/
instance measurableSMul_opposite_of_mul {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul M] : MeasurableSMul Mᵐᵒᵖ M where
  measurable_smul_const x := measurable_mul_unop.const_mul x

@[to_additive]
/--
Instance `measurableSMul₂_opposite_of_mul` / 实例 `measurableSMul₂_opposite_of_mul`

English:
instance measurableSMul₂_opposite_of_mul
  signature: {M : Type*} [Mul M] [MeasurableSpace M]
  body: ⟨measurable_snd.mul (measurable_mul_unop.comp measurable_fst)⟩

中文:
实例 measurableSMul₂_opposite_of_mul
  签名: {M : 类型} [乘法 M] [可测空间 M]
  定义体: ⟨measurable_snd.mul (measurable_mul_unop.comp measurable_fst)⟩

Depends on / 依赖: measurable_fst, measurable_mul_unop, measurable_mul_unop.comp, measurable_snd, measurable_snd.mul
-/
instance measurableSMul₂_opposite_of_mul {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul₂ M] : MeasurableSMul₂ Mᵐᵒᵖ M :=
  ⟨measurable_snd.mul (measurable_mul_unop.comp measurable_fst)⟩

end Opposite

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M α : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M] {m : MeasurableSpace α}
  {μ : Measure α}

-- TODO: `fun_prop` cannot use lemmas with a condition quantifying over the function
@[to_additive (attr := fun_prop)]
/--
theorem `List.measurable_prod` / 定理 `List.measurable_prod`

English:
theorem List.measurable_prod
  given: (l : List (α -> M)) (hl : forall f in l, Measurable f)
  proof: by
  induction l with
  | nil => exact measurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]

中文:
定理 列表.measurable_prod
  条件: (l : 列表 (α -> M)) (hl : 对任意 f in l, 可测 f)
  证明: by
  induction l with
  | nil => exact measurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]

Depends on / 依赖: List.forall_mem_cons, List.prod_cons, forall_mem_cons, measurable_one, prod_cons
-/
theorem List.measurable_prod (l : List (α -> M)) (hl : forall f in l, Measurable f) :
    Measurable l.prod := by
  induction l with
  | nil => exact measurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]
/--
theorem `List.aemeasurable_prod` / 定理 `List.aemeasurable_prod`

English:
theorem List.aemeasurable_prod
  given: (l : List (α -> M)) (hl : forall f in l, AEMeasurable f μ)
  proof: by
  induction l with
  | nil => exact aemeasurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]

中文:
定理 列表.aemeasurable_prod
  条件: (l : 列表 (α -> M)) (hl : 对任意 f in l, 几乎处处可测 f μ)
  证明: by
  induction l with
  | nil => exact aemeasurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]

Depends on / 依赖: List.forall_mem_cons, List.prod_cons, aemeasurable_one, forall_mem_cons, prod_cons
-/
theorem List.aemeasurable_prod (l : List (α -> M)) (hl : forall f in l, AEMeasurable f μ) :
    AEMeasurable l.prod μ := by
  induction l with
  | nil => exact aemeasurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]
/--
theorem `List.measurable_fun_prod` / 定理 `List.measurable_fun_prod`

English:
theorem List.measurable_fun_prod
  given: (l : List (α -> M)) (hl : forall f in l, Measurable f)
  proof: by
  simpa only [← Pi.list_prod_apply] using l.measurable_prod hl

@[to_additive (attr := fun_prop)]

中文:
定理 列表.measurable_fun_prod
  条件: (l : 列表 (α -> M)) (hl : 对任意 f in l, 可测 f)
  证明: by
  simpa only [← Pi.list_prod_apply] using l.measurable_prod hl

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Pi.list_prod_apply, l.measurable_prod, list_prod_apply, measurable_prod
-/
theorem List.measurable_fun_prod (l : List (α -> M)) (hl : forall f in l, Measurable f) :
    Measurable fun x => (l.map fun f : α -> M => f x).prod := by
  simpa only [← Pi.list_prod_apply] using l.measurable_prod hl

@[to_additive (attr := fun_prop)]
/--
theorem `List.aemeasurable_fun_prod` / 定理 `List.aemeasurable_fun_prod`

English:
theorem List.aemeasurable_fun_prod
  given: (l : List (α -> M)) (hl : forall f in l, AEMeasurable f μ)
  proof: by
  simpa only [← Pi.list_prod_apply] using l.aemeasurable_prod hl

中文:
定理 列表.aemeasurable_fun_prod
  条件: (l : 列表 (α -> M)) (hl : 对任意 f in l, 几乎处处可测 f μ)
  证明: by
  simpa only [← Pi.list_prod_apply] using l.aemeasurable_prod hl

Depends on / 依赖: Pi.list_prod_apply, aemeasurable_prod, l.aemeasurable_prod, list_prod_apply
-/
theorem List.aemeasurable_fun_prod (l : List (α -> M)) (hl : forall f in l, AEMeasurable f μ) :
    AEMeasurable (fun x => (l.map fun f : α -> M => f x).prod) μ := by
  simpa only [← Pi.list_prod_apply] using l.aemeasurable_prod hl

end Monoid

section CommMonoid

variable {M ι α β : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M]
  {m : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} {f : ι -> α -> M}

@[to_additive (attr := fun_prop)]
/--
theorem `Multiset.measurable_prod` / 定理 `Multiset.measurable_prod`

English:
theorem Multiset.measurable_prod
  given: (l : Multiset (α -> M)) (hl : forall f in l, Measurable f)
  proof: by
  rcases l with ⟨l⟩
  simpa using l.measurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]

中文:
定理 Multiset.measurable_prod
  条件: (l : Multiset (α -> M)) (hl : 对任意 f in l, 可测 f)
  证明: by
  rcases l with ⟨l⟩
  simpa using l.measurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]

Depends on / 依赖: l.measurable_prod, measurable_prod
-/
theorem Multiset.measurable_prod (l : Multiset (α -> M)) (hl : forall f in l, Measurable f) :
    Measurable l.prod := by
  rcases l with ⟨l⟩
  simpa using l.measurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]
/--
theorem `Multiset.aemeasurable_prod` / 定理 `Multiset.aemeasurable_prod`

English:
theorem Multiset.aemeasurable_prod
  given: (l : Multiset (α -> M)) (hl : forall f in l, AEMeasurable f μ)
  proof: by
  rcases l with ⟨l⟩
  simpa using l.aemeasurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]

中文:
定理 Multiset.aemeasurable_prod
  条件: (l : Multiset (α -> M)) (hl : 对任意 f in l, 几乎处处可测 f μ)
  证明: by
  rcases l with ⟨l⟩
  simpa using l.aemeasurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]

Depends on / 依赖: aemeasurable_prod, l.aemeasurable_prod
-/
theorem Multiset.aemeasurable_prod (l : Multiset (α -> M)) (hl : forall f in l, AEMeasurable f μ) :
    AEMeasurable l.prod μ := by
  rcases l with ⟨l⟩
  simpa using l.aemeasurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]
/--
theorem `Multiset.measurable_fun_prod` / 定理 `Multiset.measurable_fun_prod`

English:
theorem Multiset.measurable_fun_prod
  given: (s : Multiset (α -> M)) (hs : forall f in s, Measurable f)
  proof: by
  simpa only [← Pi.multiset_prod_apply] using s.measurable_prod hs

@[to_additive (attr := fun_prop)]

中文:
定理 Multiset.measurable_fun_prod
  条件: (s : Multiset (α -> M)) (hs : 对任意 f in s, 可测 f)
  证明: by
  simpa only [← Pi.multiset_prod_apply] using s.measurable_prod hs

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Pi.multiset_prod_apply, measurable_prod, multiset_prod_apply, s.measurable_prod
-/
theorem Multiset.measurable_fun_prod (s : Multiset (α -> M)) (hs : forall f in s, Measurable f) :
    Measurable fun x => (s.map fun f : α -> M => f x).prod := by
  simpa only [← Pi.multiset_prod_apply] using s.measurable_prod hs

@[to_additive (attr := fun_prop)]
/--
theorem `Multiset.aemeasurable_fun_prod` / 定理 `Multiset.aemeasurable_fun_prod`

English:
theorem Multiset.aemeasurable_fun_prod
  given: (s : Multiset (α -> M)) (hs : forall f in s, AEMeasurable f μ)
  proof: by
  simpa only [← Pi.multiset_prod_apply] using s.aemeasurable_prod hs

@[to_additive (attr := fun_prop)]

中文:
定理 Multiset.aemeasurable_fun_prod
  条件: (s : Multiset (α -> M)) (hs : 对任意 f in s, 几乎处处可测 f μ)
  证明: by
  simpa only [← Pi.multiset_prod_apply] using s.aemeasurable_prod hs

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Pi.multiset_prod_apply, aemeasurable_prod, multiset_prod_apply, s.aemeasurable_prod
-/
theorem Multiset.aemeasurable_fun_prod (s : Multiset (α -> M)) (hs : forall f in s, AEMeasurable f μ) :
    AEMeasurable (fun x => (s.map fun f : α -> M => f x).prod) μ := by
  simpa only [← Pi.multiset_prod_apply] using s.aemeasurable_prod hs

@[to_additive (attr := fun_prop)]
/--
theorem `Finset.measurable_fun_prod` / 定理 `Finset.measurable_fun_prod`

English:
theorem Finset.measurable_fun_prod
  given: (s : Finset ι) (hf : forall i in s, Measurable (f i))
  proof: by
  simp_rw [← Finset.prod_apply]
  exact Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf

@[to_additive (attr := fun_prop)]

中文:
定理 有限集.measurable_fun_prod
  条件: (s : 有限集 ι) (hf : 对任意 i in s, 可测 (f i))
  证明: by
  simp_rw [← Finset.prod_apply]
  exact Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Finset, Finset.prod_apply, Finset.prod_induction, Measurable, Measurable.mul, measurable_one, prod_apply, prod_induction, simp_rw
-/
theorem Finset.measurable_fun_prod (s : Finset ι) (hf : forall i in s, Measurable (f i)) :
    Measurable fun a => ∏ i in s, f i a := by
  simp_rw [← Finset.prod_apply]
  exact Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf

@[to_additive (attr := fun_prop)]
/--
theorem `Finset.measurable_prod` / 定理 `Finset.measurable_prod`

English:
theorem Finset.measurable_prod
  given: (s : Finset ι) (hf : forall i in s, Measurable (f i))
  proof: by
  simp_rw [← Finset.prod_apply]
  exact Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf

中文:
定理 有限集.measurable_prod
  条件: (s : 有限集 ι) (hf : 对任意 i in s, 可测 (f i))
  证明: by
  simp_rw [← Finset.prod_apply]
  exact Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf

Depends on / 依赖: Finset, Finset.prod_apply, Finset.prod_induction, Measurable, Measurable.mul, measurable_one, prod_apply, prod_induction, simp_rw
-/
theorem Finset.measurable_prod (s : Finset ι) (hf : forall i in s, Measurable (f i)) :
    Measurable fun a => ∏ i in s, f i a := by
  simp_rw [← Finset.prod_apply]
  exact Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf

/-- Compositional version of `Finset.measurable_prod` for use by `fun_prop`. -/
@[to_additive (attr := fun_prop)
/-- Compositional version of `Finset.measurable_sum` for use by `fun_prop`. -/]
/--
lemma `Finset.measurable_prod_apply` / 引理 `Finset.measurable_prod_apply`

English:
lemma Finset.measurable_prod_apply
  statement: {f : ι -> α -> β -> M} {g : α -> β} {s : Finset ι}
  proof: by
  simp only [prod_apply]; fun_prop

@[to_additive (attr := fun_prop)]

中文:
引理 有限集.measurable_prod_apply
  结论: {f : ι -> α -> β -> M} {g : α -> β} {s : 有限集 ι}
  证明: by
  simp only [prod_apply]; fun_prop

@[to_additive (attr := fun_prop)]

Depends on / 依赖: fun_prop, prod_apply
-/
lemma Finset.measurable_prod_apply {f : ι -> α -> β -> M} {g : α -> β} {s : Finset ι}
    (hf : forall i in s, Measurable ↿(f i)) (hg : Measurable g) :
    Measurable fun a => (∏ i in s, f i a) (g a) := by
  simp only [prod_apply]; fun_prop

@[to_additive (attr := fun_prop)]
/--
theorem `Finset.aemeasurable_prod` / 定理 `Finset.aemeasurable_prod`

English:
theorem Finset.aemeasurable_prod
  given: (s : Finset ι) (hf : forall i in s, AEMeasurable (f i) μ)
  proof: Multiset.aemeasurable_prod _ fun _g hg =>
    let ⟨_i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi

@[to_additive (attr := fun_prop)]

中文:
定理 有限集.aemeasurable_prod
  条件: (s : 有限集 ι) (hf : 对任意 i in s, 几乎处处可测 (f i) μ)
  证明: Multiset.aemeasurable_prod _ fun _g hg =>
    let ⟨_i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Multiset, Multiset.aemeasurable_prod, Multiset.mem_map, aemeasurable_prod, mem_map
-/
theorem Finset.aemeasurable_prod (s : Finset ι) (hf : forall i in s, AEMeasurable (f i) μ) :
    AEMeasurable (∏ i in s, f i) μ :=
  Multiset.aemeasurable_prod _ fun _g hg =>
    let ⟨_i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi

@[to_additive (attr := fun_prop)]
/--
theorem `Finset.aemeasurable_fun_prod` / 定理 `Finset.aemeasurable_fun_prod`

English:
theorem Finset.aemeasurable_fun_prod
  given: (s : Finset ι) (hf : forall i in s, AEMeasurable (f i) μ)
  proof: by
  simpa only [← Finset.prod_apply] using s.aemeasurable_prod hf

中文:
定理 有限集.aemeasurable_fun_prod
  条件: (s : 有限集 ι) (hf : 对任意 i in s, 几乎处处可测 (f i) μ)
  证明: by
  simpa only [← Finset.prod_apply] using s.aemeasurable_prod hf

Depends on / 依赖: Finset, Finset.prod_apply, aemeasurable_prod, prod_apply, s.aemeasurable_prod
-/
theorem Finset.aemeasurable_fun_prod (s : Finset ι) (hf : forall i in s, AEMeasurable (f i) μ) :
    AEMeasurable (fun a => ∏ i in s, f i a) μ := by
  simpa only [← Finset.prod_apply] using s.aemeasurable_prod hf

end CommMonoid

variable [MeasurableSpace α] [Mul α] [Div α] [Inv α]

@[to_additive] -- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableMul [DiscreteMeasurableSpace α] :
    MeasurableMul α where

@[to_additive DiscreteMeasurableSpace.toMeasurableAdd₂] -- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableMul₂
    [DiscreteMeasurableSpace (α × α)] : MeasurableMul₂ α := ⟨.of_discrete⟩

@[to_additive] -- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableInv [DiscreteMeasurableSpace α] :
    MeasurableInv α := ⟨.of_discrete⟩

@[to_additive] -- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableDiv [DiscreteMeasurableSpace α] :
    MeasurableDiv α where

@[to_additive DiscreteMeasurableSpace.toMeasurableSub₂] -- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableDiv₂
    [DiscreteMeasurableSpace (α × α)] : MeasurableDiv₂ α := ⟨.of_discrete⟩
