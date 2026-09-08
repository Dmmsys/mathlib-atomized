/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.Algebra.Order.Hom.Units
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Ring topologised by a valuation

For a given valuation `v : Valuation R Γ₀` on a ring `R` taking values in `Γ₀`, this file
defines the type synonym `WithVal v` of `R`. By assigning a `Valued (WithVal v) Γ₀` instance,
`WithVal v` represents the ring `R` equipped with the topology coming from `v`. The type
synonym `WithVal v` is in isomorphism to `R` as rings via `WithVal.equiv v`. This
isomorphism should be used to explicitly map terms of `WithVal v` to terms of `R`.

The `WithVal` type synonym is used to define the completion of `R` with respect to `v` in
`Valuation.Completion`. An example application of this is
`IsDedekindDomain.HeightOneSpectrum.adicCompletion`, which is the completion of the field of
fractions of a Dedekind domain with respect to a height-one prime ideal of the domain.

## Main definitions
- `WithVal` : type synonym for a ring equipped with the topology coming from a valuation.
- `WithVal.equiv` : the canonical ring equivalence between `WithValuation v` and `R`.
- `Valuation.Completion` : the uniform space completion of a field `K` according to the
  uniform structure defined by the specified valuation.
-/

@[expose] public section

noncomputable section

variable {R Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- Type synonym for a ring equipped with the topology coming from a valuation. -/
/-
**WithVal** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} →   {Γ₀ : Type u_2} → [inst : LinearOrderedCommGroupWithZer
o Γ₀] → [inst_1 : Ring R] → Valuation R Γ₀ → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type synonym for a ring equipped with the topology coming from a valuation.
-/
structure WithVal [Ring R] (v : Valuation R Γ₀) where
  /-- Converts an element of `R` to an element of `WithVal v`. -/
  toVal (v) ::
  /-- Converts an element of `WithVal v` to an element of `R`. -/
  ofVal : R

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `toVal v x` being printed as `{ ofAbs := x }` by `delabStructureInstance`. -/
@[app_delab WithVal.toVal]
meta def WithVal.delabToVal : Delab := delabApp

end Notation

namespace WithVal

section Ring

variable [Ring R] (v : Valuation R Γ₀)

/-
**WithVal.ofVal_toVal** 是 Mathlib 中的一个引理，位于命名空间 `WithVal`。
形式化陈述：ofVal_toVal (x : R) : ofVal (toVal v x) = x
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofVal_toVal (x : R) : ofVal (toVal v x) = x := rfl
/-
**WithVal.toVal_ofVal** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x : WithVal v), WithVal.toVal v x.of
Val = x
参数：v : Valuation R Γ₀；x : WithVal v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toVal_ofVal (x : WithVal v) : toVal v (ofVal x) = x := rfl
/-
**WithVal.ofVal_surjective** 是 Mathlib 中的一个引理，位于命名空间 `WithVal`。
形式化陈述：ofVal_surjective : Function.Surjective (ofVal (v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用引理 `WithVal.ofVal_toVal`：ofVal_toVal (x : R) : ofVal (toVal v x) = x
-/
lemma ofVal_surjective : Function.Surjective (ofVal (v := v)) :=
  Function.RightInverse.surjective <| ofVal_toVal _
/-
**WithVal.toVal_surjective** 是 Mathlib 中的一个引理，位于命名空间 `WithVal`。
形式化陈述：toVal_surjective : Function.Surjective (toVal v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `WithVal.toVal_ofVal`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrde
redCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x : WithVal v
), WithVa…
-/
lemma toVal_surjective : Function.Surjective (toVal v) :=
  Function.RightInverse.surjective <| toVal_ofVal _
/-
**WithVal.ofVal_injective** 是 Mathlib 中的一个引理，位于命名空间 `WithVal`。
形式化陈述：ofVal_injective : Function.Injective (ofVal (v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `WithVal.toVal_ofVal`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrde
redCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x : WithVal v
), WithVa…
-/
lemma ofVal_injective : Function.Injective (ofVal (v := v)) :=
  Function.LeftInverse.injective <| toVal_ofVal _
/-
**WithVal.toVal_injective** 是 Mathlib 中的一个引理，位于命名空间 `WithVal`。
形式化陈述：toVal_injective : Function.Injective (toVal v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用引理 `WithVal.ofVal_toVal`：ofVal_toVal (x : R) : ofVal (toVal v x) = x
-/
lemma toVal_injective : Function.Injective (toVal v) :=
  Function.LeftInverse.injective <| ofVal_toVal _
/-
**WithVal.ofVal_bijective** 是 Mathlib 中的一个引理，位于命名空间 `WithVal`。
形式化陈述：ofVal_bijective : Function.Bijective (ofVal (v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithVal.ofVal_injective`：ofVal_injective : Function.Injective (ofVal (v
· 使用引理 `WithVal.ofVal_surjective`：ofVal_surjective : Function.Surjective (ofVal 
(v
-/
lemma ofVal_bijective : Function.Bijective (ofVal (v := v)) :=
  ⟨ofVal_injective v, ofVal_surjective v⟩
/-
**WithVal.toVal_bijective** 是 Mathlib 中的一个引理，位于命名空间 `WithVal`。
形式化陈述：toVal_bijective : Function.Bijective (toVal v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithVal.toVal_injective`：toVal_injective : Function.Injective (toVal v)
· 使用引理 `WithVal.toVal_surjective`：toVal_surjective : Function.Surjective (toVal 
v)
-/
lemma toVal_bijective : Function.Bijective (toVal v) :=
  ⟨toVal_injective v, toVal_surjective v⟩
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (WithVal v) where zero := toVal _ 0
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (WithVal v) where one := toVal _ 1
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (WithVal v) where add x y := toVal _ (x.ofVal + y.ofVal)
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (WithVal v) where sub x y := toVal _ (x.ofVal - y.ofVal)
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (WithVal v) where neg x := toVal _ (-x.ofVal)
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (WithVal v) where mul x y := toVal _ (x.ofVal * y.ofVal)
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S} [SMul S R] : SMul S (WithVal v) where smul s x := toVal _ (s • x.ofVal)
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (WithVal v) ℕ where pow x n := toVal _ (x.ofVal ^ n)
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (WithVal v) where natCast n := toVal _ n
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IntCast (WithVal v) where intCast z := toVal _ z
/-
**WithVal.toVal_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀),   WithVal.toVal v 0 = 0
参数：v : Valuation R Γ₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toVal_zero : toVal v 0 = 0 := rfl
/-
**WithVal.ofVal_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀),   WithVal.ofVal 0 = 0
参数：v : Valuation R Γ₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofVal_zero : ofVal (0 : WithVal v) = 0 := rfl
/-
**WithVal.toVal_one** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀),   WithVal.toVal v 1 = 1
参数：v : Valuation R Γ₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toVal_one : toVal v 1 = 1 := rfl
/-
**WithVal.ofVal_one** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀),   WithVal.ofVal 1 = 1
参数：v : Valuation R Γ₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofVal_one : ofVal (1 : WithVal v) = 1 := rfl
/-
**WithVal.toVal_add** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x y : R), WithVal.toVal v (x + y) = 
WithVal.toVal v x + WithVal.toVal v y
参数：v : Valuation R Γ₀；x y : R；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toVal_add (x y : R) : toVal v (x + y) = toVal v x + toVal v y := rfl
/-
**WithVal.ofVal_add** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x y : WithVal v), (x + y).ofVal = x.
ofVal + y.ofVal
参数：v : Valuation R Γ₀；x y : WithVal v；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofVal_add (x y : WithVal v) : ofVal (x + y) = ofVal x + ofVal y := rfl
/-
**WithVal.toVal_sub** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x y : R), WithVal.toVal v (x - y) = 
WithVal.toVal v x - WithVal.toVal v y
参数：v : Valuation R Γ₀；x y : R；x - y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toVal_sub (x y : R) : toVal v (x - y) = toVal v x - toVal v y := rfl
/-
**WithVal.ofVal_sub** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x y : WithVal v), (x - y).ofVal = x.
ofVal - y.ofVal
参数：v : Valuation R Γ₀；x y : WithVal v；x - y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofVal_sub (x y : WithVal v) : ofVal (x - y) = ofVal x - ofVal y := rfl
/-
**WithVal.toVal_mul** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x y : R), WithVal.toVal v (x * y) = 
WithVal.toVal v x * WithVal.toVal v y
参数：v : Valuation R Γ₀；x y : R；x * y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toVal_mul (x y : R) : toVal v (x * y) = toVal v x * toVal v y := rfl
/-
**WithVal.ofVal_mul** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x y : WithVal v), (x * y).ofVal = x.
ofVal * y.ofVal
参数：v : Valuation R Γ₀；x y : WithVal v；x * y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofVal_mul (x y : WithVal v) : ofVal (x * y) = ofVal x * ofVal y := rfl
/-
**WithVal.toVal_neg** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x : R), WithVal.toVal v (-x) = -With
Val.toVal v x
参数：v : Valuation R Γ₀；x : R；-x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toVal_neg (x : R) : toVal v (-x) = -toVal v x := rfl
/-
**WithVal.ofVal_neg** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x : WithVal v), (-x).ofVal = -x.ofVa
l
参数：v : Valuation R Γ₀；x : WithVal v；-x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofVal_neg (x : WithVal v) : ofVal (-x) = -ofVal x := rfl
/-
**WithVal.toVal_pow** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x : R) (n : ℕ), WithVal.toVal v (x ^
 n) = WithVal.toVal v x ^ n
参数：v : Valuation R Γ₀；x : R；n : ℕ；x ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toVal_pow (x : R) (n : ℕ) : toVal v (x ^ n) = (toVal v x) ^ n := rfl
/-
**WithVal.ofVal_pow** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x : WithVal v) (n : ℕ), (x ^ n).ofVa
l = x.ofVal ^ n
参数：v : Valuation R Γ₀；x : WithVal v；n : ℕ；x ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofVal_pow (x : WithVal v) (n : ℕ) : ofVal (x ^ n) = (ofVal x) ^ n := rfl
/-
**WithVal.toVal_smul** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   {S : Type u_3} [inst_2 : SMul S R] (s
 : S) (r : R), WithVal.toVal v (s • r) = s • WithVal.toVal v r
参数：v : Valuation R Γ₀；s : S；r : R；s • r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toVal_smul {S} [SMul S R] (s : S) (r : R) : toVal v (s • r) = s • toVal v r := rfl
/-
**WithVal.ofVal_smul** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   {S : Type u_3} [inst_2 : SMul S R] (s
 : S) (x : WithVal v), (s • x).ofVal = s • x.ofVal
参数：v : Valuation R Γ₀；s : S；x : WithVal v；s • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofVal_smul {S} [SMul S R] (s : S) (x : WithVal v) : ofVal (s • x) = s • ofVal x :=
  rfl
/-
**WithVal.toVal_natCast** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (n : ℕ), WithVal.toVal v ↑n = ↑n
参数：v : Valuation R Γ₀；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toVal_natCast (n : ℕ) : toVal v n = n := rfl
/-
**WithVal.ofVal_natCast** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (n : ℕ), (↑n).ofVal = ↑n
参数：v : Valuation R Γ₀；n : ℕ；↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofVal_natCast (n : ℕ) : ofVal (n : WithVal v) = n := rfl
/-
**WithVal.toVal_intCast** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (z : ℤ), WithVal.toVal v ↑z = ↑z
参数：v : Valuation R Γ₀；z : ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toVal_intCast (z : ℤ) : toVal v z = z := rfl
/-
**WithVal.ofVal_intCast** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (z : ℤ), (↑z).ofVal = ↑z
参数：v : Valuation R Γ₀；z : ℤ；↑z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofVal_intCast (z : ℤ) : ofVal (z : WithVal v) = z := rfl
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Ring (WithVal v) := fast_instance% ofVal_injective v |>.ring _
  (ofVal_zero _) (ofVal_one _) (ofVal_add _) (ofVal_mul _) (ofVal_neg _) (ofVal_sub _)
  (ofVal_smul _) (ofVal_smul _) (ofVal_pow _) (ofVal_natCast _) (ofVal_intCast _)
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (WithVal v) := ⟨0⟩
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder (WithVal v) := .lift (v ∘ ofVal)
/-
**WithVal.le_def** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：le_def {v : Valuation R Γ₀} {a b : WithVal v} : a <= b ↔ v a.ofVal <= v b.
ofVal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def {v : Valuation R Γ₀} {a b : WithVal v} : a ≤ b ↔ v a.ofVal ≤ v b.ofVal := .rfl
/-
**WithVal.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：lt_def {v : Valuation R Γ₀} {a b : WithVal v} : a < b ↔ v a.ofVal < v b.of
Val
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_def {v : Valuation R Γ₀} {a b : WithVal v} : a < b ↔ v a.ofVal < v b.ofVal := .rfl
/-
**WithVal.toVal_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x : R), WithVal.toVal v x = 0 ↔ x = 
0
参数：v : Valuation R Γ₀；x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `WithVal.toVal_injective`：toVal_injective : Function.Injective (toVal v)
-/
@[simp] lemma toVal_eq_zero (x : R) : toVal v x = 0 ↔ x = 0 := (toVal_injective v).eq_iff
/-
**WithVal.ofVal_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x : WithVal v), x.ofVal = 0 ↔ x = 0
参数：v : Valuation R Γ₀；x : WithVal v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `WithVal.ofVal_injective`：ofVal_injective : Function.Injective (ofVal (v
-/
@[simp] lemma ofVal_eq_zero (x : WithVal v) : ofVal x = 0 ↔ x = 0 := (ofVal_injective v).eq_iff

/-- The canonical ring equivalence between `WithVal v` and `R`. -/
@[simps apply symm_apply]
/-
**WithVal.equiv** 是 Mathlib 中的一个定义，位于命名空间 `WithVal`。
形式化陈述：equiv : WithVal v ≃+* R where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WithVal.ofVal_mul`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrdere
dCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x y : WithVal v
), (x *…
· 使用定理 `WithVal.ofVal_add`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrdere
dCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x y : WithVal v
), (x +…

--- 原说明 ---
The canonical ring equivalence between `WithVal v` and `R`.
-/
def equiv : WithVal v ≃+* R where
  toFun := ofVal
  invFun := toVal v
  map_add' := ofVal_add v
  map_mul' := ofVal_mul v

variable {S : Type*} [Ring S] {Λ₀ : Type*} [LinearOrderedCommGroupWithZero Λ₀] (w : Valuation S Λ₀)

/-- Lift a ring hom to `WithVal`. -/
/-
**WithVal.map** 是 Mathlib 中的一个定义，位于命名空间 `WithVal`。
形式化陈述：map (f : R ->+* S) : WithVal v ->+* WithVal w
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a ring hom to `WithVal`.
-/
def map (f : R →+* S) : WithVal v →+* WithVal w := (equiv w).symm.toRingHom.comp (f.comp (equiv v))
/-
**WithVal.map_id** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀),   WithVal.map v v (RingHom.id R) = Rin
gHom.id (WithVal v)
参数：v : Valuation R Γ₀；RingHom.id R；WithVal v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem map_id : map v v (.id R) = .id (WithVal v) := rfl
/-
**WithVal.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   {S : Type u_3} [inst_2 : Ring S] {Λ₀ 
: Type u_4} [inst_3 : LinearOrderedCommGroupWithZero Λ₀] (w : Valuation S Λ₀)   
{T : Type u_5} [inst_4 : Ring T] (u : Valuation T Γ₀) (f : S →+* T) (g : R →+* S
),   WithVal.map v u (f.comp g) = (WithVal.map w u f).comp (WithVal.map v w g)
参数：v : Valuation R Γ₀；w : Valuation S Λ₀；u : Valuation T Γ₀；f : S →+* T；g : R →+
* S；f.comp g；WithVal.map w u f；WithVal.map v w g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem map_comp {T : Type*} [Ring T] (u : Valuation T Γ₀) (f : S →+* T) (g : R →+* S) :
    map v u (f.comp g) = (map w u f).comp (map v w g) := rfl
/-
**WithVal.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   {S : Type u_3} [inst_2 : Ring S] {Λ₀ 
: Type u_4} [inst_3 : LinearOrderedCommGroupWithZero Λ₀] (w : Valuation S Λ₀)   
(f : R →+* S) (x : WithVal v), (WithVal.map v w f) x = WithVal.toVal w (f x.ofVa
l)
参数：v : Valuation R Γ₀；w : Valuation S Λ₀；f : R →+* S；x : WithVal v；WithVal.map v
 w f；f x.ofVal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem map_apply (f : R →+* S) (x : WithVal v) : map v w f x = toVal w (f x.ofVal) := rfl

/-- Lift a `RingEquiv` to `WithVal`. -/
/-
**WithVal.congr** 是 Mathlib 中的一个定义，位于命名空间 `WithVal`。
形式化陈述：congr (f : R ≃+* S) : WithVal v ≃+* WithVal w where __
参数：f : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a `RingEquiv` to `WithVal`.
-/
def congr (f : R ≃+* S) : WithVal v ≃+* WithVal w where
  __ := map v w f.toRingHom
  invFun := map w v f.symm.toRingHom
  left_inv _ := by simp
  right_inv _ := by simp
/-
**WithVal.congr_refl** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀),   WithVal.congr v v (RingEquiv.refl R)
 = RingEquiv.refl (WithVal v)
参数：v : Valuation R Γ₀；RingEquiv.refl R；WithVal v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem congr_refl : congr v v (.refl R) = .refl (WithVal v) := rfl
/-
**WithVal.congr_symm** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：congr_symm (f : R ≃+* S) : (congr v w f).symm = congr w v f.symm
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_symm (f : R ≃+* S) : (congr v w f).symm = congr w v f.symm := rfl
/-
**WithVal.congr_trans** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：congr_trans {T : Type*} [Ring T] (u : Valuation T Γ₀) (f : R ≃+* S) (g : S
 ≃+* T) : congr v u (f.trans g) = (congr v w f).trans (congr w u g)
参数：u : Valuation T Γ₀；f : R ≃+* S；g : S ≃+* T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_trans {T : Type*} [Ring T] (u : Valuation T Γ₀) (f : R ≃+* S) (g : S ≃+* T) :
    congr v u (f.trans g) = (congr v w f).trans (congr w u g) := rfl
/-
**WithVal.congr_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   {S : Type u_3} [inst_2 : Ring S] {Λ₀ 
: Type u_4} [inst_3 : LinearOrderedCommGroupWithZero Λ₀] (w : Valuation S Λ₀)   
(f : R ≃+* S) (x : WithVal v), (WithVal.congr v w f) x = WithVal.toVal w (f x.of
Val)
参数：v : Valuation R Γ₀；w : Valuation S Λ₀；f : R ≃+* S；x : WithVal v；WithVal.congr
 v w f；f x.ofVal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem congr_apply (f : R ≃+* S) (x : WithVal v) :
    congr v w f x = toVal w (f x.ofVal) := rfl
/-
**WithVal.congr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   {S : Type u_3} [inst_2 : Ring S] {Λ₀ 
: Type u_4} [inst_3 : LinearOrderedCommGroupWithZero Λ₀] (w : Valuation S Λ₀)   
(f : R ≃+* S) (x : WithVal w), (WithVal.congr v w f).symm x = WithVal.toVal v (f
.symm x.ofVal)
参数：v : Valuation R Γ₀；w : Valuation S Λ₀；f : R ≃+* S；x : WithVal w；WithVal.congr
 v w f；f.symm x.ofVal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem congr_symm_apply (f : R ≃+* S) (x : WithVal w) :
    (congr v w f).symm x = toVal v (f.symm x.ofVal) := rfl

/-- Canonical valuation on the `WithVal v` type synonym. -/
/-
**WithVal.valuation** 是 Mathlib 中的一个定义，位于命名空间 `WithVal`。
形式化陈述：valuation : Valuation (WithVal v) Γ₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Canonical valuation on the `WithVal v` type synonym.
-/
def valuation : Valuation (WithVal v) Γ₀ := v.comap (equiv v)
/-
**WithVal.valuation_toVal** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x : R), (WithVal.valuation v) (WithV
al.toVal v x) = v x
参数：v : Valuation R Γ₀；x : R；WithVal.valuation v；WithVal.toVal v x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma valuation_toVal (x : R) : valuation v (toVal v x) = v x := rfl
/-
**WithVal.valuation_apply_eq_ofVal** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (x : WithVal v), (WithVal.valuation v
) x = v x.ofVal
参数：v : Valuation R Γ₀；x : WithVal v；WithVal.valuation v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma valuation_apply_eq_ofVal (x : WithVal v) : valuation v x = v x.ofVal := rfl
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Valued (WithVal v) Γ₀ := Valued.mk' (valuation v)
/-
**WithVal.apply_ofVal** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：apply_ofVal (r : WithVal v) : v r.ofVal = Valued.v r
参数：r : WithVal v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_ofVal (r : WithVal v) : v r.ofVal = Valued.v r := rfl
/-
**WithVal.val_apply_equiv** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：val_apply_equiv (r : WithVal v) : v (equiv v r) = Valued.v r
参数：r : WithVal v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_apply_equiv (r : WithVal v) : v (equiv v r) = Valued.v r := rfl
/-
**WithVal.valued_toVal** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] (v : Valuation R Γ₀)   (r : R), Valued.v (WithVal.toVal v r)
 = v r
参数：v : Valuation R Γ₀；r : R；WithVal.toVal v r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem valued_toVal (r : R) : Valued.v (toVal v r) = v r := rfl

@[deprecated (since := "2026-03-02")] alias apply_equiv := apply_ofVal
@[deprecated (since := "2026-03-02")] alias apply_symm_equiv := valued_toVal
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CharZero R] : CharZero (WithVal v) :=
  .of_addMonoidHom (equiv v).symm.toAddMonoidHom (by simp) (equiv v).symm.injective
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ValuativeRel (WithVal v) := fast_instance% .ofValuation (valuation v)
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (valuation v).Compatible := .ofValuation (valuation v)
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsValuativeTopology (WithVal v) where
  mem_nhds_iff {s x} := by
    simp only [Set.image_add_left, Set.preimage_ofPred_eq, Valued.mem_nhds]
    let e := ValuativeRel.ValueGroupWithZero.orderMonoidIso (valuation v)
    apply e.unitsCongr.symm.exists_congr fun a ↦ ?_
    simp [-OrderMonoidIso.val_unitsCongr_symm_apply, OrderMonoidIso.unitsCongr_symm_apply,
      e.lt_symm_apply, e, ← Valuation.restrict_def, sub_eq_neg_add]
    rfl

end Ring

section CommRing

variable [CommRing R] (v : Valuation R Γ₀)

/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing (WithVal v) := fast_instance% (equiv v).commRing

end CommRing

section Module

variable [Ring R] (v : Valuation R Γ₀) {S : Type*}

/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R S] : SMul (WithVal v) S where
  smul x s := ofVal x • s
/-
**WithVal.smul_left_def** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：smul_left_def [SMul R S] (x : WithVal v) (s : S) : x • s = ofVal x • s
参数：x : WithVal v；s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_left_def [SMul R S] (x : WithVal v) (s : S) : x • s = ofVal x • s := rfl
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R S] [FaithfulSMul R S] : FaithfulSMul (WithVal v) S where
  eq_of_smul_eq_smul h := ofVal_injective v <| FaithfulSMul.eq_of_smul_eq_smul h
/-
**WithVal.smul_right_def** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：smul_right_def [SMul S R] (s : S) (x : WithVal v) : s • x = toVal v (s • o
fVal x)
参数：s : S；x : WithVal v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_right_def [SMul S R] (s : S) (x : WithVal v) : s • x = toVal v (s • ofVal x) := rfl
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul S R] [FaithfulSMul S R] : FaithfulSMul S (WithVal v) where
  eq_of_smul_eq_smul h := by
    simp only [smul_right_def, toVal.injEq] at h
    exact FaithfulSMul.eq_of_smul_eq_smul fun r ↦ h (toVal v r)
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P : Type*} [SMul S P] [SMul R S] [SMul R P]
    [IsScalarTower R S P] (v : Valuation R Γ₀) : IsScalarTower (WithVal v) S P where
  smul_assoc := by simp [smul_left_def]
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P : Type*} [Ring S] [SMul P S] [SMul R S] [SMul P R]
    [IsScalarTower P R S] (v : Valuation S Γ₀) : IsScalarTower P R (WithVal v) :=
  (equiv v).isScalarTower P R
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P : Type*} [Ring S] [SMul P R] [SMul S R] [SMul P S]
    [IsScalarTower P S R] (v : Valuation S Γ₀) : IsScalarTower P (WithVal v) R where
  smul_assoc := by simp [smul_right_def, smul_left_def, -toVal_smul]
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMonoid S] [Module R S] : Module (WithVal v) S :=
  fast_instance% .compHom S (equiv v).toRingHom
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMonoid S] [Module R S] [Module.Finite R S] :
    Module.Finite (WithVal v) S := .of_restrictScalars_finite R (WithVal v) S
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring S] [Module S R] : Module S (WithVal v) :=
  fast_instance% (equiv v).module S

variable [Ring S] [Module R S] (v : Valuation S Γ₀)

variable (R) in
/-- The canonical `R`-linear isomorphism between `WithVal v` and `S`, when `v : Valuation S Γ₀`. -/
/-
**WithVal.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithVal`。
形式化陈述：linearEquiv : WithVal v ≃ₗ[R] S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `R`-linear isomorphism between `WithVal v` and `S`, when `v : Valu
ation S Γ₀`.
-/
def linearEquiv : WithVal v ≃ₗ[R] S := (equiv v).linearEquiv R
/-
**WithVal.linearEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] {S : Type u_3}   [inst_2 : Ring S] [inst_3 : _root_.Module R
 S] (v : Valuation S Γ₀) (x : WithVal v),   (WithVal.linearEquiv R v) x = x.ofVa
l
参数：v : Valuation S Γ₀；x : WithVal v；WithVal.linearEquiv R v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem linearEquiv_apply (x : WithVal v) : linearEquiv R v x = x.ofVal := rfl
/-
**WithVal.linearEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : Ring R] {S : Type u_3}   [inst_2 : Ring S] [inst_3 : _root_.Module R
 S] (v : Valuation S Γ₀) (x : S),   (WithVal.linearEquiv R v).symm x = WithVal.t
oVal v x
参数：v : Valuation S Γ₀；x : S；WithVal.linearEquiv R v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem linearEquiv_symm_apply (x : S) : (linearEquiv R v).symm x = toVal v x := rfl
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.Finite R S] :
    Module.Finite R (WithVal v) := .equiv (linearEquiv R v).symm

end Module

section Algebra

variable {S : Type*}

section left

variable [CommRing R] (v : Valuation R Γ₀) [Semiring S] [Algebra R S]

/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra (WithVal v) S := fast_instance% {
  algebraMap.toFun r := algebraMap R S (ofVal r)
  __ := Algebra.compHom S (equiv v).toRingHom }
/-
**WithVal.algebraMap_left_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：algebraMap_left_apply (s : WithVal v) : algebraMap (WithVal v) S s = algeb
raMap R S s.ofVal
参数：s : WithVal v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_left_apply (s : WithVal v) :
    algebraMap (WithVal v) S s = algebraMap R S s.ofVal := rfl
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Type*} [CommSemiring S] [Algebra R S] [i : IsFractionRing R S] :
    IsFractionRing (WithVal v) S := .of_ringEquiv_left (equiv v) (fun _ ↦ rfl)
/-
**WithVal.algebraMap_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：algebraMap_left_injective (h : Function.Injective (algebraMap R S)) : Func
tion.Injective (algebraMap (WithVal v) S)
参数：h : Function.Injective (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `WithVal.ofVal_injective`：ofVal_injective : Function.Injective (ofVal (v
-/
theorem algebraMap_left_injective (h : Function.Injective (algebraMap R S)) :
    Function.Injective (algebraMap (WithVal v) S) := h.comp (ofVal_injective v)

end left

section right

variable [CommSemiring R] [Ring S] [Algebra R S] (v : Valuation S Γ₀)

/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra R (WithVal v) := fast_instance% {
  (equiv v).algebra R with
  algebraMap.toFun r := toVal v (algebraMap R S r) }
/-
**WithVal.algebraMap_right_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：algebraMap_right_apply (r : R) : algebraMap R (WithVal v) r = toVal v (alg
ebraMap R S r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_right_apply (r : R) :
    algebraMap R (WithVal v) r = toVal v (algebraMap R S r) := rfl
/-
**WithVal.algebraMap_right_injective** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：algebraMap_right_injective (h : Function.Injective (algebraMap R S)) : Fun
ction.Injective (algebraMap R (WithVal v))
参数：h : Function.Injective (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `WithVal.toVal_injective`：toVal_injective : Function.Injective (toVal v)
-/
theorem algebraMap_right_injective (h : Function.Injective (algebraMap R S)) :
    Function.Injective (algebraMap R (WithVal v)) := (toVal_injective v).comp h

end right

variable [CommSemiring R] [Ring S] [Algebra R S] (v : Valuation S Γ₀)

variable (R) in
/-- The canonical `R`-algebra isomorphism between `WithVal v` and `S`, when `v : Valuation S Γ₀`. -/
/-
**WithVal.algEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithVal`。
形式化陈述：algEquiv : WithVal v ≃ₐ[R] S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `R`-algebra isomorphism between `WithVal v` and `S`, when `v : Val
uation S Γ₀`.
-/
def algEquiv : WithVal v ≃ₐ[R] S := (equiv v).algEquiv R
/-
**WithVal.algEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] {S : Type u_3} [inst_1 : CommSemiring R]   [inst_2 : Ring S] [inst_3 : Algebra
 R S] (v : Valuation S Γ₀) (x : WithVal v), (WithVal.algEquiv R v) x = x.ofVal
参数：v : Valuation S Γ₀；x : WithVal v；WithVal.algEquiv R v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem algEquiv_apply (x : WithVal v) : algEquiv R v x = x.ofVal := rfl
/-
**WithVal.algEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] {S : Type u_3} [inst_1 : CommSemiring R]   [inst_2 : Ring S] [inst_3 : Algebra
 R S] (v : Valuation S Γ₀) (x : S),   (WithVal.algEquiv R v).symm x = WithVal.to
Val v x
参数：v : Valuation S Γ₀；x : S；WithVal.algEquiv R v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem algEquiv_symm_apply (x : S) : (algEquiv R v).symm x = toVal v x := rfl
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Type*} [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (v : Valuation S Γ₀) : IsLocalization M (WithVal v) := by
  rwa [← IsLocalization.isLocalization_iff_of_algEquiv M (algEquiv R v).symm]

end Algebra

section DivisionRing

variable [DivisionRing R] (v : Valuation R Γ₀)

/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Div (WithVal v) where div x y := toVal _ (x.ofVal / y.ofVal)
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (WithVal v) where inv x := toVal _ x.ofVal⁻¹
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (WithVal v) ℤ where pow x z := toVal _ (x.ofVal ^ z)
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NNRatCast (WithVal v) where nnratCast q := toVal _ q
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RatCast (WithVal v) where ratCast q := toVal _ q
/-
**WithVal.toVal_div** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : DivisionRing R]   (v : Valuation R Γ₀) (x y : R), WithVal.toVal v (x
 / y) = WithVal.toVal v x / WithVal.toVal v y
参数：v : Valuation R Γ₀；x y : R；x / y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toVal_div (x y : R) : toVal v (x / y) = toVal v x / toVal v y := rfl
/-
**WithVal.ofVal_div** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : DivisionRing R]   (v : Valuation R Γ₀) (x y : WithVal v), (x / y).of
Val = x.ofVal / y.ofVal
参数：v : Valuation R Γ₀；x y : WithVal v；x / y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofVal_div (x y : WithVal v) : ofVal (x / y) = ofVal x / ofVal y := rfl
/-
**WithVal.toVal_inv** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : DivisionRing R]   (v : Valuation R Γ₀) (x : R), WithVal.toVal v x⁻¹ 
= (WithVal.toVal v x)⁻¹
参数：v : Valuation R Γ₀；x : R；WithVal.toVal v x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toVal_inv (x : R) : toVal v x⁻¹ = (toVal v x)⁻¹ := rfl
/-
**WithVal.ofVal_inv** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : DivisionRing R]   (v : Valuation R Γ₀) (x : WithVal v), x⁻¹.ofVal = 
x.ofVal⁻¹
参数：v : Valuation R Γ₀；x : WithVal v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofVal_inv (x : WithVal v) : ofVal (x⁻¹) = (ofVal x)⁻¹ := rfl
/-
**WithVal.toVal_zpow** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : DivisionRing R]   (v : Valuation R Γ₀) (x : R) (z : ℤ), WithVal.toVa
l v (x ^ z) = WithVal.toVal v x ^ z
参数：v : Valuation R Γ₀；x : R；z : ℤ；x ^ z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toVal_zpow (x : R) (z : ℤ) : toVal v (x ^ z) = (toVal v x) ^ z := rfl
/-
**WithVal.ofVal_zpow** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : DivisionRing R]   (v : Valuation R Γ₀) (x : WithVal v) (z : ℤ), (x ^
 z).ofVal = x.ofVal ^ z
参数：v : Valuation R Γ₀；x : WithVal v；z : ℤ；x ^ z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofVal_zpow (x : WithVal v) (z : ℤ) : ofVal (x ^ z) = (ofVal x) ^ z := rfl
/-
**WithVal.toVal_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : DivisionRing R]   (v : Valuation R Γ₀) (q : ℚ≥0), WithVal.toVal v ↑q
 = ↑q
参数：v : Valuation R Γ₀；q : ℚ≥0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toVal_nnratCast (q : ℚ≥0) : toVal v q = q := rfl
/-
**WithVal.ofVal_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : DivisionRing R]   (v : Valuation R Γ₀) (q : ℚ≥0), (↑q).ofVal = ↑q
参数：v : Valuation R Γ₀；q : ℚ≥0；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofVal_nnratCast (q : ℚ≥0) : ofVal (q : WithVal v) = q := rfl
/-
**WithVal.toVal_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : DivisionRing R]   (v : Valuation R Γ₀) (q : ℚ), WithVal.toVal v ↑q =
 ↑q
参数：v : Valuation R Γ₀；q : ℚ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toVal_ratCast (q : ℚ) : toVal v q = q := rfl
/-
**WithVal.ofVal_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrderedCommGroupWithZero Γ₀
] [inst_1 : DivisionRing R]   (v : Valuation R Γ₀) (q : ℚ), (↑q).ofVal = ↑q
参数：v : Valuation R Γ₀；q : ℚ；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofVal_ratCast (q : ℚ) : ofVal (q : WithVal v) = q := rfl
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DivisionRing (WithVal v) := fast_instance% (equiv v).divisionRing

end DivisionRing

section Field

variable [Field R] (v : Valuation R Γ₀)

/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Field (WithVal v) := fast_instance% ofVal_injective v |>.field _
  (ofVal_zero _) (ofVal_one _) (ofVal_add _) (ofVal_mul _) (ofVal_neg _) (ofVal_sub _)
  (ofVal_inv _) (ofVal_div _)
  (ofVal_smul _) (ofVal_smul _) (ofVal_smul _) (ofVal_smul _) (ofVal_pow _) (ofVal_zpow _)
  (ofVal_natCast _) (ofVal_intCast _) (ofVal_nnratCast _) (ofVal_ratCast _)
/-
**WithVal.** 是 Mathlib 中的一个实例，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NumberField R] : NumberField (WithVal v) where

end Field

section Ring

variable [Ring R] (v : Valuation R Γ₀)

variable {Γ'₀ : Type*} [LinearOrderedCommGroupWithZero Γ'₀]

/-- Canonical ring equivalence between `WithVal v` and `WithVal w`. -/
@[deprecated "Use `WithVal.congr v w (.refl R)` instead" (since := "2026-01-27")]
/-
**WithVal.equivWithVal** 是 Mathlib 中的一个定义，位于命名空间 `WithVal`。
形式化陈述：equivWithVal (v : Valuation R Γ₀) (w : Valuation R Γ'₀) : WithVal v ≃+* Wi
thVal w
参数：v : Valuation R Γ₀；w : Valuation R Γ'₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Canonical ring equivalence between `WithVal v` and `WithVal w`.
-/
def equivWithVal (v : Valuation R Γ₀) (w : Valuation R Γ'₀) :
    WithVal v ≃+* WithVal w :=
  (equiv v).trans (equiv w).symm

@[deprecated WithVal.congr_symm (since := "2026-01-27")]
/-
**WithVal.equivWithVal_symm** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：equivWithVal_symm (v : Valuation R Γ₀) (w : Valuation R Γ'₀) : (congr v w 
(.refl R)).symm = congr w v (.refl R)
参数：v : Valuation R Γ₀；w : Valuation R Γ'₀。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivWithVal_symm (v : Valuation R Γ₀) (w : Valuation R Γ'₀) :
    (congr v w (.refl R)).symm = congr w v (.refl R) := rfl

@[deprecated "Use `WithVal.congr_apply` instead" (since := "2026-01-27")]
/-
**WithVal.equivWithVal_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：equivWithVal_apply (v : Valuation R Γ₀) (w : Valuation R Γ'₀) {x : WithVal
 v} : congr v w (.refl R) x = (equiv w).symm (equiv v x)
参数：v : Valuation R Γ₀；w : Valuation R Γ'₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithVal.equiv_apply`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrde
redCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (self : WithVa
l v), (Wi…
· 使用定理 `WithVal.equiv_symm_apply`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : Linea
rOrderedCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (ofVal : 
R), (WithVal.e…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivWithVal_apply (v : Valuation R Γ₀) (w : Valuation R Γ'₀) {x : WithVal v} :
    congr v w (.refl R) x = (equiv w).symm (equiv v x) := by simp

@[deprecated "Use `WithVal.congr_symm_apply` instead" (since := "2026-01-27")]
/-
**WithVal.equivWithVal_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：equivWithVal_symm_apply (v : Valuation R Γ₀) (w : Valuation R Γ'₀) {x : Wi
thVal w} : (congr v w (.refl R)).symm x = (equiv v).symm (equiv w x)
参数：v : Valuation R Γ₀；w : Valuation R Γ'₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithVal.equiv_apply`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrde
redCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (self : WithVa
l v), (Wi…
· 使用定理 `WithVal.equiv_symm_apply`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : Linea
rOrderedCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (ofVal : 
R), (WithVal.e…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivWithVal_symm_apply (v : Valuation R Γ₀) (w : Valuation R Γ'₀) {x : WithVal w} :
    (congr v w (.refl R)).symm x = (equiv v).symm (equiv w x) := by simp

end Ring
section ValueGroup₀

variable {R : Type*} [Ring R] (v : Valuation R Γ₀)

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

/-
**WithVal.valueGroup_eq** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：valueGroup_eq : valueGroup (.ofClass (Valued.v (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.range_comp`：∀ {α : Type u_1} {ι : Sort u_3} {ι' : So
rt u_4} {f : ι → ι'},   Function.Surjective f → ∀ (g : ι' → α), Set.range (g ∘ f
) = Set.range g
· 使用引理 `WithVal.ofVal_surjective`：ofVal_surjective : Function.Surjective (ofVal 
(v
· 使用定理 `Subsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Mul M] (carrier car
rier_1 : Set M) (e_carrier : carrier = carrier_1)   (mul_mem' : ∀ {a b : M}, a ∈
 carrier → b ∈ c…
· 使用定理 `Submonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : MulOneClass M] (toSubs
emigroup toSubsemigroup_1 : Subsemigroup M)   (e_toSubsemigroup : toSubsemigroup
 = toSubsemig…
-/
theorem valueGroup_eq : valueGroup (.ofClass (Valued.v (R := WithVal v))) =
    valueGroup (.ofClass v) := by
  simp [valueGroup, valueMonoid, ← (WithVal.ofVal_surjective v).range_comp]
  rfl

/-- The multiplicative equivalence between the `valueGroup` of the valuation on `WithVal v`
and the valuation `v`. -/
@[simps! apply symm_apply]
/-
**WithVal.valueGroupEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithVal`。
形式化陈述：valueGroupEquiv : valueGroup (.ofClass (Valued.v (R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative equivalence between the `valueGroup` of the valuation on `Wit
hVal v`
and the valuation `v`.
-/
def valueGroupEquiv :
    valueGroup (.ofClass (Valued.v (R := WithVal v))) ≃* valueGroup (.ofClass v) where
  __ := Equiv.setCongr (by simp [valueGroup_eq v])
  map_mul' := by simp [Equiv.setCongr, Equiv.subtypeEquivProp]
/-
**WithVal.strictMono_valueGroupEquiv** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：strictMono_valueGroupEquiv : StrictMono (valueGroupEquiv v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithVal.valueGroupEquiv_apply`：∀ {Γ₀ : Type u_2} [inst : LinearOrderedCo
mmGroupWithZero Γ₀] {R : Type u_3} [inst_1 : Ring R] (v : Valuation R Γ₀)   (a :
 { a // (fun x => x…
-/
theorem strictMono_valueGroupEquiv : StrictMono (valueGroupEquiv v) :=
  fun _ _ _ ↦ by simpa
/-
**WithVal.strictMono_valueGroupEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `WithVal`。
形式化陈述：strictMono_valueGroupEquiv_symm : StrictMono (valueGroupEquiv v).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithVal.valueGroupEquiv_symm_apply`：∀ {Γ₀ : Type u_2} [inst : LinearOrde
redCommGroupWithZero Γ₀] {R : Type u_3} [inst_1 : Ring R] (v : Valuation R Γ₀)  
 (b : { b // (fun x => x…
-/
theorem strictMono_valueGroupEquiv_symm : StrictMono (valueGroupEquiv v).symm :=
  fun _ _ _ ↦ by simpa

set_option backward.isDefEq.respectTransparency.types false in
/-- The order-preserving, multiplicative equivalence between the `ValueGroup₀` of the valuation
on `WithVal v` and the valuation `v`. -/
@[simps!]
/-
**WithVal.valueGroupOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order-preserving, multiplicative equivalence between the `ValueGroup₀` of th
e valuation
on `WithVal v` and the valuation `v`.
-/
def valueGroupOrderIso₀ : ValueGroup₀ (.ofClass (Valued.v (R := WithVal v))) ≃*o
    ValueGroup₀ (.ofClass v) where
  toFun := WithZero.map' (valueGroupEquiv v)
  invFun := WithZero.map' (valueGroupEquiv v).symm
  left_inv x := by
    match x with
    | 0 => simp
    | .coe a => simp
  right_inv y := by
    match y with
    | 0 => simp
    | .coe b => simp
  map_mul' := by simp
  map_le_map_iff' {a b} := by
    match a, b with
    | 0, 0 => simp
    | 0, .coe _ => simp
    | .coe _, 0 => simp
    | .coe a, .coe b => simp
/-
**WithVal.valueGroupOrderIso** 是 Mathlib 中的一个引理，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma valueGroupOrderIso₀_restrict (b : WithVal v) :
    valueGroupOrderIso₀ v ((WithVal.valuation v).restrict b) = v.restrict b.ofVal := by
  simp [(WithVal.valuation v).restrict_def, restrict₀_apply, ← valuation_apply_eq_ofVal,
    v.restrict_def]
  by_cases hb : v b.ofVal = 0 <;> simp [hb]
/-
**WithVal.valueGroupOrderIso** 是 Mathlib 中的一个引理，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma valueGroupOrderIso₀_symm_restrict (b : R) :
    (valueGroupOrderIso₀ v).symm (Valuation.restrict v b) = Valued.v.restrict (toVal v b) := by
  simp [Valued.v.restrict_def, restrict₀_apply, ← apply_ofVal, v.restrict_def]
  by_cases hb : v b = 0 <;> simp [hb]
/-
**WithVal.strictMono_valueGroupOrderIso** 是 Mathlib 中的一个引理，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma strictMono_valueGroupOrderIso₀ :
    StrictMono (WithVal.valueGroupOrderIso₀ v) :=
  WithZero.map'_strictMono (strictMono_valueGroupEquiv v)
/-
**WithVal.strictMono_valueGroupOrderIso** 是 Mathlib 中的一个引理，位于命名空间 `WithVal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma strictMono_valueGroupOrderIso₀_symm :
    StrictMono (WithVal.valueGroupOrderIso₀ v).symm :=
  WithZero.map'_strictMono (strictMono_valueGroupEquiv_symm v)

end ValueGroup₀

end WithVal

/-! The completion of a field with respect to a valuation. -/

namespace Valuation

open WithVal

variable {R : Type*} [Ring R] (v : Valuation R Γ₀)

/-- The completion of a field with respect to a valuation. -/
/-
**Valuation.Completion** 是 Mathlib 中的一个缩写定义，位于命名空间 `Valuation`。
形式化陈述：Completion
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The completion of a field with respect to a valuation.
-/
abbrev Completion := UniformSpace.Completion (WithVal v)

-- lower priority so that `Coe (WithVal v) v.Completion` uses `UniformSpace.Completion.instCoe`
/-
**Valuation.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 99) : Coe R v.Completion where
  coe r := (WithVal.equiv v).symm r

section Equivalence

/-! The uniform isomorphism between `WithVal v` and `WithVal w` when `v` and `w` are
equivalent. -/

variable {R Γ₀ Γ₀' : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
  [LinearOrderedCommGroupWithZero Γ₀'] {v : Valuation R Γ₀} {w : Valuation R Γ₀'}

/-- If two valuations `v` and `w` are equivalent then `WithVal v` is order-isomorphic
to `WithVal w`. -/
/-
**Valuation.IsEquiv.orderRingIso** 是 Mathlib 中的一个定义，位于命名空间 `Valuation.IsEquiv`。
形式化陈述：{R : Type u_4} →   {Γ₀ : Type u_5} →     {Γ₀' : Type u_6} →       [inst : 
Ring R] →         [inst_1 : LinearOrderedCommGroupWithZero Γ₀] →           [inst
_2 : LinearOrderedCommGroupWithZero Γ₀'] →             {v : Valuation R Γ₀} → {w
 : Valuation R Γ₀'} → v.IsEquiv w → WithVal v ≃+*o WithVal w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two valuations `v` and `w` are equivalent then `WithVal v` is order-isomorphi
c
to `WithVal w`.
-/
def IsEquiv.orderRingIso (h : v.IsEquiv w) :
    WithVal v ≃+*o WithVal w where
  __ := WithVal.congr v w (.refl R)
  map_le_map_iff' := h.symm ..

@[simp]
/-
**Valuation.IsEquiv.orderRingIso_apply** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEq
uiv`。
形式化陈述：∀ {R : Type u_4} {Γ₀ : Type u_5} {Γ₀' : Type u_6} [inst : Ring R] [inst_1 
: LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : LinearOrderedCommGroupWithZero 
Γ₀'] {v : Valuation R Γ₀} {w : Valuation R Γ₀'} (h : v.IsEquiv w)   (x : WithVal
 v), h.orderRingIso x = WithVal.toVal w x.ofVal
参数：h : v.IsEquiv w；x : WithVal v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsEquiv.orderRingIso_apply (h : v.IsEquiv w) (x : WithVal v) :
    h.orderRingIso x = toVal w x.ofVal := rfl

@[simp]
/-
**Valuation.IsEquiv.orderRingIso_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Valuation
.IsEquiv`。
形式化陈述：∀ {R : Type u_4} {Γ₀ : Type u_5} {Γ₀' : Type u_6} [inst : Ring R] [inst_1 
: LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : LinearOrderedCommGroupWithZero 
Γ₀'] {v : Valuation R Γ₀} {w : Valuation R Γ₀'} (h : v.IsEquiv w)   (x : WithVal
 w), h.orderRingIso.symm x = WithVal.toVal v x.ofVal
参数：h : v.IsEquiv w；x : WithVal w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsEquiv.orderRingIso_symm_apply (h : v.IsEquiv w) (x : WithVal w) :
    h.orderRingIso.symm x = toVal v x.ofVal := rfl

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀
/-
**Valuation.IsEquiv.uniformContinuous_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Valuation
.IsEquiv`。
形式化陈述：∀ {R : Type u_4} {Γ₀ : Type u_5} {Γ₀' : Type u_6} [inst : Ring R] [inst_1 
: LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : LinearOrderedCommGroupWithZero 
Γ₀'] {v : Valuation R Γ₀} {w : Valuation R Γ₀'} [hval : Valued R Γ₀'],   Valued.
v = w → v.IsEquiv w → UniformContinuous ⇑(WithVal.equiv v)
参数：WithVal.equiv v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_of_continuousAt_zero`：∀ {α : Type u_1} {β : Type u_2} 
[inst : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {hom : Type 
u_3}   [inst_3 : UniformSpac…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Valued.hasBasis_nhds_zero`：hasBasis_nhds_zero : (𝓝 (0 : R)).HasBasis (fu
n _ => True) fun γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ => { x | v
.restrict x < γ…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Valuation.exists_div_eq_of_unit`：exists_div_eq_of_unit (γ : (ValueGroup₀
 (.ofClass v))ˣ) : exists r s, 0 < v r ∧ 0 < v s ∧ v.restrict r / v.restrict s =
 γ.1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithVal.equiv_symm_apply`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : Linea
rOrderedCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (ofVal : 
R), (WithVal.e…
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `Valuation.IsEquiv.eq_zero`：eq_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r = 
0 ↔ v₂ r = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 52 条，此处仅展示前 30 条）
-/
theorem IsEquiv.uniformContinuous_equiv [hval : Valued R Γ₀'] (hv : Valued.v = w)
    (h : v.IsEquiv w) : UniformContinuous (WithVal.equiv v) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  obtain ⟨r, s, hr₀, hs₀, hr⟩ := exists_div_eq_of_unit Valued.v γ
  use .mk0 ((instValued v).v.restrict ((WithVal.equiv v).symm r) /
    (instValued v).v.restrict ((WithVal.equiv v).symm s)) (by
    simp [Valuation.restrict_def, restrict₀_eq_zero_iff, (eq_zero h (r := r)).ne, ← hv,
      (eq_zero h (r := s)).ne, hr₀.ne', hs₀.ne'])
  intro x hx
  let y := (WithVal.equiv v) x
  have hy : toVal v y = x := rfl
  have hs0' : 0 < Valued.v.restrict (toVal v s) := by
    simp [restrict_pos_iff, h.pos_iff, ← hv, hs₀]
  have h' : v.restrict.IsEquiv w.restrict := h.restrict
  rw [← hr, equiv_apply, Set.mem_ofPred_eq, lt_div_iff₀ ((restrict_pos_iff Valued.v s).mpr hs₀), hv,
    ← map_mul, ← lt_def, ← ofVal_mul,
    ← hy, ← toVal_mul, ←  h'.orderRingIso_apply, ← h'.orderRingIso.lt_symm_apply]
  simp only [toVal_mul, orderRingIso_symm_apply, lt_def, ofVal_mul, restrict_lt_iff]
  simp only [equiv_symm_apply, Units.val_mk0, Set.mem_ofPred_eq, lt_div_iff₀ hs0'] at hx
  rwa [← map_mul, restrict_lt_iff] at hx
/-
**Valuation.IsEquiv.uniformContinuous_equiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Valu
ation.IsEquiv`。
形式化陈述：∀ {R : Type u_4} {Γ₀ : Type u_5} {Γ₀' : Type u_6} [inst : Ring R] [inst_1 
: LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : LinearOrderedCommGroupWithZero 
Γ₀'] {v : Valuation R Γ₀} {w : Valuation R Γ₀'} [hval : Valued R Γ₀'],   Valued.
v = w → w.IsEquiv v → UniformContinuous ⇑(WithVal.equiv v).symm
参数：WithVal.equiv v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_of_continuousAt_zero`：∀ {α : Type u_1} {β : Type u_2} 
[inst : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {hom : Type 
u_3}   [inst_3 : UniformSpac…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Valued.hasBasis_nhds_zero`：hasBasis_nhds_zero : (𝓝 (0 : R)).HasBasis (fu
n _ => True) fun γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ => { x | v
.restrict x < γ…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Valuation.exists_div_eq_of_unit`：exists_div_eq_of_unit (γ : (ValueGroup₀
 (.ofClass v))ˣ) : exists r s, 0 < v r ∧ 0 < v s ∧ v.restrict r / v.restrict s =
 γ.1
· 使用定理 `Valuation.IsEquiv.restrict`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Rin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)   {Γ₀' : 
Type u_7} [inst_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithVal.equiv_apply`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrde
redCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (self : WithVa
l v), (Wi…
· 使用定理 `MonoidWithZeroHom.ofClass.congr_simp`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : MulZeroOneClass α] [inst_1 : MulZeroOneClass β]   [inst_2 :
 FunLike F α β] [inst_3 : …
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `Valuation.IsEquiv.eq_zero`：eq_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r = 
0 ↔ v₂ r = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `WithVal.equiv_symm_apply`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : Linea
rOrderedCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (ofVal : 
R), (WithVal.e…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 45 条，此处仅展示前 30 条）
-/
theorem IsEquiv.uniformContinuous_equiv_symm [hval : Valued R Γ₀'] (hv : Valued.v = w)
    (h : w.IsEquiv v) : UniformContinuous (WithVal.equiv v).symm := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  obtain ⟨r, s, hr₀, hs₀, hr⟩ := exists_div_eq_of_unit Valued.v γ
  have h' : w.restrict.IsEquiv v.restrict := h.restrict
  use .mk0 ((Valued.v.restrict ((WithVal.equiv v) r)) /
    (Valued.v.restrict ((WithVal.equiv v) s))) (by
    simp only [equiv_apply, restrict_def, ne_eq, div_eq_zero_iff, restrict₀_eq_zero_iff, hv,
      MonoidWithZeroHom.coe_ofClass, not_or, (eq_zero h (r := r.ofVal)).ne,
      (eq_zero h (r := s.ofVal)).ne]
    exact ⟨hr₀.ne', hs₀.ne'⟩)
  intro x hx
  simp only [equiv_symm_apply, Set.mem_ofPred_eq]
  simp only [equiv_apply, Units.val_mk0, Set.mem_ofPred_eq] at hx
  rw [lt_div_iff₀, ← map_mul, restrict_lt_iff, hv, h.lt_iff_lt, map_mul] at hx
  · rw [← hr, lt_div_iff₀ ((restrict_pos_iff Valued.v s).mpr hs₀), ← map_mul, ← lt_def,
      ← h.orderRingIso_apply]
    simp only [orderRingIso_apply, toVal_mul, lt_def, ofVal_mul, restrict_lt_iff]
    rw [map_mul]
    exact hx
  · rw [restrict_pos_iff, hv, h.pos_iff]
    exact hs₀
/-
**Valuation.IsEquiv.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEqu
iv`。
形式化陈述：∀ {R : Type u_4} {Γ₀ : Type u_5} {Γ₀' : Type u_6} [inst : Ring R] [inst_1 
: LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : LinearOrderedCommGroupWithZero 
Γ₀'] {v : Valuation R Γ₀} {w : Valuation R Γ₀'},   v.IsEquiv w → UniformContinuo
us ⇑(RingHom.id R)
参数：RingHom.id R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.IsEquiv.restrict`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Rin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)   {Γ₀' : 
Type u_7} [inst_…
· 使用定理 `uniformContinuous_of_continuousAt_zero`：∀ {α : Type u_1} {β : Type u_2} 
[inst : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {hom : Type 
u_3}   [inst_3 : UniformSpac…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Valued.hasBasis_nhds_zero`：hasBasis_nhds_zero : (𝓝 (0 : R)).HasBasis (fu
n _ => True) fun γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ => { x | v
.restrict x < γ…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidWithZeroHom.mem_valueGroup_iff_of_comm`：mem_valueGroup_iff_of_comm
 {y : Bˣ} : y in valueGroup f ↔ exists a, f a != 0 ∧ exists x, f a * y = f x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MulEquivClass.toMonoidWithZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulZeroOneClass α]   [inst_2 :
 MulZeroOneClass β] [MulEqui…
· 使用定理 `OrderMonoidIso.instMulEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   MulEqui
vClass (α ≃*o β) α β
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 35 条，此处仅展示前 30 条）
-/
lemma IsEquiv.uniformContinuous (h : v.IsEquiv w) :
    @UniformContinuous R R (Valued.mk' w).toUniformSpace (Valued.mk' v).toUniformSpace
      (RingHom.id R) := by
  have h_val : ((Valued.mk' v).v).IsEquiv (Valued.mk' w).v := h
  have h_res : v.restrict.IsEquiv w.restrict := h_val.restrict
  refine @uniformContinuous_of_continuousAt_zero _ _ (Valued.mk' w).toUniformSpace _ _
    _ (Valued.mk' v).toUniformSpace _ _ _ _ (RingHom.id R) ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro x
  let u := WithZero.unzero (Units.ne_zero x)
  obtain ⟨a, ha, y, hu⟩ := (mem_valueGroup_iff_of_comm _).mp u.2
  simp only [Set.mem_ofPred_eq, RingHom.id_apply]
  set y₀ := h_val.orderMonoidIso x with hy₀_def
  have hy₀_ne_zero : y₀ ≠ 0 := by simp [hy₀_def]
  set y := (Units.mk0 y₀ hy₀_ne_zero) with hy_def
  use y
  intro b hb
  rwa [← h_val.orderMonoidIso_spec, hy_def, Units.val_mk0, hy₀_def,
    h_val.orderMonoidIso.strictMono.lt_iff_lt] at hb
/-
**Valuation.IsEquiv.uniformContinuous_congr** 是 Mathlib 中的一个定理，位于命名空间 `Valuation
.IsEquiv`。
形式化陈述：∀ {R : Type u_4} {Γ₀ : Type u_5} {Γ₀' : Type u_6} [inst : Ring R] [inst_1 
: LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : LinearOrderedCommGroupWithZero 
Γ₀'] {v : Valuation R Γ₀} {w : Valuation R Γ₀'},   v.IsEquiv w → UniformContinuo
us ⇑(WithVal.congr v w (RingEquiv.refl R))
参数：WithVal.congr v w (RingEquiv.refl R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingEquiv.ext_iff`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [inst_
1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] {f g : R ≃+* S},   f = g ↔ ∀ (x : R
), f x …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Valuation.IsEquiv.uniformContinuous_equiv`：∀ {R : Type u_4} {Γ₀ : Type u
_5} {Γ₀' : Type u_6} [inst : Ring R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀
]   [inst_2 : LinearOrderedComm…
· 使用定理 `Valuation.IsEquiv.uniformContinuous_equiv_symm`：∀ {R : Type u_4} {Γ₀ : T
ype u_5} {Γ₀' : Type u_6} [inst : Ring R] [inst_1 : LinearOrderedCommGroupWithZe
ro Γ₀]   [inst_2 : LinearOrderedComm…
· 使用定理 `Valuation.IsEquiv.uniformContinuous`：∀ {R : Type u_4} {Γ₀ : Type u_5} {Γ
₀' : Type u_6} [inst : Ring R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [i
nst_2 : LinearOrderedComm…
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
-/
theorem IsEquiv.uniformContinuous_congr (h : v.IsEquiv w) :
    UniformContinuous (WithVal.congr v w (.refl R)) := by
  have hcomp : WithVal.congr v w (.refl R) = _ := RingEquiv.ext_iff.mpr (congrFun rfl)
  have h1 := IsEquiv.uniformContinuous_equiv (hval := Valued.mk' w) rfl h
  have h2 := IsEquiv.uniformContinuous_equiv_symm (hval := Valued.mk' v) rfl h
  have hR : @UniformContinuous R R (Valued.mk' w).toUniformSpace (Valued.mk' v).toUniformSpace
      (RingHom.id R) := h.uniformContinuous
  apply @UniformContinuous.comp (WithVal v) R (WithVal w) _ (Valued.mk' w).toUniformSpace _
    ((RingEquiv.refl R).trans (WithVal.equiv w).symm) (WithVal.equiv v) ?_ h1
  exact @UniformContinuous.comp R R (WithVal w) (Valued.mk' w).toUniformSpace
       (Valued.mk' v).toUniformSpace _ (WithVal.equiv w).symm (RingEquiv.refl R) h2 hR

@[deprecated (since := "2026-01-27")]
  alias IsEquiv.uniformContinuous_equivWithVal := IsEquiv.uniformContinuous_congr

/-- If two valuations `v` and `w` are equivalent then `WithVal v` and `WithVal w` are
isomorphic as uniform spaces. -/
/-
**Valuation.IsEquiv.uniformEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Valuation.IsEquiv`。
形式化陈述：{R : Type u_4} →   {Γ₀ : Type u_5} →     {Γ₀' : Type u_6} →       [inst : 
Ring R] →         [inst_1 : LinearOrderedCommGroupWithZero Γ₀] →           [inst
_2 : LinearOrderedCommGroupWithZero Γ₀'] →             {v : Valuation R Γ₀} → {w
 : Valuation R Γ₀'} → v.IsEquiv w → WithVal v ≃ᵤ WithVal w
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsEquiv.uniformContinuous_congr`：∀ {R : Type u_4} {Γ₀ : Type u
_5} {Γ₀' : Type u_6} [inst : Ring R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀
]   [inst_2 : LinearOrderedComm…

--- 原说明 ---
If two valuations `v` and `w` are equivalent then `WithVal v` and `WithVal w` ar
e
isomorphic as uniform spaces.
-/
def IsEquiv.uniformEquiv (h : v.IsEquiv w) : WithVal v ≃ᵤ WithVal w where
  __ := WithVal.congr v w (.refl R)
  uniformContinuous_toFun := h.uniformContinuous_congr
  uniformContinuous_invFun := h.symm.uniformContinuous_congr

/-- Let `v : Valuation R Γ₀`. If `R` has `Valued R Γ₀'` defined via construction through
`w : Valuation R Γ₀'`, with `v` equivalent to `w`, then `WithVal.equiv` defines a uniform
space isomorphism `WithVal v ≃ᵤ R`. -/
/-
**Valuation._root_.WithVal.uniformEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `v : Valuation R Γ₀`. If `R` has `Valued R Γ₀'` defined via construction thr
ough
`w : Valuation R Γ₀'`, with `v` equivalent to `w`, then `WithVal.equiv` defines 
a uniform
space isomorphism `WithVal v ≃ᵤ R`.
-/
def _root_.WithVal.uniformEquiv [Valued R Γ₀'] (hV : Valued.v = w) (h : v.IsEquiv w) :
    WithVal v ≃ᵤ R where
  __ := WithVal.equiv v
  uniformContinuous_toFun := h.uniformContinuous_equiv hV
  uniformContinuous_invFun := h.symm.uniformContinuous_equiv_symm hV
/-
**Valuation.exists_div_eq_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：exists_div_eq_of_surjective {K : Type*} [DivisionRing K] {Γ₀ : Type*} [Lin
earOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} (hv : Function.Surjective v
) (γ : Γ₀ˣ) : exists r s, 0 < v r ∧ 0 < v s ∧ v r / v s = γ
参数：hv : Function.Surjective v；γ : Γ₀ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem exists_div_eq_of_surjective {K : Type*} [DivisionRing K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} (hv : Function.Surjective v)
    (γ : Γ₀ˣ) : ∃ r s, 0 < v r ∧ 0 < v s ∧ v r / v s = γ := by
  obtain ⟨r, hr⟩ := hv γ
  exact ⟨r, 1, by simp [hr]⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**Valuation.restrict_exists_div_eq** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：restrict_exists_div_eq {K : Type*} [DivisionRing K] {Γ₀ : Type*} [LinearOr
deredCommGroupWithZero Γ₀] (v : Valuation K Γ₀) (γ : (ValueGroup₀ (.ofClass v))ˣ
) : exists r s, 0 < v r ∧ 0 < v s ∧ v.restrict r / v.restrict s = γ.1
参数：v : Valuation K Γ₀；γ : (ValueGroup₀ (.ofClass v))ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective`：∀ {A : Type u_1} {B 
: Type u_2} [inst : GroupWithZero A] [inst_1 : GroupWithZero B] (f : A →*₀ B),  
 Function.Surjective ⇑(MonoidWithZeroHom…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀`：embedding_restrict₀ (
a : A) : ValueGroup₀.embedding (restrict₀ f a) = f a
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_strictMono`：embedding_strictMono
 : StrictMono (embedding (f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithZero.pos_iff_ne_zero`：∀ {α : Type u_1} [inst : LT α] {x : WithZero α
}, 0 < x ↔ x ≠ 0
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
-/
theorem restrict_exists_div_eq {K : Type*} [DivisionRing K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    (γ : (ValueGroup₀ (.ofClass v))ˣ) :
    ∃ r s, 0 < v r ∧ 0 < v s ∧ v.restrict r / v.restrict s = γ.1 := by
  obtain ⟨r, hr⟩ := ValueGroup₀.restrict₀_surjective (.ofClass v) γ
  exact ⟨r, 1, by
    simp only [map_one, zero_lt_one, restrict_def, hr, div_one, and_self, and_true]
    rw [← map_zero v]
    simpa [← hr] using embedding_strictMono (WithZero.pos_iff_ne_zero.mpr (Units.ne_zero γ))⟩

open UniformSpace.Completion in
/-
**Valuation.IsEquiv.valuedCompletion_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valua
tion.IsEquiv`。
形式化陈述：∀ {Γ₀ : Type u_5} {Γ₀' : Type u_6} [inst : LinearOrderedCommGroupWithZero 
Γ₀]   [inst_1 : LinearOrderedCommGroupWithZero Γ₀'] {K : Type u_7} [inst_2 : Fie
ld K] {v : Valuation K Γ₀}   {w : Valuation K Γ₀'} (h : v.IsEquiv w) {x : v.Comp
letion},   Valued.v x ≤ 1 ↔ Valued.v ((UniformSpace.Completion.mapEquiv h.unifor
mEquiv) x) ≤ 1
参数：h : v.IsEquiv w；(UniformSpace.Completion.mapEquiv h.uniformEquiv) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.induction_on`：induction_on {p : Completion α -> 
Prop} (a : Completion α) (hp : IsClosed { a | p a }) (ih : forall a : α, p a) : 
p a
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.restrict_le_one_iff`：restrict_le_one_iff {x : R} : v.restrict 
x <= 1 ↔ v x <= 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.isClosed_setOfPred_iff`：isClosed_setOfPred_iff {p : X -> Prop
} {q : Y -> Prop} (f : X ≃ₜ Y) (hs : IsClopen {x | p x}) (ht : IsClopen {y | q y
}) : IsClosed { x : X |…
· 使用定理 `Valued.isClopen_closedBall`：isClopen_closedBall {r : ValueGroup₀ (.ofCla
ss _i.v)} (hr : r != 0) : IsClopen {x | v.restrict x <= r}
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Valued.valuedCompletion_apply`：valuedCompletion_apply (x : K) : Valued.v
 (x : hat K) = v x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UniformSpace.Completion.mapEquiv_coe`：mapEquiv_coe (e : α ≃ᵤ β) (a : α) 
: mapEquiv e a = (e a)
· 使用引理 `Valuation.IsEquiv.le_one_iff_le_one`：le_one_iff_le_one (h : v₁.IsEquiv v
₂) {x : R} : v₁ x <= 1 ↔ v₂ x <= 1
-/
theorem IsEquiv.valuedCompletion_le_one_iff {K : Type*} [Field K] {v : Valuation K Γ₀}
    {w : Valuation K Γ₀'} (h : v.IsEquiv w) {x : v.Completion} :
    Valued.v x ≤ 1 ↔ Valued.v (mapEquiv h.uniformEquiv x) ≤ 1 := by
  induction x using induction_on with
  | hp =>
    have h1 (x : UniformSpace.Completion (WithVal v)) :
      Valued.v x ≤ 1 ↔ Valued.v.restrict x ≤ 1 := by rw [restrict_le_one_iff]
    simp_rw [h1]
    convert!
      (mapEquiv h.uniformEquiv).toHomeomorph.isClosed_setOfPred_iff
        (Valued.isClopen_closedBall _ one_ne_zero) (Valued.isClopen_closedBall _ one_ne_zero)
    rw [restrict_le_one_iff]
    rfl
  | ih a =>
    simpa [Valued.valuedCompletion_apply] using! h.le_one_iff_le_one

end Equivalence

end Valuation

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] (v : Valuation K Γ₀)

/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeHead (𝓞 (WithVal v)) (WithVal v) where
  coe x := RingOfIntegers.val x
/-
**NumberField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.RingOfInteg
ers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    IsIntegralClosure R ℤ (WithVal v) := .of_algEquiv _ (WithVal.algEquiv ℤ v).symm (fun _ ↦ rfl)

/-- The ring equivalence between `𝓞 (WithVal v)` and an integral closure of
`ℤ` in `K`. -/
@[simps!]
/-
**NumberField.RingOfIntegers.withValEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NumberField
.RingOfIntegers`。
形式化陈述：withValEquiv (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R I
nt K] : 𝓞 (WithVal v) ≃+* R
参数：R : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralClosureIntWithVal`：∀ {Γ₀ : Type
 u_2} [inst : LinearOrderedCommGroupWithZero Γ₀] {K : Type u_3} [inst_1 : Field 
K] (v : Valuation K Γ₀)   (R : Type u_4) [inst_2…

--- 原说明 ---
The ring equivalence between `𝓞 (WithVal v)` and an integral closure of
`ℤ` in `K`.
-/
def withValEquiv (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    𝓞 (WithVal v) ≃+* R := NumberField.RingOfIntegers.equiv R

end NumberField.RingOfIntegers

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
open scoped NumberField in
/-- The ring of integers of `WithVal v`, when `v` is a valuation on `ℚ`, is
equivalent to `ℤ`. -/
@[simps! apply]
/-
**Rat.ringOfIntegersWithValEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Rat.ringOfIntegersWithValEquiv (v : Valuation Rat Γ₀) : 𝓞 (WithVal v) ≃+* 
Int
参数：v : Valuation Rat Γ₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring of integers of `WithVal v`, when `v` is a valuation on `ℚ`, is
equivalent to `ℤ`.
-/
def Rat.ringOfIntegersWithValEquiv (v : Valuation ℚ Γ₀) : 𝓞 (WithVal v) ≃+* ℤ :=
  NumberField.RingOfIntegers.withValEquiv v ℤ
