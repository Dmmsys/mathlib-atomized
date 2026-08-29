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

/--
Definition of `WithVal` / `WithVal` 的定义

English:
structure WithVal
  parameters: [Ring R] (v : Valuation R Γ₀)
  axioms and operations (2):
    - toVal((v)) : :
    - ofVal : R

中文:
结构 WithVal
  参数: [环 R] (v : 赋值 R Γ₀)
  公理与运算 (2 个):
    - toVal((v)) : :
    - ofVal : R
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

/--
lemma `ofVal_toVal` / 引理 `ofVal_toVal`

English:
lemma ofVal_toVal
  given: (x : R)
  statement: ofVal (toVal v x) = x
  proof: rfl

中文:
引理 ofVal_toVal
  条件: (x : R)
  结论: ofVal (toVal v x) = x
  证明: rfl
-/
lemma ofVal_toVal (x : R) : ofVal (toVal v x) = x := rfl
/--
lemma `toVal_ofVal` / 引理 `toVal_ofVal`

English:
lemma toVal_ofVal
  given: (x : WithVal v)
  statement: toVal v (ofVal x) = x
  proof: rfl

中文:
引理 toVal_ofVal
  条件: (x : WithVal v)
  结论: toVal v (ofVal x) = x
  证明: rfl
-/
@[simp] lemma toVal_ofVal (x : WithVal v) : toVal v (ofVal x) = x := rfl

/--
lemma `ofVal_surjective` / 引理 `ofVal_surjective`

English:
lemma ofVal_surjective
  statement: Function.Surjective (ofVal (v := v))
  proof: Function.RightInverse.surjective ofVal_toVal _

中文:
引理 ofVal_surjective
  结论: 函数.满射 (ofVal (v := v))
  证明: Function.RightInverse.surjective ofVal_toVal _
-/
lemma ofVal_surjective : Function.Surjective (ofVal (v := v)) :=
Function.RightInverse.surjective ofVal_toVal _

/--
lemma `toVal_surjective` / 引理 `toVal_surjective`

English:
lemma toVal_surjective
  statement: Function.Surjective (toVal v)
  proof: Function.RightInverse.surjective toVal_ofVal _

中文:
引理 toVal_surjective
  结论: 函数.满射 (toVal v)
  证明: Function.RightInverse.surjective toVal_ofVal _

Depends on / 依赖: Function, Function.RightInverse.surjective, RightInverse, surjective, toVal_ofVal
-/
lemma toVal_surjective : Function.Surjective (toVal v) :=
Function.RightInverse.surjective toVal_ofVal _

/--
lemma `ofVal_injective` / 引理 `ofVal_injective`

English:
lemma ofVal_injective
  statement: Function.Injective (ofVal (v := v))
  proof: Function.LeftInverse.injective toVal_ofVal _

中文:
引理 ofVal_injective
  结论: 函数.单射 (ofVal (v := v))
  证明: Function.LeftInverse.injective toVal_ofVal _
-/
lemma ofVal_injective : Function.Injective (ofVal (v := v)) :=
Function.LeftInverse.injective toVal_ofVal _

/--
lemma `toVal_injective` / 引理 `toVal_injective`

English:
lemma toVal_injective
  statement: Function.Injective (toVal v)
  proof: Function.LeftInverse.injective ofVal_toVal _

中文:
引理 toVal_injective
  结论: 函数.单射 (toVal v)
  证明: Function.LeftInverse.injective ofVal_toVal _

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, injective, ofVal_toVal
-/
lemma toVal_injective : Function.Injective (toVal v) :=
Function.LeftInverse.injective ofVal_toVal _

/--
lemma `ofVal_bijective` / 引理 `ofVal_bijective`

English:
lemma ofVal_bijective
  statement: Function.Bijective (ofVal (v := v))
  proof: ⟨ofVal_injective v, ofVal_surjective v⟩

中文:
引理 ofVal_bijective
  结论: 函数.双射 (ofVal (v := v))
  证明: ⟨ofVal_injective v, ofVal_surjective v⟩
-/
lemma ofVal_bijective : Function.Bijective (ofVal (v := v)) :=
  ⟨ofVal_injective v, ofVal_surjective v⟩

/--
lemma `toVal_bijective` / 引理 `toVal_bijective`

English:
lemma toVal_bijective
  statement: Function.Bijective (toVal v)
  proof: ⟨toVal_injective v, toVal_surjective v⟩

中文:
引理 toVal_bijective
  结论: 函数.双射 (toVal v)
  证明: ⟨toVal_injective v, toVal_surjective v⟩

Depends on / 依赖: toVal_injective, toVal_surjective
-/
lemma toVal_bijective : Function.Bijective (toVal v) :=
  ⟨toVal_injective v, toVal_surjective v⟩


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (WithVal v)
  body: toVal _ 0

中文:
实例 :
  签名: 零 (WithVal v)
  定义体: toVal _ 0
-/
instance : Zero (WithVal v) where zero := toVal _ 0
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (WithVal v)
  body: toVal _ 1

中文:
实例 :
  签名: 幺 (WithVal v)
  定义体: toVal _ 1
-/
instance : One (WithVal v) where one := toVal _ 1
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (WithVal v)
  body: toVal _ (x.ofVal + y.ofVal)

中文:
实例 :
  签名: 加法 (WithVal v)
  定义体: toVal _ (x.ofVal + y.ofVal)

Depends on / 依赖: x.ofVal, y.ofVal
-/
instance : Add (WithVal v) where add x y := toVal _ (x.ofVal + y.ofVal)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (WithVal v)
  body: toVal _ (x.ofVal - y.ofVal)

中文:
实例 :
  签名: 减法 (WithVal v)
  定义体: toVal _ (x.ofVal - y.ofVal)

Depends on / 依赖: x.ofVal, y.ofVal
-/
instance : Sub (WithVal v) where sub x y := toVal _ (x.ofVal - y.ofVal)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (WithVal v)
  body: toVal _ (-x.ofVal)

中文:
实例 :
  签名: 取负 (WithVal v)
  定义体: toVal _ (-x.ofVal)

Depends on / 依赖: x.ofVal
-/
instance : Neg (WithVal v) where neg x := toVal _ (-x.ofVal)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (WithVal v)
  body: toVal _ (x.ofVal * y.ofVal)

中文:
实例 :
  签名: 乘法 (WithVal v)
  定义体: toVal _ (x.ofVal * y.ofVal)

Depends on / 依赖: x.ofVal, y.ofVal
-/
instance : Mul (WithVal v) where mul x y := toVal _ (x.ofVal * y.ofVal)
instance {S} [SMul S R] : SMul S (WithVal v) where smul s x := toVal _ (s • x.ofVal)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (WithVal v) Nat
  body: toVal _ (x.ofVal ^ n)

中文:
实例 :
  签名: 幂 (WithVal v) 自然数
  定义体: toVal _ (x.ofVal ^ n)

Depends on / 依赖: x.ofVal
-/
instance : Pow (WithVal v) Nat where pow x n := toVal _ (x.ofVal ^ n)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (WithVal v)
  body: toVal _ n

中文:
实例 :
  签名: 自然数嵌入 (WithVal v)
  定义体: toVal _ n
-/
instance : NatCast (WithVal v) where natCast n := toVal _ n
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IntCast (WithVal v)
  body: toVal _ z

中文:
实例 :
  签名: 整数嵌入 (WithVal v)
  定义体: toVal _ z
-/
instance : IntCast (WithVal v) where intCast z := toVal _ z

/--
lemma `toVal_zero` / 引理 `toVal_zero`

English:
lemma toVal_zero
  statement: toVal v 0 = 0
  proof: rfl

中文:
引理 toVal_zero
  结论: toVal v 0 = 0
  证明: rfl
-/
@[simp] lemma toVal_zero : toVal v 0 = 0 := rfl

/--
lemma `ofVal_zero` / 引理 `ofVal_zero`

English:
lemma ofVal_zero
  statement: ofVal (0 : WithVal v) = 0
  proof: rfl

中文:
引理 ofVal_zero
  结论: ofVal (0 : WithVal v) = 0
  证明: rfl
-/
@[simp] lemma ofVal_zero : ofVal (0 : WithVal v) = 0 := rfl

/--
lemma `toVal_one` / 引理 `toVal_one`

English:
lemma toVal_one
  statement: toVal v 1 = 1
  proof: rfl

中文:
引理 toVal_one
  结论: toVal v 1 = 1
  证明: rfl
-/
@[simp] lemma toVal_one : toVal v 1 = 1 := rfl

/--
lemma `ofVal_one` / 引理 `ofVal_one`

English:
lemma ofVal_one
  statement: ofVal (1 : WithVal v) = 1
  proof: rfl

中文:
引理 ofVal_one
  结论: ofVal (1 : WithVal v) = 1
  证明: rfl
-/
@[simp] lemma ofVal_one : ofVal (1 : WithVal v) = 1 := rfl

/--
lemma `toVal_add` / 引理 `toVal_add`

English:
lemma toVal_add
  given: (x y : R)
  statement: toVal v (x + y) = toVal v x + toVal v y
  proof: rfl

中文:
引理 toVal_add
  条件: (x y : R)
  结论: toVal v (x + y) = toVal v x + toVal v y
  证明: rfl
-/
@[simp] lemma toVal_add (x y : R) : toVal v (x + y) = toVal v x + toVal v y := rfl

/--
lemma `ofVal_add` / 引理 `ofVal_add`

English:
lemma ofVal_add
  given: (x y : WithVal v)
  statement: ofVal (x + y) = ofVal x + ofVal y
  proof: rfl

中文:
引理 ofVal_add
  条件: (x y : WithVal v)
  结论: ofVal (x + y) = ofVal x + ofVal y
  证明: rfl
-/
@[simp] lemma ofVal_add (x y : WithVal v) : ofVal (x + y) = ofVal x + ofVal y := rfl

/--
lemma `toVal_sub` / 引理 `toVal_sub`

English:
lemma toVal_sub
  given: (x y : R)
  statement: toVal v (x - y) = toVal v x - toVal v y
  proof: rfl

中文:
引理 toVal_sub
  条件: (x y : R)
  结论: toVal v (x - y) = toVal v x - toVal v y
  证明: rfl
-/
@[simp] lemma toVal_sub (x y : R) : toVal v (x - y) = toVal v x - toVal v y := rfl

/--
lemma `ofVal_sub` / 引理 `ofVal_sub`

English:
lemma ofVal_sub
  given: (x y : WithVal v)
  statement: ofVal (x - y) = ofVal x - ofVal y
  proof: rfl

中文:
引理 ofVal_sub
  条件: (x y : WithVal v)
  结论: ofVal (x - y) = ofVal x - ofVal y
  证明: rfl
-/
@[simp] lemma ofVal_sub (x y : WithVal v) : ofVal (x - y) = ofVal x - ofVal y := rfl

/--
lemma `toVal_mul` / 引理 `toVal_mul`

English:
lemma toVal_mul
  given: (x y : R)
  statement: toVal v (x * y) = toVal v x * toVal v y
  proof: rfl

中文:
引理 toVal_mul
  条件: (x y : R)
  结论: toVal v (x * y) = toVal v x * toVal v y
  证明: rfl
-/
@[simp] lemma toVal_mul (x y : R) : toVal v (x * y) = toVal v x * toVal v y := rfl

/--
lemma `ofVal_mul` / 引理 `ofVal_mul`

English:
lemma ofVal_mul
  given: (x y : WithVal v)
  statement: ofVal (x * y) = ofVal x * ofVal y
  proof: rfl

中文:
引理 ofVal_mul
  条件: (x y : WithVal v)
  结论: ofVal (x * y) = ofVal x * ofVal y
  证明: rfl
-/
@[simp] lemma ofVal_mul (x y : WithVal v) : ofVal (x * y) = ofVal x * ofVal y := rfl

/--
lemma `toVal_neg` / 引理 `toVal_neg`

English:
lemma toVal_neg
  given: (x : R)
  statement: toVal v (-x) = -toVal v x
  proof: rfl

中文:
引理 toVal_neg
  条件: (x : R)
  结论: toVal v (-x) = -toVal v x
  证明: rfl
-/
@[simp] lemma toVal_neg (x : R) : toVal v (-x) = -toVal v x := rfl

/--
lemma `ofVal_neg` / 引理 `ofVal_neg`

English:
lemma ofVal_neg
  given: (x : WithVal v)
  statement: ofVal (-x) = -ofVal x
  proof: rfl

中文:
引理 ofVal_neg
  条件: (x : WithVal v)
  结论: ofVal (-x) = -ofVal x
  证明: rfl
-/
@[simp] lemma ofVal_neg (x : WithVal v) : ofVal (-x) = -ofVal x := rfl

/--
lemma `toVal_pow` / 引理 `toVal_pow`

English:
lemma toVal_pow
  given: (x : R) (n : Nat)
  statement: toVal v (x ^ n) = (toVal v x) ^ n
  proof: rfl

中文:
引理 toVal_pow
  条件: (x : R) (n : 自然数)
  结论: toVal v (x ^ n) = (toVal v x) ^ n
  证明: rfl
-/
@[simp] lemma toVal_pow (x : R) (n : Nat) : toVal v (x ^ n) = (toVal v x) ^ n := rfl

/--
lemma `ofVal_pow` / 引理 `ofVal_pow`

English:
lemma ofVal_pow
  given: (x : WithVal v) (n : Nat)
  statement: ofVal (x ^ n) = (ofVal x) ^ n
  proof: rfl

中文:
引理 ofVal_pow
  条件: (x : WithVal v) (n : 自然数)
  结论: ofVal (x ^ n) = (ofVal x) ^ n
  证明: rfl
-/
@[simp] lemma ofVal_pow (x : WithVal v) (n : Nat) : ofVal (x ^ n) = (ofVal x) ^ n := rfl

/--
theorem `toVal_smul` / 定理 `toVal_smul`

English:
theorem toVal_smul
  given: {S} [SMul S R] (s : S) (r : R)
  statement: toVal v (s • r) = s • toVal v r
  proof: rfl

中文:
定理 toVal_smul
  条件: {S} [标量乘法 S R] (s : S) (r : R)
  结论: toVal v (s • r) = s • toVal v r
  证明: rfl
-/
@[simp] theorem toVal_smul {S} [SMul S R] (s : S) (r : R) : toVal v (s • r) = s • toVal v r := rfl

/--
theorem `ofVal_smul` / 定理 `ofVal_smul`

English:
theorem ofVal_smul
  given: {S} [SMul S R] (s : S) (x : WithVal v)
  statement: ofVal (s • x) = s • ofVal x
  proof: rfl

中文:
定理 ofVal_smul
  条件: {S} [标量乘法 S R] (s : S) (x : WithVal v)
  结论: ofVal (s • x) = s • ofVal x
  证明: rfl
-/
@[simp] theorem ofVal_smul {S} [SMul S R] (s : S) (x : WithVal v) : ofVal (s • x) = s • ofVal x :=
  rfl

/--
lemma `toVal_natCast` / 引理 `toVal_natCast`

English:
lemma toVal_natCast
  given: (n : Nat)
  statement: toVal v n = n
  proof: rfl

中文:
引理 toVal_natCast
  条件: (n : 自然数)
  结论: toVal v n = n
  证明: rfl
-/
@[simp] lemma toVal_natCast (n : Nat) : toVal v n = n := rfl

/--
lemma `ofVal_natCast` / 引理 `ofVal_natCast`

English:
lemma ofVal_natCast
  given: (n : Nat)
  statement: ofVal (n : WithVal v) = n
  proof: rfl

中文:
引理 ofVal_natCast
  条件: (n : 自然数)
  结论: ofVal (n : WithVal v) = n
  证明: rfl
-/
@[simp] lemma ofVal_natCast (n : Nat) : ofVal (n : WithVal v) = n := rfl

/--
lemma `toVal_intCast` / 引理 `toVal_intCast`

English:
lemma toVal_intCast
  given: (z : Int)
  statement: toVal v z = z
  proof: rfl

中文:
引理 toVal_intCast
  条件: (z : 整数)
  结论: toVal v z = z
  证明: rfl
-/
@[simp] lemma toVal_intCast (z : Int) : toVal v z = z := rfl

/--
lemma `ofVal_intCast` / 引理 `ofVal_intCast`

English:
lemma ofVal_intCast
  given: (z : Int)
  statement: ofVal (z : WithVal v) = z
  proof: rfl

.ring _ instance : Ring (WithVal v) := fast_instance% ofVal_injective v
  (ofVal_zero _) (ofVal_one _) (ofVal_add _) (ofVal_mul _) (ofVal_neg _) (ofVal_sub _)
  (ofVal_smul _) (ofVal_smul _) (ofVal_pow _) (ofVal_natCast _) (ofVal_intCast _)

中文:
引理 ofVal_intCast
  条件: (z : 整数)
  结论: ofVal (z : WithVal v) = z
  证明: rfl

.ring _ instance : Ring (WithVal v) := fast_instance% ofVal_injective v
  (ofVal_zero _) (ofVal_one _) (ofVal_add _) (ofVal_mul _) (ofVal_neg _) (ofVal_sub _)
  (ofVal_smul _) (ofVal_smul _) (ofVal_pow _) (ofVal_natCast _) (ofVal_intCast _)
-/
@[simp] lemma ofVal_intCast (z : Int) : ofVal (z : WithVal v) = z := rfl

.ring _ instance : Ring (WithVal v) := fast_instance% ofVal_injective v
  (ofVal_zero _) (ofVal_one _) (ofVal_add _) (ofVal_mul _) (ofVal_neg _) (ofVal_sub _)
  (ofVal_smul _) (ofVal_smul _) (ofVal_pow _) (ofVal_natCast _) (ofVal_intCast _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (WithVal v)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (WithVal v)
  定义体: ⟨0⟩
-/
instance : Inhabited (WithVal v) := ⟨0⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder (WithVal v)
  body: .lift (v ∘ ofVal)

中文:
实例 :
  签名: 预序 (WithVal v)
  定义体: .lift (v ∘ ofVal)
-/
instance : Preorder (WithVal v) := .lift (v ∘ ofVal)

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {v : Valuation R Γ₀} {a b : WithVal v}
  statement: a <= b ↔ v a.ofVal <= v b.ofVal
  proof: .rfl

中文:
定理 le_def
  条件: {v : 赋值 R Γ₀} {a b : WithVal v}
  结论: a <= b ↔ v a.ofVal <= v b.ofVal
  证明: .rfl
-/
theorem le_def {v : Valuation R Γ₀} {a b : WithVal v} : a <= b ↔ v a.ofVal <= v b.ofVal := .rfl

/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  given: {v : Valuation R Γ₀} {a b : WithVal v}
  statement: a < b ↔ v a.ofVal < v b.ofVal
  proof: .rfl

中文:
定理 lt_def
  条件: {v : 赋值 R Γ₀} {a b : WithVal v}
  结论: a < b ↔ v a.ofVal < v b.ofVal
  证明: .rfl
-/
theorem lt_def {v : Valuation R Γ₀} {a b : WithVal v} : a < b ↔ v a.ofVal < v b.ofVal := .rfl

/--
lemma `toVal_eq_zero` / 引理 `toVal_eq_zero`

English:
lemma toVal_eq_zero
  given: (x : R)
  statement: toVal v x = 0 ↔ x = 0
  proof: (toVal_injective v).eq_iff

中文:
引理 toVal_eq_zero
  条件: (x : R)
  结论: toVal v x = 0 ↔ x = 0
  证明: (toVal_injective v).eq_iff
-/
@[simp] lemma toVal_eq_zero (x : R) : toVal v x = 0 ↔ x = 0 := (toVal_injective v).eq_iff

/--
lemma `ofVal_eq_zero` / 引理 `ofVal_eq_zero`

English:
lemma ofVal_eq_zero
  given: (x : WithVal v)
  statement: ofVal x = 0 ↔ x = 0
  proof: (ofVal_injective v).eq_iff

中文:
引理 ofVal_eq_zero
  条件: (x : WithVal v)
  结论: ofVal x = 0 ↔ x = 0
  证明: (ofVal_injective v).eq_iff
-/
@[simp] lemma ofVal_eq_zero (x : WithVal v) : ofVal x = 0 ↔ x = 0 := (ofVal_injective v).eq_iff

/-- The canonical ring equivalence between `WithVal v` and `R`. -/
@[simps apply symm_apply]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : WithVal v ≃+* R where
  body: ofVal
  invFun := toVal v
  map_add' := ofVal_add v
  map_mul' := ofVal_mul v

中文:
定义 equiv
  签名: : WithVal v ≃+* R where
  定义体: ofVal
  invFun := toVal v
  map_add' := ofVal_add v
  map_mul' := ofVal_mul v
-/
def equiv : WithVal v ≃+* R where
  toFun := ofVal
  invFun := toVal v
  map_add' := ofVal_add v
  map_mul' := ofVal_mul v

variable {S : Type*} [Ring S] {Λ₀ : Type*} [LinearOrderedCommGroupWithZero Λ₀] (w : Valuation S Λ₀)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : R ->+* S)
  body: (equiv w).symm.toRingHom.comp (f.comp (equiv v))

中文:
定义 map
  签名: (f : R ->+* S)
  定义体: (equiv w).symm.toRingHom.comp (f.comp (equiv v))

Depends on / 依赖: f.comp, symm.toRingHom.comp, toRingHom
-/
def map (f : R ->+* S) : WithVal v ->+* WithVal w := (equiv w).symm.toRingHom.comp (f.comp (equiv v))

/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map v v (.id R) = .id (WithVal v)
  proof: rfl

中文:
定理 map_id
  结论: map v v (.id R) = .id (WithVal v)
  证明: rfl
-/
@[simp] theorem map_id : map v v (.id R) = .id (WithVal v) := rfl

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: {T : Type*} [Ring T] (u : Valuation T Γ₀) (f : S ->+* T) (g : R ->+* S)
  proof: rfl

中文:
定理 map_comp
  条件: {T : 类型} [环 T] (u : 赋值 T Γ₀) (f : S ->+* T) (g : R ->+* S)
  证明: rfl
-/
@[simp] theorem map_comp {T : Type*} [Ring T] (u : Valuation T Γ₀) (f : S ->+* T) (g : R ->+* S) :
    map v u (f.comp g) = (map w u f).comp (map v w g) := rfl

/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: (f : R ->+* S) (x : WithVal v)
  statement: map v w f x = toVal w (f x.ofVal)
  proof: rfl

中文:
定理 map_apply
  条件: (f : R ->+* S) (x : WithVal v)
  结论: map v w f x = toVal w (f x.ofVal)
  证明: rfl
-/
@[simp] theorem map_apply (f : R ->+* S) (x : WithVal v) : map v w f x = toVal w (f x.ofVal) := rfl

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (f : R ≃+* S)
  body: map v w f.toRingHom
  invFun := map w v f.symm.toRingHom
  left_inv _ := by simp
  right_inv _ := by simp

中文:
定义 congr
  签名: (f : R ≃+* S)
  定义体: map v w f.toRingHom
  invFun := map w v f.symm.toRingHom
  left_inv _ := by simp
  right_inv _ := by simp

Depends on / 依赖: f.toRingHom, toRingHom
-/
def congr (f : R ≃+* S) : WithVal v ≃+* WithVal w where
  __ := map v w f.toRingHom
  invFun := map w v f.symm.toRingHom
  left_inv _ := by simp
  right_inv _ := by simp

/--
theorem `congr_refl` / 定理 `congr_refl`

English:
theorem congr_refl
  statement: congr v v (.refl R) = .refl (WithVal v)
  proof: rfl

中文:
定理 congr_refl
  结论: congr v v (.refl R) = .refl (WithVal v)
  证明: rfl
-/
@[simp] theorem congr_refl : congr v v (.refl R) = .refl (WithVal v) := rfl

/--
theorem `congr_symm` / 定理 `congr_symm`

English:
theorem congr_symm
  given: (f : R ≃+* S)
  statement: (congr v w f).symm = congr w v f.symm
  proof: rfl

中文:
定理 congr_symm
  条件: (f : R ≃+* S)
  结论: (congr v w f).symm = congr w v f.symm
  证明: rfl
-/
theorem congr_symm (f : R ≃+* S) : (congr v w f).symm = congr w v f.symm := rfl

/--
theorem `congr_trans` / 定理 `congr_trans`

English:
theorem congr_trans
  given: {T : Type*} [Ring T] (u : Valuation T Γ₀) (f : R ≃+* S) (g : S ≃+* T)
  proof: rfl

中文:
定理 congr_trans
  条件: {T : 类型} [环 T] (u : 赋值 T Γ₀) (f : R ≃+* S) (g : S ≃+* T)
  证明: rfl
-/
theorem congr_trans {T : Type*} [Ring T] (u : Valuation T Γ₀) (f : R ≃+* S) (g : S ≃+* T) :
    congr v u (f.trans g) = (congr v w f).trans (congr w u g) := rfl

/--
theorem `congr_apply` / 定理 `congr_apply`

English:
theorem congr_apply
  given: (f : R ≃+* S) (x : WithVal v)
  proof: rfl

中文:
定理 congr_apply
  条件: (f : R ≃+* S) (x : WithVal v)
  证明: rfl
-/
@[simp] theorem congr_apply (f : R ≃+* S) (x : WithVal v) :
    congr v w f x = toVal w (f x.ofVal) := rfl

/--
theorem `congr_symm_apply` / 定理 `congr_symm_apply`

English:
theorem congr_symm_apply
  given: (f : R ≃+* S) (x : WithVal w)
  proof: rfl

中文:
定理 congr_symm_apply
  条件: (f : R ≃+* S) (x : WithVal w)
  证明: rfl
-/
@[simp] theorem congr_symm_apply (f : R ≃+* S) (x : WithVal w) :
    (congr v w f).symm x = toVal v (f.symm x.ofVal) := rfl

/--
Definition of `valuation` / `valuation` 的定义

English:
definition valuation
  signature: : Valuation (WithVal v) Γ₀
  body: v.comap (equiv v)

中文:
定义 valuation
  签名: : 赋值 (WithVal v) Γ₀
  定义体: v.comap (equiv v)

Depends on / 依赖: v.comap
-/
def valuation : Valuation (WithVal v) Γ₀ := v.comap (equiv v)

/--
lemma `valuation_toVal` / 引理 `valuation_toVal`

English:
lemma valuation_toVal
  given: (x : R)
  statement: valuation v (toVal v x) = v x
  proof: rfl

中文:
引理 valuation_toVal
  条件: (x : R)
  结论: valuation v (toVal v x) = v x
  证明: rfl
-/
@[simp] lemma valuation_toVal (x : R) : valuation v (toVal v x) = v x := rfl

/--
lemma `valuation_apply_eq_ofVal` / 引理 `valuation_apply_eq_ofVal`

English:
lemma valuation_apply_eq_ofVal
  given: (x : WithVal v)
  statement: valuation v x = v x.ofVal
  proof: rfl

中文:
引理 valuation_apply_eq_ofVal
  条件: (x : WithVal v)
  结论: valuation v x = v x.ofVal
  证明: rfl
-/
@[simp] lemma valuation_apply_eq_ofVal (x : WithVal v) : valuation v x = v x.ofVal := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Valued (WithVal v) Γ₀
  body: Valued.mk' (valuation v)

中文:
实例 :
  签名: 赋值 (WithVal v) Γ₀
  定义体: Valued.mk' (valuation v)

Depends on / 依赖: Valued, Valued.mk, valuation
-/
instance : Valued (WithVal v) Γ₀ := Valued.mk' (valuation v)

/--
theorem `apply_ofVal` / 定理 `apply_ofVal`

English:
theorem apply_ofVal
  given: (r : WithVal v)
  statement: v r.ofVal = Valued.v r
  proof: rfl

中文:
定理 apply_ofVal
  条件: (r : WithVal v)
  结论: v r.ofVal = 赋值.v r
  证明: rfl
-/
theorem apply_ofVal (r : WithVal v) : v r.ofVal = Valued.v r := rfl

/--
theorem `val_apply_equiv` / 定理 `val_apply_equiv`

English:
theorem val_apply_equiv
  given: (r : WithVal v)
  statement: v (equiv v r) = Valued.v r
  proof: rfl

中文:
定理 val_apply_equiv
  条件: (r : WithVal v)
  结论: v (equiv v r) = 赋值.v r
  证明: rfl
-/
theorem val_apply_equiv (r : WithVal v) : v (equiv v r) = Valued.v r := rfl

/--
theorem `valued_toVal` / 定理 `valued_toVal`

English:
theorem valued_toVal
  given: (r : R)
  statement: Valued.v (toVal v r) = v r
  proof: rfl

@[deprecated (since := "2026-03-02")] alias apply_equiv := apply_ofVal
@[deprecated (since := "2026-03-02")] alias apply_symm_equiv := valued_toVal

中文:
定理 valued_toVal
  条件: (r : R)
  结论: 赋值.v (toVal v r) = v r
  证明: rfl

@[deprecated (since := "2026-03-02")] alias apply_equiv := apply_ofVal
@[deprecated (since := "2026-03-02")] alias apply_symm_equiv := valued_toVal
-/
@[simp] theorem valued_toVal (r : R) : Valued.v (toVal v r) = v r := rfl

@[deprecated (since := "2026-03-02")] alias apply_equiv := apply_ofVal
@[deprecated (since := "2026-03-02")] alias apply_symm_equiv := valued_toVal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CharZero
  signature: R] : CharZero (WithVal v)
  body: .of_addMonoidHom (equiv v).symm.toAddMonoidHom (by simp) (equiv v).symm.injective

中文:
实例 [特征零
  签名: R] : 特征零 (WithVal v)
  定义体: .of_addMonoidHom (equiv v).symm.toAddMonoidHom (by simp) (equiv v).symm.injective

Depends on / 依赖: injective, of_addMonoidHom, symm.injective, symm.toAddMonoidHom, toAddMonoidHom
-/
instance [CharZero R] : CharZero (WithVal v) :=
  .of_addMonoidHom (equiv v).symm.toAddMonoidHom (by simp) (equiv v).symm.injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ValuativeRel (WithVal v)
  body: fast_instance% .ofValuation (valuation v)

中文:
实例 :
  签名: ValuativeRel (WithVal v)
  定义体: fast_instance% .ofValuation (valuation v)

Depends on / 依赖: fast_instance, ofValuation, valuation
-/
instance : ValuativeRel (WithVal v) := fast_instance% .ofValuation (valuation v)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (valuation v).Compatible
  body: .ofValuation (valuation v)

中文:
实例 :
  签名: (valuation v).余mpatible
  定义体: .ofValuation (valuation v)

Depends on / 依赖: ofValuation, valuation
-/
instance : (valuation v).Compatible := .ofValuation (valuation v)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsValuativeTopology (WithVal v)
  body: by
    simp only [Set.image_add_left, Set.preimage_ofPred_eq, Valued.mem_nhds]
    let e := ValuativeRel.ValueGroupWithZero.orderMonoidIso (valuation v)
    apply e.unitsCongr.symm.exists_congr fun a => ?_
    simp [-OrderMonoidIso.val_unitsCongr_symm_apply, OrderMonoidIso.unitsCongr_symm_apply,
      e.lt_symm_apply, e, ← Valuation.restrict_def, sub_eq_neg_add]
    rfl

中文:
实例 :
  签名: 是赋值拓扑 (WithVal v)
  定义体: by
    simp only [Set.image_add_left, Set.preimage_ofPred_eq, Valued.mem_nhds]
    let e := ValuativeRel.ValueGroupWithZero.orderMonoidIso (valuation v)
    apply e.unitsCongr.symm.exists_congr fun a => ?_
    simp [-OrderMonoidIso.val_unitsCongr_symm_apply, OrderMonoidIso.unitsCongr_symm_apply,
      e.lt_symm_apply, e, ← Valuation.restrict_def, sub_eq_neg_add]
    rfl

Depends on / 依赖: OrderMonoidIso, OrderMonoidIso.unitsCongr_symm_apply, OrderMonoidIso.val_unitsCongr_symm_apply, Set.image_add_left, Set.preimage_ofPred_eq, Valuation, Valuation.restrict_def, ValuativeRel, ValuativeRel.ValueGroupWithZero.orderMonoidIso, ValueGroupWithZero, Valued, Valued.mem_nhds, e.lt_symm_apply, e.unitsCongr.symm.exists_congr, exists_congr, image_add_left, lt_symm_apply, mem_nhds, orderMonoidIso, preimage_ofPred_eq
-/
instance : IsValuativeTopology (WithVal v) where
  mem_nhds_iff {s x} := by
    simp only [Set.image_add_left, Set.preimage_ofPred_eq, Valued.mem_nhds]
    let e := ValuativeRel.ValueGroupWithZero.orderMonoidIso (valuation v)
    apply e.unitsCongr.symm.exists_congr fun a => ?_
    simp [-OrderMonoidIso.val_unitsCongr_symm_apply, OrderMonoidIso.unitsCongr_symm_apply,
      e.lt_symm_apply, e, ← Valuation.restrict_def, sub_eq_neg_add]
    rfl

end Ring

section CommRing

variable [CommRing R] (v : Valuation R Γ₀)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (WithVal v)
  body: fast_instance% (equiv v).commRing

中文:
实例 :
  签名: 交换环 (WithVal v)
  定义体: fast_instance% (equiv v).commRing

Depends on / 依赖: commRing, fast_instance
-/
instance : CommRing (WithVal v) := fast_instance% (equiv v).commRing

end CommRing

section Module

variable [Ring R] (v : Valuation R Γ₀) {S : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R S] : SMul (WithVal v) S where
  body: ofVal x • s

中文:
实例 [标量乘法
  签名: R S] : 标量乘法 (WithVal v) S where
  定义体: ofVal x • s
-/
instance [SMul R S] : SMul (WithVal v) S where
  smul x s := ofVal x • s

/--
theorem `smul_left_def` / 定理 `smul_left_def`

English:
theorem smul_left_def
  given: [SMul R S] (x : WithVal v) (s : S)
  statement: x • s = ofVal x • s
  proof: rfl

中文:
定理 smul_left_def
  条件: [标量乘法 R S] (x : WithVal v) (s : S)
  结论: x • s = ofVal x • s
  证明: rfl
-/
theorem smul_left_def [SMul R S] (x : WithVal v) (s : S) : x • s = ofVal x • s := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R S] [FaithfulSMul R S] : FaithfulSMul (WithVal v) S where
  body: ofVal_injective v FaithfulSMul.eq_of_smul_eq_smul h

中文:
实例 [标量乘法
  签名: R S] [忠实标量乘法 R S] : 忠实标量乘法 (WithVal v) S where
  定义体: ofVal_injective v FaithfulSMul.eq_of_smul_eq_smul h

Depends on / 依赖: FaithfulSMul, FaithfulSMul.eq_of_smul_eq_smul, eq_of_smul_eq_smul, ofVal_injective
-/
instance [SMul R S] [FaithfulSMul R S] : FaithfulSMul (WithVal v) S where
eq_of_smul_eq_smul h := ofVal_injective v FaithfulSMul.eq_of_smul_eq_smul h

/--
theorem `smul_right_def` / 定理 `smul_right_def`

English:
theorem smul_right_def
  given: [SMul S R] (s : S) (x : WithVal v)
  statement: s • x = toVal v (s • ofVal x)
  proof: rfl

中文:
定理 smul_right_def
  条件: [标量乘法 S R] (s : S) (x : WithVal v)
  结论: s • x = toVal v (s • ofVal x)
  证明: rfl
-/
theorem smul_right_def [SMul S R] (s : S) (x : WithVal v) : s • x = toVal v (s • ofVal x) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S R] [FaithfulSMul S R] : FaithfulSMul S (WithVal v) where
  body: by
    simp only [smul_right_def, toVal.injEq] at h
    exact FaithfulSMul.eq_of_smul_eq_smul fun r => h (toVal v r)

中文:
实例 [标量乘法
  签名: S R] [忠实标量乘法 S R] : 忠实标量乘法 S (WithVal v) where
  定义体: by
    simp only [smul_right_def, toVal.injEq] at h
    exact FaithfulSMul.eq_of_smul_eq_smul fun r => h (toVal v r)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.eq_of_smul_eq_smul, eq_of_smul_eq_smul, smul_right_def, toVal.injEq
-/
instance [SMul S R] [FaithfulSMul S R] : FaithfulSMul S (WithVal v) where
  eq_of_smul_eq_smul h := by
    simp only [smul_right_def, toVal.injEq] at h
    exact FaithfulSMul.eq_of_smul_eq_smul fun r => h (toVal v r)

instance {P : Type*} [SMul S P] [SMul R S] [SMul R P]
    [IsScalarTower R S P] (v : Valuation R Γ₀) : IsScalarTower (WithVal v) S P where
  smul_assoc := by simp [smul_left_def]

instance {P : Type*} [Ring S] [SMul P S] [SMul R S] [SMul P R]
    [IsScalarTower P R S] (v : Valuation S Γ₀) : IsScalarTower P R (WithVal v) :=
  (equiv v).isScalarTower P R

instance {P : Type*} [Ring S] [SMul P R] [SMul S R] [SMul P S]
    [IsScalarTower P S R] (v : Valuation S Γ₀) : IsScalarTower P (WithVal v) R where
  smul_assoc := by simp [smul_right_def, smul_left_def, -toVal_smul]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: S] [Module R S] : Module (WithVal v) S
  body: fast_instance% .compHom S (equiv v).toRingHom

中文:
实例 [加法交换幺半群
  签名: S] [模 R S] : 模 (WithVal v) S
  定义体: fast_instance% .compHom S (equiv v).toRingHom

Depends on / 依赖: compHom, fast_instance, toRingHom
-/
instance [AddCommMonoid S] [Module R S] : Module (WithVal v) S :=
  fast_instance% .compHom S (equiv v).toRingHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: S] [Module R S] [Module.Finite R S] :
  body: .of_restrictScalars_finite R (WithVal v) S

中文:
实例 [加法交换幺半群
  签名: S] [模 R S] [模.有限 R S] :
  定义体: .of_restrictScalars_finite R (WithVal v) S

Depends on / 依赖: WithVal, of_restrictScalars_finite
-/
instance [AddCommMonoid S] [Module R S] [Module.Finite R S] :
    Module.Finite (WithVal v) S := .of_restrictScalars_finite R (WithVal v) S

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: S] [Module S R] : Module S (WithVal v)
  body: fast_instance% (equiv v).module S

中文:
实例 [半环
  签名: S] [模 S R] : 模 S (WithVal v)
  定义体: fast_instance% (equiv v).module S

Depends on / 依赖: fast_instance, module
-/
instance [Semiring S] [Module S R] : Module S (WithVal v) :=
  fast_instance% (equiv v).module S

variable [Ring S] [Module R S] (v : Valuation S Γ₀)

variable (R) in
/--
Definition of `linearEquiv` / `linearEquiv` 的定义

English:
definition linearEquiv
  signature: : WithVal v ≃ₗ[R] S
  body: (equiv v).linearEquiv R

中文:
定义 linearEquiv
  签名: : WithVal v ≃ₗ[R] S
  定义体: (equiv v).linearEquiv R

Depends on / 依赖: linearEquiv
-/
def linearEquiv : WithVal v ≃ₗ[R] S := (equiv v).linearEquiv R

/--
theorem `linearEquiv_apply` / 定理 `linearEquiv_apply`

English:
theorem linearEquiv_apply
  given: (x : WithVal v)
  statement: linearEquiv R v x = x.ofVal
  proof: rfl

中文:
定理 linearEquiv_apply
  条件: (x : WithVal v)
  结论: linearEquiv R v x = x.ofVal
  证明: rfl
-/
@[simp] theorem linearEquiv_apply (x : WithVal v) : linearEquiv R v x = x.ofVal := rfl

/--
theorem `linearEquiv_symm_apply` / 定理 `linearEquiv_symm_apply`

English:
theorem linearEquiv_symm_apply
  given: (x : S)
  statement: (linearEquiv R v).symm x = toVal v x
  proof: rfl

中文:
定理 linearEquiv_symm_apply
  条件: (x : S)
  结论: (linearEquiv R v).symm x = toVal v x
  证明: rfl
-/
@[simp] theorem linearEquiv_symm_apply (x : S) : (linearEquiv R v).symm x = toVal v x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Finite
  signature: R S] :
  body: .equiv (linearEquiv R v).symm

中文:
实例 [模.有限
  签名: R S] :
  定义体: .equiv (linearEquiv R v).symm

Depends on / 依赖: linearEquiv
-/
instance [Module.Finite R S] :
    Module.Finite R (WithVal v) := .equiv (linearEquiv R v).symm

end Module

section Algebra

variable {S : Type*}

section left

variable [CommRing R] (v : Valuation R Γ₀) [Semiring S] [Algebra R S]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra (WithVal v) S
  body: fast_instance% {
  algebraMap.toFun r := algebraMap R S (ofVal r)
  __ := Algebra.compHom S (equiv v).toRingHom }

中文:
实例 :
  签名: 代数 (WithVal v) S
  定义体: fast_instance% {
  algebraMap.toFun r := algebraMap R S (ofVal r)
  __ := Algebra.compHom S (equiv v).toRingHom }

Depends on / 依赖: fast_instance
-/
instance : Algebra (WithVal v) S := fast_instance% {
  algebraMap.toFun r := algebraMap R S (ofVal r)
  __ := Algebra.compHom S (equiv v).toRingHom }

/--
theorem `algebraMap_left_apply` / 定理 `algebraMap_left_apply`

English:
theorem algebraMap_left_apply
  given: (s : WithVal v)
  proof: rfl

中文:
定理 algebraMap_left_apply
  条件: (s : WithVal v)
  证明: rfl
-/
theorem algebraMap_left_apply (s : WithVal v) :
    algebraMap (WithVal v) S s = algebraMap R S s.ofVal := rfl

instance {S : Type*} [CommSemiring S] [Algebra R S] [i : IsFractionRing R S] :
    IsFractionRing (WithVal v) S := .of_ringEquiv_left (equiv v) (fun _ => rfl)

/--
theorem `algebraMap_left_injective` / 定理 `algebraMap_left_injective`

English:
theorem algebraMap_left_injective
  given: (h : Function.Injective (algebraMap R S))
  proof: h.comp (ofVal_injective v)

中文:
定理 algebraMap_left_injective
  条件: (h : 函数.单射 (algebraMap R S))
  证明: h.comp (ofVal_injective v)

Depends on / 依赖: h.comp, ofVal_injective
-/
theorem algebraMap_left_injective (h : Function.Injective (algebraMap R S)) :
    Function.Injective (algebraMap (WithVal v) S) := h.comp (ofVal_injective v)

end left

section right

variable [CommSemiring R] [Ring S] [Algebra R S] (v : Valuation S Γ₀)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R (WithVal v)
  body: fast_instance% {
  (equiv v).algebra R with
  algebraMap.toFun r := toVal v (algebraMap R S r) }

中文:
实例 :
  签名: 代数 R (WithVal v)
  定义体: fast_instance% {
  (equiv v).algebra R with
  algebraMap.toFun r := toVal v (algebraMap R S r) }

Depends on / 依赖: fast_instance
-/
instance : Algebra R (WithVal v) := fast_instance% {
  (equiv v).algebra R with
  algebraMap.toFun r := toVal v (algebraMap R S r) }

/--
theorem `algebraMap_right_apply` / 定理 `algebraMap_right_apply`

English:
theorem algebraMap_right_apply
  given: (r : R)
  proof: rfl

中文:
定理 algebraMap_right_apply
  条件: (r : R)
  证明: rfl
-/
theorem algebraMap_right_apply (r : R) :
    algebraMap R (WithVal v) r = toVal v (algebraMap R S r) := rfl

/--
theorem `algebraMap_right_injective` / 定理 `algebraMap_right_injective`

English:
theorem algebraMap_right_injective
  given: (h : Function.Injective (algebraMap R S))
  proof: (toVal_injective v).comp h

中文:
定理 algebraMap_right_injective
  条件: (h : 函数.单射 (algebraMap R S))
  证明: (toVal_injective v).comp h

Depends on / 依赖: toVal_injective
-/
theorem algebraMap_right_injective (h : Function.Injective (algebraMap R S)) :
    Function.Injective (algebraMap R (WithVal v)) := (toVal_injective v).comp h

end right

variable [CommSemiring R] [Ring S] [Algebra R S] (v : Valuation S Γ₀)

variable (R) in
/--
Definition of `algEquiv` / `algEquiv` 的定义

English:
definition algEquiv
  signature: : WithVal v ≃ₐ[R] S
  body: (equiv v).algEquiv R

中文:
定义 algEquiv
  签名: : WithVal v ≃ₐ[R] S
  定义体: (equiv v).algEquiv R

Depends on / 依赖: algEquiv
-/
def algEquiv : WithVal v ≃ₐ[R] S := (equiv v).algEquiv R

/--
theorem `algEquiv_apply` / 定理 `algEquiv_apply`

English:
theorem algEquiv_apply
  given: (x : WithVal v)
  statement: algEquiv R v x = x.ofVal
  proof: rfl

中文:
定理 algEquiv_apply
  条件: (x : WithVal v)
  结论: algEquiv R v x = x.ofVal
  证明: rfl
-/
@[simp] theorem algEquiv_apply (x : WithVal v) : algEquiv R v x = x.ofVal := rfl

/--
theorem `algEquiv_symm_apply` / 定理 `algEquiv_symm_apply`

English:
theorem algEquiv_symm_apply
  given: (x : S)
  statement: (algEquiv R v).symm x = toVal v x
  proof: rfl

中文:
定理 algEquiv_symm_apply
  条件: (x : S)
  结论: (algEquiv R v).symm x = toVal v x
  证明: rfl
-/
@[simp] theorem algEquiv_symm_apply (x : S) : (algEquiv R v).symm x = toVal v x := rfl

instance {S : Type*} [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (v : Valuation S Γ₀) : IsLocalization M (WithVal v) := by
  rwa [← IsLocalization.isLocalization_iff_of_algEquiv M (algEquiv R v).symm]

end Algebra

section DivisionRing

variable [DivisionRing R] (v : Valuation R Γ₀)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div (WithVal v)
  body: toVal _ (x.ofVal / y.ofVal)

中文:
实例 :
  签名: 除法 (WithVal v)
  定义体: toVal _ (x.ofVal / y.ofVal)

Depends on / 依赖: x.ofVal, y.ofVal
-/
instance : Div (WithVal v) where div x y := toVal _ (x.ofVal / y.ofVal)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (WithVal v)
  body: toVal _ x.ofVal⁻¹

中文:
实例 :
  签名: 取逆 (WithVal v)
  定义体: toVal _ x.ofVal⁻¹

Depends on / 依赖: x.ofVal
-/
instance : Inv (WithVal v) where inv x := toVal _ x.ofVal⁻¹
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (WithVal v) Int
  body: toVal _ (x.ofVal ^ z)

中文:
实例 :
  签名: 幂 (WithVal v) 整数
  定义体: toVal _ (x.ofVal ^ z)

Depends on / 依赖: x.ofVal
-/
instance : Pow (WithVal v) Int where pow x z := toVal _ (x.ofVal ^ z)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NNRatCast (WithVal v)
  body: toVal _ q

中文:
实例 :
  签名: 非负有理数嵌入 (WithVal v)
  定义体: toVal _ q
-/
instance : NNRatCast (WithVal v) where nnratCast q := toVal _ q
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RatCast (WithVal v)
  body: toVal _ q

中文:
实例 :
  签名: 有理数嵌入 (WithVal v)
  定义体: toVal _ q
-/
instance : RatCast (WithVal v) where ratCast q := toVal _ q

/--
lemma `toVal_div` / 引理 `toVal_div`

English:
lemma toVal_div
  given: (x y : R)
  statement: toVal v (x / y) = toVal v x / toVal v y
  proof: rfl

中文:
引理 toVal_div
  条件: (x y : R)
  结论: toVal v (x / y) = toVal v x / toVal v y
  证明: rfl
-/
@[simp] lemma toVal_div (x y : R) : toVal v (x / y) = toVal v x / toVal v y := rfl

/--
lemma `ofVal_div` / 引理 `ofVal_div`

English:
lemma ofVal_div
  given: (x y : WithVal v)
  statement: ofVal (x / y) = ofVal x / ofVal y
  proof: rfl

中文:
引理 ofVal_div
  条件: (x y : WithVal v)
  结论: ofVal (x / y) = ofVal x / ofVal y
  证明: rfl
-/
@[simp] lemma ofVal_div (x y : WithVal v) : ofVal (x / y) = ofVal x / ofVal y := rfl

/--
lemma `toVal_inv` / 引理 `toVal_inv`

English:
lemma toVal_inv
  given: (x : R)
  statement: toVal v x⁻¹ = (toVal v x)⁻¹
  proof: rfl

中文:
引理 toVal_inv
  条件: (x : R)
  结论: toVal v x⁻¹ = (toVal v x)⁻¹
  证明: rfl
-/
@[simp] lemma toVal_inv (x : R) : toVal v x⁻¹ = (toVal v x)⁻¹ := rfl

/--
lemma `ofVal_inv` / 引理 `ofVal_inv`

English:
lemma ofVal_inv
  given: (x : WithVal v)
  statement: ofVal (x⁻¹) = (ofVal x)⁻¹
  proof: rfl

中文:
引理 ofVal_inv
  条件: (x : WithVal v)
  结论: ofVal (x⁻¹) = (ofVal x)⁻¹
  证明: rfl
-/
@[simp] lemma ofVal_inv (x : WithVal v) : ofVal (x⁻¹) = (ofVal x)⁻¹ := rfl

/--
lemma `toVal_zpow` / 引理 `toVal_zpow`

English:
lemma toVal_zpow
  given: (x : R) (z : Int)
  statement: toVal v (x ^ z) = (toVal v x) ^ z
  proof: rfl

中文:
引理 toVal_zpow
  条件: (x : R) (z : 整数)
  结论: toVal v (x ^ z) = (toVal v x) ^ z
  证明: rfl
-/
@[simp] lemma toVal_zpow (x : R) (z : Int) : toVal v (x ^ z) = (toVal v x) ^ z := rfl

/--
lemma `ofVal_zpow` / 引理 `ofVal_zpow`

English:
lemma ofVal_zpow
  given: (x : WithVal v) (z : Int)
  statement: ofVal (x ^ z) = (ofVal x) ^ z
  proof: rfl

中文:
引理 ofVal_zpow
  条件: (x : WithVal v) (z : 整数)
  结论: ofVal (x ^ z) = (ofVal x) ^ z
  证明: rfl
-/
@[simp] lemma ofVal_zpow (x : WithVal v) (z : Int) : ofVal (x ^ z) = (ofVal x) ^ z := rfl

/--
lemma `toVal_nnratCast` / 引理 `toVal_nnratCast`

English:
lemma toVal_nnratCast
  given: (q : Rat>=0)
  statement: toVal v q = q
  proof: rfl

中文:
引理 toVal_nnratCast
  条件: (q : 有理数>=0)
  结论: toVal v q = q
  证明: rfl
-/
@[simp] lemma toVal_nnratCast (q : Rat>=0) : toVal v q = q := rfl

/--
lemma `ofVal_nnratCast` / 引理 `ofVal_nnratCast`

English:
lemma ofVal_nnratCast
  given: (q : Rat>=0)
  statement: ofVal (q : WithVal v) = q
  proof: rfl

中文:
引理 ofVal_nnratCast
  条件: (q : 有理数>=0)
  结论: ofVal (q : WithVal v) = q
  证明: rfl
-/
@[simp] lemma ofVal_nnratCast (q : Rat>=0) : ofVal (q : WithVal v) = q := rfl

/--
lemma `toVal_ratCast` / 引理 `toVal_ratCast`

English:
lemma toVal_ratCast
  given: (q : Rat)
  statement: toVal v q = q
  proof: rfl

中文:
引理 toVal_ratCast
  条件: (q : 有理数)
  结论: toVal v q = q
  证明: rfl
-/
@[simp] lemma toVal_ratCast (q : Rat) : toVal v q = q := rfl

/--
lemma `ofVal_ratCast` / 引理 `ofVal_ratCast`

English:
lemma ofVal_ratCast
  given: (q : Rat)
  statement: ofVal (q : WithVal v) = q
  proof: rfl

中文:
引理 ofVal_ratCast
  条件: (q : 有理数)
  结论: ofVal (q : WithVal v) = q
  证明: rfl
-/
@[simp] lemma ofVal_ratCast (q : Rat) : ofVal (q : WithVal v) = q := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DivisionRing (WithVal v)
  body: fast_instance% (equiv v).divisionRing

中文:
实例 :
  签名: 除环 (WithVal v)
  定义体: fast_instance% (equiv v).divisionRing

Depends on / 依赖: divisionRing, fast_instance
-/
instance : DivisionRing (WithVal v) := fast_instance% (equiv v).divisionRing

end DivisionRing

section Field

variable [Field R] (v : Valuation R Γ₀)

.field _ instance : Field (WithVal v) := fast_instance% ofVal_injective v
  (ofVal_zero _) (ofVal_one _) (ofVal_add _) (ofVal_mul _) (ofVal_neg _) (ofVal_sub _)
  (ofVal_inv _) (ofVal_div _)
  (ofVal_smul _) (ofVal_smul _) (ofVal_smul _) (ofVal_smul _) (ofVal_pow _) (ofVal_zpow _)
  (ofVal_natCast _) (ofVal_intCast _) (ofVal_nnratCast _) (ofVal_ratCast _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NumberField
  signature: R] : NumberField (WithVal v) where

中文:
实例 [数域
  签名: R] : 数域 (WithVal v) where
-/
instance [NumberField R] : NumberField (WithVal v) where

end Field

section Ring

variable [Ring R] (v : Valuation R Γ₀)

variable {Γ'₀ : Type*} [LinearOrderedCommGroupWithZero Γ'₀]

/-- Canonical ring equivalence between `WithVal v` and `WithVal w`. -/
@[deprecated "Use `WithVal.congr v w (.refl R)` instead" (since := "2026-01-27")]
/--
Definition of `equivWithVal` / `equivWithVal` 的定义

English:
definition equivWithVal
  signature: (v : Valuation R Γ₀) (w : Valuation R Γ'₀)
  body: (equiv v).trans (equiv w).symm

@[deprecated WithVal.congr_symm (since := "2026-01-27")]

中文:
定义 equivWithVal
  签名: (v : 赋值 R Γ₀) (w : 赋值 R Γ'₀)
  定义体: (equiv v).trans (equiv w).symm

@[deprecated WithVal.congr_symm (since := "2026-01-27")]
-/
def equivWithVal (v : Valuation R Γ₀) (w : Valuation R Γ'₀) :
    WithVal v ≃+* WithVal w :=
  (equiv v).trans (equiv w).symm

@[deprecated WithVal.congr_symm (since := "2026-01-27")]
/--
theorem `equivWithVal_symm` / 定理 `equivWithVal_symm`

English:
theorem equivWithVal_symm
  given: (v : Valuation R Γ₀) (w : Valuation R Γ'₀)
  proof: rfl

@[deprecated "Use `WithVal.congr_apply` instead" (since := "2026-01-27")]

中文:
定理 equivWithVal_symm
  条件: (v : 赋值 R Γ₀) (w : 赋值 R Γ'₀)
  证明: rfl

@[deprecated "Use `WithVal.congr_apply` instead" (since := "2026-01-27")]
-/
theorem equivWithVal_symm (v : Valuation R Γ₀) (w : Valuation R Γ'₀) :
    (congr v w (.refl R)).symm = congr w v (.refl R) := rfl

@[deprecated "Use `WithVal.congr_apply` instead" (since := "2026-01-27")]
/--
theorem `equivWithVal_apply` / 定理 `equivWithVal_apply`

English:
theorem equivWithVal_apply
  given: (v : Valuation R Γ₀) (w : Valuation R Γ'₀) {x : WithVal v}
  proof: by simp

@[deprecated "Use `WithVal.congr_symm_apply` instead" (since := "2026-01-27")]

中文:
定理 equivWithVal_apply
  条件: (v : 赋值 R Γ₀) (w : 赋值 R Γ'₀) {x : WithVal v}
  证明: by simp

@[deprecated "Use `WithVal.congr_symm_apply` instead" (since := "2026-01-27")]
-/
theorem equivWithVal_apply (v : Valuation R Γ₀) (w : Valuation R Γ'₀) {x : WithVal v} :
    congr v w (.refl R) x = (equiv w).symm (equiv v x) := by simp

@[deprecated "Use `WithVal.congr_symm_apply` instead" (since := "2026-01-27")]
/--
theorem `equivWithVal_symm_apply` / 定理 `equivWithVal_symm_apply`

English:
theorem equivWithVal_symm_apply
  given: (v : Valuation R Γ₀) (w : Valuation R Γ'₀) {x : WithVal w}
  proof: by simp

中文:
定理 equivWithVal_symm_apply
  条件: (v : 赋值 R Γ₀) (w : 赋值 R Γ'₀) {x : WithVal w}
  证明: by simp
-/
theorem equivWithVal_symm_apply (v : Valuation R Γ₀) (w : Valuation R Γ'₀) {x : WithVal w} :
    (congr v w (.refl R)).symm x = (equiv v).symm (equiv w x) := by simp

end Ring
section ValueGroup₀

variable {R : Type*} [Ring R] (v : Valuation R Γ₀)

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

/--
theorem `valueGroup_eq` / 定理 `valueGroup_eq`

English:
theorem valueGroup_eq
  statement: valueGroup (.ofClass (Valued.v (R := WithVal v))) =
  proof: by
  simp [valueGroup, valueMonoid, ← (WithVal.ofVal_surjective v).range_comp]
  rfl

中文:
定理 valueGroup_eq
  结论: valueGroup (.ofClass (赋值.v (R := WithVal v))) =
  证明: by
  simp [valueGroup, valueMonoid, ← (WithVal.ofVal_surjective v).range_comp]
  rfl

Depends on / 依赖: WithVal
-/
theorem valueGroup_eq : valueGroup (.ofClass (Valued.v (R := WithVal v))) =
    valueGroup (.ofClass v) := by
  simp [valueGroup, valueMonoid, ← (WithVal.ofVal_surjective v).range_comp]
  rfl

/-- The multiplicative equivalence between the `valueGroup` of the valuation on `WithVal v`
and the valuation `v`. -/
@[simps! apply symm_apply]
/--
Definition of `valueGroupEquiv` / `valueGroupEquiv` 的定义

English:
definition valueGroupEquiv
  signature: :
  body: Equiv.setCongr (by simp [valueGroup_eq v])
  map_mul' := by simp [Equiv.setCongr, Equiv.subtypeEquivProp]

中文:
定义 valueGroupEquiv
  签名: :
  定义体: Equiv.setCongr (by simp [valueGroup_eq v])
  map_mul' := by simp [Equiv.setCongr, Equiv.subtypeEquivProp]

Depends on / 依赖: WithVal, ofClass, valueGroup
-/
def valueGroupEquiv :
    valueGroup (.ofClass (Valued.v (R := WithVal v))) ≃* valueGroup (.ofClass v) where
  __ := Equiv.setCongr (by simp [valueGroup_eq v])
  map_mul' := by simp [Equiv.setCongr, Equiv.subtypeEquivProp]

/--
theorem `strictMono_valueGroupEquiv` / 定理 `strictMono_valueGroupEquiv`

English:
theorem strictMono_valueGroupEquiv
  statement: StrictMono (valueGroupEquiv v)
  proof: fun _ _ _ => by simpa

中文:
定理 strictMono_valueGroupEquiv
  结论: 严格递增 (valueGroupEquiv v)
  证明: fun _ _ _ => by simpa
-/
theorem strictMono_valueGroupEquiv : StrictMono (valueGroupEquiv v) :=
  fun _ _ _ => by simpa

/--
theorem `strictMono_valueGroupEquiv_symm` / 定理 `strictMono_valueGroupEquiv_symm`

English:
theorem strictMono_valueGroupEquiv_symm
  statement: StrictMono (valueGroupEquiv v).symm
  proof: fun _ _ _ => by simpa

中文:
定理 strictMono_valueGroupEquiv_symm
  结论: 严格递增 (valueGroupEquiv v).symm
  证明: fun _ _ _ => by simpa
-/
theorem strictMono_valueGroupEquiv_symm : StrictMono (valueGroupEquiv v).symm :=
  fun _ _ _ => by simpa

set_option backward.isDefEq.respectTransparency.types false in
/-- The order-preserving, multiplicative equivalence between the `ValueGroup₀` of the valuation
on `WithVal v` and the valuation `v`. -/
@[simps!]
/--
Definition of `valueGroupOrderIso₀` / `valueGroupOrderIso₀` 的定义

English:
definition valueGroupOrderIso₀
  signature: : ValueGroup₀ (.ofClass (Valued.v (R := WithVal v))) ≃*o
  body: WithZero.map' (valueGroupEquiv v)
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

中文:
定义 valueGroupOrderIso₀
  签名: : ValueGroup₀ (.ofClass (赋值.v (R := WithVal v))) ≃*o
  定义体: WithZero.map' (valueGroupEquiv v)
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

Depends on / 依赖: WithVal
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

/--
lemma `valueGroupOrderIso₀_restrict` / 引理 `valueGroupOrderIso₀_restrict`

English:
lemma valueGroupOrderIso₀_restrict
  given: (b : WithVal v)
  proof: by
  simp [(WithVal.valuation v).restrict_def, restrict₀_apply, ← valuation_apply_eq_ofVal,
    v.restrict_def]
  by_cases hb : v b.ofVal = 0 <;> simp [hb]

中文:
引理 valueGroupOrderIso₀_restrict
  条件: (b : WithVal v)
  证明: by
  simp [(WithVal.valuation v).restrict_def, restrict₀_apply, ← valuation_apply_eq_ofVal,
    v.restrict_def]
  by_cases hb : v b.ofVal = 0 <;> simp [hb]

Depends on / 依赖: WithVal, WithVal.valuation, b.ofVal, restrict_def, v.restrict_def, valuation, valuation_apply_eq_ofVal
-/
lemma valueGroupOrderIso₀_restrict (b : WithVal v) :
    valueGroupOrderIso₀ v ((WithVal.valuation v).restrict b) = v.restrict b.ofVal := by
  simp [(WithVal.valuation v).restrict_def, restrict₀_apply, ← valuation_apply_eq_ofVal,
    v.restrict_def]
  by_cases hb : v b.ofVal = 0 <;> simp [hb]

/--
lemma `valueGroupOrderIso₀_symm_restrict` / 引理 `valueGroupOrderIso₀_symm_restrict`

English:
lemma valueGroupOrderIso₀_symm_restrict
  given: (b : R)
  proof: by
  simp [Valued.v.restrict_def, restrict₀_apply, ← apply_ofVal, v.restrict_def]
  by_cases hb : v b = 0 <;> simp [hb]

中文:
引理 valueGroupOrderIso₀_symm_restrict
  条件: (b : R)
  证明: by
  simp [Valued.v.restrict_def, restrict₀_apply, ← apply_ofVal, v.restrict_def]
  by_cases hb : v b = 0 <;> simp [hb]

Depends on / 依赖: Valued, Valued.v.restrict_def, apply_ofVal, restrict_def, v.restrict_def
-/
lemma valueGroupOrderIso₀_symm_restrict (b : R) :
    (valueGroupOrderIso₀ v).symm (Valuation.restrict v b) = Valued.v.restrict (toVal v b) := by
  simp [Valued.v.restrict_def, restrict₀_apply, ← apply_ofVal, v.restrict_def]
  by_cases hb : v b = 0 <;> simp [hb]

/--
lemma `strictMono_valueGroupOrderIso₀` / 引理 `strictMono_valueGroupOrderIso₀`

English:
lemma strictMono_valueGroupOrderIso₀
  proof: WithZero.map'_strictMono (strictMono_valueGroupEquiv v)

中文:
引理 strictMono_valueGroupOrderIso₀
  证明: WithZero.map'_strictMono (strictMono_valueGroupEquiv v)

Depends on / 依赖: WithZero, WithZero.map, _strictMono, strictMono_valueGroupEquiv
-/
lemma strictMono_valueGroupOrderIso₀ :
    StrictMono (WithVal.valueGroupOrderIso₀ v) :=
  WithZero.map'_strictMono (strictMono_valueGroupEquiv v)

/--
lemma `strictMono_valueGroupOrderIso₀_symm` / 引理 `strictMono_valueGroupOrderIso₀_symm`

English:
lemma strictMono_valueGroupOrderIso₀_symm
  proof: WithZero.map'_strictMono (strictMono_valueGroupEquiv_symm v)

中文:
引理 strictMono_valueGroupOrderIso₀_symm
  证明: WithZero.map'_strictMono (strictMono_valueGroupEquiv_symm v)

Depends on / 依赖: WithZero, WithZero.map, _strictMono, strictMono_valueGroupEquiv_symm
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

/--
Definition of `Completion` / `Completion` 的定义

English:
abbreviation Completion
  body: UniformSpace.Completion (WithVal v)

中文:
缩写 完备化
  定义体: UniformSpace.Completion (WithVal v)

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion, WithVal
-/
abbrev Completion := UniformSpace.Completion (WithVal v)

-- lower priority so that `Coe (WithVal v) v.Completion` uses `UniformSpace.Completion.instCoe`
instance (priority := 99) : Coe R v.Completion where
  coe r := (WithVal.equiv v).symm r

section Equivalence

/-! The uniform isomorphism between `WithVal v` and `WithVal w` when `v` and `w` are
equivalent. -/

variable {R Γ₀ Γ₀' : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
  [LinearOrderedCommGroupWithZero Γ₀'] {v : Valuation R Γ₀} {w : Valuation R Γ₀'}

/--
Definition of `IsEquiv.orderRingIso` / `IsEquiv.orderRingIso` 的定义

English:
definition IsEquiv.orderRingIso
  signature: (h : v.IsEquiv w)
  body: WithVal.congr v w (.refl R)
  map_le_map_iff' := h.symm ..

@[simp]

中文:
定义 Is等价.orderRingIso
  签名: (h : v.Is等价 w)
  定义体: WithVal.congr v w (.refl R)
  map_le_map_iff' := h.symm ..

@[simp]

Depends on / 依赖: WithVal, WithVal.congr
-/
def IsEquiv.orderRingIso (h : v.IsEquiv w) :
    WithVal v ≃+*o WithVal w where
  __ := WithVal.congr v w (.refl R)
  map_le_map_iff' := h.symm ..

@[simp]
/--
theorem `IsEquiv.orderRingIso_apply` / 定理 `IsEquiv.orderRingIso_apply`

English:
theorem IsEquiv.orderRingIso_apply
  given: (h : v.IsEquiv w) (x : WithVal v)
  proof: rfl

@[simp]

中文:
定理 Is等价.orderRingIso_apply
  条件: (h : v.Is等价 w) (x : WithVal v)
  证明: rfl

@[simp]
-/
theorem IsEquiv.orderRingIso_apply (h : v.IsEquiv w) (x : WithVal v) :
    h.orderRingIso x = toVal w x.ofVal := rfl

@[simp]
/--
theorem `IsEquiv.orderRingIso_symm_apply` / 定理 `IsEquiv.orderRingIso_symm_apply`

English:
theorem IsEquiv.orderRingIso_symm_apply
  given: (h : v.IsEquiv w) (x : WithVal w)
  proof: rfl

中文:
定理 Is等价.orderRingIso_symm_apply
  条件: (h : v.Is等价 w) (x : WithVal w)
  证明: rfl
-/
theorem IsEquiv.orderRingIso_symm_apply (h : v.IsEquiv w) (x : WithVal w) :
    h.orderRingIso.symm x = toVal v x.ofVal := rfl

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

/--
theorem `IsEquiv.uniformContinuous_equiv` / 定理 `IsEquiv.uniformContinuous_equiv`

English:
theorem IsEquiv.uniformContinuous_equiv
  statement: [hval : Valued R Γ₀'] (hv : Valued.v = w)
  proof: by
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
  rw [← hr]; rw [equiv_apply]; rw [Set.mem_ofPred_eq]; rw [lt_div_iff₀ ((restrict_pos_iff Valued.v s).mpr hs₀)]; rw [hv]; rw [← map_mul]; rw [← lt_def]; rw [← ofVal_mul]; rw [← hy]; rw [← toVal_mul]; rw [← h'.orderRingIso_apply]; rw [← h'.orderRingIso.lt_symm_apply]
  simp only [toVal_mul, orderRingIso_symm_apply, lt_def, ofVal_mul, restrict_lt_iff]
  simp only [equiv_symm_apply, Units.val_mk0, Set.mem_ofPred_eq, lt_div_iff₀ hs0'] at hx
  rwa [← map_mul, restrict_lt_iff] at hx

中文:
定理 Is等价.uniformContinuous_equiv
  结论: [hval : 赋值 R Γ₀'] (hv : 赋值.v = w)
  证明: by
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
  rw [← hr]; rw [equiv_apply]; rw [Set.mem_ofPred_eq]; rw [lt_div_iff₀ ((restrict_pos_iff Valued.v s).mpr hs₀)]; rw [hv]; rw [← map_mul]; rw [← lt_def]; rw [← ofVal_mul]; rw [← hy]; rw [← toVal_mul]; rw [← h'.orderRingIso_apply]; rw [← h'.orderRingIso.lt_symm_apply]
  simp only [toVal_mul, orderRingIso_symm_apply, lt_def, ofVal_mul, restrict_lt_iff]
  simp only [equiv_symm_apply, Units.val_mk0, Set.mem_ofPred_eq, lt_div_iff₀ hs0'] at hx
  rwa [← map_mul, restrict_lt_iff] at hx

Depends on / 依赖: ContinuousAt, Valuation, Valuation.restrict_def, Valued, Valued.hasBasis_nhds_zero, Valued.v, WithVal, WithVal.equiv, eq_zero, exists_div_eq_of_unit, forall_const, hasBasis_nhds_zero, instValued, map_zero, restrict, restrict_def, simp_rw, tendsto_iff, true_and, uniformContinuous_of_continuousAt_zero
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
  rw [← hr]; rw [equiv_apply]; rw [Set.mem_ofPred_eq]; rw [lt_div_iff₀ ((restrict_pos_iff Valued.v s).mpr hs₀)]; rw [hv]; rw [← map_mul]; rw [← lt_def]; rw [← ofVal_mul]; rw [← hy]; rw [← toVal_mul]; rw [← h'.orderRingIso_apply]; rw [← h'.orderRingIso.lt_symm_apply]
  simp only [toVal_mul, orderRingIso_symm_apply, lt_def, ofVal_mul, restrict_lt_iff]
  simp only [equiv_symm_apply, Units.val_mk0, Set.mem_ofPred_eq, lt_div_iff₀ hs0'] at hx
  rwa [← map_mul, restrict_lt_iff] at hx

/--
theorem `IsEquiv.uniformContinuous_equiv_symm` / 定理 `IsEquiv.uniformContinuous_equiv_symm`

English:
theorem IsEquiv.uniformContinuous_equiv_symm
  statement: [hval : Valued R Γ₀'] (hv : Valued.v = w)
  proof: by
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
  rw [lt_div_iff₀]; rw [← map_mul]; rw [restrict_lt_iff]; rw [hv]; rw [h.lt_iff_lt]; rw [map_mul] at hx
  · rw [← hr, lt_div_iff₀ ((restrict_pos_iff Valued.v s).mpr hs₀), ← map_mul, ← lt_def,
      ← h.orderRingIso_apply]
    simp only [orderRingIso_apply, toVal_mul, lt_def, ofVal_mul, restrict_lt_iff]
    rw [map_mul]
    exact hx
  · rw [restrict_pos_iff, hv, h.pos_iff]
    exact hs₀

中文:
定理 Is等价.uniformContinuous_equiv_symm
  结论: [hval : 赋值 R Γ₀'] (hv : 赋值.v = w)
  证明: by
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
  rw [lt_div_iff₀]; rw [← map_mul]; rw [restrict_lt_iff]; rw [hv]; rw [h.lt_iff_lt]; rw [map_mul] at hx
  · rw [← hr, lt_div_iff₀ ((restrict_pos_iff Valued.v s).mpr hs₀), ← map_mul, ← lt_def,
      ← h.orderRingIso_apply]
    simp only [orderRingIso_apply, toVal_mul, lt_def, ofVal_mul, restrict_lt_iff]
    rw [map_mul]
    exact hx
  · rw [restrict_pos_iff, hv, h.pos_iff]
    exact hs₀

Depends on / 依赖: ContinuousAt, IsEquiv, Valued, Valued.hasBasis_nhds_zero, Valued.v, Valued.v.restrict, WithVal, WithVal.equiv, div_eq_zero_iff, equiv_apply, exists_div_eq_of_unit, forall_const, h.restrict, hasBasis_nhds_zero, map_zero, ne_eq, restrict, restrict_def, simp_rw, tendsto_iff
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
  rw [lt_div_iff₀]; rw [← map_mul]; rw [restrict_lt_iff]; rw [hv]; rw [h.lt_iff_lt]; rw [map_mul] at hx
  · rw [← hr, lt_div_iff₀ ((restrict_pos_iff Valued.v s).mpr hs₀), ← map_mul, ← lt_def,
      ← h.orderRingIso_apply]
    simp only [orderRingIso_apply, toVal_mul, lt_def, ofVal_mul, restrict_lt_iff]
    rw [map_mul]
    exact hx
  · rw [restrict_pos_iff, hv, h.pos_iff]
    exact hs₀

/--
lemma `IsEquiv.uniformContinuous` / 引理 `IsEquiv.uniformContinuous`

English:
lemma IsEquiv.uniformContinuous
  given: (h : v.IsEquiv w)
  proof: by
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
  have hy₀_ne_zero : y₀ != 0 := by simp [hy₀_def]
  set y := (Units.mk0 y₀ hy₀_ne_zero) with hy_def
  use y
  intro b hb
  rwa [← h_val.orderMonoidIso_spec, hy_def, Units.val_mk0, hy₀_def,
    h_val.orderMonoidIso.strictMono.lt_iff_lt] at hb

中文:
引理 Is等价.uniformContinuous
  条件: (h : v.Is等价 w)
  证明: by
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
  have hy₀_ne_zero : y₀ != 0 := by simp [hy₀_def]
  set y := (Units.mk0 y₀ hy₀_ne_zero) with hy_def
  use y
  intro b hb
  rwa [← h_val.orderMonoidIso_spec, hy_def, Units.val_mk0, hy₀_def,
    h_val.orderMonoidIso.strictMono.lt_iff_lt] at hb

Depends on / 依赖: ContinuousAt, IsEquiv, RingHom, RingHom.id, Units.ne_zero, Valued, Valued.hasBasis_nhds_zero, Valued.mk, WithZero, WithZero.unzero, forall_const, h_res, h_val, h_val.restrict, hasBasis_nhds_zero, map_zero, mem_valueGroup_iff_o, ne_zero, restrict, simp_rw
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
  have hy₀_ne_zero : y₀ != 0 := by simp [hy₀_def]
  set y := (Units.mk0 y₀ hy₀_ne_zero) with hy_def
  use y
  intro b hb
  rwa [← h_val.orderMonoidIso_spec, hy_def, Units.val_mk0, hy₀_def,
    h_val.orderMonoidIso.strictMono.lt_iff_lt] at hb

/--
theorem `IsEquiv.uniformContinuous_congr` / 定理 `IsEquiv.uniformContinuous_congr`

English:
theorem IsEquiv.uniformContinuous_congr
  given: (h : v.IsEquiv w)
  proof: by
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

中文:
定理 Is等价.uniformContinuous_congr
  条件: (h : v.Is等价 w)
  证明: by
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

Depends on / 依赖: IsEquiv, IsEquiv.uniformContinuous_equiv, IsEquiv.uniformContinuous_equiv_symm, RingEquiv, RingEquiv.ext_iff.mpr, RingEquiv.refl, RingHom, RingHom.id, UniformContinuous, UniformContinuous.comp, Valued, Valued.mk, WithVal, WithVal.congr, WithVal.equiv, ext_iff, h.uniformContinuous, toUniformSpace, uniformContinuous, uniformContinuous_equiv
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

/--
Definition of `IsEquiv.uniformEquiv` / `IsEquiv.uniformEquiv` 的定义

English:
definition IsEquiv.uniformEquiv
  signature: (h : v.IsEquiv w)
  body: WithVal.congr v w (.refl R)
  uniformContinuous_toFun := h.uniformContinuous_congr
  uniformContinuous_invFun := h.symm.uniformContinuous_congr

中文:
定义 Is等价.uniformEquiv
  签名: (h : v.Is等价 w)
  定义体: WithVal.congr v w (.refl R)
  uniformContinuous_toFun := h.uniformContinuous_congr
  uniformContinuous_invFun := h.symm.uniformContinuous_congr

Depends on / 依赖: WithVal, WithVal.congr
-/
def IsEquiv.uniformEquiv (h : v.IsEquiv w) : WithVal v ≃ᵤ WithVal w where
  __ := WithVal.congr v w (.refl R)
  uniformContinuous_toFun := h.uniformContinuous_congr
  uniformContinuous_invFun := h.symm.uniformContinuous_congr

/--
Definition of `_root_.WithVal.uniformEquiv` / `_root_.WithVal.uniformEquiv` 的定义

English:
definition _root_.WithVal.uniformEquiv
  signature: [Valued R Γ₀'] (hV : Valued.v = w) (h : v.IsEquiv w)
  body: WithVal.equiv v
  uniformContinuous_toFun := h.uniformContinuous_equiv hV
  uniformContinuous_invFun := h.symm.uniformContinuous_equiv_symm hV

中文:
定义 _root_.WithVal.uniformEquiv
  签名: [赋值 R Γ₀'] (hV : 赋值.v = w) (h : v.Is等价 w)
  定义体: WithVal.equiv v
  uniformContinuous_toFun := h.uniformContinuous_equiv hV
  uniformContinuous_invFun := h.symm.uniformContinuous_equiv_symm hV

Depends on / 依赖: WithVal, WithVal.equiv
-/
def _root_.WithVal.uniformEquiv [Valued R Γ₀'] (hV : Valued.v = w) (h : v.IsEquiv w) :
    WithVal v ≃ᵤ R where
  __ := WithVal.equiv v
  uniformContinuous_toFun := h.uniformContinuous_equiv hV
  uniformContinuous_invFun := h.symm.uniformContinuous_equiv_symm hV

/--
theorem `exists_div_eq_of_surjective` / 定理 `exists_div_eq_of_surjective`

English:
theorem exists_div_eq_of_surjective
  statement: {K : Type*} [DivisionRing K] {Γ₀ : Type*}
  proof: by
  obtain ⟨r, hr⟩ := hv γ
  exact ⟨r, 1, by simp [hr]⟩

中文:
定理 存在_div_eq_of_surjective
  结论: {K : 类型} [除环 K] {Γ₀ : 类型}
  证明: by
  obtain ⟨r, hr⟩ := hv γ
  exact ⟨r, 1, by simp [hr]⟩
-/
theorem exists_div_eq_of_surjective {K : Type*} [DivisionRing K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} (hv : Function.Surjective v)
    (γ : Γ₀ˣ) : exists r s, 0 < v r ∧ 0 < v s ∧ v r / v s = γ := by
  obtain ⟨r, hr⟩ := hv γ
  exact ⟨r, 1, by simp [hr]⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `restrict_exists_div_eq` / 定理 `restrict_exists_div_eq`

English:
theorem restrict_exists_div_eq
  statement: {K : Type*} [DivisionRing K] {Γ₀ : Type*}
  proof: by
  obtain ⟨r, hr⟩ := ValueGroup₀.restrict₀_surjective (.ofClass v) γ
  exact ⟨r, 1, by
    simp only [map_one, zero_lt_one, restrict_def, hr, div_one, and_self, and_true]
    rw [← map_zero v]
    simpa [← hr] using embedding_strictMono (WithZero.pos_iff_ne_zero.mpr (Units.ne_zero γ))⟩

中文:
定理 restrict_存在_div_eq
  结论: {K : 类型} [除环 K] {Γ₀ : 类型}
  证明: by
  obtain ⟨r, hr⟩ := ValueGroup₀.restrict₀_surjective (.ofClass v) γ
  exact ⟨r, 1, by
    simp only [map_one, zero_lt_one, restrict_def, hr, div_one, and_self, and_true]
    rw [← map_zero v]
    simpa [← hr] using embedding_strictMono (WithZero.pos_iff_ne_zero.mpr (Units.ne_zero γ))⟩

Depends on / 依赖: Units.ne_zero, WithZero, WithZero.pos_iff_ne_zero.mpr, and_self, and_true, div_one, embedding_strictMono, map_one, map_zero, ne_zero, ofClass, pos_iff_ne_zero, restrict_def, zero_lt_one
-/
theorem restrict_exists_div_eq {K : Type*} [DivisionRing K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    (γ : (ValueGroup₀ (.ofClass v))ˣ) :
    exists r s, 0 < v r ∧ 0 < v s ∧ v.restrict r / v.restrict s = γ.1 := by
  obtain ⟨r, hr⟩ := ValueGroup₀.restrict₀_surjective (.ofClass v) γ
  exact ⟨r, 1, by
    simp only [map_one, zero_lt_one, restrict_def, hr, div_one, and_self, and_true]
    rw [← map_zero v]
    simpa [← hr] using embedding_strictMono (WithZero.pos_iff_ne_zero.mpr (Units.ne_zero γ))⟩

open UniformSpace.Completion in
/--
theorem `IsEquiv.valuedCompletion_le_one_iff` / 定理 `IsEquiv.valuedCompletion_le_one_iff`

English:
theorem IsEquiv.valuedCompletion_le_one_iff
  statement: {K : Type*} [Field K] {v : Valuation K Γ₀}
  proof: by
  induction x using induction_on with
  | hp =>
    have h1 (x : UniformSpace.Completion (WithVal v)) :
      Valued.v x <= 1 ↔ Valued.v.restrict x <= 1 := by rw [restrict_le_one_iff]
    simp_rw [h1]
    convert!
      (mapEquiv h.uniformEquiv).toHomeomorph.isClosed_setOfPred_iff
        (Valued.isClopen_closedBall _ one_ne_zero) (Valued.isClopen_closedBall _ one_ne_zero)
    rw [restrict_le_one_iff]
    rfl
  | ih a =>
    simpa [Valued.valuedCompletion_apply] using! h.le_one_iff_le_one

中文:
定理 Is等价.valuedCompletion_le_one_iff
  结论: {K : 类型} [域 K] {v : 赋值 K Γ₀}
  证明: by
  induction x using induction_on with
  | hp =>
    have h1 (x : UniformSpace.Completion (WithVal v)) :
      Valued.v x <= 1 ↔ Valued.v.restrict x <= 1 := by rw [restrict_le_one_iff]
    simp_rw [h1]
    convert!
      (mapEquiv h.uniformEquiv).toHomeomorph.isClosed_setOfPred_iff
        (Valued.isClopen_closedBall _ one_ne_zero) (Valued.isClopen_closedBall _ one_ne_zero)
    rw [restrict_le_one_iff]
    rfl
  | ih a =>
    simpa [Valued.valuedCompletion_apply] using! h.le_one_iff_le_one

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion, Valued, Valued.isClopen_closedBall, Valued.v, Valued.v.restrict, Valued.valuedCompletion_apply, WithVal, convert, h.le_one_iff_le_one, h.uniformEquiv, induction_on, isClopen_closedBall, isClosed_setOfPred_iff, le_one_iff_le_one, mapEquiv, one_ne_zero, restrict, restrict_le_one_iff
-/
theorem IsEquiv.valuedCompletion_le_one_iff {K : Type*} [Field K] {v : Valuation K Γ₀}
    {w : Valuation K Γ₀'} (h : v.IsEquiv w) {x : v.Completion} :
    Valued.v x <= 1 ↔ Valued.v (mapEquiv h.uniformEquiv x) <= 1 := by
  induction x using induction_on with
  | hp =>
    have h1 (x : UniformSpace.Completion (WithVal v)) :
      Valued.v x <= 1 ↔ Valued.v.restrict x <= 1 := by rw [restrict_le_one_iff]
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeHead (𝓞 (WithVal v)) (WithVal v)
  body: RingOfIntegers.val x

中文:
实例 :
  签名: CoeHead (𝓞 (WithVal v)) (WithVal v)
  定义体: RingOfIntegers.val x

Depends on / 依赖: RingOfIntegers, RingOfIntegers.val
-/
instance : CoeHead (𝓞 (WithVal v)) (WithVal v) where
  coe x := RingOfIntegers.val x

instance (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R Int K] :
    IsIntegralClosure R Int (WithVal v) := .of_algEquiv _ (WithVal.algEquiv Int v).symm (fun _ => rfl)

/-- The ring equivalence between `𝓞 (WithVal v)` and an integral closure of
`ℤ` in `K`. -/
@[simps!]
/--
Definition of `withValEquiv` / `withValEquiv` 的定义

English:
definition withValEquiv
  signature: (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R Int K]
  body: NumberField.RingOfIntegers.equiv R

中文:
定义 withValEquiv
  签名: (R : 类型) [交换环 R] [代数 R K] [是整闭包 R 整数 K]
  定义体: NumberField.RingOfIntegers.equiv R

Depends on / 依赖: NumberField, NumberField.RingOfIntegers.equiv, RingOfIntegers
-/
def withValEquiv (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R Int K] :
    𝓞 (WithVal v) ≃+* R := NumberField.RingOfIntegers.equiv R

end NumberField.RingOfIntegers

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
open scoped NumberField in
/-- The ring of integers of `WithVal v`, when `v` is a valuation on `ℚ`, is
equivalent to `ℤ`. -/
@[simps! apply]
/--
Definition of `Rat.ringOfIntegersWithValEquiv` / `Rat.ringOfIntegersWithValEquiv` 的定义

English:
definition Rat.ringOfIntegersWithValEquiv
  signature: (v : Valuation Rat Γ₀)
  body: NumberField.RingOfIntegers.withValEquiv v Int

中文:
定义 有理数.ringOf整数egersWithValEquiv
  签名: (v : 赋值 有理数 Γ₀)
  定义体: NumberField.RingOfIntegers.withValEquiv v Int

Depends on / 依赖: NumberField, NumberField.RingOfIntegers.withValEquiv, RingOfIntegers, withValEquiv
-/
def Rat.ringOfIntegersWithValEquiv (v : Valuation Rat Γ₀) : 𝓞 (WithVal v) ≃+* Int :=
  NumberField.RingOfIntegers.withValEquiv v Int
