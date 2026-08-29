/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
module

public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Tactic.Push.Attr
public import Mathlib.Logic.Function.Defs
public import Batteries.Tactic.Alias

/-!
# Notation for algebraic operators on pi types

This file provides only the notation for (pointwise) `0`, `1`, `+`, `*`, `•`, `^`, `⁻¹` on pi types.
See `Mathlib/Algebra/Group/Pi/Basic.lean` for the `Monoid` and `Group` instances. There is also
an instance of the `Star` notation typeclass, but no default notation is included.
-/

@[expose] public section

assert_not_exists Set.range Monoid Preorder

open Function

variable {ι α β : Type*} {G M R : ι -> Type*}

namespace Pi

@[deprecated (since := "2026-04-21")]
alias prod := Function.prod

@[deprecated (since := "2026-04-21")]
alias prod_fst_snd := Function.prod_fst_snd

@[deprecated (since := "2026-04-21")]
alias prod_snd_fst := Function.prod_snd_fst

/-! `1`, `0`, `+`, `*`, `+ᵥ`, `•`, `^`, `-`, `⁻¹`, and `/` are defined pointwise. -/

section One
variable [forall i, One (M i)]

@[to_additive]
/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (forall i, M i) where one _
  body: 1

@[to_additive (attr := simp high)]

中文:
实例 instOne
  签名: : 幺 (对任意 i, M i) where one _
  定义体: 1

@[to_additive (attr := simp high)]
-/
instance instOne : One (forall i, M i) where one _ := 1

@[to_additive (attr := simp high)]
/--
lemma `one_apply` / 引理 `one_apply`

English:
lemma one_apply
  given: (i : ι)
  statement: (1 : forall i, M i) i = 1
  proof: rfl

@[to_additive (attr := push ← high)]

中文:
引理 one_apply
  条件: (i : ι)
  结论: (1 : 对任意 i, M i) i = 1
  证明: rfl

@[to_additive (attr := push ← high)]
-/
lemma one_apply (i : ι) : (1 : forall i, M i) i = 1 := rfl

@[to_additive (attr := push ← high)]
/--
lemma `one_def` / 引理 `one_def`

English:
lemma one_def
  statement: (1 : forall i, M i) = fun _ => 1
  proof: rfl

中文:
引理 one_def
  结论: (1 : 对任意 i, M i) = fun _ => 1
  证明: rfl
-/
lemma one_def : (1 : forall i, M i) = fun _ => 1 := rfl

variable {M : Type*} [One M]

/--
lemma `_root_.Function.const_one` / 引理 `_root_.Function.const_one`

English:
lemma _root_.Function.const_one
  statement: const α (1 : M) = 1
  proof: rfl

中文:
引理 _root_.函数.const_one
  结论: const α (1 : M) = 1
  证明: rfl
-/
@[to_additive (attr := simp)] lemma _root_.Function.const_one : const α (1 : M) = 1 := rfl

/--
lemma `one_comp` / 引理 `one_comp`

English:
lemma one_comp
  given: (f : α -> β)
  statement: (1 : β -> M) ∘ f = 1
  proof: rfl

中文:
引理 one_comp
  条件: (f : α -> β)
  结论: (1 : β -> M) ∘ f = 1
  证明: rfl
-/
@[to_additive (attr := simp)] lemma one_comp (f : α -> β) : (1 : β -> M) ∘ f = 1 := rfl
/--
lemma `comp_one` / 引理 `comp_one`

English:
lemma comp_one
  given: (f : M -> β)
  statement: f ∘ (1 : α -> M) = const α (f 1)
  proof: rfl

中文:
引理 comp_one
  条件: (f : M -> β)
  结论: f ∘ (1 : α -> M) = const α (f 1)
  证明: rfl
-/
@[to_additive (attr := simp)] lemma comp_one (f : M -> β) : f ∘ (1 : α -> M) = const α (f 1) := rfl

end One

section Mul
variable [forall i, Mul (M i)]

@[to_additive]
/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (forall i, M i) where mul f g i
  body: f i * g i

@[to_additive (attr := simp)]

中文:
实例 instMul
  签名: : 乘法 (对任意 i, M i) where mul f g i
  定义体: f i * g i

@[to_additive (attr := simp)]
-/
instance instMul : Mul (forall i, M i) where mul f g i := f i * g i

@[to_additive (attr := simp)]
/--
lemma `mul_apply` / 引理 `mul_apply`

English:
lemma mul_apply
  given: (f g : forall i, M i) (i : ι)
  statement: (f * g) i = f i * g i
  proof: rfl

@[to_additive (attr := push ←)]

中文:
引理 mul_apply
  条件: (f g : 对任意 i, M i) (i : ι)
  结论: (f * g) i = f i * g i
  证明: rfl

@[to_additive (attr := push ←)]
-/
lemma mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i * g i := rfl

@[to_additive (attr := push ←)]
/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  given: (f g : forall i, M i)
  statement: f * g = fun i => f i * g i
  proof: rfl

中文:
引理 mul_def
  条件: (f g : 对任意 i, M i)
  结论: f * g = fun i => f i * g i
  证明: rfl
-/
lemma mul_def (f g : forall i, M i) : f * g = fun i => f i * g i := rfl

variable {M : Type*} [Mul M]

@[to_additive (attr := simp)]
/--
lemma `_root_.Function.const_mul` / 引理 `_root_.Function.const_mul`

English:
lemma _root_.Function.const_mul
  given: (a b : M)
  statement: const ι a * const ι b = const ι (a * b)
  proof: rfl

@[to_additive]

中文:
引理 _root_.函数.const_mul
  条件: (a b : M)
  结论: const ι a * const ι b = const ι (a * b)
  证明: rfl

@[to_additive]
-/
lemma _root_.Function.const_mul (a b : M) : const ι a * const ι b = const ι (a * b) := rfl

@[to_additive]
/--
lemma `mul_comp` / 引理 `mul_comp`

English:
lemma mul_comp
  given: (f g : β -> M) (z : α -> β)
  statement: (f * g) ∘ z = f ∘ z * g ∘ z
  proof: rfl

中文:
引理 mul_comp
  条件: (f g : β -> M) (z : α -> β)
  结论: (f * g) ∘ z = f ∘ z * g ∘ z
  证明: rfl
-/
lemma mul_comp (f g : β -> M) (z : α -> β) : (f * g) ∘ z = f ∘ z * g ∘ z := rfl

end Mul

section Inv
variable [forall i, Inv (G i)]

@[to_additive]
/--
Instance `instInv` / 实例 `instInv`

English:
instance instInv
  signature: : Inv (forall i, G i) where inv f i
  body: (f i)⁻¹

@[to_additive (attr := simp)]

中文:
实例 instInv
  签名: : 取逆 (对任意 i, G i) where inv f i
  定义体: (f i)⁻¹

@[to_additive (attr := simp)]
-/
instance instInv : Inv (forall i, G i) where inv f i := (f i)⁻¹

@[to_additive (attr := simp)]
/--
lemma `inv_apply` / 引理 `inv_apply`

English:
lemma inv_apply
  given: (f : forall i, G i) (i : ι)
  statement: f⁻¹ i = (f i)⁻¹
  proof: rfl

@[to_additive (attr := push ←)]

中文:
引理 inv_apply
  条件: (f : 对任意 i, G i) (i : ι)
  结论: f⁻¹ i = (f i)⁻¹
  证明: rfl

@[to_additive (attr := push ←)]
-/
lemma inv_apply (f : forall i, G i) (i : ι) : f⁻¹ i = (f i)⁻¹ := rfl

@[to_additive (attr := push ←)]
/--
lemma `inv_def` / 引理 `inv_def`

English:
lemma inv_def
  given: (f : forall i, G i)
  statement: f⁻¹ = fun i => (f i)⁻¹
  proof: rfl

中文:
引理 inv_def
  条件: (f : 对任意 i, G i)
  结论: f⁻¹ = fun i => (f i)⁻¹
  证明: rfl
-/
lemma inv_def (f : forall i, G i) : f⁻¹ = fun i => (f i)⁻¹ := rfl

variable {G : Type*} [Inv G]

@[to_additive]
/--
lemma `_root_.Function.const_inv` / 引理 `_root_.Function.const_inv`

English:
lemma _root_.Function.const_inv
  given: (a : G)
  statement: (const ι a)⁻¹ = const ι a⁻¹
  proof: rfl

@[to_additive]

中文:
引理 _root_.函数.const_inv
  条件: (a : G)
  结论: (const ι a)⁻¹ = const ι a⁻¹
  证明: rfl

@[to_additive]
-/
lemma _root_.Function.const_inv (a : G) : (const ι a)⁻¹ = const ι a⁻¹ := rfl

@[to_additive]
/--
lemma `inv_comp` / 引理 `inv_comp`

English:
lemma inv_comp
  given: (f : β -> G) (g : α -> β)
  statement: f⁻¹ ∘ g = (f ∘ g)⁻¹
  proof: rfl

中文:
引理 inv_comp
  条件: (f : β -> G) (g : α -> β)
  结论: f⁻¹ ∘ g = (f ∘ g)⁻¹
  证明: rfl
-/
lemma inv_comp (f : β -> G) (g : α -> β) : f⁻¹ ∘ g = (f ∘ g)⁻¹ := rfl
end Inv

section Div
variable [forall i, Div (G i)]

@[to_additive]
/--
Instance `instDiv` / 实例 `instDiv`

English:
instance instDiv
  signature: : Div (forall i, G i) where div f g i
  body: f i / g i

@[to_additive (attr := simp)]

中文:
实例 instDiv
  签名: : 除法 (对任意 i, G i) where div f g i
  定义体: f i / g i

@[to_additive (attr := simp)]
-/
instance instDiv : Div (forall i, G i) where div f g i := f i / g i

@[to_additive (attr := simp)]
/--
lemma `div_apply` / 引理 `div_apply`

English:
lemma div_apply
  given: (f g : forall i, G i) (i : ι)
  statement: (f / g) i = f i / g i
  proof: rfl

@[to_additive (attr := push ←)]

中文:
引理 div_apply
  条件: (f g : 对任意 i, G i) (i : ι)
  结论: (f / g) i = f i / g i
  证明: rfl

@[to_additive (attr := push ←)]
-/
lemma div_apply (f g : forall i, G i) (i : ι) : (f / g) i = f i / g i := rfl

@[to_additive (attr := push ←)]
/--
lemma `div_def` / 引理 `div_def`

English:
lemma div_def
  given: (f g : forall i, G i)
  statement: f / g = fun i => f i / g i
  proof: rfl

中文:
引理 div_def
  条件: (f g : 对任意 i, G i)
  结论: f / g = fun i => f i / g i
  证明: rfl
-/
lemma div_def (f g : forall i, G i) : f / g = fun i => f i / g i := rfl

variable {G : Type*} [Div G]

@[to_additive]
/--
lemma `div_comp` / 引理 `div_comp`

English:
lemma div_comp
  given: (f g : β -> G) (z : α -> β)
  statement: (f / g) ∘ z = f ∘ z / g ∘ z
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 div_comp
  条件: (f g : β -> G) (z : α -> β)
  结论: (f / g) ∘ z = f ∘ z / g ∘ z
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma div_comp (f g : β -> G) (z : α -> β) : (f / g) ∘ z = f ∘ z / g ∘ z := rfl

@[to_additive (attr := simp)]
/--
lemma `_root_.Function.const_div` / 引理 `_root_.Function.const_div`

English:
lemma _root_.Function.const_div
  given: (a b : G)
  statement: const ι a / const ι b = const ι (a / b)
  proof: rfl

中文:
引理 _root_.函数.const_div
  条件: (a b : G)
  结论: const ι a / const ι b = const ι (a / b)
  证明: rfl
-/
lemma _root_.Function.const_div (a b : G) : const ι a / const ι b = const ι (a / b) := rfl

end Div

section Pow

variable [forall i, Pow (M i) α]

@[to_additive (attr := to_additive) instSMul]
/--
Instance `instPow` / 实例 `instPow`

English:
instance instPow
  signature: : Pow (forall i, M i) α where pow f a i
  body: f i ^ a

@[to_additive (attr := simp, to_additive) (reorder := 5 6) smul_apply]

中文:
实例 instPow
  签名: : 幂 (对任意 i, M i) α where pow f a i
  定义体: f i ^ a

@[to_additive (attr := simp, to_additive) (reorder := 5 6) smul_apply]
-/
instance instPow : Pow (forall i, M i) α where pow f a i := f i ^ a

@[to_additive (attr := simp, to_additive) (reorder := 5 6) smul_apply]
/--
lemma `pow_apply` / 引理 `pow_apply`

English:
lemma pow_apply
  given: (f : forall i, M i) (a : α) (i : ι)
  statement: (f ^ a) i = f i ^ a
  proof: rfl

@[to_additive (attr := push ←, to_additive) (reorder := 5 6) smul_def]

中文:
引理 pow_apply
  条件: (f : 对任意 i, M i) (a : α) (i : ι)
  结论: (f ^ a) i = f i ^ a
  证明: rfl

@[to_additive (attr := push ←, to_additive) (reorder := 5 6) smul_def]
-/
lemma pow_apply (f : forall i, M i) (a : α) (i : ι) : (f ^ a) i = f i ^ a := rfl

@[to_additive (attr := push ←, to_additive) (reorder := 5 6) smul_def]
/--
lemma `pow_def` / 引理 `pow_def`

English:
lemma pow_def
  given: (f : forall i, M i) (a : α)
  statement: f ^ a = fun i => f i ^ a
  proof: rfl

中文:
引理 pow_def
  条件: (f : 对任意 i, M i) (a : α)
  结论: f ^ a = fun i => f i ^ a
  证明: rfl
-/
lemma pow_def (f : forall i, M i) (a : α) : f ^ a = fun i => f i ^ a := rfl

variable {M : Type*} [Pow M α]

@[to_additive (attr := simp, to_additive) (reorder := 2 3, 5 6) smul_const]
/--
lemma `_root_.Function.const_pow` / 引理 `_root_.Function.const_pow`

English:
lemma _root_.Function.const_pow
  given: (a : M) (b : α)
  statement: const ι a ^ b = const ι (a ^ b)
  proof: rfl

@[to_additive (attr := to_additive) (reorder := 6 7) smul_comp]

中文:
引理 _root_.函数.const_pow
  条件: (a : M) (b : α)
  结论: const ι a ^ b = const ι (a ^ b)
  证明: rfl

@[to_additive (attr := to_additive) (reorder := 6 7) smul_comp]
-/
lemma _root_.Function.const_pow (a : M) (b : α) : const ι a ^ b = const ι (a ^ b) := rfl

@[to_additive (attr := to_additive) (reorder := 6 7) smul_comp]
/--
lemma `pow_comp` / 引理 `pow_comp`

English:
lemma pow_comp
  given: (f : β -> M) (a : α) (g : ι -> β)
  statement: (f ^ a) ∘ g = f ∘ g ^ a
  proof: rfl

中文:
引理 pow_comp
  条件: (f : β -> M) (a : α) (g : ι -> β)
  结论: (f ^ a) ∘ g = f ∘ g ^ a
  证明: rfl
-/
lemma pow_comp (f : β -> M) (a : α) (g : ι -> β) : (f ^ a) ∘ g = f ∘ g ^ a := rfl

end Pow

section Star

variable [forall i, Star (R i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star (forall i, R i)
  body: star (x i)

@[simp]

中文:
实例 :
  签名: 对合 (对任意 i, R i)
  定义体: star (x i)

@[simp]
-/
instance : Star (forall i, R i) where star x i := star (x i)

@[simp]
/--
theorem `star_apply` / 定理 `star_apply`

English:
theorem star_apply
  given: (x : forall i, R i) (i : ι)
  statement: star x i = star (x i)
  proof: rfl

@[push ←]

中文:
定理 star_apply
  条件: (x : 对任意 i, R i) (i : ι)
  结论: star x i = star (x i)
  证明: rfl

@[push ←]
-/
theorem star_apply (x : forall i, R i) (i : ι) : star x i = star (x i) := rfl

@[push ←]
/--
theorem `star_def` / 定理 `star_def`

English:
theorem star_def
  given: (x : forall i, R i)
  statement: star x = fun i => star (x i)
  proof: rfl

中文:
定理 star_def
  条件: (x : 对任意 i, R i)
  结论: star x = fun i => star (x i)
  证明: rfl
-/
theorem star_def (x : forall i, R i) : star x = fun i => star (x i) := rfl

end Star

end Pi
