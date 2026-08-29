/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Data.Prod.Basic

/-!
# Arithmetic operators on (pairwise) product types

This file provides only the notation for (componentwise) `0`, `1`, `+`, `*`, `•`, `^`, `⁻¹` on
(pairwise) product types. See `Mathlib/Algebra/Group/Prod.lean` for the `Monoid` and `Group`
instances. There is also an instance of the `Star` notation typeclass, but no default notation is
included.

-/

@[expose] public section

assert_not_exists Monoid DenselyOrdered

variable {G H M N P R S : Type*}

namespace Prod

section One

variable [One M] [One N]

@[to_additive]
/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (M × N)
  body: ⟨(1, 1)⟩

@[to_additive (attr := simp)]

中文:
实例 instOne
  签名: : 幺 (M × N)
  定义体: ⟨(1, 1)⟩

@[to_additive (attr := simp)]
-/
instance instOne : One (M × N) :=
  ⟨(1, 1)⟩

@[to_additive (attr := simp)]
/--
theorem `fst_one` / 定理 `fst_one`

English:
theorem fst_one
  statement: (1 : M × N).1 = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 fst_one
  结论: (1 : M × N).1 = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem fst_one : (1 : M × N).1 = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `snd_one` / 定理 `snd_one`

English:
theorem snd_one
  statement: (1 : M × N).2 = 1
  proof: rfl

@[to_additive]

中文:
定理 snd_one
  结论: (1 : M × N).2 = 1
  证明: rfl

@[to_additive]
-/
theorem snd_one : (1 : M × N).2 = 1 :=
  rfl

@[to_additive]
/--
theorem `one_eq_mk` / 定理 `one_eq_mk`

English:
theorem one_eq_mk
  statement: (1 : M × N) = (1, 1)
  proof: rfl

@[to_additive]

中文:
定理 one_eq_mk
  结论: (1 : M × N) = (1, 1)
  证明: rfl

@[to_additive]
-/
theorem one_eq_mk : (1 : M × N) = (1, 1) :=
  rfl

@[to_additive]
/--
theorem `mk_one_one` / 定理 `mk_one_one`

English:
theorem mk_one_one
  statement: ((1 : M), (1 : N)) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 mk_one_one
  结论: ((1 : M), (1 : N)) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem mk_one_one : ((1 : M), (1 : N)) = 1 := rfl

@[to_additive (attr := simp)]
/--
theorem `mk_eq_one` / 定理 `mk_eq_one`

English:
theorem mk_eq_one
  given: {x : M} {y : N}
  statement: (x, y) = 1 ↔ x = 1 ∧ y = 1
  proof: mk_inj

@[to_additive (attr := simp)]

中文:
定理 mk_eq_one
  条件: {x : M} {y : N}
  结论: (x, y) = 1 ↔ x = 1 ∧ y = 1
  证明: mk_inj

@[to_additive (attr := simp)]

Depends on / 依赖: mk_inj
-/
theorem mk_eq_one {x : M} {y : N} : (x, y) = 1 ↔ x = 1 ∧ y = 1 := mk_inj

@[to_additive (attr := simp)]
/--
theorem `swap_one` / 定理 `swap_one`

English:
theorem swap_one
  statement: (1 : M × N).swap = 1
  proof: rfl

中文:
定理 swap_one
  结论: (1 : M × N).swap = 1
  证明: rfl
-/
theorem swap_one : (1 : M × N).swap = 1 :=
  rfl

end One

section Mul

variable {M N : Type*} [Mul M] [Mul N]

@[to_additive]
/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (M × N)
  body: ⟨fun p q => ⟨p.1 * q.1, p.2 * q.2⟩⟩

@[to_additive (attr := simp)]

中文:
实例 instMul
  签名: : 乘法 (M × N)
  定义体: ⟨fun p q => ⟨p.1 * q.1, p.2 * q.2⟩⟩

@[to_additive (attr := simp)]
-/
instance instMul : Mul (M × N) :=
  ⟨fun p q => ⟨p.1 * q.1, p.2 * q.2⟩⟩

@[to_additive (attr := simp)]
/--
theorem `fst_mul` / 定理 `fst_mul`

English:
theorem fst_mul
  given: (p q : M × N)
  statement: (p * q).1 = p.1 * q.1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 fst_mul
  条件: (p q : M × N)
  结论: (p * q).1 = p.1 * q.1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem fst_mul (p q : M × N) : (p * q).1 = p.1 * q.1 := rfl

@[to_additive (attr := simp)]
/--
theorem `snd_mul` / 定理 `snd_mul`

English:
theorem snd_mul
  given: (p q : M × N)
  statement: (p * q).2 = p.2 * q.2
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 snd_mul
  条件: (p q : M × N)
  结论: (p * q).2 = p.2 * q.2
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem snd_mul (p q : M × N) : (p * q).2 = p.2 * q.2 := rfl

@[to_additive (attr := simp)]
/--
theorem `mk_mul_mk` / 定理 `mk_mul_mk`

English:
theorem mk_mul_mk
  given: (a₁ a₂ : M) (b₁ b₂ : N)
  statement: (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 mk_mul_mk
  条件: (a₁ a₂ : M) (b₁ b₂ : N)
  结论: (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem mk_mul_mk (a₁ a₂ : M) (b₁ b₂ : N) : (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂) := rfl

@[to_additive (attr := simp)]
/--
theorem `swap_mul` / 定理 `swap_mul`

English:
theorem swap_mul
  given: (p q : M × N)
  statement: (p * q).swap = p.swap * q.swap
  proof: rfl

@[to_additive]

中文:
定理 swap_mul
  条件: (p q : M × N)
  结论: (p * q).swap = p.swap * q.swap
  证明: rfl

@[to_additive]
-/
theorem swap_mul (p q : M × N) : (p * q).swap = p.swap * q.swap := rfl

@[to_additive]
/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (p q : M × N)
  statement: p * q = (p.1 * q.1, p.2 * q.2)
  proof: rfl

中文:
定理 mul_def
  条件: (p q : M × N)
  结论: p * q = (p.1 * q.1, p.2 * q.2)
  证明: rfl
-/
theorem mul_def (p q : M × N) : p * q = (p.1 * q.1, p.2 * q.2) := rfl

end Mul

section Inv

variable {G H : Type*} [Inv G] [Inv H]

@[to_additive]
/--
Instance `instInv` / 实例 `instInv`

English:
instance instInv
  signature: : Inv (G × H)
  body: ⟨fun p => (p.1⁻¹, p.2⁻¹)⟩

@[to_additive (attr := simp)]

中文:
实例 instInv
  签名: : 取逆 (G × H)
  定义体: ⟨fun p => (p.1⁻¹, p.2⁻¹)⟩

@[to_additive (attr := simp)]
-/
instance instInv : Inv (G × H) :=
  ⟨fun p => (p.1⁻¹, p.2⁻¹)⟩

@[to_additive (attr := simp)]
/--
theorem `fst_inv` / 定理 `fst_inv`

English:
theorem fst_inv
  given: (p : G × H)
  statement: p⁻¹.1 = p.1⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 fst_inv
  条件: (p : G × H)
  结论: p⁻¹.1 = p.1⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem fst_inv (p : G × H) : p⁻¹.1 = p.1⁻¹ := rfl

@[to_additive (attr := simp)]
/--
theorem `snd_inv` / 定理 `snd_inv`

English:
theorem snd_inv
  given: (p : G × H)
  statement: p⁻¹.2 = p.2⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 snd_inv
  条件: (p : G × H)
  结论: p⁻¹.2 = p.2⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem snd_inv (p : G × H) : p⁻¹.2 = p.2⁻¹ := rfl

@[to_additive (attr := simp)]
/--
theorem `inv_mk` / 定理 `inv_mk`

English:
theorem inv_mk
  given: (a : G) (b : H)
  statement: (a, b)⁻¹ = (a⁻¹, b⁻¹)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 inv_mk
  条件: (a : G) (b : H)
  结论: (a, b)⁻¹ = (a⁻¹, b⁻¹)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem inv_mk (a : G) (b : H) : (a, b)⁻¹ = (a⁻¹, b⁻¹) := rfl

@[to_additive (attr := simp)]
/--
theorem `swap_inv` / 定理 `swap_inv`

English:
theorem swap_inv
  given: (p : G × H)
  statement: p⁻¹.swap = p.swap⁻¹
  proof: rfl

中文:
定理 swap_inv
  条件: (p : G × H)
  结论: p⁻¹.swap = p.swap⁻¹
  证明: rfl
-/
theorem swap_inv (p : G × H) : p⁻¹.swap = p.swap⁻¹ := rfl

end Inv

section Div

variable {G H : Type*} [Div G] [Div H]

@[to_additive]
/--
Instance `instDiv` / 实例 `instDiv`

English:
instance instDiv
  signature: : Div (G × H)
  body: ⟨fun p q => ⟨p.1 / q.1, p.2 / q.2⟩⟩

@[to_additive (attr := simp)]

中文:
实例 instDiv
  签名: : 除法 (G × H)
  定义体: ⟨fun p q => ⟨p.1 / q.1, p.2 / q.2⟩⟩

@[to_additive (attr := simp)]
-/
instance instDiv : Div (G × H) :=
  ⟨fun p q => ⟨p.1 / q.1, p.2 / q.2⟩⟩

@[to_additive (attr := simp)]
/--
theorem `fst_div` / 定理 `fst_div`

English:
theorem fst_div
  given: (a b : G × H)
  statement: (a / b).1 = a.1 / b.1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 fst_div
  条件: (a b : G × H)
  结论: (a / b).1 = a.1 / b.1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem fst_div (a b : G × H) : (a / b).1 = a.1 / b.1 := rfl

@[to_additive (attr := simp)]
/--
theorem `snd_div` / 定理 `snd_div`

English:
theorem snd_div
  given: (a b : G × H)
  statement: (a / b).2 = a.2 / b.2
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 snd_div
  条件: (a b : G × H)
  结论: (a / b).2 = a.2 / b.2
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem snd_div (a b : G × H) : (a / b).2 = a.2 / b.2 := rfl

@[to_additive (attr := simp)]
/--
theorem `mk_div_mk` / 定理 `mk_div_mk`

English:
theorem mk_div_mk
  given: (x₁ x₂ : G) (y₁ y₂ : H)
  statement: (x₁, y₁) / (x₂, y₂) = (x₁ / x₂, y₁ / y₂)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 mk_div_mk
  条件: (x₁ x₂ : G) (y₁ y₂ : H)
  结论: (x₁, y₁) / (x₂, y₂) = (x₁ / x₂, y₁ / y₂)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem mk_div_mk (x₁ x₂ : G) (y₁ y₂ : H) : (x₁, y₁) / (x₂, y₂) = (x₁ / x₂, y₁ / y₂) := rfl

@[to_additive (attr := simp)]
/--
theorem `swap_div` / 定理 `swap_div`

English:
theorem swap_div
  given: (a b : G × H)
  statement: (a / b).swap = a.swap / b.swap
  proof: rfl

中文:
定理 swap_div
  条件: (a b : G × H)
  结论: (a / b).swap = a.swap / b.swap
  证明: rfl
-/
theorem swap_div (a b : G × H) : (a / b).swap = a.swap / b.swap := rfl

/--
lemma `div_def` / 引理 `div_def`

English:
lemma div_def
  given: (a b : G × H)
  statement: a / b = (a.1 / b.1, a.2 / b.2)
  proof: rfl

中文:
引理 div_def
  条件: (a b : G × H)
  结论: a / b = (a.1 / b.1, a.2 / b.2)
  证明: rfl
-/
@[to_additive] lemma div_def (a b : G × H) : a / b = (a.1 / b.1, a.2 / b.2) := rfl

end Div

section Pow

variable {E α β : Type*} [Pow α E] [Pow β E]

@[to_additive (attr := to_additive) instSMul]
/--
Instance `instPow` / 实例 `instPow`

English:
instance instPow
  signature: : Pow (α × β) E where pow p c
  body: (p.1 ^ c, p.2 ^ c)

@[to_additive (attr := to_additive, simp) (reorder := p c) smul_fst]

中文:
实例 instPow
  签名: : 幂 (α × β) E where pow p c
  定义体: (p.1 ^ c, p.2 ^ c)

@[to_additive (attr := to_additive, simp) (reorder := p c) smul_fst]
-/
instance instPow : Pow (α × β) E where pow p c := (p.1 ^ c, p.2 ^ c)

@[to_additive (attr := to_additive, simp) (reorder := p c) smul_fst]
/--
lemma `pow_fst` / 引理 `pow_fst`

English:
lemma pow_fst
  given: (p : α × β) (c : E)
  statement: (p ^ c).fst = p.fst ^ c
  proof: rfl

@[to_additive (attr := to_additive, simp) (reorder := p c) smul_snd]

中文:
引理 pow_fst
  条件: (p : α × β) (c : E)
  结论: (p ^ c).fst = p.fst ^ c
  证明: rfl

@[to_additive (attr := to_additive, simp) (reorder := p c) smul_snd]
-/
lemma pow_fst (p : α × β) (c : E) : (p ^ c).fst = p.fst ^ c := rfl

@[to_additive (attr := to_additive, simp) (reorder := p c) smul_snd]
/--
lemma `pow_snd` / 引理 `pow_snd`

English:
lemma pow_snd
  given: (p : α × β) (c : E)
  statement: (p ^ c).snd = p.snd ^ c
  proof: rfl

@[to_additive (attr := to_additive, simp) (reorder := a b c) smul_mk]

中文:
引理 pow_snd
  条件: (p : α × β) (c : E)
  结论: (p ^ c).snd = p.snd ^ c
  证明: rfl

@[to_additive (attr := to_additive, simp) (reorder := a b c) smul_mk]
-/
lemma pow_snd (p : α × β) (c : E) : (p ^ c).snd = p.snd ^ c := rfl

@[to_additive (attr := to_additive, simp) (reorder := a b c) smul_mk]
/--
lemma `pow_mk` / 引理 `pow_mk`

English:
lemma pow_mk
  given: (a : α) (b : β) (c : E)
  statement: Prod.mk a b ^ c = Prod.mk (a ^ c) (b ^ c)
  proof: rfl

@[to_additive (attr := to_additive) (reorder := p c) smul_def]

中文:
引理 pow_mk
  条件: (a : α) (b : β) (c : E)
  结论: 积类型.mk a b ^ c = 积类型.mk (a ^ c) (b ^ c)
  证明: rfl

@[to_additive (attr := to_additive) (reorder := p c) smul_def]
-/
lemma pow_mk (a : α) (b : β) (c : E) : Prod.mk a b ^ c = Prod.mk (a ^ c) (b ^ c) := rfl

@[to_additive (attr := to_additive) (reorder := p c) smul_def]
/--
lemma `pow_def` / 引理 `pow_def`

English:
lemma pow_def
  given: (p : α × β) (c : E)
  statement: p ^ c = (p.1 ^ c, p.2 ^ c)
  proof: rfl

@[to_additive (attr := to_additive, simp) (reorder := p c) smul_swap]

中文:
引理 pow_def
  条件: (p : α × β) (c : E)
  结论: p ^ c = (p.1 ^ c, p.2 ^ c)
  证明: rfl

@[to_additive (attr := to_additive, simp) (reorder := p c) smul_swap]
-/
lemma pow_def (p : α × β) (c : E) : p ^ c = (p.1 ^ c, p.2 ^ c) := rfl

@[to_additive (attr := to_additive, simp) (reorder := p c) smul_swap]
/--
lemma `pow_swap` / 引理 `pow_swap`

English:
lemma pow_swap
  given: (p : α × β) (c : E)
  statement: (p ^ c).swap = p.swap ^ c
  proof: rfl

中文:
引理 pow_swap
  条件: (p : α × β) (c : E)
  结论: (p ^ c).swap = p.swap ^ c
  证明: rfl
-/
lemma pow_swap (p : α × β) (c : E) : (p ^ c).swap = p.swap ^ c := rfl

end Pow

section Star

variable [Star R] [Star S]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star (R × S)
  body: (star x.1, star x.2)

@[simp]

中文:
实例 :
  签名: 对合 (R × S)
  定义体: (star x.1, star x.2)

@[simp]
-/
instance : Star (R × S) where star x := (star x.1, star x.2)

@[simp]
/--
theorem `fst_star` / 定理 `fst_star`

English:
theorem fst_star
  given: (x : R × S)
  statement: (star x).1 = star x.1
  proof: rfl

@[simp]

中文:
定理 fst_star
  条件: (x : R × S)
  结论: (star x).1 = star x.1
  证明: rfl

@[simp]
-/
theorem fst_star (x : R × S) : (star x).1 = star x.1 := rfl

@[simp]
/--
theorem `snd_star` / 定理 `snd_star`

English:
theorem snd_star
  given: (x : R × S)
  statement: (star x).2 = star x.2
  proof: rfl

中文:
定理 snd_star
  条件: (x : R × S)
  结论: (star x).2 = star x.2
  证明: rfl
-/
theorem snd_star (x : R × S) : (star x).2 = star x.2 := rfl

/--
theorem `star_def` / 定理 `star_def`

English:
theorem star_def
  given: (x : R × S)
  statement: star x = (star x.1, star x.2)
  proof: rfl

中文:
定理 star_def
  条件: (x : R × S)
  结论: star x = (star x.1, star x.2)
  证明: rfl
-/
theorem star_def (x : R × S) : star x = (star x.1, star x.2) := rfl

end Star


end Prod
