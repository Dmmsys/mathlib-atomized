/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.Tactic.Ring

/-!
# Set of factors

## Main definitions
* `Associates.FactorSet`: multiset of factors of an element, unique up to propositional equality.
* `Associates.factors`: determine the `FactorSet` for a given element.

## TODO
* set up the complete lattice structure on `FactorSet`.

-/

@[expose] public section

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace Associates

open UniqueFactorizationMonoid Associated Multiset

variable [CommMonoidWithZero α]

/-- `FactorSet α` representation elements of unique factorization domain as multisets.
`Multiset α` produced by `normalizedFactors` are only unique up to associated elements, while the
multisets in `FactorSet α` are unique by equality and restricted to irreducible elements. This
gives us a representation of each element as a unique multisets (or the added ⊤ for 0), which has a
complete lattice structure. Infimum is the greatest common divisor and supremum is the least common
multiple.
-/
/-
**Associates.FactorSet.** 是 Mathlib 中的一个缩写定义，位于命名空间 `Associates`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FactorSet α` representation elements of unique factorization domain as multiset
s.
`Multiset α` produced by `normalizedFactors` are only unique up to associated el
ements, while the
multisets in `FactorSet α` are unique by equality and restricted to irreducible 
elements. This
gives us a representation of each element as a unique multisets (or the added ⊤ 
for 0), which has a
complete lattice structure. Infimum is the greatest common divisor and supremum 
is the least common
multiple.
-/
abbrev FactorSet.{u} (α : Type u) [CommMonoidWithZero α] : Type u :=
  WithTop (Multiset { a : Associates α // Irreducible a })

attribute [local instance] Associated.setoid
/-
**Associates.FactorSet.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Associates.FactorSet`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoidWithZero α] {a b : Multiset { a // Irre
ducible a }}, ↑(a + b) = ↑a + ↑b
参数：a + b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem FactorSet.coe_add {a b : Multiset { a : Associates α // Irreducible a }} :
    (↑(a + b) : FactorSet α) = a + b := by norm_cast
/-
**Associates.FactorSet.sup_add_inf_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `Associates.
FactorSet`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst_1 : DecidableEq (Asso
ciates α)] (a b : Associates.FactorSet α),   a ⊔ b + a ⊓ b = a + b
参数：Associates α；a b : Associates.FactorSet α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_sup`：∀ {α : Type u_1} [inst : SemilatticeSup α] (a b : α), ↑
(a ⊔ b) = ↑a ⊔ ↑b
· 使用定理 `WithTop.coe_inf`：∀ {α : Type u_1} [inst : SemilatticeInf α] (a b : α), ↑
(a ⊓ b) = ↑a ⊓ ↑b
· 使用定理 `WithTop.coe_add`：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a 
+ ↑b
· 使用定理 `WithTop.coe_eq_coe`：∀ {α : Type u_1} {a b : α}, ↑a = ↑b ↔ a = b
· 使用引理 `Multiset.union_add_inter`：union_add_inter (s t : Multiset α) : s union t
 + s inter t = s + t
-/
theorem FactorSet.sup_add_inf_eq_add [DecidableEq (Associates α)] :
    ∀ a b : FactorSet α, a ⊔ b + a ⊓ b = a + b
  | ⊤, b => show ⊤ ⊔ b + ⊤ ⊓ b = ⊤ + b by simp
  | a, ⊤ => show a ⊔ ⊤ + a ⊓ ⊤ = a + ⊤ by simp
  | WithTop.some a, WithTop.some b =>
    show (a : FactorSet α) ⊔ b + (a : FactorSet α) ⊓ b = a + b by
      rw [← WithTop.coe_sup, ← WithTop.coe_inf, ← WithTop.coe_add, ← WithTop.coe_add,
        WithTop.coe_eq_coe]
      exact Multiset.union_add_inter _ _

/-- Evaluates the product of a `FactorSet` to be the product of the corresponding multiset,
  or `0` if there is none. -/
/-
**Associates.FactorSet.prod** 是 Mathlib 中的一个定义，位于命名空间 `Associates.FactorSet`。
形式化陈述：{α : Type u_1} → [inst : CommMonoidWithZero α] → Associates.FactorSet α → 
Associates α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the product of a `FactorSet` to be the product of the corresponding mu
ltiset,
  or `0` if there is none.
-/
def FactorSet.prod : FactorSet α → Associates α
  | ⊤ => 0
  | WithTop.some s => (s.map (↑)).prod

@[simp]
/-
**Associates.prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：prod_top : (⊤ : FactorSet α).prod = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_top : (⊤ : FactorSet α).prod = 0 :=
  rfl

@[simp]
/-
**Associates.prod_coe** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：prod_coe {s : Multiset { a : Associates α // Irreducible a }} : FactorSet.
prod (s : FactorSet α) = (s.map (↑)).prod
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_coe {s : Multiset { a : Associates α // Irreducible a }} :
    FactorSet.prod (s : FactorSet α) = (s.map (↑)).prod :=
  rfl

@[simp]
/-
**Associates.prod_add** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoidWithZero α] (a b : Associates.FactorSet
 α), (a + b).prod = a.prod * b.prod
参数：a b : Associates.FactorSet α；a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.FactorSet.coe_add`：∀ {α : Type u_1} [inst : CommMonoidWithZer
o α] {a b : Multiset { a // Irreducible a }}, ↑(a + b) = ↑a + ↑b
· 使用定理 `Associates.prod_coe`：prod_coe {s : Multiset { a : Associates α // Irredu
cible a }} : FactorSet.prod (s : FactorSet α) = (s.map (↑)).prod
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Multiset.prod_add`：prod_add (s t : Multiset M) : prod (s + t) = prod s *
 prod t
-/
theorem prod_add : ∀ a b : FactorSet α, (a + b).prod = a.prod * b.prod
  | ⊤, b => show (⊤ + b).prod = (⊤ : FactorSet α).prod * b.prod by simp
  | a, ⊤ => show (a + ⊤).prod = a.prod * (⊤ : FactorSet α).prod by simp
  | WithTop.some a, WithTop.some b => by
    rw [← FactorSet.coe_add, prod_coe, prod_coe, prod_coe, Multiset.map_add, Multiset.prod_add]

@[gcongr]
/-
**Associates.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：prod_mono : forall {a b : FactorSet α}, a <= b -> a.prod <= b.prod | ⊤, b,
 h => by have : b = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.prod_top`：prod_top : (⊤ : FactorSet α).prod = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Associates.prod_le_prod`：prod_le_prod {p q : Multiset (Associates M)} (h
 : p <= q) : p.prod <= q.prod
· 使用定理 `Multiset.map_le_map`：map_le_map {f : α -> β} {s t : Multiset α} (h : s <
= t) : map f s <= map f t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
-/
theorem prod_mono : ∀ {a b : FactorSet α}, a ≤ b → a.prod ≤ b.prod
  | ⊤, b, h => by
    have : b = ⊤ := top_unique h
    rw [this, prod_top]
  | a, ⊤, _ => show a.prod ≤ (⊤ : FactorSet α).prod by simp
  | WithTop.some _, WithTop.some _, h =>
    prod_le_prod <| Multiset.map_le_map <| WithTop.coe_le_coe.1 <| h
/-
**Associates.FactorSet.prod_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Associates.Fa
ctorSet`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [IsCancelMulZero α] [Nontri
vial α] (p : Associates.FactorSet α),   p.prod = 0 ↔ p = ⊤
参数：p : Associates.FactorSet α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Associates.prod_coe`：prod_coe {s : Multiset { a : Associates α // Irredu
cible a }} : FactorSet.prod (s : FactorSet α) = (s.map (↑)).prod
· 使用定理 `Multiset.prod_eq_zero_iff`：∀ {M₀ : Type u_3} [inst : CommMonoidWithZero 
M₀] [NoZeroDivisors M₀] [Nontrivial M₀] {s : Multiset M₀},   s.prod = 0 ↔ 0 ∈ s
· 使用定理 `Associates.instNoZeroDivisors`：∀ {M : Type u_1} [inst : CommMonoidWithZe
ro M] [IsCancelMulZero M], NoZeroDivisors (Associates M)
· 使用定理 `Associates.instNontrivial`：∀ {M : Type u_1} [inst : MonoidWithZero M] [N
ontrivial M], Nontrivial (Associates M)
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `WithTop.coe_ne_top`：∀ {α : Type u_1} {a : α}, ↑a ≠ ⊤
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `not_and_of_not_right`：∀ (a : Prop) {b : Prop}, ¬b → ¬(a ∧ b)
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem FactorSet.prod_eq_zero_iff [IsCancelMulZero α] [Nontrivial α] (p : FactorSet α) :
    p.prod = 0 ↔ p = ⊤ := by
  unfold FactorSet at p
  induction p  -- TODO: `induction_eliminator` doesn't work with `abbrev`
  · simp only [Associates.prod_top]
  · rw [prod_coe, Multiset.prod_eq_zero_iff, Multiset.mem_map, eq_false WithTop.coe_ne_top,
      iff_false, not_exists]
    exact fun a => not_and_of_not_right _ a.prop.ne_zero

section count

variable [DecidableEq (Associates α)]

/-- `bcount p s` is the multiplicity of `p` in the FactorSet `s` (with bundled `p`). -/
/-
**Associates.bcount** 是 Mathlib 中的一个定义，位于命名空间 `Associates`。
形式化陈述：{α : Type u_1} →   [inst : CommMonoidWithZero α] → [DecidableEq (Associate
s α)] → { a // Irreducible a } → Associates.FactorSet α → ℕ
参数：Associates α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bcount p s` is the multiplicity of `p` in the FactorSet `s` (with bundled `p`).
-/
def bcount (p : { a : Associates α // Irreducible a }) :
    FactorSet α → ℕ
  | ⊤ => 0
  | WithTop.some s => s.count p

variable [∀ p : Associates α, Decidable (Irreducible p)] {p : Associates α}

/-- `count p s` is the multiplicity of the irreducible `p` in the FactorSet `s`.

If `p` is not irreducible, `count p s` is defined to be `0`. -/
/-
**Associates.count** 是 Mathlib 中的一个定义，位于命名空间 `Associates`。
形式化陈述：count (p : Associates α) : FactorSet α -> Nat
参数：p : Associates α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`count p s` is the multiplicity of the irreducible `p` in the FactorSet `s`.

If `p` is not irreducible, `count p s` is defined to be `0`.
-/
def count (p : Associates α) : FactorSet α → ℕ :=
  if hp : Irreducible p then bcount ⟨p, hp⟩ else 0

@[simp]
/-
**Associates.count_some** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：count_some (hp : Irreducible p) (s : Multiset _) : count p (WithTop.some s
) = s.count ⟨p, hp⟩
参数：hp : Irreducible p；s : Multiset _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_some (hp : Irreducible p) (s : Multiset _) :
    count p (WithTop.some s) = s.count ⟨p, hp⟩ := by
  simp only [count, dif_pos hp, bcount]

@[simp]
/-
**Associates.count_zero** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：count_zero (hp : Irreducible p) : count p (0 : FactorSet α) = 0
参数：hp : Irreducible p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_zero (hp : Irreducible p) : count p (0 : FactorSet α) = 0 := by
  simp only [count, dif_pos hp, bcount, Multiset.count_zero]
/-
**Associates.count_reducible** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：count_reducible (hp : ¬Irreducible p) : count p = 0
参数：hp : ¬Irreducible p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem count_reducible (hp : ¬Irreducible p) : count p = 0 := dif_neg hp

end count

section Mem

/-- membership in a FactorSet (bundled version) -/
/-
**Associates.BfactorSetMem** 是 Mathlib 中的一个定义，位于命名空间 `Associates`。
形式化陈述：{α : Type u_1} → [inst : CommMonoidWithZero α] → { a // Irreducible a } → 
Associates.FactorSet α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
membership in a FactorSet (bundled version)
-/
def BfactorSetMem : { a : Associates α // Irreducible a } → FactorSet α → Prop
  | _, ⊤ => True
  | p, some l => p ∈ l

/-- `FactorSetMem p s` is the predicate that the irreducible `p` is a member of
`s : FactorSet α`.

If `p` is not irreducible, `p` is not a member of any `FactorSet`. -/
/-
**Associates.FactorSetMem** 是 Mathlib 中的一个定义，位于命名空间 `Associates`。
形式化陈述：FactorSetMem (s : FactorSet α) (p : Associates α) : Prop
参数：s : FactorSet α；p : Associates α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FactorSetMem p s` is the predicate that the irreducible `p` is a member of
`s : FactorSet α`.

If `p` is not irreducible, `p` is not a member of any `FactorSet`.
-/
def FactorSetMem (s : FactorSet α) (p : Associates α) : Prop :=
  letI : Decidable (Irreducible p) := Classical.dec _
  if hp : Irreducible p then BfactorSetMem ⟨p, hp⟩ s else False
/-
**Associates.** 是 Mathlib 中的一个实例，位于命名空间 `Associates`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership (Associates α) (FactorSet α) :=
  ⟨FactorSetMem⟩

@[simp]
/-
**Associates.factorSetMem_eq_mem** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：factorSetMem_eq_mem (p : Associates α) (s : FactorSet α) : FactorSetMem s 
p = (p in s)
参数：p : Associates α；s : FactorSet α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem factorSetMem_eq_mem (p : Associates α) (s : FactorSet α) : FactorSetMem s p = (p ∈ s) :=
  rfl
/-
**Associates.mem_factorSet_top** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：mem_factorSet_top {p : Associates α} {hp : Irreducible p} : p in (⊤ : Fact
orSet α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `trivial`：True
-/
theorem mem_factorSet_top {p : Associates α} {hp : Irreducible p} : p ∈ (⊤ : FactorSet α) := by
  dsimp only [Membership.mem]; dsimp only [FactorSetMem]; split_ifs; exact trivial
/-
**Associates.mem_factorSet_some** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：mem_factorSet_some {p : Associates α} {hp : Irreducible p} {l : Multiset {
 a : Associates α // Irreducible a }} : p in (l : FactorSet α) ↔ Subtype.mk p hp
 in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_factorSet_some {p : Associates α} {hp : Irreducible p}
    {l : Multiset { a : Associates α // Irreducible a }} :
    p ∈ (l : FactorSet α) ↔ Subtype.mk p hp ∈ l := by
  dsimp only [Membership.mem]; dsimp only [FactorSetMem]; split_ifs; rfl
/-
**Associates.reducible_notMem_factorSet** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：reducible_notMem_factorSet {p : Associates α} (hp : ¬Irreducible p) (s : F
actorSet α) : p ∉ s
参数：hp : ¬Irreducible p；s : FactorSet α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Associates.FactorSetMem.eq_1`：∀ {α : Type u_1} [inst : CommMonoidWithZer
o α] (s : Associates.FactorSet α) (p : Associates α),   Associates.FactorSetMem 
s p = if hp : Irre…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.factorSetMem_eq_mem`：factorSetMem_eq_mem (p : Associates α) (
s : FactorSet α) : FactorSetMem s p = (p in s)
-/
theorem reducible_notMem_factorSet {p : Associates α} (hp : ¬Irreducible p) (s : FactorSet α) :
    p ∉ s := fun h ↦ by
  rwa [← factorSetMem_eq_mem, FactorSetMem, dif_neg hp] at h
/-
**Associates.irreducible_of_mem_factorSet** 是 Mathlib 中的一个定理，位于命名空间 `Associates`
。
形式化陈述：irreducible_of_mem_factorSet {p : Associates α} {s : FactorSet α} (h : p i
n s) : Irreducible p
参数：h : p in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Associates.reducible_notMem_factorSet`：reducible_notMem_factorSet {p : A
ssociates α} (hp : ¬Irreducible p) (s : FactorSet α) : p ∉ s
-/
theorem irreducible_of_mem_factorSet {p : Associates α} {s : FactorSet α} (h : p ∈ s) :
    Irreducible p :=
  by_contra fun hp ↦ reducible_notMem_factorSet hp s h

end Mem

variable [UniqueFactorizationMonoid α]

/-
**Associates.FactorSet.unique** 是 Mathlib 中的一个定理，位于命名空间 `Associates.FactorSet`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [UniqueFactorizationMonoid 
α] [Nontrivial α]   {p q : Associates.FactorSet α}, p.prod = q.prod → p = q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.FactorSet.prod_eq_zero_iff`：∀ {α : Type u_1} [inst : CommMono
idWithZero α] [IsCancelMulZero α] [Nontrivial α] (p : Associates.FactorSet α),  
 p.prod = 0 ↔ p = ⊤
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `Associates.prod_top`：prod_top : (⊤ : FactorSet α).prod = 0
· 使用定理 `Multiset.map_eq_map`：map_eq_map {f : α -> β} (hf : Function.Injective f)
 {s t : Multiset α} : s.map f = t.map f ↔ s = t
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Associates.unique'`：unique' {p q : Multiset (Associates α)} : (forall a 
in p, Irreducible a) -> (forall a in q, Irreducible a) -> p.prod = q.prod -> p =
 q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
-/
theorem FactorSet.unique [Nontrivial α] {p q : FactorSet α} (h : p.prod = q.prod) : p = q := by
  -- TODO: `induction_eliminator` doesn't work with `abbrev`
  unfold FactorSet at p q
  induction p <;> induction q
  · rfl
  · rw [eq_comm, ← FactorSet.prod_eq_zero_iff, ← h, Associates.prod_top]
  · rw [← FactorSet.prod_eq_zero_iff, h, Associates.prod_top]
  · congr 1
    rw [← Multiset.map_eq_map Subtype.coe_injective]
    apply unique' _ _ h <;>
      · intro a ha
        obtain ⟨⟨a', irred⟩, -, rfl⟩ := Multiset.mem_map.mp ha
        rwa [Subtype.coe_mk]

/-- This returns the multiset of irreducible factors as a `FactorSet`,
  a multiset of irreducible associates `WithTop`. -/
/-
**Associates.factors'** 是 Mathlib 中的一个定义，位于命名空间 `Associates`。
形式化陈述：factors' (a : α) : Multiset { a : Associates α // Irreducible a }
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_factor`：irreducible_of_factor {
a : α} : forall x : α, x in factors a -> Irreducible x

--- 原说明 ---
This returns the multiset of irreducible factors as a `FactorSet`,
  a multiset of irreducible associates `WithTop`.
-/
noncomputable def factors' (a : α) : Multiset { a : Associates α // Irreducible a } :=
  (factors a).pmap (fun a ha => ⟨Associates.mk a, irreducible_mk.2 ha⟩) irreducible_of_factor

@[simp]
/-
**Associates.map_subtype_coe_factors'** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：map_subtype_coe_factors' {a : α} : (factors' a).map (↑) = (factors a).map 
Associates.mk
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_factor`：irreducible_of_factor {
a : α} : forall x : α, x in factors a -> Irreducible x
· 使用定理 `Multiset.map_pmap`：map_pmap {p : α -> Prop} (g : β -> γ) (f : forall a, 
p a -> β) (s) : forall H, map g (pmap f s H) = pmap (fun a h => g (f a h)) s H
· 使用定理 `Multiset.pmap_eq_map`：pmap_eq_map (p : α -> Prop) (f : α -> β) (s : Mult
iset α) : forall H, @pmap _ _ p (fun a _ => f a) s H = map f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_subtype_coe_factors' {a : α} :
    (factors' a).map (↑) = (factors a).map Associates.mk := by
  simp [factors', Multiset.map_pmap, Multiset.pmap_eq_map]
/-
**Associates.factors'_cong** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst_1 : UniqueFactorizati
onMonoid α] {a b : α},   Associated a b → Associates.factors' a = Associates.fac
tors' b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `associated_zero_iff_eq_zero`：associated_zero_iff_eq_zero [MonoidWithZero
 M] (a : M) : a ~ᵤ 0 ↔ a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `Multiset.map_eq_map`：map_eq_map {f : α -> β} (hf : Function.Injective f)
 {s t : Multiset α} : s.map f = t.map f ↔ s = t
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Associates.map_subtype_coe_factors'`：map_subtype_coe_factors' {a : α} : 
(factors' a).map (↑) = (factors a).map Associates.mk
· 使用定理 `Associates.rel_associated_iff_map_eq_map`：rel_associated_iff_map_eq_map 
{p q : Multiset M} : Multiset.Rel Associated p q ↔ p.map Associates.mk = q.map A
ssociates.mk
· 使用定理 `UniqueFactorizationMonoid.factors_unique`：factors_unique {f g : Multiset
 α} (hf : forall x in f, Irreducible x) (hg : forall x in g, Irreducible x) (h :
 f.prod ~ᵤ g.prod) : Multiset.…
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_factor`：irreducible_of_factor {
a : α} : forall x : α, x in factors a -> Irreducible x
· 使用定理 `Associated.trans`：∀ {M : Type u_1} [inst : Monoid M] {x y z : M}, Associ
ated x y → Associated y z → Associated x z
· 使用定理 `UniqueFactorizationMonoid.factors_prod`：factors_prod {a : α} (ane0 : a !
= 0) : Associated (factors a).prod a
-/
theorem factors'_cong {a b : α} (h : a ~ᵤ b) : factors' a = factors' b := by
  obtain rfl | hb := eq_or_ne b 0
  · rw [associated_zero_iff_eq_zero] at h
    rw [h]
  have ha : a ≠ 0 := by
    contrapose hb with ha
    rw [← associated_zero_iff_eq_zero, ← ha]
    exact h.symm
  rw [← Multiset.map_eq_map Subtype.coe_injective, map_subtype_coe_factors',
    map_subtype_coe_factors', ← rel_associated_iff_map_eq_map]
  exact
    factors_unique irreducible_of_factor irreducible_of_factor
      ((factors_prod ha).trans <| h.trans <| (factors_prod hb).symm)

/-- This returns the multiset of irreducible factors of an associate as a `FactorSet`,
  a multiset of irreducible associates `WithTop`. -/
/-
**Associates.factors** 是 Mathlib 中的一个定义，位于命名空间 `Associates`。
形式化陈述：factors (a : Associates α) : FactorSet α
参数：a : Associates α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This returns the multiset of irreducible factors of an associate as a `FactorSet
`,
  a multiset of irreducible associates `WithTop`.
-/
noncomputable def factors (a : Associates α) : FactorSet α := by
  classical refine if h : a = 0 then ⊤ else Quotient.hrecOn a (fun x _ => factors' x) ?_ h
  intro a b hab
  apply Function.hfunext
  · have : a ~ᵤ 0 ↔ b ~ᵤ 0 := Iff.intro (fun ha0 => hab.symm.trans ha0) fun hb0 => hab.trans hb0
    simp only [associated_zero_iff_eq_zero] at this
    simp only [quotient_mk_eq_mk, this, mk_eq_zero]
  exact fun ha hb _ => heq_of_eq <| congr_arg some <| factors'_cong hab

@[simp]
/-
**Associates.factors_zero** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：factors_zero : (0 : Associates α).factors = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem factors_zero : (0 : Associates α).factors = ⊤ :=
  dif_pos rfl


@[simp]
/-
**Associates.factors_mk** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：factors_mk (a : α) (h : a != 0) : (Associates.mk a).factors = factors' a
参数：a : α；h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Associates.mk_eq_zero`：mk_eq_zero {a : M} : Associates.mk a = 0 ↔ a = 0
-/
theorem factors_mk (a : α) (h : a ≠ 0) : (Associates.mk a).factors = factors' a := by
  apply dif_neg
  apply mt mk_eq_zero.1 h

@[simp]
/-
**Associates.factors_prod** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：factors_prod (a : Associates α) : a.factors.prod = a
参数：a : Associates α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associates.mk_surjective`：mk_surjective [Monoid M] : Function.Surjective
 (@Associates.mk M _)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.factors_zero`：factors_zero : (0 : Associates α).factors = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.factors_mk`：factors_mk (a : α) (h : a != 0) : (Associates.mk 
a).factors = factors' a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Associates.map_subtype_coe_factors'`：map_subtype_coe_factors' {a : α} : 
(factors' a).map (↑) = (factors a).map Associates.mk
· 使用定理 `Associates.prod_mk`：prod_mk {p : Multiset M} : (p.map Associates.mk).pro
d = Associates.mk p.prod
-/
theorem factors_prod (a : Associates α) : a.factors.prod = a := by
  rcases Associates.mk_surjective a with ⟨a, rfl⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · simp [ha, prod_mk, mk_eq_mk_iff_associated, UniqueFactorizationMonoid.factors_prod]

@[simp]
/-
**Associates.prod_factors** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：prod_factors [Nontrivial α] (s : FactorSet α) : s.prod.factors = s
参数：s : FactorSet α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associates.FactorSet.unique`：∀ {α : Type u_1} [inst : CommMonoidWithZero
 α] [UniqueFactorizationMonoid α] [Nontrivial α]   {p q : Associates.FactorSet α
}, p.prod = q.pro…
· 使用定理 `Associates.factors_prod`：factors_prod (a : Associates α) : a.factors.pro
d = a
-/
theorem prod_factors [Nontrivial α] (s : FactorSet α) : s.prod.factors = s :=
  FactorSet.unique <| factors_prod _

@[nontriviality]
/-
**Associates.factors_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：factors_subsingleton [Subsingleton α] {a : Associates α} : a.factors = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Associates.factors_zero`：factors_zero : (0 : Associates α).factors = ⊤
-/
theorem factors_subsingleton [Subsingleton α] {a : Associates α} : a.factors = ⊤ := by
  have : Subsingleton (Associates α) := inferInstance
  convert! factors_zero
/-
**Associates.factors_eq_top_iff_zero** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：factors_eq_top_iff_zero {a : Associates α} : a.factors = ⊤ ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Associates.factors_subsingleton`：factors_subsingleton [Subsingleton α] {
a : Associates α} : a.factors = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.factors_prod`：factors_prod (a : Associates α) : a.factors.pro
d = a
· 使用定理 `Associates.FactorSet.prod_eq_zero_iff`：∀ {α : Type u_1} [inst : CommMono
idWithZero α] [IsCancelMulZero α] [Nontrivial α] (p : Associates.FactorSet α),  
 p.prod = 0 ↔ p = ⊤
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `Associates.factors_zero`：factors_zero : (0 : Associates α).factors = ⊤
-/
theorem factors_eq_top_iff_zero {a : Associates α} : a.factors = ⊤ ↔ a = 0 := by
  nontriviality α
  exact ⟨fun h ↦ by rwa [← factors_prod a, FactorSet.prod_eq_zero_iff], fun h ↦ h ▸ factors_zero⟩
/-
**Associates.factors_eq_some_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：factors_eq_some_iff_ne_zero {a : Associates α} : (exists s : Multiset { p 
: Associates α // Irreducible p }, a.factors = s) ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Associates.factors_eq_top_iff_zero`：factors_eq_top_iff_zero {a : Associa
tes α} : a.factors = ⊤ ↔ a = 0
-/
theorem factors_eq_some_iff_ne_zero {a : Associates α} :
    (∃ s : Multiset { p : Associates α // Irreducible p }, a.factors = s) ↔ a ≠ 0 := by
  simp_rw [@eq_comm _ a.factors, ← WithTop.ne_top_iff_exists]
  exact factors_eq_top_iff_zero.not
/-
**Associates.eq_of_factors_eq_factors** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：eq_of_factors_eq_factors {a b : Associates α} (h : a.factors = b.factors) 
: a = b
参数：h : a.factors = b.factors。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.factors_prod`：factors_prod (a : Associates α) : a.factors.pro
d = a
-/
theorem eq_of_factors_eq_factors {a b : Associates α} (h : a.factors = b.factors) : a = b := by
  have : a.factors.prod = b.factors.prod := by rw [h]
  rwa [factors_prod, factors_prod] at this

@[simp]
/-
**Associates.factors_mul** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：factors_mul (a b : Associates α) : (a * b).factors = a.factors + b.factors
参数：a b : Associates α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.factors_subsingleton`：factors_subsingleton [Subsingleton α] {
a : Associates α} : a.factors = ⊤
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Associates.FactorSet.unique`：∀ {α : Type u_1} [inst : CommMonoidWithZero
 α] [UniqueFactorizationMonoid α] [Nontrivial α]   {p q : Associates.FactorSet α
}, p.prod = q.pro…
· 使用定理 `Associates.eq_of_factors_eq_factors`：eq_of_factors_eq_factors {a b : Ass
ociates α} (h : a.factors = b.factors) : a = b
· 使用定理 `Associates.prod_add`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] (a b
 : Associates.FactorSet α), (a + b).prod = a.prod * b.prod
· 使用定理 `Associates.factors_prod`：factors_prod (a : Associates α) : a.factors.pro
d = a
-/
theorem factors_mul (a b : Associates α) : (a * b).factors = a.factors + b.factors := by
  nontriviality α
  refine FactorSet.unique <| eq_of_factors_eq_factors ?_
  rw [prod_add, factors_prod, factors_prod, factors_prod]

@[gcongr]
/-
**Associates.factors_mono** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst_1 : UniqueFactorizati
onMonoid α] {a b : Associates α},   a ≤ b → a.factors ≤ b.factors
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.factors_mul`：factors_mul (a b : Associates α) : (a * b).facto
rs = a.factors + b.factors
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem factors_mono : ∀ {a b : Associates α}, a ≤ b → a.factors ≤ b.factors
  | s, t, ⟨d, eq⟩ => by rw [eq, factors_mul]; exact le_add_of_nonneg_right bot_le

@[simp]
/-
**Associates.factors_le** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：factors_le {a b : Associates α} : a.factors <= b.factors ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associates.prod_mono`：prod_mono : forall {a b : FactorSet α}, a <= b -> 
a.prod <= b.prod | ⊤, b, h => by have : b = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.factors_prod`：factors_prod (a : Associates α) : a.factors.pro
d = a
· 使用定理 `Associates.factors_mono`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] 
[inst_1 : UniqueFactorizationMonoid α] {a b : Associates α},   a ≤ b → a.factors
 ≤ b.factors
-/
theorem factors_le {a b : Associates α} : a.factors ≤ b.factors ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, factors_mono⟩
  have : a.factors.prod ≤ b.factors.prod := prod_mono h
  rwa [factors_prod, factors_prod] at this

section count

variable [DecidableEq (Associates α)] [∀ p : Associates α, Decidable (Irreducible p)]

/-
**Associates.eq_factors_of_eq_counts** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：eq_factors_of_eq_counts {a b : Associates α} (ha : a != 0) (hb : b != 0) (
h : forall p : Associates α, Irreducible p -> p.count a.factors = p.count b.fact
ors) : a.factors = b.factors
参数：ha : a != 0；hb : b != 0；h : forall p : Associates α, Irreducible p -> p.count
 a.factors = p.count b.factors。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.factors_eq_some_iff_ne_zero`：factors_eq_some_iff_ne_zero {a :
 Associates α} : (exists s : Multiset { p : Associates α // Irreducible p }, a.f
actors = s) ↔ a != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_dep_congr_ctx`：∀ {p₁ p₂ q₁ : Prop}, p₁ = p₂ → ∀ {q₂ : p₂ → Prop}
, (∀ (h : p₂), q₁ = q₂ h) → (p₁ → q₁) = ∀ (h : p₂), q₂ h
· 使用定理 `Associates.count.congr_simp`：∀ {α : Type u_1} [inst : CommMonoidWithZero
 α] {inst_1 : DecidableEq (Associates α)}   [inst_2 : DecidableEq (Associates α)
] {inst_3 : (p : …
· 使用定理 `Associates.count_some`：count_some (hp : Irreducible p) (s : Multiset _) 
: count p (WithTop.some s) = s.count ⟨p, hp⟩
-/
theorem eq_factors_of_eq_counts {a b : Associates α} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : Associates α, Irreducible p → p.count a.factors = p.count b.factors) :
    a.factors = b.factors := by
  obtain ⟨sa, h_sa⟩ := factors_eq_some_iff_ne_zero.mpr ha
  obtain ⟨sb, h_sb⟩ := factors_eq_some_iff_ne_zero.mpr hb
  simp_all only [count_some, WithTop.coe_eq_coe]
  ext
  grind
/-
**Associates.eq_of_eq_counts** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：eq_of_eq_counts {a b : Associates α} (ha : a != 0) (hb : b != 0) (h : fora
ll p : Associates α, Irreducible p -> p.count a.factors = p.count b.factors) : a
 = b
参数：ha : a != 0；hb : b != 0；h : forall p : Associates α, Irreducible p -> p.count
 a.factors = p.count b.factors。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associates.eq_of_factors_eq_factors`：eq_of_factors_eq_factors {a b : Ass
ociates α} (h : a.factors = b.factors) : a = b
· 使用定理 `Associates.eq_factors_of_eq_counts`：eq_factors_of_eq_counts {a b : Assoc
iates α} (ha : a != 0) (hb : b != 0) (h : forall p : Associates α, Irreducible p
 -> p.count a.factors = …
-/
theorem eq_of_eq_counts {a b : Associates α} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : Associates α, Irreducible p → p.count a.factors = p.count b.factors) : a = b :=
  eq_of_factors_eq_factors (eq_factors_of_eq_counts ha hb h)
/-
**Associates.count_le_count_of_factors_le** 是 Mathlib 中的一个定理，位于命名空间 `Associates`
。
形式化陈述：count_le_count_of_factors_le {a b p : Associates α} (hb : b != 0) (hp : Ir
reducible p) (h : a.factors <= b.factors) : p.count a.factors <= p.count b.facto
rs
参数：hb : b != 0；hp : Irreducible p；h : a.factors <= b.factors。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.count.congr_simp`：∀ {α : Type u_1} [inst : CommMonoidWithZero
 α] {inst_1 : DecidableEq (Associates α)}   [inst_2 : DecidableEq (Associates α)
] {inst_3 : (p : …
· 使用定理 `Associates.factors.congr_simp`：∀ {α : Type u_1} [inst : CommMonoidWithZe
ro α] [inst_1 : UniqueFactorizationMonoid α] (a a_1 : Associates α),   a = a_1 →
 a.factors = a_1.fa…
· 使用定理 `Associates.factors_zero`：factors_zero : (0 : Associates α).factors = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.factors_eq_some_iff_ne_zero`：factors_eq_some_iff_ne_zero {a :
 Associates α} : (exists s : Multiset { p : Associates α // Irreducible p }, a.f
actors = s) ↔ a != 0
· 使用定理 `Associates.count_some`：count_some (hp : Irreducible p) (s : Multiset _) 
: count p (WithTop.some s) = s.count ⟨p, hp⟩
· 使用定理 `Multiset.count_le_of_le`：count_le_of_le (a : α) {s t} : s <= t -> count 
a s <= count a t
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
-/
theorem count_le_count_of_factors_le {a b p : Associates α} (hb : b ≠ 0) (hp : Irreducible p)
    (h : a.factors ≤ b.factors) : p.count a.factors ≤ p.count b.factors := by
  by_cases ha : a = 0
  · simp_all
  obtain ⟨sa, h_sa⟩ := factors_eq_some_iff_ne_zero.mpr ha
  obtain ⟨sb, h_sb⟩ := factors_eq_some_iff_ne_zero.mpr hb
  rw [h_sa, h_sb] at h ⊢
  rw [count_some hp, count_some hp]; rw [WithTop.coe_le_coe] at h
  exact Multiset.count_le_of_le _ h
/-
**Associates.count_le_count_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：count_le_count_of_le {a b p : Associates α} (hb : b != 0) (hp : Irreducibl
e p) (h : a <= b) : p.count a.factors <= p.count b.factors
参数：hb : b != 0；hp : Irreducible p；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associates.count_le_count_of_factors_le`：count_le_count_of_factors_le {a
 b p : Associates α} (hb : b != 0) (hp : Irreducible p) (h : a.factors <= b.fact
ors) : p.count a.factors <= p…
· 使用定理 `Associates.factors_mono`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] 
[inst_1 : UniqueFactorizationMonoid α] {a b : Associates α},   a ≤ b → a.factors
 ≤ b.factors
-/
theorem count_le_count_of_le {a b p : Associates α} (hb : b ≠ 0) (hp : Irreducible p) (h : a ≤ b) :
    p.count a.factors ≤ p.count b.factors :=
  count_le_count_of_factors_le hb hp <| factors_mono h

end count

/-
**Associates.prod_le** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：prod_le [Nontrivial α] {a b : FactorSet α} : a.prod <= b.prod ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associates.factors_mono`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] 
[inst_1 : UniqueFactorizationMonoid α] {a b : Associates α},   a ≤ b → a.factors
 ≤ b.factors
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.prod_factors`：prod_factors [Nontrivial α] (s : FactorSet α) :
 s.prod.factors = s
· 使用定理 `Associates.prod_mono`：prod_mono : forall {a b : FactorSet α}, a <= b -> 
a.prod <= b.prod | ⊤, b, h => by have : b = ⊤
-/
theorem prod_le [Nontrivial α] {a b : FactorSet α} : a.prod ≤ b.prod ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, prod_mono⟩
  have : a.prod.factors ≤ b.prod.factors := factors_mono h
  rwa [prod_factors, prod_factors] at this

open scoped Classical in
/-
**Associates.** 是 Mathlib 中的一个实例，位于命名空间 `Associates`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Max (Associates α) :=
  ⟨fun a b => (a.factors ⊔ b.factors).prod⟩

open scoped Classical in
/-
**Associates.** 是 Mathlib 中的一个实例，位于命名空间 `Associates`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Min (Associates α) :=
  ⟨fun a b => (a.factors ⊓ b.factors).prod⟩

open scoped Classical in
/-
**Associates.** 是 Mathlib 中的一个实例，位于命名空间 `Associates`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Lattice (Associates α) :=
  { Associates.instPartialOrder with
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    sup_le := fun _ _ c hac hbc =>
      factors_prod c ▸ prod_mono (sup_le (factors_mono hac) (factors_mono hbc))
    le_sup_left := fun a _ => le_trans (le_of_eq (factors_prod a).symm) <| prod_mono <| le_sup_left
    le_sup_right := fun _ b =>
      le_trans (le_of_eq (factors_prod b).symm) <| prod_mono <| le_sup_right
    le_inf := fun a _ _ hac hbc =>
      factors_prod a ▸ prod_mono (le_inf (factors_mono hac) (factors_mono hbc))
    inf_le_left := fun a _ => le_trans (prod_mono inf_le_left) (le_of_eq (factors_prod a))
    inf_le_right := fun _ b => le_trans (prod_mono inf_le_right) (le_of_eq (factors_prod b)) }

open scoped Classical in
/-
**Associates.sup_mul_inf** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：sup_mul_inf (a b : Associates α) : (a ⊔ b) * (a ⊓ b) = a * b
参数：a b : Associates α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Associates.factors_subsingleton`：factors_subsingleton [Subsingleton α] {
a : Associates α} : a.factors = ⊤
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Associates.instNoZeroDivisors`：∀ {M : Type u_1} [inst : CommMonoidWithZe
ro M] [IsCancelMulZero M], NoZeroDivisors (Associates M)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Associates.eq_of_factors_eq_factors`：eq_of_factors_eq_factors {a b : Ass
ociates α} (h : a.factors = b.factors) : a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.prod_add`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] (a b
 : Associates.FactorSet α), (a + b).prod = a.prod * b.prod
· 使用定理 `Associates.prod_factors`：prod_factors [Nontrivial α] (s : FactorSet α) :
 s.prod.factors = s
· 使用定理 `Associates.factors_mul`：factors_mul (a b : Associates α) : (a * b).facto
rs = a.factors + b.factors
· 使用定理 `Associates.FactorSet.sup_add_inf_eq_add`：∀ {α : Type u_1} [inst : CommMo
noidWithZero α] [inst_1 : DecidableEq (Associates α)] (a b : Associates.FactorSe
t α),   a ⊔ b + a ⊓ b = a + b
-/
theorem sup_mul_inf (a b : Associates α) : (a ⊔ b) * (a ⊓ b) = a * b :=
  show (a.factors ⊔ b.factors).prod * (a.factors ⊓ b.factors).prod = a * b by
    nontriviality α
    refine eq_of_factors_eq_factors ?_
    rw [← prod_add, prod_factors, factors_mul, FactorSet.sup_add_inf_eq_add]
/-
**Associates.dvd_of_mem_factors** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：dvd_of_mem_factors {a p : Associates α} (hm : p in factors a) : p ∣ a
参数：hm : p in factors a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.exists_non_zero_rep`：exists_non_zero_rep {a : Associates M} :
 a != 0 -> exists a0 : M, a0 != 0 ∧ Associates.mk a0 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.factors_prod`：factors_prod (a : Associates α) : a.factors.pro
d = a
· 使用定理 `Associates.factors_mk`：factors_mk (a : α) (h : a != 0) : (Associates.mk 
a).factors = factors' a
· 使用定理 `Associates.prod_coe`：prod_coe {s : Multiset { a : Associates α // Irredu
cible a }} : FactorSet.prod (s : FactorSet α) = (s.map (↑)).prod
· 使用引理 `Multiset.dvd_prod`：dvd_prod : a in s -> a ∣ s.prod
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Associates.irreducible_of_mem_factorSet`：irreducible_of_mem_factorSet {p
 : Associates α} {s : FactorSet α} (h : p in s) : Irreducible p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Associates.mem_factorSet_some`：mem_factorSet_some {p : Associates α} {hp
 : Irreducible p} {l : Multiset { a : Associates α // Irreducible a }} : p in (l
 : FactorSet α) ↔ S…
-/
theorem dvd_of_mem_factors {a p : Associates α} (hm : p ∈ factors a) :
    p ∣ a := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact dvd_zero p
  obtain ⟨a0, nza, ha'⟩ := exists_non_zero_rep ha0
  rw [← Associates.factors_prod a]
  rw [← ha', factors_mk a0 nza] at hm ⊢
  rw [prod_coe]
  apply Multiset.dvd_prod; apply Multiset.mem_map.mpr
  exact ⟨⟨p, irreducible_of_mem_factorSet hm⟩, mem_factorSet_some.mp hm, rfl⟩
/-
**Associates.dvd_of_mem_factors'** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：dvd_of_mem_factors' {a : α} {p : Associates α} {hp : Irreducible p} {hz : 
a != 0} (h_mem : Subtype.mk p hp in factors' a) : p ∣ Associates.mk a
参数：h_mem : Subtype.mk p hp in factors' a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associates.dvd_of_mem_factors`：dvd_of_mem_factors {a p : Associates α} (
hm : p in factors a) : p ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.factors_mk`：factors_mk (a : α) (h : a != 0) : (Associates.mk 
a).factors = factors' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.mem_factorSet_some`：mem_factorSet_some {p : Associates α} {hp
 : Irreducible p} {l : Multiset { a : Associates α // Irreducible a }} : p in (l
 : FactorSet α) ↔ S…
-/
theorem dvd_of_mem_factors' {a : α} {p : Associates α} {hp : Irreducible p} {hz : a ≠ 0}
    (h_mem : Subtype.mk p hp ∈ factors' a) : p ∣ Associates.mk a := by
  have := Classical.decEq (Associates α)
  apply dvd_of_mem_factors
  rw [factors_mk _ hz]
  apply mem_factorSet_some.2 h_mem
/-
**Associates.mem_factors'_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst_1 : UniqueFactorizati
onMonoid α] {a p : α},   a ≠ 0 → ∀ (hp : Irreducible p), p ∣ a → ⟨Associates.mk 
p, ⋯⟩ ∈ Associates.factors' a
参数：hp : Irreducible p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.irreducible_mk`：irreducible_mk {a : M} : Irreducible (Associa
tes.mk a) ↔ Irreducible a
· 使用定理 `UniqueFactorizationMonoid.exists_mem_factors_of_dvd`：exists_mem_factors_
of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) : p ∣ a -> exists q in fact
ors a, p ~ᵤ q
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_factor`：irreducible_of_factor {
a : α} : forall x : α, x in factors a -> Irreducible x
· 使用定理 `Multiset.mem_pmap`：mem_pmap {p : α -> Prop} {f : forall a, p a -> β} {s 
H b} : b in pmap f s H ↔ exists (a : _) (h : a in s), f a (H a h) = b
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.mk_eq_mk_iff_associated`：mk_eq_mk_iff_associated [Monoid M] {
a b : M} : Associates.mk a = Associates.mk b ↔ a ~ᵤ b
-/
theorem mem_factors'_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) (hd : p ∣ a) :
    Subtype.mk (Associates.mk p) (irreducible_mk.2 hp) ∈ factors' a := by
  obtain ⟨q, hq, hpq⟩ := exists_mem_factors_of_dvd ha0 hp hd
  apply Multiset.mem_pmap.mpr; use q; use hq
  exact Subtype.ext (Eq.symm (mk_eq_mk_iff_associated.mpr hpq))
/-
**Associates.mem_factors'_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst_1 : UniqueFactorizati
onMonoid α] {a p : α},   a ≠ 0 → ∀ (hp : Irreducible p), ⟨Associates.mk p, ⋯⟩ ∈ 
Associates.factors' a ↔ p ∣ a
参数：hp : Irreducible p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.irreducible_mk`：irreducible_mk {a : M} : Irreducible (Associa
tes.mk a) ↔ Irreducible a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.mk_dvd_mk`：mk_dvd_mk {a b : M} : Associates.mk a ∣ Associates
.mk b ↔ a ∣ b
· 使用定理 `Associates.dvd_of_mem_factors'`：dvd_of_mem_factors' {a : α} {p : Associa
tes α} {hp : Irreducible p} {hz : a != 0} (h_mem : Subtype.mk p hp in factors' a
) : p ∣ Associates.m…
· 使用定理 `Associates.mem_factors'_of_dvd`：∀ {α : Type u_1} [inst : CommMonoidWithZ
ero α] [inst_1 : UniqueFactorizationMonoid α] {a p : α},   a ≠ 0 → ∀ (hp : Irred
ucible p), p ∣ a → ⟨…
-/
theorem mem_factors'_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    Subtype.mk (Associates.mk p) (irreducible_mk.2 hp) ∈ factors' a ↔ p ∣ a := by
  constructor
  · rw [← mk_dvd_mk]
    apply dvd_of_mem_factors'
    apply ha0
  · apply mem_factors'_of_dvd ha0 hp
/-
**Associates.mem_factors_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：mem_factors_of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) (hd : p ∣
 a) : Associates.mk p in factors (Associates.mk a)
参数：ha0 : a != 0；hp : Irreducible p；hd : p ∣ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.factors_mk`：factors_mk (a : α) (h : a != 0) : (Associates.mk 
a).factors = factors' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.irreducible_mk`：irreducible_mk {a : M} : Irreducible (Associa
tes.mk a) ↔ Irreducible a
· 使用定理 `Associates.mem_factorSet_some`：mem_factorSet_some {p : Associates α} {hp
 : Irreducible p} {l : Multiset { a : Associates α // Irreducible a }} : p in (l
 : FactorSet α) ↔ S…
· 使用定理 `Associates.mem_factors'_of_dvd`：∀ {α : Type u_1} [inst : CommMonoidWithZ
ero α] [inst_1 : UniqueFactorizationMonoid α] {a p : α},   a ≠ 0 → ∀ (hp : Irred
ucible p), p ∣ a → ⟨…
-/
theorem mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) (hd : p ∣ a) :
    Associates.mk p ∈ factors (Associates.mk a) := by
  rw [factors_mk _ ha0]
  exact mem_factorSet_some.mpr (mem_factors'_of_dvd ha0 hp hd)
/-
**Associates.mem_factors_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：mem_factors_iff_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) : Associ
ates.mk p in factors (Associates.mk a) ↔ p ∣ a
参数：ha0 : a != 0；hp : Irreducible p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.mk_dvd_mk`：mk_dvd_mk {a b : M} : Associates.mk a ∣ Associates
.mk b ↔ a ∣ b
· 使用定理 `Associates.dvd_of_mem_factors`：dvd_of_mem_factors {a p : Associates α} (
hm : p in factors a) : p ∣ a
· 使用定理 `Associates.mem_factors_of_dvd`：mem_factors_of_dvd {a p : α} (ha0 : a != 
0) (hp : Irreducible p) (hd : p ∣ a) : Associates.mk p in factors (Associates.mk
 a)
-/
theorem mem_factors_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    Associates.mk p ∈ factors (Associates.mk a) ↔ p ∣ a := by
  constructor
  · rw [← mk_dvd_mk]
    apply dvd_of_mem_factors
  · apply mem_factors_of_dvd ha0 hp
/-
**Associates.exists_prime_dvd_of_not_inf_one** 是 Mathlib 中的一个定理，位于命名空间 `Associat
es`。
形式化陈述：exists_prime_dvd_of_not_inf_one {a b : α} (ha : a != 0) (hb : b != 0) (h :
 Associates.mk a ⊓ Associates.mk b != 1) : exists p : α, Prime p ∧ p ∣ a ∧ p ∣ b
参数：ha : a != 0；hb : b != 0；h : Associates.mk a ⊓ Associates.mk b != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_zero`：prod_zero : @prod M _ 0 = 1
· 使用定理 `Multiset.exists_mem_of_ne_zero`：exists_mem_of_ne_zero {s : Multiset α} :
 s != 0 -> exists a : α, a in s
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_eq_coe`：∀ {α : Type u_1} {a b : α}, ↑a = ↑b ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_inf`：∀ {α : Type u_1} [inst : SemilatticeInf α] (a b : α), ↑
(a ⊓ b) = ↑a ⊓ ↑b
· 使用定理 `Associates.factors_mk`：factors_mk (a : α) (h : a != 0) : (Associates.mk 
a).factors = factors' a
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q
· 使用定理 `UniqueFactorizationMonoid.irreducible_iff_prime`：∀ {α : Type u_2} {inst 
: CommMonoidWithZero α} [self : UniqueFactorizationMonoid α] {a : α}, Irreducibl
e a ↔ Prime a
· 使用定理 `Associates.irreducible_mk`：irreducible_mk {a : M} : Irreducible (Associa
tes.mk a) ↔ Irreducible a
· 使用定理 `Associates.dvd_of_mk_le_mk`：dvd_of_mk_le_mk {a b : M} : Associates.mk a 
<= Associates.mk b -> a ∣ b
· 使用定理 `Associates.dvd_of_mem_factors'`：dvd_of_mem_factors' {a : α} {p : Associa
tes α} {hp : Irreducible p} {hz : a != 0} (h_mem : Subtype.mk p hp in factors' a
) : p ∣ Associates.m…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Multiset.mem_inter`：mem_inter : a in s inter t ↔ a in s ∧ a in t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Multiset.inf_eq_inter`：∀ {α : Type u_1} [inst : DecidableEq α] (s t : Mu
ltiset α), s ⊓ t = s ∩ t
-/
theorem exists_prime_dvd_of_not_inf_one {a b : α} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Associates.mk a ⊓ Associates.mk b ≠ 1) : ∃ p : α, Prime p ∧ p ∣ a ∧ p ∣ b := by
  classical
  have hz : factors (Associates.mk a) ⊓ factors (Associates.mk b) ≠ 0 := by
    contrapose h with hf
    change (factors (Associates.mk a) ⊓ factors (Associates.mk b)).prod = 1
    rw [hf]
    exact Multiset.prod_zero
  rw [factors_mk a ha, factors_mk b hb, ← WithTop.coe_inf] at hz
  obtain ⟨⟨p0, p0_irr⟩, p0_mem⟩ := Multiset.exists_mem_of_ne_zero ((mt WithTop.coe_eq_coe.mpr) hz)
  rw [Multiset.inf_eq_inter] at p0_mem
  obtain ⟨p, rfl⟩ : ∃ p, Associates.mk p = p0 := Quot.exists_rep p0
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [← UniqueFactorizationMonoid.irreducible_iff_prime, ← irreducible_mk]
    exact p0_irr
  · apply dvd_of_mk_le_mk
    apply dvd_of_mem_factors' (Multiset.mem_inter.mp p0_mem).left
    apply ha
  · apply dvd_of_mk_le_mk
    apply dvd_of_mem_factors' (Multiset.mem_inter.mp p0_mem).right
    apply hb
/-
**Associates.coprime_iff_inf_one** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：coprime_iff_inf_one {a b : α} (ha0 : a != 0) (hb0 : b != 0) : Associates.m
k a ⊓ Associates.mk b = 1 ↔ forall {d : α}, d ∣ a -> d ∣ b -> ¬Prime d
参数：ha0 : a != 0；hb0 : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.prime_mk`：prime_mk {p : M} : Prime (Associates.mk p) ↔ Prime 
p
· 使用定理 `isUnit_of_dvd_one`：isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Associates.mk_le_mk_of_dvd`：mk_le_mk_of_dvd {a b : M} : a ∣ b -> Associa
tes.mk a <= Associates.mk b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Associates.exists_prime_dvd_of_not_inf_one`：exists_prime_dvd_of_not_inf_
one {a b : α} (ha : a != 0) (hb : b != 0) (h : Associates.mk a ⊓ Associates.mk b
 != 1) : exists p : α, Prime p ∧…
-/
theorem coprime_iff_inf_one {a b : α} (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    Associates.mk a ⊓ Associates.mk b = 1 ↔ ∀ {d : α}, d ∣ a → d ∣ b → ¬Prime d := by
  constructor
  · intro hg p ha hb hp
    refine (Associates.prime_mk.mpr hp).not_isUnit (isUnit_of_dvd_one ?_)
    rw [← hg]
    exact le_inf (mk_le_mk_of_dvd ha) (mk_le_mk_of_dvd hb)
  · contrapose
    intro hg hc
    obtain ⟨p, hp, hpa, hpb⟩ := exists_prime_dvd_of_not_inf_one ha0 hb0 hg
    exact hc hpa hpb hp
/-
**Associates.factors_self** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：factors_self [Nontrivial α] {p : Associates α} (hp : Irreducible p) : p.fa
ctors = WithTop.some {⟨p, hp⟩}
参数：hp : Irreducible p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associates.FactorSet.unique`：∀ {α : Type u_1} [inst : CommMonoidWithZero
 α] [UniqueFactorizationMonoid α] [Nontrivial α]   {p q : Associates.FactorSet α
}, p.prod = q.pro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.factors_prod`：factors_prod (a : Associates α) : a.factors.pro
d = a
· 使用定理 `Associates.FactorSet.prod.eq_def`：∀ {α : Type u_1} [inst : CommMonoidWit
hZero α] (x : Associates.FactorSet α),   x.prod =     match x with     | none =>
 0     | some s => (Mu…
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
-/
theorem factors_self [Nontrivial α] {p : Associates α} (hp : Irreducible p) :
    p.factors = WithTop.some {⟨p, hp⟩} :=
  FactorSet.unique
    (by rw [factors_prod, FactorSet.prod.eq_def]; dsimp; rw [prod_singleton])
/-
**Associates.factors_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：factors_prime_pow [Nontrivial α] {p : Associates α} (hp : Irreducible p) (
k : Nat) : factors (p ^ k) = WithTop.some (Multiset.replicate k ⟨p, hp⟩)
参数：hp : Irreducible p；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associates.FactorSet.unique`：∀ {α : Type u_1} [inst : CommMonoidWithZero
 α] [UniqueFactorizationMonoid α] [Nontrivial α]   {p q : Associates.FactorSet α
}, p.prod = q.pro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.factors_prod`：factors_prod (a : Associates α) : a.factors.pro
d = a
· 使用定理 `Associates.FactorSet.prod.eq_def`：∀ {α : Type u_1} [inst : CommMonoidWit
hZero α] (x : Associates.FactorSet α),   x.prod =     match x with     | none =>
 0     | some s => (Mu…
· 使用定理 `Multiset.map_replicate`：map_replicate (f : α -> β) (k : Nat) (a : α) : (
replicate k a).map f = replicate k (f a)
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
-/
theorem factors_prime_pow [Nontrivial α] {p : Associates α} (hp : Irreducible p) (k : ℕ) :
    factors (p ^ k) = WithTop.some (Multiset.replicate k ⟨p, hp⟩) :=
  FactorSet.unique
    (by
      rw [Associates.factors_prod, FactorSet.prod.eq_def]
      dsimp; rw [Multiset.map_replicate, Multiset.prod_replicate, Subtype.coe_mk])
/-
**Associates.prime_pow_le_iff_le_bcount** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：prime_pow_le_iff_le_bcount [DecidableEq (Associates α)] {m p : Associates 
α} (h₁ : m != 0) (h₂ : Irreducible p) {k : Nat} : p ^ k <= m ↔ k <= bcount ⟨p, h
₂⟩ m.factors
参数：Associates α；h₁ : m != 0；h₂ : Irreducible p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associates.exists_non_zero_rep`：exists_non_zero_rep {a : Associates M} :
 a != 0 -> exists a0 : M, a0 != 0 ∧ Associates.mk a0 = a
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.bcount.eq_def`：∀ {α : Type u_1} [inst : CommMonoidWithZero α]
 [inst_1 : DecidableEq (Associates α)] (p : { a // Irreducible a })   (x : Assoc
iates.FactorSe…
· 使用定理 `Associates.factors_mk`：factors_mk (a : α) (h : a != 0) : (Associates.mk 
a).factors = factors' a
· 使用定理 `Multiset.le_count_iff_replicate_le`：le_count_iff_replicate_le {a : α} {s
 : Multiset α} {n : Nat} : n <= count a s ↔ replicate n a <= s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.factors_le`：factors_le {a b : Associates α} : a.factors <= b.
factors ↔ a <= b
· 使用定理 `Associates.factors_prime_pow`：factors_prime_pow [Nontrivial α] {p : Asso
ciates α} (hp : Irreducible p) (k : Nat) : factors (p ^ k) = WithTop.some (Multi
set.replicate k ⟨p…
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prime_pow_le_iff_le_bcount [DecidableEq (Associates α)] {m p : Associates α}
    (h₁ : m ≠ 0) (h₂ : Irreducible p) {k : ℕ} : p ^ k ≤ m ↔ k ≤ bcount ⟨p, h₂⟩ m.factors := by
  rcases Associates.exists_non_zero_rep h₁ with ⟨m, hm, rfl⟩
  have := nontrivial_of_ne _ _ hm
  rw [bcount.eq_def, factors_mk, Multiset.le_count_iff_replicate_le, ← factors_le,
    factors_prime_pow, factors_mk, WithTop.coe_le_coe] <;> assumption

@[simp]
/-
**Associates.factors_one** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：factors_one [Nontrivial α] : factors (1 : Associates α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associates.FactorSet.unique`：∀ {α : Type u_1} [inst : CommMonoidWithZero
 α] [UniqueFactorizationMonoid α] [Nontrivial α]   {p q : Associates.FactorSet α
}, p.prod = q.pro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.factors_prod`：factors_prod (a : Associates α) : a.factors.pro
d = a
· 使用定理 `Multiset.prod_zero`：prod_zero : @prod M _ 0 = 1
-/
theorem factors_one [Nontrivial α] : factors (1 : Associates α) = 0 := by
  apply FactorSet.unique
  rw [Associates.factors_prod]
  exact Multiset.prod_zero

@[simp]
/-
**Associates.pow_factors** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：pow_factors [Nontrivial α] {a : Associates α} {k : Nat} : (a ^ k).factors 
= k • a.factors
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Associates.factors_one`：factors_one [Nontrivial α] : factors (1 : Associ
ates α) = 0
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `Associates.factors_mul`：factors_mul (a b : Associates α) : (a * b).facto
rs = a.factors + b.factors
-/
theorem pow_factors [Nontrivial α] {a : Associates α} {k : ℕ} :
    (a ^ k).factors = k • a.factors := by
  induction k with
  | zero => rw [zero_nsmul, pow_zero]; exact factors_one
  | succ n h => rw [pow_succ, succ_nsmul, factors_mul, h]

section count

variable [DecidableEq (Associates α)] [∀ p : Associates α, Decidable (Irreducible p)]

/-
**Associates.prime_pow_dvd_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：prime_pow_dvd_iff_le {m p : Associates α} (h₁ : m != 0) (h₂ : Irreducible 
p) {k : Nat} : p ^ k <= m ↔ k <= count p m.factors
参数：h₁ : m != 0；h₂ : Irreducible p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.count.eq_1`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [i
nst_1 : DecidableEq (Associates α)]   [inst_2 : (p : Associates α) → Decidable (
Irreducible…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Associates.prime_pow_le_iff_le_bcount`：prime_pow_le_iff_le_bcount [Decid
ableEq (Associates α)] {m p : Associates α} (h₁ : m != 0) (h₂ : Irreducible p) {
k : Nat} : p ^ k <= m ↔ k <…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prime_pow_dvd_iff_le {m p : Associates α} (h₁ : m ≠ 0) (h₂ : Irreducible p) {k : ℕ} :
    p ^ k ≤ m ↔ k ≤ count p m.factors := by
  rw [count, dif_pos h₂, prime_pow_le_iff_le_bcount h₁]
/-
**Associates.le_of_count_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：le_of_count_ne_zero {m p : Associates α} (h0 : m != 0) (hp : Irreducible p
) : count p m.factors != 0 -> p <= m
参数：h0 : m != 0；hp : Irreducible p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.prime_pow_dvd_iff_le`：prime_pow_dvd_iff_le {m p : Associates 
α} (h₁ : m != 0) (h₂ : Irreducible p) {k : Nat} : p ^ k <= m ↔ k <= count p m.fa
ctors
-/
theorem le_of_count_ne_zero {m p : Associates α} (h0 : m ≠ 0) (hp : Irreducible p) :
    count p m.factors ≠ 0 → p ≤ m := by
  rw [← pos_iff_ne_zero]
  intro h
  rw [← pow_one p]
  apply (prime_pow_dvd_iff_le h0 hp).2
  simpa only
/-
**Associates.count_ne_zero_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：count_ne_zero_iff_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) : (Ass
ociates.mk p).count (Associates.mk a).factors != 0 ↔ p ∣ a
参数：ha0 : a != 0；hp : Irreducible p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.mk_le_mk_iff_dvd`：mk_le_mk_iff_dvd {a b : M} : Associates.mk 
a <= Associates.mk b ↔ a ∣ b
· 使用定理 `Associates.le_of_count_ne_zero`：le_of_count_ne_zero {m p : Associates α}
 (h0 : m != 0) (hp : Irreducible p) : count p m.factors != 0 -> p <= m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.mk_ne_zero`：mk_ne_zero {a : M} : Associates.mk a != 0 ↔ a != 
0
· 使用定理 `Associates.irreducible_mk`：irreducible_mk {a : M} : Irreducible (Associa
tes.mk a) ↔ Irreducible a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Associates.prime_pow_dvd_iff_le`：prime_pow_dvd_iff_le {m p : Associates 
α} (h₁ : m != 0) (h₂ : Irreducible p) {k : Nat} : p ^ k <= m ↔ k <= count p m.fa
ctors
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem count_ne_zero_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    (Associates.mk p).count (Associates.mk a).factors ≠ 0 ↔ p ∣ a := by
  rw [← Associates.mk_le_mk_iff_dvd]
  refine
    ⟨fun h =>
      Associates.le_of_count_ne_zero (Associates.mk_ne_zero.mpr ha0)
        (Associates.irreducible_mk.mpr hp) h,
      fun h => ?_⟩
  rw [← pow_one (Associates.mk p),
    Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr ha0)
      (Associates.irreducible_mk.mpr hp)] at h
  exact (zero_lt_one.trans_le h).ne'
/-
**Associates.count_self** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：count_self [Nontrivial α] {p : Associates α} (hp : Irreducible p) : p.coun
t p.factors = 1
参数：hp : Irreducible p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.count.congr_simp`：∀ {α : Type u_1} [inst : CommMonoidWithZero
 α] {inst_1 : DecidableEq (Associates α)}   [inst_2 : DecidableEq (Associates α)
] {inst_3 : (p : …
· 使用定理 `Associates.factors_self`：factors_self [Nontrivial α] {p : Associates α} 
(hp : Irreducible p) : p.factors = WithTop.some {⟨p, hp⟩}
· 使用定理 `Associates.count_some`：count_some (hp : Irreducible p) (s : Multiset _) 
: count p (WithTop.some s) = s.count ⟨p, hp⟩
· 使用定理 `Multiset.count_eq_one_of_mem`：count_eq_one_of_mem [DecidableEq α] {a : α
} {s : Multiset α} (d : Nodup s) (h : a in s) : count a s = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_self [Nontrivial α] {p : Associates α}
    (hp : Irreducible p) : p.count p.factors = 1 := by
  simp [factors_self hp, Associates.count_some hp]
/-
**Associates.count_eq_zero_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：count_eq_zero_of_ne {p q : Associates α} (hp : Irreducible p) (hq : Irredu
cible q) (h : p != q) : p.count q.factors = 0
参数：hp : Irreducible p；hq : Irreducible q；h : p != q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Irreducible.associated_of_dvd`：Irreducible.associated_of_dvd [Monoid M] 
{p q : M} (p_irr : Irreducible p) (q_irr : Irreducible q) (dvd : p ∣ q) : Associ
ated p q
· 使用定理 `Associates.le_of_count_ne_zero`：le_of_count_ne_zero {m p : Associates α}
 (h0 : m != 0) (hp : Irreducible p) : count p m.factors != 0 -> p <= m
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
-/
theorem count_eq_zero_of_ne {p q : Associates α} (hp : Irreducible p)
    (hq : Irreducible q) (h : p ≠ q) : p.count q.factors = 0 :=
  not_ne_iff.mp fun h' ↦ h <| associated_iff_eq.mp <| hp.associated_of_dvd hq <|
    le_of_count_ne_zero hq.ne_zero hp h'
/-
**Associates.count_mul** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：count_mul {a : Associates α} (ha : a != 0) {b : Associates α} (hb : b != 0
) {p : Associates α} (hp : Irreducible p) : count p (factors (a * b)) = count p 
a.factors + count p b.factors
参数：ha : a != 0；hb : b != 0；hp : Irreducible p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associates.exists_non_zero_rep`：exists_non_zero_rep {a : Associates M} :
 a != 0 -> exists a0 : M, a0 != 0 ∧ Associates.mk a0 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.factors_mul`：factors_mul (a b : Associates α) : (a * b).facto
rs = a.factors + b.factors
· 使用定理 `Associates.factors_mk`：factors_mk (a : α) (h : a != 0) : (Associates.mk 
a).factors = factors' a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.FactorSet.coe_add`：∀ {α : Type u_1} [inst : CommMonoidWithZer
o α] {a b : Multiset { a // Irreducible a }}, ↑(a + b) = ↑a + ↑b
· 使用定理 `Associates.count_some`：count_some (hp : Irreducible p) (s : Multiset _) 
: count p (WithTop.some s) = s.count ⟨p, hp⟩
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
-/
theorem count_mul {a : Associates α} (ha : a ≠ 0) {b : Associates α}
    (hb : b ≠ 0) {p : Associates α} (hp : Irreducible p) :
    count p (factors (a * b)) = count p a.factors + count p b.factors := by
  obtain ⟨a0, nza, rfl⟩ := exists_non_zero_rep ha
  obtain ⟨b0, nzb, rfl⟩ := exists_non_zero_rep hb
  rw [factors_mul, factors_mk a0 nza, factors_mk b0 nzb, ← FactorSet.coe_add, count_some hp,
    Multiset.count_add, count_some hp, count_some hp]
/-
**Associates.count_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：count_of_coprime {a : Associates α} (ha : a != 0) {b : Associates α} (hb :
 b != 0) (hab : forall d, d ∣ a -> d ∣ b -> ¬Prime d) {p : Associates α} (hp : I
rreducible p) : count p a.factors = 0 ∨ count p b.factors = 0
参数：ha : a != 0；hb : b != 0；hab : forall d, d ∣ a -> d ∣ b -> ¬Prime d；hp : Irred
ucible p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Associates.le_of_count_ne_zero`：le_of_count_ne_zero {m p : Associates α}
 (h0 : m != 0) (hp : Irreducible p) : count p m.factors != 0 -> p <= m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UniqueFactorizationMonoid.irreducible_iff_prime`：∀ {α : Type u_2} {inst 
: CommMonoidWithZero α} [self : UniqueFactorizationMonoid α] {a : α}, Irreducibl
e a ↔ Prime a
-/
theorem count_of_coprime {a : Associates α} (ha : a ≠ 0)
    {b : Associates α} (hb : b ≠ 0) (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) {p : Associates α}
    (hp : Irreducible p) : count p a.factors = 0 ∨ count p b.factors = 0 := by
  rw [or_iff_not_imp_left, ← Ne]
  intro hca
  contrapose! hab with hcb
  exact ⟨p, le_of_count_ne_zero ha hp hca, le_of_count_ne_zero hb hp hcb,
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hp⟩
/-
**Associates.count_mul_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：count_mul_of_coprime {a : Associates α} {b : Associates α} (hb : b != 0) {
p : Associates α} (hp : Irreducible p) (hab : forall d, d ∣ a -> d ∣ b -> ¬Prime
 d) : count p a.factors = 0 ∨ count p a.factors = count p (a * b).factors
参数：hb : b != 0；hp : Irreducible p；hab : forall d, d ∣ a -> d ∣ b -> ¬Prime d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Associates.count.congr_simp`：∀ {α : Type u_1} [inst : CommMonoidWithZero
 α] {inst_1 : DecidableEq (Associates α)}   [inst_2 : DecidableEq (Associates α)
] {inst_3 : (p : …
· 使用定理 `Associates.factors.congr_simp`：∀ {α : Type u_1} [inst : CommMonoidWithZe
ro α] [inst_1 : UniqueFactorizationMonoid α] (a a_1 : Associates α),   a = a_1 →
 a.factors = a_1.fa…
· 使用定理 `Associates.factors_zero`：factors_zero : (0 : Associates α).factors = ⊤
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Associates.count_of_coprime`：count_of_coprime {a : Associates α} (ha : a
 != 0) {b : Associates α} (hb : b != 0) (hab : forall d, d ∣ a -> d ∣ b -> ¬Prim
e d) {p : Associa…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Or.intro_right`：∀ {b : Prop} (a : Prop), b → a ∨ b
· 使用定理 `Associates.count_mul`：count_mul {a : Associates α} (ha : a != 0) {b : As
sociates α} (hb : b != 0) {p : Associates α} (hp : Irreducible p) : count p (fac
tors (a * …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem count_mul_of_coprime {a : Associates α} {b : Associates α}
    (hb : b ≠ 0) {p : Associates α} (hp : Irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) :
    count p a.factors = 0 ∨ count p a.factors = count p (a * b).factors := by
  by_cases ha : a = 0
  · simp [ha]
  rcases count_of_coprime ha hb hab hp with hz | hb0; · tauto
  apply Or.intro_right
  rw [count_mul ha hb hp, hb0, add_zero]
/-
**Associates.count_mul_of_coprime'** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：count_mul_of_coprime' {a b : Associates α} {p : Associates α} (hp : Irredu
cible p) (hab : forall d, d ∣ a -> d ∣ b -> ¬Prime d) : count p (a * b).factors 
= count p a.factors ∨ count p (a * b).factors = count p b.factors
参数：hp : Irreducible p；hab : forall d, d ∣ a -> d ∣ b -> ¬Prime d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.count.congr_simp`：∀ {α : Type u_1} [inst : CommMonoidWithZero
 α] {inst_1 : DecidableEq (Associates α)}   [inst_2 : DecidableEq (Associates α)
] {inst_3 : (p : …
· 使用定理 `Associates.factors.congr_simp`：∀ {α : Type u_1} [inst : CommMonoidWithZe
ro α] [inst_1 : UniqueFactorizationMonoid α] (a a_1 : Associates α),   a = a_1 →
 a.factors = a_1.fa…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Associates.factors_zero`：factors_zero : (0 : Associates α).factors = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Associates.count_mul`：count_mul {a : Associates α} (ha : a != 0) {b : As
sociates α} (hb : b != 0) {p : Associates α} (hp : Irreducible p) : count p (fac
tors (a * …
· 使用定理 `Associates.count_of_coprime`：count_of_coprime {a : Associates α} (ha : a
 != 0) {b : Associates α} (hb : b != 0) (hab : forall d, d ∣ a -> d ∣ b -> ¬Prim
e d) {p : Associa…
· 使用定理 `Or.intro_right`：∀ {b : Prop} (a : Prop), b → a ∨ b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Or.intro_left`：∀ {a : Prop} (b : Prop), a → a ∨ b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem count_mul_of_coprime' {a b : Associates α} {p : Associates α}
    (hp : Irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) :
    count p (a * b).factors = count p a.factors ∨ count p (a * b).factors = count p b.factors := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [count_mul ha hb hp]
  rcases count_of_coprime ha hb hab hp with ha0 | hb0
  · apply Or.intro_right
    rw [ha0, zero_add]
  · apply Or.intro_left
    rw [hb0, add_zero]
/-
**Associates.dvd_count_of_dvd_count_mul** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：dvd_count_of_dvd_count_mul {a b : Associates α} (hb : b != 0) {p : Associa
tes α} (hp : Irreducible p) (hab : forall d, d ∣ a -> d ∣ b -> ¬Prime d) {k : Na
t} (habk : k ∣ count p (a * b).factors) : k ∣ count p a.factors
参数：hb : b != 0；hp : Irreducible p；hab : forall d, d ∣ a -> d ∣ b -> ¬Prime d；hab
k : k ∣ count p (a * b).factors。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.count.congr_simp`：∀ {α : Type u_1} [inst : CommMonoidWithZero
 α] {inst_1 : DecidableEq (Associates α)}   [inst_2 : DecidableEq (Associates α)
] {inst_3 : (p : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Associates.factors.congr_simp`：∀ {α : Type u_1} [inst : CommMonoidWithZe
ro α] [inst_1 : UniqueFactorizationMonoid α] (a a_1 : Associates α),   a = a_1 →
 a.factors = a_1.fa…
· 使用定理 `Associates.factors_zero`：factors_zero : (0 : Associates α).factors = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Associates.count_of_coprime`：count_of_coprime {a : Associates α} (ha : a
 != 0) {b : Associates α} (hb : b != 0) (hab : forall d, d ∣ a -> d ∣ b -> ¬Prim
e d) {p : Associa…
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Associates.count_mul`：count_mul {a : Associates α} (ha : a != 0) {b : As
sociates α} (hb : b != 0) {p : Associates α} (hp : Irreducible p) : count p (fac
tors (a * …
-/
theorem dvd_count_of_dvd_count_mul {a b : Associates α} (hb : b ≠ 0)
    {p : Associates α} (hp : Irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) {k : ℕ}
    (habk : k ∣ count p (a * b).factors) : k ∣ count p a.factors := by
  by_cases ha : a = 0
  · simpa [*] using habk
  rcases count_of_coprime ha hb hab hp with hz | h
  · rw [hz]
    exact dvd_zero k
  · rw [count_mul ha hb hp, h] at habk
    exact habk
/-
**Associates.count_pow** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：count_pow [Nontrivial α] {a : Associates α} (ha : a != 0) {p : Associates 
α} (hp : Irreducible p) (k : Nat) : count p (a ^ k).factors = k * count p a.fact
ors
参数：ha : a != 0；hp : Irreducible p；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Associates.factors_one`：factors_one [Nontrivial α] : factors (1 : Associ
ates α) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Associates.count_zero`：count_zero (hp : Irreducible p) : count p (0 : Fa
ctorSet α) = 0
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Associates.count_mul`：count_mul {a : Associates α} (ha : a != 0) {b : As
sociates α} (hb : b != 0) {p : Associates α} (hp : Irreducible p) : count p (fac
tors (a * …
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Associates.instNoZeroDivisors`：∀ {M : Type u_1} [inst : CommMonoidWithZe
ro M] [IsCancelMulZero M], NoZeroDivisors (Associates M)
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 31 条，此处仅展示前 30 条）
-/
theorem count_pow [Nontrivial α] {a : Associates α} (ha : a ≠ 0)
    {p : Associates α} (hp : Irreducible p) (k : ℕ) :
    count p (a ^ k).factors = k * count p a.factors := by
  induction k with
  | zero => rw [pow_zero, factors_one, zero_mul, count_zero hp]
  | succ n h => rw [pow_succ', count_mul ha (pow_ne_zero _ ha) hp, h]; ring
/-
**Associates.dvd_count_pow** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：dvd_count_pow [Nontrivial α] {a : Associates α} (ha : a != 0) {p : Associa
tes α} (hp : Irreducible p) (k : Nat) : k ∣ count p (a ^ k).factors
参数：ha : a != 0；hp : Irreducible p；k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.count_pow`：count_pow [Nontrivial α] {a : Associates α} (ha : 
a != 0) {p : Associates α} (hp : Irreducible p) (k : Nat) : count p (a ^ k).fact
ors = k * …
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem dvd_count_pow [Nontrivial α] {a : Associates α} (ha : a ≠ 0)
    {p : Associates α} (hp : Irreducible p) (k : ℕ) : k ∣ count p (a ^ k).factors := by
  rw [count_pow ha hp]
  apply dvd_mul_right
/-
**Associates.is_pow_of_dvd_count** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：is_pow_of_dvd_count {a : Associates α} (ha : a != 0) {k : Nat} (hk : foral
l p : Associates α, Irreducible p -> k ∣ count p a.factors) : exists b : Associa
tes α, a = b ^ k
参数：ha : a != 0；hk : forall p : Associates α, Irreducible p -> k ∣ count p a.fact
ors。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Associates.exists_non_zero_rep`：exists_non_zero_rep {a : Associates M} :
 a != 0 -> exists a0 : M, a0 != 0 ∧ Associates.mk a0 = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.count_some`：count_some (hp : Irreducible p) (s : Multiset _) 
: count p (WithTop.some s) = s.count ⟨p, hp⟩
· 使用定理 `Associates.factors_mk`：factors_mk (a : α) (h : a != 0) : (Associates.mk 
a).factors = factors' a
· 使用定理 `Multiset.exists_smul_of_dvd_count`：exists_smul_of_dvd_count (s : Multise
t ι) {k : Nat} (h : forall a : ι, a in s -> k ∣ Multiset.count a s) : exists u :
 Multiset ι, s = k • u
· 使用定理 `Associates.eq_of_factors_eq_factors`：eq_of_factors_eq_factors {a b : Ass
ociates α} (h : a.factors = b.factors) : a = b
· 使用定理 `Associates.pow_factors`：pow_factors [Nontrivial α] {a : Associates α} {k
 : Nat} : (a ^ k).factors = k • a.factors
· 使用定理 `Associates.prod_factors`：prod_factors [Nontrivial α] (s : FactorSet α) :
 s.prod.factors = s
· 使用引理 `WithBot.coe_nsmul`：coe_nsmul (a : α) (n : Nat) : ↑(n • a) = n • (a : Wit
hBot α)
-/
theorem is_pow_of_dvd_count {a : Associates α}
    (ha : a ≠ 0) {k : ℕ} (hk : ∀ p : Associates α, Irreducible p → k ∣ count p a.factors) :
    ∃ b : Associates α, a = b ^ k := by
  nontriviality α
  obtain ⟨a0, hz, rfl⟩ := exists_non_zero_rep ha
  rw [factors_mk a0 hz] at hk
  have hk' : ∀ p, p ∈ factors' a0 → k ∣ (factors' a0).count p := by
    rintro p -
    have pp : p = ⟨p.val, p.2⟩ := by simp only [Subtype.coe_eta]
    rw [pp, ← count_some p.2]
    exact hk p.val p.2
  obtain ⟨u, hu⟩ := Multiset.exists_smul_of_dvd_count _ hk'
  use FactorSet.prod (u : FactorSet α)
  apply eq_of_factors_eq_factors
  rw [pow_factors, prod_factors, factors_mk a0 hz, hu]
  exact WithBot.coe_nsmul u k

/-- The only divisors of prime powers are prime powers. See `eq_pow_find_of_dvd_irreducible_pow`
for an explicit expression as a p-power (without using `count`). -/
/-
**Associates.eq_pow_count_factors_of_dvd_pow** 是 Mathlib 中的一个定理，位于命名空间 `Associat
es`。
形式化陈述：eq_pow_count_factors_of_dvd_pow {p a : Associates α} (hp : Irreducible p) 
{n : Nat} (h : a ∣ p ^ n) : a = p ^ p.count a.factors
参数：hp : Irreducible p；h : a ∣ p ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.count.congr_simp`：∀ {α : Type u_1} [inst : CommMonoidWithZero
 α] {inst_1 : DecidableEq (Associates α)}   [inst_2 : DecidableEq (Associates α)
] {inst_3 : (p : …
· 使用定理 `Associates.factors_subsingleton`：factors_subsingleton [Subsingleton α] {
a : Associates α} : a.factors = ⊤
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Associates.instNoZeroDivisors`：∀ {M : Type u_1} [inst : CommMonoidWithZe
ro M] [IsCancelMulZero M], NoZeroDivisors (Associates M)
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `Associates.eq_of_eq_counts`：eq_of_eq_counts {a b : Associates α} (ha : a
 != 0) (hb : b != 0) (h : forall p : Associates α, Irreducible p -> p.count a.fa
ctors = p.count …
· 使用定理 `Nat.eq_zero_of_le_zero`：∀ {n : ℕ}, n ≤ 0 → n = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.count_pow`：count_pow [Nontrivial α] {a : Associates α} (ha : 
a != 0) {p : Associates α} (hp : Irreducible p) (k : Nat) : count p (a ^ k).fact
ors = k * …
· 使用定理 `Associates.count_eq_zero_of_ne`：count_eq_zero_of_ne {p q : Associates α}
 (hp : Irreducible p) (hq : Irreducible q) (h : p != q) : p.count q.factors = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Associates.count_le_count_of_le`：count_le_count_of_le {a b p : Associate
s α} (hb : b != 0) (hp : Irreducible p) (h : a <= b) : p.count a.factors <= p.co
unt b.factors
· 使用定理 `Associates.count_self`：count_self [Nontrivial α] {p : Associates α} (hp 
: Irreducible p) : p.count p.factors = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
The only divisors of prime powers are prime powers. See `eq_pow_find_of_dvd_irre
ducible_pow`
for an explicit expression as a p-power (without using `count`).
-/
theorem eq_pow_count_factors_of_dvd_pow {p a : Associates α}
    (hp : Irreducible p) {n : ℕ} (h : a ∣ p ^ n) : a = p ^ p.count a.factors := by
  nontriviality α
  have hph := pow_ne_zero n hp.ne_zero
  have ha := ne_zero_of_dvd_ne_zero hph h
  apply eq_of_eq_counts ha (pow_ne_zero _ hp.ne_zero)
  have eq_zero_of_ne : ∀ q : Associates α, Irreducible q → q ≠ p → _ = 0 := fun q hq h' =>
    Nat.eq_zero_of_le_zero <| by
      convert! count_le_count_of_le hph hq h
      symm
      rw [count_pow hp.ne_zero hq, count_eq_zero_of_ne hq hp h', mul_zero]
  intro q hq
  rw [count_pow hp.ne_zero hq]
  by_cases h : q = p
  · rw [h, count_self hp, mul_one]
  · rw [count_eq_zero_of_ne hq hp h, mul_zero, eq_zero_of_ne q hq h]
/-
**Associates.count_factors_eq_find_of_dvd_pow** 是 Mathlib 中的一个定理，位于命名空间 `Associa
tes`。
形式化陈述：count_factors_eq_find_of_dvd_pow {a p : Associates α} (hp : Irreducible p)
 [forall n : Nat, Decidable (a ∣ p ^ n)] {n : Nat} (h : a ∣ p ^ n) : @Nat.find (
fun n => a ∣ p ^ n) _ ⟨n, h⟩ = p.count a.factors
参数：hp : Irreducible p；a ∣ p ^ n；h : a ∣ p ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Nat.find_le`：find_le {h : exists n, p n} (hn : p n) : Nat.find h <= n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.eq_pow_count_factors_of_dvd_pow`：eq_pow_count_factors_of_dvd_
pow {p a : Associates α} (hp : Irreducible p) {n : Nat} (h : a ∣ p ^ n) : a = p 
^ p.count a.factors
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Associates.instNoZeroDivisors`：∀ {M : Type u_1} [inst : CommMonoidWithZe
ro M] [IsCancelMulZero M], NoZeroDivisors (Associates M)
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.find.congr_simp`：∀ {p p_1 : ℕ → Prop} (e_p : p = p_1) {inst : Decida
blePred p} [inst_1 : DecidablePred p_1] (H : ∃ n, p n),   Nat.find H = Nat.find 
⋯
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Associates.count_pow`：count_pow [Nontrivial α] {a : Associates α} (ha : 
a != 0) {p : Associates α} (hp : Irreducible p) (k : Nat) : count p (a ^ k).fact
ors = k * …
· 使用定理 `Associates.count_self`：count_self [Nontrivial α] {p : Associates α} (hp 
: Irreducible p) : p.count p.factors = 1
· 使用定理 `Associates.count_le_count_of_le`：count_le_count_of_le {a b p : Associate
s α} (hb : b != 0) (hp : Irreducible p) (h : a <= b) : p.count a.factors <= p.co
unt b.factors
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
theorem count_factors_eq_find_of_dvd_pow {a p : Associates α}
    (hp : Irreducible p) [∀ n : ℕ, Decidable (a ∣ p ^ n)] {n : ℕ} (h : a ∣ p ^ n) :
    @Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩ = p.count a.factors := by
  apply le_antisymm
  · refine Nat.find_le ⟨1, ?_⟩
    rw [mul_one]
    symm
    exact eq_pow_count_factors_of_dvd_pow hp h
  · have hph := pow_ne_zero (@Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩) hp.ne_zero
    rcases subsingleton_or_nontrivial α with hα | hα
    · simp [eq_iff_true_of_subsingleton] at hph
    convert! count_le_count_of_le hph hp (@Nat.find_spec (fun n => a ∣ p ^ n) _ ⟨n, h⟩)
    rw [count_pow hp.ne_zero hp, count_self hp, mul_one]

end count

/-
**Associates.eq_pow_of_mul_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `Associates`。
形式化陈述：eq_pow_of_mul_eq_pow {a b c : Associates α} (ha : a != 0) (hb : b != 0) (h
ab : forall d, d ∣ a -> d ∣ b -> ¬Prime d) {k : Nat} (h : a * b = c ^ k) : exist
s d : Associates α, a = d ^ k
参数：ha : a != 0；hb : b != 0；hab : forall d, d ∣ a -> d ∣ b -> ¬Prime d；h : a * b 
= c ^ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_one`：mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Associates.is_pow_of_dvd_count`：is_pow_of_dvd_count {a : Associates α} (
ha : a != 0) {k : Nat} (hk : forall p : Associates α, Irreducible p -> k ∣ count
 p a.factors) : exis…
· 使用定理 `Associates.dvd_count_of_dvd_count_mul`：dvd_count_of_dvd_count_mul {a b :
 Associates α} (hb : b != 0) {p : Associates α} (hp : Irreducible p) (hab : fora
ll d, d ∣ a -> d ∣ b -> ¬Pr…
· 使用定理 `Associates.dvd_count_pow`：dvd_count_pow [Nontrivial α] {a : Associates α
} (ha : a != 0) {p : Associates α} (hp : Irreducible p) (k : Nat) : k ∣ count p 
(a ^ k).factor…
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `Associates.instNoZeroDivisors`：∀ {M : Type u_1} [inst : CommMonoidWithZe
ro M] [IsCancelMulZero M], NoZeroDivisors (Associates M)
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_pow_of_mul_eq_pow {a b c : Associates α} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) {k : ℕ} (h : a * b = c ^ k) :
    ∃ d : Associates α, a = d ^ k := by
  classical
  nontriviality α
  by_cases hk0 : k = 0
  · use 1
    rw [hk0, pow_zero] at h ⊢
    apply (mul_eq_one.1 h).1
  · refine is_pow_of_dvd_count ha fun p hp ↦ ?_
    apply dvd_count_of_dvd_count_mul hb hp hab
    rw [h]
    apply dvd_count_pow _ hp
    rintro rfl
    rw [zero_pow hk0] at h
    cases mul_eq_zero.mp h <;> contradiction

/-- The only divisors of prime powers are prime powers. -/
/-
**Associates.eq_pow_find_of_dvd_irreducible_pow** 是 Mathlib 中的一个定理，位于命名空间 `Assoc
iates`。
形式化陈述：eq_pow_find_of_dvd_irreducible_pow {a p : Associates α} (hp : Irreducible 
p) [forall n : Nat, Decidable (a ∣ p ^ n)] {n : Nat} (h : a ∣ p ^ n) : a = p ^ @
Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩
参数：hp : Irreducible p；a ∣ p ^ n；h : a ∣ p ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.count_factors_eq_find_of_dvd_pow`：count_factors_eq_find_of_dv
d_pow {a p : Associates α} (hp : Irreducible p) [forall n : Nat, Decidable (a ∣ 
p ^ n)] {n : Nat} (h : a ∣ p ^ n)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.eq_pow_count_factors_of_dvd_pow`：eq_pow_count_factors_of_dvd_
pow {p a : Associates α} (hp : Irreducible p) {n : Nat} (h : a ∣ p ^ n) : a = p 
^ p.count a.factors

--- 原说明 ---
The only divisors of prime powers are prime powers.
-/
theorem eq_pow_find_of_dvd_irreducible_pow {a p : Associates α} (hp : Irreducible p)
    [∀ n : ℕ, Decidable (a ∣ p ^ n)] {n : ℕ} (h : a ∣ p ^ n) :
    a = p ^ @Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩ := by
  classical rw [count_factors_eq_find_of_dvd_pow hp, ← eq_pow_count_factors_of_dvd_pow hp h]
  exact h

end Associates

