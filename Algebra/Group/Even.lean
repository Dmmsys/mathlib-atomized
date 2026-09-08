/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.Set.Operations

/-!
# Squares and even elements

This file defines square and even elements in a monoid.

## Main declarations

* `IsSquare a` means that there is some `r` such that `a = r * r`
* `Even a` means that there is some `r` such that `a = r + r`

## Note

* Many lemmas about `Even` / `IsSquare`, including important `simp` lemmas,
  are in `Mathlib/Algebra/Ring/Parity.lean`.

## TODO

* Try to generalize `IsSquare/Even` lemmas further. For example, there are still a few lemmas in
  `Algebra.Ring.Parity` whose `Semiring` assumptions I (DT) am not convinced are necessary.
* The "old" definition of `Even a` asked for the existence of an element `c` such that `a = 2 * c`.
  For this reason, several fixes introduce an extra `two_mul` or `← two_mul`.
  It might be the case that by making a careful choice of `simp` lemma, this can be avoided.

## See also

`Mathlib/Algebra/Ring/Parity.lean` for the definition of odd elements as well as facts about
`Even` / `IsSquare` in rings.
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

open MulOpposite

variable {F α β : Type*}

section Mul
variable [Mul α]

/-- An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`,
for some root `r : α`. -/
@[to_additive /-- An element `a` of a type `α` with addition satisfies `Even a` if `a = r + r`,
for some `r : α`. -/]
/-
**IsSquare** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsSquare (a : α) : Prop
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsSquare (a : α) : Prop := ∃ r, a = r * r

@[to_additive]
/-
**isSquare_iff_exists_mul_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSquare_iff_exists_mul_self (a : α) : IsSquare a ↔ exists r, a = r * r
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isSquare_iff_exists_mul_self (a : α) : IsSquare a ↔ ∃ r, a = r * r := .rfl

alias ⟨IsSquare.exists_mul_self, _⟩ := isSquare_iff_exists_mul_self
attribute [to_additive (attr := aesop unsafe 5% forward)] IsSquare.exists_mul_self

@[to_additive (attr := simp, aesop safe)]
/-
**IsSquare.mul_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSquare.mul_self (r : α) : IsSquare (r * r)
参数：r : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsSquare.mul_self (r : α) : IsSquare (r * r) := ⟨r, rfl⟩

@[to_additive]
/-
**isSquare_op_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSquare_op_iff {a : α} : IsSquare (op a) ↔ IsSquare a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma isSquare_op_iff {a : α} : IsSquare (op a) ↔ IsSquare a :=
  ⟨fun ⟨r, hr⟩ ↦ ⟨unop r, congr_arg unop hr⟩, fun ⟨r, hr⟩ ↦ ⟨op r, congr_arg op hr⟩⟩

@[to_additive]
/-
**isSquare_unop_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSquare_unop_iff {a : αᵐᵒᵖ} : IsSquare (unop a) ↔ IsSquare a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `isSquare_op_iff`：isSquare_op_iff {a : α} : IsSquare (op a) ↔ IsSquare a
-/
lemma isSquare_unop_iff {a : αᵐᵒᵖ} : IsSquare (unop a) ↔ IsSquare a := isSquare_op_iff.symm

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidablePred (IsSquare : α → Prop)] : DecidablePred (IsSquare : αᵐᵒᵖ → Prop) :=
  fun _ ↦ decidable_of_iff _ isSquare_unop_iff

@[simp]
/-
**even_ofMul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：even_ofMul_iff {a : α} : Even (Additive.ofMul a) ↔ IsSquare a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma even_ofMul_iff {a : α} : Even (Additive.ofMul a) ↔ IsSquare a := Iff.rfl

@[simp]
/-
**isSquare_toMul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSquare_toMul_iff {a : Additive α} : IsSquare (a.toMul) ↔ Even a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isSquare_toMul_iff {a : Additive α} : IsSquare (a.toMul) ↔ Even a := Iff.rfl
/-
**Additive.instDecidablePredEven** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.instDecidablePredEven [DecidablePred (IsSquare : α -> Prop)] : De
cidablePred (Even : Additive α -> Prop)
参数：IsSquare : α -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `isSquare_toMul_iff`：isSquare_toMul_iff {a : Additive α} : IsSquare (a.to
Mul) ↔ Even a
-/
instance Additive.instDecidablePredEven [DecidablePred (IsSquare : α → Prop)] :
    DecidablePred (Even : Additive α → Prop) :=
  fun _ ↦ decidable_of_iff _ isSquare_toMul_iff

end Mul

section Add
variable [Add α]

/-
**isSquare_ofAdd_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : Add α] {a : α}, IsSquare (Multiplicative.ofAdd a)
 ↔ Even a
参数：Multiplicative.ofAdd a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma isSquare_ofAdd_iff {a : α} : IsSquare (Multiplicative.ofAdd a) ↔ Even a := Iff.rfl

@[simp]
/-
**even_toAdd_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：even_toAdd_iff {a : Multiplicative α} : Even a.toAdd ↔ IsSquare a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma even_toAdd_iff {a : Multiplicative α} : Even a.toAdd ↔ IsSquare a := Iff.rfl
/-
**Multiplicative.instDecidablePredIsSquare** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.instDecidablePredIsSquare [DecidablePred (Even : α -> Prop)
] : DecidablePred (IsSquare : Multiplicative α -> Prop)
参数：Even : α -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `even_toAdd_iff`：even_toAdd_iff {a : Multiplicative α} : Even a.toAdd ↔ I
sSquare a
-/
instance Multiplicative.instDecidablePredIsSquare [DecidablePred (Even : α → Prop)] :
    DecidablePred (IsSquare : Multiplicative α → Prop) :=
  fun _ ↦ decidable_of_iff _ even_toAdd_iff

end Add

@[to_additive (attr := simp)]
/-
**IsSquare.one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSquare.one [MulOneClass α] : IsSquare (1 : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma IsSquare.one [MulOneClass α] : IsSquare (1 : α) := ⟨1, (mul_one _).symm⟩

grind_pattern IsSquare.one => IsSquare (1 : α)
grind_pattern Even.zero => Even (0 : α)

section MonoidHom
variable [MulOneClass α] [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β]

@[to_additive (attr := aesop unsafe 90%)]
/-
**IsSquare.map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSquare.map {a : α} (f : F) : IsSquare a -> IsSquare (f a)
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsSquare.map {a : α} (f : F) : IsSquare a → IsSquare (f a) :=
  fun ⟨r, _⟩ => ⟨f r, by simp [*]⟩

@[to_additive]
/-
**isSquare_subset_image_isSquare** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSquare_subset_image_isSquare {f : F} (hf : Function.Surjective f) : {b |
 IsSquare b} subseteq f '' {a | IsSquare a}
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma isSquare_subset_image_isSquare {f : F} (hf : Function.Surjective f) :
    {b | IsSquare b} ⊆ f '' {a | IsSquare a} := fun b ⟨s, _⟩ => by
  rcases hf s with ⟨r, rfl⟩
  exact ⟨r * r, by simp [*]⟩

end MonoidHom

section Monoid
variable [Monoid α] {n : ℕ} {a : α}

@[to_additive even_iff_exists_two_nsmul]
/-
**isSquare_iff_exists_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSquare_iff_exists_sq (a : α) : IsSquare a ↔ exists r, a = r ^ 2
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isSquare_iff_exists_sq (a : α) : IsSquare a ↔ ∃ r, a = r ^ 2 := by simp [IsSquare, pow_two]

@[to_additive Even.exists_two_nsmul
  /-- Alias of the forwards direction of `even_iff_exists_two_nsmul`. -/]
alias ⟨IsSquare.exists_sq, _⟩ := isSquare_iff_exists_sq

-- provable by simp in `Algebra.Ring.Parity`
@[to_additive (attr := aesop safe) Even.two_nsmul]
/-
**IsSquare.sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSquare.sq (r : α) : IsSquare (r ^ 2)
参数：r : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
lemma IsSquare.sq (r : α) : IsSquare (r ^ 2) := ⟨r, pow_two _⟩

@[to_additive (attr := aesop unsafe 80%) Even.nsmul_right]
/-
**IsSquare.pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSquare.pow (n : Nat) (ha : IsSquare a) : IsSquare (a ^ n)
参数：n : Nat；ha : IsSquare a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSquare.exists_mul_self`：∀ {α : Type u_2} [inst : Mul α] (a : α), IsSqu
are a → ∃ r, a = r * r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsSquare.pow (n : ℕ) (ha : IsSquare a) : IsSquare (a ^ n) := by
  aesop (add simp Commute.mul_pow)

@[to_additive (attr := aesop unsafe 90%) Even.nsmul_left]
/-
**Even.isSquare_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Even.isSquare_pow (hn : Even n) : forall a : α, IsSquare (a ^ n)
参数：hn : Even n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Even.exists_add_self`：∀ {α : Type u_2} [inst : Add α] (a : α), Even a → 
∃ r, a = r + r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Even.isSquare_pow (hn : Even n) : ∀ a : α, IsSquare (a ^ n) := by aesop (add simp pow_add)

end Monoid

@[to_additive (attr := aesop unsafe 90%)]
/-
**IsSquare.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSquare.mul [CommSemigroup α] {a b : α} : IsSquare a -> IsSquare b -> IsS
quare (a * b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsSquare.mul [CommSemigroup α] {a b : α} : IsSquare a → IsSquare b → IsSquare (a * b) :=
  fun ⟨r, _⟩ ⟨s, _⟩ => ⟨r * s, by simp_all [mul_mul_mul_comm]⟩

section DivisionMonoid
variable [DivisionMonoid α] {a : α}

/-
**isSquare_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : DivisionMonoid α] {a : α}, IsSquare a⁻¹ ↔ IsSquar
e a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MulEquiv.inv'_symm_apply`：∀ (G : Type u_3) [inst : DivisionMonoid G], ⇑(
MulEquiv.inv' G).symm = Inv.inv ∘ MulOpposite.unop
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `IsSquare.map`：IsSquare.map {a : α} (f : F) : IsSquare a -> IsSquare (f a
)
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isSquare_op_iff`：isSquare_op_iff {a : α} : IsSquare (op a) ↔ IsSquare a
-/
@[to_additive (attr := simp)] lemma isSquare_inv : IsSquare a⁻¹ ↔ IsSquare a := by
  constructor <;> intro h <;> simpa using (isSquare_op_iff.mpr h).map (MulEquiv.inv' α).symm

@[to_additive] alias ⟨_, IsSquare.inv⟩ := isSquare_inv

@[to_additive (attr := aesop unsafe 80%) Even.zsmul_right]
/-
**IsSquare.zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSquare.zpow (n : Int) : IsSquare a -> IsSquare (a ^ n)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSquare.exists_mul_self`：∀ {α : Type u_2} [inst : Mul α] (a : α), IsSqu
are a → ∃ r, a = r * r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.mul_zpow`：∀ {G : Type u_1} [inst : DivisionMonoid G] {a b : G}, 
Commute a b → ∀ (n : ℤ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsSquare.zpow (n : ℤ) : IsSquare a → IsSquare (a ^ n) := by
  aesop (add simp Commute.mul_zpow)

end DivisionMonoid

@[to_additive (attr := aesop unsafe 90%)]
/-
**IsSquare.div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSquare.div [DivisionCommMonoid α] {a b : α} (ha : IsSquare a) (hb : IsSq
uare b) : IsSquare (a / b)
参数：ha : IsSquare a；hb : IsSquare b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `IsSquare.mul`：IsSquare.mul [CommSemigroup α] {a b : α} : IsSquare a -> I
sSquare b -> IsSquare (a * b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma IsSquare.div [DivisionCommMonoid α] {a b : α} (ha : IsSquare a) (hb : IsSquare b) :
    IsSquare (a / b) := by aesop (add simp div_eq_mul_inv)

@[to_additive (attr := simp, aesop unsafe 90%) Even.zsmul_left]
/-
**Even.isSquare_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Even.isSquare_zpow [Group α] {n : Int} : Even n -> forall a : α, IsSquare 
(a ^ n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Even.exists_add_self`：∀ {α : Type u_2} [inst : Add α] (a : α), Even a → 
∃ r, a = r + r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Even.isSquare_zpow [Group α] {n : ℤ} : Even n → ∀ a : α, IsSquare (a ^ n) := by
  aesop (add simp zpow_add)
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {G : Type*} [CommGroup G] {a b c d e : G} (ha : IsSquare a) {n : ℕ} {k : ℤ} (hk : Even k) :
    IsSquare <| a * (b * b) / (c ^ 2) * (d ^ k) * (e ^ (n + n)) := by aesop
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {G : Type*} [AddCommGroup G] {a b c d e : G} (ha : Even a) {n : ℕ} {k : ℤ} (hk : Even k) :
    Even <| a + (b + b) - 2 • c + k • d + (n + n) • e := by aesop
