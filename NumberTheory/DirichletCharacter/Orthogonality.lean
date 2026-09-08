/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.MulChar.Duality

/-!
# Orthogonality relations for Dirichlet characters

Let `n` be a positive natural number. The main result of this file is
`DirichletCharacter.sum_char_inv_mul_char_eq`, which says that when `a : ZMod n` is a unit
and `b : ZMod n`, then the sum `∑ χ : DirichletCharacter R n, χ a⁻¹ * χ b` vanishes
when `a ≠ b` and has the value `n.totient` otherwise. This requires `R` to have
enough roots of unity (e.g., `R` could be an algebraically closed field of characteristic zero).
-/

public section

namespace DirichletCharacter

-- This is needed to be able to write down sums over characters.
/-
**DirichletCharacter.fintype** 是 Mathlib 中的一个实例，位于命名空间 `DirichletCharacter`。
形式化陈述：fintype {R : Type*} [CommRing R] [IsDomain R] {n : Nat} : Fintype (Dirichl
etCharacter R n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance fintype {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} :
    Fintype (DirichletCharacter R n) := .ofFinite _

variable (R : Type*) [CommRing R] (n : ℕ) [NeZero n]
  [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]

/-- The group of Dirichlet characters mod `n` with values in a ring `R` that has enough
roots of unity is (noncanonically) isomorphic to `(ZMod n)ˣ`. -/
/-
**DirichletCharacter.mulEquiv_units** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharacte
r`。
形式化陈述：mulEquiv_units : Nonempty (DirichletCharacter R n ≃* (ZMod n)ˣ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulChar.mulEquiv_units`：mulEquiv_units : Nonempty (MulChar M R ≃* Mˣ)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The group of Dirichlet characters mod `n` with values in a ring `R` that has eno
ugh
roots of unity is (noncanonically) isomorphic to `(ZMod n)ˣ`.
-/
lemma mulEquiv_units : Nonempty (DirichletCharacter R n ≃* (ZMod n)ˣ) :=
  MulChar.mulEquiv_units ..

/-- There are `n.totient` Dirichlet characters mod `n` with values in a ring that has enough
roots of unity. -/
/-
**DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity** 是 Mathlib 中的一个引理
，位于命名空间 `DirichletCharacter`。
形式化陈述：card_eq_totient_of_hasEnoughRootsOfUnity : Nat.card (DirichletCharacter R 
n) = n.totient
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.card_units_eq_totient`：∀ (n : ℕ) [NeZero n] [inst : Fintype (ZMod n
)ˣ], Fintype.card (ZMod n)ˣ = n.totient
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用引理 `DirichletCharacter.mulEquiv_units`：mulEquiv_units : Nonempty (DirichletC
haracter R n ≃* (ZMod n)ˣ)

--- 原说明 ---
There are `n.totient` Dirichlet characters mod `n` with values in a ring that ha
s enough
roots of unity.
-/
lemma card_eq_totient_of_hasEnoughRootsOfUnity :
    Nat.card (DirichletCharacter R n) = n.totient := by
  rw [← ZMod.card_units_eq_totient n, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (mulEquiv_units R n).some.toEquiv

variable {n}

/-- If `R` is a ring that has enough roots of unity and `n ≠ 0`, then for each
`a ≠ 1` in `ZMod n`, there exists a Dirichlet character `χ` mod `n` with values in `R`
such that `χ a ≠ 1`. -/
/-
**DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity** 是 Mathlib 中的
一个定理，位于命名空间 `DirichletCharacter`。
形式化陈述：exists_apply_ne_one_of_hasEnoughRootsOfUnity [Nontrivial R] ⦃a : ZMod n⦄ (
ha : a != 1) : exists χ : DirichletCharacter R n, χ a != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity`：exists_apply_ne_on
e_of_hasEnoughRootsOfUnity [Nontrivial R] {a : M} (ha : a != 1) : exists χ : Mul
Char M R, χ a != 1
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `R` is a ring that has enough roots of unity and `n ≠ 0`, then for each
`a ≠ 1` in `ZMod n`, there exists a Dirichlet character `χ` mod `n` with values 
in `R`
such that `χ a ≠ 1`.
-/
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity [Nontrivial R] ⦃a : ZMod n⦄ (ha : a ≠ 1) :
    ∃ χ : DirichletCharacter R n, χ a ≠ 1 :=
  MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod n) R ha

variable [IsDomain R]

/-- If `R` is an integral domain that has enough roots of unity and `n ≠ 0`, then
for each `a ≠ 1` in `ZMod n`, the sum of `χ a` over all Dirichlet characters mod `n`
with values in `R` vanishes. -/
/-
**DirichletCharacter.sum_characters_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Dirichlet
Character`。
形式化陈述：sum_characters_eq_zero ⦃a : ZMod n⦄ (ha : a != 1) : ∑ χ : DirichletCharact
er R n, χ a = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity`：exists_
apply_ne_one_of_hasEnoughRootsOfUnity [Nontrivial R] ⦃a : ZMod n⦄ (ha : a != 1) 
: exists χ : DirichletCharacter R n, χ a != 1
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `eq_zero_of_mul_eq_self_left`：eq_zero_of_mul_eq_self_left [IsRightCancelM
ulZero M₀] (h₁ : b != 1) (h₂ : b * a = a) : a = 0
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Fintype.sum_bijective`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [i
nst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι → κ), 
Function.Bi…
· 使用定理 `Group.mulLeft_bijective`：∀ {G : Type u_5} [inst : Group G] (a : G), Func
tion.Bijective fun x => a * x

--- 原说明 ---
If `R` is an integral domain that has enough roots of unity and `n ≠ 0`, then
for each `a ≠ 1` in `ZMod n`, the sum of `χ a` over all Dirichlet characters mod
 `n`
with values in `R` vanishes.
-/
theorem sum_characters_eq_zero ⦃a : ZMod n⦄ (ha : a ≠ 1) :
    ∑ χ : DirichletCharacter R n, χ a = 0 := by
  obtain ⟨χ, hχ⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity R ha
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' ↦ rfl

/-- If `R` is an integral domain that has enough roots of unity and `n ≠ 0`, then
for `a` in `ZMod n`, the sum of `χ a` over all Dirichlet characters mod `n`
with values in `R` vanishes if `a ≠ 1` and has the value `n.totient` if `a = 1`. -/
/-
**DirichletCharacter.sum_characters_eq** 是 Mathlib 中的一个定理，位于命名空间 `DirichletChara
cter`。
形式化陈述：sum_characters_eq (a : ZMod n) : ∑ χ : DirichletCharacter R n, χ a = if a 
= 1 then (n.totient : R) else 0
参数：a : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity`：card_eq_tot
ient_of_hasEnoughRootsOfUnity : Nat.card (DirichletCharacter R n) = n.totient
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `DirichletCharacter.sum_characters_eq_zero`：sum_characters_eq_zero ⦃a : Z
Mod n⦄ (ha : a != 1) : ∑ χ : DirichletCharacter R n, χ a = 0

--- 原说明 ---
If `R` is an integral domain that has enough roots of unity and `n ≠ 0`, then
for `a` in `ZMod n`, the sum of `χ a` over all Dirichlet characters mod `n`
with values in `R` vanishes if `a ≠ 1` and has the value `n.totient` if `a = 1`.
-/
theorem sum_characters_eq (a : ZMod n) :
    ∑ χ : DirichletCharacter R n, χ a = if a = 1 then (n.totient : R) else 0 := by
  split_ifs with ha
  · simpa only [ha, map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card]
      using congrArg Nat.cast <| card_eq_totient_of_hasEnoughRootsOfUnity R n
  · exact sum_characters_eq_zero R ha

/-- If `R` is an integral domain that has enough roots of unity and `n ≠ 0`, then for `a` and `b`
in `ZMod n` with `a` a unit, the sum of `χ a⁻¹ * χ b` over all Dirichlet characters
mod `n` with values in `R` vanishes if `a ≠ b` and has the value `n.totient` if `a = b`. -/
/-
**DirichletCharacter.sum_char_inv_mul_char_eq** 是 Mathlib 中的一个定理，位于命名空间 `Dirichl
etCharacter`。
形式化陈述：sum_char_inv_mul_char_eq {a : ZMod n} (ha : IsUnit a) (b : ZMod n) : ∑ χ :
 DirichletCharacter R n, χ a⁻¹ * χ b = if a = b then (n.totient : R) else 0
参数：ha : IsUnit a；b : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `DirichletCharacter.sum_characters_eq`：sum_characters_eq (a : ZMod n) : ∑
 χ : DirichletCharacter R n, χ a = if a = 1 then (n.totient : R) else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `ZMod.inv_mul_eq_one_of_isUnit`：inv_mul_eq_one_of_isUnit {n : Nat} {a : Z
Mod n} (ha : IsUnit a) (b : ZMod n) : a⁻¹ * b = 1 ↔ a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `R` is an integral domain that has enough roots of unity and `n ≠ 0`, then fo
r `a` and `b`
in `ZMod n` with `a` a unit, the sum of `χ a⁻¹ * χ b` over all Dirichlet charact
ers
mod `n` with values in `R` vanishes if `a ≠ b` and has the value `n.totient` if 
`a = b`.
-/
theorem sum_char_inv_mul_char_eq {a : ZMod n} (ha : IsUnit a) (b : ZMod n) :
    ∑ χ : DirichletCharacter R n, χ a⁻¹ * χ b = if a = b then (n.totient : R) else 0 := by
  simp only [← map_mul, sum_characters_eq, ZMod.inv_mul_eq_one_of_isUnit ha]

end DirichletCharacter

