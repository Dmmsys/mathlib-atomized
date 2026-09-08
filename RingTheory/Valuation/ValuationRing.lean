/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.RingTheory.Bezout
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Valuation Rings

A valuation ring is a domain such that for every pair of elements `a b`, either `a` divides
`b` or vice-versa.

Any valuation ring induces a natural valuation on its fraction field, as we show in this file.
Namely, given the following instances:
`[CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]`,
there is a natural valuation `Valuation A K` on `K` with values in `value_group A K` where
the image of `A` under `algebraMap A K` agrees with `(Valuation A K).integer`.

We also provide the equivalence of the following notions for a domain `R` in `ValuationRing.TFAE`.
1. `R` is a valuation ring.
2. For each `x : FractionRing K`, either `x` or `x⁻¹` is in `R`.
3. "divides" is a total relation on the elements of `R`.
4. "contains" is a total relation on the ideals of `R`.
5. `R` is a local bezout domain.

We also show that, given a valuation `v` on a field `K`, the ring of valuation integers is a
valuation ring and `K` is the fraction field of this ring.

## Implementation details

The Mathlib definition of a valuation ring requires `IsDomain A` even though the condition
does not mention zero divisors. Thus, there is a technical `PreValuationRing A` that
is defined in further generality that can be used in places where the ring cannot be a domain.
The `ValuationRing` class is kept to be in sync with the literature.

-/

@[expose] public section

assert_not_exists IsDiscreteValuationRing

universe u v w

/-- A magma is called a `PreValuationRing` provided that for any pair
of elements `a b : A`, either `a` divides `b` or vice versa. -/
/-
**PreValuationRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u) → [Mul A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A magma is called a `PreValuationRing` provided that for any pair
of elements `a b : A`, either `a` divides `b` or vice versa.
-/
class PreValuationRing (A : Type u) [Mul A] : Prop where
  cond' : ∀ a b : A, ∃ c : A, a * c = b ∨ b * c = a
/-
**PreValuationRing.cond** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PreValuationRing.cond {A : Type u} [Mul A] [PreValuationRing A] (a b : A) 
: exists c : A, a * c = b ∨ b * c = a
参数：a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PreValuationRing.cond'`：∀ {A : Type u} {inst : Mul A} [self : PreValuati
onRing A] (a b : A), ∃ c, a * c = b ∨ b * c = a
-/
lemma PreValuationRing.cond {A : Type u} [Mul A] [PreValuationRing A] (a b : A) :
    ∃ c : A, a * c = b ∨ b * c = a := @PreValuationRing.cond' A _ _ _ _

/-- An integral domain is called a `ValuationRing` provided that for any pair
of elements `a b : A`, either `a` divides `b` or vice versa. -/
/-
**ValuationRing** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：ValuationRing (A : Type u) [CommRing A] [IsDomain A] : Prop extends PreVal
uationRing A  /-- An abbreviation for `PreValuationRing.cond` which should save 
some writing. -/ alias ValuationRing.cond
参数：A : Type u。
继承自：PreValuationRing A  /-- An abbreviation for `PreValuationRing.cond` which sh
ould save some writing. -/ alias ValuationRing.cond。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An integral domain is called a `ValuationRing` provided that for any pair
of elements `a b : A`, either `a` divides `b` or vice versa.
-/
class ValuationRing (A : Type u) [CommRing A] [IsDomain A] : Prop extends PreValuationRing A

/-- An abbreviation for `PreValuationRing.cond` which should save some writing. -/
alias ValuationRing.cond := PreValuationRing.cond

namespace ValuationRing

section

variable (A : Type u) [CommRing A]
variable (K : Type v) [Field K] [Algebra A K]

/-- The value group of the valuation ring `A`. Note: this is actually a group with zero. -/
/-
**ValuationRing.ValueGroup** 是 Mathlib 中的一个定义，位于命名空间 `ValuationRing`。
形式化陈述：ValueGroup : Type v
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The value group of the valuation ring `A`. Note: this is actually a group with z
ero.
-/
def ValueGroup : Type v := Quotient (MulAction.orbitRel Aˣ K)
/-
**ValuationRing.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (ValueGroup A K) := ⟨Quotient.mk'' 0⟩
/-
**ValuationRing.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (ValueGroup A K) :=
  LE.mk fun x y =>
    Quotient.liftOn₂' x y (fun a b => ∃ c : A, c • b = a)
      (by
        rintro _ _ a b ⟨c, rfl⟩ ⟨d, rfl⟩; ext
        constructor
        · rintro ⟨e, he⟩; use (c⁻¹ : Aˣ) * e * d
          apply_fun fun t => c⁻¹ • t at he
          simpa [mul_smul] using! he
        · rintro ⟨e, he⟩; dsimp
          use c * e * (d⁻¹ : Aˣ)
          simp_rw [Units.smul_def, ← he, mul_smul]
          rw [← mul_smul _ _ b, Units.inv_mul, one_smul])
/-
**ValuationRing.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (ValueGroup A K) := ⟨Quotient.mk'' 0⟩
/-
**ValuationRing.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (ValueGroup A K) := ⟨Quotient.mk'' 1⟩
/-
**ValuationRing.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (ValueGroup A K) :=
  Mul.mk fun x y =>
    Quotient.liftOn₂' x y (fun a b => Quotient.mk'' <| a * b)
      (by
        rintro _ _ a b ⟨c, rfl⟩ ⟨d, rfl⟩
        apply Quotient.sound'
        dsimp
        use c * d
        simp only [mul_smul, Algebra.smul_def, Units.smul_def]
        ring)
/-
**ValuationRing.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (ValueGroup A K) :=
  Inv.mk fun x =>
    Quotient.liftOn' x (fun a => Quotient.mk'' a⁻¹)
      (by
        rintro _ a ⟨b, rfl⟩
        apply Quotient.sound'
        use b⁻¹
        dsimp
        rw [Units.smul_def, Units.smul_def, Algebra.smul_def, Algebra.smul_def, mul_inv,
          map_units_inv])
/-
**ValuationRing.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nontrivial (ValueGroup A K) where
  exists_pair_ne := ⟨0, 1, fun c => by
    obtain ⟨d, hd⟩ := Quotient.exact' c
    apply_fun fun t => d⁻¹ • t at hd
    dsimp at hd
    simp only [inv_smul_smul, smul_zero, one_ne_zero] at hd⟩

variable [IsDomain A] [ValuationRing A] [IsFractionRing A K]
/-
**ValuationRing.le_total** 是 Mathlib 中的一个定理，位于命名空间 `ValuationRing`。
形式化陈述：∀ (A : Type u) [inst : CommRing A] (K : Type v) [inst_1 : Field K] [inst_2
 : Algebra A K] [inst_3 : IsDomain A]   [ValuationRing A] [IsFractionRing A K] (
a b : ValuationRing.ValueGroup A K), a ≤ b ∨ b ≤ a
参数：A : Type u；K : Type v；a b : ValuationRing.ValueGroup A K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors`：∀ {R : Type u_1} [
inst : CommRing R] {K : Type u_5} [inst_1 : CommRing K] [inst_2 : Algebra R K] [
IsFractionRing R K]   [Nontrivial R] {x : …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `ValuationRing.cond`：∀ {A : Type u} [inst : Mul A] [PreValuationRing A] (
a b : A), ∃ c, a * c = b ∨ b * c = a
· 使用定理 `ValuationRing.toPreValuationRing`：∀ {A : Type u} {inst : CommRing A} {in
st_1 : IsDomain A} [self : ValuationRing A], PreValuationRing A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_ne_zero`：cons_ne_zero [GroupWithZero M]
 (r : Int) {x : M} (hx : x != 0) {l : NF M} (hl : l.eval != 0) : ((r, x) ::ᵣ l).
eval != 0
（共 74 条，此处仅展示前 30 条）
-/
protected theorem le_total (a b : ValueGroup A K) : a ≤ b ∨ b ≤ a := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  obtain ⟨xa, ya, hya, rfl⟩ := IsFractionRing.div_surjective A a
  obtain ⟨xb, yb, hyb, rfl⟩ := IsFractionRing.div_surjective A b
  have : (algebraMap A K) ya ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
  have : (algebraMap A K) yb ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hyb
  obtain ⟨c, h | h⟩ := ValuationRing.cond (xa * yb) (xb * ya)
  · right
    use c
    rw [Algebra.smul_def]
    field_simp
    simp only [← map_mul]; congr 1; linear_combination h
  · left
    use c
    rw [Algebra.smul_def]
    field_simp
    simp only [← map_mul]; congr 1; linear_combination h

set_option backward.isDefEq.respectTransparency false in
/-
**ValuationRing.linearOrder** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRing`。
形式化陈述：linearOrder : LinearOrder (ValueGroup A K) where le_refl
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationRing.le_total`：∀ (A : Type u) [inst : CommRing A] (K : Type v) 
[inst_1 : Field K] [inst_2 : Algebra A K] [inst_3 : IsDomain A]   [ValuationRing
 A] [IsFract…
-/
noncomputable instance linearOrder : LinearOrder (ValueGroup A K) where
  le_refl := by rintro ⟨⟩; use 1; rw [one_smul]
  le_trans := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨e, rfl⟩ ⟨f, rfl⟩; use e * f; rw [mul_smul]
  le_antisymm := by
    rintro ⟨a⟩ ⟨b⟩ ⟨e, rfl⟩ ⟨f, hf⟩
    by_cases hb : b = 0; · simp [hb]
    have : IsUnit e := by
      apply isUnit_of_dvd_one
      use f
      rw [mul_comm]
      rw [← mul_smul, Algebra.smul_def] at hf
      nth_rw 2 [← one_mul b] at hf
      rw [← (algebraMap A K).map_one] at hf
      exact IsFractionRing.injective _ _ (mul_right_cancel₀ hb hf).symm
    apply Quotient.sound'
    exact ⟨this.unit, rfl⟩
  le_total := ValuationRing.le_total _ _
  toDecidableLE := Classical.decRel _
/-
**ValuationRing.commGroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRing`。
形式化陈述：commGroupWithZero : CommGroupWithZero (ValueGroup A K)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationRing.instNontrivialValueGroup`：∀ (A : Type u) [inst : CommRing 
A] (K : Type v) [inst_1 : Field K] [inst_2 : Algebra A K],   Nontrivial (Valuati
onRing.ValueGroup A K)
-/
instance commGroupWithZero :
    CommGroupWithZero (ValueGroup A K) :=
  { mul_assoc := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; apply Quotient.sound'; rw [mul_assoc]
    one_mul := by rintro ⟨a⟩; apply Quotient.sound'; rw [one_mul]
    mul_one := by rintro ⟨a⟩; apply Quotient.sound'; rw [mul_one]
    mul_comm := by rintro ⟨a⟩ ⟨b⟩; apply Quotient.sound'; rw [mul_comm]
    zero_mul := by rintro ⟨a⟩; apply Quotient.sound'; rw [zero_mul]
    mul_zero := by rintro ⟨a⟩; apply Quotient.sound'; rw [mul_zero]
    inv_zero := by apply Quotient.sound'; rw [inv_zero]
    mul_inv_cancel := by
      rintro ⟨a⟩ ha
      apply Quotient.sound'
      use 1
      simp only [one_smul]
      apply (mul_inv_cancel₀ _).symm
      contrapose ha
      rw [ha]
      rfl }
/-
**ValuationRing.linearOrderedCommGroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Valuat
ionRing`。
形式化陈述：linearOrderedCommGroupWithZero : LinearOrderedCommGroupWithZero (ValueGrou
p A K) where bot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance linearOrderedCommGroupWithZero :
    LinearOrderedCommGroupWithZero (ValueGroup A K) where
  bot := 0
  bot_le := by rintro ⟨a⟩; exact ⟨0, zero_smul ..⟩
  isBot_zero := by rintro ⟨a⟩; exact ⟨0, zero_smul ..⟩
  mul_lt_mul_of_pos_left := by
    simp_rw [← not_le]
    rintro ⟨a⟩ ha ⟨b⟩ ⟨c⟩ hbc
    contrapose hbc
    obtain ⟨d, hd⟩ := hbc
    simp only [Algebra.smul_def, mul_left_comm, mul_eq_mul_left_iff] at hd
    obtain rfl | rfl := hd
    · exact ⟨d, by simp [Algebra.smul_def]⟩
    · cases ha le_rfl

/-- Any valuation ring induces a valuation on its fraction field. -/
/-
**ValuationRing.valuation** 是 Mathlib 中的一个定义，位于命名空间 `ValuationRing`。
形式化陈述：valuation : Valuation K (ValueGroup A K) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
Any valuation ring induces a valuation on its fraction field.
-/
noncomputable def valuation : Valuation K (ValueGroup A K) where
  toFun := Quotient.mk''
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add_le_max' := by
    intro a b
    obtain ⟨xa, ya, hya, rfl⟩ := IsFractionRing.div_surjective A a
    obtain ⟨xb, yb, hyb, rfl⟩ := IsFractionRing.div_surjective A b
    have : (algebraMap A K) ya ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    have : (algebraMap A K) yb ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hyb
    obtain ⟨c, h | h⟩ := ValuationRing.cond (xa * yb) (xb * ya)
    · apply le_trans _ (le_max_left _ _)
      use c + 1
      rw [Algebra.smul_def]
      field_simp
      simp only [← map_mul, ← map_add]
      congr 1; linear_combination h
    · apply le_trans _ (le_max_right _ _)
      use c + 1
      rw [Algebra.smul_def]
      field_simp
      simp only [← map_mul, ← map_add]
      congr 1; linear_combination h
/-
**ValuationRing.mem_integer_iff** 是 Mathlib 中的一个定理，位于命名空间 `ValuationRing`。
形式化陈述：mem_integer_iff (x : K) : x in (valuation A K).integer ↔ exists a : A, alg
ebraMap A K a = x
参数：x : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mem_integer_iff (x : K) : x ∈ (valuation A K).integer ↔ ∃ a : A, algebraMap A K a = x := by
  constructor
  · rintro ⟨c, rfl⟩
    use c
    rw [Algebra.smul_def, mul_one]
  · rintro ⟨c, rfl⟩
    use c
    rw [Algebra.smul_def, mul_one]

/-- The valuation ring `A` is isomorphic to the ring of integers of its associated valuation. -/
/-
**ValuationRing.equivInteger** 是 Mathlib 中的一个定义，位于命名空间 `ValuationRing`。
形式化陈述：equivInteger : A ≃+* (valuation A K).integer
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valuation ring `A` is isomorphic to the ring of integers of its associated v
aluation.
-/
noncomputable def equivInteger : A ≃+* (valuation A K).integer :=
  RingEquiv.ofBijective
    (show A →ₙ+* (valuation A K).integer from
      { toFun := fun a => ⟨algebraMap A K a, (mem_integer_iff _ _ _).mpr ⟨a, rfl⟩⟩
        map_mul' := fun _ _ => by ext1; exact (algebraMap A K).map_mul _ _
        map_zero' := by ext1; exact (algebraMap A K).map_zero
        map_add' := fun _ _ => by ext1; exact (algebraMap A K).map_add _ _ })
    (by
      constructor
      · intro x y h
        apply_fun (algebraMap (valuation A K).integer K) at h
        exact IsFractionRing.injective _ _ h
      · rintro ⟨-, ha⟩
        rw [mem_integer_iff] at ha
        obtain ⟨a, rfl⟩ := ha
        exact ⟨a, rfl⟩)

@[simp]
/-
**ValuationRing.coe_equivInteger_apply** 是 Mathlib 中的一个定理，位于命名空间 `ValuationRing`
。
形式化陈述：coe_equivInteger_apply (a : A) : (equivInteger A K a : K) = algebraMap A K
 a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem coe_equivInteger_apply (a : A) : (equivInteger A K a : K) = algebraMap A K a := rfl
/-
**ValuationRing.range_algebraMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `ValuationRing`。
形式化陈述：range_algebraMap_eq : (valuation A K).integer = (algebraMap A K).range
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.ext`：ext {S T : Subring R} (h : forall x, x in S ↔ x in T) : S =
 T
· 使用定理 `ValuationRing.mem_integer_iff`：mem_integer_iff (x : K) : x in (valuation
 A K).integer ↔ exists a : A, algebraMap A K a = x
-/
theorem range_algebraMap_eq : (valuation A K).integer = (algebraMap A K).range := by
  ext; exact mem_integer_iff _ _ _

end

section

variable (A : Type u) [CommRing A] [Nontrivial A] [PreValuationRing A]

/-
**ValuationRing.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isLocalRing : IsLocalRing A :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a ↦ by
    obtain ⟨c, h | h⟩ := PreValuationRing.cond a (1 - a)
    · left
      refine .of_mul_eq_one (c + 1) ?_
      simp [mul_add, h]
    · right
      refine .of_mul_eq_one (c + 1) ?_
      simp [mul_add, h]
/-
**ValuationRing.le_total_ideal** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRing`。
形式化陈述：le_total_ideal : @Std.Total (Ideal A) (· <= ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `PreValuationRing.cond`：PreValuationRing.cond {A : Type u} [Mul A] [PreVa
luationRing A] (a b : A) : exists c : A, a * c = b ∨ b * c = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
instance le_total_ideal : @Std.Total (Ideal A) (· ≤ ·) := by
  constructor; intro α β
  by_cases! h : ∀ x : A, x ∈ α → x ∈ β
  · exact Or.inl h
  obtain ⟨a, h₁, h₂⟩ := h
  right
  intro b hb
  obtain ⟨c, h | h⟩ := PreValuationRing.cond a b
  · rw [← h]
    exact Ideal.mul_mem_right _ _ h₁
  · exfalso; apply h₂; rw [← h]
    apply Ideal.mul_mem_right _ _ hb

open scoped Classical in
/- Todo: get rid of the `DecidableLE` argument.
Currently, this argument causes this instance to not be called often,
which hides a loop in simp-lemmas. See
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/conflicting.20simp-normal.20form.3A.20bot.20vs.200/with/566807522 -/
/-
**ValuationRing.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Todo: get rid of the `DecidableLE` argument.
Currently, this argument causes this instance to not be called often,
which hides a loop in simp-lemmas. See
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/conflicti
ng.20simp-normal.20form.3A.20bot.20vs.200/with/566807522
-/
noncomputable instance [DecidableLE (Ideal A)] : LinearOrder (Ideal A) :=
  Lattice.toLinearOrder (Ideal A)

end

section

section dvd

variable {R : Type*}

/-
**ValuationRing._root_.PreValuationRing.iff_dvd_total** 是 Mathlib 中的一个定理，位于命名空间 
`ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.PreValuationRing.iff_dvd_total [Semigroup R] :
    PreValuationRing R ↔ @Std.Total R (· ∣ ·) := by
  refine ⟨fun H => ⟨fun a b => ?_⟩, fun H => ⟨fun a b => ?_⟩⟩
  · obtain ⟨c, rfl | rfl⟩ := PreValuationRing.cond a b <;> simp
  · obtain ⟨c, rfl⟩ | ⟨c, rfl⟩ := H.total a b <;> use c <;> simp
/-
**ValuationRing._root_.PreValuationRing.iff_ideal_total** 是 Mathlib 中的一个定理，位于命名空
间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.PreValuationRing.iff_ideal_total [CommRing R] :
    PreValuationRing R ↔ @Std.Total (Ideal R) (· ≤ ·) := by
  classical
  refine ⟨fun _ => ⟨le_total⟩, fun H => PreValuationRing.iff_dvd_total.mpr ⟨fun a b => ?_⟩⟩
  have := H.total (Ideal.span {a}) (Ideal.span {b})
  simp_rw [Ideal.span_singleton_le_span_singleton] at this
  exact this.symm

variable (K)
/-
**ValuationRing.dvd_total** 是 Mathlib 中的一个定理，位于命名空间 `ValuationRing`。
形式化陈述：dvd_total [Semigroup R] [h : PreValuationRing R] (x y : R) : x ∣ y ∨ y ∣ x
参数：x y : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Total.total`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Total r] 
(a b : α), r a b ∨ r b a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PreValuationRing.iff_dvd_total`：∀ {R : Type u_1} [inst : Semigroup R], P
reValuationRing R ↔ Std.Total fun x1 x2 => x1 ∣ x2
-/
theorem dvd_total [Semigroup R] [h : PreValuationRing R] (x y : R) : x ∣ y ∨ y ∣ x :=
  (PreValuationRing.iff_dvd_total.mp h).total x y

end dvd

variable {R : Type*} [CommRing R] [IsDomain R] (K : Type*)
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-
**ValuationRing.iff_dvd_total** 是 Mathlib 中的一个定理，位于命名空间 `ValuationRing`。
形式化陈述：iff_dvd_total : ValuationRing R ↔ @Std.Total R (· ∣ ·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ValuationRing.toPreValuationRing`：∀ {A : Type u} {inst : CommRing A} {in
st_1 : IsDomain A} [self : ValuationRing A], PreValuationRing A
· 使用定理 `PreValuationRing.iff_dvd_total`：∀ {R : Type u_1} [inst : Semigroup R], P
reValuationRing R ↔ Std.Total fun x1 x2 => x1 ∣ x2
-/
theorem iff_dvd_total : ValuationRing R ↔ @Std.Total R (· ∣ ·) :=
  Iff.trans (⟨fun inst ↦ inst.toPreValuationRing, fun _ ↦ .mk⟩)
    PreValuationRing.iff_dvd_total
/-
**ValuationRing.iff_ideal_total** 是 Mathlib 中的一个定理，位于命名空间 `ValuationRing`。
形式化陈述：iff_ideal_total : ValuationRing R ↔ @Std.Total (Ideal R) (· <= ·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ValuationRing.toPreValuationRing`：∀ {A : Type u} {inst : CommRing A} {in
st_1 : IsDomain A} [self : ValuationRing A], PreValuationRing A
· 使用定理 `PreValuationRing.iff_ideal_total`：∀ {R : Type u_1} [inst : CommRing R], 
PreValuationRing R ↔ Std.Total fun x1 x2 => x1 ≤ x2
-/
theorem iff_ideal_total : ValuationRing R ↔ @Std.Total (Ideal R) (· ≤ ·) :=
  Iff.trans (⟨fun inst ↦ inst.toPreValuationRing, fun _ ↦ .mk⟩)
    PreValuationRing.iff_ideal_total
/-
**ValuationRing.unique_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `ValuationRing`。
形式化陈述：unique_irreducible [PreValuationRing R] ⦃p q : R⦄ (hp : Irreducible p) (hq
 : Irreducible q) : Associated p q
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationRing.dvd_total`：dvd_total [Semigroup R] [h : PreValuationRing R
] (x y : R) : x ∣ y ∨ y ∣ x
· 使用定理 `associated_of_dvd_dvd`：associated_of_dvd_dvd [MonoidWithZero M] [IsLeftC
ancelMulZero M] {a b : M} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Irreducible.dvd_symm`：Irreducible.dvd_symm [Monoid M] {p q : M} (hp : Ir
reducible p) (hq : Irreducible q) : p ∣ q -> q ∣ p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_self_iff`：∀ {a : Prop}, a ∨ a ↔ a
· 使用定理 `Irreducible.dvd_comm`：Irreducible.dvd_comm [Monoid M] {p q : M} (hp : Ir
reducible p) (hq : Irreducible q) : p ∣ q ↔ q ∣ p
-/
theorem unique_irreducible [PreValuationRing R] ⦃p q : R⦄ (hp : Irreducible p)
    (hq : Irreducible q) : Associated p q := by
  have := dvd_total p q
  rw [Irreducible.dvd_comm hp hq, or_self_iff] at this
  exact associated_of_dvd_dvd (Irreducible.dvd_symm hq hp this) this

variable (R)
/-
**ValuationRing.iff_isInteger_or_isInteger** 是 Mathlib 中的一个定理，位于命名空间 `ValuationR
ing`。
形式化陈述：iff_isInteger_or_isInteger : ValuationRing R ↔ forall x : K, IsLocalizatio
n.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `ValuationRing.cond`：∀ {A : Type u} [inst : Mul A] [PreValuationRing A] (
a b : A), ∃ c, a * c = b ∨ b * c = a
· 使用定理 `ValuationRing.toPreValuationRing`：∀ {A : Type u} {inst : CommRing A} {in
st_1 : IsDomain A} [self : ValuationRing A], PreValuationRing A
· 使用定理 `eq_inv_of_mul_eq_one_left`：eq_inv_of_mul_eq_one_left (h : a * b = 1) : a
 = b⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_div`：mul_div (a b c : G) : a * (b / c) = a * b / c
· 使用引理 `div_eq_one_iff_eq`：div_eq_one_iff_eq (hb : b != 0) : a / b = 1 ↔ a = b
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
-/
theorem iff_isInteger_or_isInteger :
    ValuationRing R ↔ ∀ x : K, IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹ := by
  constructor
  · intro H x
    obtain ⟨x : R, y, hy, rfl⟩ := IsFractionRing.div_surjective R x
    have := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero hy)
    obtain ⟨s, rfl | rfl⟩ := ValuationRing.cond x y
    · exact Or.inr
        ⟨s, eq_inv_of_mul_eq_one_left <| by rwa [mul_div, div_eq_one_iff_eq, map_mul, mul_comm]⟩
    · exact Or.inl ⟨s, by rwa [eq_div_iff, map_mul, mul_comm]⟩
  · intro H
    suffices PreValuationRing R from mk
    constructor
    intro a b
    by_cases ha : a = 0; · subst ha; exact ⟨0, Or.inr <| mul_zero b⟩
    by_cases hb : b = 0; · subst hb; exact ⟨0, Or.inl <| mul_zero a⟩
    replace ha := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha
    replace hb := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb
    obtain ⟨c, e⟩ | ⟨c, e⟩ := H (algebraMap R K a / algebraMap R K b)
    · rw [eq_div_iff hb, ← map_mul, (IsFractionRing.injective R K).eq_iff, mul_comm] at e
      exact ⟨c, Or.inr e⟩
    · rw [inv_div, eq_div_iff ha, ← map_mul, (IsFractionRing.injective R K).eq_iff, mul_comm c] at e
      exact ⟨c, Or.inl e⟩

variable {K}
/-
**ValuationRing.isInteger_or_isInteger** 是 Mathlib 中的一个定理，位于命名空间 `ValuationRing`
。
形式化陈述：isInteger_or_isInteger [h : ValuationRing R] (x : K) : IsLocalization.IsIn
teger R x ∨ IsLocalization.IsInteger R x⁻¹
参数：x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ValuationRing.iff_isInteger_or_isInteger`：iff_isInteger_or_isInteger : V
aluationRing R ↔ forall x : K, IsLocalization.IsInteger R x ∨ IsLocalization.IsI
nteger R x⁻¹
-/
theorem isInteger_or_isInteger [h : ValuationRing R] (x : K) :
    IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹ :=
  (iff_isInteger_or_isInteger R K).mp h x

variable {R}

-- This implies that valuation rings are integrally closed through typeclass search.
/-
**ValuationRing.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [ValuationRing R] : IsBezout R := by
  classical
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro x y
  rw [Ideal.span_insert]
  rcases le_total (Ideal.span {x} : Ideal R) (Ideal.span {y}) with h | h
  · rw [sup_eq_right.mpr h]; exact ⟨⟨_, rfl⟩⟩
  · rw [sup_eq_left.mpr h]; exact ⟨⟨_, rfl⟩⟩
/-
**ValuationRing.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [IsLocalRing R] [IsBezout R] : ValuationRing R := by
  refine iff_dvd_total.mpr ⟨fun a b => ?_⟩
  obtain ⟨g, e : _ = Ideal.span _⟩ := IsBezout.span_pair_isPrincipal a b
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp
      (show a ∈ Ideal.span {g} by rw [← e]; exact Ideal.subset_span (by simp))
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp
      (show b ∈ Ideal.span {g} by rw [← e]; exact Ideal.subset_span (by simp))
  obtain ⟨x, y, e'⟩ := Ideal.mem_span_pair.mp
      (show g ∈ Ideal.span {a * g, b * g} by rw [e]; exact Ideal.subset_span (by simp))
  rcases eq_or_ne g 0 with h | h
  · simp [h]
  have : x * a + y * b = 1 := by
    apply mul_left_injective₀ h; convert! e' using 1 <;> ring
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one this with h' | h' <;> [left; right]
  all_goals exact mul_dvd_mul_right (isUnit_iff_forall_dvd.mp (isUnit_of_mul_isUnit_right h') _) _
/-
**ValuationRing.iff_local_bezout_domain** 是 Mathlib 中的一个定理，位于命名空间 `ValuationRing
`。
形式化陈述：iff_local_bezout_domain : ValuationRing R ↔ IsLocalRing R ∧ IsBezout R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationRing.isLocalRing`：∀ (A : Type u) [inst : CommRing A] [Nontrivia
l A] [PreValuationRing A], IsLocalRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `ValuationRing.toPreValuationRing`：∀ {A : Type u} {inst : CommRing A} {in
st_1 : IsDomain A} [self : ValuationRing A], PreValuationRing A
· 使用定理 `ValuationRing.instIsBezout`：∀ {R : Type u_1} [inst : CommRing R] [inst_1
 : IsDomain R] [ValuationRing R], IsBezout R
· 使用定理 `ValuationRing.instOfIsLocalRingOfIsBezout`：∀ {R : Type u_1} [inst : Comm
Ring R] [inst_1 : IsDomain R] [IsLocalRing R] [IsBezout R], ValuationRing R
-/
theorem iff_local_bezout_domain : ValuationRing R ↔ IsLocalRing R ∧ IsBezout R :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ inferInstance⟩
/-
**ValuationRing.TFAE** 是 Mathlib 中的一个定理，位于命名空间 `ValuationRing`。
形式化陈述：∀ (R : Type u) [inst : CommRing R] [inst_1 : IsDomain R],   [ValuationRing
 R, ∀ (x : FractionRing R), IsLocalization.IsInteger R x ∨ IsLocalization.IsInte
ger R x⁻¹,       Std.Total fun x1 x2 => x1 ∣ x2, Std.Total fun x1 x2 => x1 ≤ x2,
 IsLocalRing R ∧ IsBezout R].TFAE
参数：R : Type u；x : FractionRing R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `ValuationRing.iff_isInteger_or_isInteger`：iff_isInteger_or_isInteger : V
aluationRing R ↔ forall x : K, IsLocalization.IsInteger R x ∨ IsLocalization.IsI
nteger R x⁻¹
· 使用定理 `ValuationRing.iff_dvd_total`：iff_dvd_total : ValuationRing R ↔ @Std.Tota
l R (· ∣ ·)
· 使用定理 `ValuationRing.iff_ideal_total`：iff_ideal_total : ValuationRing R ↔ @Std.
Total (Ideal R) (· <= ·)
· 使用定理 `ValuationRing.iff_local_bezout_domain`：iff_local_bezout_domain : Valuati
onRing R ↔ IsLocalRing R ∧ IsBezout R
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
protected theorem TFAE (R : Type u) [CommRing R] [IsDomain R] :
    List.TFAE
      [ValuationRing R,
        ∀ x : FractionRing R, IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹,
        @Std.Total R (· ∣ ·), @Std.Total (Ideal R) (· ≤ ·), IsLocalRing R ∧ IsBezout R] := by
  tfae_have 1 ↔ 2 := iff_isInteger_or_isInteger R _
  tfae_have 1 ↔ 3 := iff_dvd_total
  tfae_have 1 ↔ 4 := iff_ideal_total
  tfae_have 1 ↔ 5 := iff_local_bezout_domain
  tfae_finish

end

/-
**ValuationRing._root_.Function.Surjective.preValuationRing** 是 Mathlib 中的一个定理，位
于命名空间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Surjective.preValuationRing {R S : Type*} [Mul R] [PreValuationRing R]
    [Mul S] (f : R →ₙ* S) (hf : Function.Surjective f) :
    PreValuationRing S :=
  ⟨fun a b => by
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hf a, hf b
    obtain ⟨c, rfl | rfl⟩ := PreValuationRing.cond a b
    exacts [⟨f c, Or.inl <| (map_mul _ _ _).symm⟩, ⟨f c, Or.inr <| (map_mul _ _ _).symm⟩]⟩
/-
**ValuationRing._root_.Function.Surjective.valuationRing** 是 Mathlib 中的一个定理，位于命名
空间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Surjective.valuationRing {R S : Type*} [NonAssocSemiring R]
    [PreValuationRing R] [CommRing S] [IsDomain S] (f : R →+* S) (hf : Function.Surjective f) :
    ValuationRing S :=
  have : PreValuationRing S := Function.Surjective.preValuationRing (R := R) f hf
  .mk

section

variable {𝒪 : Type u} {K : Type v} {Γ : Type w} [CommRing 𝒪] [Field K] [Algebra 𝒪 K]
  [LinearOrderedCommGroupWithZero Γ]

/-
**ValuationRing._root_.isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraM
ap_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective
    (h : ∀ (x : K), ∃ a : 𝒪, x = algebraMap 𝒪 K a ∨ x⁻¹ = algebraMap 𝒪 K a)
    (hinj : Function.Injective (algebraMap 𝒪 K)) :
    IsFractionRing 𝒪 K := by
  have : IsDomain 𝒪 := hinj.isDomain
  have := (faithfulSMul_iff_algebraMap_injective ..).2 hinj
  have := IsDomain.of_faithfulSMul 𝒪 K
  refine ⟨by simp, ?_, fun hab ↦ ⟨1, by simpa using hab⟩⟩
  intro x
  obtain ⟨a, ha⟩ := h x
  by_cases h0 : a = 0
  · refine ⟨⟨0, 1⟩, by simpa [h0, eq_comm] using ha⟩
  · have : algebraMap 𝒪 K a ≠ 0 := by simpa using h0
    rw [inv_eq_iff_eq_inv, ← one_div, eq_div_iff this] at ha
    cases ha with
    | inl ha => exact ⟨⟨a, 1⟩, by simpa⟩
    | inr ha => exact ⟨⟨1, ⟨a, mem_nonZeroDivisors_of_ne_zero h0⟩⟩, by simpa using ha⟩
/-
**ValuationRing._root_.Valuation.Integers.isFractionRing** 是 Mathlib 中的一个引理，位于命名
空间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Valuation.Integers.isFractionRing {v : Valuation K Γ} (hv : v.Integers 𝒪) :
    IsFractionRing 𝒪 K :=
  isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective
    hv.eq_algebraMap_or_inv_eq_algebraMap hv.hom_inj
/-
**ValuationRing.instIsFractionRingInteger** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRi
ng`。
形式化陈述：instIsFractionRingInteger (v : Valuation K Γ) : IsFractionRing v.integer K
参数：v : Valuation K Γ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.Integers.isFractionRing`：∀ {𝒪 : Type u} {K : Type v} {Γ : Type
 w} [inst : CommRing 𝒪] [inst_1 : Field K] [inst_2 : Algebra 𝒪 K]   [inst_3 : Li
nearOrderedCommGroupWit…
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
-/
instance instIsFractionRingInteger (v : Valuation K Γ) : IsFractionRing v.integer K :=
  (Valuation.integer.integers v).isFractionRing

/-- If `𝒪` satisfies `v.integers 𝒪` where `v` is a valuation on a field, then `𝒪`
is a valuation ring. -/
/-
**ValuationRing.of_integers** 是 Mathlib 中的一个定理，位于命名空间 `ValuationRing`。
形式化陈述：of_integers (v : Valuation K Γ) (hh : v.Integers 𝒪) : haveI
参数：v : Valuation K Γ；hh : v.Integers 𝒪。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Valuation.Integers.hom_inj`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O : Ty
pe w} [inst_2 : …
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Valuation.Integers.dvd_of_le`：dvd_of_le (hv : Integers v O) {x y : O} (h
 : v (algebraMap O F x) <= v (algebraMap O F y)) : y ∣ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `𝒪` satisfies `v.integers 𝒪` where `v` is a valuation on a field, then `𝒪`
is a valuation ring.
-/
theorem of_integers (v : Valuation K Γ) (hh : v.Integers 𝒪) :
    haveI := hh.hom_inj.isDomain
    ValuationRing 𝒪 := by
  have := hh.hom_inj.isDomain
  suffices PreValuationRing 𝒪 from .mk
  constructor
  intro a b
  rcases le_total (v (algebraMap 𝒪 K a)) (v (algebraMap 𝒪 K b)) with h | h
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hh h
    use c; exact Or.inr hc.symm
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hh h
    use c; exact Or.inl hc.symm
/-
**ValuationRing.instValuationRingInteger** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRin
g`。
形式化陈述：instValuationRingInteger (v : Valuation K Γ) : ValuationRing v.integer
参数：v : Valuation K Γ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationRing.of_integers`：of_integers (v : Valuation K Γ) (hh : v.Integ
ers 𝒪) : haveI
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
-/
instance instValuationRingInteger (v : Valuation K Γ) : ValuationRing v.integer :=
  of_integers (v := v) (Valuation.integer.integers v)
/-
**ValuationRing.isFractionRing_iff** 是 Mathlib 中的一个定理，位于命名空间 `ValuationRing`。
形式化陈述：isFractionRing_iff [IsDomain 𝒪] [ValuationRing 𝒪] : IsFractionRing 𝒪 K ↔ (
forall (x : K), exists a : 𝒪, x = algebraMap 𝒪 K a ∨ x⁻¹ = algebraMap 𝒪 K a) ∧ F
unction.Injective (algebraMap 𝒪 K)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationRing.isInteger_or_isInteger`：isInteger_or_isInteger [h : Valuat
ionRing R] (x : K) : IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x
⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective
`：∀ {𝒪 : Type u} {K : Type v} [inst : CommRing 𝒪] [inst_1 : Field K] [inst_2 : A
lgebra 𝒪 K],   (∀ (x : K), ∃ a, x = (algebraMap 𝒪 K) a ∨ x⁻¹ =…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isFractionRing_iff [IsDomain 𝒪] [ValuationRing 𝒪] :
    IsFractionRing 𝒪 K ↔
      (∀ (x : K), ∃ a : 𝒪, x = algebraMap 𝒪 K a ∨ x⁻¹ = algebraMap 𝒪 K a) ∧
        Function.Injective (algebraMap 𝒪 K) := by
  refine ⟨fun h ↦ ⟨fun x ↦ ?_, IsFractionRing.injective _ _⟩, fun h ↦ ?_⟩
  · obtain (⟨a, e⟩ | ⟨a, e⟩) := isInteger_or_isInteger 𝒪 x
    exacts [⟨a, .inl e.symm⟩, ⟨a, .inr e.symm⟩]
  · exact isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective h.1 h.2

end

section

variable (K : Type u) [Field K]

/-- A field is a valuation ring. -/
/-
**ValuationRing.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A field is a valuation ring.
-/
instance (priority := 100) of_field : ValuationRing K := inferInstance

end

end ValuationRing

