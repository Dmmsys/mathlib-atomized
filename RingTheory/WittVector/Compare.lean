/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.RingTheory.WittVector.Truncated
public import Mathlib.RingTheory.WittVector.Identities
public import Mathlib.NumberTheory.Padics.RingHoms

/-!

# Comparison isomorphism between `WittVector p (ZMod p)` and `ℤ_[p]`

We construct a ring isomorphism between `WittVector p (ZMod p)` and `ℤ_[p]`.
This isomorphism follows from the fact that both satisfy the universal property
of the inverse limit of `ZMod (p^n)`.

## Main declarations

* `WittVector.toZModPow`: a family of compatible ring homs `𝕎 (ZMod p) → ZMod (p^k)`
* `WittVector.equiv`: the isomorphism

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

@[expose] public section


noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

namespace TruncatedWittVector

variable (p) (n : ℕ) (R : Type*) [CommRing R]

/-
**TruncatedWittVector.eq_of_le_of_cast_pow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Tr
uncatedWittVector`。
形式化陈述：eq_of_le_of_cast_pow_eq_zero [CharP R p] (i : Nat) (hin : i <= n) (hpi : (
p : TruncatedWittVector p n R) ^ i = 0) : i = n
参数：i : Nat；hin : i <= n；hpi : (p : TruncatedWittVector p n R) ^ i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `TruncatedWittVector.ext_iff`：∀ {p n : ℕ} {R : Type u_1} {x y : Truncated
WittVector p n R},   x = y ↔ ∀ (i : Fin n), TruncatedWittVector.coeff i x = Trun
catedWittVector.c…
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `WittVector.coeff_truncate`：coeff_truncate (x : 𝕎 R) (i : Fin n) : (trunc
ate n x).coeff i = x.coeff i
· 使用定理 `TruncatedWittVector.coeff_zero`：coeff_zero (i : Fin n) : (0 : TruncatedW
ittVector p n R).coeff i = 0
· 使用定理 `Fin.val_mk`：∀ {m n : ℕ} (h : m < n), ↑⟨m, h⟩ = m
· 使用定理 `WittVector.coeff_p_pow`：coeff_p_pow [CharP R p] (i : Nat) : ((p : 𝕎 R) ^
 i).coeff i = 1
· 使用引理 `CharP.nontrivial_of_char_ne_one`：nontrivial_of_char_ne_one {v : Nat} (hv
 : v != 1) [hr : CharP R v] : Nontrivial R
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem eq_of_le_of_cast_pow_eq_zero [CharP R p] (i : ℕ) (hin : i ≤ n)
    (hpi : (p : TruncatedWittVector p n R) ^ i = 0) : i = n := by
  contrapose! hpi
  replace hin := lt_of_le_of_ne hin hpi; clear hpi
  have : (p : TruncatedWittVector p n R) ^ i = WittVector.truncate n ((p : 𝕎 R) ^ i) := by
    rw [map_pow, map_natCast]
  rw [this, ne_eq, TruncatedWittVector.ext_iff, not_forall]; clear this
  use ⟨i, hin⟩
  rw [WittVector.coeff_truncate, coeff_zero, Fin.val_mk, WittVector.coeff_p_pow]
  have : Nontrivial R := CharP.nontrivial_of_char_ne_one hp.1.ne_one
  exact one_ne_zero

section Iso

variable {R}

/-
**TruncatedWittVector.card_zmod** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWittVector`。
形式化陈述：card_zmod : Fintype.card (TruncatedWittVector p n (ZMod p)) = p ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TruncatedWittVector.card`：card {R : Type*} [Fintype R] : Fintype.card (T
runcatedWittVector p n R) = Fintype.card R ^ n
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
-/
theorem card_zmod : Fintype.card (TruncatedWittVector p n (ZMod p)) = p ^ n := by
  rw [card, ZMod.card]
/-
**TruncatedWittVector.charP_zmod** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWittVector`
。
形式化陈述：charP_zmod : CharP (TruncatedWittVector p n (ZMod p)) (p ^ n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `charP_of_prime_pow_injective`：charP_of_prime_pow_injective (R) [Ring R] 
[Fintype R] (p n : Nat) [hp : Fact p.Prime] (hn : card R = p ^ n) (hR : forall i
 <= n, (p : R) ^ i…
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `TruncatedWittVector.card_zmod`：card_zmod : Fintype.card (TruncatedWittVe
ctor p n (ZMod p)) = p ^ n
· 使用定理 `TruncatedWittVector.eq_of_le_of_cast_pow_eq_zero`：eq_of_le_of_cast_pow_e
q_zero [CharP R p] (i : Nat) (hin : i <= n) (hpi : (p : TruncatedWittVector p n 
R) ^ i = 0) : i = n
-/
theorem charP_zmod : CharP (TruncatedWittVector p n (ZMod p)) (p ^ n) :=
  charP_of_prime_pow_injective _ _ _ (card_zmod _ _) (eq_of_le_of_cast_pow_eq_zero p n (ZMod p))

attribute [local instance] charP_zmod

/-- The unique isomorphism between `ZMod p^n` and `TruncatedWittVector p n (ZMod p)`.

This isomorphism exists, because `TruncatedWittVector p n (ZMod p)` is a finite ring
with characteristic and cardinality `p^n`.
-/
/-
**TruncatedWittVector.zmodEquivTrunc** 是 Mathlib 中的一个定义，位于命名空间 `TruncatedWittVec
tor`。
形式化陈述：zmodEquivTrunc : ZMod (p ^ n) ≃+* TruncatedWittVector p n (ZMod p)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TruncatedWittVector.charP_zmod`：charP_zmod : CharP (TruncatedWittVector 
p n (ZMod p)) (p ^ n)
· 使用定理 `TruncatedWittVector.card_zmod`：card_zmod : Fintype.card (TruncatedWittVe
ctor p n (ZMod p)) = p ^ n

--- 原说明 ---
The unique isomorphism between `ZMod p^n` and `TruncatedWittVector p n (ZMod p)`
.

This isomorphism exists, because `TruncatedWittVector p n (ZMod p)` is a finite 
ring
with characteristic and cardinality `p^n`.
-/
def zmodEquivTrunc : ZMod (p ^ n) ≃+* TruncatedWittVector p n (ZMod p) :=
  ZMod.ringEquiv (TruncatedWittVector p n (ZMod p)) (card_zmod _ _)
/-
**TruncatedWittVector.zmodEquivTrunc_apply** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedW
ittVector`。
形式化陈述：zmodEquivTrunc_apply {x : ZMod (p ^ n)} : zmodEquivTrunc p n x = ZMod.cast
Hom (m
参数：p ^ n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zmodEquivTrunc_apply {x : ZMod (p ^ n)} :
    zmodEquivTrunc p n x =
      ZMod.castHom (m := p ^ n) (by rfl) (TruncatedWittVector p n (ZMod p)) x :=
  rfl

/-- The following diagram commutes:
```text
          ZMod (p^n) ----------------------------> ZMod (p^m)
            |                                        |
            |                                        |
            v                                        v
TruncatedWittVector p n (ZMod p) ----> TruncatedWittVector p m (ZMod p)
```
Here the vertical arrows are `TruncatedWittVector.zmodEquivTrunc`,
the horizontal arrow at the top is `ZMod.castHom`,
and the horizontal arrow at the bottom is `TruncatedWittVector.truncate`.
-/
/-
**TruncatedWittVector.commutes** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWittVector`。
形式化陈述：commutes {m : Nat} (hm : n <= m) : (truncate hm).comp (zmodEquivTrunc p m)
.toRingHom = (zmodEquivTrunc p n).toRingHom.comp (ZMod.castHom (pow_dvd_pow p hm
) _)
参数：hm : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext_zmod`：RingHom.ext_zmod {n : Nat} {R : Type*} [NonAssocSemiri
ng R] (f g : ZMod n ->+* R) : f = g
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n

--- 原说明 ---
The following diagram commutes:
```text
          ZMod (p^n) ----------------------------> ZMod (p^m)
            |                                        |
            |                                        |
            v                                        v
TruncatedWittVector p n (ZMod p) ----> TruncatedWittVector p m (ZMod p)
```
Here the vertical arrows are `TruncatedWittVector.zmodEquivTrunc`,
the horizontal arrow at the top is `ZMod.castHom`,
and the horizontal arrow at the bottom is `TruncatedWittVector.truncate`.
-/
theorem commutes {m : ℕ} (hm : n ≤ m) :
    (truncate hm).comp (zmodEquivTrunc p m).toRingHom =
      (zmodEquivTrunc p n).toRingHom.comp (ZMod.castHom (pow_dvd_pow p hm) _) :=
  RingHom.ext_zmod _ _
/-
**TruncatedWittVector.commutes'** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWittVector`。
形式化陈述：commutes' {m : Nat} (hm : n <= m) (x : ZMod (p ^ m)) : truncate hm (zmodEq
uivTrunc p m x) = zmodEquivTrunc p n (ZMod.castHom (pow_dvd_pow p hm) _ x)
参数：hm : n <= m；x : ZMod (p ^ m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TruncatedWittVector.commutes`：commutes {m : Nat} (hm : n <= m) : (trunca
te hm).comp (zmodEquivTrunc p m).toRingHom = (zmodEquivTrunc p n).toRingHom.comp
 (ZMod.castHom (po…
-/
theorem commutes' {m : ℕ} (hm : n ≤ m) (x : ZMod (p ^ m)) :
    truncate hm (zmodEquivTrunc p m x) = zmodEquivTrunc p n (ZMod.castHom (pow_dvd_pow p hm) _ x) :=
  show (truncate hm).comp (zmodEquivTrunc p m).toRingHom x = _ by rw [commutes _ _ hm]; rfl
/-
**TruncatedWittVector.commutes_symm'** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWittVec
tor`。
形式化陈述：commutes_symm' {m : Nat} (hm : n <= m) (x : TruncatedWittVector p m (ZMod 
p)) : (zmodEquivTrunc p n).symm (truncate hm x) = ZMod.castHom (pow_dvd_pow p hm
) _ ((zmodEquivTrunc p m).symm x)
参数：hm : n <= m；x : TruncatedWittVector p m (ZMod p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TruncatedWittVector.commutes'`：commutes' {m : Nat} (hm : n <= m) (x : ZM
od (p ^ m)) : truncate hm (zmodEquivTrunc p m x) = zmodEquivTrunc p n (ZMod.cast
Hom (pow_dvd_pow p …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem commutes_symm' {m : ℕ} (hm : n ≤ m) (x : TruncatedWittVector p m (ZMod p)) :
    (zmodEquivTrunc p n).symm (truncate hm x) =
      ZMod.castHom (pow_dvd_pow p hm) _ ((zmodEquivTrunc p m).symm x) := by
  apply (zmodEquivTrunc p n).injective
  rw [← commutes' _ _ hm]
  simp

/-- The following diagram commutes:
```text
TruncatedWittVector p n (ZMod p) ----> TruncatedWittVector p m (ZMod p)
            |                                        |
            |                                        |
            v                                        v
          ZMod (p^n) ----------------------------> ZMod (p^m)
```
Here the vertical arrows are `(TruncatedWittVector.zmodEquivTrunc p _).symm`,
the horizontal arrow at the top is `ZMod.castHom`,
and the horizontal arrow at the bottom is `TruncatedWittVector.truncate`.
-/
/-
**TruncatedWittVector.commutes_symm** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWittVect
or`。
形式化陈述：commutes_symm {m : Nat} (hm : n <= m) : (zmodEquivTrunc p n).symm.toRingHo
m.comp (truncate hm) = (ZMod.castHom (pow_dvd_pow p hm) _).comp (zmodEquivTrunc 
p m).symm.toRingHom
参数：hm : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `TruncatedWittVector.commutes_symm'`：commutes_symm' {m : Nat} (hm : n <= 
m) (x : TruncatedWittVector p m (ZMod p)) : (zmodEquivTrunc p n).symm (truncate 
hm x) = ZMod.castHom (po…

--- 原说明 ---
The following diagram commutes:
```text
TruncatedWittVector p n (ZMod p) ----> TruncatedWittVector p m (ZMod p)
            |                                        |
            |                                        |
            v                                        v
          ZMod (p^n) ----------------------------> ZMod (p^m)
```
Here the vertical arrows are `(TruncatedWittVector.zmodEquivTrunc p _).symm`,
the horizontal arrow at the top is `ZMod.castHom`,
and the horizontal arrow at the bottom is `TruncatedWittVector.truncate`.
-/
theorem commutes_symm {m : ℕ} (hm : n ≤ m) :
    (zmodEquivTrunc p n).symm.toRingHom.comp (truncate hm) =
      (ZMod.castHom (pow_dvd_pow p hm) _).comp (zmodEquivTrunc p m).symm.toRingHom := by
  ext; apply commutes_symm'

end Iso

end TruncatedWittVector

namespace WittVector

open TruncatedWittVector

variable (p)

/-- `toZModPow` is a family of compatible ring homs. We get this family by composing
`TruncatedWittVector.zmodEquivTrunc` (in right-to-left direction) with `WittVector.truncate`. -/
/-
**WittVector.toZModPow** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：toZModPow (k : Nat) : 𝕎 (ZMod p) ->+* ZMod (p ^ k)
参数：k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toZModPow` is a family of compatible ring homs. We get this family by composing
`TruncatedWittVector.zmodEquivTrunc` (in right-to-left direction) with `WittVect
or.truncate`.
-/
def toZModPow (k : ℕ) : 𝕎 (ZMod p) →+* ZMod (p ^ k) :=
  (zmodEquivTrunc p k).symm.toRingHom.comp (truncate k)
/-
**WittVector.toZModPow_compat** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：toZModPow_compat (m n : Nat) (h : m <= n) : (ZMod.castHom (pow_dvd_pow p h
) (ZMod (p ^ m))).comp (toZModPow p n) = toZModPow p m
参数：m n : Nat；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TruncatedWittVector.commutes_symm`：commutes_symm {m : Nat} (hm : n <= m)
 : (zmodEquivTrunc p n).symm.toRingHom.comp (truncate hm) = (ZMod.castHom (pow_d
vd_pow p hm) _).comp (z…
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `TruncatedWittVector.truncate_comp_wittVector_truncate`：truncate_comp_wit
tVector_truncate {m : Nat} (hm : n <= m) : (truncate (p
-/
theorem toZModPow_compat (m n : ℕ) (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (toZModPow p n) = toZModPow p m :=
  calc
    (ZMod.castHom _ (ZMod (p ^ m))).comp ((zmodEquivTrunc p n).symm.toRingHom.comp (truncate n))
    _ = ((zmodEquivTrunc p m).symm.toRingHom.comp (TruncatedWittVector.truncate h)).comp
          (truncate n) := by
      rw [commutes_symm, RingHom.comp_assoc]
    _ = (zmodEquivTrunc p m).symm.toRingHom.comp (truncate m) := by
      rw [RingHom.comp_assoc, truncate_comp_wittVector_truncate]

/-- `toPadicInt` lifts `toZModPow : 𝕎 (ZMod p) →+* ZMod (p ^ k)` to a ring hom to `ℤ_[p]`
using `PadicInt.lift`, the universal property of `ℤ_[p]`.
-/
/-
**WittVector.toPadicInt** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：toPadicInt : 𝕎 (ZMod p) ->+* Int_[p]
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.toZModPow_compat`：toZModPow_compat (m n : Nat) (h : m <= n) :
 (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (toZModPow p n) = toZModPo
w p m

--- 原说明 ---
`toPadicInt` lifts `toZModPow : 𝕎 (ZMod p) →+* ZMod (p ^ k)` to a ring hom to `ℤ
_[p]`
using `PadicInt.lift`, the universal property of `ℤ_[p]`.
-/
def toPadicInt : 𝕎 (ZMod p) →+* ℤ_[p] :=
  PadicInt.lift <| toZModPow_compat p
/-
**WittVector.zmodEquivTrunc_compat** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：zmodEquivTrunc_compat (k₁ k₂ : Nat) (hk : k₁ <= k₂) : (TruncatedWittVector
.truncate hk).comp ((zmodEquivTrunc p k₂).toRingHom.comp (PadicInt.toZModPow k₂)
) = (zmodEquivTrunc p k₁).toRingHom.comp (PadicInt.toZModPow k₁)
参数：k₁ k₂ : Nat；hk : k₁ <= k₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `TruncatedWittVector.commutes`：commutes {m : Nat} (hm : n <= m) : (trunca
te hm).comp (zmodEquivTrunc p m).toRingHom = (zmodEquivTrunc p n).toRingHom.comp
 (ZMod.castHom (po…
· 使用定理 `PadicInt.zmod_cast_comp_toZModPow`：zmod_cast_comp_toZModPow (m n : Nat) 
(h : m <= n) : (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (@toZModPow 
p _ n) = @toZModPow p _…
-/
theorem zmodEquivTrunc_compat (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) :
    (TruncatedWittVector.truncate hk).comp
        ((zmodEquivTrunc p k₂).toRingHom.comp (PadicInt.toZModPow k₂)) =
      (zmodEquivTrunc p k₁).toRingHom.comp (PadicInt.toZModPow k₁) := by
  rw [← RingHom.comp_assoc, commutes, RingHom.comp_assoc,
    PadicInt.zmod_cast_comp_toZModPow _ _ hk]

/-- `fromPadicInt` uses `WittVector.lift` to lift `TruncatedWittVector.zmodEquivTrunc`
composed with `PadicInt.toZModPow` to a ring hom `ℤ_[p] →+* 𝕎 (ZMod p)`.
-/
/-
**WittVector.fromPadicInt** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：fromPadicInt : Int_[p] ->+* 𝕎 (ZMod p)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.zmodEquivTrunc_compat`：zmodEquivTrunc_compat (k₁ k₂ : Nat) (h
k : k₁ <= k₂) : (TruncatedWittVector.truncate hk).comp ((zmodEquivTrunc p k₂).to
RingHom.comp (PadicInt…

--- 原说明 ---
`fromPadicInt` uses `WittVector.lift` to lift `TruncatedWittVector.zmodEquivTrun
c`
composed with `PadicInt.toZModPow` to a ring hom `ℤ_[p] →+* 𝕎 (ZMod p)`.
-/
def fromPadicInt : ℤ_[p] →+* 𝕎 (ZMod p) :=
  (WittVector.lift fun k => (zmodEquivTrunc p k).toRingHom.comp (PadicInt.toZModPow k)) <|
    zmodEquivTrunc_compat _
/-
**WittVector.toPadicInt_comp_fromPadicInt** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`
。
形式化陈述：toPadicInt_comp_fromPadicInt : (toPadicInt p).comp (fromPadicInt p) = Ring
Hom.id Int_[p]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PadicInt.toZModPow_eq_iff_ext`：toZModPow_eq_iff_ext {R : Type*} [NonAsso
cSemiring R] {g g' : R ->+* Int_[p]} : (forall n, (toZModPow n).comp g = (toZMod
Pow n).comp g') ↔ g…
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `WittVector.toZModPow_compat`：toZModPow_compat (m n : Nat) (h : m <= n) :
 (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (toZModPow p n) = toZModPo
w p m
· 使用定理 `WittVector.toPadicInt.eq_1`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], WittVec
tor.toPadicInt p = PadicInt.lift ⋯
· 使用定理 `PadicInt.lift_spec`：lift_spec (n : Nat) : (toZModPow n).comp (lift f_com
pat) = f n
· 使用定理 `WittVector.zmodEquivTrunc_compat`：zmodEquivTrunc_compat (k₁ k₂ : Nat) (h
k : k₁ <= k₂) : (TruncatedWittVector.truncate hk).comp ((zmodEquivTrunc p k₂).to
RingHom.comp (PadicInt…
· 使用定理 `RingHom.comp_id`：comp_id (f : α ->+* β) : f.comp (id α) = f
· 使用定理 `WittVector.truncate_comp_lift`：truncate_comp_lift : (WittVector.truncate
 n).comp (lift _ f_compat) = f n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingEquiv.symm_toRingHom_comp_toRingHom`：symm_toRingHom_comp_toRingHom (
e : R ≃+* S) : e.symm.toRingHom.comp e.toRingHom = RingHom.id _
· 使用定理 `RingHom.id_comp`：id_comp (f : α ->+* β) : (id β).comp f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toPadicInt_comp_fromPadicInt : (toPadicInt p).comp (fromPadicInt p) = RingHom.id ℤ_[p] := by
  rw [← PadicInt.toZModPow_eq_iff_ext]
  intro n
  rw [← RingHom.comp_assoc, toPadicInt, PadicInt.lift_spec]
  simp only [fromPadicInt, toZModPow, RingHom.comp_id]
  rw [RingHom.comp_assoc, truncate_comp_lift, ← RingHom.comp_assoc]
  simp only [RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.id_comp]
/-
**WittVector.toPadicInt_comp_fromPadicInt_ext** 是 Mathlib 中的一个定理，位于命名空间 `WittVec
tor`。
形式化陈述：toPadicInt_comp_fromPadicInt_ext (x) : (toPadicInt p).comp (fromPadicInt p
) x = RingHom.id Int_[p] x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.toPadicInt_comp_fromPadicInt`：toPadicInt_comp_fromPadicInt : 
(toPadicInt p).comp (fromPadicInt p) = RingHom.id Int_[p]
-/
theorem toPadicInt_comp_fromPadicInt_ext (x) :
    (toPadicInt p).comp (fromPadicInt p) x = RingHom.id ℤ_[p] x := by
  rw [toPadicInt_comp_fromPadicInt]
/-
**WittVector.fromPadicInt_comp_toPadicInt** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`
。
形式化陈述：fromPadicInt_comp_toPadicInt : (fromPadicInt p).comp (toPadicInt p) = Ring
Hom.id (𝕎 (ZMod p))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.hom_ext`：hom_ext (g₁ g₂ : S ->+* 𝕎 R) (h : forall k, (truncat
e k).comp g₁ = (truncate k).comp g₂) : g₁ = g₂
· 使用定理 `WittVector.zmodEquivTrunc_compat`：zmodEquivTrunc_compat (k₁ k₂ : Nat) (h
k : k₁ <= k₂) : (TruncatedWittVector.truncate hk).comp ((zmodEquivTrunc p k₂).to
RingHom.comp (PadicInt…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.fromPadicInt.eq_1`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)],   Wit
tVector.fromPadicInt p =     WittVector.lift (fun k => (TruncatedWittVector.zmod
EquivTrunc p k).to…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `WittVector.truncate_comp_lift`：truncate_comp_lift : (WittVector.truncate
 n).comp (lift _ f_compat) = f n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PadicInt.lift_spec`：lift_spec (n : Nat) : (toZModPow n).comp (lift f_com
pat) = f n
· 使用定理 `WittVector.toZModPow_compat`：toZModPow_compat (m n : Nat) (h : m <= n) :
 (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (toZModPow p n) = toZModPo
w p m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingEquiv.toRingHom_comp_symm_toRingHom`：toRingHom_comp_symm_toRingHom (
e : R ≃+* S) : e.toRingHom.comp e.symm.toRingHom = RingHom.id _
· 使用定理 `RingHom.id_comp`：id_comp (f : α ->+* β) : (id β).comp f = f
· 使用定理 `RingHom.comp_id`：comp_id (f : α ->+* β) : f.comp (id α) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fromPadicInt_comp_toPadicInt :
    (fromPadicInt p).comp (toPadicInt p) = RingHom.id (𝕎 (ZMod p)) := by
  apply WittVector.hom_ext
  intro n
  rw [fromPadicInt, ← RingHom.comp_assoc, truncate_comp_lift, RingHom.comp_assoc]
  simp only [toPadicInt, toZModPow, RingHom.comp_id, PadicInt.lift_spec, RingHom.id_comp, ←
    RingHom.comp_assoc, RingEquiv.toRingHom_comp_symm_toRingHom]
/-
**WittVector.fromPadicInt_comp_toPadicInt_ext** 是 Mathlib 中的一个定理，位于命名空间 `WittVec
tor`。
形式化陈述：fromPadicInt_comp_toPadicInt_ext (x) : (fromPadicInt p).comp (toPadicInt p
) x = RingHom.id (𝕎 (ZMod p)) x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.fromPadicInt_comp_toPadicInt`：fromPadicInt_comp_toPadicInt : 
(fromPadicInt p).comp (toPadicInt p) = RingHom.id (𝕎 (ZMod p))
-/
theorem fromPadicInt_comp_toPadicInt_ext (x) :
    (fromPadicInt p).comp (toPadicInt p) x = RingHom.id (𝕎 (ZMod p)) x := by
  rw [fromPadicInt_comp_toPadicInt]

/-- The ring of Witt vectors over `ZMod p` is isomorphic to the ring of `p`-adic integers. This
equivalence is witnessed by `WittVector.toPadicInt` with inverse `WittVector.fromPadicInt`.
-/
/-
**WittVector.equiv** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：equiv : 𝕎 (ZMod p) ≃+* Int_[p] where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.fromPadicInt_comp_toPadicInt_ext`：fromPadicInt_comp_toPadicIn
t_ext (x) : (fromPadicInt p).comp (toPadicInt p) x = RingHom.id (𝕎 (ZMod p)) x
· 使用定理 `WittVector.toPadicInt_comp_fromPadicInt_ext`：toPadicInt_comp_fromPadicIn
t_ext (x) : (toPadicInt p).comp (fromPadicInt p) x = RingHom.id Int_[p] x

--- 原说明 ---
The ring of Witt vectors over `ZMod p` is isomorphic to the ring of `p`-adic int
egers. This
equivalence is witnessed by `WittVector.toPadicInt` with inverse `WittVector.fro
mPadicInt`.
-/
def equiv : 𝕎 (ZMod p) ≃+* ℤ_[p] where
  toFun := toPadicInt p
  invFun := fromPadicInt p
  left_inv := fromPadicInt_comp_toPadicInt_ext _
  right_inv := toPadicInt_comp_fromPadicInt_ext _
  map_mul' := map_mul _
  map_add' := map_add _

end WittVector

