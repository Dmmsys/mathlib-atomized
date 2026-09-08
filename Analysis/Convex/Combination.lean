/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Convex combinations

This file defines convex combinations of points in a vector space.

## Main declarations

* `Finset.centerMass`: Center of mass of a finite family of points.

## Implementation notes

We divide by the sum of the weights in the definition of `Finset.centerMass` because of the way
mathematical arguments go: one doesn't change weights, but merely adds some. This also makes a few
lemmas unconditional on the sum of the weights being `1`.
-/

@[expose] public section

assert_not_exists Cardinal

open Set Function Pointwise

universe u u'

section
variable {R R' E F ι ι' α : Type*} [Field R] [Field R'] [AddCommGroup E] [AddCommGroup F]
  [AddCommGroup α] [LinearOrder α] [Module R E] [Module R F] [Module R α] {s : Set E}

/-- Center of mass of a finite collection of points with prescribed weights.
Note that we require neither `0 ≤ w i` nor `∑ w = 1`. -/
/-
**Finset.centerMass** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Finset.centerMass (t : Finset ι) (w : ι -> R) (z : ι -> E) : E
参数：t : Finset ι；w : ι -> R；z : ι -> E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Center of mass of a finite collection of points with prescribed weights.
Note that we require neither `0 ≤ w i` nor `∑ w = 1`.
-/
def Finset.centerMass (t : Finset ι) (w : ι → R) (z : ι → E) : E :=
  (∑ i ∈ t, w i)⁻¹ • ∑ i ∈ t, w i • z i

variable (i j : ι) (c : R) (t : Finset ι) (w : ι → R) (z : ι → E)

open Finset
/-
**Finset.centerMass_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.centerMass_empty : (∅ : Finset ι).centerMass w z = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finset.centerMass_empty : (∅ : Finset ι).centerMass w z = 0 := by
  simp only [centerMass, sum_empty, smul_zero]
/-
**Finset.centerMass_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.centerMass_pair [DecidableEq ι] (hne : i != j) : ({i, j} : Finset ι
).centerMass w z = (w i / (w i + w j)) • z i + (w j / (w i + w j)) • z j
参数：hne : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_pair`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M
] {f : ι → M} [inst_1 : DecidableEq ι] {a b : ι},   a ≠ b → ∑ x ∈ {a, b}, f x = 
f a +…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf'`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a a' b : R},   a = a' → ∀ {e : ℕ}, Nat.rawCast 1 = e → a' ^ e * Nat.rawCa
st 1 = b → a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 38 条，此处仅展示前 30 条）
-/
theorem Finset.centerMass_pair [DecidableEq ι] (hne : i ≠ j) :
    ({i, j} : Finset ι).centerMass w z = (w i / (w i + w j)) • z i + (w j / (w i + w j)) • z j := by
  simp only [centerMass, sum_pair hne]
  module

variable {w}
/-
**Finset.centerMass_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.centerMass_insert [DecidableEq ι] (ha : i ∉ t) (hw : ∑ j in t, w j 
!= 0) : (insert i t).centerMass w z = (w i / (w i + ∑ j in t, w j)) • z i + ((∑ 
j in t, w j) / (w i + ∑ j in t, w j)) • t.centerMass w z
参数：ha : i ∉ t；hw : ∑ j in t, w j != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
theorem Finset.centerMass_insert [DecidableEq ι] (ha : i ∉ t) (hw : ∑ j ∈ t, w j ≠ 0) :
    (insert i t).centerMass w z =
      (w i / (w i + ∑ j ∈ t, w j)) • z i +
        ((∑ j ∈ t, w j) / (w i + ∑ j ∈ t, w j)) • t.centerMass w z := by
  simp only [centerMass, sum_insert ha, smul_add, (mul_smul _ _ _).symm, ← div_eq_inv_mul]
  congr 2
  rw [div_mul_eq_mul_div, mul_inv_cancel₀ hw, one_div]
/-
**Finset.centerMass_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.centerMass_singleton (hw : w i != 0) : ({i} : Finset ι).centerMass 
w z = z i
参数：hw : w i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.centerMass.eq_1`：∀ {R : Type u_1} {E : Type u_3} {ι : Type u_5} [
inst : Field R] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   (t : Fi
nset ι) (w :…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
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
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons_zero`：eval_mul_eval_cons_
zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M} (h : L.eval * l.eval = l'.
eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_of_pow_eq_zero`：eval_cons_of_pow_e
q_zero [CommGroupWithZero M] {r : Int} (hr : r = 0) {x : M} (hx : x != 0) (l : N
F M) : ((r, x) ::ᵣ l).eval = NF.eval l
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
（共 36 条，此处仅展示前 30 条）
-/
theorem Finset.centerMass_singleton (hw : w i ≠ 0) : ({i} : Finset ι).centerMass w z = z i := by
  rw [centerMass, sum_singleton, sum_singleton]
  match_scalars
  field
/-
**Finset.centerMass_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {R : Type u_1} {E : Type u_3} {ι : Type u_5} [inst : Field R] [inst_1 : 
AddCommGroup E] [inst_2 : _root_.Module R E]   (t : Finset ι) {w : ι → R} (z : ι
 → E), t.centerMass (-w) z = t.centerMass w z
参数：t : Finset ι；z : ι → E；-w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma Finset.centerMass_neg_left : t.centerMass (-w) z = t.centerMass w z := by
  simp [centerMass, inv_neg]
/-
**Finset.centerMass_smul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.centerMass_smul_left {c : R'} [Module R' R] [Module R' E] [SMulComm
Class R' R R] [IsScalarTower R' R R] [SMulCommClass R R' E] [IsScalarTower R' R 
E] (hc : c != 0) : t.centerMass (c • w) z = t.centerMass w z
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `smul_inv₀`：smul_inv₀ (c : G₀) (x : G₀') : (c • x)⁻¹ = c⁻¹ • x⁻¹
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `smul_smul_smul_comm`：smul_smul_smul_comm [SMul α β] [SMul α γ] [SMul β δ
] [SMul α δ] [SMul γ δ] [IsScalarTower α β δ] [IsScalarTower α γ δ] [SMulCommCla
ss β γ δ]…
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Finset.centerMass_smul_left {c : R'} [Module R' R] [Module R' E] [SMulCommClass R' R R]
    [IsScalarTower R' R R] [SMulCommClass R R' E] [IsScalarTower R' R E] (hc : c ≠ 0) :
    t.centerMass (c • w) z = t.centerMass w z := by
  simp [centerMass, -smul_assoc, smul_assoc c, ← smul_sum, smul_inv₀, smul_smul_smul_comm, hc]
/-
**Finset.centerMass_eq_of_sum_1** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.centerMass_eq_of_sum_1 (hw : ∑ i in t, w i = 1) : t.centerMass w z 
= ∑ i in t, w i • z i
参数：hw : ∑ i in t, w i = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finset.centerMass_eq_of_sum_1 (hw : ∑ i ∈ t, w i = 1) :
    t.centerMass w z = ∑ i ∈ t, w i • z i := by
  simp only [Finset.centerMass, hw, inv_one, one_smul]
/-
**Finset.centerMass_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.centerMass_smul : (t.centerMass w fun i => c • z i) = c • t.centerM
ass w z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finset.centerMass_smul : (t.centerMass w fun i => c • z i) = c • t.centerMass w z := by
  simp only [Finset.centerMass, Finset.smul_sum, (mul_smul _ _ _).symm, mul_comm c, mul_assoc]

/-- A convex combination of two centers of mass is a center of mass as well. This version
deals with two different index types. -/
/-
**Finset.centerMass_segment'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.centerMass_segment' (s : Finset ι) (t : Finset ι') (ws : ι -> R) (z
s : ι -> E) (wt : ι' -> R) (zt : ι' -> E) (hws : ∑ i in s, ws i = 1) (hwt : ∑ i 
in t, wt i = 1) (a b : R) (hab : a + b = 1) : a • s.centerMass ws zs + b • t.cen
terMass wt zt = (s.disjSum t).centerMass (Sum.elim (fun i => a * ws i) fun j => 
b * wt j) (Sum.elim zs zt)
参数：s : Finset ι；t : Finset ι'；ws : ι -> R；zs : ι -> E；wt : ι' -> R；zt : ι' -> E；
hws : ∑ i in s, ws i = 1；hwt : ∑ i in t, wt i = 1；a b : R；hab : a + b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.centerMass_eq_of_sum_1`：Finset.centerMass_eq_of_sum_1 (hw : ∑ i i
n t, w i = 1) : t.centerMass w z = ∑ i in t, w i • z i
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_sumElim`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst
 : AddCommMonoid M] (s : Finset ι) (t : Finset κ) (f : ι → M)   (g : κ → M), ∑ x
 ∈ s.dis…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A convex combination of two centers of mass is a center of mass as well. This ve
rsion
deals with two different index types.
-/
theorem Finset.centerMass_segment' (s : Finset ι) (t : Finset ι') (ws : ι → R) (zs : ι → E)
    (wt : ι' → R) (zt : ι' → E) (hws : ∑ i ∈ s, ws i = 1) (hwt : ∑ i ∈ t, wt i = 1) (a b : R)
    (hab : a + b = 1) : a • s.centerMass ws zs + b • t.centerMass wt zt = (s.disjSum t).centerMass
    (Sum.elim (fun i => a * ws i) fun j => b * wt j) (Sum.elim zs zt) := by
  rw [s.centerMass_eq_of_sum_1 _ hws, t.centerMass_eq_of_sum_1 _ hwt, smul_sum, smul_sum, ←
    Finset.sum_sumElim, Finset.centerMass_eq_of_sum_1]
  · congr with ⟨⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr, mul_smul]
  · rw [sum_sumElim, ← mul_sum, ← mul_sum, hws, hwt, mul_one, mul_one, hab]

/-- A convex combination of two centers of mass is a center of mass as well. This version
works if two centers of mass share the set of original points. -/
/-
**Finset.centerMass_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.centerMass_segment (s : Finset ι) (w₁ w₂ : ι -> R) (z : ι -> E) (hw
₁ : ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1) (a b : R) (hab : a + b = 1) :
 a • s.centerMass w₁ z + b • s.centerMass w₂ z = s.centerMass (fun i => a * w₁ i
 + b * w₂ i) z
参数：s : Finset ι；w₁ w₂ : ι -> R；z : ι -> E；hw₁ : ∑ i in s, w₁ i = 1；hw₂ : ∑ i in 
s, w₂ i = 1；a b : R；hab : a + b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.centerMass_eq_of_sum_1`：Finset.centerMass_eq_of_sum_1 (hw : ∑ i i
n t, w i = 1) : t.centerMass w z = ∑ i in t, w i • z i
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b

--- 原说明 ---
A convex combination of two centers of mass is a center of mass as well. This ve
rsion
works if two centers of mass share the set of original points.
-/
theorem Finset.centerMass_segment (s : Finset ι) (w₁ w₂ : ι → R) (z : ι → E)
    (hw₁ : ∑ i ∈ s, w₁ i = 1) (hw₂ : ∑ i ∈ s, w₂ i = 1) (a b : R) (hab : a + b = 1) :
    a • s.centerMass w₁ z + b • s.centerMass w₂ z =
    s.centerMass (fun i => a * w₁ i + b * w₂ i) z := by
  have hw : (∑ i ∈ s, (a * w₁ i + b * w₂ i)) = 1 := by
    simp only [← mul_sum, sum_add_distrib, mul_one, *]
  simp only [Finset.centerMass_eq_of_sum_1, smul_sum, sum_add_distrib, add_smul, mul_smul, *]
/-
**Finset.centerMass_ite_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.centerMass_ite_eq [DecidableEq ι] (hi : i in t) : t.centerMass (fun
 j => if i = j then (1 : R) else 0) z = z i
参数：hi : i in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.centerMass_eq_of_sum_1`：Finset.centerMass_eq_of_sum_1 (hw : ∑ i i
n t, w i = 1) : t.centerMass w z = ∑ i in t, w i • z i
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem Finset.centerMass_ite_eq [DecidableEq ι] (hi : i ∈ t) :
    t.centerMass (fun j => if i = j then (1 : R) else 0) z = z i := by
  rw [Finset.centerMass_eq_of_sum_1]
  · trans ∑ j ∈ t, if i = j then z i else 0
    · congr with i
      split_ifs with h
      exacts [h ▸ one_smul _ _, zero_smul _ _]
    · rw [sum_ite_eq, if_pos hi]
  · rw [sum_ite_eq, if_pos hi]

variable {t}
/-
**Finset.centerMass_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.centerMass_subset {t' : Finset ι} (ht : t subseteq t') (h : forall 
i in t', i ∉ t -> w i = 0) : t.centerMass w z = t'.centerMass w z
参数：ht : t subseteq t'；h : forall i in t', i ∉ t -> w i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.centerMass.eq_1`：∀ {R : Type u_1} {E : Type u_3} {ι : Type u_5} [
inst : Field R] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   (t : Fi
nset ι) (w :…
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem Finset.centerMass_subset {t' : Finset ι} (ht : t ⊆ t') (h : ∀ i ∈ t', i ∉ t → w i = 0) :
    t.centerMass w z = t'.centerMass w z := by
  rw [centerMass, sum_subset ht h, smul_sum, centerMass, smul_sum]
  apply sum_subset ht
  intro i hit' hit
  rw [h i hit' hit, zero_smul, smul_zero]
/-
**Finset.centerMass_filter_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.centerMass_filter_ne_zero [forall i, Decidable (w i != 0)] : {i in 
t | w i != 0}.centerMass w z = t.centerMass w z
参数：w i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.centerMass_subset`：Finset.centerMass_subset {t' : Finset ι} (ht :
 t subseteq t') (h : forall i in t', i ∉ t -> w i = 0) : t.centerMass w z = t'.c
enterMass w z
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem Finset.centerMass_filter_ne_zero [∀ i, Decidable (w i ≠ 0)] :
    {i ∈ t | w i ≠ 0}.centerMass w z = t.centerMass w z :=
  Finset.centerMass_subset z (filter_subset _ _) fun i hit hit' => by
    simpa only [hit, mem_filter, true_and, Ne, Classical.not_not] using hit'

namespace Finset

variable [LinearOrder R] [IsOrderedAddMonoid α] [PosSMulMono R α]

/-
**Finset.centerMass_le_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：centerMass_le_sup {s : Finset ι} {f : ι -> α} {w : ι -> R} (hw₀ : forall i
 in s, 0 <= w i) (hw₁ : 0 < ∑ i in s, w i) : s.centerMass w f <= s.sup' (nonempt
y_of_ne_empty <| by rintro rfl; simp at hw₁) f
参数：hw₀ : forall i in s, 0 <= w i；hw₁ : 0 < ∑ i in s, w i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.nonempty_of_ne_empty`：nonempty_of_ne_empty {s : Finset α} (h : s 
!= ∅) : s.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.centerMass.eq_1`：∀ {R : Type u_1} {E : Type u_3} {ι : Type u_5} [
inst : Field R] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   (t : Fi
nset ι) (w :…
· 使用引理 `inv_smul_le_iff_of_pos`：inv_smul_le_iff_of_pos [PosSMulMono α β] [PosSMu
lReflectLE α β] (ha : 0 < a) : a⁻¹ • b₁ <= b₂ ↔ b₁ <= a • b₂
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
-/
theorem centerMass_le_sup {s : Finset ι} {f : ι → α} {w : ι → R} (hw₀ : ∀ i ∈ s, 0 ≤ w i)
    (hw₁ : 0 < ∑ i ∈ s, w i) :
    s.centerMass w f ≤ s.sup' (nonempty_of_ne_empty <| by rintro rfl; simp at hw₁) f := by
  rw [centerMass, inv_smul_le_iff_of_pos hw₁, sum_smul]
  exact sum_le_sum fun i hi => smul_le_smul_of_nonneg_left (le_sup' _ hi) <| hw₀ i hi
/-
**Finset.inf_le_centerMass** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inf_le_centerMass {s : Finset ι} {f : ι -> α} {w : ι -> R} (hw₀ : forall i
 in s, 0 <= w i) (hw₁ : 0 < ∑ i in s, w i) : s.inf' (nonempty_of_ne_empty <| by 
rintro rfl; simp at hw₁) f <= s.centerMass w f
参数：hw₀ : forall i in s, 0 <= w i；hw₁ : 0 < ∑ i in s, w i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.centerMass_le_sup`：centerMass_le_sup {s : Finset ι} {f : ι -> α} 
{w : ι -> R} (hw₀ : forall i in s, 0 <= w i) (hw₁ : 0 < ∑ i in s, w i) : s.cente
rMass w f <= s…
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
-/
theorem inf_le_centerMass {s : Finset ι} {f : ι → α} {w : ι → R} (hw₀ : ∀ i ∈ s, 0 ≤ w i)
    (hw₁ : 0 < ∑ i ∈ s, w i) :
    s.inf' (nonempty_of_ne_empty <| by rintro rfl; simp at hw₁) f ≤ s.centerMass w f :=
  centerMass_le_sup (α := αᵒᵈ) hw₀ hw₁

end Finset

variable {z}

/-
**Finset.centerMass_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.centerMass_const (hw : ∑ j in t, w j != 0) (c : E) : t.centerMass w
 (Function.const _ c) = c
参数：hw : ∑ j in t, w j != 0；c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Finset.centerMass_const (hw : ∑ j ∈ t, w j ≠ 0) (c : E) :
    t.centerMass w (Function.const _ c) = c := by
  simp [centerMass, ← sum_smul, hw]
/-
**Finset.centerMass_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.centerMass_congr [DecidableEq ι] {t' : Finset ι} {w' : ι -> R} {z' 
: ι -> E} (h : forall i, (i in t ∧ w i != 0 ∨ i in t' ∧ w' i != 0) -> i in t int
er t' ∧ w i = w' i ∧ z i = z' i) : t.centerMass w z = t'.centerMass w' z'
参数：h : forall i, (i in t ∧ w i != 0 ∨ i in t' ∧ w' i != 0) -> i in t inter t' ∧ 
w i = w' i ∧ z i = z' i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.centerMass_filter_ne_zero`：Finset.centerMass_filter_ne_zero [fora
ll i, Decidable (w i != 0)] : {i in t | w i != 0}.centerMass w z = t.centerMass 
w z
· 使用定理 `Finset.centerMass.eq_1`：∀ {R : Type u_1} {E : Type u_3} {ι : Type u_5} [
inst : Field R] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   (t : Fi
nset ι) (w :…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
-/
lemma Finset.centerMass_congr [DecidableEq ι] {t' : Finset ι} {w' : ι → R} {z' : ι → E}
    (h : ∀ i, (i ∈ t ∧ w i ≠ 0 ∨ i ∈ t' ∧ w' i ≠ 0) → i ∈ t ∩ t' ∧ w i = w' i ∧ z i = z' i) :
    t.centerMass w z = t'.centerMass w' z' := by
  classical
  rw [← centerMass_filter_ne_zero, centerMass, ← centerMass_filter_ne_zero, centerMass]
  congr 1
  · congr 1
    exact sum_congr (by grind) (by grind)
  · exact sum_congr (by grind) (by grind)
/-
**Finset.centerMass_congr_finset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.centerMass_congr_finset [DecidableEq ι] {t' : Finset ι} (h : forall
 i in t union t', w i != 0 -> i in t inter t') : t.centerMass w z = t'.centerMas
s w z
参数：h : forall i in t union t', w i != 0 -> i in t inter t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.centerMass_congr`：Finset.centerMass_congr [DecidableEq ι] {t' : F
inset ι} {w' : ι -> R} {z' : ι -> E} (h : forall i, (i in t ∧ w i != 0 ∨ i in t'
 ∧ w' i != 0)…
-/
lemma Finset.centerMass_congr_finset [DecidableEq ι] {t' : Finset ι}
    (h : ∀ i ∈ t ∪ t', w i ≠ 0 → i ∈ t ∩ t') : t.centerMass w z = t'.centerMass w z :=
  centerMass_congr (by grind)
/-
**Finset.centerMass_congr_weights** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.centerMass_congr_weights {w' : ι -> R} (h : forall i in t, w i = w'
 i) : t.centerMass w z = t.centerMass w' z
参数：h : forall i in t, w i = w' i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.centerMass_congr`：Finset.centerMass_congr [DecidableEq ι] {t' : F
inset ι} {w' : ι -> R} {z' : ι -> E} (h : forall i, (i in t ∧ w i != 0 ∨ i in t'
 ∧ w' i != 0)…
-/
lemma Finset.centerMass_congr_weights {w' : ι → R} (h : ∀ i ∈ t, w i = w' i) :
    t.centerMass w z = t.centerMass w' z := by
  classical
  exact centerMass_congr (by grind)
/-
**Finset.centerMass_congr_fun** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.centerMass_congr_fun {z' : ι -> E} (h : forall i in t, w i != 0 -> 
z i = z' i) : t.centerMass w z = t.centerMass w z'
参数：h : forall i in t, w i != 0 -> z i = z' i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.centerMass_congr`：Finset.centerMass_congr [DecidableEq ι] {t' : F
inset ι} {w' : ι -> R} {z' : ι -> E} (h : forall i, (i in t ∧ w i != 0 ∨ i in t'
 ∧ w' i != 0)…
-/
lemma Finset.centerMass_congr_fun {z' : ι → E} (h : ∀ i ∈ t, w i ≠ 0 → z i = z' i) :
    t.centerMass w z = t.centerMass w z' := by
  classical
  exact centerMass_congr (by grind)
/-
**Finset.centerMass_of_sum_add_sum_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.centerMass_of_sum_add_sum_eq_zero {s t : Finset ι} (hw : ∑ i in s, 
w i + ∑ i in t, w i = 0) (hz : ∑ i in s, w i • z i + ∑ i in t, w i • z i = 0) : 
s.centerMass w z = t.centerMass w z
参数：hw : ∑ i in s, w i + ∑ i in t, w i = 0；hz : ∑ i in s, w i • z i + ∑ i in t, w
 i • z i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_neg_of_add_eq_zero_left`：∀ {G : Type u_1} [inst : SubtractionMonoid G
] {a b : G}, a + b = 0 → a = -b
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_neg_of_add_eq_zero_right`：∀ {α : Type u_1} [inst : SubtractionMonoid 
α] {a b : α}, a + b = 0 → b = -a
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Finset.centerMass_of_sum_add_sum_eq_zero {s t : Finset ι}
    (hw : ∑ i ∈ s, w i + ∑ i ∈ t, w i = 0) (hz : ∑ i ∈ s, w i • z i + ∑ i ∈ t, w i • z i = 0) :
    s.centerMass w z = t.centerMass w z := by
  simp [centerMass, eq_neg_of_add_eq_zero_right hw, eq_neg_of_add_eq_zero_left hz]

variable [LinearOrder R] [IsStrictOrderedRing R] [IsOrderedAddMonoid α] [PosSMulMono R α]

/-- The center of mass of a finite subset of a convex set belongs to the set
provided that all weights are non-negative, and the total weight is positive. -/
/-
**Convex.centerMass_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.centerMass_mem (hs : Convex R s) : (forall i in t, 0 <= w i) -> (0 
< ∑ i in t, w i) -> (forall i in t, z i in s) -> t.centerMass w z in s
参数：hs : Convex R s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst 
: AddCommMonoid N] [inst_1 : PartialOrder N] {f : ι → N} {s : Finset ι}   [AddLe
ftMono N], (∀ i ∈ s, 0…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.centerMass_insert`：Finset.centerMass_insert [DecidableEq ι] (ha :
 i ∉ t) (hw : ∑ j in t, w j != 0) : (insert i t).centerMass w z = (w i / (w i + 
∑ j in t, w j)…
· 使用定理 `convex_iff_div`：convex_iff_div : Convex 𝕜 s ↔ forall ⦃x⦄, x in s -> fora
ll ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> 0 < a + b -> (a / (a + b
)) •…
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The center of mass of a finite subset of a convex set belongs to the set
provided that all weights are non-negative, and the total weight is positive.
-/
theorem Convex.centerMass_mem (hs : Convex R s) :
    (∀ i ∈ t, 0 ≤ w i) → (0 < ∑ i ∈ t, w i) → (∀ i ∈ t, z i ∈ s) → t.centerMass w z ∈ s := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ht =>
    intro h₀ hpos hmem
    have zi : z i ∈ s := hmem _ (mem_insert_self _ _)
    have hs₀ : ∀ j ∈ t, 0 ≤ w j := fun j hj => h₀ j <| mem_insert_of_mem hj
    rw [sum_insert hi] at hpos
    by_cases hsum_t : ∑ j ∈ t, w j = 0
    · have ws : ∀ j ∈ t, w j = 0 := (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t
      have wz : ∑ j ∈ t, w j • z j = 0 := sum_eq_zero fun i hi => by simp [ws i hi]
      simp only [centerMass, sum_insert hi, wz, hsum_t, add_zero]
      simp only [hsum_t, add_zero] at hpos
      rw [← mul_smul, inv_mul_cancel₀ (ne_of_gt hpos), one_smul]
      exact zi
    · rw [Finset.centerMass_insert _ _ _ hi hsum_t]
      refine convex_iff_div.1 hs zi (ht hs₀ ?_ ?_) ?_ (sum_nonneg hs₀) hpos
      · exact lt_of_le_of_ne (sum_nonneg hs₀) (Ne.symm hsum_t)
      · intro j hj
        exact hmem j (mem_insert_of_mem hj)
      · exact h₀ _ (mem_insert_self _ _)
/-
**Convex.sum_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.sum_mem (hs : Convex R s) (h₀ : forall i in t, 0 <= w i) (h₁ : ∑ i 
in t, w i = 1) (hz : forall i in t, z i in s) : (∑ i in t, w i • z i) in s
参数：hs : Convex R s；h₀ : forall i in t, 0 <= w i；h₁ : ∑ i in t, w i = 1；hz : fora
ll i in t, z i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Convex.centerMass_mem`：Convex.centerMass_mem (hs : Convex R s) : (forall
 i in t, 0 <= w i) -> (0 < ∑ i in t, w i) -> (forall i in t, z i in s) -> t.cent
erMass w z …
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Convex.sum_mem (hs : Convex R s) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ s) : (∑ i ∈ t, w i • z i) ∈ s := by
  simpa only [h₁, centerMass, inv_one, one_smul] using
    hs.centerMass_mem h₀ (h₁.symm ▸ zero_lt_one) hz

/-- A version of `Convex.sum_mem` for `finsum`s. If `s` is a convex set, `w : ι → R` is a family of
nonnegative weights with sum one and `z : ι → E` is a family of elements of a module over `R` such
that `z i ∈ s` whenever `w i ≠ 0`, then the sum `∑ᶠ i, w i • z i` belongs to `s`. See also
`PartitionOfUnity.finsum_smul_mem_convex`. -/
/-
**Convex.finsum_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.finsum_mem {ι : Sort*} {w : ι -> R} {z : ι -> E} {s : Set E} (hs : 
Convex R s) (h₀ : forall i, 0 <= w i) (h₁ : ∑ᶠ i, w i = 1) (hz : forall i, w i !
= 0 -> z i in s) : (∑ᶠ i, w i • z i) in s
参数：hs : Convex R s；h₀ : forall i, 0 <= w i；h₁ : ∑ᶠ i, w i = 1；hz : forall i, w i
 != 0 -> z i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `finsum_def'`：∀ {M : Type u_7} {α : Sort u_8} [inst : AddCommMonoid M] (f
 : α → M),   finsum f = if h : Function.HasFiniteSupport (f ∘ PLift.down) then ∑
 …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Function.support_smul_subset_left`：support_smul_subset_left [Zero R] [Ze
ro M] [SMulWithZero R M] (f : α -> R) (g : α -> M) : support (f • g) subseteq su
pport f
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `finsum_eq_sum_plift_of_support_subset`：∀ {M : Type u_2} {α : Sort u_4} [
inst : AddCommMonoid M] {f : α → M} {s : Finset (PLift α)},   Function.support (
f ∘ PLift.down) ⊆ ↑s → ∑ᶠ (…
· 使用定理 `Convex.sum_mem`：Convex.sum_mem (hs : Convex R s) (h₀ : forall i in t, 0 
<= w i) (h₁ : ∑ i in t, w i = 1) (hz : forall i in t, z i in s) : (∑ i in t, w i
 • z…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s

--- 原说明 ---
A version of `Convex.sum_mem` for `finsum`s. If `s` is a convex set, `w : ι → R`
 is a family of
nonnegative weights with sum one and `z : ι → E` is a family of elements of a mo
dule over `R` such
that `z i ∈ s` whenever `w i ≠ 0`, then the sum `∑ᶠ i, w i • z i` belongs to `s`
. See also
`PartitionOfUnity.finsum_smul_mem_convex`.
-/
theorem Convex.finsum_mem {ι : Sort*} {w : ι → R} {z : ι → E} {s : Set E} (hs : Convex R s)
    (h₀ : ∀ i, 0 ≤ w i) (h₁ : ∑ᶠ i, w i = 1) (hz : ∀ i, w i ≠ 0 → z i ∈ s) :
    (∑ᶠ i, w i • z i) ∈ s := by
  have hfin_w : HasFiniteSupport (w ∘ PLift.down) := by
    by_contra H
    rw [finsum, dif_neg H] at h₁
    exact zero_ne_one h₁
  have hsub : support ((fun i => w i • z i) ∘ PLift.down) ⊆ hfin_w.toFinset :=
    (support_smul_subset_left _ _).trans hfin_w.coe_toFinset.ge
  rw [finsum_eq_sum_plift_of_support_subset hsub]
  refine hs.sum_mem (fun _ _ => h₀ _) ?_ fun i hi => hz _ ?_
  · rwa [finsum, dif_pos hfin_w] at h₁
  · rwa [hfin_w.mem_toFinset] at hi
/-
**convex_iff_sum_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_iff_sum_mem : Convex R s ↔ forall (t : Finset E) (w : E -> R), (for
all i in t, 0 <= w i) -> ∑ i in t, w i = 1 -> (forall x in t, x in s) -> (∑ x in
 t, w x • x) in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.sum_mem`：Convex.sum_mem (hs : Convex R s) (h₀ : forall i in t, 0 
<= w i) (h₁ : ∑ i in t, w i = 1) (hz : forall i in t, z i in s) : (∑ i in t, w i
 • z…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_pair`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M
] {f : ι → M} [inst_1 : DecidableEq ι] {a b : ι},   a ≠ b → ∑ x ∈ {a, b}, f x = 
f a +…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `trivial`：True
-/
theorem convex_iff_sum_mem : Convex R s ↔ ∀ (t : Finset E) (w : E → R),
    (∀ i ∈ t, 0 ≤ w i) → ∑ i ∈ t, w i = 1 → (∀ x ∈ t, x ∈ s) → (∑ x ∈ t, w x • x) ∈ s := by
  classical
  refine ⟨fun hs t w hw₀ hw₁ hts => hs.sum_mem hw₀ hw₁ hts, ?_⟩
  intro h x hx y hy a b ha hb hab
  by_cases h_cases : x = y
  · rw [h_cases, ← add_smul, hab, one_smul]
    exact hy
  · convert! h { x, y } (fun z => if z = y then b else a) _ _ _
    · simp only [sum_pair h_cases, if_neg h_cases, if_pos trivial]
    · grind
    · simp only [sum_pair h_cases, if_neg h_cases, if_pos trivial, hab]
    · intro i hi
      simp only [Finset.mem_singleton, Finset.mem_insert] at hi
      cases hi <;> subst i <;> assumption
/-
**Finset.centerMass_mem_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.centerMass_mem_convexHull (t : Finset ι) {w : ι -> R} (hw₀ : forall
 i in t, 0 <= w i) (hws : 0 < ∑ i in t, w i) {z : ι -> E} (hz : forall i in t, z
 i in s) : t.centerMass w z in convexHull R s
参数：t : Finset ι；hw₀ : forall i in t, 0 <= w i；hws : 0 < ∑ i in t, w i；hz : foral
l i in t, z i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.centerMass_mem`：Convex.centerMass_mem (hs : Convex R s) : (forall
 i in t, 0 <= w i) -> (0 < ∑ i in t, w i) -> (forall i in t, z i in s) -> t.cent
erMass w z …
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
-/
theorem Finset.centerMass_mem_convexHull (t : Finset ι) {w : ι → R} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hws : 0 < ∑ i ∈ t, w i) {z : ι → E} (hz : ∀ i ∈ t, z i ∈ s) :
    t.centerMass w z ∈ convexHull R s :=
  (convex_convexHull R s).centerMass_mem hw₀ hws fun i hi => subset_convexHull R s <| hz i hi

/-- A version of `Finset.centerMass_mem_convexHull` for when the weights are nonpositive. -/
/-
**Finset.centerMass_mem_convexHull_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.centerMass_mem_convexHull_of_nonpos (t : Finset ι) (hw₀ : forall i 
in t, w i <= 0) (hws : ∑ i in t, w i < 0) (hz : forall i in t, z i in s) : t.cen
terMass w z in convexHull R s
参数：t : Finset ι；hw₀ : forall i in t, w i <= 0；hws : ∑ i in t, w i < 0；hz : foral
l i in t, z i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.centerMass_neg_left`：∀ {R : Type u_1} {E : Type u_3} {ι : Type u_
5} [inst : Field R] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   (t 
: Finset ι) {w :…
· 使用定理 `Finset.centerMass_mem_convexHull`：Finset.centerMass_mem_convexHull (t : 
Finset ι) {w : ι -> R} (hw₀ : forall i in t, 0 <= w i) (hws : 0 < ∑ i in t, w i)
 {z : ι -> E} (hz : fo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N

--- 原说明 ---
A version of `Finset.centerMass_mem_convexHull` for when the weights are nonposi
tive.
-/
lemma Finset.centerMass_mem_convexHull_of_nonpos (t : Finset ι) (hw₀ : ∀ i ∈ t, w i ≤ 0)
    (hws : ∑ i ∈ t, w i < 0) (hz : ∀ i ∈ t, z i ∈ s) : t.centerMass w z ∈ convexHull R s := by
  rw [← centerMass_neg_left]
  exact Finset.centerMass_mem_convexHull _ (fun _i hi ↦ neg_nonneg.2 <| hw₀ _ hi) (by simpa) hz

/-- A refinement of `Finset.centerMass_mem_convexHull` when the indexed family is a `Finset` of
the space. -/
/-
**Finset.centerMass_id_mem_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.centerMass_id_mem_convexHull (t : Finset E) {w : E -> R} (hw₀ : for
all i in t, 0 <= w i) (hws : 0 < ∑ i in t, w i) : t.centerMass w id in convexHul
l R (t : Set E)
参数：t : Finset E；hw₀ : forall i in t, 0 <= w i；hws : 0 < ∑ i in t, w i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.centerMass_mem_convexHull`：Finset.centerMass_mem_convexHull (t : 
Finset ι) {w : ι -> R} (hw₀ : forall i in t, 0 <= w i) (hws : 0 < ∑ i in t, w i)
 {z : ι -> E} (hz : fo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)

--- 原说明 ---
A refinement of `Finset.centerMass_mem_convexHull` when the indexed family is a 
`Finset` of
the space.
-/
theorem Finset.centerMass_id_mem_convexHull (t : Finset E) {w : E → R} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hws : 0 < ∑ i ∈ t, w i) : t.centerMass w id ∈ convexHull R (t : Set E) :=
  t.centerMass_mem_convexHull hw₀ hws fun _ => mem_coe.2

/-- A version of `Finset.centerMass_mem_convexHull` for when the weights are nonpositive. -/
/-
**Finset.centerMass_id_mem_convexHull_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.centerMass_id_mem_convexHull_of_nonpos (t : Finset E) {w : E -> R} 
(hw₀ : forall i in t, w i <= 0) (hws : ∑ i in t, w i < 0) : t.centerMass w id in
 convexHull R (t : Set E)
参数：t : Finset E；hw₀ : forall i in t, w i <= 0；hws : ∑ i in t, w i < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.centerMass_mem_convexHull_of_nonpos`：Finset.centerMass_mem_convex
Hull_of_nonpos (t : Finset ι) (hw₀ : forall i in t, w i <= 0) (hws : ∑ i in t, w
 i < 0) (hz : forall i in t, z i…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)

--- 原说明 ---
A version of `Finset.centerMass_mem_convexHull` for when the weights are nonposi
tive.
-/
lemma Finset.centerMass_id_mem_convexHull_of_nonpos (t : Finset E) {w : E → R}
    (hw₀ : ∀ i ∈ t, w i ≤ 0) (hws : ∑ i ∈ t, w i < 0) :
    t.centerMass w id ∈ convexHull R (t : Set E) :=
  t.centerMass_mem_convexHull_of_nonpos hw₀ hws fun _ ↦ mem_coe.2

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-
**affineCombination_eq_centerMass** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineCombination_eq_centerMass {ι : Type*} {t : Finset ι} {p : ι -> E} {w
 : ι -> R} (hw₂ : ∑ i in t, w i = 1) : t.affineCombination R p w = centerMass t 
w p
参数：hw₂ : ∑ i in t, w i = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one`：affi
neCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι -> k) (p : ι -> P
) (h : ∑ i in s, w i = 1) (b : P) : s.affineCombination …
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.centerMass_eq_of_sum_1`：Finset.centerMass_eq_of_sum_1 (hw : ∑ i i
n t, w i = 1) : t.centerMass w z = ∑ i in t, w i • z i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem affineCombination_eq_centerMass {ι : Type*} {t : Finset ι} {p : ι → E} {w : ι → R}
    (hw₂ : ∑ i ∈ t, w i = 1) : t.affineCombination R p w = centerMass t w p := by
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ w _ hw₂ (0 : E),
    Finset.weightedVSubOfPoint_apply, vadd_eq_add, add_zero, t.centerMass_eq_of_sum_1 _ hw₂]
  simp_rw [vsub_eq_sub, sub_zero]
/-
**affineCombination_mem_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineCombination_mem_convexHull {s : Finset ι} {v : ι -> E} {w : ι -> R} 
(hw₀ : forall i in s, 0 <= w i) (hw₁ : s.sum w = 1) : s.affineCombination R v w 
in convexHull R (range v)
参数：hw₀ : forall i in s, 0 <= w i；hw₁ : s.sum w = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineCombination_eq_centerMass`：affineCombination_eq_centerMass {ι : Ty
pe*} {t : Finset ι} {p : ι -> E} {w : ι -> R} (hw₂ : ∑ i in t, w i = 1) : t.affi
neCombination R p w =…
· 使用定理 `Finset.centerMass_mem_convexHull`：Finset.centerMass_mem_convexHull (t : 
Finset ι) {w : ι -> R} (hw₀ : forall i in t, 0 <= w i) (hws : 0 < ∑ i in t, w i)
 {z : ι -> E} (hz : fo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem affineCombination_mem_convexHull {s : Finset ι} {v : ι → E} {w : ι → R}
    (hw₀ : ∀ i ∈ s, 0 ≤ w i) (hw₁ : s.sum w = 1) :
    s.affineCombination R v w ∈ convexHull R (range v) := by
  rw [affineCombination_eq_centerMass hw₁]
  apply s.centerMass_mem_convexHull hw₀
  · simp [hw₁]
  · simp

/-- The centroid can be regarded as a center of mass. -/
@[simp]
/-
**Finset.centroid_eq_centerMass** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.centroid_eq_centerMass (s : Finset ι) (hs : s.Nonempty) (p : ι -> E
) : s.centroid R p = s.centerMass (s.centroidWeights R) p
参数：s : Finset ι；hs : s.Nonempty；p : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineCombination_eq_centerMass`：affineCombination_eq_centerMass {ι : Ty
pe*} {t : Finset ι} {p : ι -> E} {w : ι -> R} (hw₂ : ∑ i in t, w i = 1) : t.affi
neCombination R p w =…
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_nonempty`：sum_centroidWeights_eq_on
e_of_nonempty [CharZero k] (h : s.Nonempty) : ∑ i in s, s.centroidWeights k i = 
1
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R

--- 原说明 ---
The centroid can be regarded as a center of mass.
-/
theorem Finset.centroid_eq_centerMass (s : Finset ι) (hs : s.Nonempty) (p : ι → E) :
    s.centroid R p = s.centerMass (s.centroidWeights R) p :=
  affineCombination_eq_centerMass (s.sum_centroidWeights_eq_one_of_nonempty R hs)
/-
**Finset.centroid_mem_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.centroid_mem_convexHull (s : Finset E) (hs : s.Nonempty) : s.centro
id R id in convexHull R (s : Set E)
参数：s : Finset E；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.centroid_eq_centerMass`：Finset.centroid_eq_centerMass (s : Finset
 ι) (hs : s.Nonempty) (p : ι -> E) : s.centroid R p = s.centerMass (s.centroidWe
ights R) p
· 使用定理 `Finset.centerMass_id_mem_convexHull`：Finset.centerMass_id_mem_convexHull
 (t : Finset E) {w : E -> R} (hw₀ : forall i in t, 0 <= w i) (hws : 0 < ∑ i in t
, w i) : t.centerMass w i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
-/
theorem Finset.centroid_mem_convexHull (s : Finset E) (hs : s.Nonempty) :
    s.centroid R id ∈ convexHull R (s : Set E) := by
  rw [s.centroid_eq_centerMass hs]
  apply s.centerMass_id_mem_convexHull
  · simp only [inv_nonneg, imp_true_iff, Nat.cast_nonneg, Finset.centroidWeights_apply]
  · have hs_card : (#s : R) ≠ 0 := by simp [Finset.nonempty_iff_ne_empty.mp hs]
    simp only [hs_card, Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀, Ne, not_false_iff,
      Finset.centroidWeights_apply, zero_lt_one]
/-
**convexHull_range_eq_exists_affineCombination** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_range_eq_exists_affineCombination (v : ι -> E) : convexHull R (
range v) = { x | exists (s : Finset ι) (w : ι -> R), (forall i in s, 0 <= w i) ∧
 s.sum w = 1 ∧ s.affineCombination R v w = x }
参数：v : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.affineCombination_eq_linear_combination`：affineCombination_eq_lin
ear_combination (s : Finset ι) (p : ι -> V) (w : ι -> k) (hw : ∑ i in s, w i = 1
) : s.affineCombination k p w = ∑ i …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.sum_ite_of_true`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [
inst : AddCommMonoid M] {p : ι → Prop} [inst_1 : DecidablePred p],   (∀ x ∈ s, p
 x) → ∀ (f g…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
（共 47 条，此处仅展示前 30 条）
-/
theorem convexHull_range_eq_exists_affineCombination (v : ι → E) : convexHull R (range v) =
    { x | ∃ (s : Finset ι) (w : ι → R), (∀ i ∈ s, 0 ≤ w i) ∧ s.sum w = 1 ∧
      s.affineCombination R v w = x } := by
  classical
  refine Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_range.mp hx
    exact ⟨{i}, Function.const ι (1 : R), by simp, by simp, by simp [hi]⟩
  · rintro x ⟨s, w, hw₀, hw₁, rfl⟩ y ⟨s', w', hw₀', hw₁', rfl⟩ a b ha hb hab
    let W : ι → R := fun i => (if i ∈ s then a * w i else 0) + if i ∈ s' then b * w' i else 0
    have hW₁ : (s ∪ s').sum W = 1 := by
      rw [sum_add_distrib, ← sum_subset subset_union_left,
        ← sum_subset subset_union_right, sum_ite_of_true,
        sum_ite_of_true, ← mul_sum, ← mul_sum, hw₁, hw₁', ← add_mul, hab,
        mul_one] <;> intros <;> simp_all
    refine ⟨s ∪ s', W, ?_, hW₁, ?_⟩
    · rintro i -
      by_cases hi : i ∈ s <;> by_cases hi' : i ∈ s' <;>
        simp [W, hi, hi', add_nonneg, mul_nonneg ha (hw₀ i _), mul_nonneg hb (hw₀' i _)]
    · simp_rw [W, affineCombination_eq_linear_combination (s ∪ s') v _ hW₁,
        affineCombination_eq_linear_combination s v w hw₁,
        affineCombination_eq_linear_combination s' v w' hw₁', add_smul, sum_add_distrib]
      rw [← sum_subset subset_union_left, ← sum_subset subset_union_right]
      · simp only [ite_smul, sum_ite_of_true fun _ hi => hi, mul_smul, ← smul_sum]
      · intro i _ hi'
        simp [hi']
      · intro i _ hi'
        simp [hi']
  · rintro x ⟨s, w, hw₀, hw₁, rfl⟩
    exact affineCombination_mem_convexHull hw₀ hw₁

/--
Convex hull of `s` is equal to the set of all centers of masses of `Finset`s `t`, `z '' t ⊆ s`.
For universe reasons, you shouldn't use this lemma to prove that a given center of mass belongs
to the convex hull. Use convexity of the convex hull instead.
-/
/-
**convexHull_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_eq (s : Set E) : convexHull R s = { x : E | exists (ι : Type) (
t : Finset ι) (w : ι -> R) (z : ι -> E), (forall i in t, 0 <= w i) ∧ ∑ i in t, w
 i = 1 ∧ (forall i in t, z i in s) ∧ t.centerMass w z = x }
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.centerMass_segment'`：Finset.centerMass_segment' (s : Finset ι) (t
 : Finset ι') (ws : ι -> R) (zs : ι -> E) (wt : ι' -> R) (zt : ι' -> E) (hws : ∑
 i in s, ws i = …
· 使用定理 `Finset.mem_disjSum`：mem_disjSum : x in s.disjSum t ↔ (exists a, a in s ∧
 inl a = x) ∨ exists b, b in t ∧ inr b = x
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Finset.sum_disjSum`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst
 : AddCommMonoid M] (s : Finset ι) (t : Finset κ) (f : ι ⊕ κ → M),   ∑ x ∈ s.dis
jSum t, …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.centerMass_mem_convexHull`：Finset.centerMass_mem_convexHull (t : 
Finset ι) {w : ι -> R} (hw₀ : forall i in t, 0 <= w i) (hws : 0 < ∑ i in t, w i)
 {z : ι -> E} (hz : fo…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Convex hull of `s` is equal to the set of all centers of masses of `Finset`s `t`
, `z '' t ⊆ s`.
For universe reasons, you shouldn't use this lemma to prove that a given center 
of mass belongs
to the convex hull. Use convexity of the convex hull instead.
-/
theorem convexHull_eq (s : Set E) : convexHull R s =
    { x : E | ∃ (ι : Type) (t : Finset ι) (w : ι → R) (z : ι → E), (∀ i ∈ t, 0 ≤ w i) ∧
      ∑ i ∈ t, w i = 1 ∧ (∀ i ∈ t, z i ∈ s) ∧ t.centerMass w z = x } := by
  refine Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    use PUnit, {PUnit.unit}, fun _ => 1, fun _ => x, fun _ _ => zero_le_one, sum_singleton _ _,
      fun _ _ => hx
    simp only [Finset.centerMass, Finset.sum_singleton, inv_one, one_smul]
  · rintro x ⟨ι, sx, wx, zx, hwx₀, hwx₁, hzx, rfl⟩ y ⟨ι', sy, wy, zy, hwy₀, hwy₁, hzy, rfl⟩ a b ha
      hb hab
    rw [Finset.centerMass_segment' _ _ _ _ _ _ hwx₁ hwy₁ _ _ hab]
    refine ⟨_, _, _, _, ?_, ?_, ?_, rfl⟩
    · rintro i hi
      rw [Finset.mem_disjSum] at hi
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
        apply_rules [mul_nonneg, hwx₀, hwy₀]
    · simp [← mul_sum, *]
    · intro i hi
      rw [Finset.mem_disjSum] at hi
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> apply_rules [hzx, hzy]
  · rintro _ ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
    exact t.centerMass_mem_convexHull hw₀ (hw₁.symm ▸ zero_lt_one) hz

/-- Universe polymorphic version of the reverse implication of `mem_convexHull_iff_exists_fintype`.
-/
/-
**mem_convexHull_of_exists_fintype** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_convexHull_of_exists_fintype {s : Set E} {x : E} [Fintype ι] (w : ι ->
 R) (z : ι -> E) (hw₀ : forall i, 0 <= w i) (hw₁ : ∑ i, w i = 1) (hz : forall i,
 z i in s) (hx : ∑ i, w i • z i = x) : x in convexHull R s
参数：w : ι -> R；z : ι -> E；hw₀ : forall i, 0 <= w i；hw₁ : ∑ i, w i = 1；hz : forall
 i, z i in s；hx : ∑ i, w i • z i = x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.centerMass_eq_of_sum_1`：Finset.centerMass_eq_of_sum_1 (hw : ∑ i i
n t, w i = 1) : t.centerMass w z = ∑ i in t, w i • z i
· 使用定理 `Finset.centerMass_mem_convexHull`：Finset.centerMass_mem_convexHull (t : 
Finset ι) {w : ι -> R} (hw₀ : forall i in t, 0 <= w i) (hws : 0 < ∑ i in t, w i)
 {z : ι -> E} (hz : fo…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R

--- 原说明 ---
Universe polymorphic version of the reverse implication of `mem_convexHull_iff_e
xists_fintype`.
-/
lemma mem_convexHull_of_exists_fintype {s : Set E} {x : E} [Fintype ι] (w : ι → R) (z : ι → E)
    (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1) (hz : ∀ i, z i ∈ s) (hx : ∑ i, w i • z i = x) :
    x ∈ convexHull R s := by
  rw [← hx, ← centerMass_eq_of_sum_1 _ _ hw₁]
  exact centerMass_mem_convexHull _ (by simpa using hw₀) (by simp [hw₁]) (by simpa using hz)

/-- The convex hull of `s` is equal to the set of centers of masses of finite families of points in
`s`.

For universe reasons, you shouldn't use this lemma to prove that a given center of mass belongs
to the convex hull. Use `mem_convexHull_of_exists_fintype` of the convex hull instead. -/
/-
**mem_convexHull_iff_exists_fintype** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_convexHull_iff_exists_fintype {s : Set E} {x : E} : x in convexHull R 
s ↔ exists (ι : Type) (_ : Fintype ι) (w : ι -> R) (z : ι -> E), (forall i, 0 <=
 w i) ∧ ∑ i, w i = 1 ∧ (forall i, z i in s) ∧ ∑ i, w i • z i = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `convexHull_eq`：convexHull_eq (s : Set E) : convexHull R s = { x : E | ex
ists (ι : Type) (t : Finset ι) (w : ι -> R) (z : ι -> E), (forall i in t, 0 <= w
 i)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.centerMass_eq_of_sum_1`：Finset.centerMass_eq_of_sum_1 (hw : ∑ i i
n t, w i = 1) : t.centerMass w z = ∑ i in t, w i • z i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `mem_convexHull_of_exists_fintype`：mem_convexHull_of_exists_fintype {s : 
Set E} {x : E} [Fintype ι] (w : ι -> R) (z : ι -> E) (hw₀ : forall i, 0 <= w i) 
(hw₁ : ∑ i, w i = 1) (…

--- 原说明 ---
The convex hull of `s` is equal to the set of centers of masses of finite famili
es of points in
`s`.

For universe reasons, you shouldn't use this lemma to prove that a given center 
of mass belongs
to the convex hull. Use `mem_convexHull_of_exists_fintype` of the convex hull in
stead.
-/
lemma mem_convexHull_iff_exists_fintype {s : Set E} {x : E} :
    x ∈ convexHull R s ↔ ∃ (ι : Type) (_ : Fintype ι) (w : ι → R) (z : ι → E), (∀ i, 0 ≤ w i) ∧
      ∑ i, w i = 1 ∧ (∀ i, z i ∈ s) ∧ ∑ i, w i • z i = x := by
  constructor
  · simp only [convexHull_eq, mem_ofPred_eq]
    rintro ⟨ι, t, w, z, h⟩
    refine ⟨t, inferInstance, w ∘ (↑), z ∘ (↑), ?_⟩
    simpa [← sum_attach t, centerMass_eq_of_sum_1 _ _ h.2.1] using h
  · rintro ⟨ι, _, w, z, hw₀, hw₁, hz, hx⟩
    exact mem_convexHull_of_exists_fintype w z hw₀ hw₁ hz hx
/-
**Finset.convexHull_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.convexHull_eq (s : Finset E) : convexHull R ↑s = { x : E | exists w
 : E -> R, (forall y in s, 0 <= w y) ∧ ∑ y in s, w y = 1 ∧ s.centerMass w id = x
 }
参数：s : Finset E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finset.centerMass_ite_eq`：Finset.centerMass_ite_eq [DecidableEq ι] (hi :
 i in t) : t.centerMass (fun j => if i = j then (1 : R) else 0) z = z i
· 使用定理 `Finset.centerMass_segment`：Finset.centerMass_segment (s : Finset ι) (w₁ 
w₂ : ι -> R) (z : ι -> E) (hw₁ : ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1) 
(a b : R) (hab …
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.centerMass_mem_convexHull`：Finset.centerMass_mem_convexHull (t : 
Finset ι) {w : ι -> R} (hw₀ : forall i in t, 0 <= w i) (hws : 0 < ∑ i in t, w i)
 {z : ι -> E} (hz : fo…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Finset.convexHull_eq (s : Finset E) : convexHull R ↑s =
    { x : E | ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧ s.centerMass w id = x } := by
  classical
  refine Set.Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    rw [Finset.mem_coe] at hx
    refine ⟨_, ?_, ?_, Finset.centerMass_ite_eq _ _ _ hx⟩
    · intros
      split_ifs
      exacts [zero_le_one, le_refl 0]
    · rw [Finset.sum_ite_eq, if_pos hx]
  · rintro x ⟨wx, hwx₀, hwx₁, rfl⟩ y ⟨wy, hwy₀, hwy₁, rfl⟩ a b ha hb hab
    rw [Finset.centerMass_segment _ _ _ _ hwx₁ hwy₁ _ _ hab]
    refine ⟨_, ?_, ?_, rfl⟩
    · rintro i hi
      apply_rules [add_nonneg, mul_nonneg, hwx₀, hwy₀]
    · simp only [Finset.sum_add_distrib, ← mul_sum, mul_one, *]
  · rintro _ ⟨w, hw₀, hw₁, rfl⟩
    exact
      s.centerMass_mem_convexHull (fun x hx => hw₀ _ hx) (hw₁.symm ▸ zero_lt_one) fun x hx => hx
/-
**Finset.mem_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.mem_convexHull {s : Finset E} {x : E} : x in convexHull R (s : Set 
E) ↔ exists w : E -> R, (forall y in s, 0 <= w y) ∧ ∑ y in s, w y = 1 ∧ s.center
Mass w id = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.convexHull_eq`：Finset.convexHull_eq (s : Finset E) : convexHull R
 ↑s = { x : E | exists w : E -> R, (forall y in s, 0 <= w y) ∧ ∑ y in s, w y = 1
 ∧ s.cente…
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Finset.mem_convexHull {s : Finset E} {x : E} : x ∈ convexHull R (s : Set E) ↔
    ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧ s.centerMass w id = x := by
  rw [Finset.convexHull_eq, Set.mem_ofPred_eq]

/-- This is a version of `Finset.mem_convexHull` stated without `Finset.centerMass`. -/
/-
**Finset.mem_convexHull'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.mem_convexHull' {s : Finset E} {x : E} : x in convexHull R (s : Set
 E) ↔ exists w : E -> R, (forall y in s, 0 <= w y) ∧ ∑ y in s, w y = 1 ∧ ∑ y in 
s, w y • y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_convexHull`：Finset.mem_convexHull {s : Finset E} {x : E} : x 
in convexHull R (s : Set E) ↔ exists w : E -> R, (forall y in s, 0 <= w y) ∧ ∑ y
 in s, w y …
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.centerMass_eq_of_sum_1`：Finset.centerMass_eq_of_sum_1 (hw : ∑ i i
n t, w i = 1) : t.centerMass w z = ∑ i in t, w i • z i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
This is a version of `Finset.mem_convexHull` stated without `Finset.centerMass`.
-/
lemma Finset.mem_convexHull' {s : Finset E} {x : E} :
    x ∈ convexHull R (s : Set E) ↔
      ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧ ∑ y ∈ s, w y • y = x := by
  rw [mem_convexHull]
  refine exists_congr fun w ↦ and_congr_right' <| and_congr_right fun hw ↦ ?_
  simp_rw [centerMass_eq_of_sum_1 _ _ hw, id_eq]
/-
**Set.Finite.convexHull_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.convexHull_eq {s : Set E} (hs : s.Finite) : convexHull R s = { 
x : E | exists w : E -> R, (forall y in s, 0 <= w y) ∧ ∑ y in hs.toFinset, w y =
 1 ∧ hs.toFinset.centerMass w id = x }
参数：hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.convexHull_eq`：Finset.convexHull_eq (s : Finset E) : convexHull R
 ↑s = { x : E | exists w : E -> R, (forall y in s, 0 <= w y) ∧ ∑ y in s, w y = 1
 ∧ s.cente…
-/
theorem Set.Finite.convexHull_eq {s : Set E} (hs : s.Finite) : convexHull R s =
    { x : E | ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ hs.toFinset, w y = 1 ∧
      hs.toFinset.centerMass w id = x } := by
  simpa only [Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, exists_prop] using
    hs.toFinset.convexHull_eq

/-- A weak version of Carathéodory's theorem. -/
/-
**convexHull_eq_union_convexHull_finite_subsets** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_eq_union_convexHull_finite_subsets (s : Set E) : convexHull R s
 = ⋃ (t : Finset E) (_ : ↑t subseteq s), convexHull R ↑t
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `convexHull_eq`：convexHull_eq (s : Set E) : convexHull R s = { x : E | ex
ists (ι : Type) (t : Finset ι) (w : ι -> R) (z : ι -> E), (forall i in t, 0 <= w
 i)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Finset.centerMass_mem_convexHull`：Finset.centerMass_mem_convexHull (t : 
Finset ι) {w : ι -> R} (hw₀ : forall i in t, 0 <= w i) (hws : 0 < ∑ i in t, w i)
 {z : ι -> E} (hz : fo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `convexHull_mono`：convexHull_mono (hst : s subseteq t) : convexHull 𝕜 s s
ubseteq convexHull 𝕜 t

--- 原说明 ---
A weak version of Carathéodory's theorem.
-/
theorem convexHull_eq_union_convexHull_finite_subsets (s : Set E) :
    convexHull R s = ⋃ (t : Finset E) (_ : ↑t ⊆ s), convexHull R ↑t := by
  classical
  refine Subset.antisymm ?_ ?_
  · rw [_root_.convexHull_eq]
    rintro x ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
    simp only [mem_iUnion]
    refine ⟨t.image z, ?_, ?_⟩
    · rw [coe_image, Set.image_subset_iff]
      exact hz
    · apply t.centerMass_mem_convexHull hw₀
      · simp only [hw₁, zero_lt_one]
      · exact fun i hi => Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)
  · exact iUnion_subset fun i => iUnion_subset convexHull_mono

/-- The `vectorSpan` of a segment is the span of the difference of its endpoints. -/
/-
**vectorSpan_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_segment {p₁ p₂ : E} : vectorSpan R (segment R p₁ p₂) = R ∙ (p₂ 
-ᵥ p₁)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `convexHull_pair`：convexHull_pair [IsOrderedRing 𝕜] (x y : E) : convexHul
l 𝕜 {x, y} = segment 𝕜 x y
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `affineSpan_convexHull`：affineSpan_convexHull (s : Set E) : affineSpan 𝕜 
(convexHull 𝕜 s) = affineSpan 𝕜 s
· 使用定理 `vectorSpan_pair_rev`：vectorSpan_pair_rev (p₁ p₂ : P) : vectorSpan k ({p₁
, p₂} : Set P) = k ∙ (p₂ -ᵥ p₁)
· 使用定理 `vsub_eq_sub`：∀ {G : Type u_1} [inst : AddGroup G] (g₁ g₂ : G), g₁ -ᵥ g₂ 
= g₁ - g₂

--- 原说明 ---
The `vectorSpan` of a segment is the span of the difference of its endpoints.
-/
theorem vectorSpan_segment {p₁ p₂ : E} :
    vectorSpan R (segment R p₁ p₂) = R ∙ (p₂ -ᵥ p₁) := by
  rw [← convexHull_pair, ← direction_affineSpan, affineSpan_convexHull,
      direction_affineSpan, vectorSpan_pair_rev, vsub_eq_sub]
/-
**mk_mem_convexHull_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mk_mem_convexHull_prod {t : Set F} {x : E} {y : F} (hx : x in convexHull R
 s) (hy : y in convexHull R t) : (x, y) in convexHull R (s ×ˢ t)
参数：hx : x in convexHull R s；hy : y in convexHull R t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mem_convexHull_iff_exists_fintype`：mem_convexHull_iff_exists_fintype {s 
: Set E} {x : E} : x in convexHull R s ↔ exists (ι : Type) (_ : Fintype ι) (w : 
ι -> R) (z : ι -> E), (…
· 使用定理 `Fintype.sum_prod_type`：∀ {γ : Type u_3} {α₁ : Type u_4} {α₂ : Type u_5} 
[inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid γ]   (f : α₁ ×
 α₂ → γ), ∑…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.sum_mul_sum`：sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι -> 
R) (g : κ -> R) : (∑ i in s, f i) * ∑ j in t, g j = ∑ i in s, ∑ j in t, f i * g 
j
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Prod.fst_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : Add
CommMonoid M] [inst_1 : AddCommMonoid N] {s : Finset ι}   {f : ι → M × N}, (∑ c 
∈ …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Prod.snd_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : Add
CommMonoid M] [inst_1 : AddCommMonoid N] {s : Finset ι}   {f : ι → M × N}, (∑ c 
∈ …
-/
theorem mk_mem_convexHull_prod {t : Set F} {x : E} {y : F} (hx : x ∈ convexHull R s)
    (hy : y ∈ convexHull R t) : (x, y) ∈ convexHull R (s ×ˢ t) := by
  rw [mem_convexHull_iff_exists_fintype] at hx hy ⊢
  obtain ⟨ι, _, w, f, hw₀, hw₁, hfs, hf⟩ := hx
  obtain ⟨κ, _, v, g, hv₀, hv₁, hgt, hg⟩ := hy
  have h_sum : ∑ i : ι × κ, w i.1 * v i.2 = 1 := by
    rw [Fintype.sum_prod_type, ← sum_mul_sum, hw₁, hv₁, mul_one]
  refine ⟨ι × κ, inferInstance, fun p => w p.1 * v p.2, fun p ↦ (f p.1, g p.2),
    fun p ↦ mul_nonneg (hw₀ _) (hv₀ _), h_sum, fun p ↦ ⟨hfs _, hgt _⟩, ?_⟩
  ext
  · simp_rw [Prod.fst_sum, Prod.smul_mk, Fintype.sum_prod_type, mul_comm (w _), mul_smul,
      sum_comm (γ := ι), ← Fintype.sum_smul_sum, hv₁, one_smul, hf]
  · simp_rw [Prod.snd_sum, Prod.smul_mk, Fintype.sum_prod_type, mul_smul, ← Fintype.sum_smul_sum,
      hw₁, one_smul, hg]

@[simp]
/-
**convexHull_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_prod (s : Set E) (t : Set F) : convexHull R (s ×ˢ t) = convexHu
ll R s ×ˢ convexHull R t
参数：s : Set E；t : Set F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `Convex.prod`：Convex.prod {s : Set E} {t : Set F} (hs : Convex 𝕜 s) (ht :
 Convex 𝕜 t) : Convex 𝕜 (s ×ˢ t)
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.prod_subset_iff`：prod_subset_iff {P : Set (α × β)} : s ×ˢ t subseteq
 P ↔ forall x in s, forall y in t, (x, y) in P
· 使用定理 `mk_mem_convexHull_prod`：mk_mem_convexHull_prod {t : Set F} {x : E} {y : 
F} (hx : x in convexHull R s) (hy : y in convexHull R t) : (x, y) in convexHull 
R (s ×ˢ t)
-/
theorem convexHull_prod (s : Set E) (t : Set F) :
    convexHull R (s ×ˢ t) = convexHull R s ×ˢ convexHull R t :=
  Subset.antisymm
      (convexHull_min (prod_mono (subset_convexHull _ _) <| subset_convexHull _ _) <|
        (convex_convexHull _ _).prod <| convex_convexHull _ _) <|
    prod_subset_iff.2 fun _ hx _ => mk_mem_convexHull_prod hx
/-
**convexHull_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_add (s t : Set E) : convexHull R (s + t) = convexHull R s + con
vexHull R t
参数：s t : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLinearMap.image_convexHull`：IsLinearMap.image_convexHull {f : E -> F} 
(hf : IsLinearMap 𝕜 f) (s : Set E) : f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s)
· 使用定理 `IsLinearMap.isLinearMap_add`：isLinearMap_add [AddCommMonoid M] [Module R
 M] : IsLinearMap R fun x : M × M => x.1 + x.2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `convexHull_prod`：convexHull_prod (s : Set E) (t : Set F) : convexHull R 
(s ×ˢ t) = convexHull R s ×ˢ convexHull R t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convexHull_add (s t : Set E) : convexHull R (s + t) = convexHull R s + convexHull R t := by
  simp_rw [← add_image_prod, ← IsLinearMap.isLinearMap_add.image_convexHull, convexHull_prod]

variable (R E)

/-- `convexHull` is an additive monoid morphism under pointwise addition. -/
@[simps]
/-
**convexHullAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：convexHullAddMonoidHom : Set E ->+ Set E where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `convexHull_add`：convexHull_add (s t : Set E) : convexHull R (s + t) = co
nvexHull R s + convexHull R t

--- 原说明 ---
`convexHull` is an additive monoid morphism under pointwise addition.
-/
noncomputable def convexHullAddMonoidHom : Set E →+ Set E where
  toFun := convexHull R
  map_add' := convexHull_add
  map_zero' := convexHull_zero

variable {R E}
/-
**convexHull_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_sub (s t : Set E) : convexHull R (s - t) = convexHull R s - con
vexHull R t
参数：s t : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `convexHull_add`：convexHull_add (s t : Set E) : convexHull R (s + t) = co
nvexHull R s + convexHull R t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convexHull_sub (s t : Set E) : convexHull R (s - t) = convexHull R s - convexHull R t := by
  simp_rw [sub_eq_add_neg, convexHull_add, ← convexHull_neg]
/-
**convexHull_list_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_list_sum (l : List (Set E)) : convexHull R l.sum = (l.map <| co
nvexHull R).sum
参数：l : List (Set E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem convexHull_list_sum (l : List (Set E)) : convexHull R l.sum = (l.map <| convexHull R).sum :=
  map_list_sum (convexHullAddMonoidHom R E) l
/-
**convexHull_multiset_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_multiset_sum (s : Multiset (Set E)) : convexHull R s.sum = (s.m
ap <| convexHull R).sum
参数：s : Multiset (Set E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_sum`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst :
 AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : FunLike F M N] [AddMono
idHomC…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem convexHull_multiset_sum (s : Multiset (Set E)) :
    convexHull R s.sum = (s.map <| convexHull R).sum :=
  map_multiset_sum (convexHullAddMonoidHom R E) s
/-
**convexHull_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_sum {ι} (s : Finset ι) (t : ι -> Set E) : convexHull R (∑ i in 
s, t i) = ∑ i in s, convexHull R (t i)
参数：s : Finset ι；t : ι -> Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem convexHull_sum {ι} (s : Finset ι) (t : ι → Set E) :
    convexHull R (∑ i ∈ s, t i) = ∑ i ∈ s, convexHull R (t i) :=
  map_sum (convexHullAddMonoidHom R E) _ _

/-- The convex hull of an affine basis is the intersection of the half-spaces defined by the
corresponding barycentric coordinates. -/
/-
**AffineBasis.convexHull_eq_nonneg_coord** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineBasis.convexHull_eq_nonneg_coord {ι : Type*} (b : AffineBasis ι R E)
 : convexHull R (range b) = { x | forall i, 0 <= b.coord i x }
参数：b : AffineBasis ι R E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `convexHull_range_eq_exists_affineCombination`：convexHull_range_eq_exists
_affineCombination (v : ι -> E) : convexHull R (range v) = { x | exists (s : Fin
set ι) (w : ι -> R), (forall i in …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `AffineBasis.coord_apply_combination_of_mem`：coord_apply_combination_of_m
em (hi : i in s) {w : ι -> k} (hw : s.sum w = 1) : b.coord i (s.affineCombinatio
n k b w) = w i
· 使用定理 `AffineBasis.coord_apply_combination_of_notMem`：coord_apply_combination_o
f_notMem (hi : i ∉ s) {w : ι -> k} (hw : s.sum w = 1) : b.coord i (s.affineCombi
nation k b w) = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `AffineBasis.tot`：tot : affineSpan k (range b) = ⊤
· 使用定理 `AffineSubspace.mem_top`：mem_top (p : P) : p in (⊤ : AffineSubspace k P)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_affineSpan_iff_eq_affineCombination`：mem_affineSpan_iff_eq_affineCom
bination [Nontrivial k] {p1 : P} {p : ι -> P} : p1 in affineSpan k (Set.range p)
 ↔ exists (s : Finset ι) (w :…
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The convex hull of an affine basis is the intersection of the half-spaces define
d by the
corresponding barycentric coordinates.
-/
theorem AffineBasis.convexHull_eq_nonneg_coord {ι : Type*} (b : AffineBasis ι R E) :
    convexHull R (range b) = { x | ∀ i, 0 ≤ b.coord i x } := by
  rw [convexHull_range_eq_exists_affineCombination]
  ext x
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨s, w, hw₀, hw₁, rfl⟩ i
    by_cases hi : i ∈ s
    · rw [b.coord_apply_combination_of_mem hi hw₁]
      exact hw₀ i hi
    · rw [b.coord_apply_combination_of_notMem hi hw₁]
  · have hx' : x ∈ affineSpan R (range b) := by
      rw [b.tot]
      exact AffineSubspace.mem_top R E x
    obtain ⟨s, w, hw₁, rfl⟩ := (mem_affineSpan_iff_eq_affineCombination R E).mp hx'
    refine ⟨s, w, ?_, hw₁, rfl⟩
    intro i hi
    specialize hx i
    rw [b.coord_apply_combination_of_mem hi hw₁] at hx
    exact hx

variable {s t t₁ t₂ : Finset E}

/-- Two simplices glue nicely if the union of their vertices is affine independent. -/
/-
**AffineIndependent.convexHull_inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AffineIndependent.convexHull_inter (hs : AffineIndependent R ((↑) : s -> E
)) (ht₁ : t₁ subseteq s) (ht₂ : t₂ subseteq s) : convexHull R (t₁ inter t₂ : Set
 E) = convexHull R t₁ inter convexHull R t₂
参数：hs : AffineIndependent R ((↑) : s -> E)；ht₁ : t₁ subseteq s；ht₂ : t₂ subseteq
 s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `convexHull_mono`：convexHull_mono (hst : s subseteq t) : convexHull 𝕜 s s
ubseteq convexHull 𝕜 t
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `Finset.sum_ite_mem`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s t : Finset ι) (f : ι → M),   (∑ i ∈ s, if i ∈ t
 then f …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.inter_eq_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Fi
nset α}, t ∩ s = s ↔ s ⊆ t
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AffineIndependent.eq_zero_of_sum_eq_zero_subtype`：AffineIndependent.eq_z
ero_of_sum_eq_zero_subtype {s : Finset V} (hp : AffineIndependent k ((↑) : s -> 
V)) {w : V -> k} (hw₀ : ∑ x in s, w x …
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.filter_mem_eq_inter`：filter_mem_eq_inter {s t : Finset α} [forall
 i, Decidable (i in t)] : (s.filter fun i => i in t) = s inter t
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
Two simplices glue nicely if the union of their vertices is affine independent.
-/
lemma AffineIndependent.convexHull_inter (hs : AffineIndependent R ((↑) : s → E))
    (ht₁ : t₁ ⊆ s) (ht₂ : t₂ ⊆ s) :
    convexHull R (t₁ ∩ t₂ : Set E) = convexHull R t₁ ∩ convexHull R t₂ := by
  classical
  refine (Set.subset_inter (convexHull_mono inf_le_left) <|
    convexHull_mono inf_le_right).antisymm ?_
  simp_rw [Set.subset_def, mem_inter_iff, Set.inf_eq_inter, ← coe_inter, mem_convexHull']
  rintro x ⟨⟨w₁, h₁w₁, h₂w₁, h₃w₁⟩, w₂, -, h₂w₂, h₃w₂⟩
  let w (x : E) : R := (if x ∈ t₁ then w₁ x else 0) - if x ∈ t₂ then w₂ x else 0
  have h₁w : ∑ i ∈ s, w i = 0 := by simp [w, Finset.inter_eq_right.2, *]
  replace hs := hs.eq_zero_of_sum_eq_zero_subtype h₁w <| by
    simp only [w, sub_smul, zero_smul, ite_smul, Finset.sum_sub_distrib, ← Finset.sum_filter, h₃w₁,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 ht₁, Finset.inter_eq_right.2 ht₂, h₃w₂,
      sub_self]
  have ht (x) (hx₁ : x ∈ t₁) (hx₂ : x ∉ t₂) : w₁ x = 0 := by
    simpa [w, hx₁, hx₂] using hs _ (ht₁ hx₁)
  refine ⟨w₁, ?_, ?_, ?_⟩
  · simp only [and_imp, Finset.mem_inter]
    exact fun y hy₁ _ ↦ h₁w₁ y hy₁
  all_goals
  · rwa [sum_subset inter_subset_left]
    rintro x
    simp_intro hx₁ hx₂
    simp [ht x hx₁ hx₂]

/-- Two simplices glue nicely if the union of their vertices is affine independent.

Note that `AffineIndependent.convexHull_inter` should be more versatile in most use cases. -/
/-
**AffineIndependent.convexHull_inter'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AffineIndependent.convexHull_inter' [DecidableEq E] (hs : AffineIndependen
t R ((↑) : ↑(t₁ union t₂) -> E)) : convexHull R (t₁ inter t₂ : Set E) = convexHu
ll R t₁ inter convexHull R t₂
参数：hs : AffineIndependent R ((↑) : ↑(t₁ union t₂) -> E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AffineIndependent.convexHull_inter`：AffineIndependent.convexHull_inter (
hs : AffineIndependent R ((↑) : s -> E)) (ht₁ : t₁ subseteq s) (ht₂ : t₂ subsete
q s) : convexHull R (t₁ …
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂

--- 原说明 ---
Two simplices glue nicely if the union of their vertices is affine independent.

Note that `AffineIndependent.convexHull_inter` should be more versatile in most 
use cases.
-/
lemma AffineIndependent.convexHull_inter' [DecidableEq E]
    (hs : AffineIndependent R ((↑) : ↑(t₁ ∪ t₂) → E)) :
    convexHull R (t₁ ∩ t₂ : Set E) = convexHull R t₁ ∩ convexHull R t₂ :=
  hs.convexHull_inter subset_union_left subset_union_right

end

section pi
variable {𝕜 ι : Type*} {E : ι → Type*} [Finite ι] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [Π i, AddCommGroup (E i)] [Π i, Module 𝕜 (E i)] {s : Set ι} {t : Π i, Set (E i)} {x : Π i, E i}

open Finset Fintype

/-
**mem_convexHull_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_convexHull_pi (h : forall i in s, x i in convexHull 𝕜 (t i)) : x in co
nvexHull 𝕜 (s.pi t)
参数：h : forall i in s, x i in convexHull 𝕜 (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `mem_convexHull_of_exists_fintype`：mem_convexHull_of_exists_fintype {s : 
Set E} {x : E} [Fintype ι] (w : ι -> R) (z : ι -> E) (hw₀ : forall i, 0 <= w i) 
(hw₁ : ∑ i, w i = 1) (…
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Fintype.prod_sum`：prod_sum {κ : ι -> Type*} [forall i, Fintype (κ i)] (f
 : forall i, κ i -> R) : ∏ i, ∑ j, f i j = ∑ x : forall i, κ i, ∏ i, f i (x i)
· 使用定理 `Finset.prod_eq_one`：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s,
 f x = 1
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fintype.sum_fiberwise`：∀ {M : Type u_4} {κ : Type u_6} {ι : Type u_7} [i
nst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   [inst_3 : Dec
idableEq κ]…
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Finset.sum_bij'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : (a
 : ι)…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.mem_piFinset`：mem_piFinset {t : forall a, Finset (δ a)} {f : for
all a, δ a} : f in piFinset t ↔ forall a, f a in t a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
（共 52 条，此处仅展示前 30 条）
-/
lemma mem_convexHull_pi (h : ∀ i ∈ s, x i ∈ convexHull 𝕜 (t i)) : x ∈ convexHull 𝕜 (s.pi t) := by
  classical
  cases nonempty_fintype ι
  wlog hs : s = Set.univ generalizing s t
  · rw [← pi_univ_ite]
    refine this (fun i _ ↦ ?_) rfl
    split_ifs with hi
    · exact h i hi
    · simp
  subst hs
  simp only [Set.mem_univ, mem_convexHull_iff_exists_fintype, true_implies] at h
  choose κ _ w f hw₀ hw₁ hft hf using h
  refine mem_convexHull_of_exists_fintype (fun k : Π i, κ i ↦ ∏ i, w i (k i)) (fun g i ↦ f _ (g i))
    (fun g ↦ prod_nonneg fun _ _ ↦ hw₀ _ _) ?_ (fun _ _ _ ↦ hft _ _) ?_
  · rw [← Fintype.prod_sum]
    exact prod_eq_one fun _ _ ↦ hw₁ _
  ext i
  calc
    _ = ∑ g : ∀ i, κ i, (∏ i, w i (g i)) • f i (g i) := by
      simp only [Finset.sum_apply, Pi.smul_apply]
    _ = ∑ j : κ i, ∑ g : {g : ∀ k, κ k // g i = j},
          (∏ k, w k (g.1 k)) • f i ((g : ∀ i, κ i) i) := by
      rw [← Fintype.sum_fiberwise fun g : ∀ k, κ k ↦ g i]
    _ = ∑ j : κ i, (∑ g : {g : ∀ k, κ k // g i = j}, ∏ k, w k (g.1 k)) • f i j := by
      simp_rw [sum_smul]
      congr! with j _ g _
      exact g.2
    _ = ∑ j : κ i, w i j • f i j := ?_
    _ = x i := hf _
  congr! with j _
  calc
    ∑ g : {g : ∀ k, κ k // g i = j}, ∏ k, w k (g.1 k)
      = ∑ g ∈ piFinset fun k ↦ if hk : k = i then hk ▸ {j} else univ, ∏ k, w k (g k) :=
      Finset.sum_bij' (fun g _ ↦ g) (fun g hg ↦ ⟨g, by simpa using mem_piFinset.1 hg i⟩)
        (by aesop) (by simp) (by simp) (by simp) (by simp)
    _ = w i j := by
      rw [← prod_univ_sum, ← prod_mul_prod_compl, Finset.prod_singleton, Finset.sum_eq_single,
        Finset.prod_eq_one, mul_one] <;> simp +contextual [hw₁]
/-
**convexHull_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {ι : Type u_2} {E : ι → Type u_3} [Finite ι] [inst : Fiel
d 𝕜] [inst_1 : LinearOrder 𝕜]   [IsStrictOrderedRing 𝕜] [inst_3 : (i : ι) → AddC
ommGroup (E i)] [inst_4 : (i : ι) → _root_.Module 𝕜 (E i)] (s : Set ι)   (t : (i
 : ι) → Set (E i)), (convexHull 𝕜) (s.pi t) = s.pi fun i => (convexHull 𝕜) (t i)
参数：i : ι；E i；i : ι；E i；s : Set ι；t : (i : ι) → Set (E i)；convexHull 𝕜；s.pi t；con
vexHull 𝕜；t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `Set.pi_mono`：pi_mono (h : forall i in s, t₁ i subseteq t₂ i) : pi s t₁ s
ubseteq pi s t₂
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `convex_pi`：convex_pi {ι : Type*} {E : ι -> Type*} [forall i, AddCommMono
id (E i)] [forall i, SMul 𝕜 (E i)] {s : Set ι} {t : forall i, Set (E i)} (ht : …
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用引理 `mem_convexHull_pi`：mem_convexHull_pi (h : forall i in s, x i in convexHu
ll 𝕜 (t i)) : x in convexHull 𝕜 (s.pi t)
-/
@[simp] lemma convexHull_pi (s : Set ι) (t : Π i, Set (E i)) :
    convexHull 𝕜 (s.pi t) = s.pi (fun i ↦ convexHull 𝕜 (t i)) :=
  Set.Subset.antisymm (convexHull_min (Set.pi_mono fun _ _ ↦ subset_convexHull _ _) <| convex_pi <|
    fun _ _ ↦ convex_convexHull _ _) fun _ ↦ mem_convexHull_pi

end pi

namespace Affine.Simplex

/-- The closed interior of a simplex is the convex hull of all vertices. -/
/-
**Affine.Simplex.convexHull_eq_closedInterior** 是 Mathlib 中的一个定理，位于命名空间 `Affine.
Simplex`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsOrderedRing 𝕜] [inst_3 : AddCommGroup V]   [inst_4 : _root_.Module 𝕜 V] {n : 
ℕ} (s : Affine.Simplex 𝕜 V n),   (convexHull 𝕜) (Set.range s.points) = s.closedI
nterior
参数：s : Affine.Simplex 𝕜 V n；convexHull 𝕜；Set.range s.points。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `convexHull_range_eq_exists_affineCombination`：convexHull_range_eq_exists
_affineCombination (v : ι -> E) : convexHull R (range v) = { x | exists (s : Fin
set ι) (w : ι -> R), (forall i in …
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_indicator_subset`：∀ {ι : Type u_1} {β : Type u_4} [inst : Add
CommMonoid β] (f : ι → β) {s t : Finset ι},   s ⊆ t → ∑ i ∈ t, (↑s).indicator f 
i = ∑ i ∈ s, f i
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `Finset.affineCombination_indicator_subset`：affineCombination_indicator_s
ubset (w : ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι} (h : s₁ subseteq s₂) : s₁.aff
ineCombination k p w = s₂.affin…
· 使用引理 `Affine.Simplex.affineCombination_mem_closedInterior_iff`：affineCombinati
on_mem_closedInterior_iff {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -> k} (
hw : ∑ i, w i = 1) : Finset.univ.affineCombin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `eq_affineCombination_of_mem_affineSpan_of_fintype`：eq_affineCombination_
of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι -> P} (h : p1 in affine
Span k (Set.range p)) : exists w : ι ->…
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用引理 `Affine.Simplex.closedInterior_subset_affineSpan`：closedInterior_subset_a
ffineSpan {n : Nat} {s : Simplex k P n} : s.closedInterior subseteq affineSpan k
 (Set.range s.points)
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The closed interior of a simplex is the convex hull of all vertices.
-/
@[simp] theorem convexHull_eq_closedInterior {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] {n : ℕ} (s : Simplex 𝕜 V n) :
    convexHull 𝕜 (Set.range s.points) = s.closedInterior := by
  ext p
  rw [convexHull_range_eq_exists_affineCombination, Set.mem_ofPred]
  constructor <;> intro h
  · obtain ⟨u, w, hw, hw1, rfl⟩ := h
    have hw' : ∀ i ∈ u, w i ≤ 1 := by
      intro i hi
      rw [← hw1]
      apply Finset.single_le_sum (fun j hj ↦ hw j hj) hi
    have hw1' : ∑ i, (u : Set (Fin (n + 1))).indicator w i = 1 := by
      simpa [Finset.sum_indicator_subset _ u.subset_univ] using hw1
    rw [Finset.affineCombination_indicator_subset _ _ u.subset_univ,
      affineCombination_mem_closedInterior_iff hw1']
    intro i
    by_cases hi : i ∈ (u : Set (Fin (n + 1))) <;> aesop
  · obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype <|
      Set.mem_of_mem_of_subset h s.closedInterior_subset_affineSpan
    rw [affineCombination_mem_closedInterior_iff hw1] at h
    exact ⟨Finset.univ, w, fun i _ ↦ (h i).1, hw1, rfl⟩

end Affine.Simplex

