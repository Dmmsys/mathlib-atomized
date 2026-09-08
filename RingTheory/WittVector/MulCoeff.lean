/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.WittVector.Truncated

/-!
# Leading terms of Witt vector multiplication

The goal of this file is to study the leading terms of the formula for the `n+1`st coefficient
of a product of Witt vectors `x` and `y` over a ring of characteristic `p`.
We aim to isolate the `n+1`st coefficients of `x` and `y`, and express the rest of the product
in terms of a function of the lower coefficients.

For most of this file we work with terms of type `MvPolynomial (Fin 2 × ℕ) ℤ`.
We will eventually evaluate them in `k`, but first we must take care of a calculation
that needs to happen in characteristic 0.

## Main declarations

* `WittVector.nth_mul_coeff`: expresses the coefficient of a product of Witt vectors
  in terms of the previous coefficients of the multiplicands.

-/

@[expose] public section


noncomputable section

namespace WittVector

variable (p : ℕ) [hp : Fact p.Prime]
variable {k : Type*} [CommRing k]

local notation "𝕎" => WittVector p

local notation "𝕄" => MvPolynomial (Fin 2 × ℕ) ℤ

open Finset MvPolynomial

/--
```
(∑ i ∈ range n, (y.coeff i)^(p^(n-i)) * p^i.val) *
(∑ i ∈ range n, (y.coeff i)^(p^(n-i)) * p^i.val)
```
-/
/-
**WittVector.wittPolyProd** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：wittPolyProd (n : Nat) : 𝕄
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
```
(∑ i ∈ range n, (y.coeff i)^(p^(n-i)) * p^i.val) *
(∑ i ∈ range n, (y.coeff i)^(p^(n-i)) * p^i.val)
```
-/
def wittPolyProd (n : ℕ) : 𝕄 :=
  rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ n) *
    rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ n)
/-
**WittVector.wittPolyProd_vars** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：wittPolyProd_vars (n : Nat) : (wittPolyProd p n).vars subseteq univ ×ˢ ran
ge (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.wittPolyProd.eq_1`：∀ (p n : ℕ),   WittVector.wittPolyProd p n
 =     (MvPolynomial.rename (Prod.mk 0)) (wittPolynomial p ℤ n) * (MvPolynomial.
rename (Prod.mk 1)…
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
· 使用定理 `MvPolynomial.vars_mul`：vars_mul [DecidableEq σ] (φ ψ : MvPolynomial σ R)
 : (φ * ψ).vars subseteq φ.vars union ψ.vars
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用定理 `MvPolynomial.vars_rename`：vars_rename [DecidableEq τ] (f : σ -> τ) (φ : 
MvPolynomial σ R) : (rename f φ).vars subseteq φ.vars.image f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `wittPolynomial_vars`：wittPolynomial_vars [CharZero R] (n : Nat) : (wittP
olynomial p R n).vars = range (n + 1)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem wittPolyProd_vars (n : ℕ) : (wittPolyProd p n).vars ⊆ univ ×ˢ range (n + 1) := by
  rw [wittPolyProd]
  apply Subset.trans (vars_mul _ _)
  refine union_subset ?_ ?_ <;>
  · refine Subset.trans (vars_rename _ _) ?_
    simp [wittPolynomial_vars, image_subset_iff]

/-- The "remainder term" of `WittVector.wittPolyProd`. See `mul_polyOfInterest_aux2`. -/
/-
**WittVector.wittPolyProdRemainder** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：wittPolyProdRemainder (n : Nat) : 𝕄
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "remainder term" of `WittVector.wittPolyProd`. See `mul_polyOfInterest_aux2`
.
-/
def wittPolyProdRemainder (n : ℕ) : 𝕄 :=
  ∑ i ∈ range n, (p : 𝕄) ^ i * wittMul p i ^ p ^ (n - i)
/-
**WittVector.wittPolyProdRemainder_vars** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：wittPolyProdRemainder_vars (n : Nat) : (wittPolyProdRemainder p n).vars su
bseteq univ ×ˢ range n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.wittPolyProdRemainder.eq_1`：∀ (p : ℕ) [hp : Fact (Nat.Prime p
)] (n : ℕ),   WittVector.wittPolyProdRemainder p n = ∑ i ∈ Finset.range n, ↑p ^ 
i * WittVector.wittMul p i …
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
· 使用定理 `MvPolynomial.vars_sum_subset`：vars_sum_subset [DecidableEq σ] : (∑ i in 
t, φ i).vars subseteq Finset.biUnion t fun i => (φ i).vars
· 使用引理 `Finset.biUnion_subset`：biUnion_subset {s' : Finset β} : s.biUnion t subs
eteq s' ↔ forall x in s, t x subseteq s'
· 使用定理 `MvPolynomial.vars_mul`：vars_mul [DecidableEq σ] (φ ψ : MvPolynomial σ R)
 : (φ * ψ).vars subseteq φ.vars union ψ.vars
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用定理 `MvPolynomial.vars_pow`：vars_pow (φ : MvPolynomial σ R) (n : Nat) : (φ ^ 
n).vars subseteq φ.vars
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.vars_C`：vars_C : (C r : MvPolynomial σ R).vars = ∅
· 使用定理 `Finset.empty_subset`：empty_subset (s : Finset α) : ∅ subseteq s
· 使用定理 `WittVector.wittMul_vars`：wittMul_vars (n : Nat) : (wittMul p n).vars sub
seteq Finset.univ ×ˢ Finset.range (n + 1)
· 使用定理 `Finset.product_subset_product`：product_subset_product (hs : s subseteq s
') (ht : t subseteq t') : s ×ˢ t subseteq s' ×ˢ t'
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
theorem wittPolyProdRemainder_vars (n : ℕ) :
    (wittPolyProdRemainder p n).vars ⊆ univ ×ˢ range n := by
  rw [wittPolyProdRemainder]
  refine Subset.trans (vars_sum_subset _ _) ?_
  rw [biUnion_subset]
  intro x hx
  apply Subset.trans (vars_mul _ _)
  refine union_subset ?_ ?_
  · apply Subset.trans (vars_pow _ _)
    have : (p : 𝕄) = C (p : ℤ) := by simp only [Int.cast_natCast, eq_intCast]
    rw [this, vars_C]
    apply empty_subset
  · apply Subset.trans (vars_pow _ _)
    apply Subset.trans (wittMul_vars _ _)
    apply product_subset_product (Subset.refl _)
    simpa using hx

/-- `remainder p n` represents the remainder term from `mul_polyOfInterest_aux3`.
`wittPolyProd p (n+1)` will have variables up to `n+1`,
but `remainder` will only have variables up to `n`.
-/
/-
**WittVector.remainder** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：remainder (n : Nat) : 𝕄
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`remainder p n` represents the remainder term from `mul_polyOfInterest_aux3`.
`wittPolyProd p (n+1)` will have variables up to `n+1`,
but `remainder` will only have variables up to `n`.
-/
def remainder (n : ℕ) : 𝕄 :=
  (∑ x ∈ range (n + 1),
    (rename (Prod.mk 0)) ((monomial (Finsupp.single x (p ^ (n + 1 - x)))) ((p : ℤ) ^ x))) *
   ∑ x ∈ range (n + 1),
    (rename (Prod.mk 1)) ((monomial (Finsupp.single x (p ^ (n + 1 - x)))) ((p : ℤ) ^ x))
/-
**WittVector.remainder_vars** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：remainder_vars (n : Nat) : (remainder p n).vars subseteq univ ×ˢ range (n 
+ 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.remainder.eq_1`：∀ (p n : ℕ),   WittVector.remainder p n =    
 (∑ x ∈ Finset.range (n + 1),         (MvPolynomial.rename (Prod.mk 0)) ((MvPoly
nomial.monomial…
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
· 使用定理 `MvPolynomial.vars_mul`：vars_mul [DecidableEq σ] (φ ψ : MvPolynomial σ R)
 : (φ * ψ).vars subseteq φ.vars union ψ.vars
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用定理 `MvPolynomial.vars_sum_subset`：vars_sum_subset [DecidableEq σ] : (∑ i in 
t, φ i).vars subseteq Finset.biUnion t fun i => (φ i).vars
· 使用引理 `Finset.biUnion_subset`：biUnion_subset {s' : Finset β} : s.biUnion t subs
eteq s' ↔ forall x in s, t x subseteq s'
· 使用定理 `MvPolynomial.rename_monomial`：rename_monomial (f : σ -> τ) (d : σ ->₀ Na
t) (r : R) : rename f (monomial d r) = monomial (d.mapDomain f) r
· 使用定理 `MvPolynomial.vars_monomial`：vars_monomial (h : r != 0) : (monomial s r).
vars = s.support
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
-/
theorem remainder_vars (n : ℕ) : (remainder p n).vars ⊆ univ ×ˢ range (n + 1) := by
  rw [remainder]
  apply Subset.trans (vars_mul _ _)
  refine union_subset ?_ ?_ <;>
  · refine Subset.trans (vars_sum_subset _ _) ?_
    rw [biUnion_subset]
    intro x hx
    rw [rename_monomial, vars_monomial, Finsupp.mapDomain_single]
    · apply Subset.trans Finsupp.support_single_subset
      simpa using mem_range.mp hx
    · apply pow_ne_zero
      exact mod_cast hp.out.ne_zero

/-- This is the polynomial whose degree we want to get a handle on. -/
/-
**WittVector.polyOfInterest** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：polyOfInterest (n : Nat) : 𝕄
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the polynomial whose degree we want to get a handle on.
-/
def polyOfInterest (n : ℕ) : 𝕄 :=
  wittMul p (n + 1) + (p : 𝕄) ^ (n + 1) * X (0, n + 1) * X (1, n + 1) -
    X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ (n + 1)) -
    X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ (n + 1))
/-
**WittVector.mul_polyOfInterest_aux1** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：mul_polyOfInterest_aux1 (n : Nat) : ∑ i in range (n + 1), (p : 𝕄) ^ i * wi
ttMul p i ^ p ^ (n - i) = wittPolyProd p n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `Finsupp.support_eq_singleton`：support_eq_singleton {f : α ->₀ M} {a : α}
 : f.support = {a} ↔ f a != 0 ∧ f = single a (f a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MvPolynomial.bind₁_monomial`：bind₁_monomial (f : σ -> MvPolynomial τ R) 
(d : σ ->₀ Nat) (r : R) : bind₁ f (monomial d r) = C r * ∏ i in d.support, f i ^
 d i
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
（共 34 条，此处仅展示前 30 条）
-/
theorem mul_polyOfInterest_aux1 (n : ℕ) :
    ∑ i ∈ range (n + 1), (p : 𝕄) ^ i * wittMul p i ^ p ^ (n - i) = wittPolyProd p n := by
  simp only [wittPolyProd]
  convert! wittStructureInt_prop p (X (0 : Fin 2) * X 1) n using 1
  · simp only [wittPolynomial, wittMul]
    rw [map_sum]
    congr 1 with i
    congr 1
    have hsupp : (Finsupp.single i (p ^ (n - i))).support = {i} := by
      rw [Finsupp.support_eq_singleton]
      simp only [and_true, Finsupp.single_eq_same, Ne]
      exact pow_ne_zero _ hp.out.ne_zero
    simp only [bind₁_monomial, hsupp, Int.cast_natCast, prod_singleton, eq_intCast,
      Finsupp.single_eq_same, Int.cast_pow]
  · simp only [map_mul, bind₁_X_right]
/-
**WittVector.mul_polyOfInterest_aux2** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：mul_polyOfInterest_aux2 (n : Nat) : (p : 𝕄) ^ n * wittMul p n + wittPolyPr
odRemainder p n = wittPolyProd p n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `WittVector.mul_polyOfInterest_aux1`：mul_polyOfInterest_aux1 (n : Nat) : 
∑ i in range (n + 1), (p : 𝕄) ^ i * wittMul p i ^ p ^ (n - i) = wittPolyProd p n
-/
theorem mul_polyOfInterest_aux2 (n : ℕ) :
    (p : 𝕄) ^ n * wittMul p n + wittPolyProdRemainder p n = wittPolyProd p n := by
  convert! mul_polyOfInterest_aux1 p n
  rw [sum_range_succ, add_comm, Nat.sub_self, pow_zero, pow_one]
  rfl

-- We redeclare `p` here to locally discard the unneeded `p.Prime` hypothesis.
/-
**WittVector.mul_polyOfInterest_aux3** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：mul_polyOfInterest_aux3 (p n : Nat) : wittPolyProd p (n + 1) = -((p : 𝕄) ^
 (n + 1) * X (0, n + 1)) * ((p : 𝕄) ^ (n + 1) * X (1, n + 1)) + (p : 𝕄) ^ (n + 1
) * X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p Int (n + 1)) +
 (p : 𝕄) ^ (n + 1) * X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial
 p Int (n + 1)) + remainder p n
参数：p n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `WittVector.wittPolyProd.eq_1`：∀ (p n : ℕ),   WittVector.wittPolyProd p n
 =     (MvPolynomial.rename (Prod.mk 0)) (wittPolynomial p ℤ n) * (MvPolynomial.
rename (Prod.mk 1)…
· 使用定理 `wittPolynomial.eq_1`：∀ (p : ℕ) (R : Type u_1) [inst : CommRing R] (n : ℕ
),   wittPolynomial p R n = ∑ i ∈ Finset.range (n + 1), (MvPolynomial.monomial f
un₀ | i =…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.C_mul_X_pow_eq_monomial`：C_mul_X_pow_eq_monomial {s : σ} {a
 : R} {n : Nat} : C a * X s ^ n = monomial (Finsupp.single s n) a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `MvPolynomial.rename_C`：rename_C (f : σ -> τ) (r : R) : rename f (C r) = 
C r
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
（共 68 条，此处仅展示前 30 条）
-/
theorem mul_polyOfInterest_aux3 (p n : ℕ) : wittPolyProd p (n + 1) =
    -((p : 𝕄) ^ (n + 1) * X (0, n + 1)) * ((p : 𝕄) ^ (n + 1) * X (1, n + 1)) +
    (p : 𝕄) ^ (n + 1) * X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ (n + 1)) +
    (p : 𝕄) ^ (n + 1) * X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ (n + 1)) +
    remainder p n := by
  -- a useful auxiliary fact
  have mvpz : (p : 𝕄) ^ (n + 1) = MvPolynomial.C ((p : ℤ) ^ (n + 1)) := by norm_cast
  rw [wittPolyProd, wittPolynomial, map_sum, map_sum]
  conv_lhs =>
    arg 1
    rw [sum_range_succ, ← C_mul_X_pow_eq_monomial, tsub_self, pow_zero, pow_one, map_mul,
      rename_C, rename_X, ← mvpz]
  conv_lhs =>
    arg 2
    rw [sum_range_succ, ← C_mul_X_pow_eq_monomial, tsub_self, pow_zero, pow_one, map_mul,
      rename_C, rename_X, ← mvpz]
  conv_rhs =>
    enter [1, 1, 2, 2]
    rw [sum_range_succ, ← C_mul_X_pow_eq_monomial, tsub_self, pow_zero, pow_one, map_mul,
      rename_C, rename_X, ← mvpz]
  conv_rhs =>
    enter [1, 2, 2]
    rw [sum_range_succ, ← C_mul_X_pow_eq_monomial, tsub_self, pow_zero, pow_one, map_mul,
      rename_C, rename_X, ← mvpz]
  simp only [add_mul, mul_add]
  rw [add_comm _ (remainder p n)]
  simp only [add_assoc]
  apply congrArg (Add.add _)
  ring
/-
**WittVector.mul_polyOfInterest_aux4** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：mul_polyOfInterest_aux4 (n : Nat) : (p : 𝕄) ^ (n + 1) * wittMul p (n + 1) 
= -((p : 𝕄) ^ (n + 1) * X (0, n + 1)) * ((p : 𝕄) ^ (n + 1) * X (1, n + 1)) + (p 
: 𝕄) ^ (n + 1) * X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p I
nt (n + 1)) + (p : 𝕄) ^ (n + 1) * X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (w
ittPolynomial p Int (n + 1)) + (remainder p n - wittPolyProdRemainder p (n + 1))
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `WittVector.mul_polyOfInterest_aux2`：mul_polyOfInterest_aux2 (n : Nat) : 
(p : 𝕄) ^ n * wittMul p n + wittPolyProdRemainder p n = wittPolyProd p n
· 使用定理 `WittVector.mul_polyOfInterest_aux3`：mul_polyOfInterest_aux3 (p n : Nat) 
: wittPolyProd p (n + 1) = -((p : 𝕄) ^ (n + 1) * X (0, n + 1)) * ((p : 𝕄) ^ (n +
 1) * X (1, n + 1)) + (p…
-/
theorem mul_polyOfInterest_aux4 (n : ℕ) :
    (p : 𝕄) ^ (n + 1) * wittMul p (n + 1) =
    -((p : 𝕄) ^ (n + 1) * X (0, n + 1)) * ((p : 𝕄) ^ (n + 1) * X (1, n + 1)) +
    (p : 𝕄) ^ (n + 1) * X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ (n + 1)) +
    (p : 𝕄) ^ (n + 1) * X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ (n + 1)) +
    (remainder p n - wittPolyProdRemainder p (n + 1)) := by
  rw [← add_sub_assoc, eq_sub_iff_add_eq, mul_polyOfInterest_aux2]
  exact mul_polyOfInterest_aux3 _ _
/-
**WittVector.mul_polyOfInterest_aux5** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：mul_polyOfInterest_aux5 (n : Nat) : (p : 𝕄) ^ (n + 1) * polyOfInterest p n
 = remainder p n - wittPolyProdRemainder p (n + 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `WittVector.mul_polyOfInterest_aux4`：mul_polyOfInterest_aux4 (n : Nat) : 
(p : 𝕄) ^ (n + 1) * wittMul p (n + 1) = -((p : 𝕄) ^ (n + 1) * X (0, n + 1)) * ((
p : 𝕄) ^ (n + 1) * X (1,…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_one_cast_of_isNat`：∀ {R : Type u_1} [inst
 : CommSemiring R] (a : R) (b : ℕ), Mathlib.Meta.NormNum.IsNat b 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
（共 53 条，此处仅展示前 30 条）
-/
theorem mul_polyOfInterest_aux5 (n : ℕ) :
    (p : 𝕄) ^ (n + 1) * polyOfInterest p n = remainder p n - wittPolyProdRemainder p (n + 1) := by
  simp only [polyOfInterest, mul_sub, mul_add, sub_eq_iff_eq_add']
  rw [mul_polyOfInterest_aux4 p n]
  ring
/-
**WittVector.mul_polyOfInterest_vars** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：mul_polyOfInterest_vars (n : Nat) : ((p : 𝕄) ^ (n + 1) * polyOfInterest p 
n).vars subseteq univ ×ˢ range (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.mul_polyOfInterest_aux5`：mul_polyOfInterest_aux5 (n : Nat) : 
(p : 𝕄) ^ (n + 1) * polyOfInterest p n = remainder p n - wittPolyProdRemainder p
 (n + 1)
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
· 使用定理 `MvPolynomial.vars_sub_subset`：vars_sub_subset [DecidableEq σ] : (p - q).
vars subseteq p.vars union q.vars
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用定理 `WittVector.remainder_vars`：remainder_vars (n : Nat) : (remainder p n).va
rs subseteq univ ×ˢ range (n + 1)
· 使用定理 `WittVector.wittPolyProdRemainder_vars`：wittPolyProdRemainder_vars (n : N
at) : (wittPolyProdRemainder p n).vars subseteq univ ×ˢ range n
-/
theorem mul_polyOfInterest_vars (n : ℕ) :
    ((p : 𝕄) ^ (n + 1) * polyOfInterest p n).vars ⊆ univ ×ˢ range (n + 1) := by
  rw [mul_polyOfInterest_aux5]
  apply Subset.trans (vars_sub_subset _)
  refine union_subset ?_ ?_
  · apply remainder_vars
  · apply wittPolyProdRemainder_vars
/-
**WittVector.polyOfInterest_vars_eq** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：polyOfInterest_vars_eq (n : Nat) : (polyOfInterest p n).vars = ((p : 𝕄) ^ 
(n + 1) * (wittMul p (n + 1) + (p : 𝕄) ^ (n + 1) * X (0, n + 1) * X (1, n + 1) -
 X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p Int (n + 1)) - X 
(1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p Int (n + 1)))).vars
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `WittVector.polyOfInterest.eq_1`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)] (n :
 ℕ),   WittVector.polyOfInterest p n =     WittVector.wittMul p (n + 1) + ↑p ^ (
n + 1) * MvPolynomia…
· 使用定理 `MvPolynomial.vars_C_mul`：vars_C_mul (a : A) (ha : a != 0) (φ : MvPolynom
ial σ A) : (C a * φ : MvPolynomial σ A).vars = φ.vars
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem polyOfInterest_vars_eq (n : ℕ) : (polyOfInterest p n).vars =
    ((p : 𝕄) ^ (n + 1) * (wittMul p (n + 1) + (p : 𝕄) ^ (n + 1) * X (0, n + 1) * X (1, n + 1) -
      X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ (n + 1)) -
      X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ (n + 1)))).vars := by
  have : (p : 𝕄) ^ (n + 1) = C ((p : ℤ) ^ (n + 1)) := by norm_cast
  rw [polyOfInterest, this, vars_C_mul]
  apply pow_ne_zero
  exact mod_cast hp.out.ne_zero
/-
**WittVector.polyOfInterest_vars** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：polyOfInterest_vars (n : Nat) : (polyOfInterest p n).vars subseteq univ ×ˢ
 range (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.polyOfInterest_vars_eq`：polyOfInterest_vars_eq (n : Nat) : (p
olyOfInterest p n).vars = ((p : 𝕄) ^ (n + 1) * (wittMul p (n + 1) + (p : 𝕄) ^ (n
 + 1) * X (0, n + 1) * …
· 使用定理 `WittVector.mul_polyOfInterest_vars`：mul_polyOfInterest_vars (n : Nat) : 
((p : 𝕄) ^ (n + 1) * polyOfInterest p n).vars subseteq univ ×ˢ range (n + 1)
-/
theorem polyOfInterest_vars (n : ℕ) : (polyOfInterest p n).vars ⊆ univ ×ˢ range (n + 1) := by
  rw [polyOfInterest_vars_eq]; apply mul_polyOfInterest_vars
/-
**WittVector.peval_polyOfInterest** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：peval_polyOfInterest (n : Nat) (x y : 𝕎 k) : peval (polyOfInterest p n) ![
fun i => x.coeff i, fun i => y.coeff i] = (x * y).coeff (n + 1) + p ^ (n + 1) * 
x.coeff (n + 1) * y.coeff (n + 1) - y.coeff (n + 1) * ∑ i in range (n + 1 + 1), 
p ^ i * x.coeff i ^ p ^ (n + 1 - i) - x.coeff (n + 1) * ∑ i in range (n + 1 + 1)
, p ^ i * y.coeff i ^ p ^ (n + 1 - i)
参数：n : Nat；x y : 𝕎 k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `MvPolynomial.eval₂Hom_X'`：eval₂Hom_X' (f : R ->+* S₁) (g : σ -> S₁) (i :
 σ) : eval₂Hom f g (X i) = g i
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `wittPolynomial_eq_sum_C_mul_X_pow`：wittPolynomial_eq_sum_C_mul_X_pow (n 
: Nat) : wittPolynomial p R n = ∑ i in range (n + 1), C ((p : R) ^ i) * X i ^ p 
^ (n - i)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
（共 33 条，此处仅展示前 30 条）
-/
theorem peval_polyOfInterest (n : ℕ) (x y : 𝕎 k) :
    peval (polyOfInterest p n) ![fun i => x.coeff i, fun i => y.coeff i] =
    (x * y).coeff (n + 1) + p ^ (n + 1) * x.coeff (n + 1) * y.coeff (n + 1) -
      y.coeff (n + 1) * ∑ i ∈ range (n + 1 + 1), p ^ i * x.coeff i ^ p ^ (n + 1 - i) -
      x.coeff (n + 1) * ∑ i ∈ range (n + 1 + 1), p ^ i * y.coeff i ^ p ^ (n + 1 - i) := by
  simp only [polyOfInterest, peval,
    Function.uncurry_apply_pair, aeval_X, Matrix.cons_val_one, map_mul, Matrix.cons_val_zero,
    map_sub]
  rw [sub_sub, add_comm (_ * _), ← sub_sub]
  simp [wittPolynomial_eq_sum_C_mul_X_pow, aeval, mul_coeff, peval, map_natCast,
    map_add, map_pow, map_mul]

variable [CharP k p]

/-- The characteristic `p` version of `peval_polyOfInterest` -/
/-
**WittVector.peval_polyOfInterest'** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：peval_polyOfInterest' (n : Nat) (x y : 𝕎 k) : peval (polyOfInterest p n) !
[fun i => x.coeff i, fun i => y.coeff i] = (x * y).coeff (n + 1) - y.coeff (n + 
1) * x.coeff 0 ^ p ^ (n + 1) - x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1)
参数：n : Nat；x y : 𝕎 k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.peval_polyOfInterest`：peval_polyOfInterest (n : Nat) (x y : 𝕎
 k) : peval (polyOfInterest p n) ![fun i => x.coeff i, fun i => y.coeff i] = (x 
* y).coeff (n + 1) + …
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
The characteristic `p` version of `peval_polyOfInterest`
-/
theorem peval_polyOfInterest' (n : ℕ) (x y : 𝕎 k) :
    peval (polyOfInterest p n) ![fun i => x.coeff i, fun i => y.coeff i] =
      (x * y).coeff (n + 1) - y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) -
        x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) := by
  rw [peval_polyOfInterest]
  have : (p : k) = 0 := CharP.cast_eq_zero k p
  simp only [this, ne_eq, add_eq_zero, and_false, zero_pow, zero_mul, add_zero,
    not_false_eq_true, reduceCtorEq]
  have sum_zero_pow_mul_pow_p (y : 𝕎 k) : ∑ x ∈ range (n + 1 + 1),
      (0 : k) ^ x * y.coeff x ^ p ^ (n + 1 - x) = y.coeff 0 ^ p ^ (n + 1) := by
    rw [Finset.sum_eq_single_of_mem 0] <;> simp +contextual
  congr <;> apply sum_zero_pow_mul_pow_p

variable (k)
/-
**WittVector.nth_mul_coeff'** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：nth_mul_coeff' (n : Nat) : exists f : TruncatedWittVector p (n + 1) k -> T
runcatedWittVector p (n + 1) k -> k, forall x y : 𝕎 k, f (truncateFun (n + 1) x)
 (truncateFun (n + 1) y) = (x * y).coeff (n + 1) - y.coeff (n + 1) * x.coeff 0 ^
 p ^ (n + 1) - x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MvPolynomial.exists_restrict_to_vars`：exists_restrict_to_vars (R : Type*
) [CommRing R] {F : MvPolynomial σ Int} (hF : ↑F.vars subseteq s) : exists f : (
s -> R) -> R, forall x : σ…
· 使用定理 `WittVector.polyOfInterest_vars`：polyOfInterest_vars (n : Nat) : (polyOfI
nterest p n).vars subseteq univ ×ˢ range (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem nth_mul_coeff' (n : ℕ) :
    ∃ f : TruncatedWittVector p (n + 1) k → TruncatedWittVector p (n + 1) k → k,
    ∀ x y : 𝕎 k, f (truncateFun (n + 1) x) (truncateFun (n + 1) y) =
      (x * y).coeff (n + 1) - y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) -
        x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) := by
  simp only [← peval_polyOfInterest']
  obtain ⟨f₀, hf₀⟩ := exists_restrict_to_vars (s := SetLike.coe (univ ×ˢ range (n + 1))) k
    (polyOfInterest_vars p n)
  let f : TruncatedWittVector p (n + 1) k → TruncatedWittVector p (n + 1) k → k := by
    intro x y
    apply f₀
    rintro ⟨a, ha⟩
    apply Function.uncurry ![x, y]
    let S : Set (Fin 2 × ℕ) := { a | a.2 = n ∨ a.2 < n }
    have ha' : a ∈ S := by grind
    refine ⟨a.fst, ⟨a.snd, ?_⟩⟩
    obtain ⟨ha, ha⟩ := ha' <;> lia
  use f
  intro x y
  dsimp [f, peval]
  rw [← hf₀]
  congr
  ext a
  obtain ⟨a, ha⟩ := a
  obtain ⟨i, m⟩ := a
  fin_cases i <;> rfl -- surely this case split is not necessary
/-
**WittVector.nth_mul_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：nth_mul_coeff (n : Nat) : exists f : TruncatedWittVector p (n + 1) k -> Tr
uncatedWittVector p (n + 1) k -> k, forall x y : 𝕎 k, (x * y).coeff (n + 1) = x.
coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) + y.coeff (n + 1) * x.coeff 0 ^ p ^ (n +
 1) + f (truncateFun (n + 1) x) (truncateFun (n + 1) y)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.nth_mul_coeff'`：nth_mul_coeff' (n : Nat) : exists f : Truncat
edWittVector p (n + 1) k -> TruncatedWittVector p (n + 1) k -> k, forall x y : 𝕎
 k, f (truncate…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_one_cast_of_isNat`：∀ {R : Type u_1} [inst
 : CommSemiring R] (a : R) (b : ℕ), Mathlib.Meta.NormNum.IsNat b 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
（共 42 条，此处仅展示前 30 条）
-/
theorem nth_mul_coeff (n : ℕ) :
    ∃ f : TruncatedWittVector p (n + 1) k → TruncatedWittVector p (n + 1) k → k,
    ∀ x y : 𝕎 k, (x * y).coeff (n + 1) =
      x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) + y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) +
      f (truncateFun (n + 1) x) (truncateFun (n + 1) y) := by
  obtain ⟨f, hf⟩ := nth_mul_coeff' p k n
  use f
  intro x y
  rw [hf x y]
  ring

variable {k}

/--
Produces the "remainder function" of the `n+1`st coefficient, which does not depend on the `n+1`st
coefficients of the inputs. -/
/-
**WittVector.nthRemainder** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：nthRemainder (n : Nat) : (Fin (n + 1) -> k) -> (Fin (n + 1) -> k) -> k
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.nth_mul_coeff`：nth_mul_coeff (n : Nat) : exists f : Truncated
WittVector p (n + 1) k -> TruncatedWittVector p (n + 1) k -> k, forall x y : 𝕎 k
, (x * y).coef…

--- 原说明 ---
Produces the "remainder function" of the `n+1`st coefficient, which does not dep
end on the `n+1`st
coefficients of the inputs.
-/
def nthRemainder (n : ℕ) : (Fin (n + 1) → k) → (Fin (n + 1) → k) → k :=
  Classical.choose (nth_mul_coeff p k n)
/-
**WittVector.nthRemainder_spec** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：nthRemainder_spec (n : Nat) (x y : 𝕎 k) : (x * y).coeff (n + 1) = x.coeff 
(n + 1) * y.coeff 0 ^ p ^ (n + 1) + y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) + 
nthRemainder p n (truncateFun (n + 1) x) (truncateFun (n + 1) y)
参数：n : Nat；x y : 𝕎 k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `WittVector.nth_mul_coeff`：nth_mul_coeff (n : Nat) : exists f : Truncated
WittVector p (n + 1) k -> TruncatedWittVector p (n + 1) k -> k, forall x y : 𝕎 k
, (x * y).coef…
-/
theorem nthRemainder_spec (n : ℕ) (x y : 𝕎 k) : (x * y).coeff (n + 1) =
    x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) + y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) +
    nthRemainder p n (truncateFun (n + 1) x) (truncateFun (n + 1) y) :=
  Classical.choose_spec (nth_mul_coeff p k n) _ _

end WittVector

