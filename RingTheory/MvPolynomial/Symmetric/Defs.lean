/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang, Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# Symmetric Polynomials and Elementary Symmetric Polynomials

This file defines symmetric `MvPolynomial`s and the bases of elementary, complete homogeneous,
power sum, and monomial symmetric `MvPolynomial`s. We also prove some basic facts about them.

## Main declarations

* `MvPolynomial.IsSymmetric`

* `MvPolynomial.symmetricSubalgebra`

* `MvPolynomial.esymm`

* `MvPolynomial.hsymm`

* `MvPolynomial.psum`

* `MvPolynomial.msymm`

## Notation

+ `esymm σ R n` is the `n`th elementary symmetric polynomial in `MvPolynomial σ R`.

+ `hsymm σ R n` is the `n`th complete homogeneous symmetric polynomial in `MvPolynomial σ R`.

+ `psum σ R n` is the degree-`n` power sum in `MvPolynomial σ R`, i.e. the sum of monomials
  `(X i)^n` over `i ∈ σ`.

+ `msymm σ R μ` is the monomial symmetric polynomial whose exponents set are the parts
  of `μ ⊢ n` in `MvPolynomial σ R`.

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R S : Type*` `[CommSemiring R]` `[CommSemiring S]` (the coefficients)

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `φ ψ : MvPolynomial σ R`

-/

@[expose] public section


open Equiv (Perm)

noncomputable section

namespace Multiset

variable {R : Type*} [CommSemiring R]

/-- The `n`th elementary symmetric function evaluated at the elements of `s` -/
/-
**Multiset.esymm** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：esymm (s : Multiset R) (n : Nat) : R
参数：s : Multiset R；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th elementary symmetric function evaluated at the elements of `s`
-/
def esymm (s : Multiset R) (n : ℕ) : R :=
  ((s.powersetCard n).map Multiset.prod).sum
/-
**Multiset._root_.Finset.esymm_map_val** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.esymm_map_val {σ} (f : σ → R) (s : Finset σ) (n : ℕ) :
    (s.val.map f).esymm n = (s.powersetCard n).sum fun t => t.prod f := by
  simp only [esymm, powersetCard_map, ← Finset.map_val_val_powersetCard, map_map]
  simp only [Function.comp_apply, Finset.prod_map_val, Finset.sum_map_val]
/-
**Multiset.pow_smul_esymm** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：pow_smul_esymm {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTowe
r S R R] [SMulCommClass S R R] (s : S) (n : Nat) (m : Multiset R) : s ^ n • m.es
ymm n = (m.map (s • ·)).esymm n
参数：s : S；n : Nat；m : Multiset R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.esymm.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (s : Multi
set R) (n : ℕ),   s.esymm n = (Multiset.map Multiset.prod (Multiset.powersetCard
 n s)).su…
· 使用定理 `Multiset.smul_sum`：Multiset.smul_sum {s : Multiset N} : r • s.sum = (s.m
ap (r • ·)).sum
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_powersetCard`：mem_powersetCard {n : Nat} {s t : Multiset α}
 : s in powersetCard n t ↔ s <= t ∧ card s = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.smul_prod`：smul_prod [Monoid M] [CommMonoid N] [MulAction M N] 
[IsScalarTower M N N] [SMulCommClass M N N] (s : Multiset N) (b : M) : b ^ card 
s • s.pr…
· 使用定理 `Multiset.powersetCard_map`：powersetCard_map {β : Type*} (f : α -> β) (n 
: Nat) (s : Multiset α) : powersetCard n (s.map f) = (powersetCard n s).map (map
 f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pow_smul_esymm {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R]
    [SMulCommClass S R R] (s : S) (n : ℕ) (m : Multiset R) :
    s ^ n • m.esymm n = (m.map (s • ·)).esymm n := by
  rw [esymm, smul_sum, map_map]
  trans ((powersetCard n m).map (fun x : Multiset R ↦ s ^ card x • x.prod)).sum
  · refine congr_arg _ (map_congr rfl (fun x hx ↦ ?_))
    rw [Function.comp_apply, (mem_powersetCard.1 hx).2]
  · simp_rw [smul_prod, esymm, powersetCard_map, map_map, Function.comp_def]

-- TODO: `Multiset.insert_eq_cons` being simp means that `esymm {x, y}` is not simp normal form
/-
**Multiset.esymm_pair_one** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (x y : R), (x ::ₘ {y}).esymm 1 = 
x + y
参数：x y : R；x ::ₘ {y}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powersetCard_cons`：powersetCard_cons (n : Nat) (a : α) (s) : po
wersetCard (n + 1) (a ::ₘ s) = powersetCard (n + 1) s + map (cons a) (powersetCa
rd n s)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Multiset.powersetCard_one`：powersetCard_one (s : Multiset α) : powersetC
ard 1 s = s.map singleton
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.powersetCard_zero_left`：powersetCard_zero_left (s : Multiset α)
 : powersetCard 0 s = {0}
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `Multiset.sum_singleton`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M
), {a}.sum = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma esymm_pair_one (x y : R) :
    esymm (x ::ₘ {y}) 1 = x + y := by
  simp [esymm, powersetCard_one, add_comm]
/-
**Multiset.esymm_pair_two** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (x y : R), (x ::ₘ {y}).esymm 2 = 
x * y
参数：x y : R；x ::ₘ {y}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.powersetCard_cons`：powersetCard_cons (n : Nat) (a : α) (s) : po
wersetCard (n + 1) (a ::ₘ s) = powersetCard (n + 1) s + map (cons a) (powersetCa
rd n s)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.powersetCard_eq_empty`：powersetCard_eq_empty {α : Type*} (n : N
at) {s : Multiset α} (h : card s < n) : powersetCard n s = 0
· 使用定理 `Multiset.card_singleton`：card_singleton (a : α) : card ({a} : Multiset α
) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Multiset.powersetCard_one`：powersetCard_one (s : Multiset α) : powersetC
ard 1 s = s.map singleton
· 使用定理 `Multiset.zero_add`：∀ {α : Type u_1} (s : Multiset α), 0 + s = s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `Multiset.sum_singleton`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M
), {a}.sum = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma esymm_pair_two (x y : R) :
    esymm (x ::ₘ {y}) 2 = x * y := by
  simp [esymm, powersetCard_one]

end Multiset

namespace MvPolynomial

variable {σ τ : Type*} {R S : Type*}

/-- A `MvPolynomial φ` is symmetric if it is invariant under
permutations of its variables by the `rename` operation -/
/-
**MvPolynomial.IsSymmetric** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：IsSymmetric [CommSemiring R] (φ : MvPolynomial σ R) : Prop
参数：φ : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `MvPolynomial φ` is symmetric if it is invariant under
permutations of its variables by the `rename` operation
-/
def IsSymmetric [CommSemiring R] (φ : MvPolynomial σ R) : Prop :=
  ∀ e : Perm σ, rename e φ = φ

/-- The subalgebra of symmetric `MvPolynomial`s. -/
/-
**MvPolynomial.symmetricSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：symmetricSubalgebra (σ R : Type*) [CommSemiring R] : Subalgebra R (MvPolyn
omial σ R) where carrier
参数：σ R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subalgebra of symmetric `MvPolynomial`s.
-/
def symmetricSubalgebra (σ R : Type*) [CommSemiring R] : Subalgebra R (MvPolynomial σ R) where
  carrier := Set.ofPred IsSymmetric
  algebraMap_mem' r e := rename_C e r
  mul_mem' ha hb e := by rw [map_mul, ha, hb]
  add_mem' ha hb e := by rw [map_add, ha, hb]

@[simp]
/-
**MvPolynomial.mem_symmetricSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mem_symmetricSubalgebra [CommSemiring R] (p : MvPolynomial σ R) : p in sym
metricSubalgebra σ R ↔ p.IsSymmetric
参数：p : MvPolynomial σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_symmetricSubalgebra [CommSemiring R] (p : MvPolynomial σ R) :
    p ∈ symmetricSubalgebra σ R ↔ p.IsSymmetric :=
  Iff.rfl

namespace IsSymmetric

section CommSemiring

variable [CommSemiring R] [CommSemiring S] {φ ψ : MvPolynomial σ R}

@[simp]
/-
**MvPolynomial.IsSymmetric.C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsSymmetric
`。
形式化陈述：C (r : R) : IsSymmetric (C r : MvPolynomial σ R)
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
-/
theorem C (r : R) : IsSymmetric (C r : MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).algebraMap_mem r

@[simp]
/-
**MvPolynomial.IsSymmetric.zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsSymmet
ric`。
形式化陈述：zero : IsSymmetric (0 : MvPolynomial σ R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.zero_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   0 ∈ S
-/
theorem zero : IsSymmetric (0 : MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).zero_mem

@[simp]
/-
**MvPolynomial.IsSymmetric.one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsSymmetr
ic`。
形式化陈述：one : IsSymmetric (1 : MvPolynomial σ R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.one_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   1 ∈ S
-/
theorem one : IsSymmetric (1 : MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).one_mem
/-
**MvPolynomial.IsSymmetric.add** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsSymmetr
ic`。
形式化陈述：add (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ + ψ)
参数：hφ : IsSymmetric φ；hψ : IsSymmetric ψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.add_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
-/
theorem add (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ + ψ) :=
  (symmetricSubalgebra σ R).add_mem hφ hψ
/-
**MvPolynomial.IsSymmetric.mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsSymmetr
ic`。
形式化陈述：mul (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ * ψ)
参数：hφ : IsSymmetric φ；hψ : IsSymmetric ψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
-/
theorem mul (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ * ψ) :=
  (symmetricSubalgebra σ R).mul_mem hφ hψ
/-
**MvPolynomial.IsSymmetric.smul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsSymmet
ric`。
形式化陈述：smul (r : R) (hφ : IsSymmetric φ) : IsSymmetric (r • φ)
参数：r : R；hφ : IsSymmetric φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.smul_mem`：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S
-/
theorem smul (r : R) (hφ : IsSymmetric φ) : IsSymmetric (r • φ) :=
  (symmetricSubalgebra σ R).smul_mem hφ r

@[simp]
/-
**MvPolynomial.IsSymmetric.map** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsSymmetr
ic`。
形式化陈述：map (hφ : IsSymmetric φ) (f : R ->+* S) : IsSymmetric (map f φ)
参数：hφ : IsSymmetric φ；f : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.map_rename`：map_rename (f : R ->+* S) (g : σ -> τ) (p : MvP
olynomial σ R) : map f (rename g p) = rename g (map f p)
-/
theorem map (hφ : IsSymmetric φ) (f : R →+* S) : IsSymmetric (map f φ) := fun e => by
  rw [← map_rename, hφ]
/-
**MvPolynomial.IsSymmetric.rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsSymm
etric`。
形式化陈述：∀ {σ : Type u_1} {τ : Type u_2} {R : Type u_3} [inst : CommSemiring R] {φ 
: MvPolynomial σ R},   φ.IsSymmetric → ∀ (e : σ ≃ τ), ((MvPolynomial.rename ⇑e) 
φ).IsSymmetric
参数：e : σ ≃ τ；(MvPolynomial.rename ⇑e) φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.rename_injective`：rename_injective (f : σ -> τ) (hf : Funct
ion.Injective f) : Function.Injective (rename f : MvPolynomial σ R -> MvPolynomi
al τ R)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.rename_rename`：rename_rename (f : σ -> τ) (g : τ -> α) (p :
 MvPolynomial σ R) : rename g (rename f p) = rename (g ∘ f) p
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.self_trans_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.trans 
e.symm = Equiv.refl α
· 使用引理 `MvPolynomial.rename_id_apply`：rename_id_apply (p : MvPolynomial σ R) : r
ename id p = p
-/
protected theorem rename (hφ : φ.IsSymmetric) (e : σ ≃ τ) : (rename e φ).IsSymmetric := fun _ => by
  apply rename_injective _ e.symm.injective
  simp_rw [rename_rename, ← Equiv.coe_trans, Equiv.self_trans_symm, Equiv.coe_refl, rename_id_apply]
  rw [hφ]

@[simp]
/-
**MvPolynomial.IsSymmetric._root_.MvPolynomial.isSymmetric_rename** 是 Mathlib 中的
一个定理，位于命名空间 `MvPolynomial.IsSymmetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MvPolynomial.isSymmetric_rename {e : σ ≃ τ} :
    (MvPolynomial.rename e φ).IsSymmetric ↔ φ.IsSymmetric :=
  ⟨fun h => by simpa using (IsSymmetric.rename (R := R) h e.symm), (IsSymmetric.rename · e)⟩

end CommSemiring

section CommRing

variable [CommRing R] {φ ψ : MvPolynomial σ R}

/-
**MvPolynomial.IsSymmetric.neg** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsSymmetr
ic`。
形式化陈述：neg (hφ : IsSymmetric φ) : IsSymmetric (-φ)
参数：hφ : IsSymmetric φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.neg_mem`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] (S : Subalgebra R A) {x : A},   x ∈ S → -x 
∈ S
-/
theorem neg (hφ : IsSymmetric φ) : IsSymmetric (-φ) :=
  (symmetricSubalgebra σ R).neg_mem hφ
/-
**MvPolynomial.IsSymmetric.sub** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial.IsSymmetr
ic`。
形式化陈述：sub (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ - ψ)
参数：hφ : IsSymmetric φ；hψ : IsSymmetric ψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.sub_mem`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] (S : Subalgebra R A) {x y : A},   x ∈ S → y
 ∈ S → x…
-/
theorem sub (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ - ψ) :=
  (symmetricSubalgebra σ R).sub_mem hφ hψ

end CommRing

end IsSymmetric

set_option backward.isDefEq.respectTransparency false in
/-- `MvPolynomial.rename` induces an isomorphism between the symmetric subalgebras. -/
@[simps! apply_coe symm_apply_coe]
/-
**MvPolynomial.renameSymmetricSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial
`。
形式化陈述：renameSymmetricSubalgebra [CommSemiring R] (e : σ ≃ τ) : symmetricSubalgeb
ra σ R ≃ₐ[R] symmetricSubalgebra τ R
参数：e : σ ≃ τ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`MvPolynomial.rename` induces an isomorphism between the symmetric subalgebras.
-/
def renameSymmetricSubalgebra [CommSemiring R] (e : σ ≃ τ) :
    symmetricSubalgebra σ R ≃ₐ[R] symmetricSubalgebra τ R :=
  AlgEquiv.ofAlgHom
    (((rename e).comp (symmetricSubalgebra σ R).val).codRestrict _ <| fun x => x.2.rename e)
    (((rename e.symm).comp <| Subalgebra.val _).codRestrict _ <| fun x => x.2.rename e.symm)
    (AlgHom.ext <| fun p => Subtype.ext <| by simp)
    (AlgHom.ext <| fun p => Subtype.ext <| by simp)

variable (σ R : Type*) [CommSemiring R] [CommSemiring S] [Fintype σ] [Fintype τ]

section ElementarySymmetric

open Finset

/-- The `n`th elementary symmetric `MvPolynomial σ R`.
It is the sum over all the degree n squarefree monomials in `MvPolynomial σ R`. -/
/-
**MvPolynomial.esymm** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：esymm (n : Nat) : MvPolynomial σ R
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th elementary symmetric `MvPolynomial σ R`.
It is the sum over all the degree n squarefree monomials in `MvPolynomial σ R`.
-/
def esymm (n : ℕ) : MvPolynomial σ R :=
  ∑ t ∈ powersetCard n univ, ∏ i ∈ t, X i

/--
`esymmPart` is the product of the symmetric polynomials `esymm μᵢ`,
where `μ = (μ₁, μ₂, ...)` is a partition.
-/
/-
**MvPolynomial.esymmPart** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：esymmPart {n : Nat} (μ : n.Partition) : MvPolynomial σ R
参数：μ : n.Partition。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`esymmPart` is the product of the symmetric polynomials `esymm μᵢ`,
where `μ = (μ₁, μ₂, ...)` is a partition.
-/
def esymmPart {n : ℕ} (μ : n.Partition) : MvPolynomial σ R := (μ.parts.map (esymm σ R)).prod

/-- The `n`th elementary symmetric `MvPolynomial σ R` is obtained by evaluating the
`n`th elementary symmetric at the `Multiset` of the monomials -/
/-
**MvPolynomial.esymm_eq_multiset_esymm** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：esymm_eq_multiset_esymm : esymm σ R = (univ.val.map X).esymm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.esymm_map_val`：∀ {R : Type u_1} [inst : CommSemiring R] {σ : Type
 u_2} (f : σ → R) (s : Finset σ) (n : ℕ),   (Multiset.map f s.val).esymm n = ∑ t
 ∈ Finset.…

--- 原说明 ---
The `n`th elementary symmetric `MvPolynomial σ R` is obtained by evaluating the
`n`th elementary symmetric at the `Multiset` of the monomials
-/
theorem esymm_eq_multiset_esymm : esymm σ R = (univ.val.map X).esymm := by
  exact funext fun n => (esymm_map_val X _ n).symm
/-
**MvPolynomial.aeval_esymm_eq_multiset_esymm** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyno
mial`。
形式化陈述：aeval_esymm_eq_multiset_esymm [Algebra R S] (n : Nat) (f : σ -> S) : aeval
 f (esymm σ R n) = (univ.val.map f).esymm n
参数：n : Nat；f : σ -> S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_sum`：aeval_sum {ι : Type*} (s : Finset ι) (φ : ι -> M
vPolynomial σ R) : aeval f (∑ i in s, φ i) = ∑ i in s, aeval f (φ i)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.aeval_prod`：aeval_prod {ι : Type*} (s : Finset ι) (φ : ι ->
 MvPolynomial σ R) : aeval f (∏ i in s, φ i) = ∏ i in s, aeval f (φ i)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.esymm_map_val`：∀ {R : Type u_1} [inst : CommSemiring R] {σ : Type
 u_2} (f : σ → R) (s : Finset σ) (n : ℕ),   (Multiset.map f s.val).esymm n = ∑ t
 ∈ Finset.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aeval_esymm_eq_multiset_esymm [Algebra R S] (n : ℕ) (f : σ → S) :
    aeval f (esymm σ R n) = (univ.val.map f).esymm n := by
  simp_rw [esymm, aeval_sum, aeval_prod, aeval_X, esymm_map_val]

/-- We can define `esymm σ R n` by summing over a subtype instead of over `powerset_len`. -/
/-
**MvPolynomial.esymm_eq_sum_subtype** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：esymm_eq_sum_subtype (n : Nat) : esymm σ R n = ∑ t : {s : Finset σ // #s =
 n}, ∏ i in (t : Finset σ), X i
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_subtype`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] {p : ι → Prop} {F : Fintype (Subtype p)} (s : Finset ι),   (∀ (x : ι), x ∈ 
s ↔ p x)…
· 使用引理 `Finset.mem_powersetCard_univ`：mem_powersetCard_univ : s in powersetCard 
k (univ : Finset α) ↔ #s = k

--- 原说明 ---
We can define `esymm σ R n` by summing over a subtype instead of over `powerset_
len`.
-/
theorem esymm_eq_sum_subtype (n : ℕ) :
    esymm σ R n = ∑ t : {s : Finset σ // #s = n}, ∏ i ∈ (t : Finset σ), X i :=
  sum_subtype _ (fun _ => mem_powersetCard_univ) _

/-- We can define `esymm σ R n` as a sum over explicit monomials -/
/-
**MvPolynomial.esymm_eq_sum_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：esymm_eq_sum_monomial (n : Nat) : esymm σ R n = ∑ t in powersetCard n univ
, monomial (∑ i in t, Finsupp.single i 1) 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.monomial_sum_one`：monomial_sum_one {α : Type*} (s : Finset 
α) (f : α -> σ ->₀ Nat) : (monomial (∑ i in s, f i) 1 : MvPolynomial σ R) = ∏ i 
in s, monomial (f i…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
We can define `esymm σ R n` as a sum over explicit monomials
-/
theorem esymm_eq_sum_monomial (n : ℕ) :
    esymm σ R n = ∑ t ∈ powersetCard n univ, monomial (∑ i ∈ t, Finsupp.single i 1) 1 := by
  simp_rw [monomial_sum_one, esymm, ← X_pow_eq_monomial, pow_one]

@[simp]
/-
**MvPolynomial.esymm_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：esymm_zero : esymm σ R 0 = 1
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
· 使用定理 `Finset.powersetCard_zero`：powersetCard_zero (s : Finset α) : s.powersetC
ard 0 = {∅}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem esymm_zero : esymm σ R 0 = 1 := by
  simp only [esymm, powersetCard_zero, sum_singleton, prod_empty]

@[simp]
/-
**MvPolynomial.esymm_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：esymm_one : esymm σ R 1 = ∑ i, X i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.singleton_injective`：singleton_injective : Injective (singleton :
 α -> Finset α)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.powersetCard_one`：powersetCard_one (s : Finset α) : s.powersetCar
d 1 = s.map ⟨_, Finset.singleton_injective⟩
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem esymm_one : esymm σ R 1 = ∑ i, X i := by simp [esymm, powersetCard_one]
/-
**MvPolynomial.esymmPart_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：esymmPart_zero : esymmPart σ R (.indiscrete 0) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Nat.Partition.partition_zero_parts`：∀ (p : Nat.Partition 0), p.parts = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem esymmPart_zero : esymmPart σ R (.indiscrete 0) = 1 := by simp [esymmPart]

@[simp]
/-
**MvPolynomial.esymmPart_indiscrete** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：esymmPart_indiscrete (n : Nat) : esymmPart σ R (.indiscrete n) = esymm σ R
 n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Nat.Partition.partition_zero_parts`：∀ (p : Nat.Partition 0), p.parts = 0
· 使用定理 `MvPolynomial.esymm_zero`：esymm_zero : esymm σ R 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.Partition.indiscrete_parts`：∀ {n : ℕ}, n ≠ 0 → (Nat.Partition.indisc
rete n).parts = {n}
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
-/
theorem esymmPart_indiscrete (n : ℕ) : esymmPart σ R (.indiscrete n) = esymm σ R n := by
  cases n <;> simp [esymmPart]
/-
**MvPolynomial.map_esymm** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_esymm (n : Nat) (f : R ->+* S) : map f (esymm σ R n) = esymm σ S n
参数：n : Nat；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_esymm (n : ℕ) (f : R →+* S) : map f (esymm σ R n) = esymm σ S n := by
  simp_rw [esymm, map_sum, map_prod, map_X]
/-
**MvPolynomial.rename_esymm** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_esymm (n : Nat) (e : σ ≃ τ) : rename e (esymm σ R n) = esymm τ R n
参数：n : Nat；e : σ ≃ τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.powersetCard_map`：powersetCard_map {β : Type*} (f : α ↪ β) (n : N
at) (s : Finset α) : powersetCard n (s.map f) = (powersetCard n s).map (mapEmbed
ding f).toEmb…
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `Finset.mapEmbedding_apply`：mapEmbedding_apply : mapEmbedding f s = map f
 s
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Finset.map_univ_equiv`：map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map
 f.toEmbedding = univ
-/
theorem rename_esymm (n : ℕ) (e : σ ≃ τ) : rename e (esymm σ R n) = esymm τ R n :=
  calc
    rename e (esymm σ R n) = ∑ x ∈ powersetCard n univ, ∏ i ∈ x, X (e i) := by
      simp_rw [esymm, map_sum, map_prod, rename_X]
    _ = ∑ t ∈ powersetCard n (univ.map e.toEmbedding), ∏ i ∈ t, X i := by
      simp [powersetCard_map, -map_univ_equiv, (mapEmbedding_apply)]
    _ = ∑ t ∈ powersetCard n univ, ∏ i ∈ t, X i := by rw [map_univ_equiv]
/-
**MvPolynomial.esymm_isSymmetric** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：esymm_isSymmetric (n : Nat) : IsSymmetric (esymm σ R n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.rename_esymm`：rename_esymm (n : Nat) (e : σ ≃ τ) : rename e
 (esymm σ R n) = esymm τ R n
-/
theorem esymm_isSymmetric (n : ℕ) : IsSymmetric (esymm σ R n) := by
  intro
  rw [rename_esymm]
/-
**MvPolynomial.support_esymm''** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_esymm'' [DecidableEq σ] [Nontrivial R] (n : Nat) : (esymm σ R n).s
upport = (powersetCard n (univ : Finset σ)).biUnion fun t => (Finsupp.single (∑ 
i in t, Finsupp.single i 1) (1 : R)).support
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.esymm_eq_sum_monomial`：esymm_eq_sum_monomial (n : Nat) : es
ymm σ R n = ∑ t in powersetCard n univ, monomial (∑ i in t, Finsupp.single i 1) 
1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddMonoidAlgebra.coeff_sum`：∀ {R : Type u_1} {M : Type u_4} {ι : Type u_
7} [inst : Semiring R] (s : Finset ι) (f : ι → AddMonoidAlgebra R M),   (∑ i ∈ s
, f i).coeff = ∑…
· 使用定理 `Finsupp.support_sum_eq_biUnion`：support_sum_eq_biUnion {α : Type*} {ι : 
Type*} {M : Type*} [DecidableEq α] [AddCommMonoid M] {g : ι -> α ->₀ M} (s : Fin
set ι) (h : forall i…
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Finset.biUnion_singleton_eq_self`：biUnion_singleton_eq_self [DecidableEq
 α] : s.biUnion (singleton : α -> Finset α) = s
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem support_esymm'' [DecidableEq σ] [Nontrivial R] (n : ℕ) :
    (esymm σ R n).support =
      (powersetCard n (univ : Finset σ)).biUnion fun t =>
        (Finsupp.single (∑ i ∈ t, Finsupp.single i 1) (1 : R)).support := by
  rw [esymm_eq_sum_monomial]
  simp only [← single_eq_monomial]
  simp only [support, MvPolynomial, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single]
  refine Finsupp.support_sum_eq_biUnion _ fun s t hst ↦ ?_
  rw [disjoint_left, Finsupp.support_single _ one_ne_zero]
  rw [Finsupp.support_single _ one_ne_zero]
  simp only [mem_singleton]
  rintro a h rfl
  have := congr_arg Finsupp.support h
  rw [Finsupp.support_sum_eq_biUnion _ (by simp), Finsupp.support_sum_eq_biUnion _ (by simp)]
    at this
  simp_all
/-
**MvPolynomial.support_esymm'** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_esymm' [DecidableEq σ] [Nontrivial R] (n : Nat) : (esymm σ R n).su
pport = (powersetCard n (univ : Finset σ)).biUnion fun t => {∑ i in t, Finsupp.s
ingle i 1}
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.support_esymm''`：support_esymm'' [DecidableEq σ] [Nontrivia
l R] (n : Nat) : (esymm σ R n).support = (powersetCard n (univ : Finset σ)).biUn
ion fun t => (Fins…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem support_esymm' [DecidableEq σ] [Nontrivial R] (n : ℕ) : (esymm σ R n).support =
    (powersetCard n (univ : Finset σ)).biUnion fun t => {∑ i ∈ t, Finsupp.single i 1} := by
  rw [support_esymm'']
  congr
  funext
  exact Finsupp.support_single _ one_ne_zero
/-
**MvPolynomial.support_esymm** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_esymm [DecidableEq σ] [Nontrivial R] (n : Nat) : (esymm σ R n).sup
port = (powersetCard n (univ : Finset σ)).image fun t => ∑ i in t, Finsupp.singl
e i 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.support_esymm'`：support_esymm' [DecidableEq σ] [Nontrivial 
R] (n : Nat) : (esymm σ R n).support = (powersetCard n (univ : Finset σ)).biUnio
n fun t => {∑ i i…
· 使用定理 `Finset.biUnion_singleton`：biUnion_singleton {f : α -> β} : (s.biUnion fu
n a => {f a}) = s.image f
-/
theorem support_esymm [DecidableEq σ] [Nontrivial R] (n : ℕ) : (esymm σ R n).support =
    (powersetCard n (univ : Finset σ)).image fun t => ∑ i ∈ t, Finsupp.single i 1 := by
  rw [support_esymm']
  exact biUnion_singleton
/-
**MvPolynomial.degrees_esymm** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_esymm [Nontrivial R] {n : Nat} (hpos : 0 < n) (hn : n <= Fintype.c
ard σ) : (esymm σ R n).degrees = (univ : Finset σ).val
参数：hpos : 0 < n；hn : n <= Fintype.card σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.toMultiset_single`：toMultiset_single (a : α) (n : Nat) : toMulti
set (single a n) = n • {a}
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.sum_multiset_singleton`：sum_multiset_singleton (s : Finset ι) : ∑
 a in s, {a} = s.val
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.degrees_def`：degrees_def [DecidableEq σ] (p : MvPolynomial 
σ R) : p.degrees = p.support.sup fun s : σ ->₀ Nat => Finsupp.toMultiset s
· 使用定理 `MvPolynomial.support_esymm`：support_esymm [DecidableEq σ] [Nontrivial R]
 (n : Nat) : (esymm σ R n).support = (powersetCard n (univ : Finset σ)).image fu
n t => ∑ i in t,…
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `Finset.apply_sup_eq_sup_comp`：apply_sup_eq_sup_comp [SemilatticeSup γ] [
OrderBot γ] {s : Finset β} {f : β -> α} (g : α -> γ) (g_sup : forall x y, g (x ⊔
 y) = g x ⊔ g y) (…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.union_val`：union_val (s t : Finset α) : (s union t).1 = s.1 union
 t.1
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finset.powersetCard_sup`：powersetCard_sup [DecidableEq α] (u : Finset α)
 (n : Nat) (hn : n < u.card) : (powersetCard n.succ u).sup id = u
· 使用定理 `Nat.lt_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n < m
-/
theorem degrees_esymm [Nontrivial R] {n : ℕ} (hpos : 0 < n) (hn : n ≤ Fintype.card σ) :
    (esymm σ R n).degrees = (univ : Finset σ).val := by
  classical
    have :
      (Finsupp.toMultiset ∘ fun t : Finset σ => ∑ i ∈ t, Finsupp.single i 1) = val := by
      funext
      simp
    rw [degrees_def, support_esymm, sup_image, this]
    have : ((powersetCard n univ).sup (fun (x : Finset σ) => x)).val
        = sup (powersetCard n univ) val := by
      refine apply_sup_eq_sup_comp _ ?_ ?_ <;> simp
    rw [← this]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    simpa using! powersetCard_sup _ _ (Nat.lt_of_succ_le hn)

end ElementarySymmetric

section CompleteHomogeneousSymmetric

open Finset Multiset Sym

variable [DecidableEq σ] [DecidableEq τ]

/-- The `n`th complete homogeneous symmetric `MvPolynomial σ R`.
It is the sum over all the degree n monomials in `MvPolynomial σ R`. -/
/-
**MvPolynomial.hsymm** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：hsymm (n : Nat) : MvPolynomial σ R
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th complete homogeneous symmetric `MvPolynomial σ R`.
It is the sum over all the degree n monomials in `MvPolynomial σ R`.
-/
def hsymm (n : ℕ) : MvPolynomial σ R := ∑ s : Sym σ n, (s.1.map X).prod

/-- `hsymmPart` is the product of the symmetric polynomials `hsymm μᵢ`,
where `μ = (μ₁, μ₂, ...)` is a partition. -/
/-
**MvPolynomial.hsymmPart** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：hsymmPart {n : Nat} (μ : n.Partition) : MvPolynomial σ R
参数：μ : n.Partition。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`hsymmPart` is the product of the symmetric polynomials `hsymm μᵢ`,
where `μ = (μ₁, μ₂, ...)` is a partition.
-/
def hsymmPart {n : ℕ} (μ : n.Partition) : MvPolynomial σ R := (μ.parts.map (hsymm σ R)).prod

@[simp]
/-
**MvPolynomial.hsymm_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：hsymm_zero : hsymm σ R 0 = 1
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
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Sym.eq_nil_of_card_zero`：eq_nil_of_card_zero (s : Sym α 0) : s = nil
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hsymm_zero : hsymm σ R 0 = 1 := by simp [hsymm, eq_nil_of_card_zero]

@[simp]
/-
**MvPolynomial.hsymm_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：hsymm_one : hsymm σ R 1 = ∑ i, X i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Sym.oneEquiv_apply`：∀ {α : Type u_1} (a : α), Sym.oneEquiv a = ⟨{a}, ⋯⟩
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem hsymm_one : hsymm σ R 1 = ∑ i, X i := by
  symm
  apply Fintype.sum_equiv oneEquiv
  simp only [oneEquiv_apply, Multiset.map_singleton, Multiset.prod_singleton, implies_true]
/-
**MvPolynomial.hsymmPart_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：hsymmPart_zero : hsymmPart σ R (.indiscrete 0) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Nat.Partition.partition_zero_parts`：∀ (p : Nat.Partition 0), p.parts = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hsymmPart_zero : hsymmPart σ R (.indiscrete 0) = 1 := by simp [hsymmPart]

@[simp]
/-
**MvPolynomial.hsymmPart_indiscrete** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：hsymmPart_indiscrete (n : Nat) : hsymmPart σ R (.indiscrete n) = hsymm σ R
 n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Nat.Partition.partition_zero_parts`：∀ (p : Nat.Partition 0), p.parts = 0
· 使用定理 `MvPolynomial.hsymm_zero`：hsymm_zero : hsymm σ R 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.Partition.indiscrete_parts`：∀ {n : ℕ}, n ≠ 0 → (Nat.Partition.indisc
rete n).parts = {n}
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
-/
theorem hsymmPart_indiscrete (n : ℕ) : hsymmPart σ R (.indiscrete n) = hsymm σ R n := by
  cases n <;> simp [hsymmPart]
/-
**MvPolynomial.map_hsymm** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_hsymm (n : Nat) (f : R ->+* S) : map f (hsymm σ R n) = hsymm σ S n
参数：n : Nat；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_hsymm (n : ℕ) (f : R →+* S) : map f (hsymm σ R n) = hsymm σ S n := by
  simp [hsymm, ← Multiset.prod_hom']
/-
**MvPolynomial.rename_hsymm** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_hsymm (n : Nat) (e : σ ≃ τ) : rename e (hsymm σ R n) = hsymm τ R n
参数：n : Nat；e : σ ≃ τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Sym.equivCongr_apply`：∀ {α : Type u_1} {β : Type u_2} {n : ℕ} (e : α ≃ β
) (x : Sym α n), (Sym.equivCongr e) x = Sym.map (⇑e) x
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem rename_hsymm (n : ℕ) (e : σ ≃ τ) : rename e (hsymm σ R n) = hsymm τ R n := by
  simp_rw [hsymm, map_sum, ← prod_hom', rename_X]
  apply Fintype.sum_equiv (equivCongr e)
  simp
/-
**MvPolynomial.hsymm_isSymmetric** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：hsymm_isSymmetric (n : Nat) : IsSymmetric (hsymm σ R n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.rename_hsymm`：rename_hsymm (n : Nat) (e : σ ≃ τ) : rename e
 (hsymm σ R n) = hsymm τ R n
-/
theorem hsymm_isSymmetric (n : ℕ) : IsSymmetric (hsymm σ R n) := rename_hsymm _ _ n

end CompleteHomogeneousSymmetric

section PowerSum

open Finset

/-- The degree-`n` power sum symmetric `MvPolynomial σ R`.
It is the sum over all the `n`-th powers of the variables. -/
/-
**MvPolynomial.psum** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：psum (n : Nat) : MvPolynomial σ R
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The degree-`n` power sum symmetric `MvPolynomial σ R`.
It is the sum over all the `n`-th powers of the variables.
-/
def psum (n : ℕ) : MvPolynomial σ R := ∑ i, X i ^ n

/-- `psumPart` is the product of the symmetric polynomials `psum μᵢ`,
where `μ = (μ₁, μ₂, ...)` is a partition. -/
/-
**MvPolynomial.psumPart** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：psumPart {n : Nat} (μ : n.Partition) : MvPolynomial σ R
参数：μ : n.Partition。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`psumPart` is the product of the symmetric polynomials `psum μᵢ`,
where `μ = (μ₁, μ₂, ...)` is a partition.
-/
def psumPart {n : ℕ} (μ : n.Partition) : MvPolynomial σ R := (μ.parts.map (psum σ R)).prod

@[simp]
/-
**MvPolynomial.psum_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：psum_zero : psum σ R 0 = Fintype.card σ
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
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem psum_zero : psum σ R 0 = Fintype.card σ := by simp [psum]

@[simp]
/-
**MvPolynomial.psum_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：psum_one : psum σ R 1 = ∑ i, X i
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
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem psum_one : psum σ R 1 = ∑ i, X i := by simp [psum]

@[simp]
/-
**MvPolynomial.psumPart_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：psumPart_zero : psumPart σ R (.indiscrete 0) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Nat.Partition.partition_zero_parts`：∀ (p : Nat.Partition 0), p.parts = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem psumPart_zero : psumPart σ R (.indiscrete 0) = 1 := by simp [psumPart]

@[simp]
/-
**MvPolynomial.psumPart_indiscrete** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：psumPart_indiscrete {n : Nat} (npos : n != 0) : psumPart σ R (.indiscrete 
n) = psum σ R n
参数：npos : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Nat.Partition.indiscrete_parts`：∀ {n : ℕ}, n ≠ 0 → (Nat.Partition.indisc
rete n).parts = {n}
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem psumPart_indiscrete {n : ℕ} (npos : n ≠ 0) :
    psumPart σ R (.indiscrete n) = psum σ R n := by simp [psumPart, npos]

@[simp]
/-
**MvPolynomial.rename_psum** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_psum (n : Nat) (e : σ ≃ τ) : rename e (psum σ R n) = psum τ R n
参数：n : Nat；e : σ ≃ τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
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
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rename_psum (n : ℕ) (e : σ ≃ τ) : rename e (psum σ R n) = psum τ R n := by
  simp_rw [psum, map_sum, map_pow, rename_X, e.sum_comp (X · ^ n)]
/-
**MvPolynomial.psum_isSymmetric** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：psum_isSymmetric (n : Nat) : IsSymmetric (psum σ R n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.rename_psum`：rename_psum (n : Nat) (e : σ ≃ τ) : rename e (
psum σ R n) = psum τ R n
-/
theorem psum_isSymmetric (n : ℕ) : IsSymmetric (psum σ R n) := rename_psum _ _ n

end PowerSum

section MonomialSymmetric

variable [DecidableEq σ] [DecidableEq τ] {n : ℕ}

/-- The monomial symmetric `MvPolynomial σ R` with exponent set μ.
It is the sum over all the monomials in `MvPolynomial σ R` such that
the multiset of exponents is equal to the multiset of parts of μ. -/
/-
**MvPolynomial.msymm** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：msymm (μ : n.Partition) : MvPolynomial σ R
参数：μ : n.Partition。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monomial symmetric `MvPolynomial σ R` with exponent set μ.
It is the sum over all the monomials in `MvPolynomial σ R` such that
the multiset of exponents is equal to the multiset of parts of μ.
-/
def msymm (μ : n.Partition) : MvPolynomial σ R :=
  ∑ s : {a : Sym σ n // .ofSym a = μ}, (s.1.1.map X).prod

@[simp]
/-
**MvPolynomial.msymm_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：msymm_zero : msymm σ R (.indiscrete 0) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.msymm.eq_1`：∀ (σ : Type u_5) (R : Type u_6) [inst : CommSem
iring R] [inst_1 : Fintype σ] [inst_2 : DecidableEq σ] {n : ℕ}   (μ : n.Partitio
n), MvPolynom…
· 使用定理 `Fintype.sum_subsingleton`：∀ {M : Type u_4} {ι : Type u_7} [inst : Fintyp
e ι] [inst_1 : AddCommMonoid M] [Subsingleton ι] (f : ι → M) (a : ι),   ∑ x, f x
 = f a
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem msymm_zero : msymm σ R (.indiscrete 0) = 1 := by
  rw [msymm, Fintype.sum_subsingleton _ ⟨(Sym.nil : Sym σ 0), rfl⟩]
  simp

@[simp]
/-
**MvPolynomial.msymm_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：msymm_one : msymm σ R (.indiscrete 1) = ∑ i, X i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.Partition.ofSym_one`：∀ {σ : Type u_1} [inst : DecidableEq σ] (s : Sy
m σ 1), Nat.Partition.ofSym s = Nat.Partition.indiscrete 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `Multiset.map_singleton`：map_singleton (f : α -> β) (a : α) : ({a} : Mult
iset α).map f = {f a}
-/
theorem msymm_one : msymm σ R (.indiscrete 1) = ∑ i, X i := by
  have : (fun (x : Sym σ 1) ↦ x ∈ Set.univ) =
      (fun x ↦ Nat.Partition.ofSym x = Nat.Partition.indiscrete 1) := by
    simp_rw [Set.mem_univ, Nat.Partition.ofSym_one]
  symm
  rw [Fintype.sum_equiv (Equiv.trans Sym.oneEquiv (Equiv.Set.univ (Sym σ 1)).symm)
    _ (fun s ↦ (s.1.1.map X).prod)]
  · apply Fintype.sum_equiv (Equiv.subtypeEquivProp this)
    intro x
    congr
  · intro x
    rw [← Multiset.prod_singleton (X x), ← Multiset.map_singleton]
    congr

@[simp]
/-
**MvPolynomial.rename_msymm** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：rename_msymm (μ : n.Partition) (e : σ ≃ τ) : rename e (msymm σ R μ) = msym
m τ R μ
参数：μ : n.Partition；e : σ ≃ τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.msymm.eq_1`：∀ (σ : Type u_5) (R : Type u_6) [inst : CommSem
iring R] [inst_1 : Fintype σ] [inst_2 : DecidableEq σ] {n : ℕ}   (μ : n.Partitio
n), MvPolynom…
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
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.prod_hom`：prod_hom (s : Multiset M) {F : Type*} [FunLike F M N]
 [MonoidHomClass F M N] (f : F) : (s.map f).prod = f s.prod
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Nat.Partition.ofSymShapeEquiv.eq_1`：∀ {n : ℕ} {σ : Type u_1} {τ : Type u
_2} [inst : DecidableEq σ] [inst_1 : DecidableEq τ] (μ : n.Partition) (e : σ ≃ τ
),   μ.ofSymShapeEquiv e…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `Sym.equivCongr_apply`：∀ {α : Type u_1} {β : Type u_2} {n : ℕ} (e : α ≃ β
) (x : Sym α n), (Sym.equivCongr e) x = Sym.map (⇑e) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rename_msymm (μ : n.Partition) (e : σ ≃ τ) :
    rename e (msymm σ R μ) = msymm τ R μ := by
  rw [msymm, map_sum]
  apply Fintype.sum_equiv (Nat.Partition.ofSymShapeEquiv μ e)
  intro
  rw [← Multiset.prod_hom, Multiset.map_map, Nat.Partition.ofSymShapeEquiv]
  simp
/-
**MvPolynomial.msymm_isSymmetric** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：msymm_isSymmetric (μ : n.Partition) : IsSymmetric (msymm σ R μ)
参数：μ : n.Partition。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.rename_msymm`：rename_msymm (μ : n.Partition) (e : σ ≃ τ) : 
rename e (msymm σ R μ) = msymm τ R μ
-/
theorem msymm_isSymmetric (μ : n.Partition) : IsSymmetric (msymm σ R μ) :=
  rename_msymm _ _ μ

end MonomialSymmetric

end MvPolynomial

