/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Vieta's Formula

The main result is `Multiset.prod_X_add_C_eq_sum_esymm`, which shows that the product of
linear terms `X + λ` with `λ` in a `Multiset s` is equal to a linear combination of the
symmetric functions `esymm s`.

From this, we deduce `MvPolynomial.prod_X_add_C_eq_sum_esymm` which is the equivalent formula
for the product of linear terms `X + X i` with `i` in a `Fintype σ` as a linear combination
of the symmetric polynomials `esymm σ R j`.

For `R` be an integral domain (so that `p.roots` is defined for any `p : R[X]` as a multiset),
we derive `Polynomial.coeff_eq_esymm_roots_of_card`, the relationship between the coefficients and
the roots of `p` for a polynomial `p` that splits (i.e. having as many roots as its degree).
-/

public section

open Finset Polynomial

namespace Multiset

section Semiring

variable {R : Type*} [CommSemiring R]

/-- A sum version of **Vieta's formula** for `Multiset`: the product of the linear terms `X + λ`
where `λ` runs through a multiset `s` is equal to a linear combination of the symmetric functions
`esymm s` of the `λ`'s . -/
/-
**Multiset.prod_X_add_C_eq_sum_esymm** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_X_add_C_eq_sum_esymm (s : Multiset R) : (s.map fun r => X + C r).prod
 = ∑ j in Finset.range (Multiset.card s + 1), (C (s.esymm j) * X ^ (Multiset.car
d s - j))
参数：s : Multiset R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.prod_map_add`：prod_map_add {s : Multiset ι} {f g : ι -> R} : pr
od (s.map fun i => f i + g i) = sum ((antidiagonal s).map fun p => (p.1.map f).p
rod * (p.2.…
· 使用定理 `Multiset.antidiagonal_eq_map_powerset`：antidiagonal_eq_map_powerset [Dec
idableEq α] (s : Multiset α) : s.antidiagonal = s.powerset.map fun t => (s - t, 
t)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.bind_powerset_len`：bind_powerset_len {α : Type*} (S : Multiset 
α) : (bind (Multiset.range (card S + 1)) fun k => S.powersetCard k) = S.powerset
· 使用定理 `Multiset.map_bind`：map_bind (m : Multiset α) (n : α -> Multiset β) (f : 
β -> γ) : map f (bind m n) = bind m fun a => map f (n a)
· 使用定理 `Multiset.sum_bind`：∀ {α : Type u_1} {β : Type v} [inst : AddCommMonoid β
] (s : Multiset α) (t : α → Multiset β),   (s.bind t).sum = (Multiset.map (fun a
 => (t …
· 使用定理 `Finset.sum_eq_multiset_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddC
ommMonoid M] (s : Finset ι) (f : ι → M),   ∑ x ∈ s, f x = (Multiset.map f s.val)
.sum
· 使用定理 `Finset.range_val`：range_val (n : Nat) : (range n).1 = Multiset.range n
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.esymm.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (s : Multi
set R) (n : ℕ),   s.esymm n = (Multiset.map Multiset.prod (Multiset.powersetCard
 n s)).su…
· 使用定理 `Multiset.sum_hom'`：∀ {ι : Type u_2} {M : Type u_5} {N : Type u_6} [inst 
: AddCommMonoid M] [inst_1 : AddCommMonoid N] (s : Multiset ι)   {F : Type u_8} 
[inst_2…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `Multiset.sum_map_mul_right`：sum_map_mul_right : sum (s.map fun i => f i 
* a) = sum (s.map f) * a
· 使用定理 `Multiset.prod_hom'`：prod_hom' (s : Multiset ι) {F : Type*} [FunLike F M 
N] [MonoidHomClass F M N] (f : F) (g : ι -> M) : (s.map fun i => f <| g i).prod 
= f (s.m…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用引理 `Multiset.card_sub`：card_sub {s t : Multiset α} (h : t <= s) : card (s - 
t) = card s - card t
· 使用定理 `Multiset.mem_powersetCard`：mem_powersetCard {n : Nat} {s t : Multiset α}
 : s in powersetCard n t ↔ s <= t ∧ card s = n
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `Polynomial.X_pow_mul_C`：X_pow_mul_C (r : R) (n : Nat) : X ^ n * C r = C 
r * X ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A sum version of **Vieta's formula** for `Multiset`: the product of the linear t
erms `X + λ`
where `λ` runs through a multiset `s` is equal to a linear combination of the sy
mmetric functions
`esymm s` of the `λ`'s .
-/
theorem prod_X_add_C_eq_sum_esymm (s : Multiset R) :
    (s.map fun r => X + C r).prod =
      ∑ j ∈ Finset.range (Multiset.card s + 1), (C (s.esymm j) * X ^ (Multiset.card s - j)) := by
  classical
    rw [prod_map_add, antidiagonal_eq_map_powerset, map_map, ← bind_powerset_len,
      map_bind, sum_bind, Finset.sum_eq_multiset_sum, Finset.range_val, map_congr (Eq.refl _)]
    intro _ _
    rw [esymm, ← sum_hom', ← sum_map_mul_right, map_congr (Eq.refl _)]
    intro s ht
    rw [mem_powersetCard] at ht
    dsimp
    rw [prod_hom' s (Polynomial.C : R →+* R[X])]
    simp [ht, prod_replicate, map_id', card_sub]

/-- Vieta's formula for the coefficients of the product of linear terms `X + λ` where `λ` runs
through a multiset `s` : the `k`th coefficient is the symmetric function `esymm (card s - k) s`. -/
/-
**Multiset.prod_X_add_C_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_X_add_C_coeff (s : Multiset R) {k : Nat} (h : k <= Multiset.card s) :
 (s.map fun r => X + C r).prod.coeff k = s.esymm (Multiset.card s - k)
参数：s : Multiset R；h : k <= Multiset.card s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_C_mul_X_pow`：coeff_C_mul_X_pow (x : R) (k n : Nat) : co
eff (C x * X ^ k : R[X]) n = if n = k then x else 0
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.ext_iff`：ext_iff {p q : R[X]} : p = q ↔ forall n, coeff p n =
 coeff q n
· 使用定理 `Multiset.prod_X_add_C_eq_sum_esymm`：prod_X_add_C_eq_sum_esymm (s : Multi
set R) : (s.map fun r => X + C r).prod = ∑ j in Finset.range (Multiset.card s + 
1), (C (s.esymm j) * X ^…

--- 原说明 ---
Vieta's formula for the coefficients of the product of linear terms `X + λ` wher
e `λ` runs
through a multiset `s` : the `k`th coefficient is the symmetric function `esymm 
(card s - k) s`.
-/
theorem prod_X_add_C_coeff (s : Multiset R) {k : ℕ} (h : k ≤ Multiset.card s) :
    (s.map fun r => X + C r).prod.coeff k = s.esymm (Multiset.card s - k) := by
  convert! Polynomial.ext_iff.mp (prod_X_add_C_eq_sum_esymm s) k using 1
  simp_rw [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single_of_mem (Multiset.card s - k) _] <;> grind
/-
**Multiset.prod_X_add_C_coeff'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_X_add_C_coeff' {σ} (s : Multiset σ) (r : σ -> R) {k : Nat} (h : k <= 
Multiset.card s) : (s.map fun i => X + C (r i)).prod.coeff k = (s.map r).esymm (
Multiset.card s - k)
参数：s : Multiset σ；r : σ -> R；h : k <= Multiset.card s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.prod_X_add_C_coeff`：prod_X_add_C_coeff (s : Multiset R) {k : Na
t} (h : k <= Multiset.card s) : (s.map fun r => X + C r).prod.coeff k = s.esymm 
(Multiset.card s …
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
-/
theorem prod_X_add_C_coeff' {σ} (s : Multiset σ) (r : σ → R) {k : ℕ} (h : k ≤ Multiset.card s) :
    (s.map fun i => X + C (r i)).prod.coeff k = (s.map r).esymm (Multiset.card s - k) := by
  rw [← Function.comp_def (f := fun r => X + C r) (g := r), ← map_map, prod_X_add_C_coeff]
    <;> rw [s.card_map r]; assumption
/-
**Multiset._root_.Finset.prod_X_add_C_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.prod_X_add_C_coeff {σ} (s : Finset σ) (r : σ → R) {k : ℕ} (h : k ≤ #s) :
    (∏ i ∈ s, (X + C (r i))).coeff k = ∑ t ∈ s.powersetCard (#s - k), ∏ i ∈ t, r i := by
  rw [Finset.prod, prod_X_add_C_coeff' _ r h, Finset.esymm_map_val]
  rfl

end Semiring

section Ring

variable {R : Type*} [CommRing R]

/-
**Multiset.esymm_neg** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：esymm_neg (s : Multiset R) (k : Nat) : (map Neg.neg s).esymm k = (-1) ^ k 
* esymm s k
参数：s : Multiset R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.esymm.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (s : Multi
set R) (n : ℕ),   s.esymm n = (Multiset.map Multiset.prod (Multiset.powersetCard
 n s)).su…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Multiset.sum_map_mul_left`：sum_map_mul_left : sum (s.map fun i => a * f 
i) = a * sum (s.map f)
· 使用定理 `Multiset.powersetCard_map`：powersetCard_map {β : Type*} (f : α -> β) (n 
: Nat) (s : Multiset α) : powersetCard n (s.map f) = (powersetCard n s).map (map
 f)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_powersetCard`：mem_powersetCard {n : Nat} {s t : Multiset α}
 : s in powersetCard n t ↔ s <= t ∧ card s = n
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `Multiset.map_const`：map_const (s : Multiset α) (b : β) : map (const α b)
 s = replicate (card s) b
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `Multiset.prod_map_mul`：prod_map_mul : (m.map fun i => f i * g i).prod = 
(m.map f).prod * (m.map g).prod
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem esymm_neg (s : Multiset R) (k : ℕ) : (map Neg.neg s).esymm k = (-1) ^ k * esymm s k := by
  rw [esymm, esymm, ← Multiset.sum_map_mul_left, Multiset.powersetCard_map, Multiset.map_map,
    map_congr rfl]
  intro x hx
  rw [(mem_powersetCard.mp hx).right.symm, ← prod_replicate, ← Multiset.map_const]
  nth_rw 3 [← map_id' x]
  rw [← prod_map_mul, map_congr rfl, Function.comp_apply]
  exact fun z _ => neg_one_mul z
/-
**Multiset.prod_X_sub_X_eq_sum_esymm** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_X_sub_X_eq_sum_esymm (s : Multiset R) : (s.map fun t => X - C t).prod
 = ∑ j in Finset.range (Multiset.card s + 1), (-1) ^ j * (C (s.esymm j) * X ^ (M
ultiset.card s - j))
参数：s : Multiset R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.esymm_neg`：esymm_neg (s : Multiset R) (k : Nat) : (map Neg.neg 
s).esymm k = (-1) ^ k * esymm s k
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.prod_X_add_C_eq_sum_esymm`：prod_X_add_C_eq_sum_esymm (s : Multi
set R) : (s.map fun r => X + C r).prod = ∑ j in Finset.range (Multiset.card s + 
1), (C (s.esymm j) * X ^…
-/
theorem prod_X_sub_X_eq_sum_esymm (s : Multiset R) :
    (s.map fun t => X - C t).prod =
      ∑ j ∈ Finset.range (Multiset.card s + 1),
        (-1) ^ j * (C (s.esymm j) * X ^ (Multiset.card s - j)) := by
  conv_lhs =>
    congr
    congr
    ext x
    rw [sub_eq_add_neg]
    rw [← map_neg C x]
  convert! prod_X_add_C_eq_sum_esymm (map (fun t => -t) s) using 1
  · rw [map_map]; rfl
  · simp only [esymm_neg, card_map, mul_assoc, map_mul, map_pow, map_neg, map_one]
/-
**Multiset.prod_X_sub_C_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_X_sub_C_coeff (s : Multiset R) {k : Nat} (h : k <= Multiset.card s) :
 (s.map fun t => X - C t).prod.coeff k = (-1) ^ (Multiset.card s - k) * s.esymm 
(Multiset.card s - k)
参数：s : Multiset R；h : k <= Multiset.card s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.esymm_neg`：esymm_neg (s : Multiset R) (k : Nat) : (map Neg.neg 
s).esymm k = (-1) ^ k * esymm s k
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Multiset.prod_X_add_C_coeff`：prod_X_add_C_coeff (s : Multiset R) {k : Na
t} (h : k <= Multiset.card s) : (s.map fun r => X + C r).prod.coeff k = s.esymm 
(Multiset.card s …
-/
theorem prod_X_sub_C_coeff (s : Multiset R) {k : ℕ} (h : k ≤ Multiset.card s) :
    (s.map fun t => X - C t).prod.coeff k =
    (-1) ^ (Multiset.card s - k) * s.esymm (Multiset.card s - k) := by
  conv_lhs =>
    congr
    congr
    congr
    ext x
    rw [sub_eq_add_neg]
    rw [← map_neg C x]
  convert! prod_X_add_C_coeff (map (fun t => -t) s) _ using 1
  · rw [map_map]; rfl
  · rw [esymm_neg, card_map]
  · rwa [card_map]

/-- Vieta's formula for the coefficients and the roots of a polynomial over an integral domain
  with as many roots as its degree. -/
/-
**Multiset._root_.Polynomial.coeff_eq_esymm_roots_of_card** 是 Mathlib 中的一个定理，位于命
名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Vieta's formula for the coefficients and the roots of a polynomial over an integ
ral domain
  with as many roots as its degree.
-/
theorem _root_.Polynomial.coeff_eq_esymm_roots_of_card [IsDomain R] {p : R[X]}
    (hroots : Multiset.card p.roots = p.natDegree) {k : ℕ} (h : k ≤ p.natDegree) :
    p.coeff k = p.leadingCoeff * (-1) ^ (p.natDegree - k) * p.roots.esymm (p.natDegree - k) := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hroots]
  rw [coeff_C_mul, mul_assoc]; congr
  have : k ≤ card (roots p) := by rw [hroots]; exact h
  convert! p.roots.prod_X_sub_C_coeff this using 3 <;> rw [hroots]

/-- Vieta's formula for split polynomials over a field. -/
/-
**Multiset._root_.Polynomial.coeff_eq_esymm_roots_of_splits** 是 Mathlib 中的一个定理，位
于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Vieta's formula for split polynomials over a field.
-/
theorem _root_.Polynomial.coeff_eq_esymm_roots_of_splits {F} [Field F] {p : F[X]}
    (hsplit : p.Splits) {k : ℕ} (h : k ≤ p.natDegree) :
    p.coeff k = p.leadingCoeff * (-1) ^ (p.natDegree - k) * p.roots.esymm (p.natDegree - k) :=
  Polynomial.coeff_eq_esymm_roots_of_card (splits_iff_card_roots.1 hsplit) h

end Ring

end Multiset

section MvPolynomial

open Finset Polynomial Fintype

variable (R σ : Type*) [CommSemiring R] [Fintype σ]

/-- A sum version of Vieta's formula for `MvPolynomial`: viewing `X i` as variables,
the product of linear terms `λ + X i` is equal to a linear combination of
the symmetric polynomials `esymm σ R j`. -/
/-
**MvPolynomial.prod_C_add_X_eq_sum_esymm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MvPolynomial.prod_C_add_X_eq_sum_esymm : (∏ i : σ, (Polynomial.X + Polynom
ial.C (MvPolynomial.X i))) = ∑ j in range (card σ + 1), Polynomial.C (MvPolynomi
al.esymm σ R j) * Polynomial.X ^ (card σ - j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Finset.card_def`：card_def (s : Finset α) : #s = Multiset.card s.1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MvPolynomial.esymm_eq_multiset_esymm`：esymm_eq_multiset_esymm : esymm σ 
R = (univ.val.map X).esymm
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.prod_X_add_C_eq_sum_esymm`：prod_X_add_C_eq_sum_esymm (s : Multi
set R) : (s.map fun r => X + C r).prod = ∑ j in Finset.range (Multiset.card s + 
1), (C (s.esymm j) * X ^…

--- 原说明 ---
A sum version of Vieta's formula for `MvPolynomial`: viewing `X i` as variables,
the product of linear terms `λ + X i` is equal to a linear combination of
the symmetric polynomials `esymm σ R j`.
-/
theorem MvPolynomial.prod_C_add_X_eq_sum_esymm :
    (∏ i : σ, (Polynomial.X + Polynomial.C (MvPolynomial.X i))) =
      ∑ j ∈ range (card σ + 1), Polynomial.C
        (MvPolynomial.esymm σ R j) * Polynomial.X ^ (card σ - j) := by
  let s := Finset.univ.val.map fun i : σ => (MvPolynomial.X i : MvPolynomial σ R)
  have : Fintype.card σ = Multiset.card s := by
    rw [Multiset.card_map, ← Finset.card_univ, Finset.card_def]
  simp_rw [this, MvPolynomial.esymm_eq_multiset_esymm σ R, Finset.prod_eq_multiset_prod]
  convert! Multiset.prod_X_add_C_eq_sum_esymm s
  simp_rw [s, Multiset.map_map, Function.comp_apply]
/-
**MvPolynomial.prod_X_add_C_coeff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MvPolynomial.prod_X_add_C_coeff (k : Nat) (h : k <= card σ) : (∏ i : σ, (P
olynomial.X + Polynomial.C (MvPolynomial.X i)) : Polynomial _).coeff k = MvPolyn
omial.esymm σ R (card σ - k)
参数：k : Nat；h : k <= card σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Finset.card_def`：card_def (s : Finset α) : #s = Multiset.card s.1
· 使用定理 `MvPolynomial.esymm_eq_multiset_esymm`：esymm_eq_multiset_esymm : esymm σ 
R = (univ.val.map X).esymm
· 使用定理 `Finset.prod_eq_multiset_prod`：prod_eq_multiset_prod [CommMonoid M] (s : 
Finset ι) (f : ι -> M) : ∏ x in s, f x = (s.1.map f).prod
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.prod_X_add_C_coeff`：prod_X_add_C_coeff (s : Multiset R) {k : Na
t} (h : k <= Multiset.card s) : (s.map fun r => X + C r).prod.coeff k = s.esymm 
(Multiset.card s …
-/
theorem MvPolynomial.prod_X_add_C_coeff (k : ℕ) (h : k ≤ card σ) :
    (∏ i : σ, (Polynomial.X + Polynomial.C (MvPolynomial.X i)) : Polynomial _).coeff k =
    MvPolynomial.esymm σ R (card σ - k) := by
  let s := Finset.univ.val.map fun i => (MvPolynomial.X i : MvPolynomial σ R)
  have : Fintype.card σ = Multiset.card s := by
    rw [Multiset.card_map, ← Finset.card_univ, Finset.card_def]
  rw [this] at h ⊢
  rw [MvPolynomial.esymm_eq_multiset_esymm σ R, Finset.prod_eq_multiset_prod]
  convert! Multiset.prod_X_add_C_coeff s h
  simp_rw [s, Multiset.map_map, Function.comp_apply]

end MvPolynomial

