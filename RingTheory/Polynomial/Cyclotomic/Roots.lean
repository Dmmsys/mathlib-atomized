/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.Minpoly

/-!
# Roots of cyclotomic polynomials.

We gather results about roots of cyclotomic polynomials. In particular we show in
`Polynomial.cyclotomic_eq_minpoly` that `cyclotomic n R` is the minimal polynomial of a primitive
root of unity.

## Main results

* `IsPrimitiveRoot.isRoot_cyclotomic` : Any `n`-th primitive root of unity is a root of
  `cyclotomic n R`.
* `isRoot_cyclotomic_iff` : if `NeZero (n : R)`, then `μ` is a root of `cyclotomic n R`
  if and only if `μ` is a primitive root of unity.
* `Polynomial.cyclotomic_eq_minpoly` : `cyclotomic n ℤ` is the minimal polynomial of a primitive
  `n`-th root of unity `μ`.
* `Polynomial.cyclotomic.irreducible` : `cyclotomic n ℤ` is irreducible.

## Implementation details

To prove `Polynomial.cyclotomic.irreducible`, the irreducibility of `cyclotomic n ℤ`, we show in
`Polynomial.cyclotomic_eq_minpoly` that `cyclotomic n ℤ` is the minimal polynomial of any `n`-th
primitive root of unity `μ : K`, where `K` is a field of characteristic `0`.
-/

public section


namespace Polynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-
**Polynomial.isRoot_of_unity_of_root_cyclotomic** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：isRoot_of_unity_of_root_cyclotomic {ζ : R} {i : Nat} (hi : i in n.divisors
) (h : (cyclotomic i R).IsRoot ζ) : ζ ^ n = 1
参数：hi : i in n.divisors；h : (cyclotomic i R).IsRoot ζ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`：prod_cyclotomic_eq_X_pow_su
b_one {n : Nat} (hpos : 0 < n) (R : Type*) [CommRing R] : ∏ i in Nat.divisors n,
 cyclotomic i R = X ^ n - 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero`：eval_eq_zero_of_dvd_of_e
val_eq_zero : p ∣ q -> eval x p = 0 -> eval x q = 0
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_add_of_sub_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G},
 a - b = c → a = b + c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `Polynomial.eval_X_pow`：eval_X_pow {x : R} (n : Nat) : (X ^ n : R[X]).eva
l x = x ^ n
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
-/
theorem isRoot_of_unity_of_root_cyclotomic {ζ : R} {i : ℕ} (hi : i ∈ n.divisors)
    (h : (cyclotomic i R).IsRoot ζ) : ζ ^ n = 1 := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact pow_zero _
  have := congr_arg (eval ζ) (prod_cyclotomic_eq_X_pow_sub_one hn R).symm
  rw [eval_sub, eval_X_pow, eval_one] at this
  convert! eq_add_of_sub_eq' this
  convert! (add_zero (M := R) _).symm
  apply eval_eq_zero_of_dvd_of_eval_eq_zero _ h
  exact Finset.dvd_prod_of_mem _ hi

section IsDomain

variable [IsDomain R]

/-
**Polynomial._root_.isRoot_of_unity_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isRoot_of_unity_iff (h : 0 < n) (R : Type*) [CommRing R] [IsDomain R] {ζ : R} :
    ζ ^ n = 1 ↔ ∃ i ∈ n.divisors, (cyclotomic i R).IsRoot ζ := by
  rw [← mem_nthRoots h, nthRoots, mem_roots <| X_pow_sub_C_ne_zero h _, C_1, ←
      prod_cyclotomic_eq_X_pow_sub_one h, isRoot_prod]

/-- Any `n`-th primitive root of unity is a root of `cyclotomic n R`. -/
/-
**Polynomial._root_.IsPrimitiveRoot.isRoot_cyclotomic** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any `n`-th primitive root of unity is a root of `cyclotomic n R`.
-/
theorem _root_.IsPrimitiveRoot.isRoot_cyclotomic (hpos : 0 < n) {μ : R} (h : IsPrimitiveRoot μ n) :
    IsRoot (cyclotomic n R) μ := by
  rw [← mem_roots (cyclotomic_ne_zero n R), cyclotomic_eq_prod_X_sub_primitiveRoots h,
    roots_prod_X_sub_C, ← Finset.mem_def]
  rwa [← mem_primitiveRoots hpos] at h
/-
**Polynomial.isRoot_cyclotomic_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem isRoot_cyclotomic_iff' {n : ℕ} {K : Type*} [Field K] {μ : K} [NeZero (n : K)] :
    IsRoot (cyclotomic n K) μ ↔ IsPrimitiveRoot μ n := by
  -- in this proof, `o` stands for `orderOf μ`
  have hnpos : 0 < n := (NeZero.of_neZero_natCast K).out.bot_lt
  refine ⟨fun hμ => ?_, IsPrimitiveRoot.isRoot_cyclotomic hnpos⟩
  have hμn : μ ^ n = 1 := by
    rw [isRoot_of_unity_iff hnpos _]
    exact ⟨n, n.mem_divisors_self hnpos.ne', hμ⟩
  by_contra hnμ
  have ho : 0 < orderOf μ := (isOfFinOrder_iff_pow_eq_one.2 <| ⟨n, hnpos, hμn⟩).orderOf_pos
  have := pow_orderOf_eq_one μ
  rw [isRoot_of_unity_iff ho] at this
  obtain ⟨i, hio, hiμ⟩ := this
  replace hio := Nat.dvd_of_mem_divisors hio
  rw [IsPrimitiveRoot.not_iff] at hnμ
  rw [← orderOf_dvd_iff_pow_eq_one] at hμn
  have key : i < n := (Nat.le_of_dvd ho hio).trans_lt ((Nat.le_of_dvd hnpos hμn).lt_of_ne hnμ)
  have key' : i ∣ n := hio.trans hμn
  rw [← Polynomial.dvd_iff_isRoot] at hμ hiμ
  have hni : {i, n} ⊆ n.divisors := by simpa [Finset.insert_subset_iff, key'] using hnpos.ne'
  obtain ⟨k, hk⟩ := hiμ
  obtain ⟨j, hj⟩ := hμ
  have := prod_cyclotomic_eq_X_pow_sub_one hnpos K
  rw [← Finset.prod_sdiff hni, Finset.prod_pair key.ne, hk, hj] at this
  have hn := (X_pow_sub_one_separable_iff.mpr <| NeZero.natCast_ne n K).squarefree
  rw [← this, Squarefree] at hn
  specialize hn (X - C μ) ⟨(∏ x ∈ n.divisors \ {i, n}, cyclotomic x K) * k * j, by ring⟩
  simp [Polynomial.isUnit_iff_degree_eq_zero] at hn
/-
**Polynomial.isRoot_cyclotomic_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isRoot_cyclotomic_iff [NeZero (n : R)] {μ : R} : IsRoot (cyclotomic n R) μ
 ↔ IsPrimitiveRoot μ n
参数：n : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `NeZero.nat_of_injective`：NeZero.nat_of_injective {n : Nat} [NeZero (n : 
R)] [RingHomClass F R S] {f : F} (hf : Function.Injective f) : NeZero (n : S)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.isRoot_map_iff`：isRoot_map_iff {R : Type*} [CommRing R] {f : 
R ->+* S} {x : R} {p : R[X]} (hf : Function.Injective f) : IsRoot (p.map f) (f x
) ↔ IsRoot p x
· 使用定理 `IsPrimitiveRoot.map_iff_of_injective`：map_iff_of_injective [MonoidHomCla
ss F M N] (hf : Injective f) : IsPrimitiveRoot (f ζ) k ↔ IsPrimitiveRoot ζ k
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.map_cyclotomic`：map_cyclotomic (n : Nat) {R S : Type*} [Ring 
R] [Ring S] (f : R ->+* S) : map f (cyclotomic n R) = cyclotomic n S
· 使用定理 `_private.Mathlib.RingTheory.Polynomial.Cyclotomic.Roots.0.Polynomial.isR
oot_cyclotomic_iff'`：∀ {n : ℕ} {K : Type u_2} [inst : Field K] {μ : K} [NeZero ↑
n],   (Polynomial.cyclotomic n K).IsRoot μ ↔ IsPrimitiveRoot μ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isRoot_cyclotomic_iff [NeZero (n : R)] {μ : R} :
    IsRoot (cyclotomic n R) μ ↔ IsPrimitiveRoot μ n := by
  have hf : Function.Injective _ := IsFractionRing.injective R (FractionRing R)
  have : NeZero (n : FractionRing R) := NeZero.nat_of_injective hf
  rw [← isRoot_map_iff hf, ← IsPrimitiveRoot.map_iff_of_injective hf, map_cyclotomic, ←
    isRoot_cyclotomic_iff']
/-
**Polynomial.roots_cyclotomic_nodup** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_cyclotomic_nodup [NeZero (n : R)] : (cyclotomic n R).roots.Nodup
参数：n : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.empty_or_exists_mem`：empty_or_exists_mem (s : Multiset α) : s =
 0 ∨ exists a, a in s
· 使用定理 `Multiset.nodup_zero`：nodup_zero : @Nodup α 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.nodup_of_le`：nodup_of_le {s t : Multiset α} (h : s <= t) : Nodu
p t -> Nodup s
· 使用定理 `Polynomial.roots.le_of_dvd`：∀ {R : Type u} [inst : CommRing R] [inst_1 :
 IsDomain R] {p q : Polynomial R}, q ≠ 0 → p ∣ q → p.roots ≤ q.roots
· 使用定理 `Polynomial.X_pow_sub_C_ne_zero`：X_pow_sub_C_ne_zero {n : Nat} (hn : 0 < 
n) (a : R) : (X : R[X]) ^ n - C a != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `NeZero.pos_of_neZero_natCast`：pos_of_neZero_natCast (R) [AddMonoidWithOn
e R] {n : Nat} [NeZero (n : R)] : 0 < n
· 使用定理 `Polynomial.cyclotomic.dvd_X_pow_sub_one`：∀ (n : ℕ) (R : Type u_1) [inst 
: Ring R], Polynomial.cyclotomic n R ∣ Polynomial.X ^ n - 1
· 使用定理 `IsPrimitiveRoot.nthRoots_one_nodup`：nthRoots_one_nodup {ζ : R} {n : Nat}
 (h : IsPrimitiveRoot ζ n) : (nthRoots n (1 : R)).Nodup
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.isRoot_cyclotomic_iff`：isRoot_cyclotomic_iff [NeZero (n : R)]
 {μ : R} : IsRoot (cyclotomic n R) μ ↔ IsPrimitiveRoot μ n
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Polynomial.cyclotomic_ne_zero`：cyclotomic_ne_zero (n : Nat) (R : Type*) 
[Ring R] [Nontrivial R] : cyclotomic n R != 0
-/
theorem roots_cyclotomic_nodup [NeZero (n : R)] : (cyclotomic n R).roots.Nodup := by
  obtain h | ⟨ζ, hζ⟩ := (cyclotomic n R).roots.empty_or_exists_mem
  · exact h.symm ▸ Multiset.nodup_zero
  rw [mem_roots <| cyclotomic_ne_zero n R, isRoot_cyclotomic_iff] at hζ
  refine Multiset.nodup_of_le
    (roots.le_of_dvd (X_pow_sub_C_ne_zero (NeZero.pos_of_neZero_natCast R) 1) <|
      cyclotomic.dvd_X_pow_sub_one n R) hζ.nthRoots_one_nodup
/-
**Polynomial.cyclotomic.roots_to_finset_eq_primitiveRoots** 是 Mathlib 中的一个定理，位于命
名空间 `Polynomial.cyclotomic`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} [inst_1 : IsDomain R] [inst_2
 : NeZero ↑n],   { val := (Polynomial.cyclotomic n R).roots, nodup := ⋯ } = prim
itiveRoots n R
参数：Polynomial.cyclotomic n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Polynomial.roots_cyclotomic_nodup`：roots_cyclotomic_nodup [NeZero (n : R
)] : (cyclotomic n R).roots.Nodup
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.cyclotomic_ne_zero`：cyclotomic_ne_zero (n : Nat) (R : Type*) 
[Ring R] [Nontrivial R] : cyclotomic n R != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `NeZero.pos_of_neZero_natCast`：pos_of_neZero_natCast (R) [AddMonoidWithOn
e R] {n : Nat} [NeZero (n : R)] : 0 < n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cyclotomic.roots_to_finset_eq_primitiveRoots [NeZero (n : R)] :
    (⟨(cyclotomic n R).roots, roots_cyclotomic_nodup⟩ : Finset _) = primitiveRoots n R := by
  ext a
  simp [cyclotomic_ne_zero n R, ← isRoot_cyclotomic_iff, mem_primitiveRoots,
    NeZero.pos_of_neZero_natCast R]
/-
**Polynomial.cyclotomic.roots_eq_primitiveRoots_val** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial.cyclotomic`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} [inst_1 : IsDomain R] [NeZero
 ↑n],   (Polynomial.cyclotomic n R).roots = (primitiveRoots n R).val
参数：Polynomial.cyclotomic n R；primitiveRoots n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.roots_cyclotomic_nodup`：roots_cyclotomic_nodup [NeZero (n : R
)] : (cyclotomic n R).roots.Nodup
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.cyclotomic.roots_to_finset_eq_primitiveRoots`：∀ {R : Type u_1
} [inst : CommRing R] {n : ℕ} [inst_1 : IsDomain R] [inst_2 : NeZero ↑n],   { va
l := (Polynomial.cyclotomic n R).roots, nodup…
-/
theorem cyclotomic.roots_eq_primitiveRoots_val [NeZero (n : R)] :
    (cyclotomic n R).roots = (primitiveRoots n R).val := by
  rw [← cyclotomic.roots_to_finset_eq_primitiveRoots]

/-- If `R` is of characteristic zero, then `ζ` is a root of `cyclotomic n R` if and only if it is a
primitive `n`-th root of unity. -/
/-
**Polynomial.isRoot_cyclotomic_iff_charZero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：isRoot_cyclotomic_iff_charZero {n : Nat} {R : Type*} [CommRing R] [IsDomai
n R] [CharZero R] {μ : R} (hn : 0 < n) : (Polynomial.cyclotomic n R).IsRoot μ ↔ 
IsPrimitiveRoot μ n
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.isRoot_cyclotomic_iff`：isRoot_cyclotomic_iff [NeZero (n : R)]
 {μ : R} : IsRoot (cyclotomic n R) μ ↔ IsPrimitiveRoot μ n
· 使用定理 `NeZero.of_gt`：of_gt [Preorder α] [IsBotZeroClass α] (h : a < b) : NeZero
 b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
If `R` is of characteristic zero, then `ζ` is a root of `cyclotomic n R` if and 
only if it is a
primitive `n`-th root of unity.
-/
theorem isRoot_cyclotomic_iff_charZero {n : ℕ} {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {μ : R} (hn : 0 < n) : (Polynomial.cyclotomic n R).IsRoot μ ↔ IsPrimitiveRoot μ n :=
  letI := NeZero.of_gt hn
  isRoot_cyclotomic_iff

end IsDomain

/-- Over a ring `R` of characteristic zero, `fun n => cyclotomic n R` is injective. -/
/-
**Polynomial.cyclotomic_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic_injective [CharZero R] : Function.Injective fun n => cyclotomic
 n R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.cyclotomic_zero`：cyclotomic_zero (R : Type*) [Ring R] : cyclo
tomic 0 R = 1
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.totient_eq_zero`：∀ {n : ℕ}, n.totient = 0 ↔ n = 0
· 使用定理 `Polynomial.natDegree_cyclotomic`：natDegree_cyclotomic (n : Nat) (R : Typ
e*) [Ring R] [Nontrivial R] : (cyclotomic n R).natDegree = Nat.totient n
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `Polynomial.map_cyclotomic_int`：map_cyclotomic_int (n : Nat) (R : Type*) 
[Ring R] : map (Int.castRingHom R) (cyclotomic n Int) = cyclotomic n R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.isPrimitiveRoot_exp`：isPrimitiveRoot_exp (n : Nat) (h0 : n != 0)
 : IsPrimitiveRoot (exp (2 * π * I / n)) n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isRoot_cyclotomic_iff`：isRoot_cyclotomic_iff [NeZero (n : R)]
 {μ : R} : IsRoot (cyclotomic n R) μ ↔ IsPrimitiveRoot μ n
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsPrimitiveRoot.eq_orderOf`：eq_orderOf (h : IsPrimitiveRoot ζ k) : k = o
rderOf ζ

--- 原说明 ---
Over a ring `R` of characteristic zero, `fun n => cyclotomic n R` is injective.
-/
theorem cyclotomic_injective [CharZero R] : Function.Injective fun n => cyclotomic n R := by
  intro n m hnm
  simp only at hnm
  rcases eq_or_ne n 0 with (rfl | hzero)
  · rw [cyclotomic_zero] at hnm
    replace hnm := congr_arg natDegree hnm
    rwa [natDegree_one, natDegree_cyclotomic, eq_comm, Nat.totient_eq_zero, eq_comm] at hnm
  · have := NeZero.mk hzero
    rw [← map_cyclotomic_int _ R, ← map_cyclotomic_int _ R] at hnm
    replace hnm := map_injective (Int.castRingHom R) Int.cast_injective hnm
    replace hnm := congr_arg (map (Int.castRingHom ℂ)) hnm
    rw [map_cyclotomic_int, map_cyclotomic_int] at hnm
    have hprim := Complex.isPrimitiveRoot_exp _ hzero
    have hroot := isRoot_cyclotomic_iff (R := ℂ).2 hprim
    rw [hnm] at hroot
    have hmzero : NeZero m := ⟨fun h => by simp [h] at hroot⟩
    rw [isRoot_cyclotomic_iff (R := ℂ)] at hroot
    replace hprim := hprim.eq_orderOf
    rwa [← IsPrimitiveRoot.eq_orderOf hroot] at hprim

/-- The minimal polynomial of a primitive `n`-th root of unity `μ` divides `cyclotomic n ℤ`. -/
/-
**Polynomial._root_.IsPrimitiveRoot.minpoly_dvd_cyclotomic** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimal polynomial of a primitive `n`-th root of unity `μ` divides `cyclotom
ic n ℤ`.
-/
theorem _root_.IsPrimitiveRoot.minpoly_dvd_cyclotomic {n : ℕ} {K : Type*} [Field K] {μ : K}
    (h : IsPrimitiveRoot μ n) (hpos : 0 < n) [CharZero K] : minpoly ℤ μ ∣ cyclotomic n ℤ := by
  apply minpoly.isIntegrallyClosed_dvd (h.isIntegral hpos)
  simpa [aeval_def, eval₂_eq_eval_map, IsRoot.def] using h.isRoot_cyclotomic hpos

section minpoly

open IsPrimitiveRoot Complex

/-
**Polynomial._root_.IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible** 是 Mat
hlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible {K : Type*} [Field K]
    {R : Type*} [CommRing R] [IsDomain R] {μ : R} {n : ℕ} [Algebra K R] (hμ : IsPrimitiveRoot μ n)
    (h : Irreducible <| cyclotomic n K) [NeZero (n : K)] : cyclotomic n K = minpoly K μ := by
  have := NeZero.of_faithfulSMul K R n
  refine minpoly.eq_of_irreducible_of_monic h ?_ (cyclotomic.monic n K)
  rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← IsRoot.def, isRoot_cyclotomic_iff]

/-- `cyclotomic n ℤ` is the minimal polynomial of a primitive `n`-th root of unity `μ`. -/
/-
**Polynomial.cyclotomic_eq_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic_eq_minpoly {n : Nat} {K : Type*} [Field K] {μ : K} (h : IsPrimi
tiveRoot μ n) (hpos : 0 < n) [CharZero K] : cyclotomic n Int = minpoly Int μ
参数：h : IsPrimitiveRoot μ n；hpos : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`：eq_of_monic_of_dvd_of_nat
Degree_le {p q : R[X]} (hp : p.Monic) (hq : q.Monic) (hdvd : p ∣ q) (hdeg : q.na
tDegree <= p.natDegree) : q = p
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `IsPrimitiveRoot.isIntegral`：isIntegral (hpos : 0 < n) : IsIntegral Int μ
· 使用定理 `Polynomial.cyclotomic.monic`：∀ (n : ℕ) (R : Type u_1) [inst : Ring R], (
Polynomial.cyclotomic n R).Monic
· 使用定理 `IsPrimitiveRoot.minpoly_dvd_cyclotomic`：∀ {n : ℕ} {K : Type u_2} [inst :
 Field K] {μ : K},   IsPrimitiveRoot μ n → 0 < n → ∀ [CharZero K], minpoly ℤ μ ∣
 Polynomial.cyclotomic n ℤ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_cyclotomic`：natDegree_cyclotomic (n : Nat) (R : Typ
e*) [Ring R] [Nontrivial R] : (cyclotomic n R).natDegree = Nat.totient n
· 使用定理 `IsPrimitiveRoot.totient_le_degree_minpoly`：totient_le_degree_minpoly : N
at.totient n <= (minpoly Int μ).natDegree
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R

--- 原说明 ---
`cyclotomic n ℤ` is the minimal polynomial of a primitive `n`-th root of unity `
μ`.
-/
theorem cyclotomic_eq_minpoly {n : ℕ} {K : Type*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n)
    (hpos : 0 < n) [CharZero K] : cyclotomic n ℤ = minpoly ℤ μ := by
  refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (IsPrimitiveRoot.isIntegral h hpos))
    (cyclotomic.monic n ℤ) (h.minpoly_dvd_cyclotomic hpos) ?_
  simpa [natDegree_cyclotomic n ℤ] using totient_le_degree_minpoly h

/-- `cyclotomic n ℚ` is the minimal polynomial of a primitive `n`-th root of unity `μ`. -/
/-
**Polynomial.cyclotomic_eq_minpoly_rat** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic_eq_minpoly_rat {n : Nat} {K : Type*} [Field K] {μ : K} (h : IsP
rimitiveRoot μ n) (hpos : 0 < n) [CharZero K] : cyclotomic n Rat = minpoly Rat μ
参数：h : IsPrimitiveRoot μ n；hpos : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_cyclotomic_int`：map_cyclotomic_int (n : Nat) (R : Type*) 
[Ring R] : map (Int.castRingHom R) (cyclotomic n Int) = cyclotomic n R
· 使用定理 `Polynomial.cyclotomic_eq_minpoly`：cyclotomic_eq_minpoly {n : Nat} {K : T
ype*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n) (hpos : 0 < n) [CharZero K] : 
cyclotomic n Int = min…
· 使用定理 `minpoly.isIntegrallyClosed_eq_field_fractions'`：isIntegrallyClosed_eq_fi
eld_fractions' [IsDomain S] [Algebra K S] [IsScalarTower R K S] {s : S} (hs : Is
Integral R s) : minpoly K s = (minpo…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsPrimitiveRoot.isIntegral`：isIntegral (hpos : 0 < n) : IsIntegral Int μ

--- 原说明 ---
`cyclotomic n ℚ` is the minimal polynomial of a primitive `n`-th root of unity `
μ`.
-/
theorem cyclotomic_eq_minpoly_rat {n : ℕ} {K : Type*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n)
    (hpos : 0 < n) [CharZero K] : cyclotomic n ℚ = minpoly ℚ μ := by
  rw [← map_cyclotomic_int, cyclotomic_eq_minpoly h hpos]
  exact (minpoly.isIntegrallyClosed_eq_field_fractions' _ (IsPrimitiveRoot.isIntegral h hpos)).symm

/-- `cyclotomic n ℤ` is irreducible. -/
/-
**Polynomial.cyclotomic.irreducible** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.cyclot
omic`。
形式化陈述：∀ {n : ℕ}, 0 < n → Irreducible (Polynomial.cyclotomic n ℤ)
参数：Polynomial.cyclotomic n ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.cyclotomic_eq_minpoly`：cyclotomic_eq_minpoly {n : Nat} {K : T
ype*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n) (hpos : 0 < n) [CharZero K] : 
cyclotomic n Int = min…
· 使用定理 `Complex.isPrimitiveRoot_exp`：isPrimitiveRoot_exp (n : Nat) (h0 : n != 0)
 : IsPrimitiveRoot (exp (2 * π * I / n)) n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsPrimitiveRoot.isIntegral`：isIntegral (hpos : 0 < n) : IsIntegral Int μ

--- 原说明 ---
`cyclotomic n ℤ` is irreducible.
-/
theorem cyclotomic.irreducible {n : ℕ} (hpos : 0 < n) : Irreducible (cyclotomic n ℤ) := by
  rw [cyclotomic_eq_minpoly (isPrimitiveRoot_exp n hpos.ne') hpos]
  apply minpoly.irreducible
  exact (isPrimitiveRoot_exp n hpos.ne').isIntegral hpos

/-- `cyclotomic n ℚ` is irreducible. -/
/-
**Polynomial.cyclotomic.irreducible_rat** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.cy
clotomic`。
形式化陈述：∀ {n : ℕ}, 0 < n → Irreducible (Polynomial.cyclotomic n ℚ)
参数：Polynomial.cyclotomic n ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_cyclotomic_int`：map_cyclotomic_int (n : Nat) (R : Type*) 
[Ring R] : map (Int.castRingHom R) (cyclotomic n Int) = cyclotomic n R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map`：∀ {
R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : Field K] [inst_2 : Al
gebra R K] [IsFractionRing R K]   [IsDomain R] [IsGCDMono…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsBezout.instIsGCDMonoidOfIsCancelMulZero`：∀ (R : Type u) [inst : CommRi
ng R] [IsBezout R] [IsCancelMulZero R], IsGCDMonoid R
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `Polynomial.cyclotomic.isPrimitive`：∀ (n : ℕ) (R : Type u_1) [inst : Comm
Ring R], (Polynomial.cyclotomic n R).IsPrimitive
· 使用定理 `Polynomial.cyclotomic.irreducible`：∀ {n : ℕ}, 0 < n → Irreducible (Polyn
omial.cyclotomic n ℤ)

--- 原说明 ---
`cyclotomic n ℚ` is irreducible.
-/
theorem cyclotomic.irreducible_rat {n : ℕ} (hpos : 0 < n) : Irreducible (cyclotomic n ℚ) := by
  rw [← map_cyclotomic_int]
  exact (IsPrimitive.irreducible_iff_irreducible_map_fraction_map (cyclotomic.isPrimitive n ℤ)).1
    (cyclotomic.irreducible hpos)

/-- If `n ≠ m`, then `(cyclotomic n ℚ)` and `(cyclotomic m ℚ)` are coprime. -/
/-
**Polynomial.cyclotomic.isCoprime_rat** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.cycl
otomic`。
形式化陈述：∀ {n m : ℕ}, n ≠ m → IsCoprime (Polynomial.cyclotomic n ℚ) (Polynomial.cyc
lotomic m ℚ)
参数：Polynomial.cyclotomic n ℚ；Polynomial.cyclotomic m ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `isCoprime_one_left`：isCoprime_one_left : IsCoprime 1 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCoprime_one_right`：isCoprime_one_right : IsCoprime x 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Irreducible.coprime_iff_not_dvd`：Irreducible.coprime_iff_not_dvd {p n : 
R} (hp : Irreducible p) : IsCoprime p n ↔ ¬p ∣ n
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Polynomial.cyclotomic.irreducible_rat`：∀ {n : ℕ}, 0 < n → Irreducible (P
olynomial.cyclotomic n ℚ)
· 使用定理 `Polynomial.cyclotomic_injective`：cyclotomic_injective [CharZero R] : Fun
ction.Injective fun n => cyclotomic n R
· 使用定理 `Polynomial.eq_of_monic_of_associated`：eq_of_monic_of_associated (hp : p.
Monic) (hq : q.Monic) (hpq : Associated p q) : p = q
· 使用定理 `Polynomial.cyclotomic.monic`：∀ (n : ℕ) (R : Type u_1) [inst : Ring R], (
Polynomial.cyclotomic n R).Monic
· 使用定理 `Irreducible.associated_of_dvd`：Irreducible.associated_of_dvd [Monoid M] 
{p q : M} (p_irr : Irreducible p) (q_irr : Irreducible q) (dvd : p ∣ q) : Associ
ated p q

--- 原说明 ---
If `n ≠ m`, then `(cyclotomic n ℚ)` and `(cyclotomic m ℚ)` are coprime.
-/
theorem cyclotomic.isCoprime_rat {n m : ℕ} (h : n ≠ m) :
    IsCoprime (cyclotomic n ℚ) (cyclotomic m ℚ) := by
  rcases n.eq_zero_or_pos with (rfl | hnzero)
  · exact isCoprime_one_left
  rcases m.eq_zero_or_pos with (rfl | hmzero)
  · exact isCoprime_one_right
  rw [Irreducible.coprime_iff_not_dvd <| cyclotomic.irreducible_rat <| hnzero]
  exact fun hdiv => h <| cyclotomic_injective <|
    eq_of_monic_of_associated (cyclotomic.monic n ℚ) (cyclotomic.monic m ℚ) <|
      Irreducible.associated_of_dvd (cyclotomic.irreducible_rat hnzero)
        (cyclotomic.irreducible_rat hmzero) hdiv

end minpoly

end Polynomial

namespace IsPrimitiveRoot

open Polynomial

variable {K : Type*} [Field K] [CharZero K]
variable {p : ℕ} {ζ : K}

/-- For a prime `p`, a ℚ-linear combination `∑_{i < p} αᵢ ζⁱ` vanishes if and only if all
coefficients `αᵢ` are equal. This follows from the irreducibility of the `p`-th cyclotomic
polynomial. See de Launey–Flannery, *Algebraic Design Theory*, Lemma 2.8.5. -/
/-
**IsPrimitiveRoot.sum_eq_zero_iff_forall_eq** 是 Mathlib 中的一个引理，位于命名空间 `IsPrimiti
veRoot`。
形式化陈述：sum_eq_zero_iff_forall_eq (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) (α : F
in p -> Rat) : ∑ i, α i * ζ ^ i.val = 0 ↔ forall i j, α i = α j
参数：hp : p.Prime；hζ : IsPrimitiveRoot ζ p；α : Fin p -> Rat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.degree_sum_le`：degree_sum_le (s : Finset ι) (f : ι -> R[X]) :
 degree (∑ i in s, f i) <= s.sup fun b => degree (f b)
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Polynomial.degree_C_mul_X_pow_le`：degree_C_mul_X_pow_le (n : Nat) (a : R
) : degree (C a * X ^ n) <= n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
（共 76 条，此处仅展示前 30 条）

--- 原说明 ---
For a prime `p`, a ℚ-linear combination `∑_{i < p} αᵢ ζⁱ` vanishes if and only i
f all
coefficients `αᵢ` are equal. This follows from the irreducibility of the `p`-th 
cyclotomic
polynomial. See de Launey–Flannery, *Algebraic Design Theory*, Lemma 2.8.5.
-/
lemma sum_eq_zero_iff_forall_eq (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) (α : Fin p → ℚ) :
    ∑ i, α i * ζ ^ i.val = 0 ↔ ∀ i j, α i = α j := by
  have : Fact p.Prime := ⟨hp⟩
  let P : ℚ[X] := ∑ i, C (α i) * X ^ i.1
  have hP (i : Fin p) : α i = P.coeff i := by simp [P, ← Fin.ext_iff]
  have hP' : P.degree ≤ ↑(p - 1) :=
    (degree_sum_le ..).trans (Finset.sup_le fun _ _ ↦ by grw [degree_C_mul_X_pow_le]; simp; grind)
  trans aeval ζ P = 0; · simp [P]
  rw [← minpoly.dvd_iff, ← cyclotomic_eq_minpoly_rat hζ hp.pos]
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun H ↦ ⟨C (α 0), Polynomial.ext fun i ↦ if h : i < p then ?_ else ?_⟩⟩
  · rw [hc, degree_mul, degree_cyclotomic, Nat.totient_prime hp] at hP'
    have : c.degree ≤ 0 := (WithBot.add_le_add_iff_left (x := ↑(p - 1)) (by simp)).mp (by simpa)
    obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp (natDegree_eq_zero_iff_degree_le_zero.mpr this)
    simp [hP, hc, cyclotomic_prime]
  · lift i to Fin p using h; simp [cyclotomic_prime, ← hP, H i 0]
  · simp [cyclotomic_prime, P, h, Fin.forall_iff, @forall_comm _ (_ = _), Finset.sum_eq_zero]

/-- Variant of `sum_eq_zero_iff_forall_eq` with integer coefficients. -/
/-
**IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int** 是 Mathlib 中的一个引理，位于命名空间 `IsPri
mitiveRoot`。
形式化陈述：sum_eq_zero_iff_forall_eq_int (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) (α
 : Fin p -> Int) : ∑ i, α i * ζ ^ i.val = 0 ↔ forall i j, α i = α j
参数：hp : p.Prime；hζ : IsPrimitiveRoot ζ p；α : Fin p -> Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `IsPrimitiveRoot.sum_eq_zero_iff_forall_eq`：sum_eq_zero_iff_forall_eq (hp
 : p.Prime) (hζ : IsPrimitiveRoot ζ p) (α : Fin p -> Rat) : ∑ i, α i * ζ ^ i.val
 = 0 ↔ forall i j, α i = α j

--- 原说明 ---
Variant of `sum_eq_zero_iff_forall_eq` with integer coefficients.
-/
lemma sum_eq_zero_iff_forall_eq_int (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) (α : Fin p → ℤ) :
    ∑ i, α i * ζ ^ i.val = 0 ↔ ∀ i j, α i = α j := by
  simpa using sum_eq_zero_iff_forall_eq hp hζ (Int.cast ∘ α)

end IsPrimitiveRoot

