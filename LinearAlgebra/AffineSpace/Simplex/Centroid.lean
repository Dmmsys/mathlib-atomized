/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Chu Zheng
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Centroid

/-!
# Centroid of a simplex in affine space

This file proves some basic properties of the centroid of a simplex in affine space.
The definition of the centroid is based on `Finset.univ.centroid` applied to the set of vertices.
For convenience, we use `Simplex.centroid` as an abbreviation.

This file also defines `faceOppositeCentroid`, which is the centroid of the facet of the simplex
obtained by removing one vertex.

We prove several relations among the `centroid`, the `faceOppositeCentroid`, and the vertices of
the simplex. In particular, we prove a version of Commandino's theorem in arbitrary dimensions:
the centroid lies on each median, dividing it in a ratio of `n : 1`, where `n` is the dimension
of the simplex.

## Main definitions

* `centroid` is the centroid of a simplex, defined via `Finset.univ.centroid` on its vertices.

* `faceOppositeCentroid` is the centroid of the facet obtained by removing one vertex from the
  simplex.

* `median` is the line connecting a vertex to the corresponding faceOppositeCentroid.

* `medial` is the simplex formed by all `faceOppositeCentroid`.

## References

* https://en.wikipedia.org/wiki/Median_(geometry)
* https://en.wikipedia.org/wiki/Commandino%27s_theorem

-/

@[expose] public section

noncomputable section

open Finset AffineSubspace

namespace Affine

namespace Simplex

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

variable {n : ℕ}

/-- The centroid of a simplex is the `Finset.centroid` of the set of all its vertices. -/
/-
**Affine.Simplex.centroid** 是 Mathlib 中的一个缩写定义，位于命名空间 `Affine.Simplex`。
形式化陈述：centroid (t : Affine.Simplex k P n) : P
参数：t : Affine.Simplex k P n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The centroid of a simplex is the `Finset.centroid` of the set of all its vertice
s.
-/
abbrev centroid (t : Affine.Simplex k P n) : P := Finset.univ.centroid k t.points
/-
**Affine.Simplex.univ_centroid_eq** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：univ_centroid_eq (s : Simplex k P n) : Finset.univ.centroid k s.points = s
.centroid
参数：s : Simplex k P n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem univ_centroid_eq (s : Simplex k P n) :
    Finset.univ.centroid k s.points = s.centroid := rfl

/-- The centroid lines in the affine span of the simplex's vertices. -/
/-
**Affine.Simplex.centroid_mem_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simpl
ex`。
形式化陈述：centroid_mem_affineSpan [CharZero k] {n : Nat} (s : Simplex k P n) : s.cen
troid in affineSpan k (Set.range s.points)
参数：s : Simplex k P n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `centroid_mem_affineSpan_of_card_eq_add_one`：centroid_mem_affineSpan_of_c
ard_eq_add_one [CharZero k] {s : Finset ι} (p : ι -> P) {n : Nat} (h : #s = n + 
1) : s.centroid k p in affineSpa…
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n

--- 原说明 ---
The centroid lines in the affine span of the simplex's vertices.
-/
theorem centroid_mem_affineSpan [CharZero k] {n : ℕ} (s : Simplex k P n) :
    s.centroid ∈ affineSpan k (Set.range s.points) :=
  centroid_mem_affineSpan_of_card_eq_add_one k _ (card_fin (n + 1))

/-- The centroid is equal to the affine combination of the points with `centroidWeights`. -/
/-
**Affine.Simplex.centroid_eq_affineCombination** 是 Mathlib 中的一个定理，位于命名空间 `Affine
.Simplex`。
形式化陈述：centroid_eq_affineCombination (s : Simplex k P n) : s.centroid = affineCom
bination k univ s.points (centroidWeights k univ)
参数：s : Simplex k P n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The centroid is equal to the affine combination of the points with `centroidWeig
hts`.
-/
theorem centroid_eq_affineCombination (s : Simplex k P n) :
    s.centroid = affineCombination k univ s.points (centroidWeights k univ) := by rfl

/-- The centroid of a simplex does not lie in the affine span of any proper subset of its
vertices. -/
/-
**Affine.Simplex.centroid_notMem_affineSpan_of_ne_univ** 是 Mathlib 中的一个定理，位于命名空间
 `Affine.Simplex`。
形式化陈述：centroid_notMem_affineSpan_of_ne_univ [CharZero k] (s : Simplex k P n) {t 
: Set (Fin (n + 1))} (ht : t != Set.univ) : s.centroid ∉ affineSpan k (s.points 
'' t)
参数：s : Simplex k P n；Fin (n + 1)；ht : t != Set.univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_of_ssubset`：exists_of_ssubset {s t : Set α} (h : s ⊂ t) : exi
sts x in t, x ∉ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_nonempty`：sum_centroidWeights_eq_on
e_of_nonempty [CharZero k] (h : s.Nonempty) : ∑ i in s, s.centroidWeights k i = 
1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan`：AffineInd
ependent.eq_zero_of_affineCombination_mem_affineSpan {p : ι -> P} (ha : AffineIn
dependent k p) {fs : Finset ι} {w : ι -> k} (hw : ∑…
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `Affine.Simplex.centroid_eq_affineCombination`：centroid_eq_affineCombinat
ion (s : Simplex k P n) : s.centroid = affineCombination k univ s.points (centro
idWeights k univ)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p

--- 原说明 ---
The centroid of a simplex does not lie in the affine span of any proper subset o
f its
vertices.
-/
theorem centroid_notMem_affineSpan_of_ne_univ [CharZero k] (s : Simplex k P n)
    {t : Set (Fin (n + 1))} (ht : t ≠ Set.univ) :
    s.centroid ∉ affineSpan k (s.points '' t) := by
  intro h
  have hssubset : t ⊂ Set.univ := by grind
  obtain ⟨i, hi⟩ := Set.exists_of_ssubset hssubset
  rw [s.centroid_eq_affineCombination] at h
  set w := (centroidWeights k (univ : Finset (Fin (n + 1)))) with wdef
  have hw : ∑ i, w i = 1 := by rw [sum_centroidWeights_eq_one_of_nonempty _ _ (by simp)]
  have h1 := AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan s.independent hw h
    (by simp) hi.2
  have h2 : w i = (1 : k) / (n + 1) := by
    simp [wdef, centroidWeights_apply, card_univ, Fintype.card_fin, Nat.cast_add,
      Nat.cast_one]
  simp only [h2, one_div, inv_eq_zero] at h1
  norm_cast at h1

/-- The vector from any point to the centroid is the average of vectors to the simplex vertices. -/
/-
**Affine.Simplex.centroid_vsub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：centroid_vsub_eq {n : Nat} [CharZero k] (s : Simplex k P n) (p : P) : s.ce
ntroid -ᵥ p = (n + 1 : k)⁻¹ • ∑ x, (s.points x -ᵥ p)
参数：s : Simplex k P n；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.centroid_vsub_const`：centroid_vsub_const [CharZero k] {p : ι -> P
} {p₀ : P} (hs : s.Nonempty) : Finset.centroid k s p -ᵥ p₀ = Finset.centroid k s
 (fun i => p i -…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.centroid_def`：centroid_def (p : ι -> P) : s.centroid k p = s.affi
neCombination k p (s.centroidWeights k)
· 使用定理 `Finset.affineCombination_eq_linear_combination`：affineCombination_eq_lin
ear_combination (s : Finset ι) (p : ι -> V) (w : ι -> k) (hw : ∑ i in s, w i = 1
) : s.affineCombination k p w = ∑ i …
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_nonempty`：sum_centroidWeights_eq_on
e_of_nonempty [CharZero k] (h : s.Nonempty) : ∑ i in s, s.centroidWeights k i = 
1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The vector from any point to the centroid is the average of vectors to the simpl
ex vertices.
-/
theorem centroid_vsub_eq {n : ℕ} [CharZero k] (s : Simplex k P n) (p : P) :
    s.centroid -ᵥ p = (n + 1 : k)⁻¹ • ∑ x, (s.points x -ᵥ p) := by
  rw [centroid_vsub_const _ _ (by simp), centroid_def, affineCombination_eq_linear_combination
    (hw := sum_centroidWeights_eq_one_of_nonempty _ _ (by simp))]
  simp [smul_sum]
/-
**Affine.Simplex.centroid_eq_smul_sum_vsub_vadd** 是 Mathlib 中的一个定理，位于命名空间 `Affin
e.Simplex`。
形式化陈述：centroid_eq_smul_sum_vsub_vadd [CharZero k] (s : Simplex k P n) (i : Fin (
n + 1)) : s.centroid = (n + 1 : k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i) +ᵥ s.poin
ts i
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.centroid_vsub_eq`：centroid_vsub_eq {n : Nat} [CharZero k]
 (s : Simplex k P n) (p : P) : s.centroid -ᵥ p = (n + 1 : k)⁻¹ • ∑ x, (s.points 
x -ᵥ p)
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
-/
theorem centroid_eq_smul_sum_vsub_vadd [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid = (n + 1 : k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i) +ᵥ s.points i := by
  rw [← s.centroid_vsub_eq, vsub_vadd]
/-
**Affine.Simplex.smul_centroid_vsub_point_eq_sum_vsub** 是 Mathlib 中的一个定理，位于命名空间 
`Affine.Simplex`。
形式化陈述：smul_centroid_vsub_point_eq_sum_vsub [CharZero k] (s : Simplex k P n) (i :
 Fin (n + 1)) : ((n : k) + 1) • (s.centroid -ᵥ s.points i) = ∑ x, (s.points x -ᵥ
 s.points i)
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.centroid_eq_smul_sum_vsub_vadd`：centroid_eq_smul_sum_vsub
_vadd [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) : s.centroid = (n + 1 :
 k)⁻¹ • ∑ x, (s.points x -ᵥ s.point…
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem smul_centroid_vsub_point_eq_sum_vsub [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    ((n : k) + 1) • (s.centroid -ᵥ s.points i) = ∑ x, (s.points x -ᵥ s.points i) := by
  rw [centroid_eq_smul_sum_vsub_vadd s i, vadd_vsub, smul_smul, mul_inv_cancel₀, one_smul]
  norm_cast

/-- The sum of vectors from the centroid to each vertex is zero. -/
/-
**Affine.Simplex.centroid_weighted_vsub_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Affin
e.Simplex`。
形式化陈述：centroid_weighted_vsub_eq_zero [CharZero k] (s : Simplex k P n) : ∑ i, (s.
points i -ᵥ s.centroid) = 0
参数：s : Simplex k P n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.centroid_vsub_eq`：centroid_vsub_eq {n : Nat} [CharZero k]
 (s : Simplex k P n) (p : P) : s.centroid -ᵥ p = (n + 1 : k)⁻¹ • ∑ x, (s.points 
x -ᵥ p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_zero_iff_right`：smul_eq_zero_iff_right (hr : r != 0) : r • m = 0
 ↔ m = 0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0

--- 原说明 ---
The sum of vectors from the centroid to each vertex is zero.
-/
theorem centroid_weighted_vsub_eq_zero [CharZero k] (s : Simplex k P n) :
    ∑ i, (s.points i -ᵥ s.centroid) = 0 := by
  have h := centroid_vsub_eq s s.centroid
  simp only [vsub_self] at h
  symm at h
  rw [smul_eq_zero_iff_right (inv_ne_zero (by norm_cast))] at h
  exact h

/-- A point is centroid if and only if the sum of vectors from the point to all vertices is zero. -/
/-
**Affine.Simplex.eq_centroid_iff_sum_vsub_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ine.Simplex`。
形式化陈述：eq_centroid_iff_sum_vsub_eq_zero [CharZero k] {s : Simplex k P n} {p : P} 
: p = s.centroid ↔ ∑ i, (s.points i -ᵥ p) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.centroid_weighted_vsub_eq_zero`：centroid_weighted_vsub_eq
_zero [CharZero k] (s : Simplex k P n) : ∑ i, (s.points i -ᵥ s.centroid) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用引理 `smul_eq_zero_iff_right`：smul_eq_zero_iff_right (hr : r != 0) : r • m = 0
 ↔ m = 0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p

--- 原说明 ---
A point is centroid if and only if the sum of vectors from the point to all vert
ices is zero.
-/
theorem eq_centroid_iff_sum_vsub_eq_zero [CharZero k] {s : Simplex k P n} {p : P} :
    p = s.centroid ↔ ∑ i, (s.points i -ᵥ p) = 0 := by
  constructor
  · intro h
    rw [h, centroid_weighted_vsub_eq_zero]
  · intro h
    rw [← vsub_eq_zero_iff_eq]
    have : ∑ i, (s.points i -ᵥ p) = ∑ i, ((s.points i -ᵥ s.centroid) - (p -ᵥ s.centroid)) := by
      apply sum_congr rfl
      intro x hx
      rw [vsub_sub_vsub_cancel_right _ _ s.centroid]
    rw [this, sum_sub_distrib, centroid_weighted_vsub_eq_zero] at h
    simp only [sum_const, card_univ, Fintype.card_fin, zero_sub, neg_eq_zero] at h
    have h' : ((n : k) + 1) • (p -ᵥ s.centroid) = 0 := by norm_cast
    rw [smul_eq_zero_iff_right (by norm_cast)] at h'
    exact h'

/-- The centroid of a face of a simplex as the centroid of a subset of
the points. -/
/-
**Affine.Simplex.face_centroid_eq_centroid** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Sim
plex`。
形式化陈述：face_centroid_eq_centroid {n : Nat} (s : Simplex k P n) {fs : Finset (Fin 
(n + 1))} {m : Nat} (h : #fs = m + 1) : Finset.univ.centroid k (s.face h).points
 = fs.centroid k s.points
参数：s : Simplex k P n；Fin (n + 1)；h : #fs = m + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.range_orderEmbOfFin`：range_orderEmbOfFin (s : Finset α) {k : Nat}
 (h : s.card = k) : Set.range (s.orderEmbOfFin h) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.centroid_map`：centroid_map (e : ι₂ ↪ ι) (p : ι -> P) : (s₂.map e)
.centroid k p = s₂.centroid k (p ∘ e)

--- 原说明 ---
The centroid of a face of a simplex as the centroid of a subset of
the points.
-/
theorem face_centroid_eq_centroid {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) : Finset.univ.centroid k (s.face h).points = fs.centroid k s.points := by
  convert! (Finset.univ.centroid_map k (fs.orderEmbOfFin h).toEmbedding s.points).symm
  rw [← Finset.coe_inj, Finset.coe_map, Finset.coe_univ, Set.image_univ]
  simp

/-- Over a characteristic-zero division ring, the centroids given by
two subsets of the points of a simplex are equal if and only if those
faces are given by the same subset of points. -/
@[simp]
/-
**Affine.Simplex.centroid_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：centroid_eq_iff [CharZero k] {n : Nat} (s : Simplex k P n) {fs₁ fs₂ : Fins
et (Fin (n + 1))} {m₁ m₂ : Nat} (h₁ : #fs₁ = m₁ + 1) (h₂ : #fs₂ = m₂ + 1) : fs₁.
centroid k s.points = fs₂.centroid k s.points ↔ fs₁ = fs₂
参数：s : Simplex k P n；Fin (n + 1)；h₁ : #fs₁ = m₁ + 1；h₂ : #fs₂ = m₂ + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `affineIndependent_iff_indicator_eq_of_affineCombination_eq`：affineIndepe
ndent_iff_indicator_eq_of_affineCombination_eq (p : ι -> P) : AffineIndependent 
k p ↔ forall (s1 s2 : Finset ι) (w1 w2 : ι -> k)…
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `Finset.sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one`：sum_centr
oidWeightsIndicator_eq_one_of_card_eq_add_one [CharZero k] [Fintype ι] {n : Nat}
 (h : #s = n + 1) : ∑ i, s.centroidWeightsIndicator…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.centroid_eq_affineCombination_fintype`：centroid_eq_affineCombinat
ion_fintype [Fintype ι] (p : ι -> P) : s.centroid k p = univ.affineCombination k
 p (s.centroidWeightsIndicator k)
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.indicator_univ`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (f :
 α → M), Set.univ.indicator f = f
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)

--- 原说明 ---
Over a characteristic-zero division ring, the centroids given by
two subsets of the points of a simplex are equal if and only if those
faces are given by the same subset of points.
-/
theorem centroid_eq_iff [CharZero k] {n : ℕ} (s : Simplex k P n) {fs₁ fs₂ : Finset (Fin (n + 1))}
    {m₁ m₂ : ℕ} (h₁ : #fs₁ = m₁ + 1) (h₂ : #fs₂ = m₂ + 1) :
    fs₁.centroid k s.points = fs₂.centroid k s.points ↔ fs₁ = fs₂ := by
  refine ⟨fun h => ?_, @congrArg _ _ fs₁ fs₂ (fun z => Finset.centroid k z s.points)⟩
  rw [Finset.centroid_eq_affineCombination_fintype,
    Finset.centroid_eq_affineCombination_fintype] at h
  have ha :=
    (affineIndependent_iff_indicator_eq_of_affineCombination_eq k s.points).1 s.independent _ _ _ _
      (fs₁.sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one k h₁)
      (fs₂.sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one k h₂) h
  simp_rw [Finset.coe_univ, Set.indicator_univ, funext_iff,
    Finset.centroidWeightsIndicator_def, Finset.centroidWeights, h₁, h₂] at ha
  ext i
  specialize ha i
  have key : ∀ n : ℕ, (n : k) + 1 ≠ 0 := fun n h => by norm_cast at h
  -- we should be able to golf this to
  -- `refine ⟨fun hi ↦ decidable.by_contradiction (fun hni ↦ ?_), ...⟩`,
  -- but for some unknown reason it doesn't work.
  constructor <;> intro hi <;> by_contra hni
  · simp [hni, hi, key] at ha
  · simpa [hni, hi, key] using ha.symm

/-- Over a characteristic-zero division ring, the centroids of two
faces of a simplex are equal if and only if those faces are given by
the same subset of points. -/
/-
**Affine.Simplex.face_centroid_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`
。
形式化陈述：face_centroid_eq_iff [CharZero k] {n : Nat} (s : Simplex k P n) {fs₁ fs₂ :
 Finset (Fin (n + 1))} {m₁ m₂ : Nat} (h₁ : #fs₁ = m₁ + 1) (h₂ : #fs₂ = m₂ + 1) :
 Finset.univ.centroid k (s.face h₁).points = Finset.univ.centroid k (s.face h₂).
points ↔ fs₁ = fs₂
参数：s : Simplex k P n；Fin (n + 1)；h₁ : #fs₁ = m₁ + 1；h₂ : #fs₂ = m₂ + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.face_centroid_eq_centroid`：face_centroid_eq_centroid {n :
 Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1
) : Finset.univ.centroid k (s.…
· 使用定理 `Affine.Simplex.centroid_eq_iff`：centroid_eq_iff [CharZero k] {n : Nat} (
s : Simplex k P n) {fs₁ fs₂ : Finset (Fin (n + 1))} {m₁ m₂ : Nat} (h₁ : #fs₁ = m
₁ + 1) (h₂ : #fs₂ = …

--- 原说明 ---
Over a characteristic-zero division ring, the centroids of two
faces of a simplex are equal if and only if those faces are given by
the same subset of points.
-/
theorem face_centroid_eq_iff [CharZero k] {n : ℕ} (s : Simplex k P n)
    {fs₁ fs₂ : Finset (Fin (n + 1))} {m₁ m₂ : ℕ} (h₁ : #fs₁ = m₁ + 1) (h₂ : #fs₂ = m₂ + 1) :
    Finset.univ.centroid k (s.face h₁).points = Finset.univ.centroid k (s.face h₂).points ↔
      fs₁ = fs₂ := by
  rw [face_centroid_eq_centroid, face_centroid_eq_centroid]
  exact s.centroid_eq_iff h₁ h₂

/-- Two simplices with the same points have the same centroid. -/
/-
**Affine.Simplex.centroid_eq_of_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simpl
ex`。
形式化陈述：centroid_eq_of_range_eq {n : Nat} {s₁ s₂ : Simplex k P n} (h : Set.range s
₁.points = Set.range s₂.points) : Finset.univ.centroid k s₁.points = Finset.univ
.centroid k s₂.points
参数：h : Set.range s₁.points = Set.range s₂.points。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.centroid_eq_of_inj_on_of_image_eq`：centroid_eq_of_inj_on_of_image
_eq {p : ι -> P} (hi : forall i in s, forall j in s, p i = p j -> i = j) {p₂ : ι
₂ -> P} (hi₂ : forall i in s₂,…
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f

--- 原说明 ---
Two simplices with the same points have the same centroid.
-/
theorem centroid_eq_of_range_eq {n : ℕ} {s₁ s₂ : Simplex k P n}
    (h : Set.range s₁.points = Set.range s₂.points) :
    Finset.univ.centroid k s₁.points = Finset.univ.centroid k s₂.points := by
  rw [← Set.image_univ, ← Set.image_univ, ← Finset.coe_univ] at h
  exact
    Finset.univ.centroid_eq_of_inj_on_of_image_eq k _
      (fun _ _ _ _ he => AffineIndependent.injective s₁.independent he)
      (fun _ _ _ _ he => AffineIndependent.injective s₂.independent he) h

/-- Replacing a vertex of a simplex by its centroid preserves affine independence. -/
/-
**Affine.Simplex.affineIndependent_points_update_centroid** 是 Mathlib 中的一个定理，位于命
名空间 `Affine.Simplex`。
形式化陈述：affineIndependent_points_update_centroid [CharZero k] (s : Simplex k P n) 
(i : Fin (n + 1)) : AffineIndependent k (Function.update s.points i s.centroid)
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.centroid_notMem_affineSpan_of_ne_univ`：centroid_notMem_af
fineSpan_of_ne_univ [CharZero k] (s : Simplex k P n) {t : Set (Fin (n + 1))} (ht
 : t != Set.univ) : s.centroid ∉ affineSpa…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AffineIndependent.affineIndependent_update_of_notMem_affineSpan`：AffineI
ndependent.affineIndependent_update_of_notMem_affineSpan [DecidableEq ι] {p : ι 
-> P} (ha : AffineIndependent k p) {i : ι} {p₀ : P} (…
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …

--- 原说明 ---
Replacing a vertex of a simplex by its centroid preserves affine independence.
-/
theorem affineIndependent_points_update_centroid [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    AffineIndependent k (Function.update s.points i s.centroid) := by
  have : s.centroid ∉ affineSpan k (s.points '' {i}ᶜ) :=
    s.centroid_notMem_affineSpan_of_ne_univ (by simp)
  exact AffineIndependent.affineIndependent_update_of_notMem_affineSpan s.independent this
/-
**Affine.Simplex.centroid_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：centroid_map [CharZero k] {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] 
[AffineSpace V₂ P₂] {n : Nat} (s : Simplex k P n) (f : P ->ᵃ[k] P₂) (hf : Functi
on.Injective f) : (s.map f hf).centroid = f (s.centroid)
参数：s : Simplex k P n；f : P ->ᵃ[k] P₂；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.centroid.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : Type 
u_3} [inst : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module
 k V] [inst_3 : Ad…
· 使用定理 `Affine.Simplex.map_points`：∀ {k : Type u_1} {V : Type u_2} {V₂ : Type u_
3} {P : Type u_5} {P₂ : Type u_6} [inst : Ring k] [inst_1 : AddCommGroup V]   [i
nst_2 : AddComm…
· 使用定理 `Affine.Simplex.centroid_eq_affineCombination`：centroid_eq_affineCombinat
ion (s : Simplex k P n) : s.centroid = affineCombination k univ s.points (centro
idWeights k univ)
· 使用定理 `Finset.map_affineCombination`：map_affineCombination {V₂ P₂ : Type*} [Add
CommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] (p : ι -> P) (w : ι -> k) (hw : 
s.sum w = 1) (f : …
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_card_ne_zero`：sum_centroidWeights_e
q_one_of_card_ne_zero [CharZero k] (h : #s != 0) : ∑ i in s, s.centroidWeights k
 i = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.centroid.eq_1`：∀ (k : Type u_1) {V : Type u_2} {P : Type u_3} [in
st : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module k V] [i
nst_3 : Ad…
-/
theorem centroid_map [CharZero k] {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂]
    [AffineSpace V₂ P₂] {n : ℕ} (s : Simplex k P n) (f : P →ᵃ[k] P₂)
    (hf : Function.Injective f) :
    (s.map f hf).centroid = f (s.centroid) := by
  rw [centroid, map_points, centroid_eq_affineCombination, Finset.map_affineCombination]
  · rw [Finset.centroid]
  · rw [sum_centroidWeights_eq_one_of_card_ne_zero]
    simp
/-
**Affine.Simplex.centroid_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：centroid_reindex {m n : Nat} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n
 + 1)) : (s.reindex e).centroid = s.centroid
参数：s : Simplex k P m；e : Fin (m + 1) ≃ Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.centroid.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : Type 
u_3} [inst : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module
 k V] [inst_3 : Ad…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Affine.Simplex.centroid_eq_affineCombination`：centroid_eq_affineCombinat
ion (s : Simplex k P n) : s.centroid = affineCombination k univ s.points (centro
idWeights k univ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_eq`：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card 
α = card β ↔ Nonempty (α ≃ β)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.univ_map_embedding`：Finset.univ_map_embedding {α : Type*} [Fintyp
e α] (e : α ↪ α) : univ.map e = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `Finset.affineCombination_map`：affineCombination_map (e : ι₂ ↪ ι) (w : ι 
-> k) (p : ι -> P) : (s₂.map e).affineCombination k p w = s₂.affineCombination k
 (p ∘ e) (w ∘ e)
-/
theorem centroid_reindex {m n : ℕ} (s : Simplex k P m)
    (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).centroid = s.centroid := by
  rw [centroid, centroid]
  simp only [centroid_eq_affineCombination]
  simp only [reindex]
  have h_eq : m = n := by simpa using Fintype.card_eq.2 ⟨e⟩
  subst h_eq
  convert! Finset.univ.affineCombination_map e.toEmbedding _ _ <;> simp [Function.comp_assoc]
/-
**Affine.Simplex.centroid_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：centroid_restrict [CharZero k] {n : Nat} (s : Simplex k P n) (S : AffineSu
bspace k P) (hS : affineSpan k (Set.range s.points) <= S) : haveI
参数：s : Simplex k P n；S : AffineSubspace k P；hS : affineSpan k (Set.range s.point
s) <= S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Affine.Simplex.centroid_map`：centroid_map [CharZero k] {V₂ P₂ : Type*} [
AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] {n : Nat} (s : Simplex k P n)
 (f : P ->ᵃ[k] P₂…
-/
theorem centroid_restrict [CharZero k] {n : ℕ} (s : Simplex k P n) (S : AffineSubspace k P)
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).centroid = s.centroid := by
  rw [eq_comm]
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  have hf : Function.Injective (S.subtype) := by
    simp only [coe_subtype, Subtype.val_injective]
  exact (s.restrict S hS).centroid_map S.subtype hf

variable [NeZero n]

/-- The faceOppositeCentroid is the centroid of the face opposite to the vertex indexed by `i`. -/
/-
**Affine.Simplex.faceOppositeCentroid** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`
。
形式化陈述：faceOppositeCentroid (s : Affine.Simplex k P n) (i : Fin (n + 1)) : P
参数：s : Affine.Simplex k P n；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The faceOppositeCentroid is the centroid of the face opposite to the vertex inde
xed by `i`.
-/
def faceOppositeCentroid (s : Affine.Simplex k P n) (i : Fin (n + 1)) : P :=
  (s.faceOpposite i).centroid

/-- The centroid of the face opposite a vertex lies in the affine span of that face. -/
/-
**Affine.Simplex.faceOppositeCentroid_mem_affineSpan_face** 是 Mathlib 中的一个定理，位于命
名空间 `Affine.Simplex`。
形式化陈述：faceOppositeCentroid_mem_affineSpan_face [CharZero k] (s : Simplex k P n) 
(i : Fin (n + 1)) : s.faceOppositeCentroid i in affineSpan k (Set.range (s.faceO
pposite i).points)
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.centroid_mem_affineSpan`：centroid_mem_affineSpan [CharZer
o k] {n : Nat} (s : Simplex k P n) : s.centroid in affineSpan k (Set.range s.poi
nts)

--- 原说明 ---
The centroid of the face opposite a vertex lies in the affine span of that face.
-/
theorem faceOppositeCentroid_mem_affineSpan_face [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i ∈ affineSpan k (Set.range (s.faceOpposite i).points) :=
  centroid_mem_affineSpan (s.faceOpposite i)

/-- The `faceOppositeCentroid` is the affine combination of the complement vertices with equal
weights `1/n`. -/
/-
**Affine.Simplex.faceOppositeCentroid_eq_affineCombination** 是 Mathlib 中的一个定理，位于
命名空间 `Affine.Simplex`。
形式化陈述：faceOppositeCentroid_eq_affineCombination (s : Affine.Simplex k P n) (i : 
Fin (n + 1)) : s.faceOppositeCentroid i = ((affineCombination k {i}ᶜ s.points) f
un _ => (↑n)⁻¹)
参数：s : Affine.Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Affine.Simplex.face_centroid_eq_centroid`：face_centroid_eq_centroid {n :
 Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1
) : Finset.univ.centroid k (s.…
· 使用定理 `Finset.centroid_def`：centroid_def (p : ι -> P) : s.centroid k p = s.affi
neCombination k p (s.centroidWeights k)
· 使用定理 `Finset.centroidWeights_eq_const`：centroidWeights_eq_const : s.centroidWe
ights k = Function.const ι (#s : k)⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
The `faceOppositeCentroid` is the affine combination of the complement vertices 
with equal
weights `1/n`.
-/
theorem faceOppositeCentroid_eq_affineCombination (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = ((affineCombination k {i}ᶜ s.points) fun _ ↦ (↑n)⁻¹) := by
  unfold faceOppositeCentroid
  have : s.faceOpposite i = s.face (fs := {i}ᶜ) (by simp [card_compl, NeZero.one_le]) := by rfl
  rw [this]
  unfold centroid
  rw [face_centroid_eq_centroid, centroid_def, centroidWeights_eq_const, card_compl]
  simp only [Fintype.card_fin, card_singleton, add_tsub_cancel_right]
  rfl

/-- The vector from a vertex to the corresponding `faceOppositeCentroid` equals the average of the
displacements to the other vertices. -/
/-
**Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_sum_vsub** 是 Mathlib 中的
一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：faceOppositeCentroid_vsub_point_eq_smul_sum_vsub [CharZero k] (s : Affine.
Simplex k P n) (i : Fin (n + 1)) : s.faceOppositeCentroid i -ᵥ (s.points i) = (n
 : k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i)
参数：s : Affine.Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.faceOppositeCentroid_eq_affineCombination`：faceOppositeCe
ntroid_eq_affineCombination (s : Affine.Simplex k P n) (i : Fin (n + 1)) : s.fac
eOppositeCentroid i = ((affineCombination k {i…
· 使用定理 `Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one`：affi
neCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι -> k) (p : ι -> P
) (h : ∑ i in s, w i = 1) (b : P) : s.affineCombination …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_compl_add_sum`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (s : Finset ι)   (f : ι
 → M), ∑ i ∈ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x

--- 原说明 ---
The vector from a vertex to the corresponding `faceOppositeCentroid` equals the 
average of the
displacements to the other vertices.
-/
theorem faceOppositeCentroid_vsub_point_eq_smul_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ (s.points i) = (n : k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i) := by
  rw [faceOppositeCentroid_eq_affineCombination,
    affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ ?_ (s.points i)]
  · simp only [weightedVSubOfPoint_apply, vadd_vsub]
    have h (i : Fin (n + 1)) : ∑ j ∈ {i}ᶜ, (n : k)⁻¹ • (s.points j -ᵥ s.points i) =
      ∑ j : (Fin (n + 1)), ((n : k)⁻¹ • (s.points j -ᵥ s.points i)) := by
      rw [← Finset.sum_compl_add_sum {i}]
      simp
    rw [h i, smul_sum]
  · simp only [sum_const, card_compl, Fintype.card_fin, card_singleton, add_tsub_cancel_right,
      nsmul_eq_mul]
    rw [mul_inv_cancel₀ (NeZero.ne (n : k))]

/-- The `faceOppositeCentroid` equals the average displacement from a vertex plus that vertex. -/
/-
**Affine.Simplex.faceOppositeCentroid_eq_sum_vsub_vadd** 是 Mathlib 中的一个定理，位于命名空间
 `Affine.Simplex`。
形式化陈述：faceOppositeCentroid_eq_sum_vsub_vadd [CharZero k] (s : Affine.Simplex k P
 n) (i : Fin (n + 1)) : s.faceOppositeCentroid i = (n : k)⁻¹ • ∑ x, (s.points x 
-ᵥ s.points i) +ᵥ (s.points i)
参数：s : Affine.Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_sum_vsub`：faceOpp
ositeCentroid_vsub_point_eq_smul_sum_vsub [CharZero k] (s : Affine.Simplex k P n
) (i : Fin (n + 1)) : s.faceOppositeCentroid i -ᵥ (s.…
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁

--- 原说明 ---
The `faceOppositeCentroid` equals the average displacement from a vertex plus th
at vertex.
-/
theorem faceOppositeCentroid_eq_sum_vsub_vadd [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = (n : k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i) +ᵥ (s.points i) := by
  rw [← faceOppositeCentroid_vsub_point_eq_smul_sum_vsub s i, vsub_vadd]

/-- The vector from a vertex to its `faceOppositeCentroid` equals the average of reversed
displacements. -/
/-
**Affine.Simplex.point_vsub_faceOppositeCentroid_eq_smul_sum_vsub** 是 Mathlib 中的
一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：point_vsub_faceOppositeCentroid_eq_smul_sum_vsub [CharZero k] (s : Affine.
Simplex k P n) (i : Fin (n + 1)) : s.points i -ᵥ s.faceOppositeCentroid i = (n :
 k)⁻¹ • ∑ x, (s.points i -ᵥ s.points x)
参数：s : Affine.Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_sum_vsub`：faceOpp
ositeCentroid_vsub_point_eq_smul_sum_vsub [CharZero k] (s : Affine.Simplex k P n
) (i : Fin (n + 1)) : s.faceOppositeCentroid i -ᵥ (s.…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Lean.Grind.Ring.neg_eq_mul_neg_one`：∀ {α : Type u} [inst : Grind.Ring α]
 (a : α), -a = a * -1
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The vector from a vertex to its `faceOppositeCentroid` equals the average of rev
ersed
displacements.
-/
theorem point_vsub_faceOppositeCentroid_eq_smul_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.points i -ᵥ s.faceOppositeCentroid i = (n : k)⁻¹ • ∑ x, (s.points i -ᵥ s.points x) := by
  rw [← neg_vsub_eq_vsub_rev, faceOppositeCentroid_vsub_point_eq_smul_sum_vsub, ← neg_smul,
    Lean.Grind.Ring.neg_eq_mul_neg_one, ← smul_smul, smul_sum]
  simp only [neg_smul, one_smul, neg_vsub_eq_vsub_rev]
/-
**Affine.Simplex.smul_faceOppositeCentroid_vsub_point_eq_sum_vsub** 是 Mathlib 中的
一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：smul_faceOppositeCentroid_vsub_point_eq_sum_vsub [CharZero k] (s : Affine.
Simplex k P n) (i : Fin (n + 1)) : (n : k) • (s.faceOppositeCentroid i -ᵥ s.poin
ts i) = ∑ x, (s.points x -ᵥ s.points i)
参数：s : Affine.Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.faceOppositeCentroid_eq_sum_vsub_vadd`：faceOppositeCentro
id_eq_sum_vsub_vadd [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) : 
s.faceOppositeCentroid i = (n : k)⁻¹ • ∑ x…
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_faceOppositeCentroid_vsub_point_eq_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    (n : k) • (s.faceOppositeCentroid i -ᵥ s.points i) = ∑ x, (s.points x -ᵥ s.points i) := by
  simp [faceOppositeCentroid_eq_sum_vsub_vadd, smul_smul, mul_inv_cancel₀ (NeZero.ne (n : k)),
    one_smul]
/-
**Affine.Simplex.smul_centroid_vsub_point_eq_smul_faceOppositeCentroid_vsub_poin
t** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：smul_centroid_vsub_point_eq_smul_faceOppositeCentroid_vsub_point [CharZero
 k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) : (n + 1 : k) • (s.centroid -ᵥ 
s.points i) = (n : k) • (s.faceOppositeCentroid i -ᵥ s.points i)
参数：s : Affine.Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.smul_faceOppositeCentroid_vsub_point_eq_sum_vsub`：smul_fa
ceOppositeCentroid_vsub_point_eq_sum_vsub [CharZero k] (s : Affine.Simplex k P n
) (i : Fin (n + 1)) : (n : k) • (s.faceOppositeCentro…
· 使用定理 `Affine.Simplex.smul_centroid_vsub_point_eq_sum_vsub`：smul_centroid_vsub_
point_eq_sum_vsub [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) : ((n : k) 
+ 1) • (s.centroid -ᵥ s.points i) = ∑ x, …
-/
theorem smul_centroid_vsub_point_eq_smul_faceOppositeCentroid_vsub_point [CharZero k]
    (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    (n + 1 : k) • (s.centroid -ᵥ s.points i) =
    (n : k) • (s.faceOppositeCentroid i -ᵥ s.points i) := by
  rw [smul_faceOppositeCentroid_vsub_point_eq_sum_vsub s i,
    smul_centroid_vsub_point_eq_sum_vsub s i]

/-- The vector between two `faceOppositeCentroid` equals `n⁻¹` times the vector between the
corresponding vertices. -/
/-
**Affine.Simplex.faceOppositeCentroid_vsub_faceOppositeCentroid** 是 Mathlib 中的一个
定理，位于命名空间 `Affine.Simplex`。
形式化陈述：faceOppositeCentroid_vsub_faceOppositeCentroid [CharZero k] (s : Affine.Si
mplex k P n) (i j : Fin (n + 1)) : s.faceOppositeCentroid i -ᵥ s.faceOppositeCen
troid j = (n : k)⁻¹ • (s.points j -ᵥ s.points i)
参数：s : Affine.Simplex k P n；i j : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.faceOppositeCentroid_eq_sum_vsub_vadd`：faceOppositeCentro
id_eq_sum_vsub_vadd [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) : 
s.faceOppositeCentroid i = (n : k)⁻¹ • ∑ x…
· 使用定理 `vadd_vsub_vadd_comm`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCommGrou
p G] [inst_1 : AddTorsor G P] (v₁ v₂ : G) (p₁ p₂ : P),   (v₁ +ᵥ p₁) -ᵥ (v₂ +ᵥ p₂
) = v₁ - …
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `sub_sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c - a - (c - b) = b - a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The vector between two `faceOppositeCentroid` equals `n⁻¹` times the vector betw
een the
corresponding vertices.
-/
theorem faceOppositeCentroid_vsub_faceOppositeCentroid [CharZero k] (s : Affine.Simplex k P n)
    (i j : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ s.faceOppositeCentroid j =
    (n : k)⁻¹ • (s.points j -ᵥ s.points i) := by
  rw [faceOppositeCentroid_eq_sum_vsub_vadd s i, faceOppositeCentroid_eq_sum_vsub_vadd s j,
    vadd_vsub_vadd_comm _ _ (s.points i) (s.points j)]
  have h1 (i : Fin (n + 1)) : ∑ x, (s.points x -ᵥ s.points i) =
      ∑ x, (s.points x -ᵥ s.points 0 - (s.points i -ᵥ s.points 0)) := by
    apply sum_congr rfl
    simp
  simp_rw [h1 i, h1 j, sum_sub_distrib]
  rw [smul_sub, smul_sub, sub_sub_sub_cancel_left, ← smul_sub, ← sum_sub_distrib,
    vsub_sub_vsub_cancel_right, sum_const, card_univ, Fintype.card_fin]
  have : (s.points i -ᵥ s.points j) = -(s.points j -ᵥ s.points i) := by simp
  rw [this, ← sub_eq_add_neg, add_smul, sub_eq_iff_eq_add, one_smul, smul_add, add_comm]
  have : (n : k)⁻¹ • n • (s.points j -ᵥ s.points i) =
      (n : k)⁻¹ • (n : k) • (s.points j -ᵥ s.points i) := by
    norm_cast0
    congr 1
  rw [this, smul_smul, inv_eq_one_div, one_div_mul_cancel (NeZero.ne (n : k)), one_smul]

/-- The vector from a vertex to its `faceOppositeCentroid` is `(n+1)` times the vector from the
`centroid` to that `faceOppositeCentroid`. -/
/-
**Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_vsub** 是 Mathlib 中的一个定理
，位于命名空间 `Affine.Simplex`。
形式化陈述：faceOppositeCentroid_vsub_point_eq_smul_vsub [CharZero k] (s : Simplex k P
 n) (i : Fin (n + 1)) : s.faceOppositeCentroid i -ᵥ s.points i = (n + 1 : k) • (
s.faceOppositeCentroid i -ᵥ s.centroid)
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_sum_vsub`：faceOpp
ositeCentroid_vsub_point_eq_smul_sum_vsub [CharZero k] (s : Affine.Simplex k P n
) (i : Fin (n + 1)) : s.faceOppositeCentroid i -ᵥ (s.…
· 使用定理 `Affine.Simplex.centroid_vsub_eq`：centroid_vsub_eq {n : Nat} [CharZero k]
 (s : Simplex k P n) (p : P) : s.centroid -ᵥ p = (n + 1 : k)⁻¹ • ∑ x, (s.points 
x -ᵥ p)
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
The vector from a vertex to its `faceOppositeCentroid` is `(n+1)` times the vect
or from the
`centroid` to that `faceOppositeCentroid`.
-/
theorem faceOppositeCentroid_vsub_point_eq_smul_vsub [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ s.points i =
    (n + 1 : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) := by
  rw [← vsub_sub_vsub_cancel_right _ (s.centroid) (s.points i),
    faceOppositeCentroid_vsub_point_eq_smul_sum_vsub, centroid_vsub_eq,
    ← sub_smul, smul_smul]
  congr
  rw [mul_sub, add_mul, mul_inv_cancel₀ (NeZero.ne (n : k)), mul_inv_cancel₀ (by norm_cast),
    one_mul]
  grind
/-
**Affine.Simplex.point_vsub_faceOppositeCentroid_eq_smul_vsub** 是 Mathlib 中的一个定理
，位于命名空间 `Affine.Simplex`。
形式化陈述：point_vsub_faceOppositeCentroid_eq_smul_vsub [CharZero k] (s : Simplex k P
 n) (i : Fin (n + 1)) : s.points i -ᵥ s.faceOppositeCentroid i = (n + 1 : k) • (
s.centroid -ᵥ s.faceOppositeCentroid i)
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_vsub`：faceOpposit
eCentroid_vsub_point_eq_smul_vsub [CharZero k] (s : Simplex k P n) (i : Fin (n +
 1)) : s.faceOppositeCentroid i -ᵥ s.points i = (…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_smul_neg`：neg_smul_neg : -r • -x = r • x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem point_vsub_faceOppositeCentroid_eq_smul_vsub [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    s.points i -ᵥ s.faceOppositeCentroid i =
    (n + 1 : k) • (s.centroid -ᵥ s.faceOppositeCentroid i) := by
  rw [← neg_vsub_eq_vsub_rev, faceOppositeCentroid_vsub_point_eq_smul_vsub, ← neg_smul,
    ← neg_smul_neg, neg_vsub_eq_vsub_rev, neg_neg]

/-- *Commandino's theorem* : For n-simplex, the vector from a vertex to the `centroid`
equals `n` times the vector from the `centroid` to the corresponding `faceOppositeCentroid`. -/
/-
**Affine.Simplex.point_vsub_centroid_eq_smul_vsub** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ine.Simplex`。
形式化陈述：point_vsub_centroid_eq_smul_vsub [CharZero k] (s : Simplex k P n) (i : Fin
 (n + 1)) : s.points i -ᵥ s.centroid = (n : k) • (s.centroid -ᵥ s.faceOppositeCe
ntroid i)
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_sum_vsub`：faceOpp
ositeCentroid_vsub_point_eq_smul_sum_vsub [CharZero k] (s : Affine.Simplex k P n
) (i : Fin (n + 1)) : s.faceOppositeCentroid i -ᵥ (s.…
· 使用定理 `Affine.Simplex.centroid_vsub_eq`：centroid_vsub_eq {n : Nat} [CharZero k]
 (s : Simplex k P n) (p : P) : s.centroid -ᵥ p = (n + 1 : k)⁻¹ • ∑ x, (s.points 
x -ᵥ p)
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p

--- 原说明 ---
*Commandino's theorem* : For n-simplex, the vector from a vertex to the `centroi
d`
equals `n` times the vector from the `centroid` to the corresponding `faceOpposi
teCentroid`.
-/
theorem point_vsub_centroid_eq_smul_vsub [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.points i -ᵥ s.centroid = (n : k) • (s.centroid -ᵥ s.faceOppositeCentroid i) := by
  symm
  rw [← vsub_sub_vsub_cancel_right _ _ (s.points i),
    faceOppositeCentroid_vsub_point_eq_smul_sum_vsub,
    centroid_vsub_eq, ← neg_vsub_eq_vsub_rev,
    centroid_vsub_eq, ← sub_smul, smul_smul, ← neg_smul]
  congr
  simp_rw [mul_sub, sub_eq_iff_eq_add, neg_add_eq_sub]
  symm
  rw [sub_eq_iff_eq_add, mul_inv_cancel₀ (NeZero.ne (n : k))]
  have : (↑n + (1 : k))⁻¹ = 1 * (↑n + (1 : k))⁻¹ := by simp
  nth_rw 2 [this]
  rw [← add_mul, mul_inv_cancel₀ (by norm_cast)]

/-- Reverse version of `point_vsub_centroid_eq_smul_vsub`. -/
/-
**Affine.Simplex.centroid_vsub_point_eq_smul_vsub** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ine.Simplex`。
形式化陈述：centroid_vsub_point_eq_smul_vsub [CharZero k] (s : Simplex k P n) (i : Fin
 (n + 1)) : s.centroid -ᵥ s.points i = (n : k) • (s.faceOppositeCentroid i -ᵥ s.
centroid)
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `Affine.Simplex.point_vsub_centroid_eq_smul_vsub`：point_vsub_centroid_eq_
smul_vsub [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) : s.points i -ᵥ s.c
entroid = (n : k) • (s.centroid -ᵥ s.…
· 使用定理 `neg_smul_neg`：neg_smul_neg : -r • -x = r • x
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a

--- 原说明 ---
Reverse version of `point_vsub_centroid_eq_smul_vsub`.
-/
theorem centroid_vsub_point_eq_smul_vsub [CharZero k]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid -ᵥ s.points i = (n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) := by
  rw [← neg_vsub_eq_vsub_rev, point_vsub_centroid_eq_smul_vsub, ← neg_smul_neg,
    neg_vsub_eq_vsub_rev, ← neg_smul, neg_neg]

/-- The vector from `centroid` to a vertex corresponding `faceOppositeCentroid` is `n⁻¹` of the
vector from the vertex to the centroid. -/
/-
**Affine.Simplex.faceOppositeCentroid_vsub_centroid_eq_smul_vsub** 是 Mathlib 中的一
个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：faceOppositeCentroid_vsub_centroid_eq_smul_vsub [CharZero k] (s : Simplex 
k P n) (i : Fin (n + 1)) : s.faceOppositeCentroid i -ᵥ s.centroid = (n : k)⁻¹ • 
(s.centroid -ᵥ s.points i)
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.centroid_vsub_point_eq_smul_vsub`：centroid_vsub_point_eq_
smul_vsub [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) : s.centroid -ᵥ s.p
oints i = (n : k) • (s.faceOppositeCe…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
The vector from `centroid` to a vertex corresponding `faceOppositeCentroid` is `
n⁻¹` of the
vector from the vertex to the centroid.
-/
theorem faceOppositeCentroid_vsub_centroid_eq_smul_vsub [CharZero k]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ s.centroid = (n : k)⁻¹ • (s.centroid -ᵥ s.points i) := by
  rw [centroid_vsub_point_eq_smul_vsub, smul_smul, inv_mul_cancel₀ (NeZero.ne (n : k)), one_smul]

/-- Reverse version of `faceOppositeCentroid_vsub_centroid_eq_smul_vsub` -/
/-
**Affine.Simplex.centroid_vsub_faceOppositeCentroid_eq_smul_vsub** 是 Mathlib 中的一
个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：centroid_vsub_faceOppositeCentroid_eq_smul_vsub [CharZero k] (s : Simplex 
k P n) (i : Fin (n + 1)) : s.centroid -ᵥ s.faceOppositeCentroid i = (n : k)⁻¹ • 
(s.points i -ᵥ s.centroid)
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.point_vsub_centroid_eq_smul_vsub`：point_vsub_centroid_eq_
smul_vsub [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) : s.points i -ᵥ s.c
entroid = (n : k) • (s.centroid -ᵥ s.…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
Reverse version of `faceOppositeCentroid_vsub_centroid_eq_smul_vsub`
-/
theorem centroid_vsub_faceOppositeCentroid_eq_smul_vsub [CharZero k]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid -ᵥ s.faceOppositeCentroid i = (n : k)⁻¹ • (s.points i -ᵥ s.centroid) := by
  rw [point_vsub_centroid_eq_smul_vsub, smul_smul, inv_mul_cancel₀ (NeZero.ne (n : k)), one_smul]

/-- The centroid of an n-simplex can be obtained from a vertex by adding
`n` times the vector from the centroid to the `faceOppositeCentroid`. -/
/-
**Affine.Simplex.centroid_eq_smul_vsub_vadd_point** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ine.Simplex`。
形式化陈述：centroid_eq_smul_vsub_vadd_point [CharZero k] (s : Simplex k P n) (i : Fin
 (n + 1)) : s.centroid = (n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) +ᵥ s
.points i
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.centroid_vsub_point_eq_smul_vsub`：centroid_vsub_point_eq_
smul_vsub [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) : s.centroid -ᵥ s.p
oints i = (n : k) • (s.faceOppositeCe…
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁

--- 原说明 ---
The centroid of an n-simplex can be obtained from a vertex by adding
`n` times the vector from the centroid to the `faceOppositeCentroid`.
-/
theorem centroid_eq_smul_vsub_vadd_point [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid = (n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) +ᵥ s.points i := by
  rw [← centroid_vsub_point_eq_smul_vsub, vsub_vadd]

/-- The point `faceOppositeCentroid` of an n-simplex can be obtained from
the centroid by adding `n⁻¹` times the vector from the vertex to the centroid. -/
/-
**Affine.Simplex.faceOppositeCentroid_eq_smul_vsub_vadd_point** 是 Mathlib 中的一个定理
，位于命名空间 `Affine.Simplex`。
形式化陈述：faceOppositeCentroid_eq_smul_vsub_vadd_point [CharZero k] (s : Simplex k P
 n) (i : Fin (n + 1)) : s.faceOppositeCentroid i = (n : k)⁻¹ • (s.centroid -ᵥ s.
points i) +ᵥ s.centroid
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.centroid_vsub_point_eq_smul_vsub`：centroid_vsub_point_eq_
smul_vsub [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) : s.centroid -ᵥ s.p
oints i = (n : k) • (s.faceOppositeCe…
· 使用定理 `eq_vadd_iff_vsub_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p₁ : P) (g : G) (p₂ : P),   p₁ = g +ᵥ p₂ ↔ p₁ -ᵥ p₂ = g
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
The point `faceOppositeCentroid` of an n-simplex can be obtained from
the centroid by adding `n⁻¹` times the vector from the vertex to the centroid.
-/
theorem faceOppositeCentroid_eq_smul_vsub_vadd_point [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = (n : k)⁻¹ • (s.centroid -ᵥ s.points i) +ᵥ s.centroid := by
  rw [centroid_vsub_point_eq_smul_vsub, eq_vadd_iff_vsub_eq, smul_smul,
    inv_mul_cancel₀ (NeZero.ne (n : k)), one_smul]
/-
**Affine.Simplex.faceOppositeCentroid_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simp
lex`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : DivisionRing k] [in
st_1 : AddCommGroup V]   [inst_2 : _root_.Module k V] [inst_3 : AddTorsor V P] [
CharZero k] {V₂ : Type u_4} {P₂ : Type u_5}   [inst_5 : AddCommGroup V₂] [inst_6
 : _root_.Module k V₂] [inst_7 : AddTorsor V₂ P₂] {n : ℕ} [inst_8 : NeZero n]   
(s : Affine.Simplex k P n) (f : P →ᵃ[k] P₂) (hf : Function.Injective ⇑f) {i : Fi
n (n + 1)},   (s.map f hf).faceOppositeCentroid i = f (s.faceOppositeCentroid i)
参数：s : Affine.Simplex k P n；f : P →ᵃ[k] P₂；hf : Function.Injective ⇑f；n + 1；s.ma
p f hf；s.faceOppositeCentroid i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Affine.Simplex.centroid_eq_affineCombination`：centroid_eq_affineCombinat
ion (s : Simplex k P n) : s.centroid = affineCombination k univ s.points (centro
idWeights k univ)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Affine.Simplex.map_points`：∀ {k : Type u_1} {V : Type u_2} {V₂ : Type u_
3} {P : Type u_5} {P₂ : Type u_6} [inst : Ring k] [inst_1 : AddCommGroup V]   [i
nst_2 : AddComm…
· 使用定理 `Finset.map_affineCombination`：map_affineCombination {V₂ P₂ : Type*} [Add
CommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] (p : ι -> P) (w : ι -> k) (hw : 
s.sum w = 1) (f : …
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_card_ne_zero`：sum_centroidWeights_e
q_one_of_card_ne_zero [CharZero k] (h : #s != 0) : ∑ i in s, s.centroidWeights k
 i = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] theorem faceOppositeCentroid_map [CharZero k] {V₂ P₂ : Type*} [AddCommGroup V₂]
    [Module k V₂] [AffineSpace V₂ P₂] {n : ℕ} [NeZero n] (s : Simplex k P n) (f : P →ᵃ[k] P₂)
    (hf : Function.Injective f) {i : Fin (n + 1)} :
    (s.map f hf).faceOppositeCentroid i = f (s.faceOppositeCentroid i) := by
  simp only [faceOppositeCentroid, faceOpposite_map, centroid_eq_affineCombination, map_points]
  rw [Finset.map_affineCombination]
  rw [sum_centroidWeights_eq_one_of_card_ne_zero]
  simp
/-
**Affine.Simplex.faceOppositeCentroid_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine
.Simplex`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : DivisionRing k] [in
st_1 : AddCommGroup V]   [inst_2 : _root_.Module k V] [inst_3 : AddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] [CharZero k]   (s : Affine.Simplex k P n) (S : Affine
Subspace k P) (hS : affineSpan k (Set.range s.points) ≤ S) {i : Fin (n + 1)},   
↑((s.restrict S hS).faceOppositeCentroid i) = s.faceOppositeCentroid i
参数：s : Affine.Simplex k P n；S : AffineSubspace k P；hS : affineSpan k (Set.range 
s.points) ≤ S；n + 1；(s.restrict S hS).faceOppositeCentroid i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Affine.Simplex.faceOppositeCentroid_map`：∀ {k : Type u_1} {V : Type u_2}
 {P : Type u_3} [inst : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _r
oot_.Module k V] [inst_3 : Ad…
-/
@[simp] theorem faceOppositeCentroid_restrict [CharZero k] (s : Simplex k P n)
    (S : AffineSubspace k P) (hS : affineSpan k (Set.range s.points) ≤ S) {i : Fin (n + 1)} :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).faceOppositeCentroid i = s.faceOppositeCentroid i := by
  rw [eq_comm]
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  have hf : Function.Injective (S.subtype) := by
    simp only [coe_subtype, Subtype.val_injective]
  exact (s.restrict S hS).faceOppositeCentroid_map S.subtype hf (i := i)
/-
**Affine.Simplex.faceOppositeCentroid_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.
Simplex`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : DivisionRing k] [in
st_1 : AddCommGroup V]   [inst_2 : _root_.Module k V] [inst_3 : AddTorsor V P] {
m n : ℕ} [inst_4 : NeZero m] [inst_5 : NeZero n]   (s : Affine.Simplex k P m) (e
 : Fin (m + 1) ≃ Fin (n + 1)),   (s.reindex e).faceOppositeCentroid = s.faceOppo
siteCentroid ∘ ⇑e.symm
参数：s : Affine.Simplex k P m；e : Fin (m + 1) ≃ Fin (n + 1)；s.reindex e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.faceOppositeCentroid.eq_1`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_3} [inst : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _
root_.Module k V] [inst_3 : Ad…
· 使用定理 `Affine.Simplex.centroid_eq_of_range_eq`：centroid_eq_of_range_eq {n : Nat
} {s₁ s₂ : Simplex k P n} (h : Set.range s₁.points = Set.range s₂.points) : Fins
et.univ.centroid k s₁.points…
· 使用引理 `Affine.Simplex.range_faceOpposite_reindex`：range_faceOpposite_reindex {m
 n : Nat} [NeZero m] [NeZero n] (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 
1)) (i : Fin (n + 1)) : Set.ran…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_eq`：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card 
α = card β ↔ Nonempty (α ≃ β)
-/
@[simp] theorem faceOppositeCentroid_reindex {m n : ℕ} [NeZero m] [NeZero n] (s : Simplex k P m)
    (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).faceOppositeCentroid = s.faceOppositeCentroid ∘ e.symm := by
  ext i
  rw [faceOppositeCentroid]
  obtain rfl : m = n := by simpa using Fintype.card_eq.2 ⟨e⟩
  exact centroid_eq_of_range_eq <| Affine.Simplex.range_faceOpposite_reindex s e i

section median

/-- The median of a simplex is the line through a vertex and its corresponding
`faceOppositeCentroid`.
-/
/-
**Affine.Simplex.median** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：median (s : Simplex k P n) (i : Fin (n + 1)) : AffineSubspace k P
参数：s : Simplex k P n；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The median of a simplex is the line through a vertex and its corresponding
`faceOppositeCentroid`.
-/
def median (s : Simplex k P n) (i : Fin (n + 1)) : AffineSubspace k P :=
  line[k, s.points i, s.faceOppositeCentroid i]
/-
**Affine.Simplex.median_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : DivisionRing k] [in
st_1 : AddCommGroup V]   [inst_2 : _root_.Module k V] [inst_3 : AddTorsor V P] {
m n : ℕ} [inst_4 : NeZero m] [inst_5 : NeZero n]   (s : Affine.Simplex k P n) (e
 : Fin (n + 1) ≃ Fin (m + 1)), (s.reindex e).median = s.median ∘ ⇑e.symm
参数：s : Affine.Simplex k P n；e : Fin (n + 1) ≃ Fin (m + 1)；s.reindex e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `AffineSubspace.ext`：ext {p q : AffineSubspace k P} (h : forall x, x in p
 ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Affine.Simplex.reindex_points`：∀ {k : Type u_1} {V : Type u_2} {P : Type
 u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
inst_3 : AddTorsor …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Affine.Simplex.faceOppositeCentroid_reindex`：∀ {k : Type u_1} {V : Type 
u_2} {P : Type u_3} [inst : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 
: _root_.Module k V] [inst_3 : Ad…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem median_reindex {m n : ℕ} [NeZero m] [NeZero n] (s : Simplex k P n)
    (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).median = s.median ∘ e.symm := by
  ext i
  simp [median]

@[simp]
/-
**Affine.Simplex.median_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：median_map [CharZero k] {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [A
ffineSpace V₂ P₂] {n : Nat} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) (f 
: P ->ᵃ[k] P₂) (hf : Function.Injective f) : (s.map f hf).median i = (s.median i
).map f
参数：s : Simplex k P n；i : Fin (n + 1)；f : P ->ᵃ[k] P₂；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Affine.Simplex.map_points`：∀ {k : Type u_1} {V : Type u_2} {V₂ : Type u_
3} {P : Type u_5} {P₂ : Type u_6} [inst : Ring k] [inst_1 : AddCommGroup V]   [i
nst_2 : AddComm…
· 使用定理 `Affine.Simplex.faceOppositeCentroid_map`：∀ {k : Type u_1} {V : Type u_2}
 {P : Type u_3} [inst : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _r
oot_.Module k V] [inst_3 : Ad…
· 使用定理 `AffineSubspace.map_span`：map_span (s : Set P₁) : (affineSpan k s).map f 
= affineSpan k (f '' s)
· 使用定理 `Set.image_pair`：image_pair (f : α -> β) (a b : α) : f '' {a, b} = {f a, 
f b}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem median_map [CharZero k] {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂]
    {n : ℕ} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1))
    (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
    (s.map f hf).median i = (s.median i).map f := by
  simp [median, map_span, Set.image_pair]
/-
**Affine.Simplex.median_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：median_restrict [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) (S : Af
fineSubspace k P) (hS : affineSpan k (Set.range s.points) <= S) : haveI
参数：s : Simplex k P n；i : Fin (n + 1)；S : AffineSubspace k P；hS : affineSpan k (S
et.range s.points) <= S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.map_span`：map_span (s : Set P₁) : (affineSpan k s).map f 
= affineSpan k (f '' s)
· 使用定理 `Set.image_pair`：image_pair (f : α -> β) (a b : α) : f '' {a, b} = {f a, 
f b}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Affine.Simplex.restrict_points_coe`：∀ {k : Type u_1} {V : Type u_2} {P :
 Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V
]   [inst_3 : AddTorsor …
· 使用定理 `Affine.Simplex.faceOppositeCentroid_restrict`：∀ {k : Type u_1} {V : Type
 u_2} {P : Type u_3} [inst : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2
 : _root_.Module k V] [inst_3 : Ad…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem median_restrict [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) (S : AffineSubspace k P)
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    AffineSubspace.map (AffineSubspace.subtype S) ((s.restrict S hS).median i) = s.median i := by
  simp [median, map_span, Set.image_pair]

/-- The `faceOppositeCentroid` lines on the median through the corresponding vertex. -/
/-
**Affine.Simplex.faceOppositeCentroid_mem_median** 是 Mathlib 中的一个定理，位于命名空间 `Affi
ne.Simplex`。
形式化陈述：faceOppositeCentroid_mem_median (s : Simplex k P n) (i : Fin (n + 1)) : s.
faceOppositeCentroid i in s.median i
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
The `faceOppositeCentroid` lines on the median through the corresponding vertex.
-/
theorem faceOppositeCentroid_mem_median (s : Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i ∈ s.median i := by
  simp [median, right_mem_affineSpan_pair]

/-- A vertex lies on its median. -/
/-
**Affine.Simplex.point_mem_median** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：point_mem_median (s : Simplex k P n) (i : Fin (n + 1)) : s.points i in s.m
edian i
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
A vertex lies on its median.
-/
theorem point_mem_median (s : Simplex k P n) (i : Fin (n + 1)) :
    s.points i ∈ s.median i := by
  simp [median, left_mem_affineSpan_pair]

/-- The centroid lies on the median from any vertex. -/
/-
**Affine.Simplex.centroid_mem_median** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：centroid_mem_median [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) : s
.centroid in s.median i
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.median.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
3} [inst : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module k
 V] [inst_3 : Ad…
· 使用定理 `eq_vadd_iff_vsub_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p₁ : P) (g : G) (p₂ : P),   p₁ = g +ᵥ p₂ ↔ p₁ -ᵥ p₂ = g
· 使用定理 `Affine.Simplex.centroid_vsub_point_eq_smul_vsub`：centroid_vsub_point_eq_
smul_vsub [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) : s.centroid -ᵥ s.p
oints i = (n : k) • (s.faceOppositeCe…
· 使用定理 `Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_vsub`：faceOpposit
eCentroid_vsub_point_eq_smul_vsub [CharZero k] (s : Simplex k P n) (i : Fin (n +
 1)) : s.faceOppositeCentroid i -ᵥ s.points i = (…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `smul_vsub_vadd_mem_affineSpan_pair`：smul_vsub_vadd_mem_affineSpan_pair (
r : k) (p₁ p₂ : P) : r • (p₂ -ᵥ p₁) +ᵥ p₁ in line[k, p₁, p₂]

--- 原说明 ---
The centroid lies on the median from any vertex.
-/
theorem centroid_mem_median [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid ∈ s.median i := by
  rw [median]
  have h : s.centroid = ((n : k) * (1 / (n + 1))) • (s.faceOppositeCentroid i -ᵥ s.points i)
    +ᵥ s.points i := by
    rw [eq_vadd_iff_vsub_eq, centroid_vsub_point_eq_smul_vsub,
      faceOppositeCentroid_vsub_point_eq_smul_vsub, smul_smul, one_div, mul_assoc,
      inv_mul_cancel₀ (by norm_cast), mul_one]
  rw [h]
  exact smul_vsub_vadd_mem_affineSpan_pair _ _ _

/-- The median of a simplex is the line through the vertex and the centroid. -/
/-
**Affine.Simplex.median_eq_line_point_centroid** 是 Mathlib 中的一个定理，位于命名空间 `Affine
.Simplex`。
形式化陈述：median_eq_line_point_centroid [CharZero k] (s : Simplex k P n) (i : Fin (n
 + 1)) : s.median i = line[k, s.points i, s.centroid]
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineSpan_pair_le_of_right_mem`：affineSpan_pair_le_of_right_mem {p₁ p₂ 
p₃ : P} (h : p₁ in line[k, p₂, p₃]) : line[k, p₂, p₁] <= line[k, p₂, p₃]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.faceOppositeCentroid_eq_smul_vsub_vadd_point`：faceOpposit
eCentroid_eq_smul_vsub_vadd_point [CharZero k] (s : Simplex k P n) (i : Fin (n +
 1)) : s.faceOppositeCentroid i = (n : k)⁻¹ • (s.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_neg_one`：mul_neg_one (a : α) : a * -1 = -a
· 使用定理 `inv_eq_one_div`：inv_eq_one_div (x : G) : x⁻¹ = 1 / x
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `smul_vsub_rev_vadd_mem_affineSpan_pair`：smul_vsub_rev_vadd_mem_affineSpa
n_pair (r : k) (p₁ p₂ : P) : r • (p₁ -ᵥ p₂) +ᵥ p₂ in line[k, p₁, p₂]
· 使用定理 `Affine.Simplex.median.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
3} [inst : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module k
 V] [inst_3 : Ad…
· 使用定理 `Affine.Simplex.centroid_mem_median`：centroid_mem_median [CharZero k] (s 
: Simplex k P n) (i : Fin (n + 1)) : s.centroid in s.median i
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b

--- 原说明 ---
The median of a simplex is the line through the vertex and the centroid.
-/
theorem median_eq_line_point_centroid [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.median i = line[k, s.points i, s.centroid] := by
  have h1 : s.median i ≤ line[k, s.points i, s.centroid] := by
    unfold median
    apply affineSpan_pair_le_of_right_mem
    rw [faceOppositeCentroid_eq_smul_vsub_vadd_point]
    have h : (n : k)⁻¹ • (s.centroid -ᵥ s.points i) = (-1 / n : k) • (s.points i -ᵥ s.centroid)
        := by
      rw [← neg_vsub_eq_vsub_rev]
      have : -(s.points i -ᵥ s.centroid) = (-1 : k) • (s.points i -ᵥ s.centroid) := by simp
      rw [this, smul_smul]
      congr 1
      rw [mul_neg_one, inv_eq_one_div, neg_div]
    rw [h]
    exact smul_vsub_rev_vadd_mem_affineSpan_pair _ _ _
  have h2 : line[k, s.points i, s.centroid] ≤ s.median i := by
    rw [median]
    apply affineSpan_pair_le_of_right_mem
    exact centroid_mem_median s i
  exact le_antisymm h1 h2

/-- The medians of a simplex are concurrent at its centroid. -/
/-
**Affine.Simplex.eq_centroid_of_forall_mem_median** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ine.Simplex`。
形式化陈述：eq_centroid_of_forall_mem_median [CharZero k] (s : Simplex k P n) {hn : 1 
< n} {p : P} (h : forall i, p in s.median i) : p = s.centroid
参数：s : Simplex k P n；h : forall i, p in s.median i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `Affine.Simplex.affineIndependent_points_update_centroid`：affineIndepende
nt_points_update_centroid [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) : A
ffineIndependent k (Function.update s.points …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `affineIndependent_iff_linearIndependent_vsub`：affineIndependent_iff_line
arIndependent_vsub (p : ι -> P) (i1 : ι) : AffineIndependent k p ↔ LinearIndepen
dent k fun i : { x // x != i1 } =>…
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.one_lt_card_iff`：one_lt_card_iff : 1 < #s ↔ exists a b, a in s ∧ 
b in s ∧ a != b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The medians of a simplex are concurrent at its centroid.
-/
theorem eq_centroid_of_forall_mem_median [CharZero k] (s : Simplex k P n) {hn : 1 < n} {p : P}
    (h : ∀ i, p ∈ s.median i) :
    p = s.centroid := by
  rw [← vsub_eq_zero_iff_eq]
  set i₀ : Fin (n + 1) := 0
  have hp : p = (p -ᵥ s.centroid) +ᵥ s.centroid := by rw [vsub_vadd]
  let s' : Finset (Fin (n + 1)) := {i₀}ᶜ
  let u : s' → V := fun i => s.points i -ᵥ s.centroid
  have h_span : ∀ i : s', p -ᵥ s.centroid ∈ (Submodule.span k ({u i} : Set V)) := by
    intro i
    have hi := h i
    grind only [median_eq_line_point_centroid, vadd_right_mem_affineSpan_pair,
      Submodule.smul_mem, Submodule.mem_span_singleton_self]
  have hi : LinearIndependent k u := by
    set p : Fin (n + 1) → P := fun x => if x = i₀ then s.centroid else s.points x
    have hindep : AffineIndependent k p := by
      have := affineIndependent_points_update_centroid s i₀
      unfold Function.update at this
      grind
    have h1 := (affineIndependent_iff_linearIndependent_vsub k p i₀).mp hindep
    simp_rw [ne_eq, p] at h1
    set f : {x // x ∈ ({i₀}ᶜ : Finset (Fin (n + 1)))} → {x // x ≠ i₀} :=
      have h (x : {x // x ∈ ({i₀}ᶜ : Finset (Fin (n + 1)))}) : x.val ≠ i₀ := by
        grind [mem_compl, Finset.notMem_singleton]
      fun x => ⟨x.val, h x⟩
    have f_inj : Function.Injective f := by intro x y hxy; grind
    have h2 := h1.comp f f_inj
    convert! h2 using 1
    grind only [mem_compl, Finset.notMem_singleton]
  have he : ∃ i j : s', i ≠ j := by
    simp only [ne_eq, Subtype.exists, Subtype.mk.injEq, exists_prop]
    have hcard : s'.card = n := by
      rw [Finset.card_compl, Fintype.card_fin, card_singleton, add_tsub_cancel_right]
    have hcard' : 1 < #s' := by grind
    rw [Finset.one_lt_card_iff] at hcard'
    tauto
  choose i j hij using he
  have h_ij : Disjoint ({i} : Set {x // x ∈ s'}) {j} := by simp [hij]
  have h_disjoint : Disjoint (Submodule.span k {u i}) (Submodule.span k {u j}) := by
    simp_rw [← Set.image_singleton, hi.disjoint_span_image h_ij]
  exact Submodule.disjoint_def.1 h_disjoint _ (h_span i) (h_span j)

end median

/-- The medial is the simplex formed by centroids on all faces. -/
/-
**Affine.Simplex.medial** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：medial [CharZero k] (s : Simplex k P n) : Simplex k P n where points i
参数：s : Simplex k P n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The medial is the simplex formed by centroids on all faces.
-/
def medial [CharZero k] (s : Simplex k P n) : Simplex k P n where
  points i := s.faceOppositeCentroid i
  independent := by
    obtain h := s.independent
    rw [affineIndependent_iff_linearIndependent_vsub k _ 0] at h ⊢
    simp_rw [faceOppositeCentroid_vsub_faceOppositeCentroid]
    convert! h.units_smul fun _ ↦ Units.mk0 (-n)⁻¹ (by simpa using NeZero.ne n) with i
    simp [← smul_neg]
/-
**Affine.Simplex.medial_points** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：medial_points [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) : s.media
l.points i = s.faceOppositeCentroid i
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem medial_points [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.medial.points i = s.faceOppositeCentroid i := rfl
/-
**Affine.Simplex.medial_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：medial_reindex {m n : Nat} [NeZero m] [NeZero n] [CharZero k] (s : Simplex
 k P n) (e : Fin (n + 1) ≃ Fin (m + 1)) : (s.reindex e).medial = s.medial.reinde
x e
参数：s : Simplex k P n；e : Fin (n + 1) ≃ Fin (m + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ext`：ext {n : Nat} {s1 s2 : Simplex k P n} (h : forall i,
 s1.points i = s2.points i) : s1 = s2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Affine.Simplex.faceOppositeCentroid_reindex`：∀ {k : Type u_1} {V : Type 
u_2} {P : Type u_3} [inst : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 
: _root_.Module k V] [inst_3 : Ad…
· 使用定理 `Affine.Simplex.reindex_points`：∀ {k : Type u_1} {V : Type u_2} {P : Type
 u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
inst_3 : AddTorsor …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem medial_reindex {m n : ℕ} [NeZero m] [NeZero n]
    [CharZero k] (s : Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).medial = s.medial.reindex e := by
  ext i
  simp [medial_points]
/-
**Affine.Simplex.medial_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：medial_map {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂
 P₂] [CharZero k] {n : Nat} [NeZero n] (s : Simplex k P n) (f : P ->ᵃ[k] P₂) (hf
 : Function.Injective f) : (s.map f hf).medial = s.medial.map f hf
参数：s : Simplex k P n；f : P ->ᵃ[k] P₂；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ext`：ext {n : Nat} {s1 s2 : Simplex k P n} (h : forall i,
 s1.points i = s2.points i) : s1 = s2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.faceOppositeCentroid_map`：∀ {k : Type u_1} {V : Type u_2}
 {P : Type u_3} [inst : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _r
oot_.Module k V] [inst_3 : Ad…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Affine.Simplex.map_points`：∀ {k : Type u_1} {V : Type u_2} {V₂ : Type u_
3} {P : Type u_5} {P₂ : Type u_6} [inst : Ring k] [inst_1 : AddCommGroup V]   [i
nst_2 : AddComm…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem medial_map {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] [CharZero k]
    {n : ℕ} [NeZero n] (s : Simplex k P n)
    (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
    (s.map f hf).medial = s.medial.map f hf := by
  ext i
  simp [medial_points]

open scoped Pointwise in
@[simp]
/-
**Affine.Simplex.affineSpan_range_medial** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simpl
ex`。
形式化陈述：affineSpan_range_medial [CharZero k] (s : Simplex k P n) : affineSpan k (S
et.range (s.medial.points)) = affineSpan k (Set.range (s.points))
参数：s : Simplex k P n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `Affine.Simplex.faceOppositeCentroid_mem_affineSpan_face`：faceOppositeCen
troid_mem_affineSpan_face [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) : s
.faceOppositeCentroid i in affineSpan k (Set.…
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `AffineSubspace.eq_iff_direction_eq_of_mem`：eq_iff_direction_eq_of_mem {s
₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p in s₁) (h₂ : p in s₂) : s₁ = s₂ ↔ s₁.
direction = s₂.direction
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Affine.Simplex.faceOppositeCentroid_vsub_faceOppositeCentroid`：faceOppos
iteCentroid_vsub_faceOppositeCentroid [CharZero k] (s : Affine.Simplex k P n) (i
 j : Fin (n + 1)) : s.faceOppositeCentroid i -ᵥ s.f…
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Submodule.span_smul_eq_of_isUnit`：span_smul_eq_of_isUnit (s : Set M) (r 
: R) (hr : IsUnit r) : span R (r • s) = span R s
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
theorem affineSpan_range_medial [CharZero k] (s : Simplex k P n) :
    affineSpan k (Set.range (s.medial.points)) = affineSpan k (Set.range (s.points)) := by
  have hmem1 : s.medial.points 0 ∈ affineSpan k (Set.range s.medial.points) :=
    mem_affineSpan _ (by simp)
  have hmem2 : s.medial.points 0 ∈ affineSpan k (Set.range s.points) := by
    apply Set.mem_of_mem_of_subset (s.faceOppositeCentroid_mem_affineSpan_face 0)
    exact affineSpan_mono k (by simp)
  rw [eq_iff_direction_eq_of_mem hmem1 hmem2]
  simp_rw [direction_affineSpan, vectorSpan_def]
  suffices Set.range s.medial.points -ᵥ Set.range s.medial.points
    = (-n : k)⁻¹ • (Set.range s.points -ᵥ Set.range s.points) by
    rw [this, Submodule.span_smul_eq_of_isUnit]
    simpa using NeZero.ne n
  ext v
  suffices (∃ a b, (n : k)⁻¹ • (s.points b -ᵥ s.points a) = v) ↔
    ∃ a b, -((n : k)⁻¹ • (s.points a -ᵥ s.points b)) = v by
    simpa [Set.mem_vsub, Set.mem_smul_set, medial_points,
      faceOppositeCentroid_vsub_faceOppositeCentroid]
  congrm ∃ a b, ?_ = v
  simp [← smul_neg]
/-
**Affine.Simplex.medial_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：medial_restrict [CharZero k] (s : Simplex k P n) (S : AffineSubspace k P) 
(hS : affineSpan k (Set.range s.points) <= S) : haveI
参数：s : Simplex k P n；S : AffineSubspace k P；hS : affineSpan k (Set.range s.point
s) <= S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Affine.Simplex.ext`：ext {n : Nat} {s1 s2 : Simplex k P n} (h : forall i,
 s1.points i = s2.points i) : s1 = s2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.affineSpan_range_medial`：affineSpan_range_medial [CharZer
o k] (s : Simplex k P n) : affineSpan k (Set.range (s.medial.points)) = affineSp
an k (Set.range (s.points))
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.faceOppositeCentroid_restrict`：∀ {k : Type u_1} {V : Type
 u_2} {P : Type u_3} [inst : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2
 : _root_.Module k V] [inst_3 : Ad…
· 使用定理 `Affine.Simplex.restrict_points_coe`：∀ {k : Type u_1} {V : Type u_2} {P :
 Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V
]   [inst_3 : AddTorsor …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem medial_restrict [CharZero k] (s : Simplex k P n) (S : AffineSubspace k P)
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).medial = s.medial.restrict S (s.affineSpan_range_medial ▸ hS) := by
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  ext i
  simp [medial_points]

end Simplex

end Affine

