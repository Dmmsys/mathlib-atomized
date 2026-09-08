/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RepresentationTheory.Semisimple

/-!
# Maschke's theorem

We prove **Maschke's theorem** for finite groups,
in the formulation that every submodule of a `k[G]` module has a complement,
when `k` is a field with `Fintype.card G` invertible in `k`.

We do the core computation in greater generality.
For any commutative ring `k` in which `Fintype.card G` is invertible,
and a `k[G]`-linear map `i : V → W` which admits a `k`-linear retraction `π`,
we produce a `k[G]`-linear retraction by
taking the average over `G` of the conjugates of `π`.

## Implementation Notes

* These results assume `IsUnit (Fintype.card G : k)` which is equivalent to the more
  familiar `¬(ringChar k ∣ Fintype.card G)`.

## Future work
It's not so far to give the usual statement, that every finite-dimensional representation
of a finite group is semisimple (i.e. a direct sum of irreducibles).
-/

@[expose] public section

noncomputable section

open Module MonoidAlgebra
open scoped Ring

/-!
We now do the key calculation in Maschke's theorem.

Given `V → W`, an inclusion of `k[G]` modules,
assume we have some retraction `π` (i.e. `∀ v, π (i v) = v`),
just as a `k`-linear map.
(When `k` is a field, this will be available cheaply, by choosing a basis.)

We now construct a retraction of the inclusion as a `k[G]`-linear map,
by the formula
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/

namespace LinearMap


-- At first we work with any `[CommRing k]`, and add the assumption that
-- `IsUnit (Fintype.card G : k)` when it is required.
variable {k : Type*} [CommRing k] {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module k V] [Module k[G] V] [IsScalarTower k k[G] V]
variable {W : Type*} [AddCommGroup W] [Module k W] [Module k[G] W] [IsScalarTower k k[G] W]
variable (π : W →ₗ[k] V)

/-- We define the conjugate of `π` by `g`, as a `k`-linear map. -/
/-
**LinearMap.conjugate** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：conjugate (g : G) : W ->ₗ[k] V
参数：g : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define the conjugate of `π` by `g`, as a `k`-linear map.
-/
def conjugate (g : G) : W →ₗ[k] V :=
  GroupSMul.linearMap k V g⁻¹ ∘ₗ π ∘ₗ GroupSMul.linearMap k W g
/-
**LinearMap.conjugate_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：conjugate_apply (g : G) (v : W) : π.conjugate g v = MonoidAlgebra.single g
⁻¹ (1 : k) • π (MonoidAlgebra.single g (1 : k) • v)
参数：g : G；v : W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjugate_apply (g : G) (v : W) :
    π.conjugate g v = MonoidAlgebra.single g⁻¹ (1 : k) • π (MonoidAlgebra.single g (1 : k) • v) :=
  rfl

variable (i : V →ₗ[k[G]] W)

section

/-
**LinearMap.conjugate_i** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：conjugate_i (h : forall v : V, π (i v) = v) (g : G) (v : V) : (conjugate π
 g : W -> V) (i v) = v
参数：h : forall v : V, π (i v) = v；g : G；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.conjugate_apply`：conjugate_apply (g : G) (v : W) : π.conjugate
 g v = MonoidAlgebra.single g⁻¹ (1 : k) • π (MonoidAlgebra.single g (1 : k) • v)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `MonoidAlgebra.single_mul_single`：single_mul_single (m₁ m₂ : M) (r₁ r₂ : 
R) : single m₁ r₁ * single m₂ r₂ = single (m₁ * m₂) (r₁ * r₂)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用引理 `MonoidAlgebra.one_def`：one_def : (1 : R[M]) = single 1 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem conjugate_i (h : ∀ v : V, π (i v) = v) (g : G) (v : V) :
    (conjugate π g : W → V) (i v) = v := by
  rw [conjugate_apply, ← i.map_smul, h, ← mul_smul, single_mul_single, mul_one, inv_mul_cancel,
    ← one_def, one_smul]

end

variable (G) [Fintype G]

/-- The sum of the conjugates of `π` by each element `g : G`, as a `k`-linear map.

(We postpone dividing by the size of the group as long as possible.)
-/
/-
**LinearMap.sumOfConjugates** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：sumOfConjugates : W ->ₗ[k] V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of the conjugates of `π` by each element `g : G`, as a `k`-linear map.

(We postpone dividing by the size of the group as long as possible.)
-/
def sumOfConjugates : W →ₗ[k] V :=
  ∑ g : G, π.conjugate g
/-
**LinearMap.sumOfConjugates_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：sumOfConjugates_apply (v : W) : π.sumOfConjugates G v = ∑ g : G, π.conjuga
te g v
参数：v : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.sum_apply`：sum_apply (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) 
(b : M) : (∑ d in t, f d) b = ∑ d in t, f d b
-/
lemma sumOfConjugates_apply (v : W) : π.sumOfConjugates G v = ∑ g : G, π.conjugate g v :=
  LinearMap.sum_apply _ _ _

/-- In fact, the sum over `g : G` of the conjugate of `π` by `g` is a `k[G]`-linear map.
-/
/-
**LinearMap.sumOfConjugatesEquivariant** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：sumOfConjugatesEquivariant : W ->ₗ[k[G]] V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In fact, the sum over `g : G` of the conjugate of `π` by `g` is a `k[G]`-linear 
map.
-/
def sumOfConjugatesEquivariant : W →ₗ[k[G]] V :=
  MonoidAlgebra.equivariantOfLinearOfComm (π.sumOfConjugates G) fun g v => by
    simp only [sumOfConjugates_apply, Finset.smul_sum, conjugate_apply]
    refine Fintype.sum_bijective (· * g) (Group.mulRight_bijective g) _ _ fun i ↦ ?_
    simp only [smul_smul, single_mul_single, mul_inv_rev, mul_inv_cancel_left, one_mul]
/-
**LinearMap.sumOfConjugatesEquivariant_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMa
p`。
形式化陈述：sumOfConjugatesEquivariant_apply (v : W) : π.sumOfConjugatesEquivariant G 
v = ∑ g : G, π.conjugate g v
参数：v : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.sumOfConjugates_apply`：sumOfConjugates_apply (v : W) : π.sumOf
Conjugates G v = ∑ g : G, π.conjugate g v
-/
theorem sumOfConjugatesEquivariant_apply (v : W) :
    π.sumOfConjugatesEquivariant G v = ∑ g : G, π.conjugate g v :=
  π.sumOfConjugates_apply G v

section

/-- We construct our `k[G]`-linear retraction of `i` as
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/
/-
**LinearMap.equivariantProjection** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：equivariantProjection : W ->ₗ[k[G]] V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We construct our `k[G]`-linear retraction of `i` as
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/
def equivariantProjection : W →ₗ[k[G]] V :=
  (Fintype.card G : k)⁻¹ʳ • π.sumOfConjugatesEquivariant G
/-
**LinearMap.equivariantProjection_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：equivariantProjection_apply (v : W) : π.equivariantProjection G v = (Nat.c
ard G : k)⁻¹ʳ • ∑ g : G, π.conjugate g v
参数：v : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `LinearMap.sumOfConjugatesEquivariant_apply`：sumOfConjugatesEquivariant_a
pply (v : W) : π.sumOfConjugatesEquivariant G v = ∑ g : G, π.conjugate g v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivariantProjection_apply (v : W) :
    π.equivariantProjection G v = (Nat.card G : k)⁻¹ʳ • ∑ g : G, π.conjugate g v := by
  simp only [equivariantProjection, smul_apply, sumOfConjugatesEquivariant_apply,
    Fintype.card_eq_nat_card]
/-
**LinearMap.equivariantProjection_condition** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
`。
形式化陈述：equivariantProjection_condition (hcard : IsUnit (Nat.card G : k)) (h : for
all v : V, π (i v) = v) (v : V) : (π.equivariantProjection G) (i v) = v
参数：hcard : IsUnit (Nat.card G : k)；h : forall v : V, π (i v) = v；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.equivariantProjection_apply`：equivariantProjection_apply (v : 
W) : π.equivariantProjection G v = (Nat.card G : k)⁻¹ʳ • ∑ g : G, π.conjugate g 
v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `LinearMap.conjugate_i`：conjugate_i (h : forall v : V, π (i v) = v) (g : 
G) (v : V) : (conjugate π g : W -> V) (i v) = v
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `Ring.inverse_mul_cancel`：inverse_mul_cancel (x : M₀) (h : IsUnit x) : x⁻
¹ʳ * x = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem equivariantProjection_condition (hcard : IsUnit (Nat.card G : k))
    (h : ∀ v : V, π (i v) = v) (v : V) : (π.equivariantProjection G) (i v) = v := by
  rw [equivariantProjection_apply]
  simp only [conjugate_i π i h]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, smul_smul,
    Fintype.card_eq_nat_card, Ring.inverse_mul_cancel _ hcard, one_smul]

end

end LinearMap

end

namespace MonoidAlgebra

-- Now we work over a `[Field k]`.
variable {k : Type*} [Field k] {G : Type*} [Finite G] [NeZero (Nat.card G : k)]
variable [Group G]
variable {V : Type*} [AddCommGroup V] [Module k[G] V]
variable {W : Type*} [AddCommGroup W] [Module k[G] W]

set_option backward.isDefEq.respectTransparency false in
/-
**MonoidAlgebra.exists_leftInverse_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Monoi
dAlgebra`。
形式化陈述：exists_leftInverse_of_injective (f : V ->ₗ[k[G]] W) (hf : LinearMap.ker f 
= ⊥) : exists g : W ->ₗ[k[G]] V, g.comp f = .id
参数：f : V ->ₗ[k[G]] W；hf : LinearMap.ker f = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsScalarTower.of_compHom`：of_compHom : letI
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearMap.leftInverse_apply_of_inj`：LinearMap.leftInverse_apply_of_inj {
f : V ->ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥) (x : V) : f.leftInverse (f x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.restrictScalars.congr_simp`：∀ (S : Type u_1) {R : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S
]   [inst_3 : _root_.Modul…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.equivariantProjection_condition`：equivariantProjection_conditi
on (hcard : IsUnit (Nat.card G : k)) (h : forall v : V, π (i v) = v) (v : V) : (
π.equivariantProjection G) (i v…
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
theorem exists_leftInverse_of_injective (f : V →ₗ[k[G]] W) (hf : LinearMap.ker f = ⊥) :
    ∃ g : W →ₗ[k[G]] V, g.comp f = .id := by
  let A := k[G]
  let : Module k W := .compHom W (algebraMap k A)
  let : Module k V := .compHom V (algebraMap k A)
  have := IsScalarTower.of_compHom k A W
  have := IsScalarTower.of_compHom k A V
  set φ := (f.restrictScalars k).leftInverse
  have hφ : ∀ (x : V), φ (f x) = x := by
    apply LinearMap.leftInverse_apply_of_inj
    simp [hf]
  have _ : Fintype G := Fintype.ofFinite G
  refine ⟨φ.equivariantProjection G, LinearMap.ext ?_⟩
  exact φ.equivariantProjection_condition G _ (.mk0 _ <| NeZero.ne _) <| hφ

namespace Submodule

/-
**MonoidAlgebra.Submodule.exists_isCompl** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebr
a.Submodule`。
形式化陈述：exists_isCompl (p : Submodule k[G] V) : exists q : Submodule k[G] V, IsCom
pl p q
参数：p : Submodule k[G] V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.exists_leftInverse_of_injective`：exists_leftInverse_of_inj
ective (f : V ->ₗ[k[G]] W) (hf : LinearMap.ker f = ⊥) : exists g : W ->ₗ[k[G]] V
, g.comp f = .id
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
· 使用定理 `LinearMap.isCompl_of_proj`：isCompl_of_proj {f : E ->ₗ[R] p} (hf : forall
 x : p, f x = x) : IsCompl p (ker f)
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem exists_isCompl (p : Submodule k[G] V) : ∃ q : Submodule k[G] V, IsCompl p q := by
  rcases MonoidAlgebra.exists_leftInverse_of_injective p.subtype p.ker_subtype with ⟨f, hf⟩
  exact ⟨LinearMap.ker f, LinearMap.isCompl_of_proj <| DFunLike.congr_fun hf⟩

/-- This also implies instances `ComplementedLattice (Submodule k[G] V)` and
`IsSemisimpleRing k[G]`. -/
/-
**MonoidAlgebra.Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra.Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This also implies instances `ComplementedLattice (Submodule k[G] V)` and
`IsSemisimpleRing k[G]`.
-/
instance : IsSemisimpleModule k[G] V where
  exists_isCompl := exists_isCompl
/-
**MonoidAlgebra.Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra.Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroup G] : IsSemisimpleRing (AddMonoidAlgebra k G) :=
  haveI : NeZero (Nat.card (Multiplicative G) : k) := by
    rwa [Nat.card_congr Multiplicative.toAdd]
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv k G (R := ℕ)).toRingEquiv.symm.isSemisimpleRing

section

variable {G k V : Type*} [Group G] [Field k] [Finite G] [NeZero (Nat.card G : k)] [AddCommGroup V]
  [Module k V] (ρ : Representation k G V)

open Representation

set_option backward.isDefEq.respectTransparency false in
/-
**MonoidAlgebra.Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra.Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSemisimpleRepresentation ρ := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  infer_instance

end

end Submodule

end MonoidAlgebra

