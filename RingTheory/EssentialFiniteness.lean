/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Essentially of finite type algebras

## Main results
- `Algebra.EssFiniteType`: The class of essentially of finite type algebras. An `R`-algebra is
  essentially of finite type if it is the localization of an algebra of finite type.
- `Algebra.EssFiniteType.algHom_ext`: The algebra homomorphisms out from an algebra essentially of
  finite type is determined by its values on a finite set.

-/

@[expose] public section

open scoped TensorProduct

namespace Algebra

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/--
An `R`-algebra is essentially of finite type if
it is the localization of an algebra of finite type.
See `essFiniteType_iff_exists_subalgebra`.

For field extensions, this is equivalent to being finitely generated as a field.
See `IntermediateField.fg_top_iff`.
-/
/-
**Algebra.EssFiniteType** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u_1) → (S : Type u_2) → [inst : CommRing R] → [inst_1 : CommRing
 S] → [Algebra R S] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-algebra is essentially of finite type if
it is the localization of an algebra of finite type.
See `essFiniteType_iff_exists_subalgebra`.

For field extensions, this is equivalent to being finitely generated as a field.
See `IntermediateField.fg_top_iff`.
-/
class EssFiniteType : Prop where
  cond : ∃ s : Finset S,
    IsLocalization ((IsUnit.submonoid S).comap (algebraMap (adjoin R (s : Set S)) S)) S

/-- Let `S` be an `R`-algebra essentially of finite type, this is a choice of a finset `s ⊆ S`
such that `S` is the localization of `R[s]`. -/
noncomputable
/-
**Algebra.EssFiniteType.finset** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.EssFiniteType`
。
形式化陈述：(R : Type u_1) →   (S : Type u_2) →     [inst : CommRing R] → [inst_1 : Co
mmRing S] → [inst_2 : Algebra R S] → [h : Algebra.EssFiniteType R S] → Finset S
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.EssFiniteType.cond`：∀ {R : Type u_1} {S : Type u_2} {inst : Comm
Ring R} {inst_1 : CommRing S} {inst_2 : Algebra R S}   [self : Algebra.EssFinite
Type R S],   ∃ s…
-/
def EssFiniteType.finset [h : EssFiniteType R S] : Finset S := h.cond.choose

/-- A choice of a subalgebra of finite type in an essentially of finite type algebra, such that
its localization is the whole ring. -/
noncomputable
/-
**Algebra.EssFiniteType.subalgebra** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.EssFiniteT
ype`。
形式化陈述：(R : Type u_1) →   (S : Type u_2) →     [inst : CommRing R] → [inst_1 : Co
mmRing S] → [inst_2 : Algebra R S] → [Algebra.EssFiniteType R S] → Subalgebra R 
S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev EssFiniteType.subalgebra [EssFiniteType R S] : Subalgebra R S :=
  Algebra.adjoin R (finset R S : Set S)
/-
**Algebra.EssFiniteType.adjoin_mem_finset** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Ess
FiniteType`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [inst_3 : Algebra.EssFiniteType R S], Algebra.adjoin R 
{x | ↑x ∈ Algebra.EssFiniteType.finset R S} = ⊤
参数：R : Type u_1；S : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_adjoin_coe_preimage`：adjoin_adjoin_coe_preimage {s : Set 
A} : adjoin R (((↑) : adjoin R s -> A) ⁻¹' s) = ⊤
-/
lemma EssFiniteType.adjoin_mem_finset [EssFiniteType R S] :
    adjoin R { x : subalgebra R S | x.1 ∈ finset R S } = ⊤ := adjoin_adjoin_coe_preimage
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EssFiniteType R S] : Algebra.FiniteType R (EssFiniteType.subalgebra R S) := by
  constructor
  rw [Subalgebra.fg_top, EssFiniteType.subalgebra]
  exact ⟨_, rfl⟩

/-- A submonoid of `EssFiniteType.subalgebra R S`, whose localization is the whole algebra `S`. -/
noncomputable
/-
**Algebra.EssFiniteType.submonoid** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.EssFiniteTy
pe`。
形式化陈述：(R : Type u_1) →   (S : Type u_2) →     [inst : CommRing R] →       [inst_
1 : CommRing S] →         [inst_2 : Algebra R S] →           [inst_3 : Algebra.E
ssFiniteType R S] → Submonoid ↥(Algebra.EssFiniteType.subalgebra R S)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def EssFiniteType.submonoid [EssFiniteType R S] : Submonoid (EssFiniteType.subalgebra R S) :=
  ((IsUnit.submonoid S).comap (algebraMap (EssFiniteType.subalgebra R S) S))
/-
**Algebra.EssFiniteType.isLocalization** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.EssFin
iteType`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [h : Algebra.EssFiniteType R S], IsLocalization (Algebr
a.EssFiniteType.submonoid R S) S
参数：R : Type u_1；S : Type u_2；Algebra.EssFiniteType.submonoid R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Algebra.EssFiniteType.cond`：∀ {R : Type u_1} {S : Type u_2} {inst : Comm
Ring R} {inst_1 : CommRing S} {inst_2 : Algebra R S}   [self : Algebra.EssFinite
Type R S],   ∃ s…
-/
instance EssFiniteType.isLocalization [h : EssFiniteType R S] :
    IsLocalization (EssFiniteType.submonoid R S) S :=
  h.cond.choose_spec
/-
**Algebra.essFiniteType_cond_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：essFiniteType_cond_iff (σ : Finset S) : IsLocalization ((IsUnit.submonoid 
S).comap (algebraMap (adjoin R (σ : Set S)) S)) S ↔ (forall s : S, exists t in A
lgebra.adjoin R (σ : Set S), IsUnit t ∧ s * t in Algebra.adjoin R (σ : Set S))
参数：σ : Finset S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.IsLocalizationMap.surj`：∀ {M : Type u_1} [inst : CommMonoid M]
 {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},   S.IsLoc
alizationMap f → ∀ (z …
· 使用定理 `IsLocalization'.toIsLocalizationMap`：∀ {R : Type u_1} {inst : CommSemiri
ng R} {M : Submonoid R} {S : Type u_2} {inst_1 : CommSemiring S}   {inst_2 : Alg
ebra R S} [self : IsLocal…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
lemma essFiniteType_cond_iff (σ : Finset S) :
    IsLocalization ((IsUnit.submonoid S).comap (algebraMap (adjoin R (σ : Set S)) S)) S ↔
    (∀ s : S, ∃ t ∈ Algebra.adjoin R (σ : Set S),
      IsUnit t ∧ s * t ∈ Algebra.adjoin R (σ : Set S)) := by
  constructor <;> intro hσ
  · intro s
    obtain ⟨⟨⟨x, hx⟩, ⟨t, ht⟩, ht'⟩, h⟩ := hσ.1.2 s
    exact ⟨t, ht, ht', h ▸ hx⟩
  · constructor; constructor
    · exact fun y ↦ y.prop
    · intro s
      obtain ⟨t, ht, ht', h⟩ := hσ s
      exact ⟨⟨⟨_, h⟩, ⟨t, ht⟩, ht'⟩, rfl⟩
    · intro x y e
      exact ⟨1, by simpa using Subtype.ext e⟩
/-
**Algebra.essFiniteType_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：essFiniteType_iff : EssFiniteType R S ↔ exists (σ : Finset S), (forall s :
 S, exists t in Algebra.adjoin R (σ : Set S), IsUnit t ∧ s * t in Algebra.adjoin
 R (σ : Set S))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma essFiniteType_iff :
    EssFiniteType R S ↔ ∃ (σ : Finset S),
      (∀ s : S, ∃ t ∈ Algebra.adjoin R (σ : Set S),
        IsUnit t ∧ s * t ∈ Algebra.adjoin R (σ : Set S)) := by
  simp_rw [← essFiniteType_cond_iff]
  constructor <;> exact fun ⟨a, b⟩ ↦ ⟨a, b⟩
/-
**Algebra.EssFiniteType.of_finiteType** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.EssFini
teType`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.FiniteType R S], Algebra.EssFiniteType R S
参数：R : Type u_1；S : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.essFiniteType_iff`：essFiniteType_iff : EssFiniteType R S ↔ exist
s (σ : Finset S), (forall s : S, exists t in Algebra.adjoin R (σ : Set S), IsUni
t t ∧ s * t in …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
instance EssFiniteType.of_finiteType [FiniteType R S] : EssFiniteType R S := by
  obtain ⟨s, hs⟩ := ‹FiniteType R S›
  rw [essFiniteType_iff]
  exact ⟨s, fun _ ↦ by simpa only [hs, mem_top, and_true, true_and] using ⟨1, isUnit_one⟩⟩

variable {R} in
/-
**Algebra.EssFiniteType.of_isLocalization** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Ess
FiniteType`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (M : Submonoid R)   [IsLocalization M S], Algebra.EssFini
teType R S
参数：S : Type u_2；M : Submonoid R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.essFiniteType_iff`：essFiniteType_iff : EssFiniteType R S ↔ exist
s (σ : Finset S), (forall s : S, exists t in Algebra.adjoin R (σ : Set S), IsUni
t t ∧ s * t in …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Algebra.adjoin_empty`：adjoin_empty : adjoin R (∅ : Set A) = ⊥
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma EssFiniteType.of_isLocalization (M : Submonoid R) [IsLocalization M S] :
    EssFiniteType R S := by
  rw [essFiniteType_iff]
  use ∅
  simp only [Finset.coe_empty, Algebra.adjoin_empty, Algebra.mem_bot,
    Set.mem_range, exists_exists_eq_and]
  intro s
  obtain ⟨⟨x, t⟩, e⟩ := IsLocalization.surj M s
  exact ⟨_, IsLocalization.map_units S t, x, e.symm⟩
/-
**Algebra.EssFiniteType.of_id** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.EssFiniteType`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R], Algebra.EssFiniteType R R
参数：R : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…
-/
lemma EssFiniteType.of_id : EssFiniteType R R := inferInstance

section
variable [Algebra S T] [IsScalarTower R S T]

/-
**Algebra.EssFiniteType.aux** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.EssFiniteType`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) (T : Type u_3) [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] [inst_5 : Algebra S T] [inst_6 : IsScalarTower R S T]   (σ : Subalgebra R S
),   (∀ (s : S), ∃ t ∈ σ, IsUnit t ∧ s * t ∈ σ) →     ∀ (τ : Set T),       ∀ t ∈
 Algebra.adjoin S τ,         ∃ s ∈ σ, IsUnit s ∧ s • t ∈ Subalgebra.map (IsScala
rTower.toAlgHom R S T) σ ⊔ Algebra.adjoin R τ
参数：R : Type u_1；S : Type u_2；T : Type u_3；σ : Subalgebra R S；∀ (s : S), ∃ t ∈ σ,
 IsUnit t ∧ s * t ∈ σ；τ : Set T；IsScalarTower.toAlgHom R S T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_induction`：adjoin_induction {p : (x : A) -> x in adjoin R
 s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_adjoin hx)) (algebraMap
 : forall r, p…
· 使用定理 `Subalgebra.one_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   1 ∈ S
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `Algebra.mem_sup_right`：mem_sup_right {S T : Subalgebra R A} : forall {x 
: A}, x in T -> x in S ⊔ T
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Algebra.mem_sup_left`：mem_sup_left {S T : Subalgebra R A} : forall {x : 
A}, x in S -> x in S ⊔ T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma EssFiniteType.aux (σ : Subalgebra R S)
    (hσ : ∀ s : S, ∃ t ∈ σ, IsUnit t ∧ s * t ∈ σ)
    (τ : Set T) (t : T) (ht : t ∈ Algebra.adjoin S τ) :
    ∃ s ∈ σ, IsUnit s ∧ s • t ∈ σ.map (IsScalarTower.toAlgHom R S T) ⊔ Algebra.adjoin R τ := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ht
  · intro t ht
    exact ⟨1, Subalgebra.one_mem _, isUnit_one,
      (one_smul S t).symm ▸ Algebra.mem_sup_right (Algebra.subset_adjoin ht)⟩
  · intro s
    obtain ⟨s', hs₁, hs₂, hs₃⟩ := hσ s
    refine ⟨_, hs₁, hs₂, Algebra.mem_sup_left ?_⟩
    rw [Algebra.smul_def, ← map_mul, mul_comm]
    exact ⟨_, hs₃, rfl⟩
  · rintro x y - - ⟨sx, hsx, hsx', hsx''⟩ ⟨sy, hsy, hsy', hsy''⟩
    refine ⟨_, σ.mul_mem hsx hsy, hsx'.mul hsy', ?_⟩
    rw [smul_add, mul_smul, mul_smul, Algebra.smul_def sx (sy • y), smul_comm,
      Algebra.smul_def sy (sx • x)]
    apply add_mem (mul_mem _ hsx'') (mul_mem _ hsy'') <;>
      exact Algebra.mem_sup_left ⟨_, ‹_›, rfl⟩
  · rintro x y - - ⟨sx, hsx, hsx', hsx''⟩ ⟨sy, hsy, hsy', hsy''⟩
    refine ⟨_, σ.mul_mem hsx hsy, hsx'.mul hsy', ?_⟩
    rw [mul_smul, ← smul_eq_mul, smul_comm sy x, ← smul_assoc, smul_eq_mul]
    exact mul_mem hsx'' hsy''
/-
**Algebra.EssFiniteType.comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.EssFiniteType`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) (T : Type u_3) [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] [inst_5 : Algebra S T] [IsScalarTower R S T]   [h₁ : Algebra.EssFiniteType 
R S] [h₂ : Algebra.EssFiniteType S T], Algebra.EssFiniteType R T
参数：R : Type u_1；S : Type u_2；T : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.essFiniteType_iff`：essFiniteType_iff : EssFiniteType R S ↔ exist
s (σ : Finset S), (forall s : S, exists t in Algebra.adjoin R (σ : Set S), IsUni
t t ∧ s * t in …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Algebra.adjoin_union`：adjoin_union (s t : Set A) : adjoin R (s union t) 
= adjoin R s ⊔ adjoin R t
· 使用定理 `Algebra.adjoin_image`：adjoin_image (f : A ->ₐ[R] B) (s : Set A) : adjoin
 R (f '' s) = (adjoin R s).map f
· 使用定理 `Algebra.EssFiniteType.aux`：∀ (R : Type u_1) (S : Type u_2) (T : Type u_3
) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Al
gebra R S] [ins…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Algebra.mem_sup_left`：mem_sup_left {S T : Subalgebra R A} : forall {x : 
A}, x in S -> x in S ⊔ T
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma EssFiniteType.comp [h₁ : EssFiniteType R S] [h₂ : EssFiniteType S T] :
    EssFiniteType R T := by
  rw [essFiniteType_iff] at h₁ h₂ ⊢
  classical
  obtain ⟨s, hs⟩ := h₁
  obtain ⟨t, ht⟩ := h₂
  use s.image (IsScalarTower.toAlgHom R S T) ∪ t
  simp only [Finset.coe_union, Finset.coe_image, Algebra.adjoin_union, Algebra.adjoin_image]
  intro x
  obtain ⟨y, hy₁, hy₂, hy₃⟩ := ht x
  obtain ⟨t₁, h₁, h₂, h₃⟩ := EssFiniteType.aux _ _ _ _ hs _ y hy₁
  obtain ⟨t₂, h₄, h₅, h₆⟩ := EssFiniteType.aux _ _ _ _ hs _ _ hy₃
  refine ⟨t₂ • t₁ • y, ?_, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact mul_mem (Algebra.mem_sup_left ⟨_, h₄, rfl⟩) h₃
  · rw [Algebra.smul_def, Algebra.smul_def]
    exact (h₅.map _).mul ((h₂.map _).mul hy₂)
  · rw [← mul_smul, mul_comm, smul_mul_assoc, mul_comm, mul_comm y, mul_smul, Algebra.smul_def]
    exact mul_mem (Algebra.mem_sup_left ⟨_, h₁, rfl⟩) h₆

open EssFiniteType in
/-
**Algebra.essFiniteType_iff_exists_subalgebra** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
`。
形式化陈述：essFiniteType_iff_exists_subalgebra : EssFiniteType R S ↔ exists (S₀ : Sub
algebra R S) (M : Submonoid S₀), FiniteType R S₀ ∧ IsLocalization M S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.instFiniteTypeSubtypeMemSubalgebraSubalgebra`：∀ (R : Type u_1) (
S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]  
 [inst_3 : Algebra.EssFiniteType R S], Alg…
· 使用定理 `Algebra.EssFiniteType.isLocalization`：∀ (R : Type u_1) (S : Type u_2) [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [h : Algebra.Es
sFiniteType R S], IsLocali…
· 使用定理 `Algebra.EssFiniteType.of_isLocalization`：∀ {R : Type u_1} (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (M : Submonoid
 R)   [IsLocalization M S], A…
· 使用定理 `Algebra.EssFiniteType.comp`：∀ (R : Type u_1) (S : Type u_2) (T : Type u_
3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 : A
lgebra R S] [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
-/
lemma essFiniteType_iff_exists_subalgebra : EssFiniteType R S ↔
    ∃ (S₀ : Subalgebra R S) (M : Submonoid S₀), FiniteType R S₀ ∧ IsLocalization M S := by
  refine ⟨fun h ↦ ⟨subalgebra R S, submonoid R S, inferInstance, inferInstance⟩, ?_⟩
  rintro ⟨S₀, M, _, _⟩
  let := of_isLocalization S M
  exact comp R S₀ S
/-
**Algebra.EssFiniteType.baseChange** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.EssFiniteT
ype`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) (T : Type u_3) [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] [h : Algebra.EssFiniteType R S],   Algebra.EssFiniteType T (TensorProduct R
 T S)
参数：R : Type u_1；S : Type u_2；T : Type u_3；TensorProduct R T S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.essFiniteType_iff`：essFiniteType_iff : EssFiniteType R S ↔ exist
s (σ : Finset S), (forall s : S, exists t in Algebra.adjoin R (σ : Set S), IsUni
t t ∧ s * t in …
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subalgebra.mem_map`：mem_map {S : Subalgebra R A} {f : A ->ₐ[R] B} {y : B
} : y in map f S ↔ exists x in S, f x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_adjoin_of_tower`：adjoin_adjoin_of_tower (s : Set A) : adj
oin S (adjoin R s : Set A) = adjoin S s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用定理 `Subalgebra.smul_mem`：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S
（共 40 条，此处仅展示前 30 条）
-/
instance EssFiniteType.baseChange [h : EssFiniteType R S] : EssFiniteType T (T ⊗[R] S) := by
  classical
  rw [essFiniteType_iff] at h ⊢
  obtain ⟨σ, hσ⟩ := h
  use σ.image Algebra.TensorProduct.includeRight
  intro s
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, isUnit_one, by simp⟩
  | tmul x y =>
    obtain ⟨t, h₁, h₂, h₃⟩ := hσ y
    have H (x : S) (hx : x ∈ Algebra.adjoin R (σ : Set S)) :
        1 ⊗ₜ[R] x ∈ Algebra.adjoin T
          ((σ.image Algebra.TensorProduct.includeRight : Finset (T ⊗[R] S)) : Set (T ⊗[R] S)) := by
      have : Algebra.TensorProduct.includeRight x ∈
          (Algebra.adjoin R (σ : Set S)).map (Algebra.TensorProduct.includeRight (A := T)) :=
        Subalgebra.mem_map.mpr ⟨_, hx, rfl⟩
      rw [← Algebra.adjoin_adjoin_of_tower R]
      apply Algebra.subset_adjoin
      simpa [← Algebra.adjoin_image] using this
    refine ⟨Algebra.TensorProduct.includeRight t, H _ h₁, h₂.map _, ?_⟩
    simp only [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one]
    rw [← mul_one x, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    apply Subalgebra.smul_mem
    exact H _ h₃
  | add x y hx hy =>
    obtain ⟨tx, hx₁, hx₂, hx₃⟩ := hx
    obtain ⟨ty, hy₁, hy₂, hy₃⟩ := hy
    refine ⟨_, mul_mem hx₁ hy₁, hx₂.mul hy₂, ?_⟩
    rw [add_mul, ← mul_assoc, mul_comm tx ty, ← mul_assoc]
    exact add_mem (mul_mem hx₃ hy₁) (mul_mem hy₃ hx₁)
/-
**Algebra.EssFiniteType.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.EssFiniteType
`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) (T : Type u_3) [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] [inst_5 : Algebra S T] [IsScalarTower R S T]   [h : Algebra.EssFiniteType R
 T], Algebra.EssFiniteType S T
参数：R : Type u_1；S : Type u_2；T : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.essFiniteType_iff`：essFiniteType_iff : EssFiniteType R S ↔ exist
s (σ : Finset S), (forall s : S, exists t in Algebra.adjoin R (σ : Set S), IsUni
t t ∧ s * t in …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_adjoin_of_tower`：adjoin_adjoin_of_tower (s : Set A) : adj
oin S (adjoin R s : Set A) = adjoin S s
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
lemma EssFiniteType.of_comp [h : EssFiniteType R T] : EssFiniteType S T := by
  rw [essFiniteType_iff] at h ⊢
  obtain ⟨σ, hσ⟩ := h
  use σ
  intro x
  obtain ⟨y, hy₁, hy₂, hy₃⟩ := hσ x
  simp_rw [← Algebra.adjoin_adjoin_of_tower R (S := S) (σ : Set T)]
  exact ⟨y, Algebra.subset_adjoin hy₁, hy₂, Algebra.subset_adjoin hy₃⟩
/-
**Algebra.EssFiniteType.comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.EssFiniteTyp
e`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) (T : Type u_3) [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] [inst_5 : Algebra S T] [IsScalarTower R S T]   [Algebra.EssFiniteType R S],
 Algebra.EssFiniteType R T ↔ Algebra.EssFiniteType S T
参数：R : Type u_1；S : Type u_2；T : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.EssFiniteType.of_comp`：∀ (R : Type u_1) (S : Type u_2) (T : Type
 u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 
: Algebra R S] [ins…
· 使用定理 `Algebra.EssFiniteType.comp`：∀ (R : Type u_1) (S : Type u_2) (T : Type u_
3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 : A
lgebra R S] [ins…
-/
lemma EssFiniteType.comp_iff [EssFiniteType R S] :
    EssFiniteType R T ↔ EssFiniteType S T :=
  ⟨fun _ ↦ of_comp R S T, fun _ ↦ comp R S T⟩
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EssFiniteType R S] (I : Ideal S) : EssFiniteType R (S ⧸ I) :=
  .comp R S _
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EssFiniteType R S] (M : Submonoid S) : EssFiniteType R (Localization M) :=
  have : EssFiniteType S (Localization M) := .of_isLocalization _ M
  .comp R S _

end

variable {R S T} in
/-
**Algebra.EssFiniteType.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.EssFini
teType`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] (f : S →ₐ[R] T),   Function.Surjective ⇑f → ∀ [Algebra.EssFiniteType R S], 
Algebra.EssFiniteType R T
参数：f : S →ₐ[R] T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `Algebra.EssFiniteType.comp`：∀ (R : Type u_1) (S : Type u_2) (T : Type u_
3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 : A
lgebra R S] [ins…
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…
-/
lemma EssFiniteType.of_surjective (f : S →ₐ[R] T) (hf : Function.Surjective f)
    [EssFiniteType R S] : EssFiniteType R T := by
  let := f.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite S T := .of_surjective (Algebra.linearMap S T) hf
  exact .comp R S T

variable {R S T} in
/-
**Algebra.EssFiniteType.iff_of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.EssFi
niteType`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] (f : S ≃ₐ[R] T), Algebra.EssFiniteType R S ↔ Algebra.EssFiniteType R T
参数：f : S ≃ₐ[R] T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.EssFiniteType.of_surjective`：∀ {R : Type u_1} {S : Type u_2} {T 
: Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [i
nst_3 : Algebra R S] [ins…
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
-/
lemma EssFiniteType.iff_of_algEquiv (f : S ≃ₐ[R] T) :
    EssFiniteType R S ↔ EssFiniteType R T where
  mp _ := .of_surjective f.toAlgHom f.surjective
  mpr _ := .of_surjective f.symm.toAlgHom f.symm.surjective

variable {R S} in
/-
**Algebra.EssFiniteType.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.EssFiniteT
ype`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} (T : Type u_3) [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] [inst_5 : Algebra.EssFiniteType R S] (f g : S →ₐ[R] T),   (∀ s ∈ Algebra.Es
sFiniteType.finset R S, f s = g s) → f = g
参数：T : Type u_3；f g : S →ₐ[R] T；∀ s ∈ Algebra.EssFiniteType.finset R S, f s = g 
s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `Algebra.EssFiniteType.isLocalization`：∀ (R : Type u_1) (S : Type u_2) [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [h : Algebra.Es
sFiniteType R S], IsLocali…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHom.ext_of_adjoin_eq_top`：ext_of_adjoin_eq_top {s : Set A} (h : adjoi
n R s = ⊤) ⦃φ₁ φ₂ : A ->ₐ[R] B⦄ (hs : s.EqOn φ₁ φ₂) : φ₁ = φ₂
· 使用定理 `Algebra.EssFiniteType.adjoin_mem_finset`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [inst_3 : Al
gebra.EssFiniteType R S], Alg…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
-/
lemma EssFiniteType.algHom_ext [EssFiniteType R S]
    (f g : S →ₐ[R] T) (H : ∀ s ∈ finset R S, f s = g s) : f = g := by
  suffices f.toRingHom = g.toRingHom by ext; exact RingHom.congr_fun this _
  apply IsLocalization.ringHom_ext (EssFiniteType.submonoid R S)
  suffices f.comp (IsScalarTower.toAlgHom R _ S) = g.comp (IsScalarTower.toAlgHom R _ S) by
    ext; exact AlgHom.congr_fun this _
  apply AlgHom.ext_of_adjoin_eq_top (s := { x | x.1 ∈ finset R S })
  · exact adjoin_mem_finset R S
  · rintro ⟨x, hx⟩ hx'; exact H x hx'
/-
**Algebra.EssFiniteType.quotient_map** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.EssFinit
eType`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.EssFiniteType R S] (p : Ideal R), Algebra.EssF
initeType (R ⧸ p) (S ⧸ Ideal.map (algebraMap R S) p)
参数：R : Type u_1；S : Type u_2；p : Ideal R；R ⧸ p；S ⧸ Ideal.map (algebraMap R S) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.EssFiniteType.of_surjective`：∀ {R : Type u_1} {S : Type u_2} {T 
: Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [i
nst_3 : Algebra R S] [ins…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `Algebra.EssFiniteType.baseChange`：∀ (R : Type u_1) (S : Type u_2) (T : T
ype u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst
_3 : Algebra R S] [ins…
-/
instance EssFiniteType.quotient_map [EssFiniteType R S] (p : Ideal R) :
    EssFiniteType (R ⧸ p) (S ⧸ p.map (algebraMap R S)) :=
  .of_surjective (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p).symm.toAlgHom
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p).symm.surjective

end Algebra

namespace RingHom

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {f : R →+* S}

/-- A ring hom is essentially of finite type if it is the composition of a localization map
and a ring hom of finite type. See `Algebra.EssFiniteType`. -/
@[algebraize Algebra.EssFiniteType]
/-
**RingHom.EssFiniteType** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：EssFiniteType (f : R ->+* S) : Prop
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring hom is essentially of finite type if it is the composition of a localizat
ion map
and a ring hom of finite type. See `Algebra.EssFiniteType`.
-/
def EssFiniteType (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.EssFiniteType R S
/-
**RingHom.essFiniteType_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：essFiniteType_algebraMap {R S : Type*} [CommRing R] [CommRing S] [Algebra 
R S] : (algebraMap R S).EssFiniteType ↔ Algebra.EssFiniteType R S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.EssFiniteType.eq_1`：∀ {R : Type u_1} {S : Type u_2} [inst : Comm
Ring R] [inst_1 : CommRing S] (f : R →+* S),   f.EssFiniteType = Algebra.EssFini
teType R S
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma essFiniteType_algebraMap {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] : (algebraMap R S).EssFiniteType ↔ Algebra.EssFiniteType R S := by
  rw [RingHom.EssFiniteType, toAlgebra_algebraMap]

/-- A choice of "essential generators" for a ring hom essentially of finite type.
See `Algebra.EssFiniteType.ext`. -/
noncomputable
/-
**RingHom.EssFiniteType.finset** 是 Mathlib 中的一个定义，位于命名空间 `RingHom.EssFiniteType`
。
形式化陈述：{R : Type u_1} →   {S : Type u_2} → [inst : CommRing R] → [inst_1 : CommRi
ng S] → {f : R →+* S} → f.EssFiniteType → Finset S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def EssFiniteType.finset (hf : f.EssFiniteType) : Finset S :=
  letI := f.toAlgebra
  haveI : Algebra.EssFiniteType R S := hf
  Algebra.EssFiniteType.finset R S
/-
**RingHom.FiniteType.essFiniteType** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.FiniteType
`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
{f : R →+* S}, f.FiniteType → f.EssFiniteType
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
-/
lemma FiniteType.essFiniteType (hf : f.FiniteType) : f.EssFiniteType := by
  algebraize [f]
  change Algebra.EssFiniteType R S
  infer_instance
/-
**RingHom.EssFiniteType.ext** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.EssFiniteType`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   {f : R →+* S} (hf : f.EssFiniteType) {g₁ 
g₂ : S →+* T},   g₁.comp f = g₂.comp f → (∀ x ∈ hf.finset, g₁ x = g₂ x) → g₁ = g
₂
参数：hf : f.EssFiniteType；∀ x ∈ hf.finset, g₁ x = g₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.EssFiniteType.algHom_ext`：∀ {R : Type u_1} {S : Type u_2} (T : T
ype u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst
_3 : Algebra R S] [ins…
-/
lemma EssFiniteType.ext (hf : f.EssFiniteType) {g₁ g₂ : S →+* T}
    (h₁ : g₁.comp f = g₂.comp f) (h₂ : ∀ x ∈ hf.finset, g₁ x = g₂ x) : g₁ = g₂ := by
  algebraize [f, g₁.comp f]
  ext x
  exact DFunLike.congr_fun (Algebra.EssFiniteType.algHom_ext T
    ⟨g₁, fun _ ↦ rfl⟩ ⟨g₂, DFunLike.congr_fun h₁.symm⟩ h₂) x

end RingHom

