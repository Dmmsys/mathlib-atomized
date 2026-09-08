/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.FieldTheory.Galois.Basic

/-!
# Galois Groups of Polynomials

In this file, we introduce the Galois group of a polynomial `p` over a field `F`,
defined as the automorphism group of its splitting field. We also provide
some results about some extension `E` above `p.SplittingField`.

## Main definitions

- `Polynomial.Gal p`: the Galois group of a polynomial p.
- `Polynomial.Gal.restrict p E`: the restriction homomorphism `Gal(E/F) → gal p`.
- `Polynomial.Gal.galAction p E`: the action of `gal p` on the roots of `p` in `E`.

## Main results

- `Polynomial.Gal.restrict_smul`: `restrict p E` is compatible with `gal_action p E`.
- `Polynomial.Gal.galActionHom_injective`: `gal p` acting on the roots of `p` in `E` is faithful.
- `Polynomial.Gal.restrictProd_injective`: `gal (p * q)` embeds as a subgroup of `gal p × gal q`.
- `Polynomial.Gal.card_of_separable`: For a separable polynomial, its Galois group has cardinality
  equal to the dimension of its splitting field over `F`.
- `Polynomial.Gal.galActionHom_bijective_of_prime_degree`:
  An irreducible polynomial of prime degree with two non-real roots has full Galois group.

## Other results
- `Polynomial.Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv`: The number of complex roots
  equals the number of real roots plus the number of roots not fixed by complex conjugation
  (i.e. with some imaginary component).

-/

@[expose] public section

assert_not_exists Real

noncomputable section

open scoped Polynomial

open Module

namespace Polynomial

variable {F : Type*} [Field F] (p q : F[X]) (E : Type*) [Field E] [Algebra F E]

/-- The Galois group of a polynomial. -/
/-
**Polynomial.Gal** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：Gal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Galois group of a polynomial.
-/
def Gal :=
  p.SplittingField ≃ₐ[F] p.SplittingField
deriving Group, Fintype, EquivLike, AlgEquivClass, MulSemiringAction _ p.SplittingField

namespace Gal

@[ext]
/-
**Polynomial.Gal.ext** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Gal`。
形式化陈述：ext {σ τ : p.Gal} (h : forall x in p.rootSet p.SplittingField, σ x = τ x) 
: σ = τ
参数：h : forall x in p.rootSet p.SplittingField, σ x = τ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgHom.mem_equalizer`：mem_equalizer (φ ψ : A ->ₐ[R] B) (x : A) : x in eq
ualizer φ ψ ↔ φ x = ψ x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.SplittingField.adjoin_rootSet`：adjoin_rootSet : Algebra.adjoi
n K (f.rootSet (SplittingField f)) = ⊤
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `Algebra.mem_top`：mem_top {x : A} : x in (⊤ : Subalgebra R A)
-/
theorem ext {σ τ : p.Gal} (h : ∀ x ∈ p.rootSet p.SplittingField, σ x = τ x) : σ = τ := by
  refine
    AlgEquiv.ext fun x =>
      (AlgHom.mem_equalizer σ.toAlgHom τ.toAlgHom x).mp
        ((SetLike.ext_iff.mp ?_ x).mpr Algebra.mem_top)
  rwa [eq_top_iff, ← SplittingField.adjoin_rootSet, Algebra.adjoin_le_iff]

set_option backward.isDefEq.respectTransparency.types false in
/-- If `p` splits in `F` then the `p.gal` is trivial. -/
@[instance_reducible]
/-
**Polynomial.Gal.uniqueGalOfSplits** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Gal`。
形式化陈述：uniqueGalOfSplits (h : p.Splits) : Unique p.Gal where default
参数：h : p.Splits。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `p` splits in `F` then the `p.gal` is trivial.
-/
def uniqueGalOfSplits (h : p.Splits) : Unique p.Gal where
  default := 1
  uniq f :=
    AlgEquiv.ext fun x => by
      obtain ⟨y, rfl⟩ :=
        Algebra.mem_bot.mp
          ((SetLike.ext_iff.mp ((IsSplittingField.splits_iff _ p).mp h) x).mp Algebra.mem_top)
      rw [AlgEquiv.commutes, AlgEquiv.commutes]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Polynomial.Gal.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Gal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : Fact p.Splits] : Unique p.Gal :=
  uniqueGalOfSplits _ h.1

set_option backward.isDefEq.respectTransparency.types false in
/-
**Polynomial.Gal.uniqueGalZero** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Gal`。
形式化陈述：uniqueGalZero : Unique (0 : F[X]).Gal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueGalZero : Unique (0 : F[X]).Gal :=
  uniqueGalOfSplits _ (by simp)

set_option backward.isDefEq.respectTransparency.types false in
/-
**Polynomial.Gal.uniqueGalOne** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Gal`。
形式化陈述：uniqueGalOne : Unique (1 : F[X]).Gal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueGalOne : Unique (1 : F[X]).Gal :=
  uniqueGalOfSplits _ Splits.one

set_option backward.isDefEq.respectTransparency.types false in
/-
**Polynomial.Gal.uniqueGalC** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Gal`。
形式化陈述：uniqueGalC (x : F) : Unique (C x).Gal
参数：x : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueGalC (x : F) : Unique (C x).Gal :=
  uniqueGalOfSplits _ (by simp)

set_option backward.isDefEq.respectTransparency.types false in
/-
**Polynomial.Gal.uniqueGalX** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Gal`。
形式化陈述：uniqueGalX : Unique (X : F[X]).Gal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueGalX : Unique (X : F[X]).Gal :=
  uniqueGalOfSplits _ Splits.X

set_option backward.isDefEq.respectTransparency.types false in
/-
**Polynomial.Gal.uniqueGalXSubC** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Gal`。
形式化陈述：uniqueGalXSubC (x : F) : Unique (X - C x).Gal
参数：x : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueGalXSubC (x : F) : Unique (X - C x).Gal :=
  uniqueGalOfSplits _ (Splits.X_sub_C _)

set_option backward.isDefEq.respectTransparency.types false in
/-
**Polynomial.Gal.uniqueGalXPow** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Gal`。
形式化陈述：uniqueGalXPow (n : Nat) : Unique (X ^ n : F[X]).Gal
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueGalXPow (n : ℕ) : Unique (X ^ n : F[X]).Gal :=
  uniqueGalOfSplits _ (Splits.X_pow _)
/-
**Polynomial.Gal.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Gal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : Fact ((p.map (algebraMap F E)).Splits)] : Algebra p.SplittingField E :=
  (IsSplittingField.lift p.SplittingField p h.1).toRingHom.toAlgebra
/-
**Polynomial.Gal.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Gal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : Fact ((p.map (algebraMap F E)).Splits)] : IsScalarTower F p.SplittingField E :=
  IsScalarTower.of_algebraMap_eq fun x =>
    ((IsSplittingField.lift p.SplittingField p h.1).commutes x).symm

-- The `Algebra p.SplittingField E` instance above behaves badly when
-- `E := p.SplittingField`, since it may result in a unification problem
-- `IsSplittingField.lift.toRingHom.toAlgebra =?= Algebra.id`,
-- which takes an extremely long time to resolve, causing timeouts.
-- Since we don't really care about this definition, marking it as irreducible
-- causes that unification to error out early.
/-- Restrict from a superfield automorphism into a member of `gal p`. -/
/-
**Polynomial.Gal.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Gal`。
形式化陈述：restrict [Fact ((p.map (algebraMap F E)).Splits)] : Gal(E/F) ->* p.Gal
参数：(p.map (algebraMap F E)).Splits。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Gal.instIsScalarTowerSplittingField`：∀ {F : Type u_1} [inst :
 Field F] (p : Polynomial F) (E : Type u_2) [inst_1 : Field E] [inst_2 : Algebra
 F E]   [h : Fact (Polynomial.map (a…

--- 原说明 ---
Restrict from a superfield automorphism into a member of `gal p`.
-/
def restrict [Fact ((p.map (algebraMap F E)).Splits)] : Gal(E/F) →* p.Gal :=
  AlgEquiv.restrictNormalHom p.SplittingField
/-
**Polynomial.Gal.restrict_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Gal`。
形式化陈述：restrict_surjective [Fact ((p.map (algebraMap F E)).Splits)] [Normal F E] 
: Function.Surjective (restrict p E)
参数：(p.map (algebraMap F E)).Splits。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.restrictNormalHom_surjective`：AlgEquiv.restrictNormalHom_surjec
tive [Normal F K₁] [Normal F E] : Function.Surjective (AlgEquiv.restrictNormalHo
m K₁ : Gal(E/F) -> K₁ ≃ₐ[F]…
· 使用定理 `Polynomial.Gal.instIsScalarTowerSplittingField`：∀ {F : Type u_1} [inst :
 Field F] (p : Polynomial F) (E : Type u_2) [inst_1 : Field E] [inst_2 : Algebra
 F E]   [h : Fact (Polynomial.map (a…
-/
theorem restrict_surjective [Fact ((p.map (algebraMap F E)).Splits)] [Normal F E] :
    Function.Surjective (restrict p E) :=
  AlgEquiv.restrictNormalHom_surjective E

section RootsAction

/-- The function taking `rootSet p p.SplittingField` to `rootSet p E`. This is actually a bijection,
see `Polynomial.Gal.mapRoots_bijective`. -/
/-
**Polynomial.Gal.mapRoots** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Gal`。
形式化陈述：mapRoots [Fact ((p.map (algebraMap F E)).Splits)] : rootSet p p.SplittingF
ield -> rootSet p E
参数：(p.map (algebraMap F E)).Splits。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Gal.instIsScalarTowerSplittingField`：∀ {F : Type u_1} [inst :
 Field F] (p : Polynomial F) (E : Type u_2) [inst_1 : Field E] [inst_2 : Algebra
 F E]   [h : Fact (Polynomial.map (a…

--- 原说明 ---
The function taking `rootSet p p.SplittingField` to `rootSet p E`. This is actua
lly a bijection,
see `Polynomial.Gal.mapRoots_bijective`.
-/
def mapRoots [Fact ((p.map (algebraMap F E)).Splits)] : rootSet p p.SplittingField → rootSet p E :=
  Set.MapsTo.restrict (IsScalarTower.toAlgHom F p.SplittingField E) _ _ <| rootSet_mapsTo _
/-
**Polynomial.Gal.mapRoots_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Gal`。
形式化陈述：mapRoots_bijective [h : Fact ((p.map (algebraMap F E)).Splits)] : Function
.Bijective (mapRoots p E)
参数：(p.map (algebraMap F E)).Splits。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.Gal.instIsScalarTowerSplittingField`：∀ {F : Type u_1} [inst :
 Field F] (p : Polynomial F) (E : Type u_2) [inst_1 : Field E] [inst_2 : Algebra
 F E]   [h : Fact (Polynomial.map (a…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.Splits.roots_map`：∀ {R : Type u_1} {S : Type u_2} [inst : Fie
ld R] [inst_1 : CommRing S] [inst_2 : IsDomain S] {f : Polynomial R},   f.Splits
 → ∀ (i : R →+* S…
· 使用定理 `Polynomial.IsSplittingField.splits`：splits (f : K[X]) [IsSplittingField 
K L f] : Splits (f.map (algebraMap K L))
· 使用定理 `Polynomial.IsSplittingField.splittingField`：∀ {K : Type v} [inst : Field
 K] (f : Polynomial K), Polynomial.IsSplittingField K f.SplittingField f
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
-/
theorem mapRoots_bijective [h : Fact ((p.map (algebraMap F E)).Splits)] :
    Function.Bijective (mapRoots p E) := by
  constructor
  · exact fun _ _ h => Subtype.ext (RingHom.injective _ (Subtype.ext_iff.mp h))
  · intro y
    -- this is just an equality of two different ways to write the roots of `p` as an `E`-polynomial
    have key := (IsSplittingField.splits p.SplittingField p).roots_map
      (IsScalarTower.toAlgHom F p.SplittingField E : p.SplittingField →+* E)
    rw [map_map, AlgHom.comp_algebraMap] at key
    have hy := Subtype.mem y
    simp only [rootSet, Finset.mem_coe, Multiset.mem_toFinset, key, Multiset.mem_map] at hy
    rcases hy with ⟨x, hx1, hx2⟩
    exact ⟨⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr hx1⟩, Subtype.ext hx2⟩

/-- The bijection between `rootSet p p.SplittingField` and `rootSet p E`. -/
/-
**Polynomial.Gal.rootsEquivRoots** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Gal`。
形式化陈述：rootsEquivRoots [Fact ((p.map (algebraMap F E)).Splits)] : rootSet p p.Spl
ittingField ≃ rootSet p E
参数：(p.map (algebraMap F E)).Splits。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Gal.mapRoots_bijective`：mapRoots_bijective [h : Fact ((p.map 
(algebraMap F E)).Splits)] : Function.Bijective (mapRoots p E)

--- 原说明 ---
The bijection between `rootSet p p.SplittingField` and `rootSet p E`.
-/
def rootsEquivRoots [Fact ((p.map (algebraMap F E)).Splits)] :
    rootSet p p.SplittingField ≃ rootSet p E :=
  Equiv.ofBijective (mapRoots p E) (mapRoots_bijective p E)
/-
**Polynomial.Gal.galActionAux** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Gal`。
形式化陈述：galActionAux : MulAction p.Gal (rootSet p p.SplittingField) where smul ϕ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance galActionAux : MulAction p.Gal (rootSet p p.SplittingField) where
  smul ϕ := Set.MapsTo.restrict ϕ _ _ <| rootSet_mapsTo ϕ.toAlgHom
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl
/-
**Polynomial.Gal.smul** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Gal`。
形式化陈述：smul [Fact ((p.map (algebraMap F E)).Splits)] : SMul p.Gal (rootSet p E) w
here smul ϕ x
参数：(p.map (algebraMap F E)).Splits。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance smul [Fact ((p.map (algebraMap F E)).Splits)] : SMul p.Gal (rootSet p E) where
  smul ϕ x := rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm x)
/-
**Polynomial.Gal.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Gal`。
形式化陈述：smul_def [Fact ((p.map (algebraMap F E)).Splits)] (ϕ : p.Gal) (x : rootSet
 p E) : ϕ • x = rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm x)
参数：(p.map (algebraMap F E)).Splits；ϕ : p.Gal；x : rootSet p E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
theorem smul_def [Fact ((p.map (algebraMap F E)).Splits)] (ϕ : p.Gal) (x : rootSet p E) :
    ϕ • x = rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm x) :=
  rfl

/-- The action of `gal p` on the roots of `p` in `E`. -/
/-
**Polynomial.Gal.galAction** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Gal`。
形式化陈述：galAction [Fact ((p.map (algebraMap F E)).Splits)] : MulAction p.Gal (root
Set p E) where one_smul _
参数：(p.map (algebraMap F E)).Splits。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of `gal p` on the roots of `p` in `E`.
-/
instance galAction [Fact ((p.map (algebraMap F E)).Splits)] : MulAction p.Gal (rootSet p E) where
  one_smul _ := by simp only [smul_def, Equiv.apply_symm_apply, one_smul]
  mul_smul _ _ _ := by
    simp only [smul_def, Equiv.symm_apply_apply, mul_smul]
/-
**Polynomial.Gal.galAction_isPretransitive** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial
.Gal`。
形式化陈述：galAction_isPretransitive [Fact ((p.map (algebraMap F E)).Splits)] (hp : I
rreducible p) : MulAction.IsPretransitive p.Gal (p.rootSet E)
参数：(p.map (algebraMap F E)).Splits；hp : Irreducible p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `minpoly.eq_of_irreducible`：eq_of_irreducible [Nontrivial B] {p : A[X]} (
hp1 : Irreducible p) (hp2 : Polynomial.aeval x p = 0) : p * C p.leadingCoeff⁻¹ =
 minpoly A x
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_rootSet`：mem_rootSet {p : T[X]} {S : Type*} [IsDomain T] 
[CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] {a : S} : a i
n p.rootSet …
· 使用定理 `Polynomial.IsSplittingField.instIsTorsionFreeSplittingField`：∀ {K : Type
 v} [inst : Field K] (f : Polynomial K), Module.IsTorsionFree K f.SplittingField
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Normal.minpoly_eq_iff_mem_orbit`：Normal.minpoly_eq_iff_mem_orbit [h : No
rmal F E] {x y : E} : minpoly F x = minpoly F y ↔ x in MulAction.orbit Gal(E/F) 
y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
lemma galAction_isPretransitive [Fact ((p.map (algebraMap F E)).Splits)] (hp : Irreducible p) :
    MulAction.IsPretransitive p.Gal (p.rootSet E) := by
  refine ⟨fun x y ↦ ?_⟩
  have hx := minpoly.eq_of_irreducible hp (mem_rootSet.mp ((rootsEquivRoots p E).symm x).2).2
  have hy := minpoly.eq_of_irreducible hp (mem_rootSet.mp ((rootsEquivRoots p E).symm y).2).2
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit p.SplittingField).mp (hy.symm.trans hx)
  exact ⟨g, (rootsEquivRoots p E).eq_symm_apply.mp (Subtype.ext hg)⟩

variable {p E}

/-- `Polynomial.Gal.restrict p E` is compatible with `Polynomial.Gal.galAction p E`. -/
@[simp]
/-
**Polynomial.Gal.restrict_smul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Gal`。
形式化陈述：restrict_smul [Fact ((p.map (algebraMap F E)).Splits)] (ϕ : Gal(E/F)) (x :
 rootSet p E) : ↑(restrict p E ϕ • x) = ϕ x
参数：(p.map (algebraMap F E)).Splits；ϕ : Gal(E/F)；x : rootSet p E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.Gal.instIsScalarTowerSplittingField`：∀ {F : Type u_1} [inst :
 Field F] (p : Polynomial F) (E : Type u_2) [inst_1 : Field E] [inst_2 : Algebra
 F E]   [h : Fact (Polynomial.map (a…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x

--- 原说明 ---
`Polynomial.Gal.restrict p E` is compatible with `Polynomial.Gal.galAction p E`.
-/
theorem restrict_smul [Fact ((p.map (algebraMap F E)).Splits)] (ϕ : Gal(E/F)) (x : rootSet p E) :
    ↑(restrict p E ϕ • x) = ϕ x := by
  let ψ := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F p.SplittingField E)
  change ↑(ψ (ψ.symm _)) = ϕ x
  rw [AlgEquiv.apply_symm_apply ψ]
  change ϕ (rootsEquivRoots p E ((rootsEquivRoots p E).symm x)) = ϕ x
  rw [Equiv.apply_symm_apply (rootsEquivRoots p E)]

variable (p E)

/-- `Polynomial.Gal.galAction` as a permutation representation -/
/-
**Polynomial.Gal.galActionHom** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Gal`。
形式化陈述：galActionHom [Fact ((p.map (algebraMap F E)).Splits)] : p.Gal ->* Equiv.Pe
rm (rootSet p E)
参数：(p.map (algebraMap F E)).Splits。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Polynomial.Gal.galAction` as a permutation representation
-/
def galActionHom [Fact ((p.map (algebraMap F E)).Splits)] : p.Gal →* Equiv.Perm (rootSet p E) :=
  MulAction.toPermHom _ _
/-
**Polynomial.Gal.galActionHom_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Gal
`。
形式化陈述：galActionHom_restrict [Fact ((p.map (algebraMap F E)).Splits)] (ϕ : Gal(E/
F)) (x : rootSet p E) : ↑(galActionHom p E (restrict p E ϕ) x) = ϕ x
参数：(p.map (algebraMap F E)).Splits；ϕ : Gal(E/F)；x : rootSet p E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.Gal.restrict_smul`：restrict_smul [Fact ((p.map (algebraMap F 
E)).Splits)] (ϕ : Gal(E/F)) (x : rootSet p E) : ↑(restrict p E ϕ • x) = ϕ x
-/
theorem galActionHom_restrict [Fact ((p.map (algebraMap F E)).Splits)] (ϕ : Gal(E/F))
    (x : rootSet p E) : ↑(galActionHom p E (restrict p E ϕ) x) = ϕ x :=
  restrict_smul ϕ x

/-- `gal p` embeds as a subgroup of permutations of the roots of `p` in `E`. -/
/-
**Polynomial.Gal.galActionHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Ga
l`。
形式化陈述：galActionHom_injective [Fact ((p.map (algebraMap F E)).Splits)] : Function
.Injective (galActionHom p E)
参数：(p.map (algebraMap F E)).Splits。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `injective_iff_map_eq_one`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9}
 [inst : Group G] [inst_1 : MulOneClass H] [inst_2 : FunLike F G H]   [MonoidHom
Class F G H] (…
· 使用定理 `Polynomial.Gal.ext`：ext {σ τ : p.Gal} (h : forall x in p.rootSet p.Split
tingField, σ x = τ x) : σ = τ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.ext_iff`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, σ = τ ↔ ∀ (x : 
α), σ x = τ x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x

--- 原说明 ---
`gal p` embeds as a subgroup of permutations of the roots of `p` in `E`.
-/
theorem galActionHom_injective [Fact ((p.map (algebraMap F E)).Splits)] :
    Function.Injective (galActionHom p E) := by
  rw [injective_iff_map_eq_one]
  intro ϕ hϕ
  ext (x hx)
  have key := Equiv.Perm.ext_iff.mp hϕ (rootsEquivRoots p E ⟨x, hx⟩)
  change
    rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm (rootsEquivRoots p E ⟨x, hx⟩)) =
      rootsEquivRoots p E ⟨x, hx⟩
    at key
  rw [Equiv.symm_apply_apply] at key
  exact Subtype.ext_iff.mp (Equiv.injective (rootsEquivRoots p E) key)

end RootsAction

variable {p q}

/-- `Polynomial.Gal.restrict`, when both fields are splitting fields of polynomials. -/
/-
**Polynomial.Gal.restrictDvd** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Gal`。
形式化陈述：restrictDvd (hpq : p ∣ q) : q.Gal ->* p.Gal
参数：hpq : p ∣ q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Polynomial.Gal.restrict`, when both fields are splitting fields of polynomials.
-/
def restrictDvd (hpq : p ∣ q) : q.Gal →* p.Gal :=
  haveI := Classical.dec (q = 0)
  if hq : q = 0 then 1
  else
    @restrict F _ p _ _ _
      ⟨(SplittingField.splits q).of_dvd (map_ne_zero hq) ((map_dvd_map' _).mpr hpq)⟩
/-
**Polynomial.Gal.restrictDvd_def** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Gal`。
形式化陈述：restrictDvd_def [Decidable (q = 0)] (hpq : p ∣ q) : restrictDvd hpq = if h
q : q = 0 then 1 else @restrict F _ p _ _ _ ⟨(SplittingField.splits q).of_dvd (m
ap_ne_zero hq) ((map_dvd_map' _).mpr hpq)⟩
参数：q = 0；hpq : p ∣ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.of_dvd`：∀ {R : Type u_1} [inst : CommRing R] {f g : Po
lynomial R} [IsDomain R], g.Splits → g ≠ 0 → f ∣ g → f.Splits
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.SplittingField.splits`：∀ {K : Type v} [inst : Field K] (f : P
olynomial K), (Polynomial.map (algebraMap K f.SplittingField) f).Splits
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.map_dvd_map'`：map_dvd_map' [Field k] (f : R ->+* k) {x y : R[
X]} : x.map f ∣ y.map f ↔ x ∣ y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
theorem restrictDvd_def [Decidable (q = 0)] (hpq : p ∣ q) :
    restrictDvd hpq =
      if hq : q = 0 then 1
      else @restrict F _ p _ _ _
        ⟨(SplittingField.splits q).of_dvd (map_ne_zero hq) ((map_dvd_map' _).mpr hpq)⟩ := by
  unfold restrictDvd
  congr
/-
**Polynomial.Gal.restrictDvd_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Ga
l`。
形式化陈述：restrictDvd_surjective (hpq : p ∣ q) (hq : q != 0) : Function.Surjective (
restrictDvd hpq)
参数：hpq : p ∣ q；hq : q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.of_dvd`：∀ {R : Type u_1} [inst : CommRing R] {f g : Po
lynomial R} [IsDomain R], g.Splits → g ≠ 0 → f ∣ g → f.Splits
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.SplittingField.splits`：∀ {K : Type v} [inst : Field K] (f : P
olynomial K), (Polynomial.map (algebraMap K f.SplittingField) f).Splits
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.map_dvd_map'`：map_dvd_map' [Field k] (f : R ->+* k) {x y : R[
X]} : x.map f ∣ y.map f ↔ x ∣ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.Gal.restrictDvd_def`：restrictDvd_def [Decidable (q = 0)] (hpq
 : p ∣ q) : restrictDvd hpq = if hq : q = 0 then 1 else @restrict F _ p _ _ _ ⟨(
SplittingField.split…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Polynomial.Gal.restrict_surjective`：restrict_surjective [Fact ((p.map (a
lgebraMap F E)).Splits)] [Normal F E] : Function.Surjective (restrict p E)
-/
theorem restrictDvd_surjective (hpq : p ∣ q) (hq : q ≠ 0) :
    Function.Surjective (restrictDvd hpq) := by
  classical
  have := Fact.mk <|
    (SplittingField.splits q).of_dvd (map_ne_zero hq) ((map_dvd_map' _).mpr hpq)
  simpa only [restrictDvd_def, dif_neg hq] using! restrict_surjective _ _

variable (p q)

/-- The Galois group of a product maps into the product of the Galois groups. -/
/-
**Polynomial.Gal.restrictProd** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Gal`。
形式化陈述：restrictProd : (p * q).Gal ->* p.Gal × q.Gal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Galois group of a product maps into the product of the Galois groups.
-/
def restrictProd : (p * q).Gal →* p.Gal × q.Gal :=
  MonoidHom.prod (restrictDvd (dvd_mul_right p q)) (restrictDvd (dvd_mul_left q p))

set_option backward.isDefEq.respectTransparency false in
/-- `Polynomial.Gal.restrictProd` is actually a subgroup embedding. -/
/-
**Polynomial.Gal.restrictProd_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Ga
l`。
形式化陈述：restrictProd_injective : Function.Injective (restrictProd p q)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Gal.ext`：ext {σ τ : p.Gal} (h : forall x in p.rootSet p.Split
tingField, σ x = τ x) : σ = τ
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_add`：mem_add {a : α} {s t : Multiset α} : a in s + t ↔ a in
 s ∨ a in t
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Polynomial.aroots_mul`：aroots_mul [IsDomain T] [CommRing S] [IsDomain S]
 [Algebra T S] [Module.IsTorsionFree T S] {p q : T[X]} (hpq : p * q != 0) : (p *
 q).aroots …
· 使用定理 `Polynomial.IsSplittingField.instIsTorsionFreeSplittingField`：∀ {K : Type
 v} [inst : Field K] (f : Polynomial K), Module.IsTorsionFree K f.SplittingField
· 使用定理 `Polynomial.rootSet_def`：rootSet_def (p : T[X]) (S) [CommRing S] [IsDomai
n S] [Algebra T S] [DecidableEq S] : p.rootSet S = (p.aroots S).toFinset
· 使用定理 `Polynomial.Splits.of_dvd`：∀ {R : Type u_1} [inst : CommRing R] {f g : Po
lynomial R} [IsDomain R], g.Splits → g ≠ 0 → f ∣ g → f.Splits
· 使用定理 `Polynomial.SplittingField.splits`：∀ {K : Type v} [inst : Field K] (f : P
olynomial K), (Polynomial.map (algebraMap K f.SplittingField) f).Splits
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.map_dvd_map'`：map_dvd_map' [Field k] (f : R ->+* k) {x y : R[
X]} : x.map f ∣ y.map f ↔ x ∣ y
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Polynomial.Gal.instIsScalarTowerSplittingField`：∀ {F : Type u_1} [inst :
 Field F] (p : Polynomial F) (E : Type u_2) [inst_1 : Field E] [inst_2 : Algebra
 F E]   [h : Fact (Polynomial.map (a…
· 使用定理 `AlgEquiv.restrictNormal_commutes`：AlgEquiv.restrictNormal_commutes [Norm
al F E] (x : E) : algebraMap E K₂ (χ.restrictNormal E x) = χ (algebraMap E K₁ x)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `AlgEquiv.ext_iff`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst 
: CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Alge
bra R …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
`Polynomial.Gal.restrictProd` is actually a subgroup embedding.
-/
theorem restrictProd_injective : Function.Injective (restrictProd p q) := by
  by_cases hpq : p * q = 0
  · have : Unique (p * q).Gal := by rw [hpq]; infer_instance
    exact fun f g _ => Eq.trans (Unique.eq_default f) (Unique.eq_default g).symm
  intro f g hfg
  classical
  simp only [restrictProd, restrictDvd_def] at hfg
  simp only [dif_neg hpq, MonoidHom.prod_apply, Prod.mk_inj] at hfg
  ext (x hx)
  rw [rootSet_def, aroots_mul hpq] at hx
  rcases Multiset.mem_add.mp (Multiset.mem_toFinset.mp hx) with h | h
  · have : Fact ((p.map (algebraMap F (p * q).SplittingField)).Splits) :=
      ⟨(SplittingField.splits (p * q)).of_dvd (map_ne_zero hpq)
        ((map_dvd_map' _).mpr (dvd_mul_right p q))⟩
    have key :
      x =
        algebraMap p.SplittingField (p * q).SplittingField
          ((rootsEquivRoots p _).invFun
            ⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr h⟩) :=
      Subtype.ext_iff.mp (Equiv.apply_symm_apply (rootsEquivRoots p _) ⟨x, _⟩).symm
    rw [key, ← AlgEquiv.restrictNormal_commutes, ← AlgEquiv.restrictNormal_commutes]
    exact congr_arg _ (AlgEquiv.ext_iff.mp hfg.1 _)
  · have : Fact ((q.map (algebraMap F (p * q).SplittingField)).Splits) :=
      ⟨(SplittingField.splits (p * q)).of_dvd (map_ne_zero hpq)
        ((map_dvd_map' _).mpr (dvd_mul_left q p))⟩
    have key :
      x =
        algebraMap q.SplittingField (p * q).SplittingField
          ((rootsEquivRoots q _).invFun
            ⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr h⟩) :=
      Subtype.ext_iff.mp (Equiv.apply_symm_apply (rootsEquivRoots q _) ⟨x, _⟩).symm
    rw [key, ← AlgEquiv.restrictNormal_commutes, ← AlgEquiv.restrictNormal_commutes]
    exact congr_arg _ (AlgEquiv.ext_iff.mp hfg.2 _)
/-
**Polynomial.Gal.mul_splits_in_splittingField_of_mul** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial.Gal`。
形式化陈述：mul_splits_in_splittingField_of_mul {p₁ q₁ p₂ q₂ : F[X]} (hq₁ : q₁ != 0) (
hq₂ : q₂ != 0) (h₁ : (p₁.map (algebraMap F q₁.SplittingField)).Splits) (h₂ : (p₂
.map (algebraMap F q₂.SplittingField)).Splits) : ((p₁ * p₂).map (algebraMap F (q
₁ * q₂).SplittingField)).Splits
参数：hq₁ : q₁ != 0；hq₂ : q₂ != 0；h₁ : (p₁.map (algebraMap F q₁.SplittingField)).Sp
lits；h₂ : (p₂.map (algebraMap F q₂.SplittingField)).Splits。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.Splits.mul`：∀ {R : Type u_1} [inst : Semiring R] {f g : Polyn
omial R}, f.Splits → g.Splits → (f * g).Splits
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.Splits.of_dvd`：∀ {R : Type u_1} [inst : CommRing R] {f g : Po
lynomial R} [IsDomain R], g.Splits → g ≠ 0 → f ∣ g → f.Splits
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.SplittingField.splits`：∀ {K : Type v} [inst : Field K] (f : P
olynomial K), (Polynomial.map (algebraMap K f.SplittingField) f).Splits
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.map_dvd_map'`：map_dvd_map' [Field k] (f : R ->+* k) {x y : R[
X]} : x.map f ∣ y.map f ↔ x ∣ y
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.Splits.map`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R},   f.Splits → ∀ {S : Type u_2} [inst_1 : Semiring S] (i : R →+* S), (Poly
nomial.map …
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
-/
theorem mul_splits_in_splittingField_of_mul {p₁ q₁ p₂ q₂ : F[X]} (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (h₁ : (p₁.map (algebraMap F q₁.SplittingField)).Splits)
    (h₂ : (p₂.map (algebraMap F q₂.SplittingField)).Splits) :
    ((p₁ * p₂).map (algebraMap F (q₁ * q₂).SplittingField)).Splits := by
  rw [Polynomial.map_mul]
  apply Splits.mul
  · rw [←
      (SplittingField.lift q₁
          ((SplittingField.splits _).of_dvd (map_ne_zero (mul_ne_zero hq₁ hq₂))
             ((map_dvd_map' _).mpr (dvd_mul_right q₁ q₂)))).comp_algebraMap, ← map_map]
    exact h₁.map _
  · rw [←
      (SplittingField.lift q₂
          ((SplittingField.splits _).of_dvd (map_ne_zero (mul_ne_zero hq₁ hq₂))
             ((map_dvd_map' _).mpr (dvd_mul_left q₂ q₁)))).comp_algebraMap, ← map_map]
    exact h₂.map _

/-- `p` splits in the splitting field of `p ∘ q`, for `q` non-constant. -/
/-
**Polynomial.Gal.splits_in_splittingField_of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial.Gal`。
形式化陈述：splits_in_splittingField_of_comp (hq : q.natDegree != 0) : (p.map (algebra
Map F (p.comp q).SplittingField)).Splits
参数：hq : q.natDegree != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.of_natDegree_le_one`：∀ {R : Type u_1} [inst : Division
Semiring R] {f : Polynomial R}, f.natDegree ≤ 1 → f.Splits
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Polynomial.natDegree_map_le`：natDegree_map_le : natDegree (p.map f) <= n
atDegree p
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Polynomial.Splits.exists_eval_eq_zero`：∀ {R : Type u_1} [inst : CommRing
 R] {f : Polynomial R}, f.Splits → f.degree ≠ 0 → ∃ a, Polynomial.eval a f = 0
· 使用定理 `Polynomial.SplittingField.splits`：∀ {K : Type v} [inst : Field K] (f : P
olynomial K), (Polynomial.map (algebraMap K f.SplittingField) f).Splits
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_comp`：natDegree_comp : natDegree (p.comp q) = natDe
gree p * natDegree q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_map`：degree_map (p : R[X]) (f : R ->+* S) : (p.map f).
degree = p.degree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Normal.isIntegral`：Normal.isIntegral (_ : Normal F K) (x : K) : IsIntegr
al F x
· 使用定理 `Polynomial.Splits.of_dvd`：∀ {R : Type u_1} [inst : CommRing R] {f g : Po
lynomial R} [IsDomain R], g.Splits → g ≠ 0 → f ∣ g → f.Splits
· 使用定理 `Normal.splits`：Normal.splits (_ : Normal F K) (x : K) : Splits ((minpoly
 F x).map (algebraMap F K))
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.map_dvd_map'`：map_dvd_map' [Field k] (f : R ->+* k) {x y : R[
X]} : x.map f ∣ y.map f ↔ x ∣ y
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
`p` splits in the splitting field of `p ∘ q`, for `q` non-constant.
-/
theorem splits_in_splittingField_of_comp (hq : q.natDegree ≠ 0) :
    (p.map (algebraMap F (p.comp q).SplittingField)).Splits := by
  let P : F[X] → Prop := fun r => (r.map (algebraMap F (r.comp q).SplittingField)).Splits
  have key1 : ∀ {r : F[X]}, Irreducible r → P r := by
    intro r hr
    by_cases hr' : natDegree r = 0
    · exact Splits.of_natDegree_le_one <| natDegree_map_le.trans (hr'.trans_le zero_le_one)
    obtain ⟨x, hx⟩ :=
      Splits.exists_eval_eq_zero (SplittingField.splits (r.comp q)) fun h =>
        hr' ((mul_eq_zero.mp (natDegree_comp.symm.trans (natDegree_eq_of_degree_eq_some
          (by rwa [degree_map] at h)))).resolve_right hq)
    rw [eval_map_algebraMap, aeval_comp] at hx
    have h_normal : Normal F (r.comp q).SplittingField := SplittingField.instNormal (r.comp q)
    have qx_int := Normal.isIntegral h_normal (aeval x q)
    exact (h_normal.splits _).of_dvd (map_ne_zero (minpoly.ne_zero (h_normal.isIntegral _)))
      ((map_dvd_map' _).mpr ((minpoly.irreducible qx_int).dvd_symm hr (minpoly.dvd F _ hx)))
  have key2 : ∀ {p₁ p₂ : F[X]}, P p₁ → P p₂ → P (p₁ * p₂) := by
    intro p₁ p₂ hp₁ hp₂
    by_cases h₁ : p₁.comp q = 0
    · rcases comp_eq_zero_iff.mp h₁ with h | h
      · rw [h, zero_mul]
        simp [P]
      · exact False.elim (hq (by rw [h.2, natDegree_C]))
    by_cases h₂ : p₂.comp q = 0
    · rcases comp_eq_zero_iff.mp h₂ with h | h
      · simp [h, P]
      · exact False.elim (hq (by rw [h.2, natDegree_C]))
    have key := mul_splits_in_splittingField_of_mul h₁ h₂ hp₁ hp₂
    rwa [← mul_comp] at key
  exact
    WfDvdMonoid.induction_on_irreducible p (by simp) (fun _ hu => hu.splits.map _)
      fun _ _ _ h => key2 (key1 h)

/-- `Polynomial.Gal.restrict` for the composition of polynomials. -/
/-
**Polynomial.Gal.restrictComp** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Gal`。
形式化陈述：restrictComp (hq : q.natDegree != 0) : (p.comp q).Gal ->* p.Gal
参数：hq : q.natDegree != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Polynomial.Gal.restrict` for the composition of polynomials.
-/
def restrictComp (hq : q.natDegree ≠ 0) : (p.comp q).Gal →* p.Gal :=
  let h : Fact (Splits (p.map (algebraMap F (p.comp q).SplittingField))) :=
    ⟨splits_in_splittingField_of_comp p q hq⟩
  @restrict F _ p _ _ _ h
/-
**Polynomial.Gal.restrictComp_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.G
al`。
形式化陈述：restrictComp_surjective (hq : q.natDegree != 0) : Function.Surjective (res
trictComp p q hq)
参数：hq : q.natDegree != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Gal.splits_in_splittingField_of_comp`：splits_in_splittingFiel
d_of_comp (hq : q.natDegree != 0) : (p.map (algebraMap F (p.comp q).SplittingFie
ld)).Splits
· 使用定理 `Polynomial.Gal.restrict_surjective`：restrict_surjective [Fact ((p.map (a
lgebraMap F E)).Splits)] [Normal F E] : Function.Surjective (restrict p E)
-/
theorem restrictComp_surjective (hq : q.natDegree ≠ 0) :
    Function.Surjective (restrictComp p q hq) := by
  have : Fact (Splits (p.map (algebraMap F (SplittingField (comp p q))))) :=
    ⟨splits_in_splittingField_of_comp p q hq⟩
  simpa only [restrictComp] using! restrict_surjective _ _

variable {p q}

open scoped IntermediateField

/-- For a separable polynomial, its Galois group has cardinality
equal to the dimension of its splitting field over `F`. -/
/-
**Polynomial.Gal.card_of_separable** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Gal`。
形式化陈述：card_of_separable (hp : p.Separable) : Nat.card p.Gal = finrank F p.Splitt
ingField
参数：hp : p.Separable。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGalois.card_aut_eq_finrank`：card_aut_eq_finrank [FiniteDimensional F E
] [IsGalois F E] : Nat.card Gal(E/F) = finrank F E
· 使用定理 `Polynomial.IsSplittingField.instFiniteDimensionalSplittingField`：∀ {K : 
Type v} [inst : Field K] (f : Polynomial K), FiniteDimensional K f.SplittingFiel
d
· 使用定理 `IsGalois.of_separable_splitting_field`：of_separable_splitting_field [p.I
sSplittingField F E] (hp : p.Separable) : IsGalois F E
· 使用定理 `Polynomial.IsSplittingField.splittingField`：∀ {K : Type v} [inst : Field
 K] (f : Polynomial K), Polynomial.IsSplittingField K f.SplittingField f

--- 原说明 ---
For a separable polynomial, its Galois group has cardinality
equal to the dimension of its splitting field over `F`.
-/
theorem card_of_separable (hp : p.Separable) : Nat.card p.Gal = finrank F p.SplittingField :=
  haveI : IsGalois F p.SplittingField := IsGalois.of_separable_splitting_field hp
  IsGalois.card_aut_eq_finrank F p.SplittingField
/-
**Polynomial.Gal.prime_degree_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Gal
`。
形式化陈述：prime_degree_dvd_card [CharZero F] (p_irr : Irreducible p) (p_deg : p.natD
egree.Prime) : p.natDegree ∣ Nat.card p.Gal
参数：p_irr : Irreducible p；p_deg : p.natDegree.Prime。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Gal.card_of_separable`：card_of_separable (hp : p.Separable) :
 Nat.card p.Gal = finrank F p.SplittingField
· 使用定理 `Irreducible.separable`：∀ {F : Type u} [inst : Field F] [CharZero F] {f :
 Polynomial F}, Irreducible f → f.Separable
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natDegree_eq_zero_iff_degree_le_zero`：natDegree_eq_zero_iff_d
egree_le_zero : p.natDegree = 0 ↔ p.degree <= 0
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.SplittingField.splits`：∀ {K : Type v} [inst : Field K] (f : P
olynomial K), (Polynomial.map (algebraMap K f.SplittingField) f).Splits
· 使用定理 `Polynomial.degree_map`：degree_map (p : R[X]) (f : R ->+* S) : (p.map f).
degree = p.degree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsIntegral.of_finite`：IsIntegral.of_finite [Module.Finite R B] (x : B) :
 IsIntegral R x
· 使用定理 `Polynomial.IsSplittingField.instFiniteDimensionalSplittingField`：∀ {K : 
Type v} [inst : Field K] (f : Polynomial K), FiniteDimensional K f.SplittingFiel
d
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `Polynomial.eval_rootOfSplits`：eval_rootOfSplits (hf : f.Splits) (hfd : f
.degree != 0) : f.eval (rootOfSplits hf hfd) = 0
· 使用定理 `Irreducible.dvd_symm`：Irreducible.dvd_symm [Monoid M] {p q : M} (hp : Ir
reducible p) (hq : Irreducible q) : p ∣ q -> q ∣ p
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Polynomial.natDegree_le_of_dvd`：natDegree_le_of_dvd (h1 : p ∣ q) (h2 : q
 != 0) : p.natDegree <= q.natDegree
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `Polynomial.SplittingField.instIsScalarTower`：∀ {K : Type u_2} [inst : Fi
eld K] (f : Polynomial K) {R : Type u_1} [inst_1 : CommSemiring R] [inst_2 : Alg
ebra R K],   IsScalarTower R K f.…
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
（共 34 条，此处仅展示前 30 条）
-/
theorem prime_degree_dvd_card [CharZero F] (p_irr : Irreducible p) (p_deg : p.natDegree.Prime) :
    p.natDegree ∣ Nat.card p.Gal := by
  rw [Gal.card_of_separable p_irr.separable]
  have hp : p.degree ≠ 0 := fun h =>
    Nat.Prime.ne_zero p_deg (natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h))
  let α : p.SplittingField :=
    rootOfSplits (SplittingField.splits p) (by rwa [degree_map])
  have hα : IsIntegral F α := .of_finite F α
  use Module.finrank F⟮α⟯ p.SplittingField
  suffices (minpoly F α).natDegree = p.natDegree by
    let _ : AddCommGroup F⟮α⟯ := Ring.toAddCommGroup
    rw [← Module.finrank_mul_finrank F F⟮α⟯ p.SplittingField,
      IntermediateField.adjoin.finrank hα, this]
  suffices minpoly F α ∣ p by
    have key := (minpoly.irreducible hα).dvd_symm p_irr this
    apply le_antisymm
    · exact natDegree_le_of_dvd this p_irr.ne_zero
    · exact natDegree_le_of_dvd key (minpoly.ne_zero hα)
  apply minpoly.dvd F α
  rw [← eval_map_algebraMap, eval_rootOfSplits]

end Gal

end Polynomial

