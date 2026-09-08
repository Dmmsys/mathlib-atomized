/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.RingTheory.Adjoin.Field

/-!
# Splitting fields

This file introduces the notion of a splitting field of a polynomial and provides an embedding from
a splitting field to any field that splits the polynomial. A polynomial `f : K[X]` splits
over a field extension `L` of `K` if it is zero or all of its irreducible factors over `L` have
degree `1`. A field extension of `K` of a polynomial `f : K[X]` is called a splitting field
if it is the smallest field extension of `K` such that `f` splits.

## Main definitions

* `Polynomial.IsSplittingField`: A predicate on a field to be a splitting field of a polynomial
  `f`.

## Main statements

* `Polynomial.IsSplittingField.lift`: An embedding of a splitting field of the polynomial `f` into
  another field such that `f` splits.

-/

@[expose] public section

noncomputable section

universe u v w

variable {F : Type u} (K : Type v) (L : Type w)

namespace Polynomial

variable [Field K] [Field L] [Field F] [Algebra K L]

/-- Typeclass characterising splitting fields. -/
@[stacks 09HV "Predicate version"]
/-
**Polynomial.IsSplittingField** 是 Mathlib 中的一个归纳类型，位于命名空间 `Polynomial`。
形式化陈述：(K : Type v) → (L : Type w) → [inst : Field K] → [inst_1 : Field L] → [Alg
ebra K L] → Polynomial K → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass characterising splitting fields.
-/
class IsSplittingField (f : K[X]) : Prop where
  splits' : Splits (f.map (algebraMap K L))
  adjoin_rootSet' : Algebra.adjoin K (f.rootSet L : Set L) = ⊤

namespace IsSplittingField

variable {K}

/-
**Polynomial.IsSplittingField.splits** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsSpl
ittingField`。
形式化陈述：splits (f : K[X]) [IsSplittingField K L f] : Splits (f.map (algebraMap K L
))
参数：f : K[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsSplittingField.splits'`：∀ {K : Type v} {L : Type w} {inst :
 Field K} {inst_1 : Field L} {inst_2 : Algebra K L} {f : Polynomial K}   [self :
 Polynomial.IsSplittingFi…
-/
theorem splits (f : K[X]) [IsSplittingField K L f] : Splits (f.map (algebraMap K L)) :=
  splits'
/-
**Polynomial.IsSplittingField.adjoin_rootSet** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al.IsSplittingField`。
形式化陈述：adjoin_rootSet (f : K[X]) [IsSplittingField K L f] : Algebra.adjoin K (f.r
ootSet L : Set L) = ⊤
参数：f : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsSplittingField.adjoin_rootSet'`：∀ {K : Type v} {L : Type w}
 {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L} {f : Polynomial K}  
 [self : Polynomial.IsSplittingFi…
-/
theorem adjoin_rootSet (f : K[X]) [IsSplittingField K L f] :
    Algebra.adjoin K (f.rootSet L : Set L) = ⊤ :=
  adjoin_rootSet'

section ScalarTower

variable [Algebra F K] [Algebra F L] [IsScalarTower F K L]

/-
**Polynomial.IsSplittingField.map** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.IsSplitt
ingField`。
形式化陈述：map (f : F[X]) [IsSplittingField F L f] : IsSplittingField K L (f.map <| a
lgebraMap F K)
参数：f : F[X]。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Polynomial.IsSplittingField.splits`：splits (f : K[X]) [IsSplittingField 
K L f] : Splits (f.map (algebraMap K L))
· 使用定理 `Subalgebra.restrictScalars_injective`：restrictScalars_injective : Functi
on.Injective (restrictScalars R : Subalgebra S A -> Subalgebra R A)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.rootSet.eq_1`：∀ {T : Type w} [inst : CommRing T] (p : Polynom
ial T) (S : Type u_1) [inst_1 : CommRing S] [inst_2 : IsDomain S]   [inst_3 : Al
gebra T S], p…
· 使用定理 `Polynomial.aroots.eq_1`：∀ {T : Type w} [inst : CommRing T] (p : Polynomi
al T) (S : Type u_1) [inst_1 : CommRing S] [inst_2 : IsDomain S]   [inst_3 : Alg
ebra T S], p…
· 使用定理 `Subalgebra.restrictScalars_top`：restrictScalars_top : restrictScalars R 
(⊤ : Subalgebra S A) = ⊤
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Polynomial.IsSplittingField.adjoin_rootSet`：adjoin_rootSet (f : K[X]) [I
sSplittingField K L f] : Algebra.adjoin K (f.rootSet L : Set L) = ⊤
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
instance map (f : F[X]) [IsSplittingField F L f] : IsSplittingField K L (f.map <| algebraMap F K) :=
  ⟨by rw [map_map, ← IsScalarTower.algebraMap_eq]; exact splits L f,
    Subalgebra.restrictScalars_injective F <| by
      rw [rootSet, aroots, map_map, ← IsScalarTower.algebraMap_eq, Subalgebra.restrictScalars_top,
        eq_top_iff, ← adjoin_rootSet L f, Algebra.adjoin_le_iff]
      exact fun x hx => @Algebra.subset_adjoin K _ _ _ _ _ _ hx⟩
/-
**Polynomial.IsSplittingField.splits_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.I
sSplittingField`。
形式化陈述：splits_iff (f : K[X]) [IsSplittingField K L f] : Splits f ↔ (⊤ : Subalgebr
a K L) = ⊥ where mp h
参数：f : K[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.IsSplittingField.adjoin_rootSet`：adjoin_rootSet (f : K[X]) [I
sSplittingField K L f] : Algebra.adjoin K (f.rootSet L : Set L) = ⊤
· 使用定理 `Polynomial.rootSet.eq_1`：∀ {T : Type w} [inst : CommRing T] (p : Polynom
ial T) (S : Type u_1) [inst_1 : CommRing S] [inst_2 : IsDomain S]   [inst_3 : Al
gebra T S], p…
· 使用定理 `Polynomial.aroots.eq_1`：∀ {T : Type w} [inst : CommRing T] (p : Polynomi
al T) (S : Type u_1) [inst_1 : CommRing S] [inst_2 : IsDomain S]   [inst_3 : Alg
ebra T S], p…
· 使用定理 `Polynomial.Splits.roots_map`：∀ {R : Type u_1} {S : Type u_2} [inst : Fie
ld R] [inst_1 : CommRing S] [inst_2 : IsDomain S] {f : Polynomial R},   f.Splits
 → ∀ (i : R →+* S…
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Multiset.toFinset_map`：Multiset.toFinset_map [DecidableEq α] [DecidableE
q β] (f : α -> β) (m : Multiset α) : (m.map f).toFinset = m.toFinset.image f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
· 使用定理 `Polynomial.map_id`：map_id : p.map (RingHom.id _) = p
· 使用定理 `RingEquiv.toRingHom_refl`：toRingHom_refl : (RingEquiv.refl R).toRingHom 
= RingHom.id R
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Algebra.bijective_algebraMap_iff`：bijective_algebraMap_iff {R A : Type*}
 [Field R] [Semiring A] [Nontrivial A] [Algebra R A] : Function.Bijective (algeb
raMap R A) ↔ (⊤ : Suba…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingEquiv.self_trans_symm`：self_trans_symm (e : R ≃+* S) : e.trans e.sym
m = RingEquiv.refl R
· 使用定理 `RingEquiv.toRingHom_trans`：toRingHom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S'
) : (e₁.trans e₂).toRingHom = e₂.toRingHom.comp e₁.toRingHom
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.Splits.map`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R},   f.Splits → ∀ {S : Type u_2} [inst_1 : Semiring S] (i : R →+* S), (Poly
nomial.map …
· 使用定理 `Polynomial.IsSplittingField.splits`：splits (f : K[X]) [IsSplittingField 
K L f] : Splits (f.map (algebraMap K L))
-/
theorem splits_iff (f : K[X]) [IsSplittingField K L f] :
    Splits f ↔ (⊤ : Subalgebra K L) = ⊥ where
  mp h := by
    rw [eq_bot_iff, ← adjoin_rootSet L f, rootSet, aroots, h.roots_map, Algebra.adjoin_le_iff]
    intro y hy
    classical
    rw [Multiset.toFinset_map, Finset.mem_coe, Finset.mem_image] at hy
    obtain ⟨x : K, -, hxy : algebraMap K L x = y⟩ := hy
    rw [← hxy]
    exact SetLike.mem_coe.2 <| Subalgebra.algebraMap_mem _ _
  mpr h := by
    rw [← Polynomial.map_id (p := f), ← RingEquiv.toRingHom_refl, ← RingEquiv.self_trans_symm
      (RingEquiv.ofBijective _ <| Algebra.bijective_algebraMap_iff.2 h),
      RingEquiv.toRingHom_trans, ← map_map]
    apply (splits L f).map
/-
**Polynomial.IsSplittingField.IsScalarTower.splits** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial.IsSplittingField.IsScalarTower`。
形式化陈述：∀ {F : Type u} {K : Type v} (L : Type w) [inst : Field K] [inst_1 : Field 
L] [inst_2 : Field F] [inst_3 : Algebra K L]   [inst_4 : Algebra F K] [inst_5 : 
Algebra F L] [IsScalarTower F K L] (f : Polynomial F)   [Polynomial.IsSplittingF
ield K L ((Polynomial.mapAlg F K) f)], ((Polynomial.mapAlg F L) f).Splits
参数：L : Type w；f : Polynomial F；(Polynomial.mapAlg F K) f；(Polynomial.mapAlg F L)
 f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mapAlg_comp`：mapAlg_comp (p : A[X]) : (mapAlg A C) p = (mapAl
g B C) (mapAlg A B p)
· 使用定理 `Polynomial.mapAlg_eq_map`：mapAlg_eq_map (S : Type v) [Semiring S] [Algeb
ra R S] (p : R[X]) : mapAlg R S p = map (algebraMap R S) p
· 使用定理 `Polynomial.IsSplittingField.splits`：splits (f : K[X]) [IsSplittingField 
K L f] : Splits (f.map (algebraMap K L))
-/
theorem IsScalarTower.splits (f : F[X]) [IsSplittingField K L (mapAlg F K f)] :
    Splits (mapAlg F L f) := by
  rw [mapAlg_comp K L f, mapAlg_eq_map]
  apply IsSplittingField.splits
/-
**Polynomial.IsSplittingField.mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsSplitt
ingField`。
形式化陈述：mul (f g : F[X]) (hf : f != 0) (hg : g != 0) [IsSplittingField F K f] [IsS
plittingField K L (g.map <| algebraMap F K)] : IsSplittingField F L (f * g)
参数：f g : F[X]；hf : f != 0；hg : g != 0；g.map <| algebraMap F K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.Splits.mul`：∀ {R : Type u_1} [inst : Semiring R] {f g : Polyn
omial R}, f.Splits → g.Splits → (f * g).Splits
· 使用定理 `Polynomial.Splits.map`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R},   f.Splits → ∀ {S : Type u_2} [inst_1 : Semiring S] (i : R →+* S), (Poly
nomial.map …
· 使用定理 `Polynomial.IsSplittingField.splits`：splits (f : K[X]) [IsSplittingField 
K L f] : Splits (f.map (algebraMap K L))
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.rootSet.eq_1`：∀ {T : Type w} [inst : CommRing T] (p : Polynom
ial T) (S : Type u_1) [inst_1 : CommRing S] [inst_2 : IsDomain S]   [inst_3 : Al
gebra T S], p…
· 使用定理 `Polynomial.aroots_mul`：aroots_mul [IsDomain T] [CommRing S] [IsDomain S]
 [Algebra T S] [Module.IsTorsionFree T S] {p q : T[X]} (hpq : p * q != 0) : (p *
 q).aroots …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Multiset.toFinset_add`：toFinset_add (s t : Multiset α) : (s + t).toFinse
t = s.toFinset union t.toFinset
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.adjoin_union_eq_adjoin_adjoin`：adjoin_union_eq_adjoin_adjoin : a
djoin R (s union t) = (adjoin (adjoin R s) t).restrictScalars R
· 使用定理 `Polynomial.aroots_def`：aroots_def (p : T[X]) (S) [CommRing S] [IsDomain 
S] [Algebra T S] : p.aroots S = (p.map (algebraMap T S)).roots
· 使用定理 `Polynomial.Splits.roots_map`：∀ {R : Type u_1} {S : Type u_2} [inst : Fie
ld R] [inst_1 : CommRing S] [inst_2 : IsDomain S] {f : Polynomial R},   f.Splits
 → ∀ (i : R →+* S…
· 使用定理 `Multiset.toFinset_map`：Multiset.toFinset_map [DecidableEq α] [DecidableE
q β] (f : α -> β) (m : Multiset α) : (m.map f).toFinset = m.toFinset.image f
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Algebra.adjoin_algebraMap`：adjoin_algebraMap (s : Set S) : adjoin R (alg
ebraMap S A '' s) = (adjoin R s).map (IsScalarTower.toAlgHom R S A)
· 使用定理 `Polynomial.IsSplittingField.adjoin_rootSet`：adjoin_rootSet (f : K[X]) [I
sSplittingField K L f] : Algebra.adjoin K (f.rootSet L : Set L) = ⊤
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `IsScalarTower.adjoin_range_toAlgHom`：adjoin_range_toAlgHom (t : Set A) :
 (Algebra.adjoin (toAlgHom R S A).range t).restrictScalars R = (Algebra.adjoin S
 t).restrictScalars R
· 使用定理 `Subalgebra.restrictScalars_top`：restrictScalars_top : restrictScalars R 
(⊤ : Subalgebra S A) = ⊤
-/
theorem mul (f g : F[X]) (hf : f ≠ 0) (hg : g ≠ 0) [IsSplittingField F K f]
    [IsSplittingField K L (g.map <| algebraMap F K)] : IsSplittingField F L (f * g) := by
  constructor
  · rw [Polynomial.map_mul, IsScalarTower.algebraMap_eq F K L, ← map_map, ← map_map]
    exact Splits.mul ((splits K f).map _) (splits L (g.map (algebraMap F K)))
  · classical
    rw [rootSet, aroots_mul (mul_ne_zero hf hg),
      Multiset.toFinset_add, Finset.coe_union, Algebra.adjoin_union_eq_adjoin_adjoin,
      aroots_def, aroots_def, IsScalarTower.algebraMap_eq F K L, ← map_map, (splits K f).roots_map,
      Multiset.toFinset_map, Finset.coe_image, Algebra.adjoin_algebraMap, ← rootSet, adjoin_rootSet,
      Algebra.map_top, IsScalarTower.adjoin_range_toAlgHom, ← map_map, ← rootSet, adjoin_rootSet,
      Subalgebra.restrictScalars_top]

end ScalarTower

open scoped Classical in
/-- Splitting field of `f` embeds into any field that splits `f`. -/
/-
**Polynomial.IsSplittingField.lift** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.IsSplit
tingField`。
形式化陈述：lift [Algebra K F] (f : K[X]) [IsSplittingField K L f] (hf : Splits (f.map
 (algebraMap K F))) : L ->ₐ[K] F
参数：f : K[X]；hf : Splits (f.map (algebraMap K F))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Splitting field of `f` embeds into any field that splits `f`.
-/
def lift [Algebra K F] (f : K[X]) [IsSplittingField K L f]
    (hf : Splits (f.map (algebraMap K F))) : L →ₐ[K] F :=
  if hf0 : f = 0 then
    (Algebra.ofId K F).comp <|
      (Algebra.botEquiv K L : (⊥ : Subalgebra K L) →ₐ[K] K).comp <| by
        rw [← (splits_iff L f).1 (show f.Splits by simp [hf0])]
        exact Algebra.toTop
  else AlgHom.comp (by
    rw [← adjoin_rootSet L f]
    exact Classical.choice (lift_of_splits _ fun y hy =>
      have : aeval y f = 0 := (eval₂_eq_eval_map _).trans <|
        (mem_roots <| map_ne_zero hf0).1 (Multiset.mem_toFinset.mp hy)
    ⟨IsAlgebraic.isIntegral ⟨f, hf0, this⟩, hf.of_dvd (map_ne_zero hf0)
      ((map_dvd_map' _).mpr (minpoly.dvd K y this))⟩)) Algebra.toTop
/-
**Polynomial.IsSplittingField.finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial.IsSplittingField`。
形式化陈述：finiteDimensional (f : K[X]) [IsSplittingField K L f] : FiniteDimensional 
K L
参数：f : K[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `fg_adjoin_of_finite`：fg_adjoin_of_finite {s : Set A} (hfs : s.Finite) (h
is : forall x in s, IsIntegral R x) : (Algebra.adjoin R s).toSubmodule.FG
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootSet_zero`：rootSet_zero (S) [CommRing S] [IsDomain S] [Alg
ebra T S] : (0 : T[X]).rootSet S = ∅
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_rootSet'`：mem_rootSet' {p : T[X]} {S : Type*} [CommRing S
] [IsDomain S] [Algebra T S] {a : S} : a in p.rootSet S ↔ p.map (algebraMap T S)
 != 0 ∧ aeval…
· 使用定理 `Polynomial.IsSplittingField.adjoin_rootSet`：adjoin_rootSet (f : K[X]) [I
sSplittingField K L f] : Algebra.adjoin K (f.rootSet L : Set L) = ⊤
· 使用定理 `Algebra.top_toSubmodule`：top_toSubmodule : Subalgebra.toSubmodule (⊤ : S
ubalgebra R A) = ⊤
-/
theorem finiteDimensional (f : K[X]) [IsSplittingField K L f] : FiniteDimensional K L := by
  classical
  exact ⟨@Algebra.top_toSubmodule K L _ _ _ ▸
    adjoin_rootSet L f ▸ fg_adjoin_of_finite (Finset.finite_toSet _) fun y hy ↦
      if hf : f = 0 then by rw [hf, rootSet_zero] at hy; cases hy
      else IsAlgebraic.isIntegral ⟨f, hf, (mem_rootSet'.mp hy).2⟩⟩
/-
**Polynomial.IsSplittingField.IsScalarTower.isAlgebraic** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial.IsSplittingField.IsScalarTower`。
形式化陈述：∀ {F : Type u} {K : Type v} (L : Type w) [inst : Field K] [inst_1 : Field 
L] [inst_2 : Field F] [inst_3 : Algebra K L]   [inst_4 : Algebra F K] [inst_5 : 
Algebra F L] [Algebra.IsAlgebraic F K] [IsScalarTower F K L] (f : Polynomial K) 
  [Polynomial.IsSplittingField K L f], Algebra.IsAlgebraic F L
参数：L : Type w；f : Polynomial K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsSplittingField.finiteDimensional`：finiteDimensional (f : K[
X]) [IsSplittingField K L f] : FiniteDimensional K L
· 使用定理 `Algebra.IsAlgebraic.trans`：∀ (R : Type u_1) (S : Type u_2) (A : Type u_3
) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebr
a R S] [inst_4 …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem IsScalarTower.isAlgebraic [Algebra F K] [Algebra F L] [Algebra.IsAlgebraic F K]
    [IsScalarTower F K L] (f : K[X]) [IsSplittingField K L f] :
    Algebra.IsAlgebraic F L := by
  have : FiniteDimensional K L := IsSplittingField.finiteDimensional L f
  exact Algebra.IsAlgebraic.trans F K L
/-
**Polynomial.IsSplittingField.of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.
IsSplittingField`。
形式化陈述：of_algEquiv [Algebra K F] (p : K[X]) (f : F ≃ₐ[K] L) [IsSplittingField K F
 p] : IsSplittingField K L p
参数：p : K[X]；f : F ≃ₐ[K] L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.Splits.map`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R},   f.Splits → ∀ {S : Type u_2} [inst_1 : Semiring S] (i : R →+* S), (Poly
nomial.map …
· 使用定理 `Polynomial.IsSplittingField.splits`：splits (f : K[X]) [IsSplittingField 
K L f] : Splits (f.map (algebraMap K L))
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgHom.range_eq_top`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Co
mmSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring 
B] [inst_…
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `Polynomial.Splits.adjoin_rootSet_eq_range`：∀ {R : Type u_1} {A : Type u_
2} {B : Type u_3} [inst : CommRing R] [inst_1 : Field A] [inst_2 : Algebra R A] 
  [inst_3 : CommRing B] [inst_4…
· 使用定理 `Polynomial.IsSplittingField.adjoin_rootSet`：adjoin_rootSet (f : K[X]) [I
sSplittingField K L f] : Algebra.adjoin K (f.rootSet L : Set L) = ⊤
-/
theorem of_algEquiv [Algebra K F] (p : K[X]) (f : F ≃ₐ[K] L) [IsSplittingField K F p] :
    IsSplittingField K L p := by
  constructor
  · rw [← f.toAlgHom.comp_algebraMap, ← map_map]
    exact (splits F p).map _
  · rw [← (AlgHom.range_eq_top f.toAlgHom).mpr f.surjective,
      (splits F p).adjoin_rootSet_eq_range, adjoin_rootSet F p]
/-
**Polynomial.IsSplittingField.adjoin_rootSet_eq_range** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial.IsSplittingField`。
形式化陈述：adjoin_rootSet_eq_range [Algebra K F] (f : K[X]) [IsSplittingField K L f] 
(i : L ->ₐ[K] F) : Algebra.adjoin K (rootSet f F) = i.range
参数：f : K[X]；i : L ->ₐ[K] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.Splits.adjoin_rootSet_eq_range`：∀ {R : Type u_1} {A : Type u_
2} {B : Type u_3} [inst : CommRing R] [inst_1 : Field A] [inst_2 : Algebra R A] 
  [inst_3 : CommRing B] [inst_4…
· 使用定理 `Polynomial.IsSplittingField.splits`：splits (f : K[X]) [IsSplittingField 
K L f] : Splits (f.map (algebraMap K L))
· 使用定理 `Polynomial.IsSplittingField.adjoin_rootSet`：adjoin_rootSet (f : K[X]) [I
sSplittingField K L f] : Algebra.adjoin K (f.rootSet L : Set L) = ⊤
-/
theorem adjoin_rootSet_eq_range [Algebra K F] (f : K[X]) [IsSplittingField K L f] (i : L →ₐ[K] F) :
    Algebra.adjoin K (rootSet f F) = i.range :=
  ((splits L f).adjoin_rootSet_eq_range i).mpr (adjoin_rootSet L f)

end IsSplittingField

end Polynomial

open Polynomial

variable {K L} [Field K] [Field L] [Algebra K L] {p : K[X]} {F : IntermediateField K L}

/-
**IntermediateField.splits_of_splits** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IntermediateField.splits_of_splits (h : (p.map (algebraMap K L)).Splits) (
hF : forall x in p.rootSet L, x in F) : (p.map (algebraMap K F)).Splits
参数：h : (p.map (algebraMap K L)).Splits；hF : forall x in p.rootSet L, x in F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Polynomial.Splits.of_splits_map`：∀ {R : Type u_1} {S : Type u_2} [inst :
 Field R] [inst_1 : CommRing S] [inst_2 : IsDomain S] {f : Polynomial R}   (i : 
R →+* S), (Polynomial…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Polynomial.rootSet_def`：rootSet_def (p : T[X]) (S) [CommRing S] [IsDomai
n S] [Algebra T S] [DecidableEq S] : p.rootSet S = (p.aroots S).toFinset
-/
theorem IntermediateField.splits_of_splits (h : (p.map (algebraMap K L)).Splits)
    (hF : ∀ x ∈ p.rootSet L, x ∈ F) : (p.map (algebraMap K F)).Splits := by
  classical
  have := Splits.of_splits_map (f := p.map (algebraMap K F)) (algebraMap F L)
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
  exact this h (by simpa [rootSet_def] using hF)
/-
**IntermediateField.splits_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IntermediateField.splits_iff_mem (h : (p.map (algebraMap K L)).Splits) : (
p.map (algebraMap K F)).Splits ↔ forall x in p.rootSet L, x in F
参数：h : (p.map (algebraMap K L)).Splits。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Splits.image_rootSet`：∀ {R : Type u_1} {A : Type u_2} {B : Ty
pe u_3} [inst : CommRing R] [inst_1 : Field A] [inst_2 : Algebra R A]   [inst_3 
: CommRing B] [inst_4…
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IntermediateField.splits_of_splits`：IntermediateField.splits_of_splits (
h : (p.map (algebraMap K L)).Splits) (hF : forall x in p.rootSet L, x in F) : (p
.map (algebraMap K F)).S…
-/
theorem IntermediateField.splits_iff_mem (h : (p.map (algebraMap K L)).Splits) :
    (p.map (algebraMap K F)).Splits ↔ ∀ x ∈ p.rootSet L, x ∈ F := by
  refine ⟨?_, IntermediateField.splits_of_splits h⟩
  intro hF
  rw [← hF.image_rootSet F.val, Set.forall_mem_image]
  exact fun x _ ↦ x.2
/-
**IsIntegral.mem_intermediateField_of_minpoly_splits** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：IsIntegral.mem_intermediateField_of_minpoly_splits {x : L} (int : IsIntegr
al K x) {F : IntermediateField K L} (h : Splits ((minpoly K x).map (algebraMap K
 F))) : x in F
参数：int : IsIntegral K x；h : Splits ((minpoly K x).map (algebraMap K F))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.fieldRange_val`：fieldRange_val : S.val.fieldRange = S
· 使用定理 `IsIntegral.mem_range_algebraMap_of_minpoly_splits`：IsIntegral.mem_range_
algebraMap_of_minpoly_splits [Algebra K L] [IsScalarTower R K L] (int : IsIntegr
al R x) (h : Splits ((minpoly R x).map …
-/
theorem IsIntegral.mem_intermediateField_of_minpoly_splits {x : L} (int : IsIntegral K x)
    {F : IntermediateField K L} (h : Splits ((minpoly K x).map (algebraMap K F))) : x ∈ F := by
  rw [← F.fieldRange_val]; exact int.mem_range_algebraMap_of_minpoly_splits h

/-- Characterize `IsSplittingField` with `IntermediateField.adjoin` instead of `Algebra.adjoin`. -/
/-
**isSplittingField_iff_intermediateField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSplittingField_iff_intermediateField : p.IsSplittingField K L ↔ (p.map (
algebraMap K L)).Splits ∧ IntermediateField.adjoin K (p.rootSet L) = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IntermediateField.toSubalgebra_injective`：toSubalgebra_injective : Funct
ion.Injective (toSubalgebra : IntermediateField K L -> _)
· 使用定理 `IntermediateField.adjoin_toSubalgebra_of_isAlgebraic`：adjoin_toSubalgebr
a_of_isAlgebraic {S : Set E} (hS : forall x in S, IsAlgebraic F x) : (adjoin F S
).toSubalgebra = Algebra.adjoin F S
· 使用定理 `isAlgebraic_of_mem_rootSet`：isAlgebraic_of_mem_rootSet {R : Type u} {A :
 Type v} [CommRing R] [Field A] [Algebra R A] {p : R[X]} {x : A} (hx : x in p.ro
otSet A) : IsAlg…

--- 原说明 ---
Characterize `IsSplittingField` with `IntermediateField.adjoin` instead of `Alge
bra.adjoin`.
-/
theorem isSplittingField_iff_intermediateField : p.IsSplittingField K L ↔
    (p.map (algebraMap K L)).Splits ∧ IntermediateField.adjoin K (p.rootSet L) = ⊤ := by
  rw [← IntermediateField.toSubalgebra_injective.eq_iff,
      IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun _ ↦ isAlgebraic_of_mem_rootSet]
  exact ⟨fun ⟨spl, adj⟩ ↦ ⟨spl, adj⟩, fun ⟨spl, adj⟩ ↦ ⟨spl, adj⟩⟩

-- Note: p.Splits (algebraMap F E) also works
/-
**IntermediateField.isSplittingField_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IntermediateField.isSplittingField_iff : p.IsSplittingField K F ↔ (p.map (
algebraMap K F)).Splits ∧ F = adjoin K (p.rootSet L)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IntermediateField.toSubalgebra_injective`：toSubalgebra_injective : Funct
ion.Injective (toSubalgebra : IntermediateField K L -> _)
· 使用定理 `IntermediateField.adjoin_toSubalgebra_of_isAlgebraic`：adjoin_toSubalgebr
a_of_isAlgebraic {S : Set E} (hS : forall x in S, IsAlgebraic F x) : (adjoin F S
).toSubalgebra = Algebra.adjoin F S
· 使用定理 `isAlgebraic_of_mem_rootSet`：isAlgebraic_of_mem_rootSet {R : Type u} {A :
 Type v} [CommRing R] [Field A] [Algebra R A] {p : R[X]} {x : A} (hx : x in p.ro
otSet A) : IsAlg…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Polynomial.Splits.adjoin_rootSet_eq_range`：∀ {R : Type u_1} {A : Type u_
2} {B : Type u_3} [inst : CommRing R] [inst_1 : Field A] [inst_2 : Algebra R A] 
  [inst_3 : CommRing B] [inst_4…
· 使用定理 `IntermediateField.range_val`：range_val : S.val.range = S.toSubalgebra
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Polynomial.IsSplittingField.splits'`：∀ {K : Type v} {L : Type w} {inst :
 Field K} {inst_1 : Field L} {inst_2 : Algebra K L} {f : Polynomial K}   [self :
 Polynomial.IsSplittingFi…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.IsSplittingField.adjoin_rootSet'`：∀ {K : Type v} {L : Type w}
 {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L} {f : Polynomial K}  
 [self : Polynomial.IsSplittingFi…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IntermediateField.isSplittingField_iff :
    p.IsSplittingField K F ↔ (p.map (algebraMap K F)).Splits ∧ F = adjoin K (p.rootSet L) := by
  suffices _ → (Algebra.adjoin K (p.rootSet F) = ⊤ ↔ F = adjoin K (p.rootSet L)) by
    exact ⟨fun h ↦ ⟨h.1, (this h.1).mp h.2⟩, fun h ↦ ⟨h.1, (this h.1).mpr h.2⟩⟩
  rw [← toSubalgebra_injective.eq_iff,
      adjoin_toSubalgebra_of_isAlgebraic fun x ↦ isAlgebraic_of_mem_rootSet]
  refine fun hp ↦ (hp.adjoin_rootSet_eq_range F.val).symm.trans ?_
  rw [← F.range_val, eq_comm]
/-
**IntermediateField.adjoin_rootSet_isSplittingField** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：IntermediateField.adjoin_rootSet_isSplittingField (hp : (p.map (algebraMap
 K L)).Splits) : p.IsSplittingField K (adjoin K (p.rootSet L))
参数：hp : (p.map (algebraMap K L)).Splits。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IntermediateField.isSplittingField_iff`：IntermediateField.isSplittingFie
ld_iff : p.IsSplittingField K F ↔ (p.map (algebraMap K F)).Splits ∧ F = adjoin K
 (p.rootSet L)
· 使用定理 `IntermediateField.splits_of_splits`：IntermediateField.splits_of_splits (
h : (p.map (algebraMap K L)).Splits) (hF : forall x in p.rootSet L, x in F) : (p
.map (algebraMap K F)).S…
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
-/
theorem IntermediateField.adjoin_rootSet_isSplittingField (hp : (p.map (algebraMap K L)).Splits) :
    p.IsSplittingField K (adjoin K (p.rootSet L)) :=
  isSplittingField_iff.mpr ⟨splits_of_splits hp fun _ hx ↦ subset_adjoin K (p.rootSet L) hx, rfl⟩
/-
**Polynomial.isSplittingField_C** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.isSplittingField_C (a : K) : Polynomial.IsSplittingField K K (C
 a) where splits'
参数：a : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.rootSet_C`：rootSet_C [CommRing S] [IsDomain S] [Algebra T S] 
(a : T) : (C a).rootSet S = ∅
· 使用定理 `Algebra.adjoin_empty`：adjoin_empty : adjoin R (∅ : Set A) = ⊥
· 使用定理 `Subalgebra.bot_eq_top_of_finrank_eq_one`：∀ {F : Type u_1} {E : Type u_2}
 [inst : CommRing F] [StrongRankCondition F] [inst_2 : Ring E] [inst_3 : Algebra
 F E]   [Nontrivial E] [Modul…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Polynomial.isSplittingField_C (a : K) : Polynomial.IsSplittingField K K (C a) where
  splits' := by simp
  adjoin_rootSet' := by simp
