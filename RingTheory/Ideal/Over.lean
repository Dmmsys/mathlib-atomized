/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yongle Hu
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Ideals over/under ideals

This file concerns ideals lying over other ideals.
Let `f : R →+* S` be a ring homomorphism (typically a ring extension), `I` an ideal of `R` and
`J` an ideal of `S`. We say `J` lies over `I` (and `I` under `J`) if `I` is the `f`-preimage of `J`.
This is expressed here by writing `I = J.comap f`.
-/

@[expose] public section

-- for going-up results about integral extensions, see `Mathlib/RingTheory/Ideal/GoingUp.lean`
assert_not_exists Algebra.IsIntegral

-- for results about finiteness, see `Mathlib/RingTheory/Finiteness/Quotient.lean`
assert_not_exists Module.Finite

variable {R : Type*} [CommRing R]

namespace Ideal

open Submodule

open scoped Pointwise

section CommRing

variable {S : Type*} [CommRing S] {f : R →+* S} {I J : Ideal S}

variable {p : Ideal R} {P : Ideal S}

/-- If there is an injective map `R/p → S/P` such that the following diagram commutes:
```
R   → S
↓     ↓
R/p → S/P
```
then `P` lies over `p`.
-/
/-
**Ideal.comap_eq_of_scalar_tower_quotient** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_eq_of_scalar_tower_quotient [Algebra R S] [Algebra (R ⧸ p) (S ⧸ P)] 
[IsScalarTower R (R ⧸ p) (S ⧸ P)] (h : Function.Injective (algebraMap (R ⧸ p) (S
 ⧸ P))) : comap (algebraMap R S) P = p
参数：R ⧸ p；S ⧸ P；R ⧸ p；S ⧸ P；h : Function.Injective (algebraMap (R ⧸ p) (S ⧸ P))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Ideal.Quotient.mk_algebraMap`：∀ (R₁ : Type u_1) {A : Type u_3} [inst : C
ommSemiring R₁] [inst_1 : Ring A] [inst_2 : Algebra R₁ A] (I : Ideal A)   [inst_
3 : I.IsTwoSided] …
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `Ideal.Quotient.algebraMap_eq`：∀ {R : Type u_5} [inst : CommRing R] (I : 
Ideal R), algebraMap R (R ⧸ I) = Ideal.Quotient.mk I
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
If there is an injective map `R/p → S/P` such that the following diagram commute
s:
```
R   → S
↓     ↓
R/p → S/P
```
then `P` lies over `p`.
-/
theorem comap_eq_of_scalar_tower_quotient [Algebra R S] [Algebra (R ⧸ p) (S ⧸ P)]
    [IsScalarTower R (R ⧸ p) (S ⧸ P)] (h : Function.Injective (algebraMap (R ⧸ p) (S ⧸ P))) :
    comap (algebraMap R S) P = p := by
  ext x
  rw [mem_comap, ← Quotient.eq_zero_iff_mem, ← Quotient.eq_zero_iff_mem, Quotient.mk_algebraMap,
    IsScalarTower.algebraMap_apply R (R ⧸ p) (S ⧸ P), Quotient.algebraMap_eq]
  exact map_eq_zero_iff _ h

variable [Algebra R S]

/-- `R / p` has a canonical map to `S / pS`. -/
/-
**Ideal.Quotient.algebraQuotientMapQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quo
tient`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     {S : Type u_2} →       [inst_
1 : CommRing S] →         {p : Ideal R} → [inst_2 : Algebra R S] → Algebra (R ⧸ 
p) (S ⧸ Ideal.map (algebraMap R S) p)
参数：R ⧸ p；S ⧸ Ideal.map (algebraMap R S) p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`R / p` has a canonical map to `S / pS`.
-/
instance Quotient.algebraQuotientMapQuotient : Algebra (R ⧸ p) (S ⧸ map (algebraMap R S) p) :=
  Ideal.Quotient.algebraQuotientOfLEComap le_comap_map

@[simp]
/-
**Ideal.Quotient.algebraMap_quotient_map_quotient** 是 Mathlib 中的一个定理，位于命名空间 `Ide
al.Quotient`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] 
{p : Ideal R} [inst_2 : Algebra R S] (x : R),   (algebraMap (R ⧸ p) (S ⧸ Ideal.m
ap (algebraMap R S) p)) ((Ideal.Quotient.mk p) x) =     (Ideal.Quotient.mk (Idea
l.map (algebraMap R S) p)) ((algebraMap R S) x)
参数：x : R；algebraMap (R ⧸ p) (S ⧸ Ideal.map (algebraMap R S) p)；(Ideal.Quotient.m
k p) x；Ideal.Quotient.mk (Ideal.map (algebraMap R S) p)；(algebraMap R S) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem Quotient.algebraMap_quotient_map_quotient (x : R) :
    letI f := algebraMap R S
    algebraMap (R ⧸ p) (S ⧸ map f p) (Ideal.Quotient.mk p x) =
    Ideal.Quotient.mk (map f p) (f x) :=
  rfl

@[simp]
/-
**Ideal.Quotient.mk_smul_mk_quotient_map_quotient** 是 Mathlib 中的一个定理，位于命名空间 `Ide
al.Quotient`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] 
{p : Ideal R} [inst_2 : Algebra R S] (x : R)   (y : S),   (Ideal.Quotient.mk p) 
x • (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p)) y =     (Ideal.Quotient.m
k (Ideal.map (algebraMap R S) p)) ((algebraMap R S) x * y)
参数：x : R；y : S；Ideal.Quotient.mk p；Ideal.Quotient.mk (Ideal.map (algebraMap R S)
 p)；Ideal.Quotient.mk (Ideal.map (algebraMap R S) p)；(algebraMap R S) x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem Quotient.mk_smul_mk_quotient_map_quotient (x : R) (y : S) :
    letI f := algebraMap R S
    Quotient.mk p x • Quotient.mk (map f p) y = Quotient.mk (map f p) (f x * y) :=
  Algebra.smul_def _ _
/-
**Ideal.Quotient.tower_quotient_map_quotient** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Qu
otient`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] 
{p : Ideal R} [inst_2 : Algebra R S],   IsScalarTower R (R ⧸ p) (S ⧸ Ideal.map (
algebraMap R S) p)
参数：R ⧸ p；S ⧸ Ideal.map (algebraMap R S) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.Quotient.algebraMap_eq`：∀ {R : Type u_5} [inst : CommRing R] (I : 
Ideal R), algebraMap R (R ⧸ I) = Ideal.Quotient.mk I
· 使用定理 `Ideal.Quotient.algebraMap_quotient_map_quotient`：∀ {R : Type u_1} [inst 
: CommRing R] {S : Type u_2} [inst_1 : CommRing S] {p : Ideal R} [inst_2 : Algeb
ra R S] (x : R),   (algebraMap (R ⧸ p…
· 使用定理 `Ideal.Quotient.mk_algebraMap`：∀ (R₁ : Type u_1) {A : Type u_3} [inst : C
ommSemiring R₁] [inst_1 : Ring A] [inst_2 : Algebra R₁ A] (I : Ideal A)   [inst_
3 : I.IsTwoSided] …
-/
instance Quotient.tower_quotient_map_quotient :
    IsScalarTower R (R ⧸ p) (S ⧸ map (algebraMap R S) p) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [Quotient.algebraMap_eq, Quotient.algebraMap_quotient_map_quotient,
      Quotient.mk_algebraMap]

end CommRing

section ideal_liesOver

section Semiring

variable (A : Type*) [CommSemiring A] {B C : Type*} [Semiring B] [Semiring C] [Algebra A B]
  [Algebra A C] (P : Ideal B) {Q : Ideal C} (p : Ideal A)
  {G : Type*} [Group G] [MulSemiringAction G B] (g : G)

/-- The ideal obtained by pulling back the ideal `P` from `B` to `A`. -/
/-
**Ideal.under** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ideal`。
形式化陈述：under : Ideal A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ideal obtained by pulling back the ideal `P` from `B` to `A`.
-/
abbrev under : Ideal A := Ideal.comap (algebraMap A B) P
/-
**Ideal.under_def** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：under_def : P.under A = Ideal.comap (algebraMap A B) P
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem under_def : P.under A = Ideal.comap (algebraMap A B) P := rfl
/-
**Ideal.mem_under** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_under {x : A} : x in P.under A ↔ algebraMap A B x in P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
-/
theorem mem_under {x : A} : x ∈ P.under A ↔ algebraMap A B x ∈ P := mem_comap
/-
**Ideal.IsPrime.under** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrime`。
形式化陈述：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type u_3} [inst_1 : Semiring
 B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrime], (Ideal.under A P).I
sPrime
参数：A : Type u_2；P : Ideal B；Ideal.under A P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
-/
instance IsPrime.under [hP : P.IsPrime] : (P.under A).IsPrime :=
  hP.comap (algebraMap A B)

@[simp]
/-
**Ideal.under_smul** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：under_smul [SMulCommClass G A B] : (g • P : Ideal B).under A = P.under A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Ideal.mem_pointwise_smul_iff_inv_smul_mem`：mem_pointwise_smul_iff_inv_sm
ul_mem {a : M} {S : Ideal R} {x : R} : x in a • S ↔ a⁻¹ • x in S
· 使用定理 `smul_algebraMap`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Algebra R A] {α : Type u_2}   [inst_3 : Monoid α] [
inst_…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma under_smul [SMulCommClass G A B] : (g • P : Ideal B).under A = P.under A := by
  ext a
  rw [mem_comap, mem_comap, mem_pointwise_smul_iff_inv_smul_mem, smul_algebraMap]

@[simp]
/-
**Ideal.smul_under** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：smul_under [MulSemiringAction G A] [SMulDistribClass G A B] : g • P.under 
A = (g • P).under A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.pointwise_smul_eq_comap`：pointwise_smul_eq_comap {a : M} (S : Idea
l R) : a • S = S.comap (MulSemiringAction.toRingAut _ _ a).symm
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.comap_coe`：comap_coe [RingHomClass F R S] (I : Ideal S) : I.comap 
(f : R ->+* S) = I.comap f
· 使用定理 `Ideal.under_def`：under_def : P.under A = Ideal.comap (algebraMap A B) P
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomClass.toRingHom.congr_simp`：∀ {F : Type u_1} {α : Type u_2} {β : 
Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSemir
ing β} [inst_1 : RingHo…
· 使用定理 `MulSemiringAction.toRingAut_apply`：∀ (G : Type u_1) (R : Type u_2) [inst
 : Group G] [inst_1 : Semiring R] [inst_2 : MulSemiringAction G R] (a : G),   (M
ulSemiringAction.toRing…
· 使用定理 `MulSemiringAction.toRingEquiv_apply_symm_apply`：∀ (G : Type u_1) [inst :
 Group G] (R : Type u_2) [inst_1 : Semiring R] [inst_2 : MulSemiringAction G R] 
(x : G) (a : R),   ((MulSemiringActi…
· 使用定理 `algebraMap.smul'`：algebraMap.smul' [Monoid A] [MulDistribMulAction A C] 
[SMulDistribClass A B C] : algebraMap B C (a • b) = a • (algebraMap B C b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_under [MulSemiringAction G A] [SMulDistribClass G A B] :
    g • P.under A = (g • P).under A := by
  conv_lhs => rw [pointwise_smul_eq_comap, ← comap_coe, under_def, comap_comap]
  conv_rhs => rw [pointwise_smul_eq_comap, ← comap_coe, under_def, comap_comap]
  congr
  ext
  simp [algebraMap.smul']

variable (B) in
/-
**Ideal.under_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：under_top : under A (⊤ : Ideal B) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_top`：comap_top : (⊤ : Ideal S).comap f = ⊤
-/
theorem under_top : under A (⊤ : Ideal B) = ⊤ := comap_top

variable {A}

/-- `P` lies over `p` if `p` is the preimage of `P` by the `algebraMap`. -/
/-
**Ideal.LiesOver** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ideal`。
形式化陈述：{A : Type u_2} →   [inst : CommSemiring A] → {B : Type u_3} → [inst_1 : Se
miring B] → [Algebra A B] → Ideal B → Ideal A → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P` lies over `p` if `p` is the preimage of `P` by the `algebraMap`.
-/
@[mk_iff] class LiesOver : Prop where
  over : p = P.under A
/-
**Ideal.over_under** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
形式化陈述：over_under : P.LiesOver (P.under A) where over
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance over_under : P.LiesOver (P.under A) where over := rfl
/-
**Ideal.over_def** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：over_def [P.LiesOver p] : p = P.under A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
-/
theorem over_def [P.LiesOver p] : p = P.under A := LiesOver.over
/-
**Ideal.mem_of_liesOver** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_of_liesOver [P.LiesOver p] (x : A) : x in p ↔ algebraMap A B x in P
参数：x : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_of_liesOver [P.LiesOver p] (x : A) : x ∈ p ↔ algebraMap A B x ∈ P := by
  rw [P.over_def p]
  rfl

variable (A B) in
/-
**Ideal.top_liesOver_top** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
形式化陈述：top_liesOver_top : (⊤ : Ideal B).LiesOver (⊤ : Ideal A) where over
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.under_top`：under_top : under A (⊤ : Ideal B) = ⊤
-/
instance top_liesOver_top : (⊤ : Ideal B).LiesOver (⊤ : Ideal A) where
  over := (under_top A B).symm
/-
**Ideal.eq_top_iff_of_liesOver** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_top_iff_of_liesOver [P.LiesOver p] : P = ⊤ ↔ p = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Ideal.comap_eq_top_iff`：comap_eq_top_iff {I : Ideal S} : I.comap f = ⊤ ↔
 I = ⊤
-/
theorem eq_top_iff_of_liesOver [P.LiesOver p] : P = ⊤ ↔ p = ⊤ := by
  rw [P.over_def p]
  exact comap_eq_top_iff.symm
/-
**Ideal.ne_top_iff_of_liesOver** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：ne_top_iff_of_liesOver [P.LiesOver p] : P != ⊤ ↔ p != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `Ideal.eq_top_iff_of_liesOver`：eq_top_iff_of_liesOver [P.LiesOver p] : P 
= ⊤ ↔ p = ⊤
-/
lemma ne_top_iff_of_liesOver [P.LiesOver p] : P ≠ ⊤ ↔ p ≠ ⊤ := (eq_top_iff_of_liesOver ..).ne
/-
**Ideal.isPrime_of_liesOver** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：isPrime_of_liesOver [P.LiesOver p] [P.IsPrime] : p.IsPrime
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
-/
lemma isPrime_of_liesOver [P.LiesOver p] [P.IsPrime] : p.IsPrime := by
  rw [over_def P p]
  exact IsPrime.under A P

variable {P}
/-
**Ideal.LiesOver.of_eq_comap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.LiesOver`。
形式化陈述：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u_3} {C : Type u_4} [in
st_1 : Semiring B] [inst_2 : Semiring C]   [inst_3 : Algebra A B] [inst_4 : Alge
bra A C] {P : Ideal B} {Q : Ideal C} (p : Ideal A) [Q.LiesOver p] {F : Type u_6}
   [inst_6 : FunLike F B C] [inst_7 : AlgHomClass F A B C] (f : F), P = Ideal.co
map f Q → P.LiesOver p
参数：p : Ideal A；f : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
-/
theorem LiesOver.of_eq_comap [Q.LiesOver p] {F : Type*} [FunLike F B C]
    [AlgHomClass F A B C] (f : F) (h : P = Q.comap f) : P.LiesOver p where
  over := by
    rw [h]
    exact (over_def Q p).trans <|
      congrFun (congrFun (congrArg
        comap ((AlgHomClass.toAlgHom f : B →ₐ[A] C).comp_algebraMap.symm)) _) Q
/-
**Ideal.LiesOver.of_eq_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.LiesOver`。
形式化陈述：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u_3} {C : Type u_4} [in
st_1 : Semiring B] [inst_2 : Semiring C]   [inst_3 : Algebra A B] [inst_4 : Alge
bra A C] {P : Ideal B} {Q : Ideal C} (p : Ideal A) [P.LiesOver p] {E : Type u_6}
   [inst_6 : EquivLike E B C] [AlgEquivClass E A B C] (σ : E), Q = Ideal.map σ P
 → Q.LiesOver p
参数：p : Ideal A；σ : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.LiesOver.of_eq_comap`：∀ {A : Type u_2} [inst : CommSemiring A] {B 
: Type u_3} {C : Type u_4} [inst_1 : Semiring B] [inst_2 : Semiring C]   [inst_3
 : Algebra A B] …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_symm`：comap_symm {I : Ideal R} (f : R ≃+* S) : I.comap f.sym
m = I.map f
-/
theorem LiesOver.of_eq_map_equiv [P.LiesOver p] {E : Type*} [EquivLike E B C]
    [AlgEquivClass E A B C] (σ : E) (h : Q = P.map σ) : Q.LiesOver p := by
  rw [← show _ = P.map σ from comap_symm (RingEquivClass.toRingEquiv σ)] at h
  exact of_eq_comap p (AlgEquivClass.toAlgEquiv σ : B ≃ₐ[A] C).symm h

variable {p} in
/-
**Ideal.LiesOver.smul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.LiesOver`。
形式化陈述：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u_3} [inst_1 : Semiring
 B] [inst_2 : Algebra A B] {P : Ideal B}   {p : Ideal A} {G : Type u_5} [inst_3 
: Group G] [inst_4 : MulSemiringAction G B] (g : G) [SMulCommClass G A B]   [h :
 P.LiesOver p], (g • P).LiesOver p
参数：g : G；g • P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.under_smul`：under_smul [SMulCommClass G A B] : (g • P : Ideal B).u
nder A = P.under A
-/
instance LiesOver.smul [SMulCommClass G A B] [h : P.LiesOver p] : (g • P).LiesOver p :=
  ⟨h.over.trans (under_smul A P g).symm⟩

variable (P) (Q)
/-
**Ideal.comap_liesOver** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
形式化陈述：comap_liesOver [Q.LiesOver p] {F : Type*} [FunLike F B C] [AlgHomClass F A
 B C] (f : F) : (Q.comap f).LiesOver p
参数：f : F。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.LiesOver.of_eq_comap`：∀ {A : Type u_2} [inst : CommSemiring A] {B 
: Type u_3} {C : Type u_4} [inst_1 : Semiring B] [inst_2 : Semiring C]   [inst_3
 : Algebra A B] …
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
instance comap_liesOver [Q.LiesOver p] {F : Type*} [FunLike F B C] [AlgHomClass F A B C]
    (f : F) : (Q.comap f).LiesOver p :=
  LiesOver.of_eq_comap p f rfl
/-
**Ideal.map_equiv_liesOver** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
形式化陈述：map_equiv_liesOver [P.LiesOver p] {E : Type*} [EquivLike E B C] [AlgEquivC
lass E A B C] (σ : E) : (P.map σ).LiesOver p
参数：σ : E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.LiesOver.of_eq_map_equiv`：∀ {A : Type u_2} [inst : CommSemiring A]
 {B : Type u_3} {C : Type u_4} [inst_1 : Semiring B] [inst_2 : Semiring C]   [in
st_3 : Algebra A B] …
-/
instance map_equiv_liesOver [P.LiesOver p] {E : Type*} [EquivLike E B C] [AlgEquivClass E A B C]
    (σ : E) : (P.map σ).LiesOver p :=
  LiesOver.of_eq_map_equiv p σ rfl

end Semiring

section CommSemiring

variable {A : Type*} [CommSemiring A] {B : Type*} [CommSemiring B] {C : Type*} [Semiring C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  (𝔓 : Ideal C) (P : Ideal B) (p : Ideal A)

@[simp]
/-
**Ideal.under_under** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：under_under : (𝔓.under B).under A = 𝔓.under A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem under_under : (𝔓.under B).under A = 𝔓.under A := by
  simp_rw [comap_comap, ← IsScalarTower.algebraMap_eq]
/-
**Ideal.LiesOver.trans** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.LiesOver`。
形式化陈述：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u_3} [inst_1 : CommSemi
ring B] {C : Type u_4} [inst_2 : Semiring C]   [inst_3 : Algebra A B] [inst_4 : 
Algebra B C] [inst_5 : Algebra A C] [IsScalarTower A B C] (𝔓 : Ideal C) (P : Ide
al B)   (p : Ideal A) [𝔓.LiesOver P] [P.LiesOver p], 𝔓.LiesOver p
参数：𝔓 : Ideal C；P : Ideal B；p : Ideal A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Ideal.under_under`：under_under : (𝔓.under B).under A = 𝔓.under A
-/
theorem LiesOver.trans [𝔓.LiesOver P] [P.LiesOver p] : 𝔓.LiesOver p where
  over := by rw [P.over_def p, 𝔓.over_def P, under_under]
/-
**Ideal.LiesOver.tower_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.LiesOver`。
形式化陈述：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u_3} [inst_1 : CommSemi
ring B] {C : Type u_4} [inst_2 : Semiring C]   [inst_3 : Algebra A B] [inst_4 : 
Algebra B C] [inst_5 : Algebra A C] [IsScalarTower A B C] (𝔓 : Ideal C) (P : Ide
al B)   (p : Ideal A) [hp : 𝔓.LiesOver p] [hP : 𝔓.LiesOver P], P.LiesOver p
参数：𝔓 : Ideal C；P : Ideal B；p : Ideal A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Ideal.under_under`：under_under : (𝔓.under B).under A = 𝔓.under A
-/
theorem LiesOver.tower_bot [hp : 𝔓.LiesOver p] [hP : 𝔓.LiesOver P] : P.LiesOver p where
  over := by rw [𝔓.over_def p, 𝔓.over_def P, under_under]
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [𝔓.LiesOver P] : 𝔓.LiesOver (P.under A) :=
  .trans 𝔓 P (P.under A)
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [𝔓.LiesOver P] : P.LiesOver (𝔓.under A) :=
  .tower_bot 𝔓 P (𝔓.under A)

/--
Consider the following commutative diagram of ring maps
```
A → B
↓   ↓
C → D
```
and let `P` be an ideal of `B`. The image in `C` of the ideal of `A` under `P` is included
in the ideal of `C` under the image of `P` in `D`.
-/
/-
**Ideal.map_under_le_under_map** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_under_le_under_map {C D : Type*} [CommSemiring C] [Semiring D] [Algebr
a A C] [Algebra C D] [Algebra A D] [Algebra B D] [IsScalarTower A C D] [IsScalar
Tower A B D] : map (algebraMap A C) (under A P) <= under C (map (algebraMap B D)
 P)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.le_comap_of_map_le`：le_comap_of_map_le : I.map f <= K -> I <= K.co
map f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f

--- 原说明 ---
Consider the following commutative diagram of ring maps
```
A → B
↓   ↓
C → D
```
and let `P` be an ideal of `B`. The image in `C` of the ideal of `A` under `P` i
s included
in the ideal of `C` under the image of `P` in `D`.
-/
theorem map_under_le_under_map {C D : Type*} [CommSemiring C] [Semiring D] [Algebra A C]
    [Algebra C D] [Algebra A D] [Algebra B D] [IsScalarTower A C D] [IsScalarTower A B D] :
    map (algebraMap A C) (under A P) ≤ under C (map (algebraMap B D) P) := by
  apply le_comap_of_map_le
  rw [map_map, ← IsScalarTower.algebraMap_eq, map_le_iff_le_comap,
    IsScalarTower.algebraMap_eq A B D, ← comap_comap]
  exact comap_mono <| le_comap_map

/--
Consider the following commutative diagram of ring maps
```
A → B
↓   ↓
C → D
```
and let `P` be an ideal of `B`. Assume that the image in `C` of the ideal of `A` under `P`
is maximal and that the image of `P` in `D` is not equal to `D`, then the image in `C` of the
ideal of `A` under `P` is equal to the ideal of `C` under the image of `P` in `D`.
-/
/-
**Ideal.under_map_eq_map_under** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：under_map_eq_map_under {C D : Type*} [CommSemiring C] [Semiring D] [Algebr
a A C] [Algebra C D] [Algebra A D] [Algebra B D] [IsScalarTower A C D] [IsScalar
Tower A B D] (h₁ : (map (algebraMap A C) (under A P)).IsMaximal) (h₂ : map (alge
braMap B D) P != ⊤) : under C (map (algebraMap B D) P) = map (algebraMap A C) (u
nder A P)
参数：h₁ : (map (algebraMap A C) (under A P)).IsMaximal；h₂ : map (algebraMap B D) P
 != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsCoatom.le_iff_eq`：IsCoatom.le_iff_eq (ha : IsCoatom a) (hb : b != ⊤) :
 a <= b ↔ b = a
· 使用定理 `Ideal.isMaximal_def`：isMaximal_def {I : Ideal α} : I.IsMaximal ↔ IsCoato
m I
· 使用定理 `Ideal.comap_ne_top`：comap_ne_top [RingHomClass F R S] (hK : K != ⊤) : co
map f K != ⊤
· 使用定理 `Ideal.map_under_le_under_map`：map_under_le_under_map {C D : Type*} [Comm
Semiring C] [Semiring D] [Algebra A C] [Algebra C D] [Algebra A D] [Algebra B D]
 [IsScalarTower A …

--- 原说明 ---
Consider the following commutative diagram of ring maps
```
A → B
↓   ↓
C → D
```
and let `P` be an ideal of `B`. Assume that the image in `C` of the ideal of `A`
 under `P`
is maximal and that the image of `P` in `D` is not equal to `D`, then the image 
in `C` of the
ideal of `A` under `P` is equal to the ideal of `C` under the image of `P` in `D
`.
-/
theorem under_map_eq_map_under {C D : Type*} [CommSemiring C] [Semiring D] [Algebra A C]
    [Algebra C D] [Algebra A D] [Algebra B D] [IsScalarTower A C D] [IsScalarTower A B D]
    (h₁ : (map (algebraMap A C) (under A P)).IsMaximal) (h₂ : map (algebraMap B D) P ≠ ⊤) :
    under C (map (algebraMap B D) P) = map (algebraMap A C) (under A P) :=
  (IsCoatom.le_iff_eq (isMaximal_def.mp h₁) (comap_ne_top (algebraMap C D) h₂)).mp <|
    map_under_le_under_map P
/-
**Ideal.disjoint_primeCompl_of_liesOver** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：disjoint_primeCompl_of_liesOver [p.IsPrime] [hPp : 𝔓.LiesOver p] : Disjoin
t ((Algebra.algebraMapSubmonoid C p.primeCompl) : Set C) (𝔓 : Set C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.coe_comap`：coe_comap [RingHomClass F R S] (I : Ideal S) : (comap f
 I : Set R) = f ⁻¹' I
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Ideal.under_def`：under_def : P.under A = Ideal.comap (algebraMap A B) P
· 使用定理 `Ideal.liesOver_iff`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u
_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   (p : Ideal A), 
P.LiesOv…
· 使用定理 `Ideal.one_notMem`：one_notMem (I : Ideal α) [hI : I.IsPrime] : 1 ∉ I
· 使用定理 `Subsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Mul M] (carrier car
rier_1 : Set M) (e_carrier : carrier = carrier_1)   (mul_mem' : ∀ {a b : M}, a ∈
 carrier → b ∈ c…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submonoid.map.congr_simp`：∀ {M : Type u_1} {N : Type u_2} [inst : MulOne
Class M] [inst_1 : MulOneClass N] {F : Type u_4} [inst_2 : FunLike F M N]   [mc 
: MonoidHomCla…
· 使用定理 `Submonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : MulOneClass M] (toSubs
emigroup toSubsemigroup_1 : Subsemigroup M)   (e_toSubsemigroup : toSubsemigroup
 = toSubsemig…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem disjoint_primeCompl_of_liesOver [p.IsPrime] [hPp : 𝔓.LiesOver p] :
  Disjoint ((Algebra.algebraMapSubmonoid C p.primeCompl) : Set C) (𝔓 : Set C) := by
  rw [liesOver_iff, under_def, SetLike.ext'_iff, coe_comap] at hPp
  simpa only [Algebra.algebraMapSubmonoid, primeCompl, hPp, ← le_compl_iff_disjoint_left]
    using! Set.subset_compl_comm.mp (by simp)
/-
**Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective** 是 Mathlib 中的一个定理
，位于命名空间 `Ideal`。
形式化陈述：algebraMapSubmonoid_primeCompl_of_liesOver_surjective [p.IsPrime] [P.IsPri
me] [P.LiesOver p] (hf : Function.Surjective (algebraMap A B)) : Algebra.algebra
MapSubmonoid B p.primeCompl = P.primeCompl
参数：hf : Function.Surjective (algebraMap A B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.primeCompl.congr_simp`：∀ {α : Type u} [inst : Semiring α] (P P_1 :
 Ideal α) (e_P : P = P_1) [hp : P.IsPrime], P.primeCompl = P_1.primeCompl
· 使用引理 `Ideal.map_primeCompl_comap_of_surjective`：map_primeCompl_comap_of_surjec
tive (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] : Submonoid.map f (p
.comap f).primeCompl = p.prime…
-/
theorem algebraMapSubmonoid_primeCompl_of_liesOver_surjective
    [p.IsPrime] [P.IsPrime] [P.LiesOver p] (hf : Function.Surjective (algebraMap A B)) :
    Algebra.algebraMapSubmonoid B p.primeCompl = P.primeCompl := by
  simpa [over_def P p] using! P.map_primeCompl_comap_of_surjective (algebraMap A B) hf

variable (B)
/-
**Ideal.under_liesOver_of_liesOver** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
形式化陈述：under_liesOver_of_liesOver [𝔓.LiesOver p] : (𝔓.under B).LiesOver p
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.LiesOver.tower_bot`：∀ {A : Type u_2} [inst : CommSemiring A] {B : 
Type u_3} [inst_1 : CommSemiring B] {C : Type u_4} [inst_2 : Semiring C]   [inst
_3 : Algebra A…
-/
instance under_liesOver_of_liesOver [𝔓.LiesOver p] : (𝔓.under B).LiesOver p :=
  LiesOver.tower_bot 𝔓 (𝔓.under B) p

end CommSemiring

section CommRing

variable (A B : Type*) [CommSemiring A] [Semiring B]
  [Algebra A B] [FaithfulSMul A B] {p : Ideal A}

@[simp]
/-
**Ideal.under_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：under_bot : under A (⊥ : Ideal B) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_bot_of_injective`：comap_bot_of_injective (hf : Function.Inje
ctive f) : Ideal.comap f ⊥ = ⊥
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem under_bot : under A (⊥ : Ideal B) = ⊥ :=
  comap_bot_of_injective (algebraMap A B) (FaithfulSMul.algebraMap_injective A B)
/-
**Ideal.bot_liesOver_bot** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
形式化陈述：bot_liesOver_bot : (⊥ : Ideal B).LiesOver (⊥ : Ideal A) where over
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.under_bot`：under_bot : under A (⊥ : Ideal B) = ⊥
-/
instance bot_liesOver_bot : (⊥ : Ideal B).LiesOver (⊥ : Ideal A) where
  over := (under_bot A B).symm

variable {A B} in
/-
**Ideal.ne_bot_of_liesOver_of_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ne_bot_of_liesOver_of_ne_bot (hp : p != ⊥) (P : Ideal B) [P.LiesOver p] : 
P != ⊥
参数：hp : p != ⊥；P : Ideal B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Ideal.under_bot`：under_bot : under A (⊥ : Ideal B) = ⊥
-/
theorem ne_bot_of_liesOver_of_ne_bot (hp : p ≠ ⊥) (P : Ideal B) [P.LiesOver p] : P ≠ ⊥ := by
  contrapose hp
  rw [over_def P p, hp, under_bot]

end CommRing

/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {K A : Type*} [Field K] [Semiring A] [Algebra K A] (P : Ideal A) [P.IsPrime] :
    P.LiesOver (⊥ : Ideal K) :=
  ⟨((IsSimpleOrder.eq_bot_or_eq_top _).resolve_right Ideal.IsPrime.ne_top').symm⟩
namespace Quotient

variable (R : Type*) [CommSemiring R] {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Algebra R A] [Algebra R B] [IsScalarTower R A B]
  (P : Ideal B) {Q : Ideal C} (p : Ideal A) [Q.LiesOver p] [P.LiesOver p]
  (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- If `P` lies over `p`, then canonically `B ⧸ P` is a `A ⧸ p`-algebra. -/
/-
**Ideal.Quotient.algebraOfLiesOver** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
形式化陈述：algebraOfLiesOver : Algebra (A ⧸ p) (B ⧸ P)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
If `P` lies over `p`, then canonically `B ⧸ P` is a `A ⧸ p`-algebra.
-/
instance algebraOfLiesOver : Algebra (A ⧸ p) (B ⧸ P) :=
  algebraQuotientOfLEComap (le_of_eq (P.over_def p))

@[simp]
/-
**Ideal.Quotient.algebraMap_mk_of_liesOver** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.Quot
ient`。
形式化陈述：algebraMap_mk_of_liesOver (x : A) : algebraMap (A ⧸ p) (B ⧸ P) (Ideal.Quot
ient.mk p x) = Ideal.Quotient.mk P (algebraMap _ _ x)
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma algebraMap_mk_of_liesOver (x : A) :
    algebraMap (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk p x) = Ideal.Quotient.mk P (algebraMap _ _ x) :=
  rfl
/-
**Ideal.Quotient.isScalarTower_of_liesOver** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quot
ient`。
形式化陈述：isScalarTower_of_liesOver : IsScalarTower R (A ⧸ p) (B ⧸ P)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
-/
instance isScalarTower_of_liesOver : IsScalarTower R (A ⧸ p) (B ⧸ P) :=
  IsScalarTower.of_algebraMap_eq' <|
    congrArg (algebraMap B (B ⧸ P)).comp (IsScalarTower.algebraMap_eq R A B)
/-
**Ideal.Quotient.instFaithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
形式化陈述：instFaithfulSMul : FaithfulSMul (A ⧸ p) (B ⧸ P)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …
· 使用定理 `Ideal.mem_of_liesOver`：mem_of_liesOver [P.LiesOver p] (x : A) : x in p ↔
 algebraMap A B x in P
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
instance instFaithfulSMul : FaithfulSMul (A ⧸ p) (B ⧸ P) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  rintro ⟨a⟩ ⟨b⟩ hab
  apply Quotient.eq.mpr ((mem_of_liesOver P p (a - b)).mpr _)
  rw [map_sub]
  exact Quotient.eq.mp hab

variable {p} in
/-
**Ideal.Quotient.nontrivial_of_liesOver_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Ide
al.Quotient`。
形式化陈述：nontrivial_of_liesOver_of_ne_top (hp : p != ⊤) : Nontrivial (B ⧸ P)
参数：hp : p != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.Quotient.nontrivial_iff`：∀ {R : Type u_3} [inst : Ring R] {I : Ide
al R}, Nontrivial (R ⧸ I) ↔ I ≠ ⊤
· 使用引理 `Ideal.ne_top_iff_of_liesOver`：ne_top_iff_of_liesOver [P.LiesOver p] : P 
!= ⊤ ↔ p != ⊤
-/
theorem nontrivial_of_liesOver_of_ne_top (hp : p ≠ ⊤) : Nontrivial (B ⧸ P) := by
  rwa [Quotient.nontrivial_iff, ne_top_iff_of_liesOver _ p]
/-
**Ideal.Quotient.nontrivial_of_liesOver_of_isPrime** 是 Mathlib 中的一个定理，位于命名空间 `Id
eal.Quotient`。
形式化陈述：nontrivial_of_liesOver_of_isPrime [hp : p.IsPrime] : Nontrivial (B ⧸ P)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.nontrivial_of_liesOver_of_ne_top`：nontrivial_of_liesOver_
of_ne_top (hp : p != ⊤) : Nontrivial (B ⧸ P)
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
-/
theorem nontrivial_of_liesOver_of_isPrime [hp : p.IsPrime] : Nontrivial (B ⧸ P) :=
  nontrivial_of_liesOver_of_ne_top P hp.ne_top

section algEquiv

variable {P} {E : Type*} [EquivLike E B C] [AlgEquivClass E A B C] (σ : E)

/-- An `A ⧸ p`-algebra isomorphism between `B ⧸ P` and `C ⧸ Q` induced by an `A`-algebra
  isomorphism between `B` and `C`, where `Q = σ P`. -/
/-
**Ideal.Quotient.algEquivOfEqMap** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：algEquivOfEqMap (h : Q = P.map σ) : (B ⧸ P) ≃ₐ[A ⧸ p] (C ⧸ Q) where __
参数：h : Q = P.map σ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
An `A ⧸ p`-algebra isomorphism between `B ⧸ P` and `C ⧸ Q` induced by an `A`-alg
ebra
  isomorphism between `B` and `C`, where `Q = σ P`.
-/
def algEquivOfEqMap (h : Q = P.map σ) : (B ⧸ P) ≃ₐ[A ⧸ p] (C ⧸ Q) where
  __ := quotientEquiv P Q (RingEquivClass.toRingEquiv σ) h
  commutes' := by
    rintro ⟨x⟩
    exact congrArg (Ideal.Quotient.mk Q) (AlgHomClass.commutes σ x)

@[simp]
/-
**Ideal.Quotient.algEquivOfEqMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient
`。
形式化陈述：algEquivOfEqMap_apply (h : Q = P.map σ) (x : B) : algEquivOfEqMap p σ h x 
= σ x
参数：h : Q = P.map σ；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem algEquivOfEqMap_apply (h : Q = P.map σ) (x : B) : algEquivOfEqMap p σ h x = σ x :=
  rfl

/-- An `A ⧸ p`-algebra isomorphism between `B ⧸ P` and `C ⧸ Q` induced by an `A`-algebra
  isomorphism between `B` and `C`, where `P = σ⁻¹ Q`. -/
/-
**Ideal.Quotient.algEquivOfEqComap** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：algEquivOfEqComap (h : P = Q.comap σ) : (B ⧸ P) ≃ₐ[A ⧸ p] (C ⧸ Q)
参数：h : P = Q.comap σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `A ⧸ p`-algebra isomorphism between `B ⧸ P` and `C ⧸ Q` induced by an `A`-alg
ebra
  isomorphism between `B` and `C`, where `P = σ⁻¹ Q`.
-/
def algEquivOfEqComap (h : P = Q.comap σ) : (B ⧸ P) ≃ₐ[A ⧸ p] (C ⧸ Q) :=
  algEquivOfEqMap p σ ((congrArg (map σ) h).trans (Q.map_comap_eq_self_of_equiv σ)).symm

@[simp]
/-
**Ideal.Quotient.algEquivOfEqComap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotie
nt`。
形式化陈述：algEquivOfEqComap_apply (h : P = Q.comap σ) (x : B) : algEquivOfEqComap p 
σ h x = σ x
参数：h : P = Q.comap σ；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem algEquivOfEqComap_apply (h : P = Q.comap σ) (x : B) : algEquivOfEqComap p σ h x = σ x :=
  rfl

end algEquiv

/-- If `P` lies over `p`, then the stabilizer of `P` acts on the extension `(B ⧸ P) / (A ⧸ p)`. -/
/-
**Ideal.Quotient.stabilizerHom** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：stabilizerHom : MulAction.stabilizer G P ->* ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) w
here toFun g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` lies over `p`, then the stabilizer of `P` acts on the extension `(B ⧸ P) 
/ (A ⧸ p)`.
-/
def stabilizerHom : MulAction.stabilizer G P →* ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) where
  toFun g := algEquivOfEqMap p (MulSemiringAction.toAlgEquiv A B g) g.2.symm
  map_one' := by
    ext ⟨x⟩
    exact congrArg (Ideal.Quotient.mk P) (one_smul G x)
  map_mul' g h := by
    ext ⟨x⟩
    exact congrArg (Ideal.Quotient.mk P) (mul_smul g h x)
/-
**Ideal.Quotient.stabilizerHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：∀ {A : Type u_3} {B : Type u_4} [inst : CommRing A] [inst_1 : CommRing B] 
[inst_2 : Algebra A B] (P : Ideal B)   (p : Ideal A) [inst_3 : P.LiesOver p] (G 
: Type u_6) [inst_4 : Group G] [inst_5 : MulSemiringAction G B]   [inst_6 : SMul
CommClass G A B] (g : ↥(MulAction.stabilizer G P)) (b : B),   ((Ideal.Quotient.s
tabilizerHom P p G) g) ((Ideal.Quotient.mk P) b) = (Ideal.Quotient.mk P) (g • b)
参数：P : Ideal B；p : Ideal A；G : Type u_6；g : ↥(MulAction.stabilizer G P)；b : B；(I
deal.Quotient.stabilizerHom P p G) g；(Ideal.Quotient.mk P) b；Ideal.Quotient.mk P
；g • b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
@[simp] theorem stabilizerHom_apply (g : MulAction.stabilizer G P) (b : B) :
    stabilizerHom P p G g b = ↑(g • b) :=
  rfl
/-
**Ideal.Quotient.ker_stabilizerHom** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.Quotient`。
形式化陈述：ker_stabilizerHom : (stabilizerHom P p G).ker = P.inertia (MulAction.stabi
lizer G P)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ker_stabilizerHom : (stabilizerHom P p G).ker = P.inertia (MulAction.stabilizer G P) := by
  ext σ
  simp [DFunLike.ext_iff, mk_surjective.forall, Quotient.eq]
/-
**Ideal.Quotient.map_ker_stabilizer_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quo
tient`。
形式化陈述：map_ker_stabilizer_subtype : (stabilizerHom P p G).ker.map (Subgroup.subty
pe _) = P.inertia G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.Quotient.ker_stabilizerHom`：ker_stabilizerHom : (stabilizerHom P p
 G).ker = P.inertia (MulAction.stabilizer G P)
· 使用引理 `AddSubgroup.inertia_map_subtype`：inertia_map_subtype (H : Subgroup G) : 
(I.inertia H).map H.subtype = I.inertia G ⊓ H
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_ker_stabilizer_subtype :
    (stabilizerHom P p G).ker.map (Subgroup.subtype _) = P.inertia G := by
  simp [ker_stabilizerHom, Ideal.inertia_le_stabilizer]
/-
**Ideal.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : Ideal R) (P : Ideal A) [P.IsPrime] [P.LiesOver p] :
    (P.map (Ideal.Quotient.mk <| p.map (algebraMap R A))).IsPrime := by
  apply Ideal.isPrime_map_quotientMk_of_isPrime
  rw [Ideal.map_le_iff_le_comap, Ideal.LiesOver.over (p := p) (P := P)]

end Quotient

end ideal_liesOver

section primesOver

variable {A : Type*} [CommSemiring A] (p : Ideal A) (B : Type*) [Semiring B] [Algebra A B]

/-- The set of all prime ideals in `B` that lie over an ideal `p` of `A`. -/
/-
**Ideal.primesOver** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：primesOver : Set (Ideal B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of all prime ideals in `B` that lie over an ideal `p` of `A`.
-/
def primesOver : Set (Ideal B) :=
  { P : Ideal B | P.IsPrime ∧ P.LiesOver p }

variable {B}
/-
**Ideal.primesOver.isPrime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.primesOver`。
形式化陈述：∀ {A : Type u_2} [inst : CommSemiring A] (p : Ideal A) {B : Type u_3} [ins
t_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p.primesOver B)), (↑Q).IsPrime
参数：p : Ideal A；Q : ↑(p.primesOver B)；↑Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance primesOver.isPrime (Q : primesOver p B) : Q.1.IsPrime :=
  Q.2.1
/-
**Ideal.primesOver.liesOver** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.primesOver`。
形式化陈述：∀ {A : Type u_2} [inst : CommSemiring A] (p : Ideal A) {B : Type u_3} [ins
t_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p.primesOver B)), (↑Q).LiesOve
r p
参数：p : Ideal A；Q : ↑(p.primesOver B)；↑Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance primesOver.liesOver (Q : primesOver p B) : Q.1.LiesOver p :=
  Q.2.2

/-- If an ideal `P` of `B` is prime and lying over `p`, then it is in `primesOver p B`. -/
/-
**Ideal.primesOver.mk** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.primesOver`。
形式化陈述：{A : Type u_2} →   [inst : CommSemiring A] →     (p : Ideal A) →       {B 
: Type u_3} →         [inst_1 : Semiring B] →           [inst_2 : Algebra A B] →
 (P : Ideal B) → [hPp : P.IsPrime] → [hp : P.LiesOver p] → ↑(p.primesOver B)
参数：p : Ideal A；P : Ideal B；p.primesOver B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an ideal `P` of `B` is prime and lying over `p`, then it is in `primesOver p 
B`.
-/
abbrev primesOver.mk (P : Ideal B) [hPp : P.IsPrime] [hp : P.LiesOver p] : primesOver p B :=
  ⟨P, ⟨hPp, hp⟩⟩

variable {p} in
/-
**Ideal.ne_bot_of_mem_primesOver** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ne_bot_of_mem_primesOver [FaithfulSMul A B] (hp : p != ⊥) {P : Ideal B} (h
P : P in p.primesOver B) : P != ⊥
参数：hp : p != ⊥；hP : P in p.primesOver B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.ne_bot_of_liesOver_of_ne_bot`：ne_bot_of_liesOver_of_ne_bot (hp : p
 != ⊥) (P : Ideal B) [P.LiesOver p] : P != ⊥
-/
theorem ne_bot_of_mem_primesOver [FaithfulSMul A B] (hp : p ≠ ⊥) {P : Ideal B}
    (hP : P ∈ p.primesOver B) : P ≠ ⊥ := by
  have : P.LiesOver p := hP.2
  exact ne_bot_of_liesOver_of_ne_bot hp P

end primesOver

end Ideal

