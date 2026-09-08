/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.IsGaloisGroup.Defs

/-!
# Galois Groups of Rings

Given an action of a group `G` on an extension of rings `B/A`, the predicate `IsGaloisGroup G A B`
states that `G` acts faithfully on `B` with fixed ring `A`. This file develops some of the theory
of this predicate without assuming Galois theory for fields.
-/

@[expose] public section

-- this file should not import any field theory beyond the contents of `FieldTheory/Fixed.lean`
-- material involving Galois theory should be placed in `FieldTheory/IsGaloisGroup.lean`
assert_not_exists IntermediateField.adjoin

open Module

section CommRing

variable (G A B : Type*) [Group G] [CommSemiring A] [Semiring B] [Algebra A B]
  [MulSemiringAction G B]

variable {C : Type*} [CommSemiring C] [Algebra C B]

variable {G} in
/-
**Subgroup.smul_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} (B : Type u_3) [inst : Group G] [inst_1 : Semiring B] [in
st_2 : MulSemiringAction G B] {C : Type u_4}   [inst_3 : CommSemiring C] [inst_4
 : Algebra C B] {H : Subgroup G} [SMulCommClass (↥H) C B] {g : G},   g ∈ H → ∀ (
x : C), g • (algebraMap C B) x = (algebraMap C B) x
参数：B : Type u_3；↥H；x : C；algebraMap C B；algebraMap C B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_algebraMap`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Algebra R A] {α : Type u_2}   [inst_3 : Monoid α] [
inst_…
-/
protected theorem Subgroup.smul_algebraMap {H : Subgroup G} [SMulCommClass H C B] {g : G}
    (hg : g ∈ H) (x : C) :
    g • algebraMap C B x = algebraMap C B x :=
  smul_algebraMap (⟨g, hg⟩ : H) x
/-
**IsGaloisGroup.smul_mem_of_normal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGaloisGroup.smul_mem_of_normal (N : Subgroup G) [hN : N.Normal] [hC : Is
GaloisGroup N C B] (g : G) (x : C) : g • algebraMap C B x in Set.range (algebraM
ap C B)
参数：N : Subgroup G；g : G；x : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsInvariant.isInvariant`：∀ {A : Type u_1} {B : Type u_2} {G : Ty
pe u_3} {inst : CommSemiring A} {inst_1 : Semiring B} {inst_2 : Algebra A B}   {
inst_3 : Group G} {in…
· 使用定理 `IsGaloisGroup.isInvariant`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4
} {inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : A
lgebra A B} {in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_smul_eq_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, g⁻¹ • a = b ↔ a = g • b
· 使用定理 `Subgroup.smul_def`：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [ins
t_1 : MulAction G α] {S : Subgroup G} (g : ↥S) (m : α),   g • m = ↑g • m
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Subgroup.smul_algebraMap`：∀ {G : Type u_1} (B : Type u_3) [inst : Group 
G] [inst_1 : Semiring B] [inst_2 : MulSemiringAction G B] {C : Type u_4}   [inst
_3 : CommSemir…
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `Subgroup.Normal.conj_mem'`：conj_mem' (nH : H.Normal) (n : G) (hn : n in 
H) (g : G) : g⁻¹ * n * g in H
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem IsGaloisGroup.smul_mem_of_normal (N : Subgroup G) [hN : N.Normal]
    [hC : IsGaloisGroup N C B] (g : G) (x : C) :
    g • algebraMap C B x ∈ Set.range (algebraMap C B) := by
  apply hC.isInvariant.isInvariant (g • algebraMap C B x)
  intro n
  rw [← inv_smul_eq_iff, Subgroup.smul_def, ← mul_smul, ← mul_smul]
  exact Subgroup.smul_algebraMap B (hN.conj_mem' n n.prop g) x

@[deprecated (since := "2026-05-28")] alias smul_eq_self := Subgroup.smul_algebraMap
@[deprecated (since := "2026-05-28")] alias smul_mem_of_normal := IsGaloisGroup.smul_mem_of_normal

end CommRing

section Field

variable (G A B K L : Type*) [Group G] [CommRing A] [CommRing B] [MulSemiringAction G B]
  [Algebra A B] [Field K] [Field L] [Algebra K L] [Algebra A K] [Algebra B L] [Algebra A L]
  [IsFractionRing A K] [IsFractionRing B L] [IsScalarTower A K L] [IsScalarTower A B L]
  [MulSemiringAction G L] [SMulDistribClass G B L]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsGaloisGroup G A B] : IsGaloisGroup G (algebraMap A B).range B where
  faithful := IsGaloisGroup.faithful A
  commutes := ⟨fun g ⟨a', ⟨a, ha⟩⟩ b ↦ by simp [Subring.smul_def, ← ha]⟩
  isInvariant := ⟨fun b hb ↦ by
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) b hb
    exact ⟨⟨algebraMap A B a, ⟨a, rfl⟩⟩, ha⟩⟩

/-- `IsGaloisGroup` for rings implies `IsGaloisGroup` for their fraction fields. -/
/-
**IsGaloisGroup.to_isFractionRing_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGaloisGroup.to_isFractionRing_of_isIntegral [Algebra.IsIntegral A B] [hG
AB : IsGaloisGroup G A B] : IsGaloisGroup G K L where faithful
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.faithful`：∀ {G : Type u_1} (A : Type u_2) {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `IsFractionRing.faithfulSMul`：∀ (G : Type u_10) (B : Type u_12) (L : Type
 u_14) [inst : Group G] [inst_1 : CommRing B]   [inst_2 : MulSemiringAction G B]
 [inst_3 : Field …
· 使用定理 `IsFractionRing.smulCommClass`：∀ (G : Type u_10) (A : Type u_11) (B : Typ
e u_12) (K : Type u_13) (L : Type u_14) [inst : Group G] [inst_1 : CommRing A]  
 [inst_2 : CommRin…
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `IsFractionRing.isInvariant_of_isIntegral`：isInvariant_of_isIntegral [Alg
ebra.IsIntegral A B] : Algebra.IsInvariant K L G
· 使用定理 `IsGaloisGroup.isInvariant`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4
} {inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : A
lgebra A B} {in…

--- 原说明 ---
`IsGaloisGroup` for rings implies `IsGaloisGroup` for their fraction fields.
-/
theorem IsGaloisGroup.to_isFractionRing_of_isIntegral
    [Algebra.IsIntegral A B] [hGAB : IsGaloisGroup G A B] :
    IsGaloisGroup G K L where
  faithful :=
    have := hGAB.faithful
    IsFractionRing.faithfulSMul G B L
  commutes := IsFractionRing.smulCommClass G A B K L
  isInvariant := IsFractionRing.isInvariant_of_isIntegral G A B K L

/-- `IsGaloisGroup` for rings implies `IsGaloisGroup` for their fraction fields. -/
/-
**IsGaloisGroup.to_isFractionRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGaloisGroup.to_isFractionRing [Finite G] [hGAB : IsGaloisGroup G A B] : 
IsGaloisGroup G K L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsInvariant.isIntegral`：isIntegral [Finite G] : Algebra.IsIntegr
al A B
· 使用定理 `IsGaloisGroup.isInvariant`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4
} {inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : A
lgebra A B} {in…
· 使用定理 `IsGaloisGroup.to_isFractionRing_of_isIntegral`：IsGaloisGroup.to_isFracti
onRing_of_isIntegral [Algebra.IsIntegral A B] [hGAB : IsGaloisGroup G A B] : IsG
aloisGroup G K L where faithful

--- 原说明 ---
`IsGaloisGroup` for rings implies `IsGaloisGroup` for their fraction fields.
-/
theorem IsGaloisGroup.to_isFractionRing [Finite G] [hGAB : IsGaloisGroup G A B] :
    IsGaloisGroup G K L :=
  have := hGAB.isInvariant.isIntegral
  IsGaloisGroup.to_isFractionRing_of_isIntegral G A B K L

/-- If `B` is an integral extension of an integrally closed domain `A`, then `IsGaloisGroup` for
their fraction fields implies `IsGaloisGroup` for these rings. -/
/-
**IsGaloisGroup.of_isFractionRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGaloisGroup.of_isFractionRing [hGKL : IsGaloisGroup G K L] [IsIntegrally
Closed A] [Algebra.IsIntegral A B] : IsGaloisGroup G A B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsGaloisGroup.faithful`：∀ {G : Type u_1} (A : Type u_2) {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `smul_div₀'`：smul_div₀' (g : α) (x y : β) : g • (x / y) = (g • x) / (g • 
y)
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用引理 `smul_mul'`：smul_mul' (a : M) (b₁ b₂ : N) : a • (b₁ * b₂) = a • b₁ * a • 
b₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `algebraMap.coe_smul'`：algebraMap.coe_smul' [Monoid A] [MulDistribMulActi
on A C] [SMulDistribClass A B C] : (a • b : B) = a • (b : C)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_algebraMap`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Algebra R A] {α : Type u_2}   [inst_3 : Monoid α] [
inst_…
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `Algebra.IsInvariant.isInvariant`：∀ {A : Type u_1} {B : Type u_2} {G : Ty
pe u_3} {inst : CommSemiring A} {inst_1 : Semiring B} {inst_2 : Algebra A B}   {
inst_3 : Group G} {in…
· 使用定理 `IsGaloisGroup.isInvariant`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4
} {inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : A
lgebra A B} {in…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `IsIntegral.algebraMap`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Ring B]   [inst_3 : Algebra R 
A] [inst_4 …
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `IsIntegrallyClosedIn.isIntegral_iff`：isIntegral_iff [IsIntegrallyClosedI
n R A] {x : A} : IsIntegral R x ↔ exists y : R, algebraMap R A y = x
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `isIntegral_algebraMap_iff`：isIntegral_algebraMap_iff [Algebra A B] [IsSc
alarTower R A B] {x : A} (hAB : Function.Injective (algebraMap A B)) : IsIntegra
l R (algebraMap…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If `B` is an integral extension of an integrally closed domain `A`, then `IsGalo
isGroup` for
their fraction fields implies `IsGaloisGroup` for these rings.
-/
theorem IsGaloisGroup.of_isFractionRing [hGKL : IsGaloisGroup G K L]
    [IsIntegrallyClosed A] [Algebra.IsIntegral A B] : IsGaloisGroup G A B := by
  have hc (a : A) : (algebraMap K L) (algebraMap A K a) = (algebraMap B L) (algebraMap A B a) := by
    simp_rw [← IsScalarTower.algebraMap_apply]
  refine ⟨⟨fun h ↦ ?_⟩, ⟨fun g x y ↦ IsFractionRing.injective B L ?_⟩, ⟨fun x h ↦ ?_⟩⟩
  · have := hGKL.faithful
    refine eq_of_smul_eq_smul fun (y : L) ↦ ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B y
    simp only [smul_div₀', ← algebraMap.coe_smul', h]
  · simp [Algebra.smul_def, algebraMap.coe_smul', ← hc]
  · obtain ⟨b, hb⟩ := hGKL.isInvariant.isInvariant (algebraMap B L x)
      (by simpa [← algebraMap.coe_smul'])
    have hx : IsIntegral A (algebraMap B L x) := (Algebra.IsIntegral.isIntegral x).algebraMap
    rw [← hb, isIntegral_algebraMap_iff (algebraMap K L).injective,
      IsIntegrallyClosedIn.isIntegral_iff] at hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, by rwa [hc, IsFractionRing.coe_inj] at hb⟩

/-- If `G` is finite and `A` is integrally closed then `IsGaloisGroup G A B` is equivalent to `B/A`
being integral and the fields of fractions `Frac(B)/Frac(A)` being Galois with Galois group `G`. -/
/-
**IsGaloisGroup.iff_isFractionRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGaloisGroup.iff_isFractionRing [Finite G] [IsIntegrallyClosed A] : IsGal
oisGroup G A B ↔ Algebra.IsIntegral A B ∧ IsGaloisGroup G K L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsInvariant.isIntegral`：isIntegral [Finite G] : Algebra.IsIntegr
al A B
· 使用定理 `IsGaloisGroup.isInvariant`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4
} {inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : A
lgebra A B} {in…
· 使用定理 `IsGaloisGroup.to_isFractionRing`：IsGaloisGroup.to_isFractionRing [Finite
 G] [hGAB : IsGaloisGroup G A B] : IsGaloisGroup G K L
· 使用定理 `IsGaloisGroup.of_isFractionRing`：IsGaloisGroup.of_isFractionRing [hGKL :
 IsGaloisGroup G K L] [IsIntegrallyClosed A] [Algebra.IsIntegral A B] : IsGalois
Group G A B

--- 原说明 ---
If `G` is finite and `A` is integrally closed then `IsGaloisGroup G A B` is equi
valent to `B/A`
being integral and the fields of fractions `Frac(B)/Frac(A)` being Galois with G
alois group `G`.
-/
theorem IsGaloisGroup.iff_isFractionRing [Finite G] [IsIntegrallyClosed A] :
    IsGaloisGroup G A B ↔ Algebra.IsIntegral A B ∧ IsGaloisGroup G K L :=
  ⟨fun h ↦ ⟨h.isInvariant.isIntegral, h.to_isFractionRing G A B K L⟩,
    fun ⟨_, h⟩ ↦ h.of_isFractionRing G A B K L⟩

@[deprecated (since := "2026-04-20")] alias FractionRing.mulSemiringAction_of_isGaloisGroup :=
  IsFractionRing.mulSemiringAction

/--
If `G` is finite and `IsGaloisGroup G A B` with `A` and `B` domains, then `G` is also
a Galois group for `FractionRing B / FractionRing A` for the action defined by
`IsFractionRing.mulSemiringAction`.
-/
/-
**IsGaloisGroup.toFractionRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsGaloisGroup.toFractionRing [IsDomain A] [IsDomain B] [Finite G] [IsGaloi
sGroup G A B] [Algebra (FractionRing A) (FractionRing B)] [IsScalarTower A (Frac
tionRing A) (FractionRing B)] : letI
参数：FractionRing A；FractionRing B；FractionRing A；FractionRing B。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsGaloisGroup.to_isFractionRing`：IsGaloisGroup.to_isFractionRing [Finite
 G] [hGAB : IsGaloisGroup G A B] : IsGaloisGroup G K L
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…

--- 原说明 ---
If `G` is finite and `IsGaloisGroup G A B` with `A` and `B` domains, then `G` is
 also
a Galois group for `FractionRing B / FractionRing A` for the action defined by
`IsFractionRing.mulSemiringAction`.
-/
instance IsGaloisGroup.toFractionRing [IsDomain A] [IsDomain B] [Finite G]
    [IsGaloisGroup G A B] [Algebra (FractionRing A) (FractionRing B)]
    [IsScalarTower A (FractionRing A) (FractionRing B)] :
    letI := IsFractionRing.mulSemiringAction G B (FractionRing B)
    IsGaloisGroup G (FractionRing A) (FractionRing B) := by
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  apply IsGaloisGroup.to_isFractionRing G A B _ _

end Field

variable (G : Type*) [Group G]

namespace IsGaloisGroup

section IsDomain

variable (A B : Type*) [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
  [MulSemiringAction G B] [IsGaloisGroup G A B] [Finite G]

attribute [local instance] FractionRing.liftAlgebra in
/-- If `G` is a finite Galois group for `B/A`, then `G` is isomorphic to `Gal(B/A)`. -/
/-
**IsGaloisGroup.mulEquivAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsGaloisGroup`。
形式化陈述：(G : Type u_1) →   [inst : Group G] →     (A : Type u_2) →       (B : Type
 u_3) →         [inst_1 : CommRing A] →           [inst_2 : CommRing B] →       
      [IsDomain B] →               [inst_4 : Algebra A B] →                 [Fai
thfulSMul A B] →                   [inst_6 : MulSemiringAction G B] → [IsGaloisG
roup G A B] → [Finite G] → G ≃* B ≃ₐ[A] B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is a finite Galois group for `B/A`, then `G` is isomorphic to `Gal(B/A)`.
-/
@[simps!] noncomputable def mulEquivAlgEquiv : G ≃* Gal(B/A) :=
  MulEquiv.ofBijective (MulSemiringAction.toAlgAut G A B) (by
    have := IsDomain.of_faithfulSMul A B
    have : FaithfulSMul G B := IsGaloisGroup.faithful A
    refine ⟨fun _ _ ↦ eq_of_smul_eq_smul ∘ DFunLike.ext_iff.mp, fun φ ↦ ?_⟩
    obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective G ⊥ ⊥
      (Ideal.Quotient.algEquivOfEqMap (⊥ : Ideal A) φ Ideal.map_bot.symm)
    use g
    rw [AlgEquiv.ext_iff] at hg ⊢
    exact fun x ↦ (AlgEquiv.quotientBot A B).symm.injective (hg x))

end IsDomain

variable (H : Subgroup G)

/-
**IsGaloisGroup.** 是 Mathlib 中的一个实例，位于命名空间 `IsGaloisGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [MulSemiringAction G S] [hGKL : IsGaloisGroup G R S] :
    IsGaloisGroup H (FixedPoints.subalgebra R S H) S where
  faithful := have := hGKL.faithful; inferInstance
  commutes := inferInstance
  isInvariant := ⟨fun x h ↦ ⟨⟨x, h⟩, rfl⟩⟩

section Quotient

section Semiring

variable (A B C : Type*) [CommSemiring A] [Semiring C] [Algebra A C] [MulSemiringAction G C]
variable (N : Subgroup G) [CommSemiring B] [Algebra B C]

/-- If `N` is a normal subgroup of `G` and `IsGaloisGroup N B C`, then `G` acts on `B`.
For `g : G` and `x : B`, `g • x` is the unique element of `B` whose image in `C` is
`g • algebraMap B C x`, see `algebraMap_smulOfNormal`. -/
@[implicit_reducible]
/-
**IsGaloisGroup.smulOfNormal** 是 Mathlib 中的一个定义，位于命名空间 `IsGaloisGroup`。
形式化陈述：smulOfNormal [N.Normal] [IsGaloisGroup N B C] : SMul G B where smul g x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.smul_mem_of_normal`：IsGaloisGroup.smul_mem_of_normal (N : 
Subgroup G) [hN : N.Normal] [hC : IsGaloisGroup N C B] (g : G) (x : C) : g • alg
ebraMap C B x in Set.r…

--- 原说明 ---
If `N` is a normal subgroup of `G` and `IsGaloisGroup N B C`, then `G` acts on `
B`.
For `g : G` and `x : B`, `g • x` is the unique element of `B` whose image in `C`
 is
`g • algebraMap B C x`, see `algebraMap_smulOfNormal`.
-/
noncomputable def smulOfNormal [N.Normal] [IsGaloisGroup N B C] : SMul G B where
  smul g x := (smul_mem_of_normal G C N g x).choose

@[simp]
/-
**IsGaloisGroup.algebraMap_smulOfNormal** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup
`。
形式化陈述：algebraMap_smulOfNormal [N.Normal] [IsGaloisGroup N B C] (g : G) (x : B) :
 letI
参数：g : G；x : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `IsGaloisGroup.smul_mem_of_normal`：IsGaloisGroup.smul_mem_of_normal (N : 
Subgroup G) [hN : N.Normal] [hC : IsGaloisGroup N C B] (g : G) (x : C) : g • alg
ebraMap C B x in Set.r…
-/
theorem algebraMap_smulOfNormal [N.Normal] [IsGaloisGroup N B C] (g : G) (x : B) :
    letI := smulOfNormal G B C
    algebraMap B C (g • x) = g • algebraMap B C x :=
  (smul_mem_of_normal G C N g x).choose_spec

/-- If `N` is normal and `IsGaloisGroup N B C`, the action `smulOfNormal G B C` satisfies
`SMulDistribClass G B C`. -/
/-
**IsGaloisGroup.smulDistribClass_smulOfNormal** 是 Mathlib 中的一个实例，位于命名空间 `IsGaloi
sGroup`。
形式化陈述：smulDistribClass_smulOfNormal [N.Normal] [IsGaloisGroup N B C] : letI
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用引理 `smul_mul'`：smul_mul' (a : M) (b₁ b₂ : N) : a • (b₁ * b₂) = a • b₁ * a • 
b₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsGaloisGroup.algebraMap_smulOfNormal`：algebraMap_smulOfNormal [N.Normal
] [IsGaloisGroup N B C] (g : G) (x : B) : letI
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `N` is normal and `IsGaloisGroup N B C`, the action `smulOfNormal G B C` sati
sfies
`SMulDistribClass G B C`.
-/
instance smulDistribClass_smulOfNormal [N.Normal] [IsGaloisGroup N B C] :
    letI := smulOfNormal G B C
    SMulDistribClass G B C :=
  let := smulOfNormal G B C
  ⟨fun g b c ↦ by simp [Algebra.smul_def]⟩

variable [FaithfulSMul B C]

/-- If `N` is a normal subgroup of `G` and `IsGaloisGroup N B C`, then `G` acts on `B` as a
`MulSemiringAction`, via the action defined in `smulOfNormal`. -/
@[implicit_reducible]
/-
**IsGaloisGroup.mulSemiringActionOfNormal** 是 Mathlib 中的一个定义，位于命名空间 `IsGaloisGro
up`。
形式化陈述：mulSemiringActionOfNormal [IsGaloisGroup N B C] [N.Normal] : MulSemiringAc
tion G B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `N` is a normal subgroup of `G` and `IsGaloisGroup N B C`, then `G` acts on `
B` as a
`MulSemiringAction`, via the action defined in `smulOfNormal`.
-/
noncomputable def mulSemiringActionOfNormal [IsGaloisGroup N B C] [N.Normal] :
    MulSemiringAction G B := by
  let : SMul G B := smulOfNormal G B C N
  have : SMulDistribClass G B C := smulDistribClass_smulOfNormal G B C N
  exact mulSemiringActionOfSmulDistribClass B C G

/-- If `N` is a normal subgroup of `G` and `IsGaloisGroup N B C`, then the quotient group `G ⧸ N`
acts on `B` by `(g : G ⧸ N) • x = g • x`. -/
@[implicit_reducible]
/-
**IsGaloisGroup.mulSemiringActionQuotient** 是 Mathlib 中的一个定义，位于命名空间 `IsGaloisGro
up`。
形式化陈述：mulSemiringActionQuotient [IsGaloisGroup N B C] [N.Normal] : MulSemiringAc
tion (G ⧸ N) B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `N` is a normal subgroup of `G` and `IsGaloisGroup N B C`, then the quotient 
group `G ⧸ N`
acts on `B` by `(g : G ⧸ N) • x = g • x`.
-/
noncomputable def mulSemiringActionQuotient [IsGaloisGroup N B C] [N.Normal] :
    MulSemiringAction (G ⧸ N) B :=
  letI := mulSemiringActionOfNormal G B C N
  { smul q x :=
      Quotient.liftOn' q (· • x) fun g₁ g₂ h ↦ by
      apply FaithfulSMul.algebraMap_injective B C
      rw [algebraMap.smul', algebraMap.smul', smul_eq_iff_eq_inv_smul, ← smul_assoc, smul_eq_mul,
        Subgroup.smul_algebraMap C (by rwa [← QuotientGroup.leftRel_apply])]
    one_smul x := one_smul G x
    mul_smul q₁ q₂ x := Quotient.inductionOn₂' q₁ q₂ fun g h ↦ mul_smul g h x
    smul_add q x y := Quotient.inductionOn' q fun g ↦ smul_add g x y
    smul_zero q := Quotient.inductionOn' q fun g ↦ smul_zero g
    smul_one q := Quotient.inductionOn' q fun g ↦ smul_one g
    smul_mul q x y := Quotient.inductionOn' q fun g ↦ smul_mul' g x y }
/-
**IsGaloisGroup.mulSemiringActionQuotient_smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Is
GaloisGroup`。
形式化陈述：mulSemiringActionQuotient_smul_def [MulSemiringAction G B] [SMulDistribCla
ss G B C] [IsGaloisGroup N B C] [N.Normal] (g : G) (b : B) : letI
参数：g : G；b : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.liftOn'_mk''`：∀ {α : Sort u_1} {φ : Sort u_4} {s₁ : Setoid α} (
f : α → φ) (h : ∀ (a b : α), s₁ a b → f a = f b) (x : α),   (Quotient.mk'' x).li
ftOn' f h =…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraMap.smul'`：algebraMap.smul' [Monoid A] [MulDistribMulAction A C] 
[SMulDistribClass A B C] : algebraMap B C (a • b) = a • (algebraMap B C b)
-/
theorem mulSemiringActionQuotient_smul_def [MulSemiringAction G B] [SMulDistribClass G B C]
    [IsGaloisGroup N B C] [N.Normal] (g : G) (b : B) :
    letI := mulSemiringActionQuotient G B C N
    (g : G ⧸ N) • b = g • b := by
  let := mulSemiringActionOfNormal G B C N
  refine (Quotient.liftOn'_mk'' (· • b) _ g).trans (FaithfulSMul.algebraMap_injective B C ?_)
  rw [algebraMap.smul', algebraMap.smul']
/-
**IsGaloisGroup.isScalarTower_mulSemiringActionQuotient** 是 Mathlib 中的一个实例，位于命名空
间 `IsGaloisGroup`。
形式化陈述：isScalarTower_mulSemiringActionQuotient [MulSemiringAction G B] [SMulDistr
ibClass G B C] [IsGaloisGroup N B C] [N.Normal] : letI
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `IsGaloisGroup.mulSemiringActionQuotient_smul_def`：mulSemiringActionQuoti
ent_smul_def [MulSemiringAction G B] [SMulDistribClass G B C] [IsGaloisGroup N B
 C] [N.Normal] (g : G) (b : B) : letI
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isScalarTower_mulSemiringActionQuotient [MulSemiringAction G B] [SMulDistribClass G B C]
    [IsGaloisGroup N B C] [N.Normal] :
    letI := mulSemiringActionQuotient G B C N
    IsScalarTower G (G ⧸ N) B :=
  let := mulSemiringActionQuotient G B C N
  ⟨fun g q b ↦ Quotient.inductionOn' q fun h ↦ by
    simp [mul_smul, mulSemiringActionQuotient_smul_def]⟩

/-- If `G` acts on `C` commuting with `A`, then the action of `G ⧸ N` on `B` commutes with `A`. -/
/-
**IsGaloisGroup.smulCommClassQuotient** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：smulCommClassQuotient [N.Normal] [Algebra A B] [IsScalarTower A B C] [SMul
CommClass G A C] [MulSemiringAction G B] [MulAction (G ⧸ N) B] [SMulDistribClass
 G B C] [IsScalarTower G (G ⧸ N) B] : SMulCommClass (G ⧸ N) A B
参数：G ⧸ N；G ⧸ N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.coe_quotient_smul`：coe_quotient_smul {H : Subgroup G} [H.Norma
l] [SMul G X] [MulAction (G ⧸ H) X] [IsScalarTower G (G ⧸ H) X] (g : G) (x : X) 
: (g : G ⧸ H) • x…
· 使用定理 `algebraMap.smul'`：algebraMap.smul' [Monoid A] [MulDistribMulAction A C] 
[SMulDistribClass A B C] : algebraMap B C (a • b) = a • (algebraMap B C b)
· 使用定理 `algebraMap.smul`：algebraMap.smul [SMul A C] [IsScalarTower A B C] : alge
braMap B C (a • b) = a • (algebraMap B C b)
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `G` acts on `C` commuting with `A`, then the action of `G ⧸ N` on `B` commute
s with `A`.
-/
theorem smulCommClassQuotient [N.Normal] [Algebra A B] [IsScalarTower A B C] [SMulCommClass G A C]
    [MulSemiringAction G B] [MulAction (G ⧸ N) B] [SMulDistribClass G B C]
    [IsScalarTower G (G ⧸ N) B] :
    SMulCommClass (G ⧸ N) A B :=
  ⟨fun g k x ↦ Quotient.inductionOn' g fun g ↦
    FaithfulSMul.algebraMap_injective B C (by
      simp [algebraMap.smul, algebraMap.smul', smul_comm])⟩

end Semiring

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [MulSemiringAction G L]

variable (F : IntermediateField K L) (N : Subgroup G) [N.Normal] [IsGaloisGroup N F L]

/-
**IsGaloisGroup.** 是 Mathlib 中的一个实例，位于命名空间 `IsGaloisGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : MulSemiringAction (G ⧸ N) F :=
  letI := smulOfNormal G F L N
  haveI := smulDistribClass_smulOfNormal G F L N
  letI := mulSemiringActionOfSmulDistribClass F L G
  mulSemiringActionQuotient G F L N
/-
**IsGaloisGroup.** 是 Mathlib 中的一个实例，位于命名空间 `IsGaloisGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass G K L] [MulSemiringAction G F] [SMulDistribClass G F L]
    [IsScalarTower G (G ⧸ N) F] : SMulCommClass (G ⧸ N) K F :=
  smulCommClassQuotient G K F L N

end Quotient

end IsGaloisGroup

