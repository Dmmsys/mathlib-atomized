/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import Mathlib.CategoryTheory.CofilteredSystem

/-!
# Invariant Extensions of Rings

In this file we generalize the results in `Mathlib/RingTheory/Invariant/Basic.lean` to profinite
groups.

## Main statements

Let `G` be a profinite group acting continuously on a
  commutative ring `B` (with the discrete topology) satisfying `Algebra.IsInvariant A B G`.

* `Algebra.IsInvariant.isIntegral_of_profinite`: `B/A` is an integral extension.
* `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`:
  `G` acts transitivity on the prime ideals of `B` lying above a given prime ideal of `A`.
* `Ideal.Quotient.stabilizerHom_surjective_of_profinite`: if `Q` is a prime ideal of `B` lying over
  a prime ideal `P` of `A`, then the stabilizer subgroup of `Q` surjects onto `Aut((B/Q)/(A/P))`.

-/

@[expose] public section

open scoped Pointwise

section ProfiniteGrp

universe u

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type u} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
variable {P : Ideal A}
variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]

open CategoryTheory

include G in
/-
**Algebra.IsInvariant.isIntegral_of_profinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.IsInvariant.isIntegral_of_profinite [Algebra.IsInvariant A B G] : 
Algebra.IsIntegral A B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`：exist_openNo
rmalSubgroup_sub_open_nhds_of_one {U : Set G} (UOpen : IsOpen U) (einU : 1 in U)
 : exists H : OpenNormalSubgroup G, (H : Set G) …
· 使用引理 `stabilizer_isOpen`：stabilizer_isOpen [DiscreteTopology X] (x : X) : IsOp
en (MulAction.stabilizer M x : Set M)
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsInvariant.isIntegral`：isIntegral [Finite G] : Algebra.IsIntegr
al A B
· 使用定理 `OpenNormalSubgroup.instNormal`：∀ {G : Type u} [inst : Group G] [inst_1 :
 TopologicalSpace G] (H : OpenNormalSubgroup G), (↑H.toOpenSubgroup).Normal
· 使用定理 `instIsInvariantSubtypeMemSubalgebraSubalgebraSubgroupQuotient`：∀ {A : Ty
pe u_1} {B : Type u_2} [inst : CommRing A] [inst_1 : CommRing B] [inst_2 : Algeb
ra A B] {G : Type u_3}   [inst_3 : Group G] [inst_4…
· 使用定理 `Subgroup.instFiniteQuotientOfSeparatelyContinuousMulOfCompactSpace`：∀ {G
 : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G] [SeparatelyContinuou
sMul G] [CompactSpace G]   (U : OpenSubgroup G), Finite …
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsIntegral.map`：IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebr
a R B] [Algebra A B] [Algebra R C] [IsScalarTower R A B] [Algebra A C] [IsScalar
Towe…
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…
-/
lemma Algebra.IsInvariant.isIntegral_of_profinite
    [Algebra.IsInvariant A B G] : Algebra.IsIntegral A B := by
  constructor
  intro x
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (stabilizer_isOpen G x) (one_mem _)
  have := (Algebra.IsInvariant.isIntegral A (FixedPoints.subalgebra A B N.1.1) (G ⧸ N.1.1)).1
    ⟨x, fun g ↦ hN g.2⟩
  exact this.map (FixedPoints.subalgebra A B N.1.1).val

set_option backward.isDefEq.respectTransparency.types false in
/-- `G` acts transitively on the prime ideals of `B` above a given prime ideal of `A`. -/
/-
**Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite [Algebra.IsInvari
ant A B G] (P Q : Ideal B) [P.IsPrime] [Q.IsPrime] (hPQ : P.under A = Q.under A)
 : exists g : G, Q = g • P
参数：P Q : Ideal B；hPQ : P.under A = Q.under A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenNormalSubgroup.instNormal`：∀ {G : Type u} [inst : Group G] [inst_1 :
 TopologicalSpace G] (H : OpenNormalSubgroup G), (↑H.toOpenSubgroup).Normal
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `QuotientGroup.mk_surjective`：mk_surjective : Function.Surjective @mk _ _
 s
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.pointwise_smul_eq_comap`：pointwise_smul_eq_comap {a : M} (S : Idea
l R) : a • S = S.comap (MulSemiringAction.toRingAut _ _ a).symm
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.comap_coe`：comap_coe [RingHomClass F R S] (I : Ideal S) : I.comap 
(f : R ->+* S) = I.comap f
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Algebra.IsInvariant.exists_smul_of_under_eq`：exists_smul_of_under_eq [Fi
nite G] [SMulCommClass G A B] (P Q : Ideal B) [hP : P.IsPrime] [hQ : Q.IsPrime] 
(hPQ : P.under A = Q.under A) : e…
· 使用定理 `instIsInvariantSubtypeMemSubalgebraSubalgebraSubgroupQuotient`：∀ {A : Ty
pe u_1} {B : Type u_2} [inst : CommRing A] [inst_1 : CommRing B] [inst_2 : Algeb
ra A B] {G : Type u_3}   [inst_3 : Group G] [inst_4…
· 使用定理 `Subgroup.instFiniteQuotientOfSeparatelyContinuousMulOfCompactSpace`：∀ {G
 : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G] [SeparatelyContinuou
sMul G] [CompactSpace G]   (U : OpenSubgroup G), Finite …
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `instSMulCommClassQuotientSubgroupSubtypeMemSubalgebraSubalgebra`：∀ {A : 
Type u_1} {B : Type u_2} [inst : CommRing A] [inst_1 : CommRing B] [inst_2 : Alg
ebra A B] {G : Type u_3}   [inst_3 : Group G] [inst_4…
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `nonempty_sections_of_finite_cofiltered_system`：nonempty_sections_of_fini
te_cofiltered_system {J : Type u} [Category.{w} J] [IsCofilteredOrEmpty J] (F : 
J ⥤ Type v) [forall j : J, Finite (…
· 使用定理 `CategoryTheory.isCofilteredOrEmpty_of_directed_ge`：∀ (α : Type u) [inst 
: Preorder α] [IsCodirectedOrder α], CategoryTheory.IsCofilteredOrEmpty α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `ProfiniteGrp.comp_apply`：comp_apply {A B C : ProfiniteGrp.{u}} (f : A ⟶ 
B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a)
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
`G` acts transitively on the prime ideals of `B` above a given prime ideal of `A
`.
-/
lemma Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    [Algebra.IsInvariant A B G] (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (hPQ : P.under A = Q.under A) :
    ∃ g : G, Q = g • P := by
  let B' := FixedPoints.subalgebra A B
  let F : OpenNormalSubgroup G ⥤ Type _ :=
  { obj N := { g : G ⧸ N.1.1 // Q.under (B' N.1.1) = g • P.under (B' N.1.1) }
    map {N N'} f := ↾fun x ↦ ⟨(QuotientGroup.map _ _ (.id _) (leOfHom f)) x.1, by
      have h : B' N'.1.1 ≤ B' N.1.1 := fun x hx n ↦ hx ⟨_, f.le n.2⟩
      obtain ⟨x, hx⟩ := x
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      simpa only [Ideal.comap_comap, Ideal.pointwise_smul_eq_comap, ← Ideal.comap_coe
        (F := RingEquiv _ _)] using! congr(Ideal.comap (Subalgebra.inclusion h).toRingHom $hx)⟩
    map_id N := by ext ⟨⟨x⟩, hx⟩; rfl
    map_comp f g := by ext ⟨⟨x⟩, hx⟩; rfl }
  have (N : _) : Nonempty (F.obj N) := by
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A
      (B' N.1.1) (G ⧸ N.1.1) (P.under _) (Q.under _) hPQ
    exact ⟨g, hg⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system F
  let a := (ProfiniteGrp.of G).isoLimittoFiniteQuotientFunctor.inv.hom
    ⟨fun N ↦ (s N).1, (fun {N N'} f ↦ congr_arg Subtype.val (hs f))⟩
  have (N : OpenNormalSubgroup G) : QuotientGroup.mk (s := N.1.1) a = s N := by
    change ((ProfiniteGrp.of G).isoLimittoFiniteQuotientFunctor.hom.hom a).1 N = _
    simp only [a]
    rw [← ProfiniteGrp.comp_apply, Iso.inv_hom_id]
    simp
  refine ⟨a, ?_⟩
  ext x
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (stabilizer_isOpen G x) (one_mem _)
  lift x to B' N.1.1 using fun g ↦ hN g.2
  change x ∈ Q.under (B' N.1.1) ↔ x ∈ Ideal.under (B' N.1.1) ((_ : G) • P)
  rw [(s N).2]
  simp only [Ideal.comap_comap, Ideal.pointwise_smul_eq_comap, ← Ideal.comap_coe
        (F := RingEquiv _ _)]
  congr! 2
  ext y
  simp [← this]
  rfl

attribute [local instance] Subgroup.finiteIndex_of_finite_quotient

omit
  [CompactSpace G]
  [TotallyDisconnectedSpace G]
  [IsTopologicalGroup G]
  [TopologicalSpace B]
  [DiscreteTopology B]
  [ContinuousSMul G B] in
/-
**Ideal.Quotient.stabilizerHomSurjectiveAuxFunctor_aux** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：Ideal.Quotient.stabilizerHomSurjectiveAuxFunctor_aux (Q : Ideal B) {N N' :
 OpenNormalSubgroup G} (e : N <= N') (x : G ⧸ N.1.1) (hx : x in MulAction.stabil
izer (G ⧸ N.1.1) (Q.under (FixedPoints.subalgebra A B N.1.1))) : QuotientGroup.m
ap _ _ (.id _) e x in MulAction.stabilizer (G ⧸ N'.1.1) (Q.under (FixedPoints.su
balgebra A B N'.1.1))
参数：Q : Ideal B；e : N <= N'；x : G ⧸ N.1.1；hx : x in MulAction.stabilizer (G ⧸ N.1
.1) (Q.under (FixedPoints.subalgebra A B N.1.1))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenNormalSubgroup.instNormal`：∀ {G : Type u} [inst : Group G] [inst_1 :
 TopologicalSpace G] (H : OpenNormalSubgroup G), (↑H.toOpenSubgroup).Normal
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `QuotientGroup.mk_surjective`：mk_surjective : Function.Surjective @mk _ _
 s
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.pointwise_smul_eq_comap`：pointwise_smul_eq_comap {a : M} (S : Idea
l R) : a • S = S.comap (MulSemiringAction.toRingAut _ _ a).symm
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.comap_coe`：comap_coe [RingHomClass F R S] (I : Ideal S) : I.comap 
(f : R ->+* S) = I.comap f
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
-/
lemma Ideal.Quotient.stabilizerHomSurjectiveAuxFunctor_aux
    (Q : Ideal B)
    {N N' : OpenNormalSubgroup G} (e : N ≤ N')
    (x : G ⧸ N.1.1)
    (hx : x ∈ MulAction.stabilizer (G ⧸ N.1.1) (Q.under (FixedPoints.subalgebra A B N.1.1))) :
    QuotientGroup.map _ _ (.id _) e x ∈
      MulAction.stabilizer (G ⧸ N'.1.1) (Q.under (FixedPoints.subalgebra A B N'.1.1)) := by
  change _ = _
  have h : FixedPoints.subalgebra A B N'.1.1 ≤ FixedPoints.subalgebra A B N.1.1 :=
    fun x hx n ↦ hx ⟨_, e n.2⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  replace hx := congr(Ideal.comap (Subalgebra.inclusion h) $hx)
  simpa only [Ideal.pointwise_smul_eq_comap,
    ← Ideal.comap_coe (F := RingEquiv _ _), Ideal.comap_comap] using! hx

/-- (Implementation)
The functor taking an open normal subgroup `N ≤ G` to the set of lifts of `σ` in `G ⧸ N`.
We will show that its inverse limit is nonempty to conclude that there exists a lift in `G`. -/
/-
**Ideal.Quotient.stabilizerHomSurjectiveAuxFunctor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.Quotient.stabilizerHomSurjectiveAuxFunctor (P : Ideal A) (Q : Ideal 
B) [Q.LiesOver P] (σ : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q) : OpenNormalSubgroup G ⥤ Type u 
where obj N
参数：P : Ideal A；Q : Ideal B；σ : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OpenNormalSubgroup.instNormal`：∀ {G : Type u} [inst : Group G] [inst_1 :
 TopologicalSpace G] (H : OpenNormalSubgroup G), (↑H.toOpenSubgroup).Normal
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
(Implementation)
The functor taking an open normal subgroup `N ≤ G` to the set of lifts of `σ` in
 `G ⧸ N`.
We will show that its inverse limit is nonempty to conclude that there exists a 
lift in `G`.
-/
def Ideal.Quotient.stabilizerHomSurjectiveAuxFunctor
    (P : Ideal A) (Q : Ideal B) [Q.LiesOver P] (σ : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q) :
    OpenNormalSubgroup G ⥤ Type u where
  obj N :=
    letI B' := FixedPoints.subalgebra A B N.1.1
    letI f : (B' ⧸ Q.under B') →ₐ[A ⧸ P] B ⧸ Q :=
    { toRingHom := Ideal.quotientMap _ B'.subtype le_rfl,
      commutes' := Quotient.ind fun _ ↦ rfl }
    { σ' // f.comp (Ideal.Quotient.stabilizerHom
      (Q.under B') P (G ⧸ N.1.1) σ').toAlgHom = σ.toAlgHom.comp f }
  map {N N'} i := ↾fun x ↦ ⟨⟨(QuotientGroup.map _ _ (.id _) (leOfHom i)) x.1,
      Ideal.Quotient.stabilizerHomSurjectiveAuxFunctor_aux Q i.le x.1.1 x.1.2⟩, by
    have h : FixedPoints.subalgebra A B N'.1.1 ≤ FixedPoints.subalgebra A B N.1.1 :=
      fun x hx n ↦ hx ⟨_, i.le n.2⟩
    obtain ⟨⟨x, hx⟩, hx'⟩ := x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    ext g
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g
    exact DFunLike.congr_fun hx' (Ideal.Quotient.mk _ (Subalgebra.inclusion h g))⟩
  map_id N := by ext ⟨⟨⟨x⟩, hx⟩, hx'⟩; rfl
  map_comp f g := by ext ⟨⟨⟨x⟩, hx⟩, hx'⟩; rfl

open Ideal.Quotient in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : Ideal A) (Q : Ideal B) [Q.LiesOver P]
    (σ : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q) (N : OpenNormalSubgroup G) :
    Finite ((stabilizerHomSurjectiveAuxFunctor P Q σ).obj N) := by
  dsimp [stabilizerHomSurjectiveAuxFunctor]
  infer_instance

open Ideal.Quotient in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]
    [Algebra.IsInvariant A B G] (σ : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q) (N : OpenNormalSubgroup G) :
    Nonempty ((stabilizerHomSurjectiveAuxFunctor P Q σ).obj N) := by
  have : IsScalarTower (A ⧸ P) (FixedPoints.subalgebra A B N.1.1 ⧸
    Q.under (FixedPoints.subalgebra A B N.1.1)) (B ⧸ Q) := IsScalarTower.of_algebraMap_eq
    (Quotient.ind fun x ↦ rfl)
  obtain ⟨σ', hσ'⟩ := Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under (G ⧸ N.1.1) P
    (Q.under (FixedPoints.subalgebra A B N.1.1)) σ
  obtain ⟨τ, rfl⟩ := Ideal.Quotient.stabilizerHom_surjective (G ⧸ N.1.1) P
    (Q.under (FixedPoints.subalgebra A B N.1.1)) σ'
  refine ⟨τ, ?_⟩
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hσ' x

/-- The stabilizer subgroup of `Q` surjects onto `Aut((B/Q)/(A/P))`. -/
/-
**Ideal.Quotient.stabilizerHom_surjective_of_profinite** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Ideal.Quotient.stabilizerHom_surjective_of_profinite (P : Ideal A) (Q : Id
eal B) [Q.IsPrime] [Q.LiesOver P] [Algebra.IsInvariant A B G] : Function.Surject
ive (Ideal.Quotient.stabilizerHom Q P G)
参数：P : Ideal A；Q : Ideal B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_sections_of_finite_cofiltered_system`：nonempty_sections_of_fini
te_cofiltered_system {J : Type u} [Category.{w} J] [IsCofilteredOrEmpty J] (F : 
J ⥤ Type v) [forall j : J, Finite (…
· 使用定理 `CategoryTheory.isCofilteredOrEmpty_of_directed_ge`：∀ (α : Type u) [inst 
: Preorder α] [IsCodirectedOrder α], CategoryTheory.IsCofilteredOrEmpty α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instFiniteObjOpenNormalSubgroupStabilizerHomSurjectiveAuxFunctor`：∀ {A :
 Type u_1} {B : Type u_2} [inst : CommRing A] [inst_1 : CommRing B] [inst_2 : Al
gebra A B] {G : Type u}   [inst_3 : Group G] [inst_4 :…
· 使用定理 `instNonemptyObjOpenNormalSubgroupStabilizerHomSurjectiveAuxFunctor`：∀ {A
 : Type u_1} {B : Type u_2} [inst : CommRing A] [inst_1 : CommRing B] [inst_2 : 
Algebra A B] {G : Type u}   [inst_3 : Group G] [inst_4 :…
· 使用定理 `OpenNormalSubgroup.instNormal`：∀ {G : Type u} [inst : Group G] [inst_1 :
 TopologicalSpace G] (H : OpenNormalSubgroup G), (↑H.toOpenSubgroup).Normal
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`：exist_openNo
rmalSubgroup_sub_open_nhds_of_one {U : Set G} (UOpen : IsOpen U) (einU : 1 in U)
 : exists H : OpenNormalSubgroup G, (H : Set G) …
· 使用引理 `stabilizer_isOpen`：stabilizer_isOpen [DiscreteTopology X] (x : X) : IsOp
en (MulAction.stabilizer M x : Set M)
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.pointwise_smul_eq_comap`：pointwise_smul_eq_comap {a : M} (S : Idea
l R) : a • S = S.comap (MulSemiringAction.toRingAut _ _ a).symm
· 使用引理 `Ideal.comap_coe`：comap_coe [RingHomClass F R S] (I : Ideal S) : I.comap 
(f : R ->+* S) = I.comap f
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The stabilizer subgroup of `Q` surjects onto `Aut((B/Q)/(A/P))`.
-/
theorem Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (P : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]
    [Algebra.IsInvariant A B G] :
    Function.Surjective (Ideal.Quotient.stabilizerHom Q P G) := by
  intro σ
  let B' := FixedPoints.subalgebra A B
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system
    (stabilizerHomSurjectiveAuxFunctor (G := G) P Q σ)
  let a := (ProfiniteGrp.of G).isoLimittoFiniteQuotientFunctor.inv.hom
    ⟨fun N ↦ (s N).1.1, (fun {N N'} f ↦ congr($(hs f).1.1))⟩
  have (N : OpenNormalSubgroup G) : QuotientGroup.mk (s := N.1.1) a = (s N).1 :=
    congr_fun (congr_arg Subtype.val (ConcreteCategory.congr_hom (ProfiniteGrp.of
      G).isoLimittoFiniteQuotientFunctor.inv_hom_id
        _)) N
  refine ⟨⟨a, ?_⟩, ?_⟩
  · ext x
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (stabilizer_isOpen G x) (one_mem _)
    lift x to B' N.1.1 using fun g ↦ hN g.2
    change x ∈ (a • Q).under (B' N.1.1) ↔ x ∈ Q.under (B' N.1.1)
    rw [← (s N).1.2]
    simp only [Ideal.comap_comap, Ideal.pointwise_smul_eq_comap, ← Ideal.comap_coe
          (F := RingEquiv _ _)]
    congr! 2
    ext y
    rw [← this]
    rfl
  · ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (stabilizer_isOpen G x) (one_mem _)
    lift x to B' N.1.1 using fun g ↦ hN g.2
    change Ideal.Quotient.mk Q (QuotientGroup.mk (s := N) a • x).1 = _
    rw [this]
    exact DFunLike.congr_fun (s N).2 (Ideal.Quotient.mk _ x)

end ProfiniteGrp

