/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# The structure sheaf on `ProjectiveSpectrum 𝒜`.

In `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Topology.lean`, we have given a topology on
`ProjectiveSpectrum 𝒜`; in this file we will construct a sheaf on `ProjectiveSpectrum 𝒜`.

## Notation
- `A` is a commutative ring;
- `σ` is a class of additive subgroups of `A`;
- `𝒜 : ℕ → σ` is the grading of `A`;
- `U` is opposite object of some open subset of `ProjectiveSpectrum.top`.

## Main definitions and results
We define the structure sheaf as the subsheaf of all dependent function
`f : Π x : U, HomogeneousLocalization 𝒜 x` such that `f` is locally expressible as ratio of two
elements of the *same grading*, i.e. `∀ y ∈ U, ∃ (V ⊆ U) (i : ℕ) (a b ∈ 𝒜 i), ∀ z ∈ V, f z = a / b`.

* `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.isLocallyFraction`: the predicate that
  a dependent function is locally expressible as a ratio of two elements of the same grading.
* `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.sectionsSubring`: the dependent functions
  satisfying the above local property forms a subring of all dependent functions
  `Π x : U, HomogeneousLocalization 𝒜 x`.
* `AlgebraicGeometry.Proj.StructureSheaf`: the sheaf with `U ↦ sectionsSubring U` and natural
  restriction map.

Then we establish that `Proj 𝒜` is a `LocallyRingedSpace`:
* `AlgebraicGeometry.Proj.stalkIso'`: for any `x : ProjectiveSpectrum 𝒜`, the stalk of
  `Proj.StructureSheaf` at `x` is isomorphic to `HomogeneousLocalization 𝒜 x`.
* `AlgebraicGeometry.Proj.toLocallyRingedSpace`: `Proj` as a locally ringed space.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/

@[expose] public section


noncomputable section

namespace AlgebraicGeometry

open scoped DirectSum Pointwise

open DirectSum SetLike Localization TopCat TopologicalSpace CategoryTheory Opposite

variable {A σ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

local notation3 "at " x =>
  HomogeneousLocalization.AtPrime 𝒜
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x))

namespace ProjectiveSpectrum.StructureSheaf

set_option backward.isDefEq.respectTransparency.types false in
variable {𝒜} in
/-- The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` of *same grading* in each of the stalks (which are localizations at various prime ideals).
-/
/-
**AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.IsFraction** 是 Mathlib 中的一
个定义，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf`。
形式化陈述：IsFraction {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : forall x : U, at x.
1) : Prop
参数：ProjectiveSpectrum.top 𝒜；f : forall x : U, at x.1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predicate saying that a dependent function on an open `U` is realised as a f
ixed fraction
`r / s` of *same grading* in each of the stalks (which are localizations at vari
ous prime ideals).
-/
def IsFraction {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : ∀ x : U, at x.1) : Prop :=
  ∃ (i : ℕ) (r s : 𝒜 i) (s_nin : ∀ x : U, s.1 ∉ x.1.asHomogeneousIdeal),
    ∀ x : U, f x = .mk ⟨i, r, s, s_nin x⟩
set_option backward.isDefEq.respectTransparency.types false in
/--
The predicate `IsFraction` is "prelocal", in the sense that if it holds on `U` it holds on any open
subset `V` of `U`.
-/
/-
**AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.isFractionPrelocal** 是 Mat
hlib 中的一个定义，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf`。
形式化陈述：isFractionPrelocal : PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 =>
 at x where pred f
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predicate `IsFraction` is "prelocal", in the sense that if it holds on `U` i
t holds on any open
subset `V` of `U`.
-/
def isFractionPrelocal : PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => at x where
  pred f := IsFraction f
  res := by rintro V U i f ⟨j, r, s, h, w⟩; exact ⟨j, r, s, (h <| i ·), (w <| i ·)⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- We will define the structure sheaf as the subsheaf of all dependent functions in
`Π x : U, HomogeneousLocalization 𝒜 x` consisting of those functions which can locally be expressed
as a ratio of `A` of same grading. -/
/-
**AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.isLocallyFraction** 是 Math
lib 中的一个定义，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf`。
形式化陈述：isLocallyFraction : LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => at 
x
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We will define the structure sheaf as the subsheaf of all dependent functions in
`Π x : U, HomogeneousLocalization 𝒜 x` consisting of those functions which can l
ocally be expressed
as a ratio of `A` of same grading.
-/
def isLocallyFraction : LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => at x :=
  (isFractionPrelocal 𝒜).sheafify

namespace SectionSubring

variable {𝒜}

open Submodule SetLike.GradedMonoid HomogeneousLocalization

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.zero_mem'**
 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.Se
ctionSubring`。
形式化陈述：zero_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) : (isLocallyFraction 
𝒜).pred (0 : forall x : U.unop, at x.1)
参数：U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SetLike.one_mem_graded`：SetLike.one_mem_graded {S : Type*} [SetLike S R]
 [One R] [Zero ι] (A : ι -> S) [SetLike.GradedOne A] : (1 : R) in A 0
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
-/
theorem zero_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFraction 𝒜).pred (0 : ∀ x : U.unop, at x.1) := fun x =>
  ⟨unop U, x.2, 𝟙 (unop U), ⟨0, ⟨0, zero_mem _⟩, ⟨1, one_mem_graded _⟩, _, fun _ => rfl⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.one_mem'** 
是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.Sec
tionSubring`。
形式化陈述：one_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) : (isLocallyFraction 𝒜
).pred (1 : forall x : U.unop, at x.1)
参数：U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `SetLike.one_mem_graded`：SetLike.one_mem_graded {S : Type*} [SetLike S R]
 [One R] [Zero ι] (A : ι -> S) [SetLike.GradedOne A] : (1 : R) in A 0
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
-/
theorem one_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFraction 𝒜).pred (1 : ∀ x : U.unop, at x.1) := fun x =>
  ⟨unop U, x.2, 𝟙 (unop U), ⟨0, ⟨1, one_mem_graded _⟩, ⟨1, one_mem_graded _⟩, _, fun _ => rfl⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.add_mem'** 
是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.Sec
tionSubring`。
形式化陈述：add_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : forall x : U.un
op, at x.1) (ha : (isLocallyFraction 𝒜).pred a) (hb : (isLocallyFraction 𝒜).pred
 b) : (isLocallyFraction 𝒜).pred (a + b)
参数：U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ；a b : forall x : U.unop, at x.1；ha :
 (isLocallyFraction 𝒜).pred a；hb : (isLocallyFraction 𝒜).pred b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SetLike.mul_mem_graded`：SetLike.mul_mem_graded {S : Type*} [SetLike S R]
 [Mul R] [Add ι] {A : ι -> S} [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi in A 
i) (hj : gj …
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_add`：val_add : forall y1 y2 : HomogeneousLoc
alization 𝒜 x, (y1 + y2).val = y1.val + y2.val
· 使用定理 `Localization.add_mk`：add_mk (a b c d) : (mk a b : Localization M) + mk c
 d = mk ((b : R) * c + (d : R) * a) (b * d)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : ∀ x : U.unop, at x.1)
    (ha : (isLocallyFraction 𝒜).pred a) (hb : (isLocallyFraction 𝒜).pred b) :
    (isLocallyFraction 𝒜).pred (a + b) := fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, hwa, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, hwb, wb⟩
  refine
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨sb * ra + sa * rb,
        add_mem (add_comm jb ja ▸ mul_mem_graded sb_mem ra_mem : sb * ra ∈ 𝒜 (ja + jb))
          (mul_mem_graded sa_mem rb_mem)⟩,
      ⟨sa * sb, mul_mem_graded sa_mem sb_mem⟩, fun y ↦
        y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hwa ⟨y.1, y.2.1⟩) (hwb ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at wa wb
  simp [wa y hy.1, wb y hy.2, ext_iff_val, add_mk, add_comm (sa * rb)]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.neg_mem'** 
是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.Sec
tionSubring`。
形式化陈述：neg_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a : forall x : U.unop
, at x.1) (ha : (isLocallyFraction 𝒜).pred a) : (isLocallyFraction 𝒜).pred (-a)
参数：U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ；a : forall x : U.unop, at x.1；ha : (
isLocallyFraction 𝒜).pred a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousLocalization.val_neg`：val_neg {x} : forall y : HomogeneousLoc
alization 𝒜 x, (-y).val = -y.val
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Localization.neg_mk`：neg_mk (a b) : -(mk a b : Localization M) = mk (-a)
 b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a : ∀ x : U.unop, at x.1)
    (ha : (isLocallyFraction 𝒜).pred a) : (isLocallyFraction 𝒜).pred (-a) := fun x => by
  rcases ha x with ⟨V, m, i, j, ⟨r, r_mem⟩, ⟨s, s_mem⟩, nin, hy⟩
  refine ⟨V, m, i, j, ⟨-r, neg_mem r_mem⟩, ⟨s, s_mem⟩, nin, fun y => ?_⟩
  simp only [ext_iff_val, val_mk] at hy
  simp only [Pi.neg_apply, ext_iff_val, val_neg, hy, val_mk, neg_mk]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.mul_mem'** 
是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.Sec
tionSubring`。
形式化陈述：mul_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : forall x : U.un
op, at x.1) (ha : (isLocallyFraction 𝒜).pred a) (hb : (isLocallyFraction 𝒜).pred
 b) : (isLocallyFraction 𝒜).pred (a * b)
参数：U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ；a b : forall x : U.unop, at x.1；ha :
 (isLocallyFraction 𝒜).pred a；hb : (isLocallyFraction 𝒜).pred b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `SetLike.mul_mem_graded`：SetLike.mul_mem_graded {S : Type*} [SetLike S R]
 [Mul R] [Add ι] {A : ι -> S} [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi in A 
i) (hj : gj …
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_mul`：val_mul : forall y1 y2 : HomogeneousLoc
alization 𝒜 x, (y1 * y2).val = y1.val * y2.val
· 使用定理 `Localization.mk_mul`：mk_mul (a c : M) (b d : S) : mk a b * mk c d = mk (
a * c) (b * d)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : ∀ x : U.unop, at x.1)
    (ha : (isLocallyFraction 𝒜).pred a) (hb : (isLocallyFraction 𝒜).pred b) :
    (isLocallyFraction 𝒜).pred (a * b) := fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, hwa, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, hwb, wb⟩
  refine
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨ra * rb, SetLike.mul_mem_graded ra_mem rb_mem⟩,
      ⟨sa * sb, SetLike.mul_mem_graded sa_mem sb_mem⟩, fun y =>
      y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hwa ⟨y.1, y.2.1⟩) (hwb ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at wa wb
  simp [wa y hy.1, wb y hy.2, ext_iff_val, Localization.mk_mul]

end SectionSubring

section

open SectionSubring

variable {𝒜}

set_option backward.isDefEq.respectTransparency.types false in
/-- The functions satisfying `isLocallyFraction` form a subring of all dependent functions
`Π x : U, HomogeneousLocalization 𝒜 x`. -/
/-
**AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.sectionsSubring** 是 Mathli
b 中的一个定义，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf`。
形式化陈述：sectionsSubring (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) : Subring (fora
ll x : U.unop, at x.1) where carrier
参数：U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.mul_m
em'`：mul_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : forall x : U.uno
p, at x.1) (ha : (isLocallyFraction 𝒜).pred a) (hb : (isLocallyFr…
· 使用定理 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.one_m
em'`：one_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) : (isLocallyFraction 𝒜)
.pred (1 : forall x : U.unop, at x.1)
· 使用定理 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.add_m
em'`：add_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : forall x : U.uno
p, at x.1) (ha : (isLocallyFraction 𝒜).pred a) (hb : (isLocallyFr…
· 使用定理 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.zero_
mem'`：zero_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) : (isLocallyFraction 
𝒜).pred (0 : forall x : U.unop, at x.1)
· 使用定理 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.SectionSubring.neg_m
em'`：neg_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a : forall x : U.unop,
 at x.1) (ha : (isLocallyFraction 𝒜).pred a) : (isLocallyFraction…

--- 原说明 ---
The functions satisfying `isLocallyFraction` form a subring of all dependent fun
ctions
`Π x : U, HomogeneousLocalization 𝒜 x`.
-/
def sectionsSubring (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Subring (∀ x : U.unop, at x.1) where
  carrier := {f | (isLocallyFraction 𝒜).pred f}
  zero_mem' := zero_mem' U
  one_mem' := one_mem' U
  add_mem' := add_mem' U _ _
  neg_mem' := neg_mem' U _
  mul_mem' := mul_mem' U _ _

end

/-- The structure sheaf (valued in `Type`, not yet `CommRing`) is the subsheaf consisting of
functions satisfying `isLocallyFraction`. -/
/-
**AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.structureSheafInType** 是 M
athlib 中的一个定义，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf`。
形式化陈述：structureSheafInType : Sheaf (Type _) (ProjectiveSpectrum.top 𝒜)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure sheaf (valued in `Type`, not yet `CommRing`) is the subsheaf consi
sting of
functions satisfying `isLocallyFraction`.
-/
def structureSheafInType : Sheaf (Type _) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜)
/-
**AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.commRingStructureSheafInTy
peObj** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.StructureS
heaf`。
形式化陈述：commRingStructureSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
 : CommRing ((structureSheafInType 𝒜).1.obj U)
参数：U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commRingStructureSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    CommRing ((structureSheafInType 𝒜).1.obj U) :=
  (sectionsSubring U).toCommRing

/-- The structure presheaf, valued in `CommRing`, constructed by dressing up the `Type`-valued
/-
**AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.presheaf.** 是 Mathlib 中的一个
结构，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure presheaf. -/
@[simps obj_carrier]
/-
**AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.structurePresheafInCommRin
g** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
`。
形式化陈述：structurePresheafInCommRing : Presheaf CommRingCat (ProjectiveSpectrum.top
 𝒜) where obj U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure presheaf, valued in `CommRing`, constructed by dressing up the `Ty
pe`-valued
structure presheaf.
-/
def structurePresheafInCommRing : Presheaf CommRingCat (ProjectiveSpectrum.top 𝒜) where
  obj U := CommRingCat.of ((structureSheafInType 𝒜).1.obj U)
  map i := CommRingCat.ofHom
    { toFun := (structureSheafInType 𝒜).1.map i
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

/-- Some glue, verifying that the structure presheaf valued in `CommRing` agrees with the
`Type`-valued structure presheaf. -/
/-
**AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.structurePresheafCompForge
t** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
`。
形式化陈述：structurePresheafCompForget : structurePresheafInCommRing 𝒜 ⋙ forget CommR
ingCat ≅ (structureSheafInType 𝒜).1
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Some glue, verifying that the structure presheaf valued in `CommRing` agrees wit
h the
`Type`-valued structure presheaf.
-/
def structurePresheafCompForget :
    structurePresheafInCommRing 𝒜 ⋙ forget CommRingCat ≅ (structureSheafInType 𝒜).1 :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

end ProjectiveSpectrum.StructureSheaf

namespace ProjectiveSpectrum

open TopCat.Presheaf ProjectiveSpectrum.StructureSheaf Opens

/-- The structure sheaf on `Proj` 𝒜, valued in `CommRing`. -/
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf** 是 Mathlib 中的一个定义，位于
命名空间 `AlgebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：{A : Type u_1} →   {σ : Type u_2} →     [inst : CommRing A] →       [inst_
1 : SetLike σ A] →         [inst_2 : AddSubgroupClass σ A] →           (𝒜 : ℕ → 
σ) → [inst_3 : GradedRing 𝒜] → TopCat.Sheaf CommRingCat (ProjectiveSpectrum.top 
𝒜)
参数：𝒜 : ℕ → σ；ProjectiveSpectrum.top 𝒜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure sheaf on `Proj` 𝒜, valued in `CommRing`.
-/
def Proj.structureSheaf : Sheaf CommRingCat (ProjectiveSpectrum.top 𝒜) :=
  ⟨structurePresheafInCommRing 𝒜,
    (-- We check the sheaf condition under `forget CommRing`.
          isSheaf_iff_isSheaf_comp
          _ _).mpr
      (isSheaf_of_iso (structurePresheafCompForget 𝒜).symm (structureSheafInType 𝒜).property)⟩

end ProjectiveSpectrum

section

open AlgebraicGeometry.ProjectiveSpectrum ProjectiveSpectrum.StructureSheaf Opens

section
variable {U V : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (i : V ⟶ U)
    (s t : (Proj.structureSheaf 𝒜).1.obj V) (x : V.unop)

@[simp]
/-
**AlgebraicGeometry.Proj.res_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.
Proj`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRing 𝒜] {U V : (T
opologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜))ᵒᵖ} (i : V ⟶ U)   (s : ↑((Alge
braicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj V)) (x : ↥(Oppos
ite.unop U)),   ↑((CategoryTheory.ConcreteCategory.hom ((AlgebraicGeometry.Proje
ctiveSpectrum.Proj.structureSheaf 𝒜).obj.map i)) s)       x =     ↑s (i.unop x)
参数：𝒜 : ℕ → σ；TopologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜)；i : V ⟶ U；s : ↑(
(AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj V)；x : ↥(Op
posite.unop U)；(CategoryTheory.ConcreteCategory.hom ((AlgebraicGeometry.Projecti
veSpectrum.Proj.structureSheaf 𝒜).obj.map i)) s；i.unop x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
theorem Proj.res_apply (x) : ((Proj.structureSheaf 𝒜).1.map i s).1 x = s.1 (i.unop x) := rfl
/-
**AlgebraicGeometry.Proj.ext** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Proj`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRing 𝒜] {V : (Top
ologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜))ᵒᵖ}   (s t : ↑((AlgebraicGeometr
y.ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj V)), ↑s = ↑t → s = t
参数：𝒜 : ℕ → σ；TopologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜)；s t : ↑((Algebra
icGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj V)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
@[ext] theorem Proj.ext (h : s.1 = t.1) : s = t := Subtype.ext h
/-
**AlgebraicGeometry.Proj.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.
Proj`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRing 𝒜] {V : (Top
ologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜))ᵒᵖ}   (s t : ↑((AlgebraicGeometr
y.ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj V)) (x : ↥(Opposite.unop V))
,   ↑(s + t) x = ↑s x + ↑t x
参数：𝒜 : ℕ → σ；TopologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜)；s t : ↑((Algebra
icGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj V)；x : ↥(Opposite.u
nop V)；s + t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
@[simp] theorem Proj.add_apply : (s + t).1 x = s.1 x + t.1 x := rfl
/-
**AlgebraicGeometry.Proj.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.
Proj`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRing 𝒜] {V : (Top
ologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜))ᵒᵖ}   (s t : ↑((AlgebraicGeometr
y.ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj V)) (x : ↥(Opposite.unop V))
,   ↑(s * t) x = ↑s x * ↑t x
参数：𝒜 : ℕ → σ；TopologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜)；s t : ↑((Algebra
icGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj V)；x : ↥(Opposite.u
nop V)；s * t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
@[simp] theorem Proj.mul_apply : (s * t).1 x = s.1 x * t.1 x := rfl
/-
**AlgebraicGeometry.Proj.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.
Proj`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRing 𝒜] {V : (Top
ologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜))ᵒᵖ}   (s t : ↑((AlgebraicGeometr
y.ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj V)) (x : ↥(Opposite.unop V))
,   ↑(s - t) x = ↑s x - ↑t x
参数：𝒜 : ℕ → σ；TopologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜)；s t : ↑((Algebra
icGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj V)；x : ↥(Opposite.u
nop V)；s - t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
@[simp] theorem Proj.sub_apply : (s - t).1 x = s.1 x - t.1 x := rfl
/-
**AlgebraicGeometry.Proj.pow_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.
Proj`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRing 𝒜] {V : (Top
ologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜))ᵒᵖ}   (s : ↑((AlgebraicGeometry.
ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj V)) (x : ↥(Opposite.unop V)) (
n : ℕ),   ↑(s ^ n) x = ↑s x ^ n
参数：𝒜 : ℕ → σ；TopologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜)；s : ↑((Algebraic
Geometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj V)；x : ↥(Opposite.uno
p V)；n : ℕ；s ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
@[simp] theorem Proj.pow_apply (n : ℕ) : (s ^ n).1 x = s.1 x ^ n := rfl
/-
**AlgebraicGeometry.Proj.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry
.Proj`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRing 𝒜] {V : (Top
ologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜))ᵒᵖ} (x : ↥(Opposite.unop V)),   
↑0 x = 0
参数：𝒜 : ℕ → σ；TopologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜)；x : ↥(Opposite.u
nop V)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
@[simp] theorem Proj.zero_apply : (0 : (Proj.structureSheaf 𝒜).1.obj V).1 x = 0 := rfl
/-
**AlgebraicGeometry.Proj.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.
Proj`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRing 𝒜] {V : (Top
ologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜))ᵒᵖ} (x : ↥(Opposite.unop V)),   
↑1 x = 1
参数：𝒜 : ℕ → σ；TopologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜)；x : ↥(Opposite.u
nop V)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
@[simp] theorem Proj.one_apply : (1 : (Proj.structureSheaf 𝒜).1.obj V).1 x = 1 := rfl

end

/-- `Proj` of a graded ring as a `SheafedSpace` -/
/-
**AlgebraicGeometry.Proj.toSheafedSpace** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.Proj`。
形式化陈述：{A : Type u_1} →   {σ : Type u_2} →     [inst : CommRing A] →       [inst_
1 : SetLike σ A] →         [inst_2 : AddSubgroupClass σ A] → (𝒜 : ℕ → σ) → [Grad
edRing 𝒜] → AlgebraicGeometry.SheafedSpace CommRingCat
参数：𝒜 : ℕ → σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Proj` of a graded ring as a `SheafedSpace`
-/
def Proj.toSheafedSpace : SheafedSpace CommRingCat where
  carrier := TopCat.of (ProjectiveSpectrum 𝒜)
  presheaf := (Proj.structureSheaf 𝒜).1
  IsSheaf := (Proj.structureSheaf 𝒜).2

set_option backward.isDefEq.respectTransparency.types false in
/-- The ring homomorphism that takes a section of the structure sheaf of `Proj` on the open set `U`,
implemented as a subtype of dependent functions to localizations at homogeneous prime ideals, and
evaluates the section on the point corresponding to a given homogeneous prime ideal. -/
/-
**AlgebraicGeometry.openToLocalization** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try`。
形式化陈述：openToLocalization (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : ProjectiveS
pectrum.top 𝒜) (hx : x in U) : (Proj.structureSheaf 𝒜).1.obj (op U) ⟶ CommRingCa
t.of (at x)
参数：U : Opens (ProjectiveSpectrum.top 𝒜)；x : ProjectiveSpectrum.top 𝒜；hx : x in U
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism that takes a section of the structure sheaf of `Proj` on t
he open set `U`,
implemented as a subtype of dependent functions to localizations at homogeneous 
prime ideals, and
evaluates the section on the point corresponding to a given homogeneous prime id
eal.
-/
def openToLocalization (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : ProjectiveSpectrum.top 𝒜)
    (hx : x ∈ U) : (Proj.structureSheaf 𝒜).1.obj (op U) ⟶ CommRingCat.of (at x) :=
  CommRingCat.ofHom
  { toFun s := (s.1 ⟨x, hx⟩ :)
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl }

set_option backward.isDefEq.respectTransparency.types false in
/-- The ring homomorphism from the stalk of the structure sheaf of `Proj` at a point corresponding
to a homogeneous prime ideal `x` to the *homogeneous localization* at `x`,
formed by gluing the `openToLocalization` maps. -/
/-
**AlgebraicGeometry.stalkToFiberRingHom** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry`。
形式化陈述：stalkToFiberRingHom (x : ProjectiveSpectrum.top 𝒜) : (Proj.structureSheaf 
𝒜).presheaf.stalk x ⟶ CommRingCat.of (at x)
参数：x : ProjectiveSpectrum.top 𝒜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism from the stalk of the structure sheaf of `Proj` at a point
 corresponding
to a homogeneous prime ideal `x` to the *homogeneous localization* at `x`,
formed by gluing the `openToLocalization` maps.
-/
def stalkToFiberRingHom (x : ProjectiveSpectrum.top 𝒜) :
    (Proj.structureSheaf 𝒜).presheaf.stalk x ⟶ CommRingCat.of (at x) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (Proj.structureSheaf 𝒜).1)
    { pt := _
      ι :=
        { app := fun U =>
            openToLocalization 𝒜 ((OpenNhds.inclusion _).obj U.unop) x U.unop.2 } }

@[simp]
/-
**AlgebraicGeometry.germ_comp_stalkToFiberRingHom** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry`。
形式化陈述：germ_comp_stalkToFiberRingHom (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : 
ProjectiveSpectrum.top 𝒜) (hx : x in U) : (Proj.structureSheaf 𝒜).presheaf.germ 
U x hx ≫ stalkToFiberRingHom 𝒜 x = openToLocalization 𝒜 U x hx
参数：U : Opens (ProjectiveSpectrum.top 𝒜)；x : ProjectiveSpectrum.top 𝒜；hx : x in U
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
-/
theorem germ_comp_stalkToFiberRingHom
    (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : ProjectiveSpectrum.top 𝒜) (hx : x ∈ U) :
    (Proj.structureSheaf 𝒜).presheaf.germ U x hx ≫ stalkToFiberRingHom 𝒜 x =
      openToLocalization 𝒜 U x hx :=
  Limits.colimit.ι_desc _ _

@[simp]
/-
**AlgebraicGeometry.stalkToFiberRingHom_germ** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：stalkToFiberRingHom_germ (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : Proje
ctiveSpectrum.top 𝒜) (hx : x in U) (s : (Proj.structureSheaf 𝒜).1.obj (op U)) : 
stalkToFiberRingHom 𝒜 x ((Proj.structureSheaf 𝒜).presheaf.germ _ x hx s) = s.1 ⟨
x, hx⟩
参数：U : Opens (ProjectiveSpectrum.top 𝒜)；x : ProjectiveSpectrum.top 𝒜；hx : x in U
；s : (Proj.structureSheaf 𝒜).1.obj (op U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `RingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g ↔ ∀ (x_2 : α), f x_2 = g x
_2
· 使用定理 `CommRingCat.hom_ext_iff`：∀ {R S : CommRingCat} {f g : R ⟶ S}, f = g ↔ Co
mmRingCat.Hom.hom f = CommRingCat.Hom.hom g
· 使用定理 `AlgebraicGeometry.germ_comp_stalkToFiberRingHom`：germ_comp_stalkToFiberR
ingHom (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : ProjectiveSpectrum.top 𝒜) (hx
 : x in U) : (Proj.structureSheaf 𝒜).…
-/
theorem stalkToFiberRingHom_germ (U : Opens (ProjectiveSpectrum.top 𝒜))
    (x : ProjectiveSpectrum.top 𝒜) (hx : x ∈ U) (s : (Proj.structureSheaf 𝒜).1.obj (op U)) :
    stalkToFiberRingHom 𝒜 x ((Proj.structureSheaf 𝒜).presheaf.germ _ x hx s) = s.1 ⟨x, hx⟩ :=
  RingHom.ext_iff.1 (CommRingCat.hom_ext_iff.mp (germ_comp_stalkToFiberRingHom 𝒜 U x hx)) s

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.mem_basicOpen_den** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeomet
ry`。
形式化陈述：mem_basicOpen_den (x : ProjectiveSpectrum.top 𝒜) (f : HomogeneousLocalizat
ion.NumDenSameDeg 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl) : x in ProjectiveSp
ectrum.basicOpen 𝒜 f.den
参数：x : ProjectiveSpectrum.top 𝒜；f : HomogeneousLocalization.NumDenSameDeg 𝒜 x.as
HomogeneousIdeal.toIdeal.primeCompl。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProjectiveSpectrum.mem_basicOpen`：mem_basicOpen (f : A) (x : ProjectiveS
pectrum 𝒜) : x in basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
-/
theorem mem_basicOpen_den (x : ProjectiveSpectrum.top 𝒜)
    (f : HomogeneousLocalization.NumDenSameDeg 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl) :
    x ∈ ProjectiveSpectrum.basicOpen 𝒜 f.den := by
  rw [ProjectiveSpectrum.mem_basicOpen]
  exact f.den_mem

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a point `x` corresponding to a homogeneous prime ideal, there is a (dependent) function
such that, for any `f` in the homogeneous localization at `x`, it returns the obvious section in the
basic open set `D(f.den)`. -/
/-
**AlgebraicGeometry.sectionInBasicOpen** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try`。
形式化陈述：sectionInBasicOpen (x : ProjectiveSpectrum.top 𝒜) : forall f : Homogeneous
Localization.NumDenSameDeg 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl, (Proj.stru
ctureSheaf 𝒜).1.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f.den))
参数：x : ProjectiveSpectrum.top 𝒜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a point `x` corresponding to a homogeneous prime ideal, there is a (depend
ent) function
such that, for any `f` in the homogeneous localization at `x`, it returns the ob
vious section in the
basic open set `D(f.den)`.
-/
def sectionInBasicOpen (x : ProjectiveSpectrum.top 𝒜) :
    ∀ f : HomogeneousLocalization.NumDenSameDeg 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl,
    (Proj.structureSheaf 𝒜).1.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f.den)) :=
  fun f =>
  ⟨fun y => HomogeneousLocalization.mk ⟨f.deg, f.num, f.den, y.2⟩, fun y =>
    ⟨ProjectiveSpectrum.basicOpen 𝒜 f.den, y.2,
      ⟨𝟙 _, ⟨f.deg, ⟨f.num, f.den, _, fun _ => rfl⟩⟩⟩⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
open HomogeneousLocalization in
/-- Given any point `x` and `f` in the homogeneous localization at `x`, there is an element in the
stalk at `x` obtained by `sectionInBasicOpen`. This is the inverse of `stalkToFiberRingHom`.
-/
/-
**AlgebraicGeometry.homogeneousLocalizationToStalk** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry`。
形式化陈述：homogeneousLocalizationToStalk (x : ProjectiveSpectrum.top 𝒜) (y : at x) :
 (Proj.structureSheaf 𝒜).presheaf.stalk x
参数：x : ProjectiveSpectrum.top 𝒜；y : at x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.mem_basicOpen_den`：mem_basicOpen_den (x : ProjectiveSp
ectrum.top 𝒜) (f : HomogeneousLocalization.NumDenSameDeg 𝒜 x.asHomogeneousIdeal.
toIdeal.primeCompl) : x i…

--- 原说明 ---
Given any point `x` and `f` in the homogeneous localization at `x`, there is an 
element in the
stalk at `x` obtained by `sectionInBasicOpen`. This is the inverse of `stalkToFi
berRingHom`.
-/
def homogeneousLocalizationToStalk (x : ProjectiveSpectrum.top 𝒜) (y : at x) :
    (Proj.structureSheaf 𝒜).presheaf.stalk x := Quotient.liftOn' y (fun f =>
  (Proj.structureSheaf 𝒜).presheaf.germ _ x (mem_basicOpen_den _ x f) (sectionInBasicOpen _ x f))
  fun f g (e : f.embedding = g.embedding) ↦ by
    simp only [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk',
      IsLocalization.mk'_eq_iff_eq,
      IsLocalization.eq_iff_exists x.asHomogeneousIdeal.toIdeal.primeCompl] at e
    obtain ⟨⟨c, hc⟩, hc'⟩ := e
    apply (Proj.structureSheaf 𝒜).presheaf.germ_ext
      (ProjectiveSpectrum.basicOpen 𝒜 f.den.1 ⊓
        ProjectiveSpectrum.basicOpen 𝒜 g.den.1 ⊓ ProjectiveSpectrum.basicOpen 𝒜 c)
      ⟨⟨mem_basicOpen_den _ x f, mem_basicOpen_den _ x g⟩, hc⟩
      (homOfLE inf_le_left ≫ homOfLE inf_le_left) (homOfLE inf_le_left ≫ homOfLE inf_le_right)
    apply Subtype.ext
    ext ⟨t, ⟨htf, htg⟩, ht'⟩
    rw [Proj.res_apply, Proj.res_apply]
    simp only [sectionInBasicOpen, HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
      IsLocalization.mk'_eq_iff_eq]
    apply (IsLocalization.map_units (M := t.asHomogeneousIdeal.toIdeal.primeCompl)
      (Localization t.asHomogeneousIdeal.toIdeal.primeCompl) ⟨c, ht'⟩).mul_left_cancel
    rw [← map_mul, ← map_mul, hc']
/-
**AlgebraicGeometry.homogeneousLocalizationToStalk_stalkToFiberRingHom** 是 Mathl
ib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：homogeneousLocalizationToStalk_stalkToFiberRingHom (x z) : homogeneousLoca
lizationToStalk 𝒜 x (stalkToFiberRingHom 𝒜 x z) = z
参数：x z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `TopCat.Presheaf.exists_germ_eq`：exists_germ_eq (F : X.Presheaf C) {x : X
} (t : ToType (stalk.{v, u} F x)) : exists (U : Opens X) (m : x in U) (s : ToTyp
e (F.obj (op U))), F…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.stalkToFiberRingHom_germ`：stalkToFiberRingHom_germ (U 
: Opens (ProjectiveSpectrum.top 𝒜)) (x : ProjectiveSpectrum.top 𝒜) (hx : x in U)
 (s : (Proj.structureSheaf 𝒜).1.…
· 使用定理 `AlgebraicGeometry.mem_basicOpen_den`：mem_basicOpen_den (x : ProjectiveSp
ectrum.top 𝒜) (f : HomogeneousLocalization.NumDenSameDeg 𝒜 x.asHomogeneousIdeal.
toIdeal.primeCompl) : x i…
· 使用定理 `AlgebraicGeometry.homogeneousLocalizationToStalk.eq_1`：∀ {A : Type u_1} 
{σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupC
lass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRin…
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.liftOn'_mk''`：∀ {α : Sort u_1} {φ : Sort u_4} {s₁ : Setoid α} (
f : α → φ) (h : ∀ (a b : α), s₁ a b → f a = f b) (x : α),   (Quotient.mk'' x).li
ftOn' f h =…
· 使用定理 `TopCat.Presheaf.germ_ext`：germ_ext (F : X.Presheaf C) {U V : Opens X} {x
 : X} {hxU : x in U} {hxV : x in V} (W : Opens X) (hxW : x in W) (iWU : W ⟶ U) (
iWV : W ⟶ V) {…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用定理 `AlgebraicGeometry.Proj.res_apply`：∀ {A : Type u_1} {σ : Type u_2} [inst 
: CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ → σ)
   [inst_3 : GradedRin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homogeneousLocalizationToStalk_stalkToFiberRingHom (x z) :
    homogeneousLocalizationToStalk 𝒜 x (stalkToFiberRingHom 𝒜 x z) = z := by
  obtain ⟨U, hxU, s, rfl⟩ := (Proj.structureSheaf 𝒜).presheaf.exists_germ_eq z
  change homogeneousLocalizationToStalk 𝒜 x ((stalkToFiberRingHom 𝒜 x).hom
      (((Proj.structureSheaf 𝒜).presheaf.germ U x hxU) s)) =
    ((Proj.structureSheaf 𝒜).presheaf.germ U x hxU) s
  obtain ⟨V, hxV, i, n, a, b, h, e⟩ := s.2 ⟨x, hxU⟩
  simp only [Subtype.forall, apply_mk] at e
  rw [stalkToFiberRingHom_germ, homogeneousLocalizationToStalk, e x hxV, Quotient.liftOn'_mk'']
  refine Presheaf.germ_ext (C := CommRingCat) _ V hxV (homOfLE <| fun _ h' ↦ h ⟨_, h'⟩) i ?_
  change ((Proj.structureSheaf 𝒜).presheaf.map (homOfLE <| fun _ h' ↦ h ⟨_, h'⟩).op) _ =
    ((Proj.structureSheaf 𝒜).presheaf.map i.op) s
  apply Subtype.ext
  ext ⟨t, ht⟩
  rw [Proj.res_apply, Proj.res_apply]
  simp [sectionInBasicOpen, HomogeneousLocalization.val_mk, Localization.mk_eq_mk', e t ht]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.stalkToFiberRingHom_homogeneousLocalizationToStalk** 是 Mathl
ib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：stalkToFiberRingHom_homogeneousLocalizationToStalk (x z) : stalkToFiberRin
gHom 𝒜 x (homogeneousLocalizationToStalk 𝒜 x z) = z
参数：x z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.mk''_surjective`：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Sur
jective Quotient.mk''
· 使用定理 `AlgebraicGeometry.mem_basicOpen_den`：mem_basicOpen_den (x : ProjectiveSp
ectrum.top 𝒜) (f : HomogeneousLocalization.NumDenSameDeg 𝒜 x.asHomogeneousIdeal.
toIdeal.primeCompl) : x i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.homogeneousLocalizationToStalk.eq_1`：∀ {A : Type u_1} 
{σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupC
lass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRin…
· 使用定理 `Quotient.liftOn'_mk''`：∀ {α : Sort u_1} {φ : Sort u_4} {s₁ : Setoid α} (
f : α → φ) (h : ∀ (a b : α), s₁ a b → f a = f b) (x : α),   (Quotient.mk'' x).li
ftOn' f h =…
· 使用定理 `AlgebraicGeometry.stalkToFiberRingHom_germ`：stalkToFiberRingHom_germ (U 
: Opens (ProjectiveSpectrum.top 𝒜)) (x : ProjectiveSpectrum.top 𝒜) (hx : x in U)
 (s : (Proj.structureSheaf 𝒜).1.…
· 使用定理 `AlgebraicGeometry.sectionInBasicOpen.eq_1`：∀ {A : Type u_1} {σ : Type u_
2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupClass σ A] (𝒜
 : ℕ → σ)   [inst_3 : GradedRin…
-/
lemma stalkToFiberRingHom_homogeneousLocalizationToStalk (x z) :
    stalkToFiberRingHom 𝒜 x (homogeneousLocalizationToStalk 𝒜 x z) = z := by
  obtain ⟨z, rfl⟩ := Quotient.mk''_surjective z
  rw [homogeneousLocalizationToStalk, Quotient.liftOn'_mk'',
    stalkToFiberRingHom_germ, sectionInBasicOpen]

set_option backward.isDefEq.respectTransparency.types false in
/-- Using `homogeneousLocalizationToStalk`, we construct a ring isomorphism between stalk at `x`
and homogeneous localization at `x` for any point `x` in `Proj`. -/
/-
**AlgebraicGeometry.Proj.stalkIso'** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.
Proj`。
形式化陈述：{A : Type u_1} →   {σ : Type u_2} →     [inst : CommRing A] →       [inst_
1 : SetLike σ A] →         [inst_2 : AddSubgroupClass σ A] →           (𝒜 : ℕ → 
σ) →             [inst_3 : GradedRing 𝒜] →               (x : ↑(ProjectiveSpectr
um.top 𝒜)) →                 ↑((AlgebraicGeometry.ProjectiveSpectrum.Proj.struct
ureSheaf 𝒜).presheaf.stalk x) ≃+*                   HomogeneousLocalization.AtPr
ime 𝒜 x.asHomogeneousIdeal.toIdeal
参数：𝒜 : ℕ → σ；x : ↑(ProjectiveSpectrum.top 𝒜)；(AlgebraicGeometry.ProjectiveSpectr
um.Proj.structureSheaf 𝒜).presheaf.stalk x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.homogeneousLocalizationToStalk_stalkToFiberRingHom`：ho
mogeneousLocalizationToStalk_stalkToFiberRingHom (x z) : homogeneousLocalization
ToStalk 𝒜 x (stalkToFiberRingHom 𝒜 x z) = z
· 使用引理 `AlgebraicGeometry.stalkToFiberRingHom_homogeneousLocalizationToStalk`：st
alkToFiberRingHom_homogeneousLocalizationToStalk (x z) : stalkToFiberRingHom 𝒜 x
 (homogeneousLocalizationToStalk 𝒜 x z) = z

--- 原说明 ---
Using `homogeneousLocalizationToStalk`, we construct a ring isomorphism between 
stalk at `x`
and homogeneous localization at `x` for any point `x` in `Proj`.
-/
def Proj.stalkIso' (x : ProjectiveSpectrum.top 𝒜) :
    (Proj.structureSheaf 𝒜).presheaf.stalk x ≃+* at x where
  __ := (stalkToFiberRingHom _ x).hom
  invFun := homogeneousLocalizationToStalk 𝒜 x
  left_inv := homogeneousLocalizationToStalk_stalkToFiberRingHom 𝒜 x
  right_inv := stalkToFiberRingHom_homogeneousLocalizationToStalk 𝒜 x

@[simp]
/-
**AlgebraicGeometry.Proj.stalkIso'_germ** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.Proj`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRing 𝒜] (U : Topo
logicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜)) (x : ↑(ProjectiveSpectrum.top 𝒜)
)   (hx : x ∈ U) (s : ↑((AlgebraicGeometry.ProjectiveSpectrum.Proj.structureShea
f 𝒜).obj.obj (Opposite.op U))),   (AlgebraicGeometry.Proj.stalkIso' 𝒜 x)       (
(CategoryTheory.ConcreteCategory.hom           ((AlgebraicGeometry.ProjectiveSpe
ctrum.Proj.structureSheaf 𝒜).presheaf.germ U x hx))         s) =     ↑s ⟨x, hx⟩
参数：𝒜 : ℕ → σ；U : TopologicalSpace.Opens ↑(ProjectiveSpectrum.top 𝒜)；x : ↑(Projec
tiveSpectrum.top 𝒜)；hx : x ∈ U；s : ↑((AlgebraicGeometry.ProjectiveSpectrum.Proj.
structureSheaf 𝒜).obj.obj (Opposite.op U))；AlgebraicGeometry.Proj.stalkIso' 𝒜 x；
(CategoryTheory.ConcreteCategory.hom           ((AlgebraicGeometry.ProjectiveSpe
ctrum.Proj.structureSheaf 𝒜).presheaf.germ U x hx))         s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AlgebraicGeometry.stalkToFiberRingHom_germ`：stalkToFiberRingHom_germ (U 
: Opens (ProjectiveSpectrum.top 𝒜)) (x : ProjectiveSpectrum.top 𝒜) (hx : x in U)
 (s : (Proj.structureSheaf 𝒜).1.…
-/
theorem Proj.stalkIso'_germ (U : Opens (ProjectiveSpectrum.top 𝒜))
    (x : ProjectiveSpectrum.top 𝒜) (hx : x ∈ U) (s : (Proj.structureSheaf 𝒜).1.obj (op U)) :
    Proj.stalkIso' 𝒜 x ((Proj.structureSheaf 𝒜).presheaf.germ _ x hx s) = s.1 ⟨x, hx⟩ :=
  stalkToFiberRingHom_germ 𝒜 U x hx s

@[simp]
/-
**AlgebraicGeometry.Proj.stalkIso'_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Proj`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRing 𝒜] (x : ↑(Pr
ojectiveSpectrum.top 𝒜))   (f : HomogeneousLocalization.NumDenSameDeg 𝒜 x.asHomo
geneousIdeal.toIdeal.primeCompl),   (AlgebraicGeometry.Proj.stalkIso' 𝒜 x).symm 
(HomogeneousLocalization.mk f) =     (CategoryTheory.ConcreteCategory.hom       
  ((AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf.germ   
        (ProjectiveSpectrum.basicOpen 𝒜 ↑f.den) x ⋯))       (AlgebraicGeometry.s
ectionInBasicOpen 𝒜 x f)
参数：𝒜 : ℕ → σ；x : ↑(ProjectiveSpectrum.top 𝒜)；f : HomogeneousLocalization.NumDenS
ameDeg 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl；AlgebraicGeometry.Proj.stalkIso
' 𝒜 x；HomogeneousLocalization.mk f；CategoryTheory.ConcreteCategory.hom         (
(AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf.germ      
     (ProjectiveSpectrum.basicOpen 𝒜 ↑f.den) x ⋯)；AlgebraicGeometry.sectionInBas
icOpen 𝒜 x f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
-/
theorem Proj.stalkIso'_symm_mk (x) (f) :
    (Proj.stalkIso' 𝒜 x).symm (.mk f) = (Proj.structureSheaf 𝒜).presheaf.germ _
      x (mem_basicOpen_den _ x f) (sectionInBasicOpen _ x f) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `Proj` of a graded ring as a `LocallyRingedSpace` -/
/-
**AlgebraicGeometry.Proj.toLocallyRingedSpace** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Proj`。
形式化陈述：{A : Type u_1} →   {σ : Type u_2} →     [inst : CommRing A] →       [inst_
1 : SetLike σ A] →         [inst_2 : AddSubgroupClass σ A] → (𝒜 : ℕ → σ) → [Grad
edRing 𝒜] → AlgebraicGeometry.LocallyRingedSpace
参数：𝒜 : ℕ → σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Proj` of a graded ring as a `LocallyRingedSpace`
-/
def Proj.toLocallyRingedSpace : LocallyRingedSpace :=
  { Proj.toSheafedSpace 𝒜 with
    isLocalRing := fun x =>
      @RingEquiv.isLocalRing _ _ _ (show IsLocalRing (at x) from inferInstance) _
        (Proj.stalkIso' 𝒜 x).symm }

end

end AlgebraicGeometry

