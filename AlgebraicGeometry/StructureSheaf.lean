/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.DepRewrite
public import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# The structure sheaf on `PrimeSpectrum R`.

We define the structure sheaf on `TopCat.of (PrimeSpectrum R)`, for an `R`-module `M` and prove
basic properties about it. We define this as a subsheaf of the sheaf of dependent functions into the
localizations, cut out by the condition that the function must be locally equal to a quotient of
an element of `M` by an element of `R`.

Because the condition "is equal to a fraction" passes to smaller open subsets,
the subset of functions satisfying this condition is automatically a subpresheaf.
Because the condition "is locally equal to a fraction" is local,
it is also a subsheaf.

(It may be helpful to refer back to `Mathlib/Topology/Sheaves/SheafOfFunctions.lean`,
where we show that dependent functions into any type family form a sheaf,
and also `Mathlib/Topology/Sheaves/LocalPredicate.lean`, where we characterise the predicates
which pick out sub-presheaves and sub-sheaves of these sheaves.)

When `M = R`, the structure sheaf is furthermore a sheaf of commutative rings, which we bundle as
`structureSheaf : Sheaf CommRingCat (PrimeSpectrum.Top R)`.

We then obtain two key descriptions of the structure sheaf. We show that the stalks `Mₓ` is the
localization of `M` at the prime corresponding to `x`, and we show that the sections `Γ(M, D(f))`
is the localization of `M` away from `f`.

Note that the results of this file are packaged into schemes and sheaf of modules in later files,
and one usually should not directly use the results in this file to respect the abstraction
boundaries.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/


universe u

noncomputable section

variable {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A]

open TopCat

open TopologicalSpace CategoryTheory Opposite

open PrimeSpectrum (basicOpen)

namespace AlgebraicGeometry

@[expose] public section Public

variable (R) in
/-- The prime spectrum as an object of `TopCat`. -/
/-
**AlgebraicGeometry.PrimeSpectrum.Top** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeomet
ry.PrimeSpectrum`。
形式化陈述：(R : Type u) → [CommRing R] → TopCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prime spectrum as an object of `TopCat`.
-/
def PrimeSpectrum.Top : TopCat := TopCat.of (PrimeSpectrum R)

namespace StructureSheaf

variable {P : PrimeSpectrum.Top R}

set_option backward.isDefEq.respectTransparency.types false in
variable (M P) in
/-- The type family over `PrimeSpectrum R` consisting of the localization over each point. -/
/-
**AlgebraicGeometry.StructureSheaf.Localizations** 是 Mathlib 中的一个缩写定义，位于命名空间 `Al
gebraicGeometry.StructureSheaf`。
形式化陈述：Localizations : Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type family over `PrimeSpectrum R` consisting of the localization over each 
point.
-/
abbrev Localizations : Type u := LocalizedModule P.asIdeal.primeCompl M

/-- The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` in each of the stalks (which are localizations at various prime ideals).
-/
/-
**AlgebraicGeometry.StructureSheaf.IsFraction** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.StructureSheaf`。
形式化陈述：IsFraction {U : Opens (PrimeSpectrum.Top R)} (f : Π x : U, Localizations M
 x.1) : Prop
参数：PrimeSpectrum.Top R；f : Π x : U, Localizations M x.1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predicate saying that a dependent function on an open `U` is realised as a f
ixed fraction
`r / s` in each of the stalks (which are localizations at various prime ideals).
-/
def IsFraction {U : Opens (PrimeSpectrum.Top R)} (f : Π x : U, Localizations M x.1) : Prop :=
  ∃ r s, ∀ x : U, ∃ hs : s ∉ x.1.asIdeal, f x = LocalizedModule.mk r ⟨s, hs⟩

variable (R M) in
/-- The predicate `IsFraction` is "prelocal",
in the sense that if it holds on `U` it holds on any open subset `V` of `U`.
-/
/-
**AlgebraicGeometry.StructureSheaf.isFractionPrelocal** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.StructureSheaf`。
形式化陈述：isFractionPrelocal : PrelocalPredicate (Localizations (R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predicate `IsFraction` is "prelocal",
in the sense that if it holds on `U` it holds on any open subset `V` of `U`.
-/
def isFractionPrelocal : PrelocalPredicate (Localizations (R := R) M) where
  pred {_} f := IsFraction f
  res := by rintro V U i f ⟨r, s, w⟩; exact ⟨r, s, fun x => w (i x)⟩

variable (R M) in
/-- We will define the structure sheaf as
the subsheaf of all dependent functions in `Π x : U, Localizations R x`
consisting of those functions which can locally be expressed as a ratio of
(the images in the localization of) elements of `R`.

Quoting Hartshorne:

For an open set $U ⊆ Spec A$, we define $𝒪(U)$ to be the set of functions
$s : U → ⨆_{𝔭 ∈ U} A_𝔭$, such that $s(𝔭) ∈ A_𝔭$ for each $𝔭$,
and such that $s$ is locally a quotient of elements of $A$:
to be precise, we require that for each $𝔭 ∈ U$, there is a neighborhood $V$ of $𝔭$,
contained in $U$, and elements $a, f ∈ A$, such that for each $𝔮 ∈ V, f ∉ 𝔮$,
and $s(𝔮) = a/f$ in $A_𝔮$.

Now Hartshorne had the disadvantage of not knowing about dependent functions,
so we replace his circumlocution about functions into a disjoint union with
`Π x : U, Localizations x`.
-/
/-
**AlgebraicGeometry.StructureSheaf.isLocallyFraction** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.StructureSheaf`。
形式化陈述：isLocallyFraction : LocalPredicate (Localizations (R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We will define the structure sheaf as
the subsheaf of all dependent functions in `Π x : U, Localizations R x`
consisting of those functions which can locally be expressed as a ratio of
(the images in the localization of) elements of `R`.

Quoting Hartshorne:

For an open set $U ⊆ Spec A$, we define $𝒪(U)$ to be the set of functions
$s : U → ⨆_{𝔭 ∈ U} A_𝔭$, such that $s(𝔭) ∈ A_𝔭$ for each $𝔭$,
and such that $s$ is locally a quotient of elements of $A$:
to be precise, we require that for each $𝔭 ∈ U$, there is a neighborhood $V$ of 
$𝔭$,
contained in $U$, and elements $a, f ∈ A$, such that for each $𝔮 ∈ V, f ∉ 𝔮$,
and $s(𝔮) = a/f$ in $A_𝔮$.

Now Hartshorne had the disadvantage of not knowing about dependent functions,
so we replace his circumlocution about functions into a disjoint union with
`Π x : U, Localizations x`.
-/
def isLocallyFraction : LocalPredicate (Localizations (R := R) M) :=
  (isFractionPrelocal R M).sheafify

set_option backward.isDefEq.respectTransparency.types false in
variable (M) in
/-- The functions satisfying `isLocallyFraction` form a submodule. -/
/-
**AlgebraicGeometry.StructureSheaf.sectionsSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.StructureSheaf`。
形式化陈述：sectionsSubmodule (U : (Opens (PrimeSpectrum.Top R))) : Submodule R (Π x :
 U, Localizations M x.1) where carrier
参数：U : (Opens (PrimeSpectrum.Top R))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functions satisfying `isLocallyFraction` form a submodule.
-/
def sectionsSubmodule (U : (Opens (PrimeSpectrum.Top R))) :
    Submodule R (Π x : U, Localizations M x.1) where
  carrier := { f | (isLocallyFraction R M).pred f }
  add_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, sb • ra + sa • rb, sa * sb, fun x ↦ ?_⟩
    obtain ⟨hsax, hsa⟩ := wa ⟨x.1, x.2.1⟩
    obtain ⟨hsbx, hsb⟩ := wb ⟨x.1, x.2.2⟩
    exact ⟨x.1.asIdeal.primeCompl.mul_mem hsax hsbx,
      congr($hsa + $hsb).trans (LocalizedModule.mk_add_mk ..)⟩
  zero_mem' x := ⟨U, x.2, 𝟙 _, 0, 1, fun y ↦ by simp [Ideal.IsPrime.one_notMem]⟩
  smul_mem' r {a} ha x := by
    obtain ⟨V, m, i, ra, sa, wa⟩ := ha x
    exact ⟨V, m, i, r • ra, sa, fun x ↦ ⟨(wa x).1,
      congr(r • $((wa x).2)).trans (LocalizedModule.smul'_mk ..)⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
variable (A) in
/-- The functions satisfying `isLocallyFraction` form a subalgebra. -/
/-
**AlgebraicGeometry.StructureSheaf.sectionsSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.StructureSheaf`。
形式化陈述：sectionsSubalgebra (U : (Opens (PrimeSpectrum.Top R))) : Subalgebra R (Π x
 : U, Localizations A x.1) where __
参数：U : (Opens (PrimeSpectrum.Top R))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functions satisfying `isLocallyFraction` form a subalgebra.
-/
def sectionsSubalgebra (U : (Opens (PrimeSpectrum.Top R))) :
    Subalgebra R (Π x : U, Localizations A x.1) where
  __ := sectionsSubmodule A U
  mul_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ra * rb, sa * sb, fun x ↦ ?_⟩
    obtain ⟨hsax, hsa⟩ := wa ⟨x.1, x.2.1⟩
    obtain ⟨hsbx, hsb⟩ := wb ⟨x.1, x.2.2⟩
    exact ⟨x.1.asIdeal.primeCompl.mul_mem hsax hsbx,
      congr($hsa * $hsb).trans (LocalizedModule.mk_mul_mk ..)⟩
  algebraMap_mem' r x :=
    ⟨U, x.2, 𝟙 _, algebraMap R A r, 1, fun y ↦ ⟨by simp [Ideal.IsPrime.one_notMem], rfl⟩⟩

set_option backward.isDefEq.respectTransparency false in
variable (M) in
/-- The functions satisfying `isLocallyFraction` form a submodule. -/
/-
**AlgebraicGeometry.StructureSheaf.sectionsSubalgebraSubmodule** 是 Mathlib 中的一个定
义，位于命名空间 `AlgebraicGeometry.StructureSheaf`。
形式化陈述：sectionsSubalgebraSubmodule (U : (Opens (PrimeSpectrum.Top R))) : Submodul
e (sectionsSubalgebra R U) (Π x : U, Localizations M x.1) where __
参数：U : (Opens (PrimeSpectrum.Top R))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functions satisfying `isLocallyFraction` form a submodule.
-/
def sectionsSubalgebraSubmodule (U : (Opens (PrimeSpectrum.Top R))) :
    Submodule (sectionsSubalgebra R U) (Π x : U, Localizations M x.1) where
  __ := sectionsSubmodule M U
  smul_mem' r {a} ha x := by
    obtain ⟨V, hxV, hVU, rx, rs, hr⟩ := r.2 x
    obtain ⟨W, hxW, hWU, ax, as, ha⟩ := ha x
    refine ⟨V ⊓ W, ⟨hxV, hxW⟩, homOfLE (inf_le_left.trans hVU.le), rx • ax, as * rs, fun y ↦ ?_⟩
    obtain ⟨hrsy, hry⟩ := hr ⟨y.1, y.2.1⟩
    obtain ⟨hasy, hay⟩ := ha ⟨y.1, y.2.2⟩
    exact ⟨y.1.asIdeal.primeCompl.mul_mem hasy hrsy, congr($hry • $hay)⟩

end StructureSheaf

open StructureSheaf

variable (R M) in
/-- The structure sheaf (valued in `Type`, not yet `CommRingCat`) is the subsheaf consisting of
functions satisfying `isLocallyFraction`. -/
/-
**AlgebraicGeometry.structureSheafInType** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry`。
形式化陈述：structureSheafInType : Sheaf (Type u) (PrimeSpectrum.Top R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure sheaf (valued in `Type`, not yet `CommRingCat`) is the subsheaf co
nsisting of
functions satisfying `isLocallyFraction`.
-/
def structureSheafInType : Sheaf (Type u) (PrimeSpectrum.Top R) :=
  subsheafToTypes (isLocallyFraction R M)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    AddCommGroup ((structureSheafInType R M).obj.obj U) :=
  (sectionsSubmodule M U.unop).toAddSubgroup.toAddCommGroup
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Module R ((structureSheafInType R M).obj.obj U) :=
  (sectionsSubmodule M U.unop).module
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    CommRing ((structureSheafInType R A).obj.obj U) :=
  (sectionsSubalgebra A U.unop).toCommRing
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Algebra R ((structureSheafInType R A).obj.obj U) :=
  (sectionsSubalgebra A U.unop).algebra

local notation "Γ(" M ", " U ")" =>
  (Functor.obj (ObjectProperty.FullSubcategory.obj (structureSheafInType _ M))) (Opposite.op U)

@[simp]
/-
**AlgebraicGeometry.structureSheafInType.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.structureSheafInType`。
形式化陈述：∀ {R M : Type u} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _
root_.Module R M]   {U : TopologicalSpace.Opens ↑(AlgebraicGeometry.PrimeSpectru
m.Top R)}   (s t : (AlgebraicGeometry.structureSheafInType R M).obj.obj (Opposit
e.op U)) (x : ↥U), ↑(s + t) x = ↑s x + ↑t x
参数：AlgebraicGeometry.PrimeSpectrum.Top R；s t : (AlgebraicGeometry.structureSheaf
InType R M).obj.obj (Opposite.op U)；x : ↥U；s + t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma structureSheafInType.add_apply {U : Opens (PrimeSpectrum.Top R)} (s t : Γ(M, U)) (x : U) :
  (s + t).1 x = s.1 x + t.1 x := rfl

@[simp]
/-
**AlgebraicGeometry.structureSheafInType.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.structureSheafInType`。
形式化陈述：∀ {R A : Type u} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algeb
ra R A]   {U : TopologicalSpace.Opens ↑(AlgebraicGeometry.PrimeSpectrum.Top R)} 
  (s t : (AlgebraicGeometry.structureSheafInType R A).obj.obj (Opposite.op U)) (
x : ↥U), ↑(s * t) x = ↑s x * ↑t x
参数：AlgebraicGeometry.PrimeSpectrum.Top R；s t : (AlgebraicGeometry.structureSheaf
InType R A).obj.obj (Opposite.op U)；x : ↥U；s * t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma structureSheafInType.mul_apply {U : Opens (PrimeSpectrum.Top R)} (s t : Γ(A, U)) (x : U) :
  (s * t).1 x = s.1 x * t.1 x := rfl

@[simp]
/-
**AlgebraicGeometry.structureSheafInType.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.structureSheafInType`。
形式化陈述：∀ {R M : Type u} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _
root_.Module R M]   {U : TopologicalSpace.Opens ↑(AlgebraicGeometry.PrimeSpectru
m.Top R)} (r : R)   (s : (AlgebraicGeometry.structureSheafInType R M).obj.obj (O
pposite.op U)) (x : ↥U), ↑(r • s) x = r • ↑s x
参数：AlgebraicGeometry.PrimeSpectrum.Top R；r : R；s : (AlgebraicGeometry.structureS
heafInType R M).obj.obj (Opposite.op U)；x : ↥U；r • s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma structureSheafInType.smul_apply {U : Opens (PrimeSpectrum.Top R)}
    (r : R) (s : Γ(M, U)) (x : U) :
  (r • s).1 x = r • s.1 x := rfl

variable (R M) in
/-- The structure presheaf, valued in `ModuleCat`, constructed by dressing up the `Type`-valued
/-
**AlgebraicGeometry.presheaf.** 是 Mathlib 中的一个结构，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure presheaf. -/
@[simps obj_carrier]
/-
**AlgebraicGeometry.structurePresheafInModuleCat** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry`。
形式化陈述：structurePresheafInModuleCat : Presheaf (ModuleCat R) (PrimeSpectrum.Top R
) where obj U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure presheaf, valued in `ModuleCat`, constructed by dressing up the `T
ype`-valued
structure presheaf.
-/
def structurePresheafInModuleCat : Presheaf (ModuleCat R) (PrimeSpectrum.Top R) where
  obj U := ModuleCat.of R ((structureSheafInType R M).1.obj U)
  map i := ModuleCat.ofHom
    { toFun := (structureSheafInType R M).1.map i
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

variable (R) in
/-- The structure presheaf, valued in `CommRingCat`, constructed by dressing up the `Type`-valued
/-
**AlgebraicGeometry.presheaf.** 是 Mathlib 中的一个结构，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure presheaf. -/
@[simps obj_carrier]
/-
**AlgebraicGeometry.structurePresheafInCommRingCat** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry`。
形式化陈述：structurePresheafInCommRingCat : Presheaf CommRingCat (PrimeSpectrum.Top R
) where obj U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure presheaf, valued in `CommRingCat`, constructed by dressing up the 
`Type`-valued
structure presheaf.
-/
def structurePresheafInCommRingCat : Presheaf CommRingCat (PrimeSpectrum.Top R) where
  obj U := .of ((structureSheafInType R R).1.obj U)
  map i := CommRingCat.ofHom
    { toFun := (structureSheafInType R R).1.map i
      map_add' _ _ := rfl
      map_mul' _ _ := rfl
      map_one' := rfl
      map_zero' := rfl }
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Module ((structureSheafInType R R).obj.obj U) ((structureSheafInType R M).obj.obj U) :=
  inferInstanceAs (Module (sectionsSubalgebra R _) (sectionsSubalgebraSubmodule M _))
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    IsScalarTower R ((structureSheafInType R R).obj.obj U) ((structureSheafInType R M).obj.obj U) :=
  .of_algebraMap_smul fun r m ↦ Subtype.ext <| funext fun x ↦
    IsScalarTower.algebraMap_smul (Localizations R x.1) r (m.1 x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (R M) in
/-- The structure sheaf of a module as a presheaf of modules on `Spec R`.
We will later package this into a `Scheme.Modules` in `Tilde.lean`. -/
/-
**AlgebraicGeometry.moduleStructurePresheaf** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry`。
形式化陈述：moduleStructurePresheaf : PresheafOfModules (structurePresheafInCommRingCa
t R ⋙ forget₂ _ _)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure sheaf of a module as a presheaf of modules on `Spec R`.
We will later package this into a `Scheme.Modules` in `Tilde.lean`.
-/
def moduleStructurePresheaf : PresheafOfModules (structurePresheafInCommRingCat R ⋙ forget₂ _ _) :=
  letI (X : (Opens ↑(PrimeSpectrum.Top R))ᵒᵖ) :
    Module ↑((structurePresheafInCommRingCat R ⋙ forget₂ CommRingCat RingCat).obj X)
      ↑((structurePresheafInModuleCat R M ⋙ forget₂ (ModuleCat R) Ab).obj X) := by
    dsimp; infer_instance
  .ofPresheaf (structurePresheafInModuleCat R M ⋙ forget₂ _ _) fun X Y f r m ↦ rfl

variable (R) in
/-- Some glue, verifying that the structure presheaf valued in `CommRingCat` agrees
with the `Type`-valued structure presheaf. -/
/-
**AlgebraicGeometry.structurePresheafCompForget** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：structurePresheafCompForget : structurePresheafInCommRingCat R ⋙ forget Co
mmRingCat ≅ (structureSheafInType R R).1
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Some glue, verifying that the structure presheaf valued in `CommRingCat` agrees
with the `Type`-valued structure presheaf.
-/
def structurePresheafCompForget :
    structurePresheafInCommRingCat R ⋙ forget CommRingCat ≅ (structureSheafInType R R).1 :=
  NatIso.ofComponents fun _ => Iso.refl _

open TopCat.Presheaf


open TopCat.Presheaf

namespace StructureSheaf

@[simp]
/-
**AlgebraicGeometry.StructureSheaf.res_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.StructureSheaf`。
形式化陈述：res_apply (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U) (s : Γ(M, U)) (x
 : V) : ((structureSheafInType R M).1.map i.op s).1 x = s.1 (i x)
参数：U V : Opens (PrimeSpectrum.Top R)；i : V ⟶ U；s : Γ(M, U)；x : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem res_apply (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U)
    (s : Γ(M, U)) (x : V) : ((structureSheafInType R M).1.map i.op s).1 x = s.1 (i x) :=
  rfl

/-- The section of `structureSheaf R` on an open `U` sending each `x ∈ U` to the element
`f/g` in the localization of `R` at `x`. -/
/-
**AlgebraicGeometry.StructureSheaf.const** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.StructureSheaf`。
形式化陈述：const (f : M) (g : R) (U : Opens (PrimeSpectrum.Top R)) (hu : U <= basicOp
en g) : Γ(M, U)
参数：f : M；g : R；U : Opens (PrimeSpectrum.Top R)；hu : U <= basicOpen g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The section of `structureSheaf R` on an open `U` sending each `x ∈ U` to the ele
ment
`f/g` in the localization of `R` at `x`.
-/
def const (f : M) (g : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : U ≤ basicOpen g) :
    Γ(M, U) :=
  ⟨fun x => .mk f ⟨g, hu x.2⟩, fun x ↦ ⟨U, x.2, 𝟙 _, f, g, fun y ↦ ⟨hu y.2, rfl⟩⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.StructureSheaf.const_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.StructureSheaf`。
形式化陈述：const_apply (f : M) (g : R) (U : Opens (PrimeSpectrum.Top R)) (hu : forall
 x in U, g in (x : PrimeSpectrum.Top R).asIdeal.primeCompl) (x : U) : (const f g
 U hu).1 x = .mk f ⟨g, hu x x.2⟩
参数：f : M；g : R；U : Opens (PrimeSpectrum.Top R)；hu : forall x in U, g in (x : Pri
meSpectrum.Top R).asIdeal.primeCompl；x : U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
theorem const_apply (f : M) (g : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : ∀ x ∈ U, g ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) (x : U) :
    (const f g U hu).1 x = .mk f ⟨g, hu x x.2⟩ :=
  rfl
/-
**AlgebraicGeometry.StructureSheaf.exists_const** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.StructureSheaf`。
形式化陈述：exists_const (U) (s : Γ(M, U)) (x : PrimeSpectrum.Top R) (hx : x in U) : e
xists (g : R) (_ : x in basicOpen g) (i : basicOpen g <= U) (f : M), const f g _
 le_rfl = (structureSheafInType R M).1.map i.hom.op s
参数：U；s : Γ(M, U)；x : PrimeSpectrum.Top R；hx : x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `PrimeSpectrum.isBasis_basic_opens`：isBasis_basic_opens : TopologicalSpac
e.Opens.IsBasis (Set.range (@basicOpen R _))
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.basicOpen_mul`：basicOpen_mul (f g : R) : basicOpen (f * g)
 = basicOpen f ⊓ basicOpen g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LocalizedModule.mk_eq`：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔
 exists u : S, u • s' • m = u • s • m'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 38 条，此处仅展示前 30 条）
-/
theorem exists_const (U) (s : Γ(M, U)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) :
    ∃ (g : R) (_ : x ∈ basicOpen g) (i : basicOpen g ≤ U) (f : M),
      const f g _ le_rfl = (structureSheafInType R M).1.map i.hom.op s := by
  obtain ⟨V, hxV, iVU, f, g, hfg⟩ := s.2 ⟨x, hx⟩
  obtain ⟨_, ⟨_, ⟨g', rfl⟩, rfl⟩, hxg', hg'U⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxV V.2
  refine ⟨g' * g, ?_, ?_, g' • f, Subtype.ext <| funext fun ⟨y, hy⟩ ↦ ?_⟩ <;>
    simp only [PrimeSpectrum.basicOpen_mul]
  · exact ⟨hxg', (hfg ⟨x, hxV⟩).1⟩
  · exact inf_le_left.trans (hg'U.trans iVU.le)
  · rw [PrimeSpectrum.basicOpen_mul] at hy
    obtain ⟨hgy, H⟩ := hfg ⟨y, hg'U hy.1⟩
    refine (LocalizedModule.mk_eq.mpr ⟨1, ?_⟩).trans H.symm
    simp [Submonoid.smul_def, ← smul_assoc]; ring_nf

@[simp]
/-
**AlgebraicGeometry.StructureSheaf.res_const** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.StructureSheaf`。
形式化陈述：res_const (f : M) (g : R) (U hu V hv i) : (structureSheafInType R M).1.map
 i (const f g U hu) = const f g V hv
参数：f : M；g : R；U hu V hv i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem res_const (f : M) (g : R) (U hu V hv i) :
    (structureSheafInType R M).1.map i (const f g U hu) = const f g V hv :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.StructureSheaf.const_zero** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.StructureSheaf`。
形式化陈述：const_zero (f : R) (U hu) : const (0 : M) f U hu = 0
参数：f : R；U hu。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.zero_oreDiv`：zero_oreDiv (s : S) : (0 : X) /ₒ s = 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem const_zero (f : R) (U hu) : const (0 : M) f U hu = 0 :=
  Subtype.ext <| funext fun x ↦ by simp; rfl

@[simp]
/-
**AlgebraicGeometry.StructureSheaf.const_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.StructureSheaf`。
形式化陈述：const_algebraMap (f : R) (U hu) : const (algebraMap R A f) f U hu = 1
参数：f : R；U hu。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LocalizedModule.mk_eq`：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔
 exists u : S, u • s' • m = u • s • m'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OreLocalization.one_def`：∀ {R : Type u_1} [inst : Monoid R] {S : Submono
id R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R
 X] [inst_3 :…
-/
theorem const_algebraMap (f : R) (U hu) : const (algebraMap R A f) f U hu = 1 :=
  Subtype.ext <| funext fun _ ↦ (LocalizedModule.mk_eq.mpr
      ⟨1, by simp [Algebra.smul_def, Submonoid.smul_def]⟩).trans
    OreLocalization.one_def.symm

@[simp]
/-
**AlgebraicGeometry.StructureSheaf.const_self** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.StructureSheaf`。
形式化陈述：const_self (f : R) (U hu) : const f f U hu = 1
参数：f : R；U hu。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.StructureSheaf.const_algebraMap`：const_algebraMap (f :
 R) (U hu) : const (algebraMap R A f) f U hu = 1
-/
theorem const_self (f : R) (U hu) : const f f U hu = 1 :=
  const_algebraMap ..

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.StructureSheaf.const_one** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.StructureSheaf`。
形式化陈述：const_one (U) : const (1 : A) (1 : R) U (by simp) = 1
参数：U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.basicOpen_one`：basicOpen_one : basicOpen (1 : R) = ⊤
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.StructureSheaf.const.congr_simp`：∀ {R M : Type u} [ins
t : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] (f f_1 : 
M),   f = f_1 →     ∀ (g g_1 : R) (e_g …
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgebraicGeometry.StructureSheaf.const_algebraMap`：const_algebraMap (f :
 R) (U hu) : const (algebraMap R A f) f U hu = 1
-/
theorem const_one (U) : const (1 : A) (1 : R) U (by simp) = 1 := by
  simpa using const_algebraMap 1 (A := A) U

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.StructureSheaf.const_add** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.StructureSheaf`。
形式化陈述：const_add (f₁ f₂ : M) (g₁ g₂ : R) (U hu₁ hu₂) : const f₁ g₁ U hu₁ + const 
f₂ g₂ U hu₂ = const (g₂ • f₁ + g₁ • f₂) (g₁ * g₂) U (by simp [*, PrimeSpectrum.b
asicOpen_mul])
参数：f₁ f₂ : M；g₁ g₂ : R；U hu₁ hu₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LocalizedModule.mk_add_mk`：mk_add_mk {m1 m2 : M} {s1 s2 : S} : mk m1 s1 
+ mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2)
-/
theorem const_add (f₁ f₂ : M) (g₁ g₂ : R) (U hu₁ hu₂) :
    const f₁ g₁ U hu₁ + const f₂ g₂ U hu₂ =
      const (g₂ • f₁ + g₁ • f₂) (g₁ * g₂) U (by simp [*, PrimeSpectrum.basicOpen_mul]) :=
  Subtype.ext <| funext fun _ ↦ LocalizedModule.mk_add_mk
/-
**AlgebraicGeometry.StructureSheaf.smul_const** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.StructureSheaf`。
形式化陈述：smul_const (f : M) (r g : R) (U hu) : r • const f g U hu = const (r • f) g
 U hu
参数：f : M；r g : R；U hu。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LocalizedModule.smul'_mk`：∀ {R : Type u} [inst : CommSemiring R] {S : Su
bmonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] {R₀ : Type u…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem smul_const (f : M) (r g : R) (U hu) :
    r • const f g U hu = const (r • f) g U hu :=
  Subtype.ext <| funext fun _ ↦ LocalizedModule.smul'_mk _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.StructureSheaf.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.StructureSheaf`。
形式化陈述：const_mul (f₁ f₂ : A) (g₁ g₂ : R) (U hu₁ hu₂) : const f₁ g₁ U hu₁ * const 
f₂ g₂ U hu₂ = const (f₁ * f₂) (g₁ * g₂) U (by simp [*, PrimeSpectrum.basicOpen_m
ul])
参数：f₁ f₂ : A；g₁ g₂ : R；U hu₁ hu₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LocalizedModule.mk_mul_mk`：mk_mul_mk {A : Type*} [Semiring A] [Algebra R
 A] {a₁ a₂ : A} {s₁ s₂ : S} : mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₁ * s₂)
-/
theorem const_mul (f₁ f₂ : A) (g₁ g₂ : R) (U hu₁ hu₂) :
    const f₁ g₁ U hu₁ * const f₂ g₂ U hu₂ =
      const (f₁ * f₂) (g₁ * g₂) U (by simp [*, PrimeSpectrum.basicOpen_mul]) :=
  Subtype.ext <| funext fun _ ↦ LocalizedModule.mk_mul_mk
/-
**AlgebraicGeometry.StructureSheaf.const_ext** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.StructureSheaf`。
形式化陈述：const_ext {f₁ f₂ : M} {g₁ g₂ : R} {U hu₁ hu₂} (h : g₂ • f₁ = g₁ • f₂) : co
nst f₁ g₁ U hu₁ = const f₂ g₂ U hu₂
参数：h : g₂ • f₁ = g₁ • f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LocalizedModule.mk_eq`：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔
 exists u : S, u • s' • m = u • s • m'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
-/
theorem const_ext {f₁ f₂ : M} {g₁ g₂ : R} {U hu₁ hu₂} (h : g₂ • f₁ = g₁ • f₂) :
    const f₁ g₁ U hu₁ = const f₂ g₂ U hu₂ :=
  Subtype.ext <| funext fun x ↦ LocalizedModule.mk_eq.mpr (by simp [h, Submonoid.smul_def])
/-
**AlgebraicGeometry.StructureSheaf.const_congr** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.StructureSheaf`。
形式化陈述：const_congr {f₁ f₂ : M} {g₁ g₂ : R} {U hu} (hf : f₁ = f₂) (hg : g₁ = g₂) :
 const f₁ g₁ U hu = const f₂ g₂ U (hg ▸ hu)
参数：hf : f₁ = f₂；hg : g₁ = g₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_congr {f₁ f₂ : M} {g₁ g₂ : R} {U hu} (hf : f₁ = f₂) (hg : g₁ = g₂) :
    const f₁ g₁ U hu = const f₂ g₂ U (hg ▸ hu) := by subst hf hg; rfl
/-
**AlgebraicGeometry.StructureSheaf.const_mul_rev** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.StructureSheaf`。
形式化陈述：const_mul_rev (f g : R) (U hu₁ hu₂) : const f g U hu₁ * const g f U hu₂ = 
1
参数：f g : R；U hu₁ hu₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.StructureSheaf.const_mul`：const_mul (f₁ f₂ : A) (g₁ g₂
 : R) (U hu₁ hu₂) : const f₁ g₁ U hu₁ * const f₂ g₂ U hu₂ = const (f₁ * f₂) (g₁ 
* g₂) U (by simp [*, PrimeSpectr…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `AlgebraicGeometry.StructureSheaf.const_congr`：const_congr {f₁ f₂ : M} {g
₁ g₂ : R} {U hu} (hf : f₁ = f₂) (hg : g₁ = g₂) : const f₁ g₁ U hu = const f₂ g₂ 
U (hg ▸ hu)
· 使用定理 `AlgebraicGeometry.StructureSheaf.const_self`：const_self (f : R) (U hu) :
 const f f U hu = 1
-/
theorem const_mul_rev (f g : R) (U hu₁ hu₂) : const f g U hu₁ * const g f U hu₂ = 1 := by
  rw [const_mul, const_congr rfl (mul_comm g f), const_self]
/-
**AlgebraicGeometry.StructureSheaf.const_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.StructureSheaf`。
形式化陈述：const_mul_cancel (f g₁ g₂ : R) (U hu₁ hu₂) : const f g₁ U hu₁ * const g₁ g
₂ U hu₂ = const f g₂ U hu₂
参数：f g₁ g₂ : R；U hu₁ hu₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.StructureSheaf.const_mul`：const_mul (f₁ f₂ : A) (g₁ g₂
 : R) (U hu₁ hu₂) : const f₁ g₁ U hu₁ * const f₂ g₂ U hu₂ = const (f₁ * f₂) (g₁ 
* g₂) U (by simp [*, PrimeSpectr…
· 使用定理 `AlgebraicGeometry.StructureSheaf.const_ext`：const_ext {f₁ f₂ : M} {g₁ g₂
 : R} {U hu₁ hu₂} (h : g₂ • f₁ = g₁ • f₂) : const f₁ g₁ U hu₁ = const f₂ g₂ U hu
₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
-/
theorem const_mul_cancel (f g₁ g₂ : R) (U hu₁ hu₂) :
    const f g₁ U hu₁ * const g₁ g₂ U hu₂ = const f g₂ U hu₂ := by
  rw [const_mul, const_ext]; simp; ring
/-
**AlgebraicGeometry.StructureSheaf.const_mul_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.StructureSheaf`。
形式化陈述：const_mul_cancel' (f g₁ g₂ : R) (U hu₁ hu₂) : const g₁ g₂ U hu₂ * const f 
g₁ U hu₁ = const f g₂ U hu₂
参数：f g₁ g₂ : R；U hu₁ hu₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `AlgebraicGeometry.StructureSheaf.const_mul_cancel`：const_mul_cancel (f g
₁ g₂ : R) (U hu₁ hu₂) : const f g₁ U hu₁ * const g₁ g₂ U hu₂ = const f g₂ U hu₂
-/
theorem const_mul_cancel' (f g₁ g₂ : R) (U hu₁ hu₂) :
    const g₁ g₂ U hu₂ * const f g₁ U hu₁ = const f g₂ U hu₂ := by
  rw [mul_comm, const_mul_cancel]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.StructureSheaf.const_eq_const_of_smul_eq_smul** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicGeometry.StructureSheaf`。
形式化陈述：const_eq_const_of_smul_eq_smul (f₁ f₂ : M) (g₁ g₂ : R) (U hu₁ hu₂) (H : g₁
 • f₂ = g₂ • f₁) : const f₁ g₁ U hu₁ = const f₂ g₂ U hu₂
参数：f₁ f₂ : M；g₁ g₂ : R；U hu₁ hu₂；H : g₁ • f₂ = g₂ • f₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
-/
theorem const_eq_const_of_smul_eq_smul (f₁ f₂ : M) (g₁ g₂ : R) (U hu₁ hu₂) (H : g₁ • f₂ = g₂ • f₁) :
    const f₁ g₁ U hu₁ = const f₂ g₂ U hu₂ :=
  Subtype.ext (funext fun x ↦ by
    simp [LocalizedModule.mk_eq, Localizations, Submonoid.smul_def, H])

set_option backward.isDefEq.respectTransparency false in
variable (R M) in
/-- The canonical linear map interpreting an element of `M` as
a section of the structure sheaf. -/
/-
**AlgebraicGeometry.StructureSheaf.toOpen** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.StructureSheaf`。
形式化陈述：toOpen (U : Opens (PrimeSpectrum.Top R)) : CommRingCat.of R ⟶ (structureSh
eaf R).1.obj (op U)
参数：U : Opens (PrimeSpectrum.Top R)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear map interpreting an element of `M` as
a section of the structure sheaf.
-/
def toOpenₗ (U : Opens (PrimeSpectrum.Top R)) :
    M →ₗ[R] Γ(M, U) where
  toFun m := const m 1 U (by simp)
  map_add' _ _ := by simp [const_add]
  map_smul' _ _ := by simp [smul_const]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.StructureSheaf.toOpen** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.StructureSheaf`。
形式化陈述：toOpen (U : Opens (PrimeSpectrum.Top R)) : CommRingCat.of R ⟶ (structureSh
eaf R).1.obj (op U)
参数：U : Opens (PrimeSpectrum.Top R)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOpenₗ_eq_const (U : Opens (PrimeSpectrum.Top R)) (f : M) :
    toOpenₗ R M U f = const f 1 U (by simp) := rfl

end StructureSheaf

end Public

local notation "Γ(" M ", " U ")" =>
  (Functor.obj (ObjectProperty.FullSubcategory.obj (structureSheafInType _ M))) (Opposite.op U)

namespace StructureSheaf

section basicOpen

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.StructureSheaf.isUnit_basicOpen** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.StructureSheaf`。
形式化陈述：isUnit_basicOpen (f : R) : IsUnit ((algebraMap R Γ(R, basicOpen f)) f)
参数：f : R。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isUnit_basicOpen (f : R) :
    IsUnit ((algebraMap R Γ(R, basicOpen f)) f) :=
  isUnit_iff_exists_inv.mpr ⟨const 1 f _ le_rfl, const_mul_rev _ _ _ (by simp) _⟩
/-
**AlgebraicGeometry.StructureSheaf.isUnit_basicOpen_end** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.StructureSheaf`。
形式化陈述：isUnit_basicOpen_end (f : R) : IsUnit ((algebraMap R (Module.End R Γ(M, ba
sicOpen f))) f)
参数：f : R。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isUnit_basicOpen_end (f : R) :
    IsUnit ((algebraMap R (Module.End R Γ(M, basicOpen f))) f) := by
  have := (isUnit_basicOpen f).map
    (algebraMap _ (Module.End Γ(R, basicOpen f) Γ(M, basicOpen f)))
  rw [Module.End.isUnit_iff] at this ⊢
  convert! this
  ext a
  simp

variable (R M) in
/-- The canonical linear map interpreting `s ∈ M_f` as a section of the structure sheaf
on the basic open defined by `f ∈ R`. -/
/-
**AlgebraicGeometry.StructureSheaf.toBasicOpen** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear map interpreting `s ∈ M_f` as a section of the structure sh
eaf
on the basic open defined by `f ∈ R`.
-/
def toBasicOpenₗ (f : R) :
    LocalizedModule.Away f M →ₗ[R] Γ(M, PrimeSpectrum.basicOpen f) :=
  IsLocalizedModule.lift (.powers f) (LocalizedModule.mkLinearMap ..) (toOpenₗ R M _) <| by
    simp only [Subtype.forall]
    exact Submonoid.powers_le (P := (IsUnit.submonoid _).comap (algebraMap R _)).mpr
      (isUnit_basicOpen_end ..)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.StructureSheaf.toBasicOpen** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBasicOpenₗ_mk (s : R) (f : M) (g : Submonoid.powers s) :
    toBasicOpenₗ R M s (.mk f g) = const f g.1 (basicOpen s) (by
    have := PrimeSpectrum.le_basicOpen_pow s; aesop (add simp [Submonoid.mem_powers_iff])) := by
  obtain ⟨_, n, rfl⟩ := g
  apply ((Module.End.isUnit_iff _).mp ((isUnit_basicOpen_end ..).pow n)).1 ?_
  rw [← map_pow]
  dsimp [toBasicOpenₗ]
  rw [← map_smul, LocalizedModule.smul'_mk, ← Submonoid.mk_smul (S := .powers s) _ ⟨n, rfl⟩,
    LocalizedModule.mk_cancel, ← LocalizedModule.mkLinearMap_apply, IsLocalizedModule.lift_apply,
    smul_const]
  dsimp [toOpenₗ]
  exact const_eq_const_of_smul_eq_smul (H := by simp) ..
/-
**AlgebraicGeometry.StructureSheaf.toBasicOpen** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBasicOpenₗ_injective (f : R) : Function.Injective (toBasicOpenₗ R M f) := by
  intro s t h_eq
  induction s using LocalizedModule.induction_on with | h a b =>
  induction t using LocalizedModule.induction_on with | h c d =>
  suffices f ∈ ((⊥ : Submodule R M).colon {d • a - b • c}).radical by
    rw [LocalizedModule.mk_eq]
    obtain ⟨n, hn⟩ := this
    exact ⟨⟨f ^ n, n, rfl⟩, by simpa [sub_eq_zero, smul_sub] using! Submodule.mem_colon.mp hn _ rfl⟩
  simp only [toBasicOpenₗ_mk] at h_eq
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.mem_vanishingIdeal]
  intro p hfp
  contrapose hfp
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp congr(($h_eq).1 ⟨p, hfp⟩)
  rw [PrimeSpectrum.mem_zeroLocus, Set.not_subset]
  exact ⟨u.1, by simpa [sub_eq_zero, smul_sub], u.2⟩

set_option backward.isDefEq.respectTransparency false in
/-
Auxiliary lemma for surjectivity of `toBasicOpen`.
A local representation of a section `s` as fractions `a i / h i` on finitely many basic opens
`basicOpen (h i)` can be "normalized" in such a way that `a i * h j = h i * a j` for all `i, j`
-/
/-
**AlgebraicGeometry.StructureSheaf.exists_le_iSup_basicOpen_and_smul_eq_smul_and
_eq_const** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.StructureSheaf`。
形式化陈述：exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const (U : Opens (PrimeSp
ectrum.Top R)) (hU : IsCompact (U : Set (PrimeSpectrum.Top R))) (s : Γ(M, U)) : 
exists (ι : Type u) (_ : Fintype ι) (a : ι -> M) (b : ι -> R) (ibU : forall i, b
asicOpen (b i) <= U), (U <= ⨆ i, basicOpen (b i)) ∧ (forall i j, b j • a i = b i
 • a j) ∧ forall i, (structureSheafInType R M).presheaf.map (ibU i).hom.op s = c
onst (a i) (b i) _ le_rfl
参数：U : Opens (PrimeSpectrum.Top R)；hU : IsCompact (U : Set (PrimeSpectrum.Top R)
)；s : Γ(M, U)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary lemma for surjectivity of `toBasicOpen`.
A local representation of a section `s` as fractions `a i / h i` on finitely man
y basic opens
`basicOpen (h i)` can be "normalized" in such a way that `a i * h j = h i * a j`
 for all `i, j`
-/
theorem exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const
    (U : Opens (PrimeSpectrum.Top R)) (hU : IsCompact (U : Set (PrimeSpectrum.Top R)))
    (s : Γ(M, U)) :
    ∃ (ι : Type u) (_ : Fintype ι) (a : ι → M) (b : ι → R) (ibU : ∀ i, basicOpen (b i) ≤ U),
      (U ≤ ⨆ i, basicOpen (b i)) ∧ (∀ i j, b j • a i = b i • a j) ∧
          ∀ i, (structureSheafInType R M).presheaf.map (ibU i).hom.op s =
              const (a i) (b i) _ le_rfl := by
  choose g hxg igU f H using fun x : U ↦ exists_const U s x.1 x.2
  have (i j : _) : LocalizedModule.mk (g i • f j) ⟨g i * g j, Submonoid.mem_powers _⟩ =
      LocalizedModule.mk (g j • f i) ⟨g i * g j, Submonoid.mem_powers _⟩ := by
    refine toBasicOpenₗ_injective (g i * g j) ?_
    simp only [toBasicOpenₗ_mk]
    have := H i
    trans (structureSheafInType R M).obj.map (homOfLE ?_).op s
    · refine .trans (Subtype.ext <| funext fun a ↦ ?_) congr((structureSheafInType R M).obj.map
        (homOfLE ((PrimeSpectrum.basicOpen_mul (g i) (g j)).trans_le inf_le_right)).op $(H j))
      exact LocalizedModule.mk_eq.mpr ⟨1, by simp [Submonoid.smul_def, ← smul_assoc]; ring_nf⟩
    · refine congr((structureSheafInType R M).obj.map (homOfLE ((PrimeSpectrum.basicOpen_mul (g i)
        (g j)).trans_le inf_le_left)).op $(H i)).symm.trans (Subtype.ext <| funext fun a ↦ ?_)
      exact LocalizedModule.mk_eq.mpr ⟨1, by simp [Submonoid.smul_def, ← smul_assoc]⟩
    · exact ((PrimeSpectrum.basicOpen_mul (g i) (g j)).trans_le inf_le_right).trans (igU _)
  simp only [LocalizedModule.mk_eq, Submonoid.smul_def, Subtype.exists, Submonoid.mem_powers_iff,
    exists_prop, exists_exists_eq_and, ← mul_smul, ← pow_succ, ← mul_assoc _ (_ * _)] at this
  choose n hn using this
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun i ↦ (basicOpen (g i) : Set (PrimeSpectrum R)))
    (fun _ ↦ (basicOpen _).2) (fun x hx ↦ Set.mem_iUnion_of_mem ⟨x, hx⟩ (hxg _))
  let N := (t ×ˢ t).sup fun x ↦ n x.1 x.2 + 1
  refine ⟨t, inferInstance, fun i ↦ g i ^ N • f i, fun i ↦ (g i) ^ (N + 1),
    fun x ↦ by simpa using igU x.1, fun x hx ↦ by simpa using ht hx, fun i j ↦ ?_, fun i ↦ ?_⟩
  · dsimp
    convert_to (g i * g ↑j) ^ N • g j • f i = (g i * g ↑j) ^ N • g i • f j
    · module
    · module
    have : n i j + 1 ≤ N := (t ×ˢ t).le_sup (f := fun x ↦ n x.1 x.2 + 1) (b := ⟨_, _⟩) (by simp)
    rw [← Nat.sub_add_cancel this, pow_add, mul_smul, mul_smul]
    congr 1
    convert! (hn i j).symm using 1 <;> module
  · convert! congr((structureSheafInType R M).presheaf.map (homOfLE ?_).op $((H i).symm)) using 1
    · refine Subtype.ext <| funext fun x ↦ LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
      simp [Submonoid.smul_def, pow_succ', mul_smul]
    · simp

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.StructureSheaf.toBasicOpen** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBasicOpenₗ_surjective (f : R) : Function.Surjective (toBasicOpenₗ R M f) := by
  intro s
  obtain ⟨ι, _, a, b, ibU, iU, hab, H⟩ := exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const _
    (PrimeSpectrum.isCompact_basicOpen _) s
  obtain ⟨n, hn⟩ : f ∈ (Ideal.span (Set.range b)).radical := by
    have : PrimeSpectrum.zeroLocus (Set.range b) ⊆ PrimeSpectrum.zeroLocus {f} := by
      simpa [← SetLike.coe_subset_coe, ← Set.compl_iInter,
        ← PrimeSpectrum.zeroLocus_iUnion, PrimeSpectrum.Top] using iU
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.zeroLocus_span,
      PrimeSpectrum.mem_vanishingIdeal]
    exact fun x hx ↦ by simpa using this hx
  replace hn := Ideal.mul_mem_right f _ hn
  rw [← pow_succ, Ideal.span, Finsupp.mem_span_range_iff_exists_finsupp] at hn
  obtain ⟨c, hc⟩ := hn
  rw [Finsupp.sum_fintype _ _ (by simp)] at hc
  refine ⟨LocalizedModule.mk (∑ i, c i • a i) ⟨f ^ (n + 1), _, rfl⟩, ?_⟩
  refine (structureSheafInType R M).eq_of_locally_eq' (fun i ↦ basicOpen (b i)) _
    (fun i ↦ (ibU _).hom) iU _ _ fun i ↦ (Subtype.ext (funext fun x ↦ ?_)).trans (H _).symm
  rw [toBasicOpenₗ_mk]
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  simp_rw [one_smul, Finset.smul_sum, Submonoid.smul_def, smul_comm (b i), hab _ i, ← smul_assoc,
    ← Finset.sum_smul, hc]

set_option backward.isDefEq.respectTransparency.types false in
public instance (f : R) : IsLocalizedModule.Away f (toOpenₗ R M (basicOpen f)) := by
  convert!
    IsLocalizedModule.of_linearEquiv (.powers f) (LocalizedModule.mkLinearMap (.powers f) M)
      (.ofBijective _ ⟨toBasicOpenₗ_injective _, toBasicOpenₗ_surjective _⟩)
  ext x
  simp [toOpenₗ]
/-
**AlgebraicGeometry.StructureSheaf.isIso_toBasicOpen** 是 Mathlib 中的一个实例，位于命名空间 `
AlgebraicGeometry.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_toBasicOpenₗ (f : R) :
    IsIso (ModuleCat.ofHom (toBasicOpenₗ R M f)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr ⟨toBasicOpenₗ_injective _, toBasicOpenₗ_surjective _⟩

set_option backward.isDefEq.respectTransparency false in
public lemma toOpenₗ_top_bijective : Function.Bijective (toOpenₗ R M ⊤) := by
  have : IsLocalizedModule ⊥ (toOpenₗ R M ⊤) := by
    convert! (inferInstance : IsLocalizedModule (.powers 1) (toOpenₗ R M (basicOpen 1)))
    rw [PrimeSpectrum.basicOpen_one, Submonoid.powers_one]
  refine ⟨fun x y e ↦ by simpa using (IsLocalizedModule.eq_iff_exists ⊥ _).mp e, fun x ↦ ?_⟩
  obtain ⟨⟨x, _, rfl⟩, rfl⟩ := IsLocalizedModule.mk'_surjective ⊥ (toOpenₗ R M ⊤) x
  exact ⟨x, (IsLocalizedModule.mk'_one ..).symm⟩

public lemma algebraMap_obj_top_bijective :
    Function.Bijective (algebraMap R Γ(R, (⊤ : Opens (PrimeSpectrum.Top R)))) :=
  toOpenₗ_top_bijective

set_option backward.isDefEq.respectTransparency false in
public instance (f : R) : IsLocalization.Away f Γ(R, basicOpen f) :=
  (isLocalizedModule_iff_isLocalization' _ _).mp <|
    inferInstanceAs (IsLocalizedModule.Away f (toOpenₗ R R (basicOpen f)))

end basicOpen

section Stalk

variable (R) in
/-- The canonical ring homomorphism interpreting an element of `R` as an element of
the stalk of `structureSheaf R` at `x`. -/
@[expose] public def toStalk (x : PrimeSpectrum.Top R) :
    CommRingCat.of R ⟶ (structurePresheafInCommRingCat R).stalk x :=
  CommRingCat.ofHom (algebraMap _ _) ≫ (structurePresheafInCommRingCat R).germ ⊤ x trivial

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[elementwise, reassoc]
public lemma algebraMap_germ
    (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hxU : x ∈ U) :
    CommRingCat.ofHom (algebraMap R Γ(R, U)) ≫ (structurePresheafInCommRingCat R).germ U x hxU =
      toStalk R x := by
  dsimp [toStalk]
  rw [← (structurePresheafInCommRingCat R).germ_res (homOfLE (le_top : U ≤ ⊤)) _ hxU]
  rfl

@[deprecated (since := "2026-02-10")] public alias toOpen_germ := algebraMap_germ

public
/-
**AlgebraicGeometry.StructureSheaf.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : PrimeSpectrum.Top R) : Algebra R ((structurePresheafInCommRingCat R).stalk x) :=
  (toStalk R x).hom.toAlgebra

public
/-
**AlgebraicGeometry.StructureSheaf.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : PrimeSpectrum.Top R) :
    Module R ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x) :=
  .compHom _ (toStalk R x).hom

variable (M) in
/-
**AlgebraicGeometry.StructureSheaf.germ** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def germₗ (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hxU : x ∈ U) :
    Γ(M, U) →ₗ[R] ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x) where
  __ := (TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf U x hxU).hom
  map_smul' r m := by
    change _ = toStalk R x _ • TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf _ _ _ _
    rw [← algebraMap_germ_apply U x hxU]
    refine .trans ?_ (PresheafOfModules.germ_smul ..)
    congr 1
    exact (IsScalarTower.algebraMap_smul Γ(R, U) r m).symm

public
/-
**AlgebraicGeometry.StructureSheaf.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : PrimeSpectrum.Top R) :
    IsScalarTower R ((structurePresheafInCommRingCat R).stalk x)
      ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x) :=
  .of_algebraMap_smul fun _ _ ↦ rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (R M) in
/-
**AlgebraicGeometry.StructureSheaf.modulePresheafStalkIso** 是 Mathlib 中的一个定义，位于命
名空间 `AlgebraicGeometry.StructureSheaf`。
形式化陈述：modulePresheafStalkIso (x : PrimeSpectrum.Top R) : ↑(TopCat.Presheaf.stalk
 (moduleStructurePresheaf R M).presheaf x) ≃ₗ[R] (structurePresheafInModuleCat R
 M).stalk x where __
参数：x : PrimeSpectrum.Top R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def modulePresheafStalkIso (x : PrimeSpectrum.Top R) :
    ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x) ≃ₗ[R]
      (structurePresheafInModuleCat R M).stalk x where
  __ := (Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves (forget₂ (ModuleCat R) Ab)
    (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙
      structurePresheafInModuleCat R M))⟩:).addCommGroupIsoToAddEquiv
  map_smul' r m := by
    let α : TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x ≅
      (forget₂ _ _).obj ((structurePresheafInModuleCat R M).stalk x) :=
      Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves (forget₂ (ModuleCat R) Ab)
      (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙
        structurePresheafInModuleCat R M))⟩
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ m
    have : TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf U x hxU ≫ α.hom =
        (forget₂ _ _).map ((structurePresheafInModuleCat R M).germ U x hxU) :=
      Limits.colimit.isoColimitCocone_ι_hom (C := Ab) ..
    have (m : _) : α.hom (TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf U x hxU m) =
        (structurePresheafInModuleCat R M).germ U x hxU m := congr($this m)
    change α.hom (r • germₗ M U x hxU _) =
      r • (show (structurePresheafInModuleCat R M).stalk x from _)
    rw [← map_smul]
    refine (this _).trans ?_
    dsimp [toStalk]
    erw [this]
    exact ((structurePresheafInModuleCat R M).germ U x hxU).hom.map_smul _ _
/-
**AlgebraicGeometry.StructureSheaf.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : PrimeSpectrum.Top R) :
    Module ((structurePresheafInCommRingCat R).stalk x)
      ((structurePresheafInModuleCat R M).stalk x) :=
  (modulePresheafStalkIso R M x).toAddEquiv.symm.module _
/-
**AlgebraicGeometry.StructureSheaf.toStalk_smul** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.StructureSheaf`。
形式化陈述：toStalk_smul (x : PrimeSpectrum.Top R) (r : R) (m : (structurePresheafInMo
duleCat R M).stalk x) : toStalk R x r • m = r • m
参数：x : PrimeSpectrum.Top R；r : R；m : (structurePresheafInModuleCat R M).stalk x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toStalk_smul (x : PrimeSpectrum.Top R) (r : R)
    (m : (structurePresheafInModuleCat R M).stalk x) :
    toStalk R x r • m = r • m := by
  change modulePresheafStalkIso R M x (toStalk R x r • (modulePresheafStalkIso R M x).symm m) = _
  rw [← (modulePresheafStalkIso R M x).eq_symm_apply, map_smul]
  rfl

variable (R M) in
/-- The canonical ring homomorphism interpreting an element of `R` as an element of
the stalk of `structureSheaf R` at `x`. -/
/-
**AlgebraicGeometry.StructureSheaf.toStalk** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.StructureSheaf`。
形式化陈述：(R : Type u) →   [inst : CommRing R] →     (x : ↑(AlgebraicGeometry.PrimeS
pectrum.Top R)) →       CommRingCat.of R ⟶ (AlgebraicGeometry.structurePresheafI
nCommRingCat R).stalk x
参数：AlgebraicGeometry.PrimeSpectrum.Top R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
The canonical ring homomorphism interpreting an element of `R` as an element of
the stalk of `structureSheaf R` at `x`.
-/
def toStalkₗ' (x : PrimeSpectrum.Top R) :
    ModuleCat.of R M ⟶ (structurePresheafInModuleCat R M).stalk x :=
  ModuleCat.ofHom (toOpenₗ R M ⊤) ≫ (structurePresheafInModuleCat R M).germ _ x trivial

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.StructureSheaf.toOpen** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.StructureSheaf`。
形式化陈述：toOpen (U : Opens (PrimeSpectrum.Top R)) : CommRingCat.of R ⟶ (structureSh
eaf R).1.obj (op U)
参数：U : Opens (PrimeSpectrum.Top R)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOpenₗ_germ (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x ∈ U) :
    ModuleCat.ofHom (toOpenₗ R M U) ≫
      (structurePresheafInModuleCat R M).germ U x hx = toStalkₗ' R M x := by
  rw [toStalkₗ', ← Presheaf.germ_res _ (homOfLE le_top) _ hx, ← Category.assoc]
  rfl
/-
**AlgebraicGeometry.StructureSheaf.isUnit_toStalk** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.StructureSheaf`。
形式化陈述：isUnit_toStalk (x : PrimeSpectrum.Top R) (f : R) (hf : x in basicOpen f) :
 IsUnit (toStalk R x f)
参数：x : PrimeSpectrum.Top R；f : R；hf : x in basicOpen f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isUnit_toStalk (x : PrimeSpectrum.Top R) (f : R) (hf : x ∈ basicOpen f) :
    IsUnit (toStalk R x f) := by
  convert! (isUnit_basicOpen f).map ((structurePresheafInCommRingCat R).germ _ x hf).hom
  exact ((structurePresheafInCommRingCat R).germ_res_apply (homOfLE (le_top : basicOpen f ≤ ⊤))
    x hf (algebraMap R Γ(R, ⊤) f)).symm
/-
**AlgebraicGeometry.StructureSheaf.isUnit_toStalk** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.StructureSheaf`。
形式化陈述：isUnit_toStalk (x : PrimeSpectrum.Top R) (f : R) (hf : x in basicOpen f) :
 IsUnit (toStalk R x f)
参数：x : PrimeSpectrum.Top R；f : R；hf : x in basicOpen f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isUnit_toStalkₗ' (x : PrimeSpectrum.Top R) (f : R) (hf : x ∈ basicOpen f) :
    IsUnit (algebraMap R (Module.End R ((structurePresheafInModuleCat R M).stalk x)) f) := by
  have := (isUnit_toStalk x f hf).map (algebraMap _
    (Module.End ((structurePresheafInCommRingCat R).stalk x)
      ((structurePresheafInModuleCat R M).stalk x)))
  rw [Module.End.isUnit_iff] at this ⊢
  convert! this
  ext a
  simp only [Module.algebraMap_end_apply]
  rw [toStalk_smul]

set_option backward.isDefEq.respectTransparency.types false in
variable (R M) in
/-- The canonical ring homomorphism from the localization of `R` at `p` to the stalk
of the structure sheaf at the point `p`. -/
/-
**AlgebraicGeometry.StructureSheaf.localizationtoStalk** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical ring homomorphism from the localization of `R` at `p` to the stalk
of the structure sheaf at the point `p`.
-/
def localizationtoStalkₗ (x : PrimeSpectrum.Top R) :
    ModuleCat.of R (LocalizedModule x.asIdeal.primeCompl M) ⟶
      (structurePresheafInModuleCat R M).stalk x :=
  ModuleCat.ofHom (IsLocalizedModule.lift x.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (toStalkₗ' R M x).hom fun f ↦ isUnit_toStalkₗ' x f.1 f.2 :)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.StructureSheaf.localizationtoStalk** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localizationtoStalkₗ_mk (x : PrimeSpectrum.Top R) (f : M) (s) :
    localizationtoStalkₗ R M x (.mk f s) = (structurePresheafInModuleCat R M).germ
      (PrimeSpectrum.basicOpen (s : R)) x s.2 (const f (s : R) _ fun _ ↦ id) := by
  apply ((Module.End.isUnit_iff _).mp (isUnit_toStalkₗ' _ s.1 s.2)).1 ?_
  dsimp [localizationtoStalkₗ]
  rw [← map_smul, LocalizedModule.smul'_mk, ← Submonoid.smul_def, LocalizedModule.mk_cancel,
    ← LocalizedModule.mkLinearMap_apply, IsLocalizedModule.lift_apply, ← map_smul,
    ← toOpenₗ_germ (basicOpen ↑s) _ s.2, smul_const]
  dsimp [toOpenₗ]
  congr 1
  exact const_eq_const_of_smul_eq_smul (H := by simp) ..

set_option backward.isDefEq.respectTransparency.types false in
variable (R M) in
/-- The ring homomorphism that takes a section of the structure sheaf of `R` on the open set `U`,
implemented as a subtype of dependent functions to localizations at prime ideals, and evaluates
the section on the point corresponding to a given prime ideal. -/
/-
**AlgebraicGeometry.StructureSheaf.openToLocalization** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism that takes a section of the structure sheaf of `R` on the 
open set `U`,
implemented as a subtype of dependent functions to localizations at prime ideals
, and evaluates
the section on the point corresponding to a given prime ideal.
-/
def openToLocalizationₗ (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x ∈ U) :
    (structurePresheafInModuleCat R M).obj (op U) ⟶
      .of R (LocalizedModule x.asIdeal.primeCompl M) :=
  ModuleCat.ofHom
  { toFun s := s.1 ⟨x, hx⟩
    map_smul' _ _ := rfl
    map_add' _ _ := rfl }

set_option backward.isDefEq.respectTransparency.types false in
variable (R M) in
/-- The ring homomorphism from the stalk of the structure sheaf of `R` at a point corresponding to
a prime ideal `p` to the localization of `R` at `p`,
formed by gluing the `openToLocalization` maps. -/
/-
**AlgebraicGeometry.StructureSheaf.stalkToLocalization** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism from the stalk of the structure sheaf of `R` at a point co
rresponding to
a prime ideal `p` to the localization of `R` at `p`,
formed by gluing the `openToLocalization` maps.
-/
def stalkToLocalizationₗ (x : PrimeSpectrum.Top R) :
    (structurePresheafInModuleCat R M).stalk x ⟶ .of R (LocalizedModule x.asIdeal.primeCompl M) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ structurePresheafInModuleCat R M)
    { pt := _
      ι.app U := openToLocalizationₗ R M ((OpenNhds.inclusion _).obj (unop U)) x (unop U).2 }

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.StructureSheaf.germ_stalkToLocalization** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem germ_stalkToLocalizationₗ
    (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x ∈ U) :
    (structurePresheafInModuleCat R M).germ U x hx ≫ stalkToLocalizationₗ R M x =
      openToLocalizationₗ R M U x hx :=
  Limits.colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.StructureSheaf.toStalk** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.StructureSheaf`。
形式化陈述：(R : Type u) →   [inst : CommRing R] →     (x : ↑(AlgebraicGeometry.PrimeS
pectrum.Top R)) →       CommRingCat.of R ⟶ (AlgebraicGeometry.structurePresheafI
nCommRingCat R).stalk x
参数：AlgebraicGeometry.PrimeSpectrum.Top R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem toStalkₗ'_stalkToFiberRingHom (x : PrimeSpectrum.Top R) :
    toStalkₗ' R M x ≫ stalkToLocalizationₗ R M x =
      ModuleCat.ofHom (LocalizedModule.mkLinearMap _ _) := by
  rw [toStalkₗ', Category.assoc, germ_stalkToLocalizationₗ]; rfl

open TopCat.Presheaf

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (R M) in
/-- The ring isomorphism between the stalk of the structure sheaf of `R` at a point `p`
corresponding to a prime ideal in `R` and the localization of `R` at `p`. -/
@[simps]
/-
**AlgebraicGeometry.StructureSheaf.stalkIso** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.StructureSheaf`。
形式化陈述：(R : Type u) →   [inst : CommRing R] →     (x : PrimeSpectrum R) →       L
ocalization.AtPrime x.asIdeal ≃ₐ[R] ↑((AlgebraicGeometry.structurePresheafInComm
RingCat R).stalk x)
参数：AlgebraicGeometry.structurePresheafInCommRingCat R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.StructureSheaf.instAtPrimeCarrierStalkCommRingCatStruc
turePresheafInCommRingCatAsIdeal`：∀ {R : Type u} [inst : CommRing R] (x : ↑(Alge
braicGeometry.PrimeSpectrum.Top R)),   IsLocalization.AtPrime (↑((AlgebraicGeome
try.structureP…

--- 原说明 ---
The ring isomorphism between the stalk of the structure sheaf of `R` at a point 
`p`
corresponding to a prime ideal in `R` and the localization of `R` at `p`.
-/
def stalkIsoₗ (x : PrimeSpectrum.Top R) :
    (structurePresheafInModuleCat R M).stalk x ≅
      .of R (LocalizedModule x.asIdeal.primeCompl M) where
  hom := stalkToLocalizationₗ R M x
  inv := localizationtoStalkₗ R M x
  hom_inv_id := by
    apply stalk_hom_ext
    intro U hxU
    ext s
    obtain ⟨g, hxg, igU, f, hs⟩ :=
      exists_const _ s x hxU
    rw [germ_stalkToLocalizationₗ_assoc, Category.comp_id, ← germ_res_apply _ igU.hom _ hxg]
    refine congr(localizationtoStalkₗ R M x (openToLocalizationₗ R M _ x hxg $hs)).symm.trans ?_
    refine (localizationtoStalkₗ_mk ..).trans
      congr((structurePresheafInModuleCat R M).germ _ x hxg $hs)
  inv_hom_id := by
    ext1
    refine IsLocalizedModule.ext x.asIdeal.primeCompl (LocalizedModule.mkLinearMap ..)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap ..)) ?_
    ext
    dsimp [localizationtoStalkₗ]
    rw [← LocalizedModule.mkLinearMap_apply, IsLocalizedModule.lift_apply,
      elementwise_of% toStalkₗ'_stalkToFiberRingHom (M := M) x]
    simp
/-
**AlgebraicGeometry.StructureSheaf.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : PrimeSpectrum R) : IsIso (stalkToLocalizationₗ R M x) :=
  (stalkIsoₗ R M x).isIso_hom
/-
**AlgebraicGeometry.StructureSheaf.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : PrimeSpectrum R) : IsIso (localizationtoStalkₗ R M x) :=
  (stalkIsoₗ R M x).isIso_inv

@[simp, reassoc]
/-
**AlgebraicGeometry.StructureSheaf.stalkToFiberRingHom_localizationToStalk** 是 M
athlib 中的一个定理，位于命名空间 `AlgebraicGeometry.StructureSheaf`。
形式化陈述：stalkToFiberRingHom_localizationToStalk (x : PrimeSpectrum.Top R) : stalkT
oLocalizationₗ R M x ≫ localizationtoStalkₗ R M x = 𝟙 _
参数：x : PrimeSpectrum.Top R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stalkToFiberRingHom_localizationToStalk (x : PrimeSpectrum.Top R) :
    stalkToLocalizationₗ R M x ≫ localizationtoStalkₗ R M x = 𝟙 _ :=
  (stalkIsoₗ R M x).hom_inv_id

@[simp, reassoc]
/-
**AlgebraicGeometry.StructureSheaf.localizationToStalk_stalkToFiberRingHom** 是 M
athlib 中的一个定理，位于命名空间 `AlgebraicGeometry.StructureSheaf`。
形式化陈述：localizationToStalk_stalkToFiberRingHom (x : PrimeSpectrum.Top R) : locali
zationtoStalkₗ R M x ≫ stalkToLocalizationₗ R M x = 𝟙 _
参数：x : PrimeSpectrum.Top R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localizationToStalk_stalkToFiberRingHom (x : PrimeSpectrum.Top R) :
    localizationtoStalkₗ R M x ≫ stalkToLocalizationₗ R M x = 𝟙 _ :=
  (stalkIsoₗ R M x).inv_hom_id

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.StructureSheaf.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : PrimeSpectrum.Top R) :
    IsLocalizedModule x.asIdeal.primeCompl (toStalkₗ' R M x).hom := by
  convert!
    IsLocalizedModule.of_linearEquiv x.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M) (stalkIsoₗ R M x).toLinearEquiv.symm
  ext m
  refine .trans ?_ (localizationtoStalkₗ_mk ..).symm
  dsimp +instances [toStalkₗ', toOpenₗ]
  rw! [PrimeSpectrum.basicOpen_one]
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (R M) in
/-- The canonical ring homomorphism interpreting an element of `R` as an element of
the stalk of `structureSheaf R` at `x`. -/
@[expose] public
/-
**AlgebraicGeometry.StructureSheaf.toStalk** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.StructureSheaf`。
形式化陈述：(R : Type u) →   [inst : CommRing R] →     (x : ↑(AlgebraicGeometry.PrimeS
pectrum.Top R)) →       CommRingCat.of R ⟶ (AlgebraicGeometry.structurePresheafI
nCommRingCat R).stalk x
参数：AlgebraicGeometry.PrimeSpectrum.Top R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
The canonical ring homomorphism interpreting an element of `R` as an element of
the stalk of `structureSheaf R` at `x`.
-/
def toStalkₗ (x : PrimeSpectrum.Top R) :
    M →ₗ[R] ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x) where
  toFun m :=
    TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf ⊤ x (by simp) (toOpenₗ R M ⊤ m)
  map_add' := by simp
  map_smul' r m := by
    change _ = toStalk R x r • TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf _ _ _ _
    rw [map_smul]
    refine .trans ?_ ((moduleStructurePresheaf R M).germ_smul ..)
    congr 1
    exact (IsScalarTower.algebraMap_smul Γ(R, _) (M := Γ(M, _)) _ _).symm

set_option backward.isDefEq.respectTransparency.types false in
public
/-
**AlgebraicGeometry.StructureSheaf.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : PrimeSpectrum.Top R) : IsLocalizedModule x.asIdeal.primeCompl (toStalkₗ R M x) := by
  convert!
    IsLocalizedModule.of_linearEquiv x.asIdeal.primeCompl (toStalkₗ' R M x).hom
      (modulePresheafStalkIso R M x).symm
  ext m
  let α : TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x ≅
    (forget₂ _ _).obj ((structurePresheafInModuleCat R M).stalk x) :=
    Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves (forget₂ (ModuleCat R) Ab)
    (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙
      structurePresheafInModuleCat R M))⟩
  refine α.addCommGroupIsoToAddEquiv.eq_symm_apply.mpr ?_
  change α.hom _ = _
  have : TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf ⊤ x (by simp) ≫ α.hom =
      (forget₂ _ _).map ((structurePresheafInModuleCat R M).germ ⊤ x (by simp)) :=
    Limits.colimit.isoColimitCocone_ι_hom (C := Ab) ..
  exact congr($this _)

set_option backward.isDefEq.respectTransparency.types false in
variable (R) in
/-- The stalk of `Spec R` at `x` is isomorphic to the stalk of `R^~` at `x`. -/
@[expose] public
/-
**AlgebraicGeometry.StructureSheaf.commRingCatStalkEquivModuleStalk** 是 Mathlib 
中的一个定义，位于命名空间 `AlgebraicGeometry.StructureSheaf`。
形式化陈述：commRingCatStalkEquivModuleStalk (x : PrimeSpectrum.Top R) : ↑(TopCat.Pres
heaf.stalk (moduleStructurePresheaf R R).presheaf x) ≃ₗ[R] (structurePresheafInC
ommRingCat R).stalk x where __
参数：x : PrimeSpectrum.Top R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGrpCat.hasColimitsOfSize`：∀ [UnivLE.{u, w}], CategoryTheory.Limit
s.HasColimitsOfSize.{v, u, w, w + 1} AddCommGrpCat

--- 原说明 ---
The stalk of `Spec R` at `x` is isomorphic to the stalk of `R^~` at `x`.
-/
def commRingCatStalkEquivModuleStalk (x : PrimeSpectrum.Top R) :
    ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R R).presheaf x) ≃ₗ[R]
      (structurePresheafInCommRingCat R).stalk x where
  __ := (Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙
      structurePresheafInCommRingCat R))⟩).addCommGroupIsoToAddEquiv
  map_smul' r m := by
    let α : TopCat.Presheaf.stalk (moduleStructurePresheaf R R).presheaf x ≅
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj
        ((structurePresheafInCommRingCat R).stalk x) :=
      (Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
      (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙
        structurePresheafInCommRingCat R))⟩)
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ m
    have : (TopCat.Presheaf.germ (moduleStructurePresheaf R R).presheaf U x hxU) ≫ α.hom =
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          ((structurePresheafInCommRingCat R).germ U x hxU) :=
      Limits.colimit.isoColimitCocone_ι_hom ..
    change α.hom (r • germₗ R U x hxU _) = toStalk R _ _ * _
    rw [← map_smul, Algebra.smul_def]
    refine congr($this _).trans ?_
    refine (((structurePresheafInCommRingCat R).germ U x hxU).hom.map_mul _ _).trans ?_
    congr 1
    · dsimp [toStalk]
      erw [← (structurePresheafInCommRingCat R).germ_res_apply (homOfLE (le_top : U ≤ ⊤)) _ hxU]
      rfl
    · exact congr($this _).symm

set_option backward.isDefEq.respectTransparency.types false in
public instance (x : PrimeSpectrum.Top R) :
    IsLocalization.AtPrime ((structurePresheafInCommRingCat R).stalk x) x.asIdeal := by
  refine (isLocalizedModule_iff_isLocalization' _ _).mp ?_
  convert!
    IsLocalizedModule.of_linearEquiv x.asIdeal.primeCompl (toStalkₗ R R x)
      (commRingCatStalkEquivModuleStalk R x)
  let α : TopCat.Presheaf.stalk (moduleStructurePresheaf R R).presheaf x ≅
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj
      ((structurePresheafInCommRingCat R).stalk x) :=
    (Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙
      structurePresheafInCommRingCat R))⟩)
  have : (TopCat.Presheaf.germ (moduleStructurePresheaf R R).presheaf ⊤ x (by simp)) ≫ α.hom =
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        ((structurePresheafInCommRingCat R).germ ⊤ x (by simp)) :=
    Limits.colimit.isoColimitCocone_ι_hom ..
  ext
  dsimp [toStalkₗ]
  simp only [map_one]
  refine .trans ?_ congr($this _).symm
  exact (((structurePresheafInCommRingCat R).germ ⊤ x (by simp)).hom.comp
    (algebraMap R Γ(R, _))).map_one.symm

set_option backward.isDefEq.respectTransparency.types false in
variable (R) in
/-- The stalk of `Spec R` at `x` is isomorphic to `Rₚ`,
where `p` is the prime corresponding to `x`. -/
public abbrev stalkIso (x : PrimeSpectrum R) :
    Localization.AtPrime x.asIdeal ≃ₐ[R] (structurePresheafInCommRingCat R).stalk x :=
  IsLocalization.algEquiv x.asIdeal.primeCompl _ _

end Stalk

@[expose] public section StructureSheaf

variable (R)

/-- The structure sheaf on $Spec R$, valued in `CommRingCat`.

This is provided as a bundled `SheafedSpace` as `Spec.SheafedSpace R` later. -/
/-
**AlgebraicGeometry.StructureSheaf._root_.AlgebraicGeometry.Spec.structureSheaf*
* 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure sheaf on $Spec R$, valued in `CommRingCat`.

This is provided as a bundled `SheafedSpace` as `Spec.SheafedSpace R` later.
-/
def _root_.AlgebraicGeometry.Spec.structureSheaf : Sheaf CommRingCat (PrimeSpectrum.Top R) :=
  ⟨structurePresheafInCommRingCat R,
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp _ _).mpr (TopCat.Presheaf.isSheaf_of_iso
      (structurePresheafCompForget R).symm (structureSheafInType R R).property)⟩

open Spec (structureSheaf)

/-- The canonical ring homomorphism interpreting an element of `R` as
a section of the structure sheaf. -/
@[deprecated "algebraMap" (since := "2026-02-10")]
/-
**AlgebraicGeometry.StructureSheaf.toOpen** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.StructureSheaf`。
形式化陈述：toOpen (U : Opens (PrimeSpectrum.Top R)) : CommRingCat.of R ⟶ (structureSh
eaf R).1.obj (op U)
参数：U : Opens (PrimeSpectrum.Top R)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical ring homomorphism interpreting an element of `R` as
a section of the structure sheaf.
-/
def toOpen (U : Opens (PrimeSpectrum.Top R)) :
    CommRingCat.of R ⟶ (structureSheaf R).1.obj (op U) := CommRingCat.ofHom (algebraMap _ _)

@[simp]
/-
**AlgebraicGeometry.StructureSheaf.algebraMap_self_map** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry.StructureSheaf`。
形式化陈述：algebraMap_self_map (U V : (Opens (PrimeSpectrum.Top R))ᵒᵖ) (i : V ⟶ U) : 
CommRingCat.ofHom (algebraMap R _) ≫ (Spec.structureSheaf R).1.map i = CommRingC
at.ofHom (algebraMap R _)
参数：U V : (Opens (PrimeSpectrum.Top R))ᵒᵖ；i : V ⟶ U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_self_map (U V : (Opens (PrimeSpectrum.Top R))ᵒᵖ) (i : V ⟶ U) :
    CommRingCat.ofHom (algebraMap R _) ≫ (Spec.structureSheaf R).1.map i =
      CommRingCat.ofHom (algebraMap R _) :=
  rfl

@[deprecated (since := "2026-02-10")] alias toOpen_res := algebraMap_self_map
/-
**AlgebraicGeometry.StructureSheaf.stalkAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Algeb
raicGeometry.StructureSheaf`。
形式化陈述：stalkAlgebra (p : PrimeSpectrum R) : Algebra R ((structureSheaf R).preshea
f.stalk p)
参数：p : PrimeSpectrum R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance stalkAlgebra (p : PrimeSpectrum R) : Algebra R ((structureSheaf R).presheaf.stalk p) :=
  (toStalk R p).hom.toAlgebra

@[simp]
/-
**AlgebraicGeometry.StructureSheaf.stalkAlgebra_map** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.StructureSheaf`。
形式化陈述：stalkAlgebra_map (p : PrimeSpectrum R) (r : R) : algebraMap R ((structureS
heaf R).presheaf.stalk p) r = toStalk R p r
参数：p : PrimeSpectrum R；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stalkAlgebra_map (p : PrimeSpectrum R) (r : R) :
    algebraMap R ((structureSheaf R).presheaf.stalk p) r = toStalk R p r :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Stalk of the structure sheaf at a prime p as localization of R -/
/-
**AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.StructureSheaf.IsLocalization`。
形式化陈述：∀ (R : Type u) [inst : CommRing R] (p : PrimeSpectrum R),   IsLocalization
.AtPrime (↑((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk p)) p.asIde
al
参数：R : Type u；p : PrimeSpectrum R；↑((AlgebraicGeometry.Spec.structureSheaf R).pr
esheaf.stalk p)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Stalk of the structure sheaf at a prime p as localization of R
-/
instance IsLocalization.to_stalk (p : PrimeSpectrum R) :
    IsLocalization.AtPrime ((structureSheaf R).presheaf.stalk p) p.asIdeal :=
  inferInstanceAs (IsLocalization.AtPrime ((structurePresheafInCommRingCat R).stalk p) p.asIdeal)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.StructureSheaf.openAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Algebr
aicGeometry.StructureSheaf`。
形式化陈述：openAlgebra (U : (Opens (PrimeSpectrum R))ᵒᵖ) : Algebra R ((structureSheaf
 R).obj.obj U)
参数：U : (Opens (PrimeSpectrum R))ᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance openAlgebra (U : (Opens (PrimeSpectrum R))ᵒᵖ) : Algebra R ((structureSheaf R).obj.obj U) :=
  inferInstanceAs (Algebra R ((structureSheafInType R R).presheaf.obj _))

set_option backward.isDefEq.respectTransparency.types false in
/-- Sections of the structure sheaf of Spec R on a basic open as localization of R -/
/-
**AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry.StructureSheaf.IsLocalization`。
形式化陈述：∀ (R : Type u) [inst : CommRing R] (r : R),   IsLocalization.Away r ↑((Alg
ebraicGeometry.Spec.structureSheaf R).obj.obj (Opposite.op (PrimeSpectrum.basicO
pen r)))
参数：R : Type u；r : R；(AlgebraicGeometry.Spec.structureSheaf R).obj.obj (Opposite.
op (PrimeSpectrum.basicOpen r))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sections of the structure sheaf of Spec R on a basic open as localization of R
-/
instance IsLocalization.to_basicOpen (r : R) :
    IsLocalization.Away r ((structureSheaf R).obj.obj (op <| basicOpen r)) :=
  inferInstanceAs (IsLocalization.Away r Γ(R, basicOpen r))

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.StructureSheaf.to_basicOpen_epi** 是 Mathlib 中的一个实例，位于命名空间 `A
lgebraicGeometry.StructureSheaf`。
形式化陈述：to_basicOpen_epi (r : R) : Epi (CommRingCat.ofHom <| algebraMap R ((struct
ureSheaf R).obj.obj (op <| basicOpen r)))
参数：r : R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen`：∀ (R : Typ
e u) [inst : CommRing R] (r : R),   IsLocalization.Away r ↑((AlgebraicGeometry.S
pec.structureSheaf R).obj.obj (Opposite.op (PrimeS…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CommRingCat.hom_ext_iff`：∀ {R S : CommRingCat} {f g : R ⟶ S}, f = g ↔ Co
mmRingCat.Hom.hom f = CommRingCat.Hom.hom g
-/
instance to_basicOpen_epi (r : R) :
    Epi (CommRingCat.ofHom <|
      algebraMap R ((structureSheaf R).obj.obj (op <| basicOpen r))) :=
  ⟨fun _ _ h => CommRingCat.hom_ext (IsLocalization.ringHom_ext (Submonoid.powers r)
    (CommRingCat.hom_ext_iff.mp h))⟩

/-- The ring isomorphism between the ring `R` and the global sections `Γ(X, 𝒪ₓ)`. -/
@[simps! inv]
/-
**AlgebraicGeometry.StructureSheaf.globalSectionsIso** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.StructureSheaf`。
形式化陈述：globalSectionsIso : CommRingCat.of R ≅ (structureSheaf R).1.obj (op ⊤)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.StructureSheaf.algebraMap_obj_top_bijective`：∀ {R : Ty
pe u} [inst : CommRing R],   Function.Bijective ⇑(algebraMap R ((AlgebraicGeomet
ry.structureSheafInType R R).obj.obj (Opposite.op ⊤…

--- 原说明 ---
The ring isomorphism between the ring `R` and the global sections `Γ(X, 𝒪ₓ)`.
-/
def globalSectionsIso : CommRingCat.of R ≅ (structureSheaf R).1.obj (op ⊤) :=
  RingEquiv.toCommRingCatIso (.ofBijective _ algebraMap_obj_top_bijective)
/-
**AlgebraicGeometry.StructureSheaf.globalSectionsIso_hom** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.StructureSheaf`。
形式化陈述：globalSectionsIso_hom (R : CommRingCat) : (globalSectionsIso R).hom = Comm
RingCat.ofHom (algebraMap _ _)
参数：R : CommRingCat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem globalSectionsIso_hom (R : CommRingCat) :
    (globalSectionsIso R).hom = CommRingCat.ofHom (algebraMap _ _) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc, elementwise nosimp]
/-
**AlgebraicGeometry.StructureSheaf.toStalk_stalkSpecializes** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.StructureSheaf`。
形式化陈述：toStalk_stalkSpecializes {R : Type*} [CommRing R] {x y : PrimeSpectrum R} 
(h : x ⤳ y) : toStalk R y ≫ (structureSheaf R).presheaf.stalkSpecializes h = toS
talk R x
参数：h : x ⤳ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `trivial`：True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `TopCat.Presheaf.germ_stalkSpecializes`：germ_stalkSpecializes (F : X.Pres
heaf C) {U : Opens X} {y : X} (hy : y in U) {x : X} (h : x ⤳ y) : F.germ U y hy 
≫ F.stalkSpecializes h = F.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toStalk_stalkSpecializes {R : Type*} [CommRing R] {x y : PrimeSpectrum R} (h : x ⤳ y) :
    toStalk R y ≫ (structureSheaf R).presheaf.stalkSpecializes h = toStalk R x := by
  dsimp [toStalk]
  simp [structureSheaf]

end StructureSheaf

@[expose] public section Comap

variable {S : Type u} [CommRing S] {N : Type u} [AddCommGroup N] [Module S N]
  {σ : R →+* S} (f : M →ₛₗ[σ] N)

set_option backward.isDefEq.respectTransparency false in
/-- The map `M_{f y} ⟶ N_{y}` used to build maps between structure sheaves. -/
/-
**AlgebraicGeometry.Localizations.comapFun** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `M_{f y} ⟶ N_{y}` used to build maps between structure sheaves.
-/
def Localizations.comapFun (y : PrimeSpectrum.Top S) :
    Localizations M (y.comap σ) →ₛₗ[σ] Localizations N y :=
  letI := Module.compHom N σ
  letI := σ.toAlgebra
  haveI : IsScalarTower R S N := .of_algebraMap_smul fun _ _ ↦ rfl
  letI f' : M →ₗ[R] N := { __ := f }
  letI g : LocalizedModule (y.comap σ).asIdeal.primeCompl M →ₗ[R]
      LocalizedModule y.asIdeal.primeCompl N :=
    IsLocalizedModule.lift (y.comap σ).asIdeal.primeCompl (LocalizedModule.mkLinearMap _ _)
      ((LocalizedModule.mkLinearMap _ _).restrictScalars R ∘ₗ f') (by
      intro x
      have := IsLocalizedModule.map_units (S := y.asIdeal.primeCompl)
        (LocalizedModule.mkLinearMap y.asIdeal.primeCompl N) ⟨σ x, x.2⟩
      rw [Module.End.isUnit_iff] at this ⊢
      convert! this using 2 with a
      exact (IsScalarTower.algebraMap_smul ..).symm)
  { __ := g,
    map_smul' r x := by simpa [Localizations] using! (IsScalarTower.algebraMap_smul ..).symm }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.Localizations.comapFun_mk** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Localizations.comapFun_mk (y : PrimeSpectrum.Top S)
    (a : M) (b : (y.comap σ).asIdeal.primeCompl) :
    Localizations.comapFun f y (.mk a b) = .mk (f a) ⟨σ b.1, b.2⟩ := by
  let := Module.compHom N σ
  let := σ.toAlgebra
  have : IsScalarTower R S N := .of_algebraMap_smul fun _ _ ↦ rfl
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (S := y.asIdeal.primeCompl)
    (LocalizedModule.mkLinearMap y.asIdeal.primeCompl N) ⟨σ b, b.2⟩)).1
  dsimp
  rw [← (comapFun f y).map_smulₛₗ, LocalizedModule.smul'_mk, ← Submonoid.smul_def,
    LocalizedModule.mk_cancel, ← LocalizedModule.mkLinearMap_apply]
  dsimp [comapFun, Localizations]
  refine (IsLocalizedModule.lift_apply ..).trans ?_
  dsimp
  rw [← LocalizedModule.mk_cancel ⟨σ b.1, b.2⟩, LocalizedModule.smul'_mk]
  rfl

/--
Given a ring homomorphism `f : R →+* S`, an open set `U` of the prime spectrum of `R` and an open
set `V` of the prime spectrum of `S`, such that `V ⊆ (comap f) ⁻¹' U`, we can push a section `s`
on `U` to a section on `V`, by composing with `Localization.localRingHom _ _ f` from the left and
`comap f` from the right. Explicitly, if `s` evaluates on `comap f p` to `a / b`, its image on `V`
evaluates on `p` to `f(a) / f(b)`.

At the moment, we work with arbitrary dependent functions `s : Π x : U, Localizations R x`. Below,
we prove the predicate `isLocallyFraction` is preserved by this map, hence it can be extended to
a morphism between the structure sheaves of `R` and `S`.
-/
/-
**AlgebraicGeometry.comapFun** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a ring homomorphism `f : R →+* S`, an open set `U` of the prime spectrum o
f `R` and an open
set `V` of the prime spectrum of `S`, such that `V ⊆ (comap f) ⁻¹' U`, we can pu
sh a section `s`
on `U` to a section on `V`, by composing with `Localization.localRingHom _ _ f` 
from the left and
`comap f` from the right. Explicitly, if `s` evaluates on `comap f p` to `a / b`
, its image on `V`
evaluates on `p` to `f(a) / f(b)`.

At the moment, we work with arbitrary dependent functions `s : Π x : U, Localiza
tions R x`. Below,
we prove the predicate `isLocallyFraction` is preserved by this map, hence it ca
n be extended to
a morphism between the structure sheaves of `R` and `S`.
-/
def comapFun (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap σ ⁻¹' U.1) (s : ∀ x : U, Localizations M x.1) (y : V) :
    Localizations N y.1 :=
  Localizations.comapFun f _ (s ⟨y.1.comap σ, hUV y.2⟩)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.isLocallyFraction_comapFun** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isLocallyFraction_comapFun (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 ⊆ PrimeSpectrum.comap σ ⁻¹' U.1)
    (s : ∀ x : U, Localizations M x.1) (hs : (isLocallyFraction R M).toPrelocalPredicate.pred s) :
    (isLocallyFraction S N).toPrelocalPredicate.pred (comapFun f U V hUV s) := by
  let := Module.compHom N σ
  let := σ.toAlgebra
  have : IsScalarTower R S N := .of_algebraMap_smul fun _ _ ↦ rfl
  rintro ⟨p, hpV⟩
  obtain ⟨W, m, iWU, a, b, h_frac⟩ := hs ⟨PrimeSpectrum.comap σ p, hUV hpV⟩
  refine ⟨⟨_, (PrimeSpectrum.continuous_comap σ).isOpen_preimage _ W.2⟩ ⊓ V,
    ⟨m, hpV⟩, Opens.infLERight _ _, f a, σ b, ?_⟩
  rintro ⟨q, ⟨hqW, hqV⟩⟩
  obtain ⟨hs, H⟩ := h_frac ⟨PrimeSpectrum.comap σ q, hqW⟩
  refine ⟨hs, ?_⟩
  dsimp [comapFun] at H ⊢
  rw [H]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-- For a ring homomorphism `f : R →+* S` and open sets `U` and `V` of the prime spectra of `R` and
`S` such that `V ⊆ (comap f) ⁻¹ U`, the induced ring homomorphism from the structure sheaf of `R`
at `U` to the structure sheaf of `S` at `V`.

Explicitly, this map is given as follows: For a point `p : V`, if the section `s` evaluates on `p`
to the fraction `a / b`, its image on `V` evaluates on `p` to the fraction `f(a) / f(b)`.
-/
/-
**AlgebraicGeometry.comap** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a ring homomorphism `f : R →+* S` and open sets `U` and `V` of the prime spe
ctra of `R` and
`S` such that `V ⊆ (comap f) ⁻¹ U`, the induced ring homomorphism from the struc
ture sheaf of `R`
at `U` to the structure sheaf of `S` at `V`.

Explicitly, this map is given as follows: For a point `p : V`, if the section `s
` evaluates on `p`
to the fraction `a / b`, its image on `V` evaluates on `p` to the fraction `f(a)
 / f(b)`.
-/
def comapₗ (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap σ ⁻¹' U.1) :
    Γ(M, U) →ₛₗ[σ] Γ(N, V) where
  toFun s := ⟨comapFun f U V hUV s.1, isLocallyFraction_comapFun f U V hUV s.1 s.2⟩
  map_add' s t := Subtype.ext <| funext fun _ ↦ by dsimp [comapFun]; rw [map_add]
  map_smul' r m := Subtype.ext <| funext fun _ ↦ by
    dsimp [comapFun]
    rw [map_smulₛₗ, ← IsScalarTower.algebraMap_smul S]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.comap** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comapₗ_const (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap σ ⁻¹' U.1) (a : M) (b : R) (hb : U ≤ basicOpen b) :
    comapₗ f U V hUV (const a b U hb) = const (f a) (σ b) V (hUV.trans (Set.preimage_mono hb)) :=
  Subtype.ext <| funext fun _ ↦ by simp [comapₗ, comapFun]

section Ring

open Spec (structureSheaf)

variable {S : Type u} [CommRing S] {P : Type u} [CommRing P]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.comap** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comapₗ_eq_localRingHom (f : R →+* S) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1)
    (s : (structureSheaf R).1.obj (op U)) (p : V) :
    (comapₗ f.toSemilinearMap U V hUV s).1 p =
      Localization.localRingHom (PrimeSpectrum.comap f p.1).asIdeal _ f rfl
        (s.1 ⟨PrimeSpectrum.comap f p.1, hUV p.2⟩) := by
  dsimp [comapₗ, comapFun]
  suffices ⇑(Localizations.comapFun f.toSemilinearMap p.1) =
      ⇑(Localization.localRingHom (PrimeSpectrum.comap f p.1).asIdeal _ f rfl) from
    congr($this _)
  ext m
  induction m using LocalizedModule.induction_on with | h m s =>
  trans LocalizedModule.mk (f m) ⟨f ↑s, s.2⟩
  · simp
  convert_to! Localization.mk _ _ = Localization.localRingHom _ _ _ _ (Localization.mk _ _)
  simp [Localization.mk_eq_mk']

set_option backward.isDefEq.respectTransparency.types false in
/-- For a ring homomorphism `f : R →+* S` and open sets `U` and `V` of the prime spectra of `R` and
`S` such that `V ⊆ (comap f) ⁻¹ U`, the induced ring homomorphism from the structure sheaf of `R`
at `U` to the structure sheaf of `S` at `V`.

Explicitly, this map is given as follows: For a point `p : V`, if the section `s` evaluates on `p`
to the fraction `a / b`, its image on `V` evaluates on `p` to the fraction `f(a) / f(b)`.
-/
/-
**AlgebraicGeometry.comap** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a ring homomorphism `f : R →+* S` and open sets `U` and `V` of the prime spe
ctra of `R` and
`S` such that `V ⊆ (comap f) ⁻¹ U`, the induced ring homomorphism from the struc
ture sheaf of `R`
at `U` to the structure sheaf of `S` at `V`.

Explicitly, this map is given as follows: For a point `p : V`, if the section `s
` evaluates on `p`
to the fraction `a / b`, its image on `V` evaluates on `p` to the fraction `f(a)
 / f(b)`.
-/
def comap (f : R →+* S) (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) :
    (structureSheaf R).1.obj (op U) →+* (structureSheaf S).1.obj (op V) where
  __ := comapₗ f.toSemilinearMap U V hUV
  map_one' := Subtype.ext <| funext fun _ ↦ by
    dsimp
    simp only [comapₗ_eq_localRingHom, PrimeSpectrum.comap_asIdeal]
    exact (Localization.localRingHom ..).map_one
  map_mul' r s := Subtype.ext <| funext fun p ↦ by
    dsimp
    change _ = (comapₗ f.toSemilinearMap U V hUV r).1 p * (comapₗ f.toSemilinearMap U V hUV s).1 p
    simp only [comapₗ_eq_localRingHom, PrimeSpectrum.comap_asIdeal]
    exact (Localization.localRingHom ..).map_mul _ _
  map_zero' := Subtype.ext <| funext fun _ ↦ by
    dsimp
    simp only [comapₗ_eq_localRingHom, PrimeSpectrum.comap_asIdeal]
    exact (Localization.localRingHom ..).map_zero

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.comap_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_apply (f : R →+* S) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1)
    (s : (structureSheaf R).1.obj (op U)) (p : V) :
    (comap f U V hUV s).1 p =
      Localization.localRingHom (PrimeSpectrum.comap f p.1).asIdeal _ f rfl
        (s.1 ⟨PrimeSpectrum.comap f p.1, hUV p.2⟩) :=
  comapₗ_eq_localRingHom ..

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.comap_const** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_const (f : R →+* S) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) (a b : R)
    (hb : ∀ x : PrimeSpectrum R, x ∈ U → b ∈ x.asIdeal.primeCompl) :
    comap f U V hUV (const a b U hb) =
      const (f a) (f b) V fun p hpV => hb (PrimeSpectrum.comap f p) (hUV hpV) :=
  Subtype.ext <| funext fun p => by
    rw [comap_apply, const_apply, const_apply]
    convert_to! Localization.localRingHom _ _ _ _ (Localization.mk _ _) = Localization.mk _ _
    simp [Localization.mk_eq_mk']

set_option backward.isDefEq.respectTransparency.types false in
/-- For an inclusion `i : V ⟶ U` between open sets of the prime spectrum of `R`, the comap of the
identity from OO_X(U) to OO_X(V) equals as the restriction map of the structure sheaf.

This is a generalization of the fact that, for fixed `U`, the comap of the identity from OO_X(U)
to OO_X(U) is the identity.
-/
/-
**AlgebraicGeometry.comap_id_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an inclusion `i : V ⟶ U` between open sets of the prime spectrum of `R`, the
 comap of the
identity from OO_X(U) to OO_X(V) equals as the restriction map of the structure 
sheaf.

This is a generalization of the fact that, for fixed `U`, the comap of the ident
ity from OO_X(U)
to OO_X(U) is the identity.
-/
theorem comap_id_eq_map (U V : Opens (PrimeSpectrum.Top R)) (iVU : V ⟶ U) :
    (comap (RingHom.id R) U V fun _ hpV => leOfHom iVU <| hpV) =
      ((structureSheaf R).1.map iVU.op).hom :=
  RingHom.ext fun s => Subtype.ext <| funext fun p => by
    rw [comap_apply]
    exact congr($(Localization.localRingHom_id ..) _)

/--
The comap of the identity is the identity. In this variant of the lemma, two open subsets `U` and
`V` are given as arguments, together with a proof that `U = V`. This is useful when `U` and `V`
are not definitionally equal.
-/
/-
**AlgebraicGeometry.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comap of the identity is the identity. In this variant of the lemma, two ope
n subsets `U` and
`V` are given as arguments, together with a proof that `U = V`. This is useful w
hen `U` and `V`
are not definitionally equal.
-/
theorem comap_id {U V : Opens (PrimeSpectrum.Top R)} (hUV : U = V) :
    (comap (RingHom.id R) U V fun p hpV => by rwa [hUV, PrimeSpectrum.comap_id]) =
      (eqToHom (show (structureSheaf R).1.obj (op U) = _ by rw [hUV])).hom := by
  rw [comap_id_eq_map U V (eqToHom hUV.symm), eqToHom_op, eqToHom_map]

@[simp]
/-
**AlgebraicGeometry.comap_id'** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_id' (U : Opens (PrimeSpectrum.Top R)) :
    (comap (RingHom.id R) U U fun p hpU => by rwa [PrimeSpectrum.comap_id]) = RingHom.id _ := by
  rw [comap_id rfl]; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.comap_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comp (f : R →+* S) (g : S →+* P) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (W : Opens (PrimeSpectrum.Top P))
    (hUV : ∀ p ∈ V, PrimeSpectrum.comap f p ∈ U) (hVW : ∀ p ∈ W, PrimeSpectrum.comap g p ∈ V) :
    (comap (g.comp f) U W fun p hpW => hUV (PrimeSpectrum.comap g p) (hVW p hpW)) =
      (comap g V W hVW).comp (comap f U V hUV) :=
  RingHom.ext fun s =>
    Subtype.ext <|
      funext fun p => by
        rw [comap_apply, Localization.localRingHom_comp _ (PrimeSpectrum.comap g p.1).asIdeal] <;>
        simp

set_option backward.isDefEq.respectTransparency.types false in
@[elementwise, reassoc]
/-
**AlgebraicGeometry.toOpen_comp_comap** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeomet
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOpen_comp_comap (f : R →+* S) (U : Opens (PrimeSpectrum.Top R)) :
    CommRingCat.ofHom (algebraMap _ _) ≫
      CommRingCat.ofHom (comap f U (Opens.comap ⟨_, PrimeSpectrum.continuous_comap f⟩ U)
        fun _ ↦ id) =
      CommRingCat.ofHom f ≫ CommRingCat.ofHom (algebraMap _ _) :=
  CommRingCat.hom_ext <| RingHom.ext fun _ ↦ Subtype.ext <| funext fun x ↦ by
    dsimp
    rw [comap_apply]
    exact Localization.localRingHom_to_map _ _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.comap_basicOpen** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_basicOpen (f : R →+* S) (x : R) :
    comap f (PrimeSpectrum.basicOpen x) (PrimeSpectrum.basicOpen (f x))
        (PrimeSpectrum.comap_basicOpen f x).le =
      IsLocalization.map (M := .powers x) (T := .powers (f x)) _ f
        (Submonoid.powers_le.mpr (Submonoid.mem_powers _)) :=
  IsLocalization.ringHom_ext (.powers x) <| by
    simpa [CommRingCat.hom_ext_iff] using! toOpen_comp_comap f _

end Ring

end Comap

end StructureSheaf

end AlgebraicGeometry

