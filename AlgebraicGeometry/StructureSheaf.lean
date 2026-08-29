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
/--
Definition of `PrimeSpectrum.Top` / `PrimeSpectrum.Top` 的定义

English:
definition PrimeSpectrum.Top
  signature: : TopCat
  body: TopCat.of (PrimeSpectrum R)

中文:
定义 PrimeSpectrum.Top
  签名: : TopCat
  定义体: TopCat.of (PrimeSpectrum R)

Depends on / 依赖: PrimeSpectrum, TopCat, TopCat.of
-/
def PrimeSpectrum.Top : TopCat := TopCat.of (PrimeSpectrum R)

namespace StructureSheaf

variable {P : PrimeSpectrum.Top R}

set_option backward.isDefEq.respectTransparency.types false in
variable (M P) in
/--
Definition of `Localizations` / `Localizations` 的定义

English:
abbreviation Localizations
  signature: : Type u
  body: LocalizedModule P.asIdeal.primeCompl M

中文:
缩写 Localizations
  签名: : 类型u
  定义体: LocalizedModule P.asIdeal.primeCompl M

Depends on / 依赖: LocalizedModule, P.asIdeal.primeCompl, asIdeal, primeCompl
-/
abbrev Localizations : Type u := LocalizedModule P.asIdeal.primeCompl M

/--
Definition of `IsFraction` / `IsFraction` 的定义

English:
definition IsFraction
  signature: {U : Opens (PrimeSpectrum.Top R)} (f : Π x : U, Localizations M x.1)
  body: exists r s, forall x : U, exists hs : s ∉ x.1.asIdeal, f x = LocalizedModule.mk r ⟨s, hs⟩

中文:
定义 IsFraction
  签名: {U : Opens (PrimeSpectrum.Top R)} (f : Π x : U, Localizations M x.1)
  定义体: exists r s, forall x : U, exists hs : s ∉ x.1.asIdeal, f x = LocalizedModule.mk r ⟨s, hs⟩

Depends on / 依赖: LocalizedModule, LocalizedModule.mk, asIdeal
-/
def IsFraction {U : Opens (PrimeSpectrum.Top R)} (f : Π x : U, Localizations M x.1) : Prop :=
  exists r s, forall x : U, exists hs : s ∉ x.1.asIdeal, f x = LocalizedModule.mk r ⟨s, hs⟩

variable (R M) in
/--
Definition of `isFractionPrelocal` / `isFractionPrelocal` 的定义

English:
definition isFractionPrelocal
  signature: : PrelocalPredicate (Localizations (R := R) M) where
  body: IsFraction f
  res := by rintro V U i f ⟨r, s, w⟩; exact ⟨r, s, fun x => w (i x)⟩

中文:
定义 isFractionPrelocal
  签名: : PrelocalPredicate (Localizations (R := R) M) where
  定义体: IsFraction f
  res := by rintro V U i f ⟨r, s, w⟩; exact ⟨r, s, fun x => w (i x)⟩
-/
def isFractionPrelocal : PrelocalPredicate (Localizations (R := R) M) where
  pred {_} f := IsFraction f
  res := by rintro V U i f ⟨r, s, w⟩; exact ⟨r, s, fun x => w (i x)⟩

variable (R M) in
/--
Definition of `isLocallyFraction` / `isLocallyFraction` 的定义

English:
definition isLocallyFraction
  signature: : LocalPredicate (Localizations (R := R) M)
  body: (isFractionPrelocal R M).sheafify

中文:
定义 isLocallyFraction
  签名: : LocalPredicate (Localizations (R := R) M)
  定义体: (isFractionPrelocal R M).sheafify
-/
def isLocallyFraction : LocalPredicate (Localizations (R := R) M) :=
  (isFractionPrelocal R M).sheafify

set_option backward.isDefEq.respectTransparency.types false in
variable (M) in
/--
Definition of `sectionsSubmodule` / `sectionsSubmodule` 的定义

English:
definition sectionsSubmodule
  signature: (U : (Opens (PrimeSpectrum.Top R)))
  body: { f | (isLocallyFraction R M).pred f }
  add_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, sb • ra + sa • rb, sa * sb, fun x => ?_⟩
    obtain ⟨hsax, hsa⟩ := wa ⟨x.1, x.2.1⟩
  

中文:
定义 sectionsSubmodule
  签名: (U : (Opens (PrimeSpectrum.Top R)))
  定义体: { f | (isLocallyFraction R M).pred f }
  add_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, sb • ra + sa • rb, sa * sb, fun x => ?_⟩
    obtain ⟨hsax, hsa⟩ := wa ⟨x.1, x.2.1⟩
  

Depends on / 依赖: isLocallyFraction
-/
def sectionsSubmodule (U : (Opens (PrimeSpectrum.Top R))) :
    Submodule R (Π x : U, Localizations M x.1) where
  carrier := { f | (isLocallyFraction R M).pred f }
  add_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, sb • ra + sa • rb, sa * sb, fun x => ?_⟩
    obtain ⟨hsax, hsa⟩ := wa ⟨x.1, x.2.1⟩
    obtain ⟨hsbx, hsb⟩ := wb ⟨x.1, x.2.2⟩
    exact ⟨x.1.asIdeal.primeCompl.mul_mem hsax hsbx,
      congr($hsa + $hsb).trans (LocalizedModule.mk_add_mk ..)⟩
  zero_mem' x := ⟨U, x.2, 𝟙 _, 0, 1, fun y => by simp [Ideal.IsPrime.one_notMem]⟩
  smul_mem' r {a} ha x := by
    obtain ⟨V, m, i, ra, sa, wa⟩ := ha x
    exact ⟨V, m, i, r • ra, sa, fun x => ⟨(wa x).1,
      congr(r • $((wa x).2)).trans (LocalizedModule.smul'_mk ..)⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
variable (A) in
/--
Definition of `sectionsSubalgebra` / `sectionsSubalgebra` 的定义

English:
definition sectionsSubalgebra
  signature: (U : (Opens (PrimeSpectrum.Top R)))
  body: sectionsSubmodule A U
  mul_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ra * rb, sa * sb, fun x => ?_⟩
    obtain ⟨hsax, hsa⟩ := wa ⟨x.1, x.2.1⟩
    obtain ⟨hsbx, hsb⟩ := wb 

中文:
定义 sectionsSubalgebra
  签名: (U : (Opens (PrimeSpectrum.Top R)))
  定义体: sectionsSubmodule A U
  mul_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ra * rb, sa * sb, fun x => ?_⟩
    obtain ⟨hsax, hsa⟩ := wa ⟨x.1, x.2.1⟩
    obtain ⟨hsbx, hsb⟩ := wb 

Depends on / 依赖: sectionsSubmodule
-/
def sectionsSubalgebra (U : (Opens (PrimeSpectrum.Top R))) :
    Subalgebra R (Π x : U, Localizations A x.1) where
  __ := sectionsSubmodule A U
  mul_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ra * rb, sa * sb, fun x => ?_⟩
    obtain ⟨hsax, hsa⟩ := wa ⟨x.1, x.2.1⟩
    obtain ⟨hsbx, hsb⟩ := wb ⟨x.1, x.2.2⟩
    exact ⟨x.1.asIdeal.primeCompl.mul_mem hsax hsbx,
      congr($hsa * $hsb).trans (LocalizedModule.mk_mul_mk ..)⟩
  algebraMap_mem' r x :=
    ⟨U, x.2, 𝟙 _, algebraMap R A r, 1, fun y => ⟨by simp [Ideal.IsPrime.one_notMem], rfl⟩⟩

set_option backward.isDefEq.respectTransparency false in
variable (M) in
/--
Definition of `sectionsSubalgebraSubmodule` / `sectionsSubalgebraSubmodule` 的定义

English:
definition sectionsSubalgebraSubmodule
  signature: (U : (Opens (PrimeSpectrum.Top R)))
  body: sectionsSubmodule M U
  smul_mem' r {a} ha x := by
    obtain ⟨V, hxV, hVU, rx, rs, hr⟩ := r.2 x
    obtain ⟨W, hxW, hWU, ax, as, ha⟩ := ha x
    refine ⟨V ⊓ W, ⟨hxV, hxW⟩, homOfLE (inf_le_left.trans hVU.le), rx • ax, as * rs, fun y => ?_⟩
    obtain ⟨hrsy, hry⟩ := hr ⟨y.1, y.2.1⟩
    obtain ⟨hasy, 

中文:
定义 sectionsSubalgebraSubmodule
  签名: (U : (Opens (PrimeSpectrum.Top R)))
  定义体: sectionsSubmodule M U
  smul_mem' r {a} ha x := by
    obtain ⟨V, hxV, hVU, rx, rs, hr⟩ := r.2 x
    obtain ⟨W, hxW, hWU, ax, as, ha⟩ := ha x
    refine ⟨V ⊓ W, ⟨hxV, hxW⟩, homOfLE (inf_le_left.trans hVU.le), rx • ax, as * rs, fun y => ?_⟩
    obtain ⟨hrsy, hry⟩ := hr ⟨y.1, y.2.1⟩
    obtain ⟨hasy, 

Depends on / 依赖: sectionsSubmodule
-/
def sectionsSubalgebraSubmodule (U : (Opens (PrimeSpectrum.Top R))) :
    Submodule (sectionsSubalgebra R U) (Π x : U, Localizations M x.1) where
  __ := sectionsSubmodule M U
  smul_mem' r {a} ha x := by
    obtain ⟨V, hxV, hVU, rx, rs, hr⟩ := r.2 x
    obtain ⟨W, hxW, hWU, ax, as, ha⟩ := ha x
    refine ⟨V ⊓ W, ⟨hxV, hxW⟩, homOfLE (inf_le_left.trans hVU.le), rx • ax, as * rs, fun y => ?_⟩
    obtain ⟨hrsy, hry⟩ := hr ⟨y.1, y.2.1⟩
    obtain ⟨hasy, hay⟩ := ha ⟨y.1, y.2.2⟩
    exact ⟨y.1.asIdeal.primeCompl.mul_mem hasy hrsy, congr($hry • $hay)⟩

end StructureSheaf

open StructureSheaf

variable (R M) in
/--
Definition of `structureSheafInType` / `structureSheafInType` 的定义

English:
definition structureSheafInType
  signature: : Sheaf (Type u) (PrimeSpectrum.Top R)
  body: subsheafToTypes (isLocallyFraction R M)

中文:
定义 structureSheafInType
  签名: : Sheaf (类型u) (PrimeSpectrum.Top R)
  定义体: subsheafToTypes (isLocallyFraction R M)

Depends on / 依赖: isLocallyFraction, subsheafToTypes
-/
def structureSheafInType : Sheaf (Type u) (PrimeSpectrum.Top R) :=
  subsheafToTypes (isLocallyFraction R M)

instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    AddCommGroup ((structureSheafInType R M).obj.obj U) :=
  (sectionsSubmodule M U.unop).toAddSubgroup.toAddCommGroup

instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Module R ((structureSheafInType R M).obj.obj U) :=
  (sectionsSubmodule M U.unop).module

instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    CommRing ((structureSheafInType R A).obj.obj U) :=
  (sectionsSubalgebra A U.unop).toCommRing

instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Algebra R ((structureSheafInType R A).obj.obj U) :=
  (sectionsSubalgebra A U.unop).algebra

local notation "Γ(" M ", " U ")" =>
  (Functor.obj (ObjectProperty.FullSubcategory.obj (structureSheafInType _ M))) (Opposite.op U)

@[simp]
/--
lemma `structureSheafInType.add_apply` / 引理 `structureSheafInType.add_apply`

English:
lemma structureSheafInType.add_apply
  given: {U : Opens (PrimeSpectrum.Top R)} (s t : Γ(M, U)) (x : U)
  proof: rfl

@[simp]

中文:
引理 structureSheafInType.add_apply
  条件: {U : Opens (PrimeSpectrum.Top R)} (s t : Γ(M, U)) (x : U)
  证明: rfl

@[simp]
-/
lemma structureSheafInType.add_apply {U : Opens (PrimeSpectrum.Top R)} (s t : Γ(M, U)) (x : U) :
  (s + t).1 x = s.1 x + t.1 x := rfl

@[simp]
/--
lemma `structureSheafInType.mul_apply` / 引理 `structureSheafInType.mul_apply`

English:
lemma structureSheafInType.mul_apply
  given: {U : Opens (PrimeSpectrum.Top R)} (s t : Γ(A, U)) (x : U)
  proof: rfl

@[simp]

中文:
引理 structureSheafInType.mul_apply
  条件: {U : Opens (PrimeSpectrum.Top R)} (s t : Γ(A, U)) (x : U)
  证明: rfl

@[simp]
-/
lemma structureSheafInType.mul_apply {U : Opens (PrimeSpectrum.Top R)} (s t : Γ(A, U)) (x : U) :
  (s * t).1 x = s.1 x * t.1 x := rfl

@[simp]
/--
lemma `structureSheafInType.smul_apply` / 引理 `structureSheafInType.smul_apply`

English:
lemma structureSheafInType.smul_apply
  statement: {U : Opens (PrimeSpectrum.Top R)}
  proof: rfl

中文:
引理 structureSheafInType.smul_apply
  结论: {U : Opens (PrimeSpectrum.Top R)}
  证明: rfl
-/
lemma structureSheafInType.smul_apply {U : Opens (PrimeSpectrum.Top R)}
    (r : R) (s : Γ(M, U)) (x : U) :
  (r • s).1 x = r • s.1 x := rfl

variable (R M) in
/-- The structure presheaf, valued in `ModuleCat`, constructed by dressing up the `Type`-valued
structure presheaf. -/
@[simps obj_carrier]
/--
Definition of `structurePresheafInModuleCat` / `structurePresheafInModuleCat` 的定义

English:
definition structurePresheafInModuleCat
  signature: : Presheaf (ModuleCat R) (PrimeSpectrum.Top R) where
  body: ModuleCat.of R ((structureSheafInType R M).1.obj U)
  map i := ModuleCat.ofHom
    { toFun := (structureSheafInType R M).1.map i
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

中文:
定义 structurePresheafInModuleCat
  签名: : Presheaf (ModuleCat R) (PrimeSpectrum.Top R) where
  定义体: ModuleCat.of R ((structureSheafInType R M).1.obj U)
  map i := ModuleCat.ofHom
    { toFun := (structureSheafInType R M).1.map i
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

Depends on / 依赖: ModuleCat, ModuleCat.of, structureSheafInType
-/
def structurePresheafInModuleCat : Presheaf (ModuleCat R) (PrimeSpectrum.Top R) where
  obj U := ModuleCat.of R ((structureSheafInType R M).1.obj U)
  map i := ModuleCat.ofHom
    { toFun := (structureSheafInType R M).1.map i
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

variable (R) in
/-- The structure presheaf, valued in `CommRingCat`, constructed by dressing up the `Type`-valued
structure presheaf. -/
@[simps obj_carrier]
/--
Definition of `structurePresheafInCommRingCat` / `structurePresheafInCommRingCat` 的定义

English:
definition structurePresheafInCommRingCat
  signature: : Presheaf CommRingCat (PrimeSpectrum.Top R) where
  body: .of ((structureSheafInType R R).1.obj U)
  map i := CommRingCat.ofHom
    { toFun := (structureSheafInType R R).1.map i
      map_add' _ _ := rfl
      map_mul' _ _ := rfl
      map_one' := rfl
      map_zero' := rfl }

中文:
定义 structurePresheafInCommRingCat
  签名: : Presheaf CommRingCat (PrimeSpectrum.Top R) where
  定义体: .of ((structureSheafInType R R).1.obj U)
  map i := CommRingCat.ofHom
    { toFun := (structureSheafInType R R).1.map i
      map_add' _ _ := rfl
      map_mul' _ _ := rfl
      map_one' := rfl
      map_zero' := rfl }

Depends on / 依赖: structureSheafInType
-/
def structurePresheafInCommRingCat : Presheaf CommRingCat (PrimeSpectrum.Top R) where
  obj U := .of ((structureSheafInType R R).1.obj U)
  map i := CommRingCat.ofHom
    { toFun := (structureSheafInType R R).1.map i
      map_add' _ _ := rfl
      map_mul' _ _ := rfl
      map_one' := rfl
      map_zero' := rfl }

instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Module ((structureSheafInType R R).obj.obj U) ((structureSheafInType R M).obj.obj U) :=
  inferInstanceAs (Module (sectionsSubalgebra R _) (sectionsSubalgebraSubmodule M _))

instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    IsScalarTower R ((structureSheafInType R R).obj.obj U) ((structureSheafInType R M).obj.obj U) :=
.of_algebraMap_smul fun r m => Subtype.ext funext fun x =>
    IsScalarTower.algebraMap_smul (Localizations R x.1) r (m.1 x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (R M) in
/--
Definition of `moduleStructurePresheaf` / `moduleStructurePresheaf` 的定义

English:
definition moduleStructurePresheaf
  signature: : PresheafOfModules (structurePresheafInCommRingCat R ⋙ forget₂ _ _)
  body: letI (X : (Opens ↑(PrimeSpectrum.Top R))ᵒᵖ) :
    Module ↑((structurePresheafInCommRingCat R ⋙ forget₂ CommRingCat RingCat).obj X)
      ↑((structurePresheafInModuleCat R M ⋙ forget₂ (ModuleCat R) Ab).obj X) := by
    dsimp; infer_instance
  .ofPresheaf (structurePresheafInModuleCat R M ⋙ forget₂ _ 

中文:
定义 moduleStructurePresheaf
  签名: : PresheafOfModules (structurePresheafInCommRingCat R ⋙ forget₂ _ _)
  定义体: letI (X : (Opens ↑(PrimeSpectrum.Top R))ᵒᵖ) :
    Module ↑((structurePresheafInCommRingCat R ⋙ forget₂ CommRingCat RingCat).obj X)
      ↑((structurePresheafInModuleCat R M ⋙ forget₂ (ModuleCat R) Ab).obj X) := by
    dsimp; infer_instance
  .ofPresheaf (structurePresheafInModuleCat R M ⋙ forget₂ _ 

Depends on / 依赖: CommRingCat, Module, ModuleCat, PrimeSpectrum, PrimeSpectrum.Top, RingCat, infer_instance, ofPresheaf, structurePresheafInCommRingCat, structurePresheafInModuleCat
-/
def moduleStructurePresheaf : PresheafOfModules (structurePresheafInCommRingCat R ⋙ forget₂ _ _) :=
  letI (X : (Opens ↑(PrimeSpectrum.Top R))ᵒᵖ) :
    Module ↑((structurePresheafInCommRingCat R ⋙ forget₂ CommRingCat RingCat).obj X)
      ↑((structurePresheafInModuleCat R M ⋙ forget₂ (ModuleCat R) Ab).obj X) := by
    dsimp; infer_instance
  .ofPresheaf (structurePresheafInModuleCat R M ⋙ forget₂ _ _) fun X Y f r m => rfl

variable (R) in
/--
Definition of `structurePresheafCompForget` / `structurePresheafCompForget` 的定义

English:
definition structurePresheafCompForget
  signature: :
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 structurePresheafCompForget
  签名: :
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def structurePresheafCompForget :
    structurePresheafInCommRingCat R ⋙ forget CommRingCat ≅ (structureSheafInType R R).1 :=
  NatIso.ofComponents fun _ => Iso.refl _

open TopCat.Presheaf


open TopCat.Presheaf

namespace StructureSheaf

@[simp]
/--
theorem `res_apply` / 定理 `res_apply`

English:
theorem res_apply
  statement: (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U)
  proof: rfl

中文:
定理 res_apply
  结论: (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U)
  证明: rfl
-/
theorem res_apply (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U)
    (s : Γ(M, U)) (x : V) : ((structureSheafInType R M).1.map i.op s).1 x = s.1 (i x) :=
  rfl

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (f : M) (g : R) (U : Opens (PrimeSpectrum.Top R))
  body: ⟨fun x => .mk f ⟨g, hu x.2⟩, fun x => ⟨U, x.2, 𝟙 _, f, g, fun y => ⟨hu y.2, rfl⟩⟩⟩

中文:
定义 const
  签名: (f : M) (g : R) (U : Opens (PrimeSpectrum.Top R))
  定义体: ⟨fun x => .mk f ⟨g, hu x.2⟩, fun x => ⟨U, x.2, 𝟙 _, f, g, fun y => ⟨hu y.2, rfl⟩⟩⟩
-/
def const (f : M) (g : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : U <= basicOpen g) :
    Γ(M, U) :=
  ⟨fun x => .mk f ⟨g, hu x.2⟩, fun x => ⟨U, x.2, 𝟙 _, f, g, fun y => ⟨hu y.2, rfl⟩⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `const_apply` / 定理 `const_apply`

English:
theorem const_apply
  statement: (f : M) (g : R) (U : Opens (PrimeSpectrum.Top R))
  proof: rfl

中文:
定理 const_apply
  结论: (f : M) (g : R) (U : Opens (PrimeSpectrum.Top R))
  证明: rfl
-/
theorem const_apply (f : M) (g : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : forall x in U, g in (x : PrimeSpectrum.Top R).asIdeal.primeCompl) (x : U) :
    (const f g U hu).1 x = .mk f ⟨g, hu x x.2⟩ :=
  rfl

/--
theorem `exists_const` / 定理 `exists_const`

English:
theorem exists_const
  statement: (U) (s : Γ(M, U)) (x : PrimeSpectrum.Top R)
  proof: by
  obtain ⟨V, hxV, iVU, f, g, hfg⟩ := s.2 ⟨x, hx⟩
  obtain ⟨_, ⟨_, ⟨g', rfl⟩, rfl⟩, hxg', hg'U⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxV V.2
refine ⟨g' * g, ?_, ?_, g' • f, Subtype.ext funext fun ⟨y, hy⟩ => ?_⟩ <;>
    simp only [PrimeSpectrum.basicOpen_mul]
  · exact

中文:
定理 exists_const
  结论: (U) (s : Γ(M, U)) (x : PrimeSpectrum.Top R)
  证明: by
  obtain ⟨V, hxV, iVU, f, g, hfg⟩ := s.2 ⟨x, hx⟩
  obtain ⟨_, ⟨_, ⟨g', rfl⟩, rfl⟩, hxg', hg'U⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxV V.2
refine ⟨g' * g, ?_, ?_, g' • f, Subtype.ext funext fun ⟨y, hy⟩ => ?_⟩ <;>
    simp only [PrimeSpectrum.basicOpen_mul]
  · exact

Depends on / 依赖: H.symm, LocalizedModule, LocalizedModule.mk_eq.mpr, PrimeSpectrum, PrimeSpectrum.basicOpen_mul, PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open, Subtype, Subtype.ext, U.trans, basicOpen_mul, exists_subset_of_mem_open, iVU.le, inf_le_left, inf_le_left.trans, isBasis_basic_opens, mk_eq
-/
theorem exists_const (U) (s : Γ(M, U)) (x : PrimeSpectrum.Top R)
    (hx : x in U) :
    exists (g : R) (_ : x in basicOpen g) (i : basicOpen g <= U) (f : M),
      const f g _ le_rfl = (structureSheafInType R M).1.map i.hom.op s := by
  obtain ⟨V, hxV, iVU, f, g, hfg⟩ := s.2 ⟨x, hx⟩
  obtain ⟨_, ⟨_, ⟨g', rfl⟩, rfl⟩, hxg', hg'U⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxV V.2
refine ⟨g' * g, ?_, ?_, g' • f, Subtype.ext funext fun ⟨y, hy⟩ => ?_⟩ <;>
    simp only [PrimeSpectrum.basicOpen_mul]
  · exact ⟨hxg', (hfg ⟨x, hxV⟩).1⟩
  · exact inf_le_left.trans (hg'U.trans iVU.le)
  · rw [PrimeSpectrum.basicOpen_mul] at hy
    obtain ⟨hgy, H⟩ := hfg ⟨y, hg'U hy.1⟩
    refine (LocalizedModule.mk_eq.mpr ⟨1, ?_⟩).trans H.symm
    simp [Submonoid.smul_def, ← smul_assoc]; ring_nf

@[simp]
/--
theorem `res_const` / 定理 `res_const`

English:
theorem res_const
  given: (f : M) (g : R) (U hu V hv i)
  proof: rfl

中文:
定理 res_const
  条件: (f : M) (g : R) (U hu V hv i)
  证明: rfl
-/
theorem res_const (f : M) (g : R) (U hu V hv i) :
    (structureSheafInType R M).1.map i (const f g U hu) = const f g V hv :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `const_zero` / 定理 `const_zero`

English:
theorem const_zero
  given: (f : R) (U hu)
  statement: const (0 : M) f U hu = 0
  proof: Subtype.ext funext fun x => by simp; rfl

@[simp]

中文:
定理 const_zero
  条件: (f : R) (U hu)
  结论: const (0 : M) f U hu = 0
  证明: Subtype.ext funext fun x => by simp; rfl

@[simp]

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem const_zero (f : R) (U hu) : const (0 : M) f U hu = 0 :=
Subtype.ext funext fun x => by simp; rfl

@[simp]
/--
theorem `const_algebraMap` / 定理 `const_algebraMap`

English:
theorem const_algebraMap
  given: (f : R) (U hu)
  statement: const (algebraMap R A f) f U hu = 1
  proof: Subtype.ext funext fun _ => (LocalizedModule.mk_eq.mpr
      ⟨1, by simp [Algebra.smul_def, Submonoid.smul_def]⟩).trans
    OreLocalization.one_def.symm

@[simp]

中文:
定理 const_algebraMap
  条件: (f : R) (U hu)
  结论: const (algebraMap R A f) f U hu = 1
  证明: Subtype.ext funext fun _ => (LocalizedModule.mk_eq.mpr
      ⟨1, by simp [Algebra.smul_def, Submonoid.smul_def]⟩).trans
    OreLocalization.one_def.symm

@[simp]

Depends on / 依赖: Algebra, Algebra.smul_def, LocalizedModule, LocalizedModule.mk_eq.mpr, OreLocalization, OreLocalization.one_def.symm, Submonoid, Submonoid.smul_def, Subtype, Subtype.ext, mk_eq, one_def, smul_def
-/
theorem const_algebraMap (f : R) (U hu) : const (algebraMap R A f) f U hu = 1 :=
Subtype.ext funext fun _ => (LocalizedModule.mk_eq.mpr
      ⟨1, by simp [Algebra.smul_def, Submonoid.smul_def]⟩).trans
    OreLocalization.one_def.symm

@[simp]
/--
theorem `const_self` / 定理 `const_self`

English:
theorem const_self
  given: (f : R) (U hu)
  statement: const f f U hu = 1
  proof: const_algebraMap ..

中文:
定理 const_self
  条件: (f : R) (U hu)
  结论: const f f U hu = 1
  证明: const_algebraMap ..

Depends on / 依赖: const_algebraMap
-/
theorem const_self (f : R) (U hu) : const f f U hu = 1 :=
  const_algebraMap ..

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `const_one` / 定理 `const_one`

English:
theorem const_one
  given: (U)
  statement: const (1 : A) (1 : R) U (by simp) = 1
  proof: by
  simpa using const_algebraMap 1 (A := A) U

中文:
定理 const_one
  条件: (U)
  结论: const (1 : A) (1 : R) U (by simp) = 1
  证明: by
  simpa using const_algebraMap 1 (A := A) U

Depends on / 依赖: const_algebraMap
-/
theorem const_one (U) : const (1 : A) (1 : R) U (by simp) = 1 := by
  simpa using const_algebraMap 1 (A := A) U

set_option backward.isDefEq.respectTransparency false in
/--
theorem `const_add` / 定理 `const_add`

English:
theorem const_add
  given: (f₁ f₂ : M) (g₁ g₂ : R) (U hu₁ hu₂)
  proof: Subtype.ext funext fun _ => LocalizedModule.mk_add_mk

中文:
定理 const_add
  条件: (f₁ f₂ : M) (g₁ g₂ : R) (U hu₁ hu₂)
  证明: Subtype.ext funext fun _ => LocalizedModule.mk_add_mk

Depends on / 依赖: LocalizedModule, LocalizedModule.mk_add_mk, Subtype, Subtype.ext, mk_add_mk
-/
theorem const_add (f₁ f₂ : M) (g₁ g₂ : R) (U hu₁ hu₂) :
    const f₁ g₁ U hu₁ + const f₂ g₂ U hu₂ =
      const (g₂ • f₁ + g₁ • f₂) (g₁ * g₂) U (by simp [*, PrimeSpectrum.basicOpen_mul]) :=
Subtype.ext funext fun _ => LocalizedModule.mk_add_mk

/--
theorem `smul_const` / 定理 `smul_const`

English:
theorem smul_const
  given: (f : M) (r g : R) (U hu)
  proof: Subtype.ext funext fun _ => LocalizedModule.smul'_mk _ _ _

中文:
定理 smul_const
  条件: (f : M) (r g : R) (U hu)
  证明: Subtype.ext funext fun _ => LocalizedModule.smul'_mk _ _ _

Depends on / 依赖: LocalizedModule, LocalizedModule.smul, Subtype, Subtype.ext
-/
theorem smul_const (f : M) (r g : R) (U hu) :
    r • const f g U hu = const (r • f) g U hu :=
Subtype.ext funext fun _ => LocalizedModule.smul'_mk _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `const_mul` / 定理 `const_mul`

English:
theorem const_mul
  given: (f₁ f₂ : A) (g₁ g₂ : R) (U hu₁ hu₂)
  proof: Subtype.ext funext fun _ => LocalizedModule.mk_mul_mk

中文:
定理 const_mul
  条件: (f₁ f₂ : A) (g₁ g₂ : R) (U hu₁ hu₂)
  证明: Subtype.ext funext fun _ => LocalizedModule.mk_mul_mk

Depends on / 依赖: LocalizedModule, LocalizedModule.mk_mul_mk, Subtype, Subtype.ext, mk_mul_mk
-/
theorem const_mul (f₁ f₂ : A) (g₁ g₂ : R) (U hu₁ hu₂) :
    const f₁ g₁ U hu₁ * const f₂ g₂ U hu₂ =
      const (f₁ * f₂) (g₁ * g₂) U (by simp [*, PrimeSpectrum.basicOpen_mul]) :=
Subtype.ext funext fun _ => LocalizedModule.mk_mul_mk

/--
theorem `const_ext` / 定理 `const_ext`

English:
theorem const_ext
  given: {f₁ f₂ : M} {g₁ g₂ : R} {U hu₁ hu₂} (h : g₂ • f₁ = g₁ • f₂)
  proof: Subtype.ext funext fun x => LocalizedModule.mk_eq.mpr (by simp [h, Submonoid.smul_def])

中文:
定理 const_ext
  条件: {f₁ f₂ : M} {g₁ g₂ : R} {U hu₁ hu₂} (h : g₂ • f₁ = g₁ • f₂)
  证明: Subtype.ext funext fun x => LocalizedModule.mk_eq.mpr (by simp [h, Submonoid.smul_def])

Depends on / 依赖: LocalizedModule, LocalizedModule.mk_eq.mpr, Submonoid, Submonoid.smul_def, Subtype, Subtype.ext, mk_eq, smul_def
-/
theorem const_ext {f₁ f₂ : M} {g₁ g₂ : R} {U hu₁ hu₂} (h : g₂ • f₁ = g₁ • f₂) :
    const f₁ g₁ U hu₁ = const f₂ g₂ U hu₂ :=
Subtype.ext funext fun x => LocalizedModule.mk_eq.mpr (by simp [h, Submonoid.smul_def])

/--
theorem `const_congr` / 定理 `const_congr`

English:
theorem const_congr
  given: {f₁ f₂ : M} {g₁ g₂ : R} {U hu} (hf : f₁ = f₂) (hg : g₁ = g₂)
  proof: by subst hf hg; rfl

中文:
定理 const_congr
  条件: {f₁ f₂ : M} {g₁ g₂ : R} {U hu} (hf : f₁ = f₂) (hg : g₁ = g₂)
  证明: by subst hf hg; rfl
-/
theorem const_congr {f₁ f₂ : M} {g₁ g₂ : R} {U hu} (hf : f₁ = f₂) (hg : g₁ = g₂) :
    const f₁ g₁ U hu = const f₂ g₂ U (hg ▸ hu) := by subst hf hg; rfl

/--
theorem `const_mul_rev` / 定理 `const_mul_rev`

English:
theorem const_mul_rev
  given: (f g : R) (U hu₁ hu₂)
  statement: const f g U hu₁ * const g f U hu₂ = 1
  proof: by
  rw [const_mul]; rw [const_congr rfl (mul_comm g f)]; rw [const_self]

中文:
定理 const_mul_rev
  条件: (f g : R) (U hu₁ hu₂)
  结论: const f g U hu₁ * const g f U hu₂ = 1
  证明: by
  rw [const_mul]; rw [const_congr rfl (mul_comm g f)]; rw [const_self]

Depends on / 依赖: const_congr, const_mul, const_self, mul_comm
-/
theorem const_mul_rev (f g : R) (U hu₁ hu₂) : const f g U hu₁ * const g f U hu₂ = 1 := by
  rw [const_mul]; rw [const_congr rfl (mul_comm g f)]; rw [const_self]

/--
theorem `const_mul_cancel` / 定理 `const_mul_cancel`

English:
theorem const_mul_cancel
  given: (f g₁ g₂ : R) (U hu₁ hu₂)
  proof: by
  rw [const_mul]; rw [const_ext]; simp; ring

中文:
定理 const_mul_cancel
  条件: (f g₁ g₂ : R) (U hu₁ hu₂)
  证明: by
  rw [const_mul]; rw [const_ext]; simp; ring

Depends on / 依赖: const_ext, const_mul
-/
theorem const_mul_cancel (f g₁ g₂ : R) (U hu₁ hu₂) :
    const f g₁ U hu₁ * const g₁ g₂ U hu₂ = const f g₂ U hu₂ := by
  rw [const_mul]; rw [const_ext]; simp; ring

/--
theorem `const_mul_cancel'` / 定理 `const_mul_cancel'`

English:
theorem const_mul_cancel'
  given: (f g₁ g₂ : R) (U hu₁ hu₂)
  proof: by
  rw [mul_comm]; rw [const_mul_cancel]

中文:
定理 const_mul_cancel'
  条件: (f g₁ g₂ : R) (U hu₁ hu₂)
  证明: by
  rw [mul_comm]; rw [const_mul_cancel]

Depends on / 依赖: const_mul_cancel, mul_comm
-/
theorem const_mul_cancel' (f g₁ g₂ : R) (U hu₁ hu₂) :
    const g₁ g₂ U hu₂ * const f g₁ U hu₁ = const f g₂ U hu₂ := by
  rw [mul_comm]; rw [const_mul_cancel]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `const_eq_const_of_smul_eq_smul` / 定理 `const_eq_const_of_smul_eq_smul`

English:
theorem const_eq_const_of_smul_eq_smul
  given: (f₁ f₂ : M) (g₁ g₂ : R) (U hu₁ hu₂) (H : g₁ • f₂ = g₂ • f₁)
  proof: Subtype.ext (funext fun x => by
    simp [LocalizedModule.mk_eq, Localizations, Submonoid.smul_def, H])

中文:
定理 const_eq_const_of_smul_eq_smul
  条件: (f₁ f₂ : M) (g₁ g₂ : R) (U hu₁ hu₂) (H : g₁ • f₂ = g₂ • f₁)
  证明: Subtype.ext (funext fun x => by
    simp [LocalizedModule.mk_eq, Localizations, Submonoid.smul_def, H])

Depends on / 依赖: Localizations, LocalizedModule, LocalizedModule.mk_eq, Submonoid, Submonoid.smul_def, Subtype, Subtype.ext, mk_eq, smul_def
-/
theorem const_eq_const_of_smul_eq_smul (f₁ f₂ : M) (g₁ g₂ : R) (U hu₁ hu₂) (H : g₁ • f₂ = g₂ • f₁) :
    const f₁ g₁ U hu₁ = const f₂ g₂ U hu₂ :=
  Subtype.ext (funext fun x => by
    simp [LocalizedModule.mk_eq, Localizations, Submonoid.smul_def, H])

set_option backward.isDefEq.respectTransparency false in
variable (R M) in
/--
Definition of `toOpenₗ` / `toOpenₗ` 的定义

English:
definition toOpenₗ
  signature: (U : Opens (PrimeSpectrum.Top R))
  body: const m 1 U (by simp)
  map_add' _ _ := by simp [const_add]
  map_smul' _ _ := by simp [smul_const]

中文:
定义 toOpenₗ
  签名: (U : Opens (PrimeSpectrum.Top R))
  定义体: const m 1 U (by simp)
  map_add' _ _ := by simp [const_add]
  map_smul' _ _ := by simp [smul_const]
-/
def toOpenₗ (U : Opens (PrimeSpectrum.Top R)) :
    M ->ₗ[R] Γ(M, U) where
  toFun m := const m 1 U (by simp)
  map_add' _ _ := by simp [const_add]
  map_smul' _ _ := by simp [smul_const]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toOpenₗ_eq_const` / 定理 `toOpenₗ_eq_const`

English:
theorem toOpenₗ_eq_const
  given: (U : Opens (PrimeSpectrum.Top R)) (f : M)
  proof: rfl

中文:
定理 toOpenₗ_eq_const
  条件: (U : Opens (PrimeSpectrum.Top R)) (f : M)
  证明: rfl
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
/--
lemma `isUnit_basicOpen` / 引理 `isUnit_basicOpen`

English:
lemma isUnit_basicOpen
  given: (f : R)
  proof: isUnit_iff_exists_inv.mpr ⟨const 1 f _ le_rfl, const_mul_rev _ _ _ (by simp) _⟩

中文:
引理 isUnit_basicOpen
  条件: (f : R)
  证明: isUnit_iff_exists_inv.mpr ⟨const 1 f _ le_rfl, const_mul_rev _ _ _ (by simp) _⟩

Depends on / 依赖: const_mul_rev, isUnit_iff_exists_inv, isUnit_iff_exists_inv.mpr, le_rfl
-/
lemma isUnit_basicOpen (f : R) :
    IsUnit ((algebraMap R Γ(R, basicOpen f)) f) :=
  isUnit_iff_exists_inv.mpr ⟨const 1 f _ le_rfl, const_mul_rev _ _ _ (by simp) _⟩

/--
lemma `isUnit_basicOpen_end` / 引理 `isUnit_basicOpen_end`

English:
lemma isUnit_basicOpen_end
  given: (f : R)
  proof: by
  have := (isUnit_basicOpen f).map
    (algebraMap _ (Module.End Γ(R, basicOpen f) Γ(M, basicOpen f)))
  rw [Module.End.isUnit_iff] at this ⊢
  convert! this
  ext a
  simp

中文:
引理 isUnit_basicOpen_end
  条件: (f : R)
  证明: by
  have := (isUnit_basicOpen f).map
    (algebraMap _ (Module.End Γ(R, basicOpen f) Γ(M, basicOpen f)))
  rw [Module.End.isUnit_iff] at this ⊢
  convert! this
  ext a
  simp

Depends on / 依赖: Module, Module.End, Module.End.isUnit_iff, algebraMap, basicOpen, convert, isUnit_basicOpen, isUnit_iff
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
/--
Definition of `toBasicOpenₗ` / `toBasicOpenₗ` 的定义

English:
definition toBasicOpenₗ
  signature: (f : R)
  body: IsLocalizedModule.lift (.powers f) (LocalizedModule.mkLinearMap ..) (toOpenₗ R M _) by
    simp only [Subtype.forall]
    exact Submonoid.powers_le (P := (IsUnit.submonoid _).comap (algebraMap R _)).mpr
      (isUnit_basicOpen_end ..)

中文:
定义 toBasicOpenₗ
  签名: (f : R)
  定义体: IsLocalizedModule.lift (.powers f) (LocalizedModule.mkLinearMap ..) (toOpenₗ R M _) by
    simp only [Subtype.forall]
    exact Submonoid.powers_le (P := (IsUnit.submonoid _).comap (algebraMap R _)).mpr
      (isUnit_basicOpen_end ..)

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.lift, IsUnit, IsUnit.submonoid, LocalizedModule, LocalizedModule.mkLinearMap, Submonoid, Submonoid.powers_le, Subtype, Subtype.forall, algebraMap, isUnit_basicOpen_end, mkLinearMap, powers, powers_le, submonoid
-/
def toBasicOpenₗ (f : R) :
    LocalizedModule.Away f M ->ₗ[R] Γ(M, PrimeSpectrum.basicOpen f) :=
IsLocalizedModule.lift (.powers f) (LocalizedModule.mkLinearMap ..) (toOpenₗ R M _) by
    simp only [Subtype.forall]
    exact Submonoid.powers_le (P := (IsUnit.submonoid _).comap (algebraMap R _)).mpr
      (isUnit_basicOpen_end ..)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `toBasicOpenₗ_mk` / 定理 `toBasicOpenₗ_mk`

English:
theorem toBasicOpenₗ_mk
  given: (s : R) (f : M) (g : Submonoid.powers s)
  proof: by
  obtain ⟨_, n, rfl⟩ := g
  apply ((Module.End.isUnit_iff _).mp ((isUnit_basicOpen_end ..).pow n)).1 ?_
  rw [← map_pow]
  dsimp [toBasicOpenₗ]
  rw [← map_smul]; rw [LocalizedModule.smul'_mk]; rw [← Submonoid.mk_smul (S := .powers s) _ ⟨n]; rw [rfl⟩]; rw [LocalizedModule.mk_cancel]; rw [← Locali

中文:
定理 toBasicOpenₗ_mk
  条件: (s : R) (f : M) (g : Submonoid.powers s)
  证明: by
  obtain ⟨_, n, rfl⟩ := g
  apply ((Module.End.isUnit_iff _).mp ((isUnit_basicOpen_end ..).pow n)).1 ?_
  rw [← map_pow]
  dsimp [toBasicOpenₗ]
  rw [← map_smul]; rw [LocalizedModule.smul'_mk]; rw [← Submonoid.mk_smul (S := .powers s) _ ⟨n]; rw [rfl⟩]; rw [LocalizedModule.mk_cancel]; rw [← Locali

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.lift_apply, LocalizedModule, LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_cancel, LocalizedModule.smul, Module, Module.End.isUnit_iff, PrimeSpectrum, PrimeSpectrum.le_basicOpen_pow, Submonoid, Submonoid.mem_powers_iff, Submonoid.mk_smul, const_eq_const_of_smul_eq, isUnit_basicOpen_end, isUnit_iff, le_basicOpen_pow, lift_apply, map_pow, map_smul
-/
theorem toBasicOpenₗ_mk (s : R) (f : M) (g : Submonoid.powers s) :
    toBasicOpenₗ R M s (.mk f g) = const f g.1 (basicOpen s) (by
    have := PrimeSpectrum.le_basicOpen_pow s; aesop (add simp [Submonoid.mem_powers_iff])) := by
  obtain ⟨_, n, rfl⟩ := g
  apply ((Module.End.isUnit_iff _).mp ((isUnit_basicOpen_end ..).pow n)).1 ?_
  rw [← map_pow]
  dsimp [toBasicOpenₗ]
  rw [← map_smul]; rw [LocalizedModule.smul'_mk]; rw [← Submonoid.mk_smul (S := .powers s) _ ⟨n]; rw [rfl⟩]; rw [LocalizedModule.mk_cancel]; rw [← LocalizedModule.mkLinearMap_apply]; rw [IsLocalizedModule.lift_apply]; rw [smul_const]
  dsimp [toOpenₗ]
  exact const_eq_const_of_smul_eq_smul (H := by simp) ..

/--
theorem `toBasicOpenₗ_injective` / 定理 `toBasicOpenₗ_injective`

English:
theorem toBasicOpenₗ_injective
  given: (f : R)
  statement: Function.Injective (toBasicOpenₗ R M f)
  proof: by
  intro s t h_eq
  induction s using LocalizedModule.induction_on with | h a b =>
  induction t using LocalizedModule.induction_on with | h c d =>
  suffices f in ((⊥ : Submodule R M).colon {d • a - b • c}).radical by
    rw [LocalizedModule.mk_eq]
    obtain ⟨n, hn⟩ := this
    exact ⟨⟨f ^ n, n,

中文:
定理 toBasicOpenₗ_injective
  条件: (f : R)
  结论: Function.Injective (toBasicOpenₗ R M f)
  证明: by
  intro s t h_eq
  induction s using LocalizedModule.induction_on with | h a b =>
  induction t using LocalizedModule.induction_on with | h c d =>
  suffices f in ((⊥ : Submodule R M).colon {d • a - b • c}).radical by
    rw [LocalizedModule.mk_eq]
    obtain ⟨n, hn⟩ := this
    exact ⟨⟨f ^ n, n,

Depends on / 依赖: LocalizedModule, LocalizedModule.induction_on, LocalizedModule.mk_eq, PrimeSpectrum, PrimeSpectrum.mem_vanishingIdeal, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, Submodule, Submodule.mem_colon.mp, h_eq, induction_on, mem_colon, mem_vanishingIdeal, mk_eq, radical, smul_sub, sub_eq_zero, vanishingIdeal_zeroLocus_eq_radical
-/
theorem toBasicOpenₗ_injective (f : R) : Function.Injective (toBasicOpenₗ R M f) := by
  intro s t h_eq
  induction s using LocalizedModule.induction_on with | h a b =>
  induction t using LocalizedModule.induction_on with | h c d =>
  suffices f in ((⊥ : Submodule R M).colon {d • a - b • c}).radical by
    rw [LocalizedModule.mk_eq]
    obtain ⟨n, hn⟩ := this
    exact ⟨⟨f ^ n, n, rfl⟩, by simpa [sub_eq_zero, smul_sub] using! Submodule.mem_colon.mp hn _ rfl⟩
  simp only [toBasicOpenₗ_mk] at h_eq
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]; rw [PrimeSpectrum.mem_vanishingIdeal]
  intro p hfp
  contrapose hfp
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp congr(($h_eq).1 ⟨p, hfp⟩)
  rw [PrimeSpectrum.mem_zeroLocus]; rw [Set.not_subset]
  exact ⟨u.1, by simpa [sub_eq_zero, smul_sub], u.2⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const` / 定理 `exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const`

English:
theorem exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const
  proof: by
  choose g hxg igU f H using fun x : U => exists_const U s x.1 x.2
  have (i j : _) : LocalizedModule.mk (g i • f j) ⟨g i * g j, Submonoid.mem_powers _⟩ =
      LocalizedModule.mk (g j • f i) ⟨g i * g j, Submonoid.mem_powers _⟩ := by
    refine toBasicOpenₗ_injective (g i * g j) ?_
    simp only 

中文:
定理 exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const
  证明: by
  choose g hxg igU f H using fun x : U => exists_const U s x.1 x.2
  have (i j : _) : LocalizedModule.mk (g i • f j) ⟨g i * g j, Submonoid.mem_powers _⟩ =
      LocalizedModule.mk (g j • f i) ⟨g i * g j, Submonoid.mem_powers _⟩ := by
    refine toBasicOpenₗ_injective (g i * g j) ?_
    simp only 

Depends on / 依赖: LocalizedModule, LocalizedModule.mk, PrimeSpectrum, PrimeSpectrum.basicOpen_m, Submonoid, Submonoid.mem_powers, Subtype, Subtype.ext, basicOpen_m, exists_const, homOfLE, mem_powers, obj.map, structureSheafInType
-/
theorem exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const
    (U : Opens (PrimeSpectrum.Top R)) (hU : IsCompact (U : Set (PrimeSpectrum.Top R)))
    (s : Γ(M, U)) :
    exists (ι : Type u) (_ : Fintype ι) (a : ι -> M) (b : ι -> R) (ibU : forall i, basicOpen (b i) <= U),
      (U <= ⨆ i, basicOpen (b i)) ∧ (forall i j, b j • a i = b i • a j) ∧
          forall i, (structureSheafInType R M).presheaf.map (ibU i).hom.op s =
              const (a i) (b i) _ le_rfl := by
  choose g hxg igU f H using fun x : U => exists_const U s x.1 x.2
  have (i j : _) : LocalizedModule.mk (g i • f j) ⟨g i * g j, Submonoid.mem_powers _⟩ =
      LocalizedModule.mk (g j • f i) ⟨g i * g j, Submonoid.mem_powers _⟩ := by
    refine toBasicOpenₗ_injective (g i * g j) ?_
    simp only [toBasicOpenₗ_mk]
    have := H i
    trans (structureSheafInType R M).obj.map (homOfLE ?_).op s
    · refine .trans (Subtype.ext <| funext fun a => ?_) congr((structureSheafInType R M).obj.map
(homOfLE ((PrimeSpectrum.basicOpen_mul (g i) (g j)).trans_le inf_le_right)).op (H j))
      exact LocalizedModule.mk_eq.mpr ⟨1, by simp [Submonoid.smul_def, ← smul_assoc]; ring_nf⟩
    · refine congr((structureSheafInType R M).obj.map (homOfLE ((PrimeSpectrum.basicOpen_mul (g i)
        (g j)).trans_le inf_le_left)).op $(H i)).symm.trans (Subtype.ext <| funext fun a => ?_)
      exact LocalizedModule.mk_eq.mpr ⟨1, by simp [Submonoid.smul_def, ← smul_assoc]⟩
    · exact ((PrimeSpectrum.basicOpen_mul (g i) (g j)).trans_le inf_le_right).trans (igU _)
  simp only [LocalizedModule.mk_eq, Submonoid.smul_def, Subtype.exists, Submonoid.mem_powers_iff,
    exists_prop, exists_exists_eq_and, ← mul_smul, ← pow_succ, ← mul_assoc _ (_ * _)] at this
  choose n hn using this
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun i => (basicOpen (g i) : Set (PrimeSpectrum R)))
    (fun _ => (basicOpen _).2) (fun x hx => Set.mem_iUnion_of_mem ⟨x, hx⟩ (hxg _))
  let N := (t ×ˢ t).sup fun x => n x.1 x.2 + 1
  refine ⟨t, inferInstance, fun i => g i ^ N • f i, fun i => (g i) ^ (N + 1),
    fun x => by simpa using igU x.1, fun x hx => by simpa using ht hx, fun i j => ?_, fun i => ?_⟩
  · dsimp
    convert_to (g i * g ↑j) ^ N • g j • f i = (g i * g ↑j) ^ N • g i • f j
    · module
    · module
    have : n i j + 1 <= N := (t ×ˢ t).le_sup (f := fun x => n x.1 x.2 + 1) (b := ⟨_, _⟩) (by simp)
    rw [← Nat.sub_add_cancel this]; rw [pow_add]; rw [mul_smul]; rw [mul_smul]
    congr 1
    convert! (hn i j).symm using 1 <;> module
  · convert! congr((structureSheafInType R M).presheaf.map (homOfLE ?_).op $((H i).symm)) using 1
· refine Subtype.ext funext fun x => LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
      simp [Submonoid.smul_def, pow_succ', mul_smul]
    · simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toBasicOpenₗ_surjective` / 定理 `toBasicOpenₗ_surjective`

English:
theorem toBasicOpenₗ_surjective
  given: (f : R)
  statement: Function.Surjective (toBasicOpenₗ R M f)
  proof: by
  intro s
  obtain ⟨ι, _, a, b, ibU, iU, hab, H⟩ := exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const _
    (PrimeSpectrum.isCompact_basicOpen _) s
  obtain ⟨n, hn⟩ : f in (Ideal.span (Set.range b)).radical := by
    have : PrimeSpectrum.zeroLocus (Set.range b) subseteq PrimeSpectrum.zeroLoc

中文:
定理 toBasicOpenₗ_surjective
  条件: (f : R)
  结论: Function.Surjective (toBasicOpenₗ R M f)
  证明: by
  intro s
  obtain ⟨ι, _, a, b, ibU, iU, hab, H⟩ := exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const _
    (PrimeSpectrum.isCompact_basicOpen _) s
  obtain ⟨n, hn⟩ : f in (Ideal.span (Set.range b)).radical := by
    have : PrimeSpectrum.zeroLocus (Set.range b) subseteq PrimeSpectrum.zeroLoc

Depends on / 依赖: Ideal.span, PrimeSpectrum, PrimeSpectrum.Top, PrimeSpectrum.isCompact_basicOpen, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.zeroLocus, PrimeSpectrum.zeroLocus_, PrimeSpectrum.zeroLocus_iUnion, Set.compl_iInter, Set.range, SetLike, SetLike.coe_subset_coe, coe_subset_coe, compl_iInter, exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const, isCompact_basicOpen, radical, subseteq, vanishingIdeal_zeroLocus_eq_radical, zeroLocus
-/
theorem toBasicOpenₗ_surjective (f : R) : Function.Surjective (toBasicOpenₗ R M f) := by
  intro s
  obtain ⟨ι, _, a, b, ibU, iU, hab, H⟩ := exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const _
    (PrimeSpectrum.isCompact_basicOpen _) s
  obtain ⟨n, hn⟩ : f in (Ideal.span (Set.range b)).radical := by
    have : PrimeSpectrum.zeroLocus (Set.range b) subseteq PrimeSpectrum.zeroLocus {f} := by
      simpa [← SetLike.coe_subset_coe, ← Set.compl_iInter,
        ← PrimeSpectrum.zeroLocus_iUnion, PrimeSpectrum.Top] using iU
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]; rw [PrimeSpectrum.zeroLocus_span]; rw [PrimeSpectrum.mem_vanishingIdeal]
    exact fun x hx => by simpa using this hx
  replace hn := Ideal.mul_mem_right f _ hn
  rw [← pow_succ]; rw [Ideal.span]; rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn
  obtain ⟨c, hc⟩ := hn
  rw [Finsupp.sum_fintype _ _ (by simp)] at hc
  refine ⟨LocalizedModule.mk (∑ i, c i • a i) ⟨f ^ (n + 1), _, rfl⟩, ?_⟩
  refine (structureSheafInType R M).eq_of_locally_eq' (fun i => basicOpen (b i)) _
    (fun i => (ibU _).hom) iU _ _ fun i => (Subtype.ext (funext fun x => ?_)).trans (H _).symm
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

/--
Instance `isIso_toBasicOpenₗ` / 实例 `isIso_toBasicOpenₗ`

English:
instance isIso_toBasicOpenₗ
  signature: (f : R)
  body: (ConcreteCategory.isIso_iff_bijective _).mpr ⟨toBasicOpenₗ_injective _, toBasicOpenₗ_surjective _⟩

中文:
实例 isIso_toBasicOpenₗ
  签名: (f : R)
  定义体: (ConcreteCategory.isIso_iff_bijective _).mpr ⟨toBasicOpenₗ_injective _, toBasicOpenₗ_surjective _⟩

Depends on / 依赖: ConcreteCategory, ConcreteCategory.isIso_iff_bijective, isIso_iff_bijective
-/
instance isIso_toBasicOpenₗ (f : R) :
    IsIso (ModuleCat.ofHom (toBasicOpenₗ R M f)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr ⟨toBasicOpenₗ_injective _, toBasicOpenₗ_surjective _⟩

set_option backward.isDefEq.respectTransparency false in
public lemma toOpenₗ_top_bijective : Function.Bijective (toOpenₗ R M ⊤) := by
  have : IsLocalizedModule ⊥ (toOpenₗ R M ⊤) := by
    convert! (inferInstance : IsLocalizedModule (.powers 1) (toOpenₗ R M (basicOpen 1)))
    rw [PrimeSpectrum.basicOpen_one]; rw [Submonoid.powers_one]
  refine ⟨fun x y e => by simpa using (IsLocalizedModule.eq_iff_exists ⊥ _).mp e, fun x => ?_⟩
  obtain ⟨⟨x, _, rfl⟩, rfl⟩ := IsLocalizedModule.mk'_surjective ⊥ (toOpenₗ R M ⊤) x
  exact ⟨x, (IsLocalizedModule.mk'_one ..).symm⟩

public lemma algebraMap_obj_top_bijective :
    Function.Bijective (algebraMap R Γ(R, (⊤ : Opens (PrimeSpectrum.Top R)))) :=
  toOpenₗ_top_bijective

set_option backward.isDefEq.respectTransparency false in
public instance (f : R) : IsLocalization.Away f Γ(R, basicOpen f) :=
(isLocalizedModule_iff_isLocalization' _ _).mp
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
    (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hxU : x in U) :
    CommRingCat.ofHom (algebraMap R Γ(R, U)) ≫ (structurePresheafInCommRingCat R).germ U x hxU =
      toStalk R x := by
  dsimp [toStalk]
  rw [← (structurePresheafInCommRingCat R).germ_res (homOfLE (le_top : U <= ⊤)) _ hxU]
  rfl

@[deprecated (since := "2026-02-10")] public alias toOpen_germ := algebraMap_germ

public
instance (x : PrimeSpectrum.Top R) : Algebra R ((structurePresheafInCommRingCat R).stalk x) :=
  (toStalk R x).hom.toAlgebra

public
instance (x : PrimeSpectrum.Top R) :
    Module R ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x) :=
  .compHom _ (toStalk R x).hom

variable (M) in
/--
Definition of `germₗ` / `germₗ` 的定义

English:
definition germₗ
  signature: (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hxU : x in U)
  body: (TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf U x hxU).hom
  map_smul' r m := by
    change _ = toStalk R x _ • TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf _ _ _ _
    rw [← algebraMap_germ_apply U x hxU]
    refine .trans ?_ (PresheafOfModules.germ_smul ..)
    congr 

中文:
定义 germₗ
  签名: (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hxU : x in U)
  定义体: (TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf U x hxU).hom
  map_smul' r m := by
    change _ = toStalk R x _ • TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf _ _ _ _
    rw [← algebraMap_germ_apply U x hxU]
    refine .trans ?_ (PresheafOfModules.germ_smul ..)
    congr 

Depends on / 依赖: Presheaf, TopCat, TopCat.Presheaf.germ, moduleStructurePresheaf, presheaf
-/
def germₗ (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hxU : x in U) :
    Γ(M, U) ->ₗ[R] ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x) where
  __ := (TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf U x hxU).hom
  map_smul' r m := by
    change _ = toStalk R x _ • TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf _ _ _ _
    rw [← algebraMap_germ_apply U x hxU]
    refine .trans ?_ (PresheafOfModules.germ_smul ..)
    congr 1
    exact (IsScalarTower.algebraMap_smul Γ(R, U) r m).symm

public
instance (x : PrimeSpectrum.Top R) :
    IsScalarTower R ((structurePresheafInCommRingCat R).stalk x)
      ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x) :=
  .of_algebraMap_smul fun _ _ => rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (R M) in
/--
Definition of `modulePresheafStalkIso` / `modulePresheafStalkIso` 的定义

English:
definition modulePresheafStalkIso
  signature: (x : PrimeSpectrum.Top R)
  body: (Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves (forget₂ (ModuleCat R) Ab)
    (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙
      structurePresheafInModuleCat R M))⟩:).addCommGroupIsoToAddEquiv
  map_smul' r m := by
    let α : TopCat.Presheaf.stalk (moduleStructurePreshea

中文:
定义 modulePresheafStalkIso
  签名: (x : PrimeSpectrum.Top R)
  定义体: (Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves (forget₂ (ModuleCat R) Ab)
    (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙
      structurePresheafInModuleCat R M))⟩:).addCommGroupIsoToAddEquiv
  map_smul' r m := by
    let α : TopCat.Presheaf.stalk (moduleStructurePreshea

Depends on / 依赖: Limits, Limits.colimit.isoColimitCocone, Limits.isColimitOfPreserves, ModuleCat, colimit, isColimitOfPreserves, isoColimitCocone
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

instance (x : PrimeSpectrum.Top R) :
    Module ((structurePresheafInCommRingCat R).stalk x)
      ((structurePresheafInModuleCat R M).stalk x) :=
  (modulePresheafStalkIso R M x).toAddEquiv.symm.module _

/--
lemma `toStalk_smul` / 引理 `toStalk_smul`

English:
lemma toStalk_smul
  statement: (x : PrimeSpectrum.Top R) (r : R)
  proof: by
  change modulePresheafStalkIso R M x (toStalk R x r • (modulePresheafStalkIso R M x).symm m) = _
  rw [← (modulePresheafStalkIso R M x).eq_symm_apply]; rw [map_smul]
  rfl

中文:
引理 toStalk_smul
  结论: (x : PrimeSpectrum.Top R) (r : R)
  证明: by
  change modulePresheafStalkIso R M x (toStalk R x r • (modulePresheafStalkIso R M x).symm m) = _
  rw [← (modulePresheafStalkIso R M x).eq_symm_apply]; rw [map_smul]
  rfl

Depends on / 依赖: eq_symm_apply, map_smul, modulePresheafStalkIso, toStalk
-/
lemma toStalk_smul (x : PrimeSpectrum.Top R) (r : R)
    (m : (structurePresheafInModuleCat R M).stalk x) :
    toStalk R x r • m = r • m := by
  change modulePresheafStalkIso R M x (toStalk R x r • (modulePresheafStalkIso R M x).symm m) = _
  rw [← (modulePresheafStalkIso R M x).eq_symm_apply]; rw [map_smul]
  rfl

variable (R M) in
/--
Definition of `toStalkₗ'` / `toStalkₗ'` 的定义

English:
definition toStalkₗ'
  signature: (x : PrimeSpectrum.Top R)
  body: ModuleCat.ofHom (toOpenₗ R M ⊤) ≫ (structurePresheafInModuleCat R M).germ _ x trivial

中文:
定义 toStalkₗ'
  签名: (x : PrimeSpectrum.Top R)
  定义体: ModuleCat.ofHom (toOpenₗ R M ⊤) ≫ (structurePresheafInModuleCat R M).germ _ x trivial

Depends on / 依赖: ModuleCat, ModuleCat.ofHom, structurePresheafInModuleCat
-/
def toStalkₗ' (x : PrimeSpectrum.Top R) :
    ModuleCat.of R M ⟶ (structurePresheafInModuleCat R M).stalk x :=
  ModuleCat.ofHom (toOpenₗ R M ⊤) ≫ (structurePresheafInModuleCat R M).germ _ x trivial

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toOpenₗ_germ` / 定理 `toOpenₗ_germ`

English:
theorem toOpenₗ_germ
  given: (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x in U)
  proof: by
  rw [toStalkₗ']; rw [← Presheaf.germ_res _ (homOfLE le_top) _ hx]; rw [← Category.assoc]
  rfl

中文:
定理 toOpenₗ_germ
  条件: (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x in U)
  证明: by
  rw [toStalkₗ']; rw [← Presheaf.germ_res _ (homOfLE le_top) _ hx]; rw [← Category.assoc]
  rfl

Depends on / 依赖: Category, Category.assoc, Presheaf, Presheaf.germ_res, germ_res, homOfLE, le_top
-/
theorem toOpenₗ_germ (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x in U) :
    ModuleCat.ofHom (toOpenₗ R M U) ≫
      (structurePresheafInModuleCat R M).germ U x hx = toStalkₗ' R M x := by
  rw [toStalkₗ']; rw [← Presheaf.germ_res _ (homOfLE le_top) _ hx]; rw [← Category.assoc]
  rfl

/--
theorem `isUnit_toStalk` / 定理 `isUnit_toStalk`

English:
theorem isUnit_toStalk
  given: (x : PrimeSpectrum.Top R) (f : R) (hf : x in basicOpen f)
  proof: by
  convert! (isUnit_basicOpen f).map ((structurePresheafInCommRingCat R).germ _ x hf).hom
  exact ((structurePresheafInCommRingCat R).germ_res_apply (homOfLE (le_top : basicOpen f <= ⊤))
    x hf (algebraMap R Γ(R, ⊤) f)).symm

中文:
定理 isUnit_toStalk
  条件: (x : PrimeSpectrum.Top R) (f : R) (hf : x in basicOpen f)
  证明: by
  convert! (isUnit_basicOpen f).map ((structurePresheafInCommRingCat R).germ _ x hf).hom
  exact ((structurePresheafInCommRingCat R).germ_res_apply (homOfLE (le_top : basicOpen f <= ⊤))
    x hf (algebraMap R Γ(R, ⊤) f)).symm

Depends on / 依赖: algebraMap, basicOpen, convert, germ_res_apply, homOfLE, isUnit_basicOpen, le_top, structurePresheafInCommRingCat
-/
theorem isUnit_toStalk (x : PrimeSpectrum.Top R) (f : R) (hf : x in basicOpen f) :
    IsUnit (toStalk R x f) := by
  convert! (isUnit_basicOpen f).map ((structurePresheafInCommRingCat R).germ _ x hf).hom
  exact ((structurePresheafInCommRingCat R).germ_res_apply (homOfLE (le_top : basicOpen f <= ⊤))
    x hf (algebraMap R Γ(R, ⊤) f)).symm

/--
theorem `isUnit_toStalkₗ'` / 定理 `isUnit_toStalkₗ'`

English:
theorem isUnit_toStalkₗ'
  given: (x : PrimeSpectrum.Top R) (f : R) (hf : x in basicOpen f)
  proof: by
  have := (isUnit_toStalk x f hf).map (algebraMap _
    (Module.End ((structurePresheafInCommRingCat R).stalk x)
      ((structurePresheafInModuleCat R M).stalk x)))
  rw [Module.End.isUnit_iff] at this ⊢
  convert! this
  ext a
  simp only [Module.algebraMap_end_apply]
  rw [toStalk_smul]

中文:
定理 isUnit_toStalkₗ'
  条件: (x : PrimeSpectrum.Top R) (f : R) (hf : x in basicOpen f)
  证明: by
  have := (isUnit_toStalk x f hf).map (algebraMap _
    (Module.End ((structurePresheafInCommRingCat R).stalk x)
      ((structurePresheafInModuleCat R M).stalk x)))
  rw [Module.End.isUnit_iff] at this ⊢
  convert! this
  ext a
  simp only [Module.algebraMap_end_apply]
  rw [toStalk_smul]

Depends on / 依赖: Module, Module.End, Module.End.isUnit_iff, Module.algebraMap_end_apply, algebraMap, algebraMap_end_apply, convert, isUnit_iff, isUnit_toStalk, structurePresheafInCommRingCat, structurePresheafInModuleCat, toStalk_smul
-/
theorem isUnit_toStalkₗ' (x : PrimeSpectrum.Top R) (f : R) (hf : x in basicOpen f) :
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
/--
Definition of `localizationtoStalkₗ` / `localizationtoStalkₗ` 的定义

English:
definition localizationtoStalkₗ
  signature: (x : PrimeSpectrum.Top R)
  body: ModuleCat.ofHom (IsLocalizedModule.lift x.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (toStalkₗ' R M x).hom fun f => isUnit_toStalkₗ' x f.1 f.2 :)

中文:
定义 localizationtoStalkₗ
  签名: (x : PrimeSpectrum.Top R)
  定义体: ModuleCat.ofHom (IsLocalizedModule.lift x.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (toStalkₗ' R M x).hom fun f => isUnit_toStalkₗ' x f.1 f.2 :)

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.lift, LocalizedModule, LocalizedModule.mkLinearMap, ModuleCat, ModuleCat.ofHom, asIdeal, mkLinearMap, primeCompl, x.asIdeal.primeCompl
-/
def localizationtoStalkₗ (x : PrimeSpectrum.Top R) :
    ModuleCat.of R (LocalizedModule x.asIdeal.primeCompl M) ⟶
      (structurePresheafInModuleCat R M).stalk x :=
  ModuleCat.ofHom (IsLocalizedModule.lift x.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (toStalkₗ' R M x).hom fun f => isUnit_toStalkₗ' x f.1 f.2 :)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `localizationtoStalkₗ_mk` / 定理 `localizationtoStalkₗ_mk`

English:
theorem localizationtoStalkₗ_mk
  given: (x : PrimeSpectrum.Top R) (f : M) (s)
  proof: by
  apply ((Module.End.isUnit_iff _).mp (isUnit_toStalkₗ' _ s.1 s.2)).1 ?_
  dsimp [localizationtoStalkₗ]
  rw [← map_smul]; rw [LocalizedModule.smul'_mk]; rw [← Submonoid.smul_def]; rw [LocalizedModule.mk_cancel]; rw [← LocalizedModule.mkLinearMap_apply]; rw [IsLocalizedModule.lift_apply]; rw [← m

中文:
定理 localizationtoStalkₗ_mk
  条件: (x : PrimeSpectrum.Top R) (f : M) (s)
  证明: by
  apply ((Module.End.isUnit_iff _).mp (isUnit_toStalkₗ' _ s.1 s.2)).1 ?_
  dsimp [localizationtoStalkₗ]
  rw [← map_smul]; rw [LocalizedModule.smul'_mk]; rw [← Submonoid.smul_def]; rw [LocalizedModule.mk_cancel]; rw [← LocalizedModule.mkLinearMap_apply]; rw [IsLocalizedModule.lift_apply]; rw [← m

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.lift_apply, LocalizedModule, LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_cancel, LocalizedModule.smul, Module, Module.End.isUnit_iff, Submonoid, Submonoid.smul_def, basicOpen, const_eq_const_of_smul_eq_smul, isUnit_iff, lift_apply, map_smul, mkLinearMap_apply, mk_cancel, smul_const, smul_def
-/
theorem localizationtoStalkₗ_mk (x : PrimeSpectrum.Top R) (f : M) (s) :
    localizationtoStalkₗ R M x (.mk f s) = (structurePresheafInModuleCat R M).germ
      (PrimeSpectrum.basicOpen (s : R)) x s.2 (const f (s : R) _ fun _ => id) := by
  apply ((Module.End.isUnit_iff _).mp (isUnit_toStalkₗ' _ s.1 s.2)).1 ?_
  dsimp [localizationtoStalkₗ]
  rw [← map_smul]; rw [LocalizedModule.smul'_mk]; rw [← Submonoid.smul_def]; rw [LocalizedModule.mk_cancel]; rw [← LocalizedModule.mkLinearMap_apply]; rw [IsLocalizedModule.lift_apply]; rw [← map_smul]; rw [← toOpenₗ_germ (basicOpen ↑s) _ s.2]; rw [smul_const]
  dsimp [toOpenₗ]
  congr 1
  exact const_eq_const_of_smul_eq_smul (H := by simp) ..

set_option backward.isDefEq.respectTransparency.types false in
variable (R M) in
/--
Definition of `openToLocalizationₗ` / `openToLocalizationₗ` 的定义

English:
definition openToLocalizationₗ
  signature: (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x in U)
  body: ModuleCat.ofHom
  { toFun s := s.1 ⟨x, hx⟩
    map_smul' _ _ := rfl
    map_add' _ _ := rfl }

中文:
定义 openToLocalizationₗ
  签名: (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x in U)
  定义体: ModuleCat.ofHom
  { toFun s := s.1 ⟨x, hx⟩
    map_smul' _ _ := rfl
    map_add' _ _ := rfl }

Depends on / 依赖: ModuleCat, ModuleCat.ofHom, map_add, map_smul
-/
def openToLocalizationₗ (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x in U) :
    (structurePresheafInModuleCat R M).obj (op U) ⟶
      .of R (LocalizedModule x.asIdeal.primeCompl M) :=
  ModuleCat.ofHom
  { toFun s := s.1 ⟨x, hx⟩
    map_smul' _ _ := rfl
    map_add' _ _ := rfl }

set_option backward.isDefEq.respectTransparency.types false in
variable (R M) in
/--
Definition of `stalkToLocalizationₗ` / `stalkToLocalizationₗ` 的定义

English:
definition stalkToLocalizationₗ
  signature: (x : PrimeSpectrum.Top R)
  body: Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ structurePresheafInModuleCat R M)
    { pt := _
      ι.app U := openToLocalizationₗ R M ((OpenNhds.inclusion _).obj (unop U)) x (unop U).2 }

@[reassoc (attr := simp)]

中文:
定义 stalkToLocalizationₗ
  签名: (x : PrimeSpectrum.Top R)
  定义体: Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ structurePresheafInModuleCat R M)
    { pt := _
      ι.app U := openToLocalizationₗ R M ((OpenNhds.inclusion _).obj (unop U)) x (unop U).2 }

@[reassoc (attr := simp)]

Depends on / 依赖: Limits, Limits.colimit.desc, OpenNhds, OpenNhds.inclusion, colimit, inclusion, structurePresheafInModuleCat
-/
def stalkToLocalizationₗ (x : PrimeSpectrum.Top R) :
    (structurePresheafInModuleCat R M).stalk x ⟶ .of R (LocalizedModule x.asIdeal.primeCompl M) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ structurePresheafInModuleCat R M)
    { pt := _
      ι.app U := openToLocalizationₗ R M ((OpenNhds.inclusion _).obj (unop U)) x (unop U).2 }

@[reassoc (attr := simp)]
/--
theorem `germ_stalkToLocalizationₗ` / 定理 `germ_stalkToLocalizationₗ`

English:
theorem germ_stalkToLocalizationₗ
  proof: Limits.colimit.ι_desc _ _

中文:
定理 germ_stalkToLocalizationₗ
  证明: Limits.colimit.ι_desc _ _

Depends on / 依赖: Limits, Limits.colimit, colimit
-/
theorem germ_stalkToLocalizationₗ
    (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x in U) :
    (structurePresheafInModuleCat R M).germ U x hx ≫ stalkToLocalizationₗ R M x =
      openToLocalizationₗ R M U x hx :=
  Limits.colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toStalkₗ'_stalkToFiberRingHom` / 定理 `toStalkₗ'_stalkToFiberRingHom`

English:
theorem toStalkₗ'_stalkToFiberRingHom
  given: (x : PrimeSpectrum.Top R)
  proof: by
  rw [toStalkₗ']; rw [Category.assoc]; rw [germ_stalkToLocalizationₗ]; rfl

中文:
定理 toStalkₗ'_stalkToFiberRingHom
  条件: (x : PrimeSpectrum.Top R)
  证明: by
  rw [toStalkₗ']; rw [Category.assoc]; rw [germ_stalkToLocalizationₗ]; rfl
-/
theorem toStalkₗ'_stalkToFiberRingHom (x : PrimeSpectrum.Top R) :
    toStalkₗ' R M x ≫ stalkToLocalizationₗ R M x =
      ModuleCat.ofHom (LocalizedModule.mkLinearMap _ _) := by
  rw [toStalkₗ']; rw [Category.assoc]; rw [germ_stalkToLocalizationₗ]; rfl

open TopCat.Presheaf

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (R M) in
/-- The ring isomorphism between the stalk of the structure sheaf of `R` at a point `p`
corresponding to a prime ideal in `R` and the localization of `R` at `p`. -/
@[simps]
/--
Definition of `stalkIsoₗ` / `stalkIsoₗ` 的定义

English:
definition stalkIsoₗ
  signature: (x : PrimeSpectrum.Top R)
  body: stalkToLocalizationₗ R M x
  inv := localizationtoStalkₗ R M x
  hom_inv_id := by
    apply stalk_hom_ext
    intro U hxU
    ext s
    obtain ⟨g, hxg, igU, f, hs⟩ :=
      exists_const _ s x hxU
    rw [germ_stalkToLocalizationₗ_assoc]; rw [Category.comp_id]; rw [← germ_res_apply _ igU.hom _ hxg]
 

中文:
定义 stalkIsoₗ
  签名: (x : PrimeSpectrum.Top R)
  定义体: stalkToLocalizationₗ R M x
  inv := localizationtoStalkₗ R M x
  hom_inv_id := by
    apply stalk_hom_ext
    intro U hxU
    ext s
    obtain ⟨g, hxg, igU, f, hs⟩ :=
      exists_const _ s x hxU
    rw [germ_stalkToLocalizationₗ_assoc]; rw [Category.comp_id]; rw [← germ_res_apply _ igU.hom _ hxg]
 
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
    rw [germ_stalkToLocalizationₗ_assoc]; rw [Category.comp_id]; rw [← germ_res_apply _ igU.hom _ hxg]
    refine congr(localizationtoStalkₗ R M x (openToLocalizationₗ R M _ x hxg $hs)).symm.trans ?_
    refine (localizationtoStalkₗ_mk ..).trans
      congr((structurePresheafInModuleCat R M).germ _ x hxg $hs)
  inv_hom_id := by
    ext1
    refine IsLocalizedModule.ext x.asIdeal.primeCompl (LocalizedModule.mkLinearMap ..)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap ..)) ?_
    ext
    dsimp [localizationtoStalkₗ]
    rw [← LocalizedModule.mkLinearMap_apply]; rw [IsLocalizedModule.lift_apply]; rw [elementwise_of% toStalkₗ'_stalkToFiberRingHom (M := M) x]
    simp

instance (x : PrimeSpectrum R) : IsIso (stalkToLocalizationₗ R M x) :=
  (stalkIsoₗ R M x).isIso_hom

instance (x : PrimeSpectrum R) : IsIso (localizationtoStalkₗ R M x) :=
  (stalkIsoₗ R M x).isIso_inv

@[simp, reassoc]
/--
theorem `stalkToFiberRingHom_localizationToStalk` / 定理 `stalkToFiberRingHom_localizationToStalk`

English:
theorem stalkToFiberRingHom_localizationToStalk
  given: (x : PrimeSpectrum.Top R)
  proof: (stalkIsoₗ R M x).hom_inv_id

@[simp, reassoc]

中文:
定理 stalkToFiberRingHom_localizationToStalk
  条件: (x : PrimeSpectrum.Top R)
  证明: (stalkIsoₗ R M x).hom_inv_id

@[simp, reassoc]

Depends on / 依赖: hom_inv_id
-/
theorem stalkToFiberRingHom_localizationToStalk (x : PrimeSpectrum.Top R) :
    stalkToLocalizationₗ R M x ≫ localizationtoStalkₗ R M x = 𝟙 _ :=
  (stalkIsoₗ R M x).hom_inv_id

@[simp, reassoc]
/--
theorem `localizationToStalk_stalkToFiberRingHom` / 定理 `localizationToStalk_stalkToFiberRingHom`

English:
theorem localizationToStalk_stalkToFiberRingHom
  given: (x : PrimeSpectrum.Top R)
  proof: (stalkIsoₗ R M x).inv_hom_id

中文:
定理 localizationToStalk_stalkToFiberRingHom
  条件: (x : PrimeSpectrum.Top R)
  证明: (stalkIsoₗ R M x).inv_hom_id

Depends on / 依赖: inv_hom_id
-/
theorem localizationToStalk_stalkToFiberRingHom (x : PrimeSpectrum.Top R) :
    localizationtoStalkₗ R M x ≫ stalkToLocalizationₗ R M x = 𝟙 _ :=
  (stalkIsoₗ R M x).inv_hom_id

set_option backward.isDefEq.respectTransparency.types false in
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
/--
Definition of `toStalkₗ` / `toStalkₗ` 的定义

English:
definition toStalkₗ
  signature: (x : PrimeSpectrum.Top R)
  body: TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf ⊤ x (by simp) (toOpenₗ R M ⊤ m)
  map_add' := by simp
  map_smul' r m := by
    change _ = toStalk R x r • TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf _ _ _ _
    rw [map_smul]
    refine .trans ?_ ((moduleStructurePresheaf 

中文:
定义 toStalkₗ
  签名: (x : PrimeSpectrum.Top R)
  定义体: TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf ⊤ x (by simp) (toOpenₗ R M ⊤ m)
  map_add' := by simp
  map_smul' r m := by
    change _ = toStalk R x r • TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf _ _ _ _
    rw [map_smul]
    refine .trans ?_ ((moduleStructurePresheaf 

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_smul, Presheaf, TopCat, TopCat.Presheaf.germ, algebraMap_smul, germ_smul, map_add, map_smul, moduleStructurePresheaf, presheaf, toStalk
-/
def toStalkₗ (x : PrimeSpectrum.Top R) :
    M ->ₗ[R] ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x) where
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
/--
Definition of `commRingCatStalkEquivModuleStalk` / `commRingCatStalkEquivModuleStalk` 的定义

English:
definition commRingCatStalkEquivModuleStalk
  signature: (x : PrimeSpectrum.Top R)
  body: (Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙
      structurePresheafInCommRingCat R))⟩).addCommGroupIsoToAddEquiv
  map_smul' r m := by
    let α : TopCa

中文:
定义 commRingCatStalkEquivModuleStalk
  签名: (x : PrimeSpectrum.Top R)
  定义体: (Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙
      structurePresheafInCommRingCat R))⟩).addCommGroupIsoToAddEquiv
  map_smul' r m := by
    let α : TopCa

Depends on / 依赖: Limits, Limits.colimit.isoColimitCocone, Limits.isColimitOfPreserves, colimit, isColimitOfPreserves, isoColimitCocone
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
    rw [← map_smul]; rw [Algebra.smul_def]
    refine congr($this _).trans ?_
    refine (((structurePresheafInCommRingCat R).germ U x hxU).hom.map_mul _ _).trans ?_
    congr 1
    · dsimp [toStalk]
      erw [← (structurePresheafInCommRingCat R).germ_res_apply (homOfLE (le_top : U <= ⊤)) _ hxU]
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

/--
Definition of `_root_.AlgebraicGeometry.Spec.structureSheaf` / `_root_.AlgebraicGeometry.Spec.structureSheaf` 的定义

English:
definition _root_.AlgebraicGeometry.Spec.structureSheaf
  signature: : Sheaf CommRingCat (PrimeSpectrum.Top R)
  body: ⟨structurePresheafInCommRingCat R,
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp _ _).mpr (TopCat.Presheaf.isSheaf_of_iso
      (structurePresheafCompForget R).symm (structureSheafInType R R).property)⟩

中文:
定义 _root_.AlgebraicGeometry.Spec.structureSheaf
  签名: : Sheaf CommRingCat (PrimeSpectrum.Top R)
  定义体: ⟨structurePresheafInCommRingCat R,
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp _ _).mpr (TopCat.Presheaf.isSheaf_of_iso
      (structurePresheafCompForget R).symm (structureSheafInType R R).property)⟩

Depends on / 依赖: Presheaf, TopCat, TopCat.Presheaf.isSheaf_iff_isSheaf_comp, TopCat.Presheaf.isSheaf_of_iso, isSheaf_iff_isSheaf_comp, isSheaf_of_iso, property, structurePresheafCompForget, structurePresheafInCommRingCat, structureSheafInType
-/
def _root_.AlgebraicGeometry.Spec.structureSheaf : Sheaf CommRingCat (PrimeSpectrum.Top R) :=
  ⟨structurePresheafInCommRingCat R,
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp _ _).mpr (TopCat.Presheaf.isSheaf_of_iso
      (structurePresheafCompForget R).symm (structureSheafInType R R).property)⟩

open Spec (structureSheaf)

/-- The canonical ring homomorphism interpreting an element of `R` as
a section of the structure sheaf. -/
@[deprecated "algebraMap" (since := "2026-02-10")]
/--
Definition of `toOpen` / `toOpen` 的定义

English:
definition toOpen
  signature: (U : Opens (PrimeSpectrum.Top R))
  body: CommRingCat.ofHom (algebraMap _ _)

@[simp]

中文:
定义 toOpen
  签名: (U : Opens (PrimeSpectrum.Top R))
  定义体: CommRingCat.ofHom (algebraMap _ _)

@[simp]

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, algebraMap
-/
def toOpen (U : Opens (PrimeSpectrum.Top R)) :
    CommRingCat.of R ⟶ (structureSheaf R).1.obj (op U) := CommRingCat.ofHom (algebraMap _ _)

@[simp]
/--
theorem `algebraMap_self_map` / 定理 `algebraMap_self_map`

English:
theorem algebraMap_self_map
  given: (U V : (Opens (PrimeSpectrum.Top R))ᵒᵖ) (i : V ⟶ U)
  proof: rfl

@[deprecated (since := "2026-02-10")] alias toOpen_res := algebraMap_self_map

中文:
定理 algebraMap_self_map
  条件: (U V : (Opens (PrimeSpectrum.Top R))ᵒᵖ) (i : V ⟶ U)
  证明: rfl

@[deprecated (since := "2026-02-10")] alias toOpen_res := algebraMap_self_map
-/
theorem algebraMap_self_map (U V : (Opens (PrimeSpectrum.Top R))ᵒᵖ) (i : V ⟶ U) :
    CommRingCat.ofHom (algebraMap R _) ≫ (Spec.structureSheaf R).1.map i =
      CommRingCat.ofHom (algebraMap R _) :=
  rfl

@[deprecated (since := "2026-02-10")] alias toOpen_res := algebraMap_self_map

/--
Instance `stalkAlgebra` / 实例 `stalkAlgebra`

English:
instance stalkAlgebra
  signature: (p : PrimeSpectrum R)
  body: (toStalk R p).hom.toAlgebra

@[simp]

中文:
实例 stalkAlgebra
  签名: (p : PrimeSpectrum R)
  定义体: (toStalk R p).hom.toAlgebra

@[simp]

Depends on / 依赖: hom.toAlgebra, toAlgebra, toStalk
-/
instance stalkAlgebra (p : PrimeSpectrum R) : Algebra R ((structureSheaf R).presheaf.stalk p) :=
  (toStalk R p).hom.toAlgebra

@[simp]
/--
theorem `stalkAlgebra_map` / 定理 `stalkAlgebra_map`

English:
theorem stalkAlgebra_map
  given: (p : PrimeSpectrum R) (r : R)
  proof: rfl

中文:
定理 stalkAlgebra_map
  条件: (p : PrimeSpectrum R) (r : R)
  证明: rfl
-/
theorem stalkAlgebra_map (p : PrimeSpectrum R) (r : R) :
    algebraMap R ((structureSheaf R).presheaf.stalk p) r = toStalk R p r :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `IsLocalization.to_stalk` / 实例 `IsLocalization.to_stalk`

English:
instance IsLocalization.to_stalk
  signature: (p : PrimeSpectrum R)
  body: inferInstanceAs (IsLocalization.AtPrime ((structurePresheafInCommRingCat R).stalk p) p.asIdeal)

中文:
实例 IsLocalization.to_stalk
  签名: (p : PrimeSpectrum R)
  定义体: inferInstanceAs (IsLocalization.AtPrime ((structurePresheafInCommRingCat R).stalk p) p.asIdeal)

Depends on / 依赖: AtPrime, IsLocalization, IsLocalization.AtPrime, asIdeal, p.asIdeal, structurePresheafInCommRingCat
-/
instance IsLocalization.to_stalk (p : PrimeSpectrum R) :
    IsLocalization.AtPrime ((structureSheaf R).presheaf.stalk p) p.asIdeal :=
  inferInstanceAs (IsLocalization.AtPrime ((structurePresheafInCommRingCat R).stalk p) p.asIdeal)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `openAlgebra` / 实例 `openAlgebra`

English:
instance openAlgebra
  signature: (U : (Opens (PrimeSpectrum R))ᵒᵖ)
  body: inferInstanceAs (Algebra R ((structureSheafInType R R).presheaf.obj _))

中文:
实例 openAlgebra
  签名: (U : (Opens (PrimeSpectrum R))ᵒᵖ)
  定义体: inferInstanceAs (Algebra R ((structureSheafInType R R).presheaf.obj _))

Depends on / 依赖: Algebra, presheaf, presheaf.obj, structureSheafInType
-/
instance openAlgebra (U : (Opens (PrimeSpectrum R))ᵒᵖ) : Algebra R ((structureSheaf R).obj.obj U) :=
  inferInstanceAs (Algebra R ((structureSheafInType R R).presheaf.obj _))

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `IsLocalization.to_basicOpen` / 实例 `IsLocalization.to_basicOpen`

English:
instance IsLocalization.to_basicOpen
  signature: (r : R)
  body: inferInstanceAs (IsLocalization.Away r Γ(R, basicOpen r))

中文:
实例 IsLocalization.to_basicOpen
  签名: (r : R)
  定义体: inferInstanceAs (IsLocalization.Away r Γ(R, basicOpen r))

Depends on / 依赖: IsLocalization, IsLocalization.Away, basicOpen
-/
instance IsLocalization.to_basicOpen (r : R) :
    IsLocalization.Away r ((structureSheaf R).obj.obj (op <| basicOpen r)) :=
  inferInstanceAs (IsLocalization.Away r Γ(R, basicOpen r))

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `to_basicOpen_epi` / 实例 `to_basicOpen_epi`

English:
instance to_basicOpen_epi
  signature: (r : R)
  body: ⟨fun _ _ h => CommRingCat.hom_ext (IsLocalization.ringHom_ext (Submonoid.powers r)
    (CommRingCat.hom_ext_iff.mp h))⟩

中文:
实例 to_basicOpen_epi
  签名: (r : R)
  定义体: ⟨fun _ _ h => CommRingCat.hom_ext (IsLocalization.ringHom_ext (Submonoid.powers r)
    (CommRingCat.hom_ext_iff.mp h))⟩

Depends on / 依赖: CommRingCat, CommRingCat.hom_ext, CommRingCat.hom_ext_iff.mp, IsLocalization, IsLocalization.ringHom_ext, Submonoid, Submonoid.powers, hom_ext, hom_ext_iff, powers, ringHom_ext
-/
instance to_basicOpen_epi (r : R) :
    Epi (CommRingCat.ofHom <|
      algebraMap R ((structureSheaf R).obj.obj (op <| basicOpen r))) :=
  ⟨fun _ _ h => CommRingCat.hom_ext (IsLocalization.ringHom_ext (Submonoid.powers r)
    (CommRingCat.hom_ext_iff.mp h))⟩

/-- The ring isomorphism between the ring `R` and the global sections `Γ(X, 𝒪ₓ)`. -/
@[simps! inv]
/--
Definition of `globalSectionsIso` / `globalSectionsIso` 的定义

English:
definition globalSectionsIso
  signature: : CommRingCat.of R ≅ (structureSheaf R).1.obj (op ⊤)
  body: RingEquiv.toCommRingCatIso (.ofBijective _ algebraMap_obj_top_bijective)

中文:
定义 globalSectionsIso
  签名: : CommRingCat.of R ≅ (structureSheaf R).1.obj (op ⊤)
  定义体: RingEquiv.toCommRingCatIso (.ofBijective _ algebraMap_obj_top_bijective)

Depends on / 依赖: RingEquiv, RingEquiv.toCommRingCatIso, algebraMap_obj_top_bijective, ofBijective, toCommRingCatIso
-/
def globalSectionsIso : CommRingCat.of R ≅ (structureSheaf R).1.obj (op ⊤) :=
  RingEquiv.toCommRingCatIso (.ofBijective _ algebraMap_obj_top_bijective)

/--
theorem `globalSectionsIso_hom` / 定理 `globalSectionsIso_hom`

English:
theorem globalSectionsIso_hom
  given: (R : CommRingCat)
  proof: rfl

中文:
定理 globalSectionsIso_hom
  条件: (R : CommRingCat)
  证明: rfl
-/
theorem globalSectionsIso_hom (R : CommRingCat) :
    (globalSectionsIso R).hom = CommRingCat.ofHom (algebraMap _ _) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc, elementwise nosimp]
/--
theorem `toStalk_stalkSpecializes` / 定理 `toStalk_stalkSpecializes`

English:
theorem toStalk_stalkSpecializes
  given: {R : Type*} [CommRing R] {x y : PrimeSpectrum R} (h : x ⤳ y)
  proof: by
  dsimp [toStalk]
  simp [structureSheaf]

中文:
定理 toStalk_stalkSpecializes
  条件: {R : 类型} [CommRing R] {x y : PrimeSpectrum R} (h : x ⤳ y)
  证明: by
  dsimp [toStalk]
  simp [structureSheaf]

Depends on / 依赖: structureSheaf, toStalk
-/
theorem toStalk_stalkSpecializes {R : Type*} [CommRing R] {x y : PrimeSpectrum R} (h : x ⤳ y) :
    toStalk R y ≫ (structureSheaf R).presheaf.stalkSpecializes h = toStalk R x := by
  dsimp [toStalk]
  simp [structureSheaf]

end StructureSheaf

@[expose] public section Comap

variable {S : Type u} [CommRing S] {N : Type u} [AddCommGroup N] [Module S N]
  {σ : R ->+* S} (f : M ->ₛₗ[σ] N)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Localizations.comapFun` / `Localizations.comapFun` 的定义

English:
definition Localizations.comapFun
  signature: (y : PrimeSpectrum.Top S)
  body: letI := Module.compHom N σ
  letI := σ.toAlgebra
  haveI : IsScalarTower R S N := .of_algebraMap_smul fun _ _ => rfl
  letI f' : M ->ₗ[R] N := { __ := f }
  letI g : LocalizedModule (y.comap σ).asIdeal.primeCompl M ->ₗ[R]
      LocalizedModule y.asIdeal.primeCompl N :=
    IsLocalizedModule.lift (y.

中文:
定义 Localizations.comapFun
  签名: (y : PrimeSpectrum.Top S)
  定义体: letI := Module.compHom N σ
  letI := σ.toAlgebra
  haveI : IsScalarTower R S N := .of_algebraMap_smul fun _ _ => rfl
  letI f' : M ->ₗ[R] N := { __ := f }
  letI g : LocalizedModule (y.comap σ).asIdeal.primeCompl M ->ₗ[R]
      LocalizedModule y.asIdeal.primeCompl N :=
    IsLocalizedModule.lift (y.

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.lift, IsLocalizedModule.map_units, IsScalarTower, LocalizedModule, LocalizedModule.mkL, LocalizedModule.mkLinearMap, Module, Module.compHom, asIdeal, asIdeal.primeCompl, compHom, map_units, mkLinearMap, of_algebraMap_smul, primeCompl, restrictScalars, toAlgebra, y.asIdeal.primeCompl, y.comap
-/
def Localizations.comapFun (y : PrimeSpectrum.Top S) :
    Localizations M (y.comap σ) ->ₛₗ[σ] Localizations N y :=
  letI := Module.compHom N σ
  letI := σ.toAlgebra
  haveI : IsScalarTower R S N := .of_algebraMap_smul fun _ _ => rfl
  letI f' : M ->ₗ[R] N := { __ := f }
  letI g : LocalizedModule (y.comap σ).asIdeal.primeCompl M ->ₗ[R]
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
/--
lemma `Localizations.comapFun_mk` / 引理 `Localizations.comapFun_mk`

English:
lemma Localizations.comapFun_mk
  statement: (y : PrimeSpectrum.Top S)
  proof: by
  let := Module.compHom N σ
  let := σ.toAlgebra
  have : IsScalarTower R S N := .of_algebraMap_smul fun _ _ => rfl
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (S := y.asIdeal.primeCompl)
    (LocalizedModule.mkLinearMap y.asIdeal.primeCompl N) ⟨σ b, b.2⟩)).1
  dsimp
  rw [

中文:
引理 Localizations.comapFun_mk
  结论: (y : PrimeSpectrum.Top S)
  证明: by
  let := Module.compHom N σ
  let := σ.toAlgebra
  have : IsScalarTower R S N := .of_algebraMap_smul fun _ _ => rfl
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (S := y.asIdeal.primeCompl)
    (LocalizedModule.mkLinearMap y.asIdeal.primeCompl N) ⟨σ b, b.2⟩)).1
  dsimp
  rw [

Depends on / 依赖: IsLocalizedModu, IsLocalizedModule, IsLocalizedModule.map_units, IsScalarTower, Localizations, LocalizedModule, LocalizedModule.mkLinearMap, LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_cancel, LocalizedModule.smul, Module, Module.End.isUnit_iff, Module.compHom, Submonoid, Submonoid.smul_def, asIdeal, comapFun, compHom, isUnit_iff, map_units
-/
lemma Localizations.comapFun_mk (y : PrimeSpectrum.Top S)
    (a : M) (b : (y.comap σ).asIdeal.primeCompl) :
    Localizations.comapFun f y (.mk a b) = .mk (f a) ⟨σ b.1, b.2⟩ := by
  let := Module.compHom N σ
  let := σ.toAlgebra
  have : IsScalarTower R S N := .of_algebraMap_smul fun _ _ => rfl
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (S := y.asIdeal.primeCompl)
    (LocalizedModule.mkLinearMap y.asIdeal.primeCompl N) ⟨σ b, b.2⟩)).1
  dsimp
  rw [← (comapFun f y).map_smulₛₗ]; rw [LocalizedModule.smul'_mk]; rw [← Submonoid.smul_def]; rw [LocalizedModule.mk_cancel]; rw [← LocalizedModule.mkLinearMap_apply]
  dsimp [comapFun, Localizations]
  refine (IsLocalizedModule.lift_apply ..).trans ?_
  dsimp
  rw [← LocalizedModule.mk_cancel ⟨σ b.1]; rw [b.2⟩]; rw [LocalizedModule.smul'_mk]
  rfl

/--
Definition of `comapFun` / `comapFun` 的定义

English:
definition comapFun
  signature: (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
  body: Localizations.comapFun f _ (s ⟨y.1.comap σ, hUV y.2⟩)

中文:
定义 comapFun
  签名: (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
  定义体: Localizations.comapFun f _ (s ⟨y.1.comap σ, hUV y.2⟩)

Depends on / 依赖: Localizations, Localizations.comapFun, comapFun
-/
def comapFun (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hUV : V.1 subseteq PrimeSpectrum.comap σ ⁻¹' U.1) (s : forall x : U, Localizations M x.1) (y : V) :
    Localizations N y.1 :=
  Localizations.comapFun f _ (s ⟨y.1.comap σ, hUV y.2⟩)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isLocallyFraction_comapFun` / 定理 `isLocallyFraction_comapFun`

English:
theorem isLocallyFraction_comapFun
  statement: (U : Opens (PrimeSpectrum.Top R))
  proof: by
  let := Module.compHom N σ
  let := σ.toAlgebra
  have : IsScalarTower R S N := .of_algebraMap_smul fun _ _ => rfl
  rintro ⟨p, hpV⟩
  obtain ⟨W, m, iWU, a, b, h_frac⟩ := hs ⟨PrimeSpectrum.comap σ p, hUV hpV⟩
  refine ⟨⟨_, (PrimeSpectrum.continuous_comap σ).isOpen_preimage _ W.2⟩ ⊓ V,
    ⟨m, hp

中文:
定理 isLocallyFraction_comapFun
  结论: (U : Opens (PrimeSpectrum.Top R))
  证明: by
  let := Module.compHom N σ
  let := σ.toAlgebra
  have : IsScalarTower R S N := .of_algebraMap_smul fun _ _ => rfl
  rintro ⟨p, hpV⟩
  obtain ⟨W, m, iWU, a, b, h_frac⟩ := hs ⟨PrimeSpectrum.comap σ p, hUV hpV⟩
  refine ⟨⟨_, (PrimeSpectrum.continuous_comap σ).isOpen_preimage _ W.2⟩ ⊓ V,
    ⟨m, hp

Depends on / 依赖: IsScalarTower, Module, Module.compHom, Opens.infLERight, PrimeSpectrum, PrimeSpectrum.comap, PrimeSpectrum.continuous_comap, comapFun, compHom, continuous_comap, h_frac, infLERight, isOpen_preimage, of_algebraMap_smul, toAlgebra
-/
theorem isLocallyFraction_comapFun (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 subseteq PrimeSpectrum.comap σ ⁻¹' U.1)
    (s : forall x : U, Localizations M x.1) (hs : (isLocallyFraction R M).toPrelocalPredicate.pred s) :
    (isLocallyFraction S N).toPrelocalPredicate.pred (comapFun f U V hUV s) := by
  let := Module.compHom N σ
  let := σ.toAlgebra
  have : IsScalarTower R S N := .of_algebraMap_smul fun _ _ => rfl
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
/--
Definition of `comapₗ` / `comapₗ` 的定义

English:
definition comapₗ
  signature: (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
  body: ⟨comapFun f U V hUV s.1, isLocallyFraction_comapFun f U V hUV s.1 s.2⟩
map_add' s t := Subtype.ext funext fun _ => by dsimp [comapFun]; rw [map_add]
map_smul' r m := Subtype.ext funext fun _ => by
    dsimp [comapFun]
    rw [map_smulₛₗ]; rw [← IsScalarTower.algebraMap_smul S]

中文:
定义 comapₗ
  签名: (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
  定义体: ⟨comapFun f U V hUV s.1, isLocallyFraction_comapFun f U V hUV s.1 s.2⟩
map_add' s t := Subtype.ext funext fun _ => by dsimp [comapFun]; rw [map_add]
map_smul' r m := Subtype.ext funext fun _ => by
    dsimp [comapFun]
    rw [map_smulₛₗ]; rw [← IsScalarTower.algebraMap_smul S]

Depends on / 依赖: comapFun, isLocallyFraction_comapFun
-/
def comapₗ (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hUV : V.1 subseteq PrimeSpectrum.comap σ ⁻¹' U.1) :
    Γ(M, U) ->ₛₗ[σ] Γ(N, V) where
  toFun s := ⟨comapFun f U V hUV s.1, isLocallyFraction_comapFun f U V hUV s.1 s.2⟩
map_add' s t := Subtype.ext funext fun _ => by dsimp [comapFun]; rw [map_add]
map_smul' r m := Subtype.ext funext fun _ => by
    dsimp [comapFun]
    rw [map_smulₛₗ]; rw [← IsScalarTower.algebraMap_smul S]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comapₗ_const` / 定理 `comapₗ_const`

English:
theorem comapₗ_const
  statement: (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
  proof: Subtype.ext funext fun _ => by simp [comapₗ, comapFun]

中文:
定理 comapₗ_const
  结论: (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
  证明: Subtype.ext funext fun _ => by simp [comapₗ, comapFun]

Depends on / 依赖: Subtype, Subtype.ext, comapFun
-/
theorem comapₗ_const (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hUV : V.1 subseteq PrimeSpectrum.comap σ ⁻¹' U.1) (a : M) (b : R) (hb : U <= basicOpen b) :
    comapₗ f U V hUV (const a b U hb) = const (f a) (σ b) V (hUV.trans (Set.preimage_mono hb)) :=
Subtype.ext funext fun _ => by simp [comapₗ, comapFun]

section Ring

open Spec (structureSheaf)

variable {S : Type u} [CommRing S] {P : Type u} [CommRing P]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `comapₗ_eq_localRingHom` / 定理 `comapₗ_eq_localRingHom`

English:
theorem comapₗ_eq_localRingHom
  statement: (f : R ->+* S) (U : Opens (PrimeSpectrum.Top R))
  proof: by
  dsimp [comapₗ, comapFun]
  suffices ⇑(Localizations.comapFun f.toSemilinearMap p.1) =
      ⇑(Localization.localRingHom (PrimeSpectrum.comap f p.1).asIdeal _ f rfl) from
    congr($this _)
  ext m
  induction m using LocalizedModule.induction_on with | h m s =>
  trans LocalizedModule.mk (f m) 

中文:
定理 comapₗ_eq_localRingHom
  结论: (f : R ->+* S) (U : Opens (PrimeSpectrum.Top R))
  证明: by
  dsimp [comapₗ, comapFun]
  suffices ⇑(Localizations.comapFun f.toSemilinearMap p.1) =
      ⇑(Localization.localRingHom (PrimeSpectrum.comap f p.1).asIdeal _ f rfl) from
    congr($this _)
  ext m
  induction m using LocalizedModule.induction_on with | h m s =>
  trans LocalizedModule.mk (f m) 

Depends on / 依赖: Localization, Localization.localRingHom, Localization.mk, Localization.mk_eq_mk, Localizations, Localizations.comapFun, LocalizedModule, LocalizedModule.induction_on, LocalizedModule.mk, PrimeSpectrum, PrimeSpectrum.comap, asIdeal, comapFun, convert_to, f.toSemilinearMap, induction_on, localRingHom, mk_eq_mk, toSemilinearMap
-/
theorem comapₗ_eq_localRingHom (f : R ->+* S) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 subseteq PrimeSpectrum.comap f ⁻¹' U.1)
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
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : R ->+* S) (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
  body: comapₗ f.toSemilinearMap U V hUV
map_one' := Subtype.ext funext fun _ => by
    dsimp
    simp only [comapₗ_eq_localRingHom, PrimeSpectrum.comap_asIdeal]
    exact (Localization.localRingHom ..).map_one
map_mul' r s := Subtype.ext funext fun p => by
    dsimp
    change _ = (comapₗ f.toSemilinearMap

中文:
定义 comap
  签名: (f : R ->+* S) (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
  定义体: comapₗ f.toSemilinearMap U V hUV
map_one' := Subtype.ext funext fun _ => by
    dsimp
    simp only [comapₗ_eq_localRingHom, PrimeSpectrum.comap_asIdeal]
    exact (Localization.localRingHom ..).map_one
map_mul' r s := Subtype.ext funext fun p => by
    dsimp
    change _ = (comapₗ f.toSemilinearMap

Depends on / 依赖: f.toSemilinearMap, toSemilinearMap
-/
def comap (f : R ->+* S) (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hUV : V.1 subseteq PrimeSpectrum.comap f ⁻¹' U.1) :
    (structureSheaf R).1.obj (op U) ->+* (structureSheaf S).1.obj (op V) where
  __ := comapₗ f.toSemilinearMap U V hUV
map_one' := Subtype.ext funext fun _ => by
    dsimp
    simp only [comapₗ_eq_localRingHom, PrimeSpectrum.comap_asIdeal]
    exact (Localization.localRingHom ..).map_one
map_mul' r s := Subtype.ext funext fun p => by
    dsimp
    change _ = (comapₗ f.toSemilinearMap U V hUV r).1 p * (comapₗ f.toSemilinearMap U V hUV s).1 p
    simp only [comapₗ_eq_localRingHom, PrimeSpectrum.comap_asIdeal]
    exact (Localization.localRingHom ..).map_mul _ _
map_zero' := Subtype.ext funext fun _ => by
    dsimp
    simp only [comapₗ_eq_localRingHom, PrimeSpectrum.comap_asIdeal]
    exact (Localization.localRingHom ..).map_zero

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `comap_apply` / 定理 `comap_apply`

English:
theorem comap_apply
  statement: (f : R ->+* S) (U : Opens (PrimeSpectrum.Top R))
  proof: comapₗ_eq_localRingHom ..

中文:
定理 comap_apply
  结论: (f : R ->+* S) (U : Opens (PrimeSpectrum.Top R))
  证明: comapₗ_eq_localRingHom ..
-/
theorem comap_apply (f : R ->+* S) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 subseteq PrimeSpectrum.comap f ⁻¹' U.1)
    (s : (structureSheaf R).1.obj (op U)) (p : V) :
    (comap f U V hUV s).1 p =
      Localization.localRingHom (PrimeSpectrum.comap f p.1).asIdeal _ f rfl
        (s.1 ⟨PrimeSpectrum.comap f p.1, hUV p.2⟩) :=
  comapₗ_eq_localRingHom ..

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comap_const` / 定理 `comap_const`

English:
theorem comap_const
  statement: (f : R ->+* S) (U : Opens (PrimeSpectrum.Top R))
  proof: Subtype.ext funext fun p => by
    rw [comap_apply]; rw [const_apply]; rw [const_apply]
    convert_to! Localization.localRingHom _ _ _ _ (Localization.mk _ _) = Localization.mk _ _
    simp [Localization.mk_eq_mk']

中文:
定理 comap_const
  结论: (f : R ->+* S) (U : Opens (PrimeSpectrum.Top R))
  证明: Subtype.ext funext fun p => by
    rw [comap_apply]; rw [const_apply]; rw [const_apply]
    convert_to! Localization.localRingHom _ _ _ _ (Localization.mk _ _) = Localization.mk _ _
    simp [Localization.mk_eq_mk']

Depends on / 依赖: Localization, Localization.localRingHom, Localization.mk, Localization.mk_eq_mk, Subtype, Subtype.ext, comap_apply, const_apply, convert_to, localRingHom, mk_eq_mk
-/
theorem comap_const (f : R ->+* S) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 subseteq PrimeSpectrum.comap f ⁻¹' U.1) (a b : R)
    (hb : forall x : PrimeSpectrum R, x in U -> b in x.asIdeal.primeCompl) :
    comap f U V hUV (const a b U hb) =
      const (f a) (f b) V fun p hpV => hb (PrimeSpectrum.comap f p) (hUV hpV) :=
Subtype.ext funext fun p => by
    rw [comap_apply]; rw [const_apply]; rw [const_apply]
    convert_to! Localization.localRingHom _ _ _ _ (Localization.mk _ _) = Localization.mk _ _
    simp [Localization.mk_eq_mk']

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `comap_id_eq_map` / 定理 `comap_id_eq_map`

English:
theorem comap_id_eq_map
  given: (U V : Opens (PrimeSpectrum.Top R)) (iVU : V ⟶ U)
  proof: RingHom.ext fun s => Subtype.ext funext fun p => by
    rw [comap_apply]
    exact congr($(Localization.localRingHom_id ..) _)

中文:
定理 comap_id_eq_map
  条件: (U V : Opens (PrimeSpectrum.Top R)) (iVU : V ⟶ U)
  证明: RingHom.ext fun s => Subtype.ext funext fun p => by
    rw [comap_apply]
    exact congr($(Localization.localRingHom_id ..) _)

Depends on / 依赖: Localization, Localization.localRingHom_id, RingHom, RingHom.ext, Subtype, Subtype.ext, comap_apply, localRingHom_id
-/
theorem comap_id_eq_map (U V : Opens (PrimeSpectrum.Top R)) (iVU : V ⟶ U) :
    (comap (RingHom.id R) U V fun _ hpV => leOfHom iVU <| hpV) =
      ((structureSheaf R).1.map iVU.op).hom :=
RingHom.ext fun s => Subtype.ext funext fun p => by
    rw [comap_apply]
    exact congr($(Localization.localRingHom_id ..) _)

/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  given: {U V : Opens (PrimeSpectrum.Top R)} (hUV : U = V)
  proof: by
  rw [comap_id_eq_map U V (eqToHom hUV.symm)]; rw [eqToHom_op]; rw [eqToHom_map]

@[simp]

中文:
定理 comap_id
  条件: {U V : Opens (PrimeSpectrum.Top R)} (hUV : U = V)
  证明: by
  rw [comap_id_eq_map U V (eqToHom hUV.symm)]; rw [eqToHom_op]; rw [eqToHom_map]

@[simp]

Depends on / 依赖: comap_id_eq_map, eqToHom, eqToHom_map, eqToHom_op, hUV.symm
-/
theorem comap_id {U V : Opens (PrimeSpectrum.Top R)} (hUV : U = V) :
    (comap (RingHom.id R) U V fun p hpV => by rwa [hUV, PrimeSpectrum.comap_id]) =
      (eqToHom (show (structureSheaf R).1.obj (op U) = _ by rw [hUV])).hom := by
  rw [comap_id_eq_map U V (eqToHom hUV.symm)]; rw [eqToHom_op]; rw [eqToHom_map]

@[simp]
/--
theorem `comap_id'` / 定理 `comap_id'`

English:
theorem comap_id'
  given: (U : Opens (PrimeSpectrum.Top R))
  proof: by
  rw [comap_id rfl]; rfl

中文:
定理 comap_id'
  条件: (U : Opens (PrimeSpectrum.Top R))
  证明: by
  rw [comap_id rfl]; rfl

Depends on / 依赖: comap_id
-/
theorem comap_id' (U : Opens (PrimeSpectrum.Top R)) :
    (comap (RingHom.id R) U U fun p hpU => by rwa [PrimeSpectrum.comap_id]) = RingHom.id _ := by
  rw [comap_id rfl]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comap_comp` / 定理 `comap_comp`

English:
theorem comap_comp
  statement: (f : R ->+* S) (g : S ->+* P) (U : Opens (PrimeSpectrum.Top R))
  proof: RingHom.ext fun s =>
Subtype.ext
      funext fun p => by
        rw [comap_apply]; rw [Localization.localRingHom_comp _ (PrimeSpectrum.comap g p.1).asIdeal] <;>
        simp

中文:
定理 comap_comp
  结论: (f : R ->+* S) (g : S ->+* P) (U : Opens (PrimeSpectrum.Top R))
  证明: RingHom.ext fun s =>
Subtype.ext
      funext fun p => by
        rw [comap_apply]; rw [Localization.localRingHom_comp _ (PrimeSpectrum.comap g p.1).asIdeal] <;>
        simp

Depends on / 依赖: Localization, Localization.localRingHom_comp, PrimeSpectrum, PrimeSpectrum.comap, RingHom, RingHom.ext, Subtype, Subtype.ext, asIdeal, comap_apply, localRingHom_comp
-/
theorem comap_comp (f : R ->+* S) (g : S ->+* P) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (W : Opens (PrimeSpectrum.Top P))
    (hUV : forall p in V, PrimeSpectrum.comap f p in U) (hVW : forall p in W, PrimeSpectrum.comap g p in V) :
    (comap (g.comp f) U W fun p hpW => hUV (PrimeSpectrum.comap g p) (hVW p hpW)) =
      (comap g V W hVW).comp (comap f U V hUV) :=
  RingHom.ext fun s =>
Subtype.ext
      funext fun p => by
        rw [comap_apply]; rw [Localization.localRingHom_comp _ (PrimeSpectrum.comap g p.1).asIdeal] <;>
        simp

set_option backward.isDefEq.respectTransparency.types false in
@[elementwise, reassoc]
/--
theorem `toOpen_comp_comap` / 定理 `toOpen_comp_comap`

English:
theorem toOpen_comp_comap
  given: (f : R ->+* S) (U : Opens (PrimeSpectrum.Top R))
  proof: CommRingCat.hom_ext RingHom.ext fun _ => Subtype.ext funext fun x => by
    dsimp
    rw [comap_apply]
    exact Localization.localRingHom_to_map _ _ _ _ _

中文:
定理 toOpen_comp_comap
  条件: (f : R ->+* S) (U : Opens (PrimeSpectrum.Top R))
  证明: CommRingCat.hom_ext RingHom.ext fun _ => Subtype.ext funext fun x => by
    dsimp
    rw [comap_apply]
    exact Localization.localRingHom_to_map _ _ _ _ _

Depends on / 依赖: CommRingCat, CommRingCat.hom_ext, Localization, Localization.localRingHom_to_map, RingHom, RingHom.ext, Subtype, Subtype.ext, comap_apply, hom_ext, localRingHom_to_map
-/
theorem toOpen_comp_comap (f : R ->+* S) (U : Opens (PrimeSpectrum.Top R)) :
    CommRingCat.ofHom (algebraMap _ _) ≫
      CommRingCat.ofHom (comap f U (Opens.comap ⟨_, PrimeSpectrum.continuous_comap f⟩ U)
        fun _ => id) =
      CommRingCat.ofHom f ≫ CommRingCat.ofHom (algebraMap _ _) :=
CommRingCat.hom_ext RingHom.ext fun _ => Subtype.ext funext fun x => by
    dsimp
    rw [comap_apply]
    exact Localization.localRingHom_to_map _ _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `comap_basicOpen` / 引理 `comap_basicOpen`

English:
lemma comap_basicOpen
  given: (f : R ->+* S) (x : R)
  proof: IsLocalization.ringHom_ext (.powers x) by
    simpa [CommRingCat.hom_ext_iff] using! toOpen_comp_comap f _

中文:
引理 comap_basicOpen
  条件: (f : R ->+* S) (x : R)
  证明: IsLocalization.ringHom_ext (.powers x) by
    simpa [CommRingCat.hom_ext_iff] using! toOpen_comp_comap f _

Depends on / 依赖: powers
-/
lemma comap_basicOpen (f : R ->+* S) (x : R) :
    comap f (PrimeSpectrum.basicOpen x) (PrimeSpectrum.basicOpen (f x))
        (PrimeSpectrum.comap_basicOpen f x).le =
      IsLocalization.map (M := .powers x) (T := .powers (f x)) _ f
        (Submonoid.powers_le.mpr (Submonoid.mem_powers _)) :=
IsLocalization.ringHom_ext (.powers x) by
    simpa [CommRingCat.hom_ext_iff] using! toOpen_comp_comap f _

end Ring

end Comap

end StructureSheaf

end AlgebraicGeometry
