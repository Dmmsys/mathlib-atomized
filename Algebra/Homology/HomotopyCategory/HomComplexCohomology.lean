/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Cohomology of the hom complex

Given `ℤ`-indexed cochain complexes `K` and `L`, and `n : ℤ`, we introduce
a type `HomComplex.CohomologyClass K L n` which is the quotient
of `HomComplex.Cocycle K L n` which identifies cohomologous cocycles.
We construct this type of cohomology classes instead of using
the homology API because `Cochain K L` can be considered both
as a complex of abelian groups or as a complex of `R`-modules
when the category is `R`-linear. This also complements the API
around `HomComplex` which is centered on terms in types
`Cochain` or `Cocycle` which are suitable for computations.

We also show that `HomComplex.CohomologyClass K L n` identifies to
the type of morphisms between `K` and `L⟦n⟧` in the homotopy category.
-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

namespace CochainComplex

variable (K L : CochainComplex C Int) (n m p : Int)

namespace HomComplex

/--
Definition of `coboundaries` / `coboundaries` 的定义

English:
definition coboundaries
  signature: : AddSubgroup (Cocycle K L n) where
  body: Set.ofPred (fun α => exists (m : Int) (hm : m + 1 = n) (β : Cochain K L m), δ m n β = α)
  zero_mem' := ⟨n - 1, by simp, 0, by simp⟩
  add_mem' := by
    rintro α₁ α₂ ⟨m, hm, β₁, hβ₁⟩ ⟨m', hm', β₂, hβ₂⟩
    obtain rfl : m = m' := by lia
    exact ⟨m, hm, β₁ + β₂, by aesop⟩
  neg_mem' := by
    rintr

中文:
定义 coboundaries
  签名: : 加法子群 (Cocycle K L n) where
  定义体: Set.ofPred (fun α => exists (m : Int) (hm : m + 1 = n) (β : Cochain K L m), δ m n β = α)
  zero_mem' := ⟨n - 1, by simp, 0, by simp⟩
  add_mem' := by
    rintro α₁ α₂ ⟨m, hm, β₁, hβ₁⟩ ⟨m', hm', β₂, hβ₂⟩
    obtain rfl : m = m' := by lia
    exact ⟨m, hm, β₁ + β₂, by aesop⟩
  neg_mem' := by
    rintr

Depends on / 依赖: Cochain, Set.ofPred, ofPred
-/
def coboundaries : AddSubgroup (Cocycle K L n) where
  carrier := Set.ofPred (fun α => exists (m : Int) (hm : m + 1 = n) (β : Cochain K L m), δ m n β = α)
  zero_mem' := ⟨n - 1, by simp, 0, by simp⟩
  add_mem' := by
    rintro α₁ α₂ ⟨m, hm, β₁, hβ₁⟩ ⟨m', hm', β₂, hβ₂⟩
    obtain rfl : m = m' := by lia
    exact ⟨m, hm, β₁ + β₂, by aesop⟩
  neg_mem' := by
    rintro α ⟨m, hm, β, hβ⟩
    exact ⟨m, hm, -β, by aesop⟩

set_option backward.isDefEq.respectTransparency.types false in
variable {K L n} in
/--
lemma `mem_coboundaries_iff` / 引理 `mem_coboundaries_iff`

English:
lemma mem_coboundaries_iff
  given: (α : Cocycle K L n) (m : Int) (hm : m + 1 = n)
  proof: by
  simp only [coboundaries, AddSubgroup.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk]
  grind

中文:
引理 mem_coboundaries_iff
  条件: (α : Cocycle K L n) (m : 整数) (hm : m + 1 = n)
  证明: by
  simp only [coboundaries, AddSubgroup.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk]
  grind

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_mk, AddSubmonoid, AddSubmonoid.mem_mk, AddSubsemigroup, AddSubsemigroup.mem_mk, coboundaries, mem_mk
-/
lemma mem_coboundaries_iff (α : Cocycle K L n) (m : Int) (hm : m + 1 = n) :
    α in coboundaries K L n ↔ exists (β : Cochain K L m), δ m n β = α := by
  simp only [coboundaries, AddSubgroup.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk]
  grind

/--
Definition of `CohomologyClass` / `CohomologyClass` 的定义

English:
definition CohomologyClass
  signature: : Type v
  body: Cocycle K L n ⧸ coboundaries K L n

中文:
定义 上同调类
  签名: : 类型v
  定义体: Cocycle K L n ⧸ coboundaries K L n

Depends on / 依赖: Cocycle, coboundaries
-/
def CohomologyClass : Type v := Cocycle K L n ⧸ coboundaries K L n

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (CohomologyClass K L n)
  body: inferInstanceAs (AddCommGroup (Cocycle K L n ⧸ coboundaries K L n))

中文:
实例 :
  签名: 加法交换群 (上同调类 K L n)
  定义体: inferInstanceAs (AddCommGroup (Cocycle K L n ⧸ coboundaries K L n))

Depends on / 依赖: AddCommGroup, Cocycle, coboundaries
-/
instance : AddCommGroup (CohomologyClass K L n) :=
  inferInstanceAs (AddCommGroup (Cocycle K L n ⧸ coboundaries K L n))

namespace CohomologyClass

variable {K L n}

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (x : Cocycle K L n)
  body: Quotient.mk _ x

中文:
定义 mk
  签名: (x : Cocycle K L n)
  定义体: Quotient.mk _ x

Depends on / 依赖: Quotient, Quotient.mk
-/
def mk (x : Cocycle K L n) : CohomologyClass K L n :=
  Quotient.mk _ x

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  statement: Function.Surjective (mk : Cocycle K L n -> _)
  proof: Quotient.mk_surjective

中文:
引理 mk_surjective
  结论: 函数.满射 (mk : Cocycle K L n -> _)
  证明: Quotient.mk_surjective

Depends on / 依赖: Quotient, Quotient.mk_surjective, mk_surjective
-/
lemma mk_surjective : Function.Surjective (mk : Cocycle K L n -> _) :=
  Quotient.mk_surjective

variable (K L n) in
@[simp]
/--
lemma `mk_zero` / 引理 `mk_zero`

English:
lemma mk_zero
  proof: rfl

@[simp]

中文:
引理 mk_zero
  证明: rfl

@[simp]
-/
lemma mk_zero :
    mk (0 : Cocycle K L n) = 0 := rfl

@[simp]
/--
lemma `mk_add` / 引理 `mk_add`

English:
lemma mk_add
  given: (x y : Cocycle K L n)
  proof: rfl

@[simp]

中文:
引理 mk_add
  条件: (x y : Cocycle K L n)
  证明: rfl

@[simp]
-/
lemma mk_add (x y : Cocycle K L n) :
    mk (x + y) = mk x + mk y := rfl

@[simp]
/--
lemma `mk_sub` / 引理 `mk_sub`

English:
lemma mk_sub
  given: (x y : Cocycle K L n)
  proof: rfl

@[simp]

中文:
引理 mk_sub
  条件: (x y : Cocycle K L n)
  证明: rfl

@[simp]
-/
lemma mk_sub (x y : Cocycle K L n) :
    mk (x - y) = mk x - mk y := rfl

@[simp]
/--
lemma `mk_neg` / 引理 `mk_neg`

English:
lemma mk_neg
  given: (x : Cocycle K L n)
  proof: rfl

中文:
引理 mk_neg
  条件: (x : Cocycle K L n)
  证明: rfl
-/
lemma mk_neg (x : Cocycle K L n) :
    mk (-x) = -mk x := rfl

/--
lemma `mk_eq_zero_iff` / 引理 `mk_eq_zero_iff`

English:
lemma mk_eq_zero_iff
  given: (x : Cocycle K L n)
  proof: QuotientAddGroup.eq_zero_iff x

中文:
引理 mk_eq_zero_iff
  条件: (x : Cocycle K L n)
  证明: QuotientAddGroup.eq_zero_iff x

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.eq_zero_iff, eq_zero_iff
-/
lemma mk_eq_zero_iff (x : Cocycle K L n) :
    mk x = 0 ↔ x in coboundaries K L n :=
  QuotientAddGroup.eq_zero_iff x

variable (K L n) in
/-- The projection map `Cocycle K L n →+ CohomologyClass K L n`. -/
@[simps]
/--
Definition of `mkAddMonoidHom` / `mkAddMonoidHom` 的定义

English:
definition mkAddMonoidHom
  signature: : Cocycle K L n ->+ CohomologyClass K L n where
  body: mk
  map_zero' := by simp
  map_add' := by simp

中文:
定义 mkAddMonoidHom
  签名: : Cocycle K L n ->+ 上同调类 K L n where
  定义体: mk
  map_zero' := by simp
  map_add' := by simp
-/
def mkAddMonoidHom : Cocycle K L n ->+ CohomologyClass K L n where
  toFun := mk
  map_zero' := by simp
  map_add' := by simp

section

variable {G : Type*} [AddCommGroup G]
  (f : Cocycle K L n ->+ G) (hf : coboundaries K L n <= f.ker)

/--
Definition of `descAddMonoidHom` / `descAddMonoidHom` 的定义

English:
definition descAddMonoidHom
  signature: :
  body: QuotientAddGroup.lift _ f hf

@[simp]

中文:
定义 descAddMonoidHom
  签名: :
  定义体: QuotientAddGroup.lift _ f hf

@[simp]

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.lift
-/
def descAddMonoidHom :
    CohomologyClass K L n ->+ G :=
  QuotientAddGroup.lift _ f hf

@[simp]
/--
lemma `descAddMonoidHom_cohomologyClass` / 引理 `descAddMonoidHom_cohomologyClass`

English:
lemma descAddMonoidHom_cohomologyClass
  given: (x : Cocycle K L n)
  proof: rfl

中文:
引理 descAddMonoidHom_cohomologyClass
  条件: (x : Cocycle K L n)
  证明: rfl
-/
lemma descAddMonoidHom_cohomologyClass (x : Cocycle K L n) :
    descAddMonoidHom f hf (mk x) = f x := rfl

end

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toHom` / `toHom` 的定义

English:
definition toHom
  signature: :
  body: descAddMonoidHom ((Functor.mapAddHom _).comp Cocycle.equivHomShift.symm.toAddMonoidHom) (by
    rintro ⟨x, _⟩ ⟨m, hm, β, rfl⟩
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
      AddEquiv.toAddMonoidHom_eq_coe, Function.comp_apply, Cocycle.equivHomShift_symm_apply,

中文:
定义 toHom
  签名: :
  定义体: descAddMonoidHom ((Functor.mapAddHom _).comp Cocycle.equivHomShift.symm.toAddMonoidHom) (by
    rintro ⟨x, _⟩ ⟨m, hm, β, rfl⟩
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
      AddEquiv.toAddMonoidHom_eq_coe, Function.comp_apply, Cocycle.equivHomShift_symm_apply,

Depends on / 依赖: AddEquiv, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom, AddMonoidHom.coe_coe, AddMonoidHom.coe_comp, AddMonoidHom.mem_ker, Cochain, Cochain.equivHomotopy, Cocycle, Cocycle.equivHomShift.symm.toAddMonoidHom, Cocycle.equivHomShift_symm_apply, Function, Function.comp_apply, Functor, Functor.mapAddHom, Functor.mapAddHom_apply, HomotopyCategory, HomotopyCategory.quotient_map_eq_zero_iff, coe_coe, coe_comp
-/
def toHom :
    CohomologyClass K L n ->+
      ((HomotopyCategory.quotient C _).obj K ⟶ (HomotopyCategory.quotient C _).obj (L⟦n⟧)) :=
  descAddMonoidHom ((Functor.mapAddHom _).comp Cocycle.equivHomShift.symm.toAddMonoidHom) (by
    rintro ⟨x, _⟩ ⟨m, hm, β, rfl⟩
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
      AddEquiv.toAddMonoidHom_eq_coe, Function.comp_apply, Cocycle.equivHomShift_symm_apply,
      Functor.mapAddHom_apply, HomotopyCategory.quotient_map_eq_zero_iff]
    exact ⟨(Cochain.equivHomotopy _ _).symm ⟨n.negOnePow • β.rightShift _ _ (by lia),
      by simp [Cochain.δ_rightShift _ _ _ _ _ _ (zero_add n), smul_smul]⟩⟩)

/--
lemma `toHom_mk` / 引理 `toHom_mk`

English:
lemma toHom_mk
  given: (x : Cocycle K L n)
  proof: rfl

中文:
引理 toHom_mk
  条件: (x : Cocycle K L n)
  证明: rfl
-/
lemma toHom_mk (x : Cocycle K L n) :
    toHom (mk x) = (HomotopyCategory.quotient C _).map (Cocycle.equivHomShift.symm x) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `toHom_mk_eq_zero_iff` / 引理 `toHom_mk_eq_zero_iff`

English:
lemma toHom_mk_eq_zero_iff
  given: (x : Cocycle K L n)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [coboundaries, exists_prop, AddSubgroup.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
    rw [toHom_mk]; rw [HomotopyCategory.quotient_map_eq_zero_iff] at h
    obtain ⟨γ, h⟩ := Cochain.equivHomotopy _ _ h.some
    

中文:
引理 toHom_mk_eq_zero_iff
  条件: (x : Cocycle K L n)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [coboundaries, exists_prop, AddSubgroup.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
    rw [toHom_mk]; rw [HomotopyCategory.quotient_map_eq_zero_iff] at h
    obtain ⟨γ, h⟩ := Cochain.equivHomotopy _ _ h.some
    

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_mk, AddSubmonoid, AddSubmonoid.mem_mk, AddSubsemigroup, AddSubsemigroup.mem_mk, Cochain, Cochain.equivHomotopy, Cochain.ofHom_zero, Cocycle, Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.equivHomShift_symm_apply, Cocycle.rightShift_coe, HomotopyCategory, HomotopyCategory.quotient_map_eq_zero_iff, Set.mem_ofPred_eq, add_zero, coboundaries, cochain_ofHom_homOf_eq_coe, equivHomShift_symm_apply
-/
lemma toHom_mk_eq_zero_iff (x : Cocycle K L n) :
    toHom (mk x) = 0 ↔ x in coboundaries K L n := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [coboundaries, exists_prop, AddSubgroup.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
    rw [toHom_mk]; rw [HomotopyCategory.quotient_map_eq_zero_iff] at h
    obtain ⟨γ, h⟩ := Cochain.equivHomotopy _ _ h.some
    simp only [Cochain.ofHom_zero, add_zero, Cocycle.equivHomShift_symm_apply,
      Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.rightShift_coe] at h
    exact ⟨n - 1, by simp, n.negOnePow • γ.rightUnshift _ (by lia),
      by simp [Cochain.δ_rightUnshift _ _ _ _ _ (zero_add n), smul_smul, ← h]⟩
  · rw [← mk_eq_zero_iff] at h
    rw [h]; rw [map_zero]

variable (K L n) in
/--
lemma `toHom_bijective` / 引理 `toHom_bijective`

English:
lemma toHom_bijective
  statement: Function.Bijective (toHom : CohomologyClass K L n -> _)
  proof: by
  refine ⟨fun x y h => ?_, fun f => ?_⟩
  · obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [← sub_eq_zero]; rw [← mk_sub]; rw [mk_eq_zero_iff]; rw [← toHom_mk_eq_zero_iff]; rw [mk_sub]; rw [map_sub]; rw [h]; rw [sub_self]
  · obtain ⟨f, rfl⟩ := Functor.map_surjec

中文:
引理 toHom_bijective
  结论: 函数.双射 (toHom : 上同调类 K L n -> _)
  证明: by
  refine ⟨fun x y h => ?_, fun f => ?_⟩
  · obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [← sub_eq_zero]; rw [← mk_sub]; rw [mk_eq_zero_iff]; rw [← toHom_mk_eq_zero_iff]; rw [mk_sub]; rw [map_sub]; rw [h]; rw [sub_self]
  · obtain ⟨f, rfl⟩ := Functor.map_surjec

Depends on / 依赖: Cocycle, Cocycle.equivHomShift, Functor, Functor.map_surjective, equivHomShift, map_sub, map_surjective, mk_eq_zero_iff, mk_sub, mk_surjective, sub_eq_zero, sub_self, toHom_mk, toHom_mk_eq_zero_iff, x.mk_surjective, y.mk_surjective
-/
lemma toHom_bijective : Function.Bijective (toHom : CohomologyClass K L n -> _) := by
  refine ⟨fun x y h => ?_, fun f => ?_⟩
  · obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [← sub_eq_zero]; rw [← mk_sub]; rw [mk_eq_zero_iff]; rw [← toHom_mk_eq_zero_iff]; rw [mk_sub]; rw [map_sub]; rw [h]; rw [sub_self]
  · obtain ⟨f, rfl⟩ := Functor.map_surjective _ f
    exact ⟨mk (Cocycle.equivHomShift f), by simp [toHom_mk]⟩

/-- Cohomology classes identify to morphisms in the homotopy category. -/
@[simps! apply]
/--
Definition of `homAddEquiv` / `homAddEquiv` 的定义

English:
definition homAddEquiv
  signature: :
  body: AddEquiv.ofBijective toHom (toHom_bijective _ _ _)

中文:
定义 homAddEquiv
  签名: :
  定义体: AddEquiv.ofBijective toHom (toHom_bijective _ _ _)

Depends on / 依赖: AddEquiv, AddEquiv.ofBijective, ofBijective, toHom_bijective
-/
noncomputable def homAddEquiv :
    CohomologyClass K L n ≃+
      ((HomotopyCategory.quotient C _).obj K ⟶ (HomotopyCategory.quotient C _).obj (L⟦n⟧)) :=
  AddEquiv.ofBijective toHom (toHom_bijective _ _ _)

end CohomologyClass

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `CohomologyClass K L m` identifies to the cohomology of the complex `HomComplex K L`
in degree `m`. -/
@[simps]
/--
Definition of `leftHomologyData'` / `leftHomologyData'` 的定义

English:
definition leftHomologyData'
  signature: (hm : n + 1 = m) (hp : m + 1 = p)
  body: .of (Cocycle K L m)
  H := .of (CohomologyClass K L m)
  i := AddCommGrpCat.ofHom (Cocycle.toCochainAddMonoidHom K L m)
  π := AddCommGrpCat.ofHom (CohomologyClass.mkAddMonoidHom K L m)
  wi := by cat_disch
  hi := Cocycle.isKernel K L _ _ hp
  wπ := by
    ext x
    dsimp
    rw [CohomologyClass.mk

中文:
定义 leftHomologyData'
  签名: (hm : n + 1 = m) (hp : m + 1 = p)
  定义体: .of (Cocycle K L m)
  H := .of (CohomologyClass K L m)
  i := AddCommGrpCat.ofHom (Cocycle.toCochainAddMonoidHom K L m)
  π := AddCommGrpCat.ofHom (CohomologyClass.mkAddMonoidHom K L m)
  wi := by cat_disch
  hi := Cocycle.isKernel K L _ _ hp
  wπ := by
    ext x
    dsimp
    rw [CohomologyClass.mk

Depends on / 依赖: Cocycle
-/
def leftHomologyData' (hm : n + 1 = m) (hp : m + 1 = p) :
    ((HomComplex K L).sc' n m p).LeftHomologyData where
  K := .of (Cocycle K L m)
  H := .of (CohomologyClass K L m)
  i := AddCommGrpCat.ofHom (Cocycle.toCochainAddMonoidHom K L m)
  π := AddCommGrpCat.ofHom (CohomologyClass.mkAddMonoidHom K L m)
  wi := by cat_disch
  hi := Cocycle.isKernel K L _ _ hp
  wπ := by
    ext x
    dsimp
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n, hm, x, rfl⟩
  hπ :=
    Cofork.IsColimit.mk _
      (fun s => AddCommGrpCat.ofHom (CohomologyClass.descAddMonoidHom s.π.hom
        (by
          rintro ⟨_, _⟩ ⟨q, hq, y, rfl⟩
          obtain rfl : n = q := by lia
          simpa only [zero_comp] using! ConcreteCategory.congr_hom s.condition y)))
      (fun s => rfl)
      (fun s l hl => by
        ext x
        obtain ⟨y, rfl⟩ := x.mk_surjective
        simpa using! ConcreteCategory.congr_hom hl y)

/-- `CohomologyClass K L m` identifies to the cohomology of the complex `HomComplex K L`
in degree `m`. -/
@[simps!]
/--
Definition of `leftHomologyData` / `leftHomologyData` 的定义

English:
definition leftHomologyData
  signature: :
  body: leftHomologyData' K L _ n _ (by simp) (by simp)

中文:
定义 leftHomologyData
  签名: :
  定义体: leftHomologyData' K L _ n _ (by simp) (by simp)

Depends on / 依赖: leftHomologyData
-/
noncomputable def leftHomologyData :
    ((HomComplex K L).sc n).LeftHomologyData :=
  leftHomologyData' K L _ n _ (by simp) (by simp)

/--
Definition of `homologyAddEquiv` / `homologyAddEquiv` 的定义

English:
definition homologyAddEquiv
  signature: :
  body: (leftHomologyData K L n).homologyIso.addCommGroupIsoToAddEquiv

中文:
定义 homologyAddEquiv
  签名: :
  定义体: (leftHomologyData K L n).homologyIso.addCommGroupIsoToAddEquiv

Depends on / 依赖: addCommGroupIsoToAddEquiv, homologyIso, homologyIso.addCommGroupIsoToAddEquiv, leftHomologyData
-/
noncomputable def homologyAddEquiv :
    (HomComplex K L).homology n ≃+ CohomologyClass K L n :=
  (leftHomologyData K L n).homologyIso.addCommGroupIsoToAddEquiv

end HomComplex

end CochainComplex
