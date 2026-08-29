/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.ULift
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Presentations of modules

Given a ring `A`, we introduce a structure `Relations A` which
contains the data that is necessary to define a module by generators and relations.
A term `relations : Relations A` involves two index types: a type `G` for the
generators and a type `R` for the relations. The relation attached to `r : R` is
an element `G →₀ A` which expresses the coefficients of the expected linear relation.

One may think of `relations : Relations A` as a particular shape for systems of
linear equations in any `A`-module `M`. Each `g : G` can be thought of as a
variable (in `M`) and each `r : R` specifies a linear relation that these
variables should satisfy. This way, we get a type `relations.Solution M`.
Then, if `solution : relations.Solution M`, we introduce the predicate
`solution.IsPresentation` which asserts that `solution` is the universal
solution to the given equations, i.e. `solution` gives a presentation
of `M` by generators and relations.

Given an `A`-module `M`, we also introduce the type `Presentation A M` which
contains all the data and properties involved in a presentation of `M` by
generators and relations.

## TODO
* Relate this to `Module.FinitePresentation`
* Behaviour of presentations with respect to the extension of scalars and the restriction of scalars

-/

@[expose] public noncomputable section

assert_not_exists Cardinal

universe w' w'' w₀ w₁ v'' v' v u

namespace Module

variable (A : Type u) [Ring A]

set_option linter.checkUnivs false in
/--
Definition of `Relations` / `Relations` 的定义

English:
structure Relations
  parameters: where
  axioms and operations (3):
    - G : Type w₀
    - R : Type w₁
    - relation((r : R)) : G ->₀ A

中文:
结构 Relations
  参数: where
  公理与运算 (3 个):
    - G : Type w₀
    - R : Type w₁
    - relation((r : R)) : G ->₀ A
-/
structure Relations where
  /-- the index type for generators -/
  G : Type w₀
  /-- the index type for relations -/
  R : Type w₁
  /-- the coefficients of the linear relations that are expected between the generators -/
  relation (r : R) : G ->₀ A

namespace Relations

variable {A} (relations : Relations.{w₀, w₁} A)

/--
Definition of `Quotient` / `Quotient` 的定义

English:
definition Quotient
  body: (relations.G ->₀ A) ⧸ Submodule.span A (Set.range relations.relation)
deriving AddCommGroup, Module A

中文:
定义 Quotient
  定义体: (relations.G ->₀ A) ⧸ Submodule.span A (Set.range relations.relation)
deriving AddCommGroup, Module A

Depends on / 依赖: Set.range, Submodule, Submodule.span, relation, relations, relations.G, relations.relation
-/
def Quotient := (relations.G ->₀ A) ⧸ Submodule.span A (Set.range relations.relation)
deriving AddCommGroup, Module A

/--
Definition of `toQuotient` / `toQuotient` 的定义

English:
definition toQuotient
  signature: : (relations.G ->₀ A) ->ₗ[A] relations.Quotient
  body: Submodule.mkQ _

中文:
定义 toQuotient
  签名: : (relations.G ->₀ A) ->ₗ[A] relations.Quotient
  定义体: Submodule.mkQ _

Depends on / 依赖: Submodule, Submodule.mkQ
-/
def toQuotient : (relations.G ->₀ A) ->ₗ[A] relations.Quotient := Submodule.mkQ _

variable {relations} in
@[ext]
/--
lemma `Quotient.linearMap_ext` / 引理 `Quotient.linearMap_ext`

English:
lemma Quotient.linearMap_ext
  statement: {M : Type v} [AddCommGroup M] [Module A M]
  proof: Submodule.linearMap_qext _ (Finsupp.lhom_ext' (fun g => LinearMap.ext_ring (h g)))

中文:
引理 Quotient.linearMap_ext
  结论: {M : 类型v} [AddCommGroup M] [Module A M]
  证明: Submodule.linearMap_qext _ (Finsupp.lhom_ext' (fun g => LinearMap.ext_ring (h g)))

Depends on / 依赖: Finsupp, Finsupp.lhom_ext, LinearMap, LinearMap.ext_ring, Submodule, Submodule.linearMap_qext, ext_ring, lhom_ext, linearMap_qext
-/
lemma Quotient.linearMap_ext {M : Type v} [AddCommGroup M] [Module A M]
    {f f' : relations.Quotient ->ₗ[A] M}
    (h : forall (g : relations.G), f (relations.toQuotient (Finsupp.single g 1)) =
      f' (relations.toQuotient (Finsupp.single g 1))) :
    f = f' :=
  Submodule.linearMap_qext _ (Finsupp.lhom_ext' (fun g => LinearMap.ext_ring (h g)))

/--
lemma `surjective_toQuotient` / 引理 `surjective_toQuotient`

English:
lemma surjective_toQuotient
  statement: Function.Surjective relations.toQuotient
  proof: Submodule.mkQ_surjective _

中文:
引理 surjective_toQuotient
  结论: Function.Surjective relations.toQuotient
  证明: Submodule.mkQ_surjective _

Depends on / 依赖: Submodule, Submodule.mkQ_surjective, mkQ_surjective
-/
lemma surjective_toQuotient : Function.Surjective relations.toQuotient :=
  Submodule.mkQ_surjective _

/--
lemma `ker_toQuotient` / 引理 `ker_toQuotient`

English:
lemma ker_toQuotient
  proof: Submodule.ker_mkQ _

中文:
引理 ker_toQuotient
  证明: Submodule.ker_mkQ _

Depends on / 依赖: Submodule, Submodule.ker_mkQ, ker_mkQ
-/
lemma ker_toQuotient :
    LinearMap.ker relations.toQuotient = Submodule.span A (Set.range relations.relation) :=
  Submodule.ker_mkQ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `toQuotient_relation` / 引理 `toQuotient_relation`

English:
lemma toQuotient_relation
  given: (r : relations.R)
  proof: by
  dsimp only [toQuotient, Quotient]
  rw [Submodule.mkQ_apply]; rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (by simp)

中文:
引理 toQuotient_relation
  条件: (r : relations.R)
  证明: by
  dsimp only [toQuotient, Quotient]
  rw [Submodule.mkQ_apply]; rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (by simp)

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.mk_eq_zero, Submodule.mkQ_apply, Submodule.subset_span, mkQ_apply, mk_eq_zero, subset_span, toQuotient
-/
lemma toQuotient_relation (r : relations.R) :
    relations.toQuotient (relations.relation r) = 0 := by
  dsimp only [toQuotient, Quotient]
  rw [Submodule.mkQ_apply]; rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (by simp)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : (relations.R ->₀ A) ->ₗ[A] (relations.G ->₀ A)
  body: Finsupp.linearCombination _ relations.relation

@[simp]

中文:
定义 map
  签名: : (relations.R ->₀ A) ->ₗ[A] (relations.G ->₀ A)
  定义体: Finsupp.linearCombination _ relations.relation

@[simp]

Depends on / 依赖: Finsupp, Finsupp.linearCombination, linearCombination, relation, relations, relations.relation
-/
def map : (relations.R ->₀ A) ->ₗ[A] (relations.G ->₀ A) :=
  Finsupp.linearCombination _ relations.relation

@[simp]
/--
lemma `map_single` / 引理 `map_single`

English:
lemma map_single
  given: (r : relations.R)
  proof: by
  simp [map]

@[simp]

中文:
引理 map_single
  条件: (r : relations.R)
  证明: by
  simp [map]

@[simp]
-/
lemma map_single (r : relations.R) :
    relations.map (Finsupp.single r 1) = relations.relation r := by
  simp [map]

@[simp]
/--
lemma `range_map` / 引理 `range_map`

English:
lemma range_map
  proof: Finsupp.range_linearCombination _

@[simp]

中文:
引理 range_map
  证明: Finsupp.range_linearCombination _

@[simp]

Depends on / 依赖: Finsupp, Finsupp.range_linearCombination, range_linearCombination
-/
lemma range_map :
    LinearMap.range relations.map = Submodule.span A (Set.range relations.relation) :=
  Finsupp.range_linearCombination _

@[simp]
/--
lemma `toQuotient_map` / 引理 `toQuotient_map`

English:
lemma toQuotient_map
  statement: relations.toQuotient.comp relations.map = 0
  proof: by aesop

@[simp]

中文:
引理 toQuotient_map
  结论: relations.toQuotient.comp relations.map = 0
  证明: by aesop

@[simp]
-/
lemma toQuotient_map : relations.toQuotient.comp relations.map = 0 := by aesop

@[simp]
/--
lemma `toQuotient_map_apply` / 引理 `toQuotient_map_apply`

English:
lemma toQuotient_map_apply
  given: (x : relations.R ->₀ A)
  proof: DFunLike.congr_fun relations.toQuotient_map x

中文:
引理 toQuotient_map_apply
  条件: (x : relations.R ->₀ A)
  证明: DFunLike.congr_fun relations.toQuotient_map x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, relations, relations.toQuotient_map, toQuotient_map
-/
lemma toQuotient_map_apply (x : relations.R ->₀ A) :
    relations.toQuotient (relations.map x) = 0 :=
  DFunLike.congr_fun relations.toQuotient_map x

variable (M : Type v) [AddCommGroup M] [Module A M]

/-- The type of solutions in a module `M` of the equations given by `relations : Relations A`. -/
@[ext]
/--
Definition of `Solution` / `Solution` 的定义

English:
structure Solution
  parameters: where
  axioms and operations (2):
    - var((g : relations.G)) : M
    - linearCombination_var_relation((r : relations.R)) : Finsupp.linearCombination _ var (relations.relation r) = 0

中文:
结构 Solution
  参数: where
  公理与运算 (2 个):
    - var((g : relations.G)) : M
    - linearCombination_var_relation((r : relations.R)) : Finsupp.linearCombination _ var (relations.relation r) = 0
-/
structure Solution where
  /-- the image in `M` of each variable -/
  var (g : relations.G) : M
  linearCombination_var_relation (r : relations.R) :
    Finsupp.linearCombination _ var (relations.relation r) = 0

namespace Solution

variable {relations M}

section

variable (solution : relations.Solution M)

/--
Definition of `π` / `π` 的定义

English:
definition π
  signature: : (relations.G ->₀ A) ->ₗ[A] M
  body: Finsupp.linearCombination _ solution.var

@[simp]

中文:
定义 π
  签名: : (relations.G ->₀ A) ->ₗ[A] M
  定义体: Finsupp.linearCombination _ solution.var

@[simp]

Depends on / 依赖: Finsupp, Finsupp.linearCombination, linearCombination, solution, solution.var
-/
def π : (relations.G ->₀ A) ->ₗ[A] M := Finsupp.linearCombination _ solution.var

@[simp]
/--
lemma `π_single` / 引理 `π_single`

English:
lemma π_single
  given: (g : relations.G)
  proof: by simp [π]

@[simp]

中文:
引理 π_single
  条件: (g : relations.G)
  证明: by simp [π]

@[simp]
-/
lemma π_single (g : relations.G) :
    solution.π (Finsupp.single g 1) = solution.var g := by simp [π]

@[simp]
/--
lemma `π_relation` / 引理 `π_relation`

English:
lemma π_relation
  given: (r : relations.R)
  statement: solution.π (relations.relation r) = 0
  proof: solution.linearCombination_var_relation r

@[simp]

中文:
引理 π_relation
  条件: (r : relations.R)
  结论: solution.π (relations.relation r) = 0
  证明: solution.linearCombination_var_relation r

@[simp]

Depends on / 依赖: linearCombination_var_relation, solution, solution.linearCombination_var_relation
-/
lemma π_relation (r : relations.R) : solution.π (relations.relation r) = 0 :=
  solution.linearCombination_var_relation r

@[simp]
/--
lemma `π_comp_map` / 引理 `π_comp_map`

English:
lemma π_comp_map
  statement: solution.π.comp relations.map = 0
  proof: by aesop

@[simp]

中文:
引理 π_comp_map
  结论: solution.π.comp relations.map = 0
  证明: by aesop

@[simp]
-/
lemma π_comp_map : solution.π.comp relations.map = 0 := by aesop

@[simp]
/--
lemma `π_comp_map_apply` / 引理 `π_comp_map_apply`

English:
lemma π_comp_map_apply
  given: (x : relations.R ->₀ A)
  statement: solution.π (relations.map x) = 0
  proof: by
  change solution.π.comp relations.map x = 0
  rw [π_comp_map]; rw [LinearMap.zero_apply]

中文:
引理 π_comp_map_apply
  条件: (x : relations.R ->₀ A)
  结论: solution.π (relations.map x) = 0
  证明: by
  change solution.π.comp relations.map x = 0
  rw [π_comp_map]; rw [LinearMap.zero_apply]

Depends on / 依赖: LinearMap, LinearMap.zero_apply, relations, relations.map, solution, zero_apply
-/
lemma π_comp_map_apply (x : relations.R ->₀ A) : solution.π (relations.map x) = 0 := by
  change solution.π.comp relations.map x = 0
  rw [π_comp_map]; rw [LinearMap.zero_apply]

/--
lemma `range_π` / 引理 `range_π`

English:
lemma range_π
  statement: LinearMap.range solution.π = Submodule.span A (Set.range solution.var)
  proof: Finsupp.range_linearCombination _

中文:
引理 range_π
  结论: LinearMap.range solution.π = Submodule.span A (Set.range solution.var)
  证明: Finsupp.range_linearCombination _

Depends on / 依赖: Finsupp, Finsupp.range_linearCombination, range_linearCombination
-/
lemma range_π : LinearMap.range solution.π = Submodule.span A (Set.range solution.var) :=
  Finsupp.range_linearCombination _

/--
lemma `span_relation_le_ker_π` / 引理 `span_relation_le_ker_π`

English:
lemma span_relation_le_ker_π
  proof: by
  rw [Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, π_relation]

中文:
引理 span_relation_le_ker_π
  证明: by
  rw [Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, π_relation]

Depends on / 依赖: LinearMap, LinearMap.mem_ker, SetLike, SetLike.mem_coe, Submodule, Submodule.span_le, mem_coe, mem_ker, span_le
-/
lemma span_relation_le_ker_π :
    Submodule.span A (Set.range relations.relation) <= LinearMap.ker solution.π := by
  rw [Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, π_relation]

/--
Definition of `fromQuotient` / `fromQuotient` 的定义

English:
definition fromQuotient
  signature: : relations.Quotient ->ₗ[A] M
  body: Submodule.liftQ _ solution.π solution.span_relation_le_ker_π

@[simp]

中文:
定义 fromQuotient
  签名: : relations.Quotient ->ₗ[A] M
  定义体: Submodule.liftQ _ solution.π solution.span_relation_le_ker_π

@[simp]

Depends on / 依赖: Submodule, Submodule.liftQ, solution, solution.span_relation_le_ker_
-/
def fromQuotient : relations.Quotient ->ₗ[A] M :=
  Submodule.liftQ _ solution.π solution.span_relation_le_ker_π

@[simp]
/--
lemma `fromQuotient_comp_toQuotient` / 引理 `fromQuotient_comp_toQuotient`

English:
lemma fromQuotient_comp_toQuotient
  proof: rfl

@[simp]

中文:
引理 fromQuotient_comp_toQuotient
  证明: rfl

@[simp]
-/
lemma fromQuotient_comp_toQuotient :
    solution.fromQuotient.comp relations.toQuotient = solution.π := rfl

@[simp]
/--
lemma `fromQuotient_toQuotient` / 引理 `fromQuotient_toQuotient`

English:
lemma fromQuotient_toQuotient
  given: (x : relations.G ->₀ A)
  proof: rfl

中文:
引理 fromQuotient_toQuotient
  条件: (x : relations.G ->₀ A)
  证明: rfl
-/
lemma fromQuotient_toQuotient (x : relations.G ->₀ A) :
    solution.fromQuotient (relations.toQuotient x) = solution.π x := rfl

variable {N : Type v'} [AddCommGroup N] [Module A N] (f : M ->ₗ[A] N)

/-- The image of a solution to `relations : Relation A` by a linear map `M →ₗ[A] N`. -/
@[simps]
/--
Definition of `postcomp` / `postcomp` 的定义

English:
definition postcomp
  signature: : relations.Solution N where
  body: f (solution.var g)
  linearCombination_var_relation r := by
    have : Finsupp.linearCombination _ (fun g => f (solution.var g)) = f.comp solution.π := by aesop
    simp [this]

@[simp]

中文:
定义 postcomp
  签名: : relations.Solution N where
  定义体: f (solution.var g)
  linearCombination_var_relation r := by
    have : Finsupp.linearCombination _ (fun g => f (solution.var g)) = f.comp solution.π := by aesop
    simp [this]

@[simp]

Depends on / 依赖: solution, solution.var
-/
def postcomp : relations.Solution N where
  var g := f (solution.var g)
  linearCombination_var_relation r := by
    have : Finsupp.linearCombination _ (fun g => f (solution.var g)) = f.comp solution.π := by aesop
    simp [this]

@[simp]
/--
lemma `postcomp_comp` / 引理 `postcomp_comp`

English:
lemma postcomp_comp
  given: {N' : Type v''} [AddCommGroup N'] [Module A N'] (g : N ->ₗ[A] N')
  proof: rfl

@[simp]

中文:
引理 postcomp_comp
  条件: {N' : 类型v''} [AddCommGroup N'] [Module A N'] (g : N ->ₗ[A] N')
  证明: rfl

@[simp]
-/
lemma postcomp_comp {N' : Type v''} [AddCommGroup N'] [Module A N'] (g : N ->ₗ[A] N') :
    solution.postcomp (g.comp f) = (solution.postcomp f).postcomp g := rfl

@[simp]
/--
lemma `postcomp_id` / 引理 `postcomp_id`

English:
lemma postcomp_id
  statement: solution.postcomp LinearMap.id = solution
  proof: rfl

中文:
引理 postcomp_id
  结论: solution.postcomp LinearMap.id = solution
  证明: rfl
-/
lemma postcomp_id : solution.postcomp LinearMap.id = solution := rfl

variable {solution}

/--
lemma `congr_var` / 引理 `congr_var`

English:
lemma congr_var
  given: {solution' : relations.Solution M} (h : solution = solution') (g : relations.G)
  proof: by rw [h]

中文:
引理 congr_var
  条件: {solution' : relations.Solution M} (h : solution = solution') (g : relations.G)
  证明: by rw [h]
-/
lemma congr_var {solution' : relations.Solution M} (h : solution = solution') (g : relations.G) :
    solution.var g = solution'.var g := by rw [h]

/--
lemma `congr_postcomp` / 引理 `congr_postcomp`

English:
lemma congr_postcomp
  statement: {solution' : relations.Solution M} (h : solution = solution')
  proof: by rw [h]

中文:
引理 congr_postcomp
  结论: {solution' : relations.Solution M} (h : solution = solution')
  证明: by rw [h]
-/
lemma congr_postcomp {solution' : relations.Solution M} (h : solution = solution')
    (f : M ->ₗ[A] N) : solution.postcomp f = solution'.postcomp f := by rw [h]

end

section

variable (π : (relations.G ->₀ A) ->ₗ[A] M) (hπ : forall (r : relations.R), π (relations.relation r) = 0)

/-- Given `relations : Relations A` and an `A`-module `M`, this is a constructor
for `relations.Solution M` for which the data is given as
a linear map `π : (relations.G →₀ A) →ₗ[A] M`. (See also `ofπ'` for an alternate
vanishing criterion.) -/
@[simps -isSimp]
/--
Definition of `ofπ` / `ofπ` 的定义

English:
definition ofπ
  signature: : relations.Solution M where
  body: π (Finsupp.single g 1)
  linearCombination_var_relation r := by
    have : π = Finsupp.linearCombination _ (fun g => π (Finsupp.single g 1)) := by ext; simp
    rw [← this]
    exact hπ r

@[simp]

中文:
定义 ofπ
  签名: : relations.Solution M where
  定义体: π (Finsupp.single g 1)
  linearCombination_var_relation r := by
    have : π = Finsupp.linearCombination _ (fun g => π (Finsupp.single g 1)) := by ext; simp
    rw [← this]
    exact hπ r

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single, single
-/
def ofπ : relations.Solution M where
  var g := π (Finsupp.single g 1)
  linearCombination_var_relation r := by
    have : π = Finsupp.linearCombination _ (fun g => π (Finsupp.single g 1)) := by ext; simp
    rw [← this]
    exact hπ r

@[simp]
/--
lemma `ofπ_π` / 引理 `ofπ_π`

English:
lemma ofπ_π
  statement: (ofπ π hπ).π = π
  proof: by ext; simp [ofπ]

中文:
引理 ofπ_π
  结论: (ofπ π hπ).π = π
  证明: by ext; simp [ofπ]
-/
lemma ofπ_π : (ofπ π hπ).π = π := by ext; simp [ofπ]

end

section

variable (π : (relations.G ->₀ A) ->ₗ[A] M) (hπ : π.comp relations.map = 0)

/-- Variant of `ofπ` where the vanishing condition is expressed in terms
of a composition of linear maps. -/
@[simps! -isSimp]
/--
Definition of `ofπ'` / `ofπ'` 的定义

English:
definition ofπ'
  signature: : relations.Solution M
  body: ofπ π (fun r => by
    simpa using DFunLike.congr_fun hπ (Finsupp.single r 1))

@[simp]

中文:
定义 ofπ'
  签名: : relations.Solution M
  定义体: ofπ π (fun r => by
    simpa using DFunLike.congr_fun hπ (Finsupp.single r 1))

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Finsupp, Finsupp.single, congr_fun, single
-/
def ofπ' : relations.Solution M :=
  ofπ π (fun r => by
    simpa using DFunLike.congr_fun hπ (Finsupp.single r 1))

@[simp]
/--
lemma `ofπ'_π` / 引理 `ofπ'_π`

English:
lemma ofπ'_π
  statement: (ofπ' π hπ).π = π
  proof: by simp [ofπ']

中文:
引理 ofπ'_π
  结论: (ofπ' π hπ).π = π
  证明: by simp [ofπ']
-/
lemma ofπ'_π : (ofπ' π hπ).π = π := by simp [ofπ']

end

section

variable (solution : relations.Solution M)

/--
lemma `injective_fromQuotient_iff_ker_π_eq_span` / 引理 `injective_fromQuotient_iff_ker_π_eq_span`

English:
lemma injective_fromQuotient_iff_ker_π_eq_span
  proof: by
  constructor
  · intro h
    rw [← ker_toQuotient]; rw [← fromQuotient_comp_toQuotient]; rw [LinearMap.ker_comp]; rw [LinearMap.ker_eq_bot.2 h]; rw [Submodule.comap_bot]
  · intro h
    rw [← LinearMap.ker_eq_bot]; rw [eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := relations.surjective_toQuot

中文:
引理 injective_fromQuotient_iff_ker_π_eq_span
  证明: by
  constructor
  · intro h
    rw [← ker_toQuotient]; rw [← fromQuotient_comp_toQuotient]; rw [LinearMap.ker_comp]; rw [LinearMap.ker_eq_bot.2 h]; rw [Submodule.comap_bot]
  · intro h
    rw [← LinearMap.ker_eq_bot]; rw [eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := relations.surjective_toQuot

Depends on / 依赖: LinearMap, LinearMap.ker, LinearMap.ker_comp, LinearMap.ker_eq_bot, LinearMap.mem_ker, Submodule, Submodule.comap_bot, Submodule.zero_, comap_bot, eq_bot_iff, fromQuotient_comp_toQuotient, fromQuotient_toQuotient, ker_comp, ker_eq_bot, ker_toQuotient, mem_ker, range_map, relations, relations.surjective_toQuotient, replace
-/
lemma injective_fromQuotient_iff_ker_π_eq_span :
    Function.Injective solution.fromQuotient ↔
      LinearMap.ker solution.π = Submodule.span A (Set.range relations.relation) := by
  constructor
  · intro h
    rw [← ker_toQuotient]; rw [← fromQuotient_comp_toQuotient]; rw [LinearMap.ker_comp]; rw [LinearMap.ker_eq_bot.2 h]; rw [Submodule.comap_bot]
  · intro h
    rw [← LinearMap.ker_eq_bot]; rw [eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := relations.surjective_toQuotient x
    replace hx : x in LinearMap.ker solution.π := by
      simpa only [LinearMap.mem_ker, fromQuotient_toQuotient] using hx
    rw [h]; rw [← range_map] at hx
    obtain ⟨x, rfl⟩ := hx
    simp only [toQuotient_map_apply, Submodule.zero_mem]

/--
lemma `surjective_fromQuotient_iff_surjective_π` / 引理 `surjective_fromQuotient_iff_surjective_π`

English:
lemma surjective_fromQuotient_iff_surjective_π
  proof: by
  simpa only [← fromQuotient_comp_toQuotient] using!
    (Function.Surjective.of_comp_iff (f := solution.fromQuotient)
      relations.surjective_toQuotient).symm

中文:
引理 surjective_fromQuotient_iff_surjective_π
  证明: by
  simpa only [← fromQuotient_comp_toQuotient] using!
    (Function.Surjective.of_comp_iff (f := solution.fromQuotient)
      relations.surjective_toQuotient).symm

Depends on / 依赖: Function, Function.Surjective.of_comp_iff, Surjective, fromQuotient, fromQuotient_comp_toQuotient, of_comp_iff, relations, relations.surjective_toQuotient, solution, solution.fromQuotient, surjective_toQuotient
-/
lemma surjective_fromQuotient_iff_surjective_π :
    Function.Surjective solution.fromQuotient ↔ Function.Surjective solution.π := by
  simpa only [← fromQuotient_comp_toQuotient] using!
    (Function.Surjective.of_comp_iff (f := solution.fromQuotient)
      relations.surjective_toQuotient).symm

/--
lemma `surjective_π_iff_span_eq_top` / 引理 `surjective_π_iff_span_eq_top`

English:
lemma surjective_π_iff_span_eq_top
  proof: by
  rw [← LinearMap.range_eq_top]; rw [range_π]

中文:
引理 surjective_π_iff_span_eq_top
  证明: by
  rw [← LinearMap.range_eq_top]; rw [range_π]

Depends on / 依赖: LinearMap, LinearMap.range_eq_top, range_eq_top
-/
lemma surjective_π_iff_span_eq_top :
    Function.Surjective solution.π ↔
      Submodule.span A (Set.range solution.var) = ⊤ := by
  rw [← LinearMap.range_eq_top]; rw [range_π]

end

/--
Definition of `IsPresentation` / `IsPresentation` 的定义

English:
structure IsPresentation
  parameters: (solution : relations.Solution M)
  axioms and operations (1):
    - bijective : Function.Bijective solution.fromQuotient

中文:
结构 IsPresentation
  参数: (solution : relations.Solution M)
  公理与运算 (1 个):
    - bijective : Function.Bijective solution.fromQuotient
-/
structure IsPresentation (solution : relations.Solution M) : Prop where
  bijective : Function.Bijective solution.fromQuotient

namespace IsPresentation

variable {solution : relations.Solution M} (h : solution.IsPresentation)

include h

/--
Definition of `linearEquiv` / `linearEquiv` 的定义

English:
definition linearEquiv
  signature: : relations.Quotient ≃ₗ[A] M
  body: LinearEquiv.ofBijective _ h.bijective

@[simp]

中文:
定义 linearEquiv
  签名: : relations.Quotient ≃ₗ[A] M
  定义体: LinearEquiv.ofBijective _ h.bijective

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, bijective, h.bijective, ofBijective
-/
def linearEquiv : relations.Quotient ≃ₗ[A] M := LinearEquiv.ofBijective _ h.bijective

@[simp]
/--
lemma `linearEquiv_apply` / 引理 `linearEquiv_apply`

English:
lemma linearEquiv_apply
  given: (x : relations.Quotient)
  proof: rfl

@[simp]

中文:
引理 linearEquiv_apply
  条件: (x : relations.Quotient)
  证明: rfl

@[simp]
-/
lemma linearEquiv_apply (x : relations.Quotient) :
    h.linearEquiv x = solution.fromQuotient x := rfl

@[simp]
/--
lemma `linearEquiv_symm_var` / 引理 `linearEquiv_symm_var`

English:
lemma linearEquiv_symm_var
  given: (g : relations.G)
  proof: h.linearEquiv.injective (by simp)

中文:
引理 linearEquiv_symm_var
  条件: (g : relations.G)
  证明: h.linearEquiv.injective (by simp)

Depends on / 依赖: h.linearEquiv.injective, injective, linearEquiv
-/
lemma linearEquiv_symm_var (g : relations.G) :
    h.linearEquiv.symm (solution.var g) = relations.toQuotient (Finsupp.single g 1) :=
  h.linearEquiv.injective (by simp)

/--
lemma `surjective_π` / 引理 `surjective_π`

English:
lemma surjective_π
  statement: Function.Surjective solution.π
  proof: by
  simpa only [← surjective_fromQuotient_iff_surjective_π] using h.bijective.2

中文:
引理 surjective_π
  结论: Function.Surjective solution.π
  证明: by
  simpa only [← surjective_fromQuotient_iff_surjective_π] using h.bijective.2

Depends on / 依赖: bijective, h.bijective
-/
lemma surjective_π : Function.Surjective solution.π := by
  simpa only [← surjective_fromQuotient_iff_surjective_π] using h.bijective.2

/--
lemma `ker_π` / 引理 `ker_π`

English:
lemma ker_π
  statement: LinearMap.ker solution.π = Submodule.span A (Set.range relations.relation)
  proof: by
  simpa only [← injective_fromQuotient_iff_ker_π_eq_span] using h.bijective.1

中文:
引理 ker_π
  结论: LinearMap.ker solution.π = Submodule.span A (Set.range relations.relation)
  证明: by
  simpa only [← injective_fromQuotient_iff_ker_π_eq_span] using h.bijective.1

Depends on / 依赖: bijective, h.bijective
-/
lemma ker_π : LinearMap.ker solution.π = Submodule.span A (Set.range relations.relation) := by
  simpa only [← injective_fromQuotient_iff_ker_π_eq_span] using h.bijective.1

/--
lemma `exact` / 引理 `exact`

English:
lemma exact
  statement: Function.Exact relations.map solution.π
  proof: by
  rw [LinearMap.exact_iff]; rw [range_map]; rw [← solution.injective_fromQuotient_iff_ker_π_eq_span]
  exact h.bijective.1

中文:
引理 exact
  结论: Function.Exact relations.map solution.π
  证明: by
  rw [LinearMap.exact_iff]; rw [range_map]; rw [← solution.injective_fromQuotient_iff_ker_π_eq_span]
  exact h.bijective.1

Depends on / 依赖: LinearMap, LinearMap.exact_iff, bijective, exact_iff, h.bijective, range_map, solution, solution.injective_fromQuotient_iff_ker_
-/
lemma exact : Function.Exact relations.map solution.π := by
  rw [LinearMap.exact_iff]; rw [range_map]; rw [← solution.injective_fromQuotient_iff_ker_π_eq_span]
  exact h.bijective.1

variable {N : Type v'} [AddCommGroup N] [Module A N]

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: (s : relations.Solution N)
  body: s.fromQuotient.comp h.linearEquiv.symm.toLinearMap

@[simp]

中文:
定义 desc
  签名: (s : relations.Solution N)
  定义体: s.fromQuotient.comp h.linearEquiv.symm.toLinearMap

@[simp]

Depends on / 依赖: fromQuotient, h.linearEquiv.symm.toLinearMap, linearEquiv, s.fromQuotient.comp, toLinearMap
-/
def desc (s : relations.Solution N) : M ->ₗ[A] N :=
  s.fromQuotient.comp h.linearEquiv.symm.toLinearMap

@[simp]
/--
lemma `desc_var` / 引理 `desc_var`

English:
lemma desc_var
  given: (s : relations.Solution N) (g : relations.G)
  proof: by
  dsimp [desc]
  simp only [linearEquiv_symm_var, fromQuotient_toQuotient, π_single]

@[simp]

中文:
引理 desc_var
  条件: (s : relations.Solution N) (g : relations.G)
  证明: by
  dsimp [desc]
  simp only [linearEquiv_symm_var, fromQuotient_toQuotient, π_single]

@[simp]

Depends on / 依赖: fromQuotient_toQuotient, linearEquiv_symm_var
-/
lemma desc_var (s : relations.Solution N) (g : relations.G) :
    h.desc s (solution.var g) = s.var g := by
  dsimp [desc]
  simp only [linearEquiv_symm_var, fromQuotient_toQuotient, π_single]

@[simp]
/--
lemma `desc_comp_π` / 引理 `desc_comp_π`

English:
lemma desc_comp_π
  given: (s : relations.Solution N)
  statement: (h.desc s).comp solution.π = s.π
  proof: by aesop

@[simp]

中文:
引理 desc_comp_π
  条件: (s : relations.Solution N)
  结论: (h.desc s).comp solution.π = s.π
  证明: by aesop

@[simp]
-/
lemma desc_comp_π (s : relations.Solution N) : (h.desc s).comp solution.π = s.π := by aesop

@[simp]
/--
lemma `π_desc_apply` / 引理 `π_desc_apply`

English:
lemma π_desc_apply
  given: (s : relations.Solution N) (x : relations.G ->₀ A)
  proof: DFunLike.congr_fun (h.desc_comp_π s) x

@[simp]

中文:
引理 π_desc_apply
  条件: (s : relations.Solution N) (x : relations.G ->₀ A)
  证明: DFunLike.congr_fun (h.desc_comp_π s) x

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, h.desc_comp_
-/
lemma π_desc_apply (s : relations.Solution N) (x : relations.G ->₀ A) :
    h.desc s (solution.π x) = s.π x :=
  DFunLike.congr_fun (h.desc_comp_π s) x

@[simp]
/--
lemma `postcomp_desc` / 引理 `postcomp_desc`

English:
lemma postcomp_desc
  given: (s : relations.Solution N)
  proof: by aesop

中文:
引理 postcomp_desc
  条件: (s : relations.Solution N)
  证明: by aesop
-/
lemma postcomp_desc (s : relations.Solution N) :
    solution.postcomp (h.desc s) = s := by aesop

/--
lemma `postcomp_injective` / 引理 `postcomp_injective`

English:
lemma postcomp_injective
  statement: {f f' : M ->ₗ[A] N}
  proof: by
  suffices f.comp solution.fromQuotient = f'.comp solution.fromQuotient by
    ext x
    obtain ⟨y, rfl⟩ := h.bijective.2 x
    exact DFunLike.congr_fun this y
  ext g
  simpa using congr_var h' g

中文:
引理 postcomp_injective
  结论: {f f' : M ->ₗ[A] N}
  证明: by
  suffices f.comp solution.fromQuotient = f'.comp solution.fromQuotient by
    ext x
    obtain ⟨y, rfl⟩ := h.bijective.2 x
    exact DFunLike.congr_fun this y
  ext g
  simpa using congr_var h' g

Depends on / 依赖: DFunLike, DFunLike.congr_fun, bijective, congr_fun, congr_var, f.comp, fromQuotient, h.bijective, solution, solution.fromQuotient
-/
lemma postcomp_injective {f f' : M ->ₗ[A] N}
    (h' : solution.postcomp f = solution.postcomp f') : f = f' := by
  suffices f.comp solution.fromQuotient = f'.comp solution.fromQuotient by
    ext x
    obtain ⟨y, rfl⟩ := h.bijective.2 x
    exact DFunLike.congr_fun this y
  ext g
  simpa using congr_var h' g

/-- If `M` admits a presentation by generators and relations, then
linear maps from `M` can be (naturally) identified to the solutions of
certain linear equations. -/
@[simps]
/--
Definition of `linearMapEquiv` / `linearMapEquiv` 的定义

English:
definition linearMapEquiv
  signature: : (M ->ₗ[A] N) ≃ relations.Solution N where
  body: solution.postcomp f
  invFun s := h.desc s
  left_inv f := h.postcomp_injective (by simp)
  right_inv s := by simp

中文:
定义 linearMapEquiv
  签名: : (M ->ₗ[A] N) ≃ relations.Solution N where
  定义体: solution.postcomp f
  invFun s := h.desc s
  left_inv f := h.postcomp_injective (by simp)
  right_inv s := by simp

Depends on / 依赖: postcomp, solution, solution.postcomp
-/
def linearMapEquiv : (M ->ₗ[A] N) ≃ relations.Solution N where
  toFun f := solution.postcomp f
  invFun s := h.desc s
  left_inv f := h.postcomp_injective (by simp)
  right_inv s := by simp

section

variable {solution' : relations.Solution N} (h' : solution'.IsPresentation)

/--
Definition of `uniq` / `uniq` 的定义

English:
definition uniq
  signature: : M ≃ₗ[A] N
  body: LinearEquiv.ofLinearMap
  (h.desc solution') (h'.desc solution)
    (h'.postcomp_injective (by simp))
    (h.postcomp_injective (by simp))

@[simp]

中文:
定义 uniq
  签名: : M ≃ₗ[A] N
  定义体: LinearEquiv.ofLinearMap
  (h.desc solution') (h'.desc solution)
    (h'.postcomp_injective (by simp))
    (h.postcomp_injective (by simp))

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, ofLinearMap
-/
def uniq : M ≃ₗ[A] N := LinearEquiv.ofLinearMap
  (h.desc solution') (h'.desc solution)
    (h'.postcomp_injective (by simp))
    (h.postcomp_injective (by simp))

@[simp]
/--
lemma `postcomp_uniq` / 引理 `postcomp_uniq`

English:
lemma postcomp_uniq
  statement: solution.postcomp (uniq h h').toLinearMap = solution'
  proof: by
  simp [uniq]

@[simp]

中文:
引理 postcomp_uniq
  结论: solution.postcomp (uniq h h').toLinearMap = solution'
  证明: by
  simp [uniq]

@[simp]
-/
lemma postcomp_uniq : solution.postcomp (uniq h h').toLinearMap = solution' := by
  simp [uniq]

@[simp]
/--
lemma `postcomp_uniq_symm` / 引理 `postcomp_uniq_symm`

English:
lemma postcomp_uniq_symm
  statement: solution'.postcomp (uniq h h').symm.toLinearMap = solution
  proof: by
  simp [uniq]

@[simp]

中文:
引理 postcomp_uniq_symm
  结论: solution'.postcomp (uniq h h').symm.toLinearMap = solution
  证明: by
  simp [uniq]

@[simp]
-/
lemma postcomp_uniq_symm : solution'.postcomp (uniq h h').symm.toLinearMap = solution := by
  simp [uniq]

@[simp]
/--
lemma `uniq_var` / 引理 `uniq_var`

English:
lemma uniq_var
  given: (g : relations.G)
  statement: uniq h h' (solution.var g) = solution'.var g
  proof: by
  simp [uniq]

@[simp]

中文:
引理 uniq_var
  条件: (g : relations.G)
  结论: uniq h h' (solution.var g) = solution'.var g
  证明: by
  simp [uniq]

@[simp]
-/
lemma uniq_var (g : relations.G) : uniq h h' (solution.var g) = solution'.var g := by
  simp [uniq]

@[simp]
/--
lemma `uniq_symm_var` / 引理 `uniq_symm_var`

English:
lemma uniq_symm_var
  given: (g : relations.G)
  statement: (uniq h h').symm (solution'.var g) = solution.var g
  proof: by
  simp [uniq]

中文:
引理 uniq_symm_var
  条件: (g : relations.G)
  结论: (uniq h h').symm (solution'.var g) = solution.var g
  证明: by
  simp [uniq]
-/
lemma uniq_symm_var (g : relations.G) : (uniq h h').symm (solution'.var g) = solution.var g := by
  simp [uniq]

end

/--
lemma `of_linearEquiv` / 引理 `of_linearEquiv`

English:
lemma of_linearEquiv
  given: (e : M ≃ₗ[A] N)
  statement: (solution.postcomp e.toLinearMap).IsPresentation where
  proof: by
    have : (solution.postcomp e.toLinearMap).fromQuotient =
      e.toLinearMap.comp (solution.fromQuotient) := by aesop
    rw [this]; rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_coe]
    exact Function.Bijective.comp e.bijective h.bijective

中文:
引理 of_linearEquiv
  条件: (e : M ≃ₗ[A] N)
  结论: (solution.postcomp e.toLinearMap).IsPresentation where
  证明: by
    have : (solution.postcomp e.toLinearMap).fromQuotient =
      e.toLinearMap.comp (solution.fromQuotient) := by aesop
    rw [this]; rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_coe]
    exact Function.Bijective.comp e.bijective h.bijective

Depends on / 依赖: Bijective, Function, Function.Bijective.comp, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, bijective, coe_coe, coe_comp, e.bijective, e.toLinearMap, e.toLinearMap.comp, fromQuotient, h.bijective, postcomp, solution, solution.fromQuotient, solution.postcomp, toLinearMap
-/
lemma of_linearEquiv (e : M ≃ₗ[A] N) : (solution.postcomp e.toLinearMap).IsPresentation where
  bijective := by
    have : (solution.postcomp e.toLinearMap).fromQuotient =
      e.toLinearMap.comp (solution.fromQuotient) := by aesop
    rw [this]; rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_coe]
    exact Function.Bijective.comp e.bijective h.bijective

end IsPresentation

variable (relations)

/-- Given `relations : Relations A`, this is the obvious solution to `relations`
in the quotient `relations.Quotient`. -/
@[simps!]
/--
Definition of `ofQuotient` / `ofQuotient` 的定义

English:
definition ofQuotient
  signature: : relations.Solution relations.Quotient
  body: ofπ relations.toQuotient (by simp)

@[simp]

中文:
定义 ofQuotient
  签名: : relations.Solution relations.Quotient
  定义体: ofπ relations.toQuotient (by simp)

@[simp]

Depends on / 依赖: relations, relations.toQuotient, toQuotient
-/
def ofQuotient : relations.Solution relations.Quotient :=
  ofπ relations.toQuotient (by simp)

@[simp]
/--
lemma `ofQuotient_π` / 引理 `ofQuotient_π`

English:
lemma ofQuotient_π
  statement: (ofQuotient relations).π = Submodule.mkQ _
  proof: ofπ_π _ _

@[simp]

中文:
引理 ofQuotient_π
  结论: (ofQuotient relations).π = Submodule.mkQ _
  证明: ofπ_π _ _

@[simp]
-/
lemma ofQuotient_π : (ofQuotient relations).π = Submodule.mkQ _ := ofπ_π _ _

@[simp]
/--
lemma `ofQuotient_fromQuotient` / 引理 `ofQuotient_fromQuotient`

English:
lemma ofQuotient_fromQuotient
  statement: (ofQuotient relations).fromQuotient = .id
  proof: by aesop

中文:
引理 ofQuotient_fromQuotient
  结论: (ofQuotient relations).fromQuotient = .id
  证明: by aesop
-/
lemma ofQuotient_fromQuotient : (ofQuotient relations).fromQuotient = .id := by aesop

/--
lemma `ofQuotient_isPresentation` / 引理 `ofQuotient_isPresentation`

English:
lemma ofQuotient_isPresentation
  statement: (ofQuotient relations).IsPresentation where
  proof: by
    simpa only [ofQuotient_fromQuotient, LinearMap.id_coe] using Function.bijective_id

中文:
引理 ofQuotient_isPresentation
  结论: (ofQuotient relations).IsPresentation where
  证明: by
    simpa only [ofQuotient_fromQuotient, LinearMap.id_coe] using Function.bijective_id

Depends on / 依赖: Function, Function.bijective_id, LinearMap, LinearMap.id_coe, bijective_id, id_coe, ofQuotient_fromQuotient
-/
lemma ofQuotient_isPresentation : (ofQuotient relations).IsPresentation where
  bijective := by
    simpa only [ofQuotient_fromQuotient, LinearMap.id_coe] using Function.bijective_id

variable {relations}

/--
Definition of `IsPresentationCore` / `IsPresentationCore` 的定义

English:
structure IsPresentationCore
  parameters: (solution : relations.Solution M)
  axioms and operations (3):
    - desc({N : Type w'} [AddCommGroup N] [Module A N] (s : relations.Solution N)) : M ->ₗ[A] N
    - postcomp_desc({N : Type w'} [AddCommGroup N] [Module A N] (s : relations.Solution N)) : solution.postcomp (desc s) = s
    - postcomp_injective({N : Type w'} [AddCommGroup N] [Module A N] {f f' : M ->ₗ[A] N} (h : solution.postcomp f = solution.postcomp f')) : f = f'

中文:
结构 IsPresentationCore
  参数: (solution : relations.Solution M)
  公理与运算 (3 个):
    - desc({N : Type w'} [AddCommGroup N] [Module A N] (s : relations.Solution N)) : M ->ₗ[A] N
    - postcomp_desc({N : Type w'} [AddCommGroup N] [Module A N] (s : relations.Solution N)) : solution.postcomp (desc s) = s
    - postcomp_injective({N : Type w'} [AddCommGroup N] [Module A N] {f f' : M ->ₗ[A] N} (h : solution.postcomp f = solution.postcomp f')) : f = f'
-/
structure IsPresentationCore (solution : relations.Solution M) where
  /-- any solution in a module `N : Type w'` is obtained in a unique way
  by postcomposing `solution : relations.Solution M` by a linear map `M →ₗ[A] N`. -/
  desc {N : Type w'} [AddCommGroup N] [Module A N] (s : relations.Solution N) : M ->ₗ[A] N
  postcomp_desc {N : Type w'} [AddCommGroup N] [Module A N] (s : relations.Solution N) :
    solution.postcomp (desc s) = s
  postcomp_injective {N : Type w'} [AddCommGroup N] [Module A N] {f f' : M ->ₗ[A] N}
      (h : solution.postcomp f = solution.postcomp f') : f = f'

namespace IsPresentationCore

variable {solution : relations.Solution M}

@[simp]
/--
lemma `desc_var` / 引理 `desc_var`

English:
lemma desc_var
  statement: (h : IsPresentationCore.{w'} solution)
  proof: congr_var (h.postcomp_desc s) g

中文:
引理 desc_var
  结论: (h : IsPresentationCore.{w'} solution)
  证明: congr_var (h.postcomp_desc s) g

Depends on / 依赖: congr_var, h.postcomp_desc, postcomp_desc
-/
lemma desc_var (h : IsPresentationCore.{w'} solution)
    {N : Type w'} [AddCommGroup N] [Module A N] (s : relations.Solution N) (g : relations.G) :
    h.desc s (solution.var g) = s.var g :=
  congr_var (h.postcomp_desc s) g

/--
Definition of `down` / `down` 的定义

English:
definition down
  signature: (h : IsPresentationCore.{max w' w''} solution)
  body: ULift.moduleEquiv.toLinearMap.comp
    (h.desc (s.postcomp ULift.moduleEquiv.symm.toLinearMap))
  postcomp_desc s := by
    simpa using! congr_postcomp
      (h.postcomp_desc (s.postcomp ULift.moduleEquiv.symm.toLinearMap))
        ULift.moduleEquiv.toLinearMap
  postcomp_injective {N _ _ f f'} h' :

中文:
定义 down
  签名: (h : IsPresentationCore.{max w' w''} solution)
  定义体: ULift.moduleEquiv.toLinearMap.comp
    (h.desc (s.postcomp ULift.moduleEquiv.symm.toLinearMap))
  postcomp_desc s := by
    simpa using! congr_postcomp
      (h.postcomp_desc (s.postcomp ULift.moduleEquiv.symm.toLinearMap))
        ULift.moduleEquiv.toLinearMap
  postcomp_injective {N _ _ f f'} h' :

Depends on / 依赖: ULift.moduleEquiv.toLinearMap.comp, moduleEquiv, toLinearMap
-/
def down (h : IsPresentationCore.{max w' w''} solution) :
    IsPresentationCore.{w''} solution where
  desc s := ULift.moduleEquiv.toLinearMap.comp
    (h.desc (s.postcomp ULift.moduleEquiv.symm.toLinearMap))
  postcomp_desc s := by
    simpa using! congr_postcomp
      (h.postcomp_desc (s.postcomp ULift.moduleEquiv.symm.toLinearMap))
        ULift.moduleEquiv.toLinearMap
  postcomp_injective {N _ _ f f'} h' := by
    ext x
    have := congr_postcomp h' ULift.moduleEquiv.{_, _, w'}.symm.toLinearMap
    simp only [← postcomp_comp] at this
    simpa using! DFunLike.congr_fun (h.postcomp_injective this) x

/--
lemma `isPresentation` / 引理 `isPresentation`

English:
lemma isPresentation
  statement: {solution : relations.Solution M}
  proof: by
    let e : relations.Quotient ≃ₗ[A] M :=
      LinearEquiv.ofLinearMap solution.fromQuotient
      ((down.{v} h).desc (ofQuotient relations))
      ((down.{max u w₀} h).postcomp_injective (by aesop)) (by aesop)
    exact e.bijective

中文:
引理 isPresentation
  结论: {solution : relations.Solution M}
  证明: by
    let e : relations.Quotient ≃ₗ[A] M :=
      LinearEquiv.ofLinearMap solution.fromQuotient
      ((down.{v} h).desc (ofQuotient relations))
      ((down.{max u w₀} h).postcomp_injective (by aesop)) (by aesop)
    exact e.bijective

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, Quotient, bijective, e.bijective, fromQuotient, ofLinearMap, ofQuotient, postcomp_injective, relations, relations.Quotient, solution, solution.fromQuotient
-/
lemma isPresentation {solution : relations.Solution M}
    (h : IsPresentationCore.{max u v w₀} solution) :
    solution.IsPresentation where
  bijective := by
    let e : relations.Quotient ≃ₗ[A] M :=
      LinearEquiv.ofLinearMap solution.fromQuotient
      ((down.{v} h).desc (ofQuotient relations))
      ((down.{max u w₀} h).postcomp_injective (by aesop)) (by aesop)
    exact e.bijective

end IsPresentationCore

variable (solution : relations.Solution M)

/--
lemma `isPresentation_iff` / 引理 `isPresentation_iff`

English:
lemma isPresentation_iff
  proof: by
  rw [← injective_fromQuotient_iff_ker_π_eq_span]; rw [← surjective_π_iff_span_eq_top]; rw [← surjective_fromQuotient_iff_surjective_π]
  exact ⟨fun h => ⟨h.bijective.2, h.bijective.1⟩, fun h => ⟨⟨h.2, h.1⟩⟩⟩

中文:
引理 isPresentation_iff
  证明: by
  rw [← injective_fromQuotient_iff_ker_π_eq_span]; rw [← surjective_π_iff_span_eq_top]; rw [← surjective_fromQuotient_iff_surjective_π]
  exact ⟨fun h => ⟨h.bijective.2, h.bijective.1⟩, fun h => ⟨⟨h.2, h.1⟩⟩⟩

Depends on / 依赖: bijective, h.bijective
-/
lemma isPresentation_iff :
    solution.IsPresentation ↔
      Submodule.span A (Set.range solution.var) = ⊤ ∧
      LinearMap.ker solution.π = Submodule.span A (Set.range relations.relation) := by
  rw [← injective_fromQuotient_iff_ker_π_eq_span]; rw [← surjective_π_iff_span_eq_top]; rw [← surjective_fromQuotient_iff_surjective_π]
  exact ⟨fun h => ⟨h.bijective.2, h.bijective.1⟩, fun h => ⟨⟨h.2, h.1⟩⟩⟩

/--
lemma `isPresentation_mk` / 引理 `isPresentation_mk`

English:
lemma isPresentation_mk
  proof: by
  rw [isPresentation_iff]; constructor <;> assumption

中文:
引理 isPresentation_mk
  证明: by
  rw [isPresentation_iff]; constructor <;> assumption

Depends on / 依赖: isPresentation_iff
-/
lemma isPresentation_mk
    (h₁ : Submodule.span A (Set.range solution.var) = ⊤)
    (h₂ : LinearMap.ker solution.π = Submodule.span A (Set.range relations.relation)) :
    solution.IsPresentation := by
  rw [isPresentation_iff]; constructor <;> assumption

end Solution

end Relations

variable (M : Type v) [AddCommGroup M] [Module A M]

set_option linter.checkUnivs false in
/--
Definition of `Presentation` / `Presentation` 的定义

English:
structure Presentation
  parameters: extends Relations.{w₀, w₁} A,
  extends: Relations.{w₀, w₁} A, 
  (no additional axioms)

中文:
结构 Presentation
  参数: extends Relations.{w₀, w₁} A,
  继承: Relations.{w₀, w₁} A, 
  (无附加公理)
-/
structure Presentation extends Relations.{w₀, w₁} A,
  toRelations.Solution M, toSolution.IsPresentation where

variable {A M}

/-- Constructor for `Module.Presentation`. -/
@[simps toRelations toSolution]
/--
Definition of `Presentation.ofIsPresentation` / `Presentation.ofIsPresentation` 的定义

English:
definition Presentation.ofIsPresentation
  signature: {relations : Relations.{w₀, w₁} A}
  body: relations
  toSolution := solution
  toIsPresentation := h

中文:
定义 Presentation.ofIsPresentation
  签名: {relations : Relations.{w₀, w₁} A}
  定义体: relations
  toSolution := solution
  toIsPresentation := h

Depends on / 依赖: relations
-/
def Presentation.ofIsPresentation {relations : Relations.{w₀, w₁} A}
    {solution : relations.Solution M} (h : solution.IsPresentation) :
    Presentation.{w₀, w₁} A M where
  __ := relations
  toSolution := solution
  toIsPresentation := h

/-- The presentation of an `A`-module `N` that is deduced from a presentation of
a module `M` and a linear equivalence `e : M ≃ₗ[A] N`. -/
@[simps! toRelations toSolution]
/--
Definition of `Presentation.ofLinearEquiv` / `Presentation.ofLinearEquiv` 的定义

English:
definition Presentation.ofLinearEquiv
  signature: (pres : Presentation.{w₀, w₁} A M)
  body: ofIsPresentation (pres.toIsPresentation.of_linearEquiv e)

中文:
定义 Presentation.ofLinearEquiv
  签名: (pres : Presentation.{w₀, w₁} A M)
  定义体: ofIsPresentation (pres.toIsPresentation.of_linearEquiv e)

Depends on / 依赖: ofIsPresentation, of_linearEquiv, pres.toIsPresentation.of_linearEquiv, toIsPresentation
-/
def Presentation.ofLinearEquiv (pres : Presentation.{w₀, w₁} A M)
    {N : Type v'} [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) :
    Presentation A N :=
  ofIsPresentation (pres.toIsPresentation.of_linearEquiv e)

end Module
