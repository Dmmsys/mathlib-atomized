/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Data.Set.Constructions

/-!

# Compacta and Compact Hausdorff Spaces

Recall that, given a monad `M` on `Type*`, an *algebra* for `M` consists of the following data:
- A type `X : Type*`
- A "structure" map `M X → X`.

This data must also satisfy a distributivity and unit axiom, and algebras for `M` form a category
in an evident way.

See the file `Mathlib/CategoryTheory/Monad/Algebra.lean` for a general version, as well as the
following link.
https://ncatlab.org/nlab/show/monad

This file proves the equivalence between the category of *compact Hausdorff topological spaces*
and the category of algebras for the *ultrafilter monad*.

## Notation:

Here are the main objects introduced in this file.
- `Compactum` is the type of compacta, which we define as algebras for the ultrafilter monad.
- `compactumToCompHaus` is the functor `Compactum ⥤ CompHaus`. Here `CompHaus` is the usual
  category of compact Hausdorff spaces.
- `compactumToCompHaus.isEquivalence` is a term of type `IsEquivalence compactumToCompHaus`.

The proof of this equivalence is a bit technical. But the idea is quite simply that the structure
map `Ultrafilter X → X` for an algebra `X` of the ultrafilter monad should be considered as the map
sending an ultrafilter to its limit in `X`. The topology on `X` is then defined by mimicking the
characterization of open sets in terms of ultrafilters.

Any `X : Compactum` is endowed with a coercion to `Type*`, as well as the following instances:
- `TopologicalSpace X`.
- `CompactSpace X`.
- `T2Space X`.

Any morphism `f : X ⟶ Y` of is endowed with a coercion to a function `X → Y`, which is shown to
be continuous in `continuous_of_hom`.

The function `Compactum.ofTopologicalSpace` can be used to construct a `Compactum` from a
topological space which satisfies `CompactSpace` and `T2Space`.

We also add wrappers around structures which already exist. Here are the main ones, all in the
`Compactum` namespace:

- `forget : Compactum ⥤ Type*` is the forgetful functor, which induces a `ConcreteCategory`
  instance for `Compactum`.
- `free : Type* ⥤ Compactum` is the left adjoint to `forget`, and the adjunction is in `adj`.
- `str : Ultrafilter X → X` is the structure map for `X : Compactum`.
  The notation `X.str` is preferred.
- `join : Ultrafilter (Ultrafilter X) → Ultrafilter X` is the monadic join for `X : Compactum`.
  Again, the notation `X.join` is preferred.
- `incl : X → Ultrafilter X` is the unit for `X : Compactum`. The notation `X.incl` is preferred.

## References

- E. Manes, Algebraic Theories, Graduate Texts in Mathematics 26, Springer-Verlag, 1976.
- https://ncatlab.org/nlab/show/ultrafilter

-/

@[expose] public section

universe u

open CategoryTheory Filter Ultrafilter TopologicalSpace CategoryTheory.Limits FiniteInter
open scoped Topology

local notation "β" => ofTypeMonad Ultrafilter

/--
Definition of `Compactum` / `Compactum` 的定义

English:
definition Compactum
  body: Monad.Algebra β deriving Category, Inhabited

中文:
定义 Compactum
  定义体: Monad.Algebra β deriving Category, Inhabited

Depends on / 依赖: Algebra, Category, Inhabited, Monad.Algebra, deriving
-/
def Compactum :=
  Monad.Algebra β deriving Category, Inhabited

namespace Compactum

/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Compactum ⥤ Type _
  body: Monad.forget _

中文:
定义 forget
  签名: : Compactum ⥤ 类型 _
  定义体: Monad.forget _

Depends on / 依赖: Monad.forget, forget
-/
def forget : Compactum ⥤ Type _ :=
  Monad.forget _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: forget.Faithful
  body: show (Monad.forget _).Faithful from inferInstance

中文:
实例 :
  签名: forget.忠实
  定义体: show (Monad.forget _).Faithful from inferInstance

Depends on / 依赖: Faithful, Monad.forget, forget
-/
instance : forget.Faithful :=
  show (Monad.forget _).Faithful from inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesLimits forget
  body: show CreatesLimits Monad.forget _ from inferInstance

中文:
实例 :
  签名: CreatesLimits forget
  定义体: show CreatesLimits Monad.forget _ from inferInstance

Depends on / 依赖: CreatesLimits, Monad.forget, forget
-/
noncomputable instance : CreatesLimits forget :=
show CreatesLimits Monad.forget _ from inferInstance

/--
Definition of `free` / `free` 的定义

English:
definition free
  signature: : Type _ ⥤ Compactum
  body: Monad.free _

中文:
定义 free
  签名: : 类型 _ ⥤ Compactum
  定义体: Monad.free _

Depends on / 依赖: Monad.free
-/
def free : Type _ ⥤ Compactum :=
  Monad.free _

/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : free ⊣ forget
  body: Monad.adj _

中文:
定义 adj
  签名: : free ⊣ forget
  定义体: Monad.adj _

Depends on / 依赖: Monad.adj
-/
def adj : free ⊣ forget :=
  Monad.adj _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort Compactum Type*
  body: ⟨fun X => X.A⟩

中文:
实例 :
  签名: CoeSort Compactum 类型
  定义体: ⟨fun X => X.A⟩
-/
instance : CoeSort Compactum Type* :=
  ⟨fun X => X.A⟩

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y : Compactum} : FunLike (X ⟶ Y) X Y where
  coe f := f.f
  coe_injective _ _ h := (Monad.forget_faithful β).map_injective (by aesop)

-- Basic instances
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory Compactum (· ⟶ ·)
  body: f
  ofHom f := f

中文:
实例 :
  签名: 余ncrete范畴 Compactum (· ⟶ ·)
  定义体: f
  ofHom f := f
-/
instance : ConcreteCategory Compactum (· ⟶ ·) where
  hom f := f
  ofHom f := f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimits Compactum
  body: hasLimits_of_hasLimits_createsLimits forget

中文:
实例 :
  签名: 有极限 Compactum
  定义体: hasLimits_of_hasLimits_createsLimits forget

Depends on / 依赖: forget, hasLimits_of_hasLimits_createsLimits
-/
instance : HasLimits Compactum :=
  hasLimits_of_hasLimits_createsLimits forget

/--
Definition of `str` / `str` 的定义

English:
definition str
  signature: (X : Compactum)
  body: X.a

中文:
定义 str
  签名: (X : Compactum)
  定义体: X.a
-/
def str (X : Compactum) : Ultrafilter X -> X :=
  X.a

/--
Definition of `join` / `join` 的定义

English:
definition join
  signature: (X : Compactum)
  body: (β).μ.app _

中文:
定义 join
  签名: (X : Compactum)
  定义体: (β).μ.app _
-/
def join (X : Compactum) : Ultrafilter (Ultrafilter X) -> Ultrafilter X :=
  (β).μ.app _

/--
Definition of `incl` / `incl` 的定义

English:
definition incl
  signature: (X : Compactum)
  body: (β).η.app _

中文:
定义 incl
  签名: (X : Compactum)
  定义体: (β).η.app _
-/
def incl (X : Compactum) : X -> Ultrafilter X :=
  (β).η.app _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `str_incl` / 定理 `str_incl`

English:
theorem str_incl
  given: (X : Compactum) (x : X)
  statement: X.str (X.incl x) = x
  proof: by
  change ((β).η.app _ ≫ X.a) _ = _
  rw [Monad.Algebra.unit]
  rfl

#adaptation_note

中文:
定理 str_incl
  条件: (X : Compactum) (x : X)
  结论: X.str (X.incl x) = x
  证明: by
  change ((β).η.app _ ≫ X.a) _ = _
  rw [Monad.Algebra.unit]
  rfl

#adaptation_note

Depends on / 依赖: Algebra, Monad.Algebra.unit
-/
theorem str_incl (X : Compactum) (x : X) : X.str (X.incl x) = x := by
  change ((β).η.app _ ≫ X.a) _ = _
  rw [Monad.Algebra.unit]
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `str_hom_commute` / 定理 `str_hom_commute`

English:
theorem str_hom_commute
  given: (X Y : Compactum) (f : X ⟶ Y) (xs : Ultrafilter X)
  proof: by
  change (X.a ≫ f.f) _ = _
  rw [← f.h]
  rfl

中文:
定理 str_hom_commute
  条件: (X Y : Compactum) (f : X ⟶ Y) (xs : Ultrafilter X)
  证明: by
  change (X.a ≫ f.f) _ = _
  rw [← f.h]
  rfl
-/
theorem str_hom_commute (X Y : Compactum) (f : X ⟶ Y) (xs : Ultrafilter X) :
    f (X.str xs) = Y.str (map f xs) := by
  change (X.a ≫ f.f) _ = _
  rw [← f.h]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `join_distrib` / 定理 `join_distrib`

English:
theorem join_distrib
  given: (X : Compactum) (uux : Ultrafilter (Ultrafilter X))
  proof: by
  change ((β).μ.app _ ≫ X.a) _ = _
  rw [Monad.Algebra.assoc]
  rfl

中文:
定理 join_distrib
  条件: (X : Compactum) (uux : Ultrafilter (Ultrafilter X))
  证明: by
  change ((β).μ.app _ ≫ X.a) _ = _
  rw [Monad.Algebra.assoc]
  rfl

Depends on / 依赖: Algebra, Monad.Algebra.assoc
-/
theorem join_distrib (X : Compactum) (uux : Ultrafilter (Ultrafilter X)) :
    X.str (X.join uux) = X.str (map X.str uux) := by
  change ((β).μ.app _ ≫ X.a) _ = _
  rw [Monad.Algebra.assoc]
  rfl

instance {X : Compactum} : TopologicalSpace X where
  IsOpen U := forall F : Ultrafilter X, X.str F in U -> U in F
  isOpen_univ _ _ := Filter.univ_sets _
  isOpen_inter _ _ h3 h4 _ h6 := Filter.inter_sets _ (h3 _ h6.1) (h4 _ h6.2)
  isOpen_sUnion := fun _ h1 _ ⟨T, hT, h2⟩ =>
    mem_of_superset (h1 T hT _ h2) (Set.subset_sUnion_of_mem hT)

/--
theorem `isClosed_iff` / 定理 `isClosed_iff`

English:
theorem isClosed_iff
  given: {X : Compactum} (S : Set X)
  proof: by
  rw [← isOpen_compl_iff]
  constructor
  · intro cond F h
    by_contra c
    specialize cond F c
    rw [compl_mem_iff_notMem] at cond
    contradiction
  · intro h1 F h2
    specialize h1 F
    rcases F.mem_or_compl_mem S with h | h
    exacts [absurd (h1 h) h2, h]

中文:
定理 isClosed_iff
  条件: {X : Compactum} (S : 集合 X)
  证明: by
  rw [← isOpen_compl_iff]
  constructor
  · intro cond F h
    by_contra c
    specialize cond F c
    rw [compl_mem_iff_notMem] at cond
    contradiction
  · intro h1 F h2
    specialize h1 F
    rcases F.mem_or_compl_mem S with h | h
    exacts [absurd (h1 h) h2, h]

Depends on / 依赖: F.mem_or_compl_mem, absurd, compl_mem_iff_notMem, exacts, isOpen_compl_iff, mem_or_compl_mem, specialize
-/
theorem isClosed_iff {X : Compactum} (S : Set X) :
    IsClosed S ↔ forall F : Ultrafilter X, S in F -> X.str F in S := by
  rw [← isOpen_compl_iff]
  constructor
  · intro cond F h
    by_contra c
    specialize cond F c
    rw [compl_mem_iff_notMem] at cond
    contradiction
  · intro h1 F h2
    specialize h1 F
    rcases F.mem_or_compl_mem S with h | h
    exacts [absurd (h1 h) h2, h]

instance {X : Compactum} : CompactSpace X := by
  constructor
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro F _
  refine ⟨X.str F, by tauto, ?_⟩
  rw [le_nhds_iff]
  intro S h1 h2
  exact h2 F h1

/--
Definition of `basic` / `basic` 的定义

English:
definition basic
  signature: {X : Compactum} (A : Set X)
  body: { F | A in F }

中文:
定义 basic
  签名: {X : Compactum} (A : 集合 X)
  定义体: { F | A in F }
-/
private def basic {X : Compactum} (A : Set X) : Set (Ultrafilter X) :=
  { F | A in F }

set_option backward.privateInPublic true in
/--
Definition of `cl` / `cl` 的定义

English:
definition cl
  signature: {X : Compactum} (A : Set X)
  body: X.str '' basic A

中文:
定义 cl
  签名: {X : Compactum} (A : 集合 X)
  定义体: X.str '' basic A
-/
private def cl {X : Compactum} (A : Set X) : Set X :=
  X.str '' basic A

/--
theorem `basic_inter` / 定理 `basic_inter`

English:
theorem basic_inter
  given: {X : Compactum} (A B : Set X)
  statement: basic (A inter B) = basic A inter basic B
  proof: by
  ext G
  constructor
  · intro hG
    constructor <;> filter_upwards [hG] with _
    exacts [And.left, And.right]
  · rintro ⟨h1, h2⟩
    exact inter_mem h1 h2

中文:
定理 basic_inter
  条件: {X : Compactum} (A B : 集合 X)
  结论: basic (A inter B) = basic A inter basic B
  证明: by
  ext G
  constructor
  · intro hG
    constructor <;> filter_upwards [hG] with _
    exacts [And.left, And.right]
  · rintro ⟨h1, h2⟩
    exact inter_mem h1 h2
-/
private theorem basic_inter {X : Compactum} (A B : Set X) : basic (A inter B) = basic A inter basic B := by
  ext G
  constructor
  · intro hG
    constructor <;> filter_upwards [hG] with _
    exacts [And.left, And.right]
  · rintro ⟨h1, h2⟩
    exact inter_mem h1 h2

/--
theorem `subset_cl` / 定理 `subset_cl`

English:
theorem subset_cl
  given: {X : Compactum} (A : Set X)
  statement: A subseteq cl A
  proof: fun a ha =>
  ⟨X.incl a, ha, by simp⟩

中文:
定理 subset_cl
  条件: {X : Compactum} (A : 集合 X)
  结论: A subseteq cl A
  证明: fun a ha =>
  ⟨X.incl a, ha, by simp⟩
-/
private theorem subset_cl {X : Compactum} (A : Set X) : A subseteq cl A := fun a ha =>
  ⟨X.incl a, ha, by simp⟩

/--
theorem `cl_cl` / 定理 `cl_cl`

English:
theorem cl_cl
  given: {X : Compactum} (A : Set X)
  statement: cl (cl A) subseteq cl A
  proof: by
  rintro _ ⟨F, hF, rfl⟩
  -- Notation to be used in this proof.
  let fsu := Finset (Set (Ultrafilter X))
  let ssu := Set (Set (Ultrafilter X))
  let ι : fsu -> ssu := fun x => ↑x
  let C0 : ssu := { Z | exists B in F, X.str ⁻¹' B = Z }
  let AA := { G : Ultrafilter X | A in G }
  let C1 := insert AA C0
  let C2 := finiteInterClosure C1
  -- C0 is closed under intersections.
  have claim1 : forall (B) (_ : B in C0) (C) (_ : C in C0), B inter C in C0 := by
    rintro B ⟨Q, hQ, rfl⟩ C ⟨R, hR, rfl⟩
    use Q inter R
    simp only [and_true, Set.preimage_inter]
    exact inter_sets _ hQ hR
  -- All sets in C0 are nonempty.
  have claim2 : forall B in C0, Set.Nonempty B := by
    rintro B ⟨Q, hQ, rfl⟩
    obtain ⟨q⟩ := Filter.nonempty_of_mem hQ
    use X.incl q
    simpa
  -- The intersection of AA with every set in C0 is nonempty.
  have claim3 : forall B in C0, (AA inter B).Nonempty := by
    rintro B ⟨Q, hQ, rfl⟩
    have : (Q inter cl A).Nonempty := Filter.nonempty_of_mem (inter_mem hQ hF)
    rcases this with ⟨q, hq1, P, hq2, hq3⟩
    refine ⟨P, hq2, ?_⟩
    rw [← hq3] at hq1
    simpa
  -- Suffices to show that the intersection of any finite subcollection of C1 is nonempty.
  suffices forall T : fsu, ι T subseteq C1 -> (⋂₀ ι T).Nonempty by
    obtain ⟨G, h1⟩ := exists_ultrafilter_of_finite_inter_nonempty _ this
    use X.join G
    have : G.map X.str = F := Ultrafilter.coe_le_coe.1 fun S hS => h1 (Or.inr ⟨S, hS, rfl⟩)
    rw [join_distrib]; rw [this]
    exact ⟨h1 (Or.inl rfl), rfl⟩
  -- C2 is closed under finite intersections (by construction!).
  have claim4 := finiteInterClosure_finiteInter C1
  -- C0 is closed under finite intersections by claim1.
  have claim5 : FiniteInter C0 := ⟨⟨_, univ_mem, Set.preimage_univ⟩, claim1⟩
  -- Every element of C2 is nonempty.
  have claim6 : forall P in C2, (P : Set (Ultrafilter X)).Nonempty := by
    suffices forall P in C2, P in C0 ∨ exists Q in C0, P = AA inter Q by
      intro P hP
      rcases this P hP with h | h
      · exact claim2 _ h
      · rcases h with ⟨Q, hQ, rfl⟩
        exact claim3 _ hQ
    intro P hP
    exact claim5.finiteInterClosure_insert _ hP
  intro T hT
  -- Suffices to show that the intersection of the T's is contained in C2.
  suffices ⋂₀ ι T in C2 by exact claim6 _ this
  -- Finish
  apply claim4.finiteInter_mem T
  intro t ht
  exact finiteInterClosure.basic (@hT t ht)

中文:
定理 cl_cl
  条件: {X : Compactum} (A : 集合 X)
  结论: cl (cl A) subseteq cl A
  证明: by
  rintro _ ⟨F, hF, rfl⟩
  -- Notation to be used in this proof.
  let fsu := Finset (Set (Ultrafilter X))
  let ssu := Set (Set (Ultrafilter X))
  let ι : fsu -> ssu := fun x => ↑x
  let C0 : ssu := { Z | exists B in F, X.str ⁻¹' B = Z }
  let AA := { G : Ultrafilter X | A in G }
  let C1 := insert AA C0
  let C2 := finiteInterClosure C1
  -- C0 is closed under intersections.
  have claim1 : forall (B) (_ : B in C0) (C) (_ : C in C0), B inter C in C0 := by
    rintro B ⟨Q, hQ, rfl⟩ C ⟨R, hR, rfl⟩
    use Q inter R
    simp only [and_true, Set.preimage_inter]
    exact inter_sets _ hQ hR
  -- All sets in C0 are nonempty.
  have claim2 : forall B in C0, Set.Nonempty B := by
    rintro B ⟨Q, hQ, rfl⟩
    obtain ⟨q⟩ := Filter.nonempty_of_mem hQ
    use X.incl q
    simpa
  -- The intersection of AA with every set in C0 is nonempty.
  have claim3 : forall B in C0, (AA inter B).Nonempty := by
    rintro B ⟨Q, hQ, rfl⟩
    have : (Q inter cl A).Nonempty := Filter.nonempty_of_mem (inter_mem hQ hF)
    rcases this with ⟨q, hq1, P, hq2, hq3⟩
    refine ⟨P, hq2, ?_⟩
    rw [← hq3] at hq1
    simpa
  -- Suffices to show that the intersection of any finite subcollection of C1 is nonempty.
  suffices forall T : fsu, ι T subseteq C1 -> (⋂₀ ι T).Nonempty by
    obtain ⟨G, h1⟩ := exists_ultrafilter_of_finite_inter_nonempty _ this
    use X.join G
    have : G.map X.str = F := Ultrafilter.coe_le_coe.1 fun S hS => h1 (Or.inr ⟨S, hS, rfl⟩)
    rw [join_distrib]; rw [this]
    exact ⟨h1 (Or.inl rfl), rfl⟩
  -- C2 is closed under finite intersections (by construction!).
  have claim4 := finiteInterClosure_finiteInter C1
  -- C0 is closed under finite intersections by claim1.
  have claim5 : FiniteInter C0 := ⟨⟨_, univ_mem, Set.preimage_univ⟩, claim1⟩
  -- Every element of C2 is nonempty.
  have claim6 : forall P in C2, (P : Set (Ultrafilter X)).Nonempty := by
    suffices forall P in C2, P in C0 ∨ exists Q in C0, P = AA inter Q by
      intro P hP
      rcases this P hP with h | h
      · exact claim2 _ h
      · rcases h with ⟨Q, hQ, rfl⟩
        exact claim3 _ hQ
    intro P hP
    exact claim5.finiteInterClosure_insert _ hP
  intro T hT
  -- Suffices to show that the intersection of the T's is contained in C2.
  suffices ⋂₀ ι T in C2 by exact claim6 _ this
  -- Finish
  apply claim4.finiteInter_mem T
  intro t ht
  exact finiteInterClosure.basic (@hT t ht)
-/
private theorem cl_cl {X : Compactum} (A : Set X) : cl (cl A) subseteq cl A := by
  rintro _ ⟨F, hF, rfl⟩
  -- Notation to be used in this proof.
  let fsu := Finset (Set (Ultrafilter X))
  let ssu := Set (Set (Ultrafilter X))
  let ι : fsu -> ssu := fun x => ↑x
  let C0 : ssu := { Z | exists B in F, X.str ⁻¹' B = Z }
  let AA := { G : Ultrafilter X | A in G }
  let C1 := insert AA C0
  let C2 := finiteInterClosure C1
  -- C0 is closed under intersections.
  have claim1 : forall (B) (_ : B in C0) (C) (_ : C in C0), B inter C in C0 := by
    rintro B ⟨Q, hQ, rfl⟩ C ⟨R, hR, rfl⟩
    use Q inter R
    simp only [and_true, Set.preimage_inter]
    exact inter_sets _ hQ hR
  -- All sets in C0 are nonempty.
  have claim2 : forall B in C0, Set.Nonempty B := by
    rintro B ⟨Q, hQ, rfl⟩
    obtain ⟨q⟩ := Filter.nonempty_of_mem hQ
    use X.incl q
    simpa
  -- The intersection of AA with every set in C0 is nonempty.
  have claim3 : forall B in C0, (AA inter B).Nonempty := by
    rintro B ⟨Q, hQ, rfl⟩
    have : (Q inter cl A).Nonempty := Filter.nonempty_of_mem (inter_mem hQ hF)
    rcases this with ⟨q, hq1, P, hq2, hq3⟩
    refine ⟨P, hq2, ?_⟩
    rw [← hq3] at hq1
    simpa
  -- Suffices to show that the intersection of any finite subcollection of C1 is nonempty.
  suffices forall T : fsu, ι T subseteq C1 -> (⋂₀ ι T).Nonempty by
    obtain ⟨G, h1⟩ := exists_ultrafilter_of_finite_inter_nonempty _ this
    use X.join G
    have : G.map X.str = F := Ultrafilter.coe_le_coe.1 fun S hS => h1 (Or.inr ⟨S, hS, rfl⟩)
    rw [join_distrib]; rw [this]
    exact ⟨h1 (Or.inl rfl), rfl⟩
  -- C2 is closed under finite intersections (by construction!).
  have claim4 := finiteInterClosure_finiteInter C1
  -- C0 is closed under finite intersections by claim1.
  have claim5 : FiniteInter C0 := ⟨⟨_, univ_mem, Set.preimage_univ⟩, claim1⟩
  -- Every element of C2 is nonempty.
  have claim6 : forall P in C2, (P : Set (Ultrafilter X)).Nonempty := by
    suffices forall P in C2, P in C0 ∨ exists Q in C0, P = AA inter Q by
      intro P hP
      rcases this P hP with h | h
      · exact claim2 _ h
      · rcases h with ⟨Q, hQ, rfl⟩
        exact claim3 _ hQ
    intro P hP
    exact claim5.finiteInterClosure_insert _ hP
  intro T hT
  -- Suffices to show that the intersection of the T's is contained in C2.
  suffices ⋂₀ ι T in C2 by exact claim6 _ this
  -- Finish
  apply claim4.finiteInter_mem T
  intro t ht
  exact finiteInterClosure.basic (@hT t ht)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `isClosed_cl` / 定理 `isClosed_cl`

English:
theorem isClosed_cl
  given: {X : Compactum} (A : Set X)
  statement: IsClosed (cl A)
  proof: by
  rw [isClosed_iff]
  intro F hF
  exact cl_cl _ ⟨F, hF, rfl⟩

中文:
定理 isClosed_cl
  条件: {X : Compactum} (A : 集合 X)
  结论: 是闭集 (cl A)
  证明: by
  rw [isClosed_iff]
  intro F hF
  exact cl_cl _ ⟨F, hF, rfl⟩

Depends on / 依赖: cl_cl, isClosed_iff
-/
theorem isClosed_cl {X : Compactum} (A : Set X) : IsClosed (cl A) := by
  rw [isClosed_iff]
  intro F hF
  exact cl_cl _ ⟨F, hF, rfl⟩

/--
theorem `str_eq_of_le_nhds` / 定理 `str_eq_of_le_nhds`

English:
theorem str_eq_of_le_nhds
  given: {X : Compactum} (F : Ultrafilter X) (x : X)
  statement: ↑F <= 𝓝 x -> X.str F = x
  proof: by
  -- Notation to be used in this proof.
  let fsu := Finset (Set (Ultrafilter X))
  let ssu := Set (Set (Ultrafilter X))
  let ι : fsu -> ssu := fun x => ↑x
  let T0 : ssu := { S | exists A in F, S = basic A }
  let AA := X.str ⁻¹' {x}
  let T1 := insert AA T0
  let T2 := finiteInterClosure T1
  intro cond
  -- If F contains a closed set A, then x is contained in A.
  have claim1 : forall A : Set X, IsClosed A -> A in F -> x in A := by
    intro A hA h
    by_contra H
    rw [le_nhds_iff] at cond
    specialize cond Aᶜ H hA.isOpen_compl
    rw [Ultrafilter.mem_coe]; rw [Ultrafilter.compl_mem_iff_notMem] at cond
    contradiction
  -- If A ∈ F, then x ∈ cl A.
  have claim2 : forall A : Set X, A in F -> x in cl A := by
    intro A hA
    exact claim1 (cl A) (isClosed_cl A) (mem_of_superset hA (subset_cl A))
  -- T0 is closed under intersections.
  have claim3 : forall (S1) (_ : S1 in T0) (S2) (_ : S2 in T0), S1 inter S2 in T0 := by
    rintro S1 ⟨S1, hS1, rfl⟩ S2 ⟨S2, hS2, rfl⟩
    exact ⟨S1 inter S2, inter_mem hS1 hS2, by simp [basic_inter]⟩
  -- For every S ∈ T0, the intersection AA ∩ S is nonempty.
  have claim4 : forall S in T0, (AA inter S).Nonempty := by
    rintro S ⟨S, hS, rfl⟩
    rcases claim2 _ hS with ⟨G, hG, hG2⟩
    exact ⟨G, hG2, hG⟩
  -- Every element of T0 is nonempty.
  have claim5 : forall S in T0, Set.Nonempty S := by
    rintro S ⟨S, hS, rfl⟩
    exact ⟨F, hS⟩
  -- Every element of T2 is nonempty.
  have claim6 : forall S in T2, Set.Nonempty S := by
    suffices forall S in T2, S in T0 ∨ exists Q in T0, S = AA inter Q by
      intro S hS
      rcases this _ hS with h | h
      · exact claim5 S h
      · rcases h with ⟨Q, hQ, rfl⟩
        exact claim4 Q hQ
    intro S hS
    apply finiteInterClosure_insert
    · constructor
      · use Set.univ
        refine ⟨Filter.univ_sets _, ?_⟩
        ext
        refine ⟨?_, by tauto⟩
        · intro
          apply Filter.univ_sets
      · exact claim3
    · exact hS
  -- It suffices to show that the intersection of any finite subset of T1 is nonempty.
  suffices forall F : fsu, ↑F subseteq T1 -> (⋂₀ ι F).Nonempty by
    obtain ⟨G, h1⟩ := Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _ this
    have c1 : X.join G = F := Ultrafilter.coe_le_coe.1 fun P hP => h1 (Or.inr ⟨P, hP, rfl⟩)
    have c2 : G.map X.str = X.incl x := by
      refine Ultrafilter.coe_le_coe.1 fun P hP => ?_
      apply mem_of_superset (h1 (Or.inl rfl))
      rintro x ⟨rfl⟩
      exact hP
    simp [← c1, c2]
  -- Finish...
  intro T hT
  refine claim6 _ (finiteInter_mem (.finiteInterClosure_finiteInter _) _ ?_)
  intro t ht
  exact finiteInterClosure.basic (@hT t ht)

中文:
定理 str_eq_of_le_nhds
  条件: {X : Compactum} (F : Ultrafilter X) (x : X)
  结论: ↑F <= 𝓝 x -> X.str F = x
  证明: by
  -- Notation to be used in this proof.
  let fsu := Finset (Set (Ultrafilter X))
  let ssu := Set (Set (Ultrafilter X))
  let ι : fsu -> ssu := fun x => ↑x
  let T0 : ssu := { S | exists A in F, S = basic A }
  let AA := X.str ⁻¹' {x}
  let T1 := insert AA T0
  let T2 := finiteInterClosure T1
  intro cond
  -- If F contains a closed set A, then x is contained in A.
  have claim1 : forall A : Set X, IsClosed A -> A in F -> x in A := by
    intro A hA h
    by_contra H
    rw [le_nhds_iff] at cond
    specialize cond Aᶜ H hA.isOpen_compl
    rw [Ultrafilter.mem_coe]; rw [Ultrafilter.compl_mem_iff_notMem] at cond
    contradiction
  -- If A ∈ F, then x ∈ cl A.
  have claim2 : forall A : Set X, A in F -> x in cl A := by
    intro A hA
    exact claim1 (cl A) (isClosed_cl A) (mem_of_superset hA (subset_cl A))
  -- T0 is closed under intersections.
  have claim3 : forall (S1) (_ : S1 in T0) (S2) (_ : S2 in T0), S1 inter S2 in T0 := by
    rintro S1 ⟨S1, hS1, rfl⟩ S2 ⟨S2, hS2, rfl⟩
    exact ⟨S1 inter S2, inter_mem hS1 hS2, by simp [basic_inter]⟩
  -- For every S ∈ T0, the intersection AA ∩ S is nonempty.
  have claim4 : forall S in T0, (AA inter S).Nonempty := by
    rintro S ⟨S, hS, rfl⟩
    rcases claim2 _ hS with ⟨G, hG, hG2⟩
    exact ⟨G, hG2, hG⟩
  -- Every element of T0 is nonempty.
  have claim5 : forall S in T0, Set.Nonempty S := by
    rintro S ⟨S, hS, rfl⟩
    exact ⟨F, hS⟩
  -- Every element of T2 is nonempty.
  have claim6 : forall S in T2, Set.Nonempty S := by
    suffices forall S in T2, S in T0 ∨ exists Q in T0, S = AA inter Q by
      intro S hS
      rcases this _ hS with h | h
      · exact claim5 S h
      · rcases h with ⟨Q, hQ, rfl⟩
        exact claim4 Q hQ
    intro S hS
    apply finiteInterClosure_insert
    · constructor
      · use Set.univ
        refine ⟨Filter.univ_sets _, ?_⟩
        ext
        refine ⟨?_, by tauto⟩
        · intro
          apply Filter.univ_sets
      · exact claim3
    · exact hS
  -- It suffices to show that the intersection of any finite subset of T1 is nonempty.
  suffices forall F : fsu, ↑F subseteq T1 -> (⋂₀ ι F).Nonempty by
    obtain ⟨G, h1⟩ := Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _ this
    have c1 : X.join G = F := Ultrafilter.coe_le_coe.1 fun P hP => h1 (Or.inr ⟨P, hP, rfl⟩)
    have c2 : G.map X.str = X.incl x := by
      refine Ultrafilter.coe_le_coe.1 fun P hP => ?_
      apply mem_of_superset (h1 (Or.inl rfl))
      rintro x ⟨rfl⟩
      exact hP
    simp [← c1, c2]
  -- Finish...
  intro T hT
  refine claim6 _ (finiteInter_mem (.finiteInterClosure_finiteInter _) _ ?_)
  intro t ht
  exact finiteInterClosure.basic (@hT t ht)
-/
theorem str_eq_of_le_nhds {X : Compactum} (F : Ultrafilter X) (x : X) : ↑F <= 𝓝 x -> X.str F = x := by
  -- Notation to be used in this proof.
  let fsu := Finset (Set (Ultrafilter X))
  let ssu := Set (Set (Ultrafilter X))
  let ι : fsu -> ssu := fun x => ↑x
  let T0 : ssu := { S | exists A in F, S = basic A }
  let AA := X.str ⁻¹' {x}
  let T1 := insert AA T0
  let T2 := finiteInterClosure T1
  intro cond
  -- If F contains a closed set A, then x is contained in A.
  have claim1 : forall A : Set X, IsClosed A -> A in F -> x in A := by
    intro A hA h
    by_contra H
    rw [le_nhds_iff] at cond
    specialize cond Aᶜ H hA.isOpen_compl
    rw [Ultrafilter.mem_coe]; rw [Ultrafilter.compl_mem_iff_notMem] at cond
    contradiction
  -- If A ∈ F, then x ∈ cl A.
  have claim2 : forall A : Set X, A in F -> x in cl A := by
    intro A hA
    exact claim1 (cl A) (isClosed_cl A) (mem_of_superset hA (subset_cl A))
  -- T0 is closed under intersections.
  have claim3 : forall (S1) (_ : S1 in T0) (S2) (_ : S2 in T0), S1 inter S2 in T0 := by
    rintro S1 ⟨S1, hS1, rfl⟩ S2 ⟨S2, hS2, rfl⟩
    exact ⟨S1 inter S2, inter_mem hS1 hS2, by simp [basic_inter]⟩
  -- For every S ∈ T0, the intersection AA ∩ S is nonempty.
  have claim4 : forall S in T0, (AA inter S).Nonempty := by
    rintro S ⟨S, hS, rfl⟩
    rcases claim2 _ hS with ⟨G, hG, hG2⟩
    exact ⟨G, hG2, hG⟩
  -- Every element of T0 is nonempty.
  have claim5 : forall S in T0, Set.Nonempty S := by
    rintro S ⟨S, hS, rfl⟩
    exact ⟨F, hS⟩
  -- Every element of T2 is nonempty.
  have claim6 : forall S in T2, Set.Nonempty S := by
    suffices forall S in T2, S in T0 ∨ exists Q in T0, S = AA inter Q by
      intro S hS
      rcases this _ hS with h | h
      · exact claim5 S h
      · rcases h with ⟨Q, hQ, rfl⟩
        exact claim4 Q hQ
    intro S hS
    apply finiteInterClosure_insert
    · constructor
      · use Set.univ
        refine ⟨Filter.univ_sets _, ?_⟩
        ext
        refine ⟨?_, by tauto⟩
        · intro
          apply Filter.univ_sets
      · exact claim3
    · exact hS
  -- It suffices to show that the intersection of any finite subset of T1 is nonempty.
  suffices forall F : fsu, ↑F subseteq T1 -> (⋂₀ ι F).Nonempty by
    obtain ⟨G, h1⟩ := Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _ this
    have c1 : X.join G = F := Ultrafilter.coe_le_coe.1 fun P hP => h1 (Or.inr ⟨P, hP, rfl⟩)
    have c2 : G.map X.str = X.incl x := by
      refine Ultrafilter.coe_le_coe.1 fun P hP => ?_
      apply mem_of_superset (h1 (Or.inl rfl))
      rintro x ⟨rfl⟩
      exact hP
    simp [← c1, c2]
  -- Finish...
  intro T hT
  refine claim6 _ (finiteInter_mem (.finiteInterClosure_finiteInter _) _ ?_)
  intro t ht
  exact finiteInterClosure.basic (@hT t ht)

/--
theorem `le_nhds_of_str_eq` / 定理 `le_nhds_of_str_eq`

English:
theorem le_nhds_of_str_eq
  given: {X : Compactum} (F : Ultrafilter X) (x : X)
  statement: X.str F = x -> ↑F <= 𝓝 x
  proof: fun h => le_nhds_iff.mpr fun s hx hs => hs _ by rwa [h]

中文:
定理 le_nhds_of_str_eq
  条件: {X : Compactum} (F : Ultrafilter X) (x : X)
  结论: X.str F = x -> ↑F <= 𝓝 x
  证明: fun h => le_nhds_iff.mpr fun s hx hs => hs _ by rwa [h]

Depends on / 依赖: le_nhds_iff, le_nhds_iff.mpr
-/
theorem le_nhds_of_str_eq {X : Compactum} (F : Ultrafilter X) (x : X) : X.str F = x -> ↑F <= 𝓝 x :=
fun h => le_nhds_iff.mpr fun s hx hs => hs _ by rwa [h]

-- All the hard work above boils down to this `T2Space` instance.
instance {X : Compactum} : T2Space X := by
  rw [t2_iff_ultrafilter]
  intro _ _ F hx hy
  rw [← str_eq_of_le_nhds _ _ hx]; rw [← str_eq_of_le_nhds _ _ hy]

/--
theorem `lim_eq_str` / 定理 `lim_eq_str`

English:
theorem lim_eq_str
  given: {X : Compactum} (F : Ultrafilter X)
  statement: F.lim = X.str F
  proof: by
  rw [Ultrafilter.lim_eq_iff_le_nhds]; rw [le_nhds_iff]
  tauto

中文:
定理 lim_eq_str
  条件: {X : Compactum} (F : Ultrafilter X)
  结论: F.lim = X.str F
  证明: by
  rw [Ultrafilter.lim_eq_iff_le_nhds]; rw [le_nhds_iff]
  tauto

Depends on / 依赖: Ultrafilter, Ultrafilter.lim_eq_iff_le_nhds, le_nhds_iff, lim_eq_iff_le_nhds
-/
theorem lim_eq_str {X : Compactum} (F : Ultrafilter X) : F.lim = X.str F := by
  rw [Ultrafilter.lim_eq_iff_le_nhds]; rw [le_nhds_iff]
  tauto

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `cl_eq_closure` / 定理 `cl_eq_closure`

English:
theorem cl_eq_closure
  given: {X : Compactum} (A : Set X)
  statement: cl A = closure A
  proof: by
  ext
  rw [mem_closure_iff_ultrafilter]
  constructor
  · rintro ⟨F, h1, h2⟩
    exact ⟨F, h1, le_nhds_of_str_eq _ _ h2⟩
  · rintro ⟨F, h1, h2⟩
    exact ⟨F, h1, str_eq_of_le_nhds _ _ h2⟩

#adaptation_note

中文:
定理 cl_eq_closure
  条件: {X : Compactum} (A : 集合 X)
  结论: cl A = closure A
  证明: by
  ext
  rw [mem_closure_iff_ultrafilter]
  constructor
  · rintro ⟨F, h1, h2⟩
    exact ⟨F, h1, le_nhds_of_str_eq _ _ h2⟩
  · rintro ⟨F, h1, h2⟩
    exact ⟨F, h1, str_eq_of_le_nhds _ _ h2⟩

#adaptation_note

Depends on / 依赖: le_nhds_of_str_eq, mem_closure_iff_ultrafilter, str_eq_of_le_nhds
-/
theorem cl_eq_closure {X : Compactum} (A : Set X) : cl A = closure A := by
  ext
  rw [mem_closure_iff_ultrafilter]
  constructor
  · rintro ⟨F, h1, h2⟩
    exact ⟨F, h1, le_nhds_of_str_eq _ _ h2⟩
  · rintro ⟨F, h1, h2⟩
    exact ⟨F, h1, str_eq_of_le_nhds _ _ h2⟩

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `continuous_of_hom` / 定理 `continuous_of_hom`

English:
theorem continuous_of_hom
  given: {X Y : Compactum} (f : X ⟶ Y)
  statement: Continuous f
  proof: by
  rw [continuous_iff_ultrafilter]
  intro x g h
  rw [Tendsto]; rw [← coe_map]
  apply le_nhds_of_str_eq
  rw [← str_hom_commute]; rw [str_eq_of_le_nhds _ x _]
  apply h

中文:
定理 continuous_of_hom
  条件: {X Y : Compactum} (f : X ⟶ Y)
  结论: 连续 f
  证明: by
  rw [continuous_iff_ultrafilter]
  intro x g h
  rw [Tendsto]; rw [← coe_map]
  apply le_nhds_of_str_eq
  rw [← str_hom_commute]; rw [str_eq_of_le_nhds _ x _]
  apply h

Depends on / 依赖: Tendsto, coe_map, continuous_iff_ultrafilter, le_nhds_of_str_eq, str_eq_of_le_nhds, str_hom_commute
-/
theorem continuous_of_hom {X Y : Compactum} (f : X ⟶ Y) : Continuous f := by
  rw [continuous_iff_ultrafilter]
  intro x g h
  rw [Tendsto]; rw [← coe_map]
  apply le_nhds_of_str_eq
  rw [← str_hom_commute]; rw [str_eq_of_le_nhds _ x _]
  apply h

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `ofTopologicalSpace` / `ofTopologicalSpace` 的定义

English:
definition ofTopologicalSpace
  signature: (X : Type*) [TopologicalSpace X] [CompactSpace X]
  body: X
  a := ↾Ultrafilter.lim
  unit := by
    ext x
    exact lim_eq (pure_le_nhds _)
  assoc := by
    ext FF
    change Ultrafilter (Ultrafilter X) at FF
    set x := (Ultrafilter.map Ultrafilter.lim FF).lim with c1
    have c2 : forall (U : Set X) (F : Ultrafilter X), F.lim in U -> IsOpen U -> U in F := by
      intro U F h1 hU
      exact isOpen_iff_ultrafilter.mp hU _ h1 _ (Ultrafilter.le_nhds_lim _)
    have c3 : ↑(Ultrafilter.map Ultrafilter.lim FF) <= 𝓝 x := by
      rw [le_nhds_iff]
      intro U hx hU
      exact mem_coe.2 (c2 _ _ (by rwa [← c1]) hU)
    have c4 : forall U : Set X, x in U -> IsOpen U -> { G : Ultrafilter X | U in G } in FF := by
      intro U hx hU
      suffices Ultrafilter.lim ⁻¹' U in FF by
        apply mem_of_superset this
        intro P hP
        exact c2 U P hP hU
      exact @c3 U (IsOpen.mem_nhds hU hx)
    apply lim_eq
    rw [le_nhds_iff]
    exact c4

中文:
定义 ofTopologicalSpace
  签名: (X : 类型) [拓扑空间 X] [紧空间 X]
  定义体: X
  a := ↾Ultrafilter.lim
  unit := by
    ext x
    exact lim_eq (pure_le_nhds _)
  assoc := by
    ext FF
    change Ultrafilter (Ultrafilter X) at FF
    set x := (Ultrafilter.map Ultrafilter.lim FF).lim with c1
    have c2 : forall (U : Set X) (F : Ultrafilter X), F.lim in U -> IsOpen U -> U in F := by
      intro U F h1 hU
      exact isOpen_iff_ultrafilter.mp hU _ h1 _ (Ultrafilter.le_nhds_lim _)
    have c3 : ↑(Ultrafilter.map Ultrafilter.lim FF) <= 𝓝 x := by
      rw [le_nhds_iff]
      intro U hx hU
      exact mem_coe.2 (c2 _ _ (by rwa [← c1]) hU)
    have c4 : forall U : Set X, x in U -> IsOpen U -> { G : Ultrafilter X | U in G } in FF := by
      intro U hx hU
      suffices Ultrafilter.lim ⁻¹' U in FF by
        apply mem_of_superset this
        intro P hP
        exact c2 U P hP hU
      exact @c3 U (IsOpen.mem_nhds hU hx)
    apply lim_eq
    rw [le_nhds_iff]
    exact c4
-/
noncomputable def ofTopologicalSpace (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] : Compactum where
  A := X
  a := ↾Ultrafilter.lim
  unit := by
    ext x
    exact lim_eq (pure_le_nhds _)
  assoc := by
    ext FF
    change Ultrafilter (Ultrafilter X) at FF
    set x := (Ultrafilter.map Ultrafilter.lim FF).lim with c1
    have c2 : forall (U : Set X) (F : Ultrafilter X), F.lim in U -> IsOpen U -> U in F := by
      intro U F h1 hU
      exact isOpen_iff_ultrafilter.mp hU _ h1 _ (Ultrafilter.le_nhds_lim _)
    have c3 : ↑(Ultrafilter.map Ultrafilter.lim FF) <= 𝓝 x := by
      rw [le_nhds_iff]
      intro U hx hU
      exact mem_coe.2 (c2 _ _ (by rwa [← c1]) hU)
    have c4 : forall U : Set X, x in U -> IsOpen U -> { G : Ultrafilter X | U in G } in FF := by
      intro U hx hU
      suffices Ultrafilter.lim ⁻¹' U in FF by
        apply mem_of_superset this
        intro P hP
        exact c2 U P hP hU
      exact @c3 U (IsOpen.mem_nhds hU hx)
    apply lim_eq
    rw [le_nhds_iff]
    exact c4

/--
Definition of `homOfContinuous` / `homOfContinuous` 的定义

English:
definition homOfContinuous
  signature: {X Y : Compactum} (f : X -> Y) (cont : Continuous f)
  body: { f := ↾f
    h := by
      rw [continuous_iff_ultrafilter] at cont
      ext (F : Ultrafilter X)
      specialize cont (X.str F) F (le_nhds_of_str_eq F (X.str F) rfl)
      simpa using! str_eq_of_le_nhds (Ultrafilter.map f F) _ cont }

中文:
定义 homOfContinuous
  签名: {X Y : Compactum} (f : X -> Y) (cont : 连续 f)
  定义体: { f := ↾f
    h := by
      rw [continuous_iff_ultrafilter] at cont
      ext (F : Ultrafilter X)
      specialize cont (X.str F) F (le_nhds_of_str_eq F (X.str F) rfl)
      simpa using! str_eq_of_le_nhds (Ultrafilter.map f F) _ cont }

Depends on / 依赖: Ultrafilter, Ultrafilter.map, X.str, continuous_iff_ultrafilter, le_nhds_of_str_eq, specialize, str_eq_of_le_nhds
-/
def homOfContinuous {X Y : Compactum} (f : X -> Y) (cont : Continuous f) : X ⟶ Y :=
  { f := ↾f
    h := by
      rw [continuous_iff_ultrafilter] at cont
      ext (F : Ultrafilter X)
      specialize cont (X.str F) F (le_nhds_of_str_eq F (X.str F) rfl)
      simpa using! str_eq_of_le_nhds (Ultrafilter.map f F) _ cont }

end Compactum

/--
Definition of `compactumToCompHaus` / `compactumToCompHaus` 的定义

English:
definition compactumToCompHaus
  signature: : Compactum ⥤ CompHaus where
  body: { toTop := TopCat.of X, prop := trivial }
  map := fun f => CompHausLike.ofHom _
    { toFun := f
      continuous_toFun := Compactum.continuous_of_hom _ }

中文:
定义 compactumToCompHaus
  签名: : Compactum ⥤ CompHaus where
  定义体: { toTop := TopCat.of X, prop := trivial }
  map := fun f => CompHausLike.ofHom _
    { toFun := f
      continuous_toFun := Compactum.continuous_of_hom _ }

Depends on / 依赖: TopCat, TopCat.of
-/
def compactumToCompHaus : Compactum ⥤ CompHaus where
  obj X := { toTop := TopCat.of X, prop := trivial }
  map := fun f => CompHausLike.ofHom _
    { toFun := f
      continuous_toFun := Compactum.continuous_of_hom _ }

namespace compactumToCompHaus

/--
Instance `full` / 实例 `full`

English:
instance full
  signature: : compactumToCompHaus.{u}.Full where
  body: ⟨Compactum.homOfContinuous f.1 f.hom.hom.2, rfl⟩

中文:
实例 full
  签名: : compactumToCompHaus.{u}.满 where
  定义体: ⟨Compactum.homOfContinuous f.1 f.hom.hom.2, rfl⟩

Depends on / 依赖: Compactum, Compactum.homOfContinuous, f.hom.hom, homOfContinuous
-/
instance full : compactumToCompHaus.{u}.Full where
  map_surjective f := ⟨Compactum.homOfContinuous f.1 f.hom.hom.2, rfl⟩

/--
Instance `faithful` / 实例 `faithful`

English:
instance faithful
  signature: : compactumToCompHaus.Faithful where
  body: by
    intro _ _ _ _ h
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` gets confused by coercion using forget.
    apply Monad.Algebra.Hom.ext
    ext
    simpa using! ConcreteCategory.congr_hom h _

中文:
实例 faithful
  签名: : compactumToCompHaus.忠实 where
  定义体: by
    intro _ _ _ _ h
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` gets confused by coercion using forget.
    apply Monad.Algebra.Hom.ext
    ext
    simpa using! ConcreteCategory.congr_hom h _
-/
instance faithful : compactumToCompHaus.Faithful where
  -- Porting note: this used to be obviously (though it consumed a bit of memory)
  map_injective := by
    intro _ _ _ _ h
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` gets confused by coercion using forget.
    apply Monad.Algebra.Hom.ext
    ext
    simpa using! ConcreteCategory.congr_hom h _

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isoOfTopologicalSpace` / `isoOfTopologicalSpace` 的定义

English:
definition isoOfTopologicalSpace
  signature: {D : CompHaus}
  body: CompHausLike.ofHom _
    { toFun := id
      continuous_toFun :=
        continuous_def.2 fun _ h => by
          rw [isOpen_iff_ultrafilter'] at h
          exact h }
  inv := CompHausLike.ofHom _
    { toFun := id
      continuous_toFun :=
        continuous_def.2 fun _ h1 => by
          rw [isOpen_iff_ultrafilter']
          intro _ h2
          exact h1 _ h2 }

中文:
定义 isoOfTopologicalSpace
  签名: {D : CompHaus}
  定义体: CompHausLike.ofHom _
    { toFun := id
      continuous_toFun :=
        continuous_def.2 fun _ h => by
          rw [isOpen_iff_ultrafilter'] at h
          exact h }
  inv := CompHausLike.ofHom _
    { toFun := id
      continuous_toFun :=
        continuous_def.2 fun _ h1 => by
          rw [isOpen_iff_ultrafilter']
          intro _ h2
          exact h1 _ h2 }

Depends on / 依赖: CompHausLike, CompHausLike.ofHom
-/
noncomputable def isoOfTopologicalSpace {D : CompHaus} :
    compactumToCompHaus.obj (Compactum.ofTopologicalSpace D) ≅ D where
  hom := CompHausLike.ofHom _
    { toFun := id
      continuous_toFun :=
        continuous_def.2 fun _ h => by
          rw [isOpen_iff_ultrafilter'] at h
          exact h }
  inv := CompHausLike.ofHom _
    { toFun := id
      continuous_toFun :=
        continuous_def.2 fun _ h1 => by
          rw [isOpen_iff_ultrafilter']
          intro _ h2
          exact h1 _ h2 }

/--
Instance `essSurj` / 实例 `essSurj`

English:
instance essSurj
  signature: : compactumToCompHaus.EssSurj
  body: { mem_essImage := fun X => ⟨Compactum.ofTopologicalSpace X,
      ⟨isoOfTopologicalSpace⟩⟩ }

中文:
实例 essSurj
  签名: : compactumToCompHaus.本质满射
  定义体: { mem_essImage := fun X => ⟨Compactum.ofTopologicalSpace X,
      ⟨isoOfTopologicalSpace⟩⟩ }

Depends on / 依赖: Compactum, Compactum.ofTopologicalSpace, isoOfTopologicalSpace, mem_essImage, ofTopologicalSpace
-/
instance essSurj : compactumToCompHaus.EssSurj :=
  { mem_essImage := fun X => ⟨Compactum.ofTopologicalSpace X,
      ⟨isoOfTopologicalSpace⟩⟩ }

/--
Instance `isEquivalence` / 实例 `isEquivalence`

English:
instance isEquivalence
  signature: : compactumToCompHaus.IsEquivalence where

中文:
实例 isEquivalence
  签名: : compactumToCompHaus.是等价 where
-/
instance isEquivalence : compactumToCompHaus.IsEquivalence where

end compactumToCompHaus

/--
Definition of `compactumToCompHausCompForget` / `compactumToCompHausCompForget` 的定义

English:
definition compactumToCompHausCompForget
  signature: :
  body: NatIso.ofComponents fun _ => eqToIso rfl

中文:
定义 compactumToCompHausCompForget
  签名: :
  定义体: NatIso.ofComponents fun _ => eqToIso rfl

Depends on / 依赖: NatIso, NatIso.ofComponents, eqToIso, ofComponents
-/
def compactumToCompHausCompForget :
    compactumToCompHaus ⋙ CategoryTheory.forget CompHaus ≅ Compactum.forget :=
  NatIso.ofComponents fun _ => eqToIso rfl

/--
Instance `CompHaus.forgetCreatesLimits` / 实例 `CompHaus.forgetCreatesLimits`

English:
instance CompHaus.forgetCreatesLimits
  signature: : CreatesLimits (forget CompHaus)
  body: by
  let e : forget CompHaus ≅ compactumToCompHaus.inv ⋙ Compactum.forget :=
    (((forget CompHaus).leftUnitor.symm ≪≫
    Functor.isoWhiskerRight compactumToCompHaus.asEquivalence.symm.unitIso (forget CompHaus)) ≪≫
    compactumToCompHaus.inv.associator compactumToCompHaus (forget CompHaus)) ≪≫
    Functor.isoWhiskerLeft _ compactumToCompHausCompForget
  exact createsLimitsOfNatIso e.symm

中文:
实例 CompHaus.forgetCreatesLimits
  签名: : CreatesLimits (forget CompHaus)
  定义体: by
  let e : forget CompHaus ≅ compactumToCompHaus.inv ⋙ Compactum.forget :=
    (((forget CompHaus).leftUnitor.symm ≪≫
    Functor.isoWhiskerRight compactumToCompHaus.asEquivalence.symm.unitIso (forget CompHaus)) ≪≫
    compactumToCompHaus.inv.associator compactumToCompHaus (forget CompHaus)) ≪≫
    Functor.isoWhiskerLeft _ compactumToCompHausCompForget
  exact createsLimitsOfNatIso e.symm

Depends on / 依赖: CompHaus, Compactum, Compactum.forget, Functor, Functor.isoWhiskerLeft, Functor.isoWhiskerRight, asEquivalence, associator, compactumToCompHaus, compactumToCompHaus.asEquivalence.symm.unitIso, compactumToCompHaus.inv, compactumToCompHaus.inv.associator, compactumToCompHausCompForget, createsLimitsOfNatIso, e.symm, forget, isoWhiskerLeft, isoWhiskerRight, leftUnitor, leftUnitor.symm
-/
noncomputable instance CompHaus.forgetCreatesLimits : CreatesLimits (forget CompHaus) := by
  let e : forget CompHaus ≅ compactumToCompHaus.inv ⋙ Compactum.forget :=
    (((forget CompHaus).leftUnitor.symm ≪≫
    Functor.isoWhiskerRight compactumToCompHaus.asEquivalence.symm.unitIso (forget CompHaus)) ≪≫
    compactumToCompHaus.inv.associator compactumToCompHaus (forget CompHaus)) ≪≫
    Functor.isoWhiskerLeft _ compactumToCompHausCompForget
  exact createsLimitsOfNatIso e.symm

/--
Instance `Profinite.forgetCreatesLimits` / 实例 `Profinite.forgetCreatesLimits`

English:
instance Profinite.forgetCreatesLimits
  signature: : CreatesLimits (forget Profinite)
  body: by
  change CreatesLimits (profiniteToCompHaus ⋙ forget _)
  infer_instance

中文:
实例 Profinite.forgetCreatesLimits
  签名: : CreatesLimits (forget Profinite)
  定义体: by
  change CreatesLimits (profiniteToCompHaus ⋙ forget _)
  infer_instance

Depends on / 依赖: CreatesLimits, forget, infer_instance, profiniteToCompHaus
-/
noncomputable instance Profinite.forgetCreatesLimits : CreatesLimits (forget Profinite) := by
  change CreatesLimits (profiniteToCompHaus ⋙ forget _)
  infer_instance
