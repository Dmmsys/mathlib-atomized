/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Pullbacks
public import Mathlib.CategoryTheory.Sites.Sieves
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!

# Precoverages

A precoverage `K` on a category `C` is a set of presieves associated to every object `X : C`,
called "covering presieves".
There are no conditions on this set. Common extensions of a precoverage are:

- `CategoryTheory.Coverage`: A coverage is a precoverage that satisfies a pullback compatibility
  condition, saying that whenever `S` is a covering presieve on `X` and `f : Y ⟶ X` is a morphism,
  then there exists some covering sieve `T` on `Y` such that `T` factors through `S` along `f`.
- `CategoryTheory.Pretopology`: If `C` has pullbacks, a pretopology on `C` is a precoverage that
  has isomorphisms and is stable under pullback and refinement.

These two are defined in later files. For precoverages, we define stability conditions:

- `CategoryTheory.Precoverage.HasIsos`: Singleton presieves by isomorphisms are covering.
- `CategoryTheory.Precoverage.IsStableUnderBaseChange`: The pullback of a covering presieve is again
  covering.
- `CategoryTheory.Precoverage.IsStableUnderComposition`: Refining a covering presieve by covering
  presieves yields a covering presieve.

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

/-- A precoverage is a collection of *covering* presieves on every object `X : C`.
See `CategoryTheory.Coverage` and `CategoryTheory.Pretopology` for common extensions of this. -/
@[ext]
/--
Definition of `Precoverage` / `Precoverage` 的定义

English:
structure Precoverage
  parameters: (C : Type*) [Category* C]
  axioms and operations (1):
    - coverings : forall (X : C), Set (Presieve X)

中文:
结构 Precoverage
  参数: (C : 类型) [Category* C]
  公理与运算 (1 个):
    - coverings : 对任意 (X : C), Set (Presieve X)
-/
structure Precoverage (C : Type*) [Category* C] where
  /-- The collection of covering presieves for an object `X`. -/
  coverings : forall (X : C), Set (Presieve X)

namespace Precoverage

variable {C : Type u} [Category.{v} C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (Precoverage C) (fun _ => (X : C) -> Set (Presieve X))
  body: coverings

中文:
实例 :
  签名: CoeFun (Precoverage C) (fun _ => (X : C) -> Set (Presieve X))
  定义体: coverings

Depends on / 依赖: coverings
-/
instance : CoeFun (Precoverage C) (fun _ => (X : C) -> Set (Presieve X)) where
  coe := coverings

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Precoverage C)
  body: A.coverings <= B.coverings
  le_refl _ _ := le_refl _
  le_trans _ _ _ h1 h2 X := le_trans (h1 X) (h2 X)
le_antisymm _ _ h1 h2 := Precoverage.ext funext
    fun X => le_antisymm (h1 X) (h2 X)

中文:
实例 :
  签名: PartialOrder (Precoverage C)
  定义体: A.coverings <= B.coverings
  le_refl _ _ := le_refl _
  le_trans _ _ _ h1 h2 X := le_trans (h1 X) (h2 X)
le_antisymm _ _ h1 h2 := Precoverage.ext funext
    fun X => le_antisymm (h1 X) (h2 X)

Depends on / 依赖: A.coverings, B.coverings, coverings
-/
instance : PartialOrder (Precoverage C) where
  le A B := A.coverings <= B.coverings
  le_refl _ _ := le_refl _
  le_trans _ _ _ h1 h2 X := le_trans (h1 X) (h2 X)
le_antisymm _ _ h1 h2 := Precoverage.ext funext
    fun X => le_antisymm (h1 X) (h2 X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Precoverage C)
  body: ⟨A.coverings ⊓ B.coverings⟩

中文:
实例 :
  签名: Min (Precoverage C)
  定义体: ⟨A.coverings ⊓ B.coverings⟩

Depends on / 依赖: A.coverings, B.coverings, coverings
-/
instance : Min (Precoverage C) where
  min A B := ⟨A.coverings ⊓ B.coverings⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (Precoverage C)
  body: ⟨A.coverings ⊔ B.coverings⟩

中文:
实例 :
  签名: Max (Precoverage C)
  定义体: ⟨A.coverings ⊔ B.coverings⟩

Depends on / 依赖: A.coverings, B.coverings, coverings
-/
instance : Max (Precoverage C) where
  max A B := ⟨A.coverings ⊔ B.coverings⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet (Precoverage C)
  body: ⟨⨆ K in A, K.coverings⟩

中文:
实例 :
  签名: SupSet (Precoverage C)
  定义体: ⟨⨆ K in A, K.coverings⟩

Depends on / 依赖: K.coverings, coverings
-/
instance : SupSet (Precoverage C) where
  sSup A := ⟨⨆ K in A, K.coverings⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Precoverage C)
  body: ⟨⨅ K in A, K.coverings⟩

中文:
实例 :
  签名: InfSet (Precoverage C)
  定义体: ⟨⨅ K in A, K.coverings⟩

Depends on / 依赖: K.coverings, coverings
-/
instance : InfSet (Precoverage C) where
  sInf A := ⟨⨅ K in A, K.coverings⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (Precoverage C)
  body: .univ

中文:
实例 :
  签名: Top (Precoverage C)
  定义体: .univ
-/
instance : Top (Precoverage C) where
  top.coverings _ := .univ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (Precoverage C)
  body: ∅

中文:
实例 :
  签名: Bot (Precoverage C)
  定义体: ∅
-/
instance : Bot (Precoverage C) where
  bot.coverings _ := ∅

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Precoverage C)
  body: Function.Injective.completeLattice Precoverage.coverings (fun _ _ hab => Precoverage.ext hab)
    .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

中文:
实例 :
  签名: CompleteLattice (Precoverage C)
  定义体: Function.Injective.completeLattice Precoverage.coverings (fun _ _ hab => Precoverage.ext hab)
    .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

Depends on / 依赖: Function, Function.Injective.completeLattice, Injective, Precoverage, Precoverage.coverings, Precoverage.ext, completeLattice, coverings
-/
instance : CompleteLattice (Precoverage C) :=
  Function.Injective.completeLattice Precoverage.coverings (fun _ _ hab => Precoverage.ext hab)
    .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

/--
Definition of `HasIsos` / `HasIsos` 的定义

English:
class HasIsos
  parameters: (J : Precoverage C)
  axioms and operations (1):
    - mem_coverings_of_isIso({S T : C} (f : S ⟶ T) [IsIso f]) : .singleton f in J T

中文:
类 HasIsos
  参数: (J : Precoverage C)
  公理与运算 (1 个):
    - mem_coverings_of_isIso({S T : C} (f : S ⟶ T) [IsIso f]) : .singleton f in J T
-/
class HasIsos (J : Precoverage C) : Prop where
  mem_coverings_of_isIso {S T : C} (f : S ⟶ T) [IsIso f] : .singleton f in J T

/--
Definition of `IsStableUnderBaseChange` / `IsStableUnderBaseChange` 的定义

English:
class IsStableUnderBaseChange
  parameters: (J : Precoverage C)
  axioms and operations (1):
    - mem_coverings_of_isPullback({ι : Type (max u v)} {S : C} {X : ι -> C} (f : forall i, X i ⟶ S) (hR : Presieve.ofArrows X f in J S) {Y : C} (g : Y ⟶ S) {P : ι -> C} (p₁ : forall i, P i ⟶ Y) (p₂ : forall i, P i ⟶ X i) (h : forall i, IsPullback (p₁ i) (p₂ i) g (f i))) : .ofArrows P p₁ in J Y

中文:
类 IsStableUnderBaseChange
  参数: (J : Precoverage C)
  公理与运算 (1 个):
    - mem_coverings_of_isPullback({ι : Type (max u v)} {S : C} {X : ι -> C} (f : 对任意 i, X i ⟶ S) (hR : Presieve.ofArrows X f in J S) {Y : C} (g : Y ⟶ S) {P : ι -> C} (p₁ : 对任意 i, P i ⟶ Y) (p₂ : 对任意 i, P i ⟶ X i) (h : 对任意 i, IsPullback (p₁ i) (p₂ i) g (f i))) : .ofArrows P p₁ in J Y
-/
class IsStableUnderBaseChange (J : Precoverage C) : Prop where
  mem_coverings_of_isPullback {ι : Type (max u v)} {S : C} {X : ι -> C} (f : forall i, X i ⟶ S)
    (hR : Presieve.ofArrows X f in J S) {Y : C} (g : Y ⟶ S)
    {P : ι -> C} (p₁ : forall i, P i ⟶ Y) (p₂ : forall i, P i ⟶ X i)
    (h : forall i, IsPullback (p₁ i) (p₂ i) g (f i)) :
    .ofArrows P p₁ in J Y

/--
Definition of `IsStableUnderComposition` / `IsStableUnderComposition` 的定义

English:
class IsStableUnderComposition
  parameters: (J : Precoverage C)
  axioms and operations (1):
    - comp_mem_coverings({ι : Type (max u v)} {S : C} {X : ι -> C} (f : forall i, X i ⟶ S) (hf : Presieve.ofArrows X f in J S) {σ : ι -> Type (max u v)} {Y : forall (i : ι), σ i -> C} (g : forall i j, Y i j ⟶ X i) (hg : forall i, Presieve.ofArrows (Y i) (g i) in J (X i))) : .ofArrows (fun p : Σ i, σ i => Y _ p.2) (fun _ => g _ _ ≫ f _) in J S

中文:
类 IsStableUnderComposition
  参数: (J : Precoverage C)
  公理与运算 (1 个):
    - comp_mem_coverings({ι : Type (max u v)} {S : C} {X : ι -> C} (f : 对任意 i, X i ⟶ S) (hf : Presieve.ofArrows X f in J S) {σ : ι -> Type (max u v)} {Y : 对任意 (i : ι), σ i -> C} (g : 对任意 i j, Y i j ⟶ X i) (hg : 对任意 i, Presieve.ofArrows (Y i) (g i) in J (X i))) : .ofArrows (fun p : Σ i, σ i => Y _ p.2) (fun _ => g _ _ ≫ f _) in J S
-/
class IsStableUnderComposition (J : Precoverage C) : Prop where
  comp_mem_coverings {ι : Type (max u v)}
    {S : C} {X : ι -> C} (f : forall i, X i ⟶ S) (hf : Presieve.ofArrows X f in J S)
    {σ : ι -> Type (max u v)} {Y : forall (i : ι), σ i -> C}
    (g : forall i j, Y i j ⟶ X i) (hg : forall i, Presieve.ofArrows (Y i) (g i) in J (X i)) :
    .ofArrows (fun p : Σ i, σ i => Y _ p.2) (fun _ => g _ _ ≫ f _) in J S

/--
Definition of `IsStableUnderSup` / `IsStableUnderSup` 的定义

English:
class IsStableUnderSup
  parameters: (J : Precoverage C)
  axioms and operations (1):
    - sup_mem_coverings({X : C} {R S : Presieve X} (hR : R in J X) (hS : S in J X)) : R ⊔ S in J X

中文:
类 IsStableUnderSup
  参数: (J : Precoverage C)
  公理与运算 (1 个):
    - sup_mem_coverings({X : C} {R S : Presieve X} (hR : R in J X) (hS : S in J X)) : R ⊔ S in J X
-/
class IsStableUnderSup (J : Precoverage C) where
  sup_mem_coverings {X : C} {R S : Presieve X} (hR : R in J X) (hS : S in J X) :
    R ⊔ S in J X

/--
Definition of `HasPullbacks` / `HasPullbacks` 的定义

English:
class HasPullbacks
  parameters: (J : Precoverage C)
  axioms and operations (1):
    - hasPullbacks_of_mem({X Y : C} {R : Presieve Y} (f : X ⟶ Y) (hR : R in J Y)) : R.HasPullbacks f

中文:
类 HasPullbacks
  参数: (J : Precoverage C)
  公理与运算 (1 个):
    - hasPullbacks_of_mem({X Y : C} {R : Presieve Y} (f : X ⟶ Y) (hR : R in J Y)) : R.HasPullbacks f

Depends on / 依赖: HasIsos, HasIsos.mem_coverings_of_isIso, mem_coverings_of_isIso
-/
class HasPullbacks (J : Precoverage C) where
  hasPullbacks_of_mem {X Y : C} {R : Presieve Y} (f : X ⟶ Y) (hR : R in J Y) : R.HasPullbacks f

alias mem_coverings_of_isIso := HasIsos.mem_coverings_of_isIso
alias sup_mem_coverings := IsStableUnderSup.sup_mem_coverings
alias hasPullbacks_of_mem := HasPullbacks.hasPullbacks_of_mem

set_option backward.isDefEq.respectTransparency.types false in
set_option warning.simp.varHead false in
attribute [local simp] Presieve.ofArrows.obj_idx Presieve.ofArrows.hom_idx in
/--
lemma `mem_coverings_of_isPullback` / 引理 `mem_coverings_of_isPullback`

English:
lemma mem_coverings_of_isPullback
  statement: {J : Precoverage C} [IsStableUnderBaseChange J]
  proof: by
  -- We need to construct `max u v`-indexed families with the same presieves.
  -- Because `f` needs not be injective, the indexing type is a sum.
  let a (i : (Presieve.ofArrows X f).uncurry oplus (Presieve.ofArrows P p₁).uncurry) : ι :=
    i.elim (fun i => i.2.idx) (fun i => i.2.idx)
  convert

中文:
引理 mem_coverings_of_isPullback
  结论: {J : Precoverage C} [IsStableUnderBaseChange J]
  证明: by
  -- We need to construct `max u v`-indexed families with the same presieves.
  -- Because `f` needs not be injective, the indexing type is a sum.
  let a (i : (Presieve.ofArrows X f).uncurry oplus (Presieve.ofArrows P p₁).uncurry) : ι :=
    i.elim (fun i => i.2.idx) (fun i => i.2.idx)
  convert
-/
lemma mem_coverings_of_isPullback {J : Precoverage C} [IsStableUnderBaseChange J]
    {ι : Type w} {S : C} {X : ι -> C}
    (f : forall i, X i ⟶ S) (hR : Presieve.ofArrows X f in J S) {Y : C} (g : Y ⟶ S)
    {P : ι -> C} (p₁ : forall i, P i ⟶ Y) (p₂ : forall i, P i ⟶ X i)
    (h : forall i, IsPullback (p₁ i) (p₂ i) g (f i)) :
    .ofArrows P p₁ in J Y := by
  -- We need to construct `max u v`-indexed families with the same presieves.
  -- Because `f` needs not be injective, the indexing type is a sum.
  let a (i : (Presieve.ofArrows X f).uncurry oplus (Presieve.ofArrows P p₁).uncurry) : ι :=
    i.elim (fun i => i.2.idx) (fun i => i.2.idx)
  convert_to Presieve.ofArrows (P ∘ a) (fun i => p₁ (a i)) in _
  · refine le_antisymm (fun Z g hg => ?_) fun Z g ⟨i⟩ => ⟨a i⟩
    exact .mk' (Sum.inr ⟨⟨_, _⟩, hg⟩) (by cat_disch) (by cat_disch)
  · refine IsStableUnderBaseChange.mem_coverings_of_isPullback (fun i => f (a i)) ?_ g _
      (fun i => p₂ (a i)) fun i => h _
    convert! hR
    refine le_antisymm (fun Z g ⟨i⟩ => .mk _) fun Z g hg => ?_
    exact .mk' (Sum.inl ⟨⟨_, _⟩, hg⟩) (by cat_disch) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option warning.simp.varHead false in
attribute [local simp] Presieve.ofArrows.obj_idx Presieve.ofArrows.hom_idx in
/--
lemma `comp_mem_coverings` / 引理 `comp_mem_coverings`

English:
lemma comp_mem_coverings
  statement: {J : Precoverage C} [IsStableUnderComposition J] {ι : Type w}
  proof: by
  -- We need to construct `max u v`-indexed families with the same presieves.
  -- Because `f` and `g` need not be injective, the indexing type is a sigma of sums.
  let ι' : Type (max u v) := (Presieve.ofArrows X f).uncurry
  let σ' (i : ι') : Type (max u v) := (Presieve.ofArrows (Y i.2.idx) (g 

中文:
引理 comp_mem_coverings
  结论: {J : Precoverage C} [IsStableUnderComposition J] {ι : Type w}
  证明: by
  -- We need to construct `max u v`-indexed families with the same presieves.
  -- Because `f` and `g` need not be injective, the indexing type is a sigma of sums.
  let ι' : Type (max u v) := (Presieve.ofArrows X f).uncurry
  let σ' (i : ι') : Type (max u v) := (Presieve.ofArrows (Y i.2.idx) (g 
-/
lemma comp_mem_coverings {J : Precoverage C} [IsStableUnderComposition J] {ι : Type w}
    {S : C} {X : ι -> C} (f : forall i, X i ⟶ S) (hf : Presieve.ofArrows X f in J S)
    {σ : ι -> Type w'} {Y : forall (i : ι), σ i -> C}
    (g : forall i j, Y i j ⟶ X i) (hg : forall i, Presieve.ofArrows (Y i) (g i) in J (X i)) :
    .ofArrows (fun p : Σ i, σ i => Y _ p.2) (fun _ => g _ _ ≫ f _) in J S := by
  -- We need to construct `max u v`-indexed families with the same presieves.
  -- Because `f` and `g` need not be injective, the indexing type is a sigma of sums.
  let ι' : Type (max u v) := (Presieve.ofArrows X f).uncurry
  let σ' (i : ι') : Type (max u v) := (Presieve.ofArrows (Y i.2.idx) (g i.2.idx)).uncurry
  let α : Type (max u v) :=
    (Presieve.ofArrows (fun p : Σ i, σ i => Y _ p.2) (fun _ => g _ _ ≫ f _)).uncurry
  let τ' (a : α) : Type (max u v) := (Presieve.ofArrows (Y a.2.idx.1) (g a.2.idx.1)).uncurry
  let fib (i : ι' oplus α) := i.elim (fun i => σ' i) (fun i => Unit oplus τ' i)
  let incl (p : ι' oplus α) : ι := p.elim (fun i => i.2.idx) (fun i => i.2.idx.1)
  let fibincl (i : ι' oplus α) (j : fib i) : σ (incl i) := match i with
    | .inl i => j.2.idx
    | .inr i => j.elim (fun _ => i.2.idx.2) (fun i => i.2.idx)
  convert_to Presieve.ofArrows _
      (fun p : Σ (i : ι' oplus α), fib i => g (incl p.1) (fibincl _ p.2) ≫ f (incl p.1)) in J.coverings S
  · refine le_antisymm (fun T u hu => ?_) fun T u ⟨p⟩ => .mk (Sigma.mk (incl p.1) (fibincl p.1 p.2))
    exact .mk' ⟨Sum.inr ⟨⟨_, _⟩, hu⟩, .inl ⟨⟩⟩ hu.obj_idx.symm hu.eq_eqToHom_comp_hom_idx
  · refine IsStableUnderComposition.comp_mem_coverings (f := fun i => f (incl i))
        (g := fun i j => g (incl i) (fibincl i j)) ?_ fun i => ?_
    · convert! hf
      refine le_antisymm (fun T u ⟨p⟩ => .mk _) fun T u hu => ?_
      exact .mk' (Sum.inl ⟨⟨_, _⟩, hu⟩) (by cat_disch) (by cat_disch)
    · convert! hg (incl i)
      refine le_antisymm (fun T u ⟨p⟩ => .mk _) fun T u hu => ?_
      match i with
      | .inl i => exact .mk' ⟨⟨_, _⟩, hu⟩ (by cat_disch) (by cat_disch)
      | .inr i => exact .mk' (.inr ⟨⟨_, _⟩, hu⟩) (by cat_disch) (by cat_disch)

instance (J : Precoverage C) [Limits.HasPullbacks C] : J.HasPullbacks where
  hasPullbacks_of_mem := inferInstance

/--
lemma `pullbackArrows_mem` / 引理 `pullbackArrows_mem`

English:
lemma pullbackArrows_mem
  statement: {J : Precoverage C} [IsStableUnderBaseChange J]
  proof: by
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  have (i : ι) : Limits.HasPullback (g i) f := Presieve.hasPullback f (Presieve.ofArrows.mk i)
  rw [← Presieve.ofArrows_pullback]
  exact mem_coverings_of_isPullback _ hR _ _ _ fun i => (IsPullback.of_hasPullback _ _).flip

中文:
引理 pullbackArrows_mem
  结论: {J : Precoverage C} [IsStableUnderBaseChange J]
  证明: by
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  have (i : ι) : Limits.HasPullback (g i) f := Presieve.hasPullback f (Presieve.ofArrows.mk i)
  rw [← Presieve.ofArrows_pullback]
  exact mem_coverings_of_isPullback _ hR _ _ _ fun i => (IsPullback.of_hasPullback _ _).flip

Depends on / 依赖: HasPullback, IsPullback, IsPullback.of_hasPullback, Limits, Limits.HasPullback, Presieve, Presieve.hasPullback, Presieve.ofArrows.mk, Presieve.ofArrows_pullback, R.exists_eq_ofArrows, exists_eq_ofArrows, hasPullback, mem_coverings_of_isPullback, ofArrows, ofArrows_pullback, of_hasPullback
-/
lemma pullbackArrows_mem {J : Precoverage C} [IsStableUnderBaseChange J]
    {X Y : C} (f : X ⟶ Y) {R : Presieve Y} (hR : R in J Y) [R.HasPullbacks f] :
    R.pullbackArrows f in J X := by
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  have (i : ι) : Limits.HasPullback (g i) f := Presieve.hasPullback f (Presieve.ofArrows.mk i)
  rw [← Presieve.ofArrows_pullback]
  exact mem_coverings_of_isPullback _ hR _ _ _ fun i => (IsPullback.of_hasPullback _ _).flip

instance (J K : Precoverage C) [HasIsos J] [HasIsos K] : HasIsos (J ⊓ K) where
  mem_coverings_of_isIso f _ := ⟨mem_coverings_of_isIso f, mem_coverings_of_isIso f⟩

instance (J K : Precoverage C) [IsStableUnderBaseChange J] [IsStableUnderBaseChange K] :
    IsStableUnderBaseChange (J ⊓ K) where
  mem_coverings_of_isPullback _ hf _ _ _ _ _ h :=
    ⟨mem_coverings_of_isPullback _ hf.1 _ _ _ h, mem_coverings_of_isPullback _ hf.2 _ _ _ h⟩

instance (J K : Precoverage C) [IsStableUnderComposition J]
    [IsStableUnderComposition K] : IsStableUnderComposition (J ⊓ K) where
  comp_mem_coverings _ h _ _ _ H :=
    ⟨comp_mem_coverings _ h.1 _ fun i => (H i).1, comp_mem_coverings _ h.2 _ fun i => (H i).2⟩

instance (J K : Precoverage C) [IsStableUnderSup J] [IsStableUnderSup K] :
    IsStableUnderSup (J ⊓ K) where
  sup_mem_coverings hR hS := ⟨J.sup_mem_coverings hR.1 hS.1, K.sup_mem_coverings hR.2 hS.2⟩

/--
lemma `hasPairwisePullbacks_of_mem` / 引理 `hasPairwisePullbacks_of_mem`

English:
lemma hasPairwisePullbacks_of_mem
  statement: (J : Precoverage C) [J.HasPullbacks] {X : C} {R : Presieve X}
  proof: (J.hasPullbacks_of_mem f hR).hasPullback h

中文:
引理 hasPairwisePullbacks_of_mem
  结论: (J : Precoverage C) [J.HasPullbacks] {X : C} {R : Presieve X}
  证明: (J.hasPullbacks_of_mem f hR).hasPullback h

Depends on / 依赖: J.hasPullbacks_of_mem, hasPullback, hasPullbacks_of_mem
-/
lemma hasPairwisePullbacks_of_mem (J : Precoverage C) [J.HasPullbacks] {X : C} {R : Presieve X}
    (hR : R in J X) :
    R.HasPairwisePullbacks where
  has_pullbacks h f _ := (J.hasPullbacks_of_mem f hR).hasPullback h

section Functoriality

variable {D : Type*} [Category* D] {F : C ⥤ D}

variable {J K : Precoverage D}

open Limits

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (F : C ⥤ D) (J : Precoverage D)
  body: {R | R.map F in J (F.obj Y)}

@[simp]

中文:
定义 comap
  签名: (F : C ⥤ D) (J : Precoverage D)
  定义体: {R | R.map F in J (F.obj Y)}

@[simp]

Depends on / 依赖: F.obj, R.map
-/
def comap (F : C ⥤ D) (J : Precoverage D) : Precoverage C where
  coverings Y := {R | R.map F in J (F.obj Y)}

@[simp]
/--
lemma `mem_comap_iff` / 引理 `mem_comap_iff`

English:
lemma mem_comap_iff
  given: {X : C} {R : Presieve X}
  proof: Iff.rfl

中文:
引理 mem_comap_iff
  条件: {X : C} {R : Presieve X}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_comap_iff {X : C} {R : Presieve X} :
    R in J.comap F X ↔ R.map F in J (F.obj X) := Iff.rfl

/--
lemma `comap_inf` / 引理 `comap_inf`

English:
lemma comap_inf
  statement: (J ⊓ K).comap F = J.comap F ⊓ K.comap F
  proof: rfl

@[simp]

中文:
引理 comap_inf
  结论: (J ⊓ K).comap F = J.comap F ⊓ K.comap F
  证明: rfl

@[simp]
-/
lemma comap_inf : (J ⊓ K).comap F = J.comap F ⊓ K.comap F := rfl

@[simp]
/--
lemma `comap_id` / 引理 `comap_id`

English:
lemma comap_id
  given: (K : Precoverage C)
  statement: K.comap (𝟭 C) = K
  proof: by
  ext
  simp

中文:
引理 comap_id
  条件: (K : Precoverage C)
  结论: K.comap (𝟭 C) = K
  证明: by
  ext
  simp
-/
lemma comap_id (K : Precoverage C) : K.comap (𝟭 C) = K := by
  ext
  simp

set_option backward.defeqAttrib.useBackward true in
/--
lemma `comap_comp` / 引理 `comap_comp`

English:
lemma comap_comp
  given: {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E) (J : Precoverage E)
  proof: by
  ext X R
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  simp

@[mono, gcongr]

中文:
引理 comap_comp
  条件: {E : 类型} [Category* E] (F : C ⥤ D) (G : D ⥤ E) (J : Precoverage E)
  证明: by
  ext X R
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  simp

@[mono, gcongr]

Depends on / 依赖: R.exists_eq_ofArrows, exists_eq_ofArrows
-/
lemma comap_comp {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E) (J : Precoverage E) :
    J.comap (F ⋙ G) = (J.comap G).comap F := by
  ext X R
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  simp

@[mono, gcongr]
/--
lemma `comap_monotone` / 引理 `comap_monotone`

English:
lemma comap_monotone
  statement: Monotone (comap F)
  proof: fun _ _ hJK _ _ hR => hJK _ hR

中文:
引理 comap_monotone
  结论: Monotone (comap F)
  证明: fun _ _ hJK _ _ hR => hJK _ hR
-/
lemma comap_monotone : Monotone (comap F) :=
  fun _ _ hJK _ _ hR => hJK _ hR

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasIsos
  signature: J] : HasIsos (J.comap F) where
  body: by simpa using mem_coverings_of_isIso (F.map f)

中文:
实例 [HasIsos
  签名: J] : HasIsos (J.comap F) where
  定义体: by simpa using mem_coverings_of_isIso (F.map f)

Depends on / 依赖: F.map, mem_coverings_of_isIso
-/
instance [HasIsos J] : HasIsos (J.comap F) where
  mem_coverings_of_isIso {S T} f hf := by simpa using mem_coverings_of_isIso (F.map f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsStableUnderComposition
  signature: J] :
  body: by
    simp only [mem_comap_iff, Presieve.map_ofArrows, Functor.map_comp] at hf hg ⊢
    exact J.comp_mem_coverings _ hf _ hg

中文:
实例 [IsStableUnderComposition
  签名: J] :
  定义体: by
    simp only [mem_comap_iff, Presieve.map_ofArrows, Functor.map_comp] at hf hg ⊢
    exact J.comp_mem_coverings _ hf _ hg

Depends on / 依赖: Functor, Functor.map_comp, J.comp_mem_coverings, Presieve, Presieve.map_ofArrows, comp_mem_coverings, map_comp, map_ofArrows, mem_comap_iff
-/
instance [IsStableUnderComposition J] :
    IsStableUnderComposition (J.comap F) where
  comp_mem_coverings {ι} S Y f hf σ Z g hg := by
    simp only [mem_comap_iff, Presieve.map_ofArrows, Functor.map_comp] at hf hg ⊢
    exact J.comp_mem_coverings _ hf _ hg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreservesLimitsOfShape
  signature: WalkingCospan F] [IsStableUnderBaseChange J] :
  body: by
    simp only [mem_comap_iff, Presieve.map_ofArrows] at hf ⊢
    exact mem_coverings_of_isPullback _ hf _ _ _
      fun i => CategoryTheory.Functor.map_isPullback F (h i)

中文:
实例 [PreservesLimitsOfShape
  签名: WalkingCospan F] [IsStableUnderBaseChange J] :
  定义体: by
    simp only [mem_comap_iff, Presieve.map_ofArrows] at hf ⊢
    exact mem_coverings_of_isPullback _ hf _ _ _
      fun i => CategoryTheory.Functor.map_isPullback F (h i)

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_isPullback, Functor, Presieve, Presieve.map_ofArrows, map_isPullback, map_ofArrows, mem_comap_iff, mem_coverings_of_isPullback
-/
instance [PreservesLimitsOfShape WalkingCospan F] [IsStableUnderBaseChange J] :
    IsStableUnderBaseChange (J.comap F) where
  mem_coverings_of_isPullback {ι} S Y f hf Z g P p₁ p₂ h := by
    simp only [mem_comap_iff, Presieve.map_ofArrows] at hf ⊢
    exact mem_coverings_of_isPullback _ hf _ _ _
      fun i => CategoryTheory.Functor.map_isPullback F (h i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CreatesLimitsOfShape
  signature: WalkingCospan F] [HasPullbacks J] : HasPullbacks (J.comap F) where
  body: by
    refine ⟨fun {Z g} hg => ?_⟩
    have : (Presieve.map F R).HasPullbacks (F.map f) := J.hasPullbacks_of_mem (F.map f) hR
    have : HasPullback (F.map g) (F.map f) := (R.map F).hasPullback _ (R.map_map hg)
    exact .of_createsLimit F g f

中文:
实例 [CreatesLimitsOfShape
  签名: WalkingCospan F] [HasPullbacks J] : HasPullbacks (J.comap F) where
  定义体: by
    refine ⟨fun {Z g} hg => ?_⟩
    have : (Presieve.map F R).HasPullbacks (F.map f) := J.hasPullbacks_of_mem (F.map f) hR
    have : HasPullback (F.map g) (F.map f) := (R.map F).hasPullback _ (R.map_map hg)
    exact .of_createsLimit F g f

Depends on / 依赖: F.map, HasPullback, HasPullbacks, J.hasPullbacks_of_mem, Presieve, Presieve.map, R.map, R.map_map, hasPullback, hasPullbacks_of_mem, map_map, of_createsLimit
-/
instance [CreatesLimitsOfShape WalkingCospan F] [HasPullbacks J] : HasPullbacks (J.comap F) where
  hasPullbacks_of_mem {X Y} R f hR := by
    refine ⟨fun {Z g} hg => ?_⟩
    have : (Presieve.map F R).HasPullbacks (F.map f) := J.hasPullbacks_of_mem (F.map f) hR
    have : HasPullback (F.map g) (F.map f) := (R.map F).hasPullback _ (R.map_map hg)
    exact .of_createsLimit F g f

end Functoriality

end Precoverage

section PreservesPullbacks

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

open Limits

/--
Definition of `Functor.PreservesPairwisePullbacks` / `Functor.PreservesPairwisePullbacks` 的定义

English:
class Functor.PreservesPairwisePullbacks
  parameters: (F : C ⥤ D) {X : C} (R : Presieve X)
  axioms and operations (1):
    - preservesLimit((R) ⦃Y Z) : C⦄ ⦃f : Y ⟶ X⦄ ⦃g : Z ⟶ X⦄ : R f -> R g -> PreservesLimit (cospan f g) F  [default: by infer_instance]

中文:
类 Functor.PreservesPairwisePullbacks
  参数: (F : C ⥤ D) {X : C} (R : Presieve X)
  公理与运算 (1 个):
    - preservesLimit((R) ⦃Y Z) : C⦄ ⦃f : Y ⟶ X⦄ ⦃g : Z ⟶ X⦄ : R f -> R g -> PreservesLimit (cospan f g) F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class Functor.PreservesPairwisePullbacks (F : C ⥤ D) {X : C} (R : Presieve X) : Prop where
  preservesLimit (R) ⦃Y Z : C⦄ ⦃f : Y ⟶ X⦄ ⦃g : Z ⟶ X⦄ : R f -> R g ->
    PreservesLimit (cospan f g) F := by infer_instance

alias Functor.preservesLimit_cospan_of_mem_presieve :=
  Functor.PreservesPairwisePullbacks.preservesLimit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreservesLimitsOfShape
  signature: WalkingCospan F] {X

中文:
实例 [PreservesLimitsOfShape
  签名: WalkingCospan F] {X
-/
instance [PreservesLimitsOfShape WalkingCospan F] {X : C} (R : Presieve X) :
    F.PreservesPairwisePullbacks R where

/--
lemma `Presieve.HasPairwisePullbacks.map_of_preservesPairwisePullbacks` / 引理 `Presieve.HasPairwisePullbacks.map_of_preservesPairwisePullbacks`

English:
lemma Presieve.HasPairwisePullbacks.map_of_preservesPairwisePullbacks
  statement: {X : C} (R : Presieve X)
  proof: fun {f} ⟨hf⟩ g ⟨hg⟩ => by
    have := Presieve.HasPairwisePullbacks.has_pullbacks hf hg
    have := F.preservesLimit_cospan_of_mem_presieve _ hf hg
    exact hasPullback_of_preservesPullback F _ _

中文:
引理 Presieve.HasPairwisePullbacks.map_of_preservesPairwisePullbacks
  结论: {X : C} (R : Presieve X)
  证明: fun {f} ⟨hf⟩ g ⟨hg⟩ => by
    have := Presieve.HasPairwisePullbacks.has_pullbacks hf hg
    have := F.preservesLimit_cospan_of_mem_presieve _ hf hg
    exact hasPullback_of_preservesPullback F _ _

Depends on / 依赖: F.preservesLimit_cospan_of_mem_presieve, HasPairwisePullbacks, Presieve, Presieve.HasPairwisePullbacks.has_pullbacks, hasPullback_of_preservesPullback, has_pullbacks, preservesLimit_cospan_of_mem_presieve
-/
lemma Presieve.HasPairwisePullbacks.map_of_preservesPairwisePullbacks {X : C} (R : Presieve X)
    [F.PreservesPairwisePullbacks R] [R.HasPairwisePullbacks] :
    (R.map F).HasPairwisePullbacks where
  has_pullbacks {Y Z} := fun {f} ⟨hf⟩ g ⟨hg⟩ => by
    have := Presieve.HasPairwisePullbacks.has_pullbacks hf hg
    have := F.preservesLimit_cospan_of_mem_presieve _ hf hg
    exact hasPullback_of_preservesPullback F _ _

namespace Precoverage

/--
Definition of `PullbacksPreservedBy` / `PullbacksPreservedBy` 的定义

English:
class PullbacksPreservedBy
  parameters: (J : Precoverage C) (F : C ⥤ D)
  axioms and operations (1):
    - preservesPairwisePullbacks_of_mem(⦃X) : C⦄ ⦃R : Presieve X⦄ : R in J X -> F.PreservesPairwisePullbacks R  [default: by infer_instance]

中文:
类 PullbacksPreservedBy
  参数: (J : Precoverage C) (F : C ⥤ D)
  公理与运算 (1 个):
    - preservesPairwisePullbacks_of_mem(⦃X) : C⦄ ⦃R : Presieve X⦄ : R in J X -> F.PreservesPairwisePullbacks R  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class PullbacksPreservedBy (J : Precoverage C) (F : C ⥤ D) : Prop where
  preservesPairwisePullbacks_of_mem ⦃X : C⦄ ⦃R : Presieve X⦄ :
    R in J X -> F.PreservesPairwisePullbacks R := by infer_instance

alias preservesPairwisePullbacks_of_mem :=
  Precoverage.PullbacksPreservedBy.preservesPairwisePullbacks_of_mem

instance (J : Precoverage C) (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F] :
    J.PullbacksPreservedBy F where

end Precoverage

end PreservesPullbacks

end CategoryTheory
