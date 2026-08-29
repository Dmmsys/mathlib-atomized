/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.Order.Closure
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Closed sieves

A natural closure operator on sieves is a closure operator on `Sieve X` for each `X` which commutes
with pullback.
We show that a Grothendieck topology `J` induces a natural closure operator, and define what the
closed sieves are. The collection of `J`-closed sieves forms a presheaf which is a sheaf for `J`,
and further this presheaf can be used to determine the Grothendieck topology from the sheaf
predicate.
Finally we show that a natural closure operator on sieves induces a Grothendieck topology, and hence
that natural closure operators are in bijection with Grothendieck topologies.

## Main definitions

* `CategoryTheory.GrothendieckTopology.close`: Sends a sieve `S` on `X` to the set of arrows
  which it covers. This has all the usual properties of a closure operator, as well as commuting
  with pullback.
* `CategoryTheory.GrothendieckTopology.closureOperator`: The bundled `ClosureOperator` given
  by `CategoryTheory.GrothendieckTopology.close`.
* `CategoryTheory.GrothendieckTopology.IsClosed`: A sieve `S` on `X` is closed for the topology `J`
  if it contains every arrow it covers.
* `CategoryTheory.Functor.closedSieves`: The presheaf sending `X` to the collection of `J`-closed
  sieves on `X`. This is additionally shown to be a sheaf for `J`, and if this is a sheaf for a
  different topology `J'`, then `J' ≤ J`.
* `CategoryTheory.topologyOfClosureOperator`: A closure operator on the
  set of sieves on every object which commutes with pullback additionally induces a Grothendieck
  topology, giving a bijection with `CategoryTheory.GrothendieckTopology.closureOperator`.


## Tags

closed sieve, closure, Grothendieck topology

## References

* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
-/

@[expose] public section


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (J₁ J₂ : GrothendieckTopology C)

namespace GrothendieckTopology

/-- The `J`-closure of a sieve is the collection of arrows which it covers. -/
@[simps]
/--
Definition of `close` / `close` 的定义

English:
definition close
  signature: {X : C} (S : Sieve X)
  body: J₁.Covers S f
  downward_closed hS := J₁.arrow_stable _ _ hS

中文:
定义 close
  签名: {X : C} (S : Sieve X)
  定义体: J₁.Covers S f
  downward_closed hS := J₁.arrow_stable _ _ hS

Depends on / 依赖: Covers
-/
def close {X : C} (S : Sieve X) : Sieve X where
  arrows _ f := J₁.Covers S f
  downward_closed hS := J₁.arrow_stable _ _ hS

/--
theorem `le_close` / 定理 `le_close`

English:
theorem le_close
  given: {X : C} (S : Sieve X)
  statement: S <= J₁.close S
  proof: fun _ _ hg => J₁.covering_of_eq_top (S.pullback_eq_top_of_mem hg)

中文:
定理 le_close
  条件: {X : C} (S : Sieve X)
  结论: S <= J₁.close S
  证明: fun _ _ hg => J₁.covering_of_eq_top (S.pullback_eq_top_of_mem hg)

Depends on / 依赖: S.pullback_eq_top_of_mem, covering_of_eq_top, pullback_eq_top_of_mem
-/
theorem le_close {X : C} (S : Sieve X) : S <= J₁.close S :=
  fun _ _ hg => J₁.covering_of_eq_top (S.pullback_eq_top_of_mem hg)

/--
Definition of `IsClosed` / `IsClosed` 的定义

English:
definition IsClosed
  signature: {X : C} (S : Sieve X)
  body: forall ⦃Y : C⦄ (f : Y ⟶ X), J₁.Covers S f -> S f

中文:
定义 IsClosed
  签名: {X : C} (S : Sieve X)
  定义体: forall ⦃Y : C⦄ (f : Y ⟶ X), J₁.Covers S f -> S f

Depends on / 依赖: Covers
-/
def IsClosed {X : C} (S : Sieve X) : Prop :=
  forall ⦃Y : C⦄ (f : Y ⟶ X), J₁.Covers S f -> S f

/--
theorem `covers_iff_mem_of_isClosed` / 定理 `covers_iff_mem_of_isClosed`

English:
theorem covers_iff_mem_of_isClosed
  given: {X : C} {S : Sieve X} (h : J₁.IsClosed S) {Y : C} (f : Y ⟶ X)
  proof: ⟨h _, J₁.arrow_max _ _⟩

中文:
定理 covers_iff_mem_of_isClosed
  条件: {X : C} {S : Sieve X} (h : J₁.IsClosed S) {Y : C} (f : Y ⟶ X)
  证明: ⟨h _, J₁.arrow_max _ _⟩

Depends on / 依赖: arrow_max
-/
theorem covers_iff_mem_of_isClosed {X : C} {S : Sieve X} (h : J₁.IsClosed S) {Y : C} (f : Y ⟶ X) :
    J₁.Covers S f ↔ S f :=
  ⟨h _, J₁.arrow_max _ _⟩

/--
theorem `isClosed_pullback` / 定理 `isClosed_pullback`

English:
theorem isClosed_pullback
  given: {X Y : C} (f : Y ⟶ X) (S : Sieve X)
  proof: fun hS Z g hg => hS (g ≫ f) (by rwa [J₁.covers_iff, Sieve.pullback_comp])

中文:
定理 isClosed_pullback
  条件: {X Y : C} (f : Y ⟶ X) (S : Sieve X)
  证明: fun hS Z g hg => hS (g ≫ f) (by rwa [J₁.covers_iff, Sieve.pullback_comp])

Depends on / 依赖: Sieve.pullback_comp, covers_iff, pullback_comp
-/
theorem isClosed_pullback {X Y : C} (f : Y ⟶ X) (S : Sieve X) :
    J₁.IsClosed S -> J₁.IsClosed (S.pullback f) :=
  fun hS Z g hg => hS (g ≫ f) (by rwa [J₁.covers_iff, Sieve.pullback_comp])

/--
theorem `le_close_of_isClosed` / 定理 `le_close_of_isClosed`

English:
theorem le_close_of_isClosed
  given: {X : C} {S T : Sieve X} (h : S <= T) (hT : J₁.IsClosed T)
  proof: fun _ f hf => hT _ (J₁.superset_covering (Sieve.pullback_monotone f h) hf)

中文:
定理 le_close_of_isClosed
  条件: {X : C} {S T : Sieve X} (h : S <= T) (hT : J₁.IsClosed T)
  证明: fun _ f hf => hT _ (J₁.superset_covering (Sieve.pullback_monotone f h) hf)

Depends on / 依赖: Sieve.pullback_monotone, pullback_monotone, superset_covering
-/
theorem le_close_of_isClosed {X : C} {S T : Sieve X} (h : S <= T) (hT : J₁.IsClosed T) :
    J₁.close S <= T :=
  fun _ f hf => hT _ (J₁.superset_covering (Sieve.pullback_monotone f h) hf)

/--
theorem `close_isClosed` / 定理 `close_isClosed`

English:
theorem close_isClosed
  given: {X : C} (S : Sieve X)
  statement: J₁.IsClosed (J₁.close S)
  proof: fun _ g hg => J₁.arrow_trans g _ S hg fun _ hS => hS

中文:
定理 close_isClosed
  条件: {X : C} (S : Sieve X)
  结论: J₁.IsClosed (J₁.close S)
  证明: fun _ g hg => J₁.arrow_trans g _ S hg fun _ hS => hS

Depends on / 依赖: arrow_trans
-/
theorem close_isClosed {X : C} (S : Sieve X) : J₁.IsClosed (J₁.close S) :=
  fun _ g hg => J₁.arrow_trans g _ S hg fun _ hS => hS

/-- A Grothendieck topology induces a natural family of closure operators on sieves. -/
@[simps! isClosed]
/--
Definition of `closureOperator` / `closureOperator` 的定义

English:
definition closureOperator
  signature: (X : C)
  body: .ofPred J₁.close J₁.IsClosed J₁.le_close J₁.close_isClosed fun _ _ => J₁.le_close_of_isClosed

中文:
定义 closureOperator
  签名: (X : C)
  定义体: .ofPred J₁.close J₁.IsClosed J₁.le_close J₁.close_isClosed fun _ _ => J₁.le_close_of_isClosed

Depends on / 依赖: IsClosed, close_isClosed, le_close, le_close_of_isClosed, ofPred
-/
def closureOperator (X : C) : ClosureOperator (Sieve X) :=
  .ofPred J₁.close J₁.IsClosed J₁.le_close J₁.close_isClosed fun _ _ => J₁.le_close_of_isClosed

/--
theorem `isClosed_iff_close_eq_self` / 定理 `isClosed_iff_close_eq_self`

English:
theorem isClosed_iff_close_eq_self
  given: {X : C} (S : Sieve X)
  statement: J₁.IsClosed S ↔ J₁.close S = S
  proof: (J₁.closureOperator _).isClosed_iff

中文:
定理 isClosed_iff_close_eq_self
  条件: {X : C} (S : Sieve X)
  结论: J₁.IsClosed S ↔ J₁.close S = S
  证明: (J₁.closureOperator _).isClosed_iff

Depends on / 依赖: closureOperator, isClosed_iff
-/
theorem isClosed_iff_close_eq_self {X : C} (S : Sieve X) : J₁.IsClosed S ↔ J₁.close S = S :=
  (J₁.closureOperator _).isClosed_iff

/--
theorem `close_eq_self_of_isClosed` / 定理 `close_eq_self_of_isClosed`

English:
theorem close_eq_self_of_isClosed
  given: {X : C} {S : Sieve X} (hS : J₁.IsClosed S)
  statement: J₁.close S = S
  proof: (J₁.isClosed_iff_close_eq_self S).1 hS

中文:
定理 close_eq_self_of_isClosed
  条件: {X : C} {S : Sieve X} (hS : J₁.IsClosed S)
  结论: J₁.close S = S
  证明: (J₁.isClosed_iff_close_eq_self S).1 hS

Depends on / 依赖: isClosed_iff_close_eq_self
-/
theorem close_eq_self_of_isClosed {X : C} {S : Sieve X} (hS : J₁.IsClosed S) : J₁.close S = S :=
  (J₁.isClosed_iff_close_eq_self S).1 hS

/--
theorem `pullback_close` / 定理 `pullback_close`

English:
theorem pullback_close
  given: {X Y : C} (f : Y ⟶ X) (S : Sieve X)
  proof: by
  apply le_antisymm
  · refine J₁.le_close_of_isClosed (Sieve.pullback_monotone _ (J₁.le_close S)) ?_
    apply J₁.isClosed_pullback _ _ (J₁.close_isClosed _)
  · intro Z g hg
    change _ in J₁ _
    rw [← Sieve.pullback_comp]
    apply hg

@[gcongr, mono]

中文:
定理 pullback_close
  条件: {X Y : C} (f : Y ⟶ X) (S : Sieve X)
  证明: by
  apply le_antisymm
  · refine J₁.le_close_of_isClosed (Sieve.pullback_monotone _ (J₁.le_close S)) ?_
    apply J₁.isClosed_pullback _ _ (J₁.close_isClosed _)
  · intro Z g hg
    change _ in J₁ _
    rw [← Sieve.pullback_comp]
    apply hg

@[gcongr, mono]

Depends on / 依赖: Sieve.pullback_comp, Sieve.pullback_monotone, close_isClosed, isClosed_pullback, le_antisymm, le_close, le_close_of_isClosed, pullback_comp, pullback_monotone
-/
theorem pullback_close {X Y : C} (f : Y ⟶ X) (S : Sieve X) :
    J₁.close (S.pullback f) = (J₁.close S).pullback f := by
  apply le_antisymm
  · refine J₁.le_close_of_isClosed (Sieve.pullback_monotone _ (J₁.le_close S)) ?_
    apply J₁.isClosed_pullback _ _ (J₁.close_isClosed _)
  · intro Z g hg
    change _ in J₁ _
    rw [← Sieve.pullback_comp]
    apply hg

@[gcongr, mono]
/--
theorem `monotone_close` / 定理 `monotone_close`

English:
theorem monotone_close
  given: {X : C}
  statement: Monotone (J₁.close : Sieve X -> Sieve X)
  proof: (J₁.closureOperator _).monotone

@[simp]

中文:
定理 monotone_close
  条件: {X : C}
  结论: Monotone (J₁.close : Sieve X -> Sieve X)
  证明: (J₁.closureOperator _).monotone

@[simp]

Depends on / 依赖: closureOperator, monotone
-/
theorem monotone_close {X : C} : Monotone (J₁.close : Sieve X -> Sieve X) :=
  (J₁.closureOperator _).monotone

@[simp]
/--
theorem `close_close` / 定理 `close_close`

English:
theorem close_close
  given: {X : C} (S : Sieve X)
  statement: J₁.close (J₁.close S) = J₁.close S
  proof: (J₁.closureOperator _).idempotent _

中文:
定理 close_close
  条件: {X : C} (S : Sieve X)
  结论: J₁.close (J₁.close S) = J₁.close S
  证明: (J₁.closureOperator _).idempotent _

Depends on / 依赖: closureOperator, idempotent
-/
theorem close_close {X : C} (S : Sieve X) : J₁.close (J₁.close S) = J₁.close S :=
  (J₁.closureOperator _).idempotent _

/--
theorem `close_eq_top_iff_mem` / 定理 `close_eq_top_iff_mem`

English:
theorem close_eq_top_iff_mem
  given: {X : C} (S : Sieve X)
  statement: J₁.close S = ⊤ ↔ S in J₁ X
  proof: by
  constructor
  · intro h
    apply J₁.transitive (J₁.top_mem X)
    intro Y f hf
    change J₁.close S f
    rwa [h]
  · intro hS
    rw [_root_.eq_top_iff]
    intro Y f _
    apply J₁.pullback_stable _ hS

中文:
定理 close_eq_top_iff_mem
  条件: {X : C} (S : Sieve X)
  结论: J₁.close S = ⊤ ↔ S in J₁ X
  证明: by
  constructor
  · intro h
    apply J₁.transitive (J₁.top_mem X)
    intro Y f hf
    change J₁.close S f
    rwa [h]
  · intro hS
    rw [_root_.eq_top_iff]
    intro Y f _
    apply J₁.pullback_stable _ hS

Depends on / 依赖: _root_, _root_.eq_top_iff, eq_top_iff, pullback_stable, top_mem, transitive
-/
theorem close_eq_top_iff_mem {X : C} (S : Sieve X) : J₁.close S = ⊤ ↔ S in J₁ X := by
  constructor
  · intro h
    apply J₁.transitive (J₁.top_mem X)
    intro Y f hf
    change J₁.close S f
    rwa [h]
  · intro hS
    rw [_root_.eq_top_iff]
    intro Y f _
    apply J₁.pullback_stable _ hS

end GrothendieckTopology

variable (C) in
/-- The presheaf sending each object to the type of sieves on it. This will turn out to be a
subobject classifier for the category of presheaves. -/
@[simps]
/--
Definition of `Functor.sieves` / `Functor.sieves` 的定义

English:
definition Functor.sieves
  signature: : Cᵒᵖ ⥤ Type max v u where
  body: Sieve X.unop
  map f := ↾fun S => S.pullback f.unop

中文:
定义 Functor.sieves
  签名: : Cᵒᵖ ⥤ Type max v u where
  定义体: Sieve X.unop
  map f := ↾fun S => S.pullback f.unop

Depends on / 依赖: X.unop
-/
def Functor.sieves : Cᵒᵖ ⥤ Type max v u where
  obj X := Sieve X.unop
  map f := ↾fun S => S.pullback f.unop

/--
The presheaf sending each object to the set of `J`-closed sieves on it. This presheaf is a `J`-sheaf
(and will turn out to be a subobject classifier for the category of `J`-sheaves).
-/
@[simps]
/--
Definition of `Functor.closedSieves` / `Functor.closedSieves` 的定义

English:
definition Functor.closedSieves
  signature: : Subfunctor (Functor.sieves C) where
  body: {S : Sieve X.unop | J₁.IsClosed S}
  map f _ := J₁.isClosed_pullback f.unop _

中文:
定义 Functor.closedSieves
  签名: : Subfunctor (Functor.sieves C) where
  定义体: {S : Sieve X.unop | J₁.IsClosed S}
  map f _ := J₁.isClosed_pullback f.unop _

Depends on / 依赖: IsClosed, X.unop
-/
def Functor.closedSieves : Subfunctor (Functor.sieves C) where
  obj X := {S : Sieve X.unop | J₁.IsClosed S}
  map f _ := J₁.isClosed_pullback f.unop _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `classifier_isSheaf` / 定理 `classifier_isSheaf`

English:
theorem classifier_isSheaf
  statement: Presieve.IsSheaf J₁ (Functor.closedSieves J₁).toFunctor
  proof: by
  intro X S hS
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨?_, ?_⟩
  · rintro x ⟨M, hM⟩ ⟨N, hN⟩ hM₂ hN₂
    dsimp at S M N ⊢
    ext Y f
    dsimp only [Subtype.coe_mk]
    rw [← J₁.covers_iff_mem_of_isClosed hM]; rw [← J₁.covers_iff_mem_of_isClosed hN]
   

中文:
定理 classifier_isSheaf
  结论: Presieve.IsSheaf J₁ (Functor.closedSieves J₁).toFunctor
  证明: by
  intro X S hS
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨?_, ?_⟩
  · rintro x ⟨M, hM⟩ ⟨N, hN⟩ hM₂ hN₂
    dsimp at S M N ⊢
    ext Y f
    dsimp only [Subtype.coe_mk]
    rw [← J₁.covers_iff_mem_of_isClosed hM]; rw [← J₁.covers_iff_mem_of_isClosed hN]
   

Depends on / 依赖: M.pullback, N.pullback, Presieve, Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor, Sieve.inter_apply, Sieve.mem_iff_pu, Subtype, Subtype.coe_mk, Subtype.val, coe_mk, congr_arg, covers_iff_mem_of_isClosed, inter_apply, isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor, mem_iff_pu, pullback
-/
theorem classifier_isSheaf : Presieve.IsSheaf J₁ (Functor.closedSieves J₁).toFunctor := by
  intro X S hS
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨?_, ?_⟩
  · rintro x ⟨M, hM⟩ ⟨N, hN⟩ hM₂ hN₂
    dsimp at S M N ⊢
    ext Y f
    dsimp only [Subtype.coe_mk]
    rw [← J₁.covers_iff_mem_of_isClosed hM]; rw [← J₁.covers_iff_mem_of_isClosed hN]
    have q : forall ⦃Z : C⦄ (g : Z ⟶ X) (_ : S g), M.pullback g = N.pullback g :=
      fun Z g hg => congr_arg Subtype.val ((hM₂ g hg).trans (hN₂ g hg).symm)
    have MSNS : M ⊓ S = N ⊓ S := by
      ext
      grind [Sieve.inter_apply, Sieve.mem_iff_pullback_eq_top]
    constructor
    · intro hf
      rw [J₁.covers_iff]
      apply J₁.superset_covering (Sieve.pullback_monotone f inf_le_left)
      rw [← MSNS]
      apply J₁.arrow_intersect f M S hf (J₁.pullback_stable _ hS)
    · intro hf
      rw [J₁.covers_iff]
      apply J₁.superset_covering (Sieve.pullback_monotone f inf_le_left)
      rw [MSNS]
      apply J₁.arrow_intersect f N S hf (J₁.pullback_stable _ hS)
  · intro x hx
    rw [Presieve.compatible_iff_sieveCompatible] at hx
    let M := Sieve.bind S fun Y f hf => (x f hf).1
    have : forall ⦃Y⦄ (f : Y ⟶ X) (hf : S f), M.pullback f = (x f hf).1 := by
      intro Y f hf
      apply le_antisymm
      · rintro Z u ⟨W, g, f', hf', hg : (x f' hf').1.1 _, c⟩
        rw [Sieve.mem_iff_pullback_eq_top]; rw [← show (x (u ≫ f) _).1 = (x f hf).1.pullback u from congr_arg Subtype.val (hx f u hf)]
        conv_lhs => congr; congr; rw [← c] -- Porting note: Originally `simp_rw [← c]`
        rw [show (x (g ≫ f') _).1 = _ from congr_arg Subtype.val (hx f' g hf')]
        apply Sieve.pullback_eq_top_of_mem _ hg
      · apply Sieve.le_pullback_bind S fun Y f hf => (x f hf).1
    refine ⟨⟨_, J₁.close_isClosed M⟩, ?_⟩
    intro Y f hf
    dsimp
    ext1
    dsimp
    rw [← J₁.pullback_close]; rw [this _ hf]
    apply le_antisymm (J₁.le_close_of_isClosed le_rfl (x f hf).2) (J₁.le_close _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `GrothendieckTopology.mem_iff_isSheafFor_closedSieves` / 引理 `GrothendieckTopology.mem_iff_isSheafFor_closedSieves`

English:
lemma GrothendieckTopology.mem_iff_isSheafFor_closedSieves
  proof: by
  refine ⟨fun hS => classifier_isSheaf _ _ hS, fun H => ?_⟩
  rw [← J.close_eq_top_iff_mem]
  have : J.IsClosed (⊤ : Sieve X) := by
    intro Y f _
    trivial
  suffices (⟨J.close S, J.close_isClosed S⟩ : Subtype _) = ⟨⊤, this⟩ by
    rw [Subtype.ext_iff] at this
    exact this
  refine H.isSepa

中文:
引理 GrothendieckTopology.mem_iff_isSheafFor_closedSieves
  证明: by
  refine ⟨fun hS => classifier_isSheaf _ _ hS, fun H => ?_⟩
  rw [← J.close_eq_top_iff_mem]
  have : J.IsClosed (⊤ : Sieve X) := by
    intro Y f _
    trivial
  suffices (⟨J.close S, J.close_isClosed S⟩ : Subtype _) = ⟨⊤, this⟩ by
    rw [Subtype.ext_iff] at this
    exact this
  refine H.isSepa

Depends on / 依赖: Functor, Functor.closedSieves_obj, Functor.sieves_obj, H.isSeparatedFor.ext, IsClosed, J.IsClosed, J.close, J.close_eq_top_iff_mem, J.close_isClosed, J.pullback_close, S.pullback_eq_top_of_mem, Set.coe_ofPred, Sieve.pullback_top, Subfunctor, Subfunctor.toFunctor_obj, Subtype, Subtype.ext_iff, classifier_isSheaf, close_eq_top_iff_mem, close_isClosed
-/
lemma GrothendieckTopology.mem_iff_isSheafFor_closedSieves
    (J : GrothendieckTopology C) {X : C} (S : Sieve X) :
    S in J X ↔ Presieve.IsSheafFor (Functor.closedSieves J).toFunctor S.arrows := by
  refine ⟨fun hS => classifier_isSheaf _ _ hS, fun H => ?_⟩
  rw [← J.close_eq_top_iff_mem]
  have : J.IsClosed (⊤ : Sieve X) := by
    intro Y f _
    trivial
  suffices (⟨J.close S, J.close_isClosed S⟩ : Subtype _) = ⟨⊤, this⟩ by
    rw [Subtype.ext_iff] at this
    exact this
  refine H.isSeparatedFor.ext fun Y f hf => ?_
  simp only [Subfunctor.toFunctor_obj, Functor.sieves_obj, Functor.closedSieves_obj, Set.coe_ofPred]
  ext1
  dsimp
  rw [Sieve.pullback_top]; rw [← J.pullback_close]; rw [S.pullback_eq_top_of_mem hf]; rw [J.close_eq_top_iff_mem]
  apply J.top_mem

/--
theorem `le_topology_of_closedSieves_isSheaf` / 定理 `le_topology_of_closedSieves_isSheaf`

English:
theorem le_topology_of_closedSieves_isSheaf
  statement: {J₁ J₂ : GrothendieckTopology C}
  proof: by
  intro X S hS
  rw [GrothendieckTopology.mem_iff_isSheafFor_closedSieves]
  exact h _ hS

中文:
定理 le_topology_of_closedSieves_isSheaf
  结论: {J₁ J₂ : GrothendieckTopology C}
  证明: by
  intro X S hS
  rw [GrothendieckTopology.mem_iff_isSheafFor_closedSieves]
  exact h _ hS

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.mem_iff_isSheafFor_closedSieves, mem_iff_isSheafFor_closedSieves
-/
theorem le_topology_of_closedSieves_isSheaf {J₁ J₂ : GrothendieckTopology C}
    (h : Presieve.IsSheaf J₁ (Functor.closedSieves J₂).toFunctor) : J₁ <= J₂ := by
  intro X S hS
  rw [GrothendieckTopology.mem_iff_isSheafFor_closedSieves]
  exact h _ hS

/--
theorem `topology_eq_iff_same_sheaves` / 定理 `topology_eq_iff_same_sheaves`

English:
theorem topology_eq_iff_same_sheaves
  given: {J₁ J₂ : GrothendieckTopology C}
  proof: by
  constructor
  · rintro rfl
    intro P
    rfl
  · intro h
    apply le_antisymm
    · apply le_topology_of_closedSieves_isSheaf
      rw [h]
      apply classifier_isSheaf
    · apply le_topology_of_closedSieves_isSheaf
      rw [← h]
      apply classifier_isSheaf

中文:
定理 topology_eq_iff_same_sheaves
  条件: {J₁ J₂ : GrothendieckTopology C}
  证明: by
  constructor
  · rintro rfl
    intro P
    rfl
  · intro h
    apply le_antisymm
    · apply le_topology_of_closedSieves_isSheaf
      rw [h]
      apply classifier_isSheaf
    · apply le_topology_of_closedSieves_isSheaf
      rw [← h]
      apply classifier_isSheaf

Depends on / 依赖: classifier_isSheaf, le_antisymm, le_topology_of_closedSieves_isSheaf
-/
theorem topology_eq_iff_same_sheaves {J₁ J₂ : GrothendieckTopology C} :
    J₁ = J₂ ↔ forall P : Cᵒᵖ ⥤ Type (max v u), Presieve.IsSheaf J₁ P ↔ Presieve.IsSheaf J₂ P := by
  constructor
  · rintro rfl
    intro P
    rfl
  · intro h
    apply le_antisymm
    · apply le_topology_of_closedSieves_isSheaf
      rw [h]
      apply classifier_isSheaf
    · apply le_topology_of_closedSieves_isSheaf
      rw [← h]
      apply classifier_isSheaf

/--
A closure (increasing, inflationary and idempotent) operation on sieves that commutes with pullback
induces a Grothendieck topology.
In fact, such operations are in bijection with Grothendieck topologies.
-/
@[simps]
/--
Definition of `topologyOfClosureOperator` / `topologyOfClosureOperator` 的定义

English:
definition topologyOfClosureOperator
  signature: (c : forall X : C, ClosureOperator (Sieve X))
  body: { S | c X S = ⊤ }
  top_mem' X := top_unique ((c X).le_closure _)
  pullback_stable' X Y S f hS := by
    rw [Set.mem_ofPred_eq] at hS
    rw [Set.mem_ofPred_eq]; rw [hc]; rw [hS]; rw [Sieve.pullback_top]
  transitive' X S hS R hR := by
    rw [Set.mem_ofPred_eq] at hS
    rw [Set.mem_ofPred_eq]; rw

中文:
定义 topologyOfClosureOperator
  签名: (c : 对任意 X : C, ClosureOperator (Sieve X))
  定义体: { S | c X S = ⊤ }
  top_mem' X := top_unique ((c X).le_closure _)
  pullback_stable' X Y S f hS := by
    rw [Set.mem_ofPred_eq] at hS
    rw [Set.mem_ofPred_eq]; rw [hc]; rw [hS]; rw [Sieve.pullback_top]
  transitive' X S hS R hR := by
    rw [Set.mem_ofPred_eq] at hS
    rw [Set.mem_ofPred_eq]; rw
-/
def topologyOfClosureOperator (c : forall X : C, ClosureOperator (Sieve X))
    (hc : forall ⦃X Y : C⦄ (f : Y ⟶ X) (S : Sieve X), c _ (S.pullback f) = (c _ S).pullback f) :
    GrothendieckTopology C where
  sieves X := { S | c X S = ⊤ }
  top_mem' X := top_unique ((c X).le_closure _)
  pullback_stable' X Y S f hS := by
    rw [Set.mem_ofPred_eq] at hS
    rw [Set.mem_ofPred_eq]; rw [hc]; rw [hS]; rw [Sieve.pullback_top]
  transitive' X S hS R hR := by
    rw [Set.mem_ofPred_eq] at hS
    rw [Set.mem_ofPred_eq]; rw [← (c X).idempotent]; rw [eq_top_iff]; rw [← hS]
    apply (c X).monotone fun Y f hf => _
    intro Y f hf
    rw [Sieve.mem_iff_pullback_eq_top]; rw [← hc]
    apply hR hf

/--
theorem `topologyOfClosureOperator_self` / 定理 `topologyOfClosureOperator_self`

English:
theorem topologyOfClosureOperator_self
  proof: by
  ext X S
  apply GrothendieckTopology.close_eq_top_iff_mem

中文:
定理 topologyOfClosureOperator_self
  证明: by
  ext X S
  apply GrothendieckTopology.close_eq_top_iff_mem

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.close_eq_top_iff_mem, close_eq_top_iff_mem
-/
theorem topologyOfClosureOperator_self :
    (topologyOfClosureOperator J₁.closureOperator fun _ _ => J₁.pullback_close) = J₁ := by
  ext X S
  apply GrothendieckTopology.close_eq_top_iff_mem

/--
theorem `topologyOfClosureOperator_close` / 定理 `topologyOfClosureOperator_close`

English:
theorem topologyOfClosureOperator_close
  statement: (c : forall X : C, ClosureOperator (Sieve X))
  proof: by
  ext Y f
  change c _ (Sieve.pullback f S) = ⊤ ↔ c _ S f
  rw [pb]; rw [Sieve.mem_iff_pullback_eq_top]

中文:
定理 topologyOfClosureOperator_close
  结论: (c : 对任意 X : C, ClosureOperator (Sieve X))
  证明: by
  ext Y f
  change c _ (Sieve.pullback f S) = ⊤ ↔ c _ S f
  rw [pb]; rw [Sieve.mem_iff_pullback_eq_top]

Depends on / 依赖: Sieve.mem_iff_pullback_eq_top, Sieve.pullback, mem_iff_pullback_eq_top, pullback
-/
theorem topologyOfClosureOperator_close (c : forall X : C, ClosureOperator (Sieve X))
    (pb : forall ⦃X Y : C⦄ (f : Y ⟶ X) (S : Sieve X), c Y (S.pullback f) = (c X S).pullback f) (X : C)
    (S : Sieve X) : (topologyOfClosureOperator c pb).close S = c X S := by
  ext Y f
  change c _ (Sieve.pullback f S) = ⊤ ↔ c _ S f
  rw [pb]; rw [Sieve.mem_iff_pullback_eq_top]

end CategoryTheory
