/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Control.Basic

/-!
# Free abelian groups

The free abelian group on a type `α`, defined as the abelianisation of
the free group on `α`.

The free abelian group on `α` can be abstractly defined as the left adjoint of the
forgetful functor from abelian groups to types. Alternatively, one could define
it as the functions `α → ℤ` which send all but finitely many `(a : α)` to `0`,
under pointwise addition. In this file, it is defined as the abelianisation
of the free group on `α`. All the constructions and theorems required to show
the adjointness of the construction and the forgetful functor are proved in this
file, but the category-theoretic adjunction statement is in
`Mathlib/Algebra/Category/Grp/Adjunctions.lean`.

## Main definitions

Here we use the following variables: `(α β : Type*) (A : Type*) [AddCommGroup A]`

* `FreeAbelianGroup α` : the free abelian group on a type `α`. As an abelian
  group it is `α →₀ ℤ`, the functions from `α` to `ℤ` such that all but finitely
  many elements get mapped to zero, however this is not how it is implemented.

* `lift f : FreeAbelianGroup α →+ A` : the group homomorphism induced
  by the map `f : α → A`.

* `map (f : α → β) : FreeAbelianGroup α →+ FreeAbelianGroup β` : functoriality
    of `FreeAbelianGroup`.

* `instance [Monoid α] : Semigroup (FreeAbelianGroup α)`

* `instance [CommMonoid α] : CommRing (FreeAbelianGroup α)`

It has been suggested that we would be better off refactoring this file
and using `Finsupp` instead.

## Implementation issues

The definition is `def FreeAbelianGroup : Type u := Additive <| Abelianization <| FreeGroup α`.

Chris Hughes has suggested that this all be rewritten in terms of `Finsupp`.
Johan Commelin has written all the API relating the definition to `Finsupp`
in the lean-liquid repo.

The lemmas `map_pure`, `map_of`, `map_zero`, `map_add`, `map_neg` and `map_sub`
are proved about the `Functor.map` `<$>` construction, and need `α` and `β` to
be in the same universe. But
`FreeAbelianGroup.map (f : α → β)` is defined to be the `AddGroup`
homomorphism `FreeAbelianGroup α →+ FreeAbelianGroup β` (with `α` and `β` now
allowed to be in different universes), so `(map f).map_add`
etc. can be used to prove that `FreeAbelianGroup.map` preserves addition. The
functions `map_id`, `map_id_apply`, `map_comp`, `map_comp_apply` and `map_of_apply`
are about `FreeAbelianGroup.map`.

-/

@[expose] public section

assert_not_exists Cardinal Multiset

universe u v

variable (α : Type u) {G : Type*}

/--
Definition of `FreeAbelianGroup` / `FreeAbelianGroup` 的定义

English:
definition FreeAbelianGroup
  signature: : Type u
  body: Additive Abelianization FreeGroup α
deriving Inhabited, AddCommGroup

中文:
定义 自由交换群
  签名: : 类型u
  定义体: Additive Abelianization FreeGroup α
deriving Inhabited, AddCommGroup

Depends on / 依赖: Abelianization, Additive, FreeGroup
-/
def FreeAbelianGroup : Type u :=
Additive Abelianization FreeGroup α
deriving Inhabited, AddCommGroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : Unique (FreeAbelianGroup α)
  body: inferInstanceAs Unique (delta% FreeAbelianGroup α)

中文:
实例 [是空
  签名: α] : 唯一 (自由交换群 α)
  定义体: inferInstanceAs Unique (delta% FreeAbelianGroup α)

Depends on / 依赖: FreeAbelianGroup, Unique
-/
instance [IsEmpty α] : Unique (FreeAbelianGroup α) :=
inferInstanceAs Unique (delta% FreeAbelianGroup α)

variable {α}

namespace FreeAbelianGroup

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (x : α)
  body: Additive.ofMul Abelianization.of FreeGroup.of x

中文:
定义 of
  签名: (x : α)
  定义体: Additive.ofMul Abelianization.of FreeGroup.of x

Depends on / 依赖: Abelianization, Abelianization.of, Additive, Additive.ofMul, FreeGroup, FreeGroup.of
-/
def of (x : α) : FreeAbelianGroup α :=
Additive.ofMul Abelianization.of FreeGroup.of x

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {β : Type v} [AddCommGroup β]
  body: (@FreeGroup.lift _ (Multiplicative β) _).trans
    (@Abelianization.lift _ _ (Multiplicative β) _).trans MonoidHom.toAdditive

中文:
定义 lift
  签名: {β : 类型v} [加法交换群 β]
  定义体: (@FreeGroup.lift _ (Multiplicative β) _).trans
    (@Abelianization.lift _ _ (Multiplicative β) _).trans MonoidHom.toAdditive

Depends on / 依赖: Abelianization, Abelianization.lift, FreeGroup, FreeGroup.lift, MonoidHom, MonoidHom.toAdditive, Multiplicative, toAdditive
-/
def lift {β : Type v} [AddCommGroup β] : (α -> β) ≃ (FreeAbelianGroup α ->+ β) :=
(@FreeGroup.lift _ (Multiplicative β) _).trans
    (@Abelianization.lift _ _ (Multiplicative β) _).trans MonoidHom.toAdditive

section lift

variable {β : Type v} [AddCommGroup β] (f : α -> β)

open FreeAbelianGroup

-- Porting note: needed to add `(β := Multiplicative β)`
@[simp]
/--
theorem `lift_apply_of` / 定理 `lift_apply_of`

English:
theorem lift_apply_of
  given: (x : α)
  statement: lift f (of x) = f x
  proof: by
  convert! Abelianization.lift_apply_of (FreeGroup.lift f (β := Multiplicative β)) (FreeGroup.of x)
  exact (FreeGroup.lift_apply_of (β := Multiplicative β)).symm

中文:
定理 lift_apply_of
  条件: (x : α)
  结论: lift f (of x) = f x
  证明: by
  convert! Abelianization.lift_apply_of (FreeGroup.lift f (β := Multiplicative β)) (FreeGroup.of x)
  exact (FreeGroup.lift_apply_of (β := Multiplicative β)).symm

Depends on / 依赖: Abelianization, Abelianization.lift_apply_of, FreeGroup, FreeGroup.lift, FreeGroup.lift_apply_of, FreeGroup.of, Multiplicative, convert, lift_apply_of
-/
theorem lift_apply_of (x : α) : lift f (of x) = f x := by
  convert! Abelianization.lift_apply_of (FreeGroup.lift f (β := Multiplicative β)) (FreeGroup.of x)
  exact (FreeGroup.lift_apply_of (β := Multiplicative β)).symm

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (g : FreeAbelianGroup α ->+ β) (hg : forall x, g (of x) = f x) {x}
  proof: DFunLike.congr_fun (lift.symm_apply_eq.mp (funext hg : g ∘ of = f)) _

中文:
定理 lift_unique
  条件: (g : 自由交换群 α ->+ β) (hg : 对任意 x, g (of x) = f x) {x}
  证明: DFunLike.congr_fun (lift.symm_apply_eq.mp (funext hg : g ∘ of = f)) _

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, lift.symm_apply_eq.mp, symm_apply_eq
-/
theorem lift_unique (g : FreeAbelianGroup α ->+ β) (hg : forall x, g (of x) = f x) {x} :
    g x = lift f x :=
  DFunLike.congr_fun (lift.symm_apply_eq.mp (funext hg : g ∘ of = f)) _

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
/--
theorem `lift_ext` / 定理 `lift_ext`

English:
theorem lift_ext
  given: (g h : FreeAbelianGroup α ->+ β) (H : forall x, g (of x) = h (of x))
  statement: g = h
  proof: lift.symm.injective funext H

中文:
定理 lift_ext
  条件: (g h : 自由交换群 α ->+ β) (H : 对任意 x, g (of x) = h (of x))
  结论: g = h
  证明: lift.symm.injective funext H

Depends on / 依赖: injective, lift.symm.injective
-/
theorem lift_ext (g h : FreeAbelianGroup α ->+ β) (H : forall x, g (of x) = h (of x)) : g = h :=
lift.symm.injective funext H

/--
theorem `lift_comp_apply` / 定理 `lift_comp_apply`

English:
theorem lift_comp_apply
  statement: {α β γ} [AddCommGroup β] [AddCommGroup γ]
  proof: by
  rw [← AddMonoidHom.comp_apply g (lift f)]
  refine (lift_unique _ _ ?_).symm
  intro a
  change g ((lift f) (of a)) = g (f a)
  simp only [lift_apply_of]

中文:
定理 lift_comp_apply
  结论: {α β γ} [加法交换群 β] [加法交换群 γ]
  证明: by
  rw [← AddMonoidHom.comp_apply g (lift f)]
  refine (lift_unique _ _ ?_).symm
  intro a
  change g ((lift f) (of a)) = g (f a)
  simp only [lift_apply_of]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.comp_apply, comp_apply, lift_apply_of, lift_unique
-/
theorem lift_comp_apply {α β γ} [AddCommGroup β] [AddCommGroup γ]
    (a : FreeAbelianGroup α) (f : α -> β) (g : β ->+ γ) : lift (g ∘ f) a = g (lift f a) := by
  rw [← AddMonoidHom.comp_apply g (lift f)]
  refine (lift_unique _ _ ?_).symm
  intro a
  change g ((lift f) (of a)) = g (f a)
  simp only [lift_apply_of]

end lift

section

/--
theorem `of_injective` / 定理 `of_injective`

English:
theorem of_injective
  statement: Function.Injective (of : α -> FreeAbelianGroup α)
  proof: by
  classical
  exact fun x y hoxy => Classical.by_contradiction fun hxy : x != y =>
    let f : FreeAbelianGroup α ->+ Int := lift fun z => if x = z then (1 : Int) else 0
have hfx1 : f (of x) = 1 := (lift_apply_of _ _).trans if_pos rfl
    have hfy1 : f (of y) = 1 := hoxy ▸ hfx1
have hfy0 : f (of 

中文:
定理 of_injective
  结论: 函数.单射 (of : α -> 自由交换群 α)
  证明: by
  classical
  exact fun x y hoxy => Classical.by_contradiction fun hxy : x != y =>
    let f : FreeAbelianGroup α ->+ Int := lift fun z => if x = z then (1 : Int) else 0
have hfx1 : f (of x) = 1 := (lift_apply_of _ _).trans if_pos rfl
    have hfy1 : f (of y) = 1 := hoxy ▸ hfx1
have hfy0 : f (of 

Depends on / 依赖: Classical, Classical.by_contradiction, FreeAbelianGroup, by_contradiction, classical, hfy1.symm.trans, if_neg, if_pos, lift_apply_of, one_ne_zero
-/
theorem of_injective : Function.Injective (of : α -> FreeAbelianGroup α) := by
  classical
  exact fun x y hoxy => Classical.by_contradiction fun hxy : x != y =>
    let f : FreeAbelianGroup α ->+ Int := lift fun z => if x = z then (1 : Int) else 0
have hfx1 : f (of x) = 1 := (lift_apply_of _ _).trans if_pos rfl
    have hfy1 : f (of y) = 1 := hoxy ▸ hfx1
have hfy0 : f (of y) = 0 := (lift_apply_of _ _).trans if_neg hxy
one_ne_zero hfy1.symm.trans hfy0

@[simp]
/--
theorem `of_ne_zero` / 定理 `of_ne_zero`

English:
theorem of_ne_zero
  given: (x : α)
  statement: of x != 0
  proof: by
  intro h
  let f : FreeAbelianGroup α ->+ Int := lift 1
  have hfx : f (of x) = 1 := lift_apply_of _ _
  have hf0 : f (of x) = 0 := by rw [h, map_zero]
exact one_ne_zero hfx.symm.trans hf0

@[simp]
.symm theorem zero_ne_of (x : α) : 0 != of x := of_ne_zero _

中文:
定理 of_ne_zero
  条件: (x : α)
  结论: of x != 0
  证明: by
  intro h
  let f : FreeAbelianGroup α ->+ Int := lift 1
  have hfx : f (of x) = 1 := lift_apply_of _ _
  have hf0 : f (of x) = 0 := by rw [h, map_zero]
exact one_ne_zero hfx.symm.trans hf0

@[simp]
.symm theorem zero_ne_of (x : α) : 0 != of x := of_ne_zero _

Depends on / 依赖: FreeAbelianGroup, hfx.symm.trans, lift_apply_of, map_zero, one_ne_zero
-/
theorem of_ne_zero (x : α) : of x != 0 := by
  intro h
  let f : FreeAbelianGroup α ->+ Int := lift 1
  have hfx : f (of x) = 1 := lift_apply_of _ _
  have hf0 : f (of x) = 0 := by rw [h, map_zero]
exact one_ne_zero hfx.symm.trans hf0

@[simp]
.symm theorem zero_ne_of (x : α) : 0 != of x := of_ne_zero _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nontrivial (FreeAbelianGroup α) where
  body: let ⟨x⟩ := ‹Nonempty α›; ⟨0, of x, zero_ne_of _⟩

中文:
实例 [非空
  签名: α] : 非平凡 (自由交换群 α) where
  定义体: let ⟨x⟩ := ‹Nonempty α›; ⟨0, of x, zero_ne_of _⟩

Depends on / 依赖: Nonempty, zero_ne_of
-/
instance [Nonempty α] : Nontrivial (FreeAbelianGroup α) where
  exists_pair_ne := let ⟨x⟩ := ‹Nonempty α›; ⟨0, of x, zero_ne_of _⟩

end

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  proof: Quotient.inductionOn' z fun x => Quot.inductionOn x fun L =>
    List.recOn L zero fun ⟨x, b⟩ _ ih => Bool.recOn b (add _ _ (neg _ (of x)) ih) (add _ _ (of x) ih)

中文:
定理 induction_on
  证明: Quotient.inductionOn' z fun x => Quot.inductionOn x fun L =>
    List.recOn L zero fun ⟨x, b⟩ _ ih => Bool.recOn b (add _ _ (neg _ (of x)) ih) (add _ _ (of x) ih)
-/
protected theorem induction_on
    {motive : FreeAbelianGroup α -> Prop} (z : FreeAbelianGroup α) (zero : motive 0)
    (of : forall x, motive (of x)) (neg : forall x, motive (.of x) -> motive (-.of x))
    (add : forall x y, motive x -> motive y -> motive (x + y)) : motive z :=
  Quotient.inductionOn' z fun x => Quot.inductionOn x fun L =>
    List.recOn L zero fun ⟨x, b⟩ _ ih => Bool.recOn b (add _ _ (neg _ (of x)) ih) (add _ _ (of x) ih)

/--
theorem `lift_add_apply` / 定理 `lift_add_apply`

English:
theorem lift_add_apply
  given: [AddCommGroup G] (f g : α -> G) (a : FreeAbelianGroup α)
  proof: by
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp only [(lift _).map_zero, zero_add]
  | of x => simp only [lift_apply_of, Pi.add_apply]
  | neg x => simp only [map_neg, lift_apply_of, Pi.add_apply, neg_add]
  | add x y hx hy => simp only [(lift _).map_add, hx, hy, add_add_a

中文:
定理 lift_add_apply
  条件: [加法交换群 G] (f g : α -> G) (a : 自由交换群 α)
  证明: by
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp only [(lift _).map_zero, zero_add]
  | of x => simp only [lift_apply_of, Pi.add_apply]
  | neg x => simp only [map_neg, lift_apply_of, Pi.add_apply, neg_add]
  | add x y hx hy => simp only [(lift _).map_add, hx, hy, add_add_a

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.induction_on, Pi.add_apply, add_add_add_comm, add_apply, induction_on, lift_apply_of, map_add, map_neg, map_zero, neg_add, zero_add
-/
theorem lift_add_apply [AddCommGroup G] (f g : α -> G) (a : FreeAbelianGroup α) :
    lift (f + g) a = lift f a + lift g a := by
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp only [(lift _).map_zero, zero_add]
  | of x => simp only [lift_apply_of, Pi.add_apply]
  | neg x => simp only [map_neg, lift_apply_of, Pi.add_apply, neg_add]
  | add x y hx hy => simp only [(lift _).map_add, hx, hy, add_add_add_comm]

/--
lemma `lift_add` / 引理 `lift_add`

English:
lemma lift_add
  given: [AddCommGroup G] (f g : α -> G)
  statement: lift (f + g) = lift f + lift g
  proof: AddMonoidHom.ext lift_add_apply _ _

#adaptation_note

中文:
引理 lift_add
  条件: [加法交换群 G] (f g : α -> G)
  结论: lift (f + g) = lift f + lift g
  证明: AddMonoidHom.ext lift_add_apply _ _

#adaptation_note
-/
@[simp] lemma lift_add [AddCommGroup G] (f g : α -> G) : lift (f + g) = lift f + lift g :=
AddMonoidHom.ext lift_add_apply _ _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- `FreeAbelianGroup.lift` as an equivalence of groups. -/
@[simps!]
/--
Definition of `liftAddEquiv` / `liftAddEquiv` 的定义

English:
definition liftAddEquiv
  signature: [AddCommGroup G]
  body: ⟨lift, lift_add⟩

中文:
定义 liftAddEquiv
  签名: [加法交换群 G]
  定义体: ⟨lift, lift_add⟩

Depends on / 依赖: lift_add
-/
def liftAddEquiv [AddCommGroup G] : (α -> G) ≃+ (FreeAbelianGroup α ->+ G) := ⟨lift, lift_add⟩

/-- If `g : FreeAbelianGroup X` and `A` is an abelian group then `liftAddGroupHom g`
is the additive group homomorphism sending a function `X → A` to the term of type `A`
corresponding to the evaluation of the induced map `FreeAbelianGroup X → A` at `g`. -/
@[simps!]
/--
Definition of `liftAddGroupHom` / `liftAddGroupHom` 的定义

English:
definition liftAddGroupHom
  signature: {α} (β) [AddCommGroup β] (a : FreeAbelianGroup α)
  body: AddMonoidHom.mk' (fun f => lift f a) (lift_add_apply · · _)

中文:
定义 liftAddGroupHom
  签名: {α} (β) [加法交换群 β] (a : 自由交换群 α)
  定义体: AddMonoidHom.mk' (fun f => lift f a) (lift_add_apply · · _)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, lift_add_apply
-/
def liftAddGroupHom {α} (β) [AddCommGroup β] (a : FreeAbelianGroup α) : (α -> β) ->+ β :=
  AddMonoidHom.mk' (fun f => lift f a) (lift_add_apply · · _)

/--
lemma `lift_neg` / 引理 `lift_neg`

English:
lemma lift_neg
  given: [AddCommGroup G] (f : α -> G)
  statement: lift (-f) = -lift f
  proof: liftAddEquiv.map_neg f

中文:
引理 lift_neg
  条件: [加法交换群 G] (f : α -> G)
  结论: lift (-f) = -lift f
  证明: liftAddEquiv.map_neg f
-/
@[simp] lemma lift_neg [AddCommGroup G] (f : α -> G) : lift (-f) = -lift f := liftAddEquiv.map_neg f

/--
lemma `lift_neg_apply` / 引理 `lift_neg_apply`

English:
lemma lift_neg_apply
  given: [AddCommGroup G] (f : α -> G) (a : FreeAbelianGroup α)
  proof: congr($(lift_neg f) a)

中文:
引理 lift_neg_apply
  条件: [加法交换群 G] (f : α -> G) (a : 自由交换群 α)
  证明: congr($(lift_neg f) a)

Depends on / 依赖: lift_neg
-/
lemma lift_neg_apply [AddCommGroup G] (f : α -> G) (a : FreeAbelianGroup α) :
    lift (-f) a = -lift f a := congr($(lift_neg f) a)

section Monad

variable {β : Type u}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monad FreeAbelianGroup.{u}
  body: of α
  bind x f := lift f x

@[elab_as_elim]

中文:
实例 :
  签名: 单子 自由交换群.{u}
  定义体: of α
  bind x f := lift f x

@[elab_as_elim]
-/
instance : Monad FreeAbelianGroup.{u} where
  pure α := of α
  bind x f := lift f x

@[elab_as_elim]
/--
theorem `induction_on'` / 定理 `induction_on'`

English:
theorem induction_on'
  proof: FreeAbelianGroup.induction_on z zero pure neg add

@[simp]

中文:
定理 induction_on'
  证明: FreeAbelianGroup.induction_on z zero pure neg add

@[simp]
-/
protected theorem induction_on'
    {motive : FreeAbelianGroup α -> Prop} (z : FreeAbelianGroup α) (zero : motive 0)
    (pure : forall x, motive <| pure x) (neg : forall x, motive (Pure.pure x) -> motive (-Pure.pure x))
    (add : forall x y, motive x -> motive y -> motive (x + y)) : motive z :=
  FreeAbelianGroup.induction_on z zero pure neg add

@[simp]
/--
theorem `map_pure` / 定理 `map_pure`

English:
theorem map_pure
  given: (f : α -> β) (x : α)
  statement: f < > (pure x : FreeAbelianGroup α) = pure (f x)
  proof: rfl

@[simp]

中文:
定理 map_pure
  条件: (f : α -> β) (x : α)
  结论: f < > (pure x : 自由交换群 α) = pure (f x)
  证明: rfl

@[simp]
-/
theorem map_pure (f : α -> β) (x : α) : f < > (pure x : FreeAbelianGroup α) = pure (f x) :=
  rfl

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (f : α -> β)
  statement: f < > (0 : FreeAbelianGroup α) = 0
  proof: (lift (of ∘ f)).map_zero

@[simp]

中文:
定理 map_zero
  条件: (f : α -> β)
  结论: f < > (0 : 自由交换群 α) = 0
  证明: (lift (of ∘ f)).map_zero

@[simp]
-/
protected theorem map_zero (f : α -> β) : f < > (0 : FreeAbelianGroup α) = 0 :=
  (lift (of ∘ f)).map_zero

@[simp]
/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (f : α -> β) (x y : FreeAbelianGroup α)
  proof: (lift _).map_add _ _

@[simp]

中文:
定理 map_add
  条件: (f : α -> β) (x y : 自由交换群 α)
  证明: (lift _).map_add _ _

@[simp]
-/
protected theorem map_add (f : α -> β) (x y : FreeAbelianGroup α) :
f < > (x + y) = f < > x + f < > y :=
  (lift _).map_add _ _

@[simp]
/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: (f : α -> β) (x : FreeAbelianGroup α)
  statement: f < > (-x) = -f < > x
  proof: map_neg (lift <| of ∘ f) _

@[simp]

中文:
定理 map_neg
  条件: (f : α -> β) (x : 自由交换群 α)
  结论: f < > (-x) = -f < > x
  证明: map_neg (lift <| of ∘ f) _

@[simp]
-/
protected theorem map_neg (f : α -> β) (x : FreeAbelianGroup α) : f < > (-x) = -f < > x :=
  map_neg (lift <| of ∘ f) _

@[simp]
/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: (f : α -> β) (x y : FreeAbelianGroup α)
  proof: map_sub (lift <| of ∘ f) _ _

@[simp]

中文:
定理 map_sub
  条件: (f : α -> β) (x y : 自由交换群 α)
  证明: map_sub (lift <| of ∘ f) _ _

@[simp]
-/
protected theorem map_sub (f : α -> β) (x y : FreeAbelianGroup α) :
f < > (x - y) = f < > x - f < > y :=
  map_sub (lift <| of ∘ f) _ _

@[simp]
/--
theorem `map_of` / 定理 `map_of`

English:
theorem map_of
  given: (f : α -> β) (y : α)
  statement: f < > of y = of (f y)
  proof: rfl

中文:
定理 map_of
  条件: (f : α -> β) (y : α)
  结论: f < > of y = of (f y)
  证明: rfl
-/
theorem map_of (f : α -> β) (y : α) : f < > of y = of (f y) :=
  rfl

/--
theorem `pure_bind` / 定理 `pure_bind`

English:
theorem pure_bind
  given: (f : α -> FreeAbelianGroup β) (x)
  statement: pure x >>= f = f x
  proof: lift_apply_of _ _

@[simp]

中文:
定理 pure_bind
  条件: (f : α -> 自由交换群 β) (x)
  结论: pure x >>= f = f x
  证明: lift_apply_of _ _

@[simp]

Depends on / 依赖: lift_apply_of
-/
theorem pure_bind (f : α -> FreeAbelianGroup β) (x) : pure x >>= f = f x :=
  lift_apply_of _ _

@[simp]
/--
theorem `zero_bind` / 定理 `zero_bind`

English:
theorem zero_bind
  given: (f : α -> FreeAbelianGroup β)
  statement: 0 >>= f = 0
  proof: (lift f).map_zero

@[simp]

中文:
定理 zero_bind
  条件: (f : α -> 自由交换群 β)
  结论: 0 >>= f = 0
  证明: (lift f).map_zero

@[simp]

Depends on / 依赖: map_zero
-/
theorem zero_bind (f : α -> FreeAbelianGroup β) : 0 >>= f = 0 :=
  (lift f).map_zero

@[simp]
/--
theorem `add_bind` / 定理 `add_bind`

English:
theorem add_bind
  given: (f : α -> FreeAbelianGroup β) (x y : FreeAbelianGroup α)
  proof: (lift _).map_add _ _

@[simp]

中文:
定理 add_bind
  条件: (f : α -> 自由交换群 β) (x y : 自由交换群 α)
  证明: (lift _).map_add _ _

@[simp]

Depends on / 依赖: map_add
-/
theorem add_bind (f : α -> FreeAbelianGroup β) (x y : FreeAbelianGroup α) :
    x + y >>= f = (x >>= f) + (y >>= f) :=
  (lift _).map_add _ _

@[simp]
/--
theorem `neg_bind` / 定理 `neg_bind`

English:
theorem neg_bind
  given: (f : α -> FreeAbelianGroup β) (x : FreeAbelianGroup α)
  statement: -x >>= f = -(x >>= f)
  proof: map_neg (lift f) _

@[simp]

中文:
定理 neg_bind
  条件: (f : α -> 自由交换群 β) (x : 自由交换群 α)
  结论: -x >>= f = -(x >>= f)
  证明: map_neg (lift f) _

@[simp]

Depends on / 依赖: map_neg
-/
theorem neg_bind (f : α -> FreeAbelianGroup β) (x : FreeAbelianGroup α) : -x >>= f = -(x >>= f) :=
  map_neg (lift f) _

@[simp]
/--
theorem `sub_bind` / 定理 `sub_bind`

English:
theorem sub_bind
  given: (f : α -> FreeAbelianGroup β) (x y : FreeAbelianGroup α)
  proof: map_sub (lift f) _ _

@[simp]

中文:
定理 sub_bind
  条件: (f : α -> 自由交换群 β) (x y : 自由交换群 α)
  证明: map_sub (lift f) _ _

@[simp]

Depends on / 依赖: map_sub
-/
theorem sub_bind (f : α -> FreeAbelianGroup β) (x y : FreeAbelianGroup α) :
    x - y >>= f = (x >>= f) - (y >>= f) :=
  map_sub (lift f) _ _

@[simp]
/--
theorem `pure_seq` / 定理 `pure_seq`

English:
theorem pure_seq
  given: (f : α -> β) (x : FreeAbelianGroup α)
  statement: pure f <*> x = f < > x
  proof: pure_bind _ _

@[simp]

中文:
定理 pure_seq
  条件: (f : α -> β) (x : 自由交换群 α)
  结论: pure f <*> x = f < > x
  证明: pure_bind _ _

@[simp]

Depends on / 依赖: pure_bind
-/
theorem pure_seq (f : α -> β) (x : FreeAbelianGroup α) : pure f <*> x = f < > x :=
  pure_bind _ _

@[simp]
/--
theorem `zero_seq` / 定理 `zero_seq`

English:
theorem zero_seq
  given: (x : FreeAbelianGroup α)
  statement: (0 : FreeAbelianGroup (α -> β)) <*> x = 0
  proof: zero_bind _

@[simp]

中文:
定理 zero_seq
  条件: (x : 自由交换群 α)
  结论: (0 : 自由交换群 (α -> β)) <*> x = 0
  证明: zero_bind _

@[simp]

Depends on / 依赖: zero_bind
-/
theorem zero_seq (x : FreeAbelianGroup α) : (0 : FreeAbelianGroup (α -> β)) <*> x = 0 :=
  zero_bind _

@[simp]
/--
theorem `add_seq` / 定理 `add_seq`

English:
theorem add_seq
  given: (f g : FreeAbelianGroup (α -> β)) (x : FreeAbelianGroup α)
  proof: add_bind _ _ _

@[simp]

中文:
定理 add_seq
  条件: (f g : 自由交换群 (α -> β)) (x : 自由交换群 α)
  证明: add_bind _ _ _

@[simp]

Depends on / 依赖: add_bind
-/
theorem add_seq (f g : FreeAbelianGroup (α -> β)) (x : FreeAbelianGroup α) :
    f + g <*> x = (f <*> x) + (g <*> x) :=
  add_bind _ _ _

@[simp]
/--
theorem `neg_seq` / 定理 `neg_seq`

English:
theorem neg_seq
  given: (f : FreeAbelianGroup (α -> β)) (x : FreeAbelianGroup α)
  statement: -f <*> x = -(f <*> x)
  proof: neg_bind _ _

@[simp]

中文:
定理 neg_seq
  条件: (f : 自由交换群 (α -> β)) (x : 自由交换群 α)
  结论: -f <*> x = -(f <*> x)
  证明: neg_bind _ _

@[simp]

Depends on / 依赖: neg_bind
-/
theorem neg_seq (f : FreeAbelianGroup (α -> β)) (x : FreeAbelianGroup α) : -f <*> x = -(f <*> x) :=
  neg_bind _ _

@[simp]
/--
theorem `sub_seq` / 定理 `sub_seq`

English:
theorem sub_seq
  given: (f g : FreeAbelianGroup (α -> β)) (x : FreeAbelianGroup α)
  proof: sub_bind _ _ _

中文:
定理 sub_seq
  条件: (f g : 自由交换群 (α -> β)) (x : 自由交换群 α)
  证明: sub_bind _ _ _

Depends on / 依赖: sub_bind
-/
theorem sub_seq (f g : FreeAbelianGroup (α -> β)) (x : FreeAbelianGroup α) :
    f - g <*> x = (f <*> x) - (g <*> x) :=
  sub_bind _ _ _

/--
Definition of `seqAddGroupHom` / `seqAddGroupHom` 的定义

English:
definition seqAddGroupHom
  signature: (f : FreeAbelianGroup (α -> β))
  body: by
  refine .mk' (f <*> ·) fun x y => ?_
  change lift (· <$> (x + y)) _ = lift (· <$> x) _ + lift (· <$> y) _
  simp [← Pi.add_def]

@[simp]

中文:
定义 seqAddGroupHom
  签名: (f : 自由交换群 (α -> β))
  定义体: by
  refine .mk' (f <*> ·) fun x y => ?_
  change lift (· <$> (x + y)) _ = lift (· <$> x) _ + lift (· <$> y) _
  simp [← Pi.add_def]

@[simp]

Depends on / 依赖: Pi.add_def, add_def
-/
def seqAddGroupHom (f : FreeAbelianGroup (α -> β)) : FreeAbelianGroup α ->+ FreeAbelianGroup β := by
  refine .mk' (f <*> ·) fun x y => ?_
  change lift (· <$> (x + y)) _ = lift (· <$> x) _ + lift (· <$> y) _
  simp [← Pi.add_def]

@[simp]
/--
theorem `seq_zero` / 定理 `seq_zero`

English:
theorem seq_zero
  given: (f : FreeAbelianGroup (α -> β))
  statement: f <*> 0 = 0
  proof: (seqAddGroupHom f).map_zero

@[simp]

中文:
定理 seq_zero
  条件: (f : 自由交换群 (α -> β))
  结论: f <*> 0 = 0
  证明: (seqAddGroupHom f).map_zero

@[simp]

Depends on / 依赖: map_zero, seqAddGroupHom
-/
theorem seq_zero (f : FreeAbelianGroup (α -> β)) : f <*> 0 = 0 :=
  (seqAddGroupHom f).map_zero

@[simp]
/--
theorem `seq_add` / 定理 `seq_add`

English:
theorem seq_add
  given: (f : FreeAbelianGroup (α -> β)) (x y : FreeAbelianGroup α)
  proof: (seqAddGroupHom f).map_add x y

@[simp]

中文:
定理 seq_add
  条件: (f : 自由交换群 (α -> β)) (x y : 自由交换群 α)
  证明: (seqAddGroupHom f).map_add x y

@[simp]

Depends on / 依赖: map_add, seqAddGroupHom
-/
theorem seq_add (f : FreeAbelianGroup (α -> β)) (x y : FreeAbelianGroup α) :
    f <*> x + y = (f <*> x) + (f <*> y) :=
  (seqAddGroupHom f).map_add x y

@[simp]
/--
theorem `seq_neg` / 定理 `seq_neg`

English:
theorem seq_neg
  given: (f : FreeAbelianGroup (α -> β)) (x : FreeAbelianGroup α)
  statement: f <*> -x = -(f <*> x)
  proof: (seqAddGroupHom f).map_neg x

@[simp]

中文:
定理 seq_neg
  条件: (f : 自由交换群 (α -> β)) (x : 自由交换群 α)
  结论: f <*> -x = -(f <*> x)
  证明: (seqAddGroupHom f).map_neg x

@[simp]

Depends on / 依赖: map_neg, seqAddGroupHom
-/
theorem seq_neg (f : FreeAbelianGroup (α -> β)) (x : FreeAbelianGroup α) : f <*> -x = -(f <*> x) :=
  (seqAddGroupHom f).map_neg x

@[simp]
/--
theorem `seq_sub` / 定理 `seq_sub`

English:
theorem seq_sub
  given: (f : FreeAbelianGroup (α -> β)) (x y : FreeAbelianGroup α)
  proof: (seqAddGroupHom f).map_sub x y

中文:
定理 seq_sub
  条件: (f : 自由交换群 (α -> β)) (x y : 自由交换群 α)
  证明: (seqAddGroupHom f).map_sub x y

Depends on / 依赖: map_sub, seqAddGroupHom
-/
theorem seq_sub (f : FreeAbelianGroup (α -> β)) (x y : FreeAbelianGroup α) :
    f <*> x - y = (f <*> x) - (f <*> y) :=
  (seqAddGroupHom f).map_sub x y

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMonad FreeAbelianGroup.{u}
  body: LawfulMonad.mk'
  (id_map := fun x => FreeAbelianGroup.induction_on' x (FreeAbelianGroup.map_zero id) (map_pure id)
    (fun x ih => by rw [FreeAbelianGroup.map_neg, ih])
    fun x y ihx ihy => by rw [FreeAbelianGroup.map_add, ihx, ihy])
  (pure_bind := fun x f => pure_bind f x)
  (bind_assoc := fun

中文:
实例 :
  签名: 合法单子 自由交换群.{u}
  定义体: LawfulMonad.mk'
  (id_map := fun x => FreeAbelianGroup.induction_on' x (FreeAbelianGroup.map_zero id) (map_pure id)
    (fun x ih => by rw [FreeAbelianGroup.map_neg, ih])
    fun x y ihx ihy => by rw [FreeAbelianGroup.map_add, ihx, ihy])
  (pure_bind := fun x f => pure_bind f x)
  (bind_assoc := fun

Depends on / 依赖: LawfulMonad, LawfulMonad.mk
-/
instance : LawfulMonad FreeAbelianGroup.{u} := LawfulMonad.mk'
  (id_map := fun x => FreeAbelianGroup.induction_on' x (FreeAbelianGroup.map_zero id) (map_pure id)
    (fun x ih => by rw [FreeAbelianGroup.map_neg, ih])
    fun x y ihx ihy => by rw [FreeAbelianGroup.map_add, ihx, ihy])
  (pure_bind := fun x f => pure_bind f x)
  (bind_assoc := fun x f g => FreeAbelianGroup.induction_on' x (by iterate 3 rw [zero_bind])
    (fun x => by iterate 2 rw [pure_bind]) (fun x ih => by iterate 3 rw [neg_bind] <;> try rw [ih])
    fun x y ihx ihy => by iterate 3 rw [add_bind] <;> try rw [ihx, ihy])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommApplicative FreeAbelianGroup.{u}
  body: by
    induction x using FreeAbelianGroup.induction_on' with
    | zero => rw [FreeAbelianGroup.map_zero, zero_seq, seq_zero]
    | pure p =>
      rw [map_pure]; rw [pure_seq]
      induction y using FreeAbelianGroup.induction_on' with
      | zero => rw [FreeAbelianGroup.map_zero, FreeAbelianGroup

中文:
实例 :
  签名: 交换适用 自由交换群.{u}
  定义体: by
    induction x using FreeAbelianGroup.induction_on' with
    | zero => rw [FreeAbelianGroup.map_zero, zero_seq, seq_zero]
    | pure p =>
      rw [map_pure]; rw [pure_seq]
      induction y using FreeAbelianGroup.induction_on' with
      | zero => rw [FreeAbelianGroup.map_zero, FreeAbelianGroup

Depends on / 依赖: FreeAbelianG, FreeAbelianGroup, FreeAbelianGroup.induction_on, FreeAbelianGroup.map_add, FreeAbelianGroup.map_neg, FreeAbelianGroup.map_zero, induction_on, map_add, map_neg, map_pure, map_zero, neg_seq, pure_seq, seq_zero, zero_seq
-/
instance : CommApplicative FreeAbelianGroup.{u} where
  commutative_prod x y := by
    induction x using FreeAbelianGroup.induction_on' with
    | zero => rw [FreeAbelianGroup.map_zero, zero_seq, seq_zero]
    | pure p =>
      rw [map_pure]; rw [pure_seq]
      induction y using FreeAbelianGroup.induction_on' with
      | zero => rw [FreeAbelianGroup.map_zero, FreeAbelianGroup.map_zero, zero_seq]
      | pure q => rw [map_pure, map_pure, pure_seq, map_pure]
      | neg q ih => rw [FreeAbelianGroup.map_neg, FreeAbelianGroup.map_neg, neg_seq, ih]
      | add y₁ y₂ ih1 ih2 =>
        rw [FreeAbelianGroup.map_add]; rw [FreeAbelianGroup.map_add]; rw [add_seq]; rw [ih1]; rw [ih2]
    | neg p ih => rw [FreeAbelianGroup.map_neg, neg_seq, seq_neg, ih]
    | add x₁ x₂ ih1 ih2 => rw [FreeAbelianGroup.map_add, add_seq, seq_add, ih1, ih2]

end Monad

universe w

variable {β : Type v} {γ : Type w}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β)
  body: lift (of ∘ f)

中文:
定义 map
  签名: (f : α -> β)
  定义体: lift (of ∘ f)
-/
def map (f : α -> β) : FreeAbelianGroup α ->+ FreeAbelianGroup β :=
  lift (of ∘ f)

/--
theorem `lift_comp` / 定理 `lift_comp`

English:
theorem lift_comp
  given: {α} {β} {γ} [AddCommGroup γ] (f : α -> β) (g : β -> γ) (x : FreeAbelianGroup α)
  proof: by
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero]
  | of => simp only [lift_apply_of, map, Function.comp]
  | neg _ h => simp only [h, map_neg]
  | add _ _ h₁ h₂ => simp only [h₁, h₂, map_add]

中文:
定理 lift_comp
  条件: {α} {β} {γ} [加法交换群 γ] (f : α -> β) (g : β -> γ) (x : 自由交换群 α)
  证明: by
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero]
  | of => simp only [lift_apply_of, map, Function.comp]
  | neg _ h => simp only [h, map_neg]
  | add _ _ h₁ h₂ => simp only [h₁, h₂, map_add]

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.induction_on, Function, Function.comp, induction_on, lift_apply_of, map_add, map_neg, map_zero
-/
theorem lift_comp {α} {β} {γ} [AddCommGroup γ] (f : α -> β) (g : β -> γ) (x : FreeAbelianGroup α) :
    lift (g ∘ f) x = lift g (map f x) := by
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero]
  | of => simp only [lift_apply_of, map, Function.comp]
  | neg _ h => simp only [h, map_neg]
  | add _ _ h₁ h₂ => simp only [h₁, h₂, map_add]

/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map id = AddMonoidHom.id (FreeAbelianGroup α)
  proof: Eq.symm
    lift_ext _ _ fun _ => lift_unique of (AddMonoidHom.id _) fun _ => AddMonoidHom.id_apply _ _

中文:
定理 map_id
  结论: map id = 加法幺半群态射.id (自由交换群 α)
  证明: Eq.symm
    lift_ext _ _ fun _ => lift_unique of (AddMonoidHom.id _) fun _ => AddMonoidHom.id_apply _ _

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, AddMonoidHom.id_apply, Eq.symm, id_apply, lift_ext, lift_unique
-/
theorem map_id : map id = AddMonoidHom.id (FreeAbelianGroup α) :=
Eq.symm
    lift_ext _ _ fun _ => lift_unique of (AddMonoidHom.id _) fun _ => AddMonoidHom.id_apply _ _

/--
theorem `map_id_apply` / 定理 `map_id_apply`

English:
theorem map_id_apply
  given: (x : FreeAbelianGroup α)
  statement: map id x = x
  proof: by
  rw [map_id]
  rfl

中文:
定理 map_id_apply
  条件: (x : 自由交换群 α)
  结论: map id x = x
  证明: by
  rw [map_id]
  rfl

Depends on / 依赖: map_id
-/
theorem map_id_apply (x : FreeAbelianGroup α) : map id x = x := by
  rw [map_id]
  rfl

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: {f : α -> β} {g : β -> γ}
  statement: map (g ∘ f) = (map g).comp (map f)
  proof: Eq.symm lift_ext _ _ fun _ => by simp [map]

中文:
定理 map_comp
  条件: {f : α -> β} {g : β -> γ}
  结论: map (g ∘ f) = (map g).comp (map f)
  证明: Eq.symm lift_ext _ _ fun _ => by simp [map]

Depends on / 依赖: Eq.symm, lift_ext
-/
theorem map_comp {f : α -> β} {g : β -> γ} : map (g ∘ f) = (map g).comp (map f) :=
Eq.symm lift_ext _ _ fun _ => by simp [map]

/--
theorem `map_comp_apply` / 定理 `map_comp_apply`

English:
theorem map_comp_apply
  given: {f : α -> β} {g : β -> γ} (x : FreeAbelianGroup α)
  proof: by
  rw [map_comp]
  rfl

中文:
定理 map_comp_apply
  条件: {f : α -> β} {g : β -> γ} (x : 自由交换群 α)
  证明: by
  rw [map_comp]
  rfl

Depends on / 依赖: map_comp
-/
theorem map_comp_apply {f : α -> β} {g : β -> γ} (x : FreeAbelianGroup α) :
    map (g ∘ f) x = (map g) ((map f) x) := by
  rw [map_comp]
  rfl

-- version of map_of which uses `map`
@[simp]
/--
theorem `map_of_apply` / 定理 `map_of_apply`

English:
theorem map_of_apply
  given: {f : α -> β} (a : α)
  statement: map f (of a) = of (f a)
  proof: rfl

中文:
定理 map_of_apply
  条件: {f : α -> β} (a : α)
  结论: map f (of a) = of (f a)
  证明: rfl
-/
theorem map_of_apply {f : α -> β} (a : α) : map f (of a) = of (f a) :=
  rfl

variable (α)

section Mul

variable [Mul α]

/--
Instance `mul` / 实例 `mul`

English:
instance mul
  signature: : Mul (FreeAbelianGroup α)
  body: ⟨fun x => lift fun x₂ => lift (fun x₁ => of (x₁ * x₂)) x⟩

中文:
实例 mul
  签名: : 乘法 (自由交换群 α)
  定义体: ⟨fun x => lift fun x₂ => lift (fun x₁ => of (x₁ * x₂)) x⟩
-/
instance mul : Mul (FreeAbelianGroup α) :=
  ⟨fun x => lift fun x₂ => lift (fun x₁ => of (x₁ * x₂)) x⟩

variable {α}

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (x y : FreeAbelianGroup α)
  proof: rfl

@[simp]

中文:
定理 mul_def
  条件: (x y : 自由交换群 α)
  证明: rfl

@[simp]
-/
theorem mul_def (x y : FreeAbelianGroup α) :
    x * y = lift (fun x₂ => lift (fun x₁ => of (x₁ * x₂)) x) y :=
  rfl

@[simp]
/--
theorem `of_mul_of` / 定理 `of_mul_of`

English:
theorem of_mul_of
  given: (x y : α)
  statement: of x * of y = of (x * y)
  proof: by
  rw [mul_def]; rw [lift_apply_of]; rw [lift_apply_of]

中文:
定理 of_mul_of
  条件: (x y : α)
  结论: of x * of y = of (x * y)
  证明: by
  rw [mul_def]; rw [lift_apply_of]; rw [lift_apply_of]

Depends on / 依赖: lift_apply_of, mul_def
-/
theorem of_mul_of (x y : α) : of x * of y = of (x * y) := by
  rw [mul_def]; rw [lift_apply_of]; rw [lift_apply_of]

/--
theorem `of_mul` / 定理 `of_mul`

English:
theorem of_mul
  given: (x y : α)
  statement: of (x * y) = of x * of y
  proof: Eq.symm of_mul_of x y

中文:
定理 of_mul
  条件: (x y : α)
  结论: of (x * y) = of x * of y
  证明: Eq.symm of_mul_of x y

Depends on / 依赖: Eq.symm, of_mul_of
-/
theorem of_mul (x y : α) : of (x * y) = of x * of y :=
Eq.symm of_mul_of x y

/--
Instance `distrib` / 实例 `distrib`

English:
instance distrib
  signature: : Distrib (FreeAbelianGroup α) where
  body: fun _ _ _ => (lift _).map_add _ _
  right_distrib x y z := by simp [mul_def, ← Pi.add_def]

中文:
实例 distrib
  签名: : Distrib (自由交换群 α) where
  定义体: fun _ _ _ => (lift _).map_add _ _
  right_distrib x y z := by simp [mul_def, ← Pi.add_def]

Depends on / 依赖: map_add
-/
instance distrib : Distrib (FreeAbelianGroup α) where
  left_distrib := fun _ _ _ => (lift _).map_add _ _
  right_distrib x y z := by simp [mul_def, ← Pi.add_def]

/--
Instance `nonUnitalNonAssocRing` / 实例 `nonUnitalNonAssocRing`

English:
instance nonUnitalNonAssocRing
  signature: : NonUnitalNonAssocRing (FreeAbelianGroup α) where
  body: by
    have h : 0 * a + 0 * a = 0 * a := by simp [← add_mul]
    simpa using h
  mul_zero _ := rfl

中文:
实例 nonUnitalNonAssocRing
  签名: : 非幺非结合环 (自由交换群 α) where
  定义体: by
    have h : 0 * a + 0 * a = 0 * a := by simp [← add_mul]
    simpa using h
  mul_zero _ := rfl

Depends on / 依赖: add_mul, mul_zero
-/
instance nonUnitalNonAssocRing : NonUnitalNonAssocRing (FreeAbelianGroup α) where
  zero_mul a := by
    have h : 0 * a + 0 * a = 0 * a := by simp [← add_mul]
    simpa using h
  mul_zero _ := rfl

end Mul

section One
variable [One α]

/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One (FreeAbelianGroup α)
  body: ⟨of 1⟩

中文:
实例 one
  签名: : 幺 (自由交换群 α)
  定义体: ⟨of 1⟩
-/
instance one : One (FreeAbelianGroup α) :=
  ⟨of 1⟩

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : FreeAbelianGroup α) = of 1
  proof: rfl

中文:
定理 one_def
  结论: (1 : 自由交换群 α) = of 1
  证明: rfl
-/
theorem one_def : (1 : FreeAbelianGroup α) = of 1 :=
  rfl

/--
theorem `of_one` / 定理 `of_one`

English:
theorem of_one
  statement: (of 1 : FreeAbelianGroup α) = 1
  proof: rfl

中文:
定理 of_one
  结论: (of 1 : 自由交换群 α) = 1
  证明: rfl
-/
theorem of_one : (of 1 : FreeAbelianGroup α) = 1 :=
  rfl

end One

/--
Instance `nonUnitalRing` / 实例 `nonUnitalRing`

English:
instance nonUnitalRing
  signature: [Semigroup α]
  body: by
    induction z using FreeAbelianGroup.induction_on with
    | zero => simp only [mul_zero]
    | of L3 =>
      induction y using FreeAbelianGroup.induction_on with
      | zero => simp only [mul_zero, zero_mul]
      | of L2 =>
        induction x using FreeAbelianGroup.induction_on with
      

中文:
实例 nonUnitalRing
  签名: [半群 α]
  定义体: by
    induction z using FreeAbelianGroup.induction_on with
    | zero => simp only [mul_zero]
    | of L3 =>
      induction y using FreeAbelianGroup.induction_on with
      | zero => simp only [mul_zero, zero_mul]
      | of L2 =>
        induction x using FreeAbelianGroup.induction_on with
      

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.induction_on, add_mul, induction_on, mul_assoc, mul_zero, neg_mul, of_mul_of, zero_mul
-/
instance nonUnitalRing [Semigroup α] : NonUnitalRing (FreeAbelianGroup α) where
  mul_assoc x y z := by
    induction z using FreeAbelianGroup.induction_on with
    | zero => simp only [mul_zero]
    | of L3 =>
      induction y using FreeAbelianGroup.induction_on with
      | zero => simp only [mul_zero, zero_mul]
      | of L2 =>
        induction x using FreeAbelianGroup.induction_on with
        | zero => simp only [zero_mul]
        | of L1 => rw [of_mul_of, of_mul_of, of_mul_of, of_mul_of, mul_assoc]
        | neg L1 ih => rw [neg_mul, neg_mul, neg_mul, ih]
        | add x₁ x₂ ih₁ ih₂ => rw [add_mul, add_mul, add_mul, ih₁, ih₂]
      | neg L2 ih => rw [neg_mul, mul_neg, mul_neg, neg_mul, ih]
      | add y₁ y₂ ih₁ ih₂ => rw [add_mul, mul_add, mul_add, add_mul, ih₁, ih₂]
    | neg L3 ih => rw [mul_neg, mul_neg, mul_neg, ih]
    | add z₁ z₂ ih₁ ih₂ => rw [mul_add, mul_add, mul_add, ih₁, ih₂]

section Monoid

variable {R : Type*} [Monoid α] [Ring R]

/--
Instance `ring` / 实例 `ring`

English:
instance ring
  signature: : Ring (FreeAbelianGroup α) where
  body: by
    rw [mul_def]; rw [one_def]; rw [lift_apply_of]
    induction x using FreeAbelianGroup.induction_on with
    | zero => rfl
    | of L => rw [lift_apply_of, mul_one]
    | neg L ih => rw [map_neg, ih]
    | add x1 x2 ih1 ih2 => rw [map_add, ih1, ih2]
  one_mul x := by
    simp_rw [mul_def, one_

中文:
实例 ring
  签名: : 环 (自由交换群 α) where
  定义体: by
    rw [mul_def]; rw [one_def]; rw [lift_apply_of]
    induction x using FreeAbelianGroup.induction_on with
    | zero => rfl
    | of L => rw [lift_apply_of, mul_one]
    | neg L ih => rw [map_neg, ih]
    | add x1 x2 ih1 ih2 => rw [map_add, ih1, ih2]
  one_mul x := by
    simp_rw [mul_def, one_

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.induction_on, induction_on, lift_apply_of, map_add, map_neg, mul_def, mul_one, one_def, one_mul, simp_rw
-/
instance ring : Ring (FreeAbelianGroup α) where
  mul_one x := by
    rw [mul_def]; rw [one_def]; rw [lift_apply_of]
    induction x using FreeAbelianGroup.induction_on with
    | zero => rfl
    | of L => rw [lift_apply_of, mul_one]
    | neg L ih => rw [map_neg, ih]
    | add x1 x2 ih1 ih2 => rw [map_add, ih1, ih2]
  one_mul x := by
    simp_rw [mul_def, one_def, lift_apply_of]
    induction x using FreeAbelianGroup.induction_on with
    | zero => rfl
    | of L => rw [lift_apply_of, one_mul]
    | neg L ih => rw [map_neg, ih]
    | add x1 x2 ih1 ih2 => rw [map_add, ih1, ih2]

variable {α}

/--
Definition of `ofMulHom` / `ofMulHom` 的定义

English:
definition ofMulHom
  signature: : α ->* FreeAbelianGroup α where
  body: of
  map_one' := of_one _
  map_mul' := of_mul

@[simp]

中文:
定义 ofMulHom
  签名: : α ->* 自由交换群 α where
  定义体: of
  map_one' := of_one _
  map_mul' := of_mul

@[simp]
-/
def ofMulHom : α ->* FreeAbelianGroup α where
  toFun := of
  map_one' := of_one _
  map_mul' := of_mul

@[simp]
/--
theorem `ofMulHom_coe` / 定理 `ofMulHom_coe`

English:
theorem ofMulHom_coe
  statement: (ofMulHom : α -> FreeAbelianGroup α) = of
  proof: rfl

中文:
定理 ofMulHom_coe
  结论: (ofMulHom : α -> 自由交换群 α) = of
  证明: rfl
-/
theorem ofMulHom_coe : (ofMulHom : α -> FreeAbelianGroup α) = of :=
  rfl

/--
Definition of `liftMonoid` / `liftMonoid` 的定义

English:
definition liftMonoid
  signature: : (α ->* R) ≃ (FreeAbelianGroup α ->+* R) where
  body: { lift f with
    toFun := lift f
    map_one' := (lift_apply_of f _).trans f.map_one
    map_mul' x y := by
      induction y using FreeAbelianGroup.induction_on with
      | zero => simp only [mul_zero, map_zero]
      | of L2 =>
        induction x using FreeAbelianGroup.induction_on with
       

中文:
定义 liftMonoid
  签名: : (α ->* R) ≃ (自由交换群 α ->+* R) where
  定义体: { lift f with
    toFun := lift f
    map_one' := (lift_apply_of f _).trans f.map_one
    map_mul' x y := by
      induction y using FreeAbelianGroup.induction_on with
      | zero => simp only [mul_zero, map_zero]
      | of L2 =>
        induction x using FreeAbelianGroup.induction_on with
       
-/
def liftMonoid : (α ->* R) ≃ (FreeAbelianGroup α ->+* R) where
  toFun f := { lift f with
    toFun := lift f
    map_one' := (lift_apply_of f _).trans f.map_one
    map_mul' x y := by
      induction y using FreeAbelianGroup.induction_on with
      | zero => simp only [mul_zero, map_zero]
      | of L2 =>
        induction x using FreeAbelianGroup.induction_on with
        | zero => simp only [zero_mul, map_zero]
        | of L1 =>
          simp_rw [of_mul_of, lift_apply_of]
          exact f.map_mul _ _
        | neg L1 ih =>
          simp_rw [neg_mul, map_neg, neg_mul]
          exact congr_arg Neg.neg ih
        | add x1 x2 ih1 ih2 => simp only [add_mul, map_add, ih1, ih2]
      | neg L2 ih => rw [mul_neg, map_neg, map_neg, mul_neg, ih]
      | add y1 y2 ih1 ih2 => rw [mul_add, map_add, map_add, mul_add, ih1, ih2] }
  invFun F := MonoidHom.comp (↑F) ofMulHom
left_inv f := MonoidHom.ext by
    simp only [RingHom.coe_monoidHom_mk, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk,
      ofMulHom_coe, Function.comp_apply, lift_apply_of, forall_const]
right_inv F := RingHom.coe_addMonoidHom_injective by
    simp only
    rw [← lift.apply_symm_apply (↑F : FreeAbelianGroup α ->+ R)]
    rfl

@[simp]
/--
theorem `liftMonoid_coe_addMonoidHom` / 定理 `liftMonoid_coe_addMonoidHom`

English:
theorem liftMonoid_coe_addMonoidHom
  given: (f : α ->* R)
  statement: ↑(liftMonoid f) = lift f
  proof: rfl

@[simp]

中文:
定理 liftMonoid_coe_addMonoidHom
  条件: (f : α ->* R)
  结论: ↑(liftMonoid f) = lift f
  证明: rfl

@[simp]
-/
theorem liftMonoid_coe_addMonoidHom (f : α ->* R) : ↑(liftMonoid f) = lift f :=
  rfl

@[simp]
/--
theorem `liftMonoid_coe` / 定理 `liftMonoid_coe`

English:
theorem liftMonoid_coe
  given: (f : α ->* R)
  statement: ⇑(liftMonoid f) = lift f
  proof: rfl

@[simp]

中文:
定理 liftMonoid_coe
  条件: (f : α ->* R)
  结论: ⇑(liftMonoid f) = lift f
  证明: rfl

@[simp]
-/
theorem liftMonoid_coe (f : α ->* R) : ⇑(liftMonoid f) = lift f :=
  rfl

@[simp]
/--
theorem `liftMonoid_symm_coe` / 定理 `liftMonoid_symm_coe`

English:
theorem liftMonoid_symm_coe
  given: (f : FreeAbelianGroup α ->+* R)
  proof: rfl

中文:
定理 liftMonoid_symm_coe
  条件: (f : 自由交换群 α ->+* R)
  证明: rfl
-/
theorem liftMonoid_symm_coe (f : FreeAbelianGroup α ->+* R) :
    ⇑(liftMonoid.symm f) = lift.symm f :=
  rfl

end Monoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: α] : CommRing (FreeAbelianGroup α) where
  body: by
    induction x using FreeAbelianGroup.induction_on with
    | zero => exact zero_mul y
    | of s =>
      induction y using FreeAbelianGroup.induction_on with
      | zero => exact (zero_mul _).symm
      | of t =>
        dsimp only [(· * ·), Mul.mul]
        iterate 4 rw [lift_apply_of]
     

中文:
实例 [交换幺半群
  签名: α] : 交换环 (自由交换群 α) where
  定义体: by
    induction x using FreeAbelianGroup.induction_on with
    | zero => exact zero_mul y
    | of s =>
      induction y using FreeAbelianGroup.induction_on with
      | zero => exact (zero_mul _).symm
      | of t =>
        dsimp only [(· * ·), Mul.mul]
        iterate 4 rw [lift_apply_of]
     

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.induction_on, Mul.mul, add_mul, induction_on, iterate, lift_apply_of, mul_add, mul_comm, mul_neg, neg_mul, neg_mul_eq_mul_neg, neg_mul_eq_neg_mul, zero_mul
-/
instance [CommMonoid α] : CommRing (FreeAbelianGroup α) where
  mul_comm x y := by
    induction x using FreeAbelianGroup.induction_on with
    | zero => exact zero_mul y
    | of s =>
      induction y using FreeAbelianGroup.induction_on with
      | zero => exact (zero_mul _).symm
      | of t =>
        dsimp only [(· * ·), Mul.mul]
        iterate 4 rw [lift_apply_of]
        congr 1
        exact mul_comm _ _
      | neg t ih => rw [mul_neg, ih, neg_mul_eq_neg_mul]
      | add y1 y2 ih1 ih2 => rw [mul_add, add_mul, ih1, ih2]
    | neg s ih => rw [neg_mul, ih, neg_mul_eq_mul_neg]
    | add x1 x2 ih1 ih2 => rw [add_mul, mul_add, ih1, ih2]

/--
Definition of `uniqueEquiv` / `uniqueEquiv` 的定义

English:
definition uniqueEquiv
  signature: (T : Type*) [Unique T]
  body: FreeAbelianGroup.lift fun _ => (1 : Int)
  invFun n := n • of Inhabited.default
  left_inv z := FreeAbelianGroup.induction_on z
    (by simp only [zero_smul, map_zero])
    (Unique.forall_iff.2 <| by simp only [one_smul, lift_apply_of]) (Unique.forall_iff.2 <| by simp)
    fun x y hx hy => by
      

中文:
定义 uniqueEquiv
  签名: (T : 类型) [唯一 T]
  定义体: FreeAbelianGroup.lift fun _ => (1 : Int)
  invFun n := n • of Inhabited.default
  left_inv z := FreeAbelianGroup.induction_on z
    (by simp only [zero_smul, map_zero])
    (Unique.forall_iff.2 <| by simp only [one_smul, lift_apply_of]) (Unique.forall_iff.2 <| by simp)
    fun x y hx hy => by
      

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.lift
-/
def uniqueEquiv (T : Type*) [Unique T] : FreeAbelianGroup T ≃+ Int where
  toFun := FreeAbelianGroup.lift fun _ => (1 : Int)
  invFun n := n • of Inhabited.default
  left_inv z := FreeAbelianGroup.induction_on z
    (by simp only [zero_smul, map_zero])
    (Unique.forall_iff.2 <| by simp only [one_smul, lift_apply_of]) (Unique.forall_iff.2 <| by simp)
    fun x y hx hy => by
      simp only [map_add, add_smul] at *
      rw [hx]; rw [hy]
  right_inv n := by
    rw [map_zsmul]; rw [lift_apply_of]
    exact zsmul_one n
  map_add' := map_add _

/--
Definition of `equivOfEquiv` / `equivOfEquiv` 的定义

English:
definition equivOfEquiv
  signature: {α β : Type*} (f : α ≃ β)
  body: map f
  invFun := map f.symm
  left_inv x := by rw [← map_comp_apply, Equiv.symm_comp_self, map_id, AddMonoidHom.id_apply]
  right_inv x := by rw [← map_comp_apply, Equiv.self_comp_symm, map_id, AddMonoidHom.id_apply]
  map_add' := map_add _

中文:
定义 equivOfEquiv
  签名: {α β : 类型} (f : α ≃ β)
  定义体: map f
  invFun := map f.symm
  left_inv x := by rw [← map_comp_apply, Equiv.symm_comp_self, map_id, AddMonoidHom.id_apply]
  right_inv x := by rw [← map_comp_apply, Equiv.self_comp_symm, map_id, AddMonoidHom.id_apply]
  map_add' := map_add _
-/
def equivOfEquiv {α β : Type*} (f : α ≃ β) : FreeAbelianGroup α ≃+ FreeAbelianGroup β where
  toFun := map f
  invFun := map f.symm
  left_inv x := by rw [← map_comp_apply, Equiv.symm_comp_self, map_id, AddMonoidHom.id_apply]
  right_inv x := by rw [← map_comp_apply, Equiv.self_comp_symm, map_id, AddMonoidHom.id_apply]
  map_add' := map_add _

end FreeAbelianGroup
