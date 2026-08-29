/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Joachim Breitner
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.GroupTheory.Congruence.Basic
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# The coproduct (a.k.a. the free product) of groups or monoids

Given an `ι`-indexed family `M` of monoids,
we define their coproduct (a.k.a. free product) `Monoid.CoprodI M`.
As usual, we use the suffix `I` for an indexed (co)product,
leaving `Coprod` for the coproduct of two monoids.

When `ι` and all `M i` have decidable equality,
the free product bijects with the type `Monoid.CoprodI.Word M` of reduced words.
This bijection is constructed
by defining an action of `Monoid.CoprodI M` on `Monoid.CoprodI.Word M`.

When `M i` are all groups, `Monoid.CoprodI M` is also a group
(and the coproduct in the category of groups).

## Main definitions

- `Monoid.CoprodI M`: the free product, defined as a quotient of a free monoid.
- `Monoid.CoprodI.of {i} : M i →* Monoid.CoprodI M`.
- `Monoid.CoprodI.lift : (∀ {i}, M i →* N) ≃ (Monoid.CoprodI M →* N)`: the universal property.
- `Monoid.CoprodI.Word M`: the type of reduced words.
- `Monoid.CoprodI.Word.equiv M : Monoid.CoprodI M ≃ word M`.
- `Monoid.CoprodI.NeWord M i j`: an inductive description of non-empty words
  with first letter from `M i` and last letter from `M j`,
  together with an API (`singleton`, `append`, `head`, `tail`, `to_word`, `Prod`, `inv`).
  Used in the proof of the Ping-Pong-lemma.
- `Monoid.CoprodI.lift_injective_of_ping_pong`: The Ping-Pong-lemma,
  proving injectivity of the `lift`. See the documentation of that theorem for more information.

## Remarks

There are many answers to the question "what is the coproduct of a family `M` of monoids?",
and they are all equivalent but not obviously equivalent.
We provide two answers.
The first, almost tautological answer is given by `Monoid.CoprodI M`,
which is a quotient of the type of words in the alphabet `Σ i, M i`.
It's straightforward to define and easy to prove its universal property.
But this answer is not completely satisfactory,
because it's difficult to tell when two elements `x y : Monoid.CoprodI M` are distinct
since `Monoid.CoprodI M` is defined as a quotient.

The second, maximally efficient answer is given by `Monoid.CoprodI.Word M`.
An element of `Monoid.CoprodI.Word M` is a word in the alphabet `Σ i, M i`,
where the letter `⟨i, 1⟩` doesn't occur and no adjacent letters share an index `i`.
Since we only work with reduced words, there is no need for quotienting,
and it is easy to tell when two elements are distinct.
However it's not obvious that this is even a monoid!

We prove that every element of `Monoid.CoprodI M` can be represented by a unique reduced word,
i.e. `Monoid.CoprodI M` and `Monoid.CoprodI.Word M` are equivalent types.
This means that `Monoid.CoprodI.Word M` can be given a monoid structure,
and it lets us tell when two elements of `Monoid.CoprodI M` are distinct.

There is also a completely tautological, maximally inefficient answer
given by `MonCat.Colimits.ColimitType`.
Whereas `Monoid.CoprodI M` at least ensures that
(any instance of) associativity holds by reflexivity,
in this answer associativity holds because of quotienting.
Yet another answer, which is constructively more satisfying,
could be obtained by showing that `Monoid.CoprodI.Rel` is confluent.

## References

[van der Waerden, *Free products of groups*][MR25465]

-/

@[expose] public section


open Set

variable {ι : Type*} (M : ι -> Type*) [forall i, Monoid (M i)]

/--
Inductive type `Monoid.CoprodI.Rel` / 归纳类型 `Monoid.CoprodI.Rel`

English:
inductive Monoid.CoprodI.Rel
  parameters: : FreeMonoid (Σ i, M i) -> FreeMonoid (Σ i, M i) -> Prop
  constructors (2):
    - of_one: (i : ι) : Monoid.CoprodI.Rel (FreeMonoid.of ⟨i, 1⟩) 1
    - of_mul: {i : ι} (x y : M i) : Monoid.CoprodI.Rel (FreeMonoid.of ⟨i, x⟩ * FreeMonoid.of ⟨i, y⟩) (FreeMonoid.of ⟨i, x * y⟩)

中文:
归纳类型 幺半群.余prodI.关系
  参数: : 自由幺半群 (Σ i, M i) -> 自由幺半群 (Σ i, M i) -> 命题
  构造子 (2 个):
    - of_one: (i : ι) : 幺半群.余prodI.关系 (自由幺半群.of ⟨i, 1⟩) 1
    - of_mul: {i : ι} (x y : M i) : 幺半群.余prodI.关系 (自由幺半群.of ⟨i, x⟩ * 自由幺半群.of ⟨i, y⟩) (自由幺半群.of ⟨i, x * y⟩)
-/
inductive Monoid.CoprodI.Rel : FreeMonoid (Σ i, M i) -> FreeMonoid (Σ i, M i) -> Prop
  | of_one (i : ι) : Monoid.CoprodI.Rel (FreeMonoid.of ⟨i, 1⟩) 1
  | of_mul {i : ι} (x y : M i) :
    Monoid.CoprodI.Rel (FreeMonoid.of ⟨i, x⟩ * FreeMonoid.of ⟨i, y⟩) (FreeMonoid.of ⟨i, x * y⟩)

/--
Definition of `Monoid.CoprodI` / `Monoid.CoprodI` 的定义

English:
definition Monoid.CoprodI
  signature: : Type _
  body: (conGen (Monoid.CoprodI.Rel M)).Quotient
deriving Monoid, Inhabited

中文:
定义 幺半群.余prodI
  签名: : 类型 _
  定义体: (conGen (Monoid.CoprodI.Rel M)).Quotient
deriving Monoid, Inhabited

Depends on / 依赖: CoprodI, Monoid, Monoid.CoprodI.Rel, Quotient, conGen
-/
def Monoid.CoprodI : Type _ := (conGen (Monoid.CoprodI.Rel M)).Quotient
deriving Monoid, Inhabited

namespace Monoid.CoprodI

/-- The type of reduced words. A reduced word cannot contain a letter `1`, and no two adjacent
letters can come from the same summand. -/
@[ext]
/--
Definition of `Word` / `Word` 的定义

English:
structure Word
  parameters: where
  axioms and operations (3):
    - toList : List (Σ i, M i)
    - ne_one : forall l in toList, Sigma.snd l != 1
    - chain_ne : toList.IsChain fun l l' => Sigma.fst l != Sigma.fst l'

中文:
结构 Word
  参数: where
  公理与运算 (3 个):
    - toList : 列表 (Σ i, M i)
    - ne_one : 对任意 l in toList, 依赖和类型.snd l != 1
    - chain_ne : toList.IsChain fun l l' => 依赖和类型.fst l != 依赖和类型.fst l'
-/
structure Word where
  /-- A `Word` is a `List (Σ i, M i)`, such that `1` is not in the list, and no
  two adjacent letters are from the same summand -/
  toList : List (Σ i, M i)
  /-- A reduced word does not contain `1` -/
  ne_one : forall l in toList, Sigma.snd l != 1
  /-- Adjacent letters are not from the same summand. -/
  chain_ne : toList.IsChain fun l l' => Sigma.fst l != Sigma.fst l'

variable {M}

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: {i : ι}
  body: Con.mk' _ (FreeMonoid.of <| Sigma.mk i x)
  map_one' := (Con.eq _).mpr (ConGen.Rel.of _ _ (CoprodI.Rel.of_one i))
map_mul' x y := Eq.symm (Con.eq _).mpr (ConGen.Rel.of _ _ (CoprodI.Rel.of_mul x y))

中文:
定义 of
  签名: {i : ι}
  定义体: Con.mk' _ (FreeMonoid.of <| Sigma.mk i x)
  map_one' := (Con.eq _).mpr (ConGen.Rel.of _ _ (CoprodI.Rel.of_one i))
map_mul' x y := Eq.symm (Con.eq _).mpr (ConGen.Rel.of _ _ (CoprodI.Rel.of_mul x y))

Depends on / 依赖: Con.mk, FreeMonoid, FreeMonoid.of, Sigma.mk
-/
def of {i : ι} : M i ->* CoprodI M where
  toFun x := Con.mk' _ (FreeMonoid.of <| Sigma.mk i x)
  map_one' := (Con.eq _).mpr (ConGen.Rel.of _ _ (CoprodI.Rel.of_one i))
map_mul' x y := Eq.symm (Con.eq _).mpr (ConGen.Rel.of _ _ (CoprodI.Rel.of_mul x y))

/--
theorem `of_apply` / 定理 `of_apply`

English:
theorem of_apply
  given: {i} (m : M i)
  statement: of m = Con.mk' _ (FreeMonoid.of <| Sigma.mk i m)
  proof: rfl

中文:
定理 of_apply
  条件: {i} (m : M i)
  结论: of m = Con.mk' _ (自由幺半群.of <| 依赖和类型.mk i m)
  证明: rfl
-/
theorem of_apply {i} (m : M i) : of m = Con.mk' _ (FreeMonoid.of <| Sigma.mk i m) :=
  rfl

variable {N : Type*} [Monoid N]

set_option backward.isDefEq.respectTransparency false in
/-- See note [partially-applied ext lemmas]. -/
@[ext 1100] -- This needs a higher `ext` priority
/--
theorem `ext_hom` / 定理 `ext_hom`

English:
theorem ext_hom
  given: (f g : CoprodI M ->* N) (h : forall i, f.comp (of : M i ->* _) = g.comp of)
  statement: f = g
  proof: (MonoidHom.cancel_right Con.mk'_surjective).mp
    FreeMonoid.hom_eq fun ⟨i, x⟩ => by
      rw [MonoidHom.comp_apply]; rw [MonoidHom.comp_apply]; rw [← of_apply]
      unfold CoprodI
      rw [← MonoidHom.comp_apply]; rw [← MonoidHom.comp_apply]; rw [h]

中文:
定理 ext_hom
  条件: (f g : 余prodI M ->* N) (h : 对任意 i, f.comp (of : M i ->* _) = g.comp of)
  结论: f = g
  证明: (MonoidHom.cancel_right Con.mk'_surjective).mp
    FreeMonoid.hom_eq fun ⟨i, x⟩ => by
      rw [MonoidHom.comp_apply]; rw [MonoidHom.comp_apply]; rw [← of_apply]
      unfold CoprodI
      rw [← MonoidHom.comp_apply]; rw [← MonoidHom.comp_apply]; rw [h]

Depends on / 依赖: Con.mk, CoprodI, FreeMonoid, FreeMonoid.hom_eq, MonoidHom, MonoidHom.cancel_right, MonoidHom.comp_apply, _surjective, cancel_right, comp_apply, hom_eq, of_apply
-/
theorem ext_hom (f g : CoprodI M ->* N) (h : forall i, f.comp (of : M i ->* _) = g.comp of) : f = g :=
(MonoidHom.cancel_right Con.mk'_surjective).mp
    FreeMonoid.hom_eq fun ⟨i, x⟩ => by
      rw [MonoidHom.comp_apply]; rw [MonoidHom.comp_apply]; rw [← of_apply]
      unfold CoprodI
      rw [← MonoidHom.comp_apply]; rw [← MonoidHom.comp_apply]; rw [h]

/-- A map out of the free product corresponds to a family of maps out of the summands. This is the
universal property of the free product, characterizing it as a categorical coproduct. -/
@[simps symm_apply]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (forall i, M i ->* N) ≃ (CoprodI M ->* N) where
  body: Con.lift _ (FreeMonoid.lift fun p : Σ i, M i => fi p.fst p.snd)
Con.conGen_le.2 fun _ _ => by
        simp_rw [Con.ker_rel]
        rintro (i | ⟨x, y⟩) <;> simp
  invFun f _ := f.comp of
  left_inv := by
    intro fi
    ext i x
    rfl
  right_inv := by
    intro f
    ext i x
    rfl

@[simp]

中文:
定义 lift
  签名: : (对任意 i, M i ->* N) ≃ (余prodI M ->* N) where
  定义体: Con.lift _ (FreeMonoid.lift fun p : Σ i, M i => fi p.fst p.snd)
Con.conGen_le.2 fun _ _ => by
        simp_rw [Con.ker_rel]
        rintro (i | ⟨x, y⟩) <;> simp
  invFun f _ := f.comp of
  left_inv := by
    intro fi
    ext i x
    rfl
  right_inv := by
    intro f
    ext i x
    rfl

@[simp]

Depends on / 依赖: Con.conGen_le, Con.ker_rel, Con.lift, FreeMonoid, FreeMonoid.lift, conGen_le, f.comp, invFun, ker_rel, left_inv, p.fst, p.snd, right_inv, simp_rw
-/
def lift : (forall i, M i ->* N) ≃ (CoprodI M ->* N) where
  toFun fi :=
Con.lift _ (FreeMonoid.lift fun p : Σ i, M i => fi p.fst p.snd)
Con.conGen_le.2 fun _ _ => by
        simp_rw [Con.ker_rel]
        rintro (i | ⟨x, y⟩) <;> simp
  invFun f _ := f.comp of
  left_inv := by
    intro fi
    ext i x
    rfl
  right_inv := by
    intro f
    ext i x
    rfl

@[simp]
/--
theorem `lift_comp_of` / 定理 `lift_comp_of`

English:
theorem lift_comp_of
  given: {N} [Monoid N] (fi : forall i, M i ->* N) i
  statement: (lift fi).comp of = fi i
  proof: congr_fun (lift.symm_apply_apply fi) i

@[simp]

中文:
定理 lift_comp_of
  条件: {N} [幺半群 N] (fi : 对任意 i, M i ->* N) i
  结论: (lift fi).comp of = fi i
  证明: congr_fun (lift.symm_apply_apply fi) i

@[simp]

Depends on / 依赖: congr_fun, lift.symm_apply_apply, symm_apply_apply
-/
theorem lift_comp_of {N} [Monoid N] (fi : forall i, M i ->* N) i : (lift fi).comp of = fi i :=
  congr_fun (lift.symm_apply_apply fi) i

@[simp]
/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: {N} [Monoid N] (fi : forall i, M i ->* N) {i} (m : M i)
  statement: lift fi (of m) = fi i m
  proof: DFunLike.congr_fun (lift_comp_of ..) m

@[simp]

中文:
定理 lift_of
  条件: {N} [幺半群 N] (fi : 对任意 i, M i ->* N) {i} (m : M i)
  结论: lift fi (of m) = fi i m
  证明: DFunLike.congr_fun (lift_comp_of ..) m

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, lift_comp_of
-/
theorem lift_of {N} [Monoid N] (fi : forall i, M i ->* N) {i} (m : M i) : lift fi (of m) = fi i m :=
  DFunLike.congr_fun (lift_comp_of ..) m

@[simp]
/--
theorem `lift_comp_of'` / 定理 `lift_comp_of'`

English:
theorem lift_comp_of'
  given: {N} [Monoid N] (f : CoprodI M ->* N)
  proof: lift.apply_symm_apply f

@[simp]

中文:
定理 lift_comp_of'
  条件: {N} [幺半群 N] (f : 余prodI M ->* N)
  证明: lift.apply_symm_apply f

@[simp]
-/
theorem lift_comp_of' {N} [Monoid N] (f : CoprodI M ->* N) :
    lift (fun i => f.comp (of (i := i))) = f :=
  lift.apply_symm_apply f

@[simp]
/--
theorem `lift_of'` / 定理 `lift_of'`

English:
theorem lift_of'
  statement: lift (fun i => (of : M i ->* CoprodI M)) = .id (CoprodI M)
  proof: lift_comp_of' (.id _)

中文:
定理 lift_of'
  结论: lift (fun i => (of : M i ->* 余prodI M)) = .id (余prodI M)
  证明: lift_comp_of' (.id _)

Depends on / 依赖: lift_comp_of
-/
theorem lift_of' : lift (fun i => (of : M i ->* CoprodI M)) = .id (CoprodI M) :=
  lift_comp_of' (.id _)

/--
theorem `of_leftInverse` / 定理 `of_leftInverse`

English:
theorem of_leftInverse
  given: [DecidableEq ι] (i : ι)
  proof: fun x => by
  simp only [lift_of, Pi.mulSingle_eq_same, MonoidHom.id_apply]

中文:
定理 of_leftInverse
  条件: [DecidableEq ι] (i : ι)
  证明: fun x => by
  simp only [lift_of, Pi.mulSingle_eq_same, MonoidHom.id_apply]

Depends on / 依赖: MonoidHom, MonoidHom.id_apply, Pi.mulSingle_eq_same, id_apply, lift_of, mulSingle_eq_same
-/
theorem of_leftInverse [DecidableEq ι] (i : ι) :
    Function.LeftInverse (lift <| Pi.mulSingle i (MonoidHom.id (M i))) of := fun x => by
  simp only [lift_of, Pi.mulSingle_eq_same, MonoidHom.id_apply]

/--
theorem `of_injective` / 定理 `of_injective`

English:
theorem of_injective
  given: (i : ι)
  statement: Function.Injective (of : M i ->* _)
  proof: by
  classical exact (of_leftInverse i).injective

中文:
定理 of_injective
  条件: (i : ι)
  结论: 函数.单射 (of : M i ->* _)
  证明: by
  classical exact (of_leftInverse i).injective

Depends on / 依赖: classical, injective, of_leftInverse
-/
theorem of_injective (i : ι) : Function.Injective (of : M i ->* _) := by
  classical exact (of_leftInverse i).injective

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mrange_eq_iSup` / 定理 `mrange_eq_iSup`

English:
theorem mrange_eq_iSup
  given: {N} [Monoid N] (f : forall i, M i ->* N)
  proof: by
  rw [lift]; rw [Equiv.coe_fn_mk]; rw [Con.lift_range]; rw [FreeMonoid.mrange_lift]; rw [range_sigma_eq_iUnion_range]; rw [Submonoid.closure_iUnion]
  simp +instances only [MonoidHom.mclosure_range]

中文:
定理 mrange_eq_iSup
  条件: {N} [幺半群 N] (f : 对任意 i, M i ->* N)
  证明: by
  rw [lift]; rw [Equiv.coe_fn_mk]; rw [Con.lift_range]; rw [FreeMonoid.mrange_lift]; rw [range_sigma_eq_iUnion_range]; rw [Submonoid.closure_iUnion]
  simp +instances only [MonoidHom.mclosure_range]

Depends on / 依赖: Con.lift_range, Equiv.coe_fn_mk, FreeMonoid, FreeMonoid.mrange_lift, MonoidHom, MonoidHom.mclosure_range, Submonoid, Submonoid.closure_iUnion, closure_iUnion, coe_fn_mk, instances, lift_range, mclosure_range, mrange_lift, range_sigma_eq_iUnion_range
-/
theorem mrange_eq_iSup {N} [Monoid N] (f : forall i, M i ->* N) :
    MonoidHom.mrange (lift f) = ⨆ i, MonoidHom.mrange (f i) := by
  rw [lift]; rw [Equiv.coe_fn_mk]; rw [Con.lift_range]; rw [FreeMonoid.mrange_lift]; rw [range_sigma_eq_iUnion_range]; rw [Submonoid.closure_iUnion]
  simp +instances only [MonoidHom.mclosure_range]

/--
theorem `lift_mrange_le` / 定理 `lift_mrange_le`

English:
theorem lift_mrange_le
  given: {N} [Monoid N] (f : forall i, M i ->* N) {s : Submonoid N}
  proof: by
  simp [mrange_eq_iSup]

@[simp]

中文:
定理 lift_mrange_le
  条件: {N} [幺半群 N] (f : 对任意 i, M i ->* N) {s : 子幺半群 N}
  证明: by
  simp [mrange_eq_iSup]

@[simp]

Depends on / 依赖: mrange_eq_iSup
-/
theorem lift_mrange_le {N} [Monoid N] (f : forall i, M i ->* N) {s : Submonoid N} :
    MonoidHom.mrange (lift f) <= s ↔ forall i, MonoidHom.mrange (f i) <= s := by
  simp [mrange_eq_iSup]

@[simp]
/--
theorem `iSup_mrange_of` / 定理 `iSup_mrange_of`

English:
theorem iSup_mrange_of
  statement: ⨆ i, MonoidHom.mrange (of : M i ->* CoprodI M) = ⊤
  proof: by
  simp [← mrange_eq_iSup]

@[simp]

中文:
定理 iSup_mrange_of
  结论: ⨆ i, 幺半群态射.mrange (of : M i ->* 余prodI M) = ⊤
  证明: by
  simp [← mrange_eq_iSup]

@[simp]

Depends on / 依赖: mrange_eq_iSup
-/
theorem iSup_mrange_of : ⨆ i, MonoidHom.mrange (of : M i ->* CoprodI M) = ⊤ := by
  simp [← mrange_eq_iSup]

@[simp]
/--
theorem `mclosure_iUnion_range_of` / 定理 `mclosure_iUnion_range_of`

English:
theorem mclosure_iUnion_range_of
  proof: by
  simp [Submonoid.closure_iUnion]

@[elab_as_elim]

中文:
定理 mclosure_iUnion_range_of
  证明: by
  simp [Submonoid.closure_iUnion]

@[elab_as_elim]

Depends on / 依赖: Submonoid, Submonoid.closure_iUnion, closure_iUnion
-/
theorem mclosure_iUnion_range_of :
    Submonoid.closure (⋃ i, Set.range (of : M i ->* CoprodI M)) = ⊤ := by
  simp [Submonoid.closure_iUnion]

@[elab_as_elim]
/--
theorem `induction_left` / 定理 `induction_left`

English:
theorem induction_left
  statement: {motive : CoprodI M -> Prop} (m : CoprodI M) (one : motive 1)
  proof: by
  induction m using Submonoid.induction_of_closure_eq_top_left mclosure_iUnion_range_of with
  | one => exact one
  | mul_left x hx y ihy =>
    obtain ⟨i, m, rfl⟩ : exists (i : ι) (m : M i), of m = x := by simpa using hx
    exact mul m y ihy

@[elab_as_elim]

中文:
定理 induction_left
  结论: {motive : 余prodI M -> 命题} (m : 余prodI M) (one : motive 1)
  证明: by
  induction m using Submonoid.induction_of_closure_eq_top_left mclosure_iUnion_range_of with
  | one => exact one
  | mul_left x hx y ihy =>
    obtain ⟨i, m, rfl⟩ : exists (i : ι) (m : M i), of m = x := by simpa using hx
    exact mul m y ihy

@[elab_as_elim]

Depends on / 依赖: Submonoid, Submonoid.induction_of_closure_eq_top_left, induction_of_closure_eq_top_left, mclosure_iUnion_range_of, mul_left
-/
theorem induction_left {motive : CoprodI M -> Prop} (m : CoprodI M) (one : motive 1)
    (mul : forall {i} (m : M i) x, motive x -> motive (of m * x)) : motive m := by
  induction m using Submonoid.induction_of_closure_eq_top_left mclosure_iUnion_range_of with
  | one => exact one
  | mul_left x hx y ihy =>
    obtain ⟨i, m, rfl⟩ : exists (i : ι) (m : M i), of m = x := by simpa using hx
    exact mul m y ihy

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {motive : CoprodI M -> Prop} (m : CoprodI M) (one : motive 1)
  proof: induction_left m one fun {_} _ _ => mul _ _ (of _ _)

中文:
定理 induction_on
  结论: {motive : 余prodI M -> 命题} (m : 余prodI M) (one : motive 1)
  证明: induction_left m one fun {_} _ _ => mul _ _ (of _ _)

Depends on / 依赖: induction_left
-/
theorem induction_on {motive : CoprodI M -> Prop} (m : CoprodI M) (one : motive 1)
    (of : forall (i) (m : M i), motive (of m))
    (mul : forall x y, motive x -> motive y -> motive (x * y)) : motive m :=
  induction_left m one fun {_} _ _ => mul _ _ (of _ _)

section Group

variable (G : ι -> Type*) [forall i, Group (G i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (CoprodI G)
  body: MulOpposite.unop ∘ lift fun i => (of : G i ->* _).op.comp (MulEquiv.inv' (G i)).toMonoidHom

中文:
实例 :
  签名: 取逆 (余prodI G)
  定义体: MulOpposite.unop ∘ lift fun i => (of : G i ->* _).op.comp (MulEquiv.inv' (G i)).toMonoidHom

Depends on / 依赖: MulEquiv, MulEquiv.inv, MulOpposite, MulOpposite.unop, op.comp, toMonoidHom
-/
instance : Inv (CoprodI G) where
  inv :=
    MulOpposite.unop ∘ lift fun i => (of : G i ->* _).op.comp (MulEquiv.inv' (G i)).toMonoidHom

/--
theorem `inv_def` / 定理 `inv_def`

English:
theorem inv_def
  given: (x : CoprodI G)
  proof: rfl

中文:
定理 inv_def
  条件: (x : 余prodI G)
  证明: rfl
-/
theorem inv_def (x : CoprodI G) :
    x⁻¹ =
      MulOpposite.unop
        (lift (fun i => (of : G i ->* _).op.comp (MulEquiv.inv' (G i)).toMonoidHom) x) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (CoprodI G)
  body: { inv_mul_cancel := by
      intro m
      rw [inv_def]
      induction m using CoprodI.induction_on with
      | one => rw [map_one, MulOpposite.unop_one, one_mul]
      | of m ih =>
        change of _⁻¹ * of _ = 1
        rw [← of.map_mul]; rw [inv_mul_cancel]; rw [of.map_one]
      | mul x y ihx

中文:
实例 :
  签名: 群 (余prodI G)
  定义体: { inv_mul_cancel := by
      intro m
      rw [inv_def]
      induction m using CoprodI.induction_on with
      | one => rw [map_one, MulOpposite.unop_one, one_mul]
      | of m ih =>
        change of _⁻¹ * of _ = 1
        rw [← of.map_mul]; rw [inv_mul_cancel]; rw [of.map_one]
      | mul x y ihx

Depends on / 依赖: CoprodI, CoprodI.induction_on, MulOpposite, MulOpposite.unop_mul, MulOpposite.unop_one, induction_on, inv_def, inv_mul_cancel, map_mul, map_one, mul_assoc, of.map_mul, of.map_one, one_mul, unop_mul, unop_one
-/
instance : Group (CoprodI G) :=
  { inv_mul_cancel := by
      intro m
      rw [inv_def]
      induction m using CoprodI.induction_on with
      | one => rw [map_one, MulOpposite.unop_one, one_mul]
      | of m ih =>
        change of _⁻¹ * of _ = 1
        rw [← of.map_mul]; rw [inv_mul_cancel]; rw [of.map_one]
      | mul x y ihx ihy =>
        rw [map_mul]; rw [MulOpposite.unop_mul]; rw [mul_assoc]; rw [← mul_assoc _ x y]; rw [ihx]; rw [one_mul]; rw [ihy] }

/--
theorem `lift_range_le` / 定理 `lift_range_le`

English:
theorem lift_range_le
  statement: {N} [Group N] (f : forall i, G i ->* N) {s : Subgroup N}
  proof: by
  rintro _ ⟨x, rfl⟩
  induction x using CoprodI.induction_on with
  | one => exact s.one_mem
  | of i x =>
    simp only [lift_of]
    exact h i (Set.mem_range_self x)
  | mul x y hx hy =>
    simp only [map_mul]
    exact s.mul_mem hx hy

中文:
定理 lift_range_le
  结论: {N} [群 N] (f : 对任意 i, G i ->* N) {s : 子群 N}
  证明: by
  rintro _ ⟨x, rfl⟩
  induction x using CoprodI.induction_on with
  | one => exact s.one_mem
  | of i x =>
    simp only [lift_of]
    exact h i (Set.mem_range_self x)
  | mul x y hx hy =>
    simp only [map_mul]
    exact s.mul_mem hx hy

Depends on / 依赖: CoprodI, CoprodI.induction_on, Set.mem_range_self, induction_on, lift_of, map_mul, mem_range_self, mul_mem, one_mem, s.mul_mem, s.one_mem
-/
theorem lift_range_le {N} [Group N] (f : forall i, G i ->* N) {s : Subgroup N}
    (h : forall i, (f i).range <= s) : (lift f).range <= s := by
  rintro _ ⟨x, rfl⟩
  induction x using CoprodI.induction_on with
  | one => exact s.one_mem
  | of i x =>
    simp only [lift_of]
    exact h i (Set.mem_range_self x)
  | mul x y hx hy =>
    simp only [map_mul]
    exact s.mul_mem hx hy

/--
theorem `range_eq_iSup` / 定理 `range_eq_iSup`

English:
theorem range_eq_iSup
  given: {N} [Group N] (f : forall i, G i ->* N)
  statement: (lift f).range = ⨆ i, (f i).range
  proof: by
  apply le_antisymm (lift_range_le _ f fun i => le_iSup (fun i => MonoidHom.range (f i)) i)
  apply iSup_le _
  rintro i _ ⟨x, rfl⟩
  exact ⟨of x, by simp only [lift_of]⟩

中文:
定理 range_eq_iSup
  条件: {N} [群 N] (f : 对任意 i, G i ->* N)
  结论: (lift f).range = ⨆ i, (f i).range
  证明: by
  apply le_antisymm (lift_range_le _ f fun i => le_iSup (fun i => MonoidHom.range (f i)) i)
  apply iSup_le _
  rintro i _ ⟨x, rfl⟩
  exact ⟨of x, by simp only [lift_of]⟩

Depends on / 依赖: MonoidHom, MonoidHom.range, iSup_le, le_antisymm, le_iSup, lift_of, lift_range_le
-/
theorem range_eq_iSup {N} [Group N] (f : forall i, G i ->* N) : (lift f).range = ⨆ i, (f i).range := by
  apply le_antisymm (lift_range_le _ f fun i => le_iSup (fun i => MonoidHom.range (f i)) i)
  apply iSup_le _
  rintro i _ ⟨x, rfl⟩
  exact ⟨of x, by simp only [lift_of]⟩

end Group

namespace Word

/-- The empty reduced word. -/
@[simps]
/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: : Word M where
  body: []
  ne_one := by simp
  chain_ne := List.isChain_nil

中文:
定义 empty
  签名: : Word M where
  定义体: []
  ne_one := by simp
  chain_ne := List.isChain_nil
-/
def empty : Word M where
  toList := []
  ne_one := by simp
  chain_ne := List.isChain_nil

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Word M)
  body: ⟨empty⟩

中文:
实例 :
  签名: 可居 (Word M)
  定义体: ⟨empty⟩
-/
instance : Inhabited (Word M) :=
  ⟨empty⟩

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (w : Word M)
  body: List.prod (w.toList.map fun l => of l.snd)

@[simp]

中文:
定义 乘积
  签名: (w : Word M)
  定义体: List.prod (w.toList.map fun l => of l.snd)

@[simp]

Depends on / 依赖: List.prod, l.snd, toList, w.toList.map
-/
def prod (w : Word M) : CoprodI M :=
  List.prod (w.toList.map fun l => of l.snd)

@[simp]
/--
theorem `prod_empty` / 定理 `prod_empty`

English:
theorem prod_empty
  statement: prod (empty : Word M) = 1
  proof: rfl

中文:
定理 prod_empty
  结论: 乘积 (empty : Word M) = 1
  证明: rfl
-/
theorem prod_empty : prod (empty : Word M) = 1 :=
  rfl

/--
Definition of `fstIdx` / `fstIdx` 的定义

English:
definition fstIdx
  signature: (w : Word M)
  body: w.toList.head?.map Sigma.fst

中文:
定义 fstIdx
  签名: (w : Word M)
  定义体: w.toList.head?.map Sigma.fst

Depends on / 依赖: Sigma.fst, toList, w.toList.head
-/
def fstIdx (w : Word M) : Option ι :=
  w.toList.head?.map Sigma.fst

/--
theorem `fstIdx_ne_iff` / 定理 `fstIdx_ne_iff`

English:
theorem fstIdx_ne_iff
  given: {w : Word M} {i}
  proof: not_iff_not.mp by simp [fstIdx]

中文:
定理 fstIdx_ne_iff
  条件: {w : Word M} {i}
  证明: not_iff_not.mp by simp [fstIdx]

Depends on / 依赖: fstIdx, not_iff_not, not_iff_not.mp
-/
theorem fstIdx_ne_iff {w : Word M} {i} :
    fstIdx w != some i ↔ forall l in w.toList.head?, i != Sigma.fst l :=
not_iff_not.mp by simp [fstIdx]

variable (M)

/-- Given an index `i : ι`, `Pair M i` is the type of pairs `(head, tail)` where `head : M i` and
`tail : Word M`, subject to the constraint that first letter of `tail` can't be `⟨i, m⟩`.
By prepending `head` to `tail`, one obtains a new word. We'll show that any word can be uniquely
obtained in this way. -/
@[ext]
/--
Definition of `Pair` / `Pair` 的定义

English:
structure Pair
  parameters: (i : ι)
  axioms and operations (3):
    - head : M i
    - tail : Word M
    - fstIdx_ne : fstIdx tail != some i

中文:
结构 对
  参数: (i : ι)
  公理与运算 (3 个):
    - head : M i
    - tail : Word M
    - fstIdx_ne : fstIdx tail != some i
-/
structure Pair (i : ι) where
  /-- An element of `M i`, the first letter of the word. -/
  head : M i
  /-- The remaining letters of the word, excluding the first letter -/
  tail : Word M
  /-- The index first letter of tail of a `Pair M i` is not equal to `i` -/
  fstIdx_ne : fstIdx tail != some i

instance (i : ι) : Inhabited (Pair M i) :=
  ⟨⟨1, empty, by tauto⟩⟩

variable {M}

/-- Construct a new `Word` without any reduction. The underlying list of
`cons m w _ _` is `⟨_, m⟩::w` -/
@[simps]
/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: {i} (m : M i) (w : Word M) (hmw : w.fstIdx != some i) (h1 : m != 1)
  body: { toList := ⟨i, m⟩ :: w.toList,
    ne_one := by
      simp only [List.mem_cons]
      rintro l (rfl | hl)
      · exact h1
      · exact w.ne_one l hl
    chain_ne := w.chain_ne.cons (fstIdx_ne_iff.mp hmw) }

@[simp]

中文:
定义 cons
  签名: {i} (m : M i) (w : Word M) (hmw : w.fstIdx != some i) (h1 : m != 1)
  定义体: { toList := ⟨i, m⟩ :: w.toList,
    ne_one := by
      simp only [List.mem_cons]
      rintro l (rfl | hl)
      · exact h1
      · exact w.ne_one l hl
    chain_ne := w.chain_ne.cons (fstIdx_ne_iff.mp hmw) }

@[simp]

Depends on / 依赖: List.mem_cons, chain_ne, fstIdx_ne_iff, fstIdx_ne_iff.mp, mem_cons, ne_one, toList, w.chain_ne.cons, w.ne_one, w.toList
-/
def cons {i} (m : M i) (w : Word M) (hmw : w.fstIdx != some i) (h1 : m != 1) : Word M :=
  { toList := ⟨i, m⟩ :: w.toList,
    ne_one := by
      simp only [List.mem_cons]
      rintro l (rfl | hl)
      · exact h1
      · exact w.ne_one l hl
    chain_ne := w.chain_ne.cons (fstIdx_ne_iff.mp hmw) }

@[simp]
/--
theorem `fstIdx_cons` / 定理 `fstIdx_cons`

English:
theorem fstIdx_cons
  given: {i} (m : M i) (w : Word M) (hmw : w.fstIdx != some i) (h1 : m != 1)
  proof: by simp [cons, fstIdx]

@[simp]

中文:
定理 fstIdx_cons
  条件: {i} (m : M i) (w : Word M) (hmw : w.fstIdx != some i) (h1 : m != 1)
  证明: by simp [cons, fstIdx]

@[simp]

Depends on / 依赖: fstIdx
-/
theorem fstIdx_cons {i} (m : M i) (w : Word M) (hmw : w.fstIdx != some i) (h1 : m != 1) :
    fstIdx (cons m w hmw h1) = some i := by simp [cons, fstIdx]

@[simp]
/--
theorem `prod_cons` / 定理 `prod_cons`

English:
theorem prod_cons
  given: (i) (m : M i) (w : Word M) (h1 : m != 1) (h2 : w.fstIdx != some i)
  proof: by
  simp [cons, prod, List.map_cons, List.prod_cons]

中文:
定理 prod_cons
  条件: (i) (m : M i) (w : Word M) (h1 : m != 1) (h2 : w.fstIdx != some i)
  证明: by
  simp [cons, prod, List.map_cons, List.prod_cons]

Depends on / 依赖: List.map_cons, List.prod_cons, map_cons, prod_cons
-/
theorem prod_cons (i) (m : M i) (w : Word M) (h1 : m != 1) (h2 : w.fstIdx != some i) :
    prod (cons m w h2 h1) = of m * prod w := by
  simp [cons, prod, List.map_cons, List.prod_cons]

section
variable [forall i, DecidableEq (M i)]

/--
Definition of `rcons` / `rcons` 的定义

English:
definition rcons
  signature: {i} (p : Pair M i)
  body: if h : p.head = 1 then p.tail
  else cons p.head p.tail p.fstIdx_ne h

@[simp]

中文:
定义 rcons
  签名: {i} (p : 对 M i)
  定义体: if h : p.head = 1 then p.tail
  else cons p.head p.tail p.fstIdx_ne h

@[simp]

Depends on / 依赖: fstIdx_ne, p.fstIdx_ne, p.head, p.tail
-/
def rcons {i} (p : Pair M i) : Word M :=
  if h : p.head = 1 then p.tail
  else cons p.head p.tail p.fstIdx_ne h

@[simp]
/--
theorem `prod_rcons` / 定理 `prod_rcons`

English:
theorem prod_rcons
  given: {i} (p : Pair M i)
  statement: prod (rcons p) = of p.head * prod p.tail
  proof: if hm : p.head = 1 then by rw [rcons, dif_pos hm, hm, map_one, one_mul]
  else by rw [rcons, dif_neg hm, cons, prod, List.map_cons, List.prod_cons, prod]

中文:
定理 prod_rcons
  条件: {i} (p : 对 M i)
  结论: 乘积 (rcons p) = of p.head * 乘积 p.tail
  证明: if hm : p.head = 1 then by rw [rcons, dif_pos hm, hm, map_one, one_mul]
  else by rw [rcons, dif_neg hm, cons, prod, List.map_cons, List.prod_cons, prod]

Depends on / 依赖: List.map_cons, List.prod_cons, dif_neg, dif_pos, map_cons, map_one, one_mul, p.head, prod_cons
-/
theorem prod_rcons {i} (p : Pair M i) : prod (rcons p) = of p.head * prod p.tail :=
  if hm : p.head = 1 then by rw [rcons, dif_pos hm, hm, map_one, one_mul]
  else by rw [rcons, dif_neg hm, cons, prod, List.map_cons, List.prod_cons, prod]

/--
theorem `rcons_inj` / 定理 `rcons_inj`

English:
theorem rcons_inj
  given: {i}
  statement: Function.Injective (rcons : Pair M i -> Word M)
  proof: by
  rintro ⟨m, w, h⟩ ⟨m', w', h'⟩ he
  by_cases hm : m = 1 <;> by_cases hm' : m' = 1
  · simp only [rcons, dif_pos hm, dif_pos hm'] at he
    simp_all
  · exfalso
    simp only [rcons, dif_pos hm, dif_neg hm'] at he
    rw [he] at h
    exact h rfl
  · exfalso
    simp only [rcons, dif_pos hm', dif

中文:
定理 rcons_inj
  条件: {i}
  结论: 函数.单射 (rcons : 对 M i -> Word M)
  证明: by
  rintro ⟨m, w, h⟩ ⟨m', w', h'⟩ he
  by_cases hm : m = 1 <;> by_cases hm' : m' = 1
  · simp only [rcons, dif_pos hm, dif_pos hm'] at he
    simp_all
  · exfalso
    simp only [rcons, dif_pos hm, dif_neg hm'] at he
    rw [he] at h
    exact h rfl
  · exfalso
    simp only [rcons, dif_pos hm', dif

Depends on / 依赖: Subtype, Subtype.ext_iff, Subtype.mk_eq_mk, dif_neg, dif_pos, eq_self_iff_true, ext_iff, heq_iff_eq, mk_eq_mk, toList, w.toList
-/
theorem rcons_inj {i} : Function.Injective (rcons : Pair M i -> Word M) := by
  rintro ⟨m, w, h⟩ ⟨m', w', h'⟩ he
  by_cases hm : m = 1 <;> by_cases hm' : m' = 1
  · simp only [rcons, dif_pos hm, dif_pos hm'] at he
    simp_all
  · exfalso
    simp only [rcons, dif_pos hm, dif_neg hm'] at he
    rw [he] at h
    exact h rfl
  · exfalso
    simp only [rcons, dif_pos hm', dif_neg hm] at he
    rw [← he] at h'
    exact h' rfl
  · have : m = m' ∧ w.toList = w'.toList := by
      simpa [cons, rcons, dif_neg hm, dif_neg hm', eq_self_iff_true, Subtype.mk_eq_mk,
        heq_iff_eq, ← Subtype.ext_iff] using he
    rcases this with ⟨rfl, h⟩
    congr
    exact Word.ext h

/--
theorem `mem_rcons_iff` / 定理 `mem_rcons_iff`

English:
theorem mem_rcons_iff
  given: {i j : ι} (p : Pair M i) (m : M j)
  proof: by
  simp only [rcons, cons, ne_eq]
  grind

中文:
定理 mem_rcons_iff
  条件: {i j : ι} (p : 对 M i) (m : M j)
  证明: by
  simp only [rcons, cons, ne_eq]
  grind

Depends on / 依赖: ne_eq
-/
theorem mem_rcons_iff {i j : ι} (p : Pair M i) (m : M j) :
    ⟨_, m⟩ in (rcons p).toList ↔ ⟨_, m⟩ in p.tail.toList ∨
      m != 1 ∧ (exists h : i = j, m = h ▸ p.head) := by
  simp only [rcons, cons, ne_eq]
  grind

end

/-- Induct on a word by adding letters one at a time without reduction,
effectively inducting on the underlying `List`. -/
@[elab_as_elim]
/--
Definition of `consRecOn` / `consRecOn` 的定义

English:
definition consRecOn
  signature: {motive : Word M -> Sort*} (w : Word M) (empty : motive empty)
  body: by
  rcases w with ⟨w, h1, h2⟩
  induction w with
  | nil => exact empty
  | cons m w ih =>
    refine cons m.1 m.2 ⟨w, fun _ hl => h1 _ (List.mem_cons_of_mem _ hl), h2.tail⟩ ?_ ?_ (ih _ _)
    · rw [List.isChain_cons] at h2
      simp only [fstIdx, ne_eq, Option.map_eq_some_iff,
        Sigma.exist

中文:
定义 consRecOn
  签名: {motive : Word M -> 类型层*} (w : Word M) (empty : motive empty)
  定义体: by
  rcases w with ⟨w, h1, h2⟩
  induction w with
  | nil => exact empty
  | cons m w ih =>
    refine cons m.1 m.2 ⟨w, fun _ hl => h1 _ (List.mem_cons_of_mem _ hl), h2.tail⟩ ?_ ?_ (ih _ _)
    · rw [List.isChain_cons] at h2
      simp only [fstIdx, ne_eq, Option.map_eq_some_iff,
        Sigma.exist

Depends on / 依赖: List.isChain_cons, List.mem_cons_of_mem, List.mem_cons_self, Option.map_eq_some_iff, Sigma.exists, exists_and_right, exists_eq_right, fstIdx, h2.tail, isChain_cons, map_eq_some_iff, mem_cons_of_mem, mem_cons_self, ne_eq, not_exists
-/
def consRecOn {motive : Word M -> Sort*} (w : Word M) (empty : motive empty)
    (cons : forall (i) (m : M i) (w) h1 h2, motive w -> motive (cons m w h1 h2)) :
    motive w := by
  rcases w with ⟨w, h1, h2⟩
  induction w with
  | nil => exact empty
  | cons m w ih =>
    refine cons m.1 m.2 ⟨w, fun _ hl => h1 _ (List.mem_cons_of_mem _ hl), h2.tail⟩ ?_ ?_ (ih _ _)
    · rw [List.isChain_cons] at h2
      simp only [fstIdx, ne_eq, Option.map_eq_some_iff,
        Sigma.exists, exists_and_right, exists_eq_right, not_exists]
      intro m' hm'
      exact h2.1 _ hm' rfl
    · exact h1 _ List.mem_cons_self

@[simp]
/--
theorem `consRecOn_empty` / 定理 `consRecOn_empty`

English:
theorem consRecOn_empty
  statement: {motive : Word M -> Sort*} (h_empty : motive empty)
  proof: rfl

@[simp]

中文:
定理 consRecOn_empty
  结论: {motive : Word M -> 类型层*} (h_empty : motive empty)
  证明: rfl

@[simp]
-/
theorem consRecOn_empty {motive : Word M -> Sort*} (h_empty : motive empty)
    (h_cons : forall (i) (m : M i) (w) h1 h2, motive w -> motive (cons m w h1 h2)) :
    consRecOn empty h_empty h_cons = h_empty := rfl

@[simp]
/--
theorem `consRecOn_cons` / 定理 `consRecOn_cons`

English:
theorem consRecOn_cons
  statement: {motive : Word M -> Sort*} (i) (m : M i) (w : Word M) h1 h2
  proof: rfl

中文:
定理 consRecOn_cons
  结论: {motive : Word M -> 类型层*} (i) (m : M i) (w : Word M) h1 h2
  证明: rfl
-/
theorem consRecOn_cons {motive : Word M -> Sort*} (i) (m : M i) (w : Word M) h1 h2
    (h_empty : motive empty)
    (h_cons : forall (i) (m : M i) (w) h1 h2, motive w -> motive (cons m w h1 h2)) :
    consRecOn (cons m w h1 h2) h_empty h_cons = h_cons i m w h1 h2
      (consRecOn w h_empty h_cons) := rfl

variable [DecidableEq ι] [forall i, DecidableEq (M i)]

set_option backward.privateInPublic true in
-- This definition is computable but not very nice to look at. Thankfully we don't have to inspect
-- it, since `rcons` is known to be injective.
/--
Definition of `equivPairAux` / `equivPairAux` 的定义

English:
definition equivPairAux
  signature: (i) (w : Word M)
  body: consRecOn w ⟨⟨1, .empty, by simp [fstIdx, empty]⟩, by simp [rcons]⟩
    fun j m w h1 h2 _ =>
      if ij : i = j then
        { val :=
          { head := ij ▸ m
            tail := w
            fstIdx_ne := ij ▸ h1 }
          property := by subst ij; simp [rcons, h2] }
      else ⟨⟨1, cons m w h1

中文:
定义 equivPairAux
  签名: (i) (w : Word M)
  定义体: consRecOn w ⟨⟨1, .empty, by simp [fstIdx, empty]⟩, by simp [rcons]⟩
    fun j m w h1 h2 _ =>
      if ij : i = j then
        { val :=
          { head := ij ▸ m
            tail := w
            fstIdx_ne := ij ▸ h1 }
          property := by subst ij; simp [rcons, h2] }
      else ⟨⟨1, cons m w h1
-/
private def equivPairAux (i) (w : Word M) : { p : Pair M i // rcons p = w } :=
consRecOn w ⟨⟨1, .empty, by simp [fstIdx, empty]⟩, by simp [rcons]⟩
    fun j m w h1 h2 _ =>
      if ij : i = j then
        { val :=
          { head := ij ▸ m
            tail := w
            fstIdx_ne := ij ▸ h1 }
          property := by subst ij; simp [rcons, h2] }
      else ⟨⟨1, cons m w h1 h2, by simp [cons, fstIdx, Ne.symm ij]⟩, by simp [rcons]⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `equivPair` / `equivPair` 的定义

English:
definition equivPair
  signature: (i)
  body: (equivPairAux i w).val
  invFun := rcons
  left_inv w := (equivPairAux i w).property
  right_inv _ := rcons_inj (equivPairAux i _).property

中文:
定义 equivPair
  签名: (i)
  定义体: (equivPairAux i w).val
  invFun := rcons
  left_inv w := (equivPairAux i w).property
  right_inv _ := rcons_inj (equivPairAux i _).property

Depends on / 依赖: equivPairAux
-/
def equivPair (i) : Word M ≃ Pair M i where
  toFun w := (equivPairAux i w).val
  invFun := rcons
  left_inv w := (equivPairAux i w).property
  right_inv _ := rcons_inj (equivPairAux i _).property

/--
theorem `equivPair_symm` / 定理 `equivPair_symm`

English:
theorem equivPair_symm
  given: (i) (p : Pair M i)
  statement: (equivPair i).symm p = rcons p
  proof: rfl

中文:
定理 equivPair_symm
  条件: (i) (p : 对 M i)
  结论: (equivPair i).symm p = rcons p
  证明: rfl
-/
theorem equivPair_symm (i) (p : Pair M i) : (equivPair i).symm p = rcons p :=
  rfl

/--
theorem `equivPair_eq_of_fstIdx_ne` / 定理 `equivPair_eq_of_fstIdx_ne`

English:
theorem equivPair_eq_of_fstIdx_ne
  given: {i} {w : Word M} (h : fstIdx w != some i)
  proof: (equivPair i).eq_symm_apply.mp Eq.symm (dif_pos rfl)

中文:
定理 equivPair_eq_of_fstIdx_ne
  条件: {i} {w : Word M} (h : fstIdx w != some i)
  证明: (equivPair i).eq_symm_apply.mp Eq.symm (dif_pos rfl)

Depends on / 依赖: Eq.symm, dif_pos, eq_symm_apply, eq_symm_apply.mp, equivPair
-/
theorem equivPair_eq_of_fstIdx_ne {i} {w : Word M} (h : fstIdx w != some i) :
    equivPair i w = ⟨1, w, h⟩ :=
(equivPair i).eq_symm_apply.mp Eq.symm (dif_pos rfl)

/--
theorem `mem_equivPair_tail_iff` / 定理 `mem_equivPair_tail_iff`

English:
theorem mem_equivPair_tail_iff
  given: {i j : ι} {w : Word M} (m : M i)
  proof: by
  simp only [equivPair, equivPairAux, ne_eq, Equiv.coe_fn_mk]
  induction w using consRecOn with
  | empty => simp
  | cons k g tail h1 h2 ih =>
    simp only [consRecOn_cons]
    split_ifs with h
    · subst k
      by_cases hij : j = i <;> simp_all
    · by_cases hik : i = k
      · subst i; si

中文:
定理 mem_equivPair_tail_iff
  条件: {i j : ι} {w : Word M} (m : M i)
  证明: by
  simp only [equivPair, equivPairAux, ne_eq, Equiv.coe_fn_mk]
  induction w using consRecOn with
  | empty => simp
  | cons k g tail h1 h2 ih =>
    simp only [consRecOn_cons]
    split_ifs with h
    · subst k
      by_cases hij : j = i <;> simp_all
    · by_cases hik : i = k
      · subst i; si

Depends on / 依赖: Equiv.coe_fn_mk, Ne.symm, coe_fn_mk, consRecOn, consRecOn_cons, eq_comm, equivPair, equivPairAux, ne_eq, or_comm, split_ifs
-/
theorem mem_equivPair_tail_iff {i j : ι} {w : Word M} (m : M i) :
    (⟨i, m⟩ in (equivPair j w).tail.toList) ↔ ⟨i, m⟩ in w.toList.tail
      ∨ i != j ∧ exists h : w.toList != [], w.toList.head h = ⟨i, m⟩ := by
  simp only [equivPair, equivPairAux, ne_eq, Equiv.coe_fn_mk]
  induction w using consRecOn with
  | empty => simp
  | cons k g tail h1 h2 ih =>
    simp only [consRecOn_cons]
    split_ifs with h
    · subst k
      by_cases hij : j = i <;> simp_all
    · by_cases hik : i = k
      · subst i; simp_all [@eq_comm _ m g, @eq_comm _ k j, or_comm]
      · simp [hik, Ne.symm hik]

/--
theorem `mem_of_mem_equivPair_tail` / 定理 `mem_of_mem_equivPair_tail`

English:
theorem mem_of_mem_equivPair_tail
  given: {i j : ι} {w : Word M} (m : M i)
  proof: by
  rw [mem_equivPair_tail_iff]
  rintro (h | h)
  · exact List.mem_of_mem_tail h
  · revert h; cases w.toList <;> simp +contextual

中文:
定理 mem_of_mem_equivPair_tail
  条件: {i j : ι} {w : Word M} (m : M i)
  证明: by
  rw [mem_equivPair_tail_iff]
  rintro (h | h)
  · exact List.mem_of_mem_tail h
  · revert h; cases w.toList <;> simp +contextual

Depends on / 依赖: List.mem_of_mem_tail, contextual, mem_equivPair_tail_iff, mem_of_mem_tail, revert, toList, w.toList
-/
theorem mem_of_mem_equivPair_tail {i j : ι} {w : Word M} (m : M i) :
    (⟨i, m⟩ in (equivPair j w).tail.toList) -> ⟨i, m⟩ in w.toList := by
  rw [mem_equivPair_tail_iff]
  rintro (h | h)
  · exact List.mem_of_mem_tail h
  · revert h; cases w.toList <;> simp +contextual

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `equivPair_head` / 定理 `equivPair_head`

English:
theorem equivPair_head
  given: {i : ι} {w : Word M}
  proof: by
  simp only [equivPair, equivPairAux]
  induction w using consRecOn with
  | empty => simp
  | cons head =>
    by_cases hi : i = head
    · subst hi; simp
    · simp [hi, Ne.symm hi]

中文:
定理 equivPair_head
  条件: {i : ι} {w : Word M}
  证明: by
  simp only [equivPair, equivPairAux]
  induction w using consRecOn with
  | empty => simp
  | cons head =>
    by_cases hi : i = head
    · subst hi; simp
    · simp [hi, Ne.symm hi]

Depends on / 依赖: Ne.symm, consRecOn, equivPair, equivPairAux
-/
theorem equivPair_head {i : ι} {w : Word M} :
    (equivPair i w).head =
      if h : exists (h : w.toList != []), (w.toList.head h).1 = i
      then h.snd ▸ (w.toList.head h.1).2
      else 1 := by
  simp only [equivPair, equivPairAux]
  induction w using consRecOn with
  | empty => simp
  | cons head =>
    by_cases hi : i = head
    · subst hi; simp
    · simp [hi, Ne.symm hi]

/--
Instance `summandAction` / 实例 `summandAction`

English:
instance summandAction
  signature: (i)
  body: rcons { equivPair i w with head := m * (equivPair i w).head }
  one_smul w := by
    apply (equivPair i).symm_apply_eq.mpr
    simp [equivPair]
  mul_smul m m' w := by
    dsimp +instances [instHSMul]
    simp [mul_assoc, ← equivPair_symm, Equiv.apply_symm_apply]

中文:
实例 summandAction
  签名: (i)
  定义体: rcons { equivPair i w with head := m * (equivPair i w).head }
  one_smul w := by
    apply (equivPair i).symm_apply_eq.mpr
    simp [equivPair]
  mul_smul m m' w := by
    dsimp +instances [instHSMul]
    simp [mul_assoc, ← equivPair_symm, Equiv.apply_symm_apply]

Depends on / 依赖: equivPair
-/
instance summandAction (i) : MulAction (M i) (Word M) where
  smul m w := rcons { equivPair i w with head := m * (equivPair i w).head }
  one_smul w := by
    apply (equivPair i).symm_apply_eq.mpr
    simp [equivPair]
  mul_smul m m' w := by
    dsimp +instances [instHSMul]
    simp [mul_assoc, ← equivPair_symm, Equiv.apply_symm_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction (CoprodI M) (Word M)
  body: MulAction.ofEndHom (lift fun _ => MulAction.toEndHom)

中文:
实例 :
  签名: 乘法作用 (余prodI M) (Word M)
  定义体: MulAction.ofEndHom (lift fun _ => MulAction.toEndHom)

Depends on / 依赖: MulAction, MulAction.ofEndHom, MulAction.toEndHom, ofEndHom, toEndHom
-/
instance : MulAction (CoprodI M) (Word M) :=
  MulAction.ofEndHom (lift fun _ => MulAction.toEndHom)

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: {i} (m : M i) (w : Word M)
  proof: rfl

中文:
定理 smul_def
  条件: {i} (m : M i) (w : Word M)
  证明: rfl

Depends on / 依赖: equivPair
-/
theorem smul_def {i} (m : M i) (w : Word M) :
    m • w = rcons { equivPair i w with head := m * (equivPair i w).head } :=
  rfl

/--
theorem `of_smul_def` / 定理 `of_smul_def`

English:
theorem of_smul_def
  given: (i) (w : Word M) (m : M i)
  proof: rfl

中文:
定理 of_smul_def
  条件: (i) (w : Word M) (m : M i)
  证明: rfl

Depends on / 依赖: equivPair
-/
theorem of_smul_def (i) (w : Word M) (m : M i) :
    of m • w = rcons { equivPair i w with head := m * (equivPair i w).head } :=
  rfl

/--
theorem `equivPair_smul_same` / 定理 `equivPair_smul_same`

English:
theorem equivPair_smul_same
  given: {i} (m : M i) (w : Word M)
  proof: by
  rw [of_smul_def]; rw [← equivPair_symm]
  simp

@[simp]

中文:
定理 equivPair_smul_same
  条件: {i} (m : M i) (w : Word M)
  证明: by
  rw [of_smul_def]; rw [← equivPair_symm]
  simp

@[simp]

Depends on / 依赖: equivPair_symm, of_smul_def
-/
theorem equivPair_smul_same {i} (m : M i) (w : Word M) :
    equivPair i (of m • w) = ⟨m * (equivPair i w).head, (equivPair i w).tail,
      (equivPair i w).fstIdx_ne⟩ := by
  rw [of_smul_def]; rw [← equivPair_symm]
  simp

@[simp]
/--
theorem `equivPair_tail` / 定理 `equivPair_tail`

English:
theorem equivPair_tail
  given: {i} (p : Pair M i)
  proof: equivPair_eq_of_fstIdx_ne _

中文:
定理 equivPair_tail
  条件: {i} (p : 对 M i)
  证明: equivPair_eq_of_fstIdx_ne _

Depends on / 依赖: equivPair_eq_of_fstIdx_ne
-/
theorem equivPair_tail {i} (p : Pair M i) :
    equivPair i p.tail = ⟨1, p.tail, p.fstIdx_ne⟩ :=
  equivPair_eq_of_fstIdx_ne _

/--
theorem `smul_eq_of_smul` / 定理 `smul_eq_of_smul`

English:
theorem smul_eq_of_smul
  given: {i} (m : M i) (w : Word M)
  proof: rfl

中文:
定理 smul_eq_of_smul
  条件: {i} (m : M i) (w : Word M)
  证明: rfl
-/
theorem smul_eq_of_smul {i} (m : M i) (w : Word M) :
    m • w = of m • w := rfl

/--
theorem `mem_smul_iff` / 定理 `mem_smul_iff`

English:
theorem mem_smul_iff
  given: {i j : ι} {m₁ : M i} {m₂ : M j} {w : Word M}
  proof: by
  rw [of_smul_def]; rw [mem_rcons_iff]; rw [mem_equivPair_tail_iff]; rw [equivPair_head]; rw [or_assoc]
  by_cases hij : i = j
  · subst i
    simp only [not_true, ne_eq, false_and, exists_prop, true_and, false_or]
    by_cases hw : ⟨j, m₁⟩ in w.toList.tail
    · simp [hw, show m₁ != 1 from w.ne_

中文:
定理 mem_smul_iff
  条件: {i j : ι} {m₁ : M i} {m₂ : M j} {w : Word M}
  证明: by
  rw [of_smul_def]; rw [mem_rcons_iff]; rw [mem_equivPair_tail_iff]; rw [equivPair_head]; rw [or_assoc]
  by_cases hij : i = j
  · subst i
    simp only [not_true, ne_eq, false_and, exists_prop, true_and, false_or]
    by_cases hw : ⟨j, m₁⟩ in w.toList.tail
    · simp [hw, show m₁ != 1 from w.ne_

Depends on / 依赖: List.head, List.mem_of_mem_tail, Option.mem_def, Option.some.injEq, _eq_some_head, and_congr_right_iff, constr, equivPair_head, exists_prop, false_and, false_or, mem_def, mem_equivPair_tail_iff, mem_of_mem_tail, mem_rcons_iff, ne_eq, ne_one, not_true, of_smul_def, or_assoc
-/
theorem mem_smul_iff {i j : ι} {m₁ : M i} {m₂ : M j} {w : Word M} :
    ⟨_, m₁⟩ in (of m₂ • w).toList ↔
      (¬i = j ∧ ⟨i, m₁⟩ in w.toList)
      ∨ (m₁ != 1 ∧ exists (hij : i = j), (⟨i, m₁⟩ in w.toList.tail) ∨
        (exists m', ⟨j, m'⟩ in w.toList.head? ∧ m₁ = hij ▸ (m₂ * m')) ∨
        (w.fstIdx != some j ∧ m₁ = hij ▸ m₂)) := by
  rw [of_smul_def]; rw [mem_rcons_iff]; rw [mem_equivPair_tail_iff]; rw [equivPair_head]; rw [or_assoc]
  by_cases hij : i = j
  · subst i
    simp only [not_true, ne_eq, false_and, exists_prop, true_and, false_or]
    by_cases hw : ⟨j, m₁⟩ in w.toList.tail
    · simp [hw, show m₁ != 1 from w.ne_one _ (List.mem_of_mem_tail hw)]
    · simp only [hw, false_or, Option.mem_def, and_congr_right_iff]
      intro hm1
      split_ifs with h
      · rcases h with ⟨hnil, rfl⟩
        simp only [List.head?_eq_some_head hnil, Option.some.injEq]
        constructor
        · rintro rfl
          exact Or.inl ⟨_, rfl, rfl⟩
        · rintro (⟨_, h, rfl⟩ | hm')
          · simp only [Sigma.ext_iff, heq_eq_eq, true_and] at h
            subst h
            rfl
          · simp only [fstIdx, Option.map_eq_some_iff, Sigma.exists,
              exists_and_right, exists_eq_right, not_exists] at hm'
            exact (hm'.1 (w.toList.head hnil).2 (by rw [List.head?_eq_some_head])).elim
      · revert h
        rw [fstIdx]
        cases w.toList
        · simp
        · simp +contextual [Sigma.ext_iff]
  · rcases w with ⟨_ | _, _, _⟩ <;>
    simp [or_comm, hij, Ne.symm hij, eq_comm]

/--
theorem `mem_smul_iff_of_ne` / 定理 `mem_smul_iff_of_ne`

English:
theorem mem_smul_iff_of_ne
  given: {i j : ι} (hij : i != j) {m₁ : M i} {m₂ : M j} {w : Word M}
  proof: by
  simp [mem_smul_iff, *]

中文:
定理 mem_smul_iff_of_ne
  条件: {i j : ι} (hij : i != j) {m₁ : M i} {m₂ : M j} {w : Word M}
  证明: by
  simp [mem_smul_iff, *]

Depends on / 依赖: mem_smul_iff
-/
theorem mem_smul_iff_of_ne {i j : ι} (hij : i != j) {m₁ : M i} {m₂ : M j} {w : Word M} :
    ⟨_, m₁⟩ in (of m₂ • w).toList ↔ ⟨i, m₁⟩ in w.toList := by
  simp [mem_smul_iff, *]

/--
theorem `cons_eq_smul` / 定理 `cons_eq_smul`

English:
theorem cons_eq_smul
  given: {i} {m : M i} {ls h1 h2}
  proof: by
  rw [of_smul_def]; rw [equivPair_eq_of_fstIdx_ne _]
  · simp [cons, rcons, h2]
  · exact h1

中文:
定理 cons_eq_smul
  条件: {i} {m : M i} {ls h1 h2}
  证明: by
  rw [of_smul_def]; rw [equivPair_eq_of_fstIdx_ne _]
  · simp [cons, rcons, h2]
  · exact h1

Depends on / 依赖: equivPair_eq_of_fstIdx_ne, of_smul_def
-/
theorem cons_eq_smul {i} {m : M i} {ls h1 h2} :
    cons m ls h1 h2 = of m • ls := by
  rw [of_smul_def]; rw [equivPair_eq_of_fstIdx_ne _]
  · simp [cons, rcons, h2]
  · exact h1

/--
theorem `rcons_eq_smul` / 定理 `rcons_eq_smul`

English:
theorem rcons_eq_smul
  given: {i} (p : Pair M i)
  proof: by
  simp [of_smul_def]

@[simp]

中文:
定理 rcons_eq_smul
  条件: {i} (p : 对 M i)
  证明: by
  simp [of_smul_def]

@[simp]

Depends on / 依赖: of_smul_def
-/
theorem rcons_eq_smul {i} (p : Pair M i) :
    rcons p = of p.head • p.tail := by
  simp [of_smul_def]

@[simp]
/--
theorem `equivPair_head_smul_equivPair_tail` / 定理 `equivPair_head_smul_equivPair_tail`

English:
theorem equivPair_head_smul_equivPair_tail
  given: {i : ι} (w : Word M)
  proof: by
  rw [← rcons_eq_smul]; rw [← equivPair_symm]; rw [Equiv.symm_apply_apply]

中文:
定理 equivPair_head_smul_equivPair_tail
  条件: {i : ι} (w : Word M)
  证明: by
  rw [← rcons_eq_smul]; rw [← equivPair_symm]; rw [Equiv.symm_apply_apply]

Depends on / 依赖: Equiv.symm_apply_apply, equivPair_symm, rcons_eq_smul, symm_apply_apply
-/
theorem equivPair_head_smul_equivPair_tail {i : ι} (w : Word M) :
    of (equivPair i w).head • (equivPair i w).tail = w := by
  rw [← rcons_eq_smul]; rw [← equivPair_symm]; rw [Equiv.symm_apply_apply]

/--
theorem `equivPair_tail_eq_inv_smul` / 定理 `equivPair_tail_eq_inv_smul`

English:
theorem equivPair_tail_eq_inv_smul
  statement: {G : ι -> Type*} [forall i, Group (G i)]
  proof: Eq.symm inv_smul_eq_iff.2 (equivPair_head_smul_equivPair_tail w).symm

@[elab_as_elim]

中文:
定理 equivPair_tail_eq_inv_smul
  结论: {G : ι -> 类型} [对任意 i, 群 (G i)]
  证明: Eq.symm inv_smul_eq_iff.2 (equivPair_head_smul_equivPair_tail w).symm

@[elab_as_elim]

Depends on / 依赖: Eq.symm, equivPair_head_smul_equivPair_tail, inv_smul_eq_iff
-/
theorem equivPair_tail_eq_inv_smul {G : ι -> Type*} [forall i, Group (G i)]
    [forall i, DecidableEq (G i)] {i} (w : Word G) :
    (equivPair i w).tail = (of (equivPair i w).head)⁻¹ • w :=
Eq.symm inv_smul_eq_iff.2 (equivPair_head_smul_equivPair_tail w).symm

@[elab_as_elim]
/--
theorem `smul_induction` / 定理 `smul_induction`

English:
theorem smul_induction
  statement: {motive : Word M -> Prop} (empty : motive empty)
  proof: by
  induction w using consRecOn with
  | empty => exact empty
  | cons _ _ _ _ _ ih =>
    rw [cons_eq_smul]
    exact smul _ _ _ ih

@[simp]

中文:
定理 smul_induction
  结论: {motive : Word M -> 命题} (empty : motive empty)
  证明: by
  induction w using consRecOn with
  | empty => exact empty
  | cons _ _ _ _ _ ih =>
    rw [cons_eq_smul]
    exact smul _ _ _ ih

@[simp]

Depends on / 依赖: consRecOn, cons_eq_smul
-/
theorem smul_induction {motive : Word M -> Prop} (empty : motive empty)
    (smul : forall (i) (m : M i) (w), motive w -> motive (of m • w)) (w : Word M) : motive w := by
  induction w using consRecOn with
  | empty => exact empty
  | cons _ _ _ _ _ ih =>
    rw [cons_eq_smul]
    exact smul _ _ _ ih

@[simp]
/--
theorem `prod_smul` / 定理 `prod_smul`

English:
theorem prod_smul
  given: (m)
  statement: forall w : Word M, prod (m • w) = m * prod w
  proof: by
  induction m using CoprodI.induction_on with
  | one =>
    intro
    rw [one_smul]; rw [one_mul]
  | of _ =>
    intros
    rw [of_smul_def]; rw [prod_rcons]; rw [of.map_mul]; rw [mul_assoc]; rw [← prod_rcons]; rw [← equivPair_symm]; rw [Equiv.symm_apply_apply]
  | mul x y hx hy =>
    intro w


中文:
定理 prod_smul
  条件: (m)
  结论: 对任意 w : Word M, 乘积 (m • w) = m * 乘积 w
  证明: by
  induction m using CoprodI.induction_on with
  | one =>
    intro
    rw [one_smul]; rw [one_mul]
  | of _ =>
    intros
    rw [of_smul_def]; rw [prod_rcons]; rw [of.map_mul]; rw [mul_assoc]; rw [← prod_rcons]; rw [← equivPair_symm]; rw [Equiv.symm_apply_apply]
  | mul x y hx hy =>
    intro w


Depends on / 依赖: CoprodI, CoprodI.induction_on, Equiv.symm_apply_apply, equivPair_symm, induction_on, intros, map_mul, mul_assoc, mul_smul, of.map_mul, of_smul_def, one_mul, one_smul, prod_rcons, symm_apply_apply
-/
theorem prod_smul (m) : forall w : Word M, prod (m • w) = m * prod w := by
  induction m using CoprodI.induction_on with
  | one =>
    intro
    rw [one_smul]; rw [one_mul]
  | of _ =>
    intros
    rw [of_smul_def]; rw [prod_rcons]; rw [of.map_mul]; rw [mul_assoc]; rw [← prod_rcons]; rw [← equivPair_symm]; rw [Equiv.symm_apply_apply]
  | mul x y hx hy =>
    intro w
    rw [mul_smul]; rw [hx]; rw [hy]; rw [mul_assoc]

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : CoprodI M ≃ Word M where
  body: m • empty
  invFun w := prod w
  left_inv m := by dsimp only; rw [prod_smul, prod_empty, mul_one]
  right_inv := by
    apply smul_induction
    · dsimp only
      rw [prod_empty]; rw [one_smul]
    · dsimp only
      intro i m w ih
      rw [prod_smul]; rw [mul_smul]; rw [ih]

中文:
定义 equiv
  签名: : 余prodI M ≃ Word M where
  定义体: m • empty
  invFun w := prod w
  left_inv m := by dsimp only; rw [prod_smul, prod_empty, mul_one]
  right_inv := by
    apply smul_induction
    · dsimp only
      rw [prod_empty]; rw [one_smul]
    · dsimp only
      intro i m w ih
      rw [prod_smul]; rw [mul_smul]; rw [ih]
-/
def equiv : CoprodI M ≃ Word M where
  toFun m := m • empty
  invFun w := prod w
  left_inv m := by dsimp only; rw [prod_smul, prod_empty, mul_one]
  right_inv := by
    apply smul_induction
    · dsimp only
      rw [prod_empty]; rw [one_smul]
    · dsimp only
      intro i m w ih
      rw [prod_smul]; rw [mul_smul]; rw [ih]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableEq (Word M)
  body: Function.Injective.decidableEq fun _ _ => Word.ext

中文:
实例 :
  签名: DecidableEq (Word M)
  定义体: Function.Injective.decidableEq fun _ _ => Word.ext

Depends on / 依赖: Function, Function.Injective.decidableEq, Injective, Word.ext, decidableEq
-/
instance : DecidableEq (Word M) :=
  Function.Injective.decidableEq fun _ _ => Word.ext

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableEq (CoprodI M)
  body: Equiv.decidableEq Word.equiv

中文:
实例 :
  签名: DecidableEq (余prodI M)
  定义体: Equiv.decidableEq Word.equiv

Depends on / 依赖: Equiv.decidableEq, Word.equiv, decidableEq
-/
instance : DecidableEq (CoprodI M) :=
  Equiv.decidableEq Word.equiv

end Word

variable (M) in
/--
Inductive type `NeWord` / 归纳类型 `NeWord`

English:
inductive NeWord
  parameters: : ι -> ι -> Type _
  constructors (2):
    - singleton: forall {i : ι} (x : M i), x != 1 -> NeWord i i
    - append: forall {i j k l} (_w₁ : NeWord i j) (_hne : j != k) (_w₂ : NeWord k l), NeWord i l

中文:
归纳类型 NeWord
  参数: : ι -> ι -> 类型 _
  构造子 (2 个):
    - singleton: 对任意 {i : ι} (x : M i), x != 1 -> NeWord i i
    - append: 对任意 {i j k l} (_w₁ : NeWord i j) (_hne : j != k) (_w₂ : NeWord k l), NeWord i l
-/
inductive NeWord : ι -> ι -> Type _
  | singleton : forall {i : ι} (x : M i), x != 1 -> NeWord i i
  | append : forall {i j k l} (_w₁ : NeWord i j) (_hne : j != k) (_w₂ : NeWord k l), NeWord i l

namespace NeWord

open Word

/-- The list represented by a given `NeWord` -/
@[simp]
/--
Definition of `toList` / `toList` 的定义

English:
definition toList
  signature: : forall {i j} (_w : NeWord M i j), List (Σ i, M i)

中文:
定义 toList
  签名: : 对任意 {i j} (_w : NeWord M i j), 列表 (Σ i, M i)
-/
def toList : forall {i j} (_w : NeWord M i j), List (Σ i, M i)
  | i, _, singleton x _ => [⟨i, x⟩]
  | _, _, append w₁ _ w₂ => w₁.toList ++ w₂.toList

/--
theorem `toList_ne_nil` / 定理 `toList_ne_nil`

English:
theorem toList_ne_nil
  given: {i j} (w : NeWord M i j)
  statement: w.toList != List.nil
  proof: by
  induction w
  · rintro ⟨rfl⟩
  · apply List.append_ne_nil_of_left_ne_nil
    assumption

中文:
定理 toList_ne_nil
  条件: {i j} (w : NeWord M i j)
  结论: w.toList != 列表.nil
  证明: by
  induction w
  · rintro ⟨rfl⟩
  · apply List.append_ne_nil_of_left_ne_nil
    assumption

Depends on / 依赖: List.append_ne_nil_of_left_ne_nil, append_ne_nil_of_left_ne_nil
-/
theorem toList_ne_nil {i j} (w : NeWord M i j) : w.toList != List.nil := by
  induction w
  · rintro ⟨rfl⟩
  · apply List.append_ne_nil_of_left_ne_nil
    assumption

/-- The first letter of a `NeWord` -/
@[simp]
/--
Definition of `head` / `head` 的定义

English:
definition head
  signature: : forall {i j} (_w : NeWord M i j), M i

中文:
定义 head
  签名: : 对任意 {i j} (_w : NeWord M i j), M i
-/
def head : forall {i j} (_w : NeWord M i j), M i
  | _, _, singleton x _ => x
  | _, _, append w₁ _ _ => w₁.head

/-- The last letter of a `NeWord` -/
@[simp]
/--
Definition of `last` / `last` 的定义

English:
definition last
  signature: : forall {i j} (_w : NeWord M i j), M j

中文:
定义 last
  签名: : 对任意 {i j} (_w : NeWord M i j), M j
-/
def last : forall {i j} (_w : NeWord M i j), M j
  | _, _, singleton x _hne1 => x
  | _, _, append _w₁ _hne w₂ => w₂.last

@[simp]
/--
theorem `toList_head?` / 定理 `toList_head?`

English:
theorem toList_head?
  given: {i j} (w : NeWord M i j)
  statement: w.toList.head? = Option.some ⟨i, w.head⟩
  proof: by
  fun_induction toList with grind [head]

@[simp]

中文:
定理 toList_head?
  条件: {i j} (w : NeWord M i j)
  结论: w.toList.head? = 选项类型.some ⟨i, w.head⟩
  证明: by
  fun_induction toList with grind [head]

@[simp]

Depends on / 依赖: fun_induction, toList
-/
theorem toList_head? {i j} (w : NeWord M i j) : w.toList.head? = Option.some ⟨i, w.head⟩ := by
  fun_induction toList with grind [head]

@[simp]
/--
theorem `toList_getLast?` / 定理 `toList_getLast?`

English:
theorem toList_getLast?
  given: {i j} (w : NeWord M i j)
  statement: w.toList.getLast? = Option.some ⟨j, w.last⟩
  proof: by
  rw [← Option.mem_def]
  induction w
  · rw [Option.mem_def]
    rfl
  · exact List.mem_getLast?_append_of_mem_getLast? (by assumption)

中文:
定理 toList_getLast?
  条件: {i j} (w : NeWord M i j)
  结论: w.toList.getLast? = 选项类型.some ⟨j, w.last⟩
  证明: by
  rw [← Option.mem_def]
  induction w
  · rw [Option.mem_def]
    rfl
  · exact List.mem_getLast?_append_of_mem_getLast? (by assumption)

Depends on / 依赖: List.mem_getLast, Option.mem_def, _append_of_mem_getLast, mem_def, mem_getLast
-/
theorem toList_getLast? {i j} (w : NeWord M i j) : w.toList.getLast? = Option.some ⟨j, w.last⟩ := by
  rw [← Option.mem_def]
  induction w
  · rw [Option.mem_def]
    rfl
  · exact List.mem_getLast?_append_of_mem_getLast? (by assumption)

/--
Definition of `toWord` / `toWord` 的定义

English:
definition toWord
  signature: {i j} (w : NeWord M i j)
  body: w.toList
  ne_one := by
    induction w
    · simpa only [toList, List.mem_singleton, ne_eq, forall_eq]
    · intro l h
      simp only [toList, List.mem_append] at h
      cases h <;> aesop
  chain_ne := by
    induction w
    · exact List.isChain_singleton _
    · refine List.IsChain.append (by as

中文:
定义 toWord
  签名: {i j} (w : NeWord M i j)
  定义体: w.toList
  ne_one := by
    induction w
    · simpa only [toList, List.mem_singleton, ne_eq, forall_eq]
    · intro l h
      simp only [toList, List.mem_append] at h
      cases h <;> aesop
  chain_ne := by
    induction w
    · exact List.isChain_singleton _
    · refine List.IsChain.append (by as

Depends on / 依赖: toList, w.toList
-/
def toWord {i j} (w : NeWord M i j) : Word M where
  toList := w.toList
  ne_one := by
    induction w
    · simpa only [toList, List.mem_singleton, ne_eq, forall_eq]
    · intro l h
      simp only [toList, List.mem_append] at h
      cases h <;> aesop
  chain_ne := by
    induction w
    · exact List.isChain_singleton _
    · refine List.IsChain.append (by assumption) (by assumption) ?_
      intro x hx y hy
      rw [toList_getLast?]; rw [Option.mem_some_iff] at hx
      rw [toList_head?]; rw [Option.mem_some_iff] at hy
      subst hx
      subst hy
      assumption

/--
theorem `of_word` / 定理 `of_word`

English:
theorem of_word
  given: (w : Word M) (h : w != empty)
  statement: exists (i j : _) (w' : NeWord M i j), w'.toWord = w
  proof: by
  suffices exists (i j : _) (w' : NeWord M i j), w'.toWord.toList = w.toList by
    rcases this with ⟨i, j, w, h⟩
    refine ⟨i, j, w, ?_⟩
    ext
    rw [h]
  obtain ⟨l, hnot1, hchain⟩ := w
  induction l with
  | nil => contradiction
  | cons x l hi =>
    rw [List.forall_mem_cons] at hnot1
    

中文:
定理 of_word
  条件: (w : Word M) (h : w != empty)
  结论: 存在 (i j : _) (w' : NeWord M i j), w'.toWord = w
  证明: by
  suffices exists (i j : _) (w' : NeWord M i j), w'.toWord.toList = w.toList by
    rcases this with ⟨i, j, w, h⟩
    refine ⟨i, j, w, ?_⟩
    ext
    rw [h]
  obtain ⟨l, hnot1, hchain⟩ := w
  induction l with
  | nil => contradiction
  | cons x l hi =>
    rw [List.forall_mem_cons] at hnot1
    

Depends on / 依赖: List.forall_mem_cons, List.isChain_cons_cons, NeWord, forall_mem_cons, hchain, isChain_cons_cons, singleton, specialize, toList, toWord, toWord.toList, w.toList
-/
theorem of_word (w : Word M) (h : w != empty) : exists (i j : _) (w' : NeWord M i j), w'.toWord = w := by
  suffices exists (i j : _) (w' : NeWord M i j), w'.toWord.toList = w.toList by
    rcases this with ⟨i, j, w, h⟩
    refine ⟨i, j, w, ?_⟩
    ext
    rw [h]
  obtain ⟨l, hnot1, hchain⟩ := w
  induction l with
  | nil => contradiction
  | cons x l hi =>
    rw [List.forall_mem_cons] at hnot1
    rcases l with - | ⟨y, l⟩
    · refine ⟨x.1, x.1, singleton x.2 hnot1.1, ?_⟩
      simp [toWord]
    · rw [List.isChain_cons_cons] at hchain
      specialize hi hnot1.2 hchain.2 (by rintro ⟨rfl⟩)
      obtain ⟨i, j, w', hw' : w'.toList = y::l⟩ := hi
      obtain rfl : y = ⟨i, w'.head⟩ := by simpa [hw'] using w'.toList_head?
      refine ⟨x.1, j, append (singleton x.2 hnot1.1) hchain.1 w', ?_⟩
      simpa [toWord] using hw'

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: {i j} (w : NeWord M i j)
  body: w.toWord.prod

@[simp]

中文:
定义 乘积
  签名: {i j} (w : NeWord M i j)
  定义体: w.toWord.prod

@[simp]

Depends on / 依赖: toWord, w.toWord.prod
-/
def prod {i j} (w : NeWord M i j) :=
  w.toWord.prod

@[simp]
/--
theorem `singleton_head` / 定理 `singleton_head`

English:
theorem singleton_head
  given: {i} (x : M i) (hne_one : x != 1)
  statement: (singleton x hne_one).head = x
  proof: rfl

@[simp]

中文:
定理 singleton_head
  条件: {i} (x : M i) (hne_one : x != 1)
  结论: (singleton x hne_one).head = x
  证明: rfl

@[simp]
-/
theorem singleton_head {i} (x : M i) (hne_one : x != 1) : (singleton x hne_one).head = x :=
  rfl

@[simp]
/--
theorem `singleton_last` / 定理 `singleton_last`

English:
theorem singleton_last
  given: {i} (x : M i) (hne_one : x != 1)
  statement: (singleton x hne_one).last = x
  proof: rfl

@[simp]

中文:
定理 singleton_last
  条件: {i} (x : M i) (hne_one : x != 1)
  结论: (singleton x hne_one).last = x
  证明: rfl

@[simp]
-/
theorem singleton_last {i} (x : M i) (hne_one : x != 1) : (singleton x hne_one).last = x :=
  rfl

@[simp]
/--
theorem `prod_singleton` / 定理 `prod_singleton`

English:
theorem prod_singleton
  given: {i} (x : M i) (hne_one : x != 1)
  statement: (singleton x hne_one).prod = of x
  proof: by
  simp [toWord, prod, Word.prod]

@[simp]

中文:
定理 prod_singleton
  条件: {i} (x : M i) (hne_one : x != 1)
  结论: (singleton x hne_one).乘积 = of x
  证明: by
  simp [toWord, prod, Word.prod]

@[simp]

Depends on / 依赖: Word.prod, toWord
-/
theorem prod_singleton {i} (x : M i) (hne_one : x != 1) : (singleton x hne_one).prod = of x := by
  simp [toWord, prod, Word.prod]

@[simp]
/--
theorem `append_head` / 定理 `append_head`

English:
theorem append_head
  given: {i j k l} {w₁ : NeWord M i j} {hne : j != k} {w₂ : NeWord M k l}
  proof: rfl

@[simp]

中文:
定理 append_head
  条件: {i j k l} {w₁ : NeWord M i j} {hne : j != k} {w₂ : NeWord M k l}
  证明: rfl

@[simp]
-/
theorem append_head {i j k l} {w₁ : NeWord M i j} {hne : j != k} {w₂ : NeWord M k l} :
    (append w₁ hne w₂).head = w₁.head :=
  rfl

@[simp]
/--
theorem `append_last` / 定理 `append_last`

English:
theorem append_last
  given: {i j k l} {w₁ : NeWord M i j} {hne : j != k} {w₂ : NeWord M k l}
  proof: rfl

@[simp]

中文:
定理 append_last
  条件: {i j k l} {w₁ : NeWord M i j} {hne : j != k} {w₂ : NeWord M k l}
  证明: rfl

@[simp]
-/
theorem append_last {i j k l} {w₁ : NeWord M i j} {hne : j != k} {w₂ : NeWord M k l} :
    (append w₁ hne w₂).last = w₂.last :=
  rfl

@[simp]
/--
theorem `append_prod` / 定理 `append_prod`

English:
theorem append_prod
  given: {i j k l} {w₁ : NeWord M i j} {hne : j != k} {w₂ : NeWord M k l}
  proof: by simp [toWord, prod, Word.prod]

中文:
定理 append_prod
  条件: {i j k l} {w₁ : NeWord M i j} {hne : j != k} {w₂ : NeWord M k l}
  证明: by simp [toWord, prod, Word.prod]

Depends on / 依赖: Word.prod, toWord
-/
theorem append_prod {i j k l} {w₁ : NeWord M i j} {hne : j != k} {w₂ : NeWord M k l} :
    (append w₁ hne w₂).prod = w₁.prod * w₂.prod := by simp [toWord, prod, Word.prod]

/--
Definition of `replaceHead` / `replaceHead` 的定义

English:
definition replaceHead
  signature: : forall {i j : ι} (x : M i) (_hnotone : x != 1) (_w : NeWord M i j), NeWord M i j

中文:
定义 replaceHead
  签名: : 对任意 {i j : ι} (x : M i) (_hnotone : x != 1) (_w : NeWord M i j), NeWord M i j
-/
def replaceHead : forall {i j : ι} (x : M i) (_hnotone : x != 1) (_w : NeWord M i j), NeWord M i j
  | _, _, x, h, singleton _ _ => singleton x h
  | _, _, x, h, append w₁ hne w₂ => append (replaceHead x h w₁) hne w₂

@[simp]
/--
theorem `replaceHead_head` / 定理 `replaceHead_head`

English:
theorem replaceHead_head
  given: {i j : ι} (x : M i) (hnotone : x != 1) (w : NeWord M i j)
  proof: by
  induction w
  · rfl
  · simp [*, replaceHead]

中文:
定理 replaceHead_head
  条件: {i j : ι} (x : M i) (hnotone : x != 1) (w : NeWord M i j)
  证明: by
  induction w
  · rfl
  · simp [*, replaceHead]

Depends on / 依赖: replaceHead
-/
theorem replaceHead_head {i j : ι} (x : M i) (hnotone : x != 1) (w : NeWord M i j) :
    (replaceHead x hnotone w).head = x := by
  induction w
  · rfl
  · simp [*, replaceHead]

/--
Definition of `mulHead` / `mulHead` 的定义

English:
definition mulHead
  signature: {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head != 1)
  body: replaceHead (x * w.head) hnotone w

@[simp]

中文:
定义 mulHead
  签名: {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head != 1)
  定义体: replaceHead (x * w.head) hnotone w

@[simp]

Depends on / 依赖: hnotone, replaceHead, w.head
-/
def mulHead {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head != 1) : NeWord M i j :=
  replaceHead (x * w.head) hnotone w

@[simp]
/--
theorem `mulHead_head` / 定理 `mulHead_head`

English:
theorem mulHead_head
  given: {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head != 1)
  proof: by
  induction w
  · rfl
  · simp [*, mulHead]

@[simp]

中文:
定理 mulHead_head
  条件: {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head != 1)
  证明: by
  induction w
  · rfl
  · simp [*, mulHead]

@[simp]

Depends on / 依赖: mulHead
-/
theorem mulHead_head {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head != 1) :
    (mulHead w x hnotone).head = x * w.head := by
  induction w
  · rfl
  · simp [*, mulHead]

@[simp]
/--
theorem `mulHead_prod` / 定理 `mulHead_prod`

English:
theorem mulHead_prod
  given: {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head != 1)
  proof: by
  unfold mulHead
  induction w with
  | singleton => simp [replaceHead]
  | append _ _ _ w_ih_w₁ w_ih_w₂ =>
    specialize w_ih_w₁ _ hnotone
    simp only [replaceHead, append_prod, ← mul_assoc]
    congr 1

中文:
定理 mulHead_prod
  条件: {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head != 1)
  证明: by
  unfold mulHead
  induction w with
  | singleton => simp [replaceHead]
  | append _ _ _ w_ih_w₁ w_ih_w₂ =>
    specialize w_ih_w₁ _ hnotone
    simp only [replaceHead, append_prod, ← mul_assoc]
    congr 1

Depends on / 依赖: append, append_prod, hnotone, mulHead, mul_assoc, replaceHead, singleton, specialize
-/
theorem mulHead_prod {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head != 1) :
    (mulHead w x hnotone).prod = of x * w.prod := by
  unfold mulHead
  induction w with
  | singleton => simp [replaceHead]
  | append _ _ _ w_ih_w₁ w_ih_w₂ =>
    specialize w_ih_w₁ _ hnotone
    simp only [replaceHead, append_prod, ← mul_assoc]
    congr 1

section Group

variable {G : ι -> Type*} [forall i, Group (G i)]

/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: : forall {i j} (_w : NeWord G i j), NeWord G j i

中文:
定义 inv
  签名: : 对任意 {i j} (_w : NeWord G i j), NeWord G j i
-/
def inv : forall {i j} (_w : NeWord G i j), NeWord G j i
  | _, _, singleton x h => singleton x⁻¹ (mt inv_eq_one.mp h)
  | _, _, append w₁ h w₂ => append w₂.inv h.symm w₁.inv

@[simp]
/--
theorem `inv_prod` / 定理 `inv_prod`

English:
theorem inv_prod
  given: {i j} (w : NeWord G i j)
  statement: w.inv.prod = w.prod⁻¹
  proof: by
  induction w <;> simp [inv, *]

@[simp]

中文:
定理 inv_prod
  条件: {i j} (w : NeWord G i j)
  结论: w.inv.乘积 = w.乘积⁻¹
  证明: by
  induction w <;> simp [inv, *]

@[simp]
-/
theorem inv_prod {i j} (w : NeWord G i j) : w.inv.prod = w.prod⁻¹ := by
  induction w <;> simp [inv, *]

@[simp]
/--
theorem `inv_head` / 定理 `inv_head`

English:
theorem inv_head
  given: {i j} (w : NeWord G i j)
  statement: w.inv.head = w.last⁻¹
  proof: by
  induction w <;> simp [inv, *]

@[simp]

中文:
定理 inv_head
  条件: {i j} (w : NeWord G i j)
  结论: w.inv.head = w.last⁻¹
  证明: by
  induction w <;> simp [inv, *]

@[simp]
-/
theorem inv_head {i j} (w : NeWord G i j) : w.inv.head = w.last⁻¹ := by
  induction w <;> simp [inv, *]

@[simp]
/--
theorem `inv_last` / 定理 `inv_last`

English:
theorem inv_last
  given: {i j} (w : NeWord G i j)
  statement: w.inv.last = w.head⁻¹
  proof: by
  induction w <;> simp [inv, *]

中文:
定理 inv_last
  条件: {i j} (w : NeWord G i j)
  结论: w.inv.last = w.head⁻¹
  证明: by
  induction w <;> simp [inv, *]
-/
theorem inv_last {i j} (w : NeWord G i j) : w.inv.last = w.head⁻¹ := by
  induction w <;> simp [inv, *]

end Group

end NeWord

section PingPongLemma

open Cardinal
open scoped Function -- required for scoped `on` notation
open scoped Pointwise

variable {G : Type*} [Group G]
variable {H : ι -> Type*} [forall i, Group (H i)]
variable (f : forall i, H i ->* G)

-- We need many groups or one group with many elements
variable (hcard : 3 <= #ι ∨ exists i, 3 <= #(H i))

-- A group action on α, and the ping-pong sets
variable {α : Type*} [MulAction G α]
variable (X : ι -> Set α)
variable (hXnonempty : forall i, (X i).Nonempty)
variable (hXdisj : Pairwise (Disjoint on X))
variable (hpp : Pairwise fun i j => forall h : H i, h != 1 -> f i h • X j subseteq X i)
include hpp

/--
theorem `lift_word_ping_pong` / 定理 `lift_word_ping_pong`

English:
theorem lift_word_ping_pong
  given: {i j k} (w : NeWord H i j) (hk : j != k)
  proof: by
  induction w generalizing k with
  | singleton x hne_one => simpa using hpp hk _ hne_one
  | @append i j k l w₁ hne w₂ hIw₁ hIw₂ =>
    calc
      lift f (NeWord.append w₁ hne w₂).prod • X k = lift f w₁.prod • lift f w₂.prod • X k := by
        simp [mul_smul]
      _ subseteq lift f w₁.prod • X

中文:
定理 lift_word_ping_pong
  条件: {i j k} (w : NeWord H i j) (hk : j != k)
  证明: by
  induction w generalizing k with
  | singleton x hne_one => simpa using hpp hk _ hne_one
  | @append i j k l w₁ hne w₂ hIw₁ hIw₂ =>
    calc
      lift f (NeWord.append w₁ hne w₂).prod • X k = lift f w₁.prod • lift f w₂.prod • X k := by
        simp [mul_smul]
      _ subseteq lift f w₁.prod • X

Depends on / 依赖: NeWord, NeWord.append, append, generalizing, hne_one, mul_smul, singleton, smul_set_subset_smul_set_iff, smul_set_subset_smul_set_iff.mpr, subseteq
-/
theorem lift_word_ping_pong {i j k} (w : NeWord H i j) (hk : j != k) :
    lift f w.prod • X k subseteq X i := by
  induction w generalizing k with
  | singleton x hne_one => simpa using hpp hk _ hne_one
  | @append i j k l w₁ hne w₂ hIw₁ hIw₂ =>
    calc
      lift f (NeWord.append w₁ hne w₂).prod • X k = lift f w₁.prod • lift f w₂.prod • X k := by
        simp [mul_smul]
      _ subseteq lift f w₁.prod • X _ := smul_set_subset_smul_set_iff.mpr (hIw₂ hk)
      _ subseteq X i := hIw₁ hne

include hXnonempty hXdisj

/--
theorem `lift_word_prod_nontrivial_of_other_i` / 定理 `lift_word_prod_nontrivial_of_other_i`

English:
theorem lift_word_prod_nontrivial_of_other_i
  statement: {i j k} (w : NeWord H i j) (hhead : k != i)
  proof: by
  intro heq1
  have : X k subseteq X i := by simpa [heq1] using lift_word_ping_pong f X hpp w hlast.symm
  obtain ⟨x, hx⟩ := hXnonempty k
  exact (hXdisj hhead).le_bot ⟨hx, this hx⟩

中文:
定理 lift_word_prod_nontrivial_of_other_i
  结论: {i j k} (w : NeWord H i j) (hhead : k != i)
  证明: by
  intro heq1
  have : X k subseteq X i := by simpa [heq1] using lift_word_ping_pong f X hpp w hlast.symm
  obtain ⟨x, hx⟩ := hXnonempty k
  exact (hXdisj hhead).le_bot ⟨hx, this hx⟩

Depends on / 依赖: hXdisj, hXnonempty, hlast.symm, le_bot, lift_word_ping_pong, subseteq
-/
theorem lift_word_prod_nontrivial_of_other_i {i j k} (w : NeWord H i j) (hhead : k != i)
    (hlast : k != j) : lift f w.prod != 1 := by
  intro heq1
  have : X k subseteq X i := by simpa [heq1] using lift_word_ping_pong f X hpp w hlast.symm
  obtain ⟨x, hx⟩ := hXnonempty k
  exact (hXdisj hhead).le_bot ⟨hx, this hx⟩

variable [Nontrivial ι]

/--
theorem `lift_word_prod_nontrivial_of_head_eq_last` / 定理 `lift_word_prod_nontrivial_of_head_eq_last`

English:
theorem lift_word_prod_nontrivial_of_head_eq_last
  given: {i} (w : NeWord H i i)
  proof: by
  obtain ⟨k, hk⟩ := exists_ne i
  exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w hk hk

中文:
定理 lift_word_prod_nontrivial_of_head_eq_last
  条件: {i} (w : NeWord H i i)
  证明: by
  obtain ⟨k, hk⟩ := exists_ne i
  exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w hk hk

Depends on / 依赖: exists_ne, hXdisj, hXnonempty, lift_word_prod_nontrivial_of_other_i
-/
theorem lift_word_prod_nontrivial_of_head_eq_last {i} (w : NeWord H i i) :
    lift f w.prod != 1 := by
  obtain ⟨k, hk⟩ := exists_ne i
  exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w hk hk

/--
theorem `lift_word_prod_nontrivial_of_head_card` / 定理 `lift_word_prod_nontrivial_of_head_card`

English:
theorem lift_word_prod_nontrivial_of_head_card
  statement: {i j} (w : NeWord H i j)
  proof: by
  obtain ⟨h, hn1, hnh⟩ := Cardinal.exists_ne_ne_of_three_le hcard 1 w.head⁻¹
  have hnot1 : h * w.head != 1 := by
    rw [← div_inv_eq_mul]
    exact div_ne_one_of_ne hnh
  let w' : NeWord H i i :=
    NeWord.append (NeWord.mulHead w h hnot1) hheadtail.symm
      (NeWord.singleton h⁻¹ (inv_ne_one

中文:
定理 lift_word_prod_nontrivial_of_head_card
  结论: {i j} (w : NeWord H i j)
  证明: by
  obtain ⟨h, hn1, hnh⟩ := Cardinal.exists_ne_ne_of_three_le hcard 1 w.head⁻¹
  have hnot1 : h * w.head != 1 := by
    rw [← div_inv_eq_mul]
    exact div_ne_one_of_ne hnh
  let w' : NeWord H i i :=
    NeWord.append (NeWord.mulHead w h hnot1) hheadtail.symm
      (NeWord.singleton h⁻¹ (inv_ne_one

Depends on / 依赖: Cardinal, Cardinal.exists_ne_ne_of_three_le, NeWord, NeWord.append, NeWord.mulHead, NeWord.singleton, append, div_inv_eq_mul, div_ne_one_of_ne, exists_ne_ne_of_three_le, hXdisj, hXnonempty, hheadtail, hheadtail.symm, inv_ne_one, inv_ne_one.mpr, lift_word_prod_nontrivial_of_head_eq_last, mulHead, singleton, w.head
-/
theorem lift_word_prod_nontrivial_of_head_card {i j} (w : NeWord H i j)
    (hcard : 3 <= #(H i)) (hheadtail : i != j) : lift f w.prod != 1 := by
  obtain ⟨h, hn1, hnh⟩ := Cardinal.exists_ne_ne_of_three_le hcard 1 w.head⁻¹
  have hnot1 : h * w.head != 1 := by
    rw [← div_inv_eq_mul]
    exact div_ne_one_of_ne hnh
  let w' : NeWord H i i :=
    NeWord.append (NeWord.mulHead w h hnot1) hheadtail.symm
      (NeWord.singleton h⁻¹ (inv_ne_one.mpr hn1))
  have hw' : lift f w'.prod != 1 :=
    lift_word_prod_nontrivial_of_head_eq_last f X hXnonempty hXdisj hpp w'
  intro heq1
  apply hw'
  simp [w', heq1]

include hcard in
/--
theorem `lift_word_prod_nontrivial_of_not_empty` / 定理 `lift_word_prod_nontrivial_of_not_empty`

English:
theorem lift_word_prod_nontrivial_of_not_empty
  given: {i j} (w : NeWord H i j)
  proof: by
  rcases hcard with hcard | hcard
  · obtain ⟨i, h1, h2⟩ := Cardinal.exists_ne_ne_of_three_le hcard i j
    exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w h1 h2
  · obtain ⟨k, hcard⟩ := hcard
    by_cases hh : i = k <;> by_cases hl : j = k
    · subst hh
      subst hl
   

中文:
定理 lift_word_prod_nontrivial_of_not_empty
  条件: {i j} (w : NeWord H i j)
  证明: by
  rcases hcard with hcard | hcard
  · obtain ⟨i, h1, h2⟩ := Cardinal.exists_ne_ne_of_three_le hcard i j
    exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w h1 h2
  · obtain ⟨k, hcard⟩ := hcard
    by_cases hh : i = k <;> by_cases hl : j = k
    · subst hh
      subst hl
   

Depends on / 依赖: Cardinal, Cardinal.exists_ne_ne_of_three_le, exists_ne_ne_of_three_le, hXdisj, hXnonempty, hl.symm, lift_word_prod_nontrivial_of_head_card, lift_word_prod_nontrivial_of_head_eq_last, lift_word_prod_nontrivial_of_other_i
-/
theorem lift_word_prod_nontrivial_of_not_empty {i j} (w : NeWord H i j) :
    lift f w.prod != 1 := by
  rcases hcard with hcard | hcard
  · obtain ⟨i, h1, h2⟩ := Cardinal.exists_ne_ne_of_three_le hcard i j
    exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w h1 h2
  · obtain ⟨k, hcard⟩ := hcard
    by_cases hh : i = k <;> by_cases hl : j = k
    · subst hh
      subst hl
      exact lift_word_prod_nontrivial_of_head_eq_last f X hXnonempty hXdisj hpp w
    · subst hh
      change j != i at hl
      exact lift_word_prod_nontrivial_of_head_card f X hXnonempty hXdisj hpp w hcard hl.symm
    · subst hl
      change i != j at hh
      have : lift f w.inv.prod != 1 :=
        lift_word_prod_nontrivial_of_head_card f X hXnonempty hXdisj hpp w.inv hcard hh.symm
      intro heq
      apply this
      simpa using heq
    · change i != k at hh
      change j != k at hl
      exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w hh.symm hl.symm

include hcard in
/--
theorem `empty_of_word_prod_eq_one` / 定理 `empty_of_word_prod_eq_one`

English:
theorem empty_of_word_prod_eq_one
  given: {w : Word H} (h : lift f w.prod = 1)
  proof: by
  by_contra hnotempty
  obtain ⟨i, j, w, rfl⟩ := NeWord.of_word w hnotempty
  exact lift_word_prod_nontrivial_of_not_empty f hcard X hXnonempty hXdisj hpp w h

中文:
定理 empty_of_word_prod_eq_one
  条件: {w : Word H} (h : lift f w.乘积 = 1)
  证明: by
  by_contra hnotempty
  obtain ⟨i, j, w, rfl⟩ := NeWord.of_word w hnotempty
  exact lift_word_prod_nontrivial_of_not_empty f hcard X hXnonempty hXdisj hpp w h

Depends on / 依赖: NeWord, NeWord.of_word, hXdisj, hXnonempty, hnotempty, lift_word_prod_nontrivial_of_not_empty, of_word
-/
theorem empty_of_word_prod_eq_one {w : Word H} (h : lift f w.prod = 1) :
    w = Word.empty := by
  by_contra hnotempty
  obtain ⟨i, j, w, rfl⟩ := NeWord.of_word w hnotempty
  exact lift_word_prod_nontrivial_of_not_empty f hcard X hXnonempty hXdisj hpp w h

set_option backward.isDefEq.respectTransparency false in
include hcard in
/--
theorem `lift_injective_of_ping_pong` / 定理 `lift_injective_of_ping_pong`

English:
theorem lift_injective_of_ping_pong
  statement: Function.Injective (lift f)
  proof: by
  classical
    apply (injective_iff_map_eq_one (lift f)).mpr
    rw [(CoprodI.Word.equiv).forall_congr_left]
    intro w Heq
    dsimp [Word.equiv] at *
    rw [empty_of_word_prod_eq_one f hcard X hXnonempty hXdisj hpp Heq]; rw [Word.prod_empty]

中文:
定理 lift_injective_of_ping_pong
  结论: 函数.单射 (lift f)
  证明: by
  classical
    apply (injective_iff_map_eq_one (lift f)).mpr
    rw [(CoprodI.Word.equiv).forall_congr_left]
    intro w Heq
    dsimp [Word.equiv] at *
    rw [empty_of_word_prod_eq_one f hcard X hXnonempty hXdisj hpp Heq]; rw [Word.prod_empty]

Depends on / 依赖: CoprodI, CoprodI.Word.equiv, Word.equiv, Word.prod_empty, classical, empty_of_word_prod_eq_one, forall_congr_left, hXdisj, hXnonempty, injective_iff_map_eq_one, prod_empty
-/
theorem lift_injective_of_ping_pong : Function.Injective (lift f) := by
  classical
    apply (injective_iff_map_eq_one (lift f)).mpr
    rw [(CoprodI.Word.equiv).forall_congr_left]
    intro w Heq
    dsimp [Word.equiv] at *
    rw [empty_of_word_prod_eq_one f hcard X hXnonempty hXdisj hpp Heq]; rw [Word.prod_empty]

end PingPongLemma

/--
Definition of `FreeGroupBasis.coprodI` / `FreeGroupBasis.coprodI` 的定义

English:
definition FreeGroupBasis.coprodI
  signature: {ι : Type*} {X : ι -> Type*} {G : ι -> Type*} [forall i, Group (G i)]
  body: ⟨MulEquiv.symm MonoidHom.toMulEquiv
    (FreeGroup.lift fun x : Σ i, X i => CoprodI.of (B x.1 x.2))
    (CoprodI.lift fun i : ι => (B i).lift fun x : X i =>
              FreeGroup.of (⟨i, x⟩ : Σ i, X i))
    (by ext; simp)
    (by ext1 i; apply (B i).ext_hom; simp)⟩

中文:
定义 FreeGroupBasis.coprodI
  签名: {ι : 类型} {X : ι -> 类型} {G : ι -> 类型} [对任意 i, 群 (G i)]
  定义体: ⟨MulEquiv.symm MonoidHom.toMulEquiv
    (FreeGroup.lift fun x : Σ i, X i => CoprodI.of (B x.1 x.2))
    (CoprodI.lift fun i : ι => (B i).lift fun x : X i =>
              FreeGroup.of (⟨i, x⟩ : Σ i, X i))
    (by ext; simp)
    (by ext1 i; apply (B i).ext_hom; simp)⟩

Depends on / 依赖: CoprodI, CoprodI.lift, CoprodI.of, FreeGroup, FreeGroup.lift, FreeGroup.of, MonoidHom, MonoidHom.toMulEquiv, MulEquiv, MulEquiv.symm, ext_hom, toMulEquiv
-/
def FreeGroupBasis.coprodI {ι : Type*} {X : ι -> Type*} {G : ι -> Type*} [forall i, Group (G i)]
    (B : forall i, FreeGroupBasis (X i) (G i)) :
    FreeGroupBasis (Σ i, X i) (CoprodI G) :=
⟨MulEquiv.symm MonoidHom.toMulEquiv
    (FreeGroup.lift fun x : Σ i, X i => CoprodI.of (B x.1 x.2))
    (CoprodI.lift fun i : ι => (B i).lift fun x : X i =>
              FreeGroup.of (⟨i, x⟩ : Σ i, X i))
    (by ext; simp)
    (by ext1 i; apply (B i).ext_hom; simp)⟩

/-- The free product of free groups is itself a free group. -/
instance {ι : Type*} (G : ι -> Type*) [forall i, Group (G i)] [forall i, IsFreeGroup (G i)] :
    IsFreeGroup (CoprodI G) :=
  (FreeGroupBasis.coprodI (fun i => IsFreeGroup.basis (G i))).isFreeGroup

-- NB: One might expect this theorem to be phrased with ℤ, but ℤ is an additive group,
-- and using `Multiplicative ℤ` runs into diamond issues.
/-- A free group is a free product of copies of the `FreeGroup` over one generator. -/
@[simps!]
/--
Definition of `_root_.freeGroupEquivCoprodI` / `_root_.freeGroupEquivCoprodI` 的定义

English:
definition _root_.freeGroupEquivCoprodI
  signature: {ι : Type u_1}
  body: by
  refine MonoidHom.toMulEquiv ?_ ?_ ?_ ?_
  · exact FreeGroup.lift fun i => @CoprodI.of ι _ _ i (FreeGroup.of Unit.unit)
  · exact CoprodI.lift fun i => FreeGroup.lift fun _ => FreeGroup.of i
  · ext; simp
  · ext i a; cases a; simp

中文:
定义 _root_.freeGroupEquivCoprodI
  签名: {ι : 类型u_1}
  定义体: by
  refine MonoidHom.toMulEquiv ?_ ?_ ?_ ?_
  · exact FreeGroup.lift fun i => @CoprodI.of ι _ _ i (FreeGroup.of Unit.unit)
  · exact CoprodI.lift fun i => FreeGroup.lift fun _ => FreeGroup.of i
  · ext; simp
  · ext i a; cases a; simp

Depends on / 依赖: CoprodI, CoprodI.lift, CoprodI.of, FreeGroup, FreeGroup.lift, FreeGroup.of, MonoidHom, MonoidHom.toMulEquiv, Unit.unit, toMulEquiv
-/
def _root_.freeGroupEquivCoprodI {ι : Type u_1} :
    FreeGroup ι ≃* CoprodI fun _ : ι => FreeGroup Unit := by
  refine MonoidHom.toMulEquiv ?_ ?_ ?_ ?_
  · exact FreeGroup.lift fun i => @CoprodI.of ι _ _ i (FreeGroup.of Unit.unit)
  · exact CoprodI.lift fun i => FreeGroup.lift fun _ => FreeGroup.of i
  · ext; simp
  · ext i a; cases a; simp

section PingPongLemma

open Cardinal
open scoped Function -- required for scoped `on` notation
open scoped Pointwise

variable [Nontrivial ι]
variable {G : Type u_1} [Group G] (a : ι -> G)

-- A group action on α, and the ping-pong sets
variable {α : Type*} [MulAction G α]
variable (X Y : ι -> Set α)
variable (hXnonempty : forall i, (X i).Nonempty)
variable (hXdisj : Pairwise (Disjoint on X))
variable (hYdisj : Pairwise (Disjoint on Y))
variable (hXYdisj : forall i j, Disjoint (X i) (Y j))
variable (hX : forall i, a i • (Y i)ᶜ subseteq X i)
variable (hY : forall i, a⁻¹ i • (X i)ᶜ subseteq Y i)

set_option backward.isDefEq.respectTransparency false in
include hXnonempty hXdisj hYdisj hXYdisj hX hY in
/--
theorem `_root_.FreeGroup.injective_lift_of_ping_pong` / 定理 `_root_.FreeGroup.injective_lift_of_ping_pong`

English:
theorem _root_.FreeGroup.injective_lift_of_ping_pong
  statement: Function.Injective (FreeGroup.lift a)
  proof: by
  -- Step one: express the free group lift via the free product lift
  have : FreeGroup.lift a =
      (CoprodI.lift fun i => FreeGroup.lift fun _ => a i).comp
        (@freeGroupEquivCoprodI ι).toMonoidHom := by
    ext i
    simp
  rw [this]; rw [MonoidHom.coe_comp]
  clear this
  refine Functi

中文:
定理 _root_.自由群.injective_lift_of_ping_pong
  结论: 函数.单射 (自由群.lift a)
  证明: by
  -- Step one: express the free group lift via the free product lift
  have : FreeGroup.lift a =
      (CoprodI.lift fun i => FreeGroup.lift fun _ => a i).comp
        (@freeGroupEquivCoprodI ι).toMonoidHom := by
    ext i
    simp
  rw [this]; rw [MonoidHom.coe_comp]
  clear this
  refine Functi
-/
theorem _root_.FreeGroup.injective_lift_of_ping_pong : Function.Injective (FreeGroup.lift a) := by
  -- Step one: express the free group lift via the free product lift
  have : FreeGroup.lift a =
      (CoprodI.lift fun i => FreeGroup.lift fun _ => a i).comp
        (@freeGroupEquivCoprodI ι).toMonoidHom := by
    ext i
    simp
  rw [this]; rw [MonoidHom.coe_comp]
  clear this
  refine Function.Injective.comp ?_ (MulEquiv.injective freeGroupEquivCoprodI)
  -- Step two: Invoke the ping-pong lemma for free products
  change Function.Injective (lift fun i : ι => FreeGroup.lift fun _ => a i)
  -- Prepare to instantiate lift_injective_of_ping_pong
  let H : ι -> Type _ := fun _i => FreeGroup Unit
  let f : forall i, H i ->* G := fun i => FreeGroup.lift fun _ => a i
  let X' : ι -> Set α := fun i => X i union Y i
  apply lift_injective_of_ping_pong f _ X'
  · show forall i, (X' i).Nonempty
    exact fun i => Set.Nonempty.inl (hXnonempty i)
  · show Pairwise (Disjoint on X')
    intro i j hij
    simp only [X']
    apply Disjoint.union_left <;> apply Disjoint.union_right
    · exact hXdisj hij
    · exact hXYdisj i j
    · exact (hXYdisj j i).symm
    · exact hYdisj hij
  · change Pairwise fun i j => forall h : H i, h != 1 -> f i h • X' j subseteq X' i
    rintro i j hij
    -- use free_group unit ≃ ℤ
    refine FreeGroup.freeGroupUnitEquivInt.forall_congr_left.mpr ?_
    intro n hne1
    change FreeGroup.lift (fun _ => a i) (FreeGroup.of () ^ n) • X' j subseteq X' i
    simp only [map_zpow, FreeGroup.lift_apply_of]
    change a i ^ n • X' j subseteq X' i
    have hnne0 : n != 0 := by
      rintro rfl
      apply hne1
      simp [H, FreeGroup.freeGroupUnitEquivInt]
    clear hne1
    simp only [X']
    -- Positive and negative powers separately
    rcases (lt_or_gt_of_ne hnne0).symm with hlt | hgt
    · have h1n : 1 <= n := hlt
      calc
        a i ^ n • X' j subseteq a i ^ n • (Y i)ᶜ :=
          smul_set_mono ((hXYdisj j i).union_left <| hYdisj hij.symm).subset_compl_right
        _ subseteq X i := by
          clear hnne0 hlt
          induction n, h1n using Int.leInduction with
          | base => rw [zpow_one]; exact hX i
          | succ n _hle hi =>
            calc
              a i ^ (n + 1) • (Y i)ᶜ = (a i ^ n * a i) • (Y i)ᶜ := by rw [zpow_add, zpow_one]
              _ = a i ^ n • a i • (Y i)ᶜ := mul_smul _ _ _
_ subseteq a i ^ n • X i := smul_set_mono hX i
              _ subseteq a i ^ n • (Y i)ᶜ := smul_set_mono (hXYdisj i i).subset_compl_right
              _ subseteq X i := hi
        _ subseteq X' i := Set.subset_union_left
    · have h1n : n <= -1 := by
        apply Int.le_of_lt_add_one
        simpa using hgt
      calc
        a i ^ n • X' j subseteq a i ^ n • (X i)ᶜ :=
          smul_set_mono ((hXdisj hij.symm).union_left (hXYdisj i j).symm).subset_compl_right
        _ subseteq Y i := by
          clear hnne0 hgt
          induction n, h1n using Int.leInductionDown with
          | base => rw [zpow_neg, zpow_one]; exact hY i
          | pred n hle hi =>
            calc
              a i ^ (n - 1) • (X i)ᶜ = (a i ^ n * (a i)⁻¹) • (X i)ᶜ := by rw [zpow_sub, zpow_one]
              _ = a i ^ n • (a i)⁻¹ • (X i)ᶜ := mul_smul _ _ _
_ subseteq a i ^ n • Y i := smul_set_mono hY i
              _ subseteq a i ^ n • (X i)ᶜ := smul_set_mono (hXYdisj i i).symm.subset_compl_right
              _ subseteq Y i := hi
        _ subseteq X' i := Set.subset_union_right
  show _ ∨ exists i, 3 <= #(H i)
  inhabit ι
  right
  use Inhabited.default
  simp only [H]
  rw [FreeGroup.freeGroupUnitEquivInt.cardinal_eq]; rw [Cardinal.mk_denumerable]
  exact natCast_le_aleph0

end PingPongLemma

end Monoid.CoprodI
