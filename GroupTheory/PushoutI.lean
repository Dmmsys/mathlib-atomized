/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.Complement

/-!

## Pushouts of Monoids and Groups

This file defines wide pushouts of monoids and groups and proves some properties
of the amalgamated product of groups (i.e. the special case where all the maps
in the diagram are injective).

## Main definitions

- `Monoid.PushoutI`: the pushout of a diagram of monoids indexed by a type `ι`
- `Monoid.PushoutI.base`: the map from the amalgamating monoid to the pushout
- `Monoid.PushoutI.of`: the map from each Monoid in the family to the pushout
- `Monoid.PushoutI.lift`: the universal property used to define homomorphisms out of the pushout.

- `Monoid.PushoutI.NormalWord`: a normal form for words in the pushout
- `Monoid.PushoutI.of_injective`: if all the maps in the diagram are injective in a pushout of
  groups then so is `of`
- `Monoid.PushoutI.Reduced.eq_empty_of_mem_range`: For any word `w` in the coproduct,
  if `w` is reduced (i.e none its letters are in the image of the base monoid), and nonempty, then
  `w` itself is not in the image of the base monoid.

## References

* The normal form theorem follows these [notes](https://webspace.maths.qmul.ac.uk/i.m.chiswell/ggt/lecture_notes/lecture2.pdf)
  from Queen Mary University

## Tags

amalgamated product, pushout, group

-/

@[expose] public section

namespace Monoid

open CoprodI Subgroup Coprod Function List

variable {ι : Type*} {G : ι -> Type*} {H : Type*} {K : Type*} [Monoid K]

/--
Definition of `PushoutI.con` / `PushoutI.con` 的定义

English:
definition PushoutI.con
  signature: [forall i, Monoid (G i)] [Monoid H] (φ : forall i, H ->* G i)
  body: conGen (fun x y : Coprod (CoprodI G) H =>
    exists i x', x = inl (of (φ i x')) ∧ y = inr x')

中文:
定义 PushoutI.con
  签名: [对任意 i, 幺半群 (G i)] [幺半群 H] (φ : 对任意 i, H ->* G i)
  定义体: conGen (fun x y : Coprod (CoprodI G) H =>
    exists i x', x = inl (of (φ i x')) ∧ y = inr x')

Depends on / 依赖: Coprod, CoprodI, conGen
-/
def PushoutI.con [forall i, Monoid (G i)] [Monoid H] (φ : forall i, H ->* G i) :
    Con (Coprod (CoprodI G) H) :=
  conGen (fun x y : Coprod (CoprodI G) H =>
    exists i x', x = inl (of (φ i x')) ∧ y = inr x')

/--
Definition of `PushoutI` / `PushoutI` 的定义

English:
definition PushoutI
  signature: [forall i, Monoid (G i)] [Monoid H] (φ : forall i, H ->* G i)
  body: (PushoutI.con φ).Quotient

中文:
定义 PushoutI
  签名: [对任意 i, 幺半群 (G i)] [幺半群 H] (φ : 对任意 i, H ->* G i)
  定义体: (PushoutI.con φ).Quotient

Depends on / 依赖: PushoutI, PushoutI.con, Quotient
-/
def PushoutI [forall i, Monoid (G i)] [Monoid H] (φ : forall i, H ->* G i) : Type _ :=
  (PushoutI.con φ).Quotient

namespace PushoutI

section Monoid

variable [forall i, Monoid (G i)] [Monoid H] {φ : forall i, H ->* G i}

/--
Instance `mul` / 实例 `mul`

English:
instance mul
  signature: : Mul (PushoutI φ)
  body: by
  delta PushoutI; infer_instance

中文:
实例 mul
  签名: : 乘法 (PushoutI φ)
  定义体: by
  delta PushoutI; infer_instance
-/
protected instance mul : Mul (PushoutI φ) := by
  delta PushoutI; infer_instance

/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One (PushoutI φ)
  body: by
  delta PushoutI; infer_instance

中文:
实例 one
  签名: : 幺 (PushoutI φ)
  定义体: by
  delta PushoutI; infer_instance
-/
protected instance one : One (PushoutI φ) := by
  delta PushoutI; infer_instance

/--
Instance `monoid` / 实例 `monoid`

English:
instance monoid
  signature: : Monoid (PushoutI φ)
  body: { Con.monoid _ with
    toMul := PushoutI.mul
    toOne := PushoutI.one }

中文:
实例 monoid
  签名: : 幺半群 (PushoutI φ)
  定义体: { Con.monoid _ with
    toMul := PushoutI.mul
    toOne := PushoutI.one }

Depends on / 依赖: Con.monoid, PushoutI, PushoutI.mul, PushoutI.one, monoid
-/
instance monoid : Monoid (PushoutI φ) :=
  { Con.monoid _ with
    toMul := PushoutI.mul
    toOne := PushoutI.one }

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (i : ι)
  body: (Con.mk' _).comp inl.comp CoprodI.of

中文:
定义 of
  签名: (i : ι)
  定义体: (Con.mk' _).comp inl.comp CoprodI.of

Depends on / 依赖: Con.mk, CoprodI, CoprodI.of, inl.comp
-/
def of (i : ι) : G i ->* PushoutI φ :=
(Con.mk' _).comp inl.comp CoprodI.of

variable (φ) in
/--
Definition of `base` / `base` 的定义

English:
definition base
  signature: : H ->* PushoutI φ
  body: (Con.mk' _).comp inr

中文:
定义 base
  签名: : H ->* PushoutI φ
  定义体: (Con.mk' _).comp inr

Depends on / 依赖: Con.mk
-/
def base : H ->* PushoutI φ :=
  (Con.mk' _).comp inr

/--
theorem `of_comp_eq_base` / 定理 `of_comp_eq_base`

English:
theorem of_comp_eq_base
  given: (i : ι)
  statement: (of i).comp (φ i) = (base φ)
  proof: by
  ext x
  apply (Con.eq _).2
  refine ConGen.Rel.of _ _ ?_
  simp only [MonoidHom.comp_apply]
  exact ⟨_, _, rfl, rfl⟩

中文:
定理 of_comp_eq_base
  条件: (i : ι)
  结论: (of i).comp (φ i) = (base φ)
  证明: by
  ext x
  apply (Con.eq _).2
  refine ConGen.Rel.of _ _ ?_
  simp only [MonoidHom.comp_apply]
  exact ⟨_, _, rfl, rfl⟩

Depends on / 依赖: Con.eq, ConGen, ConGen.Rel.of, MonoidHom, MonoidHom.comp_apply, comp_apply
-/
theorem of_comp_eq_base (i : ι) : (of i).comp (φ i) = (base φ) := by
  ext x
  apply (Con.eq _).2
  refine ConGen.Rel.of _ _ ?_
  simp only [MonoidHom.comp_apply]
  exact ⟨_, _, rfl, rfl⟩

variable (φ) in
/--
theorem `of_apply_eq_base` / 定理 `of_apply_eq_base`

English:
theorem of_apply_eq_base
  given: (i : ι) (x : H)
  statement: of i (φ i x) = base φ x
  proof: by
  rw [← MonoidHom.comp_apply]; rw [of_comp_eq_base]

中文:
定理 of_apply_eq_base
  条件: (i : ι) (x : H)
  结论: of i (φ i x) = base φ x
  证明: by
  rw [← MonoidHom.comp_apply]; rw [of_comp_eq_base]

Depends on / 依赖: MonoidHom, MonoidHom.comp_apply, comp_apply, of_comp_eq_base
-/
theorem of_apply_eq_base (i : ι) (x : H) : of i (φ i x) = base φ x := by
  rw [← MonoidHom.comp_apply]; rw [of_comp_eq_base]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : forall i, G i ->* K) (k : H ->* K)
  body: Con.lift _ (Coprod.lift (CoprodI.lift f) k) by
    apply Con.conGen_le.2 fun x y => ?_
    rintro ⟨i, x', rfl, rfl⟩
    simp only [DFunLike.ext_iff, MonoidHom.coe_comp, comp_apply] at hf
    simp [hf]

中文:
定义 lift
  签名: (f : 对任意 i, G i ->* K) (k : H ->* K)
  定义体: Con.lift _ (Coprod.lift (CoprodI.lift f) k) by
    apply Con.conGen_le.2 fun x y => ?_
    rintro ⟨i, x', rfl, rfl⟩
    simp only [DFunLike.ext_iff, MonoidHom.coe_comp, comp_apply] at hf
    simp [hf]

Depends on / 依赖: Con.conGen_le, Con.lift, Coprod, Coprod.lift, CoprodI, CoprodI.lift, DFunLike, DFunLike.ext_iff, MonoidHom, MonoidHom.coe_comp, coe_comp, comp_apply, conGen_le, ext_iff
-/
def lift (f : forall i, G i ->* K) (k : H ->* K)
    (hf : forall i, (f i).comp (φ i) = k) :
    PushoutI φ ->* K :=
Con.lift _ (Coprod.lift (CoprodI.lift f) k) by
    apply Con.conGen_le.2 fun x y => ?_
    rintro ⟨i, x', rfl, rfl⟩
    simp only [DFunLike.ext_iff, MonoidHom.coe_comp, comp_apply] at hf
    simp [hf]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  statement: (f : forall i, G i ->* K) (k : H ->* K)
  proof: by
  delta PushoutI lift of
  simp only [MonoidHom.coe_comp, Con.coe_mk', comp_apply, Con.lift_coe,
    lift_apply_inl, CoprodI.lift_of]

中文:
定理 lift_of
  结论: (f : 对任意 i, G i ->* K) (k : H ->* K)
  证明: by
  delta PushoutI lift of
  simp only [MonoidHom.coe_comp, Con.coe_mk', comp_apply, Con.lift_coe,
    lift_apply_inl, CoprodI.lift_of]

Depends on / 依赖: Con.coe_mk, Con.lift_coe, CoprodI, CoprodI.lift_of, MonoidHom, MonoidHom.coe_comp, PushoutI, coe_comp, coe_mk, comp_apply, lift_apply_inl, lift_coe, lift_of
-/
theorem lift_of (f : forall i, G i ->* K) (k : H ->* K)
    (hf : forall i, (f i).comp (φ i) = k)
    {i : ι} (g : G i) : (lift f k hf) (of i g : PushoutI φ) = f i g := by
  delta PushoutI lift of
  simp only [MonoidHom.coe_comp, Con.coe_mk', comp_apply, Con.lift_coe,
    lift_apply_inl, CoprodI.lift_of]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `lift_base` / 定理 `lift_base`

English:
theorem lift_base
  statement: (f : forall i, G i ->* K) (k : H ->* K)
  proof: by
  delta PushoutI lift base
  simp only [MonoidHom.coe_comp, Con.coe_mk', comp_apply, Con.lift_coe, lift_apply_inr]

中文:
定理 lift_base
  结论: (f : 对任意 i, G i ->* K) (k : H ->* K)
  证明: by
  delta PushoutI lift base
  simp only [MonoidHom.coe_comp, Con.coe_mk', comp_apply, Con.lift_coe, lift_apply_inr]

Depends on / 依赖: Con.coe_mk, Con.lift_coe, MonoidHom, MonoidHom.coe_comp, PushoutI, coe_comp, coe_mk, comp_apply, lift_apply_inr, lift_coe
-/
theorem lift_base (f : forall i, G i ->* K) (k : H ->* K)
    (hf : forall i, (f i).comp (φ i) = k)
    (g : H) : (lift f k hf) (base φ g : PushoutI φ) = k g := by
  delta PushoutI lift base
  simp only [MonoidHom.coe_comp, Con.coe_mk', comp_apply, Con.lift_coe, lift_apply_inr]

-- `ext` attribute should be lower priority than `hom_ext_nonempty`
@[ext 1199]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {f g : PushoutI φ ->* K}
  proof: (MonoidHom.cancel_right Con.mk'_surjective).mp
    Coprod.hom_ext
      (CoprodI.ext_hom _ _ h)
      hbase

@[ext high]

中文:
定理 hom_ext
  结论: {f g : PushoutI φ ->* K}
  证明: (MonoidHom.cancel_right Con.mk'_surjective).mp
    Coprod.hom_ext
      (CoprodI.ext_hom _ _ h)
      hbase

@[ext high]

Depends on / 依赖: Con.mk, Coprod, Coprod.hom_ext, CoprodI, CoprodI.ext_hom, MonoidHom, MonoidHom.cancel_right, _surjective, cancel_right, ext_hom, hom_ext
-/
theorem hom_ext {f g : PushoutI φ ->* K}
    (h : forall i, f.comp (of i : G i ->* _) = g.comp (of i : G i ->* _))
    (hbase : f.comp (base φ) = g.comp (base φ)) : f = g :=
(MonoidHom.cancel_right Con.mk'_surjective).mp
    Coprod.hom_ext
      (CoprodI.ext_hom _ _ h)
      hbase

@[ext high]
/--
theorem `hom_ext_nonempty` / 定理 `hom_ext_nonempty`

English:
theorem hom_ext_nonempty
  statement: [hn : Nonempty ι]
  proof: hom_ext h by
    cases hn with
    | intro i =>
      ext
      rw [← of_comp_eq_base i]; rw [← MonoidHom.comp_assoc]; rw [h]; rw [MonoidHom.comp_assoc]

中文:
定理 hom_ext_nonempty
  结论: [hn : 非空 ι]
  证明: hom_ext h by
    cases hn with
    | intro i =>
      ext
      rw [← of_comp_eq_base i]; rw [← MonoidHom.comp_assoc]; rw [h]; rw [MonoidHom.comp_assoc]

Depends on / 依赖: MonoidHom, MonoidHom.comp_assoc, comp_assoc, hom_ext, of_comp_eq_base
-/
theorem hom_ext_nonempty [hn : Nonempty ι]
    {f g : PushoutI φ ->* K}
    (h : forall i, f.comp (of i : G i ->* _) = g.comp (of i : G i ->* _)) : f = g :=
hom_ext h by
    cases hn with
    | intro i =>
      ext
      rw [← of_comp_eq_base i]; rw [← MonoidHom.comp_assoc]; rw [h]; rw [MonoidHom.comp_assoc]

/-- The equivalence that is part of the universal property of the pushout. A hom out of
the pushout is just a morphism out of all groups in the pushout that satisfies a commutativity
condition. -/
@[simps]
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: :
  body: { toFun := fun f => ⟨(fun i => f.comp (of i), f.comp (base φ)),
      fun i => by rw [MonoidHom.comp_assoc, of_comp_eq_base]⟩
    invFun := fun f => lift f.1.1 f.1.2 f.2,
    left_inv := fun _ => hom_ext (by simp [DFunLike.ext_iff])
      (by simp [DFunLike.ext_iff])
    right_inv := fun ⟨⟨_, _⟩, _⟩

中文:
定义 homEquiv
  签名: :
  定义体: { toFun := fun f => ⟨(fun i => f.comp (of i), f.comp (base φ)),
      fun i => by rw [MonoidHom.comp_assoc, of_comp_eq_base]⟩
    invFun := fun f => lift f.1.1 f.1.2 f.2,
    left_inv := fun _ => hom_ext (by simp [DFunLike.ext_iff])
      (by simp [DFunLike.ext_iff])
    right_inv := fun ⟨⟨_, _⟩, _⟩

Depends on / 依赖: DFunLike, DFunLike.ext_iff, MonoidHom, MonoidHom.comp_assoc, comp_assoc, ext_iff, f.comp, funext_iff, hom_ext, invFun, left_inv, of_comp_eq_base, right_inv
-/
def homEquiv :
    (PushoutI φ ->* K) ≃ { f : (Π i, G i ->* K) × (H ->* K) // forall i, (f.1 i).comp (φ i) = f.2 } :=
  { toFun := fun f => ⟨(fun i => f.comp (of i), f.comp (base φ)),
      fun i => by rw [MonoidHom.comp_assoc, of_comp_eq_base]⟩
    invFun := fun f => lift f.1.1 f.1.2 f.2,
    left_inv := fun _ => hom_ext (by simp [DFunLike.ext_iff])
      (by simp [DFunLike.ext_iff])
    right_inv := fun ⟨⟨_, _⟩, _⟩ => by simp [DFunLike.ext_iff, funext_iff] }

/--
Definition of `ofCoprodI` / `ofCoprodI` 的定义

English:
definition ofCoprodI
  signature: : CoprodI G ->* PushoutI φ
  body: CoprodI.lift of

@[simp]

中文:
定义 ofCoprodI
  签名: : 余prodI G ->* PushoutI φ
  定义体: CoprodI.lift of

@[simp]

Depends on / 依赖: CoprodI, CoprodI.lift
-/
def ofCoprodI : CoprodI G ->* PushoutI φ :=
  CoprodI.lift of

@[simp]
/--
theorem `ofCoprodI_of` / 定理 `ofCoprodI_of`

English:
theorem ofCoprodI_of
  given: (i : ι) (g : G i)
  proof: by
  simp [ofCoprodI]

中文:
定理 ofCoprodI_of
  条件: (i : ι) (g : G i)
  证明: by
  simp [ofCoprodI]

Depends on / 依赖: ofCoprodI
-/
theorem ofCoprodI_of (i : ι) (g : G i) :
    (ofCoprodI (CoprodI.of g) : PushoutI φ) = of i g := by
  simp [ofCoprodI]

/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {motive : PushoutI φ -> Prop}
  proof: by
  delta PushoutI PushoutI.of PushoutI.base at *
  induction x using Con.induction_on with
  | H x =>
    induction x using Coprod.induction_on with
    | inl g =>
      induction g using CoprodI.induction_on with
      | of i g => exact of i g
      | mul x y ihx ihy =>
        rw [map_mul]
     

中文:
定理 induction_on
  结论: {motive : PushoutI φ -> 命题}
  证明: by
  delta PushoutI PushoutI.of PushoutI.base at *
  induction x using Con.induction_on with
  | H x =>
    induction x using Coprod.induction_on with
    | inl g =>
      induction g using CoprodI.induction_on with
      | of i g => exact of i g
      | mul x y ihx ihy =>
        rw [map_mul]
     

Depends on / 依赖: Con.induction_on, Coprod, Coprod.induction_on, CoprodI, CoprodI.induction_on, PushoutI, PushoutI.base, PushoutI.of, induction_on, map_mul
-/
theorem induction_on {motive : PushoutI φ -> Prop}
    (x : PushoutI φ)
    (of : forall (i : ι) (g : G i), motive (of i g))
    (base : forall h, motive (base φ h))
    (mul : forall x y, motive x -> motive y -> motive (x * y)) : motive x := by
  delta PushoutI PushoutI.of PushoutI.base at *
  induction x using Con.induction_on with
  | H x =>
    induction x using Coprod.induction_on with
    | inl g =>
      induction g using CoprodI.induction_on with
      | of i g => exact of i g
      | mul x y ihx ihy =>
        rw [map_mul]
        exact mul _ _ ihx ihy
      | one => simpa using base 1
    | inr h => exact base h
    | mul x y ihx ihy => exact mul _ _ ihx ihy

end Monoid

variable [forall i, Group (G i)] [Group H] {φ : forall i, H ->* G i}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (PushoutI φ)
  body: { Con.group (PushoutI.con φ) with
    toMonoid := PushoutI.monoid }

中文:
实例 :
  签名: 群 (PushoutI φ)
  定义体: { Con.group (PushoutI.con φ) with
    toMonoid := PushoutI.monoid }

Depends on / 依赖: Con.group, PushoutI, PushoutI.con, PushoutI.monoid, monoid, toMonoid
-/
instance : Group (PushoutI φ) :=
  { Con.group (PushoutI.con φ) with
    toMonoid := PushoutI.monoid }

namespace NormalWord

/-
In this section we show that there is a normal form for words in the amalgamated product. To have a
normal form, we need to pick canonical choice of element of each right coset of the base group. The
choice of element in the base group itself is `1`. Given a choice of element of each right coset,
given by the type `Transversal φ` we can find a normal form. The normal form for an element is an
element of the base group, multiplied by a word in the coproduct, where each letter in the word is
the canonical choice of element of its coset. We then show that all groups in the diagram act
faithfully on the normal form. This implies that the maps into the coproduct are injective.

We demonstrate the action is faithful using the equivalence `equivPair`. We show that `G i` acts
faithfully on `Pair d i` and that `Pair d i` is isomorphic to `NormalWord d`. Here, `d` is a
`Transversal`. A `Pair d i` is a word in the coproduct, `Coprod G`, the `tail`, and an element
of the group `G i`, the `head`. The first letter of the `tail` must not be an element of `G i`.
Note that the `head` may be `1` Every letter in the `tail` must be in the transversal given by `d`.

We then show that the equivalence between `NormalWord` and `PushoutI`, between the set of normal
words and the elements of the amalgamated product. The key to this is the theorem `prod_smul_empty`,
which says that going from `NormalWord` to `PushoutI` and back is the identity. This is proven
by induction on the word using `consRecOn`.
-/

variable (φ)

/--
Definition of `Transversal` / `Transversal` 的定义

English:
structure Transversal
  parameters: : Type _ where
  axioms and operations (4):
    - injective : forall i, Injective (φ i)
    - set : forall i, Set (G i)
    - one_mem : forall i, 1 in set i
    - compl : forall i, IsComplement (φ i).range (set i)

中文:
结构 横截
  参数: : 类型 _ where
  公理与运算 (4 个):
    - injective : 对任意 i, 单射 (φ i)
    - set : 对任意 i, 集合 (G i)
    - one_mem : 对任意 i, 1 in set i
    - compl : 对任意 i, IsComplement (φ i).range (set i)

Depends on / 依赖: DecidableEq, Subsingleton, decidableEq_of_subsingleton
-/
structure Transversal : Type _ where
  /-- All maps in the diagram are injective -/
  injective : forall i, Injective (φ i)
  /-- The underlying set, containing exactly one element of each coset of the base group -/
  set : forall i, Set (G i)
  /-- The chosen element of the base group itself is the identity -/
  one_mem : forall i, 1 in set i
  /-- We have exactly one element of each coset of the base group -/
  compl : forall i, IsComplement (φ i).range (set i)

/--
theorem `transversal_nonempty` / 定理 `transversal_nonempty`

English:
theorem transversal_nonempty
  given: (hφ : forall i, Injective (φ i))
  statement: Nonempty (Transversal φ)
  proof: by
  choose t ht using fun i => (φ i).range.exists_isComplement_right 1
  apply Nonempty.intro
  exact
    { injective := hφ
      set := t
      one_mem := fun i => (ht i).2
      compl := fun i => (ht i).1 }

中文:
定理 transversal_nonempty
  条件: (hφ : 对任意 i, 单射 (φ i))
  结论: 非空 (横截 φ)
  证明: by
  choose t ht using fun i => (φ i).range.exists_isComplement_right 1
  apply Nonempty.intro
  exact
    { injective := hφ
      set := t
      one_mem := fun i => (ht i).2
      compl := fun i => (ht i).1 }

Depends on / 依赖: Nonempty, Nonempty.intro, Subsingleton, Subsingleton.elim, exists_isComplement_right, injective, one_mem, range.exists_isComplement_right
-/
theorem transversal_nonempty (hφ : forall i, Injective (φ i)) : Nonempty (Transversal φ) := by
  choose t ht using fun i => (φ i).range.exists_isComplement_right 1
  apply Nonempty.intro
  exact
    { injective := hφ
      set := t
      one_mem := fun i => (ht i).2
      compl := fun i => (ht i).1 }

variable {φ}

/--
Definition of `_root_.Monoid.PushoutI.NormalWord` / `_root_.Monoid.PushoutI.NormalWord` 的定义

English:
structure _root_.Monoid.PushoutI.NormalWord
  parameters: (d : Transversal φ)
  extends: CoprodI.Word G
  axioms and operations (2):
    - head : H
    - normalized : forall i g, ⟨i, g⟩ in toList -> g in d.set i

中文:
结构 _root_.幺半群.PushoutI.NormalWord
  参数: (d : 横截 φ)
  继承: 余prodI.Word G
  公理与运算 (2 个):
    - head : H
    - normalized : 对任意 i g, ⟨i, g⟩ in toList -> g in d.set i
-/
structure _root_.Monoid.PushoutI.NormalWord (d : Transversal φ) extends CoprodI.Word G where
  /-- Every `NormalWord` is the product of an element of the base group and a word made up
  of letters each of which is in the transversal. `head` is that element of the base group. -/
  head : H
  /-- All letters in the word are in the transversal. -/
  normalized : forall i g, ⟨i, g⟩ in toList -> g in d.set i

/--
Definition of `Pair` / `Pair` 的定义

English:
structure Pair
  parameters: (d : Transversal φ) (i : ι)
  extends: CoprodI.Word.Pair G i
  axioms and operations (1):
    - normalized : forall i g, ⟨i, g⟩ in tail.toList -> g in d.set i

中文:
结构 对
  参数: (d : 横截 φ) (i : ι)
  继承: 余prodI.Word.对 G i
  公理与运算 (1 个):
    - normalized : 对任意 i g, ⟨i, g⟩ in tail.toList -> g in d.set i
-/
structure Pair (d : Transversal φ) (i : ι) extends CoprodI.Word.Pair G i where
  /-- All letters in the word are in the transversal. -/
  normalized : forall i g, ⟨i, g⟩ in tail.toList -> g in d.set i

variable {d : Transversal φ}

/-- The empty normalized word, representing the identity element of the group. -/
@[simps!]
/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: : NormalWord d
  body: ⟨CoprodI.Word.empty, 1, fun i g => by simp [CoprodI.Word.empty]⟩

中文:
定义 empty
  签名: : NormalWord d
  定义体: ⟨CoprodI.Word.empty, 1, fun i g => by simp [CoprodI.Word.empty]⟩

Depends on / 依赖: CoprodI, CoprodI.Word.empty
-/
def empty : NormalWord d := ⟨CoprodI.Word.empty, 1, fun i g => by simp [CoprodI.Word.empty]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (NormalWord d)
  body: ⟨NormalWord.empty⟩

中文:
实例 :
  签名: 可居 (NormalWord d)
  定义体: ⟨NormalWord.empty⟩

Depends on / 依赖: NormalWord, NormalWord.empty
-/
instance : Inhabited (NormalWord d) := ⟨NormalWord.empty⟩

instance (i : ι) : Inhabited (Pair d i) :=
  ⟨{ (empty : NormalWord d) with
      head := 1, tail := _,
      fstIdx_ne := fun h => by cases h }⟩

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {w₁ w₂ : NormalWord d} (hhead : w₁.head = w₂.head)
  proof: by
  rcases w₁ with ⟨⟨_, _, _⟩, _, _⟩
  rcases w₂ with ⟨⟨_, _, _⟩, _, _⟩
  simp_all

中文:
定理 ext
  结论: {w₁ w₂ : NormalWord d} (hhead : w₁.head = w₂.head)
  证明: by
  rcases w₁ with ⟨⟨_, _, _⟩, _, _⟩
  rcases w₂ with ⟨⟨_, _, _⟩, _, _⟩
  simp_all
-/
theorem ext {w₁ w₂ : NormalWord d} (hhead : w₁.head = w₂.head)
    (hlist : w₁.toList = w₂.toList) : w₁ = w₂ := by
  rcases w₁ with ⟨⟨_, _, _⟩, _, _⟩
  rcases w₂ with ⟨⟨_, _, _⟩, _, _⟩
  simp_all

open Subgroup.IsComplement

/--
Instance `baseAction` / 实例 `baseAction`

English:
instance baseAction
  signature: : MulAction H (NormalWord d)
  body: { smul := fun h w => { w with head := h * w.head },
    one_smul := by simp +instances [instHSMul]
    mul_smul := by simp +instances [instHSMul, mul_assoc] }

中文:
实例 baseAction
  签名: : 乘法作用 H (NormalWord d)
  定义体: { smul := fun h w => { w with head := h * w.head },
    one_smul := by simp +instances [instHSMul]
    mul_smul := by simp +instances [instHSMul, mul_assoc] }

Depends on / 依赖: decidable_of_iff, fact_iff, fact_iff.symm, instHSMul, instances, mul_assoc, mul_smul, one_smul, w.head
-/
instance baseAction : MulAction H (NormalWord d) :=
  { smul := fun h w => { w with head := h * w.head },
    one_smul := by simp +instances [instHSMul]
    mul_smul := by simp +instances [instHSMul, mul_assoc] }

/--
theorem `base_smul_def'` / 定理 `base_smul_def'`

English:
theorem base_smul_def'
  given: (h : H) (w : NormalWord d)
  proof: rfl

中文:
定理 base_smul_def'
  条件: (h : H) (w : NormalWord d)
  证明: rfl

Depends on / 依赖: w.head
-/
theorem base_smul_def' (h : H) (w : NormalWord d) :
    h • w = { w with head := h * w.head } := rfl
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (w : NormalWord d)
  body: base φ w.head * ofCoprodI (w.toWord).prod

@[simp]

中文:
定义 乘积
  签名: (w : NormalWord d)
  定义体: base φ w.head * ofCoprodI (w.toWord).prod

@[simp]

Depends on / 依赖: ofCoprodI, toWord, w.head, w.toWord
-/
def prod (w : NormalWord d) : PushoutI φ :=
  base φ w.head * ofCoprodI (w.toWord).prod

@[simp]
/--
theorem `prod_base_smul` / 定理 `prod_base_smul`

English:
theorem prod_base_smul
  given: (h : H) (w : NormalWord d)
  proof: by
  simp only [base_smul_def', prod, map_mul, mul_assoc]

@[simp]

中文:
定理 prod_base_smul
  条件: (h : H) (w : NormalWord d)
  证明: by
  simp only [base_smul_def', prod, map_mul, mul_assoc]

@[simp]

Depends on / 依赖: base_smul_def, map_mul, mul_assoc
-/
theorem prod_base_smul (h : H) (w : NormalWord d) :
    (h • w).prod = base φ h * w.prod := by
  simp only [base_smul_def', prod, map_mul, mul_assoc]

@[simp]
/--
theorem `prod_empty` / 定理 `prod_empty`

English:
theorem prod_empty
  statement: (empty : NormalWord d).prod = 1
  proof: by
  simp [prod, empty]

中文:
定理 prod_empty
  结论: (empty : NormalWord d).乘积 = 1
  证明: by
  simp [prod, empty]
-/
theorem prod_empty : (empty : NormalWord d).prod = 1 := by
  simp [prod, empty]

/-- A constructor that multiplies a `NormalWord` by an element, with condition to make
sure the underlying list does get longer. -/
@[simps!]
/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: {i} (g : G i) (w : NormalWord d) (hmw : w.fstIdx != some i)
  body: letI n := (d.compl i).equiv (g * (φ i w.head))
  letI w' := Word.cons (n.2 : G i) w.toWord hmw
    (mt (coe_equiv_snd_eq_one_iff_mem _ (d.one_mem _)).1
      (mt (mul_mem_cancel_right (by simp)).1 hgr))
  { toWord := w'
    head := (MonoidHom.ofInjective (d.injective i)).symm n.1
    normalized := f

中文:
定义 cons
  签名: {i} (g : G i) (w : NormalWord d) (hmw : w.fstIdx != some i)
  定义体: letI n := (d.compl i).equiv (g * (φ i w.head))
  letI w' := Word.cons (n.2 : G i) w.toWord hmw
    (mt (coe_equiv_snd_eq_one_iff_mem _ (d.one_mem _)).1
      (mt (mul_mem_cancel_right (by simp)).1 hgr))
  { toWord := w'
    head := (MonoidHom.ofInjective (d.injective i)).symm n.1
    normalized := f

Depends on / 依赖: MonoidHom, MonoidHom.ofInjective, Sigma.mk.inj_iff, Word.cons, coe_equiv_snd_eq_one_iff_mem, d.compl, d.injective, d.one_mem, inj_iff, injective, mem_cons, mul_mem_cancel_right, normalized, ofInjective, one_mem, toWord, w.head, w.normalized, w.toWord
-/
noncomputable def cons {i} (g : G i) (w : NormalWord d) (hmw : w.fstIdx != some i)
    (hgr : g ∉ (φ i).range) : NormalWord d :=
  letI n := (d.compl i).equiv (g * (φ i w.head))
  letI w' := Word.cons (n.2 : G i) w.toWord hmw
    (mt (coe_equiv_snd_eq_one_iff_mem _ (d.one_mem _)).1
      (mt (mul_mem_cancel_right (by simp)).1 hgr))
  { toWord := w'
    head := (MonoidHom.ofInjective (d.injective i)).symm n.1
    normalized := fun i g hg => by
      simp only [w', Word.cons, mem_cons, Sigma.mk.inj_iff] at hg
      rcases hg with ⟨rfl, hg | hg⟩
      · simp
      · exact w.normalized _ _ (by assumption) }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `prod_cons` / 定理 `prod_cons`

English:
theorem prod_cons
  statement: {i} (g : G i) (w : NormalWord d) (hmw : w.fstIdx != some i)
  proof: by
  simp [prod, cons, ← of_apply_eq_base φ i, equiv_fst_eq_mul_inv, mul_assoc]

中文:
定理 prod_cons
  结论: {i} (g : G i) (w : NormalWord d) (hmw : w.fstIdx != some i)
  证明: by
  simp [prod, cons, ← of_apply_eq_base φ i, equiv_fst_eq_mul_inv, mul_assoc]

Depends on / 依赖: equiv_fst_eq_mul_inv, mul_assoc, of_apply_eq_base
-/
theorem prod_cons {i} (g : G i) (w : NormalWord d) (hmw : w.fstIdx != some i)
    (hgr : g ∉ (φ i).range) : (cons g w hmw hgr).prod = of i g * w.prod := by
  simp [prod, cons, ← of_apply_eq_base φ i, equiv_fst_eq_mul_inv, mul_assoc]

variable [DecidableEq ι] [forall i, DecidableEq (G i)]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `eq_one_of_smul_normalized` / 定理 `eq_one_of_smul_normalized`

English:
theorem eq_one_of_smul_normalized
  statement: (w : CoprodI.Word G) {i : ι} (h : H)
  proof: by
  simp only [← (d.compl _).equiv_snd_eq_self_iff_mem (one_mem _)] at hw hφw
  have hhead : ((d.compl i).equiv (Word.equivPair i w).head).2 =
      (Word.equivPair i w).head := by
    rw [Word.equivPair_head]
    split_ifs with h
    · rcases h with ⟨_, rfl⟩
      exact hw _ _ (List.head_mem _)
  

中文:
定理 eq_one_of_smul_normalized
  结论: (w : 余prodI.Word G) {i : ι} (h : H)
  证明: by
  simp only [← (d.compl _).equiv_snd_eq_self_iff_mem (one_mem _)] at hw hφw
  have hhead : ((d.compl i).equiv (Word.equivPair i w).head).2 =
      (Word.equivPair i w).head := by
    rw [Word.equivPair_head]
    split_ifs with h
    · rcases h with ⟨_, rfl⟩
      exact hw _ _ (List.head_mem _)
  

Depends on / 依赖: List.head_mem, Word.equivPair, Word.equivPair_head, d.compl, d.one_mem, equivPair, equivPair_head, equiv_mul_left_of_mem, equiv_one, equiv_snd_eq_self_iff_mem, head_mem, injective_iff_, one_mem, split_ifs
-/
theorem eq_one_of_smul_normalized (w : CoprodI.Word G) {i : ι} (h : H)
    (hw : forall i g, ⟨i, g⟩ in w.toList -> g in d.set i)
    (hφw : forall j g, ⟨j, g⟩ in (CoprodI.of (φ i h) • w).toList -> g in d.set j) :
    h = 1 := by
  simp only [← (d.compl _).equiv_snd_eq_self_iff_mem (one_mem _)] at hw hφw
  have hhead : ((d.compl i).equiv (Word.equivPair i w).head).2 =
      (Word.equivPair i w).head := by
    rw [Word.equivPair_head]
    split_ifs with h
    · rcases h with ⟨_, rfl⟩
      exact hw _ _ (List.head_mem _)
    · rw [equiv_one (d.compl i) (one_mem _) (d.one_mem _)]
  by_contra hh1
  have := hφw i (φ i h * (Word.equivPair i w).head) ?_
  · apply hh1
    rw [equiv_mul_left_of_mem (d.compl i) ⟨_]; rw [rfl⟩]; rw [hhead] at this
    simpa [((injective_iff_map_eq_one' _).1 (d.injective i))] using this
  · simp only [Word.mem_smul_iff, not_true, false_and, ne_eq, Option.mem_def, mul_right_inj,
      exists_eq_right', mul_eq_left, exists_prop, true_and, false_or]
    constructor
    · intro h
      apply_fun (d.compl i).equiv at h
      simp only [Prod.ext_iff, equiv_one (d.compl i) (one_mem _) (d.one_mem _),
        equiv_mul_left_of_mem (d.compl i) ⟨_, rfl⟩, hhead, Subtype.ext_iff,
        Prod.ext_iff] at h
      rcases h with ⟨h₁, h₂⟩
      rw [h₂]; rw [coe_mul]; rw [((d.compl i).coe_equiv_fst_eq_one_iff_mem (one_mem _)).mpr (d.one_mem _)]; rw [mul_one]; rw [Subtype.coe_mk]; rw [map_eq_one_iff (φ i) (d.injective i)] at h₁
      contradiction
    · rw [Word.equivPair_head]
      dsimp
      split_ifs with hep
      · rcases hep with ⟨hnil, rfl⟩
        rw [head?_eq_some_head hnil]
        simp_all
      · push Not at hep
        by_cases hw : w.toList = []
        · simp [hw, Word.fstIdx]
        · simp [head?_eq_some_head hw, Word.fstIdx, hep hw]

/--
theorem `ext_smul` / 定理 `ext_smul`

English:
theorem ext_smul
  statement: {w₁ w₂ : NormalWord d} (i : ι)
  proof: by
  rcases w₁ with ⟨w₁, h₁, hw₁⟩
  rcases w₂ with ⟨w₂, h₂, hw₂⟩
  dsimp at *
  rw [smul_eq_iff_eq_inv_smul]; rw [← mul_smul] at h
  subst h
  simp only [← map_inv, ← map_mul] at hw₁
  have : h₁⁻¹ * h₂ = 1 := eq_one_of_smul_normalized w₂ (h₁⁻¹ * h₂) hw₂ hw₁
  rw [inv_mul_eq_one] at this; subst this


中文:
定理 ext_smul
  结论: {w₁ w₂ : NormalWord d} (i : ι)
  证明: by
  rcases w₁ with ⟨w₁, h₁, hw₁⟩
  rcases w₂ with ⟨w₂, h₂, hw₂⟩
  dsimp at *
  rw [smul_eq_iff_eq_inv_smul]; rw [← mul_smul] at h
  subst h
  simp only [← map_inv, ← map_mul] at hw₁
  have : h₁⁻¹ * h₂ = 1 := eq_one_of_smul_normalized w₂ (h₁⁻¹ * h₂) hw₂ hw₁
  rw [inv_mul_eq_one] at this; subst this


Depends on / 依赖: eq_one_of_smul_normalized, inv_mul_eq_one, map_inv, map_mul, mul_smul, smul_eq_iff_eq_inv_smul
-/
theorem ext_smul {w₁ w₂ : NormalWord d} (i : ι)
    (h : CoprodI.of (φ i w₁.head) • w₁.toWord =
         CoprodI.of (φ i w₂.head) • w₂.toWord) :
    w₁ = w₂ := by
  rcases w₁ with ⟨w₁, h₁, hw₁⟩
  rcases w₂ with ⟨w₂, h₂, hw₂⟩
  dsimp at *
  rw [smul_eq_iff_eq_inv_smul]; rw [← mul_smul] at h
  subst h
  simp only [← map_inv, ← map_mul] at hw₁
  have : h₁⁻¹ * h₂ = 1 := eq_one_of_smul_normalized w₂ (h₁⁻¹ * h₂) hw₂ hw₁
  rw [inv_mul_eq_one] at this; subst this
  simp

/--
Definition of `rcons` / `rcons` 的定义

English:
definition rcons
  signature: (i : ι) (p : Pair d i)
  body: letI n := (d.compl i).equiv p.head
  let w := (Word.equivPair i).symm { p.toPair with head := n.2 }
  { toWord := w
    head := (MonoidHom.ofInjective (d.injective i)).symm n.1
    normalized := fun i g hg => by
        dsimp [w] at hg
        rw [Word.equivPair_symm]; rw [Word.mem_rcons_iff] at hg


中文:
定义 rcons
  签名: (i : ι) (p : 对 d i)
  定义体: letI n := (d.compl i).equiv p.head
  let w := (Word.equivPair i).symm { p.toPair with head := n.2 }
  { toWord := w
    head := (MonoidHom.ofInjective (d.injective i)).symm n.1
    normalized := fun i g hg => by
        dsimp [w] at hg
        rw [Word.equivPair_symm]; rw [Word.mem_rcons_iff] at hg


Depends on / 依赖: MonoidHom, MonoidHom.ofInjective, Word.equivPair, Word.equivPair_symm, Word.mem_rcons_iff, d.compl, d.injective, equivPair, equivPair_symm, injective, mem_rcons_iff, normalized, ofInjective, p.head, p.normalized, p.toPair, toPair, toWord
-/
noncomputable def rcons (i : ι) (p : Pair d i) : NormalWord d :=
  letI n := (d.compl i).equiv p.head
  let w := (Word.equivPair i).symm { p.toPair with head := n.2 }
  { toWord := w
    head := (MonoidHom.ofInjective (d.injective i)).symm n.1
    normalized := fun i g hg => by
        dsimp [w] at hg
        rw [Word.equivPair_symm]; rw [Word.mem_rcons_iff] at hg
        rcases hg with hg | ⟨_, rfl, rfl⟩
        · exact p.normalized _ _ hg
        · simp }

/--
theorem `rcons_injective` / 定理 `rcons_injective`

English:
theorem rcons_injective
  given: {i : ι}
  statement: Function.Injective (rcons (d := d) i)
  proof: by
  rintro ⟨⟨head₁, tail₁⟩, _⟩ ⟨⟨head₂, tail₂⟩, _⟩
  simp only [rcons, NormalWord.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
    Word.Pair.mk.injEq, Pair.mk.injEq, and_imp]
  rintro h₁ rfl h₃
  rw [← equiv_fst_mul_equiv_snd (d.compl i) head₁]; rw [← equiv_fst_mul_equiv_snd (d.compl i) head₂]; rw [h₁]

中文:
定理 rcons_injective
  条件: {i : ι}
  结论: 函数.单射 (rcons (d := d) i)
  证明: by
  rintro ⟨⟨head₁, tail₁⟩, _⟩ ⟨⟨head₂, tail₂⟩, _⟩
  simp only [rcons, NormalWord.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
    Word.Pair.mk.injEq, Pair.mk.injEq, and_imp]
  rintro h₁ rfl h₃
  rw [← equiv_fst_mul_equiv_snd (d.compl i) head₁]; rw [← equiv_fst_mul_equiv_snd (d.compl i) head₂]; rw [h₁]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, NormalWord, NormalWord.mk.injEq, Pair.mk.injEq, Word.Pair.mk.injEq, and_imp, apply_eq_iff_eq, d.compl, equiv_fst_mul_equiv_snd
-/
theorem rcons_injective {i : ι} : Function.Injective (rcons (d := d) i) := by
  rintro ⟨⟨head₁, tail₁⟩, _⟩ ⟨⟨head₂, tail₂⟩, _⟩
  simp only [rcons, NormalWord.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
    Word.Pair.mk.injEq, Pair.mk.injEq, and_imp]
  rintro h₁ rfl h₃
  rw [← equiv_fst_mul_equiv_snd (d.compl i) head₁]; rw [← equiv_fst_mul_equiv_snd (d.compl i) head₂]; rw [h₁]; rw [h₃]
  simp

/--
Definition of `equivPair` / `equivPair` 的定义

English:
definition equivPair
  signature: (i)
  body: letI toFun : NormalWord d -> Pair d i :=
    fun w =>
      letI p := Word.equivPair i (CoprodI.of (φ i w.head) • w.toWord)
      { toPair := p
        normalized := fun j g hg => by
          dsimp only [p] at hg
          rw [Word.of_smul_def]; rw [← Word.equivPair_symm]; rw [Equiv.apply_symm_appl

中文:
定义 equivPair
  签名: (i)
  定义体: letI toFun : NormalWord d -> Pair d i :=
    fun w =>
      letI p := Word.equivPair i (CoprodI.of (φ i w.head) • w.toWord)
      { toPair := p
        normalized := fun j g hg => by
          dsimp only [p] at hg
          rw [Word.of_smul_def]; rw [← Word.equivPair_symm]; rw [Equiv.apply_symm_appl

Depends on / 依赖: CoprodI, CoprodI.of, Equiv.apply_symm_apply, Function, Function.LeftInverse, LeftInverse, NormalWord, Word.equi, Word.equivPair, Word.equivPair_smul_same, Word.equivPair_symm, Word.mem_of_mem_equivPair_tail, Word.of_smul_def, apply_symm_apply, equivPair, equivPair_smul_same, equivPair_symm, ext_smul, leftInv, mem_of_mem_equivPair_tail
-/
noncomputable def equivPair (i) : NormalWord d ≃ Pair d i :=
  letI toFun : NormalWord d -> Pair d i :=
    fun w =>
      letI p := Word.equivPair i (CoprodI.of (φ i w.head) • w.toWord)
      { toPair := p
        normalized := fun j g hg => by
          dsimp only [p] at hg
          rw [Word.of_smul_def]; rw [← Word.equivPair_symm]; rw [Equiv.apply_symm_apply] at hg
          dsimp at hg
          exact w.normalized _ _ (Word.mem_of_mem_equivPair_tail _ hg) }
  haveI leftInv : Function.LeftInverse (rcons i) toFun :=
fun w => ext_smul i by
      simp only [toFun, rcons, Word.equivPair_symm,
        Word.equivPair_smul_same, Word.equivPair_tail_eq_inv_smul, Word.rcons_eq_smul,
        MonoidHom.apply_ofInjective_symm, equiv_fst_eq_mul_inv, mul_assoc, map_mul, map_inv,
        mul_smul, inv_smul_smul, smul_inv_smul]
  { toFun := toFun
    invFun := rcons i
    left_inv := leftInv
    right_inv := fun _ => rcons_injective (leftInv _) }

/--
Instance `summandAction` / 实例 `summandAction`

English:
instance summandAction
  signature: (i : ι)
  body: { smul := fun g w => (equivPair i).symm
      { equivPair i w with
        head := g * (equivPair i w).head }
    one_smul := fun _ => by
      dsimp +instances [instHSMul]
      rw [one_mul]
      exact (equivPair i).symm_apply_apply _
    mul_smul := fun _ _ _ => by
      dsimp +instances [instHSM

中文:
实例 summandAction
  签名: (i : ι)
  定义体: { smul := fun g w => (equivPair i).symm
      { equivPair i w with
        head := g * (equivPair i w).head }
    one_smul := fun _ => by
      dsimp +instances [instHSMul]
      rw [one_mul]
      exact (equivPair i).symm_apply_apply _
    mul_smul := fun _ _ _ => by
      dsimp +instances [instHSM

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply, equivPair, instHSMul, instances, mul_assoc, mul_smul, one_mul, one_smul, symm_apply_apply
-/
noncomputable instance summandAction (i : ι) : MulAction (G i) (NormalWord d) :=
  { smul := fun g w => (equivPair i).symm
      { equivPair i w with
        head := g * (equivPair i w).head }
    one_smul := fun _ => by
      dsimp +instances [instHSMul]
      rw [one_mul]
      exact (equivPair i).symm_apply_apply _
    mul_smul := fun _ _ _ => by
      dsimp +instances [instHSMul]
      simp [mul_assoc, Equiv.apply_symm_apply] }

/--
theorem `summand_smul_def'` / 定理 `summand_smul_def'`

English:
theorem summand_smul_def'
  given: {i : ι} (g : G i) (w : NormalWord d)
  proof: rfl

中文:
定理 summand_smul_def'
  条件: {i : ι} (g : G i) (w : NormalWord d)
  证明: rfl

Depends on / 依赖: equivPair
-/
theorem summand_smul_def' {i : ι} (g : G i) (w : NormalWord d) :
    g • w = (equivPair i).symm
      { equivPair i w with
        head := g * (equivPair i w).head } := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: : MulAction (PushoutI φ) (NormalWord d)
  body: MulAction.ofEndHom
    lift
      (fun _ => MulAction.toEndHom)
MulAction.toEndHom by
    intro i
    simp only [MulAction.toEndHom, DFunLike.ext_iff, MonoidHom.coe_comp, MonoidHom.coe_mk,
      OneHom.coe_mk, comp_apply]
    intro h
    funext w
    apply NormalWord.ext_smul i
    simp only [summan

中文:
实例 mulAction
  签名: : 乘法作用 (PushoutI φ) (NormalWord d)
  定义体: MulAction.ofEndHom
    lift
      (fun _ => MulAction.toEndHom)
MulAction.toEndHom by
    intro i
    simp only [MulAction.toEndHom, DFunLike.ext_iff, MonoidHom.coe_comp, MonoidHom.coe_mk,
      OneHom.coe_mk, comp_apply]
    intro h
    funext w
    apply NormalWord.ext_smul i
    simp only [summan

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, MonoidHom, MonoidHom.coe_comp, MonoidHom.coe_mk, MulAction, MulAction.ofEndHom, MulAction.toEndHom, NormalWord, NormalWord.ext_smul, OneHom, OneHom.coe_mk, Word.equivPair_smul_same, Word.equivPair_symm, Word.equivPair_tail_eq_inv_smul, Word.rcons_eq_smul, coe_comp, coe_fn_mk
-/
noncomputable instance mulAction : MulAction (PushoutI φ) (NormalWord d) :=
MulAction.ofEndHom
    lift
      (fun _ => MulAction.toEndHom)
MulAction.toEndHom by
    intro i
    simp only [MulAction.toEndHom, DFunLike.ext_iff, MonoidHom.coe_comp, MonoidHom.coe_mk,
      OneHom.coe_mk, comp_apply]
    intro h
    funext w
    apply NormalWord.ext_smul i
    simp only [summand_smul_def', equivPair, rcons, Word.equivPair_symm, Equiv.coe_fn_mk,
      Equiv.coe_fn_symm_mk, Word.equivPair_smul_same, Word.equivPair_tail_eq_inv_smul,
      Word.rcons_eq_smul, equiv_fst_eq_mul_inv, map_mul, map_inv, mul_smul, inv_smul_smul,
      smul_inv_smul, base_smul_def', MonoidHom.apply_ofInjective_symm]

/--
theorem `base_smul_def` / 定理 `base_smul_def`

English:
theorem base_smul_def
  given: (h : H) (w : NormalWord d)
  proof: rfl

中文:
定理 base_smul_def
  条件: (h : H) (w : NormalWord d)
  证明: rfl

Depends on / 依赖: w.head
-/
theorem base_smul_def (h : H) (w : NormalWord d) :
    base φ h • w = { w with head := h * w.head } := rfl

/--
theorem `summand_smul_def` / 定理 `summand_smul_def`

English:
theorem summand_smul_def
  given: {i : ι} (g : G i) (w : NormalWord d)
  proof: rfl

中文:
定理 summand_smul_def
  条件: {i : ι} (g : G i) (w : NormalWord d)
  证明: rfl

Depends on / 依赖: equivPair
-/
theorem summand_smul_def {i : ι} (g : G i) (w : NormalWord d) :
    of (φ := φ) i g • w = (equivPair i).symm
      { equivPair i w with
        head := g * (equivPair i w).head } := rfl

/--
theorem `of_smul_eq_smul` / 定理 `of_smul_eq_smul`

English:
theorem of_smul_eq_smul
  given: {i : ι} (g : G i) (w : NormalWord d)
  proof: by
  rw [summand_smul_def]; rw [summand_smul_def']

中文:
定理 of_smul_eq_smul
  条件: {i : ι} (g : G i) (w : NormalWord d)
  证明: by
  rw [summand_smul_def]; rw [summand_smul_def']

Depends on / 依赖: summand_smul_def
-/
theorem of_smul_eq_smul {i : ι} (g : G i) (w : NormalWord d) :
    of (φ := φ) i g • w = g • w := by
  rw [summand_smul_def]; rw [summand_smul_def']

/--
theorem `base_smul_eq_smul` / 定理 `base_smul_eq_smul`

English:
theorem base_smul_eq_smul
  given: (h : H) (w : NormalWord d)
  proof: by
  rw [base_smul_def]; rw [base_smul_def']

中文:
定理 base_smul_eq_smul
  条件: (h : H) (w : NormalWord d)
  证明: by
  rw [base_smul_def]; rw [base_smul_def']

Depends on / 依赖: base_smul_def
-/
theorem base_smul_eq_smul (h : H) (w : NormalWord d) :
    base φ h • w = h • w := by
  rw [base_smul_def]; rw [base_smul_def']

/-- Induction principle for `NormalWord`, that corresponds closely to inducting on
the underlying list. -/
@[elab_as_elim]
/--
Definition of `consRecOn` / `consRecOn` 的定义

English:
definition consRecOn
  signature: {motive : NormalWord d -> Sort _} (w : NormalWord d)
  body: by
  rcases w with ⟨w, head, h3⟩
  convert! base head ⟨w, 1, h3⟩ rfl ?_
  · simp [base_smul_def]
  · induction w using Word.consRecOn with
    | empty => exact empty
    | cons i g w h1 hg1 ih =>
      convert!
        cons i g ⟨w, 1, fun _ _ h => h3 _ _ (List.mem_cons_of_mem _ h)⟩ h1
          (h3 

中文:
定义 consRecOn
  签名: {motive : NormalWord d -> 类型层 _} (w : NormalWord d)
  定义体: by
  rcases w with ⟨w, head, h3⟩
  convert! base head ⟨w, 1, h3⟩ rfl ?_
  · simp [base_smul_def]
  · induction w using Word.consRecOn with
    | empty => exact empty
    | cons i g w h1 hg1 ih =>
      convert!
        cons i g ⟨w, 1, fun _ _ h => h3 _ _ (List.mem_cons_of_mem _ h)⟩ h1
          (h3 

Depends on / 依赖: List.mem_cons_of_mem, List.mem_cons_self, NormalWord, NormalWord.cons, Word.cons, Word.consRecOn, base_smul_def, consRecOn, convert, d.compl, d.injective, equiv_fst, equiv_snd_eq_self_iff_mem, injective, map_one, mem_cons_of_mem, mem_cons_self, mul_one, one_mem
-/
noncomputable def consRecOn {motive : NormalWord d -> Sort _} (w : NormalWord d)
    (empty : motive empty)
    (cons : forall (i : ι) (g : G i) (w : NormalWord d) (hmw : w.fstIdx != some i)
      (_hgn : g in d.set i) (hgr : g ∉ (φ i).range) (_hw1 : w.head = 1),
      motive w -> motive (cons g w hmw hgr))
    (base : forall (h : H) (w : NormalWord d), w.head = 1 -> motive w -> motive
      (base φ h • w)) : motive w := by
  rcases w with ⟨w, head, h3⟩
  convert! base head ⟨w, 1, h3⟩ rfl ?_
  · simp [base_smul_def]
  · induction w using Word.consRecOn with
    | empty => exact empty
    | cons i g w h1 hg1 ih =>
      convert!
        cons i g ⟨w, 1, fun _ _ h => h3 _ _ (List.mem_cons_of_mem _ h)⟩ h1
          (h3 _ _ List.mem_cons_self) ?_ rfl (ih ?_)
      · simp only [Word.cons, NormalWord.cons, map_one, mul_one,
          (equiv_snd_eq_self_iff_mem (d.compl i) (one_mem _)).2
          (h3 _ _ List.mem_cons_self)]
      · apply d.injective i
        simp only [NormalWord.cons, equiv_fst_eq_mul_inv, MonoidHom.apply_ofInjective_symm,
          map_one, mul_one, mul_inv_cancel, (equiv_snd_eq_self_iff_mem (d.compl i) (one_mem _)).2
          (h3 _ _ List.mem_cons_self)]
      · rwa [← SetLike.mem_coe,
          ← coe_equiv_snd_eq_one_iff_mem (d.compl i) (d.one_mem _),
          (equiv_snd_eq_self_iff_mem (d.compl i) (one_mem _)).2
          (h3 _ _ List.mem_cons_self)]


set_option backward.isDefEq.respectTransparency false in
/--
theorem `cons_eq_smul` / 定理 `cons_eq_smul`

English:
theorem cons_eq_smul
  statement: {i : ι} (g : G i)
  proof: by
  apply ext_smul i
  simp only [cons, Word.cons_eq_smul, MonoidHom.apply_ofInjective_symm,
    equiv_fst_eq_mul_inv, mul_assoc, map_mul, map_inv, mul_smul, inv_smul_smul, summand_smul_def,
    equivPair, rcons, Word.equivPair_symm, Word.rcons_eq_smul, Equiv.coe_fn_mk,
    Word.equivPair_tail_eq_i

中文:
定理 cons_eq_smul
  结论: {i : ι} (g : G i)
  证明: by
  apply ext_smul i
  simp only [cons, Word.cons_eq_smul, MonoidHom.apply_ofInjective_symm,
    equiv_fst_eq_mul_inv, mul_assoc, map_mul, map_inv, mul_smul, inv_smul_smul, summand_smul_def,
    equivPair, rcons, Word.equivPair_symm, Word.rcons_eq_smul, Equiv.coe_fn_mk,
    Word.equivPair_tail_eq_i

Depends on / 依赖: Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, MonoidHom, MonoidHom.apply_ofInjective_symm, Word.cons_eq_smul, Word.equivPair_symm, Word.equivPair_tail_eq_inv_smul, Word.rcons_eq_smul, apply_ofInjective_symm, coe_fn_mk, coe_fn_symm_mk, cons_eq_smul, equivPair, equivPair_symm, equivPair_tail_eq_inv_smul, equiv_fst_eq_mul_inv, ext_smul, inv_smul_smul, map_inv, map_mul
-/
theorem cons_eq_smul {i : ι} (g : G i)
    (w : NormalWord d) (hmw : w.fstIdx != some i)
    (hgr : g ∉ (φ i).range) : cons g w hmw hgr = of (φ := φ) i g • w := by
  apply ext_smul i
  simp only [cons, Word.cons_eq_smul, MonoidHom.apply_ofInjective_symm,
    equiv_fst_eq_mul_inv, mul_assoc, map_mul, map_inv, mul_smul, inv_smul_smul, summand_smul_def,
    equivPair, rcons, Word.equivPair_symm, Word.rcons_eq_smul, Equiv.coe_fn_mk,
    Word.equivPair_tail_eq_inv_smul, Equiv.coe_fn_symm_mk, smul_inv_smul]

@[simp]
/--
theorem `prod_summand_smul` / 定理 `prod_summand_smul`

English:
theorem prod_summand_smul
  given: {i : ι} (g : G i) (w : NormalWord d)
  proof: by
  simp only [prod, summand_smul_def', equivPair, rcons, Word.equivPair_symm,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Word.equivPair_smul_same,
    Word.equivPair_tail_eq_inv_smul, Word.rcons_eq_smul, ← of_apply_eq_base φ i,
    MonoidHom.apply_ofInjective_symm, equiv_fst_eq_mul_inv, mul_assoc,

中文:
定理 prod_summand_smul
  条件: {i : ι} (g : G i) (w : NormalWord d)
  证明: by
  simp only [prod, summand_smul_def', equivPair, rcons, Word.equivPair_symm,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Word.equivPair_smul_same,
    Word.equivPair_tail_eq_inv_smul, Word.rcons_eq_smul, ← of_apply_eq_base φ i,
    MonoidHom.apply_ofInjective_symm, equiv_fst_eq_mul_inv, mul_assoc,

Depends on / 依赖: Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, MonoidHom, MonoidHom.apply_ofInjective_symm, Word.equivPair_smul_same, Word.equivPair_symm, Word.equivPair_tail_eq_inv_smul, Word.prod_smul, Word.rcons_eq_smul, apply_ofInjective_symm, coe_fn_mk, coe_fn_symm_mk, equivPair, equivPair_smul_same, equivPair_symm, equivPair_tail_eq_inv_smul, equiv_fst_eq_mul_inv, inv_mul_cancel_left, map_inv, map_mul
-/
theorem prod_summand_smul {i : ι} (g : G i) (w : NormalWord d) :
    (g • w).prod = of i g * w.prod := by
  simp only [prod, summand_smul_def', equivPair, rcons, Word.equivPair_symm,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Word.equivPair_smul_same,
    Word.equivPair_tail_eq_inv_smul, Word.rcons_eq_smul, ← of_apply_eq_base φ i,
    MonoidHom.apply_ofInjective_symm, equiv_fst_eq_mul_inv, mul_assoc, map_mul, map_inv,
    Word.prod_smul, ofCoprodI_of, inv_mul_cancel_left, mul_inv_cancel_left]

@[simp]
/--
theorem `prod_smul` / 定理 `prod_smul`

English:
theorem prod_smul
  given: (g : PushoutI φ) (w : NormalWord d)
  proof: by
  induction g using PushoutI.induction_on generalizing w with
  | of i g => rw [of_smul_eq_smul, prod_summand_smul]
  | base h => rw [base_smul_eq_smul, prod_base_smul]
  | mul x y ihx ihy => rw [mul_smul, ihx, ihy, mul_assoc]

中文:
定理 prod_smul
  条件: (g : PushoutI φ) (w : NormalWord d)
  证明: by
  induction g using PushoutI.induction_on generalizing w with
  | of i g => rw [of_smul_eq_smul, prod_summand_smul]
  | base h => rw [base_smul_eq_smul, prod_base_smul]
  | mul x y ihx ihy => rw [mul_smul, ihx, ihy, mul_assoc]

Depends on / 依赖: PushoutI, PushoutI.induction_on, base_smul_eq_smul, generalizing, induction_on, mul_assoc, mul_smul, of_smul_eq_smul, prod_base_smul, prod_summand_smul
-/
theorem prod_smul (g : PushoutI φ) (w : NormalWord d) :
    (g • w).prod = g * w.prod := by
  induction g using PushoutI.induction_on generalizing w with
  | of i g => rw [of_smul_eq_smul, prod_summand_smul]
  | base h => rw [base_smul_eq_smul, prod_base_smul]
  | mul x y ihx ihy => rw [mul_smul, ihx, ihy, mul_assoc]

/--
theorem `prod_smul_empty` / 定理 `prod_smul_empty`

English:
theorem prod_smul_empty
  given: (w : NormalWord d)
  statement: w.prod • empty = w
  proof: by
  induction w using consRecOn with
  | empty => simp
  | cons i g w _ _ _ _ ih =>
    rw [prod_cons]; rw [mul_smul]; rw [ih]; rw [cons_eq_smul]
  | base h w _ ih =>
    rw [prod_smul]; rw [mul_smul]; rw [ih]

中文:
定理 prod_smul_empty
  条件: (w : NormalWord d)
  结论: w.乘积 • empty = w
  证明: by
  induction w using consRecOn with
  | empty => simp
  | cons i g w _ _ _ _ ih =>
    rw [prod_cons]; rw [mul_smul]; rw [ih]; rw [cons_eq_smul]
  | base h w _ ih =>
    rw [prod_smul]; rw [mul_smul]; rw [ih]

Depends on / 依赖: consRecOn, cons_eq_smul, mul_smul, prod_cons, prod_smul
-/
theorem prod_smul_empty (w : NormalWord d) : w.prod • empty = w := by
  induction w using consRecOn with
  | empty => simp
  | cons i g w _ _ _ _ ih =>
    rw [prod_cons]; rw [mul_smul]; rw [ih]; rw [cons_eq_smul]
  | base h w _ ih =>
    rw [prod_smul]; rw [mul_smul]; rw [ih]

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : PushoutI φ ≃ NormalWord d
  body: { toFun := fun g => g • .empty
    invFun := fun w => w.prod
    left_inv := fun g => by
      simp only [prod_smul, prod_empty, mul_one]
    right_inv := fun w => prod_smul_empty w }

中文:
定义 equiv
  签名: : PushoutI φ ≃ NormalWord d
  定义体: { toFun := fun g => g • .empty
    invFun := fun w => w.prod
    left_inv := fun g => by
      simp only [prod_smul, prod_empty, mul_one]
    right_inv := fun w => prod_smul_empty w }

Depends on / 依赖: invFun, left_inv, mul_one, prod_empty, prod_smul, prod_smul_empty, right_inv, w.prod
-/
noncomputable def equiv : PushoutI φ ≃ NormalWord d :=
  { toFun := fun g => g • .empty
    invFun := fun w => w.prod
    left_inv := fun g => by
      simp only [prod_smul, prod_empty, mul_one]
    right_inv := fun w => prod_smul_empty w }

/--
theorem `prod_injective` / 定理 `prod_injective`

English:
theorem prod_injective
  statement: {ι : Type*} {G : ι -> Type*} [(i : ι) -> Group (G i)] {φ : (i : ι) -> H ->* G i}
  proof: by
  let := Classical.decEq ι
  let := fun i => Classical.decEq (G i)
  exact equiv.symm.injective

中文:
定理 prod_injective
  结论: {ι : 类型} {G : ι -> 类型} [(i : ι) -> 群 (G i)] {φ : (i : ι) -> H ->* G i}
  证明: by
  let := Classical.decEq ι
  let := fun i => Classical.decEq (G i)
  exact equiv.symm.injective

Depends on / 依赖: Classical, Classical.decEq, equiv.symm.injective, injective
-/
theorem prod_injective {ι : Type*} {G : ι -> Type*} [(i : ι) -> Group (G i)] {φ : (i : ι) -> H ->* G i}
    {d : Transversal φ} : Function.Injective (prod : NormalWord d -> PushoutI φ) := by
  let := Classical.decEq ι
  let := fun i => Classical.decEq (G i)
  exact equiv.symm.injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FaithfulSMul (PushoutI φ) (NormalWord d)
  body: ⟨fun h => by simpa using congr_arg prod (h empty)⟩

中文:
实例 :
  签名: 忠实标量乘法 (PushoutI φ) (NormalWord d)
  定义体: ⟨fun h => by simpa using congr_arg prod (h empty)⟩

Depends on / 依赖: congr_arg
-/
instance : FaithfulSMul (PushoutI φ) (NormalWord d) :=
  ⟨fun h => by simpa using congr_arg prod (h empty)⟩

instance (i : ι) : FaithfulSMul (G i) (NormalWord d) :=
  ⟨by simp [summand_smul_def']⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FaithfulSMul H (NormalWord d)
  body: ⟨by simp [base_smul_def']⟩

中文:
实例 :
  签名: 忠实标量乘法 H (NormalWord d)
  定义体: ⟨by simp [base_smul_def']⟩

Depends on / 依赖: base_smul_def
-/
instance : FaithfulSMul H (NormalWord d) :=
  ⟨by simp [base_smul_def']⟩

end NormalWord

open NormalWord

/--
theorem `of_injective` / 定理 `of_injective`

English:
theorem of_injective
  given: (hφ : forall i, Function.Injective (φ i)) (i : ι)
  proof: by
  rcases transversal_nonempty φ hφ with ⟨d⟩
  let _ := Classical.decEq ι
  let _ := fun i => Classical.decEq (G i)
  refine Function.Injective.of_comp
    (f := ((· • ·) : PushoutI φ -> NormalWord d -> NormalWord d)) ?_
  intro _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp

中文:
定理 of_injective
  条件: (hφ : 对任意 i, 函数.单射 (φ i)) (i : ι)
  证明: by
  rcases transversal_nonempty φ hφ with ⟨d⟩
  let _ := Classical.decEq ι
  let _ := fun i => Classical.decEq (G i)
  refine Function.Injective.of_comp
    (f := ((· • ·) : PushoutI φ -> NormalWord d -> NormalWord d)) ?_
  intro _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp

Depends on / 依赖: Classical, Classical.decEq, Function, Function.Injective.of_comp, Injective, NormalWord, PushoutI, eq_of_smul_eq_smul, funext_iff, of_comp, of_smul_eq_smul, transversal_nonempty
-/
theorem of_injective (hφ : forall i, Function.Injective (φ i)) (i : ι) :
    Function.Injective (of (φ := φ) i) := by
  rcases transversal_nonempty φ hφ with ⟨d⟩
  let _ := Classical.decEq ι
  let _ := fun i => Classical.decEq (G i)
  refine Function.Injective.of_comp
    (f := ((· • ·) : PushoutI φ -> NormalWord d -> NormalWord d)) ?_
  intro _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp_all [funext_iff, of_smul_eq_smul])

/--
theorem `base_injective` / 定理 `base_injective`

English:
theorem base_injective
  given: (hφ : forall i, Function.Injective (φ i))
  proof: by
  rcases transversal_nonempty φ hφ with ⟨d⟩
  let _ := Classical.decEq ι
  let _ := fun i => Classical.decEq (G i)
  refine Function.Injective.of_comp
    (f := ((· • ·) : PushoutI φ -> NormalWord d -> NormalWord d)) ?_
  intro _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp

中文:
定理 base_injective
  条件: (hφ : 对任意 i, 函数.单射 (φ i))
  证明: by
  rcases transversal_nonempty φ hφ with ⟨d⟩
  let _ := Classical.decEq ι
  let _ := fun i => Classical.decEq (G i)
  refine Function.Injective.of_comp
    (f := ((· • ·) : PushoutI φ -> NormalWord d -> NormalWord d)) ?_
  intro _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp

Depends on / 依赖: Classical, Classical.decEq, Function, Function.Injective.of_comp, Injective, NormalWord, PushoutI, base_smul_eq_smul, eq_of_smul_eq_smul, funext_iff, of_comp, transversal_nonempty
-/
theorem base_injective (hφ : forall i, Function.Injective (φ i)) :
    Function.Injective (base φ) := by
  rcases transversal_nonempty φ hφ with ⟨d⟩
  let _ := Classical.decEq ι
  let _ := fun i => Classical.decEq (G i)
  refine Function.Injective.of_comp
    (f := ((· • ·) : PushoutI φ -> NormalWord d -> NormalWord d)) ?_
  intro _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp_all [funext_iff, base_smul_eq_smul])

section Reduced

variable (φ) in
/--
Definition of `Reduced` / `Reduced` 的定义

English:
definition Reduced
  signature: (w : Word G)
  body: forall g, g in w.toList -> g.2 ∉ (φ g.1).range

中文:
定义 既约
  签名: (w : Word G)
  定义体: forall g, g in w.toList -> g.2 ∉ (φ g.1).range

Depends on / 依赖: toList, w.toList
-/
def Reduced (w : Word G) : Prop :=
  forall g, g in w.toList -> g.2 ∉ (φ g.1).range

/--
theorem `Reduced.exists_normalWord_prod_eq` / 定理 `Reduced.exists_normalWord_prod_eq`

English:
theorem Reduced.exists_normalWord_prod_eq
  given: (d : Transversal φ) {w : Word G} (hw : Reduced φ w)
  proof: by
  induction w using Word.consRecOn with
  | empty => exact ⟨empty, by simp, rfl⟩
  | cons i g w hIdx hg1 ih =>
    rcases ih (fun _ hg => hw _ (List.mem_cons_of_mem _ hg)) with
      ⟨w', hw'prod, hw'map⟩
    refine ⟨cons g w' ?_ ?_, ?_⟩
    · rwa [Word.fstIdx, ← List.head?_map, hw'map, List.head

中文:
定理 既约.存在_normalWord_prod_eq
  条件: (d : 横截 φ) {w : Word G} (hw : 既约 φ w)
  证明: by
  induction w using Word.consRecOn with
  | empty => exact ⟨empty, by simp, rfl⟩
  | cons i g w hIdx hg1 ih =>
    rcases ih (fun _ hg => hw _ (List.mem_cons_of_mem _ hg)) with
      ⟨w', hw'prod, hw'map⟩
    refine ⟨cons g w' ?_ ?_, ?_⟩
    · rwa [Word.fstIdx, ← List.head?_map, hw'map, List.head

Depends on / 依赖: List.head, List.mem_cons_of_mem, List.mem_cons_self, Word.consRecOn, Word.fstIdx, _map, consRecOn, fstIdx, mem_cons_of_mem, mem_cons_self
-/
theorem Reduced.exists_normalWord_prod_eq (d : Transversal φ) {w : Word G} (hw : Reduced φ w) :
    exists w' : NormalWord d, w'.prod = ofCoprodI w.prod ∧
      w'.toList.map Sigma.fst = w.toList.map Sigma.fst := by
  induction w using Word.consRecOn with
  | empty => exact ⟨empty, by simp, rfl⟩
  | cons i g w hIdx hg1 ih =>
    rcases ih (fun _ hg => hw _ (List.mem_cons_of_mem _ hg)) with
      ⟨w', hw'prod, hw'map⟩
    refine ⟨cons g w' ?_ ?_, ?_⟩
    · rwa [Word.fstIdx, ← List.head?_map, hw'map, List.head?_map]
    · exact hw _ List.mem_cons_self
    · simp [hw'prod, hw'map]

/--
theorem `Reduced.eq_empty_of_mem_range` / 定理 `Reduced.eq_empty_of_mem_range`

English:
theorem Reduced.eq_empty_of_mem_range
  proof: by
  rcases transversal_nonempty φ hφ with ⟨d⟩
  rcases hw.exists_normalWord_prod_eq d with ⟨w', hw'prod, hw'map⟩
  rcases h with ⟨h, heq⟩
  have : (NormalWord.prod (d := d) ⟨.empty, h, by simp⟩) = base φ h := by
    simp [NormalWord.prod]
  rw [← hw'prod]; rw [← this] at heq
  suffices w'.toWord = 

中文:
定理 既约.eq_empty_of_mem_range
  证明: by
  rcases transversal_nonempty φ hφ with ⟨d⟩
  rcases hw.exists_normalWord_prod_eq d with ⟨w', hw'prod, hw'map⟩
  rcases h with ⟨h, heq⟩
  have : (NormalWord.prod (d := d) ⟨.empty, h, by simp⟩) = base φ h := by
    simp [NormalWord.prod]
  rw [← hw'prod]; rw [← this] at heq
  suffices w'.toWord = 

Depends on / 依赖: NormalWord, NormalWord.prod, eq_comm, exists_normalWord_prod_eq, hw.exists_normalWord_prod_eq, prod_injective, toWord, transversal_nonempty
-/
theorem Reduced.eq_empty_of_mem_range
    (hφ : forall i, Injective (φ i)) {w : Word G} (hw : Reduced φ w)
    (h : ofCoprodI w.prod in (base φ).range) : w = .empty := by
  rcases transversal_nonempty φ hφ with ⟨d⟩
  rcases hw.exists_normalWord_prod_eq d with ⟨w', hw'prod, hw'map⟩
  rcases h with ⟨h, heq⟩
  have : (NormalWord.prod (d := d) ⟨.empty, h, by simp⟩) = base φ h := by
    simp [NormalWord.prod]
  rw [← hw'prod]; rw [← this] at heq
  suffices w'.toWord = .empty by
    simp [this, @eq_comm _ []] at hw'map
    ext
    simp [hw'map]
  rw [← prod_injective heq]

end Reduced

/--
theorem `inf_of_range_eq_base_range` / 定理 `inf_of_range_eq_base_range`

English:
theorem inf_of_range_eq_base_range
  proof: le_antisymm
    (by
      intro x ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩
      by_contra hx
      have hx1 : x != 1 := by rintro rfl; simp_all only [ne_eq, one_mem, not_true_eq_false]
      have hg₁1 : g₁ != 1 :=
        ne_of_apply_ne (of (φ := φ) i) (by simp_all)
      have hg₂1 : g₂ != 1 :=
        ne_of_apply_n

中文:
定理 inf_of_range_eq_base_range
  证明: le_antisymm
    (by
      intro x ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩
      by_contra hx
      have hx1 : x != 1 := by rintro rfl; simp_all only [ne_eq, one_mem, not_true_eq_false]
      have hg₁1 : g₁ != 1 :=
        ne_of_apply_ne (of (φ := φ) i) (by simp_all)
      have hg₂1 : g₂ != 1 :=
        ne_of_apply_n

Depends on / 依赖: MonoidHom, MonoidHom.mem_range, le_antisymm, mem_range, ne_eq, ne_of_apply_ne, not_true_eq_false, of_apply_eq_base, one_mem
-/
theorem inf_of_range_eq_base_range
    (hφ : forall i, Injective (φ i)) {i j : ι} (hij : i != j) :
    (of i).range ⊓ (of j).range = (base φ).range :=
  le_antisymm
    (by
      intro x ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩
      by_contra hx
      have hx1 : x != 1 := by rintro rfl; simp_all only [ne_eq, one_mem, not_true_eq_false]
      have hg₁1 : g₁ != 1 :=
        ne_of_apply_ne (of (φ := φ) i) (by simp_all)
      have hg₂1 : g₂ != 1 :=
        ne_of_apply_ne (of (φ := φ) j) (by simp_all)
      have hg₁r : g₁ ∉ (φ i).range := by
        rintro ⟨y, rfl⟩
        subst hg₁
        exact hx (of_apply_eq_base φ i y ▸ MonoidHom.mem_range.2 ⟨y, rfl⟩)
      have hg₂r : g₂ ∉ (φ j).range := by
        rintro ⟨y, rfl⟩
        subst hg₂
        exact hx (of_apply_eq_base φ j y ▸ MonoidHom.mem_range.2 ⟨y, rfl⟩)
      let w : Word G := ⟨[⟨_, g₁⟩, ⟨_, g₂⁻¹⟩], by simp_all, by simp_all⟩
      have hw : Reduced φ w := by
        simp only [w, Reduced, List.mem_cons,
          forall_eq_or_imp, not_false_eq_true,
          hg₁r, hg₂r, List.mem_nil_iff, false_imp_iff, imp_true_iff, and_true,
          inv_mem_iff]
      have := hw.eq_empty_of_mem_range hφ (by
        simp only [w, Word.prod, List.map_cons, List.prod_cons, List.prod_nil,
          List.map_nil, map_mul, ofCoprodI_of, hg₁, hg₂, map_inv, mul_one,
          mul_inv_cancel, one_mem])
      simp [w, Word.empty] at this)
    (le_inf
      (by rw [← of_comp_eq_base i]
          rintro _ ⟨h, rfl⟩
          exact MonoidHom.mem_range.2 ⟨φ i h, rfl⟩)
      (by rw [← of_comp_eq_base j]
          rintro _ ⟨h, rfl⟩
          exact MonoidHom.mem_range.2 ⟨φ j h, rfl⟩))

end PushoutI

end Monoid
