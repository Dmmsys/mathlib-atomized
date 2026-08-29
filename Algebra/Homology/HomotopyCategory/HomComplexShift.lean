/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Tactic.Linarith

/-! # Shifting cochains

Let `C` be a preadditive category. Given two cochain complexes (indexed by `ℤ`),
the type of cochains `HomComplex.Cochain K L n` of degree `n` was introduced
in `Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean`. In this file, we
study how these cochains behave with respect to the shift on the complexes `K`
and `L`.

When `n`, `a`, `n'` are integers such that `h : n' + a = n`,
we obtain `rightShiftAddEquiv K L n a n' h : Cochain K L n ≃+ Cochain K (L⟦a⟧) n'`.
This definition does not involve signs, but the analogous definition
of `leftShiftAddEquiv K L n a n' h' : Cochain K L n ≃+ Cochain (K⟦a⟧) L n'`
when `h' : n + a = n'` does involve signs, as we follow the conventions
appearing in the introduction of
[Brian Conrad's book *Grothendieck duality and base change*][conrad2000].

## References
* [Brian Conrad, Grothendieck duality and base change][conrad2000]

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C Int} {n : Int}

namespace CochainComplex.HomComplex

namespace Cochain

variable (γ γ₁ γ₂ : Cochain K L n)

/--
Definition of `rightShift` / `rightShift` 的定义

English:
definition rightShift
  signature: (a n' : Int) (hn' : n' + a = n)
  body: Cochain.mk (fun p q hpq => γ.v p (p + n) rfl ≫
    (L.shiftFunctorObjXIso a q (p + n) (by lia)).inv)

中文:
定义 rightShift
  签名: (a n' : 整数) (hn' : n' + a = n)
  定义体: Cochain.mk (fun p q hpq => γ.v p (p + n) rfl ≫
    (L.shiftFunctorObjXIso a q (p + n) (by lia)).inv)

Depends on / 依赖: Cochain, Cochain.mk, L.shiftFunctorObjXIso, shiftFunctorObjXIso
-/
def rightShift (a n' : Int) (hn' : n' + a = n) : Cochain K (L⟦a⟧) n' :=
  Cochain.mk (fun p q hpq => γ.v p (p + n) rfl ≫
    (L.shiftFunctorObjXIso a q (p + n) (by lia)).inv)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `rightShift_v` / 引理 `rightShift_v`

English:
lemma rightShift_v
  statement: (a n' : Int) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q)
  proof: by
  subst hp'
  dsimp only [rightShift]
  simp only [mk_v]

中文:
引理 rightShift_v
  结论: (a n' : 整数) (hn' : n' + a = n) (p q : 整数) (hpq : p + n' = q)
  证明: by
  subst hp'
  dsimp only [rightShift]
  simp only [mk_v]

Depends on / 依赖: mk_v, rightShift
-/
lemma rightShift_v (a n' : Int) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q)
    (p' : Int) (hp' : p + n = p') :
    (γ.rightShift a n' hn').v p q hpq = γ.v p p' hp' ≫
      (L.shiftFunctorObjXIso a q p' (by rw [← hp', ← hpq, ← hn', add_assoc])).inv := by
  subst hp'
  dsimp only [rightShift]
  simp only [mk_v]

/--
Definition of `leftShift` / `leftShift` 的定义

English:
definition leftShift
  signature: (a n' : Int) (hn' : n + a = n')
  body: Cochain.mk (fun p q hpq => (a * n' + ((a * (a - 1)) / 2)).negOnePow •
    (K.shiftFunctorObjXIso a p (p + a) rfl).hom ≫ γ.v (p + a) q (by lia))

中文:
定义 leftShift
  签名: (a n' : 整数) (hn' : n + a = n')
  定义体: Cochain.mk (fun p q hpq => (a * n' + ((a * (a - 1)) / 2)).negOnePow •
    (K.shiftFunctorObjXIso a p (p + a) rfl).hom ≫ γ.v (p + a) q (by lia))

Depends on / 依赖: Cochain, Cochain.mk, K.shiftFunctorObjXIso, negOnePow, shiftFunctorObjXIso
-/
def leftShift (a n' : Int) (hn' : n + a = n') : Cochain (K⟦a⟧) L n' :=
  Cochain.mk (fun p q hpq => (a * n' + ((a * (a - 1)) / 2)).negOnePow •
    (K.shiftFunctorObjXIso a p (p + a) rfl).hom ≫ γ.v (p + a) q (by lia))

/--
lemma `leftShift_v` / 引理 `leftShift_v`

English:
lemma leftShift_v
  statement: (a n' : Int) (hn' : n + a = n') (p q : Int) (hpq : p + n' = q)
  proof: by
  obtain rfl : p' = p + a := by lia
  dsimp only [leftShift]
  simp only [mk_v]

中文:
引理 leftShift_v
  结论: (a n' : 整数) (hn' : n + a = n') (p q : 整数) (hpq : p + n' = q)
  证明: by
  obtain rfl : p' = p + a := by lia
  dsimp only [leftShift]
  simp only [mk_v]

Depends on / 依赖: leftShift, mk_v
-/
lemma leftShift_v (a n' : Int) (hn' : n + a = n') (p q : Int) (hpq : p + n' = q)
    (p' : Int) (hp' : p' + n = q) :
    (γ.leftShift a n' hn').v p q hpq = (a * n' + ((a * (a - 1)) / 2)).negOnePow •
      (K.shiftFunctorObjXIso a p p'
        (by rw [← add_left_inj n, hp', add_assoc, add_comm a, hn', hpq])).hom ≫ γ.v p' q hp' := by
  obtain rfl : p' = p + a := by lia
  dsimp only [leftShift]
  simp only [mk_v]

/--
Definition of `rightUnshift` / `rightUnshift` 的定义

English:
definition rightUnshift
  signature: {n' a : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n)
  body: Cochain.mk (fun p q hpq => γ.v p (p + n') rfl ≫
    (L.shiftFunctorObjXIso a (p + n') q (by rw [← hpq, add_assoc, hn])).hom)

中文:
定义 rightUnshift
  签名: {n' a : 整数} (γ : Cochain K (L⟦a⟧) n') (n : 整数) (hn : n' + a = n)
  定义体: Cochain.mk (fun p q hpq => γ.v p (p + n') rfl ≫
    (L.shiftFunctorObjXIso a (p + n') q (by rw [← hpq, add_assoc, hn])).hom)

Depends on / 依赖: Cochain, Cochain.mk, L.shiftFunctorObjXIso, add_assoc, shiftFunctorObjXIso
-/
def rightUnshift {n' a : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n) :
    Cochain K L n :=
  Cochain.mk (fun p q hpq => γ.v p (p + n') rfl ≫
    (L.shiftFunctorObjXIso a (p + n') q (by rw [← hpq, add_assoc, hn])).hom)

/--
lemma `rightUnshift_v` / 引理 `rightUnshift_v`

English:
lemma rightUnshift_v
  statement: {n' a : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n)
  proof: by
  subst hp'
  dsimp only [rightUnshift]
  simp only [mk_v]

中文:
引理 rightUnshift_v
  结论: {n' a : 整数} (γ : Cochain K (L⟦a⟧) n') (n : 整数) (hn : n' + a = n)
  证明: by
  subst hp'
  dsimp only [rightUnshift]
  simp only [mk_v]

Depends on / 依赖: mk_v, rightUnshift
-/
lemma rightUnshift_v {n' a : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n)
    (p q : Int) (hpq : p + n = q) (p' : Int) (hp' : p + n' = p') :
    (γ.rightUnshift n hn).v p q hpq = γ.v p p' hp' ≫
      (L.shiftFunctorObjXIso a p' q (by rw [← hpq, ← hn, ← add_assoc, hp'])).hom := by
  subst hp'
  dsimp only [rightUnshift]
  simp only [mk_v]

/--
Definition of `leftUnshift` / `leftUnshift` 的定义

English:
definition leftUnshift
  signature: {n' a : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a = n')
  body: Cochain.mk (fun p q hpq => (a * n' + ((a * (a - 1)) / 2)).negOnePow •
    (K.shiftFunctorObjXIso a (p - a) p (by lia)).inv ≫ γ.v (p - a) q (by lia))

中文:
定义 leftUnshift
  签名: {n' a : 整数} (γ : Cochain (K⟦a⟧) L n') (n : 整数) (hn : n + a = n')
  定义体: Cochain.mk (fun p q hpq => (a * n' + ((a * (a - 1)) / 2)).negOnePow •
    (K.shiftFunctorObjXIso a (p - a) p (by lia)).inv ≫ γ.v (p - a) q (by lia))

Depends on / 依赖: Cochain, Cochain.mk, K.shiftFunctorObjXIso, negOnePow, shiftFunctorObjXIso
-/
def leftUnshift {n' a : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a = n') :
    Cochain K L n :=
  Cochain.mk (fun p q hpq => (a * n' + ((a * (a - 1)) / 2)).negOnePow •
    (K.shiftFunctorObjXIso a (p - a) p (by lia)).inv ≫ γ.v (p - a) q (by lia))

/--
lemma `leftUnshift_v` / 引理 `leftUnshift_v`

English:
lemma leftUnshift_v
  statement: {n' a : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a = n')
  proof: by
  obtain rfl : p' = p - a := by lia
  rfl

中文:
引理 leftUnshift_v
  结论: {n' a : 整数} (γ : Cochain (K⟦a⟧) L n') (n : 整数) (hn : n + a = n')
  证明: by
  obtain rfl : p' = p - a := by lia
  rfl
-/
lemma leftUnshift_v {n' a : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a = n')
    (p q : Int) (hpq : p + n = q) (p' : Int) (hp' : p' + n' = q) :
    (γ.leftUnshift n hn).v p q hpq = (a * n' + ((a * (a - 1)) / 2)).negOnePow •
      (K.shiftFunctorObjXIso a p' p (by lia)).inv ≫ γ.v p' q (by lia) := by
  obtain rfl : p' = p - a := by lia
  rfl

/--
Definition of `shift` / `shift` 的定义

English:
definition shift
  signature: (a : Int)
  body: Cochain.mk (fun p q hpq => (K.shiftFunctorObjXIso a p _ rfl).hom ≫
    γ.v (p + a) (q + a) (by lia) ≫ (L.shiftFunctorObjXIso a q _ rfl).inv)

中文:
定义 shift
  签名: (a : 整数)
  定义体: Cochain.mk (fun p q hpq => (K.shiftFunctorObjXIso a p _ rfl).hom ≫
    γ.v (p + a) (q + a) (by lia) ≫ (L.shiftFunctorObjXIso a q _ rfl).inv)

Depends on / 依赖: Cochain, Cochain.mk, K.shiftFunctorObjXIso, L.shiftFunctorObjXIso, shiftFunctorObjXIso
-/
def shift (a : Int) : Cochain (K⟦a⟧) (L⟦a⟧) n :=
  Cochain.mk (fun p q hpq => (K.shiftFunctorObjXIso a p _ rfl).hom ≫
    γ.v (p + a) (q + a) (by lia) ≫ (L.shiftFunctorObjXIso a q _ rfl).inv)

/--
lemma `shift_v` / 引理 `shift_v`

English:
lemma shift_v
  statement: (a : Int) (p q : Int) (hpq : p + n = q) (p' q' : Int)
  proof: by
  subst hp' hq'
  rfl

中文:
引理 shift_v
  结论: (a : 整数) (p q : 整数) (hpq : p + n = q) (p' q' : 整数)
  证明: by
  subst hp' hq'
  rfl
-/
lemma shift_v (a : Int) (p q : Int) (hpq : p + n = q) (p' q' : Int)
    (hp' : p' = p + a) (hq' : q' = q + a) :
    (γ.shift a).v p q hpq = (K.shiftFunctorObjXIso a p p' hp').hom ≫
      γ.v p' q' (by rw [hp', hq', ← hpq, add_assoc, add_comm a, add_assoc]) ≫
      (L.shiftFunctorObjXIso a q q' hq').inv := by
  subst hp' hq'
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `shift_v'` / 引理 `shift_v'`

English:
lemma shift_v'
  given: (a : Int) (p q : Int) (hpq : p + n = q)
  proof: by
  simp only [shift_v γ a p q hpq _ _ rfl rfl, shiftFunctor_obj_X, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

中文:
引理 shift_v'
  条件: (a : 整数) (p q : 整数) (hpq : p + n = q)
  证明: by
  simp only [shift_v γ a p q hpq _ _ rfl rfl, shiftFunctor_obj_X, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv, XIsoOfEq_rfl, comp_id, id_comp, refl_hom, refl_inv, shiftFunctorObjXIso, shiftFunctor_obj_X, shift_v
-/
lemma shift_v' (a : Int) (p q : Int) (hpq : p + n = q) :
    (γ.shift a).v p q hpq = γ.v (p + a) (q + a) (by lia) := by
  simp only [shift_v γ a p q hpq _ _ rfl rfl, shiftFunctor_obj_X, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `rightUnshift_rightShift` / 引理 `rightUnshift_rightShift`

English:
lemma rightUnshift_rightShift
  given: (a n' : Int) (hn' : n' + a = n)
  proof: by
  ext p q hpq
  simp only [rightUnshift_v _ n hn' p q hpq (p + n') rfl,
    γ.rightShift_v _ _ hn' p (p + n') rfl q hpq,
    shiftFunctorObjXIso, assoc, Iso.inv_hom_id, comp_id]

中文:
引理 rightUnshift_rightShift
  条件: (a n' : 整数) (hn' : n' + a = n)
  证明: by
  ext p q hpq
  simp only [rightUnshift_v _ n hn' p q hpq (p + n') rfl,
    γ.rightShift_v _ _ hn' p (p + n') rfl q hpq,
    shiftFunctorObjXIso, assoc, Iso.inv_hom_id, comp_id]

Depends on / 依赖: Iso.inv_hom_id, comp_id, inv_hom_id, rightShift_v, rightUnshift_v, shiftFunctorObjXIso
-/
lemma rightUnshift_rightShift (a n' : Int) (hn' : n' + a = n) :
    (γ.rightShift a n' hn').rightUnshift n hn' = γ := by
  ext p q hpq
  simp only [rightUnshift_v _ n hn' p q hpq (p + n') rfl,
    γ.rightShift_v _ _ hn' p (p + n') rfl q hpq,
    shiftFunctorObjXIso, assoc, Iso.inv_hom_id, comp_id]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `rightShift_rightUnshift` / 引理 `rightShift_rightUnshift`

English:
lemma rightShift_rightUnshift
  given: {a n' : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn' : n' + a = n)
  proof: by
  ext p q hpq
  simp only [(γ.rightUnshift n hn').rightShift_v a n' hn' p q hpq (p + n) rfl,
    γ.rightUnshift_v n hn' p (p + n) rfl q hpq,
    shiftFunctorObjXIso, assoc, Iso.hom_inv_id, comp_id]

@[simp]

中文:
引理 rightShift_rightUnshift
  条件: {a n' : 整数} (γ : Cochain K (L⟦a⟧) n') (n : 整数) (hn' : n' + a = n)
  证明: by
  ext p q hpq
  simp only [(γ.rightUnshift n hn').rightShift_v a n' hn' p q hpq (p + n) rfl,
    γ.rightUnshift_v n hn' p (p + n) rfl q hpq,
    shiftFunctorObjXIso, assoc, Iso.hom_inv_id, comp_id]

@[simp]

Depends on / 依赖: Iso.hom_inv_id, comp_id, hom_inv_id, rightShift_v, rightUnshift, rightUnshift_v, shiftFunctorObjXIso
-/
lemma rightShift_rightUnshift {a n' : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn' : n' + a = n) :
    (γ.rightUnshift n hn').rightShift a n' hn' = γ := by
  ext p q hpq
  simp only [(γ.rightUnshift n hn').rightShift_v a n' hn' p q hpq (p + n) rfl,
    γ.rightUnshift_v n hn' p (p + n) rfl q hpq,
    shiftFunctorObjXIso, assoc, Iso.hom_inv_id, comp_id]

@[simp]
/--
lemma `leftUnshift_leftShift` / 引理 `leftUnshift_leftShift`

English:
lemma leftUnshift_leftShift
  given: (a n' : Int) (hn' : n + a = n')
  proof: by
  ext p q hpq
  rw [(γ.leftShift a n' hn').leftUnshift_v n hn' p q hpq (q - n') (by lia)]; rw [γ.leftShift_v a n' hn' (q - n') q (by lia) p hpq]; rw [Linear.comp_units_smul]; rw [Iso.inv_hom_id_assoc]; rw [smul_smul]; rw [Int.units_mul_self]; rw [one_smul]

@[simp]

中文:
引理 leftUnshift_leftShift
  条件: (a n' : 整数) (hn' : n + a = n')
  证明: by
  ext p q hpq
  rw [(γ.leftShift a n' hn').leftUnshift_v n hn' p q hpq (q - n') (by lia)]; rw [γ.leftShift_v a n' hn' (q - n') q (by lia) p hpq]; rw [Linear.comp_units_smul]; rw [Iso.inv_hom_id_assoc]; rw [smul_smul]; rw [Int.units_mul_self]; rw [one_smul]

@[simp]

Depends on / 依赖: Int.units_mul_self, Iso.inv_hom_id_assoc, Linear, Linear.comp_units_smul, comp_units_smul, inv_hom_id_assoc, leftShift, leftShift_v, leftUnshift_v, one_smul, smul_smul, units_mul_self
-/
lemma leftUnshift_leftShift (a n' : Int) (hn' : n + a = n') :
    (γ.leftShift a n' hn').leftUnshift n hn' = γ := by
  ext p q hpq
  rw [(γ.leftShift a n' hn').leftUnshift_v n hn' p q hpq (q - n') (by lia)]; rw [γ.leftShift_v a n' hn' (q - n') q (by lia) p hpq]; rw [Linear.comp_units_smul]; rw [Iso.inv_hom_id_assoc]; rw [smul_smul]; rw [Int.units_mul_self]; rw [one_smul]

@[simp]
/--
lemma `leftShift_leftUnshift` / 引理 `leftShift_leftUnshift`

English:
lemma leftShift_leftUnshift
  given: {a n' : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn' : n + a = n')
  proof: by
  ext p q hpq
  rw [(γ.leftUnshift n hn').leftShift_v a n' hn' p q hpq (q - n) (by lia)]; rw [γ.leftUnshift_v n hn' (q - n) q (by lia) p hpq]; rw [Linear.comp_units_smul]; rw [smul_smul]; rw [Iso.hom_inv_id_assoc]; rw [Int.units_mul_self]; rw [one_smul]

中文:
引理 leftShift_leftUnshift
  条件: {a n' : 整数} (γ : Cochain (K⟦a⟧) L n') (n : 整数) (hn' : n + a = n')
  证明: by
  ext p q hpq
  rw [(γ.leftUnshift n hn').leftShift_v a n' hn' p q hpq (q - n) (by lia)]; rw [γ.leftUnshift_v n hn' (q - n) q (by lia) p hpq]; rw [Linear.comp_units_smul]; rw [smul_smul]; rw [Iso.hom_inv_id_assoc]; rw [Int.units_mul_self]; rw [one_smul]

Depends on / 依赖: Int.units_mul_self, Iso.hom_inv_id_assoc, Linear, Linear.comp_units_smul, comp_units_smul, hom_inv_id_assoc, leftShift_v, leftUnshift, leftUnshift_v, one_smul, smul_smul, units_mul_self
-/
lemma leftShift_leftUnshift {a n' : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn' : n + a = n') :
    (γ.leftUnshift n hn').leftShift a n' hn' = γ := by
  ext p q hpq
  rw [(γ.leftUnshift n hn').leftShift_v a n' hn' p q hpq (q - n) (by lia)]; rw [γ.leftUnshift_v n hn' (q - n) q (by lia) p hpq]; rw [Linear.comp_units_smul]; rw [smul_smul]; rw [Iso.hom_inv_id_assoc]; rw [Int.units_mul_self]; rw [one_smul]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `rightShift_add` / 引理 `rightShift_add`

English:
lemma rightShift_add
  given: (a n' : Int) (hn' : n' + a = n)
  proof: by
  ext p q hpq
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, add_v, add_comp]

中文:
引理 rightShift_add
  条件: (a n' : 整数) (hn' : n' + a = n)
  证明: by
  ext p q hpq
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, add_v, add_comp]

Depends on / 依赖: add_comp, add_v, rightShift_v
-/
lemma rightShift_add (a n' : Int) (hn' : n' + a = n) :
    (γ₁ + γ₂).rightShift a n' hn' = γ₁.rightShift a n' hn' + γ₂.rightShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, add_v, add_comp]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `leftShift_add` / 引理 `leftShift_add`

English:
lemma leftShift_add
  given: (a n' : Int) (hn' : n + a = n')
  proof: by
  ext p q hpq
  dsimp
  simp only [leftShift_v _ a n' hn' p q hpq (p + a) (by lia), add_v, comp_add, smul_add]

中文:
引理 leftShift_add
  条件: (a n' : 整数) (hn' : n + a = n')
  证明: by
  ext p q hpq
  dsimp
  simp only [leftShift_v _ a n' hn' p q hpq (p + a) (by lia), add_v, comp_add, smul_add]

Depends on / 依赖: add_v, comp_add, leftShift_v, smul_add
-/
lemma leftShift_add (a n' : Int) (hn' : n + a = n') :
    (γ₁ + γ₂).leftShift a n' hn' = γ₁.leftShift a n' hn' + γ₂.leftShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [leftShift_v _ a n' hn' p q hpq (p + a) (by lia), add_v, comp_add, smul_add]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `shift_add` / 引理 `shift_add`

English:
lemma shift_add
  given: (a : Int)
  proof: by
  ext p q hpq
  dsimp
  simp only [shift_v', add_v]

中文:
引理 shift_add
  条件: (a : 整数)
  证明: by
  ext p q hpq
  dsimp
  simp only [shift_v', add_v]

Depends on / 依赖: add_v, shift_v
-/
lemma shift_add (a : Int) :
    (γ₁ + γ₂).shift a = γ₁.shift a + γ₂.shift a := by
  ext p q hpq
  dsimp
  simp only [shift_v', add_v]

variable (K L)

/-- The additive equivalence `Cochain K L n ≃+ Cochain K L⟦a⟧ n'` when `n' + a = n`. -/
@[simps]
/--
Definition of `rightShiftAddEquiv` / `rightShiftAddEquiv` 的定义

English:
definition rightShiftAddEquiv
  signature: (n a n' : Int) (hn' : n' + a = n)
  body: γ.rightShift a n' hn'
  invFun γ := γ.rightUnshift n hn'
  left_inv γ := by simp only [rightUnshift_rightShift]
  right_inv γ := by simp only [rightShift_rightUnshift]
  map_add' γ γ' := by simp only [rightShift_add]

中文:
定义 rightShiftAddEquiv
  签名: (n a n' : 整数) (hn' : n' + a = n)
  定义体: γ.rightShift a n' hn'
  invFun γ := γ.rightUnshift n hn'
  left_inv γ := by simp only [rightUnshift_rightShift]
  right_inv γ := by simp only [rightShift_rightUnshift]
  map_add' γ γ' := by simp only [rightShift_add]

Depends on / 依赖: rightShift
-/
def rightShiftAddEquiv (n a n' : Int) (hn' : n' + a = n) :
    Cochain K L n ≃+ Cochain K (L⟦a⟧) n' where
  toFun γ := γ.rightShift a n' hn'
  invFun γ := γ.rightUnshift n hn'
  left_inv γ := by simp only [rightUnshift_rightShift]
  right_inv γ := by simp only [rightShift_rightUnshift]
  map_add' γ γ' := by simp only [rightShift_add]

/-- The additive equivalence `Cochain K L n ≃+ Cochain (K⟦a⟧) L n'` when `n + a = n'`. -/
@[simps]
/--
Definition of `leftShiftAddEquiv` / `leftShiftAddEquiv` 的定义

English:
definition leftShiftAddEquiv
  signature: (n a n' : Int) (hn' : n + a = n')
  body: γ.leftShift a n' hn'
  invFun γ := γ.leftUnshift n hn'
  left_inv γ := by simp only [leftUnshift_leftShift]
  right_inv γ := by simp only [leftShift_leftUnshift]
  map_add' γ γ' := by simp only [leftShift_add]

中文:
定义 leftShiftAddEquiv
  签名: (n a n' : 整数) (hn' : n + a = n')
  定义体: γ.leftShift a n' hn'
  invFun γ := γ.leftUnshift n hn'
  left_inv γ := by simp only [leftUnshift_leftShift]
  right_inv γ := by simp only [leftShift_leftUnshift]
  map_add' γ γ' := by simp only [leftShift_add]

Depends on / 依赖: leftShift
-/
def leftShiftAddEquiv (n a n' : Int) (hn' : n + a = n') :
    Cochain K L n ≃+ Cochain (K⟦a⟧) L n' where
  toFun γ := γ.leftShift a n' hn'
  invFun γ := γ.leftUnshift n hn'
  left_inv γ := by simp only [leftUnshift_leftShift]
  right_inv γ := by simp only [leftShift_leftUnshift]
  map_add' γ γ' := by simp only [leftShift_add]

/-- The additive map `Cochain K L n →+ Cochain (K⟦a⟧) (L⟦a⟧) n`. -/
@[simps!]
/--
Definition of `shiftAddHom` / `shiftAddHom` 的定义

English:
definition shiftAddHom
  signature: (n a : Int)
  body: AddMonoidHom.mk' (fun γ => γ.shift a) (by intros; simp only [shift_add])

中文:
定义 shiftAddHom
  签名: (n a : 整数)
  定义体: AddMonoidHom.mk' (fun γ => γ.shift a) (by intros; simp only [shift_add])

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, intros, shift_add
-/
def shiftAddHom (n a : Int) : Cochain K L n ->+ Cochain (K⟦a⟧) (L⟦a⟧) n :=
  AddMonoidHom.mk' (fun γ => γ.shift a) (by intros; simp only [shift_add])

variable (n)

@[simp]
/--
lemma `rightShift_zero` / 引理 `rightShift_zero`

English:
lemma rightShift_zero
  given: (a n' : Int) (hn' : n' + a = n)
  proof: by
  change rightShiftAddEquiv K L n a n' hn' 0 = 0
  apply map_zero

@[simp]

中文:
引理 rightShift_zero
  条件: (a n' : 整数) (hn' : n' + a = n)
  证明: by
  change rightShiftAddEquiv K L n a n' hn' 0 = 0
  apply map_zero

@[simp]

Depends on / 依赖: map_zero, rightShiftAddEquiv
-/
lemma rightShift_zero (a n' : Int) (hn' : n' + a = n) :
    (0 : Cochain K L n).rightShift a n' hn' = 0 := by
  change rightShiftAddEquiv K L n a n' hn' 0 = 0
  apply map_zero

@[simp]
/--
lemma `rightUnshift_zero` / 引理 `rightUnshift_zero`

English:
lemma rightUnshift_zero
  given: (a n' : Int) (hn' : n' + a = n)
  proof: by
  change (rightShiftAddEquiv K L n a n' hn').symm 0 = 0
  apply map_zero

@[simp]

中文:
引理 rightUnshift_zero
  条件: (a n' : 整数) (hn' : n' + a = n)
  证明: by
  change (rightShiftAddEquiv K L n a n' hn').symm 0 = 0
  apply map_zero

@[simp]

Depends on / 依赖: map_zero, rightShiftAddEquiv
-/
lemma rightUnshift_zero (a n' : Int) (hn' : n' + a = n) :
    (0 : Cochain K (L⟦a⟧) n').rightUnshift n hn' = 0 := by
  change (rightShiftAddEquiv K L n a n' hn').symm 0 = 0
  apply map_zero

@[simp]
/--
lemma `leftShift_zero` / 引理 `leftShift_zero`

English:
lemma leftShift_zero
  given: (a n' : Int) (hn' : n + a = n')
  proof: by
  change leftShiftAddEquiv K L n a n' hn' 0 = 0
  apply map_zero

@[simp]

中文:
引理 leftShift_zero
  条件: (a n' : 整数) (hn' : n + a = n')
  证明: by
  change leftShiftAddEquiv K L n a n' hn' 0 = 0
  apply map_zero

@[simp]

Depends on / 依赖: leftShiftAddEquiv, map_zero
-/
lemma leftShift_zero (a n' : Int) (hn' : n + a = n') :
    (0 : Cochain K L n).leftShift a n' hn' = 0 := by
  change leftShiftAddEquiv K L n a n' hn' 0 = 0
  apply map_zero

@[simp]
/--
lemma `leftUnshift_zero` / 引理 `leftUnshift_zero`

English:
lemma leftUnshift_zero
  given: (a n' : Int) (hn' : n + a = n')
  proof: by
  change (leftShiftAddEquiv K L n a n' hn').symm 0 = 0
  apply map_zero

@[simp]

中文:
引理 leftUnshift_zero
  条件: (a n' : 整数) (hn' : n + a = n')
  证明: by
  change (leftShiftAddEquiv K L n a n' hn').symm 0 = 0
  apply map_zero

@[simp]

Depends on / 依赖: leftShiftAddEquiv, map_zero
-/
lemma leftUnshift_zero (a n' : Int) (hn' : n + a = n') :
    (0 : Cochain (K⟦a⟧) L n').leftUnshift n hn' = 0 := by
  change (leftShiftAddEquiv K L n a n' hn').symm 0 = 0
  apply map_zero

@[simp]
/--
lemma `shift_zero` / 引理 `shift_zero`

English:
lemma shift_zero
  given: (a : Int)
  proof: by
  change shiftAddHom K L n a 0 = 0
  apply map_zero

中文:
引理 shift_zero
  条件: (a : 整数)
  证明: by
  change shiftAddHom K L n a 0 = 0
  apply map_zero

Depends on / 依赖: map_zero, shiftAddHom
-/
lemma shift_zero (a : Int) :
    (0 : Cochain K L n).shift a = 0 := by
  change shiftAddHom K L n a 0 = 0
  apply map_zero

variable {K L n}

@[simp]
/--
lemma `rightShift_neg` / 引理 `rightShift_neg`

English:
lemma rightShift_neg
  given: (a n' : Int) (hn' : n' + a = n)
  proof: by
  change rightShiftAddEquiv K L n a n' hn' (-γ) = _
  apply map_neg

@[simp]

中文:
引理 rightShift_neg
  条件: (a n' : 整数) (hn' : n' + a = n)
  证明: by
  change rightShiftAddEquiv K L n a n' hn' (-γ) = _
  apply map_neg

@[simp]

Depends on / 依赖: map_neg, rightShiftAddEquiv
-/
lemma rightShift_neg (a n' : Int) (hn' : n' + a = n) :
    (-γ).rightShift a n' hn' = -γ.rightShift a n' hn' := by
  change rightShiftAddEquiv K L n a n' hn' (-γ) = _
  apply map_neg

@[simp]
/--
lemma `rightUnshift_neg` / 引理 `rightUnshift_neg`

English:
lemma rightUnshift_neg
  given: {n' a : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n)
  proof: by
  change (rightShiftAddEquiv K L n a n' hn).symm (-γ) = _
  apply map_neg

@[simp]

中文:
引理 rightUnshift_neg
  条件: {n' a : 整数} (γ : Cochain K (L⟦a⟧) n') (n : 整数) (hn : n' + a = n)
  证明: by
  change (rightShiftAddEquiv K L n a n' hn).symm (-γ) = _
  apply map_neg

@[simp]

Depends on / 依赖: map_neg, rightShiftAddEquiv
-/
lemma rightUnshift_neg {n' a : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n) :
    (-γ).rightUnshift n hn = -γ.rightUnshift n hn := by
  change (rightShiftAddEquiv K L n a n' hn).symm (-γ) = _
  apply map_neg

@[simp]
/--
lemma `leftShift_neg` / 引理 `leftShift_neg`

English:
lemma leftShift_neg
  given: (a n' : Int) (hn' : n + a = n')
  proof: by
  change leftShiftAddEquiv K L n a n' hn' (-γ) = _
  apply map_neg

@[simp]

中文:
引理 leftShift_neg
  条件: (a n' : 整数) (hn' : n + a = n')
  证明: by
  change leftShiftAddEquiv K L n a n' hn' (-γ) = _
  apply map_neg

@[simp]

Depends on / 依赖: leftShiftAddEquiv, map_neg
-/
lemma leftShift_neg (a n' : Int) (hn' : n + a = n') :
    (-γ).leftShift a n' hn' = -γ.leftShift a n' hn' := by
  change leftShiftAddEquiv K L n a n' hn' (-γ) = _
  apply map_neg

@[simp]
/--
lemma `leftUnshift_neg` / 引理 `leftUnshift_neg`

English:
lemma leftUnshift_neg
  given: {n' a : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a = n')
  proof: by
  change (leftShiftAddEquiv K L n a n' hn).symm (-γ) = _
  apply map_neg

@[simp]

中文:
引理 leftUnshift_neg
  条件: {n' a : 整数} (γ : Cochain (K⟦a⟧) L n') (n : 整数) (hn : n + a = n')
  证明: by
  change (leftShiftAddEquiv K L n a n' hn).symm (-γ) = _
  apply map_neg

@[simp]

Depends on / 依赖: leftShiftAddEquiv, map_neg
-/
lemma leftUnshift_neg {n' a : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a = n') :
    (-γ).leftUnshift n hn = -γ.leftUnshift n hn := by
  change (leftShiftAddEquiv K L n a n' hn).symm (-γ) = _
  apply map_neg

@[simp]
/--
lemma `shift_neg` / 引理 `shift_neg`

English:
lemma shift_neg
  given: (a : Int)
  proof: by
  change shiftAddHom K L n a (-γ) = _
  apply map_neg

@[simp]

中文:
引理 shift_neg
  条件: (a : 整数)
  证明: by
  change shiftAddHom K L n a (-γ) = _
  apply map_neg

@[simp]

Depends on / 依赖: map_neg, shiftAddHom
-/
lemma shift_neg (a : Int) :
    (-γ).shift a = -γ.shift a := by
  change shiftAddHom K L n a (-γ) = _
  apply map_neg

@[simp]
/--
lemma `rightUnshift_add` / 引理 `rightUnshift_add`

English:
lemma rightUnshift_add
  given: {n' a : Int} (γ₁ γ₂ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n)
  proof: by
  change (rightShiftAddEquiv K L n a n' hn).symm (γ₁ + γ₂) = _
  apply map_add

@[simp]

中文:
引理 rightUnshift_add
  条件: {n' a : 整数} (γ₁ γ₂ : Cochain K (L⟦a⟧) n') (n : 整数) (hn : n' + a = n)
  证明: by
  change (rightShiftAddEquiv K L n a n' hn).symm (γ₁ + γ₂) = _
  apply map_add

@[simp]

Depends on / 依赖: map_add, rightShiftAddEquiv
-/
lemma rightUnshift_add {n' a : Int} (γ₁ γ₂ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n) :
    (γ₁ + γ₂).rightUnshift n hn = γ₁.rightUnshift n hn + γ₂.rightUnshift n hn := by
  change (rightShiftAddEquiv K L n a n' hn).symm (γ₁ + γ₂) = _
  apply map_add

@[simp]
/--
lemma `leftUnshift_add` / 引理 `leftUnshift_add`

English:
lemma leftUnshift_add
  given: {n' a : Int} (γ₁ γ₂ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a = n')
  proof: by
  change (leftShiftAddEquiv K L n a n' hn).symm (γ₁ + γ₂) = _
  apply map_add

中文:
引理 leftUnshift_add
  条件: {n' a : 整数} (γ₁ γ₂ : Cochain (K⟦a⟧) L n') (n : 整数) (hn : n + a = n')
  证明: by
  change (leftShiftAddEquiv K L n a n' hn).symm (γ₁ + γ₂) = _
  apply map_add

Depends on / 依赖: leftShiftAddEquiv, map_add
-/
lemma leftUnshift_add {n' a : Int} (γ₁ γ₂ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a = n') :
    (γ₁ + γ₂).leftUnshift n hn = γ₁.leftUnshift n hn + γ₂.leftUnshift n hn := by
  change (leftShiftAddEquiv K L n a n' hn).symm (γ₁ + γ₂) = _
  apply map_add

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `rightShift_smul` / 引理 `rightShift_smul`

English:
lemma rightShift_smul
  given: (a n' : Int) (hn' : n' + a = n) (x : R)
  proof: by
  ext p q hpq
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, smul_v, Linear.smul_comp]

中文:
引理 rightShift_smul
  条件: (a n' : 整数) (hn' : n' + a = n) (x : R)
  证明: by
  ext p q hpq
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, smul_v, Linear.smul_comp]

Depends on / 依赖: Linear, Linear.smul_comp, rightShift_v, smul_comp, smul_v
-/
lemma rightShift_smul (a n' : Int) (hn' : n' + a = n) (x : R) :
    (x • γ).rightShift a n' hn' = x • γ.rightShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, smul_v, Linear.smul_comp]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `leftShift_smul` / 引理 `leftShift_smul`

English:
lemma leftShift_smul
  given: (a n' : Int) (hn' : n + a = n') (x : R)
  proof: by
  ext p q hpq
  dsimp
  simp only [leftShift_v _ a n' hn' p q hpq (p + a) (by lia), smul_v, Linear.comp_smul,
    smul_comm x]

中文:
引理 leftShift_smul
  条件: (a n' : 整数) (hn' : n + a = n') (x : R)
  证明: by
  ext p q hpq
  dsimp
  simp only [leftShift_v _ a n' hn' p q hpq (p + a) (by lia), smul_v, Linear.comp_smul,
    smul_comm x]

Depends on / 依赖: Linear, Linear.comp_smul, comp_smul, leftShift_v, smul_comm, smul_v
-/
lemma leftShift_smul (a n' : Int) (hn' : n + a = n') (x : R) :
    (x • γ).leftShift a n' hn' = x • γ.leftShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [leftShift_v _ a n' hn' p q hpq (p + a) (by lia), smul_v, Linear.comp_smul,
    smul_comm x]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `shift_smul` / 引理 `shift_smul`

English:
lemma shift_smul
  given: (a : Int) (x : R)
  proof: by
  ext p q hpq
  dsimp
  simp only [shift_v', smul_v]

中文:
引理 shift_smul
  条件: (a : 整数) (x : R)
  证明: by
  ext p q hpq
  dsimp
  simp only [shift_v', smul_v]

Depends on / 依赖: shift_v, smul_v
-/
lemma shift_smul (a : Int) (x : R) :
    (x • γ).shift a = x • (γ.shift a) := by
  ext p q hpq
  dsimp
  simp only [shift_v', smul_v]

variable (K L R)

set_option backward.defeqAttrib.useBackward true in
/-- The linear equivalence `Cochain K L n ≃+ Cochain K L⟦a⟧ n'` when `n' + a = n` and
the category is `R`-linear. -/
@[simps!]
/--
Definition of `rightShiftLinearEquiv` / `rightShiftLinearEquiv` 的定义

English:
definition rightShiftLinearEquiv
  signature: (n a n' : Int) (hn' : n' + a = n)
  body: (rightShiftAddEquiv K L n a n' hn').toLinearEquiv
    (fun x γ => by dsimp; simp only [rightShift_smul])

中文:
定义 rightShiftLinearEquiv
  签名: (n a n' : 整数) (hn' : n' + a = n)
  定义体: (rightShiftAddEquiv K L n a n' hn').toLinearEquiv
    (fun x γ => by dsimp; simp only [rightShift_smul])

Depends on / 依赖: rightShiftAddEquiv, rightShift_smul, toLinearEquiv
-/
def rightShiftLinearEquiv (n a n' : Int) (hn' : n' + a = n) :
    Cochain K L n ≃ₗ[R] Cochain K (L⟦a⟧) n' :=
  (rightShiftAddEquiv K L n a n' hn').toLinearEquiv
    (fun x γ => by dsimp; simp only [rightShift_smul])

set_option backward.defeqAttrib.useBackward true in
/-- The additive equivalence `Cochain K L n ≃+ Cochain (K⟦a⟧) L n'` when `n + a = n'` and
the category is `R`-linear. -/
@[simps!]
/--
Definition of `leftShiftLinearEquiv` / `leftShiftLinearEquiv` 的定义

English:
definition leftShiftLinearEquiv
  signature: (n a n' : Int) (hn : n + a = n')
  body: (leftShiftAddEquiv K L n a n' hn).toLinearEquiv
    (fun x γ => by dsimp; simp only [leftShift_smul])

中文:
定义 leftShiftLinearEquiv
  签名: (n a n' : 整数) (hn : n + a = n')
  定义体: (leftShiftAddEquiv K L n a n' hn).toLinearEquiv
    (fun x γ => by dsimp; simp only [leftShift_smul])

Depends on / 依赖: leftShiftAddEquiv, leftShift_smul, toLinearEquiv
-/
def leftShiftLinearEquiv (n a n' : Int) (hn : n + a = n') :
    Cochain K L n ≃ₗ[R] Cochain (K⟦a⟧) L n' :=
  (leftShiftAddEquiv K L n a n' hn).toLinearEquiv
    (fun x γ => by dsimp; simp only [leftShift_smul])

set_option backward.defeqAttrib.useBackward true in
/-- The linear map `Cochain K L n ≃+ Cochain (K⟦a⟧) (L⟦a⟧) n` when the category is `R`-linear. -/
@[simps!]
/--
Definition of `shiftLinearMap` / `shiftLinearMap` 的定义

English:
definition shiftLinearMap
  signature: (n a : Int)
  body: shiftAddHom K L n a
  map_smul' _ _ := by dsimp; simp only [shift_smul]

中文:
定义 shiftLinearMap
  签名: (n a : 整数)
  定义体: shiftAddHom K L n a
  map_smul' _ _ := by dsimp; simp only [shift_smul]

Depends on / 依赖: shiftAddHom
-/
def shiftLinearMap (n a : Int) :
    Cochain K L n ->ₗ[R] Cochain (K⟦a⟧) (L⟦a⟧) n where
  toAddHom := shiftAddHom K L n a
  map_smul' _ _ := by dsimp; simp only [shift_smul]

variable {K L R}

@[simp]
/--
lemma `rightShift_units_smul` / 引理 `rightShift_units_smul`

English:
lemma rightShift_units_smul
  given: (a n' : Int) (hn' : n' + a = n) (x : Rˣ)
  proof: by
  apply rightShift_smul

@[simp]

中文:
引理 rightShift_units_smul
  条件: (a n' : 整数) (hn' : n' + a = n) (x : Rˣ)
  证明: by
  apply rightShift_smul

@[simp]

Depends on / 依赖: rightShift_smul
-/
lemma rightShift_units_smul (a n' : Int) (hn' : n' + a = n) (x : Rˣ) :
    (x • γ).rightShift a n' hn' = x • γ.rightShift a n' hn' := by
  apply rightShift_smul

@[simp]
/--
lemma `leftShift_units_smul` / 引理 `leftShift_units_smul`

English:
lemma leftShift_units_smul
  given: (a n' : Int) (hn' : n + a = n') (x : Rˣ)
  proof: by
  apply leftShift_smul

中文:
引理 leftShift_units_smul
  条件: (a n' : 整数) (hn' : n + a = n') (x : Rˣ)
  证明: by
  apply leftShift_smul

Depends on / 依赖: leftShift_smul
-/
lemma leftShift_units_smul (a n' : Int) (hn' : n + a = n') (x : Rˣ) :
    (x • γ).leftShift a n' hn' = x • γ.leftShift a n' hn' := by
  apply leftShift_smul

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `shift_units_smul` / 引理 `shift_units_smul`

English:
lemma shift_units_smul
  given: (a : Int) (x : Rˣ)
  proof: by
  ext p q hpq
  dsimp
  simp only [shift_v', units_smul_v]

@[simp]

中文:
引理 shift_units_smul
  条件: (a : 整数) (x : Rˣ)
  证明: by
  ext p q hpq
  dsimp
  simp only [shift_v', units_smul_v]

@[simp]

Depends on / 依赖: shift_v, units_smul_v
-/
lemma shift_units_smul (a : Int) (x : Rˣ) :
    (x • γ).shift a = x • (γ.shift a) := by
  ext p q hpq
  dsimp
  simp only [shift_v', units_smul_v]

@[simp]
/--
lemma `rightUnshift_smul` / 引理 `rightUnshift_smul`

English:
lemma rightUnshift_smul
  given: {n' a : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n) (x : R)
  proof: by
  change (rightShiftLinearEquiv R K L n a n' hn).symm (x • γ) = _
  apply map_smul

@[simp]

中文:
引理 rightUnshift_smul
  条件: {n' a : 整数} (γ : Cochain K (L⟦a⟧) n') (n : 整数) (hn : n' + a = n) (x : R)
  证明: by
  change (rightShiftLinearEquiv R K L n a n' hn).symm (x • γ) = _
  apply map_smul

@[simp]

Depends on / 依赖: map_smul, rightShiftLinearEquiv
-/
lemma rightUnshift_smul {n' a : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n) (x : R) :
    (x • γ).rightUnshift n hn = x • γ.rightUnshift n hn := by
  change (rightShiftLinearEquiv R K L n a n' hn).symm (x • γ) = _
  apply map_smul

@[simp]
/--
lemma `rightUnshift_units_smul` / 引理 `rightUnshift_units_smul`

English:
lemma rightUnshift_units_smul
  statement: {n' a : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int)
  proof: by
  apply rightUnshift_smul

@[simp]

中文:
引理 rightUnshift_units_smul
  结论: {n' a : 整数} (γ : Cochain K (L⟦a⟧) n') (n : 整数)
  证明: by
  apply rightUnshift_smul

@[simp]

Depends on / 依赖: rightUnshift_smul
-/
lemma rightUnshift_units_smul {n' a : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int)
    (hn : n' + a = n) (x : Rˣ) :
    (x • γ).rightUnshift n hn = x • γ.rightUnshift n hn := by
  apply rightUnshift_smul

@[simp]
/--
lemma `leftUnshift_smul` / 引理 `leftUnshift_smul`

English:
lemma leftUnshift_smul
  given: {n' a : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a = n') (x : R)
  proof: by
  change (leftShiftLinearEquiv R K L n a n' hn).symm (x • γ) = _
  apply map_smul

@[simp]

中文:
引理 leftUnshift_smul
  条件: {n' a : 整数} (γ : Cochain (K⟦a⟧) L n') (n : 整数) (hn : n + a = n') (x : R)
  证明: by
  change (leftShiftLinearEquiv R K L n a n' hn).symm (x • γ) = _
  apply map_smul

@[simp]

Depends on / 依赖: leftShiftLinearEquiv, map_smul
-/
lemma leftUnshift_smul {n' a : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a = n') (x : R) :
    (x • γ).leftUnshift n hn = x • γ.leftUnshift n hn := by
  change (leftShiftLinearEquiv R K L n a n' hn).symm (x • γ) = _
  apply map_smul

@[simp]
/--
lemma `leftUnshift_units_smul` / 引理 `leftUnshift_units_smul`

English:
lemma leftUnshift_units_smul
  statement: {n' a : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int)
  proof: by
  apply leftUnshift_smul

中文:
引理 leftUnshift_units_smul
  结论: {n' a : 整数} (γ : Cochain (K⟦a⟧) L n') (n : 整数)
  证明: by
  apply leftUnshift_smul

Depends on / 依赖: leftUnshift_smul
-/
lemma leftUnshift_units_smul {n' a : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int)
    (hn : n + a = n') (x : Rˣ) :
    (x • γ).leftUnshift n hn = x • γ.leftUnshift n hn := by
  apply leftUnshift_smul

/--
lemma `rightUnshift_comp` / 引理 `rightUnshift_comp`

English:
lemma rightUnshift_comp
  statement: {m : Int} {a : Int} (γ' : Cochain L (M⟦a⟧) m) {nm : Int} (hnm : n + m = nm)
  proof: by
  ext p q hpq
  rw [(γ.comp γ' hnm).rightUnshift_v nm' hnm' p q hpq (p + n + m) (by lia)]; rw [γ.comp_v γ' hnm p (p + n) (p + n + m) rfl rfl]; rw [comp_v _ _ (show n + m' = nm' by lia) p (p + n) q (by lia) (by lia)]; rw [γ'.rightUnshift_v m' hm' (p + n) q (by lia) (p + n + m) rfl]; rw [assoc]

中文:
引理 rightUnshift_comp
  结论: {m : 整数} {a : 整数} (γ' : Cochain L (M⟦a⟧) m) {nm : 整数} (hnm : n + m = nm)
  证明: by
  ext p q hpq
  rw [(γ.comp γ' hnm).rightUnshift_v nm' hnm' p q hpq (p + n + m) (by lia)]; rw [γ.comp_v γ' hnm p (p + n) (p + n + m) rfl rfl]; rw [comp_v _ _ (show n + m' = nm' by lia) p (p + n) q (by lia) (by lia)]; rw [γ'.rightUnshift_v m' hm' (p + n) q (by lia) (p + n + m) rfl]; rw [assoc]

Depends on / 依赖: comp_v, rightUnshift_v
-/
lemma rightUnshift_comp {m : Int} {a : Int} (γ' : Cochain L (M⟦a⟧) m) {nm : Int} (hnm : n + m = nm)
    (nm' : Int) (hnm' : nm + a = nm') (m' : Int) (hm' : m + a = m') :
    (γ.comp γ' hnm).rightUnshift nm' hnm' =
      γ.comp (γ'.rightUnshift m' hm') (by lia) := by
  ext p q hpq
  rw [(γ.comp γ' hnm).rightUnshift_v nm' hnm' p q hpq (p + n + m) (by lia)]; rw [γ.comp_v γ' hnm p (p + n) (p + n + m) rfl rfl]; rw [comp_v _ _ (show n + m' = nm' by lia) p (p + n) q (by lia) (by lia)]; rw [γ'.rightUnshift_v m' hm' (p + n) q (by lia) (p + n + m) rfl]; rw [assoc]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `leftShift_comp` / 引理 `leftShift_comp`

English:
lemma leftShift_comp
  statement: (a n' : Int) (hn' : n + a = n') {m t t' : Int} (γ' : Cochain L M m)
  proof: by
  ext p q hpq
  have h' : n' + m = t' := by lia
  dsimp
  simp only [Cochain.comp_v _ _ h' p (p + n') q rfl (by lia),
    γ.leftShift_v a n' hn' p (p + n') rfl (p + a) (by lia),
    (γ.comp γ' h).leftShift_v a t' (by lia) p q hpq (p + a) (by lia),
    smul_smul, Linear.units_smul_comp, assoc, Int

中文:
引理 leftShift_comp
  结论: (a n' : 整数) (hn' : n + a = n') {m t t' : 整数} (γ' : Cochain L M m)
  证明: by
  ext p q hpq
  have h' : n' + m = t' := by lia
  dsimp
  simp only [Cochain.comp_v _ _ h' p (p + n') q rfl (by lia),
    γ.leftShift_v a n' hn' p (p + n') rfl (p + a) (by lia),
    (γ.comp γ' h).leftShift_v a t' (by lia) p q hpq (p + a) (by lia),
    smul_smul, Linear.units_smul_comp, assoc, Int

Depends on / 依赖: Cochain, Cochain.comp_v, Int.negOnePow_add, Linear, Linear.units_smul_comp, add_comm, comp_v, leftShift_v, mul_add, mul_assoc, negOnePow_add, smul_smul, units_smul_comp
-/
lemma leftShift_comp (a n' : Int) (hn' : n + a = n') {m t t' : Int} (γ' : Cochain L M m)
    (h : n + m = t) (ht' : t + a = t') :
    (γ.comp γ' h).leftShift a t' ht' = (a * m).negOnePow • (γ.leftShift a n' hn').comp γ'
      (by rw [← ht', ← h, ← hn', add_assoc, add_comm a, add_assoc]) := by
  ext p q hpq
  have h' : n' + m = t' := by lia
  dsimp
  simp only [Cochain.comp_v _ _ h' p (p + n') q rfl (by lia),
    γ.leftShift_v a n' hn' p (p + n') rfl (p + a) (by lia),
    (γ.comp γ' h).leftShift_v a t' (by lia) p q hpq (p + a) (by lia),
    smul_smul, Linear.units_smul_comp, assoc, Int.negOnePow_add, ← mul_assoc, ← h',
    comp_v _ _ h (p + a) (p + n') q (by lia) (by lia)]
  congr 2
  rw [add_comm n']; rw [mul_add]; rw [Int.negOnePow_add]

@[simp]
/--
lemma `leftShift_comp_zero_cochain` / 引理 `leftShift_comp_zero_cochain`

English:
lemma leftShift_comp_zero_cochain
  given: (a n' : Int) (hn' : n + a = n') (γ' : Cochain L M 0)
  proof: by
  rw [leftShift_comp γ a n' hn' γ' (add_zero _) hn']; rw [mul_zero]; rw [Int.negOnePow_zero]; rw [one_smul]

中文:
引理 leftShift_comp_zero_cochain
  条件: (a n' : 整数) (hn' : n + a = n') (γ' : Cochain L M 0)
  证明: by
  rw [leftShift_comp γ a n' hn' γ' (add_zero _) hn']; rw [mul_zero]; rw [Int.negOnePow_zero]; rw [one_smul]

Depends on / 依赖: Int.negOnePow_zero, add_zero, leftShift_comp, mul_zero, negOnePow_zero, one_smul
-/
lemma leftShift_comp_zero_cochain (a n' : Int) (hn' : n + a = n') (γ' : Cochain L M 0) :
    (γ.comp γ' (add_zero n)).leftShift a n' hn' =
      (γ.leftShift a n' hn').comp γ' (add_zero n') := by
  rw [leftShift_comp γ a n' hn' γ' (add_zero _) hn']; rw [mul_zero]; rw [Int.negOnePow_zero]; rw [one_smul]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ_rightShift` / 引理 `δ_rightShift`

English:
lemma δ_rightShift
  given: (a n' m' : Int) (hn' : n' + a = n) (m : Int) (hm' : m' + a = m)
  proof: by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by lia
    ext p q hpq
    dsimp
    rw [(δ n m γ).rightShift_v a m' hm' p q hpq _ rfl]; rw [δ_v n m hnm _ p (p + m) rfl (p + n) (p + 1) (by lia) rfl]; rw [δ_v n' m' hnm' _ p q hpq (p + n') (p + 1) (by lia) rfl]; rw [γ.rightShift_v a n' hn

中文:
引理 δ_rightShift
  条件: (a n' m' : 整数) (hn' : n' + a = n) (m : 整数) (hm' : m' + a = m)
  证明: by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by lia
    ext p q hpq
    dsimp
    rw [(δ n m γ).rightShift_v a m' hm' p q hpq _ rfl]; rw [δ_v n m hnm _ p (p + m) rfl (p + n) (p + 1) (by lia) rfl]; rw [δ_v n' m' hnm' _ p q hpq (p + n') (p + 1) (by lia) rfl]; rw [γ.rightShift_v a n' hn

Depends on / 依赖: HomologicalComplex, HomologicalComplex.XIsoOfEq_inv_comp_d, Linear, Linear.comp_units_smul, XIsoOfEq_inv_comp_d, comp_units_smul, rightShift_v, shiftFunctorObjXIso, shiftFunctor_obj_d
-/
lemma δ_rightShift (a n' m' : Int) (hn' : n' + a = n) (m : Int) (hm' : m' + a = m) :
    δ n' m' (γ.rightShift a n' hn') = a.negOnePow • (δ n m γ).rightShift a m' hm' := by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by lia
    ext p q hpq
    dsimp
    rw [(δ n m γ).rightShift_v a m' hm' p q hpq _ rfl]; rw [δ_v n m hnm _ p (p + m) rfl (p + n) (p + 1) (by lia) rfl]; rw [δ_v n' m' hnm' _ p q hpq (p + n') (p + 1) (by lia) rfl]; rw [γ.rightShift_v a n' hn' p (p + n') rfl (p + n) rfl]; rw [γ.rightShift_v a n' hn' (p + 1) q _ (p + m) (by lia)]
    simp only [shiftFunctorObjXIso, shiftFunctor_obj_d',
      Linear.comp_units_smul, assoc, HomologicalComplex.XIsoOfEq_inv_comp_d,
      add_comp, HomologicalComplex.d_comp_XIsoOfEq_inv, Linear.units_smul_comp, smul_add,
      add_right_inj, smul_smul]
    simp only [← hm', add_comm m', Int.negOnePow_add, ← mul_assoc,
      Int.units_mul_self, one_mul]
  · have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by lia)
    rw [δ_shape _ _ hnm']; rw [δ_shape _ _ hnm]; rw [rightShift_zero]; rw [smul_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ_rightUnshift` / 引理 `δ_rightUnshift`

English:
lemma δ_rightUnshift
  statement: {a n' : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n)
  proof: by
  obtain ⟨γ', rfl⟩ := (rightShiftAddEquiv K L n a n' hn).surjective γ
  dsimp
  simp only [rightUnshift_rightShift, γ'.δ_rightShift a n' m' hn m hm', rightUnshift_units_smul,
    smul_smul, Int.units_mul_self, one_smul]

中文:
引理 δ_rightUnshift
  结论: {a n' : 整数} (γ : Cochain K (L⟦a⟧) n') (n : 整数) (hn : n' + a = n)
  证明: by
  obtain ⟨γ', rfl⟩ := (rightShiftAddEquiv K L n a n' hn).surjective γ
  dsimp
  simp only [rightUnshift_rightShift, γ'.δ_rightShift a n' m' hn m hm', rightUnshift_units_smul,
    smul_smul, Int.units_mul_self, one_smul]

Depends on / 依赖: Int.units_mul_self, one_smul, rightShiftAddEquiv, rightUnshift_rightShift, rightUnshift_units_smul, smul_smul, surjective, units_mul_self
-/
lemma δ_rightUnshift {a n' : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n)
    (m m' : Int) (hm' : m' + a = m) :
    δ n m (γ.rightUnshift n hn) = a.negOnePow • (δ n' m' γ).rightUnshift m hm' := by
  obtain ⟨γ', rfl⟩ := (rightShiftAddEquiv K L n a n' hn).surjective γ
  dsimp
  simp only [rightUnshift_rightShift, γ'.δ_rightShift a n' m' hn m hm', rightUnshift_units_smul,
    smul_smul, Int.units_mul_self, one_smul]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ_leftShift` / 引理 `δ_leftShift`

English:
lemma δ_leftShift
  given: (a n' m' : Int) (hn' : n + a = n') (m : Int) (hm' : m + a = m')
  proof: by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by lia
    ext p q hpq
    dsimp
    rw [(δ n m γ).leftShift_v a m' hm' p q hpq (p + a) (by lia)]; rw [δ_v n m hnm _ (p + a) q (by lia) (p + n') (p + 1 + a) (by lia) (by lia)]; rw [δ_v n' m' hnm' _ p q hpq (p + n') (p + 1) (by lia) rfl]; r

中文:
引理 δ_leftShift
  条件: (a n' m' : 整数) (hn' : n + a = n') (m : 整数) (hm' : m + a = m')
  证明: by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by lia
    ext p q hpq
    dsimp
    rw [(δ n m γ).leftShift_v a m' hm' p q hpq (p + a) (by lia)]; rw [δ_v n m hnm _ (p + a) q (by lia) (p + n') (p + 1 + a) (by lia) (by lia)]; rw [δ_v n' m' hnm' _ p q hpq (p + n') (p + 1) (by lia) rfl]; r

Depends on / 依赖: HomologicalComplex, HomologicalComplex.XIsoOfEq_rfl, XIsoOfEq_rfl, leftShift_v, shiftFunctorObjXIso, shiftFunctor_obj_X
-/
lemma δ_leftShift (a n' m' : Int) (hn' : n + a = n') (m : Int) (hm' : m + a = m') :
    δ n' m' (γ.leftShift a n' hn') = a.negOnePow • (δ n m γ).leftShift a m' hm' := by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by lia
    ext p q hpq
    dsimp
    rw [(δ n m γ).leftShift_v a m' hm' p q hpq (p + a) (by lia)]; rw [δ_v n m hnm _ (p + a) q (by lia) (p + n') (p + 1 + a) (by lia) (by lia)]; rw [δ_v n' m' hnm' _ p q hpq (p + n') (p + 1) (by lia) rfl]; rw [γ.leftShift_v a n' hn' p (p + n') rfl (p + a) (by lia)]; rw [γ.leftShift_v a n' hn' (p + 1) q (by lia) (p + 1 + a) (by lia)]
    simp only [shiftFunctor_obj_X, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, id_comp, Linear.units_smul_comp, shiftFunctor_obj_d',
      Linear.comp_units_smul, smul_add, smul_smul]
    congr 2
    · rw [← hnm', add_comm n', mul_add, mul_one]
      simp only [Int.negOnePow_add, ← mul_assoc, Int.units_mul_self, one_mul]
    · simp only [← Int.negOnePow_add, ← hn', ← hm', ← hnm]
      congr 1
      linarith
  · have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by lia)
    rw [δ_shape _ _ hnm']; rw [δ_shape _ _ hnm]; rw [leftShift_zero]; rw [smul_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ_leftUnshift` / 引理 `δ_leftUnshift`

English:
lemma δ_leftUnshift
  statement: {a n' : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a = n')
  proof: by
  obtain ⟨γ', rfl⟩ := (leftShiftAddEquiv K L n a n' hn).surjective γ
  dsimp
  simp only [leftUnshift_leftShift, γ'.δ_leftShift a n' m' hn m hm', leftUnshift_units_smul,
    smul_smul, Int.units_mul_self, one_smul]

中文:
引理 δ_leftUnshift
  结论: {a n' : 整数} (γ : Cochain (K⟦a⟧) L n') (n : 整数) (hn : n + a = n')
  证明: by
  obtain ⟨γ', rfl⟩ := (leftShiftAddEquiv K L n a n' hn).surjective γ
  dsimp
  simp only [leftUnshift_leftShift, γ'.δ_leftShift a n' m' hn m hm', leftUnshift_units_smul,
    smul_smul, Int.units_mul_self, one_smul]

Depends on / 依赖: Int.units_mul_self, leftShiftAddEquiv, leftUnshift_leftShift, leftUnshift_units_smul, one_smul, smul_smul, surjective, units_mul_self
-/
lemma δ_leftUnshift {a n' : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a = n')
    (m m' : Int) (hm' : m + a = m') :
    δ n m (γ.leftUnshift n hn) = a.negOnePow • (δ n' m' γ).leftUnshift m hm' := by
  obtain ⟨γ', rfl⟩ := (leftShiftAddEquiv K L n a n' hn).surjective γ
  dsimp
  simp only [leftUnshift_leftShift, γ'.δ_leftShift a n' m' hn m hm', leftUnshift_units_smul,
    smul_smul, Int.units_mul_self, one_smul]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `δ_shift` / 引理 `δ_shift`

English:
lemma δ_shift
  given: (a m : Int)
  proof: by
  by_cases hnm : n + 1 = m
  · ext p q hpq
    dsimp
    simp only [shift_v', shiftFunctor_obj_d',
      δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl,
      δ_v n m hnm _ (p + a) (q + a) (by lia) (q - 1 + a) (p + 1 + a)
        (by lia) (by lia),
      smul_add, Linear.units_smul_comp, Linear.co

中文:
引理 δ_shift
  条件: (a m : 整数)
  证明: by
  by_cases hnm : n + 1 = m
  · ext p q hpq
    dsimp
    simp only [shift_v', shiftFunctor_obj_d',
      δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl,
      δ_v n m hnm _ (p + a) (q + a) (by lia) (q - 1 + a) (p + 1 + a)
        (by lia) (by lia),
      smul_add, Linear.units_smul_comp, Linear.co

Depends on / 依赖: Linear, Linear.comp_units_smul, Linear.units_smul_comp, add_right_inj, comp_units_smul, shiftFunctor_obj_d, shift_v, shift_zero, smul_add, smul_comm, smul_zero, units_smul_comp
-/
lemma δ_shift (a m : Int) :
    δ n m (γ.shift a) = a.negOnePow • (δ n m γ).shift a := by
  by_cases hnm : n + 1 = m
  · ext p q hpq
    dsimp
    simp only [shift_v', shiftFunctor_obj_d',
      δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl,
      δ_v n m hnm _ (p + a) (q + a) (by lia) (q - 1 + a) (p + 1 + a)
        (by lia) (by lia),
      smul_add, Linear.units_smul_comp, Linear.comp_units_smul, add_right_inj]
    rw [smul_comm]
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm, shift_zero, smul_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `leftShift_rightShift` / 引理 `leftShift_rightShift`

English:
lemma leftShift_rightShift
  given: (a n' : Int) (hn' : n' + a = n)
  proof: by
  ext p q hpq
  simp only [leftShift_v _ a n hn' p q hpq (p + a) (by lia),
    rightShift_v _ a n' hn' (p + a) q (by lia) (q + a) (by lia), units_smul_v, shift_v']
  dsimp
  rw [id_comp]; rw [comp_id]

中文:
引理 leftShift_rightShift
  条件: (a n' : 整数) (hn' : n' + a = n)
  证明: by
  ext p q hpq
  simp only [leftShift_v _ a n hn' p q hpq (p + a) (by lia),
    rightShift_v _ a n' hn' (p + a) q (by lia) (q + a) (by lia), units_smul_v, shift_v']
  dsimp
  rw [id_comp]; rw [comp_id]

Depends on / 依赖: comp_id, id_comp, leftShift_v, rightShift_v, shift_v, units_smul_v
-/
lemma leftShift_rightShift (a n' : Int) (hn' : n' + a = n) :
    (γ.rightShift a n' hn').leftShift a n hn' =
      (a * n + (a * (a - 1)) / 2).negOnePow • γ.shift a := by
  ext p q hpq
  simp only [leftShift_v _ a n hn' p q hpq (p + a) (by lia),
    rightShift_v _ a n' hn' (p + a) q (by lia) (q + a) (by lia), units_smul_v, shift_v']
  dsimp
  rw [id_comp]; rw [comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `rightShift_leftShift` / 引理 `rightShift_leftShift`

English:
lemma rightShift_leftShift
  given: (a n' : Int) (hn' : n + a = n')
  proof: by
  ext p q hpq
  simp only [rightShift_v _ a n hn' p q hpq (q + a) (by lia),
    leftShift_v _ a n' hn' p (q + a) (by lia) (p + a) (by lia), units_smul_v, shift_v']
  dsimp
  rw [id_comp]; rw [comp_id]

中文:
引理 rightShift_leftShift
  条件: (a n' : 整数) (hn' : n + a = n')
  证明: by
  ext p q hpq
  simp only [rightShift_v _ a n hn' p q hpq (q + a) (by lia),
    leftShift_v _ a n' hn' p (q + a) (by lia) (p + a) (by lia), units_smul_v, shift_v']
  dsimp
  rw [id_comp]; rw [comp_id]

Depends on / 依赖: comp_id, id_comp, leftShift_v, rightShift_v, shift_v, units_smul_v
-/
lemma rightShift_leftShift (a n' : Int) (hn' : n + a = n') :
    (γ.leftShift a n' hn').rightShift a n hn' =
      (a * n' + (a * (a - 1)) / 2).negOnePow • γ.shift a := by
  ext p q hpq
  simp only [rightShift_v _ a n hn' p q hpq (q + a) (by lia),
    leftShift_v _ a n' hn' p (q + a) (by lia) (p + a) (by lia), units_smul_v, shift_v']
  dsimp
  rw [id_comp]; rw [comp_id]

/--
lemma `leftShift_rightShift_eq_negOnePow_rightShift_leftShift` / 引理 `leftShift_rightShift_eq_negOnePow_rightShift_leftShift`

English:
lemma leftShift_rightShift_eq_negOnePow_rightShift_leftShift
  proof: by
  rw [leftShift_rightShift]; rw [rightShift_leftShift]; rw [smul_smul]; rw [← hn'']; rw [add_comm n a]; rw [mul_add]; rw [Int.negOnePow_add]; rw [Int.negOnePow_add]; rw [Int.negOnePow_add]; rw [Int.negOnePow_mul_self]; rw [← mul_assoc]; rw [← mul_assoc]; rw [Int.units_mul_self]; rw [one_mul]

中文:
引理 leftShift_rightShift_eq_negOnePow_rightShift_leftShift
  证明: by
  rw [leftShift_rightShift]; rw [rightShift_leftShift]; rw [smul_smul]; rw [← hn'']; rw [add_comm n a]; rw [mul_add]; rw [Int.negOnePow_add]; rw [Int.negOnePow_add]; rw [Int.negOnePow_add]; rw [Int.negOnePow_mul_self]; rw [← mul_assoc]; rw [← mul_assoc]; rw [Int.units_mul_self]; rw [one_mul]

Depends on / 依赖: Int.negOnePow_add, Int.negOnePow_mul_self, Int.units_mul_self, add_comm, leftShift_rightShift, mul_add, mul_assoc, negOnePow_add, negOnePow_mul_self, one_mul, rightShift_leftShift, smul_smul, units_mul_self
-/
lemma leftShift_rightShift_eq_negOnePow_rightShift_leftShift
    (a n' n'' : Int) (hn' : n' + a = n) (hn'' : n + a = n'') :
    (γ.rightShift a n' hn').leftShift a n hn' =
      a.negOnePow • (γ.leftShift a n'' hn'').rightShift a n hn'' := by
  rw [leftShift_rightShift]; rw [rightShift_leftShift]; rw [smul_smul]; rw [← hn'']; rw [add_comm n a]; rw [mul_add]; rw [Int.negOnePow_add]; rw [Int.negOnePow_add]; rw [Int.negOnePow_add]; rw [Int.negOnePow_mul_self]; rw [← mul_assoc]; rw [← mul_assoc]; rw [Int.units_mul_self]; rw [one_mul]

end Cochain

namespace Cocycle

/-- The map `Cocycle K L n → Cocycle K (L⟦a⟧) n'` when `n' + a = n`. -/
@[simps!]
/--
Definition of `rightShift` / `rightShift` 的定义

English:
definition rightShift
  signature: (γ : Cocycle K L n) (a n' : Int) (hn' : n' + a = n)
  body: Cocycle.mk (γ.1.rightShift a n' hn') _ rfl (by
    simp only [Cochain.δ_rightShift _ a n' (n' + 1) hn' (n + 1) (by lia),
      δ_eq_zero, Cochain.rightShift_zero, smul_zero])

中文:
定义 rightShift
  签名: (γ : Cocycle K L n) (a n' : 整数) (hn' : n' + a = n)
  定义体: Cocycle.mk (γ.1.rightShift a n' hn') _ rfl (by
    simp only [Cochain.δ_rightShift _ a n' (n' + 1) hn' (n + 1) (by lia),
      δ_eq_zero, Cochain.rightShift_zero, smul_zero])

Depends on / 依赖: Cochain, Cochain.rightShift_zero, Cocycle, Cocycle.mk, rightShift, rightShift_zero, smul_zero
-/
def rightShift (γ : Cocycle K L n) (a n' : Int) (hn' : n' + a = n) :
    Cocycle K (L⟦a⟧) n' :=
  Cocycle.mk (γ.1.rightShift a n' hn') _ rfl (by
    simp only [Cochain.δ_rightShift _ a n' (n' + 1) hn' (n + 1) (by lia),
      δ_eq_zero, Cochain.rightShift_zero, smul_zero])

/-- The map `Cocycle K (L⟦a⟧) n' → Cocycle K L n` when `n' + a = n`. -/
@[simps!]
/--
Definition of `rightUnshift` / `rightUnshift` 的定义

English:
definition rightUnshift
  signature: {n' a : Int} (γ : Cocycle K (L⟦a⟧) n') (n : Int) (hn : n' + a = n)
  body: Cocycle.mk (γ.1.rightUnshift n hn) _ rfl (by
    rw [Cochain.δ_rightUnshift _ n hn (n + 1) (n + 1 - a) (by lia)]; rw [δ_eq_zero]; rw [Cochain.rightUnshift_zero]; rw [smul_zero])

中文:
定义 rightUnshift
  签名: {n' a : 整数} (γ : Cocycle K (L⟦a⟧) n') (n : 整数) (hn : n' + a = n)
  定义体: Cocycle.mk (γ.1.rightUnshift n hn) _ rfl (by
    rw [Cochain.δ_rightUnshift _ n hn (n + 1) (n + 1 - a) (by lia)]; rw [δ_eq_zero]; rw [Cochain.rightUnshift_zero]; rw [smul_zero])

Depends on / 依赖: Cochain, Cochain.rightUnshift_zero, Cocycle, Cocycle.mk, rightUnshift, rightUnshift_zero, smul_zero
-/
def rightUnshift {n' a : Int} (γ : Cocycle K (L⟦a⟧) n') (n : Int) (hn : n' + a = n) :
    Cocycle K L n :=
  Cocycle.mk (γ.1.rightUnshift n hn) _ rfl (by
    rw [Cochain.δ_rightUnshift _ n hn (n + 1) (n + 1 - a) (by lia)]; rw [δ_eq_zero]; rw [Cochain.rightUnshift_zero]; rw [smul_zero])

/-- The map `Cocycle K L n → Cocycle (K⟦a⟧) L n'` when `n + a = n'`. -/
@[simps!]
/--
Definition of `leftShift` / `leftShift` 的定义

English:
definition leftShift
  signature: (γ : Cocycle K L n) (a n' : Int) (hn' : n + a = n')
  body: Cocycle.mk (γ.1.leftShift a n' hn') _ rfl (by
    simp only [Cochain.δ_leftShift _ a n' (n' + 1) hn' (n + 1) (by lia),
      δ_eq_zero, Cochain.leftShift_zero, smul_zero])

中文:
定义 leftShift
  签名: (γ : Cocycle K L n) (a n' : 整数) (hn' : n + a = n')
  定义体: Cocycle.mk (γ.1.leftShift a n' hn') _ rfl (by
    simp only [Cochain.δ_leftShift _ a n' (n' + 1) hn' (n + 1) (by lia),
      δ_eq_zero, Cochain.leftShift_zero, smul_zero])

Depends on / 依赖: Cochain, Cochain.leftShift_zero, Cocycle, Cocycle.mk, leftShift, leftShift_zero, smul_zero
-/
def leftShift (γ : Cocycle K L n) (a n' : Int) (hn' : n + a = n') :
    Cocycle (K⟦a⟧) L n' :=
  Cocycle.mk (γ.1.leftShift a n' hn') _ rfl (by
    simp only [Cochain.δ_leftShift _ a n' (n' + 1) hn' (n + 1) (by lia),
      δ_eq_zero, Cochain.leftShift_zero, smul_zero])

/-- The map `Cocycle (K⟦a⟧) L n' → Cocycle K L n` when `n + a = n'`. -/
@[simps!]
/--
Definition of `leftUnshift` / `leftUnshift` 的定义

English:
definition leftUnshift
  signature: {n' a : Int} (γ : Cocycle (K⟦a⟧) L n') (n : Int) (hn : n + a = n')
  body: Cocycle.mk (γ.1.leftUnshift n hn) _ rfl (by
    rw [Cochain.δ_leftUnshift _ n hn (n + 1) (n + 1 + a) rfl]; rw [δ_eq_zero]; rw [Cochain.leftUnshift_zero]; rw [smul_zero])

中文:
定义 leftUnshift
  签名: {n' a : 整数} (γ : Cocycle (K⟦a⟧) L n') (n : 整数) (hn : n + a = n')
  定义体: Cocycle.mk (γ.1.leftUnshift n hn) _ rfl (by
    rw [Cochain.δ_leftUnshift _ n hn (n + 1) (n + 1 + a) rfl]; rw [δ_eq_zero]; rw [Cochain.leftUnshift_zero]; rw [smul_zero])

Depends on / 依赖: Cochain, Cochain.leftUnshift_zero, Cocycle, Cocycle.mk, leftUnshift, leftUnshift_zero, smul_zero
-/
def leftUnshift {n' a : Int} (γ : Cocycle (K⟦a⟧) L n') (n : Int) (hn : n + a = n') :
    Cocycle K L n :=
  Cocycle.mk (γ.1.leftUnshift n hn) _ rfl (by
    rw [Cochain.δ_leftUnshift _ n hn (n + 1) (n + 1 + a) rfl]; rw [δ_eq_zero]; rw [Cochain.leftUnshift_zero]; rw [smul_zero])

/-- The map `Cocycle K L n → Cocycle (K⟦a⟧) (L⟦a⟧) n`. -/
@[simps!]
/--
Definition of `shift` / `shift` 的定义

English:
definition shift
  signature: (γ : Cocycle K L n) (a : Int)
  body: Cocycle.mk (γ.1.shift a) _ rfl
    (by simp only [Cochain.δ_shift, δ_eq_zero, Cochain.shift_zero, smul_zero])

中文:
定义 shift
  签名: (γ : Cocycle K L n) (a : 整数)
  定义体: Cocycle.mk (γ.1.shift a) _ rfl
    (by simp only [Cochain.δ_shift, δ_eq_zero, Cochain.shift_zero, smul_zero])

Depends on / 依赖: Cochain, Cochain.shift_zero, Cocycle, Cocycle.mk, shift_zero, smul_zero
-/
def shift (γ : Cocycle K L n) (a : Int) :
    Cocycle (K⟦a⟧) (L⟦a⟧) n :=
  Cocycle.mk (γ.1.shift a) _ rfl
    (by simp only [Cochain.δ_shift, δ_eq_zero, Cochain.shift_zero, smul_zero])

/-- The additive equivalence `Cocycle K L n ≃+ Cocycle K L⟦a⟧ n'` when `n' + a = n`. -/
@[simps]
/--
Definition of `rightShiftAddEquiv` / `rightShiftAddEquiv` 的定义

English:
definition rightShiftAddEquiv
  signature: (n a n' : Int) (hn' : n' + a = n)
  body: γ.rightShift a n' hn'
  invFun γ := γ.rightUnshift n hn'
  left_inv γ := by cat_disch
  right_inv γ := by cat_disch
  map_add' γ γ' := by cat_disch

中文:
定义 rightShiftAddEquiv
  签名: (n a n' : 整数) (hn' : n' + a = n)
  定义体: γ.rightShift a n' hn'
  invFun γ := γ.rightUnshift n hn'
  left_inv γ := by cat_disch
  right_inv γ := by cat_disch
  map_add' γ γ' := by cat_disch

Depends on / 依赖: rightShift
-/
def rightShiftAddEquiv (n a n' : Int) (hn' : n' + a = n) :
    Cocycle K L n ≃+ Cocycle K (L⟦a⟧) n' where
  toFun γ := γ.rightShift a n' hn'
  invFun γ := γ.rightUnshift n hn'
  left_inv γ := by cat_disch
  right_inv γ := by cat_disch
  map_add' γ γ' := by cat_disch

/-- The additive equivalence `K ⟶ L⟦n⟧ ≃+ Cocycle K L n`. -/
@[simps! -isSimp apply symm_apply]
/--
Definition of `equivHomShift` / `equivHomShift` 的定义

English:
definition equivHomShift
  signature: :
  body: (equivHom _ _).trans (rightShiftAddEquiv _ _ _ (zero_add n)).symm

中文:
定义 equivHomShift
  签名: :
  定义体: (equivHom _ _).trans (rightShiftAddEquiv _ _ _ (zero_add n)).symm

Depends on / 依赖: equivHom, rightShiftAddEquiv, zero_add
-/
def equivHomShift :
    (K ⟶ L⟦n⟧) ≃+ Cocycle K L n :=
  (equivHom _ _).trans (rightShiftAddEquiv _ _ _ (zero_add n)).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `equivHomShift_comp` / 引理 `equivHomShift_comp`

English:
lemma equivHomShift_comp
  statement: {K' : CochainComplex C Int}
  proof: by
  ext p q hpq
  simp [equivHomShift_apply, Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p)]

中文:
引理 equivHomShift_comp
  结论: {K' : CochainComplex C 整数}
  证明: by
  ext p q hpq
  simp [equivHomShift_apply, Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p)]

Depends on / 依赖: Cochain, Cochain.rightUnshift_v, add_zero, equivHomShift_apply, rightUnshift_v
-/
lemma equivHomShift_comp {K' : CochainComplex C Int}
    (g : K' ⟶ K) (f : K ⟶ L⟦n⟧) :
    equivHomShift (g ≫ f) = Cocycle.precomp (equivHomShift f) g := by
  ext p q hpq
  simp [equivHomShift_apply, Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p)]

/--
lemma `equivHomShift_symm_precomp` / 引理 `equivHomShift_symm_precomp`

English:
lemma equivHomShift_symm_precomp
  proof: equivHomShift.injective (by simp [equivHomShift_comp])

中文:
引理 equivHomShift_symm_precomp
  证明: equivHomShift.injective (by simp [equivHomShift_comp])

Depends on / 依赖: equivHomShift, equivHomShift.injective, equivHomShift_comp, injective
-/
lemma equivHomShift_symm_precomp
    (z : Cocycle K L n) {K' : CochainComplex C Int} (g : K' ⟶ K) :
    equivHomShift.symm (z.precomp g) = g ≫ equivHomShift.symm z :=
  equivHomShift.injective (by simp [equivHomShift_comp])

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `equivHomShift_comp_shift` / 引理 `equivHomShift_comp_shift`

English:
lemma equivHomShift_comp_shift
  given: (f : K ⟶ L⟦n⟧) {L' : CochainComplex C Int} (g : L ⟶ L')
  proof: by
  ext p q rfl
  simp [equivHomShift_apply, Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p)]

中文:
引理 equivHomShift_comp_shift
  条件: (f : K ⟶ L⟦n⟧) {L' : CochainComplex C 整数} (g : L ⟶ L')
  证明: by
  ext p q rfl
  simp [equivHomShift_apply, Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p)]

Depends on / 依赖: Cochain, Cochain.rightUnshift_v, add_zero, equivHomShift_apply, rightUnshift_v
-/
lemma equivHomShift_comp_shift (f : K ⟶ L⟦n⟧) {L' : CochainComplex C Int} (g : L ⟶ L') :
    equivHomShift (f ≫ g⟦n⟧') = Cocycle.postcomp (equivHomShift f) g := by
  ext p q rfl
  simp [equivHomShift_apply, Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p)]

/--
lemma `equivHomShift_symm_postcomp` / 引理 `equivHomShift_symm_postcomp`

English:
lemma equivHomShift_symm_postcomp
  proof: equivHomShift.injective (by simp [equivHomShift_comp_shift])

中文:
引理 equivHomShift_symm_postcomp
  证明: equivHomShift.injective (by simp [equivHomShift_comp_shift])

Depends on / 依赖: equivHomShift, equivHomShift.injective, equivHomShift_comp_shift, injective
-/
lemma equivHomShift_symm_postcomp
    (z : Cocycle K L n) {L' : CochainComplex C Int} (g : L ⟶ L') :
    equivHomShift.symm (z.postcomp g) = equivHomShift.symm z ≫ g⟦n⟧' :=
  equivHomShift.injective (by simp [equivHomShift_comp_shift])

/-- The additive equivalence `Cocycle K L n ≃+ Cocycle K⟦a⟧ L n'` when `n + a = n'`. -/
@[simps]
/--
Definition of `leftShiftAddEquiv` / `leftShiftAddEquiv` 的定义

English:
definition leftShiftAddEquiv
  signature: (n a n' : Int) (hn' : n + a = n')
  body: γ.leftShift a n' hn'
  invFun γ := γ.leftUnshift n hn'
  left_inv γ := by cat_disch
  right_inv γ := by cat_disch
  map_add' γ γ' := by cat_disch

中文:
定义 leftShiftAddEquiv
  签名: (n a n' : 整数) (hn' : n + a = n')
  定义体: γ.leftShift a n' hn'
  invFun γ := γ.leftUnshift n hn'
  left_inv γ := by cat_disch
  right_inv γ := by cat_disch
  map_add' γ γ' := by cat_disch

Depends on / 依赖: leftShift
-/
def leftShiftAddEquiv (n a n' : Int) (hn' : n + a = n') :
    Cocycle K L n ≃+ Cocycle (K⟦a⟧) L n' where
  toFun γ := γ.leftShift a n' hn'
  invFun γ := γ.leftUnshift n hn'
  left_inv γ := by cat_disch
  right_inv γ := by cat_disch
  map_add' γ γ' := by cat_disch

/-- The additive equivalence `(K⟦n⟧) ⟶ L ≃+ Cocycle K L m` when `m + n = 0`. -/
@[simps! -isSimp apply symm_apply]
/--
Definition of `equivHomShift'` / `equivHomShift'` 的定义

English:
definition equivHomShift'
  signature: (n m : Int) (h : m + n = 0)
  body: (equivHom _ _).trans (leftShiftAddEquiv _ _ _ h).symm

中文:
定义 equivHomShift'
  签名: (n m : 整数) (h : m + n = 0)
  定义体: (equivHom _ _).trans (leftShiftAddEquiv _ _ _ h).symm

Depends on / 依赖: equivHom, leftShiftAddEquiv
-/
def equivHomShift' (n m : Int) (h : m + n = 0) :
    ((K⟦n⟧) ⟶ L) ≃+ Cocycle K L m :=
  (equivHom _ _).trans (leftShiftAddEquiv _ _ _ h).symm

end Cocycle

end CochainComplex.HomComplex
