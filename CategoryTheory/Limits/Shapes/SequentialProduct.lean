/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.PiProd
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.CategoryTheory.EffectiveEpi.Basic
/-!

# ℕ-indexed products as sequential limits

Given sequences `M N : ℕ → C` of objects with morphisms `f n : M n ⟶ N n` for all `n`, this file
exhibits `∏ M` as the limit of the tower

```
⋯ → ∏_{n < m + 1} M n × ∏_{n ≥ m + 1} N n → ∏_{n < m} M n × ∏_{n ≥ m} N n → ⋯ → ∏ N
```

Further, we prove that the transition maps in this tower are epimorphisms, in the case when each
`f n` is an epimorphism and `C` has finite biproducts.
-/

@[expose] public section

namespace CategoryTheory.Limits.SequentialProduct

variable {C : Type*} {M N : Nat -> C}

/--
lemma `functorObj_eq_pos` / 引理 `functorObj_eq_pos`

English:
lemma functorObj_eq_pos
  given: {n m : Nat} (h : m < n)
  proof: dif_pos h

中文:
引理 functorObj_eq_pos
  条件: {n m : 自然数} (h : m < n)
  证明: dif_pos h

Depends on / 依赖: dif_pos
-/
lemma functorObj_eq_pos {n m : Nat} (h : m < n) :
    (fun i => if _ : i < n then M i else N i) m = M m := dif_pos h

/--
lemma `functorObj_eq_neg` / 引理 `functorObj_eq_neg`

English:
lemma functorObj_eq_neg
  given: {n m : Nat} (h : ¬(m < n))
  proof: dif_neg h

中文:
引理 functorObj_eq_neg
  条件: {n m : 自然数} (h : ¬(m < n))
  证明: dif_neg h

Depends on / 依赖: dif_neg
-/
lemma functorObj_eq_neg {n m : Nat} (h : ¬(m < n)) :
    (fun i => if _ : i < n then M i else N i) m = N m := dif_neg h

variable [Category* C] (f : forall n, M n ⟶ N n) [HasCountableProducts C]

variable (M N) in
/--
Definition of `functorObj` / `functorObj` 的定义

English:
definition functorObj
  signature: : Nat -> C
  body: fun n => ∏ᶜ (fun m => if _ : m < n then M m else N m)

中文:
定义 functorObj
  签名: : 自然数 -> C
  定义体: fun n => ∏ᶜ (fun m => if _ : m < n then M m else N m)
-/
noncomputable def functorObj : Nat -> C :=
  fun n => ∏ᶜ (fun m => if _ : m < n then M m else N m)

/--
Definition of `functorObjProj_pos` / `functorObjProj_pos` 的定义

English:
definition functorObjProj_pos
  signature: (n m : Nat) (h : m < n)
  body: Pi.π (fun m => if _ : m < n then M m else N m) m ≫ eqToHom (functorObj_eq_pos (by lia))

中文:
定义 functorObjProj_pos
  签名: (n m : 自然数) (h : m < n)
  定义体: Pi.π (fun m => if _ : m < n then M m else N m) m ≫ eqToHom (functorObj_eq_pos (by lia))

Depends on / 依赖: eqToHom, functorObj_eq_pos
-/
noncomputable def functorObjProj_pos (n m : Nat) (h : m < n) :
    functorObj M N n ⟶ M m :=
  Pi.π (fun m => if _ : m < n then M m else N m) m ≫ eqToHom (functorObj_eq_pos (by lia))

/--
Definition of `functorObjProj_neg` / `functorObjProj_neg` 的定义

English:
definition functorObjProj_neg
  signature: (n m : Nat) (h : ¬(m < n))
  body: Pi.π (fun m => if _ : m < n then M m else N m) m ≫ eqToHom (functorObj_eq_neg (by lia))

中文:
定义 functorObjProj_neg
  签名: (n m : 自然数) (h : ¬(m < n))
  定义体: Pi.π (fun m => if _ : m < n then M m else N m) m ≫ eqToHom (functorObj_eq_neg (by lia))

Depends on / 依赖: eqToHom, functorObj_eq_neg
-/
noncomputable def functorObjProj_neg (n m : Nat) (h : ¬(m < n)) :
    functorObj M N n ⟶ N m :=
  Pi.π (fun m => if _ : m < n then M m else N m) m ≫ eqToHom (functorObj_eq_neg (by lia))

/--
Definition of `functorMap` / `functorMap` 的定义

English:
definition functorMap
  signature: : forall n,
  body: by
  intro n
  refine Limits.Pi.map fun m => if h : m < n then eqToHom ?_ else
    if h' : m < n + 1 then eqToHom ?_ ≫ f m ≫ eqToHom ?_ else eqToHom ?_
  all_goals split_ifs; try rfl; try lia

中文:
定义 functorMap
  签名: : 对任意 n,
  定义体: by
  intro n
  refine Limits.Pi.map fun m => if h : m < n then eqToHom ?_ else
    if h' : m < n + 1 then eqToHom ?_ ≫ f m ≫ eqToHom ?_ else eqToHom ?_
  all_goals split_ifs; try rfl; try lia

Depends on / 依赖: Limits, Limits.Pi.map, all_goals, eqToHom, split_ifs
-/
noncomputable def functorMap : forall n,
    functorObj M N (n + 1) ⟶ functorObj M N n := by
  intro n
  refine Limits.Pi.map fun m => if h : m < n then eqToHom ?_ else
    if h' : m < n + 1 then eqToHom ?_ ≫ f m ≫ eqToHom ?_ else eqToHom ?_
  all_goals split_ifs; try rfl; try lia

set_option backward.isDefEq.respectTransparency false in
/--
lemma `functorMap_commSq_succ` / 引理 `functorMap_commSq_succ`

English:
lemma functorMap_commSq_succ
  given: (n : Nat)
  proof: by
  simp [functorMap]

中文:
引理 functorMap_commSq_succ
  条件: (n : 自然数)
  证明: by
  simp [functorMap]

Depends on / 依赖: functorMap
-/
lemma functorMap_commSq_succ (n : Nat) :
    (Functor.ofOpSequence (functorMap f)).map (homOfLE (by lia : n <= n + 1)).op ≫ Pi.π _ n ≫
      eqToHom (functorObj_eq_neg (by lia : ¬(n < n))) =
        (Pi.π (fun i => if _ : i < (n + 1) then M i else N i) n) ≫
          eqToHom (functorObj_eq_pos (by lia)) ≫ f n := by
  simp [functorMap]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `functorMap_commSq_aux` / 引理 `functorMap_commSq_aux`

English:
lemma functorMap_commSq_aux
  given: {n m k : Nat} (h : n <= m) (hh : ¬(k < m))
  proof: by
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le m h ih =>
    specialize ih (by lia)
    have : homOfLE (by lia : n <= m + 1) =
        homOfLE (by lia : n <= m) ≫ homOfLE (by lia : m <= m + 1) := by simp
    rw [this]; rw [op_comp]; rw [Functor.map_comp]
    slice_lhs 2 4 

中文:
引理 functorMap_commSq_aux
  条件: {n m k : 自然数} (h : n <= m) (hh : ¬(k < m))
  证明: by
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le m h ih =>
    specialize ih (by lia)
    have : homOfLE (by lia : n <= m + 1) =
        homOfLE (by lia : n <= m) ≫ homOfLE (by lia : m <= m + 1) := by simp
    rw [this]; rw [op_comp]; rw [Functor.map_comp]
    slice_lhs 2 4 

Depends on / 依赖: Functor, Functor.map_comp, Functor.ofOpSequence_map_homOfLE_succ, Nat.leRec, dif_neg, dite_eq_ite, functorMap, homOfLE, homOfLE_leOfHom, le_succ_of_le, map_comp, ofOpSequence_map_homOfLE_succ, op_comp, slice_lhs, specialize, split_ifs
-/
lemma functorMap_commSq_aux {n m k : Nat} (h : n <= m) (hh : ¬(k < m)) :
    (Functor.ofOpSequence (functorMap f)).map (homOfLE h).op ≫ Pi.π _ k ≫
      eqToHom (functorObj_eq_neg (by lia : ¬(k < n))) =
        (Pi.π (fun i => if _ : i < m then M i else N i) k) ≫
          eqToHom (functorObj_eq_neg hh) := by
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le m h ih =>
    specialize ih (by lia)
    have : homOfLE (by lia : n <= m + 1) =
        homOfLE (by lia : n <= m) ≫ homOfLE (by lia : m <= m + 1) := by simp
    rw [this]; rw [op_comp]; rw [Functor.map_comp]
    slice_lhs 2 4 => rw [ih]
    simp only [homOfLE_leOfHom, Functor.ofOpSequence_map_homOfLE_succ,
      functorMap, dite_eq_ite]
    split_ifs
    · omega
    simp [dif_neg (by lia : ¬(k < m)), dif_neg hh]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `functorMap_commSq` / 引理 `functorMap_commSq`

English:
lemma functorMap_commSq
  given: {n m : Nat} (h : ¬(m < n))
  proof: by
  cases m with
  | zero =>
      have : n = 0 := by lia
      subst this
      simp [functorMap]
  | succ m =>
      rw [← functorMap_commSq_succ f (m + 1)]
      simp only [homOfLE_leOfHom, dite_eq_ite,
        Functor.ofOpSequence_map_homOfLE_succ]
      have : homOfLE (by lia : n <= m + 1 + 1)

中文:
引理 functorMap_commSq
  条件: {n m : 自然数} (h : ¬(m < n))
  证明: by
  cases m with
  | zero =>
      have : n = 0 := by lia
      subst this
      simp [functorMap]
  | succ m =>
      rw [← functorMap_commSq_succ f (m + 1)]
      simp only [homOfLE_leOfHom, dite_eq_ite,
        Functor.ofOpSequence_map_homOfLE_succ]
      have : homOfLE (by lia : n <= m + 1 + 1)

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, Functor.ofOpSequence_map_homOfLE_succ, dite_eq_ite, functorMap, functorMap_commSq_aux, functorMap_commSq_succ, homOfLE, homOfLE_leOfHom, map_comp, ofOpSequence_map_homOfLE_succ, op_comp
-/
lemma functorMap_commSq {n m : Nat} (h : ¬(m < n)) :
    (Functor.ofOpSequence (functorMap f)).map (homOfLE (by lia : n <= m + 1)).op ≫ Pi.π _ m ≫
      eqToHom (functorObj_eq_neg (by lia : ¬(m < n))) =
        (Pi.π (fun i => if _ : i < m + 1 then M i else N i) m) ≫
          eqToHom (functorObj_eq_pos (by lia)) ≫ f m := by
  cases m with
  | zero =>
      have : n = 0 := by lia
      subst this
      simp [functorMap]
  | succ m =>
      rw [← functorMap_commSq_succ f (m + 1)]
      simp only [homOfLE_leOfHom, dite_eq_ite,
        Functor.ofOpSequence_map_homOfLE_succ]
      have : homOfLE (by lia : n <= m + 1 + 1) =
          homOfLE (by lia : n <= m + 1) ≫ homOfLE (by lia : m + 1 <= m + 1 + 1) := by simp
      rw [this]; rw [op_comp]; rw [Functor.map_comp]
      simp only [homOfLE_leOfHom, Functor.ofOpSequence_map_homOfLE_succ,
        Category.assoc]
      congr 1
      exact functorMap_commSq_aux f (by lia) (by lia)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `cone` / `cone` 的定义

English:
definition cone
  signature: : Cone (Functor.ofOpSequence (functorMap f)) where
  body: ∏ᶜ M
  π := by
    refine NatTrans.ofOpSequence
      (fun n => Limits.Pi.map fun m => if h : m < n then eqToHom (functorObj_eq_pos h).symm else
        f m ≫ eqToHom (functorObj_eq_neg h).symm) (fun n => ?_)
    apply Limits.Pi.hom_ext
    intro m
    simp only [Functor.const_obj_obj, dite_eq_ite, 

中文:
定义 cone
  签名: : 锥 (函子.ofOpSequence (functorMap f)) where
  定义体: ∏ᶜ M
  π := by
    refine NatTrans.ofOpSequence
      (fun n => Limits.Pi.map fun m => if h : m < n then eqToHom (functorObj_eq_pos h).symm else
        f m ≫ eqToHom (functorObj_eq_neg h).symm) (fun n => ?_)
    apply Limits.Pi.hom_ext
    intro m
    simp only [Functor.const_obj_obj, dite_eq_ite, 
-/
noncomputable def cone : Cone (Functor.ofOpSequence (functorMap f)) where
  pt := ∏ᶜ M
  π := by
    refine NatTrans.ofOpSequence
      (fun n => Limits.Pi.map fun m => if h : m < n then eqToHom (functorObj_eq_pos h).symm else
        f m ≫ eqToHom (functorObj_eq_neg h).symm) (fun n => ?_)
    apply Limits.Pi.hom_ext
    intro m
    simp only [Functor.const_obj_obj, dite_eq_ite, Functor.ofOpSequence_obj, homOfLE_leOfHom,
      Functor.const_obj_map, Category.id_comp, Pi.map_π, Functor.ofOpSequence_map_homOfLE_succ,
      functorMap, Category.assoc, Pi.map_π_assoc]
    split
    · simp [dif_pos (by lia : m < n + 1)]
    · split
      all_goals simp

/--
lemma `cone_π_app` / 引理 `cone_π_app`

English:
lemma cone_π_app
  given: (n : Nat)
  statement: (cone f).π.app ⟨n⟩ =
  proof: rfl

中文:
引理 cone_π_app
  条件: (n : 自然数)
  结论: (cone f).π.app ⟨n⟩ =
  证明: rfl
-/
lemma cone_π_app (n : Nat) : (cone f).π.app ⟨n⟩ =
    Limits.Pi.map fun m => if h : m < n then eqToHom (functorObj_eq_pos h).symm else
    f m ≫ eqToHom (functorObj_eq_neg h).symm := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `cone_π_app_comp_Pi_π_pos` / 引理 `cone_π_app_comp_Pi_π_pos`

English:
lemma cone_π_app_comp_Pi_π_pos
  given: (m n : Nat) (h : n < m)
  statement: (cone f).π.app ⟨m⟩ ≫
  proof: by
  simp [cone_π_app, dif_pos h]

中文:
引理 cone_π_app_comp_Pi_π_pos
  条件: (m n : 自然数) (h : n < m)
  结论: (cone f).π.app ⟨m⟩ ≫
  证明: by
  simp [cone_π_app, dif_pos h]

Depends on / 依赖: dif_pos
-/
lemma cone_π_app_comp_Pi_π_pos (m n : Nat) (h : n < m) : (cone f).π.app ⟨m⟩ ≫
    Pi.π (fun i => if _ : i < m then M i else N i) n =
    Pi.π _ n ≫ eqToHom (functorObj_eq_pos h).symm := by
  simp [cone_π_app, dif_pos h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `cone_π_app_comp_Pi_π_neg` / 引理 `cone_π_app_comp_Pi_π_neg`

English:
lemma cone_π_app_comp_Pi_π_neg
  given: (m n : Nat) (h : ¬(n < m))
  statement: (cone f).π.app ⟨m⟩ ≫ Pi.π _ n =
  proof: by
  simp [cone_π_app, dif_neg h]

中文:
引理 cone_π_app_comp_Pi_π_neg
  条件: (m n : 自然数) (h : ¬(n < m))
  结论: (cone f).π.app ⟨m⟩ ≫ 依赖函数类型.π _ n =
  证明: by
  simp [cone_π_app, dif_neg h]

Depends on / 依赖: dif_neg
-/
lemma cone_π_app_comp_Pi_π_neg (m n : Nat) (h : ¬(n < m)) : (cone f).π.app ⟨m⟩ ≫ Pi.π _ n =
    Pi.π _ n ≫ f n ≫ eqToHom (functorObj_eq_neg h).symm := by
  simp [cone_π_app, dif_neg h]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimit` / `isLimit` 的定义

English:
definition isLimit
  signature: : IsLimit (cone f) where
  body: Pi.lift fun m =>
    s.π.app ⟨m + 1⟩ ≫ Pi.π (fun i => if _ : i < m + 1 then M i else N i) m ≫
      eqToHom (dif_pos (by lia : m < m + 1))
  fac s := by
    intro ⟨n⟩
    apply Pi.hom_ext
    intro m
    by_cases h : m < n
    · simp only [Category.assoc, cone_π_app_comp_Pi_π_pos f _ _ h]
      simp

中文:
定义 isLimit
  签名: : 是极限 (cone f) where
  定义体: Pi.lift fun m =>
    s.π.app ⟨m + 1⟩ ≫ Pi.π (fun i => if _ : i < m + 1 then M i else N i) m ≫
      eqToHom (dif_pos (by lia : m < m + 1))
  fac s := by
    intro ⟨n⟩
    apply Pi.hom_ext
    intro m
    by_cases h : m < n
    · simp only [Category.assoc, cone_π_app_comp_Pi_π_pos f _ _ h]
      simp

Depends on / 依赖: Pi.lift
-/
noncomputable def isLimit : IsLimit (cone f) where
  lift s := Pi.lift fun m =>
    s.π.app ⟨m + 1⟩ ≫ Pi.π (fun i => if _ : i < m + 1 then M i else N i) m ≫
      eqToHom (dif_pos (by lia : m < m + 1))
  fac s := by
    intro ⟨n⟩
    apply Pi.hom_ext
    intro m
    by_cases h : m < n
    · simp only [Category.assoc, cone_π_app_comp_Pi_π_pos f _ _ h]
      simp only [dite_eq_ite, limit.lift_π_assoc,
        Discrete.functor_obj_eq_as, Fan.mk_π_app, Category.assoc, eqToHom_trans]
      have hh : m + 1 <= n := by lia
      rw [← s.w (homOfLE hh).op]
      simp only [homOfLE_leOfHom, Category.assoc]
      congr
      induction hh using Nat.leRec with
      | refl => simp
      | @le_succ_of_le n hh ih =>
        have : homOfLE (Nat.le_succ_of_le hh) = homOfLE hh ≫ homOfLE (Nat.le_succ n) := by simp
        rw [this]; rw [op_comp]; rw [Functor.map_comp]
        simp only [Nat.succ_eq_add_one, homOfLE_leOfHom,
          Functor.ofOpSequence_map_homOfLE_succ, Category.assoc]
        have h₁ : (if _ : m < m + 1 then M m else N m) = if _ : m < n then M m else N m := by
          rw [dif_pos (by lia)]; rw [dif_pos (by lia)]
        have h₂ : (if _ : m < n then M m else N m) = if _ : m < n + 1 then M m else N m := by
          rw [dif_pos h]; rw [dif_pos (by lia)]
        rw [← eqToHom_trans h₁ h₂]
        slice_lhs 2 4 => rw [ih (by lia)]
        simp only [functorMap, dite_eq_ite, Pi.π, Pi.map_π_assoc]
        split_ifs
        rw [dif_pos (by lia)]
        simp
    · simp only [Category.assoc]
      rw [cone_π_app_comp_Pi_π_neg f _ _ h]
      simp only [dite_eq_ite, limit.lift_π_assoc,
        Discrete.functor_obj_eq_as, Fan.mk_π_app, Category.assoc]
      slice_lhs 2 4 => simp only [← dite_eq_ite, ← functorMap_commSq f h]
      simp
  uniq s m h := by
    apply Pi.hom_ext
    intro n
    simp only [dite_eq_ite, limit.lift_π,
      Fan.mk_π_app, ← h ⟨n + 1⟩, Category.assoc]
    slice_rhs 2 3 => simp only [← dite_eq_ite, cone_π_app_comp_Pi_π_pos f (n + 1) n (by lia)]
    simp

section

variable [HasZeroMorphisms C] [HasFiniteBiproducts C] [forall n, Epi (f n)]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `functorMap_epi` / 引理 `functorMap_epi`

English:
lemma functorMap_epi
  given: (n : Nat)
  statement: Epi (functorMap f n)
  proof: by
  rw [functorMap]; rw [Pi.map_eq_prod_map (P := fun m : Nat => m < n + 1)]
  apply +allowSynthFailures epi_comp
  apply +allowSynthFailures epi_comp
  apply +allowSynthFailures prod.map_epi
  · apply +allowSynthFailures Pi.map_epi
    intro ⟨_, _⟩
    split
    all_goals infer_instance
  · apply 

中文:
引理 functorMap_epi
  条件: (n : 自然数)
  结论: 满态射 (functorMap f n)
  证明: by
  rw [functorMap]; rw [Pi.map_eq_prod_map (P := fun m : Nat => m < n + 1)]
  apply +allowSynthFailures epi_comp
  apply +allowSynthFailures epi_comp
  apply +allowSynthFailures prod.map_epi
  · apply +allowSynthFailures Pi.map_epi
    intro ⟨_, _⟩
    split
    all_goals infer_instance
  · apply 

Depends on / 依赖: IsIso.epi_of_iso, Pi.map_epi, Pi.map_eq_prod_map, Pi.map_isIso, all_goals, allowSynthFailures, epi_comp, epi_of_iso, functorMap, infer_instance, map_epi, map_eq_prod_map, map_isIso, prod.map_epi
-/
lemma functorMap_epi (n : Nat) : Epi (functorMap f n) := by
  rw [functorMap]; rw [Pi.map_eq_prod_map (P := fun m : Nat => m < n + 1)]
  apply +allowSynthFailures epi_comp
  apply +allowSynthFailures epi_comp
  apply +allowSynthFailures prod.map_epi
  · apply +allowSynthFailures Pi.map_epi
    intro ⟨_, _⟩
    split
    all_goals infer_instance
  · apply +allowSynthFailures IsIso.epi_of_iso
    apply +allowSynthFailures Pi.map_isIso
    intro ⟨_, _⟩
    split
    all_goals infer_instance
end

end CategoryTheory.Limits.SequentialProduct
