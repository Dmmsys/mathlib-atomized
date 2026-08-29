/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# The alternating constant complex

Given an object `X : C` and endomorphisms `φ, ψ : X ⟶ X` such that `φ ∘ ψ = ψ ∘ φ = 0`, this file
defines the periodic chain and cochain complexes
`... ⟶ X --φ--> X --ψ--> X --φ--> X --ψ--> 0` and `0 ⟶ X --ψ--> X --φ--> X --ψ--> X --φ--> ...`
(or more generally for any complex shape `c` on `ℕ` where `c.Rel i j` implies `i` and `j` have
different parity). We calculate the homology of these periodic complexes.

In particular, we show `... ⟶ X --𝟙--> X --0--> X --𝟙--> X --0--> X ⟶ 0` is homotopy equivalent
to the single complex where `X` is in degree `0`.

-/

@[expose] public section
universe v u

open CategoryTheory Limits

namespace ComplexShape

/--
lemma `up_nat_odd_add` / 引理 `up_nat_odd_add`

English:
lemma up_nat_odd_add
  given: {i j : Nat} (h : (ComplexShape.up Nat).Rel i j)
  statement: Odd (i + j)
  proof: by
  subst h
  norm_num

中文:
引理 up_nat_odd_add
  条件: {i j : 自然数} (h : (ComplexShape.up 自然数).Rel i j)
  结论: Odd (i + j)
  证明: by
  subst h
  norm_num
-/
lemma up_nat_odd_add {i j : Nat} (h : (ComplexShape.up Nat).Rel i j) : Odd (i + j) := by
  subst h
  norm_num

/--
lemma `down_nat_odd_add` / 引理 `down_nat_odd_add`

English:
lemma down_nat_odd_add
  given: {i j : Nat} (h : (ComplexShape.down Nat).Rel i j)
  statement: Odd (i + j)
  proof: by
  subst h
  norm_num

中文:
引理 down_nat_odd_add
  条件: {i j : 自然数} (h : (ComplexShape.down 自然数).Rel i j)
  结论: Odd (i + j)
  证明: by
  subst h
  norm_num
-/
lemma down_nat_odd_add {i j : Nat} (h : (ComplexShape.down Nat).Rel i j) : Odd (i + j) := by
  subst h
  norm_num

end ComplexShape

namespace HomologicalComplex

open ShortComplex

variable {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
  (A : C) {φ : A ⟶ A} {ψ : A ⟶ A} (hOdd : φ ≫ ψ = 0) (hEven : ψ ≫ φ = 0)

/-- Let `c : ComplexShape ℕ` be such that `i j : ℕ` have opposite parity if they are related by
`c`. Let `φ, ψ : A ⟶ A` be such that `φ ∘ ψ = ψ ∘ φ = 0`. This is a complex of shape `c` whose
objects are all `A`. For all `i, j` related by `c`, `dᵢⱼ = φ` when `i` is even, and `dᵢⱼ = ψ` when
`i` is odd. -/
@[simps!]
/--
Definition of `alternatingConst` / `alternatingConst` 的定义

English:
definition alternatingConst
  signature: {c : ComplexShape Nat} [DecidableRel c.Rel]
  body: A
  d i j :=
    if hij : c.Rel i j then
      if hi : Even i then φ
      else ψ
    else 0
  shape i j := by aesop
  d_comp_d' i j k hij hjk := by
    have := hc i j hij
    split_ifs with hi hj hj
· exact False.elim Nat.not_odd_iff_even.2 hi by simp_all [Nat.odd_add]
    · assumption
    · assump

中文:
定义 alternatingConst
  签名: {c : ComplexShape 自然数} [DecidableRel c.Rel]
  定义体: A
  d i j :=
    if hij : c.Rel i j then
      if hi : Even i then φ
      else ψ
    else 0
  shape i j := by aesop
  d_comp_d' i j k hij hjk := by
    have := hc i j hij
    split_ifs with hi hj hj
· exact False.elim Nat.not_odd_iff_even.2 hi by simp_all [Nat.odd_add]
    · assumption
    · assump
-/
noncomputable def alternatingConst {c : ComplexShape Nat} [DecidableRel c.Rel]
    (hc : forall i j, c.Rel i j -> Odd (i + j)) :
    HomologicalComplex C c where
  X n := A
  d i j :=
    if hij : c.Rel i j then
      if hi : Even i then φ
      else ψ
    else 0
  shape i j := by aesop
  d_comp_d' i j k hij hjk := by
    have := hc i j hij
    split_ifs with hi hj hj
· exact False.elim Nat.not_odd_iff_even.2 hi by simp_all [Nat.odd_add]
    · assumption
    · assumption
· exact False.elim hj by simp_all [Nat.odd_add]

variable {c : ComplexShape Nat} [DecidableRel c.Rel] (hc : forall i j, c.Rel i j -> Odd (i + j))

open HomologicalComplex hiding mk

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `alternatingConstScIsoEven` / `alternatingConstScIsoEven` 的定义

English:
definition alternatingConstScIsoEven
  body: isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp_all only [alternatingConst, dite_eq_ite, Iso.refl_hom, Category.id_comp,
        shortComplexFunctor'_obj_f, ↓reduceIte, Category.comp_id, right_eq_ite_iff]
      intro hi
      have := hc i j hij
exact False.elim Nat.not_odd_iff_even.2

中文:
定义 alternatingConstScIsoEven
  定义体: isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp_all only [alternatingConst, dite_eq_ite, Iso.refl_hom, Category.id_comp,
        shortComplexFunctor'_obj_f, ↓reduceIte, Category.comp_id, right_eq_ite_iff]
      intro hi
      have := hc i j hij
exact False.elim Nat.not_odd_iff_even.2

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, False.elim, Iso.refl, Iso.refl_hom, Nat.not_odd_iff_even, Nat.odd_add, _obj_f, alternatingConst, comp_id, dite_eq_ite, id_comp, not_odd_iff_even, odd_add, reduceIte, refl_hom, right_eq_ite_iff, shortComplexFunctor
-/
noncomputable def alternatingConstScIsoEven
    {i j k : Nat} (hij : c.Rel i j) (hjk : c.Rel j k) (h : Even j) :
    (alternatingConst A hOdd hEven hc).sc' i j k ≅ ShortComplex.mk ψ φ hEven :=
  isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp_all only [alternatingConst, dite_eq_ite, Iso.refl_hom, Category.id_comp,
        shortComplexFunctor'_obj_f, ↓reduceIte, Category.comp_id, right_eq_ite_iff]
      intro hi
      have := hc i j hij
exact False.elim Nat.not_odd_iff_even.2 hi by simp_all [Nat.odd_add])
    (by simp_all [alternatingConst])

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `alternatingConstScIsoOdd` / `alternatingConstScIsoOdd` 的定义

English:
definition alternatingConstScIsoOdd
  body: isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp_all only [alternatingConst, dite_eq_ite, Iso.refl_hom, Category.id_comp,
        shortComplexFunctor'_obj_f, ↓reduceIte, Category.comp_id, left_eq_ite_iff]
      intro hi
      have := hc i j hij
exact False.elim Nat.not_even_iff_odd.2 

中文:
定义 alternatingConstScIsoOdd
  定义体: isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp_all only [alternatingConst, dite_eq_ite, Iso.refl_hom, Category.id_comp,
        shortComplexFunctor'_obj_f, ↓reduceIte, Category.comp_id, left_eq_ite_iff]
      intro hi
      have := hc i j hij
exact False.elim Nat.not_even_iff_odd.2 

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, False.elim, Iso.refl, Iso.refl_hom, Nat.not_even_iff_odd, Nat.odd_add, _obj_f, alternatingConst, comp_id, dite_eq_ite, id_comp, left_eq_ite_iff, not_even_iff_odd, odd_add, reduceIte, refl_hom, shortComplexFunctor
-/
noncomputable def alternatingConstScIsoOdd
    {i j k : Nat} (hij : c.Rel i j) (hjk : c.Rel j k) (h : Odd j) :
    (alternatingConst A hOdd hEven hc).sc' i j k ≅ ShortComplex.mk φ ψ hOdd :=
  isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp_all only [alternatingConst, dite_eq_ite, Iso.refl_hom, Category.id_comp,
        shortComplexFunctor'_obj_f, ↓reduceIte, Category.comp_id, left_eq_ite_iff]
      intro hi
      have := hc i j hij
exact False.elim Nat.not_even_iff_odd.2 h by simp_all [Nat.odd_add])
    (by simp_all [alternatingConst])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `alternatingConst_iCycles_even_comp` / 引理 `alternatingConst_iCycles_even_comp`

English:
lemma alternatingConst_iCycles_even_comp
  statement: [CategoryWithHomology C]
  proof: by
  rw [← cancel_epi (ShortComplex.cyclesMapIso
    (alternatingConstScIsoEven A hOdd hEven hc hpj hnj h)).inv]
  simpa [HomologicalComplex.iCycles, -Preadditive.IsIso.comp_left_eq_zero, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, alternatingConstScIsoEven,
    Category.id_co

中文:
引理 alternatingConst_iCycles_even_comp
  结论: [CategoryWithHomology C]
  证明: by
  rw [← cancel_epi (ShortComplex.cyclesMapIso
    (alternatingConstScIsoEven A hOdd hEven hc hpj hnj h)).inv]
  simpa [HomologicalComplex.iCycles, -Preadditive.IsIso.comp_left_eq_zero, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, alternatingConstScIsoEven,
    Category.id_co

Depends on / 依赖: Category, Category.id_comp, HomologicalComplex, HomologicalComplex.iCycles, HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor, Preadditive, Preadditive.IsIso.comp_left_eq_zero, ShortComplex, ShortComplex.cyclesMapIso, ShortComplex.mk, alternatingConst, alternatingConstScIsoEven, cancel_epi, comp_left_eq_zero, cyclesMapIso, iCycles, iCycles_g, id_comp, shortComplexFunctor
-/
lemma alternatingConst_iCycles_even_comp [CategoryWithHomology C]
    {j : Nat} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Even j) :
    (alternatingConst A hOdd hEven hc).iCycles j ≫ φ = 0 := by
  rw [← cancel_epi (ShortComplex.cyclesMapIso
    (alternatingConstScIsoEven A hOdd hEven hc hpj hnj h)).inv]
  simpa [HomologicalComplex.iCycles, -Preadditive.IsIso.comp_left_eq_zero, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, alternatingConstScIsoEven,
    Category.id_comp (X := (alternatingConst A hOdd hEven hc).X _)]
    using (ShortComplex.mk ψ φ hEven).iCycles_g

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `alternatingConst_iCycles_odd_comp` / 引理 `alternatingConst_iCycles_odd_comp`

English:
lemma alternatingConst_iCycles_odd_comp
  statement: [CategoryWithHomology C]
  proof: by
  rw [← cancel_epi (ShortComplex.cyclesMapIso
    (alternatingConstScIsoOdd A hOdd hEven hc hpj hnj h)).inv]
  simpa [HomologicalComplex.iCycles, -Preadditive.IsIso.comp_left_eq_zero, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, alternatingConstScIsoOdd,
    Category.id_comp

中文:
引理 alternatingConst_iCycles_odd_comp
  结论: [CategoryWithHomology C]
  证明: by
  rw [← cancel_epi (ShortComplex.cyclesMapIso
    (alternatingConstScIsoOdd A hOdd hEven hc hpj hnj h)).inv]
  simpa [HomologicalComplex.iCycles, -Preadditive.IsIso.comp_left_eq_zero, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, alternatingConstScIsoOdd,
    Category.id_comp

Depends on / 依赖: Category, Category.id_comp, HomologicalComplex, HomologicalComplex.iCycles, HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor, Preadditive, Preadditive.IsIso.comp_left_eq_zero, ShortComplex, ShortComplex.cyclesMapIso, ShortComplex.mk, alternatingConst, alternatingConstScIsoOdd, cancel_epi, comp_left_eq_zero, cyclesMapIso, iCycles, iCycles_g, id_comp, shortComplexFunctor
-/
lemma alternatingConst_iCycles_odd_comp [CategoryWithHomology C]
    {j : Nat} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Odd j) :
    (alternatingConst A hOdd hEven hc).iCycles j ≫ ψ = 0 := by
  rw [← cancel_epi (ShortComplex.cyclesMapIso
    (alternatingConstScIsoOdd A hOdd hEven hc hpj hnj h)).inv]
  simpa [HomologicalComplex.iCycles, -Preadditive.IsIso.comp_left_eq_zero, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, alternatingConstScIsoOdd,
    Category.id_comp (X := (alternatingConst A hOdd hEven hc).X _)]
    using (ShortComplex.mk φ ψ hOdd).iCycles_g

/--
Definition of `alternatingConstHomologyIsoEven` / `alternatingConstHomologyIsoEven` 的定义

English:
definition alternatingConstHomologyIsoEven
  signature: [CategoryWithHomology C]
  body: ShortComplex.homologyMapIso (alternatingConstScIsoEven A hOdd hEven hc hpj hnj h)

中文:
定义 alternatingConstHomologyIsoEven
  签名: [CategoryWithHomology C]
  定义体: ShortComplex.homologyMapIso (alternatingConstScIsoEven A hOdd hEven hc hpj hnj h)

Depends on / 依赖: ShortComplex, ShortComplex.homologyMapIso, alternatingConstScIsoEven, homologyMapIso
-/
noncomputable def alternatingConstHomologyIsoEven [CategoryWithHomology C]
    {j : Nat} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Even j) :
    (alternatingConst A hOdd hEven hc).homology j ≅ (ShortComplex.mk ψ φ hEven).homology :=
  ShortComplex.homologyMapIso (alternatingConstScIsoEven A hOdd hEven hc hpj hnj h)

/--
Definition of `alternatingConstHomologyIsoOdd` / `alternatingConstHomologyIsoOdd` 的定义

English:
definition alternatingConstHomologyIsoOdd
  signature: [CategoryWithHomology C]
  body: ShortComplex.homologyMapIso (alternatingConstScIsoOdd A hOdd hEven hc hpj hnj h)

中文:
定义 alternatingConstHomologyIsoOdd
  签名: [CategoryWithHomology C]
  定义体: ShortComplex.homologyMapIso (alternatingConstScIsoOdd A hOdd hEven hc hpj hnj h)

Depends on / 依赖: ShortComplex, ShortComplex.homologyMapIso, alternatingConstScIsoOdd, homologyMapIso
-/
noncomputable def alternatingConstHomologyIsoOdd [CategoryWithHomology C]
    {j : Nat} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Odd j) :
    (alternatingConst A hOdd hEven hc).homology j ≅ (ShortComplex.mk φ ψ hOdd).homology :=
  ShortComplex.homologyMapIso (alternatingConstScIsoOdd A hOdd hEven hc hpj hnj h)

end HomologicalComplex

open CategoryTheory Limits AlgebraicTopology

variable {C : Type*} [Category* C]

namespace ChainComplex

set_option backward.defeqAttrib.useBackward true in
/-- The chain complex `X ←0- X ←𝟙- X ←0- X ←𝟙- X ⋯`.
It is exact away from `0` and has homology `X` at `0`. -/
@[simps]
/--
Definition of `alternatingConst` / `alternatingConst` 的定义

English:
definition alternatingConst
  signature: [HasZeroMorphisms C]
  body: HomologicalComplex.alternatingConst X (Category.id_comp 0) (Category.comp_id 0)
    (fun _ _ => ComplexShape.down_nat_odd_add)
  map {X Y} f := {
    f _ := f
    comm' i j hij := by by_cases Even i <;> simp_all [-Nat.not_even_iff_odd] }

中文:
定义 alternatingConst
  签名: [HasZeroMorphisms C]
  定义体: HomologicalComplex.alternatingConst X (Category.id_comp 0) (Category.comp_id 0)
    (fun _ _ => ComplexShape.down_nat_odd_add)
  map {X Y} f := {
    f _ := f
    comm' i j hij := by by_cases Even i <;> simp_all [-Nat.not_even_iff_odd] }

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, HomologicalComplex, HomologicalComplex.alternatingConst, alternatingConst, comp_id, id_comp
-/
noncomputable def alternatingConst [HasZeroMorphisms C] : C ⥤ ChainComplex C Nat where
  obj X := HomologicalComplex.alternatingConst X (Category.id_comp 0) (Category.comp_id 0)
    (fun _ _ => ComplexShape.down_nat_odd_add)
  map {X Y} f := {
    f _ := f
    comm' i j hij := by by_cases Even i <;> simp_all [-Nat.not_even_iff_odd] }

variable [HasZeroMorphisms C] [HasZeroObject C]

open ZeroObject

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `n`-th homology of the alternating constant complex is zero for non-zero even `n`. -/
noncomputable
/--
Definition of `alternatingConstHomologyDataEvenNEZero` / `alternatingConstHomologyDataEvenNEZero` 的定义

English:
definition alternatingConstHomologyDataEvenNEZero
  signature: (X : C) (n : Nat) (hn : Even n) (h₀ : n != 0)
  body: .ofIsLimitKernelFork _ (by simp [Nat.even_add_one, hn]) _
    (Limits.zeroKernelOfCancelZero _ (by cases n <;> simp_all))

中文:
定义 alternatingConstHomologyDataEvenNEZero
  签名: (X : C) (n : 自然数) (hn : Even n) (h₀ : n != 0)
  定义体: .ofIsLimitKernelFork _ (by simp [Nat.even_add_one, hn]) _
    (Limits.zeroKernelOfCancelZero _ (by cases n <;> simp_all))

Depends on / 依赖: Limits, Limits.zeroKernelOfCancelZero, Nat.even_add_one, even_add_one, ofIsLimitKernelFork, zeroKernelOfCancelZero
-/
def alternatingConstHomologyDataEvenNEZero (X : C) (n : Nat) (hn : Even n) (h₀ : n != 0) :
    ((alternatingConst.obj X).sc n).HomologyData :=
  .ofIsLimitKernelFork _ (by simp [Nat.even_add_one, hn]) _
    (Limits.zeroKernelOfCancelZero _ (by cases n <;> simp_all))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `n`-th homology of the alternating constant complex is zero for odd `n`. -/
noncomputable
/--
Definition of `alternatingConstHomologyDataOdd` / `alternatingConstHomologyDataOdd` 的定义

English:
definition alternatingConstHomologyDataOdd
  signature: (X : C) (n : Nat) (hn : Odd n)
  body: .ofIsColimitCokernelCofork _ (by simp [hn]) _ (Limits.zeroCokernelOfZeroCancel _ (by simp [hn]))

中文:
定义 alternatingConstHomologyDataOdd
  签名: (X : C) (n : 自然数) (hn : Odd n)
  定义体: .ofIsColimitCokernelCofork _ (by simp [hn]) _ (Limits.zeroCokernelOfZeroCancel _ (by simp [hn]))

Depends on / 依赖: Limits, Limits.zeroCokernelOfZeroCancel, ofIsColimitCokernelCofork, zeroCokernelOfZeroCancel
-/
def alternatingConstHomologyDataOdd (X : C) (n : Nat) (hn : Odd n) :
    ((alternatingConst.obj X).sc n).HomologyData :=
  .ofIsColimitCokernelCofork _ (by simp [hn]) _ (Limits.zeroCokernelOfZeroCancel _ (by simp [hn]))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `n`-th homology of the alternating constant complex is `X` for `n = 0`. -/
noncomputable
/--
Definition of `alternatingConstHomologyDataZero` / `alternatingConstHomologyDataZero` 的定义

English:
definition alternatingConstHomologyDataZero
  signature: (X : C) (n : Nat) (hn : n = 0)
  body: .ofZeros _ (by simp [hn]) (by simp [hn])

中文:
定义 alternatingConstHomologyDataZero
  签名: (X : C) (n : 自然数) (hn : n = 0)
  定义体: .ofZeros _ (by simp [hn]) (by simp [hn])

Depends on / 依赖: ofZeros
-/
def alternatingConstHomologyDataZero (X : C) (n : Nat) (hn : n = 0) :
    ((alternatingConst.obj X).sc n).HomologyData :=
  .ofZeros _ (by simp [hn]) (by simp [hn])

instance (X : C) (n : Nat) : (alternatingConst.obj X).HasHomology n := by
  rcases n.even_or_odd with h | h
  · rcases n with - | n
    · exact ⟨⟨alternatingConstHomologyDataZero X _ rfl⟩⟩
    · exact ⟨⟨alternatingConstHomologyDataEvenNEZero X _ h (by simp)⟩⟩
  · exact ⟨⟨alternatingConstHomologyDataOdd X _ h⟩⟩

/--
lemma `alternatingConst_exactAt` / 引理 `alternatingConst_exactAt`

English:
lemma alternatingConst_exactAt
  given: (X : C) (n : Nat) (hn : n != 0)
  proof: by
  rcases n.even_or_odd with h | h
  · exact ⟨(alternatingConstHomologyDataEvenNEZero X _ h hn), isZero_zero C⟩
  · exact ⟨(alternatingConstHomologyDataOdd X _ h), isZero_zero C⟩

中文:
引理 alternatingConst_exactAt
  条件: (X : C) (n : 自然数) (hn : n != 0)
  证明: by
  rcases n.even_or_odd with h | h
  · exact ⟨(alternatingConstHomologyDataEvenNEZero X _ h hn), isZero_zero C⟩
  · exact ⟨(alternatingConstHomologyDataOdd X _ h), isZero_zero C⟩

Depends on / 依赖: alternatingConstHomologyDataEvenNEZero, alternatingConstHomologyDataOdd, even_or_odd, isZero_zero, n.even_or_odd
-/
lemma alternatingConst_exactAt (X : C) (n : Nat) (hn : n != 0) :
    (alternatingConst.obj X).ExactAt n := by
  rcases n.even_or_odd with h | h
  · exact ⟨(alternatingConstHomologyDataEvenNEZero X _ h hn), isZero_zero C⟩
  · exact ⟨(alternatingConstHomologyDataOdd X _ h), isZero_zero C⟩

/-- The `n`-th homology of the alternating constant complex is `X` for `n = 0`. -/
noncomputable
/--
Definition of `alternatingConstHomologyZero` / `alternatingConstHomologyZero` 的定义

English:
definition alternatingConstHomologyZero
  signature: (X : C)
  body: (alternatingConstHomologyDataZero X _ rfl).left.homologyIso

中文:
定义 alternatingConstHomologyZero
  签名: (X : C)
  定义体: (alternatingConstHomologyDataZero X _ rfl).left.homologyIso

Depends on / 依赖: alternatingConstHomologyDataZero, homologyIso, left.homologyIso
-/
def alternatingConstHomologyZero (X : C) : (alternatingConst.obj X).homology 0 ≅ X :=
  (alternatingConstHomologyDataZero X _ rfl).left.homologyIso

end ChainComplex

variable [Preadditive C] [HasZeroObject C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `AlgebraicTopology.alternatingFaceMapComplexConst` / `AlgebraicTopology.alternatingFaceMapComplexConst` 的定义

English:
definition AlgebraicTopology.alternatingFaceMapComplexConst
  signature: :
  body: NatIso.ofComponents (fun X => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) <| by
    rintro _ i rfl
    simp [SimplicialObject.δ, ← Finset.sum_smul, Fin.sum_neg_one_pow, Nat.even_add_one,
      -Nat.not_even_iff_odd]) (by intros; ext; simp)

中文:
定义 AlgebraicTopology.alternatingFaceMapComplexConst
  签名: :
  定义体: NatIso.ofComponents (fun X => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) <| by
    rintro _ i rfl
    simp [SimplicialObject.δ, ← Finset.sum_smul, Fin.sum_neg_one_pow, Nat.even_add_one,
      -Nat.not_even_iff_odd]) (by intros; ext; simp)

Depends on / 依赖: Fin.sum_neg_one_pow, Finset, Finset.sum_smul, HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, Iso.refl, Nat.even_add_one, Nat.not_even_iff_odd, NatIso, NatIso.ofComponents, SimplicialObject, even_add_one, intros, isoOfComponents, not_even_iff_odd, ofComponents, sum_neg_one_pow, sum_smul
-/
noncomputable def AlgebraicTopology.alternatingFaceMapComplexConst :
    Functor.const _ ⋙ alternatingFaceMapComplex C ≅ ChainComplex.alternatingConst :=
  NatIso.ofComponents (fun X => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) <| by
    rintro _ i rfl
    simp [SimplicialObject.δ, ← Finset.sum_smul, Fin.sum_neg_one_pow, Nat.even_add_one,
      -Nat.not_even_iff_odd]) (by intros; ext; simp)

namespace ChainComplex

/--
Definition of `alternatingConstHomotopyEquiv` / `alternatingConstHomotopyEquiv` 的定义

English:
definition alternatingConstHomotopyEquiv
  signature: (X : C)
  body: (HomotopyEquiv.ofIso (alternatingFaceMapComplexConst.app X).symm).trans
    ((SimplicialObject.Augmented.ExtraDegeneracy.const X).homotopyEquiv)

中文:
定义 alternatingConstHomotopyEquiv
  签名: (X : C)
  定义体: (HomotopyEquiv.ofIso (alternatingFaceMapComplexConst.app X).symm).trans
    ((SimplicialObject.Augmented.ExtraDegeneracy.const X).homotopyEquiv)

Depends on / 依赖: Augmented, ExtraDegeneracy, HomotopyEquiv, HomotopyEquiv.ofIso, SimplicialObject, SimplicialObject.Augmented.ExtraDegeneracy.const, alternatingFaceMapComplexConst, alternatingFaceMapComplexConst.app, homotopyEquiv
-/
noncomputable def alternatingConstHomotopyEquiv (X : C) :
    HomotopyEquiv (alternatingConst.obj X) ((single₀ C).obj X) :=
  (HomotopyEquiv.ofIso (alternatingFaceMapComplexConst.app X).symm).trans
    ((SimplicialObject.Augmented.ExtraDegeneracy.const X).homotopyEquiv)

end ChainComplex
