/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.Algebra.Homology.ExactSequenceFour
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Kernel and cokernel of the differential of a spectral object

Let `X` be a spectral object indexed by the category `ι`
in the abelian category `C`. In this file, we introduce
the kernel `X.cycles` and the cokernel `X.opcycles` of `X.δ`.
These are defined when `f` and `g` are composable morphisms
in `ι` and for any integer `n`.
In the documentation, the kernel `X.cycles n f g` of
`δ : H^n(g) ⟶ H^{n+1}(f)` shall be denoted `Z^n(f, g)`,
and the cokernel `X.opcycles n f g` of `δ : H^{n-1}(g) ⟶ H^n(f)`
shall be denoted `opZ^n(f, g)`.
The definitions `cyclesMap` and `opcyclesMap` give the
functoriality of these definitions with respect
to morphisms in `ComposableArrows ι 2`.

We record that `Z^n(f, g)` is a kernel by the lemma
`kernelSequenceCycles_exact` and that `opZ^n(f, g)` is
a cokernel by the lemma `cokernelSequenceOpcycles_exact`.
We also provide a constructor `X.liftCycles` for morphisms
to cycles and `X.descOpcycles` for morphisms from opcycles.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]
-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

namespace SpectralObject

variable (X : SpectralObject C ι)

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : Int)

/--
Definition of `cycles` / `cycles` 的定义

English:
definition cycles
  signature: : C
  body: kernel (X.δ f g n (n + 1))

中文:
定义 cycles
  签名: : C
  定义体: kernel (X.δ f g n (n + 1))

Depends on / 依赖: kernel
-/
noncomputable def cycles : C := kernel (X.δ f g n (n + 1))

/--
Definition of `opcycles` / `opcycles` 的定义

English:
definition opcycles
  signature: : C
  body: cokernel (X.δ f g (n - 1) n)

中文:
定义 opcycles
  签名: : C
  定义体: cokernel (X.δ f g (n - 1) n)

Depends on / 依赖: cokernel
-/
noncomputable def opcycles : C := cokernel (X.δ f g (n - 1) n)

/--
Definition of `iCycles` / `iCycles` 的定义

English:
definition iCycles
  signature: :
  body: kernel.ι _

中文:
定义 iCycles
  签名: :
  定义体: kernel.ι _

Depends on / 依赖: kernel
-/
noncomputable def iCycles :
    X.cycles f g n ⟶ (X.H n).obj (mk₁ g) :=
  kernel.ι _

/--
Definition of `pOpcycles` / `pOpcycles` 的定义

English:
definition pOpcycles
  signature: :
  body: cokernel.π _

中文:
定义 pOpcycles
  签名: :
  定义体: cokernel.π _

Depends on / 依赖: cokernel
-/
noncomputable def pOpcycles :
    (X.H n).obj (mk₁ f) ⟶ X.opcycles f g n :=
  cokernel.π _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (X.iCycles f g n)
  body: by
  dsimp [iCycles]
  infer_instance

中文:
实例 :
  签名: Mono (X.iCycles f g n)
  定义体: by
  dsimp [iCycles]
  infer_instance

Depends on / 依赖: iCycles, infer_instance
-/
instance : Mono (X.iCycles f g n) := by
  dsimp [iCycles]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (X.pOpcycles f g n)
  body: by
  dsimp [pOpcycles]
  infer_instance

中文:
实例 :
  签名: Epi (X.pOpcycles f g n)
  定义体: by
  dsimp [pOpcycles]
  infer_instance

Depends on / 依赖: infer_instance, pOpcycles
-/
instance : Epi (X.pOpcycles f g n) := by
  dsimp [pOpcycles]
  infer_instance

/--
lemma `isZero_opcycles` / 引理 `isZero_opcycles`

English:
lemma isZero_opcycles
  given: (h : IsZero ((X.H n).obj (mk₁ f)))
  proof: by
  rw [IsZero.iff_id_eq_zero]; rw [← cancel_epi (X.pOpcycles ..)]
  apply h.eq_of_src

中文:
引理 isZero_opcycles
  条件: (h : IsZero ((X.H n).obj (mk₁ f)))
  证明: by
  rw [IsZero.iff_id_eq_zero]; rw [← cancel_epi (X.pOpcycles ..)]
  apply h.eq_of_src

Depends on / 依赖: IsZero, IsZero.iff_id_eq_zero, X.pOpcycles, cancel_epi, eq_of_src, h.eq_of_src, iff_id_eq_zero, pOpcycles
-/
lemma isZero_opcycles (h : IsZero ((X.H n).obj (mk₁ f))) :
    IsZero (X.opcycles f g n) := by
  rw [IsZero.iff_id_eq_zero]; rw [← cancel_epi (X.pOpcycles ..)]
  apply h.eq_of_src

/--
lemma `isZero_cycles` / 引理 `isZero_cycles`

English:
lemma isZero_cycles
  given: (h : IsZero ((X.H n).obj (mk₁ g)))
  proof: by
  rw [IsZero.iff_id_eq_zero]; rw [← cancel_mono (X.iCycles ..)]
  apply h.eq_of_tgt

中文:
引理 isZero_cycles
  条件: (h : IsZero ((X.H n).obj (mk₁ g)))
  证明: by
  rw [IsZero.iff_id_eq_zero]; rw [← cancel_mono (X.iCycles ..)]
  apply h.eq_of_tgt

Depends on / 依赖: IsZero, IsZero.iff_id_eq_zero, X.iCycles, cancel_mono, eq_of_tgt, h.eq_of_tgt, iCycles, iff_id_eq_zero
-/
lemma isZero_cycles (h : IsZero ((X.H n).obj (mk₁ g))) :
    IsZero (X.cycles f g n) := by
  rw [IsZero.iff_id_eq_zero]; rw [← cancel_mono (X.iCycles ..)]
  apply h.eq_of_tgt

end

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : Int)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `iCycles_δ` / 引理 `iCycles_δ`

English:
lemma iCycles_δ
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  subst hn₁
  simp [iCycles]

中文:
引理 iCycles_δ
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  subst hn₁
  simp [iCycles]

Depends on / 依赖: X.iCycles, iCycles
-/
lemma iCycles_δ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.iCycles f g n₀ ≫ X.δ f g n₀ n₁ hn₁ = 0 := by
  subst hn₁
  simp [iCycles]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `δ_pOpcycles` / 引理 `δ_pOpcycles`

English:
lemma δ_pOpcycles
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  obtain rfl : n₀ = n₁ - 1 := by lia
  simp [pOpcycles]

中文:
引理 δ_pOpcycles
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  obtain rfl : n₀ = n₁ - 1 := by lia
  simp [pOpcycles]

Depends on / 依赖: X.pOpcycles, pOpcycles
-/
lemma δ_pOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f g n₀ n₁ hn₁ ≫ X.pOpcycles f g n₁ = 0 := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  simp [pOpcycles]

/-- The short complex which expresses `X.cycles` as the kernel of `X.δ`. -/
@[simps]
/--
Definition of `kernelSequenceCycles` / `kernelSequenceCycles` 的定义

English:
definition kernelSequenceCycles
  signature: (hn₁ : n₀ + 1 = n₁ := by lia)
  body: ShortComplex.mk _ _ (X.iCycles_δ f g n₀ n₁ hn₁)

中文:
定义 kernelSequenceCycles
  签名: (hn₁ : n₀ + 1 = n₁ := by lia)
  定义体: ShortComplex.mk _ _ (X.iCycles_δ f g n₀ n₁ hn₁)

Depends on / 依赖: ShortComplex, ShortComplex.mk, X.iCycles_
-/
noncomputable def kernelSequenceCycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.iCycles_δ f g n₀ n₁ hn₁)

/-- The short complex which expresses `X.opcycles` as the cokernel of `X.δ`. -/
@[simps]
/--
Definition of `cokernelSequenceOpcycles` / `cokernelSequenceOpcycles` 的定义

English:
definition cokernelSequenceOpcycles
  signature: (hn₁ : n₀ + 1 = n₁ := by lia)
  body: ShortComplex.mk _ _ (X.δ_pOpcycles f g n₀ n₁ hn₁)

中文:
定义 cokernelSequenceOpcycles
  签名: (hn₁ : n₀ + 1 = n₁ := by lia)
  定义体: ShortComplex.mk _ _ (X.δ_pOpcycles f g n₀ n₁ hn₁)

Depends on / 依赖: ShortComplex, ShortComplex.mk
-/
noncomputable def cokernelSequenceOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.δ_pOpcycles f g n₀ n₁ hn₁)

set_option backward.defeqAttrib.useBackward true in
instance (hn₁ : n₀ + 1 = n₁) :
    Mono (X.kernelSequenceCycles f g n₀ n₁ hn₁).f := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
instance (hn₁ : n₀ + 1 = n₁) :
    Epi (X.cokernelSequenceOpcycles f g n₀ n₁ hn₁).g := by
  dsimp
  infer_instance

/--
lemma `kernelSequenceCycles_exact` / 引理 `kernelSequenceCycles_exact`

English:
lemma kernelSequenceCycles_exact
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  subst hn₁
  apply ShortComplex.exact_kernel

中文:
引理 kernelSequenceCycles_exact
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  subst hn₁
  apply ShortComplex.exact_kernel

Depends on / 依赖: ShortComplex, ShortComplex.exact_kernel, X.kernelSequenceCycles, exact_kernel, kernelSequenceCycles
-/
lemma kernelSequenceCycles_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.kernelSequenceCycles f g n₀ n₁ hn₁).Exact := by
  subst hn₁
  apply ShortComplex.exact_kernel

/--
lemma `cokernelSequenceOpcycles_exact` / 引理 `cokernelSequenceOpcycles_exact`

English:
lemma cokernelSequenceOpcycles_exact
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  obtain rfl : n₀ = n₁ - 1 := by lia
  apply ShortComplex.exact_cokernel

中文:
引理 cokernelSequenceOpcycles_exact
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  obtain rfl : n₀ = n₁ - 1 := by lia
  apply ShortComplex.exact_cokernel

Depends on / 依赖: ShortComplex, ShortComplex.exact_cokernel, X.cokernelSequenceOpcycles, cokernelSequenceOpcycles, exact_cokernel
-/
lemma cokernelSequenceOpcycles_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.cokernelSequenceOpcycles f g n₀ n₁ hn₁).Exact := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  apply ShortComplex.exact_cokernel

section

variable (hn₁ : n₀ + 1 = n₁) {A : C} (x : A ⟶ (X.H n₀).obj (mk₁ g))
    (hx : x ≫ X.δ f g n₀ n₁ hn₁ = 0)

/--
Definition of `liftCycles` / `liftCycles` 的定义

English:
definition liftCycles
  signature: :
  body: kernel.lift _ x (by subst hn₁; exact hx)

@[reassoc (attr := simp)]

中文:
定义 liftCycles
  签名: :
  定义体: kernel.lift _ x (by subst hn₁; exact hx)

@[reassoc (attr := simp)]

Depends on / 依赖: kernel, kernel.lift
-/
noncomputable def liftCycles :
    A ⟶ X.cycles f g n₀ :=
  kernel.lift _ x (by subst hn₁; exact hx)

@[reassoc (attr := simp)]
/--
lemma `liftCycles_i` / 引理 `liftCycles_i`

English:
lemma liftCycles_i
  statement: X.liftCycles f g n₀ n₁ hn₁ x hx ≫ X.iCycles f g n₀ = x
  proof: by
  apply kernel.lift_ι

中文:
引理 liftCycles_i
  结论: X.liftCycles f g n₀ n₁ hn₁ x hx ≫ X.iCycles f g n₀ = x
  证明: by
  apply kernel.lift_ι

Depends on / 依赖: kernel, kernel.lift_
-/
lemma liftCycles_i : X.liftCycles f g n₀ n₁ hn₁ x hx ≫ X.iCycles f g n₀ = x := by
  apply kernel.lift_ι

end

section

variable (hn₁ : n₀ + 1 = n₁) {A : C} (x : (X.H n₁).obj (mk₁ f) ⟶ A)
    (hx : X.δ f g n₀ n₁ hn₁ ≫ x = 0)

/--
Definition of `descOpcycles` / `descOpcycles` 的定义

English:
definition descOpcycles
  signature: :
  body: cokernel.desc _ x (by
    obtain rfl : n₀ = n₁ -1 := by lia
    exact hx)

@[reassoc (attr := simp)]

中文:
定义 descOpcycles
  签名: :
  定义体: cokernel.desc _ x (by
    obtain rfl : n₀ = n₁ -1 := by lia
    exact hx)

@[reassoc (attr := simp)]

Depends on / 依赖: cokernel, cokernel.desc
-/
noncomputable def descOpcycles :
    X.opcycles f g n₁ ⟶ A :=
  cokernel.desc _ x (by
    obtain rfl : n₀ = n₁ -1 := by lia
    exact hx)

@[reassoc (attr := simp)]
/--
lemma `p_descOpcycles` / 引理 `p_descOpcycles`

English:
lemma p_descOpcycles
  statement: X.pOpcycles f g n₁ ≫ X.descOpcycles f g n₀ n₁ hn₁ x hx = x
  proof: by
  apply cokernel.π_desc

中文:
引理 p_descOpcycles
  结论: X.pOpcycles f g n₁ ≫ X.descOpcycles f g n₀ n₁ hn₁ x hx = x
  证明: by
  apply cokernel.π_desc

Depends on / 依赖: cokernel
-/
lemma p_descOpcycles : X.pOpcycles f g n₁ ≫ X.descOpcycles f g n₀ n₁ hn₁ x hx = x := by
  apply cokernel.π_desc

end

end

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

/--
Definition of `cyclesMap` / `cyclesMap` 的定义

English:
definition cyclesMap
  signature: (α : mk₂ f g ⟶ mk₂ f' g') (n : Int)
  body: X.liftCycles _ _ _ _ rfl
    (X.iCycles f g n ≫ (X.H n).map (homMk₁ (α.app 1) (α.app 2)
      (naturality' α 1 2))) (by
      rw [Category.assoc]; rw [X.δ_naturality f g f' g'
        (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
          (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) n (n + 1

中文:
定义 cyclesMap
  签名: (α : mk₂ f g ⟶ mk₂ f' g') (n : 整数)
  定义体: X.liftCycles _ _ _ _ rfl
    (X.iCycles f g n ≫ (X.H n).map (homMk₁ (α.app 1) (α.app 2)
      (naturality' α 1 2))) (by
      rw [Category.assoc]; rw [X.δ_naturality f g f' g'
        (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
          (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) n (n + 1

Depends on / 依赖: Category, Category.assoc, X.iCycles, X.liftCycles, iCycles, liftCycles, naturality, zero_comp
-/
noncomputable def cyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (n : Int) :
    X.cycles f g n ⟶ X.cycles f' g' n :=
  X.liftCycles _ _ _ _ rfl
    (X.iCycles f g n ≫ (X.H n).map (homMk₁ (α.app 1) (α.app 2)
      (naturality' α 1 2))) (by
      rw [Category.assoc]; rw [X.δ_naturality f g f' g'
        (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
          (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) n (n + 1)]; rw [iCycles_δ_assoc _ _ _ _ _]; rw [zero_comp])

@[reassoc]
/--
lemma `cyclesMap_i` / 引理 `cyclesMap_i`

English:
lemma cyclesMap_i
  statement: (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ g ⟶ mk₁ g') (n : Int)
  proof: by
  subst hβ
  simp [cyclesMap]

@[simp]

中文:
引理 cyclesMap_i
  结论: (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ g ⟶ mk₁ g') (n : 整数)
  证明: by
  subst hβ
  simp [cyclesMap]

@[simp]

Depends on / 依赖: X.cyclesMap, X.iCycles, cat_disch, cyclesMap, iCycles
-/
lemma cyclesMap_i (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ g ⟶ mk₁ g') (n : Int)
    (hβ : β = homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2) := by cat_disch) :
    X.cyclesMap f g f' g' α n ≫ X.iCycles f' g' n =
      X.iCycles f g n ≫ (X.H n).map β := by
  subst hβ
  simp [cyclesMap]

@[simp]
/--
lemma `cyclesMap_id` / 引理 `cyclesMap_id`

English:
lemma cyclesMap_id
  given: (n : Int)
  proof: by
  rw [← cancel_mono (X.iCycles f g n)]; rw [X.cyclesMap_i f g f g (𝟙 _) (𝟙 _) n]; rw [Functor.map_id]; rw [Category.comp_id]; rw [Category.id_comp]

@[reassoc]

中文:
引理 cyclesMap_id
  条件: (n : 整数)
  证明: by
  rw [← cancel_mono (X.iCycles f g n)]; rw [X.cyclesMap_i f g f g (𝟙 _) (𝟙 _) n]; rw [Functor.map_id]; rw [Category.comp_id]; rw [Category.id_comp]

@[reassoc]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Functor, Functor.map_id, X.cyclesMap_i, X.iCycles, cancel_mono, comp_id, cyclesMap_i, iCycles, id_comp, map_id
-/
lemma cyclesMap_id (n : Int) :
    X.cyclesMap f g f g (𝟙 _) n = 𝟙 _ := by
  rw [← cancel_mono (X.iCycles f g n)]; rw [X.cyclesMap_i f g f g (𝟙 _) (𝟙 _) n]; rw [Functor.map_id]; rw [Category.comp_id]; rw [Category.id_comp]

@[reassoc]
/--
lemma `cyclesMap_comp` / 引理 `cyclesMap_comp`

English:
lemma cyclesMap_comp
  statement: (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
  proof: by
  subst h
  rw [← cancel_mono (X.iCycles f'' g'' n)]; rw [Category.assoc]; rw [X.cyclesMap_i f' g' f'' g'' α' _ n rfl]; rw [X.cyclesMap_i_assoc f g f' g' α _ n rfl]; rw [← Functor.map_comp]
  exact (X.cyclesMap_i _ _ _ _ _ _ _).symm

中文:
引理 cyclesMap_comp
  结论: (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
  证明: by
  subst h
  rw [← cancel_mono (X.iCycles f'' g'' n)]; rw [Category.assoc]; rw [X.cyclesMap_i f' g' f'' g'' α' _ n rfl]; rw [X.cyclesMap_i_assoc f g f' g' α _ n rfl]; rw [← Functor.map_comp]
  exact (X.cyclesMap_i _ _ _ _ _ _ _).symm

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, X.cyclesMap, X.cyclesMap_i, X.cyclesMap_i_assoc, X.iCycles, cancel_mono, cat_disch, cyclesMap, cyclesMap_i, cyclesMap_i_assoc, iCycles, map_comp
-/
lemma cyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
    (α'' : mk₂ f g ⟶ mk₂ f'' g'') (n : Int) (h : α ≫ α' = α'' := by cat_disch) :
    X.cyclesMap f g f' g' α n ≫ X.cyclesMap f' g' f'' g'' α' n =
      X.cyclesMap f g f'' g'' α'' n := by
  subst h
  rw [← cancel_mono (X.iCycles f'' g'' n)]; rw [Category.assoc]; rw [X.cyclesMap_i f' g' f'' g'' α' _ n rfl]; rw [X.cyclesMap_i_assoc f g f' g' α _ n rfl]; rw [← Functor.map_comp]
  exact (X.cyclesMap_i _ _ _ _ _ _ _).symm

/--
Definition of `opcyclesMap` / `opcyclesMap` 的定义

English:
definition opcyclesMap
  signature: (α : mk₂ f g ⟶ mk₂ f' g') (n : Int)
  body: X.descOpcycles _ _ (n - 1) n (by lia)
    ((X.H n).map (homMk₁ (by exact α.app 0) (by exact α.app 1)
      (naturality' α 0 1)) ≫ X.pOpcycles f' g' n) (by
      rw [← X.δ_naturality_assoc f g f' g'
        (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
        (homMk₁ (α.app 1) (α.app 2) (naturali

中文:
定义 opcyclesMap
  签名: (α : mk₂ f g ⟶ mk₂ f' g') (n : 整数)
  定义体: X.descOpcycles _ _ (n - 1) n (by lia)
    ((X.H n).map (homMk₁ (by exact α.app 0) (by exact α.app 1)
      (naturality' α 0 1)) ≫ X.pOpcycles f' g' n) (by
      rw [← X.δ_naturality_assoc f g f' g'
        (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
        (homMk₁ (α.app 1) (α.app 2) (naturali

Depends on / 依赖: X.descOpcycles, X.pOpcycles, comp_zero, descOpcycles, naturality, pOpcycles
-/
noncomputable def opcyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (n : Int) :
    X.opcycles f g n ⟶ X.opcycles f' g' n :=
  X.descOpcycles _ _ (n - 1) n (by lia)
    ((X.H n).map (homMk₁ (by exact α.app 0) (by exact α.app 1)
      (naturality' α 0 1)) ≫ X.pOpcycles f' g' n) (by
      rw [← X.δ_naturality_assoc f g f' g'
        (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
        (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) _ _]; rw [δ_pOpcycles _ _ _ _ _]; rw [comp_zero])

@[reassoc]
/--
lemma `p_opcyclesMap` / 引理 `p_opcyclesMap`

English:
lemma p_opcyclesMap
  statement: (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ f ⟶ mk₁ f') (n : Int)
  proof: by
  subst hβ
  simp [opcyclesMap]

@[simp]

中文:
引理 p_opcyclesMap
  结论: (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ f ⟶ mk₁ f') (n : 整数)
  证明: by
  subst hβ
  simp [opcyclesMap]

@[simp]

Depends on / 依赖: X.opcyclesMap, X.pOpcycles, cat_disch, opcyclesMap, pOpcycles
-/
lemma p_opcyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ f ⟶ mk₁ f') (n : Int)
    (hβ : β = homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1) := by cat_disch) :
    X.pOpcycles f g n ≫ X.opcyclesMap f g f' g' α n =
      (X.H n).map β ≫ X.pOpcycles f' g' n := by
  subst hβ
  simp [opcyclesMap]

@[simp]
/--
lemma `opcyclesMap_id` / 引理 `opcyclesMap_id`

English:
lemma opcyclesMap_id
  given: (n : Int)
  proof: by
  rw [← cancel_epi (X.pOpcycles f g n)]; rw [X.p_opcyclesMap f g f g (𝟙 _) (𝟙 _)]; rw [Functor.map_id]; rw [Category.comp_id]; rw [Category.id_comp]

中文:
引理 opcyclesMap_id
  条件: (n : 整数)
  证明: by
  rw [← cancel_epi (X.pOpcycles f g n)]; rw [X.p_opcyclesMap f g f g (𝟙 _) (𝟙 _)]; rw [Functor.map_id]; rw [Category.comp_id]; rw [Category.id_comp]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Functor, Functor.map_id, X.pOpcycles, X.p_opcyclesMap, cancel_epi, comp_id, id_comp, map_id, pOpcycles, p_opcyclesMap
-/
lemma opcyclesMap_id (n : Int) :
    X.opcyclesMap f g f g (𝟙 _) n = 𝟙 _ := by
  rw [← cancel_epi (X.pOpcycles f g n)]; rw [X.p_opcyclesMap f g f g (𝟙 _) (𝟙 _)]; rw [Functor.map_id]; rw [Category.comp_id]; rw [Category.id_comp]

/--
lemma `opcyclesMap_comp` / 引理 `opcyclesMap_comp`

English:
lemma opcyclesMap_comp
  statement: (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
  proof: by
  subst h
  rw [← cancel_epi (X.pOpcycles f g n)]; rw [X.p_opcyclesMap_assoc f g f' g' α _]; rw [X.p_opcyclesMap f' g' f'' g'' α' _]; rw [← Functor.map_comp_assoc]
  exact (X.p_opcyclesMap _ _ _ _ _ _ _ (by cat_disch)).symm

中文:
引理 opcyclesMap_comp
  结论: (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
  证明: by
  subst h
  rw [← cancel_epi (X.pOpcycles f g n)]; rw [X.p_opcyclesMap_assoc f g f' g' α _]; rw [X.p_opcyclesMap f' g' f'' g'' α' _]; rw [← Functor.map_comp_assoc]
  exact (X.p_opcyclesMap _ _ _ _ _ _ _ (by cat_disch)).symm

Depends on / 依赖: Functor, Functor.map_comp_assoc, X.opcyclesMap, X.pOpcycles, X.p_opcyclesMap, X.p_opcyclesMap_assoc, cancel_epi, cat_disch, map_comp_assoc, opcyclesMap, pOpcycles, p_opcyclesMap, p_opcyclesMap_assoc
-/
lemma opcyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
    (α'' : mk₂ f g ⟶ mk₂ f'' g'') (n : Int) (h : α ≫ α' = α'' := by cat_disch) :
    X.opcyclesMap f g f' g' α n ≫ X.opcyclesMap f' g' f'' g'' α' n =
      X.opcyclesMap f g f'' g'' α'' n := by
  subst h
  rw [← cancel_epi (X.pOpcycles f g n)]; rw [X.p_opcyclesMap_assoc f g f' g' α _]; rw [X.p_opcyclesMap f' g' f'' g'' α' _]; rw [← Functor.map_comp_assoc]
  exact (X.p_opcyclesMap _ _ _ _ _ _ _ (by cat_disch)).symm

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

/--
Definition of `cokernelIsoCycles` / `cokernelIsoCycles` 的定义

English:
definition cokernelIsoCycles
  signature: (n : Int)
  body: (X.composableArrows₅_exact f g fg h n (n + 1)).cokerIsoKer 0

@[reassoc (attr := simp)]

中文:
定义 cokernelIsoCycles
  签名: (n : 整数)
  定义体: (X.composableArrows₅_exact f g fg h n (n + 1)).cokerIsoKer 0

@[reassoc (attr := simp)]

Depends on / 依赖: X.composableArrows, cokerIsoKer
-/
noncomputable def cokernelIsoCycles (n : Int) :
    cokernel ((X.H n).map (twoδ₂Toδ₁ f g fg h)) ≅ X.cycles f g n :=
  (X.composableArrows₅_exact f g fg h n (n + 1)).cokerIsoKer 0

@[reassoc (attr := simp)]
/--
lemma `cokernelIsoCycles_hom_fac` / 引理 `cokernelIsoCycles_hom_fac`

English:
lemma cokernelIsoCycles_hom_fac
  given: (n : Int)
  proof: (X.composableArrows₅_exact f g fg h n (n + 1)).cokerIsoKer_hom_fac 0

中文:
引理 cokernelIsoCycles_hom_fac
  条件: (n : 整数)
  证明: (X.composableArrows₅_exact f g fg h n (n + 1)).cokerIsoKer_hom_fac 0

Depends on / 依赖: X.composableArrows, cokerIsoKer_hom_fac
-/
lemma cokernelIsoCycles_hom_fac (n : Int) :
    cokernel.π _ ≫ (X.cokernelIsoCycles f g fg h n).hom ≫
      X.iCycles f g n = (X.H n).map (twoδ₁Toδ₀ f g fg h) :=
  (X.composableArrows₅_exact f g fg h n (n + 1)).cokerIsoKer_hom_fac 0

/--
Definition of `opcyclesIsoKernel` / `opcyclesIsoKernel` 的定义

English:
definition opcyclesIsoKernel
  signature: (n : Int)
  body: (X.composableArrows₅_exact f g fg h (n - 1) n).cokerIsoKer 2

@[reassoc (attr := simp)]

中文:
定义 opcyclesIsoKernel
  签名: (n : 整数)
  定义体: (X.composableArrows₅_exact f g fg h (n - 1) n).cokerIsoKer 2

@[reassoc (attr := simp)]

Depends on / 依赖: X.composableArrows, cokerIsoKer
-/
noncomputable def opcyclesIsoKernel (n : Int) :
    X.opcycles f g n ≅ kernel ((X.H n).map (twoδ₁Toδ₀ f g fg h)) :=
  (X.composableArrows₅_exact f g fg h (n - 1) n).cokerIsoKer 2

@[reassoc (attr := simp)]
/--
lemma `opcyclesIsoKernel_hom_fac` / 引理 `opcyclesIsoKernel_hom_fac`

English:
lemma opcyclesIsoKernel_hom_fac
  given: (n : Int)
  proof: (X.composableArrows₅_exact f g fg h (n - 1) n).cokerIsoKer_hom_fac 2

中文:
引理 opcyclesIsoKernel_hom_fac
  条件: (n : 整数)
  证明: (X.composableArrows₅_exact f g fg h (n - 1) n).cokerIsoKer_hom_fac 2

Depends on / 依赖: X.composableArrows, cokerIsoKer_hom_fac
-/
lemma opcyclesIsoKernel_hom_fac (n : Int) :
    X.pOpcycles f g n ≫ (X.opcyclesIsoKernel f g fg h n).hom ≫
      kernel.ι _ = (X.H n).map (twoδ₂Toδ₁ f g fg h) :=
  (X.composableArrows₅_exact f g fg h (n - 1) n).cokerIsoKer_hom_fac 2

/--
Definition of `toCycles` / `toCycles` 的定义

English:
definition toCycles
  signature: (n : Int)
  body: kernel.lift _ ((X.H n).map (twoδ₁Toδ₀ f g fg h)) (by simp)

中文:
定义 toCycles
  签名: (n : 整数)
  定义体: kernel.lift _ ((X.H n).map (twoδ₁Toδ₀ f g fg h)) (by simp)

Depends on / 依赖: kernel, kernel.lift
-/
noncomputable def toCycles (n : Int) :
    (X.H n).obj (mk₁ fg) ⟶ X.cycles f g n :=
  kernel.lift _ ((X.H n).map (twoδ₁Toδ₀ f g fg h)) (by simp)

instance (n : Int) : Epi (X.toCycles f g fg h n) :=
  (ShortComplex.exact_iff_epi_kernel_lift _).1 (X.exact₃ f g fg h n (n + 1))

@[reassoc (attr := simp)]
/--
lemma `toCycles_i` / 引理 `toCycles_i`

English:
lemma toCycles_i
  given: (n : Int)
  proof: kernel.lift_ι ..

中文:
引理 toCycles_i
  条件: (n : 整数)
  证明: kernel.lift_ι ..

Depends on / 依赖: kernel, kernel.lift_
-/
lemma toCycles_i (n : Int) :
    X.toCycles f g fg h n ≫ X.iCycles f g n = (X.H n).map (twoδ₁Toδ₀ f g fg h) :=
  kernel.lift_ι ..

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `toCycles_cyclesMap` / 引理 `toCycles_cyclesMap`

English:
lemma toCycles_cyclesMap
  statement: (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg') (n : Int)
  proof: by
  rw [← cancel_mono (X.iCycles f' g' n)]; rw [Category.assoc]; rw [Category.assoc]; rw [toCycles_i]; rw [X.cyclesMap_i f g f' g' α (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) n rfl]; rw [toCycles_i_assoc]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
  congr 1
  ext
  · dsimp
    rw [hβ₀

中文:
引理 toCycles_cyclesMap
  结论: (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg') (n : 整数)
  证明: by
  rw [← cancel_mono (X.iCycles f' g' n)]; rw [Category.assoc]; rw [Category.assoc]; rw [toCycles_i]; rw [X.cyclesMap_i f g f' g' α (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) n rfl]; rw [toCycles_i_assoc]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
  congr 1
  ext
  · dsimp
    rw [hβ₀

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, X.cyclesMap, X.cyclesMap_i, X.iCycles, X.toCycles, cancel_mono, cat_disch, cyclesMap, cyclesMap_i, iCycles, map_comp, naturality, toCycles, toCycles_i, toCycles_i_assoc
-/
lemma toCycles_cyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg') (n : Int)
    (hβ₀ : β.app 0 = α.app 0 := by cat_disch) (hβ₁ : β.app 1 = α.app 2 := by cat_disch) :
    X.toCycles f g fg h n ≫ X.cyclesMap f g f' g' α n =
      (X.H n).map β ≫ X.toCycles f' g' fg' h' n := by
  rw [← cancel_mono (X.iCycles f' g' n)]; rw [Category.assoc]; rw [Category.assoc]; rw [toCycles_i]; rw [X.cyclesMap_i f g f' g' α (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) n rfl]; rw [toCycles_i_assoc]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
  congr 1
  ext
  · dsimp
    rw [hβ₀]
    exact naturality' α 0 1
  · dsimp
    rw [hβ₁]; rw [Category.comp_id]; rw [Category.id_comp]

/--
Definition of `fromOpcycles` / `fromOpcycles` 的定义

English:
definition fromOpcycles
  signature: (n : Int)
  body: cokernel.desc _ ((X.H n).map (twoδ₂Toδ₁ f g fg h)) (by simp)

中文:
定义 fromOpcycles
  签名: (n : 整数)
  定义体: cokernel.desc _ ((X.H n).map (twoδ₂Toδ₁ f g fg h)) (by simp)

Depends on / 依赖: IsSolvable, IsSolvable.solvable, LieSubmodule, LieSubmodule.baseChange_bot, baseChange_bot, cokernel, cokernel.desc, derivedSeries_baseChange, isSolvable_iff, solvable
-/
noncomputable def fromOpcycles (n : Int) :
    X.opcycles f g n ⟶ (X.H n).obj (mk₁ fg) :=
  cokernel.desc _ ((X.H n).map (twoδ₂Toδ₁ f g fg h)) (by simp)

instance (n : Int) : Mono (X.fromOpcycles f g fg h n) :=
  (ShortComplex.exact_iff_mono_cokernel_desc _).1 (X.exact₁ f g fg h (n - 1) n)

@[reassoc (attr := simp)]
/--
lemma `p_fromOpcycles` / 引理 `p_fromOpcycles`

English:
lemma p_fromOpcycles
  given: (n : Int)
  proof: cokernel.π_desc ..

中文:
引理 p_fromOpcycles
  条件: (n : 整数)
  证明: cokernel.π_desc ..

Depends on / 依赖: cokernel
-/
lemma p_fromOpcycles (n : Int) :
    X.pOpcycles f g n ≫ X.fromOpcycles f g fg h n =
      (X.H n).map (twoδ₂Toδ₁ f g fg h) :=
  cokernel.π_desc ..

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `opcyclesMap_fromOpcycles` / 引理 `opcyclesMap_fromOpcycles`

English:
lemma opcyclesMap_fromOpcycles
  statement: (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg') (n : Int)
  proof: by
  rw [← cancel_epi (X.pOpcycles f g n)]; rw [p_fromOpcycles_assoc]; rw [X.p_opcyclesMap_assoc f g f' g' α (homMk₁ (α.app 0) (α.app 1)
      (naturality' α 0 1)) n rfl]; rw [p_fromOpcycles]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
  congr 1
  ext
  · cat_disch
  · dsimp
    rw [hβ₁]
    e

中文:
引理 opcyclesMap_fromOpcycles
  结论: (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg') (n : 整数)
  证明: by
  rw [← cancel_epi (X.pOpcycles f g n)]; rw [p_fromOpcycles_assoc]; rw [X.p_opcyclesMap_assoc f g f' g' α (homMk₁ (α.app 0) (α.app 1)
      (naturality' α 0 1)) n rfl]; rw [p_fromOpcycles]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
  congr 1
  ext
  · cat_disch
  · dsimp
    rw [hβ₁]
    e

Depends on / 依赖: Functor, Functor.map_comp, X.fromOpcycles, X.opcyclesMap, X.pOpcycles, X.p_opcyclesMap_assoc, cancel_epi, cat_disch, fromOpcycles, map_comp, naturality, opcyclesMap, pOpcycles, p_fromOpcycles, p_fromOpcycles_assoc, p_opcyclesMap_assoc
-/
lemma opcyclesMap_fromOpcycles (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg') (n : Int)
    (hβ₀ : β.app 0 = α.app 0 := by cat_disch) (hβ₁ : β.app 1 = α.app 2 := by cat_disch) :
    X.opcyclesMap f g f' g' α n ≫ X.fromOpcycles f' g' fg' h' n =
      X.fromOpcycles f g fg h n ≫ (X.H n).map β := by
  rw [← cancel_epi (X.pOpcycles f g n)]; rw [p_fromOpcycles_assoc]; rw [X.p_opcyclesMap_assoc f g f' g' α (homMk₁ (α.app 0) (α.app 1)
      (naturality' α 0 1)) n rfl]; rw [p_fromOpcycles]; rw [← Functor.map_comp]; rw [← Functor.map_comp]
  congr 1
  ext
  · cat_disch
  · dsimp
    rw [hβ₁]
    exact (naturality' α 1 2).symm

@[reassoc (attr := simp)]
/--
lemma `H_map_twoδ₂Toδ₁_toCycles` / 引理 `H_map_twoδ₂Toδ₁_toCycles`

English:
lemma H_map_twoδ₂Toδ₁_toCycles
  given: (n : Int)
  proof: by
  simp [← cancel_mono (X.iCycles f g n)]

@[reassoc (attr := simp)]

中文:
引理 H_map_twoδ₂Toδ₁_toCycles
  条件: (n : 整数)
  证明: by
  simp [← cancel_mono (X.iCycles f g n)]

@[reassoc (attr := simp)]

Depends on / 依赖: A.incl_injective.lieAlgebra_isSolvable, X.iCycles, cancel_mono, iCycles, incl_injective, lieAlgebra_isSolvable
-/
lemma H_map_twoδ₂Toδ₁_toCycles (n : Int) :
    (X.H n).map (twoδ₂Toδ₁ f g fg h) ≫ X.toCycles f g fg h n = 0 := by
  simp [← cancel_mono (X.iCycles f g n)]

@[reassoc (attr := simp)]
/--
lemma `fromOpcycles_H_map_twoδ₁Toδ₀` / 引理 `fromOpcycles_H_map_twoδ₁Toδ₀`

English:
lemma fromOpcycles_H_map_twoδ₁Toδ₀
  given: (n : Int)
  proof: by
  simp [← cancel_epi (X.pOpcycles f g n)]

中文:
引理 fromOpcycles_H_map_twoδ₁Toδ₀
  条件: (n : 整数)
  证明: by
  simp [← cancel_epi (X.pOpcycles f g n)]

Depends on / 依赖: X.pOpcycles, cancel_epi, pOpcycles
-/
lemma fromOpcycles_H_map_twoδ₁Toδ₀ (n : Int) :
    X.fromOpcycles f g fg h n ≫ (X.H n).map (twoδ₁Toδ₀ f g fg h) = 0 := by
  simp [← cancel_epi (X.pOpcycles f g n)]

/-- The short complex expressing `Z^n(f, g)` as a cokernel of
the map `H^n(f) ⟶ H^n(f ≫ g)`. -/
@[simps]
/--
Definition of `cokernelSequenceCycles` / `cokernelSequenceCycles` 的定义

English:
definition cokernelSequenceCycles
  signature: (n : Int)
  body: ShortComplex.mk _ _ (X.H_map_twoδ₂Toδ₁_toCycles f g fg h n)

中文:
定义 cokernelSequenceCycles
  签名: (n : 整数)
  定义体: ShortComplex.mk _ _ (X.H_map_twoδ₂Toδ₁_toCycles f g fg h n)

Depends on / 依赖: ShortComplex, ShortComplex.mk, X.H_map_two
-/
noncomputable def cokernelSequenceCycles (n : Int) : ShortComplex C :=
  ShortComplex.mk _ _ (X.H_map_twoδ₂Toδ₁_toCycles f g fg h n)

/-- The short complex expressing `opZ^n(f, g)` as a kernel of
the map `H^n(f ≫ g) ⟶ H^n(g)`. -/
@[simps]
/--
Definition of `kernelSequenceOpcycles` / `kernelSequenceOpcycles` 的定义

English:
definition kernelSequenceOpcycles
  signature: (n : Int)
  body: ShortComplex.mk _ _ (X.fromOpcycles_H_map_twoδ₁Toδ₀ f g fg h n)

中文:
定义 kernelSequenceOpcycles
  签名: (n : 整数)
  定义体: ShortComplex.mk _ _ (X.fromOpcycles_H_map_twoδ₁Toδ₀ f g fg h n)

Depends on / 依赖: ShortComplex, ShortComplex.mk, X.fromOpcycles_H_map_two
-/
noncomputable def kernelSequenceOpcycles (n : Int) : ShortComplex C :=
  ShortComplex.mk _ _ (X.fromOpcycles_H_map_twoδ₁Toδ₀ f g fg h n)

set_option backward.defeqAttrib.useBackward true in
instance (n : Int) : Epi (X.cokernelSequenceCycles f g fg h n).g := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
instance (n : Int) : Mono (X.kernelSequenceOpcycles f g fg h n).f := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `cokernelSequenceCycles_exact` / 引理 `cokernelSequenceCycles_exact`

English:
lemma cokernelSequenceCycles_exact
  given: (n : Int)
  proof: by
  apply ShortComplex.exact_of_g_is_cokernel
  exact IsColimit.ofIsoColimit (cokernelIsCokernel _)
    (Cofork.ext (X.cokernelIsoCycles f g fg h n) (by
      simp [← cancel_mono (X.iCycles f g n)]))

中文:
引理 cokernelSequenceCycles_exact
  条件: (n : 整数)
  证明: by
  apply ShortComplex.exact_of_g_is_cokernel
  exact IsColimit.ofIsoColimit (cokernelIsCokernel _)
    (Cofork.ext (X.cokernelIsoCycles f g fg h n) (by
      simp [← cancel_mono (X.iCycles f g n)]))

Depends on / 依赖: Cofork, Cofork.ext, IsColimit, IsColimit.ofIsoColimit, ShortComplex, ShortComplex.exact_of_g_is_cokernel, X.cokernelIsoCycles, X.iCycles, cancel_mono, cokernelIsCokernel, cokernelIsoCycles, exact_of_g_is_cokernel, iCycles, ofIsoColimit
-/
lemma cokernelSequenceCycles_exact (n : Int) :
    (X.cokernelSequenceCycles f g fg h n).Exact := by
  apply ShortComplex.exact_of_g_is_cokernel
  exact IsColimit.ofIsoColimit (cokernelIsCokernel _)
    (Cofork.ext (X.cokernelIsoCycles f g fg h n) (by
      simp [← cancel_mono (X.iCycles f g n)]))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `kernelSequenceOpcycles_exact` / 引理 `kernelSequenceOpcycles_exact`

English:
lemma kernelSequenceOpcycles_exact
  given: (n : Int)
  proof: by
  apply ShortComplex.exact_of_f_is_kernel
  exact IsLimit.ofIsoLimit (kernelIsKernel _)
    (Iso.symm (Fork.ext (X.opcyclesIsoKernel f g fg h n) (by
      simp [← cancel_epi (X.pOpcycles f g n)])))

中文:
引理 kernelSequenceOpcycles_exact
  条件: (n : 整数)
  证明: by
  apply ShortComplex.exact_of_f_is_kernel
  exact IsLimit.ofIsoLimit (kernelIsKernel _)
    (Iso.symm (Fork.ext (X.opcyclesIsoKernel f g fg h n) (by
      simp [← cancel_epi (X.pOpcycles f g n)])))

Depends on / 依赖: Fork.ext, IsLieAbelian, IsLimit, IsLimit.ofIsoLimit, IsSolvable, Iso.symm, LieIdeal, LieIdeal.topEquiv, ShortComplex, ShortComplex.exact_of_f_is_kernel, X.opcyclesIsoKernel, X.pOpcycles, abelian_iff_derived_one_eq_bot, cancel_epi, exact_of_f_is_kernel, infer_instance, kernelIsKernel, lie_abelian_iff_equiv_lie_abelian, ofAbelianIsSolvable, ofIsoLimit
-/
lemma kernelSequenceOpcycles_exact (n : Int) :
    (X.kernelSequenceOpcycles f g fg h n).Exact := by
  apply ShortComplex.exact_of_f_is_kernel
  exact IsLimit.ofIsoLimit (kernelIsKernel _)
    (Iso.symm (Fork.ext (X.opcyclesIsoKernel f g fg h n) (by
      simp [← cancel_epi (X.pOpcycles f g n)])))

/--
lemma `isIso_toCycles` / 引理 `isIso_toCycles`

English:
lemma isIso_toCycles
  given: (n : Int) (hf : IsZero ((X.H n).obj (mk₁ f)))
  proof: by
  have : Mono (X.toCycles f g fg h n) :=
    (X.cokernelSequenceCycles_exact f g fg h n).mono_g (hf.eq_of_src _ _)
  exact Balanced.isIso_of_mono_of_epi _

中文:
引理 isIso_toCycles
  条件: (n : 整数) (hf : IsZero ((X.H n).obj (mk₁ f)))
  证明: by
  have : Mono (X.toCycles f g fg h n) :=
    (X.cokernelSequenceCycles_exact f g fg h n).mono_g (hf.eq_of_src _ _)
  exact Balanced.isIso_of_mono_of_epi _

Depends on / 依赖: Balanced, Balanced.isIso_of_mono_of_epi, X.cokernelSequenceCycles_exact, X.toCycles, cokernelSequenceCycles_exact, eq_of_src, hf.eq_of_src, isIso_of_mono_of_epi, mono_g, toCycles
-/
lemma isIso_toCycles (n : Int) (hf : IsZero ((X.H n).obj (mk₁ f))) :
    IsIso (X.toCycles f g fg h n) := by
  have : Mono (X.toCycles f g fg h n) :=
    (X.cokernelSequenceCycles_exact f g fg h n).mono_g (hf.eq_of_src _ _)
  exact Balanced.isIso_of_mono_of_epi _

/--
lemma `isIso_fromOpcycles` / 引理 `isIso_fromOpcycles`

English:
lemma isIso_fromOpcycles
  given: (n : Int) (hg : IsZero ((X.H n).obj (mk₁ g)))
  proof: by
  have : Epi (X.fromOpcycles f g fg h n) :=
    (X.kernelSequenceOpcycles_exact f g fg h n).epi_f (hg.eq_of_tgt _ _)
  exact Balanced.isIso_of_mono_of_epi _

中文:
引理 isIso_fromOpcycles
  条件: (n : 整数) (hg : IsZero ((X.H n).obj (mk₁ g)))
  证明: by
  have : Epi (X.fromOpcycles f g fg h n) :=
    (X.kernelSequenceOpcycles_exact f g fg h n).epi_f (hg.eq_of_tgt _ _)
  exact Balanced.isIso_of_mono_of_epi _

Depends on / 依赖: Balanced, Balanced.isIso_of_mono_of_epi, X.fromOpcycles, X.kernelSequenceOpcycles_exact, epi_f, eq_of_tgt, fromOpcycles, hg.eq_of_tgt, isIso_of_mono_of_epi, kernelSequenceOpcycles_exact
-/
lemma isIso_fromOpcycles (n : Int) (hg : IsZero ((X.H n).obj (mk₁ g))) :
    IsIso (X.fromOpcycles f g fg h n) := by
  have : Epi (X.fromOpcycles f g fg h n) :=
    (X.kernelSequenceOpcycles_exact f g fg h n).epi_f (hg.eq_of_tgt _ _)
  exact Balanced.isIso_of_mono_of_epi _

section

variable {A : C} {n : Int} (x : (X.H n).obj (mk₁ fg) ⟶ A)
  (hx : (X.H n).map (twoδ₂Toδ₁ f g fg h) ≫ x = 0)

/--
Definition of `descCycles` / `descCycles` 的定义

English:
definition descCycles
  signature: :
  body: (X.cokernelSequenceCycles_exact f g fg h n).desc x hx

@[reassoc (attr := simp)]

中文:
定义 descCycles
  签名: :
  定义体: (X.cokernelSequenceCycles_exact f g fg h n).desc x hx

@[reassoc (attr := simp)]

Depends on / 依赖: X.cokernelSequenceCycles_exact, cokernelSequenceCycles_exact
-/
noncomputable def descCycles :
    X.cycles f g n ⟶ A :=
  (X.cokernelSequenceCycles_exact f g fg h n).desc x hx

@[reassoc (attr := simp)]
/--
lemma `toCycles_descCycles` / 引理 `toCycles_descCycles`

English:
lemma toCycles_descCycles
  proof: (X.cokernelSequenceCycles_exact f g fg h n).g_desc x hx

中文:
引理 toCycles_descCycles
  证明: (X.cokernelSequenceCycles_exact f g fg h n).g_desc x hx

Depends on / 依赖: X.cokernelSequenceCycles_exact, cokernelSequenceCycles_exact, g_desc
-/
lemma toCycles_descCycles :
    X.toCycles f g fg h n ≫ X.descCycles f g fg h x hx = x :=
  (X.cokernelSequenceCycles_exact f g fg h n).g_desc x hx

end

section

variable {A : C} {n : Int} (x : A ⟶ (X.H n).obj (mk₁ fg))
  (hx : x ≫ (X.H n).map (twoδ₁Toδ₀ f g fg h) = 0)

/--
Definition of `liftOpcycles` / `liftOpcycles` 的定义

English:
definition liftOpcycles
  signature: :
  body: (X.kernelSequenceOpcycles_exact f g fg h n).lift x hx

@[reassoc (attr := simp)]

中文:
定义 liftOpcycles
  签名: :
  定义体: (X.kernelSequenceOpcycles_exact f g fg h n).lift x hx

@[reassoc (attr := simp)]

Depends on / 依赖: X.kernelSequenceOpcycles_exact, kernelSequenceOpcycles_exact
-/
noncomputable def liftOpcycles :
    A ⟶ X.opcycles f g n :=
  (X.kernelSequenceOpcycles_exact f g fg h n).lift x hx

@[reassoc (attr := simp)]
/--
lemma `liftOpcycles_fromOpcycles` / 引理 `liftOpcycles_fromOpcycles`

English:
lemma liftOpcycles_fromOpcycles
  proof: (X.kernelSequenceOpcycles_exact f g fg h n).lift_f x hx

中文:
引理 liftOpcycles_fromOpcycles
  证明: (X.kernelSequenceOpcycles_exact f g fg h n).lift_f x hx

Depends on / 依赖: X.kernelSequenceOpcycles_exact, kernelSequenceOpcycles_exact, lift_f
-/
lemma liftOpcycles_fromOpcycles :
    X.liftOpcycles f g fg h x hx ≫ X.fromOpcycles f g fg h n = x :=
  (X.kernelSequenceOpcycles_exact f g fg h n).lift_f x hx

end

end

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ : Int)
/--
Definition of `δToCycles` / `δToCycles` 的定义

English:
definition δToCycles
  signature: (hn₁ : n₀ + 1 = n₁ := by lia)
  body: X.liftCycles f₁ f₂ _ _ rfl (X.δ f₂ f₃ n₀ n₁) (by simp)

@[reassoc (attr := simp)]

中文:
定义 δToCycles
  签名: (hn₁ : n₀ + 1 = n₁ := by lia)
  定义体: X.liftCycles f₁ f₂ _ _ rfl (X.δ f₂ f₃ n₀ n₁) (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: X.cycles, X.liftCycles, cycles, liftCycles
-/
noncomputable def δToCycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.H n₀).obj (mk₁ f₃) ⟶ X.cycles f₁ f₂ n₁ :=
  X.liftCycles f₁ f₂ _ _ rfl (X.δ f₂ f₃ n₀ n₁) (by simp)

@[reassoc (attr := simp)]
/--
lemma `δToCycles_iCycles` / 引理 `δToCycles_iCycles`

English:
lemma δToCycles_iCycles
  given: (hn₁ : n₀ + 1 = n₁)
  proof: by
  simp only [δToCycles, liftCycles_i]

@[reassoc (attr := simp)]

中文:
引理 δToCycles_iCycles
  条件: (hn₁ : n₀ + 1 = n₁)
  证明: by
  simp only [δToCycles, liftCycles_i]

@[reassoc (attr := simp)]

Depends on / 依赖: liftCycles_i
-/
lemma δToCycles_iCycles (hn₁ : n₀ + 1 = n₁) :
    X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ ≫ X.iCycles f₁ f₂ n₁ =
      X.δ f₂ f₃ n₀ n₁ hn₁ := by
  simp only [δToCycles, liftCycles_i]

@[reassoc (attr := simp)]
/--
lemma `δ_toCycles` / 引理 `δ_toCycles`

English:
lemma δ_toCycles
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  rw [← cancel_mono (X.iCycles f₁ f₂ n₁)]; rw [Category.assoc]; rw [toCycles_i]; rw [δToCycles_iCycles]; rw [← X.δ_naturality f₁₂ f₃ f₂ f₃ (twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂) (𝟙 _) n₀ n₁]; rw [Functor.map_id]; rw [Category.id_comp]

中文:
引理 δ_toCycles
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  rw [← cancel_mono (X.iCycles f₁ f₂ n₁)]; rw [Category.assoc]; rw [toCycles_i]; rw [δToCycles_iCycles]; rw [← X.δ_naturality f₁₂ f₃ f₂ f₃ (twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂) (𝟙 _) n₀ n₁]; rw [Functor.map_id]; rw [Category.id_comp]

Depends on / 依赖: Category, Category.assoc, Category.id_comp, Functor, Functor.map_id, X.iCycles, X.toCycles, cancel_mono, iCycles, id_comp, map_id, toCycles, toCycles_i
-/
lemma δ_toCycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f₁₂ f₃ n₀ n₁ hn₁ ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ =
      X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ := by
  rw [← cancel_mono (X.iCycles f₁ f₂ n₁)]; rw [Category.assoc]; rw [toCycles_i]; rw [δToCycles_iCycles]; rw [← X.δ_naturality f₁₂ f₃ f₂ f₃ (twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂) (𝟙 _) n₀ n₁]; rw [Functor.map_id]; rw [Category.id_comp]

/--
Definition of `δFromOpcycles` / `δFromOpcycles` 的定义

English:
definition δFromOpcycles
  signature: (hn₁ : n₀ + 1 = n₁ := by lia)
  body: X.descOpcycles f₂ f₃ (n₀ - 1) n₀ (by lia) (X.δ f₁ f₂ n₀ n₁ hn₁) (by simp)

@[reassoc (attr := simp)]

中文:
定义 δFromOpcycles
  签名: (hn₁ : n₀ + 1 = n₁ := by lia)
  定义体: X.descOpcycles f₂ f₃ (n₀ - 1) n₀ (by lia) (X.δ f₁ f₂ n₀ n₁ hn₁) (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: X.descOpcycles, X.opcycles, descOpcycles, opcycles
-/
noncomputable def δFromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.opcycles f₂ f₃ n₀ ⟶ (X.H n₁).obj (mk₁ f₁) :=
  X.descOpcycles f₂ f₃ (n₀ - 1) n₀ (by lia) (X.δ f₁ f₂ n₀ n₁ hn₁) (by simp)

@[reassoc (attr := simp)]
/--
lemma `pOpcycles_δFromOpcycles` / 引理 `pOpcycles_δFromOpcycles`

English:
lemma pOpcycles_δFromOpcycles
  given: (hn₁ : n₀ + 1 = n₁)
  proof: by
  simp only [δFromOpcycles, p_descOpcycles]

@[reassoc (attr := simp)]

中文:
引理 pOpcycles_δFromOpcycles
  条件: (hn₁ : n₀ + 1 = n₁)
  证明: by
  simp only [δFromOpcycles, p_descOpcycles]

@[reassoc (attr := simp)]

Depends on / 依赖: p_descOpcycles
-/
lemma pOpcycles_δFromOpcycles (hn₁ : n₀ + 1 = n₁) :
    X.pOpcycles f₂ f₃ n₀ ≫ X.δFromOpcycles f₁ f₂ f₃ n₀ n₁ hn₁ =
      X.δ f₁ f₂ n₀ n₁ hn₁ := by
  simp only [δFromOpcycles, p_descOpcycles]

@[reassoc (attr := simp)]
/--
lemma `fromOpcyles_δ` / 引理 `fromOpcyles_δ`

English:
lemma fromOpcyles_δ
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  rw [← cancel_epi (X.pOpcycles f₂ f₃ n₀)]; rw [p_fromOpcycles_assoc]; rw [pOpcycles_δFromOpcycles]; rw [X.δ_naturality f₁ f₂ f₁ f₂₃ (𝟙 _) (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) n₀ n₁]; rw [Functor.map_id]; rw [Category.comp_id]

中文:
引理 fromOpcyles_δ
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  rw [← cancel_epi (X.pOpcycles f₂ f₃ n₀)]; rw [p_fromOpcycles_assoc]; rw [pOpcycles_δFromOpcycles]; rw [X.δ_naturality f₁ f₂ f₁ f₂₃ (𝟙 _) (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) n₀ n₁]; rw [Functor.map_id]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, Functor, Functor.map_id, X.fromOpcycles, X.pOpcycles, cancel_epi, comp_id, fromOpcycles, map_id, pOpcycles, p_fromOpcycles_assoc
-/
lemma fromOpcyles_δ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₀ ≫ X.δ f₁ f₂₃ n₀ n₁ hn₁ =
      X.δFromOpcycles f₁ f₂ f₃ n₀ n₁ hn₁ := by
  rw [← cancel_epi (X.pOpcycles f₂ f₃ n₀)]; rw [p_fromOpcycles_assoc]; rw [pOpcycles_δFromOpcycles]; rw [X.δ_naturality f₁ f₂ f₁ f₂₃ (𝟙 _) (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) n₀ n₁]; rw [Functor.map_id]; rw [Category.comp_id]

end

end SpectralObject

end Abelian

end CategoryTheory
