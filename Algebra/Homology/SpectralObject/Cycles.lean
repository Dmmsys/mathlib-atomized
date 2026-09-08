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

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ)

/-- The kernel of `δ : H^n(g) ⟶ H^{n+1}(f)`. In the documentation,
this may be shortened as `Z^n(f, g)` -/
/-
**CategoryTheory.Abelian.SpectralObject.cycles** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Abelian.SpectralObject`。
形式化陈述：cycles : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of `δ : H^n(g) ⟶ H^{n+1}(f)`. In the documentation,
this may be shortened as `Z^n(f, g)`
-/
noncomputable def cycles : C := kernel (X.δ f g n (n + 1))

/-- The cokernel of `δ : H^{n-1}(g) ⟶ H^n(g)`. In the documentation,
this may be shortened as `opZ^n₁(f, g)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.opcycles** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Abelian.SpectralObject`。
形式化陈述：opcycles : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel of `δ : H^{n-1}(g) ⟶ H^n(g)`. In the documentation,
this may be shortened as `opZ^n₁(f, g)`.
-/
noncomputable def opcycles : C := cokernel (X.δ f g (n - 1) n)

/-- The inclusion `Z^n(f, g) ⟶ H^n(g)` of the kernel of `δ`. -/
/-
**CategoryTheory.Abelian.SpectralObject.iCycles** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Abelian.SpectralObject`。
形式化陈述：iCycles : X.cycles f g n ⟶ (X.H n).obj (mk₁ g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `Z^n(f, g) ⟶ H^n(g)` of the kernel of `δ`.
-/
noncomputable def iCycles :
    X.cycles f g n ⟶ (X.H n).obj (mk₁ g) :=
  kernel.ι _

/-- The projection `H^n(f) ⟶ opZ^n(f, g)` to the cokernel of `δ`. -/
/-
**CategoryTheory.Abelian.SpectralObject.pOpcycles** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Abelian.SpectralObject`。
形式化陈述：pOpcycles : (X.H n).obj (mk₁ f) ⟶ X.opcycles f g n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection `H^n(f) ⟶ opZ^n(f, g)` to the cokernel of `δ`.
-/
noncomputable def pOpcycles :
    (X.H n).obj (mk₁ f) ⟶ X.opcycles f g n :=
  cokernel.π _

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (X.iCycles f g n) := by
  dsimp [iCycles]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi (X.pOpcycles f g n) := by
  dsimp [pOpcycles]
  infer_instance
/-
**CategoryTheory.Abelian.SpectralObject.isZero_opcycles** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：isZero_opcycles (h : IsZero ((X.H n).obj (mk₁ f))) : IsZero (X.opcycles f 
g n)
参数：h : IsZero ((X.H n).obj (mk₁ f))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiPOpcycles`：∀ {C : Type u_1}
 {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
-/
lemma isZero_opcycles (h : IsZero ((X.H n).obj (mk₁ f))) :
    IsZero (X.opcycles f g n) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_epi (X.pOpcycles ..)]
  apply h.eq_of_src
/-
**CategoryTheory.Abelian.SpectralObject.isZero_cycles** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Abelian.SpectralObject`。
形式化陈述：isZero_cycles (h : IsZero ((X.H n).obj (mk₁ g))) : IsZero (X.cycles f g n)
参数：h : IsZero ((X.H n).obj (mk₁ g))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instMonoICycles`：∀ {C : Type u_1} 
{ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
-/
lemma isZero_cycles (h : IsZero ((X.H n).obj (mk₁ g))) :
    IsZero (X.cycles f g n) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (X.iCycles ..)]
  apply h.eq_of_tgt

end

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : ℤ)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.iCycles_** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iCycles_δ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.iCycles f g n₀ ≫ X.δ f g n₀ n₁ hn₁ = 0 := by
  subst hn₁
  simp [iCycles]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_pOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f g n₀ n₁ hn₁ ≫ X.pOpcycles f g n₁ = 0 := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  simp [pOpcycles]

/-- The short complex which expresses `X.cycles` as the kernel of `X.δ`. -/
@[simps]
/-
**CategoryTheory.Abelian.SpectralObject.kernelSequenceCycles** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：kernelSequenceCycles (hn₁ : n₀ + 1 = n₁
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.iCycles_δ`：iCycles_δ (hn₁ : n₀ + 1
 = n₁

--- 原说明 ---
The short complex which expresses `X.cycles` as the kernel of `X.δ`.
-/
noncomputable def kernelSequenceCycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.iCycles_δ f g n₀ n₁ hn₁)

/-- The short complex which expresses `X.opcycles` as the cokernel of `X.δ`. -/
@[simps]
/-
**CategoryTheory.Abelian.SpectralObject.cokernelSequenceOpcycles** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cokernelSequenceOpcycles (hn₁ : n₀ + 1 = n₁
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.δ_pOpcycles`：δ_pOpcycles (hn₁ : n₀
 + 1 = n₁

--- 原说明 ---
The short complex which expresses `X.opcycles` as the cokernel of `X.δ`.
-/
noncomputable def cokernelSequenceOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.δ_pOpcycles f g n₀ n₁ hn₁)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hn₁ : n₀ + 1 = n₁) :
    Mono (X.kernelSequenceCycles f g n₀ n₁ hn₁).f := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hn₁ : n₀ + 1 = n₁) :
    Epi (X.cokernelSequenceOpcycles f g n₀ n₁ hn₁).g := by
  dsimp
  infer_instance
/-
**CategoryTheory.Abelian.SpectralObject.kernelSequenceCycles_exact** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：kernelSequenceCycles_exact (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.exact_kernel`：exact_kernel {X Y : C} (f : X 
⟶ Y) : (ShortComplex.mk (kernel.ι f) f (by simp)).Exact
-/
lemma kernelSequenceCycles_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.kernelSequenceCycles f g n₀ n₁ hn₁).Exact := by
  subst hn₁
  apply ShortComplex.exact_kernel
/-
**CategoryTheory.Abelian.SpectralObject.cokernelSequenceOpcycles_exact** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cokernelSequenceOpcycles_exact (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.exact_cokernel`：exact_cokernel {X Y : C} (f 
: X ⟶ Y) : (ShortComplex.mk f (cokernel.π f) (by simp)).Exact
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma cokernelSequenceOpcycles_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.cokernelSequenceOpcycles f g n₀ n₁ hn₁).Exact := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  apply ShortComplex.exact_cokernel

section

variable (hn₁ : n₀ + 1 = n₁) {A : C} (x : A ⟶ (X.H n₀).obj (mk₁ g))
    (hx : x ≫ X.δ f g n₀ n₁ hn₁ = 0)

/-- Constructor for morphisms to `X.cycles`. -/
/-
**CategoryTheory.Abelian.SpectralObject.liftCycles** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Abelian.SpectralObject`。
形式化陈述：liftCycles : A ⟶ X.cycles f g n₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms to `X.cycles`.
-/
noncomputable def liftCycles :
    A ⟶ X.cycles f g n₀ :=
  kernel.lift _ x (by subst hn₁; exact hx)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.liftCycles_i** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Abelian.SpectralObject`。
形式化陈述：liftCycles_i : X.liftCycles f g n₀ n₁ hn₁ x hx ≫ X.iCycles f g n₀ = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
-/
lemma liftCycles_i : X.liftCycles f g n₀ n₁ hn₁ x hx ≫ X.iCycles f g n₀ = x := by
  apply kernel.lift_ι

end

section

variable (hn₁ : n₀ + 1 = n₁) {A : C} (x : (X.H n₁).obj (mk₁ f) ⟶ A)
    (hx : X.δ f g n₀ n₁ hn₁ ≫ x = 0)

/-- Constructor for morphisms from `X.opcycles`. -/
/-
**CategoryTheory.Abelian.SpectralObject.descOpcycles** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Abelian.SpectralObject`。
形式化陈述：descOpcycles : X.opcycles f g n₁ ⟶ A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms from `X.opcycles`.
-/
noncomputable def descOpcycles :
    X.opcycles f g n₁ ⟶ A :=
  cokernel.desc _ x (by
    obtain rfl : n₀ = n₁ -1 := by lia
    exact hx)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.p_descOpcycles** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：p_descOpcycles : X.pOpcycles f g n₁ ≫ X.descOpcycles f g n₀ n₁ hn₁ x hx = 
x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
-/
lemma p_descOpcycles : X.pOpcycles f g n₁ ≫ X.descOpcycles f g n₀ n₁ hn₁ x hx = x := by
  apply cokernel.π_desc

end

end

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

/-- The functoriality of `X.cycles` with respect to morphisms in
`ComposableArrows ι 2`. -/
/-
**CategoryTheory.Abelian.SpectralObject.cyclesMap** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Abelian.SpectralObject`。
形式化陈述：cyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (n : Int) : X.cycles f g n ⟶ X.cycles 
f' g' n
参数：α : mk₂ f g ⟶ mk₂ f' g'；n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functoriality of `X.cycles` with respect to morphisms in
`ComposableArrows ι 2`.
-/
noncomputable def cyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (n : ℤ) :
    X.cycles f g n ⟶ X.cycles f' g' n :=
  X.liftCycles _ _ _ _ rfl
    (X.iCycles f g n ≫ (X.H n).map (homMk₁ (α.app 1) (α.app 2)
      (naturality' α 1 2))) (by
      rw [Category.assoc, X.δ_naturality f g f' g'
        (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
          (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) n (n + 1),
        iCycles_δ_assoc _ _ _ _ _, zero_comp])

@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.cyclesMap_i** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Abelian.SpectralObject`。
形式化陈述：cyclesMap_i (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ g ⟶ mk₁ g') (n : Int) (hβ :
 β = homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)
参数：α : mk₂ f g ⟶ mk₂ f' g'；β : mk₁ g ⟶ mk₁ g'；n : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.liftCycles_i`：liftCycles_i : X.lif
tCycles f g n₀ n₁ hn₁ x hx ≫ X.iCycles f g n₀ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma cyclesMap_i (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ g ⟶ mk₁ g') (n : ℤ)
    (hβ : β = homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2) := by cat_disch) :
    X.cyclesMap f g f' g' α n ≫ X.iCycles f' g' n =
      X.iCycles f g n ≫ (X.H n).map β := by
  subst hβ
  simp [cyclesMap]

@[simp]
/-
**CategoryTheory.Abelian.SpectralObject.cyclesMap_id** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cyclesMap_id (n : Int) : X.cyclesMap f g f g (𝟙 _) n = 𝟙 _
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instMonoICycles`：∀ {C : Type u_1} 
{ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cyclesMap_i`：cyclesMap_i (α : mk₂ 
f g ⟶ mk₂ f' g') (β : mk₁ g ⟶ mk₁ g') (n : Int) (hβ : β = homMk₁ (α.app 1) (α.ap
p 2) (naturality' α 1 2)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₁`：hom_ext₁ {F G : ComposableArro
ws C 1} {φ φ' : F ⟶ G} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
 φ = φ'
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma cyclesMap_id (n : ℤ) :
    X.cyclesMap f g f g (𝟙 _) n = 𝟙 _ := by
  rw [← cancel_mono (X.iCycles f g n), X.cyclesMap_i f g f g (𝟙 _) (𝟙 _) n,
    Functor.map_id, Category.comp_id, Category.id_comp]

@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.cyclesMap_comp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'') (α
'' : mk₂ f g ⟶ mk₂ f'' g'') (n : Int) (h : α ≫ α' = α''
参数：α : mk₂ f g ⟶ mk₂ f' g'；α' : mk₂ f' g' ⟶ mk₂ f'' g''；α'' : mk₂ f g ⟶ mk₂ f'' 
g''；n : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instMonoICycles`：∀ {C : Type u_1} 
{ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cyclesMap_i`：cyclesMap_i (α : mk₂ 
f g ⟶ mk₂ f' g') (β : mk₁ g ⟶ mk₁ g') (n : Int) (hβ : β = homMk₁ (α.app 1) (α.ap
p 2) (naturality' α 1 2)
· 使用定理 `CategoryTheory.Abelian.SpectralObject.cyclesMap_i_assoc`：∀ {C : Type u_1
} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₁`：hom_ext₁ {F G : ComposableArro
ws C 1} {φ φ' : F ⟶ G} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
 φ = φ'
-/
lemma cyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
    (α'' : mk₂ f g ⟶ mk₂ f'' g'') (n : ℤ) (h : α ≫ α' = α'' := by cat_disch) :
    X.cyclesMap f g f' g' α n ≫ X.cyclesMap f' g' f'' g'' α' n =
      X.cyclesMap f g f'' g'' α'' n := by
  subst h
  rw [← cancel_mono (X.iCycles f'' g'' n), Category.assoc,
    X.cyclesMap_i f' g' f'' g'' α' _ n rfl,
    X.cyclesMap_i_assoc f g f' g' α _ n rfl,
    ← Functor.map_comp]
  exact (X.cyclesMap_i _ _ _ _ _ _ _).symm

/-- The functoriality of `X.opcycles` with respect to morphisms in
`ComposableArrows ι 2`. -/
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesMap** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Abelian.SpectralObject`。
形式化陈述：opcyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (n : Int) : X.opcycles f g n ⟶ X.opc
ycles f' g' n
参数：α : mk₂ f g ⟶ mk₂ f' g'；n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functoriality of `X.opcycles` with respect to morphisms in
`ComposableArrows ι 2`.
-/
noncomputable def opcyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (n : ℤ) :
    X.opcycles f g n ⟶ X.opcycles f' g' n :=
  X.descOpcycles _ _ (n - 1) n (by lia)
    ((X.H n).map (homMk₁ (by exact α.app 0) (by exact α.app 1)
      (naturality' α 0 1)) ≫ X.pOpcycles f' g' n) (by
      rw [← X.δ_naturality_assoc f g f' g'
        (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
        (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) _ _,
        δ_pOpcycles _ _ _ _ _, comp_zero])

@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.p_opcyclesMap** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Abelian.SpectralObject`。
形式化陈述：p_opcyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ f ⟶ mk₁ f') (n : Int) (hβ
 : β = homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1)
参数：α : mk₂ f g ⟶ mk₂ f' g'；β : mk₁ f ⟶ mk₁ f'；n : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.p_descOpcycles`：p_descOpcycles : X
.pOpcycles f g n₁ ≫ X.descOpcycles f g n₀ n₁ hn₁ x hx = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma p_opcyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ f ⟶ mk₁ f') (n : ℤ)
    (hβ : β = homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1) := by cat_disch) :
    X.pOpcycles f g n ≫ X.opcyclesMap f g f' g' α n =
      (X.H n).map β ≫ X.pOpcycles f' g' n := by
  subst hβ
  simp [opcyclesMap]

@[simp]
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesMap_id** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：opcyclesMap_id (n : Int) : X.opcyclesMap f g f g (𝟙 _) n = 𝟙 _
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiPOpcycles`：∀ {C : Type u_1}
 {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.p_opcyclesMap`：p_opcyclesMap (α : 
mk₂ f g ⟶ mk₂ f' g') (β : mk₁ f ⟶ mk₁ f') (n : Int) (hβ : β = homMk₁ (α.app 0) (
α.app 1) (naturality' α 0 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₁`：hom_ext₁ {F G : ComposableArro
ws C 1} {φ φ' : F ⟶ G} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
 φ = φ'
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma opcyclesMap_id (n : ℤ) :
    X.opcyclesMap f g f g (𝟙 _) n = 𝟙 _ := by
  rw [← cancel_epi (X.pOpcycles f g n),
    X.p_opcyclesMap f g f g (𝟙 _) (𝟙 _),
    Functor.map_id, Category.comp_id, Category.id_comp]
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesMap_comp** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：opcyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'') 
(α'' : mk₂ f g ⟶ mk₂ f'' g'') (n : Int) (h : α ≫ α' = α''
参数：α : mk₂ f g ⟶ mk₂ f' g'；α' : mk₂ f' g' ⟶ mk₂ f'' g''；α'' : mk₂ f g ⟶ mk₂ f'' 
g''；n : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiPOpcycles`：∀ {C : Type u_1}
 {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `CategoryTheory.Abelian.SpectralObject.p_opcyclesMap_assoc`：∀ {C : Type u
_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.p_opcyclesMap`：p_opcyclesMap (α : 
mk₂ f g ⟶ mk₂ f' g') (β : mk₁ f ⟶ mk₁ f') (n : Int) (hβ : β = homMk₁ (α.app 0) (
α.app 1) (naturality' α 0 1)
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₁`：hom_ext₁ {F G : ComposableArro
ws C 1} {φ φ' : F ⟶ G} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
 φ = φ'
-/
lemma opcyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
    (α'' : mk₂ f g ⟶ mk₂ f'' g'') (n : ℤ) (h : α ≫ α' = α'' := by cat_disch) :
    X.opcyclesMap f g f' g' α n ≫ X.opcyclesMap f' g' f'' g'' α' n =
      X.opcyclesMap f g f'' g'' α'' n := by
  subst h
  rw [← cancel_epi (X.pOpcycles f g n),
    X.p_opcyclesMap_assoc f g f' g' α _,
    X.p_opcyclesMap f' g' f'' g'' α' _,
    ← Functor.map_comp_assoc]
  exact (X.p_opcyclesMap _ _ _ _ _ _ _ (by cat_disch)).symm

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

/-- `X.cycles` also identifies to a cokernel. More precisely,
`Z^n(f, g)` identifies to the cokernel of `H^n(f) ⟶ H^n(f ≫ g)` -/
/-
**CategoryTheory.Abelian.SpectralObject.cokernelIsoCycles** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cokernelIsoCycles (n : Int) : cokernel ((X.H n).map (twoδ₂Toδ₁ f g fg h)) 
≅ X.cycles f g n
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X.cycles` also identifies to a cokernel. More precisely,
`Z^n(f, g)` identifies to the cokernel of `H^n(f) ⟶ H^n(f ≫ g)`
-/
noncomputable def cokernelIsoCycles (n : ℤ) :
    cokernel ((X.H n).map (twoδ₂Toδ₁ f g fg h)) ≅ X.cycles f g n :=
  (X.composableArrows₅_exact f g fg h n (n + 1)).cokerIsoKer 0

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.cokernelIsoCycles_hom_fac** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cokernelIsoCycles_hom_fac (n : Int) : cokernel.π _ ≫ (X.cokernelIsoCycles 
f g fg h n).hom ≫ X.iCycles f g n = (X.H n).map (twoδ₁Toδ₀ f g fg h)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.Exact.cokerIsoKer_hom_fac`：cokerIsoKer_h
om_fac (k : Nat) (hk : k <= n
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用引理 `CategoryTheory.Abelian.SpectralObject.composableArrows₅_exact`：composabl
eArrows₅_exact (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
-/
lemma cokernelIsoCycles_hom_fac (n : ℤ) :
    cokernel.π _ ≫ (X.cokernelIsoCycles f g fg h n).hom ≫
      X.iCycles f g n = (X.H n).map (twoδ₁Toδ₀ f g fg h) :=
  (X.composableArrows₅_exact f g fg h n (n + 1)).cokerIsoKer_hom_fac 0

/-- `X.opcycles` also identifies to a kernel. More precisely,
`opZ(f, g)` identifies to the kernel of `H^n(f ≫ g) ⟶ H^n(g)` -/
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesIsoKernel** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：opcyclesIsoKernel (n : Int) : X.opcycles f g n ≅ kernel ((X.H n).map (twoδ
₁Toδ₀ f g fg h))
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X.opcycles` also identifies to a kernel. More precisely,
`opZ(f, g)` identifies to the kernel of `H^n(f ≫ g) ⟶ H^n(g)`
-/
noncomputable def opcyclesIsoKernel (n : ℤ) :
    X.opcycles f g n ≅ kernel ((X.H n).map (twoδ₁Toδ₀ f g fg h)) :=
  (X.composableArrows₅_exact f g fg h (n - 1) n).cokerIsoKer 2

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesIsoKernel_hom_fac** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：opcyclesIsoKernel_hom_fac (n : Int) : X.pOpcycles f g n ≫ (X.opcyclesIsoKe
rnel f g fg h n).hom ≫ kernel.ι _ = (X.H n).map (twoδ₂Toδ₁ f g fg h)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.Exact.cokerIsoKer_hom_fac`：cokerIsoKer_h
om_fac (k : Nat) (hk : k <= n
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用引理 `CategoryTheory.Abelian.SpectralObject.composableArrows₅_exact`：composabl
eArrows₅_exact (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
-/
lemma opcyclesIsoKernel_hom_fac (n : ℤ) :
    X.pOpcycles f g n ≫ (X.opcyclesIsoKernel f g fg h n).hom ≫
      kernel.ι _ = (X.H n).map (twoδ₂Toδ₁ f g fg h) :=
  (X.composableArrows₅_exact f g fg h (n - 1) n).cokerIsoKer_hom_fac 2

/-- The map `H^n(fg) ⟶ H^n(g)` factors through `Z^n(f, g)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.toCycles** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Abelian.SpectralObject`。
形式化陈述：toCycles (n : Int) : (X.H n).obj (mk₁ fg) ⟶ X.cycles f g n
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `H^n(fg) ⟶ H^n(g)` factors through `Z^n(f, g)`.
-/
noncomputable def toCycles (n : ℤ) :
    (X.H n).obj (mk₁ fg) ⟶ X.cycles f g n :=
  kernel.lift _ ((X.H n).map (twoδ₁Toδ₀ f g fg h)) (by simp)
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : Epi (X.toCycles f g fg h n) :=
  (ShortComplex.exact_iff_epi_kernel_lift _).1 (X.exact₃ f g fg h n (n + 1))

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.toCycles_i** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Abelian.SpectralObject`。
形式化陈述：toCycles_i (n : Int) : X.toCycles f g fg h n ≫ X.iCycles f g n = (X.H n).m
ap (twoδ₁Toδ₀ f g fg h)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
-/
lemma toCycles_i (n : ℤ) :
    X.toCycles f g fg h n ≫ X.iCycles f g n = (X.H n).map (twoδ₁Toδ₀ f g fg h) :=
  kernel.lift_ι ..

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.toCycles_cyclesMap** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：toCycles_cyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg') (n : I
nt) (hβ₀ : β.app 0 = α.app 0
参数：α : mk₂ f g ⟶ mk₂ f' g'；β : mk₁ fg ⟶ mk₁ fg'；n : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instMonoICycles`：∀ {C : Type u_1} 
{ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.toCycles_i`：toCycles_i (n : Int) :
 X.toCycles f g fg h n ≫ X.iCycles f g n = (X.H n).map (twoδ₁Toδ₀ f g fg h)
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cyclesMap_i`：cyclesMap_i (α : mk₂ 
f g ⟶ mk₂ f' g') (β : mk₁ g ⟶ mk₁ g') (n : Int) (hβ : β = homMk₁ (α.app 1) (α.ap
p 2) (naturality' α 1 2)
· 使用定理 `CategoryTheory.Abelian.SpectralObject.toCycles_i_assoc`：∀ {C : Type u_1}
 {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₁`：hom_ext₁ {F G : ComposableArro
ws C 1} {φ φ' : F ⟶ G} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
 φ = φ'
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma toCycles_cyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg') (n : ℤ)
    (hβ₀ : β.app 0 = α.app 0 := by cat_disch) (hβ₁ : β.app 1 = α.app 2 := by cat_disch) :
    X.toCycles f g fg h n ≫ X.cyclesMap f g f' g' α n =
      (X.H n).map β ≫ X.toCycles f' g' fg' h' n := by
  rw [← cancel_mono (X.iCycles f' g' n), Category.assoc, Category.assoc, toCycles_i,
    X.cyclesMap_i f g f' g' α (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) n rfl,
    toCycles_i_assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext
  · dsimp
    rw [hβ₀]
    exact naturality' α 0 1
  · dsimp
    rw [hβ₁, Category.comp_id, Category.id_comp]

/-- The map `H^n(f) ⟶ H^n(f ≫ g)` factors through `opZ^n(f, g)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.fromOpcycles** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Abelian.SpectralObject`。
形式化陈述：fromOpcycles (n : Int) : X.opcycles f g n ⟶ (X.H n).obj (mk₁ fg)
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `H^n(f) ⟶ H^n(f ≫ g)` factors through `opZ^n(f, g)`.
-/
noncomputable def fromOpcycles (n : ℤ) :
    X.opcycles f g n ⟶ (X.H n).obj (mk₁ fg) :=
  cokernel.desc _ ((X.H n).map (twoδ₂Toδ₁ f g fg h)) (by simp)
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : Mono (X.fromOpcycles f g fg h n) :=
  (ShortComplex.exact_iff_mono_cokernel_desc _).1 (X.exact₁ f g fg h (n - 1) n)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.p_fromOpcycles** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：p_fromOpcycles (n : Int) : X.pOpcycles f g n ≫ X.fromOpcycles f g fg h n =
 (X.H n).map (twoδ₂Toδ₁ f g fg h)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
-/
lemma p_fromOpcycles (n : ℤ) :
    X.pOpcycles f g n ≫ X.fromOpcycles f g fg h n =
      (X.H n).map (twoδ₂Toδ₁ f g fg h) :=
  cokernel.π_desc ..

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesMap_fromOpcycles** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：opcyclesMap_fromOpcycles (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg') 
(n : Int) (hβ₀ : β.app 0 = α.app 0
参数：α : mk₂ f g ⟶ mk₂ f' g'；β : mk₁ fg ⟶ mk₁ fg'；n : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiPOpcycles`：∀ {C : Type u_1}
 {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.p_fromOpcycles_assoc`：∀ {C : Type 
u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Ca
tegoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `CategoryTheory.Abelian.SpectralObject.p_opcyclesMap_assoc`：∀ {C : Type u
_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.p_fromOpcycles`：p_fromOpcycles (n 
: Int) : X.pOpcycles f g n ≫ X.fromOpcycles f g fg h n = (X.H n).map (twoδ₂Toδ₁ 
f g fg h)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₁`：hom_ext₁ {F G : ComposableArro
ws C 1} {φ φ' : F ⟶ G} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
 φ = φ'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma opcyclesMap_fromOpcycles (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg') (n : ℤ)
    (hβ₀ : β.app 0 = α.app 0 := by cat_disch) (hβ₁ : β.app 1 = α.app 2 := by cat_disch) :
    X.opcyclesMap f g f' g' α n ≫ X.fromOpcycles f' g' fg' h' n =
      X.fromOpcycles f g fg h n ≫ (X.H n).map β := by
  rw [← cancel_epi (X.pOpcycles f g n), p_fromOpcycles_assoc,
    X.p_opcyclesMap_assoc f g f' g' α (homMk₁ (α.app 0) (α.app 1)
      (naturality' α 0 1)) n rfl,
    p_fromOpcycles, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext
  · cat_disch
  · dsimp
    rw [hβ₁]
    exact (naturality' α 1 2).symm

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.H_map_two** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma H_map_twoδ₂Toδ₁_toCycles (n : ℤ) :
    (X.H n).map (twoδ₂Toδ₁ f g fg h) ≫ X.toCycles f g fg h n = 0 := by
  simp [← cancel_mono (X.iCycles f g n)]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.fromOpcycles_H_map_two** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromOpcycles_H_map_twoδ₁Toδ₀ (n : ℤ) :
    X.fromOpcycles f g fg h n ≫ (X.H n).map (twoδ₁Toδ₀ f g fg h) = 0 := by
  simp [← cancel_epi (X.pOpcycles f g n)]

/-- The short complex expressing `Z^n(f, g)` as a cokernel of
the map `H^n(f) ⟶ H^n(f ≫ g)`. -/
@[simps]
/-
**CategoryTheory.Abelian.SpectralObject.cokernelSequenceCycles** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cokernelSequenceCycles (n : Int) : ShortComplex C
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.H_map_twoδ₂Toδ₁_toCycles`：H_map_tw
oδ₂Toδ₁_toCycles (n : Int) : (X.H n).map (twoδ₂Toδ₁ f g fg h) ≫ X.toCycles f g f
g h n = 0

--- 原说明 ---
The short complex expressing `Z^n(f, g)` as a cokernel of
the map `H^n(f) ⟶ H^n(f ≫ g)`.
-/
noncomputable def cokernelSequenceCycles (n : ℤ) : ShortComplex C :=
  ShortComplex.mk _ _ (X.H_map_twoδ₂Toδ₁_toCycles f g fg h n)

/-- The short complex expressing `opZ^n(f, g)` as a kernel of
the map `H^n(f ≫ g) ⟶ H^n(g)`. -/
@[simps]
/-
**CategoryTheory.Abelian.SpectralObject.kernelSequenceOpcycles** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：kernelSequenceOpcycles (n : Int) : ShortComplex C
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.fromOpcycles_H_map_twoδ₁Toδ₀`：from
Opcycles_H_map_twoδ₁Toδ₀ (n : Int) : X.fromOpcycles f g fg h n ≫ (X.H n).map (tw
oδ₁Toδ₀ f g fg h) = 0

--- 原说明 ---
The short complex expressing `opZ^n(f, g)` as a kernel of
the map `H^n(f ≫ g) ⟶ H^n(g)`.
-/
noncomputable def kernelSequenceOpcycles (n : ℤ) : ShortComplex C :=
  ShortComplex.mk _ _ (X.fromOpcycles_H_map_twoδ₁Toδ₀ f g fg h n)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : Epi (X.cokernelSequenceCycles f g fg h n).g := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : Mono (X.kernelSequenceOpcycles f g fg h n).f := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `Z^n(f, g)` identifies to a cokernel of the `H^n(f) ⟶ H^n(f ≫ g)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.cokernelSequenceCycles_exact** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cokernelSequenceCycles_exact (n : Int) : (X.cokernelSequenceCycles f g fg 
h n).Exact
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_g_is_cokernel`：exact_of_g_is_cokern
el (hS : IsColimit (CokernelCofork.ofπ S.g S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instMonoICycles`：∀ {C : Type u_1} 
{ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cokernelIsoCycles_hom_fac`：cokerne
lIsoCycles_hom_fac (n : Int) : cokernel.π _ ≫ (X.cokernelIsoCycles f g fg h n).h
om ≫ X.iCycles f g n = (X.H n).map (twoδ₁Toδ₀ f g fg …
· 使用引理 `CategoryTheory.Abelian.SpectralObject.toCycles_i`：toCycles_i (n : Int) :
 X.toCycles f g fg h n ≫ X.iCycles f g n = (X.H n).map (twoδ₁Toδ₀ f g fg h)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
`Z^n(f, g)` identifies to a cokernel of the `H^n(f) ⟶ H^n(f ≫ g)`.
-/
lemma cokernelSequenceCycles_exact (n : ℤ) :
    (X.cokernelSequenceCycles f g fg h n).Exact := by
  apply ShortComplex.exact_of_g_is_cokernel
  exact IsColimit.ofIsoColimit (cokernelIsCokernel _)
    (Cofork.ext (X.cokernelIsoCycles f g fg h n) (by
      simp [← cancel_mono (X.iCycles f g n)]))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `opZ^n(f, g)` identifies to the kernel of `H^n(f ≫ g) ⟶ H^n(g)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.kernelSequenceOpcycles_exact** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：kernelSequenceOpcycles_exact (n : Int) : (X.kernelSequenceOpcycles f g fg 
h n).Exact
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_f_is_kernel`：exact_of_f_is_kernel (
hS : IsLimit (KernelFork.ofι S.f S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiPOpcycles`：∀ {C : Type u_1}
 {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.opcyclesIsoKernel_hom_fac`：opcycle
sIsoKernel_hom_fac (n : Int) : X.pOpcycles f g n ≫ (X.opcyclesIsoKernel f g fg h
 n).hom ≫ kernel.ι _ = (X.H n).map (twoδ₂Toδ₁ f g fg …
· 使用引理 `CategoryTheory.Abelian.SpectralObject.p_fromOpcycles`：p_fromOpcycles (n 
: Int) : X.pOpcycles f g n ≫ X.fromOpcycles f g fg h n = (X.H n).map (twoδ₂Toδ₁ 
f g fg h)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
`opZ^n(f, g)` identifies to the kernel of `H^n(f ≫ g) ⟶ H^n(g)`.
-/
lemma kernelSequenceOpcycles_exact (n : ℤ) :
    (X.kernelSequenceOpcycles f g fg h n).Exact := by
  apply ShortComplex.exact_of_f_is_kernel
  exact IsLimit.ofIsoLimit (kernelIsKernel _)
    (Iso.symm (Fork.ext (X.opcyclesIsoKernel f g fg h n) (by
      simp [← cancel_epi (X.pOpcycles f g n)])))
/-
**CategoryTheory.Abelian.SpectralObject.isIso_toCycles** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：isIso_toCycles (n : Int) (hf : IsZero ((X.H n).obj (mk₁ f))) : IsIso (X.to
Cycles f g fg h n)
参数：n : Int；hf : IsZero ((X.H n).obj (mk₁ f))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.mono_g`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : 
CategoryTheory.ShortComplex C}…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cokernelSequenceCycles_exact`：coke
rnelSequenceCycles_exact (n : Int) : (X.cokernelSequenceCycles f g fg h n).Exact
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `CategoryTheory.Balanced.isIso_of_mono_of_epi`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.Balanced C] {X Y : C} (f :
 X ⟶ Y)   [CategoryTheory.Mono f] …
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiToCycles`：∀ {C : Type u_1} 
{ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
-/
lemma isIso_toCycles (n : ℤ) (hf : IsZero ((X.H n).obj (mk₁ f))) :
    IsIso (X.toCycles f g fg h n) := by
  have : Mono (X.toCycles f g fg h n) :=
    (X.cokernelSequenceCycles_exact f g fg h n).mono_g (hf.eq_of_src _ _)
  exact Balanced.isIso_of_mono_of_epi _
/-
**CategoryTheory.Abelian.SpectralObject.isIso_fromOpcycles** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：isIso_fromOpcycles (n : Int) (hg : IsZero ((X.H n).obj (mk₁ g))) : IsIso (
X.fromOpcycles f g fg h n)
参数：n : Int；hg : IsZero ((X.H n).obj (mk₁ g))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.epi_f`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : C
ategoryTheory.ShortComplex C}…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.kernelSequenceOpcycles_exact`：kern
elSequenceOpcycles_exact (n : Int) : (X.kernelSequenceOpcycles f g fg h n).Exact
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用定理 `CategoryTheory.Balanced.isIso_of_mono_of_epi`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.Balanced C] {X Y : C} (f :
 X ⟶ Y)   [CategoryTheory.Mono f] …
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instMonoFromOpcycles`：∀ {C : Type 
u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Ca
tegoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
-/
lemma isIso_fromOpcycles (n : ℤ) (hg : IsZero ((X.H n).obj (mk₁ g))) :
    IsIso (X.fromOpcycles f g fg h n) := by
  have : Epi (X.fromOpcycles f g fg h n) :=
    (X.kernelSequenceOpcycles_exact f g fg h n).epi_f (hg.eq_of_tgt _ _)
  exact Balanced.isIso_of_mono_of_epi _

section

variable {A : C} {n : ℤ} (x : (X.H n).obj (mk₁ fg) ⟶ A)
  (hx : (X.H n).map (twoδ₂Toδ₁ f g fg h) ≫ x = 0)

/-- Constructor for morphisms from `X.cycles`. -/
/-
**CategoryTheory.Abelian.SpectralObject.descCycles** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Abelian.SpectralObject`。
形式化陈述：descCycles : X.cycles f g n ⟶ A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cokernelSequenceCycles_exact`：coke
rnelSequenceCycles_exact (n : Int) : (X.cokernelSequenceCycles f g fg h n).Exact
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiGCokernelSequenceCycles`：∀ 
{C : Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [i
nst_1 : CategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…

--- 原说明 ---
Constructor for morphisms from `X.cycles`.
-/
noncomputable def descCycles :
    X.cycles f g n ⟶ A :=
  (X.cokernelSequenceCycles_exact f g fg h n).desc x hx

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.toCycles_descCycles** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：toCycles_descCycles : X.toCycles f g fg h n ≫ X.descCycles f g fg h x hx =
 x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.Exact.g_desc`：g_desc (hS : S.Exact) {A : C} 
(k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] : S.g ≫ hS.desc k hk = k
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cokernelSequenceCycles_exact`：coke
rnelSequenceCycles_exact (n : Int) : (X.cokernelSequenceCycles f g fg h n).Exact
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiGCokernelSequenceCycles`：∀ 
{C : Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [i
nst_1 : CategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
-/
lemma toCycles_descCycles :
    X.toCycles f g fg h n ≫ X.descCycles f g fg h x hx = x :=
  (X.cokernelSequenceCycles_exact f g fg h n).g_desc x hx

end

section

variable {A : C} {n : ℤ} (x : A ⟶ (X.H n).obj (mk₁ fg))
  (hx : x ≫ (X.H n).map (twoδ₁Toδ₀ f g fg h) = 0)

/-- Constructor for morphisms to `X.opcycles`. -/
/-
**CategoryTheory.Abelian.SpectralObject.liftOpcycles** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Abelian.SpectralObject`。
形式化陈述：liftOpcycles : A ⟶ X.opcycles f g n
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.kernelSequenceOpcycles_exact`：kern
elSequenceOpcycles_exact (n : Int) : (X.kernelSequenceOpcycles f g fg h n).Exact
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instMonoFKernelSequenceOpcycles`：∀
 {C : Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [
inst_1 : CategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…

--- 原说明 ---
Constructor for morphisms to `X.opcycles`.
-/
noncomputable def liftOpcycles :
    A ⟶ X.opcycles f g n :=
  (X.kernelSequenceOpcycles_exact f g fg h n).lift x hx

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.liftOpcycles_fromOpcycles** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：liftOpcycles_fromOpcycles : X.liftOpcycles f g fg h x hx ≫ X.fromOpcycles 
f g fg h n = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.Exact.lift_f`：lift_f (hS : S.Exact) {A : C} 
(k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] : hS.lift k hk ≫ S.f = k
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用引理 `CategoryTheory.Abelian.SpectralObject.kernelSequenceOpcycles_exact`：kern
elSequenceOpcycles_exact (n : Int) : (X.kernelSequenceOpcycles f g fg h n).Exact
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instMonoFKernelSequenceOpcycles`：∀
 {C : Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [
inst_1 : CategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
-/
lemma liftOpcycles_fromOpcycles :
    X.liftOpcycles f g fg h x hx ≫ X.fromOpcycles f g fg h n = x :=
  (X.kernelSequenceOpcycles_exact f g fg h n).lift_f x hx

end

end

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ : ℤ)
/-- The morphism `H^{n₀}(f₃) ⟶ Z^{n₁}(f₁, f₂)` induced by `δ`
when `f₁`, `f₂`, `f₃` are composable morphisms and `n₀ + 1 = n₁`. -/
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `H^{n₀}(f₃) ⟶ Z^{n₁}(f₁, f₂)` induced by `δ`
when `f₁`, `f₂`, `f₃` are composable morphisms and `n₀ + 1 = n₁`.
-/
noncomputable def δToCycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.H n₀).obj (mk₁ f₃) ⟶ X.cycles f₁ f₂ n₁ :=
  X.liftCycles f₁ f₂ _ _ rfl (X.δ f₂ f₃ n₀ n₁) (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δToCycles_iCycles (hn₁ : n₀ + 1 = n₁) :
    X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ ≫ X.iCycles f₁ f₂ n₁ =
      X.δ f₂ f₃ n₀ n₁ hn₁ := by
  simp only [δToCycles, liftCycles_i]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_toCycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f₁₂ f₃ n₀ n₁ hn₁ ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ =
      X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ := by
  rw [← cancel_mono (X.iCycles f₁ f₂ n₁), Category.assoc,
    toCycles_i, δToCycles_iCycles,
    ← X.δ_naturality f₁₂ f₃ f₂ f₃ (twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂) (𝟙 _) n₀ n₁,
    Functor.map_id, Category.id_comp]

/-- The morphism `opZ^{n₀}(f₂, f₃) ⟶ H^{n₁}(f₁)` induced by `δ`
when `f₁`, `f₂`, `f₃` are composable morphisms and `n₀ + 1 = n₁`. -/
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `opZ^{n₀}(f₂, f₃) ⟶ H^{n₁}(f₁)` induced by `δ`
when `f₁`, `f₂`, `f₃` are composable morphisms and `n₀ + 1 = n₁`.
-/
noncomputable def δFromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.opcycles f₂ f₃ n₀ ⟶ (X.H n₁).obj (mk₁ f₁) :=
  X.descOpcycles f₂ f₃ (n₀ - 1) n₀ (by lia) (X.δ f₁ f₂ n₀ n₁ hn₁) (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.pOpcycles_** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pOpcycles_δFromOpcycles (hn₁ : n₀ + 1 = n₁) :
    X.pOpcycles f₂ f₃ n₀ ≫ X.δFromOpcycles f₁ f₂ f₃ n₀ n₁ hn₁ =
      X.δ f₁ f₂ n₀ n₁ hn₁ := by
  simp only [δFromOpcycles, p_descOpcycles]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.fromOpcyles_** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromOpcyles_δ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₀ ≫ X.δ f₁ f₂₃ n₀ n₁ hn₁ =
      X.δFromOpcycles f₁ f₂ f₃ n₀ n₁ hn₁ := by
  rw [← cancel_epi (X.pOpcycles f₂ f₃ n₀),
    p_fromOpcycles_assoc, pOpcycles_δFromOpcycles,
    X.δ_naturality f₁ f₂ f₁ f₂₃ (𝟙 _) (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) n₀ n₁,
    Functor.map_id, Category.comp_id]

end

end SpectralObject

end Abelian

end CategoryTheory

