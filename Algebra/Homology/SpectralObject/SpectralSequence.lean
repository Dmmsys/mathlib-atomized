/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Homology
public import Mathlib.Algebra.Homology.SpectralObject.HasSpectralSequence
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Order.WithBotTop

/-!
# The spectral sequence of a spectral object

The main definition in this file is `Abelian.SpectralObject.spectralSequence`.
Assume that `X` is a spectral object indexed by `ι` in an abelian category `C`,
and that we have `data : SpectralSequenceDataCore ι c r₀` for a family
of complex shapes `c : ℤ → ComplexShape κ` for a type `κ` and `r₀ : ℤ`.
Then, under the assumption `X.HasSpectralSequence data` (see the file
`Mathlib/Algebra/Homology/SpectralObject/HasSpectralSequence.lean`),
we obtain `X.spectralSequence data` which is a spectral sequence starting
on page `r₀`, such that the `r`th page (for `r₀ ≤ r`) is a homological
complex of shape `c r`.

## Outline of the construction

The construction of the spectral sequence is as follows. If `r₀ ≤ r`
and `pq : κ`, we define the object of the spectral sequence in position `pq`
on the `r`th page as `E^d(i₀ r pq ≤ i₁ pq ≤ i₂ pq ≤ i₃ r pq)`
where `d := data.deg pq` and the indices `i₀`, `i₁`, `i₂`, `i₃` are given
by `data` (they all depend on `pq`, and `i₀` and `i₃` also depend on the page `r`),
see `spectralSequencePageXIso`.

When `(c r).Rel pq pq'`, the differential from the object in position `pq`
to the object in position `pq'` on the `r`th page can be related to
the differential `X.d` of the spectral object (see the lemma
`spectralSequence_page_d_eq`). Indeed, the assumptions that
are part of `data` give equalities of indices `i₂ r pq' = i₀ r pq`
and `i₃ pq' = i₁ pq`, so that we have a chain of inequalities
`i₀ r pq' ≤ i₁ pq' ≤ i₂ pq' ≤ i₃ r pq' ≤ i₂ pq ≤ i₃ r pq` for which
the API of spectral objects provides a differential
`X.d : E^n(i₀ r pq ≤ i₁ pq ≤ i₂ pq ≤ i₃ r pq) ⟶ E^{n + 1}(i₀ r pq' ≤ i₁ pq' ≤ i₂ pq' ≤ i₃ r pq')`.

Now, fix `r` and three positions `pq`, `pq'` and `pq''` such that
`pq` is the previous object of `pq'` for `c r` and `pq''` is the next
object of `pq'`. (Note that in case there are no nontrivial differentials
to the object `pq'` for the complex shape `c r`, according to the homological
complex API, we have `pq = pq'` and the differential is zero. Similarly,
when there are no nontrivial differentials from the object in position `pq'`,
we have `pq'' = pq` and the corresponding differential is zero.)
In the favourable case where both `(c r).Rel pq pq'` and `(c r).Rel pq' pq''`
hold, the definition `SpectralObject.SpectralSequence.shortComplexIso`
in this file can be used in combination to `SpectralObject.SpectralSequence.dHomologyIso`
in order to compute the homology of the differentials.)

In the general case, using the assumptions in `X.HasSpectralSequence data`,
we provide a limit kernel fork `kf` and
a limit cokernel cofork `cc` of the differentials on the `r`th page,
together with an epi-mono factorization `fac` which allows
to obtain that the homology of the `r`th page identifies to the next page (see the definitions
`SpectralObject.SpectralSequence.homologyData` and
`SpectralObject.spectralSequenceHomologyData`).

## Spectral objects indexed by `EInt`.

When `X` is a spectral object indexed by the extended integers `EInt`,
we obtain the `E₂`-cohomological spectral sequence
`X.E₂SpectralSequence` where the objects of each page are indexed by
`ℤ × ℤ` (the condition `HasSpectralSequence` is automatically satisfied).
Under the `X.IsFirstQuadrant` assumption, we obtain
`X.E₂SpectralSequenceNat` which is a first quadrant `E₂`-spectral
sequence (the objects in the pages are indexed by `ℕ × ℕ` instead
of `ℤ × ℤ`).

-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceDataCore ι c r₀)

namespace SpectralSequence

/-- The object on position `pq` on the `r`th page of the spectral sequence. -/
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageX** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence`。
形式化陈述：pageX (r : Int) (pq : κ) (hr : r₀ <= r
参数：r : Int；pq : κ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…

--- 原说明 ---
The object on position `pq` on the `r`th page of the spectral sequence.
-/
noncomputable def pageX (r : ℤ) (pq : κ) (hr : r₀ ≤ r := by lia) : C :=
  X.E (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)

/-- The object on position `pq` on the `r`th page of the spectral sequence identifies
to `E^{deg pq}(i₀ ≤ i₁ ≤ i₂ ≤ i₃)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence`。
形式化陈述：pageXIso (r : Int) (hr : r₀ <= r) (pq : κ) (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = da
ta.i₀ r pq) (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r p
q) (n₀ n₁ n₂ : Int) (h : n₁ = data.deg pq) (hn₁ : n₀ + 1 = n₁
参数：r : Int；hr : r₀ <= r；pq : κ；i₀ i₁ i₂ i₃ : ι；h₀ : i₀ = data.i₀ r pq；h₁ : i₁ = 
data.i₁ pq；h₂ : i₂ = data.i₂ pq；h₃ : i₃ = data.i₃ r pq；n₀ n₁ n₂ : Int；h : n₁ = d
ata.deg pq。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃

--- 原说明 ---
The object on position `pq` on the `r`th page of the spectral sequence identifie
s
to `E^{deg pq}(i₀ ≤ i₁ ≤ i₂ ≤ i₃)`.
-/
noncomputable def pageXIso (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    pageX X data r pq hr ≅ X.E
      (homOfLE (data.le₀₁' r hr pq h₀ h₁))
      (homOfLE (data.le₁₂' pq h₁ h₂))
      (homOfLE (data.le₂₃' r hr pq h₂ h₃))
      n₀ n₁ n₂ hn₁ hn₂ :=
  eqToIso (by
    obtain rfl : n₀ = n₁ - 1 := by lia
    subst h hn₂ h₀ h₁ h₂ h₃
    rfl)

open scoped Classical in
/-- The differential on the `r`th page of the spectral sequence. -/
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence`。
形式化陈述：pageD (r : Int) (pq pq' : κ) (hr : r₀ <= r
参数：r : Int；pq pq' : κ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…

--- 原说明 ---
The differential on the `r`th page of the spectral sequence.
-/
noncomputable def pageD (r : ℤ) (pq pq' : κ) (hr : r₀ ≤ r := by lia) :
    pageX X data r pq hr ⟶ pageX X data r pq' hr :=
  if hpq : (c r).Rel pq pq'
    then
      X.d (homOfLE (data.le₀₁ r pq'))
        (homOfLE (data.le₁₂' pq' rfl (data.hc₀₂ r pq pq' hpq)))
        (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
        (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (data.deg pq + 2) ≫
      (pageXIso _ _ _ _ _ _ _ _ _ rfl rfl
        (data.hc₀₂ r pq pq' hpq) (data.hc₁₃ r pq pq' hpq) _ _ _ (data.hc r pq pq' hpq) rfl _).inv
    else 0

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD_eq** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence`。
形式化陈述：pageD_eq (r : Int) (hr : r₀ <= r) (pq pq' : κ) (hpq : (c r).Rel pq pq') {i
₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃) (f₄ : i₃ ⟶ i₄
) (f₅ : i₄ ⟶ i₅) (h₀ : i₀ = data.i₀ r pq') (h₁ : i₁ = data.i₁ pq') (h₂ : i₂ = da
ta.i₀ r pq) (h₃ : i₃ = data.i₁ pq) (h₄ : i₄ = data.i₂ pq) (h₅ : i₅ = data.i₃ r p
q) (n₀ n₁ n₂ n₃ : Int) (hn₁' : n₁ = data.deg pq) (hn₁ : n₀ + 1 = n₁
参数：r : Int；hr : r₀ <= r；pq pq' : κ；hpq : (c r).Rel pq pq'；f₁ : i₀ ⟶ i₁；f₂ : i₁ ⟶
 i₂；f₃ : i₂ ⟶ i₃；f₄ : i₃ ⟶ i₄；f₅ : i₄ ⟶ i₅；h₀ : i₀ = data.i₀ r pq'；h₁ : i₁ = dat
a.i₁ pq'；h₂ : i₂ = data.i₀ r pq；h₃ : i₃ = data.i₁ pq；h₄ : i₄ = data.i₂ pq；h₅ : i
₅ = data.i₃ r pq；n₀ n₁ n₂ n₃ : Int；hn₁' : n₁ = data.deg pq。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma pageD_eq (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (hpq : (c r).Rel pq pq')
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
    (h₀ : i₀ = data.i₀ r pq') (h₁ : i₁ = data.i₁ pq') (h₂ : i₂ = data.i₀ r pq)
    (h₃ : i₃ = data.i₁ pq) (h₄ : i₄ = data.i₂ pq) (h₅ : i₅ = data.i₃ r pq)
    (n₀ n₁ n₂ n₃ : ℤ) (hn₁' : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    pageD X data r pq pq' =
      (pageXIso _ _ _ _ _ _ _ _ _ h₂ h₃ h₄ h₅ _ _ _ hn₁' _ _).hom ≫
        X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
        (pageXIso _ _ _ _ _ _ _ _ _ h₀ h₁ (by rw [h₂, data.hc₀₂ r pq pq' hpq])
          (by rw [h₃, data.hc₁₃ r pq pq' hpq]) _ _ _
          (by simpa only [← hn₂, hn₁'] using data.hc r pq pq' hpq) _ _).inv := by
  subst hn₁' h₀ h₁ h₂ h₃ h₄ h₅
  obtain rfl : n₀ = data.deg pq - 1 := by lia
  obtain rfl : n₂ = data.deg pq + 1 := by lia
  obtain rfl : n₃ = data.deg pq + 2 := by lia
  dsimp [pageD, pageXIso]
  rw [dif_pos hpq, Category.id_comp]
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD_pageD** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence`。
形式化陈述：pageD_pageD (r : Int) (hr : r₀ <= r) (pq pq' pq'' : κ) : pageD X data r pq
 pq' hr ≫ pageD X data r pq' pq'' hr = 0
参数：r : Int；hr : r₀ <= r；pq pq' pq'' : κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.hc₁₃`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.hc₀₂`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD_eq`：pageD_e
q (r : Int) (hr : r₀ <= r) (pq pq' : κ) (hpq : (c r).Rel pq pq') {i₀ i₁ i₂ i₃ i₄
 i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.hc`：∀ {ι 
: Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : ℤ}
   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Abelian.SpectralObject.d_d_assoc`：∀ {C : Type u_1} {ι : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma pageD_pageD (r : ℤ) (hr : r₀ ≤ r) (pq pq' pq'' : κ) :
    pageD X data r pq pq' hr ≫ pageD X data r pq' pq'' hr = 0 := by
  by_cases hpq : (c r).Rel pq pq'
  · by_cases hpq' : (c r).Rel pq' pq''
    · rw [pageD_eq X data r hr pq pq' hpq (homOfLE (data.le₂₃ r pq''))
          (homOfLE (data.le₁₂' pq' (data.hc₁₃ r pq' pq'' hpq').symm
          (data.hc₀₂ r pq pq' hpq))) (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq))
          (homOfLE (data.le₂₃ r pq))
          (data.hc₀₂ r pq' pq'' hpq').symm (data.hc₁₃ r pq' pq'' hpq').symm rfl rfl rfl rfl
          (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (data.deg pq + 2) rfl,
        pageD_eq X data r hr pq' pq'' hpq' (homOfLE (data.le₀₁ r pq''))
          (homOfLE (data.le₁₂ pq'')) (homOfLE (data.le₂₃ r pq''))
          (homOfLE (data.le₁₂' pq' (data.hc₁₃ r pq' pq'' hpq').symm (data.hc₀₂ r pq pq' hpq)))
          (homOfLE (data.le₀₁ r pq)) rfl rfl
          (data.hc₀₂ r pq' pq'' hpq').symm (data.hc₁₃ r pq' pq'' hpq').symm
          (data.hc₀₂ r pq pq' hpq) (data.hc₁₃ r pq pq' hpq)
          _ _ (data.deg pq + 2) _ (data.hc r pq pq' hpq) rfl (by lia) rfl,
        Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
        d_d_assoc .., zero_comp, comp_zero]
    · dsimp only [pageD]
      rw [dif_neg hpq', comp_zero]
  · dsimp only [pageD]
    rw [dif_neg hpq, zero_comp]

/-- The `r`th page of the spectral sequence. -/
@[simps]
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.page** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence`。
形式化陈述：page (r : Int) (hr : r₀ <= r) : HomologicalComplex C (c r) where X pq
参数：r : Int；hr : r₀ <= r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `r`th page of the spectral sequence.
-/
noncomputable def page (r : ℤ) (hr : r₀ ≤ r) :
    HomologicalComplex C (c r) where
  X pq := pageX X data r pq
  d := pageD X data r
  shape pq pq' hpq := dif_neg hpq

set_option backward.isDefEq.respectTransparency.types false in
/-- The short complex of the `r`th page of the spectral sequence on position `pq'`
identifies to the short complex given by the differentials of the spectral object.
Then, the homology of this short complex can be computed using
`SpectralSequence.dHomologyIso`.
(This only applies in the favourable case when there are `pq` and `pq''` such
that `(c r).Rel pq pq'` and `(c r).Rel pq' pq''` hold.) -/
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.shortComplexIso** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence`。
形式化陈述：shortComplexIso (r : Int) (hr : r₀ <= r) (pq pq' pq'' : κ) (hpq : (c r).Re
l pq pq') (hpq' : (c r).Rel pq' pq'') (n₀ n₁ n₂ n₃ n₄ : Int) (hn₁ : n₀ + 1 = n₁)
 (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) (hn₄ : n₃ + 1 = n₄) (hn₂' : n₂ = data.d
eg pq') : (page X data r hr).sc' pq pq' pq'' ≅ X.dShortComplex (homOfLE (data.le
₀₁ r pq'')) (homOfLE (data.le₁₂ pq'')) (homOfLE (data.le₂₃ r pq'')) (homOfLE (by
 simpa only [← data.hc₁₃ r pq' pq'' hpq', data.hc₀₂ r pq pq' hpq] using data.le₁
₂ pq')) (homOfLE (data.le₀
参数：r : Int；hr : r₀ <= r；pq pq' pq'' : κ；hpq : (c r).Rel pq pq'；hpq' : (c r).Rel 
pq' pq''；n₀ n₁ n₂ n₃ n₄ : Int；hn₁ : n₀ + 1 = n₁；hn₂ : n₁ + 1 = n₂；hn₃ : n₂ + 1 =
 n₃；hn₄ : n₃ + 1 = n₄；hn₂' : n₂ = data.deg pq'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…

--- 原说明 ---
The short complex of the `r`th page of the spectral sequence on position `pq'`
identifies to the short complex given by the differentials of the spectral objec
t.
Then, the homology of this short complex can be computed using
`SpectralSequence.dHomologyIso`.
(This only applies in the favourable case when there are `pq` and `pq''` such
that `(c r).Rel pq pq'` and `(c r).Rel pq' pq''` hold.)
-/
noncomputable def shortComplexIso (r : ℤ) (hr : r₀ ≤ r) (pq pq' pq'' : κ)
    (hpq : (c r).Rel pq pq') (hpq' : (c r).Rel pq' pq'')
    (n₀ n₁ n₂ n₃ n₄ : ℤ)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) (hn₄ : n₃ + 1 = n₄)
    (hn₂' : n₂ = data.deg pq') :
    (page X data r hr).sc' pq pq' pq'' ≅
      X.dShortComplex (homOfLE (data.le₀₁ r pq''))
        (homOfLE (data.le₁₂ pq'')) (homOfLE (data.le₂₃ r pq''))
        (homOfLE (by simpa only [← data.hc₁₃ r pq' pq'' hpq', data.hc₀₂ r pq pq' hpq]
          using data.le₁₂ pq')) (homOfLE (data.le₀₁ r pq))
        (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq)) n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄ := by
  refine ShortComplex.isoMk
    (pageXIso _ _ _ hr _ _ _ _ _ rfl rfl rfl rfl _ _ _ (by have := data.hc r pq pq' hpq; lia))
    (pageXIso _ _ _ hr _ _ _ _ _ (by rw [data.hc₀₂ r pq' pq'' hpq'])
    (by rw [data.hc₁₃ r pq' pq'' hpq'])
    (by rw [data.hc₀₂ r pq pq' hpq]) (by rw [data.hc₁₃ r pq pq' hpq]) _ _ _ hn₂')
    (pageXIso _ _ _ hr _ _ _ _ _ rfl rfl rfl rfl _ _ _ (by have := data.hc r pq' pq'' hpq'; lia))
    ?_ ?_
  · simp only [← Iso.comp_inv_eq, Category.assoc]
    exact (pageD_eq X data r hr pq pq' hpq _ _ _ _ _ (data.hc₀₂ r pq' pq'' hpq').symm
      (data.hc₁₃ r pq' pq'' hpq').symm ..).symm
  · simp only [← Iso.comp_inv_eq, Category.assoc]
    exact (pageD_eq X data r hr pq' pq'' hpq' _ _ _ _ _ rfl rfl ..).symm

section

variable (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
  (pq pq' pq'' : κ) (hpq : (c r).prev pq' = pq) (hpq' : (c r).next pq' = pq'')
  (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
  (hi₀' : i₀' = data.i₀ r' pq')
  (hi₀ : i₀ = data.i₀ r pq')
  (hi₁ : i₁ = data.i₁ pq')
  (hi₂ : i₂ = data.i₂ pq')
  (hi₃ : i₃ = data.i₃ r pq')
  (hi₃' : i₃' = data.i₃ r' pq')
  (n₀ n₁ n₂ : ℤ)
  (hn₁' : n₁ = data.deg pq')

namespace HomologyData

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.kf_w** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.Hom
ologyData`。
形式化陈述：kf_w (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.i₀_le'`：i
₀_le' {r r' : Int} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ) {i₀' i₀ : ι} (hi
₀' : i₀' = data.i₀ r' pq') (hi₀ : i₀ = data.i₀ r pq') : i₀'…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.i₀_prev`：
∀ {ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀
 : ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD_eq`：pageD_e
q (r : Int) (hr : r₀ <= r) (pq pq' : κ) (hpq : (c r).Rel pq pq') {i₀ i₁ i₂ i₃ i₄
 i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Abelian.SpectralObject.map_fourδ₁Toδ₀_d_assoc`：∀ {C : Typ
e u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Ca
tegoryTheory.Abelian C]   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma kf_w (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.mapFourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (data.i₀_le' hrr' hr pq' hi₀' hi₀)
      (data.le₀₁' r hr pq' hi₀ hi₁) (data.le₁₂' pq' hi₁ hi₂) (data.le₂₃' r hr pq' hi₂ hi₃)
        n₀ n₁ n₂ hn₁ hn₂ ≫
      (pageXIso X data _ hr _ _ _ _ _ hi₀ hi₁ hi₂ hi₃ _ _ _ hn₁' _ _).inv) ≫
        (page X data r hr).d pq' pq'' = 0 := by
  by_cases h : (c r).Rel pq' pq''
  · dsimp
    rw [pageD_eq X data r hr pq' pq'' h
      (homOfLE (by simpa only [hi₀', data.i₀_prev r r' _ _ h] using data.le₀₁ r pq''))
      (homOfLE (data.i₀_le' hrr' hr pq' hi₀' hi₀)) (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁))
      (homOfLE (data.le₁₂' pq' hi₁ hi₂)) (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃)) rfl
      (by rw [hi₀', data.i₀_prev r r' pq' pq'' h]) hi₀ hi₁ hi₂ hi₃ _ _ _ _ hn₁' hn₁ hn₂ rfl,
      Category.assoc, Iso.inv_hom_id_assoc, map_fourδ₁Toδ₀_d_assoc .., zero_comp]
  · rw [HomologicalComplex.shape _ _ _ h, comp_zero]

/-- A (limit) kernel fork of the differential on the `r`th page whose point
identifies to an object `X.E` -/
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.kf** 是 Mat
hlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.Hom
ologyData`。
形式化陈述：kf (hn₁ : n₀ + 1 = n₁
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.i₀_le'`：i
₀_le' {r r' : Int} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ) {i₀' i₀ : ι} (hi
₀' : i₀' = data.i₀ r' pq') (hi₀ : i₀ = data.i₀ r pq') : i₀'…

--- 原说明 ---
A (limit) kernel fork of the differential on the `r`th page whose point
identifies to an object `X.E`
-/
noncomputable abbrev kf (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    KernelFork ((page X data r hr).d pq' pq'') :=
  KernelFork.ofι _ (kf_w X data r r' hrr' hr pq' pq''
    i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁')

/-- The (exact) short complex attached to the kernel fork `kf`. -/
@[simps!]
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.kfSc** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.Hom
ologyData`。
形式化陈述：kfSc (hn₁ : n₀ + 1 = n₁
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.i₀_le'`：i
₀_le' {r r' : Int} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ) {i₀' i₀ : ι} (hi
₀' : i₀' = data.i₀ r' pq') (hi₀ : i₀ = data.i₀ r pq') : i₀'…

--- 原说明 ---
The (exact) short complex attached to the kernel fork `kf`.
-/
noncomputable def kfSc (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (kf_w X data r r' hrr' hr pq' pq''
    i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' hn₁)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.** 是 Mathl
ib 中的一个实例，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.Homolog
yData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (kfSc X data r r' hrr' hr pq' pq'' i₀' i₀ i₁ i₂ i₃
      hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' hn₁ hn₂).f := by
  dsimp
  infer_instance

variable [X.HasSpectralSequence data] in
include hpq' hn₁' in
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.isIso_mapF
our** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSeq
uence.HomologyData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_mapFourδ₁Toδ₀' (h : ¬ (c r).Rel pq' pq'')
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.mapFourδ₁Toδ₀'
      i₀' i₀ i₁ i₂ i₃ (data.i₀_le' hrr' hr pq' hi₀' hi₀) (data.le₀₁' r hr pq' hi₀ hi₁)
        (data.le₁₂' pq' hi₁ hi₂) (data.le₂₃' r hr pq' hi₂ hi₃) n₀ n₁ n₂ hn₁ hn₂) := by
  apply X.isIso_map_fourδ₁Toδ₀_of_isZero ..
  refine X.isZero_H_obj_mk₁_i₀_le' data r r' hrr' hr pq' (fun k hk ↦ ?_) _ (by lia) _ _ hi₀' hi₀
  obtain rfl := (c r).next_eq' hk
  subst hpq'
  exact h hk

set_option backward.defeqAttrib.useBackward true in
variable [X.HasSpectralSequence data] in
include hpq' in
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.kfSc_exact
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequen
ce.HomologyData`。
形式化陈述：kfSc_exact (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_iso`：exact_of_iso (e : S₁ ≅ S₂) (h 
: S₁.Exact) : S₂.Exact
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.i₀_prev`：
∀ {ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀
 : ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.i₀_le'`：i
₀_le' {r r' : Int} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ) {i₀' i₀ : ι} (hi
₀' : i₀' = data.i₀ r' pq') (hi₀ : i₀ = data.i₀ r pq') : i₀'…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.hc₀₂`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.hc₁₃`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.hc`：∀ {ι 
: Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : ℤ}
   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD_eq`：pageD_e
q (r : Int) (hr : r₀ <= r) (pq pq' : κ) (hpq : (c r).Rel pq pq') {i₀ i₁ i₂ i₃ i₄
 i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.dKernelSequence_exact`：dKernelSequ
ence_exact (hn₁ : n₀ + 1 = n₁
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_epi`：exact_iff_epi [HasZeroObject 
C] (hg : S.g = 0) : S.Exact ↔ Epi S.f
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.isIs
o_mapFourδ₁Toδ₀'`：isIso_mapFourδ₁Toδ₀' (h : ¬ (c r).Rel pq' pq'') (hn₁ : n₀ + 1 
= n₁
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma kfSc_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (kfSc X data r r' hrr' hr pq' pq'' i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃
      n₀ n₁ n₂ hn₁' hn₁ hn₂).Exact := by
  by_cases h : (c r).Rel pq' pq''
  · refine ShortComplex.exact_of_iso (Iso.symm ?_)
      (X.dKernelSequence_exact
        (homOfLE (show data.i₀ r pq'' ≤ i₀' by
          simpa only [hi₀', data.i₀_prev r r' _ _ h] using data.le₀₁ r pq''))
        (homOfLE (data.i₀_le' hrr' hr pq' hi₀' hi₀)) (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁))
        (homOfLE (data.le₁₂' pq' hi₁ hi₂)) (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃)) _ rfl
        n₀ n₁ n₂ (n₂ + 1) hn₁ hn₂ rfl)
    refine ShortComplex.isoMk (Iso.refl _)
      (pageXIso X data _ hr _ _ _ _ _ hi₀ hi₁ hi₂ hi₃ _ _ _ hn₁')
      (pageXIso X data _ hr _ _ _ _ _ rfl (by rw [hi₀', data.i₀_prev r r' _ _ h])
      (by rw [hi₀, data.hc₀₂ r _ _ h]) (by rw [hi₁, data.hc₁₃ r _ _ h]) _ _ _
      (by have := data.hc r _ _ h; lia)) ?_ ?_
    · simp
    · dsimp
      rw [pageD_eq X data r hr pq' pq'' h
        (homOfLE (data.le₀₁' r hr pq'' rfl (by simpa [← data.i₀_prev r r' _ _ h])))
        (homOfLE (data.i₀_le' hrr' hr pq' hi₀' hi₀)) (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁))
        (homOfLE (data.le₁₂' pq' hi₁ hi₂)) (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃))
        rfl (by rw [hi₀', data.i₀_prev r r' _ _ h]) hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ (n₂ + 1) hn₁',
        Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [ShortComplex.exact_iff_epi _ ((page X data r hr).shape _ _ h)]
    have := isIso_mapFourδ₁Toδ₀' X data r r' hrr' hr pq' pq'' hpq'
      i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' h
    dsimp
    infer_instance

variable [X.HasSpectralSequence data] in
/-- The kernel fork `kf` is a limit. -/
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.isLimitKf*
* 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequenc
e.HomologyData`。
形式化陈述：isLimitKf (hn₁ : n₀ + 1 = n₁
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.kfSc
_exact`：kfSc_exact (hn₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.inst
MonoFKfSc`：∀ {C : Type u_1} {ι : Type u_2} {κ : Type u_3} [inst : CategoryTheory
.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Abelian C] [inst_2 :…

--- 原说明 ---
The kernel fork `kf` is a limit.
-/
noncomputable def isLimitKf (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsLimit (kf X data r r' hrr' hr pq' pq''
      i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' hn₁ hn₂) :=
  (kfSc_exact X data r r' hrr' hr pq' pq'' hpq'
    i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' hn₁ hn₂).fIsKernel

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.cc_w** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.Hom
ologyData`。
形式化陈述：cc_w (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₃₃'`：le
₃₃' {r r' : Int} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ) {i₃ i₃' : ι} (hi₃ 
: i₃ = data.i₃ r pq') (hi₃' : i₃' = data.i₃ r' pq') : i₃ <…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.hc₀₂`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.hc₁₃`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.i₃_next`：
∀ {ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀
 : ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.hc`：∀ {ι 
: Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : ℤ}
   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD_eq`：pageD_e
q (r : Int) (hr : r₀ <= r) (pq pq' : κ) (hpq : (c r).Rel pq pq') {i₀ i₁ i₂ i₃ i₄
 i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用引理 `CategoryTheory.Abelian.SpectralObject.d_map_fourδ₄Toδ₃`：d_map_fourδ₄Toδ₃
 (hn₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma cc_w (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (page X data r hr).d pq pq' ≫
      (pageXIso X data _ hr _ _ _ _ _ hi₀ hi₁ hi₂ hi₃ _ _ _ hn₁').hom ≫
      X.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃' _ _ _
        (data.le₃₃' hrr' hr pq' hi₃ hi₃') n₀ n₁ n₂ = 0 := by
  by_cases h : (c r).Rel pq pq'
  · dsimp
    rw [pageD_eq X data r hr pq pq' h (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁))
      (homOfLE (data.le₁₂' pq' hi₁ hi₂)) (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃))
      (homOfLE (data.le₃₃' hrr' hr pq' hi₃ hi₃'))
      (homOfLE (by simpa only [hi₃', data.i₃_next r r' _ _ h] using data.le₂₃ r pq))
      hi₀ hi₁ (by rw [hi₂, data.hc₀₂ r _ _ h])
      (by rw [hi₃, data.hc₁₃ r _ _ h]) (by rw [hi₃', data.i₃_next r r' _ _ h]) rfl
      (n₀ - 1) n₀ n₁ n₂ (by have := data.hc r pq pq' h; lia) (by simp) hn₁ hn₂,
      Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
      d_map_fourδ₄Toδ₃ .., comp_zero]
    rfl
  · rw [HomologicalComplex.shape _ _ _ h, zero_comp]

/-- A (limit) cokernel cofork of the differential on the `r`th page whose point
identifies to an object `X.E` -/
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.cc** 是 Mat
hlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.Hom
ologyData`。
形式化陈述：cc (hn₁ : n₀ + 1 = n₁
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₃₃'`：le
₃₃' {r r' : Int} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ) {i₃ i₃' : ι} (hi₃ 
: i₃ = data.i₃ r pq') (hi₃' : i₃' = data.i₃ r' pq') : i₃ <…

--- 原说明 ---
A (limit) cokernel cofork of the differential on the `r`th page whose point
identifies to an object `X.E`
-/
noncomputable abbrev cc (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    CokernelCofork ((page X data r hr).d pq pq') :=
  CokernelCofork.ofπ _
    (cc_w X data r r' hrr' hr pq pq' i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁')

/-- The (exact) short complex attached to the cokernel cofork `cc`. -/
@[simps!]
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.ccSc** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.Hom
ologyData`。
形式化陈述：ccSc (hn₁ : n₀ + 1 = n₁
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₃₃'`：le
₃₃' {r r' : Int} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ) {i₃ i₃' : ι} (hi₃ 
: i₃ = data.i₃ r pq') (hi₃' : i₃' = data.i₃ r' pq') : i₃ <…

--- 原说明 ---
The (exact) short complex attached to the cokernel cofork `cc`.
-/
noncomputable def ccSc (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (cc_w X data r r' hrr' hr pq pq'
    i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁')

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.** 是 Mathl
ib 中的一个实例，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.Homolog
yData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (ccSc X data r r' hrr' hr pq pq'
    i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).g := by
  dsimp
  infer_instance

variable [X.HasSpectralSequence data] in
include hpq hn₁' in
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.isIso_mapF
our** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSeq
uence.HomologyData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_mapFourδ₄Toδ₃' (h : ¬ (c r).Rel pq pq')
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃'
      (data.le₀₁' r hr pq' hi₀ hi₁) (data.le₁₂' pq' hi₁ hi₂)
      (data.le₂₃' r hr pq' hi₂ hi₃) (data.le₃₃' hrr' hr pq' hi₃ hi₃') n₀ n₁ n₂) := by
  apply X.isIso_map_fourδ₄Toδ₃_of_isZero _ _ _ _ _ _ _ _ _ _
  refine X.isZero_H_obj_mk₁_i₃_le' data r r' hrr' hr pq' (fun _ hk ↦ ?_) _ (by lia) _ _ hi₃ hi₃'
  obtain rfl := (c r).prev_eq' hk
  subst hpq
  exact h hk

set_option backward.defeqAttrib.useBackward true in
variable [X.HasSpectralSequence data] in
include hpq in
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.ccSc_exact
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequen
ce.HomologyData`。
形式化陈述：ccSc_exact (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_iso`：exact_of_iso (e : S₁ ≅ S₂) (h 
: S₁.Exact) : S₂.Exact
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₃₃'`：le
₃₃' {r r' : Int} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ) {i₃ i₃' : ι} (hi₃ 
: i₃ = data.i₃ r pq') (hi₃' : i₃' = data.i₃ r' pq') : i₃ <…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.i₃_next`：
∀ {ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀
 : ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.hc₀₂`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.hc₁₃`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.hc`：∀ {ι 
: Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : ℤ}
   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD_eq`：pageD_e
q (r : Int) (hr : r₀ <= r) (pq pq' : κ) (hpq : (c r).Rel pq pq') {i₀ i₁ i₂ i₃ i₄
 i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.Abelian.SpectralObject.dCokernelSequence_exact`：dCokernel
Sequence_exact (hn₁ : n₀ + 1 = n₁
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_mono`：exact_iff_mono [HasZeroObjec
t C] (hf : S.f = 0) : S.Exact ↔ Mono S.g
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.isIs
o_mapFourδ₄Toδ₃'`：isIso_mapFourδ₄Toδ₃' (h : ¬ (c r).Rel pq pq') (hn₁ : n₀ + 1 = 
n₁
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
（共 34 条，此处仅展示前 30 条）
-/
lemma ccSc_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (ccSc X data r r' hrr' hr pq pq'
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').Exact := by
  by_cases h : (c r).Rel pq pq'
  · refine ShortComplex.exact_of_iso (Iso.symm ?_)
      (X.dCokernelSequence_exact
      (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁))
      (homOfLE (data.le₁₂' pq' hi₁ hi₂)) (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃))
      (homOfLE (data.le₃₃' hrr' hr pq' hi₃ hi₃'))
      (show i₃' ⟶ data.i₃ r pq from homOfLE (by
        simpa only [hi₃', data.i₃_next r r' _ _ h] using data.le₂₃ r pq)) _ rfl
      (n₀ - 1) n₀ n₁ n₂ (by simp) hn₁ hn₂)
    refine ShortComplex.isoMk
      (pageXIso X data _ hr _ _ _ _ _
        (by rw [hi₂, data.hc₀₂ r _ _ h]) (by rw [hi₃, data.hc₁₃ r _ _ h])
        (by rw [hi₃', data.i₃_next r r' _ _ h]) rfl _ _ _ (by have := data.hc r _ _ h; lia))
      (pageXIso X data _ hr _ _ _ _ _ hi₀ hi₁ hi₂ hi₃ _ _ _ hn₁') (Iso.refl _) ?_ (by simp)
    dsimp
    rw [pageD_eq X data r hr pq pq' h
          (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁)) (homOfLE (data.le₁₂' pq' hi₁ hi₂))
          (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃)) (homOfLE (data.le₃₃' hrr' hr pq' hi₃ hi₃'))
          (homOfLE (data.le₂₃' r hr pq (by rw [hi₃', data.i₃_next r r' pq pq' h]) rfl))
          hi₀ hi₁ (hi₂.trans (data.hc₀₂ r pq pq' h).symm)
          (hi₃.trans (data.hc₁₃ r pq pq' h).symm) (hi₃'.trans (data.i₃_next r r' pq pq' h)) rfl
          (n₀ - 1) n₀ n₁ n₂ (by have := data.hc r _ _ h; lia),
        Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · refine (ShortComplex.exact_iff_mono _ ((page X data r hr).shape _ _ h)).mpr ?_
    have := isIso_mapFourδ₄Toδ₃' X data r r' hrr' hr pq pq' hpq
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' h
    dsimp
    infer_instance

variable [X.HasSpectralSequence data] in
/-- The cokernel cofork `cc` is a colimit. -/
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.isColimitC
c** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSeque
nce.HomologyData`。
形式化陈述：isColimitCc (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel cofork `cc` is a colimit.
-/
noncomputable def isColimitCc (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsColimit (cc X data r r' hrr' hr pq pq'
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁') :=
  (ccSc_exact X data r r' hrr' hr pq pq' hpq i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' ..).gIsCokernel

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.fac** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.Homo
logyData`。
形式化陈述：fac (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.i₀_le'`：i
₀_le' {r r' : Int} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ) {i₀' i₀ : ι} (hi
₀' : i₀' = data.i₀ r' pq') (hi₀ : i₀ = data.i₀ r pq') : i₀'…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₃₃'`：le
₃₃' {r r' : Int} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ) {i₃ i₃' : ι} (hi₃ 
: i₃ = data.i₃ r pq') (hi₃' : i₃' = data.i₃ r' pq') : i₃ <…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma fac (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
  (kf X data r r' hrr' hr pq' pq'' i₀' i₀ i₁ i₂ i₃
      hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁').ι ≫
    (cc X data r r' hrr' hr pq pq' i₀ i₁ i₂ i₃ i₃'
      hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').π =
  X.mapFourδ₄Toδ₃' i₀' i₁ i₂ i₃ i₃' _ _ _ (data.le₃₃' hrr' hr pq' hi₃ hi₃') n₀ n₁ n₂ ≫
    X.mapFourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃'
      (data.i₀_le' hrr' hr pq' hi₀' hi₀) _ _ _ n₀ n₁ n₂ := by
  simp [← map_comp]
  rfl

end HomologyData

variable [X.HasSpectralSequence data]

set_option backward.isDefEq.respectTransparency false in
open HomologyData in
/-- The homology data for the short complex given by differentials on the
`r`th page of the spectral sequence which shows that the homology identifies
to an object on the next page. -/
@[simps!]
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.homologyData** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence`。
形式化陈述：homologyData (hn₁ : n₀ + 1 = n₁
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₃₃'`：le
₃₃' {r r' : Int} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ) {i₃ i₃' : ι} (hi₃ 
: i₃ = data.i₃ r pq') (hi₃' : i₃' = data.i₃ r' pq') : i₃ <…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.i₀_le'`：i
₀_le' {r r' : Int} (hrr' : r + 1 = r') (hr : r₀ <= r) (pq' : κ) {i₀' i₀ : ι} (hi
₀' : i₀' = data.i₀ r' pq') (hi₀ : i₀ = data.i₀ r pq') : i₀'…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁

--- 原说明 ---
The homology data for the short complex given by differentials on the
`r`th page of the spectral sequence which shows that the homology identifies
to an object on the next page.
-/
noncomputable def homologyData (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ((page X data r hr).sc' pq pq' pq'').HomologyData :=
  ShortComplex.HomologyData.ofEpiMonoFactorisation
    ((page X data r hr).sc' pq pq' pq'')
    (isLimitKf X data r r' hrr' hr pq' pq'' hpq' i₀' i₀ i₁ i₂ i₃
      hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁')
    (isColimitCc X data r r' hrr' hr pq pq' hpq i₀ i₁ i₂ i₃ i₃'
      hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁')
    (fac X data r r' hrr' hr pq pq' pq'' i₀' i₀ i₁ i₂ i₃ i₃'
      hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁')

/-- The homology of the differentials on a page of the spectral sequence identifies
to the objects on the next page. -/
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.homologyIso'** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence`。
形式化陈述：homologyIso' (hn₁ : n₀ + 1 = n₁
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂

--- 原说明 ---
The homology of the differentials on a page of the spectral sequence identifies
to the objects on the next page.
-/
noncomputable def homologyIso' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ((page X data r hr).sc' pq pq' pq'').homology ≅ (page X data r' (by lia)).X pq' :=
  (homologyData X data r r' hrr' hr pq pq' pq'' hpq hpq'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').left.homologyIso ≪≫
      (pageXIso X data _ (by lia) _ _ _ _ _ hi₀' hi₁ hi₂ hi₃' _ _ _ hn₁').symm

/-- The homology of the differentials on a page of the spectral sequence identifies
to the objects on the next page. -/
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequence.homologyIso** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequence`。
形式化陈述：homologyIso : (page X data r hr).homology pq' ≅ (page X data r' (hr.trans 
(by lia))).X pq'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology of the differentials on a page of the spectral sequence identifies
to the objects on the next page.
-/
noncomputable def homologyIso :
    (page X data r hr).homology pq' ≅
      (page X data r' (hr.trans (by lia))).X pq' :=
  homologyIso' X data r r' hrr' hr _ pq' _ rfl rfl _ _ _ _ _ _ rfl rfl
    rfl rfl rfl rfl (data.deg pq' - 1) (data.deg pq') _ rfl (by lia) rfl

end

end SpectralSequence

section

variable [X.HasSpectralSequence data] in
/-- The spectral sequence attached to a spectral object in an abelian category. -/
@[irreducible]
/-
**CategoryTheory.Abelian.SpectralObject.spectralSequence** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：spectralSequence : SpectralSequence C c r₀ where page
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The spectral sequence attached to a spectral object in an abelian category.
-/
noncomputable def spectralSequence : SpectralSequence C c r₀ where
  page := SpectralSequence.page X data
  iso r r' pq hrr' hr := SpectralSequence.homologyIso X data r r' hrr' hr pq

variable [X.HasSpectralSequence data]

unseal spectralSequence in
/-- The objects on the pages of a spectral sequence attached to a spectral object `X`
identifies an object `X.E`. -/
/-
**CategoryTheory.Abelian.SpectralObject.spectralSequencePageXIso** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：spectralSequencePageXIso (r : Int) (hr : r₀ <= r) (pq : κ) (i₀ i₁ i₂ i₃ : 
ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq) (h₃ : 
i₃ = data.i₃ r pq) (n₀ n₁ n₂ : Int) (h : n₁ = data.deg pq) (hn₁ : n₀ + 1 = n₁
参数：r : Int；hr : r₀ <= r；pq : κ；i₀ i₁ i₂ i₃ : ι；h₀ : i₀ = data.i₀ r pq；h₁ : i₁ = 
data.i₁ pq；h₂ : i₂ = data.i₂ pq；h₃ : i₃ = data.i₃ r pq；n₀ n₁ n₂ : Int；h : n₁ = d
ata.deg pq。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The objects on the pages of a spectral sequence attached to a spectral object `X
`
identifies an object `X.E`.
-/
noncomputable def spectralSequencePageXIso (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq)
    (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ((X.spectralSequence data).page r).X pq ≅
      X.E (homOfLE (data.le₀₁' r hr pq h₀ h₁)) (homOfLE (data.le₁₂' pq h₁ h₂))
        (homOfLE (data.le₂₃' r hr pq h₂ h₃)) n₀ n₁ n₂ :=
  SpectralSequence.pageXIso X data _ hr _ _ _ _ _ h₀ h₁ h₂ h₃ _ _ _ h

unseal spectralSequence in
/-
**CategoryTheory.Abelian.SpectralObject.spectralSequence_page_d_eq** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：spectralSequence_page_d_eq (r : Int) (hr : r₀ <= r) (pq pq' : κ) (hpq : (c
 r).Rel pq pq') {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶
 i₃) (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (h₀ : i₀ = data.i₀ r pq') (h₁ : i₁ = data.i₁ 
pq') (h₂ : i₂ = data.i₀ r pq) (h₃ : i₃ = data.i₁ pq) (h₄ : i₄ = data.i₂ pq) (h₅ 
: i₅ = data.i₃ r pq) (n₀ n₁ n₂ n₃ : Int) (hn₁' : n₁ = data.deg pq) (hn₁ : n₀ + 1
 = n₁
参数：r : Int；hr : r₀ <= r；pq pq' : κ；hpq : (c r).Rel pq pq'；f₁ : i₀ ⟶ i₁；f₂ : i₁ ⟶
 i₂；f₃ : i₂ ⟶ i₃；f₄ : i₃ ⟶ i₄；f₅ : i₄ ⟶ i₅；h₀ : i₀ = data.i₀ r pq'；h₁ : i₁ = dat
a.i₁ pq'；h₂ : i₂ = data.i₀ r pq；h₃ : i₃ = data.i₁ pq；h₄ : i₄ = data.i₂ pq；h₅ : i
₅ = data.i₃ r pq；n₀ n₁ n₂ n₃ : Int；hn₁' : n₁ = data.deg pq。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD_eq`：pageD_e
q (r : Int) (hr : r₀ <= r) (pq pq' : κ) (hpq : (c r).Rel pq pq') {i₀ i₁ i₂ i₃ i₄
 i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)…
-/
lemma spectralSequence_page_d_eq (r : ℤ) (hr : r₀ ≤ r)
    (pq pq' : κ) (hpq : (c r).Rel pq pq')
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
    (h₀ : i₀ = data.i₀ r pq') (h₁ : i₁ = data.i₁ pq')
    (h₂ : i₂ = data.i₀ r pq)
    (h₃ : i₃ = data.i₁ pq) (h₄ : i₄ = data.i₂ pq) (h₅ : i₅ = data.i₃ r pq)
    (n₀ n₁ n₂ n₃ : ℤ) (hn₁' : n₁ = data.deg pq) (hn₁ : n₀ + 1 = n₁ := by lia)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    ((X.spectralSequence data).page r).d pq pq' =
      (X.spectralSequencePageXIso data r hr _ _ _ _ _ h₂ h₃ h₄ h₅ _ _ _ hn₁').hom ≫
        X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
          (X.spectralSequencePageXIso data r hr _ _ _ _ _ h₀ h₁
            (by rw [h₂, ← data.hc₀₂ r pq pq' hpq]) (by rw [h₃, data.hc₁₃ r pq pq' hpq]) _ _ _
              (by simpa only [← hn₂, hn₁'] using data.hc r pq pq' hpq)).inv :=
  SpectralSequence.pageD_eq _ _ _ hr _ _ hpq ..
/-
**CategoryTheory.Abelian.SpectralObject.isZero_spectralSequence_page_X_iff** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：isZero_spectralSequence_page_X_iff (r : Int) (hr : r₀ <= r) (pq : κ) (i₀ i
₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ 
pq) (h₃ : i₃ = data.i₃ r pq) (n₀ n₁ n₂ : Int) (h : n₁ = data.deg pq) (hn₁ : n₀ +
 1 = n₁
参数：r : Int；hr : r₀ <= r；pq : κ；i₀ i₁ i₂ i₃ : ι；h₀ : i₀ = data.i₀ r pq；h₁ : i₁ = 
data.i₁ pq；h₂ : i₂ = data.i₂ pq；h₃ : i₃ = data.i₃ r pq；n₀ n₁ n₂ : Int；h : n₁ = d
ata.deg pq。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isZero_iff`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (e : X ≅ Y),   CategoryTheory.Limits.IsZero X ↔ Catego
ryTheory.Limits.IsZ…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
-/
lemma isZero_spectralSequence_page_X_iff (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq) (hn₁ : n₀ + 1 = n₁ := by lia)
    (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsZero (((X.spectralSequence data).page r).X pq) ↔
      IsZero (X.E (homOfLE (data.le₀₁' r hr pq h₀ h₁))
        (homOfLE (data.le₁₂' pq h₁ h₂))
        (homOfLE (data.le₂₃' r hr pq h₂ h₃)) n₀ n₁ n₂) :=
  Iso.isZero_iff (X.spectralSequencePageXIso data r hr pq i₀ i₁ i₂ i₃
    h₀ h₁ h₂ h₃ n₀ n₁ n₂ h)
/-
**CategoryTheory.Abelian.SpectralObject.isZero_spectralSequence_page_X_of_isZero
_H** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：isZero_spectralSequence_page_X_of_isZero_H (r : Int) (hr : r₀ <= r) (pq : 
κ) (n : Int) (hn : n = data.deg pq) (i₁ i₂ : ι) (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ 
= data.i₂ pq) (h : IsZero ((X.H n).obj (mk₁ (homOfLE (by simpa only [h₁, h₂] usi
ng data.le₁₂ pq) : i₁ ⟶ i₂)))) : IsZero (((X.spectralSequence data).page r).X pq
)
参数：r : Int；hr : r₀ <= r；pq : κ；n : Int；hn : n = data.deg pq；i₁ i₂ : ι；h₁ : i₁ = 
data.i₁ pq；h₂ : i₂ = data.i₂ pq；h : IsZero ((X.H n).obj (mk₁ (homOfLE (by simpa 
only [h₁, h₂] using data.le₁₂ pq) : i₁ ⟶ i₂)))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.isZero_spectralSequence_page_X_iff
`：isZero_spectralSequence_page_X_iff (r : Int) (hr : r₀ <= r) (pq : κ) (i₀ i₁ i₂
 i₃ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq) (h₂ :…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.isZero_E_of_isZero_H`：isZero_E_of_
isZero_H (h : IsZero ((X.H n₁).obj (mk₁ f₂))) (hn₁ : n₀ + 1 = n₁
-/
lemma isZero_spectralSequence_page_X_of_isZero_H (r : ℤ) (hr : r₀ ≤ r)
    (pq : κ) (n : ℤ) (hn : n = data.deg pq)
    (i₁ i₂ : ι) (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (h : IsZero ((X.H n).obj
      (mk₁ (homOfLE (by simpa only [h₁, h₂] using data.le₁₂ pq) : i₁ ⟶ i₂)))) :
    IsZero (((X.spectralSequence data).page r).X pq) := by
  rw [X.isZero_spectralSequence_page_X_iff data r hr pq
    _ i₁ i₂ _ rfl h₁ h₂ rfl (n - 1) n (n + 1) hn]
  exact isZero_E_of_isZero_H _ _ _ _ _ _ _ h
/-
**CategoryTheory.Abelian.SpectralObject.isZero_spectralSequence_page_X_of_isZero
_H'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：isZero_spectralSequence_page_X_of_isZero_H' (r : Int) (hr : r₀ <= r) (pq :
 κ) (h : IsZero ((X.H (data.deg pq)).obj (mk₁ (homOfLE (data.le₁₂ pq))))) : IsZe
ro (((X.spectralSequence data).page r).X pq)
参数：r : Int；hr : r₀ <= r；pq : κ；h : IsZero ((X.H (data.deg pq)).obj (mk₁ (homOfLE
 (data.le₁₂ pq))))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂`：∀ {
ι : Type u_2} {κ : Type u_3} [inst : Preorder ι] {c : ℤ → ComplexShape κ} {r₀ : 
ℤ}   (self : CategoryTheory.Abelian.SpectralObject.Spectr…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.isZero_spectralSequence_page_X_of_
isZero_H`：isZero_spectralSequence_page_X_of_isZero_H (r : Int) (hr : r₀ <= r) (p
q : κ) (n : Int) (hn : n = data.deg pq) (i₁ i₂ : ι) (h₁ : i₁ = data.i₁…
-/
lemma isZero_spectralSequence_page_X_of_isZero_H' (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (h : IsZero ((X.H (data.deg pq)).obj (mk₁ (homOfLE (data.le₁₂ pq))))) :
    IsZero (((X.spectralSequence data).page r).X pq) :=
  X.isZero_spectralSequence_page_X_of_isZero_H data r hr pq _ rfl _ _ rfl rfl h

unseal spectralSequence in
/-- The short complex of the `r`th page of the spectral sequence on position `pq'`
identifies to the short complex given by the differentials of the spectral object.
Then, the homology of this short complex can be computed using
`SpectralSequence.dHomologyIso`.
(This only applies in the favourable case when there are `pq` and `pq''` such
that `(c r).Rel pq pq'` and `(c r).Rel pq' pq''` hold.) -/
/-
**CategoryTheory.Abelian.SpectralObject.spectralSequencePageSc'Iso** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：{C : Type u_1} →   {ι : Type u_2} →     {κ : Type u_3} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Abelian C]
 →           [inst_2 : Preorder ι] →             (X : CategoryTheory.Abelian.Spe
ctralObject C ι) →               {c : ℤ → ComplexShape κ} →                 {r₀ 
: ℤ} →                   (data : CategoryTheory.Abelian.SpectralObject.SpectralS
equenceDataCore ι c r₀) →                     [inst_3 : X.HasSpectralSequence da
ta] →                       (r : ℤ) →                         (hr : r₀ ≤ r) →   
                        (pq pq' pq'' : κ) →                             (hpq : (
c r).Rel pq pq') →                               (hpq' : (c r).Rel pq' pq'') →  
                               (n₀ n₁ n₂ n₃ n₄ : ℤ) →                           
        n₂ = data.deg pq' →                                     (hn₁ :          
                               autoParam (n₀ + 1 = n₁)                          
                 CategoryTheory.Abelian.SpectralObject.spectralSequencePageSc'Is
o._auto_1) →                                       (hn₂ :                       
                    autoParam (n₁ + 1 = n₂)                                     
        CategoryTheory.Abelian.SpectralObject.spectralSequencePageSc'Iso._auto_3
) →                                         (hn₃ :                              
               autoParam (n₂ + 1 = n₃)                                          
     CategoryTheory.Abelian.SpectralObject.spectralSequencePageSc'Iso._auto_5) →
                                           (hn₄ :                               
                autoParam (n₃ + 1 = n₄)                                         
        CategoryTheory.Abelian.SpectralObject.spectralSequencePageSc'Iso._auto_7
) →                                             ((X.spectralSequence data).page 
r ⋯).sc' pq pq' pq'' ≅                                               X.dShortCom
plex (CategoryTheory.homOfLE ⋯) (CategoryTheory.homOfLE ⋯)                      
                           (CategoryTheory.homOfLE ⋯) (CategoryTheory.homOfLE ⋯)
                                                 (CategoryTheory.homOfLE ⋯) (Cat
egoryTheory.homOfLE ⋯)                                                 (Category
Theory.homOfLE ⋯) n₀ n₁ n₂ n₃ n₄ ⋯ ⋯ ⋯ ⋯
参数：X : CategoryTheory.Abelian.SpectralObject C ι；data : CategoryTheory.Abelian.S
pectralObject.SpectralSequenceDataCore ι c r₀；r : ℤ；hr : r₀ ≤ r；pq pq' pq'' : κ；
hpq : (c r).Rel pq pq'；hpq' : (c r).Rel pq' pq''；n₀ n₁ n₂ n₃ n₄ : ℤ；hn₁ :       
                                  autoParam (n₀ + 1 = n₁)                       
                    CategoryTheory.Abelian.SpectralObject.spectralSequencePageSc
'Iso._auto_1；hn₂ :                                           autoParam (n₁ + 1 =
 n₂)                                             CategoryTheory.Abelian.Spectral
Object.spectralSequencePageSc'Iso._auto_3；hn₃ :                                 
            autoParam (n₂ + 1 = n₃)                                             
  CategoryTheory.Abelian.SpectralObject.spectralSequencePageSc'Iso._auto_5；hn₄ :
                                               autoParam (n₃ + 1 = n₄)          
                                       CategoryTheory.Abelian.SpectralObject.spe
ctralSequencePageSc'Iso._auto_7；(X.spectralSequence data).page r ⋯；CategoryTheor
y.homOfLE ⋯；CategoryTheory.homOfLE ⋯；CategoryTheory.homOfLE ⋯；CategoryTheory.hom
OfLE ⋯；CategoryTheory.homOfLE ⋯；CategoryTheory.homOfLE ⋯；CategoryTheory.homOfLE 
⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex of the `r`th page of the spectral sequence on position `pq'`
identifies to the short complex given by the differentials of the spectral objec
t.
Then, the homology of this short complex can be computed using
`SpectralSequence.dHomologyIso`.
(This only applies in the favourable case when there are `pq` and `pq''` such
that `(c r).Rel pq pq'` and `(c r).Rel pq' pq''` hold.)
-/
noncomputable def spectralSequencePageSc'Iso (r : ℤ) (hr : r₀ ≤ r) (pq pq' pq'' : κ)
    (hpq : (c r).Rel pq pq') (hpq' : (c r).Rel pq' pq'')
    (n₀ n₁ n₂ n₃ n₄ : ℤ)
    (hn₂' : n₂ = data.deg pq')
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) (hn₄ : n₃ + 1 = n₄ := by lia) :
    ((X.spectralSequence data).page r).sc' pq pq' pq'' ≅
      X.dShortComplex (homOfLE (data.le₀₁ r pq''))
        (homOfLE (data.le₁₂ pq'')) (homOfLE (data.le₂₃ r pq''))
        (homOfLE (by simpa only [← data.hc₁₃ r pq' pq'' hpq', data.hc₀₂ r pq pq' hpq]
          using data.le₁₂ pq')) (homOfLE (data.le₀₁ r pq))
        (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
        n₀ n₁ n₂ n₃ n₄ :=
  SpectralSequence.shortComplexIso _ _ _ hr _ _ _ hpq hpq' _ _ _ _ _ _ _ _ _ hn₂'

section

variable (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
  (pq pq' pq'' : κ) (hpq : (c r).prev pq' = pq) (hpq' : (c r).next pq' = pq'')
  (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
  (hi₀' : i₀' = data.i₀ r' pq')
  (hi₀ : i₀ = data.i₀ r pq')
  (hi₁ : i₁ = data.i₁ pq')
  (hi₂ : i₂ = data.i₂ pq')
  (hi₃ : i₃ = data.i₃ r pq')
  (hi₃' : i₃' = data.i₃ r' pq')
  (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq')


#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
unseal spectralSequence in
/-- The homology data for the short complexes given by the differentials
of a spectral sequence attached to a spectral object in an abelian category. -/
@[simps! left_K left_H left_π right_Q right_H right_ι iso_hom iso_inv]
/-
**CategoryTheory.Abelian.SpectralObject.spectralSequenceHomologyData** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：spectralSequenceHomologyData (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology data for the short complexes given by the differentials
of a spectral sequence attached to a spectral object in an abelian category.
-/
noncomputable def spectralSequenceHomologyData
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (((X.spectralSequence data).page r hr).sc' pq pq' pq'').HomologyData :=
  SpectralSequence.homologyData X data r r' hrr' hr
    pq pq' pq'' hpq hpq' i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁'

unseal spectralSequence in
@[simp]
/-
**CategoryTheory.Abelian.SpectralObject.spectralSequenceHomologyData_left_i** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：spectralSequenceHomologyData_left_i (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma spectralSequenceHomologyData_left_i
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).left.i =
    X.mapFourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃
      (data.i₀_le' hrr' hr pq' hi₀' hi₀) _ _ _ n₀ n₁ n₂ ≫
        (X.spectralSequencePageXIso data r hr pq'
          i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁').inv :=
  rfl

unseal spectralSequence in
@[simp]
/-
**CategoryTheory.Abelian.SpectralObject.spectralSequenceHomologyData_right_p** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：spectralSequenceHomologyData_right_p (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma spectralSequenceHomologyData_right_p
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).right.p =
    (X.spectralSequencePageXIso data r hr pq'
      i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁').hom ≫
        X.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃' _ _ _
          (data.le₃₃' hrr' hr pq' hi₃ hi₃') n₀ n₁ n₂ := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.spectralSequenceHomologyData_right_homol
ogyIso_eq_left_homologyIso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.Spe
ctralObject`。
形式化陈述：spectralSequenceHomologyData_right_homologyIso_eq_left_homologyIso (hn₁ : 
n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.HomologyData.right_homologyIso_eq_left_homol
ogyIso_trans_iso`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst
_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortComp…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma spectralSequenceHomologyData_right_homologyIso_eq_left_homologyIso
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').right.homologyIso =
    (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').left.homologyIso := by
  ext1
  simp [ShortComplex.HomologyData.right_homologyIso_eq_left_homologyIso_trans_iso]

set_option backward.isDefEq.respectTransparency.types false in
unseal spectralSequence in
/-
**CategoryTheory.Abelian.SpectralObject.spectralSequence_iso** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：spectralSequence_iso (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomologicalComplex.homologyIsoSc'_eq_refl`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {ι : Type u_2} {c : Com…
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma spectralSequence_iso (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequence data).iso r r' pq' =
    ((X.spectralSequence data).page r).homologyIsoSc' pq pq' pq'' hpq hpq' ≪≫
      (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').left.homologyIso ≪≫
        (X.spectralSequencePageXIso data r' (by lia) _ _ _ _ _
          hi₀' hi₁ hi₂ hi₃' _ _ _ hn₁').symm := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  obtain rfl : n₂ = n₁ + 1 := by lia
  subst hpq hpq' hn₁' hi₀ hi₁ hi₂ hi₃ hi₀' hi₃'
  ext
  simp [spectralSequencePageXIso, spectralSequence, spectralSequenceHomologyData,
    SpectralSequence.homologyIso, SpectralSequence.homologyIso']

end

end

section

variable (Y : SpectralObject C EInt)

/-- The `E₂` cohomological spectral sequence indexed by `ℤ × ℤ` attached to
a spectral object indexed by `EInt`. -/
/-
**CategoryTheory.Abelian.SpectralObject.E** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Abelian.SpectralObject`。
形式化陈述：E (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `E₂` cohomological spectral sequence indexed by `ℤ × ℤ` attached to
a spectral object indexed by `EInt`.
-/
noncomputable abbrev E₂SpectralSequence : E₂CohomologicalSpectralSequence C :=
  Y.spectralSequence coreE₂Cohomological

section

variable [Y.IsFirstQuadrant]

/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hq : q < 0) :
    IsZero ((Y.E₂SpectralSequence.page r).X ⟨p, q⟩) :=
  isZero_spectralSequence_page_X_of_isZero_H' _ _ _ hr _
    (Y.isZero₁_of_isFirstQuadrant _ _ _ (by simp; lia) _)
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hp : p < 0) :
    IsZero ((Y.E₂SpectralSequence.page r).X ⟨p, q⟩) :=
  isZero_spectralSequence_page_X_of_isZero_H' _ _ _ hr _
    (Y.isZero₂_of_isFirstQuadrant _ _ _ _ (by simp; lia))

/-- The `E₂` cohomological spectral sequence indexed by `ℕ × ℕ` attached to
a first quadrant spectral object indexed by `EInt`. -/
/-
**CategoryTheory.Abelian.SpectralObject.E** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Abelian.SpectralObject`。
形式化陈述：E (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `E₂` cohomological spectral sequence indexed by `ℕ × ℕ` attached to
a first quadrant spectral object indexed by `EInt`.
-/
noncomputable abbrev E₂SpectralSequenceNat := Y.spectralSequence coreE₂CohomologicalNat

end

section

variable [Y.IsThirdQuadrant]

/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hq : 0 < q) :
    IsZero ((Y.E₂SpectralSequence.page r).X ⟨p, q⟩) := by
  apply isZero_spectralSequence_page_X_of_isZero_H' _ _ _ hr
  apply Y.isZero₁_of_isThirdQuadrant
  simp
  lia
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hp : 0 < p) :
    IsZero ((Y.E₂SpectralSequence.page r).X ⟨p, q⟩) := by
  apply isZero_spectralSequence_page_X_of_isZero_H' _ _ _ hr
  apply Y.isZero₂_of_isThirdQuadrant
  simp
  lia

/-- The `E₂` homological spectral sequence indexed by `ℕ × ℕ` attached to
a third quadrant spectral object indexed by `EInt`. -/
/-
**CategoryTheory.Abelian.SpectralObject.E** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Abelian.SpectralObject`。
形式化陈述：E (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `E₂` homological spectral sequence indexed by `ℕ × ℕ` attached to
a third quadrant spectral object indexed by `EInt`.
-/
noncomputable abbrev E₂HomologicalSpectralSequenceNat := Y.spectralSequence coreE₂HomologicalNat

end

end

end SpectralObject

end Abelian

end CategoryTheory

