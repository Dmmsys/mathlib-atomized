/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# The first page of the spectral sequence of a spectral object

Let `ι` be a preordered type, `X` a spectral object in an abelian
category indexed by `ι`. Let `data : SpectralSequenceDataCore ι c r₀`.
Assume that `X.HasSpectralSequence data` holds. In this file,
we introduce a property `data.HasFirstPageComputation` which allows
to "compute" the objects of the `r₀`th page of the spectral
sequence attached to `X` in terms of objects of the form `X.H`,
and we compute the differential on the first page in terms of `X.δ`,
see `spectralSequence_first_page_d_eq`.

-/

@[expose] public section

namespace CategoryTheory

open Category ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι κ : Type*} [Category C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (data : SpectralSequenceDataCore ι c r₀)

namespace SpectralSequenceDataCore

/-- Given `data : SpectralSequenceDataCore ι c r₀`, this is the property
that on the page `r₀`, indices `i₀` and `i₁` are equal,
and indices `i₂` and `i₃` are equal. This condition allows
to express the objects of the `r₀`th page of the spectral sequences
obtained using a spectral object `X` indexed by `ι` and `data` as objects
of the form `X.H`, see `SpectralObject.spectralSequenceFirstPageXIso`. -/
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.HasFirstPageCom
putation** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Abelian.SpectralObject.Spec
tralSequenceDataCore`。
形式化陈述：{ι : Type u_2} →   {κ : Type u_3} →     [inst : Preorder ι] →       {c : ℤ
 → ComplexShape κ} → {r₀ : ℤ} → CategoryTheory.Abelian.SpectralObject.SpectralSe
quenceDataCore ι c r₀ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `data : SpectralSequenceDataCore ι c r₀`, this is the property
that on the page `r₀`, indices `i₀` and `i₁` are equal,
and indices `i₂` and `i₃` are equal. This condition allows
to express the objects of the `r₀`th page of the spectral sequences
obtained using a spectral object `X` indexed by `ι` and `data` as objects
of the form `X.H`, see `SpectralObject.spectralSequenceFirstPageXIso`.
-/
class HasFirstPageComputation : Prop where
  hi₀₁ (pq : κ) : data.i₀ r₀ pq = data.i₁ pq
  hi₂₃ (pq : κ) : data.i₂ pq = data.i₃ r₀ pq

export HasFirstPageComputation (hi₀₁ hi₂₃)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.** 是 Mathlib 中的
一个实例，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : coreE₂Cohomological.HasFirstPageComputation where
  hi₀₁ pq := by dsimp; lia
  hi₂₃ pq := by dsimp; lia

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.** 是 Mathlib 中的
一个实例，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : coreE₂CohomologicalNat.HasFirstPageComputation where
  hi₀₁ pq := by dsimp; lia
  hi₂₃ pq := by dsimp; lia

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.** 是 Mathlib 中的
一个实例，位于命名空间 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : coreE₂HomologicalNat.HasFirstPageComputation where
  hi₀₁ pq := by dsimp; lia
  hi₂₃ pq := by dsimp; lia

end SpectralSequenceDataCore

variable [data.HasFirstPageComputation] [X.HasSpectralSequence data]

/-- If `data : SpectralSequenceDataCore ι c r₀` is such that
`data.HasFirstPageComputation` holds, this is an isomorphism which
allows to "compute" the objects on the `r₀`th page of the spectral sequence
obtained from a spectral object `X` indexed by `ι` using data as objects
of the form `X.H`. See also `spectralSequence_first_page_d_eq` for the relation
between the differentials of the first page of the spectral sequence and `X.δ`. -/
/-
**CategoryTheory.Abelian.SpectralObject.spectralSequenceFirstPageXIso** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：spectralSequenceFirstPageXIso (pq : κ) (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq)
 (hi₂ : i₂ = data.i₂ pq) (n : Int) (hn : n = data.deg pq) : ((X.spectralSequence
 data).page r₀).X pq ≅ (X.H n).obj (mk₁ (homOfLE (data.le₁₂' pq hi₁ hi₂)))
参数：pq : κ；i₁ i₂ : ι；hi₁ : i₁ = data.i₁ pq；hi₂ : i₂ = data.i₂ pq；n : Int；hn : n =
 data.deg pq。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂

--- 原说明 ---
If `data : SpectralSequenceDataCore ι c r₀` is such that
`data.HasFirstPageComputation` holds, this is an isomorphism which
allows to "compute" the objects on the `r₀`th page of the spectral sequence
obtained from a spectral object `X` indexed by `ι` using data as objects
of the form `X.H`. See also `spectralSequence_first_page_d_eq` for the relation
between the differentials of the first page of the spectral sequence and `X.δ`.
-/
noncomputable def spectralSequenceFirstPageXIso (pq : κ)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n : ℤ) (hn : n = data.deg pq) :
    ((X.spectralSequence data).page r₀).X pq ≅
      (X.H n).obj (mk₁ (homOfLE (data.le₁₂' pq hi₁ hi₂))) :=
  X.spectralSequencePageXIso data _ (by rfl) _ _ _ _ _
    (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) _ _ _ hn ≪≫
      X.EIsoH (homOfLE _) (n - 1) n (n + 1)

@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.spectralSequenceFirstPageXIso_hom** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：spectralSequenceFirstPageXIso_hom (pq : κ) (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁
 pq) (hi₂ : i₂ = data.i₂ pq) (n₀ n₁ n₂ : Int) (hn₁' : n₁ = data.deg pq) (hn₁ : n
₀ + 1 = n₁
参数：pq : κ；i₁ i₂ : ι；hi₁ : i₁ = data.i₁ pq；hi₂ : i₂ = data.i₂ pq；n₀ n₁ n₂ : Int；h
n₁' : n₁ = data.deg pq。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma spectralSequenceFirstPageXIso_hom (pq : κ)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequenceFirstPageXIso data pq i₁ i₂ hi₁ hi₂ n₁ hn₁').hom =
      (X.spectralSequencePageXIso data r₀ (by rfl) _ _ _ _ _
        (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) _ _ _ hn₁').hom ≫
          (X.EIsoH _ n₀ n₁ n₂ hn₁ hn₂).hom := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  obtain rfl := hn₂
  rfl

@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.spectralSequenceFirstPageXIso_inv** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：spectralSequenceFirstPageXIso_inv (pq : κ) (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁
 pq) (hi₂ : i₂ = data.i₂ pq) (n₀ n₁ n₂ : Int) (hn₁' : n₁ = data.deg pq) (hn₁ : n
₀ + 1 = n₁
参数：pq : κ；i₁ i₂ : ι；hi₁ : i₁ = data.i₁ pq；hi₂ : i₂ = data.i₂ pq；n₀ n₁ n₂ : Int；h
n₁' : n₁ = data.deg pq。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₀₁'`：le
₀₁' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₀ i₁ : ι} (hi₀ : i₀ = data.i₀ r pq') (h
i₁ : i₁ = data.i₁ pq') : i₀ <= i₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₂₃'`：le
₂₃' (r : Int) (hr : r₀ <= r) (pq' : κ) {i₂ i₃ : ι} (hi₂ : i₂ = data.i₂ pq') (hi₃
 : i₃ = data.i₃ r pq') : i₂ <= i₃
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma spectralSequenceFirstPageXIso_inv (pq : κ)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequenceFirstPageXIso data pq i₁ i₂ hi₁ hi₂ n₁ hn₁').inv =
      (X.EIsoH _ n₀ n₁ n₂ hn₁ hn₂).inv ≫
      (X.spectralSequencePageXIso data r₀ (by rfl) _ _ _ _ _
        (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) _ _ _ hn₁').inv := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  obtain rfl := hn₂
  rfl

@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.spectralSequence_first_page_d_eq** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：spectralSequence_first_page_d_eq (pq pq' : κ) (hpq : (c r₀).Rel pq pq') (i
 j k : ι) (hi : i = data.i₁ pq') (hj : j = data.i₁ pq) (hk : k = data.i₂ pq) (n 
n' : Int) (hn : n = data.deg pq) (hn' : n + 1 = n'
参数：pq pq' : κ；hpq : (c r₀).Rel pq pq'；i j k : ι；hi : i = data.i₁ pq'；hj : j = da
ta.i₁ pq；hk : k = data.i₂ pq；n n' : Int；hn : n = data.deg pq。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.le₁₂'`：le
₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') : i₁
 <= i₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.spectralSequenceFirstPageXIso_hom`
：spectralSequenceFirstPageXIso_hom (pq : κ) (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) 
(hi₂ : i₂ = data.i₂ pq) (n₀ n₁ n₂ : Int) (hn₁' : n₁ = data.de…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.spectralSequenceFirstPageXIso_inv`
：spectralSequenceFirstPageXIso_inv (pq : κ) (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) 
(hi₂ : i₂ = data.i₂ pq) (n₀ n₁ n₂ : Int) (hn₁' : n₁ = data.de…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Abelian.SpectralObject.d_EIsoH_hom_assoc`：∀ {C : Type u_1
} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用引理 `CategoryTheory.Abelian.SpectralObject.spectralSequence_page_d_eq`：spectr
alSequence_page_d_eq (r : Int) (hr : r₀ <= r) (pq pq' : κ) (hpq : (c r).Rel pq p
q') {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ …
-/
lemma spectralSequence_first_page_d_eq (pq pq' : κ)
    (hpq : (c r₀).Rel pq pq') (i j k : ι)
    (hi : i = data.i₁ pq') (hj : j = data.i₁ pq) (hk : k = data.i₂ pq)
    (n n' : ℤ) (hn : n = data.deg pq) (hn' : n + 1 = n' := by lia) :
    ((X.spectralSequence data).page r₀).d pq pq' =
      (X.spectralSequenceFirstPageXIso data pq j k hj hk n hn).hom ≫
      X.δ
        (homOfLE
          (by simpa only [hi, hj, data.hc₁₃ r₀ pq pq' hpq, ← data.hi₂₃ pq']
            using data.le₁₂ pq'))
        (homOfLE (by simpa only [hj, hk] using data.le₁₂ pq)) n n' hn' ≫
      (X.spectralSequenceFirstPageXIso data pq' i j hi
        (by rw [hj, ← data.hc₀₂ r₀ pq pq' hpq, data.hi₀₁ pq]) n'
        (by rw [← hn', hn, data.hc r₀ pq pq' hpq])).inv := by
  simpa [X.spectralSequenceFirstPageXIso_hom data pq j k hj hk (n - 1) n n',
    ← X.d_EIsoH_hom_assoc _ _ (n - 1) n n' (n' + 1),
    X.spectralSequenceFirstPageXIso_inv data pq' i j hi _ _ n' _ _ hn' _]
    using spectralSequence_page_d_eq _ _ _ _ _ _ hpq ..

end SpectralObject

end Abelian

end CategoryTheory

