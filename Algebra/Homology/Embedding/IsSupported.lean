/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Support of homological complexes

Given an embedding `e : c.Embedding c'` of complex shapes, we say
that `K : HomologicalComplex C c'` is supported (resp. strictly supported) on `e`
if `K` is exact in degree `i'` (resp. `K.X i'` is zero) whenever `i'` is
not of the form `e.f i`. This defines two typeclasses `K.IsSupported e`
and `K.IsStrictlySupported e`.

We also define predicates `K.IsSupportedOutside e` and `K.IsStrictlySupportedOutside e`
when the conditions above are satisfied for those `i'` that are of the form `e.f i`.
(These two predicates are not made typeclasses because in most practical applications,
they are equivalent to `K.IsSupported e'` or `K.IsStrictlySupported e'` for a
complementary embedding `e'`.)

-/

public section

open CategoryTheory Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

section

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (e' : K ≅ L) (φ : K ⟶ L) (e : c.Embedding c')

/-- If `K : HomologicalComplex C c'`, then `K.IsStrictlySupported e` holds for
an embedding `e : c.Embedding c'` of complex shapes if `K.X i'` is zero
whenever `i'` is not of the form `e.f i` for some `i`. -/
/-
**HomologicalComplex.IsStrictlySupported** 是 Mathlib 中的一个归纳类型，位于命名空间 `Homologica
lComplex`。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {c : ComplexShape ι} →       {c' 
: ComplexShape ι'} →         {C : Type u_3} →           [inst : CategoryTheory.C
ategory.{v_1, u_3} C] →             [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C] → HomologicalComplex C c' → c.Embedding c' → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `K : HomologicalComplex C c'`, then `K.IsStrictlySupported e` holds for
an embedding `e : c.Embedding c'` of complex shapes if `K.X i'` is zero
whenever `i'` is not of the form `e.f i` for some `i`.
-/
class IsStrictlySupported : Prop where
  isZero (i' : ι') (hi' : ∀ i, e.f i ≠ i') : IsZero (K.X i')
/-
**HomologicalComplex.isZero_X_of_isStrictlySupported** 是 Mathlib 中的一个引理，位于命名空间 `
HomologicalComplex`。
形式化陈述：isZero_X_of_isStrictlySupported [K.IsStrictlySupported e] (i' : ι') (hi' :
 forall i, e.f i != i') : IsZero (K.X i')
参数：i' : ι'；hi' : forall i, e.f i != i'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.IsStrictlySupported.isZero`：∀ {ι : Type u_1} {ι' : Ty
pe u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   {inst : Cat
egoryTheory.Category.{v_1, u_3} C} …
-/
lemma isZero_X_of_isStrictlySupported [K.IsStrictlySupported e]
    (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero (K.X i') :=
  IsStrictlySupported.isZero i' hi'

include e' in
variable {K L} in
/-
**HomologicalComplex.isStrictlySupported_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Homol
ogicalComplex`。
形式化陈述：isStrictlySupported_of_iso [K.IsStrictlySupported e] : L.IsStrictlySupport
ed e where isZero i' hi'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用引理 `HomologicalComplex.isZero_X_of_isStrictlySupported`：isZero_X_of_isStrict
lySupported [K.IsStrictlySupported e] (i' : ι') (hi' : forall i, e.f i != i') : 
IsZero (K.X i')
-/
lemma isStrictlySupported_of_iso [K.IsStrictlySupported e] : L.IsStrictlySupported e where
  isZero i' hi' := (K.isZero_X_of_isStrictlySupported e i' hi').of_iso
    ((eval _ _ i').mapIso e'.symm)

@[simp]
/-
**HomologicalComplex.isStrictlySupported_op_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homol
ogicalComplex`。
形式化陈述：isStrictlySupported_op_iff : K.op.IsStrictlySupported e.op ↔ K.IsStrictlyS
upported e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.unop`：unop {X : Cᵒᵖ} (h : IsZero X) : IsZer
o (Opposite.unop X)
· 使用引理 `HomologicalComplex.isZero_X_of_isStrictlySupported`：isZero_X_of_isStrict
lySupported [K.IsStrictlySupported e] (i' : ι') (hi' : forall i, e.f i != i') : 
IsZero (K.X i')
· 使用定理 `CategoryTheory.Limits.IsZero.op`：op (h : IsZero X) : IsZero (Opposite.op
 X)
-/
lemma isStrictlySupported_op_iff :
    K.op.IsStrictlySupported e.op ↔ K.IsStrictlySupported e :=
  ⟨(fun _ ↦ ⟨fun i' hi' ↦ (K.op.isZero_X_of_isStrictlySupported e.op i' hi').unop⟩),
    (fun _ ↦ ⟨fun i' hi' ↦ (K.isZero_X_of_isStrictlySupported e i' hi').op⟩)⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [K.IsStrictlySupported e] : K.op.IsStrictlySupported e.op := by
  rw [isStrictlySupported_op_iff]
  infer_instance

/-- If `K : HomologicalComplex C c'`, then `K.IsStrictlySupported e` holds for
an embedding `e : c.Embedding c'` of complex shapes if `K` is exact at `i'`
whenever `i'` is not of the form `e.f i` for some `i`. -/
@[mk_iff]
/-
**HomologicalComplex.IsSupported** 是 Mathlib 中的一个归纳类型，位于命名空间 `HomologicalComplex
`。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {c : ComplexShape ι} →       {c' 
: ComplexShape ι'} →         {C : Type u_3} →           [inst : CategoryTheory.C
ategory.{v_1, u_3} C] →             [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C] → HomologicalComplex C c' → c.Embedding c' → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `K : HomologicalComplex C c'`, then `K.IsStrictlySupported e` holds for
an embedding `e : c.Embedding c'` of complex shapes if `K` is exact at `i'`
whenever `i'` is not of the form `e.f i` for some `i`.
-/
class IsSupported : Prop where
  exactAt (i' : ι') (hi' : ∀ i, e.f i ≠ i') : K.ExactAt i'
/-
**HomologicalComplex.exactAt_of_isSupported** 是 Mathlib 中的一个引理，位于命名空间 `Homologic
alComplex`。
形式化陈述：exactAt_of_isSupported [K.IsSupported e] (i' : ι') (hi' : forall i, e.f i 
!= i') : K.ExactAt i'
参数：i' : ι'；hi' : forall i, e.f i != i'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.IsSupported.exactAt`：∀ {ι : Type u_1} {ι' : Type u_2}
 {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   {inst : CategoryTh
eory.Category.{v_1, u_3} C} …
-/
lemma exactAt_of_isSupported [K.IsSupported e] (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    K.ExactAt i' :=
  IsSupported.exactAt i' hi'

include e' in
variable {K L} in
/-
**HomologicalComplex.isSupported_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：isSupported_of_iso [K.IsSupported e] : L.IsSupported e where exactAt i' hi
'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.ExactAt.of_iso`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   
{ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.exactAt_of_isSupported`：exactAt_of_isSupported [K.IsS
upported e] (i' : ι') (hi' : forall i, e.f i != i') : K.ExactAt i'
-/
lemma isSupported_of_iso [K.IsSupported e] : L.IsSupported e where
  exactAt i' hi' :=
    (K.exactAt_of_isSupported e i' hi').of_iso e'

variable {K L} in
/-
**HomologicalComplex.isSupported_iff_of_quasiIso** 是 Mathlib 中的一个引理，位于命名空间 `Homo
logicalComplex`。
形式化陈述：isSupported_iff_of_quasiIso [forall i, K.HasHomology i] [forall i, L.HasHo
mology i] [QuasiIso φ] : K.IsSupported e ↔ L.IsSupported e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `exactAt_iff_of_quasiIsoAt`：exactAt_iff_of_quasiIsoAt (f : K ⟶ L) (i : ι)
 [K.HasHomology i] [L.HasHomology i] [QuasiIsoAt f i] : K.ExactAt i ↔ L.ExactAt 
i
· 使用定理 `QuasiIso.quasiIsoAt`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isSupported_iff_of_quasiIso [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    [QuasiIso φ] :
    K.IsSupported e ↔ L.IsSupported e := by
  simp [isSupported_iff, exactAt_iff_of_quasiIsoAt φ]
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [K.IsStrictlySupported e] : K.IsSupported e where
  exactAt i' hi' := by
    rw [exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ (K.isZero_X_of_isStrictlySupported e i' hi')

@[simp]
/-
**HomologicalComplex.isSupported_op_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：isSupported_op_iff : K.op.IsSupported e.op ↔ K.IsSupported e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.ExactAt.unop`：∀ {ι : Type u_1} {V : Type u_2} [inst :
 CategoryTheory.Category.{v_1, u_2} V] {c : ComplexShape ι}   [inst_1 : Category
Theory.Limits.HasZero…
· 使用引理 `HomologicalComplex.exactAt_of_isSupported`：exactAt_of_isSupported [K.IsS
upported e] (i' : ι') (hi' : forall i, e.f i != i') : K.ExactAt i'
· 使用定理 `HomologicalComplex.ExactAt.op`：∀ {ι : Type u_1} {V : Type u_2} [inst : C
ategoryTheory.Category.{v_1, u_2} V] {c : ComplexShape ι}   [inst_1 : CategoryTh
eory.Limits.HasZero…
-/
lemma isSupported_op_iff :
    K.op.IsSupported e.op ↔ K.IsSupported e :=
  ⟨fun _ ↦ ⟨fun i' hi' ↦ (K.op.exactAt_of_isSupported e.op i' hi').unop⟩,
    fun _ ↦ ⟨fun i' hi' ↦ (K.exactAt_of_isSupported e i' hi').op⟩⟩

/-- If `K : HomologicalComplex C c'`, then `K.IsStrictlySupportedOutside e` holds for
an embedding `e : c.Embedding c'` of complex shapes if `K.X (e.f i)` is zero for all `i`. -/
/-
**HomologicalComplex.IsStrictlySupportedOutside** 是 Mathlib 中的一个归纳类型，位于命名空间 `Hom
ologicalComplex`。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {c : ComplexShape ι} →       {c' 
: ComplexShape ι'} →         {C : Type u_3} →           [inst : CategoryTheory.C
ategory.{v_1, u_3} C] →             [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C] → HomologicalComplex C c' → c.Embedding c' → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `K : HomologicalComplex C c'`, then `K.IsStrictlySupportedOutside e` holds fo
r
an embedding `e : c.Embedding c'` of complex shapes if `K.X (e.f i)` is zero for
 all `i`.
-/
structure IsStrictlySupportedOutside : Prop where
  isZero (i : ι) : IsZero (K.X (e.f i))

@[simp]
/-
**HomologicalComplex.isStrictlySupportedOutside_op_iff** 是 Mathlib 中的一个引理，位于命名空间
 `HomologicalComplex`。
形式化陈述：isStrictlySupportedOutside_op_iff : K.op.IsStrictlySupportedOutside e.op ↔
 K.IsStrictlySupportedOutside e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.unop`：unop {X : Cᵒᵖ} (h : IsZero X) : IsZer
o (Opposite.unop X)
· 使用定理 `HomologicalComplex.IsStrictlySupportedOutside.isZero`：∀ {ι : Type u_1} {
ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [ins
t : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `CategoryTheory.Limits.IsZero.op`：op (h : IsZero X) : IsZero (Opposite.op
 X)
-/
lemma isStrictlySupportedOutside_op_iff :
    K.op.IsStrictlySupportedOutside e.op ↔ K.IsStrictlySupportedOutside e :=
  ⟨fun h ↦ ⟨fun i ↦ (h.isZero i).unop⟩, fun h ↦ ⟨fun i ↦ (h.isZero i).op⟩⟩

/-- If `K : HomologicalComplex C c'`, then `K.IsSupportedOutside e` holds for
an embedding `e : c.Embedding c'` of complex shapes if `K` is exact at `e.f i` for all `i`. -/
/-
**HomologicalComplex.IsSupportedOutside** 是 Mathlib 中的一个归纳类型，位于命名空间 `Homological
Complex`。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {c : ComplexShape ι} →       {c' 
: ComplexShape ι'} →         {C : Type u_3} →           [inst : CategoryTheory.C
ategory.{v_1, u_3} C] →             [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C] → HomologicalComplex C c' → c.Embedding c' → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `K : HomologicalComplex C c'`, then `K.IsSupportedOutside e` holds for
an embedding `e : c.Embedding c'` of complex shapes if `K` is exact at `e.f i` f
or all `i`.
-/
structure IsSupportedOutside : Prop where
  exactAt (i : ι) : K.ExactAt (e.f i)

@[simp]
/-
**HomologicalComplex.isSupportedOutside_op_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homolo
gicalComplex`。
形式化陈述：isSupportedOutside_op_iff : K.op.IsSupportedOutside e.op ↔ K.IsSupportedOu
tside e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.ExactAt.unop`：∀ {ι : Type u_1} {V : Type u_2} [inst :
 CategoryTheory.Category.{v_1, u_2} V] {c : ComplexShape ι}   [inst_1 : Category
Theory.Limits.HasZero…
· 使用定理 `HomologicalComplex.IsSupportedOutside.exactAt`：∀ {ι : Type u_1} {ι' : Ty
pe u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : Cat
egoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `HomologicalComplex.ExactAt.op`：∀ {ι : Type u_1} {V : Type u_2} [inst : C
ategoryTheory.Category.{v_1, u_2} V] {c : ComplexShape ι}   [inst_1 : CategoryTh
eory.Limits.HasZero…
-/
lemma isSupportedOutside_op_iff :
    K.op.IsSupportedOutside e.op ↔ K.IsSupportedOutside e :=
  ⟨fun h ↦ ⟨fun i ↦ (h.exactAt i).unop⟩, fun h ↦ ⟨fun i ↦ (h.exactAt i).op⟩⟩

variable {K e} in
/-
**HomologicalComplex.IsStrictlySupportedOutside.isSupportedOutside** 是 Mathlib 中
的一个定理，位于命名空间 `HomologicalComplex.IsStrictlySupportedOutside`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {C : Type u_3}   [inst : CategoryTheory.Category.{v_1, u_3} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {K : HomologicalComplex C c'} {e : c.Emb
edding c'}, K.IsStrictlySupportedOutside e → K.IsSupportedOutside e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_isZero_X₂`：exact_of_isZero_X₂ (h : 
IsZero S.X₂) : S.Exact
· 使用定理 `HomologicalComplex.IsStrictlySupportedOutside.isZero`：∀ {ι : Type u_1} {
ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [ins
t : CategoryTheory.Category.{v_1, u_3} C] …
-/
lemma IsStrictlySupportedOutside.isSupportedOutside (h : K.IsStrictlySupportedOutside e) :
    K.IsSupportedOutside e where
  exactAt i := ShortComplex.exact_of_isZero_X₂ _ (h.isZero i)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] : (0 : HomologicalComplex C c').IsStrictlySupported e where
  isZero i _ := (eval _ _ i).map_isZero (Limits.isZero_zero _)
/-
**HomologicalComplex.isZero_iff_isStrictlySupported_and_isStrictlySupportedOutsi
de** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside : IsZero K ↔
 K.IsStrictlySupported e ∧ K.IsStrictlySupportedOutside e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.map_isZero`：map_isZero (F : C ⥤ D) [PreservesZero
Morphisms F] {X : C} (hX : IsZero X) : IsZero (F.obj X)
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `HomologicalComplex.IsStrictlySupportedOutside.isZero`：∀ {ι : Type u_1} {
ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [ins
t : CategoryTheory.Category.{v_1, u_3} C] …
· 使用引理 `HomologicalComplex.isZero_X_of_isStrictlySupported`：isZero_X_of_isStrict
lySupported [K.IsStrictlySupported e] (i' : ι') (hi' : forall i, e.f i != i') : 
IsZero (K.X i')
-/
lemma isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside :
    IsZero K ↔ K.IsStrictlySupported e ∧ K.IsStrictlySupportedOutside e := by
  constructor
  · intro hK
    constructor
    all_goals
      constructor
      intros
      exact (eval _ _ _).map_isZero hK
  · rintro ⟨h₁, h₂⟩
    rw [IsZero.iff_id_eq_zero]
    ext n
    apply IsZero.eq_of_src
    by_cases hn : ∃ i, e.f i = n
    · obtain ⟨i, rfl⟩ := hn
      exact h₂.isZero i
    · exact K.isZero_X_of_isStrictlySupported e _ (by simpa using hn)

end

section

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (K : HomologicalComplex C c') (F : C ⥤ D) [F.PreservesZeroMorphisms] (e : c.Embedding c')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.map_isStrictlySupported** 是 Mathlib 中的一个实例，位于命名空间 `Homologi
calComplex`。
形式化陈述：map_isStrictlySupported [K.IsStrictlySupported e] : ((F.mapHomologicalComp
lex c').obj K).IsStrictlySupported e where isZero i' hi'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用引理 `HomologicalComplex.isZero_X_of_isStrictlySupported`：isZero_X_of_isStrict
lySupported [K.IsStrictlySupported e] (i' : ι') (hi' : forall i, e.f i != i') : 
IsZero (K.X i')
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
-/
instance map_isStrictlySupported [K.IsStrictlySupported e] :
    ((F.mapHomologicalComplex c').obj K).IsStrictlySupported e where
  isZero i' hi' := by
    rw [IsZero.iff_id_eq_zero]
    dsimp
    rw [← F.map_id, (K.isZero_X_of_isStrictlySupported e i' hi').eq_of_src (𝟙 _) 0, F.map_zero]
/-
**HomologicalComplex.isStrictlySupported_mapHomologicalComplex_obj_iff** 是 Mathl
ib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：isStrictlySupported_mapHomologicalComplex_obj_iff [F.Faithful] : ((F.mapHo
mologicalComplex c').obj K).IsStrictlySupported e ↔ K.IsStrictlySupported e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用引理 `HomologicalComplex.isZero_X_of_isStrictlySupported`：isZero_X_of_isStrict
lySupported [K.IsStrictlySupported e] (i' : ι') (hi' : forall i, e.f i != i') : 
IsZero (K.X i')
-/
lemma isStrictlySupported_mapHomologicalComplex_obj_iff [F.Faithful] :
    ((F.mapHomologicalComplex c').obj K).IsStrictlySupported e ↔ K.IsStrictlySupported e := by
  refine ⟨fun _ ↦ ⟨fun i' hi' ↦ ?_⟩, fun _ ↦ inferInstance⟩
  rw [IsZero.iff_id_eq_zero]
  exact F.map_injective ((isZero_X_of_isStrictlySupported
    ((F.mapHomologicalComplex c').obj K) e i' hi').eq_of_src _ _)

end

end HomologicalComplex

