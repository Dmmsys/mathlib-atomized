/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ExactSequence

/-!
# Exact sequences with four terms

The main definition in this file is `ComposableArrows.Exact.cokerIsoKer`:
given an exact sequence `S` (involving at least four objects),
this is the isomorphism from the cokernel of `S.map' k (k + 1)`
to the kernel of `S.map' (k + 2) (k + 3)`. This is intended
to be used for exact sequences in abelian categories, but the
construction works for preadditive balanced categories.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ComposableArrows

section HasZeroMorphisms

namespace IsComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C] {n : ℕ} {S : ComposableArrows C (n + 3)}
  (hS : S.IsComplex) (k : ℕ)

section

set_option backward.isDefEq.respectTransparency false in
/-- If `S` is a complex, this is the morphism from a cokernel of `S.map' k (k + 1)`
to a kernel of `S.map' (k + 2) (k + 3)`. -/
/-
**CategoryTheory.ComposableArrows.IsComplex.cokerToKer'** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.ComposableArrows.IsComplex`。
形式化陈述：cokerToKer' (hk : k <= n) (cc : CokernelCofork (S.map' k (k + 1))) (kf : K
ernelFork (S.map' (k + 2) (k + 3))) (hcc : IsColimit cc) (hkf : IsLimit kf) : cc
.pt ⟶ kf.pt
参数：hk : k <= n；cc : CokernelCofork (S.map' k (k + 1))；kf : KernelFork (S.map' (k
 + 2) (k + 3))；hcc : IsColimit cc；hkf : IsLimit kf。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is a complex, this is the morphism from a cokernel of `S.map' k (k + 1)`
to a kernel of `S.map' (k + 2) (k + 3)`.
-/
def cokerToKer' (hk : k ≤ n) (cc : CokernelCofork (S.map' k (k + 1)))
    (kf : KernelFork (S.map' (k + 2) (k + 3))) (hcc : IsColimit cc) (hkf : IsLimit kf) :
    cc.pt ⟶ kf.pt :=
  IsColimit.desc hcc (CokernelCofork.ofπ _
    (show S.map' k (k + 1) ≫ IsLimit.lift hkf (KernelFork.ofι _ (hS.zero (k + 1))) = _ from
      Fork.IsLimit.hom_ext hkf (by simpa using hS.zero k)))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ComposableArrows.IsComplex.cokerToKer'_fac** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.ComposableArrows.IsComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{u_2, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {n : ℕ} {S : CategoryTheory.Composabl
eArrows C (n + 3)} (hS : S.IsComplex) (k : ℕ) (hk : k ≤ n)   (cc : CategoryTheor
y.Limits.CokernelCofork (S.map' k (k + 1) ⋯ ⋯))   (kf : CategoryTheory.Limits.Ke
rnelFork (S.map' (k + 2) (k + 3) ⋯ ⋯)) (hcc : CategoryTheory.Limits.IsColimit cc
)   (hkf : CategoryTheory.Limits.IsLimit kf),   CategoryTheory.CategoryStruct.co
mp (CategoryTheory.Limits.Cofork.π cc)       (CategoryTheory.CategoryStruct.comp
 (hS.cokerToKer' k hk cc kf hcc hkf) (CategoryTheory.Limits.Fork.ι kf)) =     S.
map' (k + 1) (k + 2) ⋯ ⋯
参数：n + 3；hS : S.IsComplex；k : ℕ；hk : k ≤ n；cc : CategoryTheory.Limits.CokernelCo
fork (S.map' k (k + 1) ⋯ ⋯)；kf : CategoryTheory.Limits.KernelFork (S.map' (k + 2
) (k + 3) ⋯ ⋯)；hcc : CategoryTheory.Limits.IsColimit cc；hkf : CategoryTheory.Lim
its.IsLimit kf；CategoryTheory.Limits.Cofork.π cc；CategoryTheory.CategoryStruct.c
omp (hS.cokerToKer' k hk cc kf hcc hkf) (CategoryTheory.Limits.Fork.ι kf)；k + 1；
k + 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.π_desc_assoc`：∀ {C : Type u} {X Y
 : C} [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   {s t : CategoryT
heory.Limits.Cofork f g} (hs : CategoryTh…
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.lift_ι`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s t : CategoryTheory.Limits
.Fork f g}   (hs : CategoryTheo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cokerToKer'_fac (hk : k ≤ n) (cc : CokernelCofork (S.map' k (k + 1)))
    (kf : KernelFork (S.map' (k + 2) (k + 3))) (hcc : IsColimit cc) (hkf : IsLimit kf) :
    cc.π ≫ hS.cokerToKer' k hk cc kf hcc hkf ≫ kf.ι =
      S.map' (k + 1) (k + 2) := by
  simp [cokerToKer']

end

section

/-- If `S` is a complex, this is the morphism from the cokernel of `S.map' k (k + 1)`
to the kernel of `S.map' (k + 2) (k + 3)`. -/
/-
**CategoryTheory.ComposableArrows.IsComplex.cokerToKer** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ComposableArrows.IsComplex`。
形式化陈述：cokerToKer (hk : k <= n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is a complex, this is the morphism from the cokernel of `S.map' k (k + 1)
`
to the kernel of `S.map' (k + 2) (k + 3)`.
-/
noncomputable def cokerToKer (hk : k ≤ n := by lia)
    [HasCokernel (S.map' k (k + 1))] [HasKernel (S.map' (k + 2) (k + 3))] :
    cokernel (S.map' k (k + 1)) ⟶ kernel (S.map' (k + 2) (k + 3)) :=
  hS.cokerToKer' k hk (CokernelCofork.ofπ _ (cokernel.condition _))
    (KernelFork.ofι _ (kernel.condition _)) (cokernelIsCokernel _) (kernelIsKernel _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ComposableArrows.IsComplex.cokerToKer_fac** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ComposableArrows.IsComplex`。
形式化陈述：cokerToKer_fac (hk : k <= n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ComposableArrows.IsComplex.cokerToKer'_fac`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{u_2, u_1} C] [inst_1 : CategoryTheory.Limit
s.HasZeroMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma cokerToKer_fac (hk : k ≤ n := by lia)
    [HasCokernel (S.map' k (k + 1))] [HasKernel (S.map' (k + 2) (k + 3))] :
    cokernel.π _ ≫ hS.cokerToKer k hk ≫ kernel.ι _ = S.map' (k + 1) (k + 2) :=
  hS.cokerToKer'_fac k hk _ _ (cokernelIsCokernel _) (kernelIsKernel _)

end

section

/-- If `S` is a complex, this is the morphism from the opcycles of `S` in
degree `k + 1` to the cycles of `S` in degree `k + 2`. -/
/-
**CategoryTheory.ComposableArrows.IsComplex.opcyclesToCycles** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.ComposableArrows.IsComplex`。
形式化陈述：opcyclesToCycles (hk : k <= n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is a complex, this is the morphism from the opcycles of `S` in
degree `k + 1` to the cycles of `S` in degree `k + 2`.
-/
noncomputable def opcyclesToCycles (hk : k ≤ n := by lia)
    [(S.sc hS k).HasRightHomology] [(S.sc hS (k + 1)).HasLeftHomology] :
    (S.sc hS k _).opcycles ⟶ (S.sc hS (k + 1) _).cycles :=
  hS.cokerToKer' k hk _ _ (S.sc hS k _).opcyclesIsCokernel
    (S.sc hS (k + 1) _).cyclesIsKernel

@[reassoc (attr := simp)]
/-
**CategoryTheory.ComposableArrows.IsComplex.opcyclesToCycles_fac** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ComposableArrows.IsComplex`。
形式化陈述：opcyclesToCycles_fac (hk : k <= n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ComposableArrows.IsComplex.cokerToKer'_fac`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{u_2, u_1} C] [inst_1 : CategoryTheory.Limit
s.HasZeroMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用引理 `CategoryTheory.ShortComplex.f_pOpcycles`：f_pOpcycles : S.f ≫ S.pOpcycles
 = 0
· 使用引理 `CategoryTheory.ShortComplex.iCycles_g`：iCycles_g : S.iCycles ≫ S.g = 0
-/
lemma opcyclesToCycles_fac (hk : k ≤ n := by lia)
    [(S.sc hS k).HasRightHomology] [(S.sc hS (k + 1)).HasLeftHomology] :
    (S.sc hS k _).pOpcycles ≫ hS.opcyclesToCycles k ≫ (S.sc hS (k + 1) _).iCycles =
      S.map' (k + 1) (k + 2) :=
  hS.cokerToKer'_fac k hk _ _ (S.sc hS k _).opcyclesIsCokernel
    (S.sc hS (k + 1) _).cyclesIsKernel

end

end IsComplex

end HasZeroMorphisms

section Preadditive

variable {C : Type*} [Category C] [Preadditive C] {n : ℕ} {S : ComposableArrows C (n + 3)}

namespace IsComplex

variable (hS : S.IsComplex) (k : ℕ) (hk : k ≤ n)
  (cc : CokernelCofork (S.map' k (k + 1))) (kf : KernelFork (S.map' (k + 2) (k + 3)))
  (hcc : IsColimit cc) (hkf : IsLimit kf)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ComposableArrows.IsComplex.epi_cokerToKer'** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ComposableArrows.IsComplex`。
形式化陈述：epi_cokerToKer' (hS' : (S.sc hS (k + 1)).Exact) : Epi (hS.cokerToKer' k hk
 cc kf hcc hkf)
参数：hS' : (S.sc hS (k + 1)).Exact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.hasZeroObject`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.Exact.hasHomology`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.exact_iff_epi_f'`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.P
readditive C]   {S : CategoryTheory.ShortComplex C}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instMonoI`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_i`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.Exact.leftHomologyDataOfIsLimitKernelFork_i`
：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Catego
ryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ComposableArrows.IsComplex.cokerToKer'_fac`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{u_2, u_1} C] [inst_1 : CategoryTheory.Limit
s.HasZeroMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
-/
lemma epi_cokerToKer' (hS' : (S.sc hS (k + 1)).Exact) :
    Epi (hS.cokerToKer' k hk cc kf hcc hkf) := by
  have := hS'.hasZeroObject
  have := hS'.hasHomology
  let h := hS'.leftHomologyDataOfIsLimitKernelFork kf hkf
  have := h.exact_iff_epi_f'.1 hS'
  have fac : cc.π ≫ hS.cokerToKer' k hk cc kf hcc hkf = h.f' := by
    rw [← cancel_mono h.i, h.f'_i, ShortComplex.Exact.leftHomologyDataOfIsLimitKernelFork_i,
      assoc, IsComplex.cokerToKer'_fac]
  exact epi_of_epi_fac fac

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ComposableArrows.IsComplex.mono_cokerToKer'** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ComposableArrows.IsComplex`。
形式化陈述：mono_cokerToKer' (hS' : (S.sc hS k).Exact) : Mono (hS.cokerToKer' k hk cc 
kf hcc hkf)
参数：hS' : (S.sc hS k).Exact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.hasZeroObject`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.Exact.hasHomology`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.exact_iff_mono_g'`：∀ {C : 
Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory
.Preadditive C]   {S : CategoryTheory.ShortComplex C}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.instEpiP`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.p_g'`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.Exact.rightHomologyDataOfIsColimitCokernelCo
fork_p`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 :
 CategoryTheory.Preadditive C]   {S : CategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.ComposableArrows.IsComplex.cokerToKer'_fac`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{u_2, u_1} C] [inst_1 : CategoryTheory.Limit
s.HasZeroMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
-/
lemma mono_cokerToKer' (hS' : (S.sc hS k).Exact) :
    Mono (hS.cokerToKer' k hk cc kf hcc hkf) := by
  have := hS'.hasZeroObject
  have := hS'.hasHomology
  let h := hS'.rightHomologyDataOfIsColimitCokernelCofork cc hcc
  have := h.exact_iff_mono_g'.1 hS'
  have fac : hS.cokerToKer' k hk cc kf hcc hkf ≫ kf.ι = h.g' := by
    rw [← cancel_epi h.p, h.p_g', ShortComplex.Exact.rightHomologyDataOfIsColimitCokernelCofork_p,
      cokerToKer'_fac]
  exact mono_of_mono_fac fac

end IsComplex

end Preadditive

section Balanced

variable {C : Type*} [Category C] [Preadditive C] [Balanced C] {n : ℕ}
  {S : ComposableArrows C (n + 3)} (hS : S.Exact)

namespace Exact

section

variable (k : ℕ) (hk : k ≤ n)
  (cc : CokernelCofork (S.map' k (k + 1))) (kf : KernelFork (S.map' (k + 2) (k + 3)))
  (hcc : IsColimit cc) (hkf : IsLimit kf)

/-- If `S` is an exact sequence, this is the morphism from a cokernel
of `S.map' k (k + 1)` to a kernel of `S.map' (k + 2) (k + 3)`. -/
/-
**CategoryTheory.ComposableArrows.Exact.cokerToKer'** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.ComposableArrows.Exact`。
形式化陈述：cokerToKer' : cc.pt ⟶ kf.pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is an exact sequence, this is the morphism from a cokernel
of `S.map' k (k + 1)` to a kernel of `S.map' (k + 2) (k + 3)`.
-/
abbrev cokerToKer' : cc.pt ⟶ kf.pt :=
  hS.toIsComplex.cokerToKer' k hk cc kf hcc hkf
/-
**CategoryTheory.ComposableArrows.Exact.isIso_cokerToKer'** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory.ComposableArrows.Exact`。
形式化陈述：isIso_cokerToKer' : IsIso (hS.cokerToKer' k hk cc kf hcc hkf)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.IsComplex.mono_cokerToKer'`：mono_cokerTo
Ker' (hS' : (S.sc hS k).Exact) : Mono (hS.cokerToKer' k hk cc kf hcc hkf)
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `CategoryTheory.ComposableArrows.IsComplex.epi_cokerToKer'`：epi_cokerToKe
r' (hS' : (S.sc hS (k + 1)).Exact) : Epi (hS.cokerToKer' k hk cc kf hcc hkf)
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
-/
instance isIso_cokerToKer' : IsIso (hS.cokerToKer' k hk cc kf hcc hkf) := by
  have : Mono (hS.cokerToKer' k hk cc kf hcc hkf) :=
      hS.toIsComplex.mono_cokerToKer' k hk cc kf hcc hkf
    (hS.exact k)
  have : Epi (hS.cokerToKer' k hk cc kf hcc hkf) :=
    hS.epi_cokerToKer' k hk cc kf hcc hkf (hS.exact (k + 1))
  apply isIso_of_mono_of_epi

/-- If `S` is an exact sequence, this is the isomorphism from a cokernel
of `S.map' k (k + 1)` to a kernel of `S.map' (k + 2) (k + 3)`. -/
@[simps! hom]
/-
**CategoryTheory.ComposableArrows.Exact.cokerIsoKer'** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ComposableArrows.Exact`。
形式化陈述：cokerIsoKer' : cc.pt ≅ kf.pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is an exact sequence, this is the isomorphism from a cokernel
of `S.map' k (k + 1)` to a kernel of `S.map' (k + 2) (k + 3)`.
-/
noncomputable def cokerIsoKer' : cc.pt ≅ kf.pt :=
  asIso (hS.cokerToKer' k hk cc kf hcc hkf)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ComposableArrows.Exact.cokerIsoKer'_hom_inv_id** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.ComposableArrows.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{u_2, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.Balanced C] {n : ℕ} {S :
 CategoryTheory.ComposableArrows C (n + 3)} (hS : S.Exact) (k : ℕ)   (hk : k ≤ n
) (cc : CategoryTheory.Limits.CokernelCofork (S.map' k (k + 1) ⋯ ⋯))   (kf : Cat
egoryTheory.Limits.KernelFork (S.map' (k + 2) (k + 3) ⋯ ⋯)) (hcc : CategoryTheor
y.Limits.IsColimit cc)   (hkf : CategoryTheory.Limits.IsLimit kf),   CategoryThe
ory.CategoryStruct.comp (hS.cokerToKer' k hk cc kf hcc hkf) (hS.cokerIsoKer' k h
k cc kf hcc hkf).inv =     CategoryTheory.CategoryStruct.id cc.pt
参数：n + 3；hS : S.Exact；k : ℕ；hk : k ≤ n；cc : CategoryTheory.Limits.CokernelCofork
 (S.map' k (k + 1) ⋯ ⋯)；kf : CategoryTheory.Limits.KernelFork (S.map' (k + 2) (k
 + 3) ⋯ ⋯)；hcc : CategoryTheory.Limits.IsColimit cc；hkf : CategoryTheory.Limits.
IsLimit kf；hS.cokerToKer' k hk cc kf hcc hkf；hS.cokerIsoKer' k hk cc kf hcc hkf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
lemma cokerIsoKer'_hom_inv_id :
    hS.cokerToKer' k hk cc kf hcc hkf ≫ (hS.cokerIsoKer' k hk cc kf hcc hkf).inv = 𝟙 _ :=
  (hS.cokerIsoKer' k hk cc kf hcc hkf).hom_inv_id

@[reassoc (attr := simp)]
/-
**CategoryTheory.ComposableArrows.Exact.cokerIsoKer'_inv_hom_id** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.ComposableArrows.Exact`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{u_2, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.Balanced C] {n : ℕ} {S :
 CategoryTheory.ComposableArrows C (n + 3)} (hS : S.Exact) (k : ℕ)   (hk : k ≤ n
) (cc : CategoryTheory.Limits.CokernelCofork (S.map' k (k + 1) ⋯ ⋯))   (kf : Cat
egoryTheory.Limits.KernelFork (S.map' (k + 2) (k + 3) ⋯ ⋯)) (hcc : CategoryTheor
y.Limits.IsColimit cc)   (hkf : CategoryTheory.Limits.IsLimit kf),   CategoryThe
ory.CategoryStruct.comp (hS.cokerIsoKer' k hk cc kf hcc hkf).inv (hS.cokerToKer'
 k hk cc kf hcc hkf) =     CategoryTheory.CategoryStruct.id kf.pt
参数：n + 3；hS : S.Exact；k : ℕ；hk : k ≤ n；cc : CategoryTheory.Limits.CokernelCofork
 (S.map' k (k + 1) ⋯ ⋯)；kf : CategoryTheory.Limits.KernelFork (S.map' (k + 2) (k
 + 3) ⋯ ⋯)；hcc : CategoryTheory.Limits.IsColimit cc；hkf : CategoryTheory.Limits.
IsLimit kf；hS.cokerIsoKer' k hk cc kf hcc hkf；hS.cokerToKer' k hk cc kf hcc hkf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma cokerIsoKer'_inv_hom_id :
    (hS.cokerIsoKer' k hk cc kf hcc hkf).inv ≫ hS.cokerToKer' k hk cc kf hcc hkf = 𝟙 _ :=
  (hS.cokerIsoKer' k hk cc kf hcc hkf).inv_hom_id

end

section

/-- If `S` is an exact sequence, this is the isomorphism from the cokernel
of `S.map' k (k + 1)` to the kernel of `S.map' (k + 2) (k + 3)`. -/
/-
**CategoryTheory.ComposableArrows.Exact.cokerIsoKer** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.ComposableArrows.Exact`。
形式化陈述：cokerIsoKer (k : Nat) (hk : k <= n
参数：k : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is an exact sequence, this is the isomorphism from the cokernel
of `S.map' k (k + 1)` to the kernel of `S.map' (k + 2) (k + 3)`.
-/
noncomputable def cokerIsoKer (k : ℕ) (hk : k ≤ n := by lia)
  [HasCokernel (S.map' k (k + 1))] [HasKernel (S.map' (k + 2) (k + 3))] :
    cokernel (S.map' k (k + 1) _ _) ≅ kernel (S.map' (k + 2) (k + 3) _ _) :=
  hS.cokerIsoKer' k hk (CokernelCofork.ofπ _ (cokernel.condition _))
    (KernelFork.ofι _ (kernel.condition _)) (cokernelIsCokernel _) (kernelIsKernel _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ComposableArrows.Exact.cokerIsoKer_hom_fac** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ComposableArrows.Exact`。
形式化陈述：cokerIsoKer_hom_fac (k : Nat) (hk : k <= n
参数：k : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.IsComplex.cokerToKer_fac`：cokerToKer_fac
 (hk : k <= n
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
-/
lemma cokerIsoKer_hom_fac (k : ℕ) (hk : k ≤ n := by lia)
    [HasCokernel (S.map' k (k + 1))] [HasKernel (S.map' (k + 2) (k + 3))] :
    cokernel.π _ ≫ (hS.cokerIsoKer k).hom ≫ kernel.ι _ = S.map' (k + 1) (k + 2) :=
  hS.toIsComplex.cokerToKer_fac k

end

section

/-- If `S` is an exact sequence, this is the isomorphism from the opcycles of `S` in
degree `k + 1` to the cycles of `S` in degree `k + 2`. -/
/-
**CategoryTheory.ComposableArrows.Exact.opcyclesIsoCycles** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.ComposableArrows.Exact`。
形式化陈述：opcyclesIsoCycles (k : Nat) (hk : k <= n
参数：k : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is an exact sequence, this is the isomorphism from the opcycles of `S` in
degree `k + 1` to the cycles of `S` in degree `k + 2`.
-/
noncomputable def opcyclesIsoCycles (k : ℕ) (hk : k ≤ n := by lia)
    [h₁ : (hS.sc k).HasRightHomology] [h₂ : (hS.sc (k + 1)).HasLeftHomology] :
    (hS.sc k _).opcycles ≅ (hS.sc (k + 1) _).cycles :=
  hS.cokerIsoKer' k hk _ _ (hS.sc k _).opcyclesIsCokernel (hS.sc (k + 1) _).cyclesIsKernel

@[reassoc (attr := simp)]
/-
**CategoryTheory.ComposableArrows.Exact.opcyclesIsoCycles_hom_fac** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.ComposableArrows.Exact`。
形式化陈述：opcyclesIsoCycles_hom_fac (k : Nat) (hk : k <= n
参数：k : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.IsComplex.opcyclesToCycles_fac`：opcycles
ToCycles_fac (hk : k <= n
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
-/
lemma opcyclesIsoCycles_hom_fac (k : ℕ) (hk : k ≤ n := by lia)
    [h₁ : (hS.sc k).HasRightHomology] [h₂ : (hS.sc (k + 1)).HasLeftHomology] :
    (hS.sc k _).pOpcycles ≫ (hS.opcyclesIsoCycles k).hom ≫ (hS.sc (k + 1) _).iCycles =
      S.map' (k + 1) (k + 2) :=
  hS.toIsComplex.opcyclesToCycles_fac k hk

end

end Exact

end Balanced

end ComposableArrows

end CategoryTheory

