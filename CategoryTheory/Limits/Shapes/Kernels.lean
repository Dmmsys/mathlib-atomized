/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Kernels and cokernels

In a category with zero morphisms, the kernel of a morphism `f : X ⟶ Y` is
the equalizer of `f` and `0 : X ⟶ Y`. (Similarly the cokernel is the coequalizer.)

The basic definitions are
* `kernel : (X ⟶ Y) → C`

* `kernel.ι : kernel f ⟶ X`
* `kernel.condition : kernel.ι f ≫ f = 0` and
* `kernel.lift (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f` (as well as the dual versions)

## Main statements

Besides the definition and lifts, we prove
* `kernel.ιZeroIsIso`: a kernel map of a zero morphism is an isomorphism
* `kernel.eq_zero_of_epi_kernel`: if `kernel.ι f` is an epimorphism, then `f = 0`
* `kernel.ofMono`: the kernel of a monomorphism is the zero object
* `kernel.liftMono`: the lift of a monomorphism `k : W ⟶ X` such that `k ≫ f = 0`
  is still a monomorphism
* `kernel.isLimitConeZeroCone`: if our category has a zero object, then the map from the zero
  object is a kernel map of any monomorphism
* `kernel.ιOfZero`: `kernel.ι (0 : X ⟶ Y)` is an isomorphism

and the corresponding dual statements.

## Future work
* TODO: connect this with existing work in the group theory and ring theory libraries.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbrev`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

@[expose] public section


noncomputable section

universe v v₂ u u' u₂

open CategoryTheory

open CategoryTheory.Limits.WalkingParallelPair

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable [HasZeroMorphisms C]

/-- A morphism `f` has a kernel if the functor `ParallelPair f 0` has a limit. -/
/-
**CategoryTheory.Limits.HasKernel** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：HasKernel {X Y : C} (f : X ⟶ Y) : Prop
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `f` has a kernel if the functor `ParallelPair f 0` has a limit.
-/
abbrev HasKernel {X Y : C} (f : X ⟶ Y) : Prop :=
  HasLimit (parallelPair f 0)

/-- A morphism `f` has a cokernel if the functor `ParallelPair f 0` has a colimit. -/
/-
**CategoryTheory.Limits.HasCokernel** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：HasCokernel {X Y : C} (f : X ⟶ Y) : Prop
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `f` has a cokernel if the functor `ParallelPair f 0` has a colimit.
-/
abbrev HasCokernel {X Y : C} (f : X ⟶ Y) : Prop :=
  HasColimit (parallelPair f 0)

variable {X Y : C} (f : X ⟶ Y)

section

/-- A kernel fork is just a fork where the second morphism is a zero morphism. -/
/-
**CategoryTheory.Limits.KernelFork** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：KernelFork
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A kernel fork is just a fork where the second morphism is a zero morphism.
-/
abbrev KernelFork :=
  Fork f 0

variable {f}

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.KernelFork.condition** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.KernelFork`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   {f : X ⟶ Y} (s : CategoryTheory.L
imits.KernelFork f),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits
.Fork.ι s) f = 0
参数：s : CategoryTheory.Limits.KernelFork f；CategoryTheory.Limits.Fork.ι s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Fork.condition`：∀ {C : Type u} {X Y : C} [inst : C
ategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Fork f
 g),   CategoryTheory.Cate…
· 使用定理 `CategoryTheory.Limits.HasZeroMorphisms.comp_zero`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   (f : X ⟶ Y) (Z : C), …
-/
theorem KernelFork.condition (s : KernelFork f) : Fork.ι s ≫ f = 0 := by
  rw [Fork.condition, HasZeroMorphisms.comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.KernelFork.app_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.KernelFork`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   {f : X ⟶ Y} (s : CategoryTheory.L
imits.KernelFork f), s.π.app CategoryTheory.Limits.WalkingParallelPair.one = 0
参数：s : CategoryTheory.Limits.KernelFork f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Fork.app_one_eq_ι_comp_left`：∀ {C : Type u} {X Y :
 C} [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (s : CategoryTheory.
Limits.Fork f g),   s.π.app CategoryThe…
· 使用定理 `CategoryTheory.Limits.KernelFork.condition`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
 {X Y : C}   {f : X ⟶ Y} (s : Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem KernelFork.app_one (s : KernelFork f) : s.π.app one = 0 := by
  simp

/-- A morphism `ι` satisfying `ι ≫ f = 0` determines a kernel fork over `f`. -/
/-
**CategoryTheory.Limits.KernelFork.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `ι` satisfying `ι ≫ f = 0` determines a kernel fork over `f`.
-/
abbrev KernelFork.ofι {Z : C} (ι : Z ⟶ X) (w : ι ≫ f = 0) : KernelFork f :=
  Fork.ofι ι <| by rw [w, HasZeroMorphisms.comp_zero]

@[simp]
/-
**CategoryTheory.Limits.KernelFork.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem KernelFork.ι_ofι {X Y P : C} (f : X ⟶ Y) (ι : P ⟶ X) (w : ι ≫ f = 0) :
    Fork.ι (KernelFork.ofι ι w) = ι := rfl

section

attribute [local aesop safe cases] WalkingParallelPair WalkingParallelPairHom

set_option backward.defeqAttrib.useBackward true in
/-- Every kernel fork `s` is isomorphic (actually, equal) to `fork.ofι (fork.ι s) _`. -/
/-
**CategoryTheory.Limits.isoOf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every kernel fork `s` is isomorphic (actually, equal) to `fork.ofι (fork.ι s) _`
.
-/
def isoOfι (s : Fork f 0) : s ≅ Fork.ofι (Fork.ι s) (Fork.condition s) :=
  Cone.ext (Iso.refl _) <| by aesop

set_option backward.isDefEq.respectTransparency.types false in
/-- If `ι = ι'`, then `fork.ofι ι _` and `fork.ofι ι' _` are isomorphic. -/
/-
**CategoryTheory.Limits.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ι = ι'`, then `fork.ofι ι _` and `fork.ofι ι' _` are isomorphic.
-/
def ofιCongr {P : C} {ι ι' : P ⟶ X} {w : ι ≫ f = 0} (h : ι = ι') :
    KernelFork.ofι ι w ≅ KernelFork.ofι ι' (by rw [← h, w]) :=
  Cone.ext (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- If `F` is an equivalence, then applying `F` to a diagram indexing a (co)kernel of `f` yields
the diagram indexing the (co)kernel of `F.map f`. -/
/-
**CategoryTheory.Limits.compNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：compNatIso {D : Type u'} [Category.{v} D] [HasZeroMorphisms D] (F : C ⥤ D)
 [F.IsEquivalence] : parallelPair f 0 ⋙ F ≅ parallelPair (F.map f) 0
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is an equivalence, then applying `F` to a diagram indexing a (co)kernel o
f `f` yields
the diagram indexing the (co)kernel of `F.map f`.
-/
def compNatIso {D : Type u'} [Category.{v} D] [HasZeroMorphisms D] (F : C ⥤ D) [F.IsEquivalence] :
    parallelPair f 0 ⋙ F ≅ parallelPair (F.map f) 0 :=
  let app (j : WalkingParallelPair) :
      (parallelPair f 0 ⋙ F).obj j ≅ (parallelPair (F.map f) 0).obj j :=
    match j with
    | zero => Iso.refl _
    | one => Iso.refl _
  NatIso.ofComponents app <| by rintro ⟨i⟩ ⟨j⟩ <;> rintro (g | g) <;> aesop

end

/-- If `s` is a limit kernel fork and `k : W ⟶ X` satisfies `k ≫ f = 0`, then there is some
`l : W ⟶ s.X` such that `l ≫ fork.ι s = k`. -/
/-
**CategoryTheory.Limits.KernelFork.IsLimit.lift'** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.KernelFork.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         {f : X ⟶ 
Y} →           {s : CategoryTheory.Limits.KernelFork f} →             CategoryTh
eory.Limits.IsLimit s →               {W : C} →                 (k : W ⟶ X) →   
                CategoryTheory.CategoryStruct.comp k f = 0 →                    
 { l // CategoryTheory.CategoryStruct.comp l (CategoryTheory.Limits.Fork.ι s) = 
k }
参数：k : W ⟶ X；CategoryTheory.Limits.Fork.ι s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a limit kernel fork and `k : W ⟶ X` satisfies `k ≫ f = 0`, then there 
is some
`l : W ⟶ s.X` such that `l ≫ fork.ι s = k`.
-/
def KernelFork.IsLimit.lift' {s : KernelFork f} (hs : IsLimit s) {W : C} (k : W ⟶ X)
    (h : k ≫ f = 0) : { l : W ⟶ s.pt // l ≫ Fork.ι s = k } :=
  ⟨hs.lift <| KernelFork.ofι _ h, hs.fac _ _⟩

/-- This is a slightly more convenient method to verify that a kernel fork is a limit cone. It
only asks for a proof of facts that carry any mathematical content -/
/-
**CategoryTheory.Limits.isLimitAux** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：isLimitAux (t : KernelFork f) (lift : forall s : KernelFork f, s.pt ⟶ t.pt
) (fac : forall s : KernelFork f, lift s ≫ t.ι = s.ι) (uniq : forall (s : Kernel
Fork f) (m : s.pt ⟶ t.pt) (_ : m ≫ t.ι = s.ι), m = lift s) : IsLimit t
参数：t : KernelFork f；lift : forall s : KernelFork f, s.pt ⟶ t.pt；fac : forall s :
 KernelFork f, lift s ≫ t.ι = s.ι；uniq : forall (s : KernelFork f) (m : s.pt ⟶ t
.pt) (_ : m ≫ t.ι = s.ι), m = lift s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a slightly more convenient method to verify that a kernel fork is a limi
t cone. It
only asks for a proof of facts that carry any mathematical content
-/
def isLimitAux (t : KernelFork f) (lift : ∀ s : KernelFork f, s.pt ⟶ t.pt)
    (fac : ∀ s : KernelFork f, lift s ≫ t.ι = s.ι)
    (uniq : ∀ (s : KernelFork f) (m : s.pt ⟶ t.pt) (_ : m ≫ t.ι = s.ι), m = lift s) : IsLimit t :=
  { lift
    fac := fun s j => by
      cases j
      · exact fac s
      · simp
    uniq := fun s m w => uniq s m (w Limits.WalkingParallelPair.zero) }

/-- This is a more convenient formulation to show that a `KernelFork` constructed using
`KernelFork.ofι` is a limit cone.
-/
/-
**CategoryTheory.Limits.KernelFork.IsLimit.of** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a more convenient formulation to show that a `KernelFork` constructed us
ing
`KernelFork.ofι` is a limit cone.
-/
def KernelFork.IsLimit.ofι {W : C} (g : W ⟶ X) (eq : g ≫ f = 0)
    (lift : ∀ {W' : C} (g' : W' ⟶ X) (_ : g' ≫ f = 0), W' ⟶ W)
    (fac : ∀ {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0), lift g' eq' ≫ g = g')
    (uniq :
      ∀ {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0) (m : W' ⟶ W) (_ : m ≫ g = g'), m = lift g' eq') :
    IsLimit (KernelFork.ofι g eq) :=
  isLimitAux _ (fun s => lift s.ι s.condition) (fun s => fac s.ι s.condition) fun s =>
    uniq s.ι s.condition

/-- This is a more convenient formulation to show that a `KernelFork` of the form
`KernelFork.ofι i _` is a limit cone when we know that `i` is a monomorphism. -/
/-
**CategoryTheory.Limits.KernelFork.IsLimit.of** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a more convenient formulation to show that a `KernelFork` of the form
`KernelFork.ofι i _` is a limit cone when we know that `i` is a monomorphism.
-/
def KernelFork.IsLimit.ofι' {X Y K : C} {f : X ⟶ Y} (i : K ⟶ X) (w : i ≫ f = 0)
    (h : ∀ {A : C} (k : A ⟶ X) (_ : k ≫ f = 0), { l : A ⟶ K // l ≫ i = k}) [hi : Mono i] :
    IsLimit (KernelFork.ofι i w) :=
  ofι _ _ (fun {_} k hk => (h k hk).1) (fun {_} k hk => (h k hk).2) (fun {A} k hk m hm => by
    rw [← cancel_mono i, (h k hk).2, hm])

set_option backward.isDefEq.respectTransparency false in
/-- Every kernel of `f` induces a kernel of `f ≫ g` if `g` is mono. -/
/-
**CategoryTheory.Limits.isKernelCompMono** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：isKernelCompMono {c : KernelFork f} (i : IsLimit c) {Z} (g : Y ⟶ Z) [hg : 
Mono g] {h : X ⟶ Z} (hh : h = f ≫ g) : IsLimit (KernelFork.ofι c.ι (by simp [hh]
) : KernelFork h)
参数：i : IsLimit c；g : Y ⟶ Z；hh : h = f ≫ g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.KernelFork.condition`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
 {X Y : C}   {f : X ⟶ Y} (s : Ca…

--- 原说明 ---
Every kernel of `f` induces a kernel of `f ≫ g` if `g` is mono.
-/
def isKernelCompMono {c : KernelFork f} (i : IsLimit c) {Z} (g : Y ⟶ Z) [hg : Mono g] {h : X ⟶ Z}
    (hh : h = f ≫ g) : IsLimit (KernelFork.ofι c.ι (by simp [hh]) : KernelFork h) :=
  Fork.IsLimit.mk' _ fun s =>
    let s' : KernelFork f := Fork.ofι s.ι (by rw [← cancel_mono g]; simp [← hh, s.condition])
    let l := KernelFork.IsLimit.lift' i s'.ι s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Fork.IsLimit.hom_ext i; rw [Fork.ι_ofι] at hm; rw [hm]; exact l.2.symm⟩
/-
**CategoryTheory.Limits.isKernelCompMono_lift** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：isKernelCompMono_lift {c : KernelFork f} (i : IsLimit c) {Z} (g : Y ⟶ Z) [
hg : Mono g] {h : X ⟶ Z} (hh : h = f ≫ g) (s : KernelFork h) : (isKernelCompMono
 i g hh).lift s = i.lift (Fork.ofι s.ι (by rw [← cancel_mono g]; rw [Category.as
soc]; rw [← hh] simp))
参数：i : IsLimit c；g : Y ⟶ Z；hh : h = f ≫ g；s : KernelFork h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isKernelCompMono_lift {c : KernelFork f} (i : IsLimit c) {Z} (g : Y ⟶ Z) [hg : Mono g]
    {h : X ⟶ Z} (hh : h = f ≫ g) (s : KernelFork h) :
    (isKernelCompMono i g hh).lift s = i.lift (Fork.ofι s.ι (by
      rw [← cancel_mono g, Category.assoc, ← hh]
      simp)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every kernel of `f ≫ g` is also a kernel of `f`, as long as `c.ι ≫ f` vanishes. -/
/-
**CategoryTheory.Limits.isKernelOfComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：isKernelOfComp {W : C} (g : Y ⟶ W) (h : X ⟶ W) {c : KernelFork h} (i : IsL
imit c) (hf : c.ι ≫ f = 0) (hfg : f ≫ g = h) : IsLimit (KernelFork.ofι c.ι hf)
参数：g : Y ⟶ W；h : X ⟶ W；i : IsLimit c；hf : c.ι ≫ f = 0；hfg : f ≫ g = h。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every kernel of `f ≫ g` is also a kernel of `f`, as long as `c.ι ≫ f` vanishes.
-/
def isKernelOfComp {W : C} (g : Y ⟶ W) (h : X ⟶ W) {c : KernelFork h} (i : IsLimit c)
    (hf : c.ι ≫ f = 0) (hfg : f ≫ g = h) : IsLimit (KernelFork.ofι c.ι hf) :=
  Fork.IsLimit.mk _ (fun s => i.lift (KernelFork.ofι s.ι (by simp [← hfg])))
    (fun s => by simp only [KernelFork.ι_ofι, Fork.IsLimit.lift_ι]) fun s m h => by
    apply Fork.IsLimit.hom_ext i; simpa using h

/-- `X` identifies to the kernel of a zero map `X ⟶ Y`. -/
/-
**CategoryTheory.Limits.KernelFork.IsLimit.ofId** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.KernelFork.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           (hf : f = 0) →             CategoryTheory.Limits.IsLimit (Categor
yTheory.Limits.KernelFork.ofι (CategoryTheory.CategoryStruct.id X) ⋯)
参数：f : X ⟶ Y；hf : f = 0；CategoryTheory.Limits.KernelFork.ofι (CategoryTheory.Cat
egoryStruct.id X) ⋯。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…

--- 原说明 ---
`X` identifies to the kernel of a zero map `X ⟶ Y`.
-/
def KernelFork.IsLimit.ofId {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
    IsLimit (KernelFork.ofι (𝟙 X) (show 𝟙 X ≫ f = 0 by rw [hf, comp_zero])) :=
  KernelFork.IsLimit.ofι _ _ (fun x _ => x) (fun _ _ => Category.comp_id _)
    (fun _ _ _ hb => by simp only [← hb, Category.comp_id])

/-- Any zero object identifies to the kernel of a given monomorphisms. -/
/-
**CategoryTheory.Limits.KernelFork.IsLimit.ofMonoOfIsZero** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Limits.KernelFork.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         {f : X ⟶ 
Y} →           (c : CategoryTheory.Limits.KernelFork f) →             CategoryTh
eory.Mono f → CategoryTheory.Limits.IsZero c.pt → CategoryTheory.Limits.IsLimit 
c
参数：c : CategoryTheory.Limits.KernelFork f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any zero object identifies to the kernel of a given monomorphisms.
-/
def KernelFork.IsLimit.ofMonoOfIsZero {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
    (hf : Mono f) (h : IsZero c.pt) : IsLimit c :=
  isLimitAux _ (fun _ => 0) (fun s => by rw [zero_comp, ← cancel_mono f, zero_comp, s.condition])
    (fun _ _ _ => h.eq_of_tgt _ _)
/-
**CategoryTheory.Limits.KernelFork.IsLimit.isIso_** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma KernelFork.IsLimit.isIso_ι {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
    (hc : IsLimit c) (hf : f = 0) : IsIso c.ι := isIso_limit_cone_parallelPair_of_eq hf hc

set_option backward.isDefEq.respectTransparency false in
/-- If `c` is a limit kernel fork for `g : X ⟶ Y`, `e : X ≅ X'` and `g' : X' ⟶ Y` is a morphism,
then there is a limit kernel fork for `g'` with the same point as `c` if for any
morphism `φ : W ⟶ X`, there is an equivalence `φ ≫ g = 0 ↔ φ ≫ e.hom ≫ g' = 0`. -/
/-
**CategoryTheory.Limits.KernelFork.isLimitOfIsLimitOfIff** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits.KernelFork`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         {g : X ⟶ 
Y} →           {c : CategoryTheory.Limits.KernelFork g} →             CategoryTh
eory.Limits.IsLimit c →               {X' Y' : C} →                 (g' : X' ⟶ Y
') →                   (e : X ≅ X') →                     (iff :                
         ∀ ⦃W : C⦄ (φ : W ⟶ X),                           CategoryTheory.Categor
yStruct.comp φ g = 0 ↔                             CategoryTheory.CategoryStruct
.comp φ (CategoryTheory.CategoryStruct.comp e.hom g') = 0) →                    
   CategoryTheory.Limits.IsLimit                         (CategoryTheory.Limits.
KernelFork.ofι                           (CategoryTheory.CategoryStruct.comp (Ca
tegoryTheory.Limits.Fork.ι c) e.hom) ⋯)
参数：g' : X' ⟶ Y'；e : X ≅ X'；iff :                         ∀ ⦃W : C⦄ (φ : W ⟶ X), 
                          CategoryTheory.CategoryStruct.comp φ g = 0 ↔          
                   CategoryTheory.CategoryStruct.comp φ (CategoryTheory.Category
Struct.comp e.hom g') = 0；CategoryTheory.Limits.KernelFork.ofι                  
         (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Fork.ι c) e.
hom) ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a limit kernel fork for `g : X ⟶ Y`, `e : X ≅ X'` and `g' : X' ⟶ Y` is
 a morphism,
then there is a limit kernel fork for `g'` with the same point as `c` if for any
morphism `φ : W ⟶ X`, there is an equivalence `φ ≫ g = 0 ↔ φ ≫ e.hom ≫ g' = 0`.
-/
def KernelFork.isLimitOfIsLimitOfIff {X Y : C} {g : X ⟶ Y} {c : KernelFork g} (hc : IsLimit c)
    {X' Y' : C} (g' : X' ⟶ Y') (e : X ≅ X')
    (iff : ∀ ⦃W : C⦄ (φ : W ⟶ X), φ ≫ g = 0 ↔ φ ≫ e.hom ≫ g' = 0) :
    IsLimit (KernelFork.ofι (f := g') (c.ι ≫ e.hom) (by simp [← iff])) :=
  KernelFork.IsLimit.ofι _ _
    (fun s hs ↦ hc.lift (KernelFork.ofι (ι := s ≫ e.inv)
      (by rw [iff, Category.assoc, Iso.inv_hom_id_assoc, hs])))
    (fun s hs ↦ by simp)
    (fun s hs m hm ↦ Fork.IsLimit.hom_ext hc (by simpa [← cancel_mono e.hom] using hm))

set_option backward.defeqAttrib.useBackward true in
/-- If `c` is a limit kernel fork for `g : X ⟶ Y`, and `g' : X ⟶ Y'` is another morphism,
then there is a limit kernel fork for `g'` with the same point as `c` if for any
morphism `φ : W ⟶ X`, there is an equivalence `φ ≫ g = 0 ↔ φ ≫ g' = 0`. -/
/-
**CategoryTheory.Limits.KernelFork.isLimitOfIsLimitOfIff'** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Limits.KernelFork`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         {g : X ⟶ 
Y} →           {c : CategoryTheory.Limits.KernelFork g} →             CategoryTh
eory.Limits.IsLimit c →               {Y' : C} →                 (g' : X ⟶ Y') →
                   (iff :                       ∀ ⦃W : C⦄ (φ : W ⟶ X),          
               CategoryTheory.CategoryStruct.comp φ g = 0 ↔ CategoryTheory.Categ
oryStruct.comp φ g' = 0) →                     CategoryTheory.Limits.IsLimit    
                   (CategoryTheory.Limits.KernelFork.ofι (CategoryTheory.Limits.
Fork.ι c) ⋯)
参数：g' : X ⟶ Y'；iff :                       ∀ ⦃W : C⦄ (φ : W ⟶ X),               
          CategoryTheory.CategoryStruct.comp φ g = 0 ↔ CategoryTheory.CategorySt
ruct.comp φ g' = 0；CategoryTheory.Limits.KernelFork.ofι (CategoryTheory.Limits.F
ork.ι c) ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a limit kernel fork for `g : X ⟶ Y`, and `g' : X ⟶ Y'` is another morp
hism,
then there is a limit kernel fork for `g'` with the same point as `c` if for any
morphism `φ : W ⟶ X`, there is an equivalence `φ ≫ g = 0 ↔ φ ≫ g' = 0`.
-/
def KernelFork.isLimitOfIsLimitOfIff' {X Y : C} {g : X ⟶ Y} {c : KernelFork g} (hc : IsLimit c)
    {Y' : C} (g' : X ⟶ Y')
    (iff : ∀ ⦃W : C⦄ (φ : W ⟶ X), φ ≫ g = 0 ↔ φ ≫ g' = 0) :
    IsLimit (KernelFork.ofι (f := g') c.ι (by simp [← iff])) :=
  IsLimit.ofIsoLimit (isLimitOfIsLimitOfIff hc g' (Iso.refl _) (by simpa using iff))
    (Fork.ext (Iso.refl _))
/-
**CategoryTheory.Limits.KernelFork.IsLimit.isZero_of_mono** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.KernelFork.IsLimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   {f : X ⟶ Y} {c : CategoryTheory.L
imits.KernelFork f} (hc : CategoryTheory.Limits.IsLimit c) [CategoryTheory.Mono 
f],   CategoryTheory.Limits.IsZero c.pt
参数：hc : CategoryTheory.Limits.IsLimit c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.mono`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Limits.For
k f g}   (hs : CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.KernelFork.condition`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
 {X Y : C}   {f : X ⟶ Y} (s : Ca…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma KernelFork.IsLimit.isZero_of_mono {X Y : C} {f : X ⟶ Y}
    {c : KernelFork f} (hc : IsLimit c) [Mono f] : IsZero c.pt := by
  have := Fork.IsLimit.mono hc
  rw [IsZero.iff_id_eq_zero, ← cancel_mono c.ι, ← cancel_mono f, Category.assoc,
    Category.assoc, c.condition, comp_zero, zero_comp]

end

namespace KernelFork

variable {f} {X' Y' : C} {f' : X' ⟶ Y'}

set_option backward.isDefEq.respectTransparency false in
/-- The morphism between points of kernel forks induced by a morphism
in the category of arrows. -/
/-
**CategoryTheory.Limits.KernelFork.mapOfIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.KernelFork`。
形式化陈述：mapOfIsLimit (kf : KernelFork f) {kf' : KernelFork f'} (hf' : IsLimit kf')
 (φ : Arrow.mk f ⟶ Arrow.mk f') : kf.pt ⟶ kf'.pt
参数：kf : KernelFork f；hf' : IsLimit kf'；φ : Arrow.mk f ⟶ Arrow.mk f'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism between points of kernel forks induced by a morphism
in the category of arrows.
-/
def mapOfIsLimit (kf : KernelFork f) {kf' : KernelFork f'} (hf' : IsLimit kf')
    (φ : Arrow.mk f ⟶ Arrow.mk f') : kf.pt ⟶ kf'.pt :=
  hf'.lift (KernelFork.ofι (kf.ι ≫ φ.left) (by simp))

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.KernelFork.mapOfIsLimit_** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits.KernelFork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma mapOfIsLimit_ι (kf : KernelFork f) {kf' : KernelFork f'} (hf' : IsLimit kf')
    (φ : Arrow.mk f ⟶ Arrow.mk f') :
    kf.mapOfIsLimit hf' φ ≫ kf'.ι = kf.ι ≫ φ.left :=
  hf'.fac _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between points of limit kernel forks induced by an isomorphism
in the category of arrows. -/
@[simps]
/-
**CategoryTheory.Limits.KernelFork.mapIsoOfIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.KernelFork`。
形式化陈述：mapIsoOfIsLimit {kf : KernelFork f} {kf' : KernelFork f'} (hf : IsLimit kf
) (hf' : IsLimit kf') (φ : Arrow.mk f ≅ Arrow.mk f') : kf.pt ≅ kf'.pt where hom
参数：hf : IsLimit kf；hf' : IsLimit kf'；φ : Arrow.mk f ≅ Arrow.mk f'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between points of limit kernel forks induced by an isomorphism
in the category of arrows.
-/
def mapIsoOfIsLimit {kf : KernelFork f} {kf' : KernelFork f'}
    (hf : IsLimit kf) (hf' : IsLimit kf')
    (φ : Arrow.mk f ≅ Arrow.mk f') : kf.pt ≅ kf'.pt where
  hom := kf.mapOfIsLimit hf' φ.hom
  inv := kf'.mapOfIsLimit hf φ.inv
  hom_inv_id := Fork.IsLimit.hom_ext hf (by simp)
  inv_hom_id := Fork.IsLimit.hom_ext hf' (by simp)

end KernelFork

section

variable [HasKernel f]

/-- The kernel of a morphism, expressed as the equalizer with the 0 morphism. -/
/-
**CategoryTheory.Limits.kernel** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limit
s`。
形式化陈述：kernel (f : X ⟶ Y) [HasKernel f] : C
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a morphism, expressed as the equalizer with the 0 morphism.
-/
abbrev kernel (f : X ⟶ Y) [HasKernel f] : C :=
  equalizer f 0

/-- The map from `kernel f` into the source of `f`. -/
/-
**CategoryTheory.Limits.kernel.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limi
ts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from `kernel f` into the source of `f`.
-/
abbrev kernel.ι : kernel f ⟶ X :=
  equalizer.ι f 0

@[simp]
/-
**CategoryTheory.Limits.equalizer_as_kernel** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：equalizer_as_kernel : equalizer.ι f 0 = kernel.ι f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equalizer_as_kernel : equalizer.ι f 0 = kernel.ι f := rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.kernel.condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.kernel`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   (f : X ⟶ Y) [inst_2 : CategoryThe
ory.Limits.HasKernel f],   CategoryTheory.CategoryStruct.comp (CategoryTheory.Li
mits.kernel.ι f) f = 0
参数：f : X ⟶ Y；CategoryTheory.Limits.kernel.ι f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.KernelFork.condition`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
 {X Y : C}   {f : X ⟶ Y} (s : Ca…
-/
theorem kernel.condition : kernel.ι f ≫ f = 0 :=
  KernelFork.condition _

set_option backward.defeqAttrib.useBackward true in
/-- The kernel built from `kernel.ι f` is limiting. -/
/-
**CategoryTheory.Limits.kernelIsKernel** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：kernelIsKernel : IsLimit (Fork.ofι (kernel.ι f) ((kernel.condition f).tran
s comp_zero.symm))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel built from `kernel.ι f` is limiting.
-/
def kernelIsKernel : IsLimit (Fork.ofι (kernel.ι f) ((kernel.condition f).trans comp_zero.symm)) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (Fork.ext (Iso.refl _) (by simp))

/-- Given any morphism `k : W ⟶ X` satisfying `k ≫ f = 0`, `k` factors through `kernel.ι f`
via `kernel.lift : W ⟶ kernel f`. -/
/-
**CategoryTheory.Limits.kernel.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.kernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           [inst_2 : CategoryTheory.Limits.HasKernel f] →             {W : C
} → (k : W ⟶ X) → CategoryTheory.CategoryStruct.comp k f = 0 → (W ⟶ CategoryTheo
ry.Limits.kernel f)
参数：f : X ⟶ Y；k : W ⟶ X；W ⟶ CategoryTheory.Limits.kernel f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given any morphism `k : W ⟶ X` satisfying `k ≫ f = 0`, `k` factors through `kern
el.ι f`
via `kernel.lift : W ⟶ kernel f`.
-/
abbrev kernel.lift {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f :=
  (kernelIsKernel f).lift (KernelFork.ofι k h)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.kernel.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kernel.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : kernel.lift f k h ≫ kernel.ι f = k :=
  (kernelIsKernel f).fac (KernelFork.ofι k h) WalkingParallelPair.zero

@[simp]
/-
**CategoryTheory.Limits.kernel.lift_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.kernel`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   (f : X ⟶ Y) [inst_2 : CategoryThe
ory.Limits.HasKernel f] {W : C} {h : CategoryTheory.CategoryStruct.comp 0 f = 0}
,   CategoryTheory.Limits.kernel.lift f 0 h = 0
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kernel.lift_zero {W : C} {h} : kernel.lift f (0 : W ⟶ X) h = 0 := by
  ext; simp
/-
**CategoryTheory.Limits.kernel.lift_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.kernel`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   (f : X ⟶ Y) [inst_2 : CategoryThe
ory.Limits.HasKernel f] {W : C} (k : W ⟶ X)   (h : CategoryTheory.CategoryStruct
.comp k f = 0) [CategoryTheory.Mono k],   CategoryTheory.Mono (CategoryTheory.Li
mits.kernel.lift f k h)
参数：f : X ⟶ Y；k : W ⟶ X；h : CategoryTheory.CategoryStruct.comp k f = 0；CategoryTh
eory.Limits.kernel.lift f k h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
-/
instance kernel.lift_mono {W : C} (k : W ⟶ X) (h : k ≫ f = 0) [Mono k] : Mono (kernel.lift f k h) :=
  ⟨fun {Z} g g' w => by
    replace w := w =≫ kernel.ι f
    simp only [Category.assoc, kernel.lift_ι] at w
    exact (cancel_mono k).1 w⟩

/-- Any morphism `k : W ⟶ X` satisfying `k ≫ f = 0` induces a morphism `l : W ⟶ kernel f` such that
`l ≫ kernel.ι f = k`. -/
/-
**CategoryTheory.Limits.kernel.lift'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.kernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           [inst_2 : CategoryTheory.Limits.HasKernel f] →             {W : C
} →               (k : W ⟶ X) →                 CategoryTheory.CategoryStruct.co
mp k f = 0 →                   { l // CategoryTheory.CategoryStruct.comp l (Cate
goryTheory.Limits.kernel.ι f) = k }
参数：f : X ⟶ Y；k : W ⟶ X；CategoryTheory.Limits.kernel.ι f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…

--- 原说明 ---
Any morphism `k : W ⟶ X` satisfying `k ≫ f = 0` induces a morphism `l : W ⟶ kern
el f` such that
`l ≫ kernel.ι f = k`.
-/
def kernel.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : { l : W ⟶ kernel f // l ≫ kernel.ι f = k } :=
  ⟨kernel.lift f k h, kernel.lift_ι _ _ _⟩

/-- A commuting square induces a morphism of kernels. -/
/-
**CategoryTheory.Limits.kernel.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.kernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           [inst_2 : CategoryTheory.Limits.HasKernel f] →             {X' Y'
 : C} →               (f' : X' ⟶ Y') →                 [inst_3 : CategoryTheory.
Limits.HasKernel f'] →                   (p : X ⟶ X') →                     (q :
 Y ⟶ Y') →                       CategoryTheory.CategoryStruct.comp f q = Catego
ryTheory.CategoryStruct.comp p f' →                         (CategoryTheory.Limi
ts.kernel f ⟶ CategoryTheory.Limits.kernel f')
参数：f : X ⟶ Y；f' : X' ⟶ Y'；p : X ⟶ X'；q : Y ⟶ Y'；CategoryTheory.Limits.kernel f ⟶
 CategoryTheory.Limits.kernel f'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commuting square induces a morphism of kernels.
-/
abbrev kernel.map {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') : kernel f ⟶ kernel f' :=
  kernel.lift f' (kernel.ι f ≫ p) (by simp [← w])

@[simp]
/-
**CategoryTheory.Limits.kernel.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.kernel`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   (f : X ⟶ Y) [inst_2 : CategoryThe
ory.Limits.HasKernel f] (q : Y ⟶ Y)   (w :     CategoryTheory.CategoryStruct.com
p f q = CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.id X) 
f),   CategoryTheory.Limits.kernel.map f f (CategoryTheory.CategoryStruct.id X) 
q w =     CategoryTheory.CategoryStruct.id (CategoryTheory.Limits.kernel f)
参数：f : X ⟶ Y；q : Y ⟶ Y；w :     CategoryTheory.CategoryStruct.comp f q = Category
Theory.CategoryStruct.comp (CategoryTheory.CategoryStruct.id X) f；CategoryTheory
.CategoryStruct.id X；CategoryTheory.Limits.kernel f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma kernel.map_id {X Y : C} (f : X ⟶ Y) [HasKernel f] (q : Y ⟶ Y)
    (w : f ≫ q = 𝟙 _ ≫ f) : kernel.map f f (𝟙 _) q w = 𝟙 _ := by
  cat_disch
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') [IsIso p] [Mono q] :
    IsIso (kernel.map _ _ _ _ w) :=
  ⟨kernel.lift _ (kernel.ι f' ≫ inv p) (by simp [← cancel_mono q, w]),
    by cat_disch, by cat_disch⟩

/-- Given a commutative diagram
```
    X --f--> Y --g--> Z
    |        |        |
    |        |        |
    v        v        v
    X' -f'-> Y' -g'-> Z'
```
with horizontal arrows composing to zero,
then we obtain a commutative square
```
   X ---> kernel g
   |         |
   |         | kernel.map
   |         |
   v         v
   X' --> kernel g'
```
-/
/-
**CategoryTheory.Limits.kernel.lift_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.kernel`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {X Y Z X' Y' Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z
) [inst_2 : CategoryTheory.Limits.HasKernel g]   (w : CategoryTheory.CategoryStr
uct.comp f g = 0) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')   [inst_3 : CategoryTheory.Limit
s.HasKernel g'] (w' : CategoryTheory.CategoryStruct.comp f' g' = 0) (p : X ⟶ X')
   (q : Y ⟶ Y') (r : Z ⟶ Z'),   CategoryTheory.CategoryStruct.comp f q = Categor
yTheory.CategoryStruct.comp p f' →     ∀ (h₂ : CategoryTheory.CategoryStruct.com
p g r = CategoryTheory.CategoryStruct.comp q g'),       CategoryTheory.CategoryS
truct.comp (CategoryTheory.Limits.kernel.lift g f w)           (CategoryTheory.L
imits.kernel.map g g' q r h₂) =         CategoryTheory.CategoryStruct.comp p (Ca
tegoryTheory.Limits.kernel.lift g' f' w')
参数：f : X ⟶ Y；g : Y ⟶ Z；w : CategoryTheory.CategoryStruct.comp f g = 0；f' : X' ⟶ 
Y'；g' : Y' ⟶ Z'；w' : CategoryTheory.CategoryStruct.comp f' g' = 0；p : X ⟶ X'；q :
 Y ⟶ Y'；r : Z ⟶ Z'；h₂ : CategoryTheory.CategoryStruct.comp g r = CategoryTheory.
CategoryStruct.comp q g'；CategoryTheory.Limits.kernel.lift g f w；CategoryTheory.
Limits.kernel.map g g' q r h₂；CategoryTheory.Limits.kernel.lift g' f' w'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι_assoc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
{X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given a commutative diagram
```
    X --f--> Y --g--> Z
    |        |        |
    |        |        |
    v        v        v
    X' -f'-> Y' -g'-> Z'
```
with horizontal arrows composing to zero,
then we obtain a commutative square
```
   X ---> kernel g
   |         |
   |         | kernel.map
   |         |
   v         v
   X' --> kernel g'
```
-/
theorem kernel.lift_map {X Y Z X' Y' Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel g] (w : f ≫ g = 0)
    (f' : X' ⟶ Y') (g' : Y' ⟶ Z') [HasKernel g'] (w' : f' ≫ g' = 0) (p : X ⟶ X') (q : Y ⟶ Y')
    (r : Z ⟶ Z') (h₁ : f ≫ q = p ≫ f') (h₂ : g ≫ r = q ≫ g') :
    kernel.lift g f w ≫ kernel.map g g' q r h₂ = p ≫ kernel.lift g' f' w' := by
  ext; simp [h₁]

@[simp]
/-
**CategoryTheory.Limits.kernel.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.kernel`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') 
[inst_2 : CategoryTheory.Limits.HasKernel f]   [inst_3 : CategoryTheory.Limits.H
asKernel f'] (q : Y ⟶ Y')   (w : CategoryTheory.CategoryStruct.comp f q = Catego
ryTheory.CategoryStruct.comp 0 f'),   CategoryTheory.Limits.kernel.map f f' 0 q 
w = 0
参数：f : X ⟶ Y；f' : X' ⟶ Y'；q : Y ⟶ Y'；w : CategoryTheory.CategoryStruct.comp f q 
= CategoryTheory.CategoryStruct.comp 0 f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma kernel.map_zero {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') [HasKernel f] [HasKernel f']
    (q : Y ⟶ Y') (w : f ≫ q = 0 ≫ f') : kernel.map f f' 0 q w = 0 := by
  cat_disch

/-- A commuting square of isomorphisms induces an isomorphism of kernels. -/
@[simps]
/-
**CategoryTheory.Limits.kernel.mapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.kernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           [inst_2 : CategoryTheory.Limits.HasKernel f] →             {X' Y'
 : C} →               (f' : X' ⟶ Y') →                 [inst_3 : CategoryTheory.
Limits.HasKernel f'] →                   (p : X ≅ X') →                     (q :
 Y ≅ Y') →                       CategoryTheory.CategoryStruct.comp f q.hom = Ca
tegoryTheory.CategoryStruct.comp p.hom f' →                         (CategoryThe
ory.Limits.kernel f ≅ CategoryTheory.Limits.kernel f')
参数：f : X ⟶ Y；f' : X' ⟶ Y'；p : X ≅ X'；q : Y ≅ Y'；CategoryTheory.Limits.kernel f ≅
 CategoryTheory.Limits.kernel f'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commuting square of isomorphisms induces an isomorphism of kernels.
-/
def kernel.mapIso {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ≅ X') (q : Y ≅ Y')
    (w : f ≫ q.hom = p.hom ≫ f') : kernel f ≅ kernel f' where
  hom := kernel.map f f' p.hom q.hom w
  inv :=
    kernel.map f' f p.inv q.inv
      (by
        refine (cancel_mono q.hom).1 ?_
        simp [w])

/-- Every kernel of the zero morphism is an isomorphism -/
/-
**CategoryTheory.Limits.kernel.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every kernel of the zero morphism is an isomorphism
-/
instance kernel.ι_zero_isIso : IsIso (kernel.ι (0 : X ⟶ Y)) :=
  equalizer.ι_of_self _
/-
**CategoryTheory.Limits.eq_zero_of_epi_kernel** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：eq_zero_of_epi_kernel [Epi (kernel.ι f)] : f = 0
参数：kernel.ι f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_zero_of_epi_kernel [Epi (kernel.ι f)] : f = 0 :=
  (cancel_epi (kernel.ι f)).1 (by simp)

/-- The kernel of a zero morphism is isomorphic to the source. -/
/-
**CategoryTheory.Limits.kernelZeroIsoSource** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：kernelZeroIsoSource : kernel (0 : X ⟶ Y) ≅ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a zero morphism is isomorphic to the source.
-/
def kernelZeroIsoSource : kernel (0 : X ⟶ Y) ≅ X :=
  equalizer.isoSourceOfSelf 0

@[simp]
/-
**CategoryTheory.Limits.kernelZeroIsoSource_hom** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：kernelZeroIsoSource_hom : kernelZeroIsoSource.hom = kernel.ι (0 : X ⟶ Y)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kernelZeroIsoSource_hom : kernelZeroIsoSource.hom = kernel.ι (0 : X ⟶ Y) := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.kernelZeroIsoSource_inv** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：kernelZeroIsoSource_inv : kernelZeroIsoSource.inv = kernel.lift (0 : X ⟶ Y
) (𝟙 X) (by simp)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.equalizer.isoSourceOfSelf_inv`：∀ {C : Type u} {X Y
 : C} [inst : CategoryTheory.Category.{v, u} C] (f : X ⟶ Y),   (CategoryTheory.L
imits.equalizer.isoSourceOfSelf f).inv = …
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kernelZeroIsoSource_inv :
    kernelZeroIsoSource.inv = kernel.lift (0 : X ⟶ Y) (𝟙 X) (by simp) := by
  ext
  simp [kernelZeroIsoSource]

/-- If two morphisms are known to be equal, then their kernels are isomorphic. -/
/-
**CategoryTheory.Limits.kernelIsoOfEq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：kernelIsoOfEq {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) : kern
el f ≅ kernel g
参数：h : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two morphisms are known to be equal, then their kernels are isomorphic.
-/
def kernelIsoOfEq {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) : kernel f ≅ kernel g :=
  HasLimit.isoOfNatIso (by rw [h])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.kernelIsoOfEq_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：kernelIsoOfEq_refl {h : f = f} : kernelIsoOfEq h = Iso.refl (kernel f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.HasLimit.isoOfNatIso_hom_π`：∀ {J : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Cate
gory.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kernelIsoOfEq_refl {h : f = f} : kernelIsoOfEq h = Iso.refl (kernel f) := by
  ext
  simp [kernelIsoOfEq]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.kernelIsoOfEq_hom_comp_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kernelIsoOfEq_hom_comp_ι {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) :
    (kernelIsoOfEq h).hom ≫ kernel.ι g = kernel.ι f := by
  subst h; simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.kernelIsoOfEq_inv_comp_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kernelIsoOfEq_inv_comp_ι {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) :
    (kernelIsoOfEq h).inv ≫ kernel.ι _ = kernel.ι _ := by
  subst h; simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.lift_comp_kernelIsoOfEq_hom** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：lift_comp_kernelIsoOfEq_hom {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] 
(h : f = g) (e : Z ⟶ X) (he) : kernel.lift _ e he ≫ (kernelIsoOfEq h).hom = kern
el.lift _ e (by simp [← h, he])
参数：h : f = g；e : Z ⟶ X；he。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernelIsoOfEq_refl`：kernelIsoOfEq_refl {h : f = f}
 : kernelIsoOfEq h = Iso.refl (kernel f)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_comp_kernelIsoOfEq_hom {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
    (e : Z ⟶ X) (he) :
    kernel.lift _ e he ≫ (kernelIsoOfEq h).hom = kernel.lift _ e (by simp [← h, he]) := by
  subst h; simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.lift_comp_kernelIsoOfEq_inv** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：lift_comp_kernelIsoOfEq_inv {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] 
(h : f = g) (e : Z ⟶ X) (he) : kernel.lift _ e he ≫ (kernelIsoOfEq h).inv = kern
el.lift _ e (by simp [h, he])
参数：h : f = g；e : Z ⟶ X；he。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernelIsoOfEq_refl`：kernelIsoOfEq_refl {h : f = f}
 : kernelIsoOfEq h = Iso.refl (kernel f)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem lift_comp_kernelIsoOfEq_inv {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
    (e : Z ⟶ X) (he) :
    kernel.lift _ e he ≫ (kernelIsoOfEq h).inv = kernel.lift _ e (by simp [h, he]) := by
  cases h; simp

@[simp]
/-
**CategoryTheory.Limits.kernelIsoOfEq_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：kernelIsoOfEq_trans {f g h : X ⟶ Y} [HasKernel f] [HasKernel g] [HasKernel
 h] (w₁ : f = g) (w₂ : g = h) : kernelIsoOfEq w₁ ≪≫ kernelIsoOfEq w₂ = kernelIso
OfEq (w₁.trans w₂)
参数：w₁ : f = g；w₂ : g = h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernelIsoOfEq_refl`：kernelIsoOfEq_refl {h : f = f}
 : kernelIsoOfEq h = Iso.refl (kernel f)
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem kernelIsoOfEq_trans {f g h : X ⟶ Y} [HasKernel f] [HasKernel g] [HasKernel h] (w₁ : f = g)
    (w₂ : g = h) : kernelIsoOfEq w₁ ≪≫ kernelIsoOfEq w₂ = kernelIsoOfEq (w₁.trans w₂) := by
  cases w₁; simp

variable {f}
/-
**CategoryTheory.Limits.kernel_not_epi_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：kernel_not_epi_of_nonzero (w : f != 0) : ¬Epi (kernel.ι f)
参数：w : f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.eq_zero_of_epi_kernel`：eq_zero_of_epi_kernel [Epi 
(kernel.ι f)] : f = 0
-/
theorem kernel_not_epi_of_nonzero (w : f ≠ 0) : ¬Epi (kernel.ι f) := fun _ =>
  w (eq_zero_of_epi_kernel f)
/-
**CategoryTheory.Limits.kernel_not_iso_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：kernel_not_iso_of_nonzero (w : f != 0) : IsIso (kernel.ι f) -> False
参数：w : f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.kernel_not_epi_of_nonzero`：kernel_not_epi_of_nonze
ro (w : f != 0) : ¬Epi (kernel.ι f)
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
-/
theorem kernel_not_iso_of_nonzero (w : f ≠ 0) : IsIso (kernel.ι f) → False := fun _ =>
  kernel_not_epi_of_nonzero w inferInstance
/-
**CategoryTheory.Limits.hasKernel_comp_mono** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：hasKernel_comp_mono {X Y Z : C} (f : X ⟶ Y) [HasKernel f] (g : Y ⟶ Z) [Mon
o g] : HasKernel (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasKernel_comp_mono {X Y Z : C} (f : X ⟶ Y) [HasKernel f] (g : Y ⟶ Z) [Mono g] :
    HasKernel (f ≫ g) :=
  ⟨⟨{   cone := _
        isLimit := isKernelCompMono (limit.isLimit _) g rfl }⟩⟩

/-- When `g` is a monomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of `f`.
-/
@[simps]
/-
**CategoryTheory.Limits.kernelCompMono** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：kernelCompMono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel f] [Mono g] 
: kernel (f ≫ g) ≅ kernel f where hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `g` is a monomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of
 `f`.
-/
def kernelCompMono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel f] [Mono g] :
    kernel (f ≫ g) ≅ kernel f where
  hom :=
    kernel.lift _ (kernel.ι _)
      (by
        rw [← cancel_mono g]
        simp)
  inv := kernel.lift _ (kernel.ι _) (by simp)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.hasKernel_iso_comp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：hasKernel_iso_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [HasKerne
l g] : HasKernel (f ≫ g) where exists_limit
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.KernelFork.condition`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
 {X Y : C}   {f : X ⟶ Y} (s : Ca…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι_assoc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
{X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.kernel.lift.congr_simp`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C] {X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
-/
instance hasKernel_iso_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [HasKernel g] :
    HasKernel (f ≫ g) where
  exists_limit :=
    ⟨{  cone := KernelFork.ofι (kernel.ι g ≫ inv f) (by simp)
        isLimit := isLimitAux _ (fun s => kernel.lift _ (s.ι ≫ f) (by simp))
            (by simp) fun s (m : _ ⟶ kernel _) w => by
          simp_rw [← w]
          apply equalizer.hom_ext
          simp }⟩

/-- When `f` is an isomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of `g`.
-/
@[simps]
/-
**CategoryTheory.Limits.kernelIsIsoComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：kernelIsIsoComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [HasKernel g
] : kernel (f ≫ g) ≅ kernel g where hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `f` is an isomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of
 `g`.
-/
def kernelIsIsoComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [HasKernel g] :
    kernel (f ≫ g) ≅ kernel g where
  hom := kernel.lift _ (kernel.ι _ ≫ f) (by simp)
  inv := kernel.lift _ (kernel.ι _ ≫ inv f) (by simp)

@[deprecated (since := "2026-07-03")] alias kernel.congr := kernelIsoOfEq
/-
**CategoryTheory.Limits.isZero_kernel_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：isZero_kernel_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] [HasKernel f] : IsZer
o (kernel f)
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.KernelFork.IsLimit.isZero_of_mono`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {X Y : C}   {f : X ⟶ Y} {c : Ca…
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
-/
lemma isZero_kernel_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] [HasKernel f] :
    IsZero (kernel f) :=
  KernelFork.IsLimit.isZero_of_mono (c := KernelFork.ofι _ (kernel.condition f))
    (kernelIsKernel f)

end

section HasZeroObject

variable [HasZeroObject C]

open ZeroObject

/-- The morphism from the zero object determines a cone on a kernel diagram -/
@[simps! pt]
/-
**CategoryTheory.Limits.kernel.zeroKernelFork** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.kernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} → (f : X ⟶ Y) → [Ca
tegoryTheory.Limits.HasZeroObject C] → CategoryTheory.Limits.KernelFork f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism from the zero object determines a cone on a kernel diagram
-/
def kernel.zeroKernelFork : KernelFork f :=
  KernelFork.ofι (0 : 0 ⟶ X) zero_comp

@[simp]
/-
**CategoryTheory.Limits.kernel.zeroKernelFork_** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma kernel.zeroKernelFork_ι : (kernel.zeroKernelFork f).ι = 0 := rfl

/-- The map from the zero object is a kernel of a monomorphism -/
/-
**CategoryTheory.Limits.kernel.isLimitConeZeroCone** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.kernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           [inst_2 : CategoryTheory.Limits.HasZeroObject C] →             [C
ategoryTheory.Mono f] → CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.ker
nel.zeroKernelFork f)
参数：f : X ⟶ Y；CategoryTheory.Limits.kernel.zeroKernelFork f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the zero object is a kernel of a monomorphism
-/
def kernel.isLimitConeZeroCone [Mono f] : IsLimit (kernel.zeroKernelFork f) :=
  Fork.IsLimit.mk _ (fun _ => 0)
    (fun s => by
      rw [zero_comp]
      refine (zero_of_comp_mono f ?_).symm
      exact KernelFork.condition _)
    fun _ _ _ => zero_of_to_zero _

/-- The kernel of a monomorphism is isomorphic to the zero object -/
/-
**CategoryTheory.Limits.kernel.ofMono** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.kernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           [inst_2 : CategoryTheory.Limits.HasZeroObject C] →             [i
nst_3 : CategoryTheory.Limits.HasKernel f] → [CategoryTheory.Mono f] → CategoryT
heory.Limits.kernel f ≅ 0
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a monomorphism is isomorphic to the zero object
-/
def kernel.ofMono [HasKernel f] [Mono f] : kernel f ≅ 0 :=
  Functor.mapIso (Cone.forget _) <|
    IsLimit.uniqueUpToIso (limit.isLimit (parallelPair f 0)) (kernel.isLimitConeZeroCone f)

/-- The kernel morphism of a monomorphism is a zero morphism -/
/-
**CategoryTheory.Limits.kernel.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel morphism of a monomorphism is a zero morphism
-/
theorem kernel.ι_of_mono [HasKernel f] [Mono f] : kernel.ι f = 0 :=
  zero_of_source_iso_zero _ (kernel.ofMono f)

/-- If `g ≫ f = 0` implies `g = 0` for all `g`, then `0 : 0 ⟶ X` is a kernel of `f`. -/
/-
**CategoryTheory.Limits.zeroKernelOfCancelZero** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：zeroKernelOfCancelZero {X Y : C} (f : X ⟶ Y) (hf : forall (Z : C) (g : Z ⟶
 X) (_ : g ≫ f = 0), g = 0) : IsLimit (KernelFork.ofι (0 : 0 ⟶ X) (show 0 ≫ f = 
0 by simp))
参数：f : X ⟶ Y；hf : forall (Z : C) (g : Z ⟶ X) (_ : g ≫ f = 0), g = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g ≫ f = 0` implies `g = 0` for all `g`, then `0 : 0 ⟶ X` is a kernel of `f`.
-/
def zeroKernelOfCancelZero {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (Z : C) (g : Z ⟶ X) (_ : g ≫ f = 0), g = 0) :
    IsLimit (KernelFork.ofι (0 : 0 ⟶ X) (show 0 ≫ f = 0 by simp)) :=
  Fork.IsLimit.mk _ (fun _ => 0) (fun s => by rw [hf _ _ (KernelFork.condition s), zero_comp])
    fun s m _ => by apply HasZeroObject.to_zero_ext

end HasZeroObject

section Transport

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport an `IsKernel` across isomorphisms. -/
/-
**CategoryTheory.Limits.IsKernel.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.IsKernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           {X' Y' : C} →             {f' : X' ⟶ Y'} →               {s : Cat
egoryTheory.Limits.KernelFork f} →                 CategoryTheory.Limits.IsLimit
 s →                   (s' : CategoryTheory.Limits.KernelFork f') →             
        (eX : X ≅ X') →                       (eY : Y ≅ Y') →                   
      (e : s.pt ≅ s'.pt) →                           CategoryTheory.CategoryStru
ct.comp eX.hom f' = CategoryTheory.CategoryStruct.comp f eY.hom →               
              CategoryTheory.CategoryStruct.comp e.hom (CategoryTheory.Limits.Fo
rk.ι s') =                                 CategoryTheory.CategoryStruct.comp (C
ategoryTheory.Limits.Fork.ι s) eX.hom →                               CategoryTh
eory.Limits.IsLimit s'
参数：f : X ⟶ Y；s' : CategoryTheory.Limits.KernelFork f'；eX : X ≅ X'；eY : Y ≅ Y'；e 
: s.pt ≅ s'.pt；CategoryTheory.Limits.Fork.ι s'；CategoryTheory.Limits.Fork.ι s。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transport an `IsKernel` across isomorphisms.
-/
def IsKernel.ofIso {X' Y' : C} {f' : X' ⟶ Y'} {s : KernelFork f} (hs : IsLimit s)
    (s' : KernelFork f') (eX : X ≅ X') (eY : Y ≅ Y') (e : s.pt ≅ s'.pt)
    (H : eX.hom ≫ f' = f ≫ eY.hom) (H' : e.hom ≫ s'.ι = s.ι ≫ eX.hom) :
    IsLimit s' :=
  let α : parallelPair f 0 ≅ parallelPair f' 0 := parallelPairIsoMk eX eY H.symm (by simp)
  IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv α s).symm hs) <|
    Cone.ext e (by rintro (_ | _) <;> simp [α, ← H'])

set_option backward.isDefEq.respectTransparency false in
/-- If `i` is an isomorphism such that `l ≫ i.hom = f`, any kernel of `f` is a kernel of `l`. -/
/-
**CategoryTheory.Limits.IsKernel.ofCompIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.IsKernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           {Z : C} →             (l : X ⟶ Z) →               (i : Z ≅ Y) →  
               (h : CategoryTheory.CategoryStruct.comp l i.hom = f) →           
        {s : CategoryTheory.Limits.KernelFork f} →                     CategoryT
heory.Limits.IsLimit s →                       CategoryTheory.Limits.IsLimit    
                     (CategoryTheory.Limits.KernelFork.ofι (CategoryTheory.Limit
s.Fork.ι s) ⋯)
参数：f : X ⟶ Y；l : X ⟶ Z；i : Z ≅ Y；h : CategoryTheory.CategoryStruct.comp l i.hom 
= f；CategoryTheory.Limits.KernelFork.ofι (CategoryTheory.Limits.Fork.ι s) ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i` is an isomorphism such that `l ≫ i.hom = f`, any kernel of `f` is a kerne
l of `l`.
-/
def IsKernel.ofCompIso {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.hom = f) {s : KernelFork f}
    (hs : IsLimit s) :
    IsLimit
      (KernelFork.ofι (Fork.ι s) <| show Fork.ι s ≫ l = 0 by simp [← i.comp_inv_eq.2 h.symm]) :=
  Fork.IsLimit.mk _ (fun s => hs.lift <| KernelFork.ofι (Fork.ι s) <| by simp [← h])
    (fun s => by simp) fun s m h => by
      apply Fork.IsLimit.hom_ext hs
      simpa using h

/-- If `i` is an isomorphism such that `l ≫ i.hom = f`, the kernel of `f` is a kernel of `l`. -/
/-
**CategoryTheory.Limits.kernel.ofCompIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.kernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           [inst_2 : CategoryTheory.Limits.HasKernel f] →             {Z : C
} →               (l : X ⟶ Z) →                 (i : Z ≅ Y) →                   
(h : CategoryTheory.CategoryStruct.comp l i.hom = f) →                     Categ
oryTheory.Limits.IsLimit                       (CategoryTheory.Limits.KernelFork
.ofι (CategoryTheory.Limits.kernel.ι f) ⋯)
参数：f : X ⟶ Y；l : X ⟶ Z；i : Z ≅ Y；h : CategoryTheory.CategoryStruct.comp l i.hom 
= f；CategoryTheory.Limits.KernelFork.ofι (CategoryTheory.Limits.kernel.ι f) ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i` is an isomorphism such that `l ≫ i.hom = f`, the kernel of `f` is a kerne
l of `l`.
-/
def kernel.ofCompIso [HasKernel f] {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.hom = f) :
    IsLimit
      (KernelFork.ofι (kernel.ι f) <| show kernel.ι f ≫ l = 0 by simp [← i.comp_inv_eq.2 h.symm]) :=
  IsKernel.ofCompIso f l i h <| limit.isLimit _

set_option backward.defeqAttrib.useBackward true in
/-- If `s` is any limit kernel cone over `f` and if `i` is an isomorphism such that
`i.hom ≫ s.ι = l`, then `l` is a kernel of `f`. -/
/-
**CategoryTheory.Limits.IsKernel.isoKernel** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.IsKernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           {Z : C} →             (l : Z ⟶ X) →               {s : CategoryTh
eory.Limits.KernelFork f} →                 CategoryTheory.Limits.IsLimit s →   
                (i : Z ≅ s.pt) →                     (h : CategoryTheory.Categor
yStruct.comp i.hom (CategoryTheory.Limits.Fork.ι s) = l) →                      
 CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.KernelFork.ofι l ⋯)
参数：f : X ⟶ Y；l : Z ⟶ X；i : Z ≅ s.pt；h : CategoryTheory.CategoryStruct.comp i.hom
 (CategoryTheory.Limits.Fork.ι s) = l；CategoryTheory.Limits.KernelFork.ofι l ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is any limit kernel cone over `f` and if `i` is an isomorphism such that
`i.hom ≫ s.ι = l`, then `l` is a kernel of `f`.
-/
def IsKernel.isoKernel {Z : C} (l : Z ⟶ X) {s : KernelFork f} (hs : IsLimit s) (i : Z ≅ s.pt)
    (h : i.hom ≫ Fork.ι s = l) : IsLimit (KernelFork.ofι l <| show l ≫ f = 0 by simp [← h]) :=
  IsLimit.ofIsoLimit hs <|
    Cone.ext i.symm fun j => by
      cases j
      · exact (Iso.eq_inv_comp i).2 h
      · dsimp; rw [← h]; simp

/-- If `i` is an isomorphism such that `i.hom ≫ kernel.ι f = l`, then `l` is a kernel of `f`. -/
/-
**CategoryTheory.Limits.kernel.isoKernel** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.kernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           [inst_2 : CategoryTheory.Limits.HasKernel f] →             {Z : C
} →               (l : Z ⟶ X) →                 (i : Z ≅ CategoryTheory.Limits.k
ernel f) →                   (h : CategoryTheory.CategoryStruct.comp i.hom (Cate
goryTheory.Limits.kernel.ι f) = l) →                     CategoryTheory.Limits.I
sLimit (CategoryTheory.Limits.KernelFork.ofι l ⋯)
参数：f : X ⟶ Y；l : Z ⟶ X；i : Z ≅ CategoryTheory.Limits.kernel f；h : CategoryTheory
.CategoryStruct.comp i.hom (CategoryTheory.Limits.kernel.ι f) = l；CategoryTheory
.Limits.KernelFork.ofι l ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i` is an isomorphism such that `i.hom ≫ kernel.ι f = l`, then `l` is a kerne
l of `f`.
-/
def kernel.isoKernel [HasKernel f] {Z : C} (l : Z ⟶ X) (i : Z ≅ kernel f)
    (h : i.hom ≫ kernel.ι f = l) :
    IsLimit (@KernelFork.ofι _ _ _ _ _ f _ l <| by simp [← h]) :=
  IsKernel.isoKernel f l (limit.isLimit _) i h

end Transport

section

/-- The kernel morphism of a zero morphism is an isomorphism -/
/-
**CategoryTheory.Limits.kernel.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel morphism of a zero morphism is an isomorphism
-/
theorem kernel.ι_of_zero {f : X ⟶ Y} [HasKernel f] (eq : f = 0) :
    IsIso (kernel.ι f) := equalizer.ι_of_eq eq

end

section

/-- A cokernel cofork is just a cofork where the second morphism is a zero morphism. -/
/-
**CategoryTheory.Limits.CokernelCofork** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：CokernelCofork
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cokernel cofork is just a cofork where the second morphism is a zero morphism.
-/
abbrev CokernelCofork :=
  Cofork f 0

variable {f}

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.CokernelCofork.condition** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.CokernelCofork`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   {f : X ⟶ Y} (s : CategoryTheory.L
imits.CokernelCofork f),   CategoryTheory.CategoryStruct.comp f (CategoryTheory.
Limits.Cofork.π s) = 0
参数：s : CategoryTheory.Limits.CokernelCofork f；CategoryTheory.Limits.Cofork.π s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Cofork.condition`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Cofo
rk f g),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
theorem CokernelCofork.condition (s : CokernelCofork f) : f ≫ s.π = 0 := by
  rw [Cofork.condition, zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.CokernelCofork.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem CokernelCofork.π_eq_zero (s : CokernelCofork f) : s.ι.app zero = 0 := by
  simp

/-- A morphism `π` satisfying `f ≫ π = 0` determines a cokernel cofork on `f`. -/
/-
**CategoryTheory.Limits.CokernelCofork.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `π` satisfying `f ≫ π = 0` determines a cokernel cofork on `f`.
-/
abbrev CokernelCofork.ofπ {Z : C} (π : Y ⟶ Z) (w : f ≫ π = 0) : CokernelCofork f :=
  Cofork.ofπ π <| by rw [w, zero_comp]

@[simp]
/-
**CategoryTheory.Limits.CokernelCofork.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem CokernelCofork.π_ofπ {X Y P : C} (f : X ⟶ Y) (π : Y ⟶ P) (w : f ≫ π = 0) :
    Cofork.π (CokernelCofork.ofπ π w) = π :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- Every cokernel cofork `s` is isomorphic (actually, equal) to `cofork.ofπ (cofork.π s) _`. -/
/-
**CategoryTheory.Limits.isoOf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every cokernel cofork `s` is isomorphic (actually, equal) to `cofork.ofπ (cofork
.π s) _`.
-/
def isoOfπ (s : Cofork f 0) : s ≅ Cofork.ofπ (Cofork.π s) (Cofork.condition s) :=
  Cocone.ext (Iso.refl _) fun j => by cases j <;> cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/-- If `π = π'`, then `CokernelCofork.of_π π _` and `CokernelCofork.of_π π' _` are isomorphic. -/
/-
**CategoryTheory.Limits.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `π = π'`, then `CokernelCofork.of_π π _` and `CokernelCofork.of_π π' _` are i
somorphic.
-/
def ofπCongr {P : C} {π π' : Y ⟶ P} {w : f ≫ π = 0} (h : π = π') :
    CokernelCofork.ofπ π w ≅ CokernelCofork.ofπ π' (by rw [← h, w]) :=
  Cocone.ext (Iso.refl _) fun j => by cases j <;> cat_disch

/-- If `s` is a colimit cokernel cofork, then every `k : Y ⟶ W` satisfying `f ≫ k = 0` induces
`l : s.X ⟶ W` such that `cofork.π s ≫ l = k`. -/
/-
**CategoryTheory.Limits.CokernelCofork.IsColimit.desc'** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.CokernelCofork.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         {f : X ⟶ 
Y} →           {s : CategoryTheory.Limits.CokernelCofork f} →             Catego
ryTheory.Limits.IsColimit s →               {W : C} →                 (k : Y ⟶ W
) →                   CategoryTheory.CategoryStruct.comp f k = 0 →              
       { l // CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Cofork.π
 s) l = k }
参数：k : Y ⟶ W；CategoryTheory.Limits.Cofork.π s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a colimit cokernel cofork, then every `k : Y ⟶ W` satisfying `f ≫ k = 
0` induces
`l : s.X ⟶ W` such that `cofork.π s ≫ l = k`.
-/
def CokernelCofork.IsColimit.desc' {s : CokernelCofork f} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = 0) : { l : s.pt ⟶ W // Cofork.π s ≫ l = k } :=
  ⟨hs.desc <| CokernelCofork.ofπ _ h, hs.fac _ _⟩

set_option backward.defeqAttrib.useBackward true in
/-- This is a slightly more convenient method to verify that a cokernel cofork is a colimit cocone.
It only asks for a proof of facts that carry any mathematical content -/
/-
**CategoryTheory.Limits.isColimitAux** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：isColimitAux (t : CokernelCofork f) (desc : forall s : CokernelCofork f, t
.pt ⟶ s.pt) (fac : forall s : CokernelCofork f, t.π ≫ desc s = s.π) (uniq : fora
ll (s : CokernelCofork f) (m : t.pt ⟶ s.pt) (_ : t.π ≫ m = s.π), m = desc s) : I
sColimit t
参数：t : CokernelCofork f；desc : forall s : CokernelCofork f, t.pt ⟶ s.pt；fac : fo
rall s : CokernelCofork f, t.π ≫ desc s = s.π；uniq : forall (s : CokernelCofork 
f) (m : t.pt ⟶ s.pt) (_ : t.π ≫ m = s.π), m = desc s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a slightly more convenient method to verify that a cokernel cofork is a 
colimit cocone.
It only asks for a proof of facts that carry any mathematical content
-/
def isColimitAux (t : CokernelCofork f) (desc : ∀ s : CokernelCofork f, t.pt ⟶ s.pt)
    (fac : ∀ s : CokernelCofork f, t.π ≫ desc s = s.π)
    (uniq : ∀ (s : CokernelCofork f) (m : t.pt ⟶ s.pt) (_ : t.π ≫ m = s.π), m = desc s) :
    IsColimit t :=
  { desc
    fac := fun s j => by
      cases j
      · simp
      · exact fac s
    uniq := fun s m w => uniq s m (w Limits.WalkingParallelPair.one) }

/-- This is a more convenient formulation to show that a `CokernelCofork` constructed using
`CokernelCofork.ofπ` is a limit cone.
-/
/-
**CategoryTheory.Limits.CokernelCofork.IsColimit.of** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a more convenient formulation to show that a `CokernelCofork` constructe
d using
`CokernelCofork.ofπ` is a limit cone.
-/
def CokernelCofork.IsColimit.ofπ {Z : C} (g : Y ⟶ Z) (eq : f ≫ g = 0)
    (desc : ∀ {Z' : C} (g' : Y ⟶ Z') (_ : f ≫ g' = 0), Z ⟶ Z')
    (fac : ∀ {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0), g ≫ desc g' eq' = g')
    (uniq :
      ∀ {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0) (m : Z ⟶ Z') (_ : g ≫ m = g'), m = desc g' eq') :
    IsColimit (CokernelCofork.ofπ g eq) :=
  isColimitAux _ (fun s => desc s.π s.condition) (fun s => fac s.π s.condition) fun s =>
    uniq s.π s.condition

/-- This is a more convenient formulation to show that a `CokernelCofork` of the form
`CokernelCofork.ofπ p _` is a colimit cocone when we know that `p` is an epimorphism. -/
/-
**CategoryTheory.Limits.CokernelCofork.IsColimit.of** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a more convenient formulation to show that a `CokernelCofork` of the for
m
`CokernelCofork.ofπ p _` is a colimit cocone when we know that `p` is an epimorp
hism.
-/
def CokernelCofork.IsColimit.ofπ' {X Y Q : C} {f : X ⟶ Y} (p : Y ⟶ Q) (w : f ≫ p = 0)
    (h : ∀ {A : C} (k : Y ⟶ A) (_ : f ≫ k = 0), { l : Q ⟶ A // p ≫ l = k}) [hp : Epi p] :
    IsColimit (CokernelCofork.ofπ p w) :=
  ofπ _ _ (fun {_} k hk => (h k hk).1) (fun {_} k hk => (h k hk).2) (fun {A} k hk m hm => by
    rw [← cancel_epi p, (h k hk).2, hm])

set_option backward.isDefEq.respectTransparency false in
/-- Every cokernel of `f` induces a cokernel of `g ≫ f` if `g` is epi. -/
/-
**CategoryTheory.Limits.isCokernelEpiComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：isCokernelEpiComp {c : CokernelCofork f} (i : IsColimit c) {W} (g : W ⟶ X)
 [hg : Epi g] {h : W ⟶ Y} (hh : h = g ≫ f) : IsColimit (CokernelCofork.ofπ c.π (
by rw [hh]; simp) : CokernelCofork h)
参数：i : IsColimit c；g : W ⟶ X；hh : h = g ≫ f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.CokernelCofork.condition`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   {f : X ⟶ Y} (s : Ca…

--- 原说明 ---
Every cokernel of `f` induces a cokernel of `g ≫ f` if `g` is epi.
-/
def isCokernelEpiComp {c : CokernelCofork f} (i : IsColimit c) {W} (g : W ⟶ X) [hg : Epi g]
    {h : W ⟶ Y} (hh : h = g ≫ f) :
    IsColimit (CokernelCofork.ofπ c.π (by rw [hh]; simp) : CokernelCofork h) :=
  Cofork.IsColimit.mk' _ fun s =>
    let s' : CokernelCofork f :=
      Cofork.ofπ s.π
        (by
          apply hg.left_cancellation
          rw [← Category.assoc, ← hh, s.condition]
          simp)
    let l := CokernelCofork.IsColimit.desc' i s'.π s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Cofork.IsColimit.hom_ext i; rw [Cofork.π_ofπ] at hm; rw [hm]; exact l.2.symm⟩

@[simp]
/-
**CategoryTheory.Limits.isCokernelEpiComp_desc** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：isCokernelEpiComp_desc {c : CokernelCofork f} (i : IsColimit c) {W} (g : W
 ⟶ X) [hg : Epi g] {h : W ⟶ Y} (hh : h = g ≫ f) (s : CokernelCofork h) : (isCoke
rnelEpiComp i g hh).desc s = i.desc (Cofork.ofπ s.π (by rw [← cancel_epi g]; rw 
[← Category.assoc]; rw [← hh] simp))
参数：i : IsColimit c；g : W ⟶ X；hh : h = g ≫ f；s : CokernelCofork h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isCokernelEpiComp_desc {c : CokernelCofork f} (i : IsColimit c) {W} (g : W ⟶ X) [hg : Epi g]
    {h : W ⟶ Y} (hh : h = g ≫ f) (s : CokernelCofork h) :
    (isCokernelEpiComp i g hh).desc s =
      i.desc
        (Cofork.ofπ s.π
          (by
            rw [← cancel_epi g, ← Category.assoc, ← hh]
            simp)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every cokernel of `g ≫ f` is also a cokernel of `f`, as long as `f ≫ c.π` vanishes. -/
/-
**CategoryTheory.Limits.isCokernelOfComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：isCokernelOfComp {W : C} (g : W ⟶ X) (h : W ⟶ Y) {c : CokernelCofork h} (i
 : IsColimit c) (hf : f ≫ c.π = 0) (hfg : g ≫ f = h) : IsColimit (CokernelCofork
.ofπ c.π hf)
参数：g : W ⟶ X；h : W ⟶ Y；i : IsColimit c；hf : f ≫ c.π = 0；hfg : g ≫ f = h。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every cokernel of `g ≫ f` is also a cokernel of `f`, as long as `f ≫ c.π` vanish
es.
-/
def isCokernelOfComp {W : C} (g : W ⟶ X) (h : W ⟶ Y) {c : CokernelCofork h} (i : IsColimit c)
    (hf : f ≫ c.π = 0) (hfg : g ≫ f = h) : IsColimit (CokernelCofork.ofπ c.π hf) :=
  Cofork.IsColimit.mk _ (fun s => i.desc (CokernelCofork.ofπ s.π (by simp [← hfg])))
    (fun s => by simp only [CokernelCofork.π_ofπ, Cofork.IsColimit.π_desc]) fun s m h => by
      apply Cofork.IsColimit.hom_ext i
      simpa using h

/-- `Y` identifies to the cokernel of a zero map `X ⟶ Y`. -/
/-
**CategoryTheory.Limits.CokernelCofork.IsColimit.ofId** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.CokernelCofork.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           (hf : f = 0) →             CategoryTheory.Limits.IsColimit       
        (CategoryTheory.Limits.CokernelCofork.ofπ (CategoryTheory.CategoryStruct
.id Y) ⋯)
参数：f : X ⟶ Y；hf : f = 0；CategoryTheory.Limits.CokernelCofork.ofπ (CategoryTheory
.CategoryStruct.id Y) ⋯。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
`Y` identifies to the cokernel of a zero map `X ⟶ Y`.
-/
def CokernelCofork.IsColimit.ofId {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
    IsColimit (CokernelCofork.ofπ (𝟙 Y) (show f ≫ 𝟙 Y = 0 by rw [hf, zero_comp])) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun x _ => x) (fun _ _ => Category.id_comp _)
    (fun _ _ _ hb => by simp only [← hb, Category.id_comp])

/-- Any zero object identifies to the cokernel of a given epimorphisms. -/
/-
**CategoryTheory.Limits.CokernelCofork.IsColimit.ofEpiOfIsZero** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Limits.CokernelCofork.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         {f : X ⟶ 
Y} →           (c : CategoryTheory.Limits.CokernelCofork f) →             Catego
ryTheory.Epi f → CategoryTheory.Limits.IsZero c.pt → CategoryTheory.Limits.IsCol
imit c
参数：c : CategoryTheory.Limits.CokernelCofork f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any zero object identifies to the cokernel of a given epimorphisms.
-/
def CokernelCofork.IsColimit.ofEpiOfIsZero {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
    (hf : Epi f) (h : IsZero c.pt) : IsColimit c :=
  isColimitAux _ (fun _ => 0) (fun s => by rw [comp_zero, ← cancel_epi f, comp_zero, s.condition])
    (fun _ _ _ => h.eq_of_src _ _)
/-
**CategoryTheory.Limits.CokernelCofork.IsColimit.isIso_** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma CokernelCofork.IsColimit.isIso_π {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
    (hc : IsColimit c) (hf : f = 0) : IsIso c.π :=
  isIso_colimit_cocone_parallelPair_of_eq hf hc

set_option backward.isDefEq.respectTransparency false in
/-- If `c` is a colimit cokernel cofork for `f : X ⟶ Y`, `e : Y ≅ Y'` and `f' : X' ⟶ Y` is a
morphism, then there is a colimit cokernel cofork for `f'` with the same point as `c` if for any
morphism `φ : Y ⟶ W`, there is an equivalence `f ≫ φ = 0 ↔ f' ≫ e.hom ≫ φ = 0`. -/
/-
**CategoryTheory.Limits.CokernelCofork.isColimitOfIsColimitOfIff** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Limits.CokernelCofork`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         {f : X ⟶ 
Y} →           {c : CategoryTheory.Limits.CokernelCofork f} →             Catego
ryTheory.Limits.IsColimit c →               {X' Y' : C} →                 (f' : 
X' ⟶ Y') →                   (e : Y' ≅ Y) →                     (iff :          
               ∀ ⦃W : C⦄ (φ : Y ⟶ W),                           CategoryTheory.C
ategoryStruct.comp f φ = 0 ↔                             CategoryTheory.Category
Struct.comp f' (CategoryTheory.CategoryStruct.comp e.hom φ) = 0) →              
         CategoryTheory.Limits.IsColimit                         (CategoryTheory
.Limits.CokernelCofork.ofπ                           (CategoryTheory.CategoryStr
uct.comp e.hom (CategoryTheory.Limits.Cofork.π c)) ⋯)
参数：f' : X' ⟶ Y'；e : Y' ≅ Y；iff :                         ∀ ⦃W : C⦄ (φ : Y ⟶ W), 
                          CategoryTheory.CategoryStruct.comp f φ = 0 ↔          
                   CategoryTheory.CategoryStruct.comp f' (CategoryTheory.Categor
yStruct.comp e.hom φ) = 0；CategoryTheory.Limits.CokernelCofork.ofπ              
             (CategoryTheory.CategoryStruct.comp e.hom (CategoryTheory.Limits.Co
fork.π c)) ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a colimit cokernel cofork for `f : X ⟶ Y`, `e : Y ≅ Y'` and `f' : X' ⟶
 Y` is a
morphism, then there is a colimit cokernel cofork for `f'` with the same point a
s `c` if for any
morphism `φ : Y ⟶ W`, there is an equivalence `f ≫ φ = 0 ↔ f' ≫ e.hom ≫ φ = 0`.
-/
def CokernelCofork.isColimitOfIsColimitOfIff {X Y : C} {f : X ⟶ Y} {c : CokernelCofork f}
    (hc : IsColimit c) {X' Y' : C} (f' : X' ⟶ Y') (e : Y' ≅ Y)
    (iff : ∀ ⦃W : C⦄ (φ : Y ⟶ W), f ≫ φ = 0 ↔ f' ≫ e.hom ≫ φ = 0) :
    IsColimit (CokernelCofork.ofπ (f := f') (e.hom ≫ c.π) (by simp [← iff])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun s hs ↦ hc.desc (CokernelCofork.ofπ (π := e.inv ≫ s)
      (by rw [iff, e.hom_inv_id_assoc, hs])))
    (fun s hs ↦ by simp)
    (fun s hs m hm ↦ Cofork.IsColimit.hom_ext hc (by simpa [← cancel_epi e.hom] using hm))

set_option backward.defeqAttrib.useBackward true in
/-- If `c` is a colimit cokernel cofork for `f : X ⟶ Y`, and `f' : X' ⟶ Y` is another
morphism, then there is a colimit cokernel cofork for `f'` with the same point as `c` if for any
morphism `φ : Y ⟶ W`, there is an equivalence `f ≫ φ = 0 ↔ f' ≫ φ = 0`. -/
/-
**CategoryTheory.Limits.CokernelCofork.isColimitOfIsColimitOfIff'** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Limits.CokernelCofork`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         {f : X ⟶ 
Y} →           {c : CategoryTheory.Limits.CokernelCofork f} →             Catego
ryTheory.Limits.IsColimit c →               {X' : C} →                 (f' : X' 
⟶ Y) →                   (iff :                       ∀ ⦃W : C⦄ (φ : Y ⟶ W),    
                     CategoryTheory.CategoryStruct.comp f φ = 0 ↔ CategoryTheory
.CategoryStruct.comp f' φ = 0) →                     CategoryTheory.Limits.IsCol
imit                       (CategoryTheory.Limits.CokernelCofork.ofπ (CategoryTh
eory.Limits.Cofork.π c) ⋯)
参数：f' : X' ⟶ Y；iff :                       ∀ ⦃W : C⦄ (φ : Y ⟶ W),               
          CategoryTheory.CategoryStruct.comp f φ = 0 ↔ CategoryTheory.CategorySt
ruct.comp f' φ = 0；CategoryTheory.Limits.CokernelCofork.ofπ (CategoryTheory.Limi
ts.Cofork.π c) ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a colimit cokernel cofork for `f : X ⟶ Y`, and `f' : X' ⟶ Y` is anothe
r
morphism, then there is a colimit cokernel cofork for `f'` with the same point a
s `c` if for any
morphism `φ : Y ⟶ W`, there is an equivalence `f ≫ φ = 0 ↔ f' ≫ φ = 0`.
-/
def CokernelCofork.isColimitOfIsColimitOfIff' {X Y : C} {f : X ⟶ Y} {c : CokernelCofork f}
    (hc : IsColimit c) {X' : C} (f' : X' ⟶ Y)
    (iff : ∀ ⦃W : C⦄ (φ : Y ⟶ W), f ≫ φ = 0 ↔ f' ≫ φ = 0) :
    IsColimit (CokernelCofork.ofπ (f := f') c.π (by simp [← iff])) :=
  IsColimit.ofIsoColimit (isColimitOfIsColimitOfIff hc f' (Iso.refl _) (by simpa using iff))
    (Cofork.ext (Iso.refl _))
/-
**CategoryTheory.Limits.CokernelCofork.IsColimit.isZero_of_epi** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits.CokernelCofork.IsColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   {f : X ⟶ Y} {c : CategoryTheory.L
imits.CokernelCofork f} (hc : CategoryTheory.Limits.IsColimit c)   [CategoryTheo
ry.Epi f], CategoryTheory.Limits.IsZero c.pt
参数：hc : CategoryTheory.Limits.IsColimit c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.epi`：∀ {C : Type u} {X Y : C} [in
st : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Limits.
Cofork f g}   (hs : CategoryTheo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.CokernelCofork.condition_assoc`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C] {X Y : C}   {f : X ⟶ Y} (s : Ca…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma CokernelCofork.IsColimit.isZero_of_epi {X Y : C} {f : X ⟶ Y}
    {c : CokernelCofork f} (hc : IsColimit c) [Epi f] : IsZero c.pt := by
  have := Cofork.IsColimit.epi hc
  rw [IsZero.iff_id_eq_zero, ← cancel_epi c.π, ← cancel_epi f,
    c.condition_assoc, comp_zero, comp_zero, zero_comp]

end

namespace CokernelCofork

variable {f} {X' Y' : C} {f' : X' ⟶ Y'}

set_option backward.isDefEq.respectTransparency false in
/-- The morphism between points of cokernel coforks induced by a morphism
in the category of arrows. -/
/-
**CategoryTheory.Limits.CokernelCofork.mapOfIsColimit** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.CokernelCofork`。
形式化陈述：mapOfIsColimit {cc : CokernelCofork f} (hf : IsColimit cc) (cc' : Cokernel
Cofork f') (φ : Arrow.mk f ⟶ Arrow.mk f') : cc.pt ⟶ cc'.pt
参数：hf : IsColimit cc；cc' : CokernelCofork f'；φ : Arrow.mk f ⟶ Arrow.mk f'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism between points of cokernel coforks induced by a morphism
in the category of arrows.
-/
def mapOfIsColimit {cc : CokernelCofork f} (hf : IsColimit cc) (cc' : CokernelCofork f')
    (φ : Arrow.mk f ⟶ Arrow.mk f') : cc.pt ⟶ cc'.pt :=
  hf.desc (CokernelCofork.ofπ (φ.right ≫ cc'.π) (by
    erw [← Arrow.w_assoc φ, condition, comp_zero]))

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.CokernelCofork.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Limits.CokernelCofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma π_mapOfIsColimit {cc : CokernelCofork f} (hf : IsColimit cc) (cc' : CokernelCofork f')
    (φ : Arrow.mk f ⟶ Arrow.mk f') :
    cc.π ≫ mapOfIsColimit hf cc' φ = φ.right ≫ cc'.π :=
  hf.fac _ _

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between points of limit cokernel coforks induced by an isomorphism
in the category of arrows. -/
@[simps]
/-
**CategoryTheory.Limits.CokernelCofork.mapIsoOfIsColimit** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits.CokernelCofork`。
形式化陈述：mapIsoOfIsColimit {cc : CokernelCofork f} {cc' : CokernelCofork f'} (hf : 
IsColimit cc) (hf' : IsColimit cc') (φ : Arrow.mk f ≅ Arrow.mk f') : cc.pt ≅ cc'
.pt where hom
参数：hf : IsColimit cc；hf' : IsColimit cc'；φ : Arrow.mk f ≅ Arrow.mk f'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between points of limit cokernel coforks induced by an isomorphi
sm
in the category of arrows.
-/
def mapIsoOfIsColimit {cc : CokernelCofork f} {cc' : CokernelCofork f'}
    (hf : IsColimit cc) (hf' : IsColimit cc')
    (φ : Arrow.mk f ≅ Arrow.mk f') : cc.pt ≅ cc'.pt where
  hom := mapOfIsColimit hf cc' φ.hom
  inv := mapOfIsColimit hf' cc φ.inv
  hom_inv_id := Cofork.IsColimit.hom_ext hf (by simp)
  inv_hom_id := Cofork.IsColimit.hom_ext hf' (by simp)

end CokernelCofork

section

variable [HasCokernel f]

/-- The cokernel of a morphism, expressed as the coequalizer with the 0 morphism. -/
/-
**CategoryTheory.Limits.cokernel** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：cokernel : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel of a morphism, expressed as the coequalizer with the 0 morphism.
-/
abbrev cokernel : C :=
  coequalizer f 0

/-- The map from the target of `f` to `cokernel f`. -/
/-
**CategoryTheory.Limits.cokernel.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Li
mits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the target of `f` to `cokernel f`.
-/
abbrev cokernel.π : Y ⟶ cokernel f :=
  coequalizer.π f 0

@[simp]
/-
**CategoryTheory.Limits.coequalizer_as_cokernel** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：coequalizer_as_cokernel : coequalizer.π f 0 = cokernel.π f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coequalizer_as_cokernel : coequalizer.π f 0 = cokernel.π f :=
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.cokernel.condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.cokernel`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   (f : X ⟶ Y) [inst_2 : CategoryThe
ory.Limits.HasCokernel f],   CategoryTheory.CategoryStruct.comp f (CategoryTheor
y.Limits.cokernel.π f) = 0
参数：f : X ⟶ Y；CategoryTheory.Limits.cokernel.π f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.CokernelCofork.condition`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   {f : X ⟶ Y} (s : Ca…
-/
theorem cokernel.condition : f ≫ cokernel.π f = 0 :=
  CokernelCofork.condition _

set_option backward.defeqAttrib.useBackward true in
/-- The cokernel built from `cokernel.π f` is colimiting. -/
/-
**CategoryTheory.Limits.cokernelIsCokernel** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：cokernelIsCokernel : IsColimit (Cofork.ofπ (cokernel.π f) ((cokernel.condi
tion f).trans zero_comp.symm))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel built from `cokernel.π f` is colimiting.
-/
def cokernelIsCokernel :
    IsColimit (Cofork.ofπ (cokernel.π f) ((cokernel.condition f).trans zero_comp.symm)) :=
  IsColimit.ofIsoColimit (colimit.isColimit _) (Cofork.ext (Iso.refl _))

/-- Given any morphism `k : Y ⟶ W` such that `f ≫ k = 0`, `k` factors through `cokernel.π f`
via `cokernel.desc : cokernel f ⟶ W`. -/
/-
**CategoryTheory.Limits.cokernel.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.cokernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           [inst_2 : CategoryTheory.Limits.HasCokernel f] →             {W :
 C} → (k : Y ⟶ W) → CategoryTheory.CategoryStruct.comp f k = 0 → (CategoryTheory
.Limits.cokernel f ⟶ W)
参数：f : X ⟶ Y；k : Y ⟶ W；CategoryTheory.Limits.cokernel f ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given any morphism `k : Y ⟶ W` such that `f ≫ k = 0`, `k` factors through `coker
nel.π f`
via `cokernel.desc : cokernel f ⟶ W`.
-/
abbrev cokernel.desc {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) : cokernel f ⟶ W :=
  (cokernelIsCokernel f).desc (CokernelCofork.ofπ k h)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.cokernel.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limi
ts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cokernel.π_desc {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) :
    cokernel.π f ≫ cokernel.desc f k h = k :=
  (cokernelIsCokernel f).fac (CokernelCofork.ofπ k h) WalkingParallelPair.one

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.colimit_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limit
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma colimit_ι_zero_cokernel_desc {C : Type*} [Category* C]
    [HasZeroMorphisms C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0) [HasCokernel f] :
    colimit.ι (parallelPair f 0) WalkingParallelPair.zero ≫ cokernel.desc f g h = 0 := by
  rw [(colimit.w (parallelPair f 0) WalkingParallelPairHom.left).symm]
  simp

@[simp]
/-
**CategoryTheory.Limits.cokernel.desc_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.cokernel`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   (f : X ⟶ Y) [inst_2 : CategoryThe
ory.Limits.HasCokernel f] {W : C} {h : CategoryTheory.CategoryStruct.comp f 0 = 
0},   CategoryTheory.Limits.cokernel.desc f 0 h = 0
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cokernel.desc_zero {W : C} {h} : cokernel.desc f (0 : Y ⟶ W) h = 0 := by
  ext; simp
/-
**CategoryTheory.Limits.cokernel.desc_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.cokernel`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   (f : X ⟶ Y) [inst_2 : CategoryThe
ory.Limits.HasCokernel f] {W : C} (k : Y ⟶ W)   (h : CategoryTheory.CategoryStru
ct.comp f k = 0) [CategoryTheory.Epi k],   CategoryTheory.Epi (CategoryTheory.Li
mits.cokernel.desc f k h)
参数：f : X ⟶ Y；k : Y ⟶ W；h : CategoryTheory.CategoryStruct.comp f k = 0；CategoryTh
eory.Limits.cokernel.desc f k h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
] {X Y : C}   (f : X ⟶ Y) [inst_2…
-/
instance cokernel.desc_epi {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) [Epi k] :
    Epi (cokernel.desc f k h) :=
  ⟨fun {Z} g g' w => by
    replace w := cokernel.π f ≫= w
    simp only [cokernel.π_desc_assoc] at w
    exact (cancel_epi k).1 w⟩

/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = 0` induces `l : cokernel f ⟶ W` such that
`cokernel.π f ≫ l = k`. -/
/-
**CategoryTheory.Limits.cokernel.desc'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.cokernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           [inst_2 : CategoryTheory.Limits.HasCokernel f] →             {W :
 C} →               (k : Y ⟶ W) →                 CategoryTheory.CategoryStruct.
comp f k = 0 →                   { l // CategoryTheory.CategoryStruct.comp (Cate
goryTheory.Limits.cokernel.π f) l = k }
参数：f : X ⟶ Y；k : Y ⟶ W；CategoryTheory.Limits.cokernel.π f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…

--- 原说明 ---
Any morphism `k : Y ⟶ W` satisfying `f ≫ k = 0` induces `l : cokernel f ⟶ W` suc
h that
`cokernel.π f ≫ l = k`.
-/
def cokernel.desc' {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) :
    { l : cokernel f ⟶ W // cokernel.π f ≫ l = k } :=
  ⟨cokernel.desc f k h, cokernel.π_desc _ _ _⟩

/-- A commuting square induces a morphism of cokernels. -/
/-
**CategoryTheory.Limits.cokernel.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.cokernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           [inst_2 : CategoryTheory.Limits.HasCokernel f] →             {X' 
Y' : C} →               (f' : X' ⟶ Y') →                 [inst_3 : CategoryTheor
y.Limits.HasCokernel f'] →                   (p : X ⟶ X') →                     
(q : Y ⟶ Y') →                       CategoryTheory.CategoryStruct.comp f q = Ca
tegoryTheory.CategoryStruct.comp p f' →                         (CategoryTheory.
Limits.cokernel f ⟶ CategoryTheory.Limits.cokernel f')
参数：f : X ⟶ Y；f' : X' ⟶ Y'；p : X ⟶ X'；q : Y ⟶ Y'；CategoryTheory.Limits.cokernel f
 ⟶ CategoryTheory.Limits.cokernel f'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commuting square induces a morphism of cokernels.
-/
abbrev cokernel.map {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') : cokernel f ⟶ cokernel f' :=
  cokernel.desc f (q ≫ cokernel.π f') (by
    have : f ≫ q ≫ π f' = p ≫ f' ≫ π f' := by
      simp only [← Category.assoc]
      apply congrArg (· ≫ π f') w
    simp [this])
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') [Epi p] [IsIso q] :
    IsIso (cokernel.map _ _ _ _ w) :=
  ⟨cokernel.desc _ (inv q ≫ cokernel.π f) (by simp [← cancel_epi p, ← reassoc_of% w]),
    by cat_disch, by cat_disch⟩

@[simp]
/-
**CategoryTheory.Limits.cokernel.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.cokernel`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   (f : X ⟶ Y) [inst_2 : CategoryThe
ory.Limits.HasCokernel f] (q : X ⟶ X)   (w :     CategoryTheory.CategoryStruct.c
omp f (CategoryTheory.CategoryStruct.id Y) = CategoryTheory.CategoryStruct.comp 
q f),   CategoryTheory.Limits.cokernel.map f f q (CategoryTheory.CategoryStruct.
id Y) w =     CategoryTheory.CategoryStruct.id (CategoryTheory.Limits.cokernel f
)
参数：f : X ⟶ Y；q : X ⟶ X；w :     CategoryTheory.CategoryStruct.comp f (CategoryThe
ory.CategoryStruct.id Y) = CategoryTheory.CategoryStruct.comp q f；CategoryTheory
.CategoryStruct.id Y；CategoryTheory.Limits.cokernel f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cokernel.map_id {X Y : C} (f : X ⟶ Y) [HasCokernel f] (q : X ⟶ X)
    (w : f ≫ 𝟙 _ = q ≫ f) : cokernel.map f f q (𝟙 _) w = 𝟙 _ := by
  cat_disch

/-- Given a commutative diagram
```
    X --f--> Y --g--> Z
    |        |        |
    |        |        |
    v        v        v
    X' -f'-> Y' -g'-> Z'
```
with horizontal arrows composing to zero,
then we obtain a commutative square
```
   cokernel f ---> Z
   |               |
   | cokernel.map  |
   |               |
   v               v
   cokernel f' --> Z'
```
-/
/-
**CategoryTheory.Limits.cokernel.map_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.cokernel`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {X Y Z X' Y' Z' : C} (f : X ⟶ Y) [inst_2 : 
CategoryTheory.Limits.HasCokernel f] (g : Y ⟶ Z)   (w : CategoryTheory.CategoryS
truct.comp f g = 0) (f' : X' ⟶ Y') [inst_3 : CategoryTheory.Limits.HasCokernel f
']   (g' : Y' ⟶ Z') (w' : CategoryTheory.CategoryStruct.comp f' g' = 0) (p : X ⟶
 X') (q : Y ⟶ Y') (r : Z ⟶ Z')   (h₁ : CategoryTheory.CategoryStruct.comp f q = 
CategoryTheory.CategoryStruct.comp p f'),   CategoryTheory.CategoryStruct.comp g
 r = CategoryTheory.CategoryStruct.comp q g' →     CategoryTheory.CategoryStruct
.comp (CategoryTheory.Limits.cokernel.map f f' p q h₁)         (CategoryTheory.L
imits.cokernel.desc f' g' w') =       CategoryTheory.CategoryStruct.comp (Catego
ryTheory.Limits.cokernel.desc f g w) r
参数：f : X ⟶ Y；g : Y ⟶ Z；w : CategoryTheory.CategoryStruct.comp f g = 0；f' : X' ⟶ 
Y'；g' : Y' ⟶ Z'；w' : CategoryTheory.CategoryStruct.comp f' g' = 0；p : X ⟶ X'；q :
 Y ⟶ Y'；r : Z ⟶ Z'；h₁ : CategoryTheory.CategoryStruct.comp f q = CategoryTheory.
CategoryStruct.comp p f'；CategoryTheory.Limits.cokernel.map f f' p q h₁；Category
Theory.Limits.cokernel.desc f' g' w'；CategoryTheory.Limits.cokernel.desc f g w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
] {X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given a commutative diagram
```
    X --f--> Y --g--> Z
    |        |        |
    |        |        |
    v        v        v
    X' -f'-> Y' -g'-> Z'
```
with horizontal arrows composing to zero,
then we obtain a commutative square
```
   cokernel f ---> Z
   |               |
   | cokernel.map  |
   |               |
   v               v
   cokernel f' --> Z'
```
-/
theorem cokernel.map_desc {X Y Z X' Y' Z' : C} (f : X ⟶ Y) [HasCokernel f] (g : Y ⟶ Z)
    (w : f ≫ g = 0) (f' : X' ⟶ Y') [HasCokernel f'] (g' : Y' ⟶ Z') (w' : f' ≫ g' = 0) (p : X ⟶ X')
    (q : Y ⟶ Y') (r : Z ⟶ Z') (h₁ : f ≫ q = p ≫ f') (h₂ : g ≫ r = q ≫ g') :
    cokernel.map f f' p q h₁ ≫ cokernel.desc f' g' w' = cokernel.desc f g w ≫ r := by
  ext; simp [h₂]

@[simp]
/-
**CategoryTheory.Limits.cokernel.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.cokernel`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') 
[inst_2 : CategoryTheory.Limits.HasCokernel f]   [inst_3 : CategoryTheory.Limits
.HasCokernel f'] (q : X ⟶ X')   (w : CategoryTheory.CategoryStruct.comp f 0 = Ca
tegoryTheory.CategoryStruct.comp q f'),   CategoryTheory.Limits.cokernel.map f f
' q 0 w = 0
参数：f : X ⟶ Y；f' : X' ⟶ Y'；q : X ⟶ X'；w : CategoryTheory.CategoryStruct.comp f 0 
= CategoryTheory.CategoryStruct.comp q f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cokernel.map_zero {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
    [HasCokernel f] [HasCokernel f'] (q : X ⟶ X') (w : f ≫ 0 = q ≫ f') :
    cokernel.map f f' q 0 w = 0 := by
  cat_disch

/-- A commuting square of isomorphisms induces an isomorphism of cokernels. -/
@[simps]
/-
**CategoryTheory.Limits.cokernel.mapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.cokernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           [inst_2 : CategoryTheory.Limits.HasCokernel f] →             {X' 
Y' : C} →               (f' : X' ⟶ Y') →                 [inst_3 : CategoryTheor
y.Limits.HasCokernel f'] →                   (p : X ≅ X') →                     
(q : Y ≅ Y') →                       CategoryTheory.CategoryStruct.comp f q.hom 
= CategoryTheory.CategoryStruct.comp p.hom f' →                         (Categor
yTheory.Limits.cokernel f ≅ CategoryTheory.Limits.cokernel f')
参数：f : X ⟶ Y；f' : X' ⟶ Y'；p : X ≅ X'；q : Y ≅ Y'；CategoryTheory.Limits.cokernel f
 ≅ CategoryTheory.Limits.cokernel f'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commuting square of isomorphisms induces an isomorphism of cokernels.
-/
def cokernel.mapIso {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ≅ X') (q : Y ≅ Y')
    (w : f ≫ q.hom = p.hom ≫ f') : cokernel f ≅ cokernel f' where
  hom := cokernel.map f f' p.hom q.hom w
  inv := cokernel.map f' f p.inv q.inv (by
          refine (cancel_mono q.hom).1 ?_
          simp [w])

/-- The cokernel of the zero morphism is an isomorphism -/
/-
**CategoryTheory.Limits.cokernel.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limi
ts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel of the zero morphism is an isomorphism
-/
instance cokernel.π_zero_isIso : IsIso (cokernel.π (0 : X ⟶ Y)) :=
  coequalizer.π_of_self _
/-
**CategoryTheory.Limits.eq_zero_of_mono_cokernel** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：eq_zero_of_mono_cokernel [Mono (cokernel.π f)] : f = 0
参数：cokernel.π f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_zero_of_mono_cokernel [Mono (cokernel.π f)] : f = 0 :=
  (cancel_mono (cokernel.π f)).1 (by simp)

/-- The cokernel of a zero morphism is isomorphic to the target. -/
/-
**CategoryTheory.Limits.cokernelZeroIsoTarget** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：cokernelZeroIsoTarget : cokernel (0 : X ⟶ Y) ≅ Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel of a zero morphism is isomorphic to the target.
-/
def cokernelZeroIsoTarget : cokernel (0 : X ⟶ Y) ≅ Y :=
  coequalizer.isoTargetOfSelf 0

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.cokernelZeroIsoTarget_hom** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：cokernelZeroIsoTarget_hom : cokernelZeroIsoTarget.hom = cokernel.desc (0 :
 X ⟶ Y) (𝟙 Y) (by simp)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coequalizer.isoTargetOfSelf_hom`：∀ {C : Type u} {X
 Y : C} [inst : CategoryTheory.Category.{v, u} C] (f : X ⟶ Y),   (CategoryTheory
.Limits.coequalizer.isoTargetOfSelf f).hom …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cokernelZeroIsoTarget_hom :
    cokernelZeroIsoTarget.hom = cokernel.desc (0 : X ⟶ Y) (𝟙 Y) (by simp) := by
  ext; simp [cokernelZeroIsoTarget]

@[simp]
/-
**CategoryTheory.Limits.cokernelZeroIsoTarget_inv** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：cokernelZeroIsoTarget_inv : cokernelZeroIsoTarget.inv = cokernel.π (0 : X 
⟶ Y)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cokernelZeroIsoTarget_inv : cokernelZeroIsoTarget.inv = cokernel.π (0 : X ⟶ Y) :=
  rfl

/-- If two morphisms are known to be equal, then their cokernels are isomorphic. -/
/-
**CategoryTheory.Limits.cokernelIsoOfEq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：cokernelIsoOfEq {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) 
: cokernel f ≅ cokernel g
参数：h : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two morphisms are known to be equal, then their cokernels are isomorphic.
-/
def cokernelIsoOfEq {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) :
    cokernel f ≅ cokernel g :=
  HasColimit.isoOfNatIso (by simp [h]; rfl)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.cokernelIsoOfEq_refl** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：cokernelIsoOfEq_refl {h : f = f} : cokernelIsoOfEq h = Iso.refl (cokernel 
f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom`：∀ {J : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Ca
tegory.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cokernelIsoOfEq_refl {h : f = f} : cokernelIsoOfEq h = Iso.refl (cokernel f) := by
  ext; simp [cokernelIsoOfEq]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_comp_cokernelIsoOfEq_hom {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) :
    cokernel.π f ≫ (cokernelIsoOfEq h).hom = cokernel.π g := by
  cases h; simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_comp_cokernelIsoOfEq_inv {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) :
    cokernel.π _ ≫ (cokernelIsoOfEq h).inv = cokernel.π _ := by
  cases h; simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.cokernelIsoOfEq_hom_comp_desc** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：cokernelIsoOfEq_hom_comp_desc {Z} {f g : X ⟶ Y} [HasCokernel f] [HasCokern
el g] (h : f = g) (e : Y ⟶ Z) (he) : (cokernelIsoOfEq h).hom ≫ cokernel.desc _ e
 he = cokernel.desc _ e (by simp [h, he])
参数：h : f = g；e : Y ⟶ Z；he。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.cokernelIsoOfEq_refl`：cokernelIsoOfEq_refl {h : f 
= f} : cokernelIsoOfEq h = Iso.refl (cokernel f)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem cokernelIsoOfEq_hom_comp_desc {Z} {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
    (e : Y ⟶ Z) (he) :
    (cokernelIsoOfEq h).hom ≫ cokernel.desc _ e he = cokernel.desc _ e (by simp [h, he]) := by
  cases h; simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.cokernelIsoOfEq_inv_comp_desc** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：cokernelIsoOfEq_inv_comp_desc {Z} {f g : X ⟶ Y} [HasCokernel f] [HasCokern
el g] (h : f = g) (e : Y ⟶ Z) (he) : (cokernelIsoOfEq h).inv ≫ cokernel.desc _ e
 he = cokernel.desc _ e (by simp [← h, he])
参数：h : f = g；e : Y ⟶ Z；he。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.cokernelIsoOfEq_refl`：cokernelIsoOfEq_refl {h : f 
= f} : cokernelIsoOfEq h = Iso.refl (cokernel f)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem cokernelIsoOfEq_inv_comp_desc {Z} {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
    (e : Y ⟶ Z) (he) :
    (cokernelIsoOfEq h).inv ≫ cokernel.desc _ e he = cokernel.desc _ e (by simp [← h, he]) := by
  cases h; simp

@[simp]
/-
**CategoryTheory.Limits.cokernelIsoOfEq_trans** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：cokernelIsoOfEq_trans {f g h : X ⟶ Y} [HasCokernel f] [HasCokernel g] [Has
Cokernel h] (w₁ : f = g) (w₂ : g = h) : cokernelIsoOfEq w₁ ≪≫ cokernelIsoOfEq w₂
 = cokernelIsoOfEq (w₁.trans w₂)
参数：w₁ : f = g；w₂ : g = h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.cokernelIsoOfEq_refl`：cokernelIsoOfEq_refl {h : f 
= f} : cokernelIsoOfEq h = Iso.refl (cokernel f)
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem cokernelIsoOfEq_trans {f g h : X ⟶ Y} [HasCokernel f] [HasCokernel g] [HasCokernel h]
    (w₁ : f = g) (w₂ : g = h) :
    cokernelIsoOfEq w₁ ≪≫ cokernelIsoOfEq w₂ = cokernelIsoOfEq (w₁.trans w₂) := by
  cases w₁; simp

variable {f}
/-
**CategoryTheory.Limits.cokernel_not_mono_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：cokernel_not_mono_of_nonzero (w : f != 0) : ¬Mono (cokernel.π f)
参数：w : f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.eq_zero_of_mono_cokernel`：eq_zero_of_mono_cokernel
 [Mono (cokernel.π f)] : f = 0
-/
theorem cokernel_not_mono_of_nonzero (w : f ≠ 0) : ¬Mono (cokernel.π f) := fun _ =>
  w (eq_zero_of_mono_cokernel f)
/-
**CategoryTheory.Limits.cokernel_not_iso_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：cokernel_not_iso_of_nonzero (w : f != 0) : IsIso (cokernel.π f) -> False
参数：w : f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.cokernel_not_mono_of_nonzero`：cokernel_not_mono_of
_nonzero (w : f != 0) : ¬Mono (cokernel.π f)
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
-/
theorem cokernel_not_iso_of_nonzero (w : f ≠ 0) : IsIso (cokernel.π f) → False := fun _ =>
  cokernel_not_mono_of_nonzero w inferInstance

set_option backward.defeqAttrib.useBackward true in
-- TODO the remainder of this section has obvious generalizations to `HasCoequalizer f g`.
/-
**CategoryTheory.Limits.hasCokernel_comp_iso** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Limits`。
形式化陈述：hasCokernel_comp_iso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCokernel f] [
IsIso g] : HasCokernel (f ≫ g) where exists_colimit
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.CokernelCofork.condition`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   {f : X ⟶ Y} (s : Ca…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.Limits.cokernel.desc.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
-/
instance hasCokernel_comp_iso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCokernel f] [IsIso g] :
    HasCokernel (f ≫ g) where
  exists_colimit :=
    ⟨{  cocone := CokernelCofork.ofπ (inv g ≫ cokernel.π f) (by simp)
        isColimit :=
          isColimitAux _
            (fun s =>
              cokernel.desc _ (g ≫ s.π) (by rw [← Category.assoc, CokernelCofork.condition]))
            (by simp) fun s (m : cokernel _ ⟶ _) w => by
            simp_rw [← w]
            apply coequalizer.hom_ext
            simp }⟩

/-- When `g` is an isomorphism, the cokernel of `f ≫ g` is isomorphic to the cokernel of `f`.
-/
@[simps]
/-
**CategoryTheory.Limits.cokernelCompIsIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：cokernelCompIsIso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCokernel f] [IsI
so g] : cokernel (f ≫ g) ≅ cokernel f where hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `g` is an isomorphism, the cokernel of `f ≫ g` is isomorphic to the cokerne
l of `f`.
-/
def cokernelCompIsIso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCokernel f] [IsIso g] :
    cokernel (f ≫ g) ≅ cokernel f where
  hom := cokernel.desc _ (inv g ≫ cokernel.π f) (by simp)
  inv := cokernel.desc _ (g ≫ cokernel.π (f ≫ g)) (by rw [← Category.assoc, cokernel.condition])
/-
**CategoryTheory.Limits.hasCokernel_epi_comp** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Limits`。
形式化陈述：hasCokernel_epi_comp {X Y : C} (f : X ⟶ Y) [HasCokernel f] {W} (g : W ⟶ X)
 [Epi g] : HasCokernel (g ≫ f)
参数：f : X ⟶ Y；g : W ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCokernel_epi_comp {X Y : C} (f : X ⟶ Y) [HasCokernel f] {W} (g : W ⟶ X) [Epi g] :
    HasCokernel (g ≫ f) :=
  ⟨⟨{   cocone := _
        isColimit := isCokernelEpiComp (colimit.isColimit _) g rfl }⟩⟩

/-- When `f` is an epimorphism, the cokernel of `f ≫ g` is isomorphic to the cokernel of `g`.
-/
@[simps]
/-
**CategoryTheory.Limits.cokernelEpiComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：cokernelEpiComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] [HasCokernel g
] : cokernel (f ≫ g) ≅ cokernel g where hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `f` is an epimorphism, the cokernel of `f ≫ g` is isomorphic to the cokerne
l of `g`.
-/
def cokernelEpiComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] [HasCokernel g] :
    cokernel (f ≫ g) ≅ cokernel g where
  hom := cokernel.desc _ (cokernel.π g) (by simp)
  inv :=
    cokernel.desc _ (cokernel.π (f ≫ g))
      (by
        rw [← cancel_epi f, ← Category.assoc]
        simp)

@[deprecated (since := "2026-07-03")] alias cokernel.congr := cokernelIsoOfEq
/-
**CategoryTheory.Limits.isZero_cokernel_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：isZero_cokernel_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] [HasCokernel f] : IsZ
ero (cokernel f)
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.CokernelCofork.IsColimit.isZero_of_epi`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C] {X Y : C}   {f : X ⟶ Y} {c : Ca…
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
-/
lemma isZero_cokernel_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] [HasCokernel f] :
    IsZero (cokernel f) :=
  CokernelCofork.IsColimit.isZero_of_epi (c := CokernelCofork.ofπ _ (cokernel.condition f))
    (cokernelIsCokernel f)

end

section HasZeroObject

variable [HasZeroObject C]

open ZeroObject

/-- The morphism to the zero object determines a cocone on a cokernel diagram -/
@[simps! pt]
/-
**CategoryTheory.Limits.cokernel.zeroCokernelCofork** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.cokernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} → (f : X ⟶ Y) → [Ca
tegoryTheory.Limits.HasZeroObject C] → CategoryTheory.Limits.CokernelCofork f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism to the zero object determines a cocone on a cokernel diagram
-/
def cokernel.zeroCokernelCofork : CokernelCofork f :=
    CokernelCofork.ofπ (0 : Y ⟶ 0) comp_zero

@[simp]
/-
**CategoryTheory.Limits.cokernel.zeroCokernelCofork_** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cokernel.zeroCokernelCofork_π : (cokernel.zeroCokernelCofork f).π = 0 := rfl

/-- The morphism to the zero object is a cokernel of an epimorphism -/
/-
**CategoryTheory.Limits.cokernel.isColimitCoconeZeroCocone** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits.cokernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           [inst_2 : CategoryTheory.Limits.HasZeroObject C] →             [C
ategoryTheory.Epi f] →               CategoryTheory.Limits.IsColimit (CategoryTh
eory.Limits.cokernel.zeroCokernelCofork f)
参数：f : X ⟶ Y；CategoryTheory.Limits.cokernel.zeroCokernelCofork f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism to the zero object is a cokernel of an epimorphism
-/
def cokernel.isColimitCoconeZeroCocone [Epi f] : IsColimit (cokernel.zeroCokernelCofork f) :=
  Cofork.IsColimit.mk _ (fun _ => 0)
    fun _ => by simp [zero_of_epi_comp f _]
    fun _ _ _ => zero_of_from_zero _

/-- The cokernel of an epimorphism is isomorphic to the zero object -/
/-
**CategoryTheory.Limits.cokernel.ofEpi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.cokernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           [inst_2 : CategoryTheory.Limits.HasZeroObject C] →             [i
nst_3 : CategoryTheory.Limits.HasCokernel f] →               [CategoryTheory.Epi
 f] → CategoryTheory.Limits.cokernel f ≅ 0
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel of an epimorphism is isomorphic to the zero object
-/
def cokernel.ofEpi [HasCokernel f] [Epi f] : cokernel f ≅ 0 :=
  Functor.mapIso (Cocone.forget _) <|
    IsColimit.uniqueUpToIso (colimit.isColimit (parallelPair f 0))
      (cokernel.isColimitCoconeZeroCocone f)

/-- The cokernel morphism of an epimorphism is a zero morphism -/
/-
**CategoryTheory.Limits.cokernel.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limi
ts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel morphism of an epimorphism is a zero morphism
-/
theorem cokernel.π_of_epi [HasCokernel f] [Epi f] : cokernel.π f = 0 :=
  zero_of_target_iso_zero _ (cokernel.ofEpi f)

end HasZeroObject

section MonoFactorisation

variable {f}

@[simp]
/-
**CategoryTheory.Limits.MonoFactorisation.kernel_** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoFactorisation.kernel_ι_comp [HasKernel f] (F : MonoFactorisation f) :
    kernel.ι f ≫ F.e = 0 := by
  rw [← cancel_mono F.m, zero_comp, Category.assoc, F.fac, kernel.condition]

end MonoFactorisation

section HasImage

/-- The cokernel of the image inclusion of a morphism `f` is isomorphic to the cokernel of `f`.

(This result requires that the factorisation through the image is an epimorphism.
This holds in any category with equalizers.)
-/
@[simps]
/-
**CategoryTheory.Limits.cokernelImage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel of the image inclusion of a morphism `f` is isomorphic to the coker
nel of `f`.

(This result requires that the factorisation through the image is an epimorphism
.
This holds in any category with equalizers.)
-/
def cokernelImageι {X Y : C} (f : X ⟶ Y) [HasImage f] [HasCokernel (image.ι f)] [HasCokernel f]
    [Epi (factorThruImage f)] : cokernel (image.ι f) ≅ cokernel f where
  hom :=
    cokernel.desc _ (cokernel.π f)
      (by
        have w := cokernel.condition f
        conv at w =>
          lhs
          congr
          rw [← image.fac f]
        rw [← HasZeroMorphisms.comp_zero (Limits.factorThruImage f), Category.assoc,
          cancel_epi] at w
        exact w)
  inv :=
    cokernel.desc _ (cokernel.π _)
      (by
        conv =>
          lhs
          congr
          rw [← image.fac f]
        rw [Category.assoc, cokernel.condition, HasZeroMorphisms.comp_zero])

section

variable (f : X ⟶ Y) [HasKernel f] [HasImage f] [HasKernel (factorThruImage f)]

/-- The kernel of the morphism `X ⟶ image f` is just the kernel of `f`. -/
/-
**CategoryTheory.Limits.kernelFactorThruImage** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：kernelFactorThruImage : kernel (factorThruImage f) ≅ kernel f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…

--- 原说明 ---
The kernel of the morphism `X ⟶ image f` is just the kernel of `f`.
-/
def kernelFactorThruImage : kernel (factorThruImage f) ≅ kernel f :=
  (kernelCompMono (factorThruImage f) (image.ι f)).symm ≪≫ (kernelIsoOfEq (by simp))

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.kernelFactorThruImage_hom_comp_** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kernelFactorThruImage_hom_comp_ι :
    (kernelFactorThruImage f).hom ≫ kernel.ι f = kernel.ι (factorThruImage f) := by
  simp [kernelFactorThruImage]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.kernelFactorThruImage_inv_comp_** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kernelFactorThruImage_inv_comp_ι :
    (kernelFactorThruImage f).inv ≫ kernel.ι (factorThruImage f) = kernel.ι f := by
  simp [kernelFactorThruImage]

end

end HasImage

section

/-- The cokernel of a zero morphism is an isomorphism -/
/-
**CategoryTheory.Limits.cokernel.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limi
ts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel of a zero morphism is an isomorphism
-/
theorem cokernel.π_of_zero {f : X ⟶ Y} [HasCokernel f] (eq : f = 0) :
    IsIso (cokernel.π f) := coequalizer.π_of_eq eq

end

section HasZeroObject

variable [HasZeroObject C]

open ZeroObject

/-- The kernel of the cokernel of an epimorphism is an isomorphism -/
/-
**CategoryTheory.Limits.kernel.of_cokernel_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.kernel`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   (f : X ⟶ Y) [CategoryTheory.Limit
s.HasZeroObject C] [inst_3 : CategoryTheory.Limits.HasCokernel f]   [inst_4 : Ca
tegoryTheory.Limits.HasKernel (CategoryTheory.Limits.cokernel.π f)] [CategoryThe
ory.Epi f],   CategoryTheory.IsIso (CategoryTheory.Limits.kernel.ι (CategoryTheo
ry.Limits.cokernel.π f))
参数：f : X ⟶ Y；CategoryTheory.Limits.cokernel.π f；CategoryTheory.Limits.kernel.ι (
CategoryTheory.Limits.cokernel.π f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.ι_of_eq`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g],   f = …
· 使用定理 `CategoryTheory.Limits.cokernel.π_of_epi`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X
 Y : C}   (f : X ⟶ Y) [Catego…

--- 原说明 ---
The kernel of the cokernel of an epimorphism is an isomorphism
-/
instance kernel.of_cokernel_of_epi [HasCokernel f] [HasKernel (cokernel.π f)] [Epi f] :
    IsIso (kernel.ι (cokernel.π f)) :=
  equalizer.ι_of_eq <| cokernel.π_of_epi f

/-- The cokernel of the kernel of a monomorphism is an isomorphism -/
/-
**CategoryTheory.Limits.cokernel.of_kernel_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.cokernel`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {X Y : C}   (f : X ⟶ Y) [CategoryTheory.Limit
s.HasZeroObject C] [inst_3 : CategoryTheory.Limits.HasKernel f]   [inst_4 : Cate
goryTheory.Limits.HasCokernel (CategoryTheory.Limits.kernel.ι f)] [CategoryTheor
y.Mono f],   CategoryTheory.IsIso (CategoryTheory.Limits.cokernel.π (CategoryThe
ory.Limits.kernel.ι f))
参数：f : X ⟶ Y；CategoryTheory.Limits.kernel.ι f；CategoryTheory.Limits.cokernel.π (
CategoryTheory.Limits.kernel.ι f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.π_of_eq`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g],   f …
· 使用定理 `CategoryTheory.Limits.kernel.ι_of_mono`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [Catego…

--- 原说明 ---
The cokernel of the kernel of a monomorphism is an isomorphism
-/
instance cokernel.of_kernel_of_mono [HasKernel f] [HasCokernel (kernel.ι f)] [Mono f] :
    IsIso (cokernel.π (kernel.ι f)) :=
  coequalizer.π_of_eq <| kernel.ι_of_mono f

/-- If `f ≫ g = 0` implies `g = 0` for all `g`, then `0 : Y ⟶ 0` is a cokernel of `f`. -/
/-
**CategoryTheory.Limits.zeroCokernelOfZeroCancel** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：zeroCokernelOfZeroCancel {X Y : C} (f : X ⟶ Y) (hf : forall (Z : C) (g : Y
 ⟶ Z) (_ : f ≫ g = 0), g = 0) : IsColimit (CokernelCofork.ofπ (0 : Y ⟶ 0) (show 
f ≫ 0 = 0 by simp))
参数：f : X ⟶ Y；hf : forall (Z : C) (g : Y ⟶ Z) (_ : f ≫ g = 0), g = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f ≫ g = 0` implies `g = 0` for all `g`, then `0 : Y ⟶ 0` is a cokernel of `f
`.
-/
def zeroCokernelOfZeroCancel {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (Z : C) (g : Y ⟶ Z) (_ : f ≫ g = 0), g = 0) :
    IsColimit (CokernelCofork.ofπ (0 : Y ⟶ 0) (show f ≫ 0 = 0 by simp)) :=
  Cofork.IsColimit.mk _ (fun _ => 0)
    (fun s => by rw [hf _ _ (CokernelCofork.condition s), comp_zero]) fun s m _ => by
      apply HasZeroObject.from_zero_ext

end HasZeroObject

section Transport

set_option backward.isDefEq.respectTransparency false in
/-- If `i` is an isomorphism such that `i.hom ≫ l = f`, then any cokernel of `f` is a cokernel of
`l`. -/
/-
**CategoryTheory.Limits.IsCokernel.ofIsoComp** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.IsCokernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           {Z : C} →             (l : Z ⟶ Y) →               (i : X ≅ Z) →  
               (h : CategoryTheory.CategoryStruct.comp i.hom l = f) →           
        {s : CategoryTheory.Limits.CokernelCofork f} →                     Categ
oryTheory.Limits.IsColimit s →                       CategoryTheory.Limits.IsCol
imit                         (CategoryTheory.Limits.CokernelCofork.ofπ (Category
Theory.Limits.Cofork.π s) ⋯)
参数：f : X ⟶ Y；l : Z ⟶ Y；i : X ≅ Z；h : CategoryTheory.CategoryStruct.comp i.hom l 
= f；CategoryTheory.Limits.CokernelCofork.ofπ (CategoryTheory.Limits.Cofork.π s) 
⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i` is an isomorphism such that `i.hom ≫ l = f`, then any cokernel of `f` is 
a cokernel of
`l`.
-/
def IsCokernel.ofIsoComp {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.hom ≫ l = f) {s : CokernelCofork f}
    (hs : IsColimit s) :
    IsColimit
      (CokernelCofork.ofπ (Cofork.π s) <| show l ≫ Cofork.π s = 0 by simp [i.eq_inv_comp.2 h]) :=
  Cofork.IsColimit.mk _ (fun s => hs.desc <| CokernelCofork.ofπ (Cofork.π s) <| by simp [← h])
    (fun s => by simp) fun s m h => by
      apply Cofork.IsColimit.hom_ext hs
      simpa using h

/-- If `i` is an isomorphism such that `i.hom ≫ l = f`, then the cokernel of `f` is a cokernel of
`l`. -/
/-
**CategoryTheory.Limits.cokernel.ofIsoComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.cokernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           [inst_2 : CategoryTheory.Limits.HasCokernel f] →             {Z :
 C} →               (l : Z ⟶ Y) →                 (i : X ≅ Z) →                 
  (h : CategoryTheory.CategoryStruct.comp i.hom l = f) →                     Cat
egoryTheory.Limits.IsColimit                       (CategoryTheory.Limits.Cokern
elCofork.ofπ (CategoryTheory.Limits.cokernel.π f) ⋯)
参数：f : X ⟶ Y；l : Z ⟶ Y；i : X ≅ Z；h : CategoryTheory.CategoryStruct.comp i.hom l 
= f；CategoryTheory.Limits.CokernelCofork.ofπ (CategoryTheory.Limits.cokernel.π f
) ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i` is an isomorphism such that `i.hom ≫ l = f`, then the cokernel of `f` is 
a cokernel of
`l`.
-/
def cokernel.ofIsoComp [HasCokernel f] {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.hom ≫ l = f) :
    IsColimit
      (CokernelCofork.ofπ (cokernel.π f) <|
        show l ≫ cokernel.π f = 0 by simp [i.eq_inv_comp.2 h]) :=
  IsCokernel.ofIsoComp f l i h <| colimit.isColimit _

set_option backward.defeqAttrib.useBackward true in
/-- If `s` is any colimit cokernel cocone over `f` and `i` is an isomorphism such that
`s.π ≫ i.hom = l`, then `l` is a cokernel of `f`. -/
/-
**CategoryTheory.Limits.IsCokernel.cokernelIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.IsCokernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           {Z : C} →             (l : Y ⟶ Z) →               {s : CategoryTh
eory.Limits.CokernelCofork f} →                 CategoryTheory.Limits.IsColimit 
s →                   (i : s.pt ≅ Z) →                     (h : CategoryTheory.C
ategoryStruct.comp (CategoryTheory.Limits.Cofork.π s) i.hom = l) →              
         CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.CokernelCofork.o
fπ l ⋯)
参数：f : X ⟶ Y；l : Y ⟶ Z；i : s.pt ≅ Z；h : CategoryTheory.CategoryStruct.comp (Cate
goryTheory.Limits.Cofork.π s) i.hom = l；CategoryTheory.Limits.CokernelCofork.ofπ
 l ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is any colimit cokernel cocone over `f` and `i` is an isomorphism such th
at
`s.π ≫ i.hom = l`, then `l` is a cokernel of `f`.
-/
def IsCokernel.cokernelIso {Z : C} (l : Y ⟶ Z) {s : CokernelCofork f} (hs : IsColimit s)
    (i : s.pt ≅ Z) (h : Cofork.π s ≫ i.hom = l) :
    IsColimit (CokernelCofork.ofπ l <| show f ≫ l = 0 by simp [← h]) :=
  IsColimit.ofIsoColimit hs <|
    Cocone.ext i fun j => by
      cases j
      · dsimp; rw [← h]; simp
      · exact h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Transport an `IsCokernel` across isomorphisms. -/
/-
**CategoryTheory.Limits.IsCokernel.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.IsCokernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           {X' Y' : C} →             {f' : X' ⟶ Y'} →               {s : Cat
egoryTheory.Limits.CokernelCofork f} →                 CategoryTheory.Limits.IsC
olimit s →                   (s' : CategoryTheory.Limits.CokernelCofork f') →   
                  (eX : X ≅ X') →                       (eY : Y ≅ Y') →         
                (e : s.pt ≅ s'.pt) →                           CategoryTheory.Ca
tegoryStruct.comp eX.hom f' = CategoryTheory.CategoryStruct.comp f eY.hom →     
                        CategoryTheory.CategoryStruct.comp eY.hom (CategoryTheor
y.Limits.Cofork.π s') =                                 CategoryTheory.CategoryS
truct.comp (CategoryTheory.Limits.Cofork.π s) e.hom →                           
    CategoryTheory.Limits.IsColimit s'
参数：f : X ⟶ Y；s' : CategoryTheory.Limits.CokernelCofork f'；eX : X ≅ X'；eY : Y ≅ Y
'；e : s.pt ≅ s'.pt；CategoryTheory.Limits.Cofork.π s'；CategoryTheory.Limits.Cofor
k.π s。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transport an `IsCokernel` across isomorphisms.
-/
def IsCokernel.ofIso {X' Y' : C} {f' : X' ⟶ Y'} {s : CokernelCofork f} (hs : IsColimit s)
    (s' : CokernelCofork f') (eX : X ≅ X') (eY : Y ≅ Y') (e : s.pt ≅ s'.pt)
    (H : eX.hom ≫ f' = f ≫ eY.hom) (H' : eY.hom ≫ s'.π = s.π ≫ e.hom) :
    IsColimit s' :=
  let α : parallelPair f 0 ≅ parallelPair f' 0 := parallelPairIsoMk eX eY H.symm (by simp)
  IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv α.symm s).symm hs) <|
    Cocone.ext e (by rintro (_ | _) <;> simp [α, ← H'])

/-- If `i` is an isomorphism such that `cokernel.π f ≫ i.hom = l`, then `l` is a cokernel of `f`. -/
/-
**CategoryTheory.Limits.cokernel.cokernelIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.cokernel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f : X ⟶ 
Y) →           [inst_2 : CategoryTheory.Limits.HasCokernel f] →             {Z :
 C} →               (l : Y ⟶ Z) →                 (i : CategoryTheory.Limits.cok
ernel f ≅ Z) →                   (h : CategoryTheory.CategoryStruct.comp (Catego
ryTheory.Limits.cokernel.π f) i.hom = l) →                     CategoryTheory.Li
mits.IsColimit (CategoryTheory.Limits.CokernelCofork.ofπ l ⋯)
参数：f : X ⟶ Y；l : Y ⟶ Z；i : CategoryTheory.Limits.cokernel f ≅ Z；h : CategoryTheo
ry.CategoryStruct.comp (CategoryTheory.Limits.cokernel.π f) i.hom = l；CategoryTh
eory.Limits.CokernelCofork.ofπ l ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i` is an isomorphism such that `cokernel.π f ≫ i.hom = l`, then `l` is a cok
ernel of `f`.
-/
def cokernel.cokernelIso [HasCokernel f] {Z : C} (l : Y ⟶ Z) (i : cokernel f ≅ Z)
    (h : cokernel.π f ≫ i.hom = l) :
    IsColimit (@CokernelCofork.ofπ _ _ _ _ _ f _ l <| by simp [← h]) :=
  IsCokernel.cokernelIso f l (colimit.isColimit _) i h

end Transport

section Comparison

variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
variable (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

/-- The comparison morphism for the kernel of `f`.
This is an isomorphism iff `G` preserves the kernel of `f`; see
`Mathlib/CategoryTheory/Limits/Preserves/Shapes/Kernels.lean`
-/
/-
**CategoryTheory.Limits.kernelComparison** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：kernelComparison [HasKernel f] [HasKernel (G.map f)] : G.obj (kernel f) ⟶ 
kernel (G.map f)
参数：G.map f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comparison morphism for the kernel of `f`.
This is an isomorphism iff `G` preserves the kernel of `f`; see
`Mathlib/CategoryTheory/Limits/Preserves/Shapes/Kernels.lean`
-/
def kernelComparison [HasKernel f] [HasKernel (G.map f)] : G.obj (kernel f) ⟶ kernel (G.map f) :=
  kernel.lift _ (G.map (kernel.ι f))
    (by simp only [← G.map_comp, kernel.condition, Functor.map_zero])

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.kernelComparison_comp_** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kernelComparison_comp_ι [HasKernel f] [HasKernel (G.map f)] :
    kernelComparison f G ≫ kernel.ι (G.map f) = G.map (kernel.ι f) :=
  kernel.lift_ι _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.map_lift_kernelComparison** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：map_lift_kernelComparison [HasKernel f] [HasKernel (G.map f)] {Z : C} {h :
 Z ⟶ X} (w : h ≫ f = 0) : G.map (kernel.lift _ h w) ≫ kernelComparison f G = ker
nel.lift _ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero])
参数：G.map f；w : h ≫ f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernelComparison_comp_ι`：kernelComparison_comp_ι [
HasKernel f] [HasKernel (G.map f)] : kernelComparison f G ≫ kernel.ι (G.map f) =
 G.map (kernel.ι f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_lift_kernelComparison [HasKernel f] [HasKernel (G.map f)] {Z : C} {h : Z ⟶ X}
    (w : h ≫ f = 0) :
    G.map (kernel.lift _ h w) ≫ kernelComparison f G =
      kernel.lift _ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) := by
  ext; simp [← G.map_comp]

@[reassoc]
/-
**CategoryTheory.Limits.kernelComparison_comp_kernel_map** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：kernelComparison_comp_kernel_map {X' Y' : C} [HasKernel f] [HasKernel (G.m
ap f)] (g : X' ⟶ Y') [HasKernel g] [HasKernel (G.map g)] (p : X ⟶ X') (q : Y ⟶ Y
') (hpq : f ≫ q = p ≫ g) : kernelComparison f G ≫ kernel.map (G.map f) (G.map g)
 (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) = G.map (kernel.map
 f g p q hpq) ≫ kernelComparison g G
参数：G.map f；g : X' ⟶ Y'；G.map g；p : X ⟶ X'；q : Y ⟶ Y'；hpq : f ≫ q = p ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.kernel.lift_map`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {X
 Y Z X' Y' Z' : C} (f : X ⟶…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
-/
theorem kernelComparison_comp_kernel_map {X' Y' : C} [HasKernel f] [HasKernel (G.map f)]
    (g : X' ⟶ Y') [HasKernel g] [HasKernel (G.map g)] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    kernelComparison f G ≫
        kernel.map (G.map f) (G.map g) (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) =
      G.map (kernel.map f g p q hpq) ≫ kernelComparison g G :=
  kernel.lift_map _ _ (by rw [← G.map_comp, kernel.condition, G.map_zero]) _ _
    (by rw [← G.map_comp, kernel.condition, G.map_zero]) _ _ _
    (by simp only [← G.map_comp]; exact G.congr_map (kernel.lift_ι _ _ _).symm) _

/-- The comparison morphism for the cokernel of `f`. -/
/-
**CategoryTheory.Limits.cokernelComparison** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：cokernelComparison [HasCokernel f] [HasCokernel (G.map f)] : cokernel (G.m
ap f) ⟶ G.obj (cokernel f)
参数：G.map f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comparison morphism for the cokernel of `f`.
-/
def cokernelComparison [HasCokernel f] [HasCokernel (G.map f)] :
    cokernel (G.map f) ⟶ G.obj (cokernel f) :=
  cokernel.desc _ (G.map (coequalizer.π _ _))
    (by simp only [← G.map_comp, cokernel.condition, Functor.map_zero])

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_comp_cokernelComparison [HasCokernel f] [HasCokernel (G.map f)] :
    cokernel.π (G.map f) ≫ cokernelComparison f G = G.map (cokernel.π _) :=
  cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.cokernelComparison_map_desc** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：cokernelComparison_map_desc [HasCokernel f] [HasCokernel (G.map f)] {Z : C
} {h : Y ⟶ Z} (w : f ≫ h = 0) : cokernelComparison f G ≫ G.map (cokernel.desc _ 
h w) = cokernel.desc _ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zer
o])
参数：G.map f；w : f ≫ h = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.π_comp_cokernelComparison_assoc`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {X Y : C}   (f : X ⟶ Y) {D : Ty…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cokernelComparison_map_desc [HasCokernel f] [HasCokernel (G.map f)] {Z : C} {h : Y ⟶ Z}
    (w : f ≫ h = 0) :
    cokernelComparison f G ≫ G.map (cokernel.desc _ h w) =
      cokernel.desc _ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) := by
  ext; simp [← G.map_comp]

@[reassoc]
/-
**CategoryTheory.Limits.cokernel_map_comp_cokernelComparison** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：cokernel_map_comp_cokernelComparison {X' Y' : C} [HasCokernel f] [HasCoker
nel (G.map f)] (g : X' ⟶ Y') [HasCokernel g] [HasCokernel (G.map g)] (p : X ⟶ X'
) (q : Y ⟶ Y') (hpq : f ≫ q = p ≫ g) : cokernel.map (G.map f) (G.map g) (G.map p
) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) ≫ cokernelComparison _ G = c
okernelComparison _ G ≫ G.map (cokernel.map f g p q hpq)
参数：G.map f；g : X' ⟶ Y'；G.map g；p : X ⟶ X'；q : Y ⟶ Y'；hpq : f ≫ q = p ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.cokernel.map_desc`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   
{X Y Z X' Y' Z' : C} (f : X ⟶…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
-/
theorem cokernel_map_comp_cokernelComparison {X' Y' : C} [HasCokernel f] [HasCokernel (G.map f)]
    (g : X' ⟶ Y') [HasCokernel g] [HasCokernel (G.map g)] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    cokernel.map (G.map f) (G.map g) (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) ≫
        cokernelComparison _ G =
      cokernelComparison _ G ≫ G.map (cokernel.map f g p q hpq) :=
  cokernel.map_desc _ _ (by rw [← G.map_comp, cokernel.condition, G.map_zero]) _ _
    (by rw [← G.map_comp, cokernel.condition, G.map_zero]) _ _ _ _
    (by simp only [← G.map_comp]; exact G.congr_map (cokernel.π_desc _ _ _))

end Comparison

end CategoryTheory.Limits

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]
variable [HasZeroMorphisms C]

/-- `HasKernels` represents the existence of kernels for every morphism. -/
/-
**CategoryTheory.Limits.HasKernels** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：HasKernels : Prop where has_limit : forall {X Y : C} (f : X ⟶ Y), HasKerne
l f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasKernels` represents the existence of kernels for every morphism.
-/
class HasKernels : Prop where
  has_limit : ∀ {X Y : C} (f : X ⟶ Y), HasKernel f := by infer_instance

/-- `HasCokernels` represents the existence of cokernels for every morphism. -/
/-
**CategoryTheory.Limits.HasCokernels** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：HasCokernels : Prop where has_colimit : forall {X Y : C} (f : X ⟶ Y), HasC
okernel f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasCokernels` represents the existence of cokernels for every morphism.
-/
class HasCokernels : Prop where
  has_colimit : ∀ {X Y : C} (f : X ⟶ Y), HasCokernel f := by infer_instance

attribute [instance 100] HasKernels.has_limit HasCokernels.has_colimit
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasKernels_of_hasEqualizers [HasEqualizers C] : HasKernels C where
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasCokernels_of_hasCoequalizers [HasCoequalizers C] :
    HasCokernels C where

section HasKernels
variable [HasKernels C]

/-- The kernel of an arrow is natural. -/
@[simps]
/-
**CategoryTheory.Limits.ker** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：ker : Arrow C ⥤ C where obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of an arrow is natural.
-/
noncomputable def ker : Arrow C ⥤ C where
  obj f := kernel f.hom
  map {f g} u := kernel.lift _ (kernel.ι _ ≫ u.left) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The kernel inclusion is natural. -/
/-
**CategoryTheory.Limits.ker.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel inclusion is natural.
-/
@[simps] def ker.ι : ker (C := C) ⟶ Arrow.leftFunc where app f := kernel.ι _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.ker.condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.ker`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limits.HasKernels 
C],   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.ker.ι C) Categor
yTheory.Arrow.leftToRight = 0
参数：C : Type u；CategoryTheory.Limits.ker.ι C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…

--- 原说明 ---
The kernel inclusion is natural.
-/
@[reassoc (attr := simp)] lemma ker.condition : ι C ≫ Arrow.leftToRight = 0 := by cat_disch

end HasKernels

section HasCokernels
variable [HasCokernels C]

/-- The cokernel of an arrow is natural. -/
@[simps]
/-
**CategoryTheory.Limits.coker** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：coker : Arrow C ⥤ C where obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel of an arrow is natural.
-/
noncomputable def coker : Arrow C ⥤ C where
  obj f := cokernel f.hom
  map {f g} u := cokernel.desc _ (u.right ≫ cokernel.π _) (by simp [← Arrow.w_assoc u])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The cokernel projection is natural. -/
/-
**CategoryTheory.Limits.coker.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel projection is natural.
-/
@[simps] def coker.π : Arrow.rightFunc ⟶ coker (C := C) where app f := cokernel.π _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.coker.condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.coker`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limits.HasCokernel
s C],   CategoryTheory.CategoryStruct.comp CategoryTheory.Arrow.leftToRight (Cat
egoryTheory.Limits.coker.π C) = 0
参数：C : Type u；CategoryTheory.Limits.coker.π C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…

--- 原说明 ---
The cokernel projection is natural.
-/
@[reassoc (attr := simp)] lemma coker.condition : Arrow.leftToRight ≫ π C = 0 := by cat_disch

end HasCokernels

end CategoryTheory.Limits

