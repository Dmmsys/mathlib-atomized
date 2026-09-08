/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Normal mono categories with finite products and kernels have all equalizers.

This, and the dual result, are used in the development of abelian categories.
-/

public section


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace CategoryTheory.NormalMonoCategory

variable [HasFiniteProducts C] [HasKernels C] [IsNormalMonoCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of two monomorphisms exists. -/
/-
**CategoryTheory.NormalMonoCategory.pullback_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.NormalMonoCategory`。
形式化陈述：pullback_of_mono {X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z) [Mono a] [Mono b] : H
asLimit (cospan a b)
参数：a : X ⟶ Z；b : Y ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.lift_fst`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
· 使用定理 `CategoryTheory.Limits.kernel.condition_assoc`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C] {X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.prod.lift_snd`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition_assoc`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   (t : 
CategoryTheory.Limits.PullbackCone f g) …
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.KernelFork.ι_ofι`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y P : C}   (f : X ⟶ Y) (ι : …
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The pullback of two monomorphisms exists.
-/
lemma pullback_of_mono {X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z) [Mono a] [Mono b] :
    HasLimit (cospan a b) :=
  let ⟨P, f, haf, i⟩ := normalMonoOfMono a
  let ⟨Q, g, hbg, i'⟩ := normalMonoOfMono b
  let ⟨a', ha'⟩ :=
    KernelFork.IsLimit.lift' i (kernel.ι (prod.lift f g)) <|
      calc kernel.ι (prod.lift f g) ≫ f
        _ = kernel.ι (prod.lift f g) ≫ prod.lift f g ≫ Limits.prod.fst := by rw [prod.lift_fst]
        _ = (0 : kernel (prod.lift f g) ⟶ P ⨯ Q) ≫ Limits.prod.fst := by rw [kernel.condition_assoc]
        _ = 0 := zero_comp
  let ⟨b', hb'⟩ :=
    KernelFork.IsLimit.lift' i' (kernel.ι (prod.lift f g)) <|
      calc kernel.ι (prod.lift f g) ≫ g
        _ = kernel.ι (prod.lift f g) ≫ prod.lift f g ≫ Limits.prod.snd := by rw [prod.lift_snd]
        _ = (0 : kernel (prod.lift f g) ⟶ P ⨯ Q) ≫ Limits.prod.snd := by rw [kernel.condition_assoc]
        _ = 0 := zero_comp
  HasLimit.mk
    { cone :=
        PullbackCone.mk a' b' <| by rw [dsimp% ha', dsimp% hb']
      isLimit :=
        PullbackCone.IsLimit.mk _
          (fun s =>
            kernel.lift (prod.lift f g) (PullbackCone.snd s ≫ b) <|
              Limits.prod.hom_ext
                (calc
                  ((PullbackCone.snd s ≫ b) ≫ prod.lift f g) ≫ Limits.prod.fst =
                      PullbackCone.snd s ≫ b ≫ f := by simp only [prod.lift_fst, Category.assoc]
                  _ = PullbackCone.fst s ≫ a ≫ f := by rw [PullbackCone.condition_assoc]
                  _ = PullbackCone.fst s ≫ 0 := by rw [haf]
                  _ = 0 ≫ Limits.prod.fst := by rw [comp_zero, zero_comp])
                (calc
                  ((PullbackCone.snd s ≫ b) ≫ prod.lift f g) ≫ Limits.prod.snd =
                      PullbackCone.snd s ≫ b ≫ g := by
                    simp only [prod.lift_snd, Category.assoc]
                  _ = PullbackCone.snd s ≫ 0 := by rw [hbg]
                  _ = 0 ≫ Limits.prod.snd := by rw [comp_zero, zero_comp]))
          (fun s =>
            (cancel_mono a).1 <| by
              rw [KernelFork.ι_ofι] at ha'
              simp [ha', PullbackCone.condition s])
          (fun s =>
            (cancel_mono b).1 <| by
              rw [KernelFork.ι_ofι] at hb'
              simp [hb'])
          fun s m h₁ _ =>
          (cancel_mono (kernel.ι (prod.lift f g))).1 <|
            calc
              m ≫ kernel.ι (prod.lift f g) = m ≫ a' ≫ a := by
                congr
                exact ha'.symm
              _ = PullbackCone.fst s ≫ a := by rw [← Category.assoc, h₁]
              _ = PullbackCone.snd s ≫ b := PullbackCone.condition s
              _ =
                  kernel.lift (prod.lift f g) (PullbackCone.snd s ≫ b) _ ≫
                    kernel.ι (prod.lift f g) := by rw [kernel.lift_ι]
               }

section

attribute [local instance] pullback_of_mono

/-- The pullback of `(𝟙 X, f)` and `(𝟙 X, g)` -/
/-
**CategoryTheory.NormalMonoCategory.P** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.NormalMonoCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of `(𝟙 X, f)` and `(𝟙 X, g)`
-/
private abbrev P {X Y : C} (f g : X ⟶ Y) [Mono (prod.lift (𝟙 X) f)] [Mono (prod.lift (𝟙 X) g)] :
    C :=
  pullback (prod.lift (𝟙 X) f) (prod.lift (𝟙 X) g)

set_option backward.isDefEq.respectTransparency false in
/-- The equalizer of `f` and `g` exists. -/
/-
**CategoryTheory.NormalMonoCategory.hasLimit_parallelPair** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.NormalMonoCategory`。
形式化陈述：hasLimit_parallelPair {X Y : C} (f g : X ⟶ Y) : HasLimit (parallelPair f g
)
参数：f g : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.prod.mono_lift_of_mono_left`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limit
s.HasBinaryProduct X Y] (f : W ⟶ X) (g …
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.lift_fst`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.prod.lift_snd`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.Fork.condition`：∀ {C : Type u} {X Y : C} [inst : C
ategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Fork f
 g),   CategoryTheory.Cate…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…

--- 原说明 ---
The equalizer of `f` and `g` exists.
-/
lemma hasLimit_parallelPair {X Y : C} (f g : X ⟶ Y) : HasLimit (parallelPair f g) :=
  have huv : (pullback.fst _ _ : P f g ⟶ X) = pullback.snd _ _ :=
    calc
      (pullback.fst _ _ : P f g ⟶ X) = pullback.fst _ _ ≫ 𝟙 _ := Eq.symm <| Category.comp_id _
      _ = pullback.fst _ _ ≫ prod.lift (𝟙 X) f ≫ Limits.prod.fst := by rw [prod.lift_fst]
      _ = pullback.snd _ _ ≫ prod.lift (𝟙 X) g ≫ Limits.prod.fst := by rw [pullback.condition_assoc]
      _ = pullback.snd _ _ := by rw [prod.lift_fst, Category.comp_id]
  have hvu : (pullback.fst _ _ : P f g ⟶ X) ≫ f = pullback.snd _ _ ≫ g :=
    calc
      (pullback.fst _ _ : P f g ⟶ X) ≫ f =
        pullback.fst _ _ ≫ prod.lift (𝟙 X) f ≫ Limits.prod.snd := by rw [prod.lift_snd]
      _ = pullback.snd _ _ ≫ prod.lift (𝟙 X) g ≫ Limits.prod.snd := by rw [pullback.condition_assoc]
      _ = pullback.snd _ _ ≫ g := by rw [prod.lift_snd]
  have huu : (pullback.fst _ _ : P f g ⟶ X) ≫ f = pullback.fst _ _ ≫ g := by rw [hvu, ← huv]
  HasLimit.mk
    { cone := Fork.ofι (pullback.fst _ _) huu
      isLimit :=
        Fork.IsLimit.mk _
          (fun s =>
            pullback.lift (Fork.ι s) (Fork.ι s) <|
              Limits.prod.hom_ext (by simp only [prod.lift_fst, Category.assoc])
                (by simp only [prod.comp_lift, Fork.condition s]))
          (fun s => by simp) fun s m h =>
          pullback.hom_ext (by simpa only [pullback.lift_fst] using! h)
            (by simpa only [huv.symm, pullback.lift_fst] using! h) }

end

section

attribute [local instance] hasLimit_parallelPair

/-- A `NormalMonoCategory` category with finite products and kernels has all equalizers. -/
/-
**CategoryTheory.NormalMonoCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.N
ormalMonoCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `NormalMonoCategory` category with finite products and kernels has all equaliz
ers.
-/
instance (priority := 100) hasEqualizers : HasEqualizers C :=
  hasEqualizers_of_hasLimit_parallelPair _

end

set_option backward.isDefEq.respectTransparency false in
/-- If a zero morphism is a cokernel of `f`, then `f` is an epimorphism. -/
/-
**CategoryTheory.NormalMonoCategory.epi_of_zero_cokernel** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.NormalMonoCategory`。
形式化陈述：epi_of_zero_cokernel {X Y : C} (f : X ⟶ Y) (Z : C) (l : IsColimit (Cokerne
lCofork.ofπ (0 : Y ⟶ Z) (show f ≫ 0 = 0 by simp))) : Epi f
参数：f : X ⟶ Y；Z : C；l : IsColimit (CokernelCofork.ofπ (0 : Y ⟶ Z) (show f ≫ 0 = 0
 by simp))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.NormalMonoCategory.hasEqualizers`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   [CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.isIso_limit_cone_parallelPair_of_eq`：isIso_limit_c
one_parallelPair_of_eq (h₀ : f = g) {c : Fork f g} (h : IsLimit c) : IsIso c.ι
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.Cofork.π_ofπ`：∀ {C : Type u} {X Y : C} [inst : Cat
egoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {P : C} (π : Y ⟶ P)   (w : Category
Theory.CategoryStruct.co…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…

--- 原说明 ---
If a zero morphism is a cokernel of `f`, then `f` is an epimorphism.
-/
theorem epi_of_zero_cokernel {X Y : C} (f : X ⟶ Y) (Z : C)
    (l : IsColimit (CokernelCofork.ofπ (0 : Y ⟶ Z) (show f ≫ 0 = 0 by simp))) : Epi f :=
  ⟨fun u v huv => by
    obtain ⟨W, w, hw, hl⟩ := normalMonoOfMono (equalizer.ι u v)
    obtain ⟨m, hm⟩ := equalizer.lift' f huv
    have hwf : f ≫ w = 0 := by rw [← hm, Category.assoc, hw, comp_zero]
    obtain ⟨n, hn⟩ := CokernelCofork.IsColimit.desc' l _ hwf
    rw [Cofork.π_ofπ, zero_comp] at hn
    have : IsIso (equalizer.ι u v) := by apply isIso_limit_cone_parallelPair_of_eq hn.symm hl
    apply (cancel_epi (equalizer.ι u v)).1
    exact equalizer.condition _ _⟩

section

variable [HasZeroObject C]

open ZeroObject

/-- If `f ≫ g = 0` implies `g = 0` for all `g`, then `g` is a monomorphism. -/
/-
**CategoryTheory.NormalMonoCategory.epi_of_zero_cancel** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.NormalMonoCategory`。
形式化陈述：epi_of_zero_cancel {X Y : C} (f : X ⟶ Y) (hf : forall (Z : C) (g : Y ⟶ Z) 
(_ : f ≫ g = 0), g = 0) : Epi f
参数：f : X ⟶ Y；hf : forall (Z : C) (g : Y ⟶ Z) (_ : f ≫ g = 0), g = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NormalMonoCategory.epi_of_zero_cokernel`：epi_of_zero_coke
rnel {X Y : C} (f : X ⟶ Y) (Z : C) (l : IsColimit (CokernelCofork.ofπ (0 : Y ⟶ Z
) (show f ≫ 0 = 0 by simp))) : Epi f

--- 原说明 ---
If `f ≫ g = 0` implies `g = 0` for all `g`, then `g` is a monomorphism.
-/
theorem epi_of_zero_cancel {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (Z : C) (g : Y ⟶ Z) (_ : f ≫ g = 0), g = 0) : Epi f :=
  epi_of_zero_cokernel f 0 <| zeroCokernelOfZeroCancel f hf

variable {D : Type*} [Category* D] [HasZeroMorphisms D] [HasZeroObject D]
/-
**CategoryTheory.NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.NormalMonoCategory`。
形式化陈述：preservesEpimorphisms_of_preservesCokernels (F : D ⥤ C) [F.PreservesZeroMo
rphisms] [forall {X Y : D} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] :
 F.PreservesEpimorphisms where preserves f
参数：F : D ⥤ C；f : X ⟶ Y；parallelPair f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NormalMonoCategory.epi_of_zero_cokernel`：epi_of_zero_coke
rnel {X Y : C} (f : X ⟶ Y) (Z : C) (l : IsColimit (CokernelCofork.ofπ (0 : Y ⟶ Z
) (show f ≫ 0 = 0 by simp))) : Epi f
-/
lemma preservesEpimorphisms_of_preservesCokernels (F : D ⥤ C) [F.PreservesZeroMorphisms]
    [∀ {X Y : D} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] :
    F.PreservesEpimorphisms where
  preserves f :=
    epi_of_zero_cokernel _ _ <| IsColimit.equivIsoColimit (mapZeroCokernelCofork F f) <|
    (cokernel.zeroCokernelCofork f).mapIsColimit (cokernel.isColimitCoconeZeroCocone f) F

end

end CategoryTheory.NormalMonoCategory

namespace CategoryTheory.NormalEpiCategory

variable [HasFiniteCoproducts C] [HasCokernels C] [IsNormalEpiCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The pushout of two epimorphisms exists. -/
/-
**CategoryTheory.NormalEpiCategory.pushout_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.NormalEpiCategory`。
形式化陈述：pushout_of_epi {X Y Z : C} (a : X ⟶ Y) (b : X ⟶ Z) [Epi a] [Epi b] : HasCo
limit (span a b)
参数：a : X ⟶ Y；b : X ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.inl_desc_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasB
inaryCoproduct X Y] (f : X ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.HasZeroMorphisms.comp_zero`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   (f : X ⟶ Y) (Z : C), …
· 使用定理 `CategoryTheory.Limits.coprod.inr_desc_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasB
inaryCoproduct X Y] (f : X ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `CategoryTheory.Limits.PushoutCocone.condition`：condition (t : PushoutCoc
one f g) : f ≫ inl t = g ≫ inr t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.CokernelCofork.π_ofπ`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
 {X Y P : C}   (f : X ⟶ Y) (π : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…

--- 原说明 ---
The pushout of two epimorphisms exists.
-/
lemma pushout_of_epi {X Y Z : C} (a : X ⟶ Y) (b : X ⟶ Z) [Epi a] [Epi b] :
    HasColimit (span a b) :=
  let ⟨P, f, hfa, i⟩ := normalEpiOfEpi a
  let ⟨Q, g, hgb, i'⟩ := normalEpiOfEpi b
  let ⟨a', ha'⟩ :=
    CokernelCofork.IsColimit.desc' i (cokernel.π (coprod.desc f g)) <|
      calc
        f ≫ cokernel.π (coprod.desc f g) =
            coprod.inl ≫ coprod.desc f g ≫ cokernel.π (coprod.desc f g) := by
          rw [coprod.inl_desc_assoc]
        _ = coprod.inl ≫ (0 : P ⨿ Q ⟶ cokernel (coprod.desc f g)) := by rw [cokernel.condition]
        _ = 0 := HasZeroMorphisms.comp_zero _ _
  let ⟨b', hb'⟩ :=
    CokernelCofork.IsColimit.desc' i' (cokernel.π (coprod.desc f g)) <|
      calc
        g ≫ cokernel.π (coprod.desc f g) =
            coprod.inr ≫ coprod.desc f g ≫ cokernel.π (coprod.desc f g) := by
          rw [coprod.inr_desc_assoc]
        _ = coprod.inr ≫ (0 : P ⨿ Q ⟶ cokernel (coprod.desc f g)) := by rw [cokernel.condition]
        _ = 0 := HasZeroMorphisms.comp_zero _ _
  HasColimit.mk
    { cocone :=
        PushoutCocone.mk a' b' <| by
          simp only [Cofork.π_ofπ] at ha' hb'
          rw [ha', hb']
      isColimit :=
        PushoutCocone.IsColimit.mk _
          (fun s =>
            cokernel.desc (coprod.desc f g) (b ≫ PushoutCocone.inr s) <|
              coprod.hom_ext
                (calc
                  coprod.inl ≫ coprod.desc f g ≫ b ≫ PushoutCocone.inr s =
                      f ≫ b ≫ PushoutCocone.inr s := by rw [coprod.inl_desc_assoc]
                  _ = f ≫ a ≫ PushoutCocone.inl s := by rw [PushoutCocone.condition]
                  _ = 0 ≫ PushoutCocone.inl s := by rw [← Category.assoc, eq_whisker hfa]
                  _ = coprod.inl ≫ 0 := by rw [comp_zero, zero_comp])
                (calc
                  coprod.inr ≫ coprod.desc f g ≫ b ≫ PushoutCocone.inr s =
                      g ≫ b ≫ PushoutCocone.inr s := by rw [coprod.inr_desc_assoc]
                  _ = 0 ≫ PushoutCocone.inr s := by rw [← Category.assoc, eq_whisker hgb]
                  _ = coprod.inr ≫ 0 := by rw [comp_zero, zero_comp]))
          (fun s =>
            (cancel_epi a).1 <| by
              rw [CokernelCofork.π_ofπ] at ha'
              have reassoced {W : C} (h : cokernel (coprod.desc f g) ⟶ W) : a ≫ a' ≫ h
                = cokernel.π (coprod.desc f g) ≫ h := by rw [← Category.assoc, eq_whisker ha']
              simp [reassoced, PushoutCocone.condition s])
          (fun s =>
            (cancel_epi b).1 <| by
              rw [CokernelCofork.π_ofπ] at hb'
              have reassoced' {W : C} (h : cokernel (coprod.desc f g) ⟶ W) : b ≫ b' ≫ h
                = cokernel.π (coprod.desc f g) ≫ h := by rw [← Category.assoc, eq_whisker hb']
              simp [reassoced'])
          fun s m h₁ _ =>
          (cancel_epi (cokernel.π (coprod.desc f g))).1 <|
            calc
              cokernel.π (coprod.desc f g) ≫ m = (a ≫ a') ≫ m := by
                congr
                exact ha'.symm
              _ = a ≫ PushoutCocone.inl s := by rw [Category.assoc, h₁]
              _ = b ≫ PushoutCocone.inr s := PushoutCocone.condition s
              _ =
                  cokernel.π (coprod.desc f g) ≫
                    cokernel.desc (coprod.desc f g) (b ≫ PushoutCocone.inr s) _ := by
                rw [cokernel.π_desc]
               }

section

attribute [local instance] pushout_of_epi

/-- The pushout of `(𝟙 Y, f)` and `(𝟙 Y, g)`. -/
/-
**CategoryTheory.NormalEpiCategory.Q** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.NormalEpiCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushout of `(𝟙 Y, f)` and `(𝟙 Y, g)`.
-/
private abbrev Q {X Y : C} (f g : X ⟶ Y) [Epi (coprod.desc (𝟙 Y) f)] [Epi (coprod.desc (𝟙 Y) g)] :
    C :=
  pushout (coprod.desc (𝟙 Y) f) (coprod.desc (𝟙 Y) g)

set_option backward.isDefEq.respectTransparency false in
/-- The coequalizer of `f` and `g` exists. -/
/-
**CategoryTheory.NormalEpiCategory.hasColimit_parallelPair** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.NormalEpiCategory`。
形式化陈述：hasColimit_parallelPair {X Y : C} (f g : X ⟶ Y) : HasColimit (parallelPair
 f g)
参数：f g : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coprod.epi_desc_of_epi_left`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limit
s.HasBinaryCoproduct X Y] (f : X ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.inl_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryC
oproduct X Y] (f : X ⟶ W) (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.coprod.inr_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryC
oproduct X Y] (f : X ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `CategoryTheory.Limits.coprod.inl_desc_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasB
inaryCoproduct X Y] (f : X ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.Limits.Cofork.condition`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Cofo
rk f g),   CategoryTheory.Ca…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pushout.inl_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPushout …
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …

--- 原说明 ---
The coequalizer of `f` and `g` exists.
-/
lemma hasColimit_parallelPair {X Y : C} (f g : X ⟶ Y) : HasColimit (parallelPair f g) :=
  have huv : (pushout.inl _ _ : Y ⟶ Q f g) = pushout.inr _ _ :=
    calc
      (pushout.inl _ _ : Y ⟶ Q f g) = 𝟙 _ ≫ pushout.inl _ _ := Eq.symm <| Category.id_comp _
      _ = (coprod.inl ≫ coprod.desc (𝟙 Y) f) ≫ pushout.inl _ _ := by rw [coprod.inl_desc]
      _ = (coprod.inl ≫ coprod.desc (𝟙 Y) g) ≫ pushout.inr _ _ := by
        simp only [Category.assoc, pushout.condition]
      _ = pushout.inr _ _ := by rw [coprod.inl_desc, Category.id_comp]
  have hvu : f ≫ (pushout.inl _ _ : Y ⟶ Q f g) = g ≫ pushout.inr _ _ :=
    calc
      f ≫ (pushout.inl _ _ : Y ⟶ Q f g) = (coprod.inr ≫ coprod.desc (𝟙 Y) f) ≫ pushout.inl _ _ := by
        rw [coprod.inr_desc]
      _ = (coprod.inr ≫ coprod.desc (𝟙 Y) g) ≫ pushout.inr _ _ := by
        simp only [Category.assoc, pushout.condition]
      _ = g ≫ pushout.inr _ _ := by rw [coprod.inr_desc]
  have huu : f ≫ (pushout.inl _ _ : Y ⟶ Q f g) = g ≫ pushout.inl _ _ := by rw [hvu, huv]
  HasColimit.mk
    { cocone := Cofork.ofπ (pushout.inl _ _) huu
      isColimit :=
        Cofork.IsColimit.mk _
          (fun s =>
            pushout.desc (Cofork.π s) (Cofork.π s) <|
              coprod.hom_ext (by simp only [coprod.inl_desc_assoc])
                (by simp only [coprod.desc_comp, Cofork.condition s]))
          (fun s => by simp only [pushout.inl_desc, Cofork.π_ofπ]) fun s m h =>
          pushout.hom_ext (by simpa only [pushout.inl_desc] using! h)
            (by simpa only [huv.symm, pushout.inl_desc] using! h) }

end

section

attribute [local instance] hasColimit_parallelPair

/-- A `NormalEpiCategory` category with finite coproducts and cokernels has all coequalizers. -/
/-
**CategoryTheory.NormalEpiCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.No
rmalEpiCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `NormalEpiCategory` category with finite coproducts and cokernels has all coeq
ualizers.
-/
instance (priority := 100) hasCoequalizers : HasCoequalizers C :=
  hasCoequalizers_of_hasColimit_parallelPair _

end

set_option backward.isDefEq.respectTransparency false in
/-- If a zero morphism is a kernel of `f`, then `f` is a monomorphism. -/
/-
**CategoryTheory.NormalEpiCategory.mono_of_zero_kernel** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.NormalEpiCategory`。
形式化陈述：mono_of_zero_kernel {X Y : C} (f : X ⟶ Y) (Z : C) (l : IsLimit (KernelFork
.ofι (0 : Z ⟶ X) (show 0 ≫ f = 0 by simp))) : Mono f
参数：f : X ⟶ Y；Z : C；l : IsLimit (KernelFork.ofι (0 : Z ⟶ X) (show 0 ≫ f = 0 by si
mp))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.NormalEpiCategory.hasCoequalizers`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   [CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.isIso_colimit_cocone_parallelPair_of_eq`：isIso_col
imit_cocone_parallelPair_of_eq (h₀ : f = g) {c : Cofork f g} (h : IsColimit c) :
 IsIso c.π
· 使用定理 `CategoryTheory.Limits.HasZeroMorphisms.comp_zero`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   (f : X ⟶ Y) (Z : C), …
· 使用定理 `CategoryTheory.Limits.Fork.ι_ofι`：∀ {C : Type u} {X Y : C} [inst : Categ
oryTheory.Category.{v, u} C] {f g : X ⟶ Y} {P : C} (ι : P ⟶ X)   (w : CategoryTh
eory.CategoryStruct.co…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Limits.coequalizer.condition`：∀ {C : Type u} {X Y : C} [i
nst : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory
.Limits.HasCoequalizer f g],   Ca…

--- 原说明 ---
If a zero morphism is a kernel of `f`, then `f` is a monomorphism.
-/
theorem mono_of_zero_kernel {X Y : C} (f : X ⟶ Y) (Z : C)
    (l : IsLimit (KernelFork.ofι (0 : Z ⟶ X) (show 0 ≫ f = 0 by simp))) : Mono f :=
  ⟨fun u v huv => by
    obtain ⟨W, w, hw, hl⟩ := normalEpiOfEpi (coequalizer.π u v)
    obtain ⟨m, hm⟩ := coequalizer.desc' f huv
    have reassoced {W : C} (h : coequalizer u v ⟶ W) : w ≫ coequalizer.π u v ≫ h = 0 ≫ h := by
      rw [← Category.assoc, eq_whisker hw]
    have hwf : w ≫ f = 0 := by rw [← hm, reassoced, zero_comp]
    obtain ⟨n, hn⟩ := KernelFork.IsLimit.lift' l _ hwf
    rw [Fork.ι_ofι, HasZeroMorphisms.comp_zero] at hn
    have : IsIso (coequalizer.π u v) := by
      apply isIso_colimit_cocone_parallelPair_of_eq hn.symm hl
    apply (cancel_mono (coequalizer.π u v)).1
    exact coequalizer.condition _ _⟩

section

variable [HasZeroObject C]

open ZeroObject

/-- If `g ≫ f = 0` implies `g = 0` for all `g`, then `f` is a monomorphism. -/
/-
**CategoryTheory.NormalEpiCategory.mono_of_cancel_zero** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.NormalEpiCategory`。
形式化陈述：mono_of_cancel_zero {X Y : C} (f : X ⟶ Y) (hf : forall (Z : C) (g : Z ⟶ X)
 (_ : g ≫ f = 0), g = 0) : Mono f
参数：f : X ⟶ Y；hf : forall (Z : C) (g : Z ⟶ X) (_ : g ≫ f = 0), g = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NormalEpiCategory.mono_of_zero_kernel`：mono_of_zero_kerne
l {X Y : C} (f : X ⟶ Y) (Z : C) (l : IsLimit (KernelFork.ofι (0 : Z ⟶ X) (show 0
 ≫ f = 0 by simp))) : Mono f

--- 原说明 ---
If `g ≫ f = 0` implies `g = 0` for all `g`, then `f` is a monomorphism.
-/
theorem mono_of_cancel_zero {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (Z : C) (g : Z ⟶ X) (_ : g ≫ f = 0), g = 0) : Mono f :=
  mono_of_zero_kernel f 0 <| zeroKernelOfCancelZero f hf

variable {D : Type*} [Category* D] [HasZeroMorphisms D] [HasZeroObject D]
/-
**CategoryTheory.NormalEpiCategory.preservesMonomorphisms_of_preservesKernels** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.NormalEpiCategory`。
形式化陈述：preservesMonomorphisms_of_preservesKernels (F : D ⥤ C) [F.PreservesZeroMor
phisms] [forall {X Y : D} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] : F.
PreservesMonomorphisms where preserves f
参数：F : D ⥤ C；f : X ⟶ Y；parallelPair f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NormalEpiCategory.mono_of_zero_kernel`：mono_of_zero_kerne
l {X Y : C} (f : X ⟶ Y) (Z : C) (l : IsLimit (KernelFork.ofι (0 : Z ⟶ X) (show 0
 ≫ f = 0 by simp))) : Mono f
-/
lemma preservesMonomorphisms_of_preservesKernels (F : D ⥤ C) [F.PreservesZeroMorphisms]
    [∀ {X Y : D} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    F.PreservesMonomorphisms where
  preserves f :=
    mono_of_zero_kernel _ _ <| IsLimit.equivIsoLimit (mapZeroKernelFork F f) <|
    (kernel.zeroKernelFork f).mapIsLimit (kernel.isLimitConeZeroCone f) F

end

end CategoryTheory.NormalEpiCategory

