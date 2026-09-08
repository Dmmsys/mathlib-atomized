/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.RingTheory.Ideal.Maps

/-!

# Some basic lemmas for manipulating `Ext` over `ModuleCat`

-/

@[expose] public section

universe v u

open LinearMap CategoryTheory Limits

variable {R : Type u} [CommRing R]

variable {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace CategoryTheory.Abelian

variable [Small.{v} R] {M N : ModuleCat.{v} R}

/-- If `r • N = 0`, then `r • 𝟙 M` induces the zero endomorphism on `Ext M N n`. -/
/-
**CategoryTheory.Abelian.Ext.postcomp_smul_id_eq_zero_of_mem_annihilator** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.Abelian.Ext`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [inst_1 : Small.{v, u} R] {M N : Module
Cat R} {r : R},   r ∈ Module.annihilator R ↑N →     ∀ (n : ℕ),       AddCommGrpC
at.ofHom ((CategoryTheory.Abelian.Ext.mk₀ (r • CategoryTheory.CategoryStruct.id 
M)).postcomp N ⋯) = 0
参数：n : ℕ；(CategoryTheory.Abelian.Ext.mk₀ (r • CategoryTheory.CategoryStruct.id M
)).postcomp N ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGrpCat.hom_ext`：∀ {X Y : AddCommGrpCat} {f g : X ⟶ Y}, AddCommGrp
Cat.Hom.hom f = AddCommGrpCat.Hom.hom g → f = g
· 使用定理 `instHasExtModuleCatOfSmall`：∀ (R : Type u) [inst : Ring R] [Small.{v, u}
 R], CategoryTheory.HasExt (ModuleCat R)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Module.mem_annihilator_iff_lsmul_eq_zero`：Module.mem_annihilator_iff_lsm
ul_eq_zero {R : Type*} [CommSemiring R] [Module R M] {r : R} : r in Module.annih
ilator R M ↔ LinearMap.lsmul R…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CategoryTheory.Abelian.Ext.comp.congr_simp`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Cat
egoryTheory.HasExt C] {X Y Z : C…
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_smul`：mk₀_smul (r : R) (f : X ⟶ Y) : mk₀ 
(r • f) = r • mk₀ f
· 使用引理 `CategoryTheory.Abelian.Ext.smul_comp`：smul_comp {X Y Z : C} {a b : Nat} 
(α : Ext X Y a) (β : Ext Y Z b) {c : Nat} (h : a + b = c) (r : R) : (r • α).comp
 β h = r • α.comp β h
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_id_comp`：mk₀_id_comp (α : Ext X Y n) : (m
k₀ (𝟙 X)).comp α (zero_add n) = α
· 使用定理 `CategoryTheory.Abelian.Ext.postcomp.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 :
 CategoryTheory.HasExt C] {Y Z : C} …
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Abelian.Ext.bilinearComp_apply_apply`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [ins
t_2 : CategoryTheory.HasExt C] (X Y Z : C…
· 使用引理 `CategoryTheory.Abelian.Ext.comp_smul`：comp_smul {X Y Z : C} {a b : Nat} 
(α : Ext X Y a) (β : Ext Y Z b) {c : Nat} (h : a + b = c) (r : R) : α.comp (r • 
β) h = r • α.comp β h
· 使用引理 `CategoryTheory.Abelian.Ext.comp_mk₀_id`：comp_mk₀_id (α : Ext X Y n) : α.
comp (mk₀ (𝟙 Y)) (add_zero n) = α
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_zero`：mk₀_zero : mk₀ (0 : X ⟶ Y) = 0
· 使用引理 `CategoryTheory.Abelian.Ext.zero_comp`：zero_comp {m : Nat} (β : Ext Y Z m
) (p : Nat) (h : n + m = p) : (0 : Ext X Y n).comp β h = 0

--- 原说明 ---
If `r • N = 0`, then `r • 𝟙 M` induces the zero endomorphism on `Ext M N n`.
-/
lemma Ext.postcomp_smul_id_eq_zero_of_mem_annihilator {r : R} (mem_ann : r ∈ Module.annihilator R N)
    (n : ℕ) : AddCommGrpCat.ofHom ((Ext.mk₀ (r • 𝟙 M)).postcomp N (add_zero n)) = 0 := by
  ext h
  have : r • 𝟙 N = 0 := by
    simp [← ModuleCat.lsmul_eq_smul_id, Module.mem_annihilator_iff_lsmul_eq_zero.mp mem_ann]
  have smul_eq : r • h = (Ext.mk₀ (r • 𝟙 N)).comp h (zero_add n) := by simp [Ext.mk₀_smul]
  simp [Ext.mk₀_smul, this, smul_eq]

/-- `r • 𝟙 M` induces a monomorphism in `Ext M N n` if and only if scalar multiplication by `r`
is faithful on `Ext M N n`. -/
/-
**CategoryTheory.Abelian.Ext.postcomp_smul_id_mono_iff** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Abelian.Ext`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [inst_1 : Small.{v, u} R] {M N : Module
Cat R} (r : R) (i : ℕ),   CategoryTheory.Mono       (AddCommGrpCat.ofHom ((Categ
oryTheory.Abelian.Ext.mk₀ (r • CategoryTheory.CategoryStruct.id M)).postcomp N ⋯
)) ↔     IsSMulRegular (CategoryTheory.Abelian.Ext N M i) r
参数：r : R；i : ℕ；AddCommGrpCat.ofHom ((CategoryTheory.Abelian.Ext.mk₀ (r • Categor
yTheory.CategoryStruct.id M)).postcomp N ⋯)；CategoryTheory.Abelian.Ext N M i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasExtModuleCatOfSmall`：∀ (R : Type u) [inst : Ring R] [Small.{v, u}
 R], CategoryTheory.HasExt (ModuleCat R)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Abelian.Ext.postcomp.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 :
 CategoryTheory.HasExt C] {Y Z : C} …
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_smul`：mk₀_smul (r : R) (f : X ⟶ Y) : mk₀ 
(r • f) = r • mk₀ f
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Abelian.Ext.bilinearComp_apply_apply`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [ins
t_2 : CategoryTheory.HasExt C] (X Y Z : C…
· 使用引理 `CategoryTheory.Abelian.Ext.comp_smul`：comp_smul {X Y Z : C} {a b : Nat} 
(α : Ext X Y a) (β : Ext Y Z b) {c : Nat} (h : a + b = c) (r : R) : α.comp (r • 
β) h = r • α.comp β h
· 使用引理 `CategoryTheory.Abelian.Ext.comp_mk₀_id`：comp_mk₀_id (α : Ext X Y n) : α.
comp (mk₀ (𝟙 Y)) (add_zero n) = α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`r • 𝟙 M` induces a monomorphism in `Ext M N n` if and only if scalar multiplica
tion by `r`
is faithful on `Ext M N n`.
-/
lemma Ext.postcomp_smul_id_mono_iff (r : R) (i : ℕ) :
    Mono (AddCommGrpCat.ofHom ((Ext.mk₀ (r • 𝟙 M)).postcomp N (add_zero i))) ↔
      IsSMulRegular (Ext N M i) r := by
  simp only [IsSMulRegular, AddCommGrpCat.mono_iff_injective]
  congr!
  ext
  simp [Ext.mk₀_smul]

end CategoryTheory.Abelian

