/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory

/-!
# Homology of complexes in concrete categories

The homology of short complexes in concrete categories was studied in
`Mathlib/Algebra/Homology/ShortComplex/ConcreteCategory.lean`. In this file,
we introduce specific definitions and lemmas for the homology
of homological complexes in concrete categories. In particular,
we give a computation of the connecting homomorphism of
the homology sequence in terms of (co)cycles.

-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC] [HasForget₂ C Ab.{v}]
  [Abelian C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  {ι : Type*} {c : ComplexShape ι}

namespace HomologicalComplex

variable (K : HomologicalComplex C c)

/-- Constructor for cycles of a homological complex in a concrete category. -/
/-
**HomologicalComplex.cyclesMk** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：cyclesMk {i : ι} (x : (forget₂ C Ab).obj (K.X i)) (j : ι) (hj : c.next i =
 j) (hx : ((forget₂ C Ab).map (K.d i j)) x = 0) : (forget₂ C Ab).obj (K.cycles i
)
参数：x : (forget₂ C Ab).obj (K.X i)；j : ι；hj : c.next i = j；hx : ((forget₂ C Ab).m
ap (K.d i j)) x = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for cycles of a homological complex in a concrete category.
-/
noncomputable def cyclesMk {i : ι} (x : (forget₂ C Ab).obj (K.X i)) (j : ι) (hj : c.next i = j)
    (hx : ((forget₂ C Ab).map (K.d i j)) x = 0) :
    (forget₂ C Ab).obj (K.cycles i) :=
  (K.sc i).cyclesMk x (by subst hj; exact hx)

@[simp]
/-
**HomologicalComplex.i_cyclesMk** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：i_cyclesMk {i : ι} (x : (forget₂ C Ab).obj (K.X i)) (j : ι) (hj : c.next i
 = j) (hx : ((forget₂ C Ab).map (K.d i j)) x = 0) : ((forget₂ C Ab).map (K.iCycl
es i)) (K.cyclesMk x j hj hx) = x
参数：x : (forget₂ C Ab).obj (K.X i)；j : ι；hj : c.next i = j；hx : ((forget₂ C Ab).m
ap (K.d i j)) x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用引理 `CategoryTheory.ShortComplex.i_cyclesMk`：i_cyclesMk [S.HasHomology] (x₂ :
 (forget₂ C Ab).obj S.X₂) (hx₂ : ((forget₂ C Ab).map S.g) x₂ = 0) : (forget₂ C A
b).map S.iCycles (S.cyclesMk…
-/
lemma i_cyclesMk {i : ι} (x : (forget₂ C Ab).obj (K.X i)) (j : ι) (hj : c.next i = j)
    (hx : ((forget₂ C Ab).map (K.d i j)) x = 0) :
    ((forget₂ C Ab).map (K.iCycles i)) (K.cyclesMk x j hj hx) = x := by
  subst hj
  apply (K.sc i).i_cyclesMk

end HomologicalComplex

namespace CategoryTheory

namespace ShortComplex

namespace ShortExact

variable {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

/-
**CategoryTheory.ShortComplex.ShortExact.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_apply' (x₃ : (forget₂ C Ab).obj (S.X₃.homology i))
    (x₂ : (forget₂ C Ab).obj (S.X₂.opcycles i))
    (x₁ : (forget₂ C Ab).obj (S.X₁.cycles j))
    (h₂ : (forget₂ C Ab).map (HomologicalComplex.opcyclesMap S.g i) x₂ =
      (forget₂ C Ab).map (S.X₃.homologyι i) x₃)
    (h₁ : (forget₂ C Ab).map (HomologicalComplex.cyclesMap S.f j) x₁ =
      (forget₂ C Ab).map (S.X₂.opcyclesToCycles i j) x₂) :
    (forget₂ C Ab).map (hS.δ i j hij) x₃ = (forget₂ C Ab).map (S.X₁.homologyπ j) x₁ :=
  (HomologicalComplex.HomologySequence.snakeInput hS i j hij).δ_apply' x₃ x₂ x₁ h₂ h₁

include hS in
/--
In the short exact sequence of complexes
```
       0            0            0
       |            |            |
       v            v            v
...-> X_1,i -----> X_1,j --d--> X_1,k ->...
       |            |            |
       |          f |            |
       v            v            v
...-> X_2,i --d--> X_2,j -----> X_2,k ->...
       |            |            |
       v            v            v
...-> X_3,i -----> X_3,j -----> X_3,k ->...
       |            |            |
       v            v            v
       0            0            0
```
if `x₁ ∈ X_1,j` and `x₂ ∈ X_2,i` and if `f(x₁) = d(x₂)` then `d(x₁) = 0`. -/
/-
**CategoryTheory.ShortComplex.ShortExact.d_eq_zero_of_f_eq_d_apply** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：d_eq_zero_of_f_eq_d_apply (x₂ : ((forget₂ C Ab).obj (S.X₂.X i))) (x₁ : ((f
orget₂ C Ab).obj (S.X₁.X j))) (hx₁ : ((forget₂ C Ab).map (S.f.f j)) x₁ = ((forge
t₂ C Ab).map (S.X₂.d i j)) x₂) (k : ι) : ((forget₂ C Ab).map (S.X₁.d j k)) x₁ = 
0
参数：x₂ : ((forget₂ C Ab).obj (S.X₂.X i))；x₁ : ((forget₂ C Ab).obj (S.X₁.X j))；hx₁
 : ((forget₂ C Ab).map (S.f.f j)) x₁ = ((forget₂ C Ab).map (S.X₂.d i j)) x₂；k : 
ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Preadditive.mono_iff_injective`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [ins
t_1 : (X Y : C) → FunLike (FC X Y) …
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `HomologicalComplex.instMonoFOfHasFiniteLimits`：∀ {C : Type u_1} {ι : Typ
e u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c : ComplexShape ι}   [ins
t_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.forget₂_comp_apply`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   
{CC : outParam (C → Type w)} [inst_1 : o…
· 使用定理 `HomologicalComplex.Hom.comm`：∀ {ι : Type u_1} {V : Type u} [inst : Categ
oryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
V] {c : ComplexSh…
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
In the short exact sequence of complexes
```
       0            0            0
       |            |            |
       v            v            v
...-> X_1,i -----> X_1,j --d--> X_1,k ->...
       |            |            |
       |          f |            |
       v            v            v
...-> X_2,i --d--> X_2,j -----> X_2,k ->...
       |            |            |
       v            v            v
...-> X_3,i -----> X_3,j -----> X_3,k ->...
       |            |            |
       v            v            v
       0            0            0
```
if `x₁ ∈ X_1,j` and `x₂ ∈ X_2,i` and if `f(x₁) = d(x₂)` then `d(x₁) = 0`.
-/
theorem d_eq_zero_of_f_eq_d_apply
    (x₂ : ((forget₂ C Ab).obj (S.X₂.X i))) (x₁ : ((forget₂ C Ab).obj (S.X₁.X j)))
    (hx₁ : ((forget₂ C Ab).map (S.f.f j)) x₁ = ((forget₂ C Ab).map (S.X₂.d i j)) x₂) (k : ι) :
    ((forget₂ C Ab).map (S.X₁.d j k)) x₁ = 0 := by
  have := hS.mono_f
  apply (Preadditive.mono_iff_injective (S.f.f k)).1 inferInstance
  rw [← ConcreteCategory.forget₂_comp_apply, ← HomologicalComplex.Hom.comm,
    ConcreteCategory.forget₂_comp_apply, hx₁, ← ConcreteCategory.forget₂_comp_apply,
    HomologicalComplex.d_comp_d, Functor.map_zero, map_zero]
  rfl
/-
**CategoryTheory.ShortComplex.ShortExact.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_apply (x₃ : (forget₂ C Ab).obj (S.X₃.X i))
    (hx₃ : (forget₂ C Ab).map (S.X₃.d i j) x₃ = 0)
    (x₂ : (forget₂ C Ab).obj (S.X₂.X i)) (hx₂ : (forget₂ C Ab).map (S.g.f i) x₂ = x₃)
    (x₁ : (forget₂ C Ab).obj (S.X₁.X j))
    (hx₁ : (forget₂ C Ab).map (S.f.f j) x₁ = (forget₂ C Ab).map (S.X₂.d i j) x₂)
    (k : ι) (hk : c.next j = k) :
    (forget₂ C Ab).map (hS.δ i j hij)
      ((forget₂ C Ab).map (S.X₃.homologyπ i) (S.X₃.cyclesMk x₃ j (c.next_eq' hij) hx₃)) =
        (forget₂ C Ab).map (S.X₁.homologyπ j) (S.X₁.cyclesMk x₁ k hk
          (d_eq_zero_of_f_eq_d_apply hS _ _ x₂ x₁ hx₁ _)) := by
  refine hS.δ_apply' i j hij _ ((forget₂ C Ab).map (S.X₂.pOpcycles i) x₂) _ ?_ ?_
  · rw [← ConcreteCategory.forget₂_comp_apply, ← ConcreteCategory.forget₂_comp_apply,
      HomologicalComplex.p_opcyclesMap, Functor.map_comp, ConcreteCategory.comp_apply,
      HomologicalComplex.homology_π_ι, ConcreteCategory.forget₂_comp_apply, hx₂,
      HomologicalComplex.i_cyclesMk]
  · apply (Preadditive.mono_iff_injective (S.X₂.iCycles j)).1 inferInstance
    conv_lhs =>
      rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.cyclesMap_i,
        ConcreteCategory.forget₂_comp_apply, HomologicalComplex.i_cyclesMk, hx₁]
    conv_rhs =>
      rw [← ConcreteCategory.forget₂_comp_apply, ← ConcreteCategory.forget₂_comp_apply,
        HomologicalComplex.pOpcycles_opcyclesToCycles_assoc, HomologicalComplex.toCycles_i]

end ShortExact

end ShortComplex

end CategoryTheory

