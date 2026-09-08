/-
Copyright (c) 2019 Kenny Lau, Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Jujian Zhang
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Congruence.Defs
public import Mathlib.Data.Finset.Order
public import Mathlib.Tactic.SuppressCompilation

/-!
# Direct limit of modules and abelian groups

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

Generalizes the notion of "union", or "gluing", of incomparable modules over the same ring,
or incomparable abelian groups.

It is constructed as a quotient of the free module instead of a quotient of the disjoint union
so as to make the operations (addition etc.) "computable".

## Main definitions

* `Module.DirectLimit G f`
* `AddCommGroup.DirectLimit G f`

-/

@[expose] public section

suppress_compilation
noncomputable section -- needed for `deriving`

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

open Submodule

namespace Module

alias DirectedSystem.map_self := DirectedSystem.map_self'
alias DirectedSystem.map_map := DirectedSystem.map_map'

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

/-- The relation on the direct sum that generates the additive congruence that defines the
colimit as a quotient. -/
/-
**Module.DirectLimit.Eqv** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module.DirectLimit`。
形式化陈述：{R : Type u_1} →   [inst : Semiring R] →     {ι : Type u_2} →       [inst_
1 : Preorder ι] →         {G : ι → Type u_3} →           [inst_2 : (i : ι) → Add
CommMonoid (G i)] →             [inst_3 : (i : ι) → _root_.Module R (G i)] →    
           ((i j : ι) → i ≤ j → G i →ₗ[R] G j) → [DecidableEq ι] → DirectSum ι G
 → DirectSum ι G → Prop
参数：i : ι；G i；i : ι；G i；(i j : ι) → i ≤ j → G i →ₗ[R] G j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation on the direct sum that generates the additive congruence that defin
es the
colimit as a quotient.
-/
inductive DirectLimit.Eqv [DecidableEq ι] : DirectSum ι G → DirectSum ι G → Prop
  | of_map {i j} (h : i ≤ j) (x : G i) :
    Eqv (DirectSum.lof R ι G i x) (DirectSum.lof R ι G j <| f i j h x)

/-- The congruence relation to quotient the direct sum by to obtain the direct limit. -/
/-
**Module.DirectLimit.moduleCon** 是 Mathlib 中的一个定义，位于命名空间 `Module.DirectLimit`。
形式化陈述：{R : Type u_1} →   [inst : Semiring R] →     {ι : Type u_2} →       [inst_
1 : Preorder ι] →         {G : ι → Type u_3} →           [inst_2 : (i : ι) → Add
CommMonoid (G i)] →             [inst_3 : (i : ι) → _root_.Module R (G i)] →    
           ((i j : ι) → i ≤ j → G i →ₗ[R] G j) → [DecidableEq ι] → ModuleCon R (
DirectSum ι G)
参数：i : ι；G i；i : ι；G i；(i j : ι) → i ≤ j → G i →ₗ[R] G j；DirectSum ι G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The congruence relation to quotient the direct sum by to obtain the direct limit
.
-/
def DirectLimit.moduleCon [DecidableEq ι] : ModuleCon R (DirectSum ι G) :=
  SMulCon.addConGen' (Eqv f) <| by rintro _ _ _ ⟨⟩; simpa only [← map_smul] using .of_map ..

variable (G)

/-- The direct limit of a directed system is the modules glued together along the maps. -/
/-
**Module.DirectLimit** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：DirectLimit [DecidableEq ι] : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The direct limit of a directed system is the modules glued together along the ma
ps.
-/
def DirectLimit [DecidableEq ι] : Type _ := (DirectLimit.moduleCon f).Quotient

variable [DecidableEq ι]

namespace DirectLimit

section Basic

/-
**Module.DirectLimit.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Module.DirectLimit
`。
形式化陈述：addCommMonoid : AddCommMonoid (DirectLimit G f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid : AddCommMonoid (DirectLimit G f) :=
  inferInstanceAs (AddCommMonoid (moduleCon f).Quotient)
/-
**Module.DirectLimit.module** 是 Mathlib 中的一个实例，位于命名空间 `Module.DirectLimit`。
形式化陈述：module : Module R (DirectLimit G f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module : Module R (DirectLimit G f) := inferInstanceAs (Module R (moduleCon f).Quotient)
/-
**Module.DirectLimit.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Module.DirectLimit`
。
形式化陈述：addCommGroup (G : ι -> Type*) [forall i, AddCommGroup (G i)] [forall i, Mo
dule R (G i)] (f : forall i j, i <= j -> G i ->ₗ[R] G j) : AddCommGroup (DirectL
imit G f)
参数：G : ι -> Type*；G i；G i；f : forall i j, i <= j -> G i ->ₗ[R] G j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroup (G : ι → Type*) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) : AddCommGroup (DirectLimit G f) :=
  inferInstanceAs (AddCommGroup (moduleCon f).Quotient)
/-
**Module.DirectLimit.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `Module.DirectLimit`。
形式化陈述：inhabited : Inhabited (DirectLimit G f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited : Inhabited (DirectLimit G f) :=
  ⟨0⟩
/-
**Module.DirectLimit.unique** 是 Mathlib 中的一个实例，位于命名空间 `Module.DirectLimit`。
形式化陈述：unique [IsEmpty ι] : Unique (DirectLimit G f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance unique [IsEmpty ι] : Unique (DirectLimit G f) :=
  inferInstanceAs <| Unique (Quotient _)

variable (R ι)

/-- The canonical map from a component to the direct limit. -/
/-
**Module.DirectLimit.of** 是 Mathlib 中的一个定义，位于命名空间 `Module.DirectLimit`。
形式化陈述：of (i) : G i ->ₗ[R] DirectLimit G f
参数：i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from a component to the direct limit.
-/
def of (i) : G i →ₗ[R] DirectLimit G f :=
  .comp { __ := AddCon.mk' _, map_smul' := fun _ _ ↦ rfl } <| DirectSum.lof R ι G i

variable {R ι G f}
/-
**Module.DirectLimit.quotMk_of** 是 Mathlib 中的一个定理，位于命名空间 `Module.DirectLimit`。
形式化陈述：quotMk_of (i x) : Quot.mk _ (.of G i x) = of R ι G f i x
参数：i x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotMk_of (i x) : Quot.mk _ (.of G i x) = of R ι G f i x := rfl

@[simp]
/-
**Module.DirectLimit.of_f** 是 Mathlib 中的一个定理，位于命名空间 `Module.DirectLimit`。
形式化陈述：of_f {i j hij x} : of R ι G f j (f i j hij x) = of R ι G f i x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddCon.eq`：∀ {M : Type u_1} [inst : Add M] (c : AddCon M) {a b : M}, ↑a 
= ↑b ↔ c a b
-/
theorem of_f {i j hij x} : of R ι G f j (f i j hij x) = of R ι G f i x :=
  (AddCon.eq _).mpr <| .symm <| .of _ _ (.of_map _ _)

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
/-
**Module.DirectLimit.exists_of** 是 Mathlib 中的一个定理，位于命名空间 `Module.DirectLimit`。
形式化陈述：exists_of [Nonempty ι] [IsDirectedOrder ι] (z : DirectLimit G f) : exists 
i x, of R ι G f i x = z
参数：z : DirectLimit G f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `DirectSum.induction_on`：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) 
→ AddCommMonoid (β i)] [inst_1 : DecidableEq ι]   {motive : (DirectSum ι fun i =
> β i) → Pro…
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Module.DirectLimit.of_f`：of_f {i j hij x} : of R ι G f j (f i j hij x) =
 of R ι G f i x

--- 原说明 ---
Every element of the direct limit corresponds to some element in
some component of the directed system.
-/
theorem exists_of [Nonempty ι] [IsDirectedOrder ι] (z : DirectLimit G f) :
    ∃ i x, of R ι G f i x = z :=
  Nonempty.elim (by infer_instance) fun ind : ι ↦
    Quotient.inductionOn' z fun z ↦
      DirectSum.induction_on z ⟨ind, 0, map_zero _⟩ (fun i x ↦ ⟨i, x, rfl⟩)
        fun p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩ ↦
        let ⟨k, hik, hjk⟩ := exists_ge_ge i j
        ⟨k, f i k hik x + f j k hjk y, by
          rw [map_add, of_f, of_f, ihx, ihy]
          rfl ⟩
/-
**Module.DirectLimit.exists_of** 是 Mathlib 中的一个定理，位于命名空间 `Module.DirectLimit`。
形式化陈述：exists_of [Nonempty ι] [IsDirectedOrder ι] (z : DirectLimit G f) : exists 
i x, of R ι G f i x = z
参数：z : DirectLimit G f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `DirectSum.induction_on`：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) 
→ AddCommMonoid (β i)] [inst_1 : DecidableEq ι]   {motive : (DirectSum ι fun i =
> β i) → Pro…
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Module.DirectLimit.of_f`：of_f {i j hij x} : of R ι G f j (f i j hij x) =
 of R ι G f i x
-/
theorem exists_of₂ [Nonempty ι] [IsDirectedOrder ι] (z w : DirectLimit G f) :
    ∃ i x y, of R ι G f i x = z ∧ of R ι G f i y = w :=
  have ⟨i, x, hx⟩ := exists_of z
  have ⟨j, y, hy⟩ := exists_of w
  have ⟨k, hik, hjk⟩ := exists_ge_ge i j
  ⟨k, f i k hik x, f j k hjk y, by rw [of_f, hx], by rw [of_f, hy]⟩

@[elab_as_elim]
/-
**Module.DirectLimit.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Module.DirectLimit`
。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {ι : Type u_2} [inst_1 : Preorder ι] 
{G : ι → Type u_3}   [inst_2 : (i : ι) → AddCommMonoid (G i)] [inst_3 : (i : ι) 
→ _root_.Module R (G i)]   {f : (i j : ι) → i ≤ j → G i →ₗ[R] G j} [inst_4 : Dec
idableEq ι] [Nonempty ι] [IsDirectedOrder ι]   {C : Module.DirectLimit G f → Pro
p} (z : Module.DirectLimit G f),   (∀ (i : ι) (x : G i), C ((Module.DirectLimit.
of R ι G f i) x)) → C z
参数：i : ι；G i；i : ι；G i；i j : ι；z : Module.DirectLimit G f；∀ (i : ι) (x : G i), C
 ((Module.DirectLimit.of R ι G f i) x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DirectLimit.exists_of`：exists_of [Nonempty ι] [IsDirectedOrder ι]
 (z : DirectLimit G f) : exists i x, of R ι G f i x = z
-/
protected theorem induction_on [Nonempty ι] [IsDirectedOrder ι] {C : DirectLimit G f → Prop}
    (z : DirectLimit G f) (ih : ∀ i x, C (of R ι G f i x)) : C z :=
  let ⟨i, x, h⟩ := exists_of z
  h ▸ ih i x

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable (R ι G f) in
/-- The universal property of the direct limit: maps from the components to another module
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
/-
**Module.DirectLimit.lift** 是 Mathlib 中的一个定义，位于命名空间 `Module.DirectLimit`。
形式化陈述：lift (g : forall i, G i ->ₗ[R] P) (Hg : forall i j hij x, g j (f i j hij x
) = g i x) : DirectLimit G f ->ₗ[R] P where __
参数：g : forall i, G i ->ₗ[R] P；Hg : forall i j hij x, g j (f i j hij x) = g i x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of the direct limit: maps from the components to another 
module
that respect the directed system structure (i.e. make some diagram commute) give
 rise
to a unique map out of the direct limit.
-/
def lift (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →ₗ[R] P where
  __ := AddCon.lift _ (DirectSum.toModule R ι P g) <|
    AddCon.addConGen_le.2 fun _ _ ⟨_, _⟩ ↦ by simpa using (Hg _ _ _ _).symm
  map_smul' r := by rintro ⟨x⟩; exact map_smul (DirectSum.toModule R ι P g) r x

variable (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
/-
**Module.DirectLimit.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `Module.DirectLimit`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {ι : Type u_2} [inst_1 : Preorder ι] 
{G : ι → Type u_3}   [inst_2 : (i : ι) → AddCommMonoid (G i)] [inst_3 : (i : ι) 
→ _root_.Module R (G i)]   {f : (i j : ι) → i ≤ j → G i →ₗ[R] G j} [inst_4 : Dec
idableEq ι] {P : Type u_4} [inst_5 : AddCommMonoid P]   [inst_6 : _root_.Module 
R P] (g : (i : ι) → G i →ₗ[R] P)   (Hg : ∀ (i j : ι) (hij : i ≤ j) (x : G i), (g
 j) ((f i j hij) x) = (g i) x) {i : ι} (x : G i),   (Module.DirectLimit.lift R ι
 G f g Hg) ((Module.DirectLimit.of R ι G f i) x) = (g i) x
参数：i : ι；G i；i : ι；G i；i j : ι；g : (i : ι) → G i →ₗ[R] P；Hg : ∀ (i j : ι) (hij :
 i ≤ j) (x : G i), (g j) ((f i j hij) x) = (g i) x；x : G i；Module.DirectLimit.li
ft R ι G f g Hg；(Module.DirectLimit.of R ι G f i) x；g i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.toModule_lof`：toModule_lof (i) (x : M i) : toModule R ι N φ (l
of R ι M i x) = φ i x
-/
@[simp] theorem lift_of {i} (x) : lift R ι G f g Hg (of R ι G f i x) = g i x :=
  DirectSum.toModule_lof R _ _

@[ext]
/-
**Module.DirectLimit.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Module.DirectLimit`。
形式化陈述：hom_ext {g₁ g₂ : DirectLimit G f ->ₗ[R] P} (h : forall i, g₁ ∘ₗ of R ι G f
 i = g₂ ∘ₗ of R ι G f i) : g₁ = g₂
参数：h : forall i, g₁ ∘ₗ of R ι G f i = g₂ ∘ₗ of R ι G f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toAddMonoidHom_injective`：toAddMonoidHom_injective : Function.
Injective (toAddMonoidHom : (M ->ₛₗ[σ] M₃) -> M ->+ M₃)
· 使用定理 `AddCon.hom_ext`：∀ {M : Type u_1} {P : Type u_3} [inst : AddZeroClass M] 
[inst_1 : AddZeroClass P] {c : AddCon M}   {f g : c.Quotient →+ P}, f.comp c.mk'
 = g…
· 使用定理 `DirectSum.addHom_ext'`：addHom_ext' {γ : Type*} [AddZeroClass γ] ⦃f g : (
⨁ i, β i) ->+ γ⦄ (H : forall i : ι, f.comp (of _ i) = g.comp (of _ i)) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f →ₗ[R] P}
    (h : ∀ i, g₁ ∘ₗ of R ι G f i = g₂ ∘ₗ of R ι G f i) :
    g₁ = g₂ :=
  LinearMap.toAddMonoidHom_injective <| AddCon.hom_ext <| DirectSum.addHom_ext' fun i =>
    congr($(h i).toAddMonoidHom)

@[simp]
/-
**Module.DirectLimit.lift_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `Module.DirectLimit`
。
形式化陈述：lift_comp_of (F : DirectLimit G f ->ₗ[R] P) : lift R ι G f (fun i => F.com
p <| of R ι G f i) (fun i j hij x => by simp) = F
参数：F : DirectLimit G f ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DirectLimit.hom_ext`：hom_ext {g₁ g₂ : DirectLimit G f ->ₗ[R] P} (
h : forall i, g₁ ∘ₗ of R ι G f i = g₂ ∘ₗ of R ι G f i) : g₁ = g₂
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.DirectLimit.lift_of`：∀ {R : Type u_1} [inst : Semiring R] {ι : Ty
pe u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → AddCommMo
noid (G i)] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_comp_of (F : DirectLimit G f →ₗ[R] P) :
    lift R ι G f (fun i ↦ F.comp <| of R ι G f i) (fun i j hij x ↦ by simp) = F := by
  ext; simp

@[simp]
/-
**Module.DirectLimit.lift_of'** 是 Mathlib 中的一个定理，位于命名空间 `Module.DirectLimit`。
形式化陈述：lift_of' : lift R ι G f (of R ι G f) (fun i j hij x => by simp) = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DirectLimit.hom_ext`：hom_ext {g₁ g₂ : DirectLimit G f ->ₗ[R] P} (
h : forall i, g₁ ∘ₗ of R ι G f i = g₂ ∘ₗ of R ι G f i) : g₁ = g₂
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.DirectLimit.lift_of`：∀ {R : Type u_1} [inst : Semiring R] {ι : Ty
pe u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → AddCommMo
noid (G i)] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_of' : lift R ι G f (of R ι G f) (fun i j hij x ↦ by simp) = .id := by
  ext; simp
/-
**Module.DirectLimit.lift_injective** 是 Mathlib 中的一个引理，位于命名空间 `Module.DirectLimi
t`。
形式化陈述：lift_injective [IsDirectedOrder ι] (injective : forall i, Function.Injecti
ve <| g i) : Function.Injective (lift R ι G f g Hg)
参数：injective : forall i, Function.Injective <| g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Function.injective_of_subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} [Sub
singleton α] (f : α → β), Function.Injective f
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Module.DirectLimit.exists_of₂`：exists_of₂ [Nonempty ι] [IsDirectedOrder 
ι] (z w : DirectLimit G f) : exists i x y, of R ι G f i x = z ∧ of R ι G f i y =
 w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.DirectLimit.lift_of`：∀ {R : Type u_1} [inst : Semiring R] {ι : Ty
pe u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → AddCommMo
noid (G i)] [ins…
-/
lemma lift_injective [IsDirectedOrder ι]
    (injective : ∀ i, Function.Injective <| g i) :
    Function.Injective (lift R ι G f g Hg) := by
  cases isEmpty_or_nonempty ι
  · apply Function.injective_of_subsingleton
  intro z w eq
  obtain ⟨i, x, y, rfl, rfl⟩ := exists_of₂ z w
  simp_rw [lift_of] at eq
  rw [injective _ eq]

section functorial

variable {G' : ι → Type*} [∀ i, AddCommMonoid (G' i)] [∀ i, Module R (G' i)]
variable {f' : ∀ i j, i ≤ j → G' i →ₗ[R] G' j}
variable {G'' : ι → Type*} [∀ i, AddCommMonoid (G'' i)] [∀ i, Module R (G'' i)]
variable {f'' : ∀ i j, i ≤ j → G'' i →ₗ[R] G'' j}

/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of linear maps `gᵢ : Gᵢ ⟶ G'ᵢ` such that `g ∘ f = f' ∘ g` induces a linear map
`lim G ⟶ lim G'`.
-/
/-
**Module.DirectLimit.map** 是 Mathlib 中的一个定义，位于命名空间 `Module.DirectLimit`。
形式化陈述：map (g : (i : ι) -> G i ->ₗ[R] G' i) (hg : forall i j h, g j ∘ₗ f i j h = 
f' i j h ∘ₗ g i) : DirectLimit G f ->ₗ[R] DirectLimit G' f'
参数：g : (i : ι) -> G i ->ₗ[R] G' i；hg : forall i j h, g j ∘ₗ f i j h = f' i j h ∘
ₗ g i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` resp
ectively, any
family of linear maps `gᵢ : Gᵢ ⟶ G'ᵢ` such that `g ∘ f = f' ∘ g` induces a linea
r map
`lim G ⟶ lim G'`.
-/
def map (g : (i : ι) → G i →ₗ[R] G' i) (hg : ∀ i j h, g j ∘ₗ f i j h = f' i j h ∘ₗ g i) :
    DirectLimit G f →ₗ[R] DirectLimit G' f' :=
  lift _ _ _ _ (fun i ↦ of _ _ _ _ _ ∘ₗ g i) fun i j h g ↦ by
    have eq1 := LinearMap.congr_fun (hg i j h) g
    simp only [LinearMap.coe_comp, Function.comp_apply] at eq1 ⊢
    rw [eq1, of_f]
/-
**Module.DirectLimit.map_apply_of** 是 Mathlib 中的一个定理，位于命名空间 `Module.DirectLimit`
。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {ι : Type u_2} [inst_1 : Preorder ι] 
{G : ι → Type u_3}   [inst_2 : (i : ι) → AddCommMonoid (G i)] [inst_3 : (i : ι) 
→ _root_.Module R (G i)]   {f : (i j : ι) → i ≤ j → G i →ₗ[R] G j} [inst_4 : Dec
idableEq ι] {G' : ι → Type u_5}   [inst_5 : (i : ι) → AddCommMonoid (G' i)] [ins
t_6 : (i : ι) → _root_.Module R (G' i)]   {f' : (i j : ι) → i ≤ j → G' i →ₗ[R] G
' j} (g : (i : ι) → G i →ₗ[R] G' i)   (hg : ∀ (i j : ι) (h : i ≤ j), g j ∘ₗ f i 
j h = f' i j h ∘ₗ g i) {i : ι} (x : G i),   (Module.DirectLimit.map g hg) ((Modu
le.DirectLimit.of R ι G f i) x) = (Module.DirectLimit.of R ι G' f' i) ((g i) x)
参数：i : ι；G i；i : ι；G i；i j : ι；i : ι；G' i；i : ι；G' i；i j : ι；g : (i : ι) → G i →
ₗ[R] G' i；hg : ∀ (i j : ι) (h : i ≤ j), g j ∘ₗ f i j h = f' i j h ∘ₗ g i；x : G i
；Module.DirectLimit.map g hg；(Module.DirectLimit.of R ι G f i) x；Module.DirectLi
mit.of R ι G' f' i；(g i) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DirectLimit.lift_of`：∀ {R : Type u_1} [inst : Semiring R] {ι : Ty
pe u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → AddCommMo
noid (G i)] [ins…
-/
@[simp] lemma map_apply_of (g : (i : ι) → G i →ₗ[R] G' i)
    (hg : ∀ i j h, g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
    {i : ι} (x : G i) :
    map g hg (of _ _ G f _ x) = of R ι G' f' i (g i x) :=
  lift_of _ _ _
/-
**Module.DirectLimit.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Module.DirectLimit`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {ι : Type u_2} [inst_1 : Preorder ι] 
{G : ι → Type u_3}   [inst_2 : (i : ι) → AddCommMonoid (G i)] [inst_3 : (i : ι) 
→ _root_.Module R (G i)]   {f : (i j : ι) → i ≤ j → G i →ₗ[R] G j} [inst_4 : Dec
idableEq ι],   Module.DirectLimit.map (fun x => LinearMap.id) ⋯ = LinearMap.id
参数：i : ι；G i；i : ι；G i；i j : ι；fun x => LinearMap.id。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DirectLimit.hom_ext`：hom_ext {g₁ g₂ : DirectLimit G f ->ₗ[R] P} (
h : forall i, g₁ ∘ₗ of R ι G f i = g₂ ∘ₗ of R ι G f i) : g₁ = g₂
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.DirectLimit.map_apply_of`：∀ {R : Type u_1} [inst : Semiring R] {ι
 : Type u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → AddC
ommMonoid (G i)] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_id :
    map (fun _ ↦ LinearMap.id) (fun _ _ _ ↦ rfl) = LinearMap.id (M := DirectLimit G f) := by
  ext; simp
/-
**Module.DirectLimit.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `Module.DirectLimit`。
形式化陈述：map_comp (g₁ : (i : ι) -> G i ->ₗ[R] G' i) (g₂ : (i : ι) -> G' i ->ₗ[R] G'
' i) (hg₁ : forall i j h, g₁ j ∘ₗ f i j h = f' i j h ∘ₗ g₁ i) (hg₂ : forall i j 
h, g₂ j ∘ₗ f' i j h = f'' i j h ∘ₗ g₂ i) : (map g₂ hg₂ ∘ₗ map g₁ hg₁ : DirectLim
it G f ->ₗ[R] DirectLimit G'' f'') = (map (fun i => g₂ i ∘ₗ g₁ i) fun i j h => b
y rw [LinearMap.comp_assoc]; rw [hg₁ i]; rw [← LinearMap.comp_assoc]; rw [hg₂ i]
; rw [LinearMap.comp_assoc] : DirectLimit G f ->ₗ[R] DirectLimit G'' f'')
参数：g₁ : (i : ι) -> G i ->ₗ[R] G' i；g₂ : (i : ι) -> G' i ->ₗ[R] G'' i；hg₁ : foral
l i j h, g₁ j ∘ₗ f i j h = f' i j h ∘ₗ g₁ i；hg₂ : forall i j h, g₂ j ∘ₗ f' i j h
 = f'' i j h ∘ₗ g₂ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DirectLimit.hom_ext`：hom_ext {g₁ g₂ : DirectLimit G f ->ₗ[R] P} (
h : forall i, g₁ ∘ₗ of R ι G f i = g₂ ∘ₗ of R ι G f i) : g₁ = g₂
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.DirectLimit.map_apply_of`：∀ {R : Type u_1} [inst : Semiring R] {ι
 : Type u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → AddC
ommMonoid (G i)] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp (g₁ : (i : ι) → G i →ₗ[R] G' i) (g₂ : (i : ι) → G' i →ₗ[R] G'' i)
    (hg₁ : ∀ i j h, g₁ j ∘ₗ f i j h = f' i j h ∘ₗ g₁ i)
    (hg₂ : ∀ i j h, g₂ j ∘ₗ f' i j h = f'' i j h ∘ₗ g₂ i) :
    (map g₂ hg₂ ∘ₗ map g₁ hg₁ :
      DirectLimit G f →ₗ[R] DirectLimit G'' f'') =
    (map (fun i ↦ g₂ i ∘ₗ g₁ i) fun i j h ↦ by
        rw [LinearMap.comp_assoc, hg₁ i, ← LinearMap.comp_assoc, hg₂ i, LinearMap.comp_assoc] :
      DirectLimit G f →ₗ[R] DirectLimit G'' f'') := by
  ext; simp

open LinearEquiv LinearMap in
/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of equivalences `eᵢ : Gᵢ ≅ G'ᵢ` such that `e ∘ f = f' ∘ e` induces an equivalence
`lim G ≅ lim G'`.
-/
/-
**Module.DirectLimit.congr** 是 Mathlib 中的一个定义，位于命名空间 `Module.DirectLimit`。
形式化陈述：congr (e : (i : ι) -> G i ≃ₗ[R] G' i) (he : forall i j h, e j ∘ₗ f i j h =
 f' i j h ∘ₗ e i) : DirectLimit G f ≃ₗ[R] DirectLimit G' f'
参数：e : (i : ι) -> G i ≃ₗ[R] G' i；he : forall i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ
 e i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` resp
ectively, any
family of equivalences `eᵢ : Gᵢ ≅ G'ᵢ` such that `e ∘ f = f' ∘ e` induces an equ
ivalence
`lim G ≅ lim G'`.
-/
def congr (e : (i : ι) → G i ≃ₗ[R] G' i) (he : ∀ i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i) :
    DirectLimit G f ≃ₗ[R] DirectLimit G' f' :=
  LinearEquiv.ofLinearMap (map (e ·) he)
    (map (fun i ↦ (e i).symm) fun i j h ↦ by
      rw [toLinearMap_symm_comp_eq, ← comp_assoc, he i, comp_assoc, comp_coe, symm_trans_self,
        refl_toLinearMap, comp_id])
    (by simp [map_comp]) (by simp [map_comp])
/-
**Module.DirectLimit.congr_apply_of** 是 Mathlib 中的一个引理，位于命名空间 `Module.DirectLimi
t`。
形式化陈述：congr_apply_of (e : (i : ι) -> G i ≃ₗ[R] G' i) (he : forall i j h, e j ∘ₗ 
f i j h = f' i j h ∘ₗ e i) {i : ι} (g : G i) : congr e he (of _ _ G f i g) = of 
_ _ G' f' i (e i g)
参数：e : (i : ι) -> G i ≃ₗ[R] G' i；he : forall i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ
 e i；g : G i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DirectLimit.map_apply_of`：∀ {R : Type u_1} [inst : Semiring R] {ι
 : Type u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → AddC
ommMonoid (G i)] [ins…
-/
lemma congr_apply_of (e : (i : ι) → G i ≃ₗ[R] G' i) (he : ∀ i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i)
    {i : ι} (g : G i) :
    congr e he (of _ _ G f i g) = of _ _ G' f' i (e i g) :=
  map_apply_of _ he _

open LinearEquiv LinearMap in
/-
**Module.DirectLimit.congr_symm_apply_of** 是 Mathlib 中的一个引理，位于命名空间 `Module.Direc
tLimit`。
形式化陈述：congr_symm_apply_of (e : (i : ι) -> G i ≃ₗ[R] G' i) (he : forall i j h, e 
j ∘ₗ f i j h = f' i j h ∘ₗ e i) {i : ι} (g : G' i) : (congr e he).symm (of _ _ G
' f' i g) = of _ _ G f i ((e i).symm g)
参数：e : (i : ι) -> G i ≃ₗ[R] G' i；he : forall i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ
 e i；g : G' i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DirectLimit.map_apply_of`：∀ {R : Type u_1} [inst : Semiring R] {ι
 : Type u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → AddC
ommMonoid (G i)] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.toLinearMap_symm_comp_eq`：toLinearMap_symm_comp_eq (f : M₃ -
>ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂) : e₁₂.symm.toLinearMap.comp g = f ↔ g = e₁₂.t
oLinearMap.comp f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearEquiv.comp_coe`：comp_coe (f : M₁ ≃ₛₗ[σ₁₂] M₂) (f' : M₂ ≃ₛₗ[σ₂₃] M₃
) : (f' : M₂ ->ₛₗ[σ₂₃] M₃).comp (f : M₁ ->ₛₗ[σ₁₂] M₂) = (f.trans f' : M₁ ≃ₛₗ[σ₁₃
] M₃)
· 使用定理 `LinearEquiv.symm_trans_self`：symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.sy
mm.trans f = LinearEquiv.refl R₂ M₂
· 使用定理 `LinearEquiv.refl_toLinearMap`：refl_toLinearMap [Module R M] : (LinearEqu
iv.refl R M : M ->ₗ[R] M) = LinearMap.id
· 使用定理 `LinearMap.comp_id`：comp_id : f.comp id = f
-/
lemma congr_symm_apply_of (e : (i : ι) → G i ≃ₗ[R] G' i)
    (he : ∀ i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i) {i : ι} (g : G' i) :
    (congr e he).symm (of _ _ G' f' i g) = of _ _ G f i ((e i).symm g) :=
  map_apply_of _ (fun i j h ↦ by
    rw [toLinearMap_symm_comp_eq, ← comp_assoc, he i, comp_assoc, comp_coe, symm_trans_self,
      refl_toLinearMap, comp_id]) _

end functorial

end Basic

section equiv

variable [Nonempty ι] [IsDirectedOrder ι] [DirectedSystem G (f · · ·)]
open _root_.DirectLimit

/-- The direct limit constructed as a quotient of the direct sum is isomorphic to
the direct limit constructed as a quotient of the disjoint union. -/
/-
**Module.DirectLimit.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Module.DirectLimit`。
形式化陈述：linearEquiv : DirectLimit G f ≃ₗ[R] _root_.DirectLimit G f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DirectLimit.of_f`：of_f {i j hij x} : of R ι G f j (f i j hij x) =
 of R ι G f i x

--- 原说明 ---
The direct limit constructed as a quotient of the direct sum is isomorphic to
the direct limit constructed as a quotient of the disjoint union.
-/
def linearEquiv : DirectLimit G f ≃ₗ[R] _root_.DirectLimit G f :=
  .ofLinearMap
    (lift _ _ _ _ (Module.of _ _ _ _) fun _ _ _ _ ↦ .symm <| eq_of_le ..)
    (Module.lift _ _ _ _ (of _ _ _ _) fun _ _ _ _ ↦ of_f ..)
    (by ext; simp)
    (by ext; simp)

@[simp]
/-
**Module.DirectLimit.linearEquiv_of** 是 Mathlib 中的一个定理，位于命名空间 `Module.DirectLimi
t`。
形式化陈述：linearEquiv_of {i g} : linearEquiv _ _ (of _ _ G f i g) = ⟦⟨i, g⟩⟧
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.DirectLimit.lift_of`：∀ {R : Type u_1} [inst : Semiring R] {ι : Ty
pe u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → AddCommMo
noid (G i)] [ins…
· 使用定理 `DirectLimit.Module.of_apply`：∀ (R : Type u_1) (ι : Type u_2) [inst : Pre
order ι] (G : ι → Type u_3) {T : ⦃i j : ι⦄ → i ≤ j → Type u_6}   (f : (x x_1 : ι
) → (h : x ≤ x_1)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearEquiv_of {i g} : linearEquiv _ _ (of _ _ G f i g) = ⟦⟨i, g⟩⟧ := by
  simp [linearEquiv]

@[simp]
/-
**Module.DirectLimit.linearEquiv_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `Module.Direc
tLimit`。
形式化陈述：linearEquiv_symm_mk {g} : (linearEquiv _ _).symm ⟦g⟧ = of _ _ G f g.1 g.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem linearEquiv_symm_mk {g} : (linearEquiv _ _).symm ⟦g⟧ = of _ _ G f g.1 g.2 := rfl

end equiv

variable {G f} [DirectedSystem G (f · · ·)] [IsDirectedOrder ι]

/-
**Module.DirectLimit.exists_eq_of_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Module.Direct
Limit`。
形式化陈述：exists_eq_of_of_eq {i x y} (h : of R ι G f i x = of R ι G f i y) : exists 
j hij, f i j hij x = f i j hij y
参数：h : of R ι G f i x = of R ι G f i y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.DirectLimit.linearEquiv_of`：linearEquiv_of {i g} : linearEquiv _ 
_ (of _ _ G f i g) = ⟦⟨i, g⟩⟧
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_eq_of_of_eq {i x y} (h : of R ι G f i x = of R ι G f i y) :
    ∃ j hij, f i j hij x = f i j hij y := by
  have := Nonempty.intro i
  apply_fun linearEquiv _ _ at h
  simp_rw [linearEquiv_of] at h
  have ⟨j, h⟩ := Quotient.exact h
  exact ⟨j, h.1, h.2.2⟩

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
/-
**Module.DirectLimit.of.zero_exact** 是 Mathlib 中的一个定理，位于命名空间 `Module.DirectLimit
.of`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {ι : Type u_2} [inst_1 : Preorder ι] 
{G : ι → Type u_3}   [inst_2 : (i : ι) → AddCommMonoid (G i)] [inst_3 : (i : ι) 
→ _root_.Module R (G i)]   {f : (i j : ι) → i ≤ j → G i →ₗ[R] G j} [inst_4 : Dec
idableEq ι] [DirectedSystem G fun x1 x2 x3 => ⇑(f x1 x2 x3)]   [IsDirectedOrder 
ι] {i : ι} {x : G i},   (Module.DirectLimit.of R ι G f i) x = 0 → ∃ j, ∃ (hij : 
i ≤ j), (f i j hij) x = 0
参数：i : ι；G i；i : ι；G i；i j : ι；f x1 x2 x3；Module.DirectLimit.of R ι G f i；hij : 
i ≤ j；f i j hij。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Module.DirectLimit.exists_eq_of_of_eq`：exists_eq_of_of_eq {i x y} (h : o
f R ι G f i x = of R ι G f i y) : exists j hij, f i j hij x = f i j hij y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system.
-/
theorem of.zero_exact {i x} (H : of R ι G f i x = 0) :
    ∃ j hij, f i j hij x = (0 : G j) := by
  convert! exists_eq_of_of_eq (H.trans (map_zero <| _).symm)
  rw [map_zero]

end DirectLimit

end Module

namespace AddCommGroup

variable (G) [∀ i, AddCommMonoid (G i)]

/-- The direct limit of a directed system is the abelian groups glued together along the maps. -/
/-
**AddCommGroup.DirectLimit** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGroup`。
形式化陈述：DirectLimit [DecidableEq ι] (f : forall i j, i <= j -> G i ->+ G j) : Type
 _
参数：f : forall i j, i <= j -> G i ->+ G j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The direct limit of a directed system is the abelian groups glued together along
 the maps.
-/
def DirectLimit [DecidableEq ι] (f : ∀ i j, i ≤ j → G i →+ G j) : Type _ :=
  @Module.DirectLimit ℕ _ ι _ G _ _ (fun i j hij ↦ (f i j hij).toNatLinearMap) _
deriving AddCommMonoid, Inhabited

namespace DirectLimit

variable (f : ∀ i j, i ≤ j → G i →+ G j)

local instance directedSystem [h : DirectedSystem G fun i j h ↦ f i j h] :
    DirectedSystem G fun i j hij ↦ (f i j hij).toNatLinearMap :=
  h

variable [DecidableEq ι]

/-
**AddCommGroup.DirectLimit.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGroup.
DirectLimit`。
形式化陈述：addCommGroup (G : ι -> Type*) [forall i, AddCommGroup (G i)] (f : forall i
 j, i <= j -> G i ->+ G j) : AddCommGroup (DirectLimit G f)
参数：G : ι -> Type*；G i；f : forall i j, i <= j -> G i ->+ G j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroup (G : ι → Type*) [∀ i, AddCommGroup (G i)]
    (f : ∀ i j, i ≤ j → G i →+ G j) : AddCommGroup (DirectLimit G f) :=
  inferInstanceAs <| AddCommGroup (Module.DirectLimit G _)
/-
**AddCommGroup.DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGroup.DirectLimit`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty ι] : Unique (DirectLimit G f) :=
  inferInstanceAs <| Unique (Module.DirectLimit G _)

/-- The canonical map from a component to the direct limit. -/
/-
**AddCommGroup.DirectLimit.of** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGroup.DirectLimi
t`。
形式化陈述：of (i) : G i ->+ DirectLimit G f
参数：i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from a component to the direct limit.
-/
def of (i) : G i →+ DirectLimit G f :=
  (Module.DirectLimit.of ℕ ι G _ i).toAddMonoidHom

variable {G f}

@[simp]
/-
**AddCommGroup.DirectLimit.of_f** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.DirectLi
mit`。
形式化陈述：of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x
参数：hij；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DirectLimit.of_f`：of_f {i j hij x} : of R ι G f j (f i j hij x) =
 of R ι G f i x
-/
theorem of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x :=
  Module.DirectLimit.of_f

@[elab_as_elim]
/-
**AddCommGroup.DirectLimit.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.
DirectLimit`。
形式化陈述：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι → Type u_3} [inst_1 : (i : ι) 
→ AddCommMonoid (G i)]   {f : (i j : ι) → i ≤ j → G i →+ G j} [inst_2 : Decidabl
eEq ι] [Nonempty ι] [IsDirectedOrder ι]   {C : AddCommGroup.DirectLimit G f → Pr
op} (z : AddCommGroup.DirectLimit G f),   (∀ (i : ι) (x : G i), C ((AddCommGroup
.DirectLimit.of G f i) x)) → C z
参数：i : ι；G i；i j : ι；z : AddCommGroup.DirectLimit G f；∀ (i : ι) (x : G i), C ((A
ddCommGroup.DirectLimit.of G f i) x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DirectLimit.induction_on`：∀ {R : Type u_1} [inst : Semiring R] {ι
 : Type u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → AddC
ommMonoid (G i)] [ins…
-/
protected theorem induction_on [Nonempty ι] [IsDirectedOrder ι] {C : DirectLimit G f → Prop}
    (z : DirectLimit G f) (ih : ∀ i x, C (of G f i x)) : C z :=
  Module.DirectLimit.induction_on z ih

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
/-
**AddCommGroup.DirectLimit.of.zero_exact** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup
.DirectLimit.of`。
形式化陈述：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι → Type u_3} [inst_1 : (i : ι) 
→ AddCommMonoid (G i)]   {f : (i j : ι) → i ≤ j → G i →+ G j} [inst_2 : Decidabl
eEq ι] [IsDirectedOrder ι]   [DirectedSystem G fun i j h => ⇑(f i j h)] (i : ι) 
(x : G i),   (AddCommGroup.DirectLimit.of G f i) x = 0 → ∃ j, ∃ (hij : i ≤ j), (
f i j hij) x = 0
参数：i : ι；G i；i j : ι；f i j h；i : ι；x : G i；AddCommGroup.DirectLimit.of G f i；hij
 : i ≤ j；f i j hij。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DirectLimit.of.zero_exact`：∀ {R : Type u_1} [inst : Semiring R] {
ι : Type u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → Add
CommMonoid (G i)] [ins…
· 使用定理 `AddCommGroup.DirectLimit.directedSystem`：∀ {ι : Type u_2} [inst : Preord
er ι] (G : ι → Type u_3) [inst_1 : (i : ι) → AddCommMonoid (G i)]   (f : (i j : 
ι) → i ≤ j → G i →+ G j) [h :…

--- 原说明 ---
A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system.
-/
theorem of.zero_exact [IsDirectedOrder ι] [DirectedSystem G fun i j h ↦ f i j h] (i x)
    (h : of G f i x = 0) : ∃ j hij, f i j hij x = 0 :=
  Module.DirectLimit.of.zero_exact h

variable (P : Type*) [AddCommMonoid P]
variable (g : ∀ i, G i →+ P)
variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
variable (G f)

/-- The universal property of the direct limit: maps from the components to another abelian group
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
/-
**AddCommGroup.DirectLimit.lift** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGroup.DirectLi
mit`。
形式化陈述：lift : DirectLimit G f ->+ P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of the direct limit: maps from the components to another 
abelian group
that respect the directed system structure (i.e. make some diagram commute) give
 rise
to a unique map out of the direct limit.
-/
def lift : DirectLimit G f →+ P :=
  (Module.DirectLimit.lift ℕ ι G (fun i j hij ↦ (f i j hij).toNatLinearMap)
    (fun i ↦ (g i).toNatLinearMap) Hg).toAddMonoidHom

variable {G f}

@[simp]
/-
**AddCommGroup.DirectLimit.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.Direc
tLimit`。
形式化陈述：lift_of (i x) : lift G f P g Hg (of G f i x) = g i x
参数：i x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DirectLimit.lift_of`：∀ {R : Type u_1} [inst : Semiring R] {ι : Ty
pe u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → AddCommMo
noid (G i)] [ins…
-/
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x :=
  Module.DirectLimit.lift_of
    -- Note: had to make these arguments explicit https://github.com/leanprover-community/mathlib4/pull/8386
    (f := fun i j hij ↦ (f i j hij).toNatLinearMap)
    (fun i ↦ (g i).toNatLinearMap)
    Hg
    x

@[ext]
/-
**AddCommGroup.DirectLimit.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.Direc
tLimit`。
形式化陈述：hom_ext {g₁ g₂ : DirectLimit G f ->+ P} (h : forall i, g₁.comp (of G f i) 
= g₂.comp (of G f i)) : g₁ = g₂
参数：h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.hom_ext`：∀ {M : Type u_1} {P : Type u_3} [inst : AddZeroClass M] 
[inst_1 : AddZeroClass P] {c : AddCon M}   {f g : c.Quotient →+ P}, f.comp c.mk'
 = g…
· 使用定理 `DirectSum.addHom_ext'`：addHom_ext' {γ : Type*} [AddZeroClass γ] ⦃f g : (
⨁ i, β i) ->+ γ⦄ (H : forall i : ι, f.comp (of _ i) = g.comp (of _ i)) : f = g
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f →+ P} (h : ∀ i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ :=
  AddCon.hom_ext <| DirectSum.addHom_ext' h

@[simp]
/-
**AddCommGroup.DirectLimit.lift_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.
DirectLimit`。
形式化陈述：lift_comp_of (F : DirectLimit G f ->+ P) : lift G f _ (fun i => F.comp <| 
of G f i) (fun i j hij x => by simp) = F
参数：F : DirectLimit G f ->+ P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.DirectLimit.hom_ext`：hom_ext {g₁ g₂ : DirectLimit G f ->+ P
} (h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)) : g₁ = g₂
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.DirectLimit.lift_of`：lift_of (i x) : lift G f P g Hg (of G 
f i x) = g i x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_comp_of (F : DirectLimit G f →+ P) :
    lift G f _ (fun i ↦ F.comp <| of G f i) (fun i j hij x ↦ by simp) = F := by
  ext; simp

@[simp]
/-
**AddCommGroup.DirectLimit.lift_of'** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.Dire
ctLimit`。
形式化陈述：lift_of' : lift G f _ (of G f) (fun i j hij x => by simp) = .id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.DirectLimit.hom_ext`：hom_ext {g₁ g₂ : DirectLimit G f ->+ P
} (h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)) : g₁ = g₂
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.DirectLimit.lift_of`：lift_of (i x) : lift G f P g Hg (of G 
f i x) = g i x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddMonoidHom.id_comp`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N), (AddMonoidHom.id N).comp f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_of' : lift G f _ (of G f) (fun i j hij x ↦ by simp) = .id _ := by
  ext; simp
/-
**AddCommGroup.DirectLimit.lift_injective** 是 Mathlib 中的一个引理，位于命名空间 `AddCommGrou
p.DirectLimit`。
形式化陈述：lift_injective [IsDirectedOrder ι] (injective : forall i, Function.Injecti
ve <| g i) : Function.Injective (lift G f P g Hg)
参数：injective : forall i, Function.Injective <| g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.DirectLimit.lift_injective`：lift_injective [IsDirectedOrder ι] (i
njective : forall i, Function.Injective <| g i) : Function.Injective (lift R ι G
 f g Hg)
-/
lemma lift_injective [IsDirectedOrder ι]
    (injective : ∀ i, Function.Injective <| g i) :
    Function.Injective (lift G f P g Hg) :=
  Module.DirectLimit.lift_injective (f := fun i j hij ↦ (f i j hij).toNatLinearMap) _ Hg injective

section functorial

variable {G' : ι → Type*} [∀ i, AddCommMonoid (G' i)]
variable {f' : ∀ i j, i ≤ j → G' i →+ G' j}
variable {G'' : ι → Type*} [∀ i, AddCommMonoid (G'' i)]
variable {f'' : ∀ i j, i ≤ j → G'' i →+ G'' j}

/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of group homomorphisms `gᵢ : Gᵢ ⟶ G'ᵢ` such that `g ∘ f = f' ∘ g` induces a group
homomorphism `lim G ⟶ lim G'`.
-/
/-
**AddCommGroup.DirectLimit.map** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGroup.DirectLim
it`。
形式化陈述：map (g : (i : ι) -> G i ->+ G' i) (hg : forall i j h, (g j).comp (f i j h)
 = (f' i j h).comp (g i)) : DirectLimit G f ->+ DirectLimit G' f'
参数：g : (i : ι) -> G i ->+ G' i；hg : forall i j h, (g j).comp (f i j h) = (f' i j
 h).comp (g i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` resp
ectively, any
family of group homomorphisms `gᵢ : Gᵢ ⟶ G'ᵢ` such that `g ∘ f = f' ∘ g` induces
 a group
homomorphism `lim G ⟶ lim G'`.
-/
def map (g : (i : ι) → G i →+ G' i)
    (hg : ∀ i j h, (g j).comp (f i j h) = (f' i j h).comp (g i)) :
    DirectLimit G f →+ DirectLimit G' f' :=
  lift _ _ _ (fun i ↦ (of _ _ _).comp (g i)) fun i j h g ↦ by
    have eq1 := DFunLike.congr_fun (hg i j h) g
    simp only [AddMonoidHom.coe_comp, Function.comp_apply] at eq1 ⊢
    rw [eq1, of_f]
/-
**AddCommGroup.DirectLimit.map_apply_of** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.
DirectLimit`。
形式化陈述：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι → Type u_3} [inst_1 : (i : ι) 
→ AddCommMonoid (G i)]   {f : (i j : ι) → i ≤ j → G i →+ G j} [inst_2 : Decidabl
eEq ι] {G' : ι → Type u_5}   [inst_3 : (i : ι) → AddCommMonoid (G' i)] {f' : (i 
j : ι) → i ≤ j → G' i →+ G' j} (g : (i : ι) → G i →+ G' i)   (hg : ∀ (i j : ι) (
h : i ≤ j), (g j).comp (f i j h) = (f' i j h).comp (g i)) {i : ι} (x : G i),   (
AddCommGroup.DirectLimit.map g hg) ((AddCommGroup.DirectLimit.of G f i) x) =    
 (AddCommGroup.DirectLimit.of G' f' i) ((g i) x)
参数：i : ι；G i；i j : ι；i : ι；G' i；i j : ι；g : (i : ι) → G i →+ G' i；hg : ∀ (i j : 
ι) (h : i ≤ j), (g j).comp (f i j h) = (f' i j h).comp (g i)；x : G i；AddCommGrou
p.DirectLimit.map g hg；(AddCommGroup.DirectLimit.of G f i) x；AddCommGroup.Direct
Limit.of G' f' i；(g i) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.DirectLimit.lift_of`：lift_of (i x) : lift G f P g Hg (of G 
f i x) = g i x
-/
@[simp] lemma map_apply_of (g : (i : ι) → G i →+ G' i)
    (hg : ∀ i j h, (g j).comp (f i j h) = (f' i j h).comp (g i))
    {i : ι} (x : G i) :
    map g hg (of G f _ x) = of G' f' i (g i x) :=
  lift_of _ _ _ _ _
/-
**AddCommGroup.DirectLimit.map_id** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.Direct
Limit`。
形式化陈述：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι → Type u_3} [inst_1 : (i : ι) 
→ AddCommMonoid (G i)]   {f : (i j : ι) → i ≤ j → G i →+ G j} [inst_2 : Decidabl
eEq ι],   AddCommGroup.DirectLimit.map (fun x => AddMonoidHom.id (G x)) ⋯ = AddM
onoidHom.id (AddCommGroup.DirectLimit G f)
参数：i : ι；G i；i j : ι；fun x => AddMonoidHom.id (G x)；AddCommGroup.DirectLimit G f
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.DirectLimit.hom_ext`：hom_ext {g₁ g₂ : DirectLimit G f ->+ P
} (h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)) : g₁ = g₂
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.DirectLimit.map_apply_of`：∀ {ι : Type u_2} [inst : Preorder
 ι] {G : ι → Type u_3} [inst_1 : (i : ι) → AddCommMonoid (G i)]   {f : (i j : ι)
 → i ≤ j → G i →+ G j} [ins…
· 使用定理 `AddMonoidHom.id_apply`：∀ (M : Type u_10) [inst : AddZero M] (x : M), (Ad
dMonoidHom.id M) x = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddMonoidHom.id_comp`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N), (AddMonoidHom.id N).comp f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_id :
    map (fun _ ↦ AddMonoidHom.id _) (fun _ _ _ ↦ rfl) = AddMonoidHom.id (DirectLimit G f) := by
  ext; simp
/-
**AddCommGroup.DirectLimit.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `AddCommGroup.Dire
ctLimit`。
形式化陈述：map_comp (g₁ : (i : ι) -> G i ->+ G' i) (g₂ : (i : ι) -> G' i ->+ G'' i) (
hg₁ : forall i j h, (g₁ j).comp (f i j h) = (f' i j h).comp (g₁ i)) (hg₂ : foral
l i j h, (g₂ j).comp (f' i j h) = (f'' i j h).comp (g₂ i)) : ((map g₂ hg₂).comp 
(map g₁ hg₁) : DirectLimit G f ->+ DirectLimit G'' f'') = (map (fun i => (g₂ i).
comp (g₁ i)) fun i j h => by rw [AddMonoidHom.comp_assoc]; rw [hg₁ i]; rw [← Add
MonoidHom.comp_assoc]; rw [hg₂ i]; rw [AddMonoidHom.comp_assoc] : DirectLimit G 
f ->+ DirectLimit G'' f'')
参数：g₁ : (i : ι) -> G i ->+ G' i；g₂ : (i : ι) -> G' i ->+ G'' i；hg₁ : forall i j 
h, (g₁ j).comp (f i j h) = (f' i j h).comp (g₁ i)；hg₂ : forall i j h, (g₂ j).com
p (f' i j h) = (f'' i j h).comp (g₂ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.DirectLimit.hom_ext`：hom_ext {g₁ g₂ : DirectLimit G f ->+ P
} (h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)) : g₁ = g₂
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.DirectLimit.map_apply_of`：∀ {ι : Type u_2} [inst : Preorder
 ι] {G : ι → Type u_3} [inst_1 : (i : ι) → AddCommMonoid (G i)]   {f : (i j : ι)
 → i ≤ j → G i →+ G j} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp (g₁ : (i : ι) → G i →+ G' i) (g₂ : (i : ι) → G' i →+ G'' i)
    (hg₁ : ∀ i j h, (g₁ j).comp (f i j h) = (f' i j h).comp (g₁ i))
    (hg₂ : ∀ i j h, (g₂ j).comp (f' i j h) = (f'' i j h).comp (g₂ i)) :
    ((map g₂ hg₂).comp (map g₁ hg₁) :
      DirectLimit G f →+ DirectLimit G'' f'') =
    (map (fun i ↦ (g₂ i).comp (g₁ i)) fun i j h ↦ by
      rw [AddMonoidHom.comp_assoc, hg₁ i, ← AddMonoidHom.comp_assoc, hg₂ i,
        AddMonoidHom.comp_assoc] :
      DirectLimit G f →+ DirectLimit G'' f'') := by
  ext; simp

set_option backward.isDefEq.respectTransparency.types false in
/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of equivalences `eᵢ : Gᵢ ≅ G'ᵢ` such that `e ∘ f = f' ∘ e` induces an equivalence
`lim G ⟶ lim G'`.
-/
/-
**AddCommGroup.DirectLimit.congr** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGroup.DirectL
imit`。
形式化陈述：congr (e : (i : ι) -> G i ≃+ G' i) (he : forall i j h, (e j).toAddMonoidHo
m.comp (f i j h) = (f' i j h).comp (e i)) : DirectLimit G f ≃+ DirectLimit G' f'
参数：e : (i : ι) -> G i ≃+ G' i；he : forall i j h, (e j).toAddMonoidHom.comp (f i 
j h) = (f' i j h).comp (e i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` resp
ectively, any
family of equivalences `eᵢ : Gᵢ ≅ G'ᵢ` such that `e ∘ f = f' ∘ e` induces an equ
ivalence
`lim G ⟶ lim G'`.
-/
def congr (e : (i : ι) → G i ≃+ G' i)
    (he : ∀ i j h, (e j).toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i)) :
    DirectLimit G f ≃+ DirectLimit G' f' :=
  AddMonoidHom.toAddEquiv (map (e ·) he)
    (map (fun i ↦ (e i).symm) fun i j h ↦ DFunLike.ext _ _ fun x ↦ by
      have eq1 := DFunLike.congr_fun (he i j h) ((e i).symm x)
      simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply,
        AddMonoidHom.coe_coe, AddEquiv.apply_symm_apply] at eq1 ⊢
      simp [← eq1])
    (by simp [map_comp]) (by simp [map_comp])

set_option backward.isDefEq.respectTransparency.types false in
/-
**AddCommGroup.DirectLimit.congr_apply_of** 是 Mathlib 中的一个引理，位于命名空间 `AddCommGrou
p.DirectLimit`。
形式化陈述：congr_apply_of (e : (i : ι) -> G i ≃+ G' i) (he : forall i j h, (e j).toAd
dMonoidHom.comp (f i j h) = (f' i j h).comp (e i)) {i : ι} (g : G i) : congr e h
e (of G f i g) = of G' f' i (e i g)
参数：e : (i : ι) -> G i ≃+ G' i；he : forall i j h, (e j).toAddMonoidHom.comp (f i 
j h) = (f' i j h).comp (e i)；g : G i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `AddCommGroup.DirectLimit.map_apply_of`：∀ {ι : Type u_2} [inst : Preorder
 ι] {G : ι → Type u_3} [inst_1 : (i : ι) → AddCommMonoid (G i)]   {f : (i j : ι)
 → i ≤ j → G i →+ G j} [ins…
-/
lemma congr_apply_of (e : (i : ι) → G i ≃+ G' i)
    (he : ∀ i j h, (e j).toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G i) :
    congr e he (of G f i g) = of G' f' i (e i g) :=
  map_apply_of _ he _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AddCommGroup.DirectLimit.congr_symm_apply_of** 是 Mathlib 中的一个引理，位于命名空间 `AddCom
mGroup.DirectLimit`。
形式化陈述：congr_symm_apply_of (e : (i : ι) -> G i ≃+ G' i) (he : forall i j h, (e j)
.toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i)) {i : ι} (g : G' i) : (co
ngr e he).symm (of G' f' i g) = of G f i ((e i).symm g)
参数：e : (i : ι) -> G i ≃+ G' i；he : forall i j h, (e j).toAddMonoidHom.comp (f i 
j h) = (f' i j h).comp (e i)；g : G' i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AddMonoidHom.toAddEquiv_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZeroClass M] [inst_1 : AddZeroClass N] (f : M →+ N) (g : N →+ M)   (h₁ : 
g.comp f = AddMonoidHom.…
· 使用定理 `AddCommGroup.DirectLimit.map_apply_of`：∀ {ι : Type u_2} [inst : Preorder
 ι] {G : ι → Type u_3} [inst_1 : (i : ι) → AddCommMonoid (G i)]   {f : (i j : ι)
 → i ≤ j → G i →+ G j} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma congr_symm_apply_of (e : (i : ι) → G i ≃+ G' i)
    (he : ∀ i j h, (e j).toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G' i) :
    (congr e he).symm (of G' f' i g) = of G f i ((e i).symm g) := by
  simp only [congr, AddMonoidHom.toAddEquiv_symm_apply, map_apply_of, AddMonoidHom.coe_coe]

end functorial

end DirectLimit

end AddCommGroup

