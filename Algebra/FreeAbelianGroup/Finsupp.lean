/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.End
public import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# Isomorphism between `FreeAbelianGroup X` and `X →₀ ℤ`

In this file we construct the canonical isomorphism between `FreeAbelianGroup X` and `X →₀ ℤ`.
We use this to transport the notion of `support` from `Finsupp` to `FreeAbelianGroup`.

## Main declarations

- `FreeAbelianGroup.equivFinsupp`: group isomorphism between `FreeAbelianGroup X` and `X →₀ ℤ`
- `FreeAbelianGroup.coeff`: the multiplicity of `x : X` in `a : FreeAbelianGroup X`
- `FreeAbelianGroup.support`: the finset of `x : X` that occur in `a : FreeAbelianGroup X`
-/

@[expose] public section

assert_not_exists Cardinal Module.Basis

noncomputable section

variable {X : Type*}

/-- The group homomorphism `FreeAbelianGroup X →+ (X →₀ ℤ)`. -/
/-
**FreeAbelianGroup.toFinsupp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FreeAbelianGroup.toFinsupp : FreeAbelianGroup X ->+ X ->₀ Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group homomorphism `FreeAbelianGroup X →+ (X →₀ ℤ)`.
-/
def FreeAbelianGroup.toFinsupp : FreeAbelianGroup X →+ X →₀ ℤ :=
  FreeAbelianGroup.lift fun x => Finsupp.single x (1 : ℤ)

/-- The group homomorphism `(X →₀ ℤ) →+ FreeAbelianGroup X`. -/
/-
**Finsupp.toFreeAbelianGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Finsupp.toFreeAbelianGroup : (X ->₀ Int) ->+ FreeAbelianGroup X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group homomorphism `(X →₀ ℤ) →+ FreeAbelianGroup X`.
-/
def Finsupp.toFreeAbelianGroup : (X →₀ ℤ) →+ FreeAbelianGroup X :=
  Finsupp.liftAddHom fun x => (smulAddHom ℤ (FreeAbelianGroup X)).flip (FreeAbelianGroup.of x)
/-
**FreeAbelianGroup.toFinsupp_of** 是 Mathlib 中的一个定理，位于命名空间 `FreeAbelianGroup`。
形式化陈述：∀ {X : Type u_1} (x : X), FreeAbelianGroup.toFinsupp (FreeAbelianGroup.of 
x) = fun₀ | x => 1
参数：x : X；FreeAbelianGroup.of x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeAbelianGroup.lift_apply_of`：lift_apply_of (x : α) : lift f (of x) = 
f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma FreeAbelianGroup.toFinsupp_of (x : X) : toFinsupp (of x) = .single x 1 := by
  simp [toFinsupp]
/-
**Finsupp.toFreeAbelianGroup_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {X : Type u_1} (x : X) (n : ℤ), (Finsupp.toFreeAbelianGroup fun₀ | x => 
n) = n • FreeAbelianGroup.of x
参数：x : X；n : ℤ；Finsupp.toFreeAbelianGroup fun₀ | x => n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma Finsupp.toFreeAbelianGroup_single (x : X) (n : ℤ) :
    toFreeAbelianGroup (single x n) = n • .of x := by simp [toFreeAbelianGroup]

open Finsupp FreeAbelianGroup

@[simp]
/-
**Finsupp.toFreeAbelianGroup_comp_singleAddHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finsupp.toFreeAbelianGroup_comp_singleAddHom (x : X) : Finsupp.toFreeAbeli
anGroup.comp (Finsupp.singleAddHom x) = (smulAddHom Int (FreeAbelianGroup X)).fl
ip (of x)
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Finsupp.toFreeAbelianGroup_single`：∀ {X : Type u_1} (x : X) (n : ℤ), (Fi
nsupp.toFreeAbelianGroup fun₀ | x => n) = n • FreeAbelianGroup.of x
-/
theorem Finsupp.toFreeAbelianGroup_comp_singleAddHom (x : X) :
    Finsupp.toFreeAbelianGroup.comp (Finsupp.singleAddHom x) =
      (smulAddHom ℤ (FreeAbelianGroup X)).flip (of x) :=
  AddMonoidHom.ext <| toFreeAbelianGroup_single _

@[simp]
/-
**FreeAbelianGroup.toFinsupp_comp_toFreeAbelianGroup** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：FreeAbelianGroup.toFinsupp_comp_toFreeAbelianGroup : toFinsupp.comp toFree
AbelianGroup = AddMonoidHom.id (X ->₀ Int)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.addHom_ext'`：addHom_ext' [AddZeroClass N] ⦃f g : (α ->₀ M) ->+ N
⦄ (H : forall x, f.comp (singleAddHom x) = g.comp (singleAddHom x)) : f = g
· 使用定理 `AddMonoidHom.ext_int`：ext_int [AddMonoid A] {f g : Int ->+ A} (h1 : f 1 
= g 1) : f = g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.singleAddHom_apply`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZ
eroClass M] (a : ι) (b : M), (Finsupp.singleAddHom a) b = fun₀ | a => b
· 使用定理 `Finsupp.toFreeAbelianGroup_single`：∀ {X : Type u_1} (x : X) (n : ℤ), (Fi
nsupp.toFreeAbelianGroup fun₀ | x => n) = n • FreeAbelianGroup.of x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `FreeAbelianGroup.toFinsupp_of`：∀ {X : Type u_1} (x : X), FreeAbelianGrou
p.toFinsupp (FreeAbelianGroup.of x) = fun₀ | x => 1
· 使用定理 `AddMonoidHom.id_comp`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N), (AddMonoidHom.id N).comp f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem FreeAbelianGroup.toFinsupp_comp_toFreeAbelianGroup :
    toFinsupp.comp toFreeAbelianGroup = AddMonoidHom.id (X →₀ ℤ) := by
  ext
  simp

@[simp]
/-
**Finsupp.toFreeAbelianGroup_comp_toFinsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finsupp.toFreeAbelianGroup_comp_toFinsupp : toFreeAbelianGroup.comp toFins
upp = AddMonoidHom.id (FreeAbelianGroup X)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeAbelianGroup.lift_ext`：lift_ext (g h : FreeAbelianGroup α ->+ β) (H 
: forall x, g (of x) = h (of x)) : g = h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.toFreeAbelianGroup.eq_1`：∀ {X : Type u_1},   Finsupp.toFreeAbeli
anGroup =     Finsupp.liftAddHom fun x => (smulAddHom ℤ (FreeAbelianGroup X)).fl
ip (FreeAbelianGroup.…
· 使用定理 `FreeAbelianGroup.toFinsupp.eq_1`：∀ {X : Type u_1}, FreeAbelianGroup.toFi
nsupp = FreeAbelianGroup.lift fun x => fun₀ | x => 1
· 使用定理 `AddMonoidHom.comp_apply`：∀ {M : Type u_4} {N : Type u_5} {P : Type u_6} 
[inst : AddZero M] [inst_1 : AddZero N] [inst_2 : AddZero P] (g : N →+ P)   (f :
 M →+ N) (x :…
· 使用定理 `FreeAbelianGroup.lift_apply_of`：lift_apply_of (x : α) : lift f (of x) = 
f x
· 使用定理 `Finsupp.liftAddHom_apply_single`：liftAddHom_apply_single [AddZeroClass M
] [AddCommMonoid N] (f : α -> M ->+ N) (a : α) (b : M) : (liftAddHom (α
· 使用定理 `AddMonoidHom.flip_apply`：∀ {M : Type uM} {N : Type uN} {P : Type uP} {x 
: AddZeroClass M} {x_1 : AddZeroClass N} {x_2 : AddCommMonoid P}   (f : M →+ N →
+ P) (x_3 : M…
· 使用定理 `smulAddHom_apply`：smulAddHom_apply : smulAddHom R M r x = r • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `AddMonoidHom.id_apply`：∀ (M : Type u_10) [inst : AddZero M] (x : M), (Ad
dMonoidHom.id M) x = x
-/
theorem Finsupp.toFreeAbelianGroup_comp_toFinsupp :
    toFreeAbelianGroup.comp toFinsupp = AddMonoidHom.id (FreeAbelianGroup X) := by
  ext
  rw [toFreeAbelianGroup, toFinsupp, AddMonoidHom.comp_apply, lift_apply_of,
    liftAddHom_apply_single, AddMonoidHom.flip_apply, smulAddHom_apply, one_smul,
    AddMonoidHom.id_apply]

@[simp]
/-
**Finsupp.toFreeAbelianGroup_toFinsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finsupp.toFreeAbelianGroup_toFinsupp {X} (x : FreeAbelianGroup X) : Finsup
p.toFreeAbelianGroup (FreeAbelianGroup.toFinsupp x) = x
参数：x : FreeAbelianGroup X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidHom.comp_apply`：∀ {M : Type u_4} {N : Type u_5} {P : Type u_6} 
[inst : AddZero M] [inst_1 : AddZero N] [inst_2 : AddZero P] (g : N →+ P)   (f :
 M →+ N) (x :…
· 使用定理 `Finsupp.toFreeAbelianGroup_comp_toFinsupp`：Finsupp.toFreeAbelianGroup_co
mp_toFinsupp : toFreeAbelianGroup.comp toFinsupp = AddMonoidHom.id (FreeAbelianG
roup X)
· 使用定理 `AddMonoidHom.id_apply`：∀ (M : Type u_10) [inst : AddZero M] (x : M), (Ad
dMonoidHom.id M) x = x
-/
theorem Finsupp.toFreeAbelianGroup_toFinsupp {X} (x : FreeAbelianGroup X) :
    Finsupp.toFreeAbelianGroup (FreeAbelianGroup.toFinsupp x) = x := by
  rw [← AddMonoidHom.comp_apply, Finsupp.toFreeAbelianGroup_comp_toFinsupp, AddMonoidHom.id_apply]

namespace FreeAbelianGroup

open Finsupp

@[simp]
/-
**FreeAbelianGroup.toFinsupp_toFreeAbelianGroup** 是 Mathlib 中的一个定理，位于命名空间 `FreeA
belianGroup`。
形式化陈述：toFinsupp_toFreeAbelianGroup (f : X ->₀ Int) : FreeAbelianGroup.toFinsupp 
(Finsupp.toFreeAbelianGroup f) = f
参数：f : X ->₀ Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidHom.comp_apply`：∀ {M : Type u_4} {N : Type u_5} {P : Type u_6} 
[inst : AddZero M] [inst_1 : AddZero N] [inst_2 : AddZero P] (g : N →+ P)   (f :
 M →+ N) (x :…
· 使用定理 `FreeAbelianGroup.toFinsupp_comp_toFreeAbelianGroup`：FreeAbelianGroup.toF
insupp_comp_toFreeAbelianGroup : toFinsupp.comp toFreeAbelianGroup = AddMonoidHo
m.id (X ->₀ Int)
· 使用定理 `AddMonoidHom.id_apply`：∀ (M : Type u_10) [inst : AddZero M] (x : M), (Ad
dMonoidHom.id M) x = x
-/
theorem toFinsupp_toFreeAbelianGroup (f : X →₀ ℤ) :
    FreeAbelianGroup.toFinsupp (Finsupp.toFreeAbelianGroup f) = f := by
  rw [← AddMonoidHom.comp_apply, toFinsupp_comp_toFreeAbelianGroup, AddMonoidHom.id_apply]

variable (X)

/-- The additive equivalence between `FreeAbelianGroup X` and `(X →₀ ℤ)`. -/
@[simps!]
/-
**FreeAbelianGroup.equivFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `FreeAbelianGroup`。
形式化陈述：equivFinsupp : FreeAbelianGroup X ≃+ (X ->₀ Int) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.toFreeAbelianGroup_toFinsupp`：Finsupp.toFreeAbelianGroup_toFinsu
pp {X} (x : FreeAbelianGroup X) : Finsupp.toFreeAbelianGroup (FreeAbelianGroup.t
oFinsupp x) = x
· 使用定理 `FreeAbelianGroup.toFinsupp_toFreeAbelianGroup`：toFinsupp_toFreeAbelianGr
oup (f : X ->₀ Int) : FreeAbelianGroup.toFinsupp (Finsupp.toFreeAbelianGroup f) 
= f

--- 原说明 ---
The additive equivalence between `FreeAbelianGroup X` and `(X →₀ ℤ)`.
-/
def equivFinsupp : FreeAbelianGroup X ≃+ (X →₀ ℤ) where
  toFun := toFinsupp
  invFun := toFreeAbelianGroup
  left_inv := toFreeAbelianGroup_toFinsupp
  right_inv := toFinsupp_toFreeAbelianGroup
  map_add' := toFinsupp.map_add

variable {X}

/-- `coeff x` is the additive group homomorphism `FreeAbelianGroup X →+ ℤ`
that sends `a` to the multiplicity of `x : X` in `a`. -/
/-
**FreeAbelianGroup.coeff** 是 Mathlib 中的一个定义，位于命名空间 `FreeAbelianGroup`。
形式化陈述：coeff (x : X) : FreeAbelianGroup X ->+ Int
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`coeff x` is the additive group homomorphism `FreeAbelianGroup X →+ ℤ`
that sends `a` to the multiplicity of `x : X` in `a`.
-/
def coeff (x : X) : FreeAbelianGroup X →+ ℤ :=
  (Finsupp.applyAddHom x).comp toFinsupp

/-- `support a` for `a : FreeAbelianGroup X` is the finite set of `x : X`
that occur in the formal sum `a`. -/
/-
**FreeAbelianGroup.support** 是 Mathlib 中的一个定义，位于命名空间 `FreeAbelianGroup`。
形式化陈述：support (a : FreeAbelianGroup X) : Finset X
参数：a : FreeAbelianGroup X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`support a` for `a : FreeAbelianGroup X` is the finite set of `x : X`
that occur in the formal sum `a`.
-/
def support (a : FreeAbelianGroup X) : Finset X :=
  a.toFinsupp.support

@[simp]
/-
**FreeAbelianGroup.mem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeAbelianGroup`。
形式化陈述：mem_support_iff (x : X) (a : FreeAbelianGroup X) : x in a.support ↔ coeff 
x a != 0
参数：x : X；a : FreeAbelianGroup X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeAbelianGroup.support.eq_1`：∀ {X : Type u_1} (a : FreeAbelianGroup X)
, a.support = (FreeAbelianGroup.toFinsupp a).support
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_support_iff (x : X) (a : FreeAbelianGroup X) : x ∈ a.support ↔ coeff x a ≠ 0 := by
  rw [support, Finsupp.mem_support_iff]
  exact Iff.rfl
/-
**FreeAbelianGroup.notMem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeAbelianGrou
p`。
形式化陈述：notMem_support_iff (x : X) (a : FreeAbelianGroup X) : x ∉ a.support ↔ coef
f x a = 0
参数：x : X；a : FreeAbelianGroup X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeAbelianGroup.support.eq_1`：∀ {X : Type u_1} (a : FreeAbelianGroup X)
, a.support = (FreeAbelianGroup.toFinsupp a).support
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem notMem_support_iff (x : X) (a : FreeAbelianGroup X) : x ∉ a.support ↔ coeff x a = 0 := by
  rw [support, Finsupp.notMem_support_iff]
  exact Iff.rfl

@[simp]
/-
**FreeAbelianGroup.support_zero** 是 Mathlib 中的一个定理，位于命名空间 `FreeAbelianGroup`。
形式化陈述：support_zero : support (0 : FreeAbelianGroup X) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem support_zero : support (0 : FreeAbelianGroup X) = ∅ := by
  simp only [support, Finsupp.support_zero, map_zero]

@[simp]
/-
**FreeAbelianGroup.support_of** 是 Mathlib 中的一个定理，位于命名空间 `FreeAbelianGroup`。
形式化陈述：support_of (x : X) : support (of x) = {x}
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeAbelianGroup.support.eq_1`：∀ {X : Type u_1} (a : FreeAbelianGroup X)
, a.support = (FreeAbelianGroup.toFinsupp a).support
· 使用定理 `FreeAbelianGroup.toFinsupp_of`：∀ {X : Type u_1} (x : X), FreeAbelianGrou
p.toFinsupp (FreeAbelianGroup.of x) = fun₀ | x => 1
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem support_of (x : X) : support (of x) = {x} := by
  rw [support, toFinsupp_of, Finsupp.support_single _ one_ne_zero]

@[simp]
/-
**FreeAbelianGroup.support_neg** 是 Mathlib 中的一个定理，位于命名空间 `FreeAbelianGroup`。
形式化陈述：support_neg (a : FreeAbelianGroup X) : support (-a) = support a
参数：a : FreeAbelianGroup X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用引理 `Finsupp.support_neg`：support_neg (f : ι ->₀ G) : support (-f) = support 
f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem support_neg (a : FreeAbelianGroup X) : support (-a) = support a := by
  simp only [support, map_neg, Finsupp.support_neg]

@[simp]
/-
**FreeAbelianGroup.support_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `FreeAbelianGroup`。
形式化陈述：support_zsmul (k : Int) (h : k != 0) (a : FreeAbelianGroup X) : support (k
 • a) = support a
参数：k : Int；h : k != 0；a : FreeAbelianGroup X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_zsmul (k : ℤ) (h : k ≠ 0) (a : FreeAbelianGroup X) :
    support (k • a) = support a := by
  ext x
  simp [h]

@[simp]
/-
**FreeAbelianGroup.support_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `FreeAbelianGroup`。
形式化陈述：support_nsmul (k : Nat) (h : k != 0) (a : FreeAbelianGroup X) : support (k
 • a) = support a
参数：k : Nat；h : k != 0；a : FreeAbelianGroup X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeAbelianGroup.support_zsmul`：support_zsmul (k : Int) (h : k != 0) (a 
: FreeAbelianGroup X) : support (k • a) = support a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem support_nsmul (k : ℕ) (h : k ≠ 0) (a : FreeAbelianGroup X) :
    support (k • a) = support a := by
  apply support_zsmul k _ a
  exact mod_cast h

open scoped Classical in
/-
**FreeAbelianGroup.support_add** 是 Mathlib 中的一个定理，位于命名空间 `FreeAbelianGroup`。
形式化陈述：support_add (a b : FreeAbelianGroup X) : support (a + b) subseteq a.suppor
t union b.support
参数：a b : FreeAbelianGroup X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用引理 `Finsupp.support_add`：support_add [DecidableEq ι] : (g₁ + g₂).support sub
seteq g₁.support union g₂.support
-/
theorem support_add (a b : FreeAbelianGroup X) : support (a + b) ⊆ a.support ∪ b.support := by
  simp only [support, map_add]
  apply Finsupp.support_add
/-
**FreeAbelianGroup.support_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `FreeAbelianGroup`
。
形式化陈述：∀ {X : Type u_1} {a : FreeAbelianGroup X}, a.support = ∅ ↔ a = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finsupp.support_eq_empty`：support_eq_empty {f : α ->₀ M} : f.support = ∅
 ↔ f = 0
· 使用定理 `AddEquiv.map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZer
oClass M] [inst_1 : AddZeroClass N] (h : M ≃+ N) {x : M}, h x = 0 ↔ x = 0
-/
@[simp] theorem support_eq_empty {a : FreeAbelianGroup X} : a.support = ∅ ↔ a = 0 :=
  Finsupp.support_eq_empty.trans (equivFinsupp X).map_eq_zero_iff
/-
**FreeAbelianGroup.nonempty_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeAbelianGr
oup`。
形式化陈述：∀ {X : Type u_1} {a : FreeAbelianGroup X}, a.support.Nonempty ↔ a ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₃`：contrapose_iff₃ {p q : Prop} 
: (¬ p ↔ q) -> (p ↔ ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeAbelianGroup.support_eq_empty`：∀ {X : Type u_1} {a : FreeAbelianGrou
p X}, a.support = ∅ ↔ a = 0
-/
@[simp] theorem nonempty_support_iff {a : FreeAbelianGroup X} :
    a.support.Nonempty ↔ a ≠ 0 := by
  contrapose!; exact support_eq_empty
/-
**FreeAbelianGroup.card_support_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `FreeAbelianGr
oup`。
形式化陈述：card_support_eq_zero {a : FreeAbelianGroup X} : a.support.card = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem card_support_eq_zero {a : FreeAbelianGroup X} : a.support.card = 0 ↔ a = 0 := by
  simp
/-
**FreeAbelianGroup.eq_sum_support_coeff_smul_of** 是 Mathlib 中的一个定理，位于命名空间 `FreeA
belianGroup`。
形式化陈述：eq_sum_support_coeff_smul_of (a : FreeAbelianGroup X) : a = ∑ x in a.suppo
rt, coeff x a • of x
参数：a : FreeAbelianGroup X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.toFreeAbelianGroup_toFinsupp`：Finsupp.toFreeAbelianGroup_toFinsu
pp {X} (x : FreeAbelianGroup X) : Finsupp.toFreeAbelianGroup (FreeAbelianGroup.t
oFinsupp x) = x
· 使用定理 `Finsupp.sum_single`：sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum s
ingle = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.toFreeAbelianGroup_single`：∀ {X : Type u_1} (x : X) (n : ℤ), (Fi
nsupp.toFreeAbelianGroup fun₀ | x => n) = n • FreeAbelianGroup.of x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.applyAddHom_apply`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZe
roClass M] (a : ι) (g : ι →₀ M), (Finsupp.applyAddHom a) g = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_sum_support_coeff_smul_of (a : FreeAbelianGroup X) :
    a = ∑ x ∈ a.support, coeff x a • of x := by
  conv_lhs => rw [← toFreeAbelianGroup_toFinsupp a, ← sum_single a.toFinsupp]
  simp [sum, support, coeff]

end FreeAbelianGroup

